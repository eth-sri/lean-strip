"""Strip a Palomar-style Lean repository in place.

Run it from a repository that contains comparator.json plus the solution and
challenge modules it names. The repository is built (or its build reused),
copied into a scratch workspace under .lean-strip/, isolated to the
solution/challenge import closure, and stripped by the LeanLean preprocessing.
Only .lean files of the repository are then changed: stripped sources are
rewritten and Lean files outside the closure are deleted. The challenge file,
the Lake configuration, READMEs and every other file are left untouched, unless
--retain-lean-only asks for everything the Lean build does not need to go too.
"""

from __future__ import annotations

import argparse
import json
import os
import posixpath
import re
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any, Callable

from lean_strip._pipeline import palomar_normalize as normalize

from . import benchmark
from .choose import ConfigError, ask_for_comparator, describe, find_comparators, load_comparator
from .engine import StripFailure, StripSettings, iter_lean_files, run_strip
from .report import measure_tree, render_summary, summarize
from .workspace import LocalWorkspace

try:
    import resource
except ImportError:  # not available on Windows
    resource = None

STATE_DIR = ".lean-strip"
# Never treated as project files. `.lean_strip` is the state directory of
# versions before the rename.
SKIP_DIRS = (STATE_DIR, ".lean_strip")
DOCUMENT_NAMES = ("readme", "license", "licence", "notice", "copying")
# Lake's job status symbols (✔ ✖ ⚠ …); `✖` also marks jobs still running.
_LEADING_SYMBOLS = re.compile(r"^[^\w\[]+")


class _Console:
    def __init__(self, log_path: Path, quiet: bool) -> None:
        self.log_file = log_path.open("w", encoding="utf-8")
        self.quiet = quiet
        self.started = time.perf_counter()

    def log(self, line: str) -> None:
        stamp = f"{time.perf_counter() - self.started:8.1f}s"
        self.log_file.write(f"{stamp} {line}\n")
        self.log_file.flush()

    def say(self, line: str = "", *, always: bool = False) -> None:
        self.log(line)
        if always or not self.quiet:
            print(line, file=sys.stderr, flush=True)

    def stage(self, name: str) -> "_Stage":
        return _Stage(self, name)


class _Stage:
    def __init__(self, console: _Console, name: str) -> None:
        self.console = console
        self.name = name
        self.notes: list[str] = []
        self.details: list[str] = []
        self.seconds = 0.0

    def note(self, text: str) -> None:
        """Add to the summary after the stage's status."""
        self.notes.append(text)

    def detail(self, text: str) -> None:
        """Add a line printed under the stage's status."""
        self.details.append(text)

    def progress(self, text: str) -> None:
        """Show ``text`` after the stage name until the stage ends (terminals only)."""

        text = _LEADING_SYMBOLS.sub("", " ".join(text.split()))
        if self._live and text:
            self._text = text
            self._draw()

    def _draw(self) -> None:
        # Called from reader threads and the ticker, hence the lock.
        with self._lock:
            if not self._live:
                return
            elapsed = time.perf_counter() - self._start
            line = f"{self._prefix}{'':<6} {elapsed:7.1f}s  {self._text}"
            width = shutil.get_terminal_size().columns - 1
            print(f"\r\x1b[2K{line[:width]}", end="", file=sys.stderr, flush=True)

    def _tick(self) -> None:
        while not self._done.wait(0.5):
            self._draw()

    def __enter__(self) -> "_Stage":
        self.console.log(f"== {self.name}")
        self._prefix = f"  • {self.name:<24}"
        self._start = time.perf_counter()
        self._live = not self.console.quiet and sys.stderr.isatty()
        self._text = ""
        self._lock = threading.Lock()
        self._done = threading.Event()
        if not self.console.quiet:
            print(self._prefix, end="", file=sys.stderr, flush=True)
        if self._live:
            threading.Thread(target=self._tick, daemon=True).start()
        return self

    def __exit__(self, kind, error, _traceback) -> None:
        self.seconds = round(time.perf_counter() - self._start, 1)
        status = "ok" if kind is None else "FAILED"
        detail = "; ".join(self.notes)
        line = f"{status:<6} {self.seconds:7.1f}s" + (f"  {detail}" if detail else "")
        self.console.log(f"== {self.name}: {line}")
        for detail in self.details:
            self.console.log(f"==   {detail}")
        self._done.set()
        if self._live:
            with self._lock:
                self._live = False
                print(f"\r\x1b[2K{self._prefix}", end="", file=sys.stderr)
        if not self.console.quiet:
            print(line, file=sys.stderr, flush=True)
            for detail in self.details:
                print(f"      ↳ {detail}", file=sys.stderr, flush=True)


def _version() -> str:
    from importlib.metadata import PackageNotFoundError, version

    try:
        return version("lean-strip")
    except PackageNotFoundError:
        return "unknown (not installed)"


def _run(
    console: _Console, argv: list[str], cwd: Path, *, env: dict | None = None,
    progress: Callable[[str], None],
) -> subprocess.CompletedProcess:
    """Run ``argv`` with stdout and stderr merged, passing each line to ``progress``."""

    console.log("$ " + " ".join(argv) + f"   (cwd={cwd})")
    process = subprocess.Popen(
        argv, cwd=cwd, env=env, text=True, errors="replace",
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    lines = []
    assert process.stdout is not None
    for line in process.stdout:  # universal newlines: `\r` updates arrive as lines too
        lines.append(line)
        progress(line)
    output = "".join(lines)
    process.wait()
    console.log(f"  -> rc={process.returncode}")
    if output.strip():
        console.log(output.rstrip()[-20000:])
    return subprocess.CompletedProcess(argv, process.returncode, output, "")


def _manifest_packages(repo: Path) -> list[dict[str, Any]]:
    path = repo / "lake-manifest.json"
    try:
        packages = json.loads(path.read_text()).get("packages", []) if path.is_file() else []
    except (OSError, ValueError):
        return []
    return [package for package in packages if isinstance(package, dict)]


def _package_version(package: dict[str, Any]) -> str:
    """The requested tag or branch, else the short commit."""

    wanted = str(package.get("inputRev") or "")
    rev = str(package.get("rev") or "")
    return wanted if wanted and wanted != rev else rev[:7]


def _cache_summary(output: str) -> str:
    """What `lake exe cache get` did, from its output."""

    downloaded = re.findall(r"Downloaded: (\d+) file", output)
    unpacked = re.findall(r"Decompressed (\d+)", output)
    parts = []
    if downloaded:
        parts.append(f"{int(downloaded[-1]):,} files downloaded")
    elif "No files to download" in output:
        parts.append("already downloaded")
    if unpacked:
        parts.append(f"{int(unpacked[-1]):,} unpacked")
    return ", ".join(parts) or "done"


def _build_summary(output: str) -> str:
    """Job counts from `lake build` output."""

    jobs = re.findall(r"\((\d+) jobs?\)", output)
    compiled = len(re.findall(r"\] Built ", output))
    total = f"{int(jobs[-1]):,} jobs" if jobs else "done"
    return f"{total}, {compiled:,} compiled here" if compiled else f"{total}, all from cache"


def _raise_nofile_limit() -> None:
    if resource is None:
        return
    soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
    if hard == resource.RLIM_INFINITY or hard > soft:
        try:
            resource.setrlimit(resource.RLIMIT_NOFILE, (hard, hard))
        except (ValueError, OSError):
            pass


def _comparator(
    parser: argparse.ArgumentParser, repo: Path, given: Path | None
) -> tuple[Path, dict[str, Any]]:
    """The config named by --comparator, the only comparator*.json, or the user's pick."""

    if given is not None:
        path = given.resolve()
        if not path.is_file():
            parser.error(f"no comparator config at {path}")
        try:
            return path, load_comparator(path)
        except ConfigError as error:
            parser.error(str(error))
    candidates, skipped = [], []
    for path in find_comparators(repo, SKIP_DIRS):
        try:
            candidates.append((path, load_comparator(path)))
        except ConfigError as error:
            skipped.append(str(error))
    if len(candidates) == 1:
        return candidates[0]
    if not (sys.stdin.isatty() and sys.stderr.isatty()):
        if not candidates:
            parser.error(
                "no usable comparator*.json found; pass --comparator"
                + "".join(f"\n  skipped {problem}" for problem in skipped)
            )
        parser.error(
            f"found {len(candidates)} comparator configs; pick one with --comparator:"
            + "".join(f"\n  {describe(repo, path, config)}" for path, config in candidates)
        )
    return ask_for_comparator(repo, candidates, skipped)


def _in_git(repo: Path) -> bool:
    inside = subprocess.run(
        ["git", "rev-parse", "--is-inside-work-tree"], cwd=repo, capture_output=True, text=True
    )
    return inside.returncode == 0


def _dirty_files(repo: Path, *pathspec: str) -> list[str] | None:
    if not _in_git(repo):
        return None
    status = subprocess.run(
        ["git", "status", "--porcelain=v1", "--", *pathspec], cwd=repo, capture_output=True, text=True
    )
    return [line[3:] for line in status.stdout.splitlines() if line.strip()]


def _repository_files(repo: Path) -> list[str]:
    """Tracked and untracked, not ignored, files; every file outside a Git repository."""

    if _in_git(repo):
        listed = subprocess.run(
            ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
            cwd=repo, capture_output=True, text=True, check=True,
        )
        paths = listed.stdout.split("\0")
    else:
        paths = [path.relative_to(repo).as_posix() for path in repo.rglob("*")]
    return sorted(
        relative for relative in paths
        if relative
        and Path(relative).parts[0] not in {".git", ".lake", *SKIP_DIRS}
        and (repo / relative).is_file()
    )


def _prepare_workspace(repo: Path, work: Path) -> None:
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(
        repo, work, symlinks=True,
        ignore=lambda directory, names: [
            name for name in names
            if Path(directory) == repo and name in {".git", ".lake", *SKIP_DIRS}
        ],
    )
    (work / ".lake").mkdir()
    packages = repo / ".lake" / "packages"
    if packages.is_dir():
        (work / ".lake" / "packages").symlink_to(packages.resolve(), target_is_directory=True)
    build = repo / ".lake" / "build"
    if build.is_dir():
        shutil.copytree(build, work / ".lake" / "build", symlinks=True)
    # Lake applies package overrides (e.g. path-pinned dependencies) from here;
    # without them the scratch build would try to re-resolve Git packages.
    overrides = repo / ".lake" / "package-overrides.json"
    if overrides.is_file():
        shutil.copyfile(overrides, work / ".lake" / "package-overrides.json")


def _remove_documents(work: Path) -> None:
    """Drop Markdown and README/LICENSE-style files before isolation.

    The benchmark pipeline does this too, so isolation sees the same tree. Only
    the scratch copy is affected.
    """

    for path in sorted(work.rglob("*")):
        relative = path.relative_to(work)
        if relative.parts[0] in {".lake", ".git"} or not path.is_file():
            continue
        name = path.name.lower()
        if name.endswith(".lean"):
            continue
        if name.endswith(".md") or any(
            name == stem or name.startswith(stem + ".") for stem in DOCUMENT_NAMES
        ):
            path.unlink()
    for directory in sorted((p for p in work.rglob("*") if p.is_dir()), reverse=True):
        if ".lake" in directory.relative_to(work).parts:
            continue
        try:
            directory.rmdir()
        except OSError:
            pass


def _apply_to_repository(
    repo: Path, final_sources: dict[str, str], challenge: str, backup: Path | None
) -> dict[str, list[str]]:
    """Write stripped sources back; delete Lean files that did not survive.

    With ``backup=None`` (a dry run) nothing is written; the result still lists
    what would change.
    """

    final = {path.removeprefix("/testbed/"): source for path, source in final_sources.items()}
    changed, deleted = [], []
    for relative in iter_lean_files(repo, skip=SKIP_DIRS):
        if relative == challenge or Path(relative).name == "lakefile.lean":
            continue
        target = repo / relative
        original = target.read_bytes()
        if backup is not None:
            (backup / relative).parent.mkdir(parents=True, exist_ok=True)
            (backup / relative).write_bytes(original)
        if relative in final:
            content = final[relative].encode("utf-8")
            if content != original:
                if backup is not None:
                    target.write_bytes(content)
                changed.append(relative)
        else:
            if backup is not None:
                target.unlink()
            deleted.append(relative)
    missing = sorted(set(final) - set(iter_lean_files(repo, skip=SKIP_DIRS)))
    if missing:
        raise RuntimeError(f"stripped tree has Lean files the repository lacks: {missing}")
    if backup is not None:
        _remove_empty_parents(repo, deleted)
    return {"changed": changed, "deleted": deleted}


def _remove_empty_parents(repo: Path, removed: list[str]) -> None:
    for relative in removed:
        parent = (repo / relative).parent
        while parent != repo:
            try:
                parent.rmdir()
            except OSError:
                break
            parent = parent.parent


def _lake_libraries(repo: Path) -> list[tuple[str, list[str]]]:
    """(source directory, root modules) of each Lean library in the lakefile."""

    libraries: list[tuple[str, list[str]]] = []
    toml = repo / "lakefile.toml"
    lean = repo / "lakefile.lean"
    if toml.is_file():
        payload = normalize.tomllib.loads(toml.read_text())
        package_dir = str(payload.get("srcDir", "."))
        for library in payload.get("lean_lib", []) or []:
            if isinstance(library, dict):
                libraries.append((
                    posixpath.normpath(posixpath.join(package_dir, str(library.get("srcDir", ".")))),
                    list(library.get("roots") or [str(library.get("name", ""))]),
                ))
    elif lean.is_file():
        for library in normalize._lean_libraries(lean.read_text()):
            src_dir = re.search(r'srcDir[ \t]*:=[ \t]*"([^"]*)"', str(library["section"]))
            libraries.append((
                posixpath.normpath(src_dir.group(1) if src_dir else "."),
                list(library["roots"] or [str(library["name"])]),
            ))
    return libraries


def _module_source(repo: Path, module: str) -> str:
    """Repository-relative source file of `module`, honouring lakefile `srcDir`s.

    The repository root is tried first, so projects without a `srcDir` resolve
    exactly as before; otherwise each Lean library's source directory is tried.
    """

    relative = normalize._module_to_relative_path(module).as_posix()
    candidates = [relative]
    for src_dir, _roots in _lake_libraries(repo):
        if src_dir != ".":
            candidate = posixpath.join(src_dir, relative)
            if candidate not in candidates:
                candidates.append(candidate)
    for candidate in candidates:
        if (repo / candidate).is_file():
            return candidate
    return relative


def _root_stubs(repo: Path, final_sources: dict[str, str], challenge: str) -> dict[str, str]:
    """Import-only replacements for lakefile root modules the strip deleted.

    Lake builds a library from its root modules, so deleting an umbrella root
    (`Foo.lean` for `lean_lib Foo`) breaks plain `lake build`. The stub imports
    every surviving module under the root instead, and the lakefile stays as it is.
    """

    surviving = {path.removeprefix("/testbed/") for path in final_sources}
    stubs: dict[str, str] = {}
    for src_dir, roots in _lake_libraries(repo):
        base = "" if src_dir == "." else src_dir + "/"
        for root in roots:
            relative = base + root.replace(".", "/") + ".lean"
            if relative in surviving or relative == challenge or not (repo / relative).is_file():
                continue
            prefix = base + root.replace(".", "/") + "/"
            modules = sorted(
                path[len(base):].removesuffix(".lean").replace("/", ".")
                for path in surviving
                if path.startswith(prefix) and path.endswith(".lean")
            )
            stubs[relative] = "".join(f"import {module}\n" for module in modules)
    return stubs


def _retain_lean_only(
    repo: Path, keep: set[str], backup: Path | None
) -> list[str]:
    """Delete repository files outside ``keep``; ``backup=None`` only lists them."""

    removed = [relative for relative in _repository_files(repo) if relative not in keep]
    if backup is not None:
        for relative in removed:
            (backup / relative).parent.mkdir(parents=True, exist_ok=True)
            shutil.move(repo / relative, backup / relative)
        _remove_empty_parents(repo, removed)
    return removed


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="lean-strip",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--version", action="version", version=f"%(prog)s {_version()}")
    parser.add_argument("repo", nargs="?", default=".", type=Path, help="repository root (default: .)")
    parser.add_argument("--comparator", type=Path, help="comparator config (default: the repository's comparator*.json; asks if there are several)")
    parser.add_argument("--dry-run", action="store_true", help="strip in the scratch workspace only; do not touch the repository")
    parser.add_argument("--force", action="store_true", help="run even if the repository has uncommitted .lean changes (any changes with --retain-lean-only)")
    parser.add_argument("--keep-work", action="store_true", help="keep .lean-strip/work after a successful run")
    parser.add_argument("--jobs", type=int, default=8, help="LEAN_NUM_THREADS and parallel grind files (default: 8)")
    parser.add_argument("--timeout", type=int, default=21600, help="per-command timeout in seconds (default: 21600)")
    parser.add_argument("--quiet", action="store_true", help="only print the final summary")
    parser.add_argument("--clean-certify", action="store_true", help="also rebuild the stripped project from a clean .lake/build before accepting it")
    parser.add_argument("--retain-lean-only", action="store_true", help="also delete every file the Lean build does not need (READMEs, docs, scripts, CI, ...); git-ignored files stay")
    parser.add_argument("--leanlean-benchmark", action="store_true", help="write the repository in the published LeanLean benchmark's layout: its lakefile roots and non-Lean files, without the challenge and comparator config")
    parser.add_argument("--lake-root-repair", action="store_true", help="with --leanlean-benchmark: also synchronize the lakefile roots with every locally imported module (the benchmark's publication repair)")
    parser.add_argument("--asset-rule", choices=("comment-aware", "before-cleanup"), help="with --leanlean-benchmark: the benchmark's asset resolver revision (default: comment-aware)")
    args = parser.parse_args(argv)
    if (args.lake_root_repair or args.asset_rule) and not args.leanlean_benchmark:
        parser.error("--lake-root-repair and --asset-rule require --leanlean-benchmark")
    if args.leanlean_benchmark and args.retain_lean_only:
        parser.error("--leanlean-benchmark decides the non-Lean files itself; drop --retain-lean-only")
    strict = args.retain_lean_only or args.leanlean_benchmark

    repo = args.repo.resolve()
    if not any((repo / name).is_file() for name in ("lakefile.toml", "lakefile.lean")):
        parser.error(f"{repo} is not a Lake project (no lakefile)")
    try:
        comparator_path, comparator = _comparator(parser, repo, args.comparator)
    except (KeyboardInterrupt, EOFError):
        print("\ncancelled", file=sys.stderr)
        return 130
    solution_module = comparator["solution_module"]
    challenge_module = comparator["challenge_module"]
    solution_rel = _module_source(repo, solution_module)
    challenge_rel = _module_source(repo, challenge_module)
    for relative in (solution_rel, challenge_rel):
        if not (repo / relative).is_file():
            parser.error(f"{relative} (named by {comparator_path.name}) does not exist")

    dirty = _dirty_files(repo, *(() if strict else ("*.lean",)))
    if dirty and not args.force and not args.dry_run:
        parser.error(
            f"uncommitted {'' if strict else '.lean '}changes "
            "(commit them or pass --force): " + ", ".join(dirty[:10])
        )

    state = repo / STATE_DIR
    state.mkdir(exist_ok=True)
    (state / ".gitignore").write_text("*\n")
    work = state / "work"
    diagnostics = state / "diagnostics"
    if diagnostics.exists():
        shutil.rmtree(diagnostics)
    diagnostics.mkdir()
    console = _Console(state / "log.txt", args.quiet)
    _raise_nofile_limit()
    build_target = f"+{solution_module}"
    lake_env = {**os.environ, "LEAN_NUM_THREADS": str(args.jobs)}

    shown = comparator_path.relative_to(repo) if comparator_path.is_relative_to(repo) else comparator_path
    theorems = len(set(comparator.get("theorem_names", [])))
    definitions = len(set(comparator.get("definition_names", [])))
    toolchain = repo / "lean-toolchain"
    requires = [
        f"{p['name']} {_package_version(p)}"
        for p in _manifest_packages(repo) if not p.get("inherited") and p.get("name")
    ]
    console.say(f"lean-strip {repo}")
    console.say(f"  config     {shown}")
    console.say(f"  solution   {solution_rel}")
    console.say(f"  challenge  {challenge_rel}")
    console.say(f"  protects   {theorems} theorem(s), {definitions} definition(s)")
    if toolchain.is_file():
        console.say(f"  toolchain  {toolchain.read_text().strip()}")
    if requires:
        console.say(f"  requires   {', '.join(requires)}")
    console.say(f"  jobs       {args.jobs}" + ("   (dry run: the repository stays unchanged)"
                                                if args.dry_run else ""))
    console.say("")
    before = measure_tree(repo, skip=SKIP_DIRS, exclude={challenge_rel})
    challenge_metrics = measure_tree(repo, only={challenge_rel})
    result = None
    outcome: dict[str, Any] = {"status": "failed"}
    started = time.perf_counter()
    try:
        with console.stage("Build repository") as stage:
            stage.progress("checking for an up-to-date build")
            # Expected to fail when a rebuild is needed; only its dependency
            # fetching (`info: mathlib: cloning ...`) is worth showing.
            fresh = _run(
                console, ["lake", "build", build_target, "--no-build"], repo, env=lake_env,
                progress=lambda line: line.startswith("info:") and stage.progress(line),
            )
            if fresh.returncode == 0:
                stage.note("existing build is up to date")
            else:
                mathlib = next(
                    (p for p in _manifest_packages(repo) if p.get("name") == "mathlib"), None
                )
                if mathlib is not None:
                    stage.progress("fetching the Mathlib build cache")
                    cache = _run(console, ["lake", "exe", "cache", "get"], repo, env=lake_env,
                                 progress=stage.progress)
                    stage.detail(
                        f"Mathlib {_package_version(mathlib)} detected, "
                        + (f"using its prebuilt cache ({_cache_summary(cache.stdout)})"
                           if cache.returncode == 0
                           else "no prebuilt cache available: building it from source")
                    )
                stage.progress(f"lake build {build_target}")
                built = _run(console, ["lake", "build", build_target], repo, env=lake_env,
                             progress=stage.progress)
                if built.returncode != 0:
                    raise StripFailure("repository_build", "lake build failed in the repository",
                                       built.stdout)
                stage.detail(f"lake build {build_target}: {_build_summary(built.stdout)}")
                stage.note("built")

        with console.stage("Isolate") as stage:
            _prepare_workspace(repo, work)
            _remove_documents(work)
            lean_before = len(set(iter_lean_files(work)) - {"lakefile.lean"})
            try:
                isolation = normalize.normalize(
                    work,
                    (Path(solution_rel), Path(challenge_rel)),
                    drop_entries=(Path(challenge_rel),),
                    root_modules=(solution_module, challenge_module),
                )
            except subprocess.CalledProcessError as error:
                raise StripFailure("isolate", str(error), error.stdout or "") from error
            except ValueError as error:
                raise StripFailure("isolate", str(error)) from error
            isolated_lean = set(iter_lean_files(work))
            kept = isolation["retained_local_source_count"]
            stage.note(
                f"kept {kept} / {lean_before} Lean file(s) in the solution/challenge "
                f"closure, deleted {lean_before - kept}"
            )

        ws = LocalWorkspace(
            work, state / "tmp", default_timeout=args.timeout,
            lean_threads=args.jobs, command_log=console.log,
        )
        settings = StripSettings(
            entry_module=solution_module,
            build_target=build_target,
            protected=set(comparator["protected"]),
            diagnostics_dir=diagnostics,
            query_timeout=args.timeout,
            file_workers=args.jobs,
            clean_certify=args.clean_certify,
        )
        result = run_strip(ws, settings, console.stage)

        if not result.discarded:
            with console.stage("Challenge check") as stage:
                (work / challenge_rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(repo / challenge_rel, work / challenge_rel)
                check = ws.execute_stream(
                    ["lake", "build", f"+{challenge_module}"],
                    timeout=args.timeout, on_output=stage.progress,
                )
                (work / challenge_rel).unlink()
                if check["returncode"] != 0:
                    raise StripFailure("challenge_check", "the challenge no longer elaborates", check["output"])
                stage.note("challenge statements elaborate against the stripped tree")

        stubs: dict[str, str] = {}
        benchmark_files: set[str] = set()
        if not result.discarded and args.leanlean_benchmark:
            # Decided on the repository as it still is, before it is rewritten.
            benchmark_files = benchmark.benchmark_non_lean_files(
                repo, isolation["retained_local_sources"], _repository_files(repo),
                before_cleanup=args.asset_rule == "before-cleanup",
            )
        elif not result.discarded:
            stubs = _root_stubs(repo, result.final_sources, challenge_rel)
        if stubs:
            with console.stage("Lakefile roots") as stage:
                for relative, content in stubs.items():
                    (work / relative).parent.mkdir(parents=True, exist_ok=True)
                    (work / relative).write_text(content)
                imported = sorted({
                    line.removeprefix("import ")
                    for content in stubs.values() for line in content.splitlines()
                })
                checks = [["lake", "build", *(f"+{module}" for module in imported)]] if imported else []
                checks += [["lake", "env", "lean", relative] for relative in sorted(stubs)]
                failed = None
                for argv in checks:
                    check = ws.execute_stream(argv, timeout=args.timeout, on_output=stage.progress)
                    if check["returncode"] != 0:
                        failed = check
                        break
                if failed is not None:
                    # `lake build +M` only accepts modules covered by a library's
                    # roots/globs; `lake lean` builds a stub's imports through module
                    # resolution instead, retried while Lake races on rebuilt imports.
                    if not re.search(r"unknown module|object file '[^']*\.olean' of module \S+ does not exist",
                                     failed["output"]):
                        raise StripFailure("lakefile_roots", "an import stub for a deleted lakefile root does not elaborate", failed["output"])
                    for relative in sorted(stubs):
                        for _attempt in range(4):
                            check = ws.execute_stream(["lake", "lean", relative], timeout=args.timeout, on_output=stage.progress)
                            if check["returncode"] == 0 or not re.search(
                                r"object file '[^']*\.olean' of module \S+ does not exist", check["output"]
                            ):
                                break
                        if check["returncode"] != 0:
                            raise StripFailure("lakefile_roots", "an import stub for a deleted lakefile root does not elaborate", check["output"])
                stage.note(f"kept {', '.join(sorted(stubs))} as import-only stub(s)")

        final_sources = {**result.final_sources, **{f"/testbed/{r}": c for r, c in stubs.items()}}
        keep = {path.removeprefix("/testbed/") for path in final_sources} | {challenge_rel}
        keep |= set(normalize.ROOT_BUILD_METADATA) | set(isolation.get("retained_local_assets", []))
        if comparator_path.is_relative_to(repo):
            keep.add(comparator_path.relative_to(repo).as_posix())
        applied = {"changed": [], "deleted": []}
        retained_away: list[str] = []
        if args.dry_run and not result.discarded:
            applied = _apply_to_repository(repo, final_sources, challenge_rel, None)
            if args.retain_lean_only:
                retained_away = _retain_lean_only(repo, keep, None)
        elif not result.discarded:
            with console.stage("Apply to repository") as stage:
                backup = state / "original"
                if backup.exists():
                    shutil.rmtree(backup)
                applied = _apply_to_repository(repo, final_sources, challenge_rel, backup)
                stage.note(f"{len(applied['changed'])} rewritten, {len(applied['deleted'])} deleted")
                if args.retain_lean_only:
                    retained_away = _retain_lean_only(repo, keep, backup)
                    stage.note(f"{len(retained_away)} other file(s) deleted")
            if args.leanlean_benchmark:
                with console.stage("LeanLean benchmark layout") as stage:
                    comparator_rel = (comparator_path.relative_to(repo).as_posix()
                                      if comparator_path.is_relative_to(repo) else None)
                    layout_keep = {path.removeprefix("/testbed/") for path in final_sources} | benchmark_files
                    layout_keep -= {challenge_rel, comparator_rel}
                    retained_away = _retain_lean_only(repo, layout_keep, backup)
                    lake_roots = benchmark.benchmark_lake_roots(
                        repo, solution_module, challenge_module, repair=args.lake_root_repair,
                        sources=[repo / path for path in _repository_files(repo) if path.endswith(".lean")],
                    )
                    benchmark_layout = {
                        "asset_rule": args.asset_rule or "comment-aware",
                        "lake_roots": lake_roots,
                        "removed": retained_away,
                    }
                    stage.note(f"{len(retained_away)} file(s) removed; lakefile roots "
                               f"{lake_roots['isolation'].get('status')}"
                               + (", repaired" if args.lake_root_repair else ""))
        # Root stubs are Lake scaffolding, not project code, so they are not measured.
        after = (
            measure_tree(repo, skip=SKIP_DIRS, exclude={challenge_rel, *stubs})
            if not args.dry_run
            else measure_tree(work, exclude=set(stubs))
        )
        outcome = summarize(
            repo=repo,
            before=before,
            isolated=sorted(isolated_lean),
            after=after,
            challenge=challenge_metrics,
            isolation=isolation,
            result=result,
            applied=applied,
            dry_run=args.dry_run,
        )
        outcome["lake_root_stubs"] = sorted(stubs)
        if args.leanlean_benchmark and not result.discarded and not args.dry_run:
            outcome["leanlean_benchmark"] = benchmark_layout
        outcome["files"]["deleted_non_lean"] = retained_away
        outcome["status"] = "discarded" if result.discarded else "stripped"
        if not args.keep_work and not args.dry_run:
            shutil.rmtree(work, ignore_errors=True)
    except StripFailure as failure:
        outcome = {"status": "failed", "stage": failure.stage, "error": str(failure)}
        (state / "failure.log").write_text(failure.output)
        console.say(f"\nFAILED at {failure.stage}: {failure}", always=True)
        if failure.output:
            console.say("  last output lines:", always=True)
            for line in failure.output.strip().splitlines()[-15:]:
                console.say("    " + line, always=True)
        console.say(f"  full log: {state / 'log.txt'}; workspace kept at {work}", always=True)
    finally:
        outcome["seconds"] = round(time.perf_counter() - started, 1)
        if result is not None:
            outcome["engine_report"] = result.report
        (state / "report.json").write_text(json.dumps(outcome, indent=2, sort_keys=True) + "\n")

    if outcome["status"] == "failed":
        return 1
    console.say("")
    console.say(render_summary(outcome), always=True)
    console.say(f"\nreport: {state / 'report.json'}   log: {state / 'log.txt'}", always=True)
    if not args.dry_run and outcome["status"] == "stripped":
        console.say(f"originals backed up in {state / 'original'}; `git diff --stat` shows the change")
    return 0


if __name__ == "__main__":
    sys.exit(main())
