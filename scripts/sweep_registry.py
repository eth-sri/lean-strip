#!/usr/bin/env python3
"""Run lean-strip over every Palomar registry result, one container per result.

    python3 scripts/sweep_registry.py snapshot   --out sweep/          # freeze the registry
    python3 scripts/sweep_registry.py run        --out sweep/ --parallel 6 --memory 64g --cpus 8
    python3 scripts/sweep_registry.py summary    --out sweep/

Each result is cloned at its registered commit (falling back to the registry's
preservation fork), and lean-strip runs in its project directory against the
comparator config, solution and challenge the record names. Successful
checkouts are deleted right away (with ``--keep-checkouts``, kept like failed
ones); failed ones keep their sources, lean-strip's logs and the clone's `.git`
(so `git diff` shows the strip) but lose every `.lake` and `.lean-strip/work`,
so the disk only ever holds the builds in flight. No run starts while the disk
has less than ``--min-free-gb`` free. Results go to `results.jsonl`, one line per run; a rerun skips results
that already have one (``--retry-failed`` reruns failures).

Write a number to `<out>/parallel` to change how many results run at once, or
create `<out>/stop` to let the runs in flight finish and start no more.

This is a test harness for lean-strip itself, not part of the installed tool.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import shutil
import signal
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
from pathlib import Path

API = "https://data.palomar-registry.org/api/v1/results"
DATA = "https://data.palomar-registry.org/"
USER_AGENT = "lean-strip-sweep/1.1 (+https://github.com/eth-sri/lean-strip)"
REPO_ROOT = Path(__file__).resolve().parents[1]
_write_lock = threading.Lock()


def _code_version() -> str:
    """A hash of the lean-strip sources the runs use, recorded with every result."""

    import hashlib

    digest = hashlib.sha256()
    for path in sorted((REPO_ROOT / "src" / "lean_strip").rglob("*.py")):
        digest.update(path.relative_to(REPO_ROOT).as_posix().encode() + path.read_bytes())
    return digest.hexdigest()[:12]


def _get_json(url: str) -> dict:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        return json.load(response)


def snapshot(out: Path) -> None:
    """Every current result and its full record, pinned to one registry revision."""

    entries, cursor, meta = [], None, None
    while True:
        query = {"trust": "all", "order": "registered", **({"cursor": cursor} if cursor else {})}
        page = _get_json(API + "?" + urllib.parse.urlencode(query))
        if meta is None:
            meta = {key: page[key] for key in ("revision", "release", "totals")}
        elif page["revision"] != meta["revision"]:
            raise SystemExit("the registry changed while paging; run snapshot again")
        entries += page.get("entries") or []
        cursor = page.get("next")
        if not cursor:
            break
    records = out / "records"
    records.mkdir(parents=True, exist_ok=True)
    with concurrent.futures.ThreadPoolExecutor(16) as pool:
        for entry, record in zip(entries, pool.map(lambda e: _get_json(DATA + e["path"]), entries)):
            (records / f"{entry['id']}.json").write_text(json.dumps(record, indent=1) + "\n")
    (out / "snapshot.json").write_text(json.dumps(
        {**meta, "taken_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
         "ids": [entry["id"] for entry in entries]}, indent=1) + "\n")
    print(f"registry revision {meta['revision']}: {len(entries)} results -> {records}")


def _git(args: list[str], cwd: Path, timeout: int = 1800) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True, timeout=timeout,
                          env={**os.environ, "GIT_TERMINAL_PROMPT": "0"})


def _checkout(record: dict, target: Path) -> str:
    """Clone the registered commit into ``target``; returns the repository used."""

    source = record["source"]
    # The registry also preserves the project's dependencies; only the
    # project's own fork can hold its commit.
    forks = [repo["fork_repository"]
             for repo in (record.get("preservation") or {}).get("repositories", [])
             if repo.get("fork_repository") and repo.get("source_repository") == source["repository"]]
    errors = []
    for repository in [source["repository"], *forks]:
        if target.exists():
            shutil.rmtree(target)
        target.mkdir(parents=True)
        _git(["init", "-q"], target)
        _git(["remote", "add", "origin", f"https://github.com/{repository}"], target)
        fetched = _git(["fetch", "-q", "--depth", "1", "origin", source["commit"]], target)
        if fetched.returncode == 0 and _git(["checkout", "-q", "FETCH_HEAD"], target).returncode == 0:
            return repository
        errors.append(f"{repository}: {fetched.stderr.strip()[-300:]}")
    raise RuntimeError("could not fetch the registered commit: " + "; ".join(errors))


_MISSING_DEPENDENCY = ("reference is not a tree", "Repository not found",
                       "couldn't find remote ref", "not our ref", "unadvertised object")


def _use_preserved_dependencies(record: dict, project_dir: Path, work: Path) -> bool:
    """Point lake-manifest.json at the registry's preserved forks of each dependency.

    A dependency's pinned commit can vanish upstream (PALOMAR-2026-09-04-000003);
    the registry keeps a fork of every dependency at that commit. The change is
    committed in the throwaway checkout so lean-strip sees a clean tree.
    """

    def key(url: str) -> str:
        path = url.rstrip("/").removesuffix(".git").split("github.com/")[-1]
        return path.lower()

    forks = {key(repo["source_repository"]): repo["fork_repository"]
             for repo in (record.get("preservation") or {}).get("repositories", [])
             if repo.get("fork_repository") and repo.get("source_repository")}
    manifest_path = project_dir / "lake-manifest.json"
    if not manifest_path.is_file():
        return False
    manifest = json.loads(manifest_path.read_text())
    changed = False
    for package in manifest.get("packages", []):
        fork = forks.get(key(str(package.get("url", ""))))
        if package.get("type") == "git" and fork:
            package["url"] = f"https://github.com/{fork}"
            changed = True
            shutil.rmtree(project_dir / ".lake" / "packages" / str(package.get("name")), ignore_errors=True)
    if not changed:
        return False
    manifest_path.write_text(json.dumps(manifest, indent=1) + "\n")
    _git(["-c", "user.email=sweep@lean-strip", "-c", "user.name=sweep", "commit", "-qam",
          "Use the Palomar registry's preserved dependency forks"], work)
    return True


def _relative(path: str, project: str | None) -> str:
    return path[len(project) + 1:] if project and path.startswith(project + "/") else path


def _run_one(record: dict, args: argparse.Namespace) -> dict:
    rid = record["id"]
    work = args.out / "work" / rid
    log = args.out / "logs" / f"{rid}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    project = record["source"].get("project_path") or None
    form = record["formalization"]
    row: dict = {"id": rid, "repository": record["source"]["repository"],
                 "commit": record["source"]["commit"], "project_path": project,
                 "mode": "retain-lean-only" if args.retain_lean_only else "normal",
                 "code_version": args.code_version}
    started = time.time()
    try:
        row["fetched_from"] = _checkout(record, work)
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        row.update(status="failed", stage="checkout", error=str(error)[-500:])
        shutil.rmtree(work, ignore_errors=True)
        return row
    project_dir = work / project if project else work
    comparator = project_dir / _relative(form["comparator_config_path"], project)
    row["expected"] = {key: _relative(form[key], project)
                       for key in ("solution_path", "challenge_path", "comparator_config_path")}
    command = [sys.executable, "-m", "lean_strip", str(project_dir), "--comparator", str(comparator),
               "--container", args.engine, "--memory", args.memory, "--cpus", str(args.cpus),
               "--timeout", str(args.timeout)]
    if args.retain_lean_only:
        command.append("--retain-lean-only")
    def strip() -> dict:
        with log.open("w") as stream:
            process = subprocess.Popen(
                command, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True,
                env={**os.environ, "PYTHONPATH": str(REPO_ROOT / "src"),
                     # Mathlib caches one archive set per version: keep them with the sweep.
                     "XDG_CACHE_HOME": str(args.out / "cache")},
            )
            try:
                row["returncode"] = process.wait(timeout=3 * args.timeout)
            except subprocess.TimeoutExpired:
                # SIGTERM first: `podman run` forwards it, so the container
                # stops and is removed; a SIGKILL would orphan it.
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=120)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                row["returncode"] = None
        path = project_dir / ".lean-strip" / "report.json"
        return json.loads(path.read_text()) if path.is_file() else {}

    report = strip()
    failure_log = project_dir / ".lean-strip" / "failure.log"
    if (report.get("stage") == "repository_build" and failure_log.is_file()
            and any(marker in failure_log.read_text(errors="replace") for marker in _MISSING_DEPENDENCY)
            and _use_preserved_dependencies(record, project_dir, work)):
        row["dependency_forks"] = True
        report = strip()
    row["seconds"] = round(time.time() - started, 1)
    row["status"] = report.get("status") or ("timeout" if row["returncode"] is None else "failed")
    if row["status"] == "failed":
        row["stage"] = report.get("stage") or "cli"
        row["error"] = (report.get("error") or _tail(log))[-800:]
    else:
        row["tokens"] = (report.get("totals") or {}).get("tokens")
        fallback = report.get("build_fallback")
        if fallback:
            row["build_fallback"] = {"rounds": fallback.get("rounds"),
                                     "grind_restored_files": len(fallback["grind_restored_files"]),
                                     "private_module_lint_silenced": len(fallback["private_module_lint_silenced"]),
                                     "heartbeats": fallback.get("heartbeats") or [],
                                     "errors": fallback.get("errors", [])[:3]}
        lake = report.get("lakefile") or {}
        row["lakefile"] = {"rewritten": lake.get("rewritten"), "changes": lake.get("changes"),
                           "unresolved": lake.get("unresolved"),
                           "lake_build_ok": (lake.get("lake_build") or {}).get("ok")}
        verdict = report.get("comparator") or {}
        row["comparator"] = {key: verdict.get(key) for key in ("status", "judge", "sandbox", "seconds", "reason")} \
            if verdict else None
        # What the run changed in the clone; without --retain-lean-only only
        # Lean sources and the lakefile may differ.
        status = subprocess.run(["git", "status", "--porcelain", "--", "."], cwd=project_dir,
                                capture_output=True, text=True, check=False).stdout
        changed = [line[3:] for line in status.splitlines()]
        row["files_changed"] = len(changed)
        row["non_lean_changed"] = [
            path for path in changed
            if not path.endswith(".lean") and Path(path).name not in {"lakefile.toml", "lakefile.lean"}
        ][:50]
    keep = args.out / "reports" / rid
    keep.mkdir(parents=True, exist_ok=True)
    for name in ("report.json", "log.txt", "failure.log"):
        if (project_dir / ".lean-strip" / name).is_file():
            shutil.copyfile(project_dir / ".lean-strip" / name, keep / name)
    if row["status"] in {"stripped", "repaired", "discarded"} and not args.keep_checkouts:
        shutil.rmtree(work, ignore_errors=True)
    else:
        # Keep sources and logs; the builds are what fill the disk. The
        # backup of the original files is in the clone's `.git` as well.
        for scratch in ("work", "original", "tmp"):
            shutil.rmtree(project_dir / ".lean-strip" / scratch, ignore_errors=True)
        for parent, dirs, _ in os.walk(work):
            if ".lake" in dirs:
                dirs.remove(".lake")
                shutil.rmtree(Path(parent) / ".lake", ignore_errors=True)
    return row


def _tail(path: Path) -> str:
    try:
        return "\n".join(path.read_text(errors="replace").splitlines()[-15:])
    except OSError:
        return ""


def run(args: argparse.Namespace) -> None:
    ids = json.loads((args.out / "snapshot.json").read_text())["ids"]
    if args.only:
        ids = [rid for rid in ids if rid in set(args.only)]
    results = args.out / "results.jsonl"
    done: dict[str, dict] = {}
    if results.is_file():
        for line in results.read_text().splitlines():
            row = json.loads(line)
            done[row["id"]] = row
    todo = [rid for rid in ids if rid not in done or args.rerun
            or (args.retry_failed and done[rid]["status"] not in {"stripped", "repaired", "discarded"})]
    # Longest previous runs first (unknown ones before them), so that hour-long
    # results do not form the tail of the sweep; `--order-from` lends the times
    # of other sweeps.
    seconds = {rid: row.get("seconds") for rid, row in done.items()}
    for other in args.order_from or []:
        for line in Path(other).read_text().splitlines():
            row = json.loads(line)
            seconds.setdefault(row["id"], row.get("seconds"))
    todo.sort(key=lambda rid: -(seconds.get(rid) or float("inf")))
    if args.limit:
        todo = todo[: args.limit]
    print(f"{len(todo)} to run ({len(done)} already recorded), {args.parallel} at a time", flush=True)

    def task(rid: str) -> None:
        record = json.loads((args.out / "records" / f"{rid}.json").read_text())
        try:
            row = _run_one(record, args)
        except Exception as error:  # a harness bug must not stop the sweep
            row = {"id": rid, "status": "failed", "stage": "harness", "error": repr(error)[-800:]}
        with _write_lock:
            with results.open("a") as stream:
                stream.write(json.dumps(row, sort_keys=True) + "\n")
            print(f"[{time.strftime('%H:%M:%S')}] {rid}: {row['status']}"
                  + (f" at {row.get('stage')}" if row["status"] == "failed" else "")
                  + (f" ({row.get('seconds')}s)" if row.get("seconds") else ""), flush=True)

    # Parallelism can change while the sweep runs: write a number to
    # `<out>/parallel`; an existing `<out>/stop` starts no further runs.
    running: set[concurrent.futures.Future] = set()
    with concurrent.futures.ThreadPoolExecutor(max_workers=256) as pool:
        queue = list(todo)
        while queue or running:
            running = {future for future in running if not future.done()}
            stop = (args.out / "stop").exists() or shutil.disk_usage(args.out).free < args.min_free_gb * 1024**3
            if queue and not stop and len(running) < _parallelism(args):
                running.add(pool.submit(task, queue.pop(0)))
                continue
            if stop and not running:
                print(f"stopped with {len(queue)} left", flush=True)
                return
            time.sleep(5)


def _parallelism(args: argparse.Namespace) -> int:
    try:
        return max(0, int((args.out / "parallel").read_text().strip()))
    except (OSError, ValueError):
        return args.parallel


def summary(out: Path) -> None:
    rows: dict[str, dict] = {}
    for line in (out / "results.jsonl").read_text().splitlines():
        row = json.loads(line)
        rows[row["id"]] = row  # the latest run of each result wins
    from collections import Counter
    print(Counter(row["status"] for row in rows.values()))
    print(Counter(row.get("stage") for row in rows.values() if row["status"] == "failed"))
    edited = [row for row in rows.values() if (row.get("lakefile") or {}).get("rewritten")]
    broken = [row["id"] for row in rows.values() if (row.get("lakefile") or {}).get("lake_build_ok") is False]
    print(f"lakefile edited: {len(edited)}; plain lake build failing: {len(broken)} {broken[:10]}")
    fell_back = [row["id"] for row in rows.values() if row.get("build_fallback")]
    print(f"build fallback (strip missed a dependency): {len(fell_back)} {fell_back[:10]}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("snapshot", "run", "summary"))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--parallel", type=int, default=4)
    parser.add_argument("--memory", default="64g")
    parser.add_argument("--cpus", type=int, default=8)
    parser.add_argument("--engine", default="auto", choices=("auto", "podman", "docker"))
    parser.add_argument("--timeout", type=int, default=6 * 3600)
    parser.add_argument("--retain-lean-only", action="store_true")
    parser.add_argument("--keep-checkouts", action="store_true",
                        help="keep successful checkouts too (without .lake)")
    parser.add_argument("--min-free-gb", type=int, default=60,
                        help="start no run while the disk has less free")
    parser.add_argument("--only", nargs="*")
    parser.add_argument("--order-from", nargs="*", type=Path,
                        help="results.jsonl files whose run times order this sweep, longest first")
    parser.add_argument("--limit", type=int)
    parser.add_argument("--retry-failed", action="store_true")
    parser.add_argument("--rerun", action="store_true",
                        help="with --only: run those results again even if already recorded")
    args = parser.parse_args()
    if args.rerun and not args.only:
        parser.error("--rerun needs --only")
    args.out = args.out.resolve()
    args.code_version = _code_version()
    if args.command == "snapshot":
        snapshot(args.out)
    elif args.command == "run":
        run(args)
    else:
        summary(args.out)


if __name__ == "__main__":
    main()
