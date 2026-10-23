"""The strip stage sequence, run against a local ``LocalWorkspace``.

Stages: raw build, grind normalization, dependency graph, module pruning,
declaration strip, grind restore and a final build. A final build that fails
falls back to restoring files unstripped (see ``_recover_build``), so a
dependency the graph misses costs compression rather than the run.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shlex
import shutil
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from lean_strip._pipeline.preprocessing import comparator_closure
from lean_strip._pipeline.preprocessing import contract as preprocessing_contract
from lean_strip._pipeline.preprocessing import frontend
from lean_strip._pipeline.preprocessing import strip as lean_strip
from lean_strip._pipeline.preprocessing.examples import collect_anonymous_example_ranges
from lean_strip._pipeline.preprocessing.dependency_graph import (
    METHOD,
    collect_dependency_graph,
    project_source_dirs,
)
from lean_strip._pipeline.preprocessing.graph_artifact import (
    build_graph_artifact,
    graph_sha256,
    write_graph_artifact,
)
from lean_strip._pipeline.preprocessing.grind_discovery import (
    DISCOVERY_FLAGS,
    find_discovery_calls,
)
from lean_strip._pipeline.preprocessing.grind_normalization import (
    classify_edit_survival,
    normalize_discovery_sources,
    restore_original_discovery_sources,
)

from . import stacks
from .workspace import CONTAINER_ROOT, LocalWorkspace


class StripFailure(RuntimeError):
    """The repository was rejected by one of the engine's fail-closed gates."""

    def __init__(self, stage: str, message: str, output: str = "") -> None:
        super().__init__(message)
        self.stage = stage
        self.output = output


@dataclass
class StripSettings:
    entry_module: str
    build_target: str
    protected: set[str]
    diagnostics_dir: Path
    query_timeout: int = 21600
    stack_kib: int = 32768
    file_workers: int = 8
    clean_certify: bool = False
    # Stop after the dependency graph and write it (lean-strip --graph-only).
    graph_only: bool = False
    # The comparator config's names (`protected` is their union).
    theorem_names: tuple[str, ...] = ()
    definition_names: tuple[str, ...] = ()
    permitted_axioms: tuple[str, ...] = ()


@dataclass
class StripResult:
    report: dict[str, Any]
    final_sources: dict[str, str]
    decls: list[dict[str, Any]] = field(default_factory=list)
    module_paths: dict[str, str] = field(default_factory=dict)
    discarded: bool = False
    graph_only: bool = False


Stage = Callable[[str], Any]


def _parse_json_messages(output: str) -> list[dict[str, object]]:
    messages: list[dict[str, object]] = []
    for line in output.splitlines():
        try:
            row = json.loads(line)
        except ValueError:
            continue
        if isinstance(row, dict):
            messages.append(row)
    return messages


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


# Incremental rebuilds of projects using Lean's `module` system can start a
# module before Lake has rebuilt one of its (transitive) imports; Lean then
# reports the import's missing object file and a second pass succeeds.
_MISSING_IMPORT_OBJECT_RE = re.compile(
    r"object file '[^']*\.olean' of module \S+ does not exist"
)
_LAKE_RACE_RETRIES = 2
lake_race_retries: list[str] = []


# Lean aborts with this when the kernel refuses a new thread: under memory
# pressure (a container's memory limit) or a finite address space. Lake runs
# up to LEAN_NUM_THREADS Lean processes at once, so fewer threads relieve both;
# smaller thread stacks relieve an address-space limit further.
_THREAD_FAILURE = "failed to create thread"
# An address-space limit can also surface as an allocation failure.
_RESOURCE_FAILURES = (_THREAD_FAILURE, "INTERNAL PANIC: out of memory")


def resource_failure(output: str) -> bool:
    """Whether a build failed because Lean ran out of threads or address space."""

    return any(marker in output for marker in _RESOURCE_FAILURES)


def relieve_thread_pressure(env: dict[str, str], project: Path) -> str | None:
    """Lower Lean's address-space demand in ``env`` one step; None when nothing is left.

    First shrink every Lean thread's stack (see `stacks`), then halve
    LEAN_NUM_THREADS: each worker thread holds a stack too.
    """

    current = stacks.current_stack_kib(env)
    smaller = [kib for kib in stacks.STACK_STEPS_KIB if current is None or kib < current]
    if smaller:
        stacks.use_stack(env, project, smaller[0])
        return f"{smaller[0] // 1024} MiB Lean thread stacks"
    threads = int(env.get("LEAN_NUM_THREADS", "1"))
    if threads > 1:
        env["LEAN_NUM_THREADS"] = str(max(1, threads // 2))
        return f"{env['LEAN_NUM_THREADS']} Lean thread(s)"
    return None


def _lake_build(
    ws: LocalWorkspace, build_target: str, timeout: int, progress: Callable[[str], None]
) -> tuple[bool, str]:
    races = 0
    while True:
        result = ws.execute_stream(["lake", "build", build_target], timeout=timeout, on_output=progress)
        ok, output = result["returncode"] == 0, result["output"]
        if ok:
            return ok, output
        if resource_failure(output) and (relieved := relieve_thread_pressure(ws.environment, ws.root)):
            progress(f"Lean ran out of threads or address space; retrying with {relieved}")
            continue
        failures = [line for line in output.splitlines() if line.startswith("error:")]
        if races == _LAKE_RACE_RETRIES or not failures or not all(
            _MISSING_IMPORT_OBJECT_RE.search(line)
            or line in {"error: Lean exited with code 1", "error: build failed"}
            for line in failures
        ):
            return ok, output
        races += 1
        lake_race_retries.append(build_target)
        progress("retrying: Lake started a module before its rebuilt import")


_ERROR_FILE_RE = re.compile(r"^error: (?P<path>[^\s:][^:]*\.lean):\d+:\d+:", re.MULTILINE)
# Each round is an incremental rebuild.
_FALLBACK_ROUNDS = 8
# Lake prints a job's messages as indented blocks between job status lines.
_JOB_STATUS_RE = re.compile(r"^(?:[✔✖⚠]|error:|warning:|info:|trace:|Some required targets)")


def _error_blocks(output: str, limit: int = 10) -> list[str]:
    """The first ``limit`` Lean errors, each with its continuation lines."""

    blocks: list[list[str]] = []
    current: list[str] | None = None
    for line in output.splitlines():
        if line.startswith("error:") and ".lean:" in line:
            current = [line]
            blocks.append(current)
        elif current is not None and line.strip() and not _JOB_STATUS_RE.match(line):
            if len(current) < 40:
                current.append(line)
        else:
            current = None
    return ["\n".join(block) for block in blocks[:limit]]


# Stripping a module down to private declarations trips Lean's privateModule
# linter, an error under `warningAsError`. The file needs no restoring: the
# linter is told the module was stripped on purpose (PALOMAR-2026-09-18-000005).
_PRIVATE_MODULE_RE = re.compile(
    r"^error: (?P<path>[^\s:][^:]*\.lean):\d+:\d+: The current module only contains private declarations",
    re.MULTILINE,
)
_HEADER_LINE_RE = re.compile(r"^(?:module|prelude|(?:public |meta |private )*import\s+\S+.*|\s*|--.*)$")
_PRIVATE_MODULE_OPTION = "set_option linter.privateModule false"


def _silence_private_module_linter(source: str) -> str | None:
    """``source`` with the linter option after its header; None if already there."""

    if _PRIVATE_MODULE_OPTION in source:
        return None
    lines = source.split("\n")
    end = 0
    in_comment = False
    for index, line in enumerate(lines):
        stripped = line.strip()
        if in_comment:
            in_comment = "-/" not in stripped
            end = index + 1
            continue
        if stripped.startswith("/-") and not stripped.startswith("/-!") and not stripped.startswith("/--"):
            in_comment = "-/" not in stripped
            end = index + 1
            continue
        if not _HEADER_LINE_RE.match(line.rstrip("\r")):
            break
        if stripped:
            end = index + 1
    return "\n".join(lines[:end] + ["", _PRIVATE_MODULE_OPTION] + lines[end:])


def _silence_private_only_modules(
    desired: dict[str, str], originals: dict[str, str], rows: list[dict], module_paths: dict[str, str],
) -> tuple[dict[str, str], list[str]]:
    """Silence the privateModule linter in files the strip leaves only private declarations in.

    The linter reports "The current module only contains private declarations",
    an error under `warningAsError` (PALOMAR-2026-09-17-000001 kept four private
    helpers of a file whose public theorem it dropped).
    """

    kept: dict[str, list[str]] = {}
    for row in rows:
        if row["keep"] and (path := module_paths.get(str(row["module"]))):
            kept.setdefault(path, []).append(str(row["name"]))
    silenced = []
    out = dict(desired)
    for path, names in kept.items():
        content = out.get(path)
        if (content is None or content == originals.get(path)
                or not all(name.startswith("_private.") for name in names)):
            continue
        if (text := _silence_private_module_linter(content)) is not None:
            out[path] = text
            silenced.append(path)
    return out, sorted(silenced)


_TIMEOUT_RE = re.compile(
    r"\(deterministic\) timeout at `(?P<where>[^`]+)`, maximum number of heartbeats \((?P<limit>\d+)\)"
)
_ERROR_LINE_RE = re.compile(r"^error: (?P<path>[^\s:][^:]*\.lean):(?P<line>\d+):\d+:")
_HEARTBEAT_DEFAULTS = {"maxHeartbeats": 200000, "synthInstance.maxHeartbeats": 20000}
# Raised heartbeats stop here; beyond it the strip broke more than elaboration speed.
_HEARTBEAT_MAX_FACTOR = 8
_DECLARATION_LINE_RE = re.compile(
    r"^(?:@\[.*\]\s*)?(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec"
    r"|scoped|local|meta)\s+)*(?:theorem|lemma|def|abbrev|instance|example|opaque|structure"
    r"|class|inductive)\b"
)
_IN_PREFIX_RE = re.compile(r"^(?:set_option\s+\S+\s+\S+|omit\b.*|include\b.*|open\b.*|variable\b.*)\s+in\s*$")
_SET_OPTION_IN_RE = re.compile(r"^set_option\s+(?P<option>\S+)\s+(?P<value>\d+)\s+in\s*$")


def _command_start(lines: list[str], declaration: int) -> int:
    """The first line of the declaration at index ``declaration``: its docstring,
    attribute lines and `… in` prefixes included."""

    start = declaration
    while start > 0:
        previous = lines[start - 1]
        if previous.startswith("@[") or _IN_PREFIX_RE.match(previous):
            start -= 1
        elif previous.rstrip().endswith("-/"):
            opening = next((i for i in range(start - 1, -1, -1) if "/-" in lines[i]), None)
            if opening is None or not lines[opening].lstrip().startswith("/--"):
                break
            start = opening
        else:
            break
    return start


def _declaration_at(lines: list[str], index: int) -> int | None:
    """The line of the declaration that line ``index`` belongs to.

    Lean reports an error in a whole declaration at its first line, which may be
    its docstring or an attribute: those belong to the declaration below them
    (PALOMAR-2026-10-05-000007), anything else to the nearest one above.
    """

    in_docstring = False
    for below in range(index, len(lines)):
        line = lines[below]
        if in_docstring:
            in_docstring = "-/" not in line
        elif _DECLARATION_LINE_RE.match(line):
            return below
        elif line.lstrip().startswith("/--"):
            in_docstring = "-/" not in line
        elif not (line.startswith("@[") or _IN_PREFIX_RE.match(line)):
            break
    return next((i for i in range(index, -1, -1) if _DECLARATION_LINE_RE.match(lines[i])), None)


def _declaration_anchor(lines: list[str], declaration: int) -> str:
    """The declaration's first two lines: `theorem` alone on a line is common."""

    return "\n".join(lines[declaration:declaration + 2])


def _with_heartbeats(text: str, anchor: str, option: str, value: int) -> str | None:
    """``text`` with ``set_option option value in`` on the declaration starting with
    ``anchor`` (see ``_declaration_anchor``), replacing a smaller setting; None
    if the declaration is gone."""

    lines = text.split("\n")
    declaration = next((i for i in range(len(lines))
                        if _declaration_anchor(lines, i) == anchor), None)
    if declaration is None:
        return None
    start = _command_start(lines, declaration)
    setting = f"set_option {option} {value} in"
    for index in range(start, declaration):
        match = _SET_OPTION_IN_RE.match(lines[index])
        if match and match.group("option") == option:
            if int(match.group("value")) >= value:
                return text
            lines[index] = setting
            return "\n".join(lines)
    lines.insert(start, setting)
    return "\n".join(lines)


def _heartbeat_timeout(block: str, current: dict[str, str]) -> tuple[str, str, str, int] | None:
    """For a heartbeat timeout error: (path, declaration anchor, option, doubled limit)."""

    timeout = _TIMEOUT_RE.search(block)
    position = _ERROR_LINE_RE.match(block)
    if timeout is None or position is None:
        return None
    option = "synthInstance.maxHeartbeats" if timeout.group("where") == "typeclass" else "maxHeartbeats"
    value = 2 * int(timeout.group("limit"))
    if value > _HEARTBEAT_MAX_FACTOR * _HEARTBEAT_DEFAULTS[option]:
        return None
    path = f"{CONTAINER_ROOT}/{position.group('path').removeprefix('./')}"
    lines = current.get(path, "").split("\n")
    declaration = _declaration_at(lines, min(int(position.group("line")), len(lines)) - 1)
    if declaration is None:
        return None
    return path, _declaration_anchor(lines, declaration), option, value


def _remove_stale_build_outputs(ws: LocalWorkspace) -> list[str]:
    """Delete the project's build outputs for modules whose source is gone.

    The work tree reuses the repository's `.lake/build`, so a deleted module
    keeps its `.olean` and Lean imports that instead of failing: the stripped
    PALOMAR-2026-09-25-000018 "built" without the 415 files holding its proof.
    Only the root package's outputs; vendored packages build in their own
    `.lake` and are not project sources.
    """

    vendored = tuple(f"{CONTAINER_ROOT}/{path.strip('/')}" for path in ws.project_skip)
    source_dirs = [
        ws.host_path(directory)
        for directory in (project_source_dirs(ws) or [CONTAINER_ROOT])
        if not any(directory == root or directory.startswith(root + "/") for root in vendored)
    ]
    build = ws.root / ".lake" / "build"
    lib = build / "lib" / "lean"
    removed = []
    for olean in sorted(lib.rglob("*.olean")) if lib.is_dir() else []:
        relative = olean.relative_to(lib).with_suffix("")
        if any((directory / relative).with_suffix(".lean").is_file() for directory in source_dirs):
            continue
        for outputs in (lib, build / "ir"):
            for artifact in (outputs / relative.parent).glob(relative.name + ".*"):
                artifact.unlink()
        removed.append(".".join(relative.parts))
    return removed


_GRIND_FAILED_RE = re.compile(r"^error: [^\n]*\.lean:\d+:\d+: `grind` failed", re.MULTILINE)


def _grind_failure_path(block: str) -> str | None:
    """The file of an error that is `grind` itself failing, else None."""

    if not _GRIND_FAILED_RE.match(block):
        return None
    position = _ERROR_LINE_RE.match(block)
    return f"{CONTAINER_ROOT}/{position.group('path').removeprefix('./')}" if position else None


def _recover_build(
    ws: LocalWorkspace, build_target: str, timeout: int, raw_originals: dict[str, str],
    output: str, stage: Any,
) -> dict[str, Any]:
    """Repair a stripped tree that does not build, but only for errors the strip
    may legitimately cause; any other error fails the run.

    Each round handles one build's errors:

    1. A heartbeat timeout gets twice the limit on its declaration
       (`set_option … in`), up to 8x Lean's default: the strip changed how
       fast the declaration elaborates, not what it needs
       (PALOMAR-2026-10-05-000007, PALOMAR-2026-09-28-000002).
    2. A module stripped down to private declarations gets the privateModule
       linter silenced.
    3. `grind` failing restores that file unstripped: `grind +suggestions`
       picks lemmas from the environment, so a smaller environment can change
       what it finds without any dependency being missing.

    Any other error is a dependency the graph missed. Nothing is restored or
    kept to hide it: the result is ``ok: False`` with those errors in
    ``unrepaired_errors``, so the graph can be fixed.
    """

    restored: set[str] = set()
    silenced: set[str] = set()
    heartbeats: dict[tuple[str, str], tuple[str, int]] = {}
    errors: list[str] = []

    def reapply() -> None:
        for path in restored:
            ws.write_text(path, raw_originals[path])
        current = ws.snapshot([path for path in raw_originals if ws.host_path(path).is_file()])
        for path in silenced:
            if path in current and (text := _silence_private_module_linter(current[path])) is not None:
                current[path] = text
                ws.write_text(path, text)
        for (path, line), (option, value) in heartbeats.items():
            text = _with_heartbeats(current[path], line, option, value) if path in current else None
            if text is not None and text != current[path]:
                current[path] = text
                ws.write_text(path, text)

    def result(ok: bool, output: str, rounds: int, unrepaired: list[str] | None = None) -> dict[str, Any]:
        return {
            "ok": ok, "rounds": rounds,
            "heartbeats": [{"path": path, "declaration": " ".join(line.split()), "option": option, "value": value}
                           for (path, line), (option, value) in sorted(heartbeats.items())],
            "grind_restored_files": sorted(restored),
            "private_module_lint_silenced": sorted(silenced - restored),
            "unrepaired_errors": unrepaired or [],
            "errors": errors, "output": output,
        }

    rounds = 0
    while rounds < _FALLBACK_ROUNDS:
        blocks = _error_blocks(output, limit=1000)
        errors += blocks[:10]
        if not blocks:
            return result(False, output, rounds, ["the build failed without a Lean error: "
                                                  + "\n".join(output.strip().splitlines()[-5:])])
        current = ws.snapshot([path for path in raw_originals if ws.host_path(path).is_file()])
        # This round's repairs count only if every error has one.
        unrepaired: list[str] = []
        silence: set[str] = set()
        bumps: dict[tuple[str, str], tuple[str, int]] = {}
        grind: set[str] = set()
        for block in blocks:
            if (match := _PRIVATE_MODULE_RE.match(block)):
                path = f"{CONTAINER_ROOT}/{match.group('path').removeprefix('./')}"
                if path not in silenced and path in current \
                        and _silence_private_module_linter(current[path]) is not None:
                    silence.add(path)
                else:
                    unrepaired.append(block)
            elif (bump := _heartbeat_timeout(block, current)) and \
                    heartbeats.get(bump[:2], (bump[2], 0))[1] < bump[3]:
                bumps[bump[:2]] = bump[2:]
            elif (path := _grind_failure_path(block)) and path not in restored \
                    and path in raw_originals and current.get(path) != raw_originals[path]:
                grind.add(path)
            else:  # including a timeout more heartbeats did not fix
                unrepaired.append(block)
        if unrepaired:
            return result(False, output, rounds, unrepaired)
        silenced |= silence
        heartbeats.update(bumps)
        restored |= grind
        rounds += 1
        reapply()
        stage.progress(
            f"fallback round {rounds}: {len(heartbeats)} declaration(s) with more heartbeats, "
            f"{len(restored)} file(s) restored for grind; rebuilding"
        )
        ok, output = _lake_build(ws, build_target, timeout, stage.progress)
        if ok:
            return result(True, output, rounds)
    return result(False, output, rounds, _error_blocks(output))


def _fallback_summary(fallback: dict[str, Any]) -> str:
    """What the build fallback gave up, in a few words."""

    parts = []
    if fallback.get("heartbeats"):
        parts.append(f"raised heartbeats on {len(fallback['heartbeats'])} declaration(s)")
    if fallback.get("private_module_lint_silenced"):
        parts.append(f"silenced the privateModule linter in {len(fallback['private_module_lint_silenced'])} file(s)")
    if fallback.get("grind_restored_files"):
        parts.append(f"restored {len(fallback['grind_restored_files'])} file(s) unstripped where grind failed")
    rounds = fallback.get("rounds", 1)
    return (", ".join(parts) or "rebuilt") + f" ({rounds} round{'s' if rounds != 1 else ''})"


def _forget_restored_drops(
    report: dict[str, Any], fallback: dict[str, Any],
    decl_modules: dict[str, str], module_paths: dict[str, str],
) -> None:
    """Keep the report honest: declarations in restored files were not dropped."""

    restored = set(fallback["grind_restored_files"])
    for key in ("dropped_decls", "module_pruned_declarations"):
        report[key] = [
            name for name in report.get(key, [])
            if module_paths.get(decl_modules.get(name, "")) not in restored
        ]
    pruning = report.get("module_pruning") or {}
    if "deleted_files" in pruning:
        pruning["deleted_files"] = [
            path for path in pruning["deleted_files"] if f"{CONTAINER_ROOT}/{path}" not in restored
        ]


_NAMES_IN_ENVIRONMENT_LEAN = """
import Lean
open Lean

def main (args : List String) : IO Unit := do
  let some module := args.head? | return
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := module.toName }] {} 0
  for name in args.tail do
    if let some idx := env.getModuleIdxFor? name.toName then
      IO.println s!"{name}\t{env.header.moduleNames[idx]!}"
    else if env.contains name.toName then
      IO.println s!"{name}\t"
"""


def _names_in_environment(
    ws: LocalWorkspace, module: str, names: set[str], timeout: int
) -> dict[str, str]:
    """Those of ``names`` the environment importing ``module`` declares, with
    the module declaring each ("" for built-in constants)."""

    script = "/tmp/_names_in_environment.lean"
    ws.write_text(script, _NAMES_IN_ENVIRONMENT_LEAN)
    command = "cd /testbed && lake env lean --run " + " ".join(
        shlex.quote(arg) for arg in [script, module, *sorted(names)]
    )
    result = ws.execute(command, timeout=timeout)
    if result["returncode"] != 0:
        return {}
    found: dict[str, str] = {}
    for line in result["output"].splitlines():
        name, _tab, owner = line.partition("\t")
        if name in names:
            found[name] = owner.strip()
    return found


_GENERATED_COMPONENT_RE = re.compile(r"^(?:_[A-Za-z].*|match_\d+|eq_\d+|eq_def|proof_\d+)$")


def _generated_owner(name: str, declared: set[str]) -> str | None:
    """The declaration a generated helper such as ``foo._proof_1`` belongs to.

    Only names whose trailing components are all generated (``_proof_1``,
    ``match_2``, ``eq_1``, ...) count; the owner is the longest declared prefix.
    """

    parts = name.split(".")
    for cut in range(len(parts) - 1, 0, -1):
        if not all(_GENERATED_COMPONENT_RE.match(part) for part in parts[cut:]):
            return None
        owner = ".".join(parts[:cut])
        if owner in declared:
            return owner
    return None


def _comparator_realization_roots(
    ws: LocalWorkspace,
    settings: StripSettings,
    decls: list[dict],
    module_names: set[str],
    timeout: int,
) -> tuple[set[str], dict[str, Any] | None]:
    """The declarations that realized constants the comparator compares exactly.

    See comparator_closure.py. Only configs with ``definition_names`` get
    them (PALOMAR-2026-10-20-000013); a theorem-only config keeps the strip it
    had, and nothing runs for it. A failed query fails the run.
    """

    if not settings.definition_names:
        return set(), None
    try:
        compared, reach = comparator_closure.collect_comparator_closure(
            ws,
            entry_module=settings.entry_module,
            project_modules=module_names | {str(d["module"]) for d in decls},
            theorem_names=settings.theorem_names,
            definition_names=settings.definition_names,
            permitted_axioms=settings.permitted_axioms,
            timeout=timeout,
        )
    except RuntimeError as error:
        raise StripFailure("comparator_closure", str(error)) from error
    plan = comparator_closure.plan_realization_roots(
        compared, comparator_closure.realization_sites(reach), {str(d["name"]) for d in decls},
    )
    return plan["roots"], plan["report"]


def _list_project_lean_files(ws: LocalWorkspace) -> list[str]:
    """Project ``.lean`` files as ``/testbed/...`` paths, in byte order."""

    return sorted(
        f"/testbed/{relative}"
        for relative in iter_lean_files(ws.root, skip=ws.project_skip)
        if Path(relative).name != "lakefile.lean"
    )


def iter_lean_files(root: Path, *, skip: tuple[str, ...] = ()) -> list[str]:
    """Sorted relative ``.lean`` paths, never descending into build/VCS state.

    ``skip`` holds relative directory paths (``.lean-strip``, ``vendor/Dep``)
    that are not project sources.
    """

    skipped = {directory.strip("/") for directory in skip}
    found: list[str] = []
    for current, directories, files in os.walk(root):
        relative_dir = Path(current).relative_to(root)
        directories[:] = sorted(
            name for name in directories
            if name not in {".lake", ".git"} and (relative_dir / name).as_posix() not in skipped
        )
        for name in files:
            if name.endswith(".lean"):
                found.append((relative_dir / name).as_posix())
    return sorted(found)


# ---------------------------------------------------------------------------
# grind discovery normalization / restoration
# ---------------------------------------------------------------------------


def _global_grind_registry(
    ws: LocalWorkspace, entry_module: str, *, timeout: int, stack_kib: int, log_path: Path
) -> set[tuple[str, str, bool]]:
    if not re.fullmatch(
        r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_'.]*)*", entry_module
    ):
        raise ValueError(f"unsafe Lean entry module {entry_module!r}")
    digest = hashlib.sha256(entry_module.encode()).hexdigest()[:12]
    helper_path = f"/tmp/GrindRegistry_{digest}.lean"
    helper = f"""import {entry_module}
import Lean.Elab.Tactic.Grind.Main

open Lean Elab Command Meta

elab \"#dump_grind_registry\" : command => do
  let state := Grind.grindExt.getState (← getEnv)
  for origin in state.ematch.getOrigins do
    match origin with
    | .decl name =>
      for thm in state.ematch.find origin do
        logInfo m!\"GLOBAL_GRIND\\t{{name}}\\t{{repr thm.kind}}\\t{{thm.minIndexable}}\"
    | _ => pure ()

#dump_grind_registry
"""
    ws.write_text(helper_path, helper)
    result = ws.run_argv(
        ["lake", "env", "lean", "-s", str(stack_kib), "--json", helper_path],
        timeout=timeout,
    )
    log_path.write_text(result.stdout + ("\n" + result.stderr if result.stderr else ""))
    if result.returncode != 0:
        raise RuntimeError(f"global Grind registry export failed ({result.returncode})")
    marker = "GLOBAL_GRIND\t"
    kind_prefix = "Lean.Meta.Grind.EMatchTheoremKind."
    registry: set[tuple[str, str, bool]] = set()
    for row in _parse_json_messages(result.stdout):
        data = str(row.get("data", ""))
        if not data.startswith(marker):
            continue
        parts = data.split("\t")
        if len(parts) != 4:
            raise RuntimeError(f"malformed global Grind registry row: {data!r}")
        kind = " ".join(parts[2].removeprefix(kind_prefix).split())
        registry.add((parts[1], kind, parts[3] == "true"))
    if not registry:
        raise RuntimeError("global Grind registry export was empty")
    return registry


def _file_elaborator(
    ws: LocalWorkspace, output_dir: Path, *, timeout: int, stack_kib: int, replay_only: bool,
    progress: Callable[[str], None],
):
    counter = 0
    lock = threading.Lock()

    def elaborate(path: str, source: str, query: bool):
        nonlocal counter
        if replay_only and query:
            raise ValueError("original-call restoration only supports replay")
        with lock:
            counter += 1
            sequence = counter
        ws.write_text(path, source)
        safe = hashlib.sha256(path.encode()).hexdigest()[:12]
        mode = "query" if query else "replay"
        progress(f"elaboration {sequence}: {path.removeprefix('/testbed/')} ({mode})")
        log_path = output_dir / f"{sequence:04d}-{safe}-{mode}.jsonl"
        started = time.perf_counter()
        result = ws.run_argv(
            ["lake", "env", "lean", "-s", str(stack_kib), "-DmaxHeartbeats=0", "--json", path],
            timeout=timeout,
        )
        elapsed = round(time.perf_counter() - started, 3)
        log_path.write_text(result.stdout + ("\n" + result.stderr if result.stderr else ""))
        messages = _parse_json_messages(result.stdout)
        return {
            "passed": result.returncode == 0,
            "returncode": result.returncode,
            "seconds": elapsed,
            "messages": len(messages),
            "log": str(log_path),
        }, messages

    return elaborate


def _normalize_grind_discovery(
    ws: LocalWorkspace, settings: StripSettings, originals: dict[str, str],
    progress: Callable[[str], None],
) -> tuple[dict[str, str], dict]:
    output_dir = settings.diagnostics_dir / "grind-normalization"
    output_dir.mkdir(parents=True, exist_ok=True)
    if not any(find_discovery_calls(source) for source in originals.values()):
        def unreachable(_path: str, _source: str, _query: bool):
            raise AssertionError("zero-call normalization must not elaborate")

        normalized, report = normalize_discovery_sources(
            originals, unreachable, global_registry=set(),
            file_workers=settings.file_workers, retain_failed_files=True,
        )
        report["global_grind_registry_entries"] = 0
        report["global_grind_registry_export"] = "skipped_no_target_calls"
        return normalized, report

    progress("exporting the global grind registry")
    registry = _global_grind_registry(
        ws, settings.entry_module, timeout=settings.query_timeout,
        stack_kib=settings.stack_kib, log_path=output_dir / "global_registry.jsonl",
    )
    normalized, report = normalize_discovery_sources(
        originals,
        _file_elaborator(
            ws, output_dir, timeout=settings.query_timeout,
            stack_kib=settings.stack_kib, replay_only=False, progress=progress,
        ),
        global_registry=registry,
        file_workers=settings.file_workers,
        retain_failed_files=True,
    )
    for path, source in normalized.items():
        ws.write_text(path, source)
    report["global_grind_registry_entries"] = len(registry)
    report["logs_directory"] = str(output_dir)
    return normalized, report


def _revert_failing_grind_files(
    ws: LocalWorkspace, build_target: str, timeout: int, raw_originals: dict[str, str],
    normalized: dict[str, str], normalization: dict, output: str, stage: Any,
) -> tuple[bool, str]:
    """Undo the explicit-grind edits of files that fail only in the whole tree.

    Each file's edits were replayed alone, yet a file can still fail in the
    aggregate build (an explicit lemma Lean rejects as redundant because a
    later import already tags it `@[grind]`, PALOMAR-2026-09-14-000008). Such a
    file is put back as it was and retained whole, the policy files whose
    calls could not be normalized already get.
    """

    reverted: set[str] = set()
    ok = False
    for _round in range(_FALLBACK_ROUNDS):
        failing = {
            f"{CONTAINER_ROOT}/{match.group('path').removeprefix('./')}"
            for match in _ERROR_FILE_RE.finditer(output)
        }
        fixable = sorted(
            path for path in failing
            if path in raw_originals and normalized.get(path) != raw_originals[path]
        )
        if not fixable:
            break
        for path in fixable:
            normalized[path] = raw_originals[path]
            ws.write_text(path, raw_originals[path])
        reverted.update(fixable)
        stage.progress(f"undoing explicit grind edits in {len(fixable)} file(s)")
        ok, output = _lake_build(ws, build_target, timeout, stage.progress)
        if ok:
            break
    if reverted:
        for row in normalization.get("files", []):
            if row.get("path") in reverted:
                for call in row.get("calls", []):
                    call["persisted_after_file_decision"] = False
        normalization["retained_failed_files"] = sorted(
            set(normalization.get("retained_failed_files", [])) | reverted
        )
        normalization["aggregate_reverted_files"] = sorted(reverted)
    return ok, output


def _restore_original_grind_sources(
    ws: LocalWorkspace, settings: StripSettings, sources: dict[str, str], normalization: dict,
    progress: Callable[[str], None],
) -> tuple[dict[str, str], dict]:
    output_dir = settings.diagnostics_dir / "grind-original-restore"
    output_dir.mkdir(parents=True, exist_ok=True)
    restored, report = restore_original_discovery_sources(
        sources,
        normalization,
        _file_elaborator(
            ws, output_dir, timeout=settings.query_timeout,
            stack_kib=settings.stack_kib, replay_only=True, progress=progress,
        ),
        file_workers=settings.file_workers,
    )
    for path, source in restored.items():
        ws.write_text(path, source)
    report["logs_directory"] = str(output_dir)
    return restored, report


def _with_entry_module_path(
    module_paths: dict[str, str], entry_module: str, originals: dict[str, str],
    source_dirs: list[str] | None = None,
) -> dict[str, str]:
    entry_path = module_paths.get(entry_module) or lean_strip.resolve_module_paths(
        {entry_module}, list(originals), source_dirs
    ).get(entry_module)
    if entry_path is None:
        raise RuntimeError(f"entry module has no source mapping: {entry_module}")
    return {**module_paths, entry_module: entry_path}


# ---------------------------------------------------------------------------
# the stage sequence
# ---------------------------------------------------------------------------


def run_strip(ws: LocalWorkspace, settings: StripSettings, stage: Stage) -> StripResult:
    """Strip the isolated project in ``ws`` in place; raise on rejection."""

    timeout = settings.query_timeout
    build_target = settings.build_target
    seed = set(settings.protected)
    if not seed:
        raise StripFailure("seed", "comparator.json names no protected declarations")
    report: dict[str, Any] = {
        "preprocessing_version": preprocessing_contract.PREPROCESSING_VERSION,
        "preprocessing_algorithm": preprocessing_contract.PREPROCESSING_ALGORITHM,
        "pipeline_contract": preprocessing_contract.report_contract(),
        "grind_discovery_flags": list(DISCOVERY_FLAGS),
        "build_target": build_target,
        "seed_count": len(seed),
        "protected_declarations": sorted(seed),
    }
    timing: dict[str, float] = {}
    report["timing_sec"] = timing
    lake_race_retries.clear()
    started = time.perf_counter()

    # 1. Warm raw build of the isolated tree.
    with stage("Raw build") as _t:
        report["stale_build_outputs_removed"] = _remove_stale_build_outputs(ws)
        ok, output = _lake_build(ws, build_target, timeout, _t.progress)
        report["raw_baseline_build"] = {"passed": ok, "output_sha256": _sha256(output)}
        if not ok:
            raise StripFailure("raw_baseline_build", "lake build failed on the isolated tree", output)
    timing["raw_build"] = _t.seconds

    project_paths = _list_project_lean_files(ws)
    raw_originals = ws.snapshot(project_paths)
    originals = dict(raw_originals)

    # 2. grind +suggestions / +locals -> explicit grind [...] instrumentation.
    with stage("Grind normalization") as _t:
        normalized, normalization = _normalize_grind_discovery(
            ws, settings, raw_originals, _t.progress
        )
        report["grind_normalization"] = normalization
        if normalization.get("policy_satisfied") is not True:
            normalization["aggregate_decision"] = "rejected_unresolved_or_failed_grind"
            raise StripFailure(
                "grind_normalization",
                "grind discovery normalization did not satisfy the failed-file policy",
            )
        ok, output = _lake_build(ws, build_target, timeout, _t.progress)
        if not ok:
            ok, output = _revert_failing_grind_files(
                ws, build_target, timeout, raw_originals, normalized, normalization, output, _t,
            )
        normalization["aggregate_build_passed"] = ok
        if not ok:
            normalization["aggregate_decision"] = "rejected_explicit_tree"
            raise StripFailure("normalized_grind_build", "explicit-grind tree does not build", output)
        originals = normalized
        normalization["aggregate_decision"] = "accepted"
        _t.note(_grind_note(normalization))
    timing["grind_normalization"] = _t.seconds

    # 3. Dependency graph: .olean kernel terms + .ilean references + source text.
    with stage("Dependency graph") as _t:
        _t.progress("reading declarations and references from .olean/.ilean files")
        graph = collect_dependency_graph(
            ws, originals, modules=None, timeout=timeout,
            allow_missing_sources=True, allow_empty=True,
        )
        decls, deps, imported_namespaces = (
            graph.declarations, graph.dependencies, graph.imported_namespaces,
        )
        report["total_decls"] = len(decls)
        report["meta_decls"] = sum(1 for d in decls if d["meta"])
        report["imported_namespace_count"] = len(imported_namespaces)
        _t.note(
            f"{len(decls)} declarations, "
            f"{graph.evidence.get('total_edges', 0) if graph.evidence else 0} edges "
            f"(kernel {len(graph.edge_layers['kernel'])}, "
            f"ilean {len(graph.edge_layers['ilean'])}, "
            f"source {len(graph.edge_layers['source_text'])})"
        )
    timing["decl_graph"] = _t.seconds
    if settings.graph_only:
        report["dependency_evidence"] = graph.evidence
        payload = build_graph_artifact(
            repository=ws.root.name,
            source_image="local",
            source_image_id="local",
            declarations=[dict(row) for row in decls],
            kernel_edges=set(graph.edge_layers.get("kernel", set())),
            ilean_edges=set(graph.edge_layers.get("ilean", set())),
            source_text_edges=set(graph.edge_layers.get("source_text", set())),
            reports={"production": report},
            originals=dict(originals),
            module_paths=dict(graph.module_paths),
        )
        payload["graph_method"] = METHOD
        payload["sha256"] = graph_sha256(payload)
        write_graph_artifact(settings.diagnostics_dir / "dependency-graph.json", payload)
        timing["total"] = round(time.perf_counter() - started, 1)
        return StripResult(report, dict(originals), decls=[dict(row) for row in decls],
                           module_paths=dict(graph.module_paths), graph_only=True)
    if not decls:
        report["discarded"] = True
        report["discard"] = {
            "policy": "discard_zero_project_declarations",
            "reason": "entry_module_imports_only_dependency_code",
        }
        return StripResult(report, dict(originals), discarded=True)

    missing_seeds = seed - {d["name"] for d in decls}
    if missing_seeds:
        # A protected name the project does not declare may come from a
        # dependency (PALOMAR-2026-09-25-000001 protects definitions of its
        # vendored packages). The strip cannot touch it, so it needs no seed;
        # a name that exists nowhere still fails the gate.
        project_modules = set(graph.module_paths) | {str(d["module"]) for d in decls}
        owners = _names_in_environment(ws, settings.entry_module, missing_seeds, timeout)
        # Only a dependency's name needs no seed; a project constant without a
        # source range (a generated one) must still fail the gate.
        from_dependencies = {name for name, owner in owners.items() if owner not in project_modules}
        report["seed_from_dependencies"] = sorted(from_dependencies)
        missing_seeds -= from_dependencies
        seed -= from_dependencies
    # A generated helper (`foo._proof_1`, `foo.match_2`) has no source range;
    # a comparator config may still list it (PALOMAR-2026-10-21-000010). It
    # is part of the declaration it is named under, so seed that one.
    declared = {str(d["name"]) for d in decls}
    owners_of_generated = {name: owner for name in missing_seeds
                           if (owner := _generated_owner(name, declared)) is not None}
    if owners_of_generated:
        report["seed_generated_owners"] = dict(sorted(owners_of_generated.items()))
        missing_seeds -= set(owners_of_generated)
        seed = (seed - set(owners_of_generated)) | set(owners_of_generated.values())
    report["seed_unresolved"] = sorted(missing_seeds)
    if missing_seeds:
        raise StripFailure(
            "graph_seed_gate",
            "protected names are not project declarations: " + ", ".join(sorted(missing_seeds)),
        )

    mod_path = graph.module_paths
    unresolved = {d["module"] for d in decls} - set(mod_path)
    if len(unresolved) > len(mod_path):
        raise StripFailure(
            "module_path_resolution",
            f"module->file resolution failed ({len(mod_path)} resolved, {len(unresolved)} unresolved)",
        )
    report["dependency_evidence"] = graph.evidence
    graph_declarations = [dict(row) for row in decls]
    graph_originals = dict(originals)
    graph_module_paths = dict(mod_path)

    # 4. Roots and retention (pure planning).
    with stage("Roots and retention") as _t:
        implicit_roots = lean_strip.collect_implicit_dependency_roots(decls, originals, mod_path)
        attributed_roots = implicit_roots["attributed"]
        force_kinds = implicit_roots["implicit_kinds"]
        exact_environment_roots = attributed_roots | force_kinds
        # What redeclared dependency theorems use (see ilean.py).
        report["shadowed_owner_roots"] = sorted(
            set((graph.evidence or {}).get("ilean", {}).get("shadowed_owner_targets", []))
            & {str(d["name"]) for d in decls}
        )
        exact_environment_roots |= set(report["shadowed_owner_roots"])
        realization_roots, closure_report = _comparator_realization_roots(
            ws, settings, decls, set(graph.module_paths), timeout,
        )
        if closure_report is not None:
            report["comparator_closure"] = closure_report
        exact_environment_roots |= realization_roots
        retention = lean_strip.plan_source_retention(
            decls, originals, mod_path,
            set(normalization.get("retained_failed_files", [])),
        )
        retain_exact_files = retention["retain_exact_files"]
        retain_exact_modules = retention["retain_exact_modules"]
        retain_exact_decls = retention["retain_exact_declarations"]
        environment_files = retention["preserve_command_files"]
        command_roots = retention["environment_command_roots"]
        report["failed_grind_retained_files"] = sorted(retain_exact_files)
        report["environment_command_files"] = sorted(environment_files)
        _t.note(
            f"{len(exact_environment_roots)} environment roots "
            f"(instances/attributes/syntax), {len(command_roots)} command roots, "
            f"{len(retain_exact_files)} files retained whole"
            + (f", {len(realization_roots)} realization sites of compared constants"
               if settings.definition_names else "")
        )
    timing["roots"] = _t.seconds

    # 5. Anonymous `example` ranges from the Lean frontend.
    module_root_decls = seed | command_roots | exact_environment_roots | retain_exact_decls
    mod_path = _with_entry_module_path(mod_path, settings.entry_module, originals, graph.source_dirs)
    with stage("Example ranges") as _t:
        affected_example_paths = sorted(
            path for path, source in originals.items()
            if lean_strip.source_may_contain_anonymous_example(source)
        )
        example_module_by_path = {
            path: module for module, path in mod_path.items() if path in affected_example_paths
        }
        unmapped = set(affected_example_paths) - set(example_module_by_path)
        if unmapped:
            raise StripFailure(
                "anonymous_examples",
                "candidate files have no module mapping: " + ", ".join(sorted(unmapped)),
            )
        pre_prune_example_ranges = collect_anonymous_example_ranges(ws, affected_example_paths)
        for path, rows in pre_prune_example_ranges.items():
            for row in rows:
                row["module"] = example_module_by_path[path]
        example_count = sum(len(rows) for rows in pre_prune_example_ranges.values())
        _t.note(f"{example_count} anonymous example(s) in {len(affected_example_paths)} file(s)")
    timing["examples"] = _t.seconds

    # 6. Module prune: delete modules outside the live import closure.
    with stage("Module prune") as _t:
        pre_prune = originals
        planned, module_prune = lean_strip.plan_protected_module_prune(
            originals, decls, deps, module_root_decls, settings.entry_module,
            extra_keep_modules=retain_exact_modules,
            known_module_paths=mod_path,
        )
        module_prune["deleted_files"] = [
            path.removeprefix("/testbed/") for path in module_prune["deleted_files"]
        ]
        module_prune["rewritten_files"] = sorted(
            path.removeprefix("/testbed/")
            for path, source in planned.items()
            if originals.get(path) != source
        )
        ws.apply_source_tree(originals, planned)
        originals = planned
        remapped_decls = lean_strip.remap_decl_ranges_after_source_rewrite(
            decls, pre_prune, originals, mod_path,
        )
        pre_prune_example_rows = [
            row for rows in pre_prune_example_ranges.values() for row in rows
        ]
        remapped_example_rows = lean_strip.remap_decl_ranges_after_source_rewrite(
            pre_prune_example_rows, pre_prune, originals, mod_path,
        )
        decls = remapped_decls
        report["module_pruning"] = module_prune
        surviving_modules = {m for m, p in mod_path.items() if p in originals}
        decls = [d for d in decls if d["module"] in surviving_modules]
        surviving_names = {d["name"] for d in decls}
        if seed - surviving_names:
            raise StripFailure(
                "module_prune",
                "module pruning removed protected declarations: "
                + ", ".join(sorted(seed - surviving_names)),
            )
        deps = {
            name: set(targets) & surviving_names
            for name, targets in deps.items()
            if name in surviving_names
        }
        mod_path = {m: p for m, p in mod_path.items() if p in originals}
        command_roots &= surviving_names
        exact_environment_roots &= surviving_names
        retain_exact_decls &= surviving_names
        retain_exact_files &= set(originals)
        environment_files &= set(originals)
        _t.note(
            f"{len(module_prune['deleted_files'])} module(s) deleted, "
            f"{len(module_prune['rewritten_files'])} rewritten"
        )
    timing["module_prune"] = _t.seconds

    anonymous_example_ranges: dict[str, list[dict]] = {}
    for row in remapped_example_rows:
        path = mod_path.get(str(row["module"]))
        if path in originals:
            anonymous_example_ranges.setdefault(path, []).append(row)

    # 7. Declaration strip.
    roots = set(command_roots) | retain_exact_decls | exact_environment_roots
    module_pruned = {str(r["name"]) for r in graph_declarations} - {str(r["name"]) for r in decls}
    report["module_pruned_declarations"] = sorted(module_pruned)

    # Lean's own view of the files the strip changes (frontend.py), by path.
    syntax: dict[str, frontend.FileSyntax] = {}
    keep_sets: dict[frozenset[str], set[str]] = {}

    def keep_set(extra_roots: set[str]) -> set[str]:
        """The keep-set with ``extra_roots``, and the namespaces surviving `open`s need."""

        key = frozenset(extra_roots)
        if key not in keep_sets:
            keep = lean_strip.compute_keep_set(decls, deps, seed, roots | extra_roots)
            # Each anchor can open the way for more.
            while anchors := lean_strip.namespace_anchor_roots(
                originals, decls, keep, mod_path, set(imported_namespaces)
            ) - keep:
                extra_roots = extra_roots | anchors
                keep = lean_strip.compute_keep_set(decls, deps, seed, roots | extra_roots)
            keep_sets[key] = keep
        return set(keep_sets[key])

    def plan_strip(extra_roots: set[str]) -> tuple[set[str], dict[str, str], dict[str, Any]]:
        """The keep-set and stripped sources, keeping ``extra_roots`` as well."""

        keep = keep_set(extra_roots)
        rows = lean_strip.attach_keep(decls, keep)
        desired, strip_summary = lean_strip.plan_stripped_sources(
            originals,
            rows,
            mod_path,
            preserve_command_files=set(environment_files),
            retain_exact_files=set(retain_exact_files),
            anonymous_example_ranges=anonymous_example_ranges,
            all_project_declarations={str(row["name"]) for row in graph_declarations},
            imported_namespaces=set(imported_namespaces),
            syntax=syntax,
        )
        desired, silenced = _silence_private_only_modules(desired, originals, rows, mod_path)
        report["private_module_lint_silenced"] = silenced
        report["keep_decls"] = len(keep)
        report["kept_declarations"] = sorted(keep)
        report["strip"] = strip_summary
        report["dropped_decls"] = sorted(
            {d["name"] for d in decls if d["name"] not in keep} | module_pruned
        )
        return keep, desired, strip_summary

    # 7a. Lean's own parse, scopes and name resolution for the files the
    # strip changes; the edits below use them instead of the regex model.
    if not os.environ.get("LEAN_STRIP_NO_LEAN_SYNTAX"):
        with stage("Lean syntax") as _t:
            _keep, first_plan, first_summary = plan_strip(set())
            path_modules = {path: module for module, path in mod_path.items()}
            stubs = set(first_summary.get("stub_paths", ()))
            jobs = [
                frontend.FrontendJob(path, path_modules[path], "header" if path in stubs else "full")
                for path, content in sorted(first_plan.items())
                if originals.get(path) != content and path in path_modules
            ]
            analyses, report["lean_syntax"] = frontend.analyze_sources(
                ws, jobs, originals,
                set(graph_module_paths) | {str(row["module"]) for row in graph_declarations},
                workers=settings.file_workers,
                timeout=float(os.environ.get("LEAN_STRIP_LEAN_SYNTAX_TIMEOUT", frontend.DEFAULT_FILE_TIMEOUT)),
                progress=_t.progress,
            )
            syntax.update(analyses)
            failed = report["lean_syntax"]["failures"]
            _t.note(
                f"{len(analyses)} of {len(jobs)} changed file(s) analysed"
                + (f", {len(failed)} keep the regex edits" if failed else "")
            )
        timing["lean_syntax"] = _t.seconds

    with stage("Declaration strip") as _t:
        keep, desired, strip_summary = plan_strip(set())
        changed = 0
        for path, content in desired.items():
            if originals.get(path) != content:
                ws.write_text(path, content)
                changed += 1
        if changed != strip_summary["source_files_changed"]:
            raise StripFailure("strip_application", "pure strip plan and workspace state diverged")
        if changed == 0 and strip_summary["unresolved_drops"]:
            raise StripFailure(
                "strip_application",
                f"{strip_summary['unresolved_drops']} dropped declaration(s) have unresolved module paths",
            )
        _t.note(
            f"keep {len(keep)} / drop {len(report['dropped_decls'])} declarations; "
            f"{changed} file(s) changed"
        )
    timing["strip"] = _t.seconds

    # 8. Put the original grind calls back.
    with stage("Restore grind calls") as _t:
        surviving_paths = _list_project_lean_files(ws)
        stripped_explicit = ws.snapshot(surviving_paths)
        _, restore_report = _restore_original_grind_sources(
            ws, settings, stripped_explicit, normalization, _t.progress,
        )
        report["grind_original_restore"] = restore_report
    timing["grind_restore"] = _t.seconds

    # 9. Certify: warm build (Lake's traces rebuild everything the strip touched);
    # a clean project build only on request.
    with stage("Final warm build") as _t:
        report["stale_build_outputs_removed"] += _remove_stale_build_outputs(ws)
        ok, output = _lake_build(ws, build_target, timeout, _t.progress)
        if not ok:
            (settings.diagnostics_dir / "failed-final-build.log").write_text(output)
            # What the strip decided, to explain the failure afterwards.
            (settings.diagnostics_dir / "strip-plan.json").write_text(json.dumps({
                "seed": sorted(seed), "roots": sorted(roots),
                "kept": sorted(keep), "dropped": report.get("dropped_decls", []),
                "dependencies": {name: sorted(targets) for name, targets in deps.items() if targets},
            }, indent=1))
        if not ok and not os.environ.get("LEAN_STRIP_NO_BUILD_FALLBACK"):
            fallback = _recover_build(ws, build_target, timeout, raw_originals, output, _t)
            report["build_fallback"] = fallback
            ok, output = fallback["ok"], fallback.pop("output")
            if not ok:
                (settings.diagnostics_dir / "build-fallback.json").write_text(json.dumps(fallback, indent=1))
                unrepaired = fallback["unrepaired_errors"]
                raise StripFailure(
                    "final_warm_build",
                    f"stripped tree does not build: {len(unrepaired)} error(s) lean-strip does not repair"
                    " (a dependency the strip missed); first: " + (unrepaired[0].splitlines()[0] if unrepaired else "?"),
                    output,
                )
            if fallback["grind_restored_files"]:
                _forget_restored_drops(
                    report, fallback,
                    {str(row["name"]): str(row["module"]) for row in graph_declarations},
                    graph_module_paths,
                )
                _t.note("stripped tree did not build; " + _fallback_summary(fallback))
        report["final_build_passed"] = ok
        if not ok:
            raise StripFailure("final_warm_build", "stripped tree does not build", output)
    timing["final_warm_build"] = _t.seconds
    report["lake_race_retries"] = len(lake_race_retries)
    if settings.clean_certify:
        with stage("Final clean build") as _t:
            build_dir = ws.root / ".lake" / "build"
            if build_dir.is_symlink():
                raise StripFailure("final_clean_build", "refusing to clear a symlinked .lake/build")
            if build_dir.exists():
                shutil.rmtree(build_dir)
            ok, output = _lake_build(ws, build_target, timeout, _t.progress)
            report["final_clean_build_passed"] = ok
            if not ok:
                raise StripFailure("final_clean_build", "stripped tree does not build from clean", output)
        timing["final_clean_build"] = _t.seconds

    final_sources = ws.snapshot(_list_project_lean_files(ws))
    if normalization.get("aggregate_decision") == "accepted":
        normalization["post_strip_edit_outcomes"] = classify_edit_survival(
            normalization,
            ws.snapshot([path for path in project_paths if ws.host_path(path).is_file()]),
        )
    graph_payload = build_graph_artifact(
        repository=ws.root.name,
        source_image="local",
        source_image_id="local",
        declarations=graph_declarations,
        kernel_edges=set(graph.edge_layers.get("kernel", set())),
        ilean_edges=set(graph.edge_layers.get("ilean", set())),
        source_text_edges=set(graph.edge_layers.get("source_text", set())),
        reports={"production": report},
        originals=graph_originals,
        module_paths=graph_module_paths,
    )
    graph_payload["graph_method"] = METHOD
    graph_payload["sha256"] = graph_sha256(graph_payload)
    write_graph_artifact(settings.diagnostics_dir / "dependency-graph.json", graph_payload)
    timing["total"] = round(time.perf_counter() - started, 1)
    return StripResult(
        report, final_sources, decls=graph_declarations, module_paths=graph_module_paths,
    )


def _grind_note(normalization: dict) -> str:
    files = normalization.get("files", [])
    calls = sum(int(row.get("initial_calls", 0)) for row in files)
    if not calls:
        return "no grind +suggestions/+locals calls"
    retained = len(normalization.get("retained_failed_files", []))
    return f"{calls} discovery call(s) in {len(files)} file(s); {retained} file(s) retained whole"
