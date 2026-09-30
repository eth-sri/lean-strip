"""The strip stage sequence, run against a local ``LocalWorkspace``.

The stages and the planner calls follow the LeanLean benchmark's
preprocessing, in the same order and with the same arguments, so a repository
stripped here comes out byte-identical to the benchmark's version.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from lean_strip._pipeline.preprocessing import contract as preprocessing_contract
from lean_strip._pipeline.preprocessing import strip as lean_strip
from lean_strip._pipeline.preprocessing.examples import collect_anonymous_example_ranges
from lean_strip._pipeline.preprocessing.dependency_graph import (
    METHOD,
    collect_dependency_graph,
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

from .workspace import LocalWorkspace


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


@dataclass
class StripResult:
    report: dict[str, Any]
    final_sources: dict[str, str]
    decls: list[dict[str, Any]] = field(default_factory=list)
    module_paths: dict[str, str] = field(default_factory=dict)
    discarded: bool = False


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


def _lake_build(
    ws: LocalWorkspace, build_target: str, timeout: int, progress: Callable[[str], None]
) -> tuple[bool, str]:
    for attempt in range(_LAKE_RACE_RETRIES + 1):
        result = ws.execute_stream(["lake", "build", build_target], timeout=timeout, on_output=progress)
        ok, output = result["returncode"] == 0, result["output"]
        if ok or attempt == _LAKE_RACE_RETRIES:
            return ok, output
        failures = [line for line in output.splitlines() if line.startswith("error:")]
        if not failures or not all(
            _MISSING_IMPORT_OBJECT_RE.search(line)
            or line in {"error: Lean exited with code 1", "error: build failed"}
            for line in failures
        ):
            return ok, output
        lake_race_retries.append(build_target)
        progress("retrying: Lake started a module before its rebuilt import")
    return ok, output


def _list_project_lean_files(ws: LocalWorkspace) -> list[str]:
    """Project ``.lean`` files as ``/testbed/...`` paths, in byte order."""

    return sorted(
        f"/testbed/{relative}"
        for relative in iter_lean_files(ws.root)
        if Path(relative).name != "lakefile.lean"
    )


def iter_lean_files(root: Path, *, skip: tuple[str, ...] = ()) -> list[str]:
    """Sorted relative ``.lean`` paths, never descending into build/VCS state."""

    found: list[str] = []
    for current, directories, files in os.walk(root):
        relative_dir = Path(current).relative_to(root)
        at_root = relative_dir == Path(".")
        directories[:] = sorted(
            name for name in directories
            if name not in {".lake", ".git"} and not (at_root and name in skip)
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
    module_paths: dict[str, str], entry_module: str, originals: dict[str, str]
) -> dict[str, str]:
    entry_path = lean_strip.resolve_module_paths({entry_module}, list(originals)).get(entry_module)
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
    if not decls:
        report["discarded"] = True
        report["discard"] = {
            "policy": "discard_zero_project_declarations",
            "reason": "entry_module_imports_only_dependency_code",
        }
        return StripResult(report, dict(originals), discarded=True)

    missing_seeds = seed - {d["name"] for d in decls}
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
        )
    timing["roots"] = _t.seconds

    # 5. Anonymous `example` ranges from the Lean frontend.
    module_root_decls = seed | command_roots | exact_environment_roots | retain_exact_decls
    mod_path = _with_entry_module_path(mod_path, settings.entry_module, originals)
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
    with stage("Declaration strip") as _t:
        keep = lean_strip.compute_keep_set(
            decls, deps, seed, set(command_roots) | retain_exact_decls | exact_environment_roots,
        )
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
        )
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
        module_pruned = {str(r["name"]) for r in graph_declarations} - {str(r["name"]) for r in decls}
        report["keep_decls"] = len(keep)
        report["kept_declarations"] = sorted(keep)
        report["strip"] = strip_summary
        report["module_pruned_declarations"] = sorted(module_pruned)
        report["dropped_decls"] = sorted(
            {d["name"] for d in decls if d["name"] not in keep} | module_pruned
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
        ok, output = _lake_build(ws, build_target, timeout, _t.progress)
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
