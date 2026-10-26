"""Canonical preprocessing graph: .olean + .ilean + source-reference edges.

The strip consumes the union of all three layers; each edge also records which
layers found it. Callers own builds and source snapshots.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from lean_strip._pipeline.preprocessing import ilean as lean_ilean, strip as lean_strip
from lean_strip._pipeline.preprocessing.examples import discover_modules
from lean_strip._pipeline.preprocessing.olean import read_olean_declarations

from .identity import Dependencies, Edge

METHOD = "preprocessing_olean_ilean_source_v2"


def dependency_edges(deps: Dependencies) -> set[Edge]:
    return {
        (source, target)
        for source, targets in deps.items()
        for target in targets
    }


def combine_dependency_evidence(
    ilean_reader: Any,
    decls: list[dict],
    deps: Dependencies,
    originals: dict[str, str],
    mod_path: dict[str, str],
    *,
    modules: set[str] | None = None,
) -> tuple[Dependencies, dict, dict[str, set[Edge]]]:
    """Union every static dependency evidence layer into one graph.

    The kernel graph is authoritative for dependencies retained in elaborated
    terms. ``.ilean`` adds exact elaborator-resolved source references (for
    example field notation), and the textual scan adds source-level names that
    do not occur in either compiled artifact. Each stage is additive.
    """

    # Each layer is derived independently from an empty base so the graph can
    # record every layer that found an edge, rather than crediting whichever
    # layer happened to run first. The union is what the strip consumes.
    kernel_edges = dependency_edges(deps)
    ilean_deps, ilean_report = lean_ilean.union_ilean_reference_edges(
        ilean_reader,
        decls,
        {},
        modules=modules,
    )
    unsupported = ilean_report["unsupported_versions"]
    missing_modules = ilean_report["modules_missing"]
    if unsupported or missing_modules:
        raise RuntimeError(
            ".ilean dependency evidence is incomplete: "
            f"unsupported_versions={unsupported}, "
            f"missing_modules={missing_modules}"
        )
    ilean_edges = dependency_edges(ilean_deps)
    source_ambiguities: list[dict] = []
    source_edges = dependency_edges(
        lean_strip.augment_deps_with_source(
            decls, {}, originals, mod_path, ambiguities=source_ambiguities
        )
    )
    # Restore the report's kernel-relative meaning, which the empty base above
    # would otherwise leave measured against nothing.
    ilean_report["already_present_edges"] = len(ilean_edges & kernel_edges)
    ilean_report["added_edges"] = len(ilean_edges - kernel_edges)

    augmented: Dependencies = {}
    for source, target in kernel_edges | ilean_edges | source_edges:
        augmented.setdefault(source, set()).add(target)
    union_edges = dependency_edges(augmented)
    report = {
        "schema": "static_dependency_evidence_v3",
        "composition": "set_union",
        "attribution": "multi_label_per_edge",
        "kernel_edges": len(kernel_edges),
        "ilean": ilean_report,
        "ilean_edges": len(ilean_edges),
        "source_text_edges": len(source_edges),
        "source_text_ambiguous_targets": source_ambiguities,
        "ilean_edges_added": len(ilean_edges - kernel_edges),
        "source_text_edges_added": len(
            source_edges - kernel_edges - ilean_edges
        ),
        "total_edges": len(union_edges),
    }
    edge_layers = {
        "kernel": kernel_edges,
        "ilean": ilean_edges,
        "source_text": source_edges,
    }
    return augmented, report, edge_layers


@dataclass
class DependencyGraph:
    declarations: list[dict]
    dependencies: Dependencies
    imported_namespaces: set[str]
    originals: Mapping[str, str]
    module_paths: dict[str, str]
    evidence: dict
    edge_layers: dict[str, set[Edge]]
    source_dirs: list[str] | None = None


def project_source_dirs(env: Any) -> list[str] | None:
    """The project's own ``LEAN_SRC_PATH`` entries, in Lean's search order."""

    result = env.execute("cd /testbed && lake env printenv LEAN_SRC_PATH")
    if result["returncode"] != 0:
        return None
    lines = [line for line in result["output"].splitlines() if line.strip()]
    if not lines:
        return None
    return [
        directory.rstrip("/")
        for directory in lines[-1].strip().split(":")
        if (directory == "/testbed" or directory.startswith("/testbed/"))
        and "/.lake/" not in directory + "/"
    ] or None


def collect_dependency_graph(env: Any, originals: Mapping[str, str], *,
                             modules: list[str] | None = None,
                             timeout: int = 3600,
                             allow_missing_sources: bool = False,
                             allow_empty: bool = False) -> DependencyGraph:
    """Collect all static evidence from an already built, matching source state.

    A failed .olean query or incomplete .ilean set is an error, not an empty
    graph. Source mapping is required unless ``allow_missing_sources`` is set;
    ``modules=None`` discovers every built project module.
    """
    if modules is None:
        modules = discover_modules(env)
    if not modules and allow_empty:
        return DependencyGraph([], {}, set(), originals, {}, {},
                               {"kernel": set(), "ilean": set(), "source_text": set()})
    if not modules:
        raise RuntimeError("No project modules discovered for dependency graph")
    declarations, kernel, namespaces = read_olean_declarations(
        env, modules=modules, timeout=timeout)
    if not declarations and allow_empty:
        return DependencyGraph([], {}, namespaces, originals, {}, {},
                               {"kernel": set(), "ilean": set(), "source_text": set()})
    if not declarations:
        raise RuntimeError("Dependency graph extraction returned no declarations")
    names = {str(d["module"]) for d in declarations}
    source_dirs = project_source_dirs(env)
    paths = lean_strip.resolve_module_paths(names | set(modules), list(originals), source_dirs)
    missing = names - set(paths)
    if missing and not allow_missing_sources:
        raise RuntimeError("Source mapping missing for modules: " + ", ".join(sorted(missing)))
    dependencies, evidence, layers = combine_dependency_evidence(
        env,
        declarations, kernel, dict(originals), paths,
        modules=set(modules) | names,
    )
    return DependencyGraph(declarations, dependencies, namespaces, originals, paths, evidence, layers,
                           source_dirs)
