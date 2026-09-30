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

METHOD = "preprocessing_olean_ilean_source_v1"


def dependency_edges(deps: dict[str, set[str]]) -> set[tuple[str, str]]:
    return {
        (source, target)
        for source, targets in deps.items()
        for target in targets
    }


def combine_dependency_evidence(
    ilean_reader: Any,
    decls: list[dict],
    deps: dict[str, set[str]],
    originals: dict[str, str],
    mod_path: dict[str, str],
    *,
    modules: set[str] | None = None,
) -> tuple[dict[str, set[str]], dict, dict[str, set[tuple[str, str]]]]:
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
    source_edges = dependency_edges(
        lean_strip.augment_deps_with_source(decls, {}, originals, mod_path)
    )
    # Restore the report's kernel-relative meaning, which the empty base above
    # would otherwise leave measured against nothing.
    ilean_report["already_present_edges"] = len(ilean_edges & kernel_edges)
    ilean_report["added_edges"] = len(ilean_edges - kernel_edges)

    augmented: dict[str, set[str]] = {}
    for source, target in kernel_edges | ilean_edges | source_edges:
        augmented.setdefault(source, set()).add(target)
    union_edges = dependency_edges(augmented)
    report = {
        "schema": "static_dependency_evidence_v2",
        "composition": "set_union",
        "attribution": "multi_label_per_edge",
        "kernel_edges": len(kernel_edges),
        "ilean": ilean_report,
        "ilean_edges": len(ilean_edges),
        "source_text_edges": len(source_edges),
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
    dependencies: dict[str, set[str]]
    imported_namespaces: set[str]
    originals: Mapping[str, str]
    module_paths: dict[str, str]
    evidence: dict
    edge_layers: dict[str, set[tuple[str, str]]]


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
    paths = lean_strip.resolve_module_paths(names | set(modules), list(originals))
    missing = names - set(paths)
    if missing and not allow_missing_sources:
        raise RuntimeError("Source mapping missing for modules: " + ", ".join(sorted(missing)))
    dependencies, evidence, layers = combine_dependency_evidence(
        env,
        declarations, kernel, dict(originals), paths,
        modules=set(modules) | names,
    )
    return DependencyGraph(declarations, dependencies, namespaces, originals, paths, evidence, layers)
