"""Build and write the declaration dependency-graph diagnostic artifact."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from .identity import DeclId, Edge, DeclarationIndex, decl_id


GRAPH_SCHEMA = "preprocessing_dependency_graph_v3"
# Every edge stores a bitmask of *every* layer that found it.
EDGE_KIND_BITS = {"source_text": 1, "kernel": 2, "ilean": 4}


def graph_sha256(payload: Mapping[str, Any]) -> str:
    """Hash the complete graph envelope, excluding only its hash field."""

    canonical_payload = dict(payload)
    canonical_payload.pop("sha256", None)
    canonical = json.dumps(
        canonical_payload, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(canonical).hexdigest()


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _name_set(value: Any) -> set[str]:
    if not isinstance(value, list):
        return set()
    names: set[str] = set()
    for item in value:
        if isinstance(item, Mapping):
            item = item.get("name")
        if isinstance(item, str) and item:
            names.add(item)
    return names


def policy_state(
    report: Mapping[str, Any],
    node_names: list[str] | list[DeclId],
    node_modules: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    """Map qualified report identities onto physical graph-node indexes.

    Legacy name-only reports apply to every matching provider. They cannot
    distinguish providers; current reports always include identity records.
    """
    identities = [
        value if isinstance(value, tuple) else ((node_modules or {}).get(value, ""), value)
        for value in node_names
    ]
    index = DeclarationIndex({"module": module, "name": name} for module, name in identities)

    def selected(container, exact_key, legacy_key):
        values = container.get(exact_key, container.get(legacy_key, []))
        return index.select(values) if isinstance(values, list) else set()

    pruning = _mapping(report.get("module_pruning"))
    live = selected(pruning, "live_declaration_identities", "live_declarations")
    dropped = selected(report, "dropped_declaration_identities", "dropped_decls")
    protected = selected(report, "protected_declaration_identities", "protected_declarations")
    if isinstance(report.get("kept_declaration_identities", report.get("kept_declarations")), list):
        kept = selected(report, "kept_declaration_identities", "kept_declarations")
    else:
        kept_modules = _name_set(pruning.get("kept_modules"))
        kept = ({identity for identity in identities if identity[0] in kept_modules}
                if kept_modules else live) - dropped
    return {
        "kept": [i for i, identity in enumerate(identities) if identity in kept],
        "removed": [i for i, identity in enumerate(identities) if identity not in kept],
        "protected": [i for i, identity in enumerate(identities) if identity in protected],
        "status_source": "preprocessing_report",
        "grind_evidence_source": "preprocessing_report",
    }


def _line_at_offset(source: str, offset: Any) -> int | None:
    if not isinstance(offset, int) or offset < 0 or offset > len(source):
        return None
    return source.count("\n", 0, offset) + 1


def _owner_at_line(
    declarations: list[Mapping[str, Any]], line: int
) -> DeclId | None:
    candidates = [
        declaration
        for declaration in declarations
        if isinstance(declaration.get("start_line"), int)
        and isinstance(declaration.get("end_line"), int)
        and int(declaration["start_line"]) <= line <= int(declaration["end_line"])
    ]
    if not candidates:
        return None
    candidates.sort(
        key=lambda declaration: (
            int(declaration["end_line"]) - int(declaration["start_line"]),
            str(declaration.get("name") or ""),
        )
    )
    return decl_id(candidates[0])


def _resolve_rule(name: str, index: DeclarationIndex) -> set[DeclId]:
    exact = index.resolve(name)
    if exact:
        return exact
    names = [candidate for candidate in index.by_name if candidate.endswith("." + name)]
    return index.resolve(names[0]) if len(names) == 1 else set()


def grind_edges(
    report: Mapping[str, Any],
    *,
    declarations: list[Mapping[str, Any]],
    originals: Mapping[str, str],
    module_paths: Mapping[str, str],
) -> tuple[list[Edge], dict[str, Any]]:
    """Recover explicit Grind-rule edges from recorded query/replay decisions."""

    by_path: dict[str, list[Mapping[str, Any]]] = {}
    for declaration in declarations:
        module = declaration.get("module")
        path = module_paths.get(str(module))
        if path:
            by_path.setdefault(path, []).append(declaration)
    index = DeclarationIndex(declarations)
    edges: set[Edge] = set()
    stats = {"calls": 0, "resolved": 0, "owner_unresolved": 0, "rule_unresolved": 0,
             "ambiguous_targets": []}
    files = _mapping(report.get("grind_normalization")).get("files")
    if not isinstance(files, list):
        return [], stats
    for file_row in files:
        if not isinstance(file_row, Mapping):
            continue
        path = str(file_row.get("path") or "")
        source = originals.get(path)
        declarations_in_file = by_path.get(path, [])
        calls = file_row.get("calls")
        if not isinstance(source, str) or not isinstance(calls, list):
            continue
        for call in calls:
            if not isinstance(call, Mapping):
                continue
            normalization = _mapping(call.get("normalization"))
            retained = normalization.get("retained_parameters")
            if not isinstance(retained, list) or not retained:
                continue
            stats["calls"] += 1
            line = _line_at_offset(source, call.get("tactic_offset"))
            owner = (
                _owner_at_line(declarations_in_file, line)
                if line is not None
                else None
            )
            if owner is None:
                stats["owner_unresolved"] += 1
                continue
            call_resolved = False
            for value in retained:
                if not isinstance(value, str) or not value:
                    continue
                targets = _resolve_rule(value, index)
                if not targets:
                    stats["rule_unresolved"] += 1
                    continue
                if len(targets) > 1:
                    stats["ambiguous_targets"].append({"source": list(owner), "name": value,
                                                       "candidates": [list(t) for t in sorted(targets)]})
                    continue
                edges.add((owner, next(iter(targets))))
                call_resolved = True
            if call_resolved:
                stats["resolved"] += 1
    return sorted(edges), stats


def build_graph_artifact(
    *,
    repository: str,
    source_image: str,
    source_image_id: str,
    declarations: list[Mapping[str, Any]],
    kernel_edges: set[Edge],
    ilean_edges: set[Edge],
    source_text_edges: set[Edge],
    reports: Mapping[str, Mapping[str, Any]],
    originals: Mapping[str, str],
    module_paths: Mapping[str, str],
    ambiguous_targets: Mapping[str, list[Mapping[str, Any]]] | None = None,
) -> dict[str, Any]:
    """Build a compact graph with multi-labelled edges and per-report status."""

    ordered = sorted(
        declarations,
        key=lambda declaration: (
            str(declaration.get("module") or ""),
            int(declaration.get("start_line") or 0),
            str(declaration.get("name") or ""),
        ),
    )
    nodes = [
        {
            "name": str(declaration.get("name") or ""),
            "module": str(declaration.get("module") or ""),
            "kind": str(declaration.get("kind") or "unknown"),
            "start_line": declaration.get("start_line"),
            "end_line": declaration.get("end_line"),
        }
        for declaration in ordered
        if declaration.get("name")
    ]
    identities = [decl_id(node) for node in nodes]
    index = DeclarationIndex(nodes)
    by_identity = {identity: i for i, identity in enumerate(identities)}
    ambiguous_edges: list[dict[str, Any]] = []

    # Each layer is recorded independently: an edge that three methods agree on
    # carries all three bits, so per-layer coverage is readable straight off the
    # artifact instead of being an artefact of evaluation order.
    masks: dict[tuple[int, int], int] = {}
    for kind, edges in (
        ("source_text", source_text_edges),
        ("kernel", kernel_edges),
        ("ilean", ilean_edges),
    ):
        bit = EDGE_KIND_BITS[kind]
        for source, target in sorted(edges, key=repr):
            sources, targets = index.resolve(source), index.resolve(target)
            if not sources or not targets:
                continue
            if len(sources) != 1 or len(targets) != 1:
                ambiguous_edges.append({
                    "source_candidates": sorted(by_identity[s] for s in sources),
                    "target_candidates": sorted(by_identity[t] for t in targets),
                    "kind_mask": bit,
                })
                continue
            pair = (by_identity[next(iter(sources))], by_identity[next(iter(targets))])
            masks[pair] = masks.get(pair, 0) | bit
        for reference in (ambiguous_targets or {}).get(kind, []):
            sources = index.resolve(reference.get("source"))
            targets = index.select(reference.get("candidates", []))
            ambiguous_edges.append({
                "source_candidates": sorted(by_identity[s] for s in sources),
                "target_candidates": sorted(by_identity[t] for t in targets),
                "kind_mask": bit,
            })
    ambiguous_masks: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
    for edge in ambiguous_edges:
        candidates = (tuple(edge["source_candidates"]), tuple(edge["target_candidates"]))
        ambiguous_masks[candidates] = ambiguous_masks.get(candidates, 0) | edge["kind_mask"]
    ambiguous_edges = [
        {"source_candidates": list(sources), "target_candidates": list(targets), "kind_mask": mask}
        for (sources, targets), mask in sorted(ambiguous_masks.items())
    ]
    typed_edges: list[list[Any]] = [
        [pair[0], pair[1], mask] for pair, mask in sorted(masks.items())
    ]

    policies: dict[str, Any] = {}
    declaration_rows = [dict(value) for value in ordered if value.get("name")]
    for policy, report in reports.items():
        state = policy_state(report, identities)
        recovered, recovery = grind_edges(
            report,
            declarations=declaration_rows,
            originals=originals,
            module_paths=module_paths,
        )
        state["grind_edges"] = [
            [by_identity[source], by_identity[target]]
            for source, target in recovered
            if source in by_identity and target in by_identity
        ]
        state["grind_recovery"] = recovery
        policies[str(policy)] = state

    payload = {
        "schema": GRAPH_SCHEMA,
        "repository": repository,
        "source_image": source_image,
        "source_image_id": source_image_id,
        "nodes": nodes,
        "edges": typed_edges,
        "ambiguous_edges": ambiguous_edges,
        "policies": policies,
        "counts": {
            "nodes": len(nodes),
            "edges": len(typed_edges),
            "ambiguous_edges": len(ambiguous_edges),
            # Coverage: how many union edges each layer found, independently.
            "source_text_edges": sum(
                edge[2] & EDGE_KIND_BITS["source_text"] != 0
                for edge in typed_edges
            ),
            "kernel_edges": sum(
                edge[2] & EDGE_KIND_BITS["kernel"] != 0 for edge in typed_edges
            ),
            "ilean_edges": sum(
                edge[2] & EDGE_KIND_BITS["ilean"] != 0 for edge in typed_edges
            ),
            # Exclusive: edges no other layer supplies - the necessity figure.
            "source_text_only_edges": sum(
                edge[2] == EDGE_KIND_BITS["source_text"] for edge in typed_edges
            ),
            "kernel_only_edges": sum(
                edge[2] == EDGE_KIND_BITS["kernel"] for edge in typed_edges
            ),
            "ilean_only_edges": sum(
                edge[2] == EDGE_KIND_BITS["ilean"] for edge in typed_edges
            ),
            "all_layers_edges": sum(edge[2] == 7 for edge in typed_edges),
        },
        "edge_kind_bits": dict(EDGE_KIND_BITS),
    }
    payload["sha256"] = graph_sha256(payload)
    return payload


def write_graph_artifact(path: Path, payload: Mapping[str, Any]) -> None:
    complete = dict(payload)
    complete["sha256"] = graph_sha256(complete)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(complete, separators=(",", ":")) + "\n")
    temporary.replace(path)
