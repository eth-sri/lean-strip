"""Elaborator-resolved dependency edges from Lean ``.ilean`` metadata.

Kernel terms in ``.olean`` files intentionally omit some names that were used
only during elaboration (field notation, named tactic arguments, overloaded
syntax, and similar source-level references).  ``.ilean`` files retain those
resolved references.  This module parses them and *unions* exact
owner-declaration -> referenced-declaration edges into an existing dependency
graph; it never removes or replaces another evidence source.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import json
from typing import Any, Iterable, Mapping

from lean_strip._pipeline.preprocessing.olean import DeclRange
from lean_strip._pipeline.preprocessing.strip import module_to_relpath


SUPPORTED_ILEAN_VERSIONS = frozenset({3, 4, 5})


def _pos(line: int, column: int) -> tuple[int, int]:
    return line, column


def _contains(decl: DeclRange, usage: list[Any]) -> bool:
    if len(usage) < 4 or any(not isinstance(value, int) for value in usage[:4]):
        return False
    values = (
        decl.get("start_line"),
        decl.get("start_col"),
        decl.get("end_line"),
        decl.get("end_col"),
    )
    if any(value is None for value in values):
        return False
    start = _pos(int(values[0]), int(values[1]))
    end = _pos(int(values[2]), int(values[3]))
    usage_start = _pos(usage[0], usage[1])
    usage_end = _pos(usage[2], usage[3])
    return start <= usage_start and usage_end <= end


def _span_key(decl: DeclRange) -> tuple[int, int, int]:
    """Order containing ranges from narrowest to broadest."""
    start_line = int(decl["start_line"])
    start_col = int(decl["start_col"])
    end_line = int(decl["end_line"])
    end_col = int(decl["end_col"])
    return end_line - start_line, end_col - start_col, start_line


def _resolve_in_module(
    raw_name: str,
    module: str,
    names: set[str],
    names_by_module: Mapping[str, set[str]],
) -> set[str]:
    if raw_name in names:
        return {raw_name}
    qualified = f"{module}.{raw_name}" if module else raw_name
    if qualified in names:
        return {qualified}
    last = raw_name.rsplit(".", 1)[-1]
    candidates = {
        name
        for name in names_by_module.get(module, set())
        if name == raw_name
        or name.endswith("." + raw_name)
        or name.rsplit(".", 1)[-1] == last
    }
    return candidates


def _positional_owners(
    source_module: str,
    usage: list[Any],
    decls_by_module: Mapping[str, list[DeclRange]],
) -> set[str]:
    candidates = [
        decl
        for decl in decls_by_module.get(source_module, [])
        if _contains(decl, usage)
    ]
    if not candidates:
        return set()
    narrowest = min(_span_key(decl) for decl in candidates)
    return {
        str(decl["name"])
        for decl in candidates
        if _span_key(decl) == narrowest
    }


def union_ilean_documents(
    documents: Iterable[tuple[str, Mapping[str, Any]]],
    decls: list[DeclRange],
    deps: Mapping[str, set[str]],
    *,
    modules: Iterable[str] | None = None,
) -> tuple[dict[str, set[str]], dict[str, Any]]:
    """Union project-local semantic reference edges from parsed ``.ilean`` JSON.

    Version 5 usage records carry their enclosing declaration name directly.
    Version 3 records do not, so the owner is recovered from the already
    available Lean declaration ranges. If several constants share the same
    narrowest source range, the edge is added to the full tied owner set.
    """

    names = {str(decl["name"]) for decl in decls}
    requested_modules = set(modules or (str(decl["module"]) for decl in decls))
    names_by_module: dict[str, set[str]] = defaultdict(set)
    decls_by_module: dict[str, list[DeclRange]] = defaultdict(list)
    for decl in decls:
        module = str(decl["module"])
        names_by_module[module].add(str(decl["name"]))
        if decl.get("start_line") is not None:
            decls_by_module[module].append(decl)

    out = {name: set(targets) for name, targets in deps.items()}
    original_edges = {
        (source, target)
        for source, targets in out.items()
        for target in targets
    }
    candidate_edges: set[tuple[str, str]] = set()
    versions: Counter[int] = Counter()
    seen_modules: set[str] = set()
    unsupported_versions: set[int] = set()
    project_target_unresolved: set[str] = set()
    owner_unresolved: set[str] = set()
    # A reference can resolve to an exact project declaration even when its
    # enclosing command has no declaration node of its own. Report such exact
    # targets as roots unless the owner is Lean's generated `_example`: those
    # non-persistent validation commands are removed using Lean frontend
    # ranges (examples.py) instead of rooting everything they mention.
    owner_unresolved_targets: set[str] = set()
    anonymous_example_modules: set[str] = set()
    anonymous_example_targets: set[str] = set()
    anonymous_example_targets_by_module: dict[str, set[str]] = defaultdict(set)
    documents_seen = 0
    references_seen = 0
    constant_references = 0
    usage_records = 0
    named_owner_usages = 0
    positional_owner_usages = 0
    ambiguous_target_usages = 0
    ambiguous_owner_usages = 0
    owner_mismatch_usages = 0
    owner_mismatches: set[str] = set()
    malformed_usage_records = 0

    for path, document in documents:
        module = document.get("module")
        if not isinstance(module, str) or module not in requested_modules:
            continue
        documents_seen += 1
        seen_modules.add(module)
        version = document.get("version")
        if not isinstance(version, int):
            unsupported_versions.add(-1)
            continue
        versions[version] += 1
        if version not in SUPPORTED_ILEAN_VERSIONS:
            unsupported_versions.add(version)
            continue
        references = document.get("references", {})
        if not isinstance(references, dict):
            raise ValueError(f"{path}: .ilean references is not an object")
        references_seen += len(references)
        for encoded_reference, value in references.items():
            try:
                reference = json.loads(encoded_reference)
            except (TypeError, json.JSONDecodeError):
                continue
            constant = reference.get("c") if isinstance(reference, dict) else None
            if not isinstance(constant, dict):
                continue
            target_name = constant.get("n")
            target_module = constant.get("m")
            if not isinstance(target_name, str) or not isinstance(target_module, str):
                continue
            constant_references += 1
            targets = _resolve_in_module(
                target_name, target_module, names, names_by_module
            )
            target_is_project_local = target_module in requested_modules
            if not targets:
                if target_is_project_local:
                    project_target_unresolved.add(f"{target_module}:{target_name}")
                continue
            if len(targets) > 1:
                ambiguous_target_usages += 1
            usages = value.get("usages", []) if isinstance(value, dict) else []
            if not isinstance(usages, list):
                raise ValueError(f"{path}: usages for {target_name} is not an array")
            for usage in usages:
                usage_records += 1
                if not isinstance(usage, list) or len(usage) < 4:
                    malformed_usage_records += 1
                    continue
                named_owners: set[str] = set()
                raw_named_owner: str | None = None
                if len(usage) >= 5 and isinstance(usage[4], str):
                    raw_named_owner = usage[4]
                    named_owners = _resolve_in_module(
                        raw_named_owner, module, names, names_by_module
                    )
                    if named_owners:
                        named_owner_usages += 1
                positional_owners = _positional_owners(
                    module, usage, decls_by_module
                )
                if named_owners and positional_owners and (
                    named_owners != positional_owners
                ):
                    # Version-5 owner metadata and source ranges can disagree
                    # after generated declarations or tooling changes.  An
                    # edge assigned to the wrong owner can make a live target
                    # appear dead, so retain the target from both candidates.
                    owner_mismatch_usages += 1
                    owner_mismatches.add(
                        f"{module}:{usage[0]}:{usage[1]}:{target_name}:"
                        f"named={','.join(sorted(named_owners))}:"
                        f"positional={','.join(sorted(positional_owners))}"
                    )
                owners = named_owners | positional_owners
                if not named_owners and positional_owners:
                    positional_owner_usages += 1
                if not owners:
                    owner_unresolved.add(
                        f"{module}:{usage[0]}:{usage[1]}:{target_name}"
                    )
                    if raw_named_owner is not None and (
                        raw_named_owner == "_example"
                        or raw_named_owner.endswith("._example")
                    ):
                        # Anonymous examples are non-persistent validation
                        # commands. Record their source modules so the Lean
                        # frontend can remove the complete command instead
                        # of conservatively rooting every declaration it uses.
                        anonymous_example_modules.add(module)
                        anonymous_example_targets.update(targets)
                        anonymous_example_targets_by_module[module].update(targets)
                    else:
                        owner_unresolved_targets.update(targets)
                    continue
                if len(owners) > 1:
                    ambiguous_owner_usages += 1
                for owner in owners:
                    for target in targets:
                        if owner != target:
                            candidate_edges.add((owner, target))

    for source, target in candidate_edges:
        out.setdefault(source, set()).add(target)

    added_edges = candidate_edges - original_edges
    report = {
        "schema": "lean_ilean_reference_edges_v1",
        "supported_versions": sorted(SUPPORTED_ILEAN_VERSIONS),
        "schema_versions": {
            str(version): count for version, count in sorted(versions.items())
        },
        "unsupported_versions": sorted(unsupported_versions),
        "documents": documents_seen,
        "modules_requested": len(requested_modules),
        "modules_seen": len(seen_modules),
        "modules_missing": sorted(requested_modules - seen_modules),
        "references": references_seen,
        "constant_references": constant_references,
        "usage_records": usage_records,
        "named_owner_usages": named_owner_usages,
        "positional_owner_usages": positional_owner_usages,
        "ambiguous_target_usages": ambiguous_target_usages,
        "ambiguous_owner_usages": ambiguous_owner_usages,
        "owner_mismatch_usages": owner_mismatch_usages,
        "owner_mismatches": sorted(owner_mismatches),
        "malformed_usage_records": malformed_usage_records,
        "project_target_unresolved": sorted(project_target_unresolved),
        "owner_unresolved": sorted(owner_unresolved),
        "owner_unresolved_targets": sorted(owner_unresolved_targets),
        "owner_unresolved_target_count": len(owner_unresolved_targets),
        "anonymous_example_modules": sorted(anonymous_example_modules),
        "anonymous_example_module_count": len(anonymous_example_modules),
        "anonymous_example_targets": sorted(anonymous_example_targets),
        "anonymous_example_target_count": len(anonymous_example_targets),
        "anonymous_example_targets_by_module": {
            module: sorted(targets)
            for module, targets in sorted(
                anonymous_example_targets_by_module.items()
            )
        },
        "candidate_edges": len(candidate_edges),
        "already_present_edges": len(candidate_edges & original_edges),
        "added_edges": len(added_edges),
    }
    return out, report


def module_to_ilean_relpath(module: str) -> str:
    """Map Lean module syntax to its build-artifact path."""

    source_path = module_to_relpath(module)
    return source_path.removesuffix(".lean") + ".ilean"


def union_ilean_reference_edges(
    reader: Any,
    decls: list[DeclRange],
    deps: Mapping[str, set[str]],
    *,
    modules: Iterable[str] | None = None,
) -> tuple[dict[str, set[str]], dict[str, Any]]:
    """Collect and union ``.ilean`` edges for one already-built project.

    ``reader.iter_ilean_documents(modules)`` yields ``(path, document)`` pairs
    for the built ``.ilean`` files.
    """

    documents = reader.iter_ilean_documents(modules)
    return union_ilean_documents(documents, decls, deps, modules=modules)
