"""Before/after metrics and the human-readable summary for ``lean-strip``."""

from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Any

from lean_strip._pipeline.metrics.source_archive import count_lean_words_in_source
from lean_strip._pipeline.metrics.tokens import count_lean_tokens_in_source, remove_lean_comments

from .engine import StripResult, iter_lean_files

METRICS = ("lines", "code_lines", "tokens", "words")


def measure_source(source: str) -> dict[str, int]:
    return {
        "lines": len(source.splitlines()),
        "code_lines": sum(1 for line in remove_lean_comments(source).splitlines() if line.strip()),
        "tokens": count_lean_tokens_in_source(source),
        "words": count_lean_words_in_source(source),
    }


def measure_tree(
    root: Path,
    *,
    skip: tuple[str, ...] = (),
    exclude: set[str] | None = None,
    only: set[str] | None = None,
) -> dict[str, Any]:
    """Per-file and total metrics over a tree's ``.lean`` sources.

    ``lakefile.lean`` is Lake configuration, not project code, and is never
    counted.
    """

    files = {}
    for relative in iter_lean_files(root, skip=skip):
        if Path(relative).name == "lakefile.lean":
            continue
        if exclude and relative in exclude or only is not None and relative not in only:
            continue
        files[relative] = measure_source((root / relative).read_bytes().decode("utf-8", "replace"))
    totals = {key: sum(row[key] for row in files.values()) for key in METRICS}
    totals["files"] = len(files)
    return {"files": files, "totals": totals}


def _saved(before: dict[str, int], after: dict[str, int]) -> dict[str, Any]:
    return {
        key: {
            "before": before[key],
            "after": after[key],
            "saved": before[key] - after[key],
            "reduction": round(1 - after[key] / before[key], 4) if before[key] else 0.0,
        }
        for key in (*METRICS, "files")
    }


def _span(row: dict[str, Any]) -> tuple[tuple[int, int], tuple[int, int]] | None:
    if row.get("start_line") is None or row.get("end_line") is None:
        return None
    return (
        (int(row["start_line"]), int(row.get("start_col") or 0)),
        (int(row["end_line"]), int(row.get("end_col") or 0)),
    )


def _generated_helpers(
    dropped: list[str], kept: set[str], by_name: dict[str, dict[str, Any]]
) -> set[str]:
    """Dropped names whose source range lies inside a kept declaration.

    These are compiler-generated companions (``.elim``, ``noConfusion``, ...)
    of declarations that stay, so no source text goes away with them.
    """

    kept_spans: dict[str, list[tuple[tuple[int, int], tuple[int, int]]]] = {}
    for name in kept:
        row = by_name.get(name)
        span = _span(row) if row else None
        if span:
            kept_spans.setdefault(str(row["module"]), []).append(span)
    helpers = set()
    for name in dropped:
        row = by_name.get(name)
        span = _span(row) if row else None
        if span and any(
            start <= span[0] and span[1] <= end
            for start, end in kept_spans.get(str(row["module"]), [])
        ):
            helpers.add(name)
    return helpers


def summarize(
    *,
    repo: Path,
    before: dict[str, Any],
    isolated: list[str],
    after: dict[str, Any],
    challenge: dict[str, Any],
    isolation: dict[str, Any],
    result: StripResult,
    applied: dict[str, list[str]],
    dry_run: bool,
) -> dict[str, Any]:
    report = result.report
    isolated_set = set(isolated)
    isolation_deleted = sorted(set(before["files"]) - isolated_set)
    isolated_totals = {
        key: sum(row[key] for path, row in before["files"].items() if path in isolated_set)
        for key in METRICS
    }
    isolated_totals["files"] = sum(1 for path in before["files"] if path in isolated_set)

    by_name = {str(row["name"]): row for row in result.decls}
    path_of = {module: path.removeprefix("/testbed/") for module, path in result.module_paths.items()}
    all_dropped = [str(name) for name in report.get("dropped_decls", [])]
    helpers = _generated_helpers(all_dropped, set(report.get("kept_declarations", [])), by_name)
    dropped = [name for name in all_dropped if name not in helpers]
    module_pruned = set(report.get("module_pruned_declarations", []))
    kinds = Counter(str(by_name.get(name, {}).get("kind", "?")) for name in dropped)
    per_file: Counter[str] = Counter(
        path_of.get(str(by_name.get(name, {}).get("module")), "?") for name in dropped
    )
    grind = report.get("grind_normalization", {})
    grind_files = grind.get("files", [])

    return {
        "repository": str(repo),
        "dry_run": dry_run,
        "scope": "all .lean files except lakefile.lean, the challenge (which is never modified) and lakefile root stubs",
        "totals": _saved(before["totals"], after["totals"]),
        "phases": {
            "isolation": _saved(before["totals"], isolated_totals),
            "stripping": _saved(isolated_totals, after["totals"]),
        },
        "challenge": challenge["totals"],
        "files": {
            "deleted_by_isolation": isolation_deleted,
            "deleted_by_module_prune": report.get("module_pruning", {}).get("deleted_files", []),
            "rewritten": applied.get("changed", []),
            "deleted": applied.get("deleted", []),
        },
        "declarations": {
            "total": report.get("total_decls", 0),
            "kept": report.get("keep_decls", 0),
            "dropped": len(dropped),
            "dropped_with_deleted_modules": len(module_pruned),
            "protected": report.get("protected_declarations", []),
            "dropped_by_kind": dict(kinds.most_common()),
            "dropped_by_file": dict(per_file.most_common()),
            "dropped_names": dropped,
            "dropped_generated_helpers": sorted(helpers),
        },
        "grind": {
            "discovery_calls": sum(int(row.get("initial_calls", 0)) for row in grind_files),
            "files_with_calls": len(grind_files),
            "files_retained_whole": grind.get("retained_failed_files", []),
        },
        "strip_summary": report.get("strip", {}),
        "timing_sec": report.get("timing_sec", {}),
        "isolation": {
            key: isolation.get(key)
            for key in ("retained_local_sources", "removed_paths", "lake_metadata")
        },
    }


def _pct(row: dict[str, Any]) -> str:
    return f"{100 * row['reduction']:5.1f}%"


def render_summary(outcome: dict[str, Any]) -> str:
    if outcome.get("status") == "discarded":
        return "No project declarations: the solution only re-exports dependency code; nothing to strip."
    totals = outcome["totals"]
    phases = outcome["phases"]
    lines = [
        "Summary" + (" (dry run: repository unchanged)" if outcome["dry_run"] else ""),
        f"  {'':<12}{'before':>10}{'after':>10}{'saved':>10}{'':>8}"
        f"   {'isolation':>10}{'stripping':>10}",
    ]
    labels = {"files": "Lean files", "lines": "lines", "code_lines": "code lines",
              "tokens": "Lean tokens", "words": "words"}
    for key in ("files", "lines", "code_lines", "tokens", "words"):
        row = totals[key]
        lines.append(
            f"  {labels[key]:<12}{row['before']:>10,}{row['after']:>10,}{row['saved']:>10,}"
            f"{_pct(row):>8}   {phases['isolation'][key]['saved']:>10,}"
            f"{phases['stripping'][key]['saved']:>10,}"
        )
    lines.append("  (tokens and words exclude comments and imports; the challenge file is excluded)")

    declarations = outcome["declarations"]
    lines.append("")
    lines.append(
        f"Declarations: kept {declarations['kept']:,} of {declarations['total']:,}, "
        f"dropped {declarations['dropped']:,}"
        + (f" ({declarations['dropped_with_deleted_modules']} inside deleted modules)"
           if declarations["dropped_with_deleted_modules"] else "")
        + (f", plus {len(declarations['dropped_generated_helpers']):,} unused generated "
           "helper(s) of kept declarations"
           if declarations["dropped_generated_helpers"] else "")
    )
    if declarations["dropped_by_kind"]:
        lines.append("  by kind: " + ", ".join(
            f"{count} {kind}" for kind, count in declarations["dropped_by_kind"].items()
        ))
    top = list(declarations["dropped_by_file"].items())[:8]
    for path, count in top:
        lines.append(f"  {count:>5}  {path}")
    if len(declarations["dropped_by_file"]) > len(top):
        lines.append(f"  ... {len(declarations['dropped_by_file']) - len(top)} more file(s)")

    files = outcome["files"]
    lines.append("")
    lines.append(
        f"Files: {len(files['deleted_by_isolation'])} deleted by isolation (outside the "
        f"solution/challenge import closure), {len(files['deleted_by_module_prune'])} by "
        f"module pruning, {len(files['rewritten'])} rewritten"
    )
    for path in (files["deleted_by_isolation"] + files["deleted_by_module_prune"])[:12]:
        lines.append(f"  - {path}")
    grind = outcome["grind"]
    if grind["discovery_calls"]:
        lines.append(
            f"grind: {grind['discovery_calls']} `grind +suggestions/+locals` call(s) in "
            f"{grind['files_with_calls']} file(s) resolved for dependency tracking and restored "
            f"verbatim; {len(grind['files_retained_whole'])} file(s) kept whole"
        )
    non_lean = files.get("deleted_non_lean") or []
    if non_lean:
        lines.append(f"--retain-lean-only: {len(non_lean)} other file(s) deleted")
        for path in non_lean[:12]:
            lines.append(f"  - {path}")
        if len(non_lean) > 12:
            lines.append(f"  ... {len(non_lean) - 12} more")
    stubs = outcome.get("lake_root_stubs") or []
    if stubs:
        lines.append(
            "lakefile roots: " + ", ".join(stubs) + " kept as import-only stub(s) of the "
            "surviving modules, so plain `lake build` still works"
        )
    return "\n".join(lines)
