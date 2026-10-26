"""Before/after metrics and the human-readable summary for ``lean-strip``."""

from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Any

from lean_strip._pipeline.metrics.source_archive import count_lean_words_in_source
from lean_strip._pipeline.metrics.tokens import count_lean_tokens_in_source, remove_lean_comments

from ._pipeline.preprocessing.identity import DeclId, DeclarationIndex, decl_id, identity_rows
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
    dropped: list[DeclId], kept: set[DeclId], by_identity: dict[DeclId, dict[str, Any]]
) -> set[DeclId]:
    """Dropped names whose source range lies inside a kept declaration.

    These are compiler-generated companions (``.elim``, ``noConfusion``, ...)
    of declarations that stay, so no source text goes away with them.
    """

    kept_spans: dict[str, list[tuple[tuple[int, int], tuple[int, int]]]] = {}
    for name in kept:
        row = by_identity.get(name)
        span = _span(row) if row else None
        if span:
            kept_spans.setdefault(str(row["module"]), []).append(span)
    helpers = set()
    for name in dropped:
        row = by_identity.get(name)
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

    by_identity = {decl_id(row): row for row in result.decls}
    index = DeclarationIndex(result.decls)
    path_of = {module: path.removeprefix("/testbed/") for module, path in result.module_paths.items()}
    all_dropped = sorted(index.select(report.get(
        "dropped_declaration_identities", report.get("dropped_decls", [])
    )))
    kept = index.select(report.get("kept_declaration_identities", report.get("kept_declarations", [])))
    helpers = _generated_helpers(all_dropped, kept, by_identity)
    dropped = [name for name in all_dropped if name not in helpers]
    module_pruned = index.select(report.get(
        "module_pruned_declaration_identities", report.get("module_pruned_declarations", [])
    ))
    kinds = Counter(str(by_identity.get(name, {}).get("kind", "?")) for name in dropped)
    per_file: Counter[str] = Counter(
        path_of.get(str(by_identity.get(name, {}).get("module")), "?") for name in dropped
    )
    def display(identity: DeclId) -> str:
        module, name = identity
        return f"{module}:{name}" if len(index.by_name[name]) > 1 else name

    grind = report.get("grind_normalization", {})
    grind_files = grind.get("files", [])

    return {
        "repository": str(repo),
        "dry_run": dry_run,
        "scope": "all .lean files except lakefile.lean and the challenge (which is never modified)",
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
            "protected_identities": report.get("protected_declaration_identities", []),
            "dropped_by_kind": dict(kinds.most_common()),
            "dropped_by_file": dict(per_file.most_common()),
            "dropped_names": [display(identity) for identity in dropped],
            "dropped_identities": identity_rows(dropped),
            "dropped_generated_helpers": [display(identity) for identity in sorted(helpers)],
        },
        "grind": {
            "discovery_calls": sum(int(row.get("initial_calls", 0)) for row in grind_files),
            "files_with_calls": len(grind_files),
            "files_retained_whole": grind.get("retained_failed_files", []),
        },
        "build_fallback": report.get("build_fallback"),
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
    fallback = outcome.get("build_fallback")
    if fallback:
        lines.extend(fallback_lines(fallback))
    lines.extend(lakefile_warnings(outcome.get("lakefile") or {}))
    verdict = outcome.get("comparator")
    if verdict and verdict.get("status") == "accepted":
        lines.append(f"comparator: {verdict.get('judge')} accepts the stripped solution"
                     + ("" if verdict.get("sandbox") else " (judged without a sandbox; lean-strip built the same code itself)"))
    elif verdict and verdict.get("status") == "unavailable":
        lines.append(f"warning: comparator could not run: {verdict['reason']}")
    return "\n".join(lines)


def fallback_lines(fallback: dict[str, Any]) -> list[str]:
    """The summary's account of what the build fallback changed."""

    def shown(paths: list[str]) -> str:
        return ", ".join(path.removeprefix("/testbed/") for path in paths)

    rounds = fallback.get("rounds", 1)
    lines = [f"warning: the stripped tree did not build; lean-strip repaired it in "
             f"{rounds} rebuild{'s' if rounds != 1 else ''}:"]
    for raised in fallback.get("heartbeats") or []:
        lines.append(f"  - `set_option {raised['option']} {raised['value']} in` before "
                     f"{raised['declaration'][:70]} ({raised['path'].removeprefix('/testbed/')}): "
                     "it elaborates more slowly in the stripped tree")
    silenced = fallback.get("private_module_lint_silenced") or []
    if silenced:
        lines.append(f"  - `set_option linter.privateModule false` in {shown(silenced[:4])}")
    if fallback.get("grind_restored_files"):
        lines.append(f"  - restored {len(fallback['grind_restored_files'])} file(s) unstripped where grind failed: "
                     + shown(fallback["grind_restored_files"][:6]))
    lines.append("  First errors:")
    lines.extend("    " + line[:200] for line in fallback.get("errors", [])[:4])
    return lines


def lakefile_warnings(lake: dict[str, Any]) -> list[str]:
    """Warnings about the lakefile edit and plain `lake build`, for the summary."""

    lines: list[str] = []
    if lake.get("rewritten"):
        lines.append(f"warning: {lake['path']} was edited because the strip deleted modules it names:")
        lines.extend(f"  - {change}" for change in lake.get("changes", []))
    if lake.get("unresolved"):
        lines.append(f"warning: {lake.get('path')} may still name deleted modules; check by hand:")
        lines.extend(f"  - {problem}" for problem in lake["unresolved"])
    build = lake.get("lake_build") or {}
    if build and not build.get("ok"):
        lines.append("warning: plain `lake build` fails on the stripped tree "
                     "(the solution and challenge were checked and build); last lines:")
        lines.extend("    " + line for line in build.get("output_tail", "").splitlines()[-10:])
    return lines
