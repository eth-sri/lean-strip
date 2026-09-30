"""Repository-neutral, fail-closed normalization of Grind discovery flags.

The runtime-facing code supplies a callback that elaborates one source file.
This module owns the deterministic state machine:

* discover executable ``grind +suggestions`` / ``grind +locals`` calls;
* query one call at a time with ``grind?``;
* translate Lean's ``grind only [...]`` recommendation to ordinary
  ``grind [...]`` while preserving the ambient global Grind registry;
* accept the edit only after the edited file elaborates; and
* leave unresolved or failing calls byte-identical.

engine.py supplies the elaboration callback and does all build and filesystem
I/O; this module holds only the decision logic.
"""

from __future__ import annotations

import hashlib
import re
from collections import Counter, defaultdict
from collections.abc import Callable, Iterable, Mapping
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Any

from lean_strip._pipeline.preprocessing.grind_discovery import (
    DISCOVERY_FLAGS,
    find_discovery_calls,
)
from lean_strip._pipeline.preprocessing.query_replay import (
    QuerySite,
    disable_scoped_heartbeats,
    merge_suggestions,
    message_span,
    only_parts,
)

_APPLY_RE = re.compile(r"(?m)^[ \t]*\[apply\][ \t]+")
_ANCHOR_RE = re.compile(r"^#[0-9a-fA-F]+$")


def _is_entrypoint_only_tactic(candidate: str) -> bool:
    """Recognize ``grind ... only`` but reject ``grind => ... only``."""

    flat = " ".join(candidate.split())
    if not flat.startswith("grind"):
        return False
    only = re.search(r"\bonly\b", flat)
    if only is None:
        return False
    arrow = flat.find("=>")
    return arrow < 0 or only.start() < arrow


def extract_anchor_free_only_suggestions(data: str) -> list[str]:
    markers = list(_APPLY_RE.finditer(data))
    candidates: list[str] = []
    if markers:
        for index, marker in enumerate(markers):
            end = markers[index + 1].start() if index + 1 < len(markers) else len(data)
            cleaned = data[marker.end() : end].strip()
            if _is_entrypoint_only_tactic(cleaned):
                candidates.append(cleaned)
    else:
        match = re.search(r"Try (?:this|these):[ \t]*(.*)", data, re.S)
        if match:
            cleaned = match.group(1).strip()
            if _is_entrypoint_only_tactic(cleaned):
                candidates.append(cleaned)

    def has_anchor(candidate: str) -> bool:
        parts = only_parts(candidate)
        if parts is None:
            return True
        return any(_ANCHOR_RE.match(item.strip()) for item in parts[1])

    anchor_free = [candidate for candidate in candidates if not has_anchor(candidate)]
    return anchor_free or candidates


def instrument_discovery_call(
    source: str,
    call_index: int,
) -> tuple[str, list[QuerySite], dict[str, object]]:
    """Query one remaining discovery call selected by its source-order index."""

    calls = find_discovery_calls(source)
    if not 0 <= call_index < len(calls):
        raise IndexError(
            f"discovery call index {call_index} is outside 0..{len(calls) - 1}"
        )
    call = calls[call_index]
    instrumented = source[: call.tactic_end] + "?" + source[call.tactic_end :]
    site = QuerySite(
        tactic="grind",
        token_start=call.tactic_start,
        token_end=call.tactic_end,
        question_offset=call.tactic_end,
    )
    return instrumented, [site], {
        "remaining_calls_before": len(calls),
        "selected_call_index": call_index,
        "flag": call.flag,
        "tactic_offset": call.tactic_start,
    }


GlobalGrindRegistry = set[tuple[str, str, bool]]


_MODIFIER_KINDS = (
    ("_=_ gen ", "eqBoth true"),
    ("=_ gen ", "eqRhs true"),
    ("← gen ", "bwd true"),
    (". gen ", "default true"),
    ("=_ ", "eqRhs false"),
    ("_=_ ", "eqBoth false"),
    ("←= ", "eqBwd"),
    ("=> ", "leftRight"),
    ("<= ", "rightLeft"),
    ("= ", "eqLhs false"),
    ("→ ", "fwd"),
    ("← ", "bwd false"),
    (". ", "default false"),
)


def _parameter_registry_key(parameter: str) -> tuple[str, str, bool] | None:
    value = parameter.strip()
    min_indexable = value.startswith("!")
    if min_indexable:
        value = value[1:].lstrip()
    if value.startswith("usr "):
        return value[4:].strip(), "user", min_indexable
    for prefix, kind in _MODIFIER_KINDS:
        if value.startswith(prefix):
            return value[len(prefix) :].strip(), kind, min_indexable
    if " " in value or not value:
        return None
    return value, "default false", min_indexable


def _is_globally_redundant(
    parameter: str,
    registry: GlobalGrindRegistry,
) -> bool:
    key = _parameter_registry_key(parameter)
    if key is None:
        return False
    name, kind, min_indexable = key
    if kind == "eqBoth false":
        return (
            (name, "eqLhs false", min_indexable) in registry
            and (name, "eqRhs false", min_indexable) in registry
        )
    if kind == "eqBoth true":
        return (
            (name, "eqLhs true", min_indexable) in registry
            and (name, "eqRhs true", min_indexable) in registry
        )
    return key in registry


def to_ordinary_grind(
    suggestion: str,
    global_registry: GlobalGrindRegistry | None = None,
) -> tuple[str, dict[str, object]]:
    """Add non-global suggested rules to ordinary ``grind``.

    ``usr decl`` means that ``decl`` is already installed with its user-supplied
    global grind pattern.  Adding ``decl`` without ``usr`` is not equivalent:
    it can be rejected or install a different inferred pattern.  Since
    normalization deliberately preserves the global ``[grind]`` database, the
    complete ``usr decl`` parameter is omitted from the explicit list.
    """

    parts = only_parts(suggestion)
    if parts is None:
        raise ValueError(f"cannot parse grind-only suggestion: {suggestion}")
    prefix, items, suffix = parts
    if not items and "[" not in prefix:
        return suggestion.replace(" only", "", 1), {
            "retained_parameters": [],
            "usable_explicit_rules": False,
            "dropped_anchors": [],
            "dropped_usr_parameters": [],
            "dropped_global_parameters": [],
        }

    registry = global_registry or set()
    translated: list[str] = []
    dropped_anchors: list[str] = []
    dropped_usr: list[str] = []
    dropped_global: list[str] = []
    for item in items:
        stripped = item.strip()
        if stripped.startswith("#"):
            dropped_anchors.append(stripped)
            continue
        without_bang = stripped[1:].lstrip() if stripped.startswith("!") else stripped
        if without_bang.startswith("usr "):
            dropped_usr.append(stripped)
            continue
        if _is_globally_redundant(stripped, registry):
            dropped_global.append(stripped)
            continue
        translated.append(stripped)

    ordinary_prefix = prefix.replace(" only", "", 1)
    if translated:
        replacement = f"{ordinary_prefix}{', '.join(translated)}{suffix}"
    else:
        # ``prefix`` includes the opening bracket and ``suffix`` the closing one.
        replacement = ordinary_prefix[:-1].rstrip() + suffix[1:]
    return replacement, {
        "retained_parameters": translated,
        "usable_explicit_rules": bool(translated),
        "dropped_anchors": dropped_anchors,
        "dropped_usr_parameters": dropped_usr,
        "dropped_global_parameters": dropped_global,
    }


def normalize_one_discovery_from_messages(
    original: str,
    instrumented: str,
    sites: list[QuerySite],
    messages: Iterable[dict[str, object]],
    global_registry: GlobalGrindRegistry | None = None,
) -> tuple[str, dict[str, object]]:
    """Translate the selected target's recommendation, even if its file later fails."""

    if len(sites) != 1:
        raise ValueError(f"expected one query site, found {len(sites)}")
    by_span: dict[tuple[int, int, int], list[str]] = defaultdict(list)
    rejected: list[dict[str, object]] = []
    for message in messages:
        suggestions = extract_anchor_free_only_suggestions(
            str(message.get("data", ""))
        )
        if not suggestions:
            continue
        span = message_span(instrumented, message, sites)
        if span is None:
            rejected.append({"reason": "unmatched_range", "message": message})
            continue
        start, end, site = span
        by_span[(start, end, site.question_offset)].extend(suggestions)

    if len(by_span) != 1 or rejected:
        return original, {
            "applied": False,
            "matched_spans": len(by_span),
            "rejected_messages": rejected,
        }
    (start, end, question), suggestions = next(iter(by_span.items()))
    try:
        merged, was_merged = merge_suggestions(suggestions)
        replacement, translation = to_ordinary_grind(merged, global_registry)
    except ValueError as error:
        return original, {
            "applied": False,
            "error": str(error),
            "suggestions": suggestions,
        }
    if not translation["usable_explicit_rules"]:
        return original, {
            "applied": False,
            "error": "suggestion_has_no_persistable_explicit_rules",
            "suggestion": merged,
            "replacement": replacement,
            "merged": was_merged,
            **translation,
        }
    if not start <= question < end or instrumented[question] != "?":
        return original, {
            "applied": False,
            "error": "matched edit span does not contain the inserted question mark",
        }
    original_call = (
        instrumented[start:question] + instrumented[question + 1:end]
    )
    original_end = end - 1
    normalized = instrumented[:start] + replacement + instrumented[end:]
    before = len(find_discovery_calls(original))
    after = len(find_discovery_calls(normalized))
    applied = after == before - 1 and "grind?" not in normalized
    return (normalized if applied else original), {
        "applied": applied,
        "question_offset": question,
        "suggestion": merged,
        "replacement": replacement,
        "original_call": original_call,
        "prefix_context": original[max(0, start - 160):start],
        "suffix_context": original[original_end:original_end + 160],
        "merged": was_merged,
        "remaining_calls_before": before,
        "remaining_calls_after": after,
        **translation,
    }


Elaborate = Callable[
    [str, str, bool],
    tuple[Mapping[str, Any], list[dict[str, object]]],
]


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _normalization_report(
    sources: Mapping[str, str],
    rows: list[dict[str, Any]],
    counters: Counter[str],
    *,
    file_parallelism: int,
    retain_failed_files: bool,
) -> dict[str, Any]:
    inventory = Counter(
        call.flag
        for text in sources.values()
        for call in find_discovery_calls(text)
    )
    report: dict[str, Any] = {
        "schema_version": 2,
        "policy": {
            "targets": list(DISCOVERY_FLAGS),
            "query_granularity": "one_call_at_a_time_per_file",
            "file_parallelism": file_parallelism,
            "accepted_replacement": (
                "ordinary_grind_with_nonempty_persistent_rules_after_file_replay"
            ),
            "ambient_global_grind_registry": "preserved",
            "unresolved_or_failed": (
                "restore_exact_file_and_stop"
                if retain_failed_files
                else "keep_original_call_and_reject_aggregate"
            ),
        },
        "inventory": {
            "calls": sum(inventory.values()),
            "by_flag": dict(sorted(inventory.items())),
            "affected_files": len(rows),
        },
        "counts": dict(sorted(counters.items())),
        "changed_files": sum(row["changed"] for row in rows),
        "remaining_calls": sum(row["remaining_calls"] for row in rows),
        "retained_failed_files": [
            row["path"] for row in rows if row["retained_whole_file"]
        ],
        "files": rows,
    }
    report["strictly_normalized"] = (
        report["remaining_calls"] == 0
        and counters["normalized"] == sum(inventory.values())
        and counters["replay_failed"] == 0
        and counters["unresolved"] == 0
    )
    report["policy_satisfied"] = all(
        row["remaining_calls"] == 0
        or (
            retain_failed_files
            and row["retained_whole_file"]
            and row["original_sha256"] == row["normalized_sha256"]
        )
        for row in rows
    )
    return report


def normalize_discovery_sources(
    sources: Mapping[str, str],
    elaborate: Elaborate,
    *,
    global_registry: GlobalGrindRegistry | None = None,
    file_workers: int = 1,
    retain_failed_files: bool = False,
) -> tuple[dict[str, str], dict[str, Any]]:
    """Return replay-verified sources and a complete per-call audit report.

    ``elaborate(path, source, query)`` may mutate an external scratch checkout,
    but this function never mutates ``sources``.  Query diagnostics are useful
    even when the query file has unrelated errors, so a recommendation is still
    replayed and may be accepted in that case. A replay failure keeps that call
    byte-identical. When ``retain_failed_files`` is false, the caller rejects
    the aggregate unless every targeted call has a replay certificate. When it
    is true, the first uncertified call restores that file's exact input bytes,
    stops querying that file, and marks the whole file for explicit retention.
    """

    if file_workers < 1:
        raise ValueError("file_workers must be positive")
    targeted = {
        path: source
        for path, source in sources.items()
        if find_discovery_calls(source)
    }
    if file_workers > 1 and len(targeted) > 1:
        normalized = dict(sources)
        reports: list[dict[str, Any]] = []
        with ThreadPoolExecutor(
            max_workers=min(file_workers, len(targeted))
        ) as pool:
            futures = {
                pool.submit(
                    normalize_discovery_sources,
                    {path: source},
                    elaborate,
                    global_registry=global_registry,
                    file_workers=1,
                    retain_failed_files=retain_failed_files,
                ): path
                for path, source in targeted.items()
            }
            for future in as_completed(futures):
                child_sources, child_report = future.result()
                normalized.update(child_sources)
                reports.append(child_report)
        rows = sorted(
            (row for report in reports for row in report["files"]),
            key=lambda row: row["path"],
        )
        counters: Counter[str] = Counter()
        for report in reports:
            counters.update(report["counts"])
        report = _normalization_report(
            sources,
            rows,
            counters,
            file_parallelism=min(file_workers, len(targeted)),
            retain_failed_files=retain_failed_files,
        )
        return normalized, report

    normalized = dict(sources)
    rows: list[dict[str, Any]] = []
    counters: Counter[str] = Counter()

    for path in sorted(sources):
        original = sources[path]
        initial_calls = find_discovery_calls(original)
        if not initial_calls:
            continue

        current = original
        call_index = 0
        attempt = 0
        call_rows: list[dict[str, Any]] = []
        retention_trigger: dict[str, Any] | None = None
        while call_index < len(find_discovery_calls(current)):
            attempt += 1
            queried, sites, instrumentation = instrument_discovery_call(
                current, call_index
            )
            query_source, disabled_budgets = disable_scoped_heartbeats(queried)
            query_result, messages = elaborate(path, query_source, True)
            counters["query_pass" if query_result.get("passed") else "query_fail"] += 1

            candidate, decision = normalize_one_discovery_from_messages(
                current,
                queried,
                sites,
                messages,
                global_registry=global_registry,
            )
            row: dict[str, Any] = {
                "attempt": attempt,
                "remaining_call_index": call_index,
                "flag": instrumentation["flag"],
                "tactic_offset": instrumentation["tactic_offset"],
                "heartbeat_budgets_disabled_for_query": disabled_budgets,
                "query": dict(query_result),
                "normalization": decision,
                "source_sha256_before": _sha256(current),
            }

            if not decision.get("applied"):
                row["status"] = "kept_original_no_recommendation"
                row["replay"] = {"passed": False, "skipped": True}
                row["source_sha256_after"] = _sha256(current)
                counters["unresolved"] += 1
                call_rows.append(row)
                if retain_failed_files:
                    retention_trigger = {
                        "attempt": attempt,
                        "status": row["status"],
                        "flag": row["flag"],
                    }
                    break
                call_index += 1
                continue

            # Query elaboration already removes any source-scoped heartbeat
            # ceilings. Replay must use the same resource policy: otherwise a
            # valid recommendation can be rejected because an unrelated later
            # proof in the file exhausts Lean's default/scoped budget. Keep the
            # accepted source unchanged apart from the Grind replacement; this
            # heartbeat rewrite exists only in the replay candidate.
            replay_source, replay_disabled_budgets = disable_scoped_heartbeats(
                candidate
            )
            replay_result, _ = elaborate(path, replay_source, False)
            row["replay"] = dict(replay_result)
            row["heartbeat_budgets_disabled_for_replay"] = (
                replay_disabled_budgets
            )
            if replay_result.get("passed"):
                current = candidate
                row["status"] = "normalized_replay_passed"
                counters["normalized"] += 1
                # The selected call disappeared; the same index now addresses
                # the next remaining discovery call.
            else:
                row["status"] = "kept_original_replay_failed"
                counters["replay_failed"] += 1
                if retain_failed_files:
                    retention_trigger = {
                        "attempt": attempt,
                        "status": row["status"],
                        "flag": row["flag"],
                    }
                call_index += 1
            row["source_sha256_after"] = _sha256(current)
            call_rows.append(row)
            if retention_trigger is not None:
                break

        if retention_trigger is not None:
            certified = sum(
                row["status"] == "normalized_replay_passed"
                for row in call_rows
            )
            if certified:
                counters["normalized"] -= certified
                counters["replay_certified_then_reverted"] += certified
            skipped = len(initial_calls) - len(call_rows)
            counters["skipped_after_file_retention"] += skipped
            current = original
            for row in call_rows:
                row["persisted_after_file_decision"] = False
                if row["status"] == "normalized_replay_passed":
                    row["reverted_by_file_retention"] = True
        else:
            skipped = 0
            for row in call_rows:
                row["persisted_after_file_decision"] = (
                    row["status"] == "normalized_replay_passed"
                )

        remaining = find_discovery_calls(current)
        normalized[path] = current
        rows.append(
            {
                "path": path,
                "original_sha256": _sha256(original),
                "normalized_sha256": _sha256(current),
                "initial_calls": len(initial_calls),
                "remaining_calls": len(remaining),
                "changed": current != original,
                "retained_whole_file": retention_trigger is not None,
                "retention_trigger": retention_trigger,
                "attempted_calls": len(call_rows),
                "skipped_calls": skipped,
                "calls": call_rows,
            }
        )

    report = _normalization_report(
        sources,
        rows,
        counters,
        file_parallelism=1,
        retain_failed_files=retain_failed_files,
    )
    return normalized, report


def _common_suffix_length(left: str, right: str) -> int:
    limit = min(len(left), len(right))
    matched = 0
    while matched < limit and left[-matched - 1] == right[-matched - 1]:
        matched += 1
    return matched


def _common_prefix_length(left: str, right: str) -> int:
    limit = min(len(left), len(right))
    matched = 0
    while matched < limit and left[matched] == right[matched]:
        matched += 1
    return matched


def _replacement_offsets(source: str, replacement: str) -> list[int]:
    if not replacement:
        return []
    offsets: list[int] = []
    start = 0
    while True:
        found = source.find(replacement, start)
        if found < 0:
            return offsets
        offsets.append(found)
        start = found + 1


def _locate_accepted_edit(source: str, call: Mapping[str, Any]) -> tuple[int | None, dict]:
    normalization = call.get("normalization", {})
    replacement = str(normalization.get("replacement", ""))
    original_call = str(normalization.get("original_call", ""))
    prefix = str(normalization.get("prefix_context", ""))
    suffix = str(normalization.get("suffix_context", ""))
    offsets = _replacement_offsets(source, replacement)
    if not replacement or not original_call:
        return None, {"reason": "missing_original_call_provenance"}
    if not offsets:
        return None, {"reason": "replacement_absent_owner_dropped"}

    scored = []
    for offset in offsets:
        prefix_score = _common_suffix_length(source[:offset], prefix)
        end = offset + len(replacement)
        suffix_score = _common_prefix_length(source[end:], suffix)
        scored.append((prefix_score + suffix_score, prefix_score, suffix_score, offset))
    scored.sort(reverse=True)
    best = scored[0]
    tied = [row for row in scored if row[:3] == best[:3]]
    required = min(24, max(len(prefix), len(suffix)))
    if len(tied) != 1 or best[0] < required:
        return None, {
            "reason": "ambiguous_or_weak_context_match",
            "occurrences": len(offsets),
            "best_context_score": best[0],
            "required_context_score": required,
        }
    return best[3], {
        "reason": "located",
        "occurrences": len(offsets),
        "prefix_score": best[1],
        "suffix_score": best[2],
    }


def _plan_file_restoration(
    source: str,
    calls: list[Mapping[str, Any]],
) -> tuple[str, list[dict], list[dict]]:
    """Restore locatable accepted edits in reverse source order."""
    current = source
    planned: list[dict] = []
    skipped: list[dict] = []
    accepted = [
        call for call in calls
        if call.get("status") == "normalized_replay_passed"
        and call.get("persisted_after_file_decision") is not False
    ]
    for call in reversed(accepted):
        offset, location = _locate_accepted_edit(current, call)
        base = {
            "attempt": call.get("attempt"),
            "flag": call.get("flag"),
            "replacement": call.get("normalization", {}).get("replacement", ""),
            "original_call": call.get("normalization", {}).get("original_call", ""),
            "location": location,
        }
        if offset is None:
            skipped.append({**base, "status": location["reason"]})
            continue
        replacement = str(base["replacement"])
        original_call = str(base["original_call"])
        current = (
            current[:offset] + original_call + current[offset + len(replacement):]
        )
        planned.append({**base, "offset": offset})
    return current, planned, skipped


def restore_original_discovery_sources(
    sources: Mapping[str, str],
    normalization_report: Mapping[str, Any],
    elaborate: Elaborate,
    *,
    file_workers: int = 1,
) -> tuple[dict[str, str], dict[str, Any]]:
    """Remove temporary explicit Grind instrumentation from the stripped tree.

    All surviving accepted edits in one file are restored to their exact
    original calls and replayed as a batch. A passing file needs one replay.
    A failing all-original candidate is retained so the caller's aggregate
    warm build rejects the repository. Temporary explicit Grind arguments are
    dependency instrumentation and can never become output source.
    """
    if file_workers < 1:
        raise ValueError("file_workers must be positive")
    by_path = {
        str(row["path"]): row
        for row in normalization_report.get("files", [])
        if any(
            call.get("status") == "normalized_replay_passed"
            and call.get("persisted_after_file_decision") is not False
            for call in row.get("calls", [])
        )
    }
    targeted = {
        path: row for path, row in by_path.items()
        if path in sources
    }

    def restore_file(path: str, file_row: Mapping[str, Any]):
        source = sources[path]
        batch_candidate, planned, skipped = _plan_file_restoration(
            source, list(file_row.get("calls", []))
        )
        row: dict[str, Any] = {
            "path": path,
            "accepted_candidates": sum(
                call.get("status") == "normalized_replay_passed"
                and call.get("persisted_after_file_decision") is not False
                for call in file_row.get("calls", [])
            ),
            "located_surviving_calls": len(planned),
            "calls": list(reversed(skipped)),
        }
        if not planned:
            row["batch_replay"] = {"passed": True, "skipped": True}
            return path, source, row

        batch_replay_source, batch_disabled_budgets = disable_scoped_heartbeats(
            batch_candidate
        )
        batch_result, _ = elaborate(path, batch_replay_source, False)
        row["batch_replay"] = dict(batch_result)
        row["heartbeat_budgets_disabled_for_batch_replay"] = (
            batch_disabled_budgets
        )
        if batch_result.get("passed"):
            row["calls"].extend(
                {**call, "status": "restored_original_batch_passed"}
                for call in reversed(planned)
            )
            return path, batch_candidate, row

        row["calls"].extend(
            {**call, "status": "restored_original_batch_failed"}
            for call in reversed(planned)
        )
        return path, batch_candidate, row

    restored = dict(sources)
    rows: list[dict] = []
    workers = min(file_workers, len(targeted)) if targeted else 0
    if workers == 0:
        results = []
    elif workers == 1:
        results = [
            restore_file(path, targeted[path])
            for path in sorted(targeted)
        ]
    else:
        results = []
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures = {
                pool.submit(restore_file, path, row): path
                for path, row in targeted.items()
            }
            for future in as_completed(futures):
                results.append(future.result())

    counters: Counter[str] = Counter()
    for path, source, row in sorted(results):
        restored[path] = source
        rows.append(row)
        for call in row["calls"]:
            counters[str(call["status"])] += 1
    report = {
        "schema_version": 1,
        "policy": {
            "target_state": "exact_original_grind_call",
            "common_case": "one_batch_replay_per_file",
            "batch_failure": "retain_original_candidate_for_aggregate_rejection",
            "failed_call": "reject_repository",
            "file_parallelism": workers,
        },
        "targeted_files": len(targeted),
        "counts": dict(sorted(counters.items())),
        "files": rows,
    }
    return restored, report


def classify_edit_survival(
    report: Mapping[str, Any],
    final_sources: Mapping[str, str],
) -> dict[str, int]:
    """Classify what happened to each accepted edit after stripping.

    A missing replacement with no remaining discovery syntax means the owner
    command was deleted by the dependency slice, so an accepted edit can
    legitimately be absent from the final sources.
    """

    counts: Counter[str] = Counter()
    for file_row in report.get("files", []):
        path = str(file_row["path"])
        final = final_sources.get(path, "")
        for call in file_row.get("calls", []):
            if call.get("status") != "normalized_replay_passed":
                counts[str(call.get("status", "unknown"))] += 1
                continue
            replacement = str(call.get("normalization", {}).get("replacement", ""))
            flag = str(call.get("flag", ""))
            if replacement and replacement in final:
                counts["accepted_edit_survived_strip"] += 1
            elif f"grind +{flag}" in final:
                counts["accepted_edit_reverted_or_ambiguous"] += 1
            else:
                counts["accepted_edit_owner_command_dropped"] += 1
    return dict(sorted(counts.items()))
