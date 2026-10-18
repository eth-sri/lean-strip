#!/usr/bin/env python3
"""Collect a sweep's per-result reductions into one JSON table.

    python3 scripts/reduction_table.py --out sweep/ > reductions.json

Reads `results.jsonl` (the latest run of each result wins), each result's
saved `reports/<id>/report.json` and its registry record. One row per
registry result; failed results are listed with their stage so nothing is
silently missing from the table.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

METRICS = ("files", "lines", "code_lines", "tokens", "words")


def _metric(block: dict, metric: str) -> dict:
    row = block.get(metric) or {}
    return {key: row.get(key) for key in ("before", "after", "saved", "reduction")}


def collect(out: Path) -> dict:
    latest: dict[str, dict] = {}
    for line in (out / "results.jsonl").read_text().splitlines():
        row = json.loads(line)
        latest[row["id"]] = row
    snapshot = json.loads((out / "snapshot.json").read_text())
    rows = []
    for rid in snapshot["ids"]:
        record = json.loads((out / "records" / f"{rid}.json").read_text())
        result = latest.get(rid)
        row = {
            "id": rid,
            "title": record.get("title"),
            "repository": record["source"]["repository"],
            "commit": record["source"]["commit"],
            "project_path": record["source"].get("project_path"),
            "toolchain": record["formalization"].get("lean_toolchain", "").strip(),
            "protected": len(record["formalization"].get("theorem_names") or [])
            + len(record["formalization"].get("definition_names") or []),
            "status": result["status"] if result else "not_run",
        }
        report_path = out / "reports" / rid / "report.json"
        report = json.loads(report_path.read_text()) if report_path.is_file() else {}
        if row["status"] == "failed":
            row["stage"] = result.get("stage")
            row["error"] = (result.get("error") or "")[:300]
        elif report.get("totals"):
            row["seconds"] = report.get("seconds")
            row["totals"] = {metric: _metric(report["totals"], metric) for metric in METRICS}
            row["isolation"] = {metric: _metric(report["phases"]["isolation"], metric) for metric in METRICS}
            row["stripping"] = {metric: _metric(report["phases"]["stripping"], metric) for metric in METRICS}
            declarations = report.get("declarations") or {}
            row["declarations"] = {key: declarations.get(key) for key in ("total", "kept", "dropped")}
            lake = report.get("lakefile") or {}
            row["lakefile_edited"] = bool(lake.get("rewritten"))
            row["lake_build_ok"] = (lake.get("lake_build") or {}).get("ok")
            fallback = report.get("build_fallback")
            row["build_fallback"] = None if not fallback else {
                "rounds": fallback.get("rounds"),
                "heartbeats": len(fallback.get("heartbeats") or []),
                "grind_restored_files": len(fallback.get("grind_restored_files") or []),
                # Reports from before 1.2, whose fallback also kept more
                # declarations and restored files for any error.
                "whole_tree": fallback.get("whole_tree", False),
                "restored_files": len(fallback.get("restored_files") or []),
                "rerooted_declarations": len(fallback.get("rerooted_declarations") or []),
            }
            verdict = report.get("comparator") or {}
            row["comparator"] = {key: verdict.get(key) for key in ("status", "judge", "sandbox", "seconds")} \
                if verdict else None
        rows.append(row)
    return {
        "registry_revision": snapshot["revision"],
        "registry_release": snapshot["release"],
        "taken_at": snapshot["taken_at"],
        "results": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", type=Path, required=True, help="the sweep directory")
    args = parser.parse_args()
    print(json.dumps(collect(args.out), indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
