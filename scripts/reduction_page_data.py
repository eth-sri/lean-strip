#!/usr/bin/env python3
"""Compact per-result data for the reduction page, from a sweep directory.

    python3 scripts/reduction_page_data.py --out sweep/ > data.json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from reduction_table import collect  # noqa: E402


# A build that cannot get threads or address space even with one Lean thread
# and small stacks hit the host's limits, not a lean-strip problem.
_HOST_LIMIT_MARKERS = ("failed to create thread", "INTERNAL PANIC: out of memory")


def _host_limited(out: Path, rid: str) -> bool:
    log = out / "reports" / rid / "failure.log"
    text = log.read_text(errors="replace") if log.is_file() else ""
    return any(marker in text for marker in _HOST_LIMIT_MARKERS)


def _smaller_stacks(out: Path, rid: str) -> bool:
    """Whether a build needed smaller Lean thread stacks (a `ulimit -v` host)."""

    log = out / "reports" / rid / "log.txt"
    return log.is_file() and "MiB Lean thread stacks" in log.read_text(errors="replace")


def _pair(block: dict, metric: str) -> list:
    row = (block or {}).get(metric) or {}
    return [row.get("before"), row.get("after")]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    table = collect(out)
    latest: dict[str, str | None] = {}  # the latest run of each result wins
    for line in (out / "results.jsonl").read_text().splitlines():
        row = json.loads(line)
        latest[row["id"]] = row.get("code_version")
    versions = set(latest.values())
    rows = []
    for row in table["results"]:
        compact = {
            "id": row["id"], "title": row["title"], "repo": row["repository"],
            "commit": row["commit"], "path": row["project_path"], "status": row["status"],
            "protected": row["protected"], "toolchain": row["toolchain"].split(":")[-1],
        }
        if row["status"] == "failed":
            compact["stage"], compact["error"] = row.get("stage"), row.get("error")
            compact["hostLimit"] = _host_limited(out, row["id"])
        elif row.get("totals"):
            isolated = row["isolation"]["tokens"]["after"]
            compact.update(
                tokens=[row["totals"]["tokens"]["before"], isolated, row["totals"]["tokens"]["after"]],
                files=_pair(row["totals"], "files"),
                lines=_pair(row["totals"], "lines"),
                decls=[row["declarations"].get(key) for key in ("total", "kept", "dropped")],
                seconds=row.get("seconds"),
                lakefile=row.get("lakefile_edited"),
                lakeBuild=row.get("lake_build_ok"),
                fallback=row.get("build_fallback"),
                comparator=row.get("comparator"),
                stacks=_smaller_stacks(out, row["id"]),
            )
        rows.append(compact)
    print(json.dumps({
        "registry": {"revision": table["registry_revision"], "release": table["registry_release"],
                     "snapshot": table["taken_at"]},
        "tool": {"version": "1.1.2", "code": sorted(v for v in versions if v)},
        "mode": "--retain-lean-only",
        "rows": rows,
    }, separators=(",", ":"), ensure_ascii=False))


if __name__ == "__main__":
    main()
