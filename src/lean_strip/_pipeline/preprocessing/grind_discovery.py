"""Find executable Lean ``grind +suggestions`` and ``grind +locals`` calls."""

from __future__ import annotations

import re
from dataclasses import dataclass

from lean_strip._pipeline.preprocessing.query_replay import (
    inside_attribute,
    masked_regions,
)


DISCOVERY_FLAGS = ("suggestions", "locals")
_TARGET_RE = re.compile(
    r"(?<![A-Za-z0-9_.])"
    r"(?P<tactic>grind)"
    r"(?P<spacing>[ \t\r\n]+)"
    r"\+(?P<flag>suggestions|locals)\b"
)


@dataclass(frozen=True)
class DiscoveryCall:
    tactic_start: int
    tactic_end: int
    flag: str


def find_discovery_calls(source: str) -> list[DiscoveryCall]:
    """Find executable ``grind +suggestions`` and ``grind +locals`` calls."""

    masked = masked_regions(source)
    calls: list[DiscoveryCall] = []
    seen_tactics: set[int] = set()
    for match in _TARGET_RE.finditer(source):
        start, end = match.span()
        tactic_start, tactic_end = match.span("tactic")
        if any(masked[start:end]):
            continue
        if inside_attribute(source, masked, tactic_start):
            continue
        if tactic_start in seen_tactics:
            continue
        seen_tactics.add(tactic_start)
        calls.append(
            DiscoveryCall(
                tactic_start=tactic_start,
                tactic_end=tactic_end,
                flag=match.group("flag"),
            )
        )
    return calls
