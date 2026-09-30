"""Pure source helpers for replaying explicit Grind discovery queries."""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass


_HEARTBEAT_RE = re.compile(r"\bset_option\s+maxHeartbeats\s+(\d+)")


@dataclass(frozen=True)
class QuerySite:
    tactic: str
    token_start: int
    token_end: int
    question_offset: int


def masked_regions(source: str) -> list[bool]:
    """Mask comments, string literals, and syntax quotations.

    Syntax quotations are intentionally excluded: a tactic inside
    `` `(tactic| ...) `` is macro data, not the executable call whose query
    code action can be applied at that source location.
    """

    masked = [False] * len(source)
    index = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False
    while index < len(source):
        char = source[index]
        nxt = source[index + 1] if index + 1 < len(source) else ""
        if in_line:
            masked[index] = True
            if char == "\n":
                in_line = False
            index += 1
            continue
        if block_depth:
            masked[index] = True
            if char == "/" and nxt == "-":
                masked[index + 1] = True
                block_depth += 1
                index += 2
            elif char == "-" and nxt == "/":
                masked[index + 1] = True
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue
        if in_string:
            masked[index] = True
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if char == "-" and nxt == "-":
            masked[index] = masked[index + 1] = True
            in_line = True
            index += 2
        elif char == "/" and nxt == "-":
            masked[index] = masked[index + 1] = True
            block_depth = 1
            index += 2
        elif char == '"':
            masked[index] = True
            in_string = True
            index += 1
        else:
            index += 1

    # Mask balanced syntax quotations after comments/strings are known.
    index = 0
    while index + 1 < len(source):
        if masked[index] or source[index : index + 2] != "`(":
            index += 1
            continue
        depth = 0
        end = index + 1
        while end < len(source):
            if masked[end]:
                end += 1
                continue
            if source[end] == "(":
                depth += 1
            elif source[end] == ")":
                depth -= 1
                if depth == 0:
                    end += 1
                    break
            end += 1
        for position in range(index, min(end, len(source))):
            masked[position] = True
        index = max(end, index + 2)
    return masked


def inside_attribute(source: str, masked: list[bool], offset: int) -> bool:
    stack: list[int] = []
    for index in range(offset):
        if masked[index]:
            continue
        if source[index] == "[":
            stack.append(index)
        elif source[index] == "]" and stack:
            stack.pop()
    if not stack:
        return False
    opening = stack[-1]
    prefix = source[max(0, opening - 40) : opening]
    return prefix.rstrip().endswith("@") or bool(
        re.search(r"\battribute\s*$", prefix)
    )


def disable_scoped_heartbeats(source: str) -> tuple[str, list[int]]:
    """Replace source heartbeat budgets with zero, preserving every offset."""

    masked = masked_regions(source)
    out = list(source)
    budgets: list[int] = []
    for match in _HEARTBEAT_RE.finditer(source):
        start, end = match.span(1)
        if any(masked[start:end]):
            continue
        budgets.append(int(match.group(1)))
        out[start:end] = "0" + " " * (end - start - 1)
    return "".join(out), budgets


def _line_start(source: str, line: int) -> tuple[int, str]:
    if line < 1:
        raise ValueError(f"invalid line {line}")
    lines = source.splitlines(keepends=True)
    if line > len(lines):
        raise ValueError(f"line {line} exceeds {len(lines)}")
    start = sum(len(part) for part in lines[: line - 1])
    return start, lines[line - 1].rstrip("\r\n")


def position_offsets(source: str, position: dict[str, object]) -> list[int]:
    """Return plausible offsets for Lean JSON columns.

    Lean versions differ: some expose Unicode scalar columns while others
    expose UTF-8 byte columns, so callers validate both candidates against
    the instrumented query token.
    """

    line = int(position["line"])
    column = int(position.get("column", 0))
    start, content = _line_start(source, line)
    candidates: list[int] = []
    if 0 <= column <= len(content):
        candidates.append(start + column)
    encoded = content.encode("utf-8")
    if 0 <= column <= len(encoded):
        try:
            prefix = encoded[:column].decode("utf-8")
        except UnicodeDecodeError:
            pass
        else:
            candidate = start + len(prefix)
            if candidate not in candidates:
                candidates.append(candidate)
    return candidates


def _matching_square(text: str, opening: int) -> int | None:
    depth = 0
    in_string = False
    escaped = False
    for index in range(opening, len(text)):
        char = text[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            in_string = True
        elif char == "[":
            depth += 1
        elif char == "]":
            depth -= 1
            if depth == 0:
                return index
    return None


def _split_items(contents: str) -> list[str]:
    items: list[str] = []
    start = 0
    stack: list[str] = []
    pairs = {")": "(", "]": "[", "}": "{"}
    in_string = False
    escaped = False
    for index, char in enumerate(contents):
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char in "([{":
            stack.append(char)
        elif char in ")]}" and stack and stack[-1] == pairs[char]:
            stack.pop()
        elif char == "," and not stack:
            item = contents[start:index].strip()
            if item:
                items.append(item)
            start = index + 1
    final = contents[start:].strip()
    if final:
        items.append(final)
    return items


def only_parts(suggestion: str) -> tuple[str, list[str], str] | None:
    marker = re.search(r"\bonly\b", suggestion)
    if marker is None:
        return None
    opening = suggestion.find("[", marker.end())
    if opening < 0:
        # ``simp only`` and ``grind only`` with an empty rule set are valid.
        return suggestion, [], ""
    closing = _matching_square(suggestion, opening)
    if closing is None:
        return None
    return (
        suggestion[: opening + 1],
        _split_items(suggestion[opening + 1 : closing]),
        suggestion[closing:],
    )


def merge_suggestions(suggestions: Iterable[str]) -> tuple[str, bool]:
    """Union compatible rule lists emitted for one multi-goal tactic span."""

    unique = list(dict.fromkeys(suggestions))
    if not unique:
        raise ValueError("no suggestions")
    if len(unique) == 1:
        return unique[0], False
    parts = [only_parts(suggestion) for suggestion in unique]
    if any(part is None for part in parts):
        raise ValueError(f"incompatible suggestions: {unique}")
    signatures = {
        (" ".join(part[0].split()), " ".join(part[2].split()))
        for part in parts
        if part is not None
    }
    if len(signatures) != 1:
        raise ValueError(f"incompatible suggestions: {unique}")
    prefix, _, suffix = parts[0]  # type: ignore[misc]
    items: list[str] = []
    item_keys: set[str] = set()
    for _, current, _ in parts:  # type: ignore[misc]
        for item in current:
            key = " ".join(item.split())
            if key not in item_keys:
                items.append(item)
                item_keys.add(key)
    return f"{prefix}{', '.join(items)}{suffix}", True


def _balanced_suffix_end(source: str, opening: int) -> int | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    opener = source[opening]
    if opener not in pairs:
        return None
    stack = [pairs[opener]]
    in_string = False
    escaped = False
    index = opening + 1
    while index < len(source):
        char = source[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            in_string = True
        elif char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
            if not stack:
                return index + 1
        index += 1
    return None


def tactic_tail_end(source: str, token_end: int) -> int:
    """Consume the suffix omitted from simp?/grind? diagnostic ranges.

    Lean's JSON ``pos``/``endPos`` is a diagnostic highlight, not the actual
    code-action edit.  For simp-family and grind queries it commonly covers
    only the query token, while the suggested replacement also contains the
    original config, lemma list, and ``at`` target.  This parser consumes just
    those grammar components and stops before tactic combinators or the next
    line.
    """

    index = token_end
    consumed = False
    while True:
        cursor = index
        while cursor < len(source) and source[cursor] in " \t":
            cursor += 1
        if cursor < len(source) and source[cursor] == "\n":
            lookahead = cursor + 1
            while lookahead < len(source) and source[lookahead] in " \t\r\n":
                lookahead += 1
            continues = (
                lookahead < len(source)
                and (
                    source[lookahead] in "[({+-"
                    or re.match(r"at\b", source[lookahead:]) is not None
                )
            )
            if not continues:
                return index
            cursor = lookahead
        if cursor >= len(source):
            return index
        if source[cursor] in "[({":
            end = _balanced_suffix_end(source, cursor)
            if end is None:
                return index
            index = end
            consumed = True
            continue
        flag = re.match(r"[+-][A-Za-z_][A-Za-z0-9_]*", source[cursor:])
        if flag is not None:
            index = cursor + flag.end()
            consumed = True
            continue
        if re.match(r"at\b", source[cursor:]) is not None:
            end = cursor + 2
            while end < len(source):
                if source[end] == "\n" or source.startswith("<;>", end):
                    break
                if source[end] in ";)}]":
                    break
                end += 1
            return len(source[:end].rstrip(" \t"))
        return index if consumed else token_end


def message_span(
    source: str,
    message: dict[str, object],
    sites: list[QuerySite],
) -> tuple[int, int, QuerySite] | None:
    pos = message.get("pos")
    end_pos = message.get("endPos")
    if not isinstance(pos, dict) or not isinstance(end_pos, dict):
        return None
    for start in position_offsets(source, pos):
        for end in position_offsets(source, end_pos):
            if start >= end:
                continue
            contained = [
                site
                for site in sites
                if start <= site.token_start and site.question_offset < end
            ]
            if contained:
                site = min(contained, key=lambda item: item.token_start)
                if end == site.question_offset + 1 and site.tactic != "simpa":
                    end = tactic_tail_end(source, end)
                return start, end, site
    return None
