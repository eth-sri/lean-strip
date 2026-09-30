"""Whitespace-delimited Lean word metric."""

from __future__ import annotations

from .tokens import remove_lean_comments


def count_lean_words_in_source(source: str) -> int:
    """Count non-comment, non-import whitespace-delimited Lean words."""

    total = 0
    for line in remove_lean_comments(source).splitlines():
        if line.lstrip().startswith("import "):
            continue
        total += len(line.split())
    return total
