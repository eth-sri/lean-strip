"""Lean source-token metric.

Every non-comment, non-import source token is counted, including theorem
statements and helper declarations, so splitting a proof into many small
lemmas does not make declaration overhead free.
"""

from __future__ import annotations

import re


# Multi-character operators rejoined after the character-level lexer splits
# them into single characters.
LEAN_OPERATORS = (
    ":=",
    "!=",
    "&&",
    "-.",
    "->",
    "←",
    "..",
    "...",
    "::",
    ":>",
    "<;>",
    ";;",
    "==",
    "||",
    "=>",
    "<=",
    ">=",
    "−1",
    "?_",
)
_SPACED_OPERATORS = tuple(" ".join(operator) for operator in LEAN_OPERATORS)
_SPACED_OPERATOR_MAP = dict(zip(_SPACED_OPERATORS, LEAN_OPERATORS, strict=False))

_IMPORT_COMMAND_RE = re.compile(r"^\s*(?:(?:public|private)\s+)?import(?:\s|$)")


def remove_lean_comments(source: str, *, mask_strings: bool = False) -> str:
    """Mask comments while preserving offsets; optionally mask strings too."""

    result: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False

    while index < len(source):
        char = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                result.append(char)
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth:
            if char == "/" and following == "-":
                result.extend((" ", " "))
                block_depth += 1
                index += 2
                continue
            if char == "-" and following == "/":
                result.extend((" ", " "))
                block_depth -= 1
                index += 2
                continue
            result.append(char if char == "\n" else " ")
            index += 1
            continue

        if in_string:
            result.append(" " if mask_strings and char != "\n" else char)
            if char == "\\" and following:
                result.append(" " if mask_strings and following != "\n" else following)
                index += 2
                continue
            if char == '"':
                in_string = False
            index += 1
            continue

        if char == "-" and following == "-":
            result.extend((" ", " "))
            in_line_comment = True
            index += 2
            continue
        if char == "/" and following == "-":
            result.extend((" ", " "))
            block_depth = 1
            index += 2
            continue
        if char == '"':
            in_string = True

        result.append(" " if mask_strings and char == '"' else char)
        index += 1

    return "".join(result)


def _lex(lean_snippet: str) -> str:
    """Space-separate the tokens of each line of a Lean snippet."""

    tokenized_lines: list[str] = []
    for line in lean_snippet.splitlines():
        tokens: list[str] = []
        token = ""
        for char in line:
            if char == " ":
                if token:
                    tokens.append(token)
                token = ""
            elif char.isalnum() or char in "._'":
                token += char
            else:
                if token:
                    tokens.append(token)
                token = ""
                tokens.append(char)
        if token:
            tokens.append(token)

        tokenized_line = " ".join(tokens)
        for spaced_operator in _SPACED_OPERATORS:
            if spaced_operator in tokenized_line:
                tokenized_line = tokenized_line.replace(
                    spaced_operator,
                    _SPACED_OPERATOR_MAP[spaced_operator],
                )
        tokenized_lines.append(tokenized_line)

    return "\n".join(tokenized_lines)


def _token_count(source: str) -> int:
    tokenized = _lex(source.strip())
    # ``split()`` rather than ``split(" ")``: the latter counts an empty
    # tokenized line as one token, so whitespace-only lines would change the
    # score.
    return sum(len(line.split()) for line in tokenized.splitlines())


def count_lean_tokens_in_source(source: str) -> int:
    """Count all source tokens except comments and import commands."""

    without_comments = remove_lean_comments(source)
    masked_strings = remove_lean_comments(source, mask_strings=True)
    without_imports = "\n".join(
        "" if _IMPORT_COMMAND_RE.match(masked_line) else source_line
        for source_line, masked_line in zip(
            without_comments.splitlines(),
            masked_strings.splitlines(),
            strict=True,
        )
    )
    return _token_count(without_imports)
