"""Declarations a notation or macro body names.

`notation`, `infix`/`prefix`/`postfix` and `macro` commands are always kept,
and Lean checks the identifiers in their right-hand side when the command is
elaborated ("Unknown identifier `D.rank` at quotation precheck"). The command
is not a declaration, so what its body names gets no dependency edge: when no
kept declaration uses the notation any more, the strip deleted what the body
names and the kept command stopped elaborating (PALOMAR-2026-10-22-000019:
`local notation "r" => D.rank ∘ g`, with `D : SquareCrosscutData _` a section
`variable`).

Every name the body resolves to is rooted: a plain or dotted name through the
enclosing namespaces and the `open`s in scope, and `x.f` with `x` a section
`variable` through the head of that variable's type, as Lean resolves
generalised field notation.
"""

from __future__ import annotations

import re

from lean_strip._pipeline.preprocessing import strip as _strip

# The command head, possibly behind `local`/`scoped` and attributes; its
# right-hand side starts at the first `=>`.
_NOTATION_HEAD_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:local|scoped)[ \t]+)*"
    r"(?:notation\d*|infixl|infixr|infix|prefix|postfix|macro)\b"
)
_VARIABLE_HEAD_RE = re.compile(r"^[ \t]*variable\b")
# A name, not a field access on something else (`.f`) and not inside a
# quoted atom (`"r"` is masked as a string anyway).
_NAME_RE = re.compile(rf"(?<![{_strip._ID_REST}.`])({_strip._LEAN_COMMAND_NAME_PATTERN})")


_OPEN_TO_CLOSE = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}


def _variable_binder_types(command: str) -> dict[str, str]:
    """Binder names of a `variable` command and the head name of their type.

    Brackets are matched with nesting, so `(D : SquareCrosscutData (112*n+1))`
    gives `D -> SquareCrosscutData`.
    """

    out: dict[str, str] = {}
    index = 0
    while index < len(command):
        opener = command[index]
        if opener not in _OPEN_TO_CLOSE:
            index += 1
            continue
        depth, end = 0, index
        while end < len(command):
            char = command[end]
            if char in _OPEN_TO_CLOSE:
                depth += 1
            elif char in _OPEN_TO_CLOSE.values():
                depth -= 1
                if depth == 0:
                    break
            end += 1
        group = command[index + 1:end]
        index = end + 1
        binders, colon, type_part = group.partition(":")
        if not colon:
            continue
        head = _strip._IDENT_RE.match(type_part.strip())
        if head is None:
            continue
        for binder in binders.split():
            if _strip._IDENT_RE.fullmatch(binder):
                out[binder] = head.group(0)
    return out


def _command_lines(lines: list[str], start: int) -> tuple[str, int]:
    """The command starting at ``start``: its first line and indented continuations."""

    end = start + 1
    while end < len(lines) and lines[end].strip() and lines[end][:1].isspace():
        end += 1
    return "\n".join(lines[start:end]), end


def detect_notation_body_roots(decls: list[dict], originals: dict[str, str]) -> set[str]:
    """Project declarations named in the right-hand side of notation/macro commands."""

    names = {str(d["name"]) for d in decls}
    roots: set[str] = set()
    for text in originals.values():
        if not any(keyword in text for keyword in ("notation", "infix", "prefix", "postfix", "macro")):
            continue
        masked = _strip._mask_comments_preserve_layout(text)
        lines = masked.split("\n")
        namespace_by_line, opens_by_line = _strip._source_namespace_resolution_contexts(text)
        variable_types: dict[str, str] = {}
        index = 0
        while index < len(lines):
            line = lines[index]
            if _VARIABLE_HEAD_RE.match(line):
                command, index = _command_lines(lines, index)
                variable_types.update(_variable_binder_types(command))
                continue
            if not _NOTATION_HEAD_RE.match(line):
                index += 1
                continue
            command, end = _command_lines(lines, index)
            line_no = index + 1
            index = end
            _head, arrow, body = command.partition("=>")
            if not arrow:
                continue
            namespace = namespace_by_line.get(line_no, "")
            opened = tuple(opens_by_line.get(line_no, ()))
            for token in _NAME_RE.findall(body):
                candidates = _strip._namespace_name_candidates(token, namespace)
                if not token.startswith("_root_."):
                    candidates += [f"{prefix}.{token}" for prefix in opened]
                hit = next((name for name in candidates if name in names), None)
                if hit is not None:
                    roots.add(hit)
                    continue
                receiver, dot, field = token.partition(".")
                type_head = variable_types.get(receiver) if dot else None
                if type_head and field:
                    for type_name in _strip._namespace_name_candidates(type_head, namespace) + [
                        f"{prefix}.{type_head}" for prefix in opened
                    ]:
                        if f"{type_name}.{field}" in names:
                            roots.add(f"{type_name}.{field}")
                            break
    return roots
