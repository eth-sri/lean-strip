"""Source edits decided from Lean's own view of a file (see frontend.py).

`plan_file` is the counterpart of `strip.strip_source` followed by
`strip.remove_dead_commands` for a file the Lean pass analysed. Nothing here
models Lean: command boundaries and kinds come from Lean's parser, scopes from
the elaborator's state, and "this names a deleted declaration" from the
constants Lean's elaborated terms denote. What remains in Python is the
editing policy (which commands may go, how the text is tidied), which is the
same as the regex path's.
"""

from __future__ import annotations

from bisect import bisect_right
from dataclasses import dataclass, field
from typing import Iterable

from lean_strip._pipeline.preprocessing.frontend import (
    Binder, Command, FileSyntax, Node, _Offsets,
)
from lean_strip._pipeline.preprocessing import strip as _strip


_IN = "Lean.Parser.Command.in"
_GUARD_MSGS = "Lean.guardMsgsCmd"
_OPEN = "Lean.Parser.Command.open"
_OPEN_SIMPLE = "Lean.Parser.Command.openSimple"
_OPEN_ONLY = "Lean.Parser.Command.openOnly"
_EXPORT = "Lean.Parser.Command.export"
_ATTRIBUTE = "Lean.Parser.Command.attribute"
_VARIABLE = "Lean.Parser.Command.variable"
_INCLUDE = "Lean.Parser.Command.include"
_OMIT = "Lean.Parser.Command.omit"
_INST_BINDER = "Lean.Parser.Term.instBinder"
_IMPORT = "Lean.Parser.Module.import"

# Commands that only print or check something (`#check`, `#print axioms`).
_DIAGNOSTIC_ATOMS = frozenset({"#check", "#print", "#reduce", "#synth"})
# Commands that run code; they stay unless they name a deleted declaration.
_EVAL_ATOMS = frozenset({"#eval", "#eval!", "#guard_expr", "#guard"})


def usable(analysis: FileSyntax | None, text: str) -> bool:
    """Whether ``analysis`` describes ``text`` and can be trusted for edits.

    A declaration that failed to elaborate here (it built in the real build)
    means this elaboration differs from the real one; later commands may then
    have resolved names differently, so the whole file keeps the regex path.
    """

    return (
        analysis is not None
        and analysis.mode == "full"
        and analysis.text == text
        and bool(analysis.commands)
        and not any(command.error for command in analysis.commands if command.declaration)
    )


def header_stub(analysis: FileSyntax | None, text: str) -> str | None:
    """The module header as Lean parsed it, as a dead module's stub.

    The lines holding `module`, `prelude` and each `import` (in any form,
    over several lines) are kept verbatim, CRLF line ends included
    (PALOMAR-2026-10-13-000008 lost its `module\\r`); comments and blank lines
    between them go, as in `strip.import_only_stub`. None when the analysis
    does not describe ``text``.
    """

    if analysis is None or analysis.text != text or analysis.header is None:
        return None
    spans = [
        node.span for node in analysis.header.walk()
        if node.span and (node.kind == _IMPORT or node.atom in ("module", "prelude"))
    ]
    offsets = _Offsets(text)
    lines = sorted({
        line
        for start, end in spans
        for line in range(offsets.line_column(start)[0], offsets.line_column(end)[0] + 1)
    })
    source_lines = text.split("\n")
    kept = [source_lines[line - 1] for line in lines]
    return "\n".join(kept) + ("\n" if kept else "")


class _Owners:
    """The project declaration a constant belongs to.

    A constant without a source range (`Foo.rec`, `Foo.mk.injEq`, a `match`
    auxiliary) belongs to its nearest ranged prefix, as in the graph dump.
    """

    def __init__(self, declarations: set[str]) -> None:
        self.declarations = declarations
        self.cache: dict[str, str | None] = {}

    def __call__(self, constant: str) -> str | None:
        if constant not in self.cache:
            name = constant
            while name and name not in self.declarations:
                name = name.rpartition(".")[0]
            self.cache[constant] = name or None
        return self.cache[constant]


@dataclass
class Context:
    """What the whole plan knows, shared by every file's edits."""

    project_declarations: set[str]
    deleted: set[str]
    kept: set[str]
    imported_namespaces: set[str]
    custom_commands: frozenset[str] = frozenset()
    owners: _Owners = field(init=False)
    _members: dict[str, set[str]] | None = field(default=None, init=False)

    def __post_init__(self) -> None:
        self.owners = _Owners(self.project_declarations)

    def namespace_members(self, namespace: str) -> set[str]:
        """Project declarations inside ``namespace`` (private ones by source name)."""

        if self._members is None:
            self._members = {}
            for name in self.project_declarations:
                _module, display = _strip._private_owner_and_display(name)
                parts = display.split(".")
                for end in range(1, len(parts)):
                    self._members.setdefault(".".join(parts[:end]), set()).add(name)
        return self._members.get(namespace, set())

    def is_deleted(self, constant: str) -> bool:
        owner = self.owners(constant)
        return owner is not None and owner in self.deleted


def _parts(node: Node) -> list[Node]:
    """The commands an ``A in B`` chain combines: prefixes first, body last."""

    if node.kind == _IN and len(node.children) >= 3:
        return _parts(node.children[0]) + _parts(node.children[2])
    return [node]


def _unwrap(node: Node) -> Node:
    """The command a ``#guard_msgs in`` wraps."""

    while node.kind == _GUARD_MSGS:
        inner = [child for child in node.children if child.command]
        if not inner:
            break
        node = inner[-1]
    return node


def _within(span: tuple[int, int], start: int, end: int) -> bool:
    return span[0] <= start and end <= span[1]


def _overlaps(span: tuple[int, int], start: int, end: int) -> bool:
    return start < span[1] and span[0] < end


@dataclass
class _CommandPlan:
    remove: bool = False
    # Inline removals (identifiers, binders) and prefix removals (`… in`).
    inline: list[tuple[int, int]] = field(default_factory=list)
    prefixes: list[tuple[int, int]] = field(default_factory=list)


class _FilePlanner:
    def __init__(self, context: Context, analysis: FileSyntax, visible_kept: set[str]) -> None:
        self.context = context
        self.analysis = analysis
        self.text = analysis.text
        self.visible_kept = visible_kept
        self.removed_binders: set[tuple[int, int]] = set()
        self.stats = dict.fromkeys(_strip._DEAD_COMMAND_STAT_KEYS, 0)
        self.custom_head = _strip._check_command_head(context.custom_commands)

    # -- what a span denotes -------------------------------------------------

    def _constants(self, command: Command, span: tuple[int, int]) -> set[str]:
        return {
            constant
            for reference in command.references
            if _within(span, reference.start, reference.end)
            for constant in reference.constants
        }

    def _names_deleted(self, command: Command, node: Node) -> bool:
        """Whether a term or identifier in ``node`` denotes a deleted declaration.

        Elaborated terms answer exactly. An identifier Lean did not elaborate
        (a command's own argument, or a command that failed here) counts when
        every constant Lean's name resolution offers for it was deleted.
        """

        span = node.span
        if span is None:
            return False
        if any(self.context.is_deleted(c) for c in self._constants(command, span)):
            return True
        covered = [(r.start, r.end) for r in command.references] + [
            (r.start, r.end) for r in command.locals
        ]
        for ident in node.idents():
            if any(_overlaps(other, *ident.span) for other in covered):
                continue
            candidates = [name for name, _fields in ident.globals]
            if candidates and all(self.context.is_deleted(name) for name in candidates):
                return True
        return False

    def _target_deleted(self, command: Command, ident: Node, namespaces: Iterable[str] = ()) -> bool:
        """Whether a command's target identifier names a deleted declaration."""

        constants = self._constants(command, ident.span)
        if not constants and ident.ident is not None:
            # Not elaborated here: resolve the target the way the command does.
            constants = {name for name, fields in ident.globals if not fields}
            constants |= {
                f"{namespace}.{ident.ident}" for namespace in namespaces
                if f"{namespace}.{ident.ident}" in self.context.project_declarations
            }
        return bool(constants) and all(self.context.is_deleted(c) for c in constants)

    def _namespace_dead(self, namespaces: Iterable[str], members_live: set[str]) -> bool:
        """An opened name whose every namespace loses all its declarations.

        ``namespaces`` are the ones Lean's ``resolveNamespace`` found. A
        namespace that also holds imported declarations (or export aliases)
        stays, and so does one the project does not populate.
        """

        namespaces = list(namespaces)
        if not namespaces:
            return False
        members: set[str] = set()
        for namespace in namespaces:
            if namespace in self.context.imported_namespaces:
                return False
            members |= self.context.namespace_members(namespace)
        return bool(members) and not (members & members_live)

    # -- one command ---------------------------------------------------------

    def plan(self, command: Command) -> _CommandPlan:
        plan = _CommandPlan()
        if command.tree is None:
            return plan
        parts = _parts(command.tree)
        for index, part in enumerate(parts):
            body = index == len(parts) - 1
            removals, remove = self._plan_part(command, _unwrap(part), body)
            if remove and body:
                plan.remove = True
                return plan
            if remove:
                following = parts[index + 1].start
                if part.start is not None and following is not None:
                    plan.prefixes.append((part.start, following))
            else:
                plan.inline.extend(removals)
        return plan

    def _plan_part(self, command: Command, part: Node, body: bool) -> tuple[list[tuple[int, int]], bool]:
        atoms = part.atoms()
        first = atoms[0] if atoms else ""
        if part.declaration or part.big:
            return [], False
        if atoms[:2] in (["open", "private"], ["export", "private"]):
            return self._open_private(part)
        if part.kind == _OPEN:
            return self._open(command, part)
        if part.kind == _EXPORT:
            return self._export(command, part)
        if part.kind == _ATTRIBUTE:
            return self._attribute(command, part)
        if part.kind == _VARIABLE:
            return self._variable(command, part)
        if part.kind in (_INCLUDE, _OMIT):
            return self._include_omit(command, part)
        if not body:
            return [], False
        if first in _DIAGNOSTIC_ATOMS:
            self.stats["diagnostics_removed"] += 1
            return [], True
        if first in _EVAL_ATOMS and self._names_deleted(command, part):
            self.stats["evals_removed"] += 1
            return [], True
        if first and self.custom_head.match(first) and self._names_deleted(command, part):
            self.stats["custom_commands_removed"] += 1
            return [], True
        return [], False

    def _open_private(self, part: Node) -> tuple[list[tuple[int, int]], bool]:
        """Batteries' ``open private ids from M``; see `strip._prune_open_private_command`."""

        span = part.span
        if span is None:
            return [], False
        pruned = _strip._prune_open_private_command(
            self.text[span[0]:span[1]], self.context.project_declarations, self.context.deleted,
        )
        if pruned is None:
            return [], False
        if not pruned:
            self.stats["open_commands_removed"] += 1
            return [], True
        self.stats["open_declarations_removed"] += 1
        # Remove exactly the identifiers the pruned command no longer names.
        kept_ids = set(_strip._IDENT_RE.findall(pruned))
        removals = [ident.span for ident in part.idents()
                    if ident.ident not in kept_ids and ident.span]
        return removals, False

    def _open(self, command: Command, part: Node) -> tuple[list[tuple[int, int]], bool]:
        declaration = part.child(1)
        if declaration.kind == _OPEN_SIMPLE:
            names = [node for node in declaration.child(0).children if node.ident is not None]
            dead = [node for node in names if self._namespace_dead(node.namespaces, self.visible_kept)]
            if not dead:
                return [], False
            self.stats["open_namespaces_removed"] += len(dead)
            if len(dead) == len(names):
                self.stats["open_commands_removed"] += 1
                return [], True
            return [node.span for node in dead], False
        if declaration.kind == _OPEN_ONLY:
            namespaces = declaration.child(0).namespaces
            targets = [node for node in declaration.child(2).children if node.ident is not None]
            dead = [node for node in targets if self._target_deleted(command, node, namespaces)]
            if not dead:
                return [], False
            self.stats["open_declarations_removed"] += len(dead)
            if len(dead) == len(targets):
                self.stats["open_commands_removed"] += 1
                return [], True
            return [node.span for node in dead], False
        # `open scoped`, `hiding` and `renaming` stay: they act on notation and
        # name visibility the declaration graph does not see.
        return [], False

    def _export(self, command: Command, part: Node) -> tuple[list[tuple[int, int]], bool]:
        namespaces = part.child(1).namespaces
        targets = [node for node in part.child(3).children if node.ident is not None]
        dead = [node for node in targets if self._target_deleted(command, node, namespaces)]
        members: set[str] = set()
        for namespace in namespaces:
            members |= self.context.namespace_members(namespace)
        if len(dead) == len(targets) or (members and not (members & self.context.kept)):
            self.stats["exports_removed"] += 1
            return [], True
        if not dead:
            return [], False
        self.stats["export_targets_removed"] += len(dead)
        return [node.span for node in dead], False

    def _attribute(self, command: Command, part: Node) -> tuple[list[tuple[int, int]], bool]:
        targets = [node for node in part.child(4).children if node.ident is not None]
        dead = [node for node in targets if self._target_deleted(command, node)]
        if not dead:
            return [], False
        self.stats["attribute_targets_removed"] += len(dead)
        if len(dead) == len(targets):
            self.stats["attribute_commands_removed"] += 1
            return [], True
        return [node.span for node in dead], False

    def _binder_in_scope(self, command: Command, name: str, own: list[Binder]) -> Binder | None:
        for binder in reversed([*command.variables, *own]):
            if name in binder.names:
                return binder
        return None

    def _variable(self, command: Command, part: Node) -> tuple[list[tuple[int, int]], bool]:
        """Binders whose type denotes a deleted declaration, or a binder removed before.

        The constants are the ones Lean chose: an overloaded name denotes the
        alternative that elaborated, so a binder goes exactly when the
        declaration it used went (PALOMAR-2026-10-07-000001 keeps `hmatch`,
        whose `ownerEquiv` survived; PALOMAR-2026-08-27-000009 drops `hW`,
        whose `FunctionField.IsCanonical` did not).
        """

        binders = [node for node in part.child(1).children if node.span and node.kind]
        own: list[Binder] = []
        removed = 0
        for node in binders:
            name_nodes = [child for child in node.child(1).walk() if child.ident is not None]
            names = tuple(child.ident for child in name_nodes if child.ident)
            binder = Binder(node.start, node.end, names)
            name_spans = [child.span for child in name_nodes if child.span]
            dead = any(self.context.is_deleted(c) for c in self._constants(command, node.span))
            for local in command.locals:
                if dead:
                    break
                if not _within(node.span, local.start, local.end):
                    continue
                if any(_overlaps(span, local.start, local.end) for span in name_spans):
                    continue
                target = self._binder_in_scope(command, local.name, own)
                dead = target is not None and (target.start, target.end) in self.removed_binders
            if not dead and command.error:
                dead = self._names_deleted(command, node)
            if dead:
                self.removed_binders.add((binder.start, binder.end))
                removed += 1
            own.append(binder)
        if not removed:
            return [], False
        self.stats["variable_binders_removed"] += removed
        if removed == len(binders):
            self.stats["variable_commands_removed"] += 1
            return [], True
        return [(b.start, b.end) for b in own if (b.start, b.end) in self.removed_binders], False

    def _include_omit(self, command: Command, part: Node) -> tuple[list[tuple[int, int]], bool]:
        arguments = [node for node in part.child(1).children if node.span]
        dead = []
        for node in arguments:
            if node.ident is not None:
                binder = self._binder_in_scope(command, node.ident, [])
                if binder is not None and (binder.start, binder.end) in self.removed_binders:
                    dead.append(node)
            elif node.kind == _INST_BINDER and self._names_deleted(command, node):
                dead.append(node)
        if not dead:
            return [], False
        self.stats["include_omit_names_removed"] += len(dead)
        if len(dead) == len(arguments):
            self.stats["include_omit_commands_removed"] += 1
            return [], True
        return [node.span for node in dead], False


# -- text edits ----------------------------------------------------------------

_MARK = "\x00"


def _inline_removal(text: str, start: int, end: int) -> tuple[int, int]:
    """Widen an identifier or binder removal over one adjacent run of blanks."""

    widened = end
    while widened < len(text) and text[widened] in " \t":
        widened += 1
    if widened > end:
        return start, widened
    while start > 0 and text[start - 1] in " \t":
        start -= 1
    return start, end


def _edited_command(text: str, start: int, end: int, plan: _CommandPlan) -> str:
    """The command's new text after its inline and prefix removals.

    Lines an inline removal emptied disappear, and a line left holding only
    the closing parenthesis joins the line above it.
    """

    edits = [(*_inline_removal(text, s, e), _MARK) for s, e in plan.inline]
    edits += [(s, e, "") for s, e in plan.prefixes]
    out = text[start:end]
    for s, e, replacement in sorted(edits, reverse=True):
        out = out[: s - start] + replacement + out[e - start:]
    lines: list[str] = []
    for line in out.split("\n"):
        if _MARK not in line:
            lines.append(line)
            continue
        line = line.replace(_MARK, "").rstrip()
        if not line.strip():
            continue
        if line.strip() == ")" and lines:
            lines[-1] = lines[-1].rstrip() + ")"
            continue
        lines.append(line)
    return "\n".join(lines)


def _removal(text: str, start: int, end: int) -> tuple[int, int]:
    """A whole command's removal, widened to its lines when it has them alone.

    A trailing ``--`` comment on its last line goes with it, as with the
    line-based deletion.
    """

    line_start = text.rfind("\n", 0, start) + 1
    line_end = text.find("\n", end)
    line_end = len(text) if line_end < 0 else line_end
    before, after = text[line_start:start], text[end:line_end]
    if not before.strip() and (not after.strip() or after.lstrip().startswith("--")):
        return line_start, min(line_end + 1, len(text))
    while end < len(text) and text[end] in " \t":
        end += 1
    return start, end


def _command_index(commands: list[Command]) -> tuple[list[int], list[Command]]:
    ordered = sorted(commands, key=lambda command: command.start)
    return [command.start for command in ordered], ordered


def _containing(starts: list[int], ordered: list[Command], offset: int) -> Command | None:
    index = bisect_right(starts, offset) - 1
    while index >= 0:
        command = ordered[index]
        if command.start <= offset <= command.end:
            return command
        if command.end < offset:
            return None
        index -= 1
    return None


def declaration_commands(
    analysis: FileSyntax, rows: list[dict],
) -> tuple[set[int], set[str]] | None:
    """The commands to delete for ``rows`` and the declarations they hold.

    A command goes when it holds a dropped declaration and no kept one: its
    attributes, doc comment, ``… in`` prefixes and ``mutual … end`` go with
    it, and a ``namespace``/``section``/``end`` never does. Rows are placed by
    their end position. None when a dropped row lies in no command, so the
    caller keeps the line-based path for the file.
    """

    offsets = _Offsets(analysis.text)
    starts, ordered = _command_index(
        [command for command in analysis.commands if command.kind != "Lean.Parser.Command.eoi"]
    )
    by_command: dict[int, list[dict]] = {}
    for row in rows:
        if row.get("start_line") is None or row.get("end_line") is None:
            continue
        end = offsets.offset(int(row["end_line"]), int(row.get("end_col") or 0))
        command = _containing(starts, ordered, end)
        if command is None:
            start = offsets.offset(int(row["start_line"]), int(row.get("start_col") or 0))
            command = _containing(starts, ordered, start)
        if command is None:
            if row.get("keep"):
                continue
            return None
        by_command.setdefault(command.index, []).append(row)
    removed = {
        index for index, members in by_command.items()
        if not any(row.get("keep") for row in members)
    }
    names = {str(row["name"]) for index in removed for row in by_command[index]}
    return removed, names


def plan_file(
    analysis: FileSyntax,
    rows: list[dict],
    context: Context,
    *,
    visible_kept: set[str],
    removed_commands: set[int] | None = None,
) -> tuple[str, dict[str, int]] | None:
    """Strip one analysed file: its dropped declarations and dead commands.

    ``rows`` are this file's declaration rows with their ``keep`` flags
    (empty for a file whose declarations all stay). Returns the new text and
    the dead-command statistics, or None when the analysis cannot place a
    dropped declaration (the caller then uses the regex path).
    """

    text = analysis.text
    if removed_commands is None:
        placed = declaration_commands(analysis, rows)
        if placed is None:
            return None
        removed_commands = placed[0]
    planner = _FilePlanner(context, analysis, visible_kept)
    edits: list[tuple[int, int, str]] = []
    for command in sorted(analysis.commands, key=lambda command: command.start):
        if command.kind == "Lean.Parser.Command.eoi":
            continue
        if command.index in removed_commands:
            edits.append((*_removal(text, command.start, command.end), ""))
            continue
        if command.declaration:
            continue
        plan = planner.plan(command)
        if plan.remove:
            edits.append((*_removal(text, command.start, command.end), ""))
        elif plan.inline or plan.prefixes:
            edits.append((command.start, command.end,
                          _edited_command(text, command.start, command.end, plan)))
    if not edits:
        return text, planner.stats
    out = text
    previous_start = len(text) + 1
    for start, end, replacement in sorted(edits, reverse=True):
        if end > previous_start:
            return None  # overlapping edits: not a layout this planner understands
        out = out[:start] + replacement + out[end:]
        previous_start = start
    return _strip._collapse_blank_runs(out), planner.stats
