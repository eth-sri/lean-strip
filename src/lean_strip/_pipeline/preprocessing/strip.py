"""Pure source-text planning for module- and declaration-level stripping.

Given a Lean source file's text and the declaration ranges emitted by the
`.olean` declaration reader (see preprocessing/olean.py), `strip_source` removes
the source spans of every declaration NOT in the keep-set, leaving all
non-declaration scaffolding (imports, `open`, `namespace`/`end`, `variable`,
`notation`/`macro`, free-floating comments) untouched.

Everything here is pure text -> text. engine.py owns all I/O: it builds the
project, writes the planned sources back, and certifies the result with the
final builds.

Key facts about the ranges (verified empirically against the pinned toolchains):
  * Line numbers are 1-based; the command range is [start_line, end_line]
    inclusive.
  * The range INCLUDES a leading docstring (`/-- ... -/`), so deleting a
    dropped decl's span removes its docstring too — no orphans.
  * A standalone `@[attr]` line ABOVE the keyword is NOT part of the range, so
    we extend a deletion upward over such lines.
  * Range-less decls (auto-generated `.rec`/`.ctor`/`.match_n`/...) carry
    start_line is None and are never deleted (they have no source).
"""

from __future__ import annotations

import difflib
import functools
import re
from collections.abc import Callable, Iterable, Iterator
from typing import Any

from .identity import DeclId, Dependencies, DeclarationIndex, decl_id, identity_rows

DeclRange = dict[str, Any]

# Lines that decorate the *following* declaration but sit ABOVE the keyword and
# are NOT part of the decl's command range, so a deletion of that decl must
# consume them too — otherwise they dangle and corrupt parsing:
#   * a standalone attribute line: `@[simp]`, `@[simp, norm_cast]`
#   * a command-prefix modifier ending in `in`: `set_option ... in`,
#     `open ... in`, `attribute [...] ... in` (these apply to the next command;
#     left orphaned they swallow the subsequent `end`/decl and desync scoping).
_ATTR_ONLY_RE = re.compile(r"^\s*@\[[^\]]*\]\s*$")
# Lean identifier characters, exactly as Lean's lexer defines them
# (`isLetterLike`, `isIdFirst`, `isIdRest`, `isSubScriptAlnum` in
# Init/Meta/Defs.lean; unchanged from v4.28 through v4.34). Everything else,
# such as `‖`, `⟨`, `⦃`, `×`, `²` or arrows, is syntax. A class that admits
# those glues a delimiter onto the neighbouring name (`‖f‖` becomes one token
# that resolves to nothing), which loses the dependency on `f`.
_LETTER_LIKE = (
    "\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u017F"  # Latin-1 letters but × ÷, Latin Extended-A
    "\u0391-\u039F\u03A1\u03A2\u03A4-\u03A9"   # upper Greek but Π Σ
    "\u03B1-\u03BA\u03BC-\u03C9"               # lower Greek but λ
    "\u03CA-\u03FB"                            # Coptic
    "\u1F00-\u1FFE"                            # Greek Extended
    "\u2100-\u214F"                            # Letterlike Symbols
    "\U0001D49C-\U0001D59F"                    # script, double-struck, Fraktur
)
_ID_FIRST = "A-Za-z_" + _LETTER_LIKE
_ID_REST = _ID_FIRST + "0-9'!?" + "\u2080-\u2089\u2090-\u209C\u1D62-\u1D6A\u2C7C"
# One identifier, possibly dotted (`Nat.succ`, `h.1`, `hx.le`).
_LEAN_COMMAND_NAME_PATTERN = f"[{_ID_FIRST}][{_ID_REST}.]*"
_IDENT_RE = re.compile(_LEAN_COMMAND_NAME_PATTERN)
# `` `Foo.bar `` and ``` ``Foo.bar ```: a Lean `Name` literal.
_QUOTED_NAME_RE = re.compile(rf"(?<![{_ID_REST}`])``?({_LEAN_COMMAND_NAME_PATTERN})")
# End of a command keyword. `\b` is wrong here: `'`, `!` and `?` continue a
# Lean identifier, so `\bsection\b` matches the structure field `section'`.
_KW_END = rf"(?![{_ID_REST}])"

# Command-prefix modifiers that scope to the *next* command via a trailing
# `in` (so they sit above the decl keyword, outside its range). Anchored on the
# keyword so docstring/comment prose merely ending in the word "in" is ignored.
_PREFIX_IN_RE = re.compile(
    r"^\s*(set_option|open|attribute|omit|include|variable|universe|#guard_msgs)"
    + _KW_END
    + r"[\s\S]*\bin\s*$"
)
_PREFIX_START_RE = re.compile(
    r"^\s*(set_option|open|attribute|omit|include|variable|universe|#guard_msgs)"
    + _KW_END
)


# Lean 4 mangles a `private` declaration to `_private.<Module>.0.<SourceName>`.
# The module component is a *visibility constraint*: a private declaration is
# inaccessible outside the module that defines it, so it must never enter
# another module's candidate set. The trailing component is what source text
# actually writes.
_PRIVATE_KERNEL_NAME_RE = re.compile(
    r"^_private\.((?:(?:«[^»]*»|[^.«»]+)\.)+?)[0-9]+\.(.+)$"
)


def _private_owner_and_display(name: str) -> tuple[str | None, str]:
    """Split a kernel name into (private-defining module or None, source name)."""

    if not name.startswith("_private."):
        return None, name
    match = _PRIVATE_KERNEL_NAME_RE.match(name)
    if match is None:
        return None, name
    return match.group(1).rstrip("."), match.group(2)



# A binder group such as `(hF : IsSmoothBounded F)` or `{x y : Foo}`. Lean's
# generalised field notation resolves `hF.memLp` through the *type* of `hF`, so
# a scan that ignores binder types cannot see that reference at all. Binders
# written in the declaration's own source are recoverable without elaboration.
_BINDER_GROUP_RE = re.compile(
    r"[(\{\[⦃]\s*([^:()\{\}\[\]⦃⦄]+?)\s*:\s*([^()\{\}\[\]⦃⦄]+?)\s*[)\}\]⦄]"
)


def _binder_head_types(span: str) -> dict[str, str]:
    """Map binder names in one declaration's source to their type's head name."""

    out: dict[str, str] = {}
    for binder_part, type_part in _BINDER_GROUP_RE.findall(span):
        head = _IDENT_RE.match(type_part.strip())
        if head is None:
            continue
        for binder in binder_part.split():
            if _IDENT_RE.fullmatch(binder):
                out.setdefault(binder, head.group(0))
    return out


class _VisibleNames:
    """The project declarations visible from one module, by index key.

    ``by_display``, ``by_last`` and ``by_suffix`` answer ``.get`` like a dict
    from key to the set of visible names, and ``name in view`` tests one name.
    """

    def __init__(self, names: "_ProjectNames", module: str, closure: set[str]) -> None:
        self.module = module
        self._names = names
        self._closure = closure
        self._visible: dict[str, bool] = {}
        self.by_display = _VisibleIndex(names.by_display, self)
        self.by_last = _VisibleIndex(names.by_last, self)
        self.by_suffix = _VisibleIndex(names.by_suffix, self)

    def __contains__(self, name: object) -> bool:
        if not isinstance(name, str):
            return False
        known = self._visible.get(name)
        if known is None:
            modules = self._names.modules_of.get(name, ())
            owner = self._names.private_owner.get(name)
            # An unreachable private homonym would make a real same-module
            # reference look ambiguous.
            known = (owner is None or owner == self.module) and any(
                module in self._closure for module in modules
            )
            self._visible[name] = known
        return known


class _VisibleIndex:
    """One project-wide name index, filtered to one module's visible names."""

    def __init__(self, index: dict[str, list[str]], visible: _VisibleNames) -> None:
        self._index = index
        self._visible = visible
        self._cache: dict[str, frozenset[str]] = {}

    def get(self, key: str, default: Any = None) -> Any:
        hits = self._cache.get(key)
        if hits is None:
            hits = frozenset(name for name in self._index.get(key, ()) if name in self._visible)
            self._cache[key] = hits
        return hits if hits else default


class _ProjectNames:
    """Every project declaration indexed once by its display name, its last
    component and every dotted suffix of the display name.

    A module sees the names of its transitive project-import closure. Indexing
    that set separately for every module costs memory proportional to the sum
    of all closures, which a project of ten thousand modules does not have
    (PALOMAR-2026-10-21-000025); the shared index is filtered per lookup.
    """

    def __init__(self, names_by_module: dict[str, set[str]]) -> None:
        self.modules_of: dict[str, list[str]] = {}
        for module, module_names in names_by_module.items():
            for name in module_names:
                self.modules_of.setdefault(name, []).append(module)
        self.private_owner: dict[str, str] = {}
        self.by_display: dict[str, list[str]] = {}
        self.by_last: dict[str, list[str]] = {}
        self.by_suffix: dict[str, list[str]] = {}
        for name in self.modules_of:
            owner, display = _private_owner_and_display(name)
            if owner is not None:
                self.private_owner[name] = owner
            self.by_display.setdefault(display, []).append(name)
            self.by_last.setdefault(display.rsplit(".", 1)[-1], []).append(name)
            for index, char in enumerate(display):
                if char == "." and index + 1 < len(display):
                    self.by_suffix.setdefault(display[index + 1 :], []).append(name)

    def visible_from(self, module: str, closure: set[str]) -> _VisibleNames:
        return _VisibleNames(self, module, closure)


def _enclosing_declarations(file_decls: list[DeclRange]) -> list[list[str]]:
    """For each declaration of one file, the other names whose source range
    strictly contains its range (an identical range does not count)."""

    spans = [
        (
            (int(decl["start_line"]), int(decl.get("start_col") or 0)),
            (int(decl["end_line"]), int(decl.get("end_col") or 0)),
        )
        for decl in file_decls
    ]
    if any(end < start for start, end in spans):
        # The sweep below assumes well-formed ranges; compare every pair.
        return [
            [
                outer["name"]
                for outer, (outer_start, outer_end) in zip(file_decls, spans)
                if outer["name"] != child["name"]
                and outer_start <= child_start
                and child_end <= outer_end
                and (outer_start, outer_end) != (child_start, child_end)
            ]
            for child, (child_start, child_end) in zip(file_decls, spans)
        ]
    members: dict[tuple[tuple[int, int], tuple[int, int]], list[int]] = {}
    for index, span in enumerate(spans):
        members.setdefault(span, []).append(index)
    # By start, widest first: every range that contains a span comes before
    # it, and a range that ends before a span starts contains nothing later.
    ordered = sorted(members, key=lambda span: (span[0], -span[1][0], -span[1][1]))
    containers: dict[tuple[tuple[int, int], tuple[int, int]], list[tuple[tuple[int, int], tuple[int, int]]]] = {}
    open_spans: list[tuple[tuple[int, int], tuple[int, int]]] = []
    for span in ordered:
        start, end = span
        open_spans = [other for other in open_spans if other[1] >= start]
        containers[span] = [other for other in open_spans if other[1] >= end]
        open_spans.append(span)
    return [
        [
            file_decls[outer]["name"]
            for container in containers[span]
            for outer in members[container]
            if file_decls[outer]["name"] != child["name"]
        ]
        for child, span in zip(file_decls, spans)
    ]


def augment_deps_with_source(
    decls: list[DeclRange],
    deps: Dependencies,
    originals: dict[str, str],
    mod_path: dict[str, str],
    *,
    ambiguities: list[dict[str, Any]] | None = None,
) -> Dependencies:
    """Add dependency edges from SOURCE-level identifier references.

    `foldConsts` over the elaborated term misses declarations that a decl needs
    only to *elaborate* (lemmas named in `simp`/`rw`, dot-notation projections,
    `open`ed helpers) because they don't survive into the final term. Those names
    do appear textually in the decl's source, so we add an edge for every source
    identifier that resolves to a *visible* project decl by full name, or
    unambiguously by last component (e.g. `b.fivefold` ->
    `Foo.Ball.fivefold` when that's the only visible `*.fivefold`).
    Visibility is the source module plus its transitive project imports.
    Comments/docstrings are masked first to avoid keeping things merely
    mentioned in prose.
    """
    names_by_module: dict[str, set[str]] = {}
    for decl in decls:
        names_by_module.setdefault(decl["module"], set()).add(decl["name"])

    # Text is only meaningful in the environment in which its source module
    # elaborates. Resolving an unqualified token against *every* project
    # declaration creates false cross-branch edges: an obsolete module merely
    # imported by an umbrella can otherwise keep itself alive because it owns
    # the project's only declaration with that last component. Mirror Lean's
    # module visibility instead: a declaration may name declarations from its
    # own module and its transitive project-import closure.
    source_root = derive_source_root(mod_path)
    import_graph = (
        build_module_import_graph(
            originals,
            source_root,
            known_module_paths=mod_path,
        )[0]
        if source_root is not None
        else {}
    )
    names = _ProjectNames(names_by_module)
    source_lines_by_path: dict[
        str,
        tuple[
            list[str],
            list[str],
            dict[int, str],
            dict[int, tuple[str, ...]],
        ],
    ] = {}

    # One module at a time, so that only one module's view of the visible
    # names and one module's source lines are alive at once. The edges found
    # are applied in declaration order afterwards.
    indexes_by_module: dict[str, list[int]] = {}
    for index, decl in enumerate(decls):
        indexes_by_module.setdefault(decl["module"], []).append(index)
    token_edges: dict[int, set[str]] = {}
    quoted_edges: dict[int, list[str]] = {}
    # A quoted name is matched against every project declaration (see below).
    all_names = {str(decl["name"]) for decl in decls}
    view: _VisibleNames | None = None
    for index in [index for indexes in indexes_by_module.values() for index in indexes]:
        d = decls[index]
        if view is not None and view.module != d["module"]:
            view = None
            source_lines_by_path.clear()
        if d["start_line"] is None:
            continue
        path = mod_path.get(d["module"])
        text = originals.get(path) if path else None
        if not text:
            continue
        cached_lines = source_lines_by_path.get(path)
        if cached_lines is None:
            namespace_contexts, opened_namespaces = (
                _source_namespace_resolution_contexts(text)
            )
            cached_lines = (
                text.split("\n"),
                _mask_comments_preserve_layout(text).split("\n"),
                namespace_contexts,
                opened_namespaces,
            )
            source_lines_by_path[path] = cached_lines
        lines, code_lines, namespace_contexts, opened_namespaces = cached_lines
        # Include a scoped ``attribute [...] target in`` prefix in the
        # following declaration's source evidence. Its target is needed only
        # when that declaration survives, so this creates an edge rather than
        # a global root.
        start = _extend_up(
            code_lines, min(len(code_lines), max(1, int(d["start_line"])))
        )
        span = "\n".join(lines[start - 1: d["end_line"]])
        span = _mask_comments_preserve_layout(span)
        edges = token_edges[index] = set()
        if view is None:
            # `_closure` always contains `module` itself, even without a graph.
            view = names.visible_from(d["module"], _closure(import_graph, {d["module"]}))
        visible, by_last, by_suffix, by_display = view, view.by_last, view.by_suffix, view.by_display
        declaration_line = min(
            len(code_lines), max(1, int(d["start_line"]))
        )
        lexical_namespace = namespace_contexts.get(declaration_line, "")
        lexical_opens = opened_namespaces.get(declaration_line, ())
        binder_types = _binder_head_types(span)
        for tok in _IDENT_RE.findall(span):
            # Lean resolves an identifier through its enclosing namespaces
            # from innermost outwards and falls back to the root name last, so
            # the bare name must NOT be tried first: inside `namespace N` the
            # token `A.b` denotes `N.A.b` whenever that exists, even when an
            # unrelated root-level `A.b` is also in scope. Trying the bare name
            # first silently attributes the edge to a homonym in another
            # module. `_namespace_name_candidates` already yields Lean's order
            # and ends with the bare token. Lookups go through display names so
            # a `private` declaration, written in source under its plain name,
            # maps back to the kernel name the declaration graph uses.
            # A local binder shadows any global of the same name, so a token
            # that *is* a binder in this declaration never denotes a project
            # declaration: `lemma f (c : ℂ)` must not depend on a global `c`.
            if tok in binder_types:
                continue
            resolved_name: str | None = None
            self_reference = False
            for candidate in _namespace_name_candidates(tok, lexical_namespace):
                hits = by_display.get(candidate, set())
                if not hits:
                    continue
                if hits == {d["name"]}:
                    self_reference = True
                    break
                unambiguous = hits - {d["name"]}
                if len(unambiguous) == 1:
                    resolved_name = next(iter(unambiguous))
                    break
                break
            if self_reference:
                continue
            if resolved_name is None and tok in visible:
                # Namespace-qualified resolution was ambiguous or absent; the
                # token is itself a full declaration name, so use it.
                resolved_name = None if tok == d["name"] else tok
                if resolved_name is None:
                    continue
            if resolved_name is not None:
                edges.add(resolved_name)
                continue
            opened_hits = {
                resolved
                for namespace in lexical_opens
                for resolved in by_display.get(f"{namespace}.{tok}", set())
                if resolved != d["name"]
            }
            if len(opened_hits) == 1:
                edges.add(next(iter(opened_hits)))
                continue
            # Generalised field notation: `hF.memLp` where `hF` is a binder of
            # type `IsSmoothBounded F` denotes `IsSmoothBounded.memLp`. The
            # receiver's type is written in the declaration's own signature, so
            # this particular type-directed reference needs no elaborator.
            if "." in tok:
                receiver, _, field = tok.partition(".")
                type_head = binder_types.get(receiver)
                if type_head and field:
                    for candidate in _namespace_name_candidates(
                        type_head, lexical_namespace
                    ):
                        type_hits = by_display.get(candidate, set())
                        if not type_hits:
                            continue
                        field_hits: set[str] = set()
                        for raw_type in type_hits:
                            _owner, type_display = _private_owner_and_display(
                                raw_type
                            )
                            field_hits |= by_display.get(
                                f"{type_display}.{field}", set()
                            )
                        field_hits -= {d["name"]}
                        if len(field_hits) == 1:
                            edges.add(next(iter(field_hits)))
                        break
            # A source file inside a namespace may use a partially-qualified
            # name (for example ``Tensorial.numIndices`` for
            # ``TensorSpecies.Tensorial.numIndices``). Prefer its unique
            # visible qualified-suffix match before falling back to the final
            # component, which can be ambiguous.
            suffix_cands = by_suffix.get(tok, set()) - {d["name"]}
            if len(suffix_cands) == 1:
                edges.add(next(iter(suffix_cands)))
                continue
            # Lean tactics may print names of range-less generated helpers such
            # as `foo._proof_1_7` or `foo.match_1`. Those constants disappear
            # if the source declaration `foo` is removed, but they are absent
            # from `decls` because the declaration graph intentionally
            # contains only source-backed ranges. Resolve the longest dotted
            # source-backed prefix so an explicit replay-certified tactic rule
            # keeps the command that recreates its generated helper.
            prefix = tok
            while "." in prefix:
                prefix = prefix.rsplit(".", 1)[0]
                # Resolve the prefix the way Lean resolves any identifier:
                # through the enclosing namespaces first, bare name last.
                prefix_hits: set[str] = set()
                for candidate in _namespace_name_candidates(
                    prefix, lexical_namespace
                ):
                    prefix_hits = by_display.get(candidate, set())
                    if prefix_hits:
                        break
                if prefix_hits:
                    unambiguous = prefix_hits - {d["name"]}
                    if len(unambiguous) == 1:
                        edges.add(next(iter(unambiguous)))
                    break
            else:
                prefix = ""
            if prefix:
                continue
            cands = by_last.get(tok.rsplit(".", 1)[-1])
            if cands and len(cands) == 1:
                c = next(iter(cands))
                if c != d["name"]:
                    edges.add(c)

        # A quoted name (`` `Foo.bar `` or ``` ``Foo.bar ```) is looked up when
        # the code runs, in the environment of whichever module uses it, not of
        # the module that wrote it: `resolveConst? `FourColor.contractProg`
        # inside a command elaborator (PALOMAR-2026-09-27-000005). Exact full
        # names are matched against every project declaration, without the
        # visibility filter.
        start_line = int(d["start_line"])
        code_span = "\n".join(code_lines[start_line - 1 : int(d["end_line"])])
        for match in _QUOTED_NAME_RE.finditer(code_span):
            quoted = match.group(1).removeprefix("_root_.")
            # ``Foo resolves through the enclosing namespaces when it is written.
            line = start_line + code_span.count("\n", 0, match.start())
            candidates = (_namespace_name_candidates(quoted, namespace_contexts.get(line, ""))
                          if match.group(0).startswith("``") else [quoted])
            hit = next((candidate for candidate in candidates if candidate in all_names), None)
            if hit is not None and hit != d["name"]:
                quoted_edges.setdefault(index, []).append(hit)

    out: dict[DeclId, set[str]] = {}
    for index, d in enumerate(decls):
        if index in token_edges:
            out.setdefault(decl_id(d), set()).update(token_edges[index])

    # Lean exposes source-backed local declarations such as a `let rec`
    # helper as separate constants whose ranges are strictly nested inside the
    # enclosing command. The local constant can occur in the dependency graph
    # independently, but its source cannot survive without the outer command's
    # header. Make that syntactic ownership explicit in the graph so retaining
    # a local helper always retains every declaration command containing it.
    ranged_by_path: dict[str, list[DeclRange]] = {}
    for decl in decls:
        if decl.get("start_line") is None or decl.get("end_line") is None:
            continue
        path = mod_path.get(decl["module"])
        if path and path in originals:
            ranged_by_path.setdefault(path, []).append(decl)

    for file_decls in ranged_by_path.values():
        for child, outers in zip(file_decls, _enclosing_declarations(file_decls)):
            out.setdefault(decl_id(child), set()).update(outers)

    declaration_index = DeclarationIndex(decls)
    result = declaration_index.dependencies(deps)
    current_module = None
    visible_modules: set[str] = set()
    for source, target_names in sorted(out.items()):
        if current_module != source[0]:
            current_module = source[0]
            visible_modules = _closure(import_graph, {current_module})
        for name in sorted(target_names):
            targets = {target for target in declaration_index.resolve(name) if target[0] in visible_modules}
            if len(targets) > 1 and ambiguities is not None:
                ambiguities.append({"source": {"module": source[0], "name": source[1]},
                                    "name": name, "candidates": identity_rows(targets)})
            result.setdefault(source, set()).update(targets - {source})
    for index, d in enumerate(decls):
        source = decl_id(d)
        for name in sorted(set(quoted_edges.get(index, ()))):
            targets = declaration_index.resolve(name)
            if len(targets) > 1 and ambiguities is not None:
                ambiguities.append({"source": {"module": source[0], "name": source[1]},
                                    "name": name, "candidates": identity_rows(targets)})
            result.setdefault(source, set()).update(targets - {source})
    return result


# Every attributed declaration is semantically live for stripping. Lean
# attributes are open-ended: projects define custom simp sets (`delta0_simps`),
# tactic extensions (`tactic`, `positivity`, `delab`), code generators, and
# other environment registrations. Maintaining an allow-list inevitably misses
# new attributes, so any `@[...]` declaration is a root.
_ATTR_TAG_RE = re.compile(r"@\[[^\]]*\]")
# A standalone `attribute [foo] bar` command applying tags to named decls. The
# first-line regex is complemented by continuation handling below.
_SCOPED_ATTRIBUTE_PREFIX = r"(?:scoped[ \t]*\[[^\]\n]*\][ \t]+)?"
_ATTRIBUTE_CMD_RE = re.compile(
    r"^[ \t]*" + _SCOPED_ATTRIBUTE_PREFIX
    + r"attribute\s*\[[^\]]*\]\s*(.*?)\s*$",
    re.MULTILINE,
)


def _attribute_command_payloads(text: str) -> list[str]:
    return [payload for _line, payload in _attribute_command_payloads_with_lines(text)]


def _attribute_command_payloads_with_lines(text: str) -> list[tuple[int, str]]:
    """Return source payloads of standalone ``attribute [...]`` commands.

    The payload excludes the attribute list itself and includes indented
    continuation lines. Commands ending in ``in`` are returned as well: they
    still root their named targets, but callers can distinguish them from
    persistent environment registrations with ``_is_prefix_attribute``.
    Scoped registrations such as ``scoped[Order] attribute [instance] x``
    are persistent too and use the same exact-target policy.
    """

    lines = _mask_comments_preserve_layout(text).split("\n")
    payloads: list[tuple[int, str]] = []
    i = 0
    while i < len(lines):
        match = _ATTRIBUTE_CMD_RE.match(lines[i])
        if not match:
            i += 1
            continue
        payload = [match.group(1)]
        # Lean commonly formats an attribute command as
        #   attribute [fun_prop]
        #     theorem₁
        #     theorem₂
        # Continue through its indented target lines.
        j = i + 1
        while j < len(lines) and lines[j].strip() and lines[j][:1].isspace():
            payload.append(lines[j])
            j += 1
        payloads.append((i + 1, " ".join(payload).strip()))
        i = max(j, i + 1)
    return payloads


def _is_prefix_attribute(payload: str) -> bool:
    """Whether an attribute command is a ``... in`` next-command prefix."""

    return bool(re.search(r"\bin\s*$", payload))

# Declaration kinds whose deps are NOT name-references and so are invisible to
# the closure: typeclass `instance`s (pulled by synthesis at elaboration time)
# and custom-syntax decls — `macro`/`elab`/`syntax`/`notation`/`macro_rules`
# (a surviving proof invokes the syntax, but the call site names no constant).
# Force-keep any decl whose command header is one of these. The keyword may sit
# behind attributes and modifiers (`@[…] noncomputable scoped instance …`).
# `deriving instance C for T` is an instance too; its range is that command, so
# dropping it as unused deletes a `deriving instance … in` prefix the next
# declaration needs. Mixfix notation, unification hints, binder predicates,
# syntax categories and simprocs are likewise used without being named.
_FORCE_KEEP_KINDS = (
    r"deriving\s+instance|instance|macro_rules|macro|elab_rules|elab|syntax|notation"
    r"|infixl|infixr|infix|prefix|postfix|unif_hint|binder_predicate|declare_syntax_cat"
    r"|simproc|dsimproc"
)
_KIND_KW_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:public\s+|private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|"
    r"partial\s+|unsafe\s+)*"
    rf"(?:{_FORCE_KEEP_KINDS}){_KW_END}",
    re.MULTILINE)


def _decls_by_path(
    decls: list[DeclRange], mod_path: dict[str, str]
) -> dict[str | None, list[DeclRange]]:
    """Declarations grouped by their module's source path, in order.

    The detectors below split (and mask) a file once for all of its
    declarations instead of once per declaration, which is quadratic for
    generated files of thousands of declarations (PALOMAR-2026-10-22-000009).
    """

    grouped: dict[str | None, list[DeclRange]] = {}
    for decl in decls:
        grouped.setdefault(mod_path.get(decl["module"]), []).append(decl)
    return grouped


def detect_automation_tagged(
    decls: list[DeclRange],
    originals: dict[str, str],
    mod_path: dict[str, str],
) -> set[str]:
    """Return every project declaration carrying any Lean attribute.

    This includes inline/above `@[...]` annotations and targets of standalone
    `attribute [...] name` commands, including multiline target lists.
    """
    out: set[str] = set()
    # Split and mask each file once: doing it per declaration was quadratic,
    # and a 21,000-declaration project spent hours here (PALOMAR-2026-10-22-000008).
    for path, path_decls in _decls_by_path(decls, mod_path).items():
        if not path or path not in originals:
            continue
        lines = originals[path].split("\n")
        code_lines: list[str] | None = None
        for d in path_decls:
            if d["start_line"] is None:
                continue
            start, end = int(d["start_line"]), min(len(lines), int(d["end_line"]))
            # The decl's own command span (attributes only appear as `@[...]`
            # annotations, never inside tactic blocks, so a body `by simp` is safe).
            # The range includes a leading docstring, so an `@[simp]` between the
            # docstring and keyword is in-span.
            span = "\n".join(lines[start - 1:end])
            if _ATTR_TAG_RE.search(span):
                out.add(d["name"])
                continue
            # A declaration an `attribute` command generates, whose range is the
            # command itself: `attribute [reassoc (attr := simp)] pD_idem` adds
            # `pD_idem_assoc`. Dropping it deleted the command, and with it the
            # simp attribute on `pD_idem` (PALOMAR-2026-10-16-000006).
            payloads = _attribute_command_payloads(span)
            if payloads and not all(_is_prefix_attribute(payload) for payload in payloads):
                out.add(d["name"])
                continue
            # Plus a standalone, possibly multiline `@[...]` block directly
            # above the declaration range (the range may start at its docstring).
            if code_lines is None:
                code_lines = _mask_comments_preserve_layout(originals[path]).split("\n")
            j = start - 1
            while j >= 1 and code_lines[j - 1].strip() == "":
                j -= 1
            if _attribute_block_start(code_lines, j) is not None:
                out.add(d["name"])

    out.update(detect_attribute_command_roots(decls, originals))
    return out


def detect_attribute_command_roots(
    decls: list[DeclRange], originals: dict[str, str]
) -> set[str]:
    """Resolve project declarations named by explicit ``attribute`` commands."""

    name_set = {d["name"] for d in decls}
    by_last: dict[str, list[str]] = {}
    for name in name_set:
        by_last.setdefault(name.rsplit(".", 1)[-1], []).append(name)

    out: set[str] = set()
    for text in originals.values():
        namespaces, opens = _source_namespace_resolution_contexts(text)
        for line_no, payload in _attribute_command_payloads_with_lines(text):
            if _is_prefix_attribute(payload):
                continue
            namespace = namespaces.get(line_no, "")
            for tok in _IDENT_RE.findall(payload):
                # Lean resolves the target through the enclosing namespaces,
                # then the opened ones; a bare-name guess comes last. Several
                # namespaces declaring `ideleClassGroupIsMulCommutative` must not
                # leave `attribute [local instance] ideleClassGroupIsMulCommutative`
                # unrooted (PALOMAR-2026-09-28-000001).
                candidates = _namespace_name_candidates(tok, namespace) + [
                    f"{opened}.{tok}" for opened in opens.get(line_no, ())
                ]
                resolved = next((name for name in candidates if name in name_set), None)
                if resolved is None:
                    by_suffix = by_last.get(tok.rsplit(".", 1)[-1], [])
                    resolved = by_suffix[0] if len(by_suffix) == 1 else None
                if resolved is not None:
                    out.add(resolved)
    return out


# Environment mutations without an explicit attribute target. Their command
# text must survive tree-shaking, but that does not make every declaration in
# the containing file live. Named ``initialize``/``register_option`` commands
# are ordinary source declarations in Lean's range data and are rooted below;
# their bodies then receive the same kernel/iLean/source dependency edges as
# every other declaration.
_OPAQUE_ENVIRONMENT_COMMAND_RE = re.compile(
    r"^[ \t]*(?:"
    r"declare_aesop_rule_sets?|register_simp_attr|register_grind_attr|"
    rf"initialize{_KW_END}|builtin_initialize{_KW_END}|register_option{_KW_END})",
    re.MULTILINE,
)


def detect_attribute_command_files(originals: dict[str, str]) -> set[str]:
    """Return files with persistent, explicit attribute registrations.

    These files must preserve the command text even if all ordinary
    declarations are removed, but their unrelated declarations do *not* need
    to be rooted. ``attribute [...] target in`` is a next-command prefix and
    is deleted atomically with that command by ``strip_source`` instead.
    """

    return {
        path
        for path, text in originals.items()
        if any(
            not _is_prefix_attribute(payload)
            for payload in _attribute_command_payloads(text)
        )
    }


def detect_opaque_environment_command_files(
    originals: dict[str, str],
) -> set[str]:
    """Return files containing non-attribute environment commands."""

    return {
        path
        for path, text in originals.items()
        if _OPAQUE_ENVIRONMENT_COMMAND_RE.search(
            _mask_comments_preserve_layout(text)
        )
    }


def detect_opaque_environment_command_roots(
    decls: list[DeclRange],
    originals: dict[str, str],
    mod_path: dict[str, str],
) -> set[str]:
    """Root source declarations whose range owns an opaque environment command.

    This is declaration-granular: an ``initialize foo := ...`` command keeps
    ``foo`` and the dependencies of its body, not unrelated lemmas elsewhere
    in the file. Commands without a declaration range are preserved as source
    scaffolding by the source-retention plan.
    """

    out: set[str] = set()
    for path, path_decls in _decls_by_path(decls, mod_path).items():
        text = originals.get(path) if path else None
        if text is None:
            continue
        lines = text.split("\n")
        for decl in path_decls:
            if decl.get("start_line") is None or decl.get("end_line") is None:
                continue
            start = max(1, int(decl["start_line"]))
            end = min(len(lines), int(decl["end_line"]))
            span = "\n".join(lines[start - 1:end])
            if _OPAQUE_ENVIRONMENT_COMMAND_RE.search(
                _mask_comments_preserve_layout(span)
            ):
                out.add(decl["name"])
    return out


# A name-based declaration graph has no node for namespaces themselves. If a
# surviving file says `open Project.Namespace`, at least one declaration owned
# by that project-local namespace must remain so Lean can resolve the command.
# Seed the complete matching namespace: this is deterministic and avoids
# iterative guessing about which declaration was intended by a later command.
_OPEN_NAMESPACE_RE = re.compile(
    r"^[ \t]*open(?![ \t]+scoped\b)[ \t]+([^\n]+)", re.MULTILINE
)
# Batteries' `open private a b from M` (and `export private`): opens private
# declarations of module `M` by name suffix.
_OPEN_PRIVATE_HEAD_RE = re.compile(r"^[ \t]*(?:open|export)[ \t]+private" + _KW_END)
_OPEN_PRIVATE_COMMAND_RE = re.compile(
    r"^[ \t]*(?:open|export)[ \t]+private\s+(?P<ids>.*?)\s+from\s+(?P<modules>.*?)\s*\Z", re.DOTALL
)
# `open A B` whose namespace list may continue on deeper-indented lines
# (PALOMAR-2026-09-13-000001).
_OPEN_HEAD_RE = re.compile(r"^[ \t]*open" + _KW_END)
_PLAIN_OPEN_COMMAND_RE = re.compile(
    r"^(?P<indent>[ \t]*)open[ \t]+(?P<names>" + _LEAN_COMMAND_NAME_PATTERN
    + r"(?:\s+" + _LEAN_COMMAND_NAME_PATTERN + r")*)\s*\Z"
)
# `open Foo (a b c)`, whose target list may continue over several lines.
_SELECTIVE_OPEN_HEAD_RE = re.compile(
    r"^(?P<indent>[ \t]*)open[ \t]+(?P<namespace>"
    + _LEAN_COMMAND_NAME_PATTERN
    + r")\s+\("
)
_SELECTIVE_OPEN_COMMAND_RE = re.compile(
    _SELECTIVE_OPEN_HEAD_RE.pattern + r"(?P<targets>[^()]*)\)[ \t]*\Z"
)
# A target list longer than this is not a selective open we understand.
_PARENTHESIZED_MAX_LINES = 64


def _selective_open_spans(code_lines: list[str]) -> dict[int, int]:
    """Zero-based inclusive line spans of ``open Foo (...)`` commands."""

    return _parenthesized_command_spans(code_lines, _SELECTIVE_OPEN_HEAD_RE)


def _parenthesized_command_spans(
    code_lines: list[str], head_re: re.Pattern[str]
) -> dict[int, int]:
    """Spans of commands whose head (matched by ``head_re``, ending at ``(``)
    opens a target list that closes on the same or a later line.

    The closing parenthesis may sit on its own unindented line, which the
    indentation-based ``_continued_command_spans`` would cut off.
    """

    spans: dict[int, int] = {}
    for start, line in enumerate(code_lines):
        head, first = head_re.match(line), start
        if head is None:
            # The list may open on the next line: `open Foo` then `  (a b …)`
            # (PALOMAR-2026-10-11-000001).
            following = code_lines[start + 1] if start + 1 < len(code_lines) else ""
            if not following.lstrip().startswith("("):
                continue
            head = head_re.match(line + "\n" + following)
            if head is None:
                continue
            first = start + 1
            line = following[following.index("(") + 1:]
        else:
            line = line[head.end():]
        rest = [line, *code_lines[first + 1 : first + _PARENTHESIZED_MAX_LINES]]
        for offset, text in enumerate(rest):
            if "(" in text:
                break
            if ")" in text:
                spans[start] = first + offset
                break
    return spans
_NAMESPACE_SCOPE_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+|private[ \t]+)?namespace[ \t]+"
    rf"({_LEAN_COMMAND_NAME_PATTERN})[ \t]*$"
)
# `section`, `noncomputable section`, `@[expose] public section`, `mutual`: each
# is closed by an `end` that must not pop the enclosing namespace.
_NON_NAMESPACE_SCOPE_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:public|private|noncomputable)[ \t]+)*(?:section|mutual)" + _KW_END
)
_SCOPE_END_RE = re.compile(r"^[ \t]*end(?:[ \t]+[^\s]+)?[ \t]*$")


def _namespace_name_candidates(token: str, lexical_namespace: str) -> list[str]:
    """Return Lean-style exact namespace candidates, nearest scope first."""

    if token.startswith("_root_."):
        return [token.removeprefix("_root_.")]
    components = [part for part in lexical_namespace.split(".") if part]
    candidates: list[str] = []
    for length in range(len(components), -1, -1):
        prefix = ".".join(components[:length])
        candidate = f"{prefix}.{token}" if prefix else token
        if candidate not in candidates:
            candidates.append(candidate)
    return candidates


def _source_namespace_resolution_contexts(
    file_text: str, *, strict: bool = False,
) -> tuple[dict[int, str], dict[int, tuple[str, ...]]]:
    """Return lexical namespace and persistent ``open`` context per line.

    This models command-level namespace/section scopes and never guesses from
    arbitrary dotted substrings: such a guess would treat Mathlib's top-level
    ``Topology`` namespace as project-local merely because a project
    declaration lives below ``ForMathlib.Topology``.

    By default an ``open Foo (a)`` or ``open Foo hiding b`` counts as opening
    ``Foo``, which errs towards finding references (keeping more). ``strict``
    counts only plain ``open Foo``, for decisions to remove something.
    """

    code_lines = _mask_comments_preserve_layout(file_text).split("\n")
    namespace = ""
    opened: list[str] = []
    frames: list[tuple[str, list[str]]] = []
    namespaces_by_line: dict[int, str] = {}
    opens_by_line: dict[int, tuple[str, ...]] = {}

    for line_no, code_line in enumerate(code_lines, 1):
        namespaces_by_line[line_no] = namespace
        opens_by_line[line_no] = tuple(opened)

        namespace_scope = _NAMESPACE_SCOPE_RE.match(code_line)
        if namespace_scope:
            frames.append((namespace, list(opened)))
            namespace = _namespace_name_candidates(
                namespace_scope.group(1), namespace
            )[0]
            continue
        if _NON_NAMESPACE_SCOPE_RE.match(code_line):
            frames.append((namespace, list(opened)))
            continue
        if _SCOPE_END_RE.match(code_line):
            if frames:
                namespace, opened = frames.pop()
            continue

        open_command = _OPEN_NAMESPACE_RE.match(code_line)
        if not open_command:
            continue
        following = code_lines[line_no] if line_no < len(code_lines) else ""
        selective = _SELECTIVE_OPEN_HEAD_RE.match(code_line) or (
            _SELECTIVE_OPEN_HEAD_RE.match(code_line + "\n" + following)
            if following.lstrip().startswith("(") else None
        )
        payload = open_command.group(1)
        if not selective:
            indent = len(code_line) - len(code_line.lstrip())
            for following in code_lines[line_no:]:
                if not following.strip() or len(following) - len(following.lstrip()) <= indent:
                    break
                payload += " " + following
        tokens = (
            [selective.group("namespace")]
            if selective
            else _IDENT_RE.findall(payload)
        )
        if "in" in tokens or tokens[:1] == ["private"]:
            continue
        if strict and (selective or "hiding" in tokens or "renaming" in tokens):
            continue
        for token in tokens:
            for candidate in _namespace_name_candidates(token, namespace):
                if candidate not in opened:
                    opened.append(candidate)

    return namespaces_by_line, opens_by_line


def _dotted_prefix_index(declarations: Iterable[str]) -> dict[str, list[str]]:
    """Each name under every text before one of its dots: ``A.B.c`` under
    ``A`` and ``A.B``, so the names that start with ``ns + "."`` are
    ``index[ns]``."""

    index: dict[str, list[str]] = {}
    for name in declarations:
        dot = name.find(".")
        while dot != -1:
            index.setdefault(name[:dot], []).append(name)
            dot = name.find(".", dot + 1)
    return index


def _resolve_project_namespace_members(
    namespace: str,
    declarations: set[str],
    lexical_namespace: str,
    prefix_index: dict[str, list[str]] | None = None,
) -> set[str]:
    """Resolve a namespace only by Lean's exact lexical prefixes.

    ``prefix_index`` (``_dotted_prefix_index(declarations)``) answers the same
    without scanning every declaration, for callers that resolve many.
    """

    for candidate in _namespace_name_candidates(namespace, lexical_namespace):
        if prefix_index is not None:
            members = set(prefix_index.get(candidate, ()))
        else:
            prefix = candidate + "."
            members = {name for name in declarations if name.startswith(prefix)}
        if members:
            return members
    return set()


@functools.lru_cache(maxsize=4)
def _namespace_members(project_declarations: frozenset[str]) -> dict[str, frozenset[str]]:
    """Project declarations under each namespace, by every enclosing namespace.

    Private declarations still create and inhabit their source namespace, so
    they are indexed by their user name but listed by their kernel name: the
    keep-set intersections need the exact identities.
    """

    index: dict[str, set[str]] = {}
    for name in project_declarations:
        _owner, source_name = _private_owner_and_display(name)
        parts = source_name.split(".")
        for length in range(1, len(parts)):
            index.setdefault(".".join(parts[:length]), set()).add(name)
    return {namespace: frozenset(names) for namespace, names in index.items()}


def _namespace_candidates_in_scope(
    namespace: str, lexical_namespace: str, opened_namespaces: tuple[str, ...],
) -> list[str]:
    candidates = _namespace_name_candidates(namespace, lexical_namespace)
    if not namespace.startswith("_root_."):
        candidates += [f"{opened}.{namespace}" for opened in opened_namespaces]
    return list(dict.fromkeys(candidates))


def _resolve_namespace_provenance(
    namespace: str,
    project_declarations: set[str],
    imported_namespaces: set[str],
    lexical_namespace: str,
    opened_namespaces: tuple[str, ...] = (),
) -> tuple[set[str], bool]:
    """Resolve every namespace an ``open`` of ``namespace`` brings into scope.

    Lean opens all existing candidates: each enclosing-namespace prefix and each
    already opened namespace. The project members of all of them are returned,
    so an ``open`` is dead only when none of its candidates keeps a member;
    taking just the nearest candidate deleted
    ``open HilbertRamification.ValuationSubring`` whose live target was reached
    through an earlier ``open RamificationTheory`` (PALOMAR-2026-10-06-000009).

    A namespace may contain both project declarations and imported declarations.
    Such mixed namespaces remain semantically imported even after every project
    extension is stripped, so an ``open`` for them must survive: ``imported`` is
    true when any candidate has imported provenance.
    """

    index = _namespace_members(frozenset(project_declarations))
    members: set[str] = set()
    imported = False
    for candidate in _namespace_candidates_in_scope(namespace, lexical_namespace, opened_namespaces):
        members |= index.get(candidate, frozenset())
        imported = imported or candidate in imported_namespaces
    return members, imported


def _existing_namespaces(
    namespace: str,
    project_declarations: set[str],
    imported_namespaces: set[str],
    lexical_namespace: str,
    opened_namespaces: tuple[str, ...],
) -> list[str]:
    """The namespaces ``open namespace`` opens: the candidates that exist."""

    index = _namespace_members(frozenset(project_declarations))
    return [
        candidate
        for candidate in _namespace_candidates_in_scope(namespace, lexical_namespace, opened_namespaces)
        if candidate in index or candidate in imported_namespaces
    ]


def export_alias_namespaces(originals: dict[str, str]) -> set[str]:
    """Namespaces an ``export`` command adds aliases to, and their prefixes.

    Aliases are not declarations, so a namespace holding only aliases looks
    empty to the declaration graph; an ``open`` of it is still live
    (PALOMAR-2026-09-17-000001 re-exports `TauCeti.ApproximationNumber` into
    `TauCeti.DavisKahan.ExactSinTheta` and opens that).
    """

    namespaces: set[str] = set()
    for text in originals.values():
        if "export" not in text:
            continue
        code_lines = _mask_comments_preserve_layout(text).split("\n")
        namespace_by_line, _opens = _source_namespace_resolution_contexts(text)
        for line_no, code_line in enumerate(code_lines, 1):
            if _EXPORT_COMMAND_HEAD_RE.match(code_line):
                parts = namespace_by_line.get(line_no, "").split(".")
                namespaces |= {".".join(parts[:end]) for end in range(1, len(parts) + 1) if parts[0]}
    return namespaces


_OPEN_HIDING_RE = re.compile(
    r"^\s*open\s+([^\n]*?)\s+hiding\s+([^\n]*)$", re.MULTILINE
)


def _command_continuation(masked: str, end: int) -> str:
    """The indented lines that continue a command whose first line ends at ``end``.

    `open X hiding a b` and `open X renaming a → b` may list their names over
    several lines; PALOMAR-2026-10-19-000009 hides 26 names over seven.
    """

    lines: list[str] = []
    for line in masked[end:].split("\n")[1:]:
        if not line.strip() or not line[:1].isspace():
            break
        lines.append(line)
    return " ".join(lines)


def detect_open_hiding_roots(
    decls: list[DeclRange], originals: dict[str, str]
) -> set[str]:
    """Return declarations named by an ``open ... hiding ...`` clause.

    A `hiding` clause names declarations in order to exclude them, so the file
    does not depend on their *meaning* - but it does require them to exist:
    deleting one leaves the clause referring to an unknown constant and the
    module stops elaborating. The clause sits in the file header, outside every
    declaration's source range, so the span-based scan never sees it and no
    edge is produced; these names are therefore rooted directly.
    """

    names = {d["name"] for d in decls}
    by_suffix: dict[str, set[str]] = {}
    for name in names:
        for index, char in enumerate(name):
            if char == "." and index + 1 < len(name):
                by_suffix.setdefault(name[index + 1 :], set()).add(name)
    roots: set[str] = set()
    for text in originals.values():
        masked = _mask_comments_preserve_layout(text)
        for match in _OPEN_HIDING_RE.finditer(masked):
            namespaces = match.group(1)
            hidden = match.group(2) + " " + _command_continuation(masked, match.end())
            opened = [n for n in namespaces.split() if _IDENT_RE.fullmatch(n)]
            for token in hidden.split():
                if not _IDENT_RE.fullmatch(token):
                    continue
                for namespace in opened:
                    candidate = f"{namespace}.{token}"
                    if candidate in names:
                        roots.add(candidate)
                    else:
                        matches = by_suffix.get(candidate, set())
                        if len(matches) == 1:
                            roots.add(next(iter(matches)))
    return roots


_OPEN_RENAMING_RE = re.compile(
    r"^[ \t]*open[ \t]+(\S+)[ \t]+renaming[ \t]+([^\n]*)$", re.MULTILINE
)
_RENAMING_PAIR_RE = re.compile(rf"({_LEAN_COMMAND_NAME_PATTERN})\s*(?:→|->)")


def detect_open_renaming_roots(
    decls: list[DeclRange], originals: dict[str, str]
) -> set[str]:
    """Return declarations named by an ``open X renaming a → b`` clause.

    Like ``hiding``, the clause sits outside every declaration's range, and
    deleting ``X.a`` makes Lean reject the whole ``open``, so every later use
    of ``b`` fails too: PALOMAR-2026-10-13-000010 renames dozens of
    declarations this way (``open _root_.Foo renaming bar → bar``). ``X`` is
    resolved through the enclosing namespaces as Lean resolves it.
    """

    names = {d["name"] for d in decls}
    roots: set[str] = set()
    for text in originals.values():
        masked = _mask_comments_preserve_layout(text)
        namespace_by_line = _source_namespace_resolution_contexts(text)[0]
        for match in _OPEN_RENAMING_RE.finditer(masked):
            namespace = match.group(1)
            pairs = match.group(2) + " " + _command_continuation(masked, match.end())
            line = masked.count("\n", 0, match.start()) + 1
            prefixes = _namespace_name_candidates(namespace, namespace_by_line.get(line, ""))
            for pair in _RENAMING_PAIR_RE.finditer(pairs):
                hit = next((f"{prefix}.{pair.group(1)}" for prefix in prefixes
                            if f"{prefix}.{pair.group(1)}" in names), None)
                if hit is not None:
                    roots.add(hit)
    return roots


# `run_cmd`/`run_elab`/`run_meta` run code at elaboration time, often an axiom
# audit over a list of quoted theorem names (PALOMAR-2026-10-10-000001). The
# command has no declaration range, so its quoted names give no edge; deleting
# one makes ``X fail with "Unknown constant". The command runs to the next
# unindented line.
_RUN_COMMAND_RE = re.compile(rf"^(?:run_cmd|run_elab|run_meta){_KW_END}")
# A name the command's code names: quoted (`` `X ``, ``` ``X ```) or called
# directly (PALOMAR-2026-10-11-000009 runs `_root_.Proj.EventTransport.run`,
# which re-issues declarations the paper needs). Not a field after `.`.
_RUN_COMMAND_NAME_RE = re.compile(rf"(?<![{_ID_REST}`.])(``?)?({_LEAN_COMMAND_NAME_PATTERN})")


def detect_run_command_roots(
    decls: list[DeclRange], originals: dict[str, str]
) -> set[str]:
    """Return project declarations named in top-level ``run_cmd`` commands."""

    names = {d["name"] for d in decls}
    roots: set[str] = set()
    for text in originals.values():
        code_lines = _mask_comments_preserve_layout(text).split("\n")
        namespace_by_line = None
        index = 0
        while index < len(code_lines):
            if not _RUN_COMMAND_RE.match(code_lines[index]):
                index += 1
                continue
            if namespace_by_line is None:
                namespace_by_line = _source_namespace_resolution_contexts(text)[0]
            start = index
            index += 1
            while index < len(code_lines) and (
                    not code_lines[index].strip() or code_lines[index][0] in " \t"):
                index += 1
            for offset, line in enumerate(code_lines[start:index]):
                for quoted in _RUN_COMMAND_NAME_RE.finditer(line):
                    name = quoted.group(2)
                    candidates = (
                        [name.removeprefix("_root_.")] if quoted.group(1) == "`"
                        else _namespace_name_candidates(name, namespace_by_line.get(start + offset + 1, ""))
                    )
                    hit = next((c for c in candidates if c in names), None)
                    if hit is not None:
                        roots.add(hit)
    return roots


def detect_open_namespace_roots(
    decls: list[DeclRange], originals: dict[str, str]
) -> set[str]:
    """Return exact project-local candidates exposed by persistent ``open``.

    These are dependency-resolution candidates, not blanket keep roots. The
    dependency graph uses lexical source edges to retain only candidates that
    surviving source actually references.
    """

    names = {d["name"] for d in decls}
    # Thousands of files' `open`s, each resolved against every declaration,
    # were quadratic (PALOMAR-2026-10-21-000025).
    prefix_index = _dotted_prefix_index(names)
    roots: set[str] = set()
    for text in originals.values():
        masked = _mask_comments_preserve_layout(text)
        namespace_contexts, _ = _source_namespace_resolution_contexts(text)
        for match in _OPEN_NAMESPACE_RE.finditer(masked):
            selective = _SELECTIVE_OPEN_HEAD_RE.match(match.group(0))
            tokens = (
                [selective.group("namespace")]
                if selective
                else _IDENT_RE.findall(match.group(1))
            )
            if "in" in tokens:
                continue
            line_no = masked.count("\n", 0, match.start()) + 1
            lexical_namespace = namespace_contexts.get(line_no, "")
            for namespace in tokens:
                roots.update(
                    _resolve_project_namespace_members(
                        namespace, names, lexical_namespace, prefix_index
                    )
                )
    return roots


# When the full subproject environment imports two independent modules that
# define the same fully-qualified constant, Lean records only one module as the
# declaration owner. Detect the unambiguous textual form (a dotted declaration
# name) for diagnostics; module import closure, rather than whole-file rooting,
# decides whether either provider is live.
_DECL_HEADER_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)*"
    r"(?P<modifiers>(?:(?:public|private|protected|noncomputable|local|scoped|unsafe|partial|nonrec)"
    r"[ \t]+)*)(?:class[ \t]+inductive|def|theorem|lemma|abbrev|opaque|axiom|instance|structure|class|inductive)\s+"
    rf"(?P<name>(?:_root_\.)?[{_ID_FIRST}][{_ID_REST}]*(?:\.[{_ID_FIRST}][{_ID_REST}]*)*)",
    re.MULTILINE,
)


def detect_duplicate_declaration_files(originals: dict[str, str]) -> set[str]:
    """Return every file declaring a full name that another project file declares too."""

    return {
        path
        for paths in duplicate_declaration_providers(originals).values()
        for path in paths
    }


def duplicate_declaration_providers(originals: dict[str, str]) -> dict[str, set[str]]:
    """Full names that more than one project file declares, with those files.

    Two modules that are never imported together may both declare
    ``NumberField.foo`` (PALOMAR-2026-09-30-000031). Lean merges two such
    theorems at import when their statements agree, keeping one proof, so the
    graph reads every copy from its own module's data (olean.py). Full names
    follow the enclosing ``namespace``; ``private`` declarations are
    module-local in Lean and never collide.
    """

    return {
        name: {path for path, _line, _written in copies}
        for name, copies in duplicate_declaration_copies(originals).items()
    }


def duplicate_declaration_copies(
    originals: dict[str, str],
) -> dict[str, list[tuple[str, int, str]]]:
    """Like ``duplicate_declaration_providers``, with each copy's header line
    and the name as written there: ``(path, line, written name)``."""

    copies: dict[str, list[tuple[str, int, str]]] = {}
    for path, text in originals.items():
        masked = _mask_comments_preserve_layout(text)
        namespaces, _opens = _source_namespace_resolution_contexts(text)
        for match in _DECL_HEADER_RE.finditer(masked):
            if "private" in match.group("modifiers").split():
                continue
            name = match.group("name")
            line_no = masked.count("\n", 0, match.start()) + 1
            namespace = namespaces.get(line_no, "")
            full = (name.removeprefix("_root_.") if name.startswith("_root_.") or not namespace
                    else f"{namespace}.{name}")
            copies.setdefault(full, []).append((path, line_no, name))
    return {
        name: rows for name, rows in copies.items()
        if len({path for path, _line, _written in rows}) > 1
    }


def _graph_has_copy(
    nodes: list[tuple[int, int, str]], line: int, written: str,
) -> bool:
    """Whether one of a module's graph ``nodes`` (start line, end line, source
    name) is the declaration whose header, at ``line``, writes ``written``.

    The graph's own range and name decide it, not the namespace the source
    scan worked out: that scan can misread a file and invent a duplicate.
    """

    rooted = written.startswith("_root_.")
    bare = written.removeprefix("_root_.")
    return any(
        start <= line <= end and (name == bare or (not rooted and name.endswith("." + bare)))
        for start, end, name in nodes
    )


# Lean's source-range API occasionally attaches a surrounding scope command to
# the first or last declaration in that scope. Record these files for audit;
# ``strip_source`` protects namespace/section commands line-wise and handles
# mutual blocks atomically.
_RANGE_STRUCTURAL_COMMAND_RE = re.compile(
    r"^[ \t]*(?:namespace|section|end|mutual)" + _KW_END, re.MULTILINE
)


def detect_structural_range_files(
    decls: list[DeclRange],
    originals: dict[str, str],
    mod_path: dict[str, str],
) -> set[str]:
    """Return files where a declaration range overlaps a scope command."""
    code_lines = {
        path: _mask_comments_preserve_layout(text).split("\n")
        for path, text in originals.items()
    }
    out: set[str] = set()
    for decl in decls:
        if decl.get("start_line") is None or decl.get("end_line") is None:
            continue
        path = mod_path.get(decl["module"])
        if not path or path not in code_lines:
            continue
        lines = code_lines[path]
        start = max(1, int(decl["start_line"]))
        end = min(len(lines), int(decl["end_line"]))
        if any(
            _RANGE_STRUCTURAL_COMMAND_RE.match(lines[line_no - 1])
            for line_no in range(start, end + 1)
        ):
            out.add(path)
    return out


def file_text_references(text: str, declarations: set[str]) -> set[str]:
    """Project declarations a whole file names, resolved as Lean would (see
    ``resolve_candidates``); used to root everything a verbatim file needs."""

    namespaces, opens = _source_namespace_resolution_contexts(text)
    found: set[str] = set()
    for line_no, line in enumerate(_mask_comments_preserve_layout(text).split("\n"), 1):
        for token in _IDENT_RE.findall(line):
            found |= resolve_candidates(token, declarations, namespaces.get(line_no, ""),
                                        opens.get(line_no, ()))
    return found


def plan_source_retention(
    decls: list[DeclRange],
    originals: dict[str, str],
    mod_path: dict[str, str],
    retain_exact_files: set[str] | None = None,
) -> dict[str, Any]:
    """Return the source-retention policy.

    Source-contract files are retained byte-for-byte and seed every declaration
    they own; so are files providing a duplicated full name. Environment
    commands remain in the stripped source and root their declaration-level
    dependencies. Structural-range collisions are reported for auditing; the
    line-safe stripper handles them without whole-file declaration roots.
    """

    retain_exact_files = set(retain_exact_files or ())
    unknown_exact_files = retain_exact_files - set(originals)
    if unknown_exact_files:
        raise ValueError(
            "normalization reported unknown retained files: "
            + ", ".join(sorted(unknown_exact_files))
        )
    retained_modules = {
        module for module, path in mod_path.items() if path in retain_exact_files
    }
    unmapped_exact_files = retain_exact_files - set(mod_path.values())
    if unmapped_exact_files:
        raise ValueError(
            "cannot seed declarations for retained files: "
            + ", ".join(sorted(unmapped_exact_files))
        )

    attribute_command_files = detect_attribute_command_files(originals)
    opaque_environment_files = detect_opaque_environment_command_files(
        originals
    )
    environment_command_files = (
        attribute_command_files | opaque_environment_files
    )
    attribute_command_roots = scoped_source_roots(
        decls, originals, mod_path, detect_attribute_command_roots
    )
    opaque_environment_roots = scoped_source_roots(
        decls, originals, mod_path,
        lambda candidates, sources: detect_opaque_environment_command_roots(candidates, sources, mod_path),
    )
    structural_range_files = detect_structural_range_files(
        decls, originals, mod_path
    )
    # The graph reads every copy of a duplicated full name from its own
    # module. A copy it has no node for (a name the source scan reads
    # differently from Lean) is invisible to it: keep that file verbatim and
    # seed its declarations.
    module_of_path = {path: module for module, path in mod_path.items()}
    # A copy may be private: in a `module` file a declaration without `public`
    # is, so Lean names it `_private.<Module>.0.<name>` and it collides with
    # nothing (PALOMAR-2026-09-25-000001). Match it by its source name.
    graph_copies = {
        (_private_owner_and_display(str(decl["name"]))[1], str(decl["module"])) for decl in decls
    }
    # A copy also counts as seen when a node of its module spans its header
    # and carries the name written there: the scan may have resolved the
    # namespace wrongly (a `namespace Foo\r` it did not recognise read
    # `Foo.minmax` as `minmax`, PALOMAR-2026-10-09-000003).
    module_nodes: dict[str, list[tuple[int, int, str]]] = {}
    for decl in decls:
        if decl.get("start_line") is None or decl.get("end_line") is None:
            continue
        module_nodes.setdefault(str(decl["module"]), []).append((
            int(decl["start_line"]), int(decl["end_line"]),
            _private_owner_and_display(str(decl["name"]))[1],
        ))
    duplicate_provider_files = {
        path
        for name, copies in duplicate_declaration_copies(originals).items()
        for path, line, written in copies
        if (name, module_of_path.get(path)) not in graph_copies
        and not _graph_has_copy(module_nodes.get(module_of_path.get(path, ""), []), line, written)
    }
    mapped_files = set(mod_path.values())
    retain_exact_files |= duplicate_provider_files & mapped_files
    retained_modules |= {
        module for module, path in mod_path.items() if path in duplicate_provider_files
    }

    # A file kept verbatim keeps everything it names, not only what it
    # declares: its anonymous examples and commands use other files'
    # declarations too (PALOMAR-2026-09-29-000002).
    names = {str(decl["name"]) for decl in decls}
    referenced = set().union(*(
        file_text_references(originals[path], names) for path in sorted(retain_exact_files)
    )) if retain_exact_files else set()
    return {
        "retain_exact_files": retain_exact_files,
        "retain_exact_modules": retained_modules,
        "retain_exact_declarations": {
            decl_id(decl)
            for decl in decls
            if decl["module"] in retained_modules
        } | DeclarationIndex(decls).select(referenced),
        "preserve_command_files": environment_command_files,
        "environment_command_roots": (
            attribute_command_roots | opaque_environment_roots
        ),
        "attribute_command_roots": attribute_command_roots,
        "opaque_environment_command_roots": opaque_environment_roots,
        "environment_command_files": environment_command_files,
        "attribute_command_files": attribute_command_files,
        "opaque_environment_command_files": opaque_environment_files,
        "structural_range_files": structural_range_files,
        "duplicate_provider_files": duplicate_provider_files,
    }


# `@[instance] def foo : C := …` — instance declared via attribute on a `def`
# rather than the `instance` keyword (the keyword form is caught by _KIND_KW_RE).
_INSTANCE_ATTR_RE = re.compile(r"@\[[^\]]*\binstance\b[^\]]*\]")


def detect_force_keep_kinds(
    decls: list[DeclRange],
    originals: dict[str, str],
    mod_path: dict[str, str],
) -> set[str]:
    """Return project decls that must be force-kept because their dependents
    reach them WITHOUT a name reference: typeclass `instance`s (resolved by
    synthesis) and custom-syntax decls (`macro`/`elab`/`syntax`/`notation`/
    `macro_rules`, invoked as syntax). Both are invisible to the name-based
    dependency closure, so dropping one can break elaboration without naming a
    missing constant.

    Detected from the declaration's source header (keyword behind any
    attributes/modifiers), plus the `@[instance] def` attribute form.
    A standalone `deriving instance C for T` command counts as an instance; a
    `deriving` clause on a type is part of that type's range and goes with it."""
    out: set[str] = set()
    for path, path_decls in _decls_by_path(decls, mod_path).items():
        if not path or path not in originals:
            continue
        lines = originals[path].split("\n")
        for d in path_decls:
            if d["start_line"] is None:
                continue
            start, end = int(d["start_line"]), min(len(lines), int(d["end_line"]))
            span = "\n".join(lines[start - 1:end])
            if _KIND_KW_RE.search(span) or _INSTANCE_ATTR_RE.search(span):
                out.add(d["name"])
            elif ".Simps." in "." + str(d["name"]):
                # Custom `@[simps]` projections (`Foo.Simps.apply`) are found by
                # name when `initialize_simps_projections Foo` runs; dropping one
                # silently changes every lemma `@[simps]` generates for `Foo`.
                out.add(d["name"])
    return out


def collect_implicit_dependency_roots(
    decls: list[DeclRange],
    originals: dict[str, str],
    mod_path: dict[str, str],
) -> dict[str, set[DeclId]]:
    """Return physical roots for attributes, syntax and environment commands."""
    from .notation_roots import detect_notation_body_roots

    index = DeclarationIndex(decls)
    attributed: set[DeclId] = set()
    implicit: set[DeclId] = set()
    by_module: dict[str, list[DeclRange]] = {}
    for decl in decls:
        by_module.setdefault(decl["module"], []).append(decl)
    for module, path in mod_path.items():
        local = by_module.get(module, [])
        sources = {path: originals[path]} if path in originals else {}
        local_index = DeclarationIndex(local)
        # Declaration annotations belong to this module's copy only.
        attributed |= local_index.select(detect_automation_tagged(local, sources, mod_path))
        implicit |= local_index.select(detect_force_keep_kinds(local, sources, mod_path))
    attributed |= scoped_source_roots(decls, originals, mod_path, detect_attribute_command_roots)
    implicit |= scoped_source_roots(decls, originals, mod_path, detect_open_hiding_roots)
    for detector in (detect_open_renaming_roots, detect_run_command_roots, detect_notation_body_roots):
        implicit |= scoped_source_roots(decls, originals, mod_path, detector)
    return {
        "attributed": attributed,
        "implicit_kinds": implicit,
        "open_namespace_candidates": index.select(detect_open_namespace_roots(decls, originals)),
    }


def scoped_source_roots(
    decls: list[DeclRange],
    originals: dict[str, str],
    mod_path: dict[str, str],
    detector: Callable[[list[DeclRange], dict[str, str]], set[str]],
) -> set[DeclId]:
    """Resolve command roots only among providers visible in that source file."""
    index = DeclarationIndex(decls)
    if all(len(providers) == 1 for providers in index.by_name.values()):
        return index.select(detector(decls, originals))
    graph, _paths = build_module_import_graph(
        originals, derive_source_root(mod_path) or "/testbed/", known_module_paths=mod_path
    )
    roots: set[DeclId] = set()
    for module, path in mod_path.items():
        if path not in originals:
            continue
        visible = _closure(graph, {module})
        candidates = [decl for decl in decls if decl["module"] in visible]
        roots |= DeclarationIndex(candidates).select(detector(candidates, {path: originals[path]}))
    return roots


def compute_keep_set(
    decls: list[DeclRange],
    deps: Dependencies,
    seed: set[DeclId],
    implicit_roots: set[DeclId] | None = None,
) -> set[DeclId]:
    """Transitive forward-dependency closure = the set of decls to keep.

    Starts from `seed` (the protected declarations), plus every
    `meta` declaration (notation/macro/elab machinery — force-kept because it's
    used implicitly at parse time and never shows up in any term's deps), plus
    names in `implicit_roots` whose use is mediated by the environment rather
    than a term reference. Follows `deps` edges (decl -> the project names it
    references) until the worklist drains.

    Names in either root set that are not project declarations are ignored.
    Semantic acceptance, including axiom policy, belongs exclusively to the
    official comparator and never changes this reachability closure.
    """
    index = DeclarationIndex(decls)
    name_set = index.identities
    deps = index.dependencies(deps)
    keep: set[DeclId] = set()
    work: list[DeclId] = []

    def _add(n: DeclId) -> None:
        if n in name_set and n not in keep:
            keep.add(n)
            work.append(n)

    for s in index.select(seed):
        _add(s)
    for n in index.select(implicit_roots or set()):
        _add(n)
    for d in decls:
        if d["meta"]:
            _add(decl_id(d))

    while work:
        n = work.pop()
        for dep in deps.get(n, ()):
            _add(dep)
    return keep


def attach_keep(decls: list[DeclRange], keep: set[DeclId]) -> list[DeclRange]:
    """Return decls with a `keep` bool set from membership in `keep`."""
    selected = DeclarationIndex(decls).select(keep)
    return [{**d, "keep": decl_id(d) in selected} for d in decls]


def module_to_relpath(module: str) -> str:
    """Render a Lean module name as its source path without losing quotes.

    Dots inside guillemet-quoted components are literal filename characters,
    and the guillemets themselves are syntax rather than path characters.
    """

    components: list[str] = []
    component: list[str] = []
    quoted = False
    for char in module:
        if char == "«" and not quoted:
            quoted = True
        elif char == "»" and quoted:
            quoted = False
        elif char == "." and not quoted:
            components.append("".join(component))
            component = []
        else:
            component.append(char)
    if quoted:
        raise ValueError(f"unterminated quoted module component: {module!r}")
    components.append("".join(component))
    return "/".join(components) + ".lean"


def resolve_module_paths(
    modules: Iterable[str],
    original_paths: Iterable[str],
    source_dirs: Iterable[str] | None = None,
) -> dict[str, str]:
    """Map each module name to its source file path.

    With ``source_dirs`` (the project's ``LEAN_SRC_PATH`` entries, in order) a
    module resolves as Lean resolves it: to the first of those directories
    holding its file among ``original_paths`` (the project's sources). Without them, a module resolves only when exactly one path ends in its
    relative path; a repository with both `Solution.lean` and
    `Paper/Solution.lean` (PALOMAR-2026-09-28-000004) must not guess. Modules
    with no (unambiguous) file are omitted.
    """
    paths = list(original_paths)
    out: dict[str, str] = {}
    if source_dirs is not None:
        known = set(paths)
        directories = [directory.rstrip("/") + "/" for directory in source_dirs]
        for m in modules:
            rel = module_to_relpath(m)
            hit = next((d + rel for d in directories if d + rel in known), None)
            if hit:
                out[m] = hit
        return out
    by_suffix: dict[str, list[str]] = {}
    for p in paths:
        segs = p.split("/")
        for i in range(len(segs)):
            by_suffix.setdefault("/".join(segs[i:]), []).append(p)
    for m in modules:
        hits = by_suffix.get(module_to_relpath(m), [])
        if len(hits) == 1:
            out[m] = hits[0]
    return out


def file_has_kept_decl(decl_ranges: list[DeclRange]) -> bool:
    """True if any decl with a real source range in this file is kept.

    `plan_stripped_sources` reduces a file with no kept decls to an
    import-only stub unless it must preserve environment commands.
    """
    return any(r["keep"] and r["start_line"] is not None for r in decl_ranges)


def _mask_comments_preserve_layout(
    text: str, *, mask_strings: bool = False
) -> str:
    """Replace comment contents with spaces while preserving newlines/columns.

    This is deliberately layout-preserving: callers can decide whether the
    lines between a command prefix and its declaration are only comment/blank
    trivia without losing the original declaration line numbers. Lean block
    comments nest, and comment markers inside strings are ordinary characters.
    """
    out: list[str] = []
    i = 0
    nest = 0
    in_line = False
    in_string = False
    while i < len(text):
        char = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if in_line:
            if char == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if nest:
            if char == "/" and nxt == "-":
                nest += 1
                out.extend((" ", " "))
                i += 2
                continue
            if char == "-" and nxt == "/":
                nest -= 1
                out.extend((" ", " "))
                i += 2
                continue
            out.append("\n" if char == "\n" else " ")
            i += 1
            continue
        if in_string:
            out.append(" " if mask_strings and char != "\n" else char)
            if char == "\\" and nxt:
                out.append(" " if mask_strings and nxt != "\n" else nxt)
                i += 2
                continue
            if char == '"':
                in_string = False
            i += 1
            continue
        if char == "-" and nxt == "-":
            in_line = True
            out.extend((" ", " "))
            i += 2
            continue
        if char == "/" and nxt == "-":
            nest = 1
            out.extend((" ", " "))
            i += 2
            continue
        if char == '"':
            in_string = True
        out.append(" " if mask_strings and in_string else char)
        i += 1
    return "".join(out)


def _attribute_block_start(code_lines: list[str], end_line: int) -> int | None:
    """Return the start of a standalone (possibly multiline) `@[...]` block."""
    if end_line < 1 or not code_lines[end_line - 1].rstrip().endswith("]"):
        return None
    for line_no in range(end_line, 0, -1):
        line = code_lines[line_no - 1]
        if "@[" in line:
            block = "\n".join(code_lines[line_no - 1:end_line])
            return line_no if _ATTR_ONLY_RE.match(block) else None
        if not line.strip():
            return None
    return None


def _prefix_block_start(code_lines: list[str], end_line: int) -> int | None:
    """Return the first line of a possibly multiline `... in` modifier."""
    if end_line < 1 or not re.search(r"\bin\s*$", code_lines[end_line - 1]):
        return None
    for line_no in range(end_line, 0, -1):
        line = code_lines[line_no - 1]
        if not line.strip():
            return None
        if _PREFIX_START_RE.match(line):
            block = "\n".join(code_lines[line_no - 1:end_line])
            return line_no if _PREFIX_IN_RE.match(block) else None
    return None


def _extend_up(code_lines: list[str], start_line: int) -> int:
    """Extend a deletion start upward over decoration lines that belong to this
    decl (standalone `@[attr]` and `... in` command-prefix modifiers), skipping
    blank/comment-only trivia between them. `code_lines` is the same source
    with comments layout-masked. `start_line` and the return are 1-based."""
    s = start_line
    while True:
        j = s - 1
        while j >= 1 and code_lines[j - 1].strip() == "":
            j -= 1  # skip blank and comment-only lines above
        attr_start = _attribute_block_start(code_lines, j)
        prefix_start = _prefix_block_start(code_lines, j)
        if attr_start is not None:
            s = attr_start
        elif prefix_start is not None:
            s = prefix_start
        else:
            break
    return s


def _extend_guarded_diagnostic_up(
    lines: list[str], code_lines: list[str], diagnostic_line: int
) -> int:
    """Include a ``#guard_msgs`` command's expected-message comment.

    Lean encodes expected diagnostics as a doc/block comment immediately above
    ``#guard_msgs in``. Comment masking turns that comment into blank lines, so
    the ordinary modifier walk can find an earlier ``set_option ... in`` but
    otherwise leaves the expected-message comment behind. Only absorb masked
    trivia when ``#guard_msgs`` is the topmost prefix.
    """

    start = _extend_up(code_lines, diagnostic_line)
    if not code_lines[start - 1].lstrip().startswith("#guard_msgs"):
        return start
    j = start - 1
    while j >= 1 and not lines[j - 1].strip():
        j -= 1
    if j < 1 or not lines[j - 1].rstrip().endswith("-/"):
        return start
    for line_no in range(j, 0, -1):
        stripped = lines[line_no - 1].lstrip()
        if stripped.startswith("/--"):
            return line_no
        if not stripped or code_lines[line_no - 1].strip():
            break
    return start


_STRUCTURAL_COMMAND_RE = re.compile(
    r"^\s*(?:namespace|section|end|mutual)" + _KW_END
)
_STRUCTURAL_OPEN_RE = re.compile(r"^\s*(namespace|section|mutual)" + _KW_END)
_STRUCTURAL_END_RE = re.compile(r"^\s*end(?:\s|$)")


def _mutual_blocks(code_lines: list[str]) -> list[tuple[int, int]]:
    """Find balanced top-level `mutual ... end` blocks using masked source."""
    stack: list[tuple[str, int]] = []
    blocks: list[tuple[int, int]] = []
    for line_no, line in enumerate(code_lines, 1):
        opened = _STRUCTURAL_OPEN_RE.match(line)
        if opened:
            stack.append((opened.group(1), line_no))
            continue
        if _STRUCTURAL_END_RE.match(line) and stack:
            kind, start = stack.pop()
            if kind == "mutual":
                blocks.append((start, line_no))
    return blocks


def _collapse_blank_runs(text: str) -> str:
    """Collapse runs of 3+ blank lines (left behind by deletions) to one, and
    trim leading/trailing blank lines. Preserves a single trailing newline."""
    text = re.sub(r"\n[ \t]*\n([ \t]*\n)+", "\n\n", text)
    text = text.strip("\n")
    return text + "\n" if text else ""


def strip_source(file_text: str, decl_ranges: list[DeclRange]) -> str:
    """Return `file_text` with every dropped declaration's source span removed.

    `decl_ranges` is the subset of rows for THIS file. Rows that are kept or
    range-less are left in place; a `keep == False` row's lines are deleted
    (extended upward over standalone attribute lines).

    Declaration ranges can OVERLAP — most importantly, a `structure`/`inductive`
    and its auto-generated `casesOn`/`noConfusion`/projection helpers report the
    SAME (or nested) source range, and those helpers are usually dropped while
    the type itself is kept. So **keep wins per line**: a line is deleted only
    if it lies in a drop range AND no kept declaration covers it. A drop decl
    whose own start line is covered by a kept decl is skipped entirely (it's a
    nested/auto-generated sibling of something we're keeping).
    """
    lines = file_text.split("\n")
    code_lines = _mask_comments_preserve_layout(file_text).split("\n")
    n = len(lines)
    keep_mask = [False] * (n + 2)  # 1-based; index 0 unused
    delete = [False] * (n + 2)
    forced_delete = [False] * (n + 2)

    source_rows = [
        r for r in decl_ranges
        if r.get("start_line") is not None and r.get("end_line") is not None
    ]
    kept_source_rows = [r for r in source_rows if r["keep"]]

    def contains_kept_child(outer: DeclRange) -> bool:
        outer_start = (
            int(outer["start_line"]), int(outer.get("start_col") or 0)
        )
        outer_end = (
            int(outer["end_line"]), int(outer.get("end_col") or 0)
        )
        return any(
            outer_start
            <= (int(child["start_line"]), int(child.get("start_col") or 0))
            and (int(child["end_line"]), int(child.get("end_col") or 0))
            <= outer_end
            for child in kept_source_rows
        )

    # Defense in depth for callers that supply an inconsistent keep-set: a
    # source-backed local declaration (for example `outer.key` from a
    # `let rec key`) cannot be retained while deleting the command that
    # lexically contains it. Protect every containing command atomically.
    protected_rows = [r for r in source_rows if contains_kept_child(r)]
    for r in protected_rows:
        s = max(1, int(r["start_line"]))
        e = min(n, int(r["end_line"]))
        for i in range(s, e + 1):
            keep_mask[i] = True

    # `findDeclarationRanges?` can attach `mutual` and/or its closing `end` to
    # only one member's range. Treat the block atomically: retaining one member
    # retains the complete mutual command; dropping all source-backed members
    # removes its opener and closer together.
    for block_start, block_end in _mutual_blocks(code_lines):
        block_rows = [
            r for r in source_rows
            if int(r["start_line"]) <= block_end
            and int(r["end_line"]) >= block_start
        ]
        if not block_rows:
            continue
        if any(r["keep"] for r in block_rows):
            for i in range(block_start, min(n, block_end) + 1):
                keep_mask[i] = True
        else:
            for i in range(block_start, min(n, block_end) + 1):
                forced_delete[i] = True

    for r in decl_ranges:
        if r["keep"] or r["start_line"] is None:
            continue
        s = max(1, int(r["start_line"]))
        e = min(n, int(r["end_line"]))
        if e < s:
            continue
        if keep_mask[s]:
            # start line is protected by an overlapping kept decl -> this is a
            # nested/auto-generated sibling; leave the whole span alone.
            continue
        s = _extend_up(code_lines, s)
        for i in range(s, e + 1):
            if not keep_mask[i]:
                delete[i] = True

    for i in range(1, n + 1):
        if forced_delete[i] and not keep_mask[i]:
            delete[i] = True
        elif _STRUCTURAL_COMMAND_RE.match(code_lines[i - 1]):
            # Declaration ranges occasionally begin at their surrounding
            # namespace/section opener. Never delete one side of a structural
            # scope; dead mutual blocks were handled atomically above.
            delete[i] = False

    kept = [lines[i - 1] for i in range(1, n + 1) if not delete[i]]
    return _collapse_blank_runs("\n".join(kept))



_DIAGNOSTIC_COMMAND_RE = re.compile(
    r"^[ \t]*#(?:check|print|reduce|synth)" + _KW_END + r"[^\n]*$"
)
# `#eval`/`#guard` run code and are kept, unless they name a deleted
# declaration: then they cannot elaborate any more.
_EVAL_COMMAND_RE = re.compile(r"^[ \t]*#(?:eval|guard_expr|guard)" + _KW_END)
# A command the project itself declares, e.g. `elab "audit_axioms" n:ident : command`.
_CUSTOM_COMMAND_DECL_RE = re.compile(
    r'^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:local|scoped|private|public)[ \t]+)*'
    r'(?:syntax|elab|macro)(?:[ \t]*\([^)\n]*\))*[ \t]+"[ \t]*(?P<atom>[^"\s]+)[ \t]*"[^\n]*:[ \t]*command\b',
    re.MULTILINE,
)


def project_command_atoms(originals: dict[str, str]) -> set[str]:
    """Leading atoms of commands the project declares (`audit_standard_axioms`)."""

    atoms: set[str] = set()
    for text in originals.values():
        masked = _mask_comments_preserve_layout(text)
        atoms.update(match.group("atom") for match in _CUSTOM_COMMAND_DECL_RE.finditer(masked))
    return atoms


@functools.lru_cache(maxsize=8)
def _check_command_head(custom_commands: frozenset[str]) -> re.Pattern[str]:
    """Commands the project declares, plus `#name` and `assert_name` commands,
    which by convention only check things (`assert_no_sorry`, `#audit_axioms`)."""

    return re.compile(
        r"^[ \t]*(?:"
        + "".join(re.escape(atom) + "|" for atom in sorted(custom_commands, key=len, reverse=True))
        + r"#(?!(?:guard_msgs|eval|guard_expr|guard|check|print|reduce|synth|exit)" + _KW_END + r")"
        + _LEAN_COMMAND_NAME_PATTERN + r"|assert_" + _LEAN_COMMAND_NAME_PATTERN + r")" + _KW_END
    )


def _private_display_index(
    declarations: set[str], module: str | None = None,
) -> dict[str, set[str]]:
    """Kernel names of private declarations, by the name source text uses.

    Lean sees only the current module's private declarations; with ``module``
    the index is limited to them.
    """

    index: dict[str, set[str]] = {}
    for name in declarations:
        owner, display = _private_owner_and_display(name)
        if owner is not None and (module is None or owner == module):
            index.setdefault(display, set()).add(name)
    return index


def resolve_candidates(
    token: str, declarations: set[str], namespace: str = "",
    opens: tuple[str, ...] = (), private_index: dict[str, set[str]] | None = None,
    *, prefixes: bool = True,
) -> set[str]:
    """Every project declaration ``token`` may denote, as Lean resolves it.

    Tries the token and then (with ``prefixes``) its dotted prefixes (the
    receiver of `my_lemma.symm`), each through the enclosing namespaces and the
    opened ones, then the current module's private names. Lean elaborates an
    identifier with several matches as overloaded and keeps the one that
    type-checks, so all of them are candidates: a removal needs every one of
    them deleted (PALOMAR-2026-10-07-000001 opened three namespaces with an
    `ownerEquiv` each, and only an unused one was deleted). Never guesses from
    a last component: that once took Mathlib's `Semiring` in
    `variable [Semiring B]` for a deleted project `….Semiring`
    (PALOMAR-2026-09-14-000002).
    """

    # Universe applications tokenize `Foo.{u}` as `Foo.` and `u`.
    parts = token.rstrip(".").split(".")
    shortest = 1 if prefixes else len(parts)
    for end in range(len(parts), shortest - 1, -1):
        name = ".".join(parts[:end])
        if name in {"", "_root_"}:
            continue
        candidates = _namespace_name_candidates(name, namespace)
        if not name.startswith("_root_."):
            candidates += [f"{opened}.{name}" for opened in opens]
        hits = {candidate for candidate in candidates if candidate in declarations}
        if hits:
            return hits
        if private_index:
            private: set[str] = set()
            for display in _namespace_name_candidates(name, namespace):
                private |= private_index.get(display, set())
            if private:
                return private
    return set()


def _names_deleted_declaration(
    payload: str, declarations: set[str], deleted_declarations: set[str],
    namespace: str, opens: tuple[str, ...] = (),
    private_index: dict[str, set[str]] | None = None,
) -> bool:
    """Whether an identifier in ``payload`` resolves exactly to a deleted declaration."""

    for token in _global_identifiers(payload):
        candidates = resolve_candidates(token, declarations, namespace, opens, private_index)
        if candidates and candidates <= deleted_declarations:
            return True
    return False


def _global_identifiers(text: str) -> Iterator[str]:
    """The identifiers in ``text`` that can name a global declaration.

    Not one right after a `.`: `(e).below` and `.inl c` are a field and a
    constructor of a type, which a declaration called `below` or `inl` does
    not affect (PALOMAR-2026-10-07-000001 lost `variable (hmatch …)` to a
    deleted `below`).
    """

    for match in _IDENT_RE.finditer(text):
        if match.start() == 0 or text[match.start() - 1] != ".":
            yield match.group(0)


_ANONYMOUS_EXAMPLE_TOKEN_RE = re.compile(r"\bexample\b")
_EXPORT_COMMAND_HEAD_RE = re.compile(r"^[ \t]*export" + _KW_END)
# `export Foo (a b c)`, whose target list may continue over several lines.
_EXPORT_OPEN_RE = re.compile(
    r"^[ \t]*export[ \t]+" + _LEAN_COMMAND_NAME_PATTERN + r"\s*\("
)
_EXPORT_COMMAND_RE = re.compile(
    r"^[ \t]*export\s+(?P<namespace>"
    + _LEAN_COMMAND_NAME_PATTERN
    + r")\s*\((?P<targets>[^()]*)\)\s*$"
)


_ATTRIBUTE_COMMAND_HEAD_RE = re.compile(
    r"^[ \t]*" + _SCOPED_ATTRIBUTE_PREFIX
    + r"attribute\s*\[[^\]]*\]"
)
_VARIABLE_COMMAND_HEAD_RE = re.compile(r"^[ \t]*variable" + _KW_END)
_INCLUDE_OMIT_COMMAND_HEAD_RE = re.compile(
    r"^[ \t]*(?P<kind>include|omit)" + _KW_END
)


def source_may_contain_anonymous_example(file_text: str) -> bool:
    """Return whether Lean should inspect this file for ``example`` commands.

    This is only a cheap candidate filter. Comments and strings are masked;
    false positives are harmless because Lean's official frontend identifies
    the actual outer command ranges. The transformation never uses a textual
    range guess.
    """

    masked = _mask_comments_preserve_layout(file_text, mask_strings=True)
    return bool(_ANONYMOUS_EXAMPLE_TOKEN_RE.search(masked))


def _continued_command_spans(
    code_lines: list[str], head: re.Pattern[str]
) -> dict[int, int]:
    """Return zero-based inclusive spans for simple multiline commands.

    Lean conventionally indents continuation operands more deeply than the
    command keyword. Restricting continuation lines by relative indentation
    keeps a following, independently-indented command out of the span.
    """

    spans: dict[int, int] = {}
    i = 0
    while i < len(code_lines):
        if not head.match(code_lines[i]):
            i += 1
            continue
        indent = len(code_lines[i]) - len(code_lines[i].lstrip())
        j = i + 1
        while j < len(code_lines) and code_lines[j].strip():
            next_indent = len(code_lines[j]) - len(code_lines[j].lstrip())
            if next_indent <= indent:
                break
            j += 1
        spans[i] = j - 1
        i = j
    return spans


def _remove_text_spans(
    text: str, spans: list[tuple[int, int]]
) -> str:
    out = text
    for start, end in sorted(spans, reverse=True):
        # Remove the redundant separator, preserving newlines and indentation.
        if start > 0 and out[start - 1] in " \t":
            while end < len(out) and out[end] in " \t":
                end += 1
        out = out[:start] + out[end:]
    return out


def _deleted_references(
    text: str,
    project_declarations: set[str],
    deleted_declarations: set[str],
    *,
    local_names: set[str] | None = None,
    lexical_namespace: str = "",
    opens: tuple[str, ...] = (),
    private_index: dict[str, set[str]] | None = None,
) -> tuple[bool, bool]:
    """Whether a name in ``text`` denotes only deleted declarations, and whether
    one denotes a deleted declaration among others (see ``resolve_candidates``)."""

    local_names = local_names or set()
    only_deleted = some_deleted = False
    for token in _global_identifiers(text):
        if token.removeprefix("_root_.").split(".", 1)[0] in local_names:
            continue
        candidates = resolve_candidates(
            token, project_declarations, lexical_namespace, opens, private_index
        )
        if candidates and candidates <= deleted_declarations:
            only_deleted = True
        elif candidates & deleted_declarations:
            some_deleted = True
    return only_deleted, some_deleted


def _outer_binder_spans(
    masked_command: str, payload_start: int
) -> list[tuple[int, int]]:
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack: list[tuple[str, int]] = []
    spans: list[tuple[int, int]] = []
    for index in range(payload_start, len(masked_command)):
        char = masked_command[index]
        if char in pairs:
            stack.append((char, index))
        elif stack and char == pairs[stack[-1][0]]:
            _, start = stack.pop()
            if not stack:
                spans.append((start, index + 1))
    return spans


def _top_level_colon(masked_binder: str) -> int | None:
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack: list[str] = []
    for index, char in enumerate(masked_binder):
        if char in pairs:
            stack.append(char)
        elif stack and char == pairs[stack[-1]]:
            stack.pop()
        elif char == ":" and len(stack) == 1:
            return index
    return None


def _binder_names(masked_binder: str) -> set[str]:
    colon = _top_level_colon(masked_binder)
    opener = masked_binder[:1]
    if colon is None and opener == "[":
        # `[Class alpha]` is an anonymous instance binder, not a name list.
        return set()
    end = colon if colon is not None else len(masked_binder) - 1
    return set(_IDENT_RE.findall(masked_binder[1:end]))


def _binder_dependency_text(masked_binder: str) -> str:
    colon = _top_level_colon(masked_binder)
    if colon is not None:
        return masked_binder[colon + 1 : -1]
    if masked_binder.startswith("["):
        return masked_binder[1:-1]
    return ""


def _prune_open_private_command(
    command: str, project_declarations: set[str], deleted_declarations: set[str],
) -> str | None:
    """``open private ids from M`` without the ids whose declarations were all deleted.

    Batteries matches an id against the private declarations of ``M`` by name
    suffix and fails on one that matches nothing, so an id stays while any of
    its matches survives (PALOMAR-2026-10-08-000003 opened a private lemma the
    strip removed). None: unchanged; "": nothing left.
    """

    masked = _mask_comments_preserve_layout(command, mask_strings=True)
    parsed = _OPEN_PRIVATE_COMMAND_RE.match(masked)
    if parsed is None or re.search(r"\bin\b", parsed.group("ids")):
        return None  # the `in declarations` form names declarations, not modules
    prefixes = tuple(f"_private.{module}.0." for module in _IDENT_RE.findall(parsed.group("modules")))
    private = [name for name in project_declarations if name.startswith(prefixes)]
    removals: list[tuple[int, int]] = []
    kept = 0
    for match in _IDENT_RE.finditer(parsed.group("ids")):
        parts = match.group(0).split(".")
        matches = {name for name in private if name.split(".")[-len(parts):] == parts}
        if matches and matches <= deleted_declarations:
            start = parsed.start("ids") + match.start()
            removals.append((start, parsed.start("ids") + match.end()))
        else:
            kept += 1
    if not removals:
        return None
    if not kept:
        return ""
    return "\n".join(line.rstrip() for line in _remove_text_spans(command, removals).split("\n"))


def _prune_attribute_command(
    command: str,
    project_declarations: set[str],
    deleted_declarations: set[str],
    lexical_namespace: str,
    opens: tuple[str, ...] = (),
    private_index: dict[str, set[str]] | None = None,
) -> tuple[str, int]:
    masked = _mask_comments_preserve_layout(command, mask_strings=True)
    head = _ATTRIBUTE_COMMAND_HEAD_RE.match(masked)
    if head is None:
        return command, 0
    payload = masked[head.end() :]
    removals: list[tuple[int, int]] = []
    for match in _IDENT_RE.finditer(payload):
        token = match.group(0)
        if token == "in" and not payload[match.end() :].strip():
            continue
        # An attribute target names a constant itself, never a receiver.
        candidates = resolve_candidates(
            token, project_declarations, lexical_namespace, opens, private_index,
            prefixes=False,
        )
        if candidates and candidates <= deleted_declarations:
            removals.append(
                (head.end() + match.start(), head.end() + match.end())
            )
    if not removals:
        return command, 0

    pruned = "\n".join(
        line.rstrip()
        for line in _remove_text_spans(command, removals).split("\n")
    )
    pruned_masked = _mask_comments_preserve_layout(pruned, mask_strings=True)
    pruned_head = _ATTRIBUTE_COMMAND_HEAD_RE.match(pruned_masked)
    assert pruned_head is not None
    remaining = [
        token
        for token in _IDENT_RE.findall(pruned_masked[pruned_head.end() :])
        if token != "in"
    ]
    return (pruned if remaining else ""), len(removals)


def _prune_export_command(
    command: str,
    project_declarations: set[str],
    deleted_declarations: set[str],
    kept_declarations: set[str],
    lexical_namespace: str,
) -> tuple[str, int]:
    """Drop deleted targets from ``export NS (a b ...)``.

    Returns the pruned command ("" when it should be removed) and the number
    of targets removed. Imported, kept and unresolved targets remain. A command
    whose project-local namespace lost every declaration is removed whole.
    """

    masked = _mask_comments_preserve_layout(command, mask_strings=True)
    exported = _EXPORT_COMMAND_RE.match(masked)
    if exported is None:
        return command, 0
    namespace = exported.group("namespace")
    namespace_candidates = _namespace_name_candidates(namespace, lexical_namespace)
    removals: list[tuple[int, int]] = []
    remaining = 0
    for match in _IDENT_RE.finditer(exported.group("targets")):
        token = match.group(0)
        resolved = next(
            (
                f"{candidate}.{token}"
                for candidate in namespace_candidates
                if f"{candidate}.{token}" in project_declarations
            ),
            None,
        )
        if resolved in deleted_declarations:
            offset = exported.start("targets")
            removals.append((offset + match.start(), offset + match.end()))
        else:
            remaining += 1
    members = _resolve_project_namespace_members(
        namespace, project_declarations, lexical_namespace
    )
    if not remaining or (members and not (members & kept_declarations)):
        return "", max(len(removals), 1)
    if not removals:
        return command, 0
    pruned = "\n".join(
        line.rstrip()
        for line in _remove_text_spans(command, removals).split("\n")
    )
    # Drop continuation lines emptied by the removal.
    head, *rest = pruned.split("\n")
    return "\n".join([head, *(line for line in rest if line.strip())]), len(removals)


def _prune_variable_command(
    command: str,
    project_declarations: set[str],
    deleted_declarations: set[str],
    live_variable_names: set[str],
    dead_variable_names: set[str],
    lexical_namespace: str,
    opens: tuple[str, ...] = (),
    private_index: dict[str, set[str]] | None = None,
    mentioned_names: set[str] | None = None,
) -> tuple[str, set[str], set[str], int]:
    """``command`` without the binders that cannot elaborate after the strip.

    A binder goes when a name in its type denotes only deleted declarations,
    or a variable already gone. A name that also denotes a kept declaration
    (Lean elaborates it as overloaded) is decided by use: a binder some kept
    code still mentions stays, since that code keeps the declaration Lean
    picked (PALOMAR-2026-10-07-000001's `hmatch`); an unused one goes, as Lean
    could take the surviving candidate and fail (PALOMAR-2026-08-27-000009's
    `hW : IsCanonical k K W`, whose `FunctionField.IsCanonical` was deleted
    while `Chart.IsCanonical` survived).
    """

    masked = _mask_comments_preserve_layout(command, mask_strings=True)
    head = _VARIABLE_COMMAND_HEAD_RE.match(masked)
    if head is None:
        return command, set(), set(), 0

    removals: list[tuple[int, int]] = []
    removed_names: set[str] = set()
    surviving_names: set[str] = set()
    locally_live = set(live_variable_names)
    for start, end in _outer_binder_spans(masked, head.end()):
        binder = masked[start:end]
        names = _binder_names(binder)
        dependencies = _binder_dependency_text(binder)
        dependency_tokens = set(_IDENT_RE.findall(dependencies))
        references_dead_variable = any(
            token.removeprefix("_root_.").split(".", 1)[0]
            in dead_variable_names
            for token in dependency_tokens
        )
        only_deleted, some_deleted = _deleted_references(
            dependencies,
            project_declarations,
            deleted_declarations,
            local_names=locally_live,
            lexical_namespace=lexical_namespace,
            opens=opens,
            private_index=private_index,
        )
        unused = not (names & (mentioned_names or set()))
        if references_dead_variable or only_deleted or (some_deleted and unused):
            removals.append((start, end))
            removed_names.update(names)
        else:
            surviving_names.update(names)
            locally_live.update(names)

    if not removals:
        return command, removed_names, surviving_names, 0
    pruned = "\n".join(
        line.rstrip()
        for line in _remove_text_spans(command, removals).split("\n")
    )
    pruned_masked = _mask_comments_preserve_layout(pruned, mask_strings=True)
    pruned_head = _VARIABLE_COMMAND_HEAD_RE.match(pruned_masked)
    assert pruned_head is not None
    if not pruned_masked[pruned_head.end() :].strip():
        pruned = ""
    return pruned, removed_names, surviving_names, len(removals)


def _prune_include_omit_command(
    command: str, dead_variable_names: set[str]
) -> tuple[str, int]:
    masked = _mask_comments_preserve_layout(command, mask_strings=True)
    head = _INCLUDE_OMIT_COMMAND_HEAD_RE.match(masked)
    if head is None:
        return command, 0
    payload = masked[head.end() :]
    removals: list[tuple[int, int]] = []
    for match in _IDENT_RE.finditer(payload):
        token = match.group(0)
        if token in dead_variable_names:
            removals.append(
                (head.end() + match.start(), head.end() + match.end())
            )
    if not removals:
        return command, 0
    pruned = "\n".join(
        line.rstrip()
        for line in _remove_text_spans(command, removals).split("\n")
    )
    pruned_masked = _mask_comments_preserve_layout(pruned, mask_strings=True)
    pruned_head = _INCLUDE_OMIT_COMMAND_HEAD_RE.match(pruned_masked)
    assert pruned_head is not None
    remaining = [
        token
        for token in _IDENT_RE.findall(pruned_masked[pruned_head.end() :])
        if token != "in"
    ]
    return (pruned if remaining else ""), len(removals)




# Per-kind counters reported by `remove_dead_commands`, in report order.
_DEAD_COMMAND_STAT_KEYS = (
    "diagnostics_removed",
    "open_namespaces_removed",
    "open_declarations_removed",
    "open_commands_removed",
    "exports_removed",
    "export_targets_removed",
    "attribute_commands_removed",
    "attribute_targets_removed",
    "variable_commands_removed",
    "variable_binders_removed",
    "include_omit_commands_removed",
    "include_omit_names_removed",
    "evals_removed",
    "custom_commands_removed",
)


def remove_dead_commands(
    file_text: str,
    project_declarations: Iterable[str],
    kept_declarations: set[str],
    imported_namespaces: set[str] | None = None,
    *,
    visible_kept_declarations: set[str] | None = None,
    custom_commands: set[str] | None = None,
    module: str | None = None,
    visible_declarations: set[str] | None = None,
) -> tuple[str, dict[str, int]]:
    """Remove non-semantic diagnostics and commands with deleted targets.

    ``#check``, ``#print``, ``#reduce``, and ``#synth`` only query or print
    elaborated information. They do not add declarations or mutate the
    environment, so they are always removed regardless of target.
    ``#eval``/``#guard`` are retained because they may execute arbitrary IO,
    unless they name a deleted project declaration and so cannot elaborate.
    The same holds for commands the project declares itself (``custom_commands``,
    their leading atoms, e.g. ``audit_standard_axioms Foo.thm``).
    Bare ``open`` entries resolving exactly to an exclusively project-owned
    namespace with no live declarations are pruned. Imported and mixed
    namespaces, scoped opens, prefixes, and ambiguous opens remain because they
    can activate notation or elaboration behavior invisible in the declaration
    graph. ``export`` targets that resolve to deleted
    project declarations are dropped, and the command with them when none
    remain or its project-local namespace disappeared. Persistent ``attribute`` targets and typed
    ``variable`` binders are pruned when they resolve exactly to deleted project
    declarations. Any associated ``include``/``omit`` operands are pruned with
    the dead binder. Ambiguous identifiers fail closed by remaining in the
    source; the warm build then reports the unresolved case instead of guessing.
    """

    lines = file_text.split("\n")
    code_lines = _mask_comments_preserve_layout(file_text).split("\n")
    namespace_contexts, open_contexts = _source_namespace_resolution_contexts(file_text)
    visible_kept = (
        kept_declarations
        if visible_kept_declarations is None
        else visible_kept_declarations
    )
    deleted_declarations = project_declarations - kept_declarations
    # Removal decisions resolve names exactly: only declarations this file can
    # see, only its own private names, only namespaces opened whole.
    # Frozen once: the namespace index is cached by it (a frozenset of a
    # frozenset is the same object, so callers that freeze it pay nothing).
    project_declarations = frozenset(project_declarations)
    visible = project_declarations if visible_declarations is None else visible_declarations
    private_index = _private_display_index(project_declarations, module) if module else None
    _strict_namespaces, strict_opens = _source_namespace_resolution_contexts(file_text, strict=True)
    imported_namespaces = set(imported_namespaces or ())
    delete_lines: set[int] = set()
    replacements: dict[int, str] = {}
    stats = dict.fromkeys(_DEAD_COMMAND_STAT_KEYS, 0)

    attribute_spans = _continued_command_spans(
        code_lines, _ATTRIBUTE_COMMAND_HEAD_RE
    )
    variable_spans = _continued_command_spans(
        code_lines, _VARIABLE_COMMAND_HEAD_RE
    )
    include_omit_spans = _continued_command_spans(
        code_lines, _INCLUDE_OMIT_COMMAND_HEAD_RE
    )
    diagnostic_spans = _continued_command_spans(
        code_lines, _DIAGNOSTIC_COMMAND_RE
    )
    # PALOMAR-2026-09-18-000005 closes a long `export` list on an unindented
    # line; the parenthesis, not the indentation, ends the command.
    export_spans = {
        **_continued_command_spans(code_lines, _EXPORT_COMMAND_HEAD_RE),
        **_parenthesized_command_spans(code_lines, _EXPORT_OPEN_RE),
    }
    eval_spans = _continued_command_spans(code_lines, _EVAL_COMMAND_RE)
    custom_head = _check_command_head(frozenset(custom_commands or ()))
    custom_spans = _continued_command_spans(code_lines, custom_head)
    selective_open_spans = _selective_open_spans(code_lines)
    open_private_spans = _continued_command_spans(code_lines, _OPEN_PRIVATE_HEAD_RE)
    open_spans = _continued_command_spans(code_lines, _OPEN_HEAD_RE)
    continuation_lines = {
        line
        for start, end in (
            list(attribute_spans.items())
            + list(variable_spans.items())
            + list(include_omit_spans.items())
            + list(diagnostic_spans.items())
            + list(export_spans.items())
            + list(eval_spans.items())
            + list(custom_spans.items())
            + list(selective_open_spans.items())
            + list(open_private_spans.items())
            + list(open_spans.items())
        )
        for line in range(start + 1, end + 1)
    }
    live_variable_names: set[str] = set()
    dead_variable_names: set[str] = set()
    # Names the file uses outside `variable`/`include`/`omit`: a binder named
    # here may be in use (a homonymous parameter only makes this cautious).
    binder_command_lines = {
        line
        for start, end in list(variable_spans.items()) + list(include_omit_spans.items())
        for line in range(start, end + 1)
    }
    mentioned_names = {
        token.split(".", 1)[0]
        for index, code_line in enumerate(code_lines) if index not in binder_command_lines
        for token in _IDENT_RE.findall(code_line)
    }

    for line_no, code_line in enumerate(code_lines, 1):
        zero_based = line_no - 1
        if zero_based in continuation_lines:
            continue

        if zero_based in attribute_spans:
            end = attribute_spans[zero_based]
            command = "\n".join(lines[zero_based : end + 1])
            pruned, target_count = _prune_attribute_command(
                command,
                visible,
                deleted_declarations,
                namespace_contexts.get(line_no, ""),
                strict_opens.get(line_no, ()),
                private_index,
            )
            if target_count:
                stats["attribute_targets_removed"] += target_count
                delete_lines.update(range(line_no + 1, end + 2))
                if pruned:
                    replacements[line_no] = pruned
                else:
                    delete_lines.add(line_no)
                    stats["attribute_commands_removed"] += 1
            continue

        if zero_based in variable_spans:
            end = variable_spans[zero_based]
            command = "\n".join(lines[zero_based : end + 1])
            pruned, removed_names, surviving_names, binder_count = (
                _prune_variable_command(
                    command,
                    visible,
                    deleted_declarations,
                    live_variable_names,
                    dead_variable_names,
                    namespace_contexts.get(line_no, ""),
                    strict_opens.get(line_no, ()),
                    private_index,
                    mentioned_names,
                )
            )
            dead_variable_names.update(removed_names)
            dead_variable_names.difference_update(surviving_names)
            live_variable_names.difference_update(removed_names)
            live_variable_names.update(surviving_names)
            if binder_count:
                stats["variable_binders_removed"] += binder_count
                delete_lines.update(range(line_no + 1, end + 2))
                if pruned:
                    replacements[line_no] = pruned
                else:
                    delete_lines.add(line_no)
                    stats["variable_commands_removed"] += 1
            continue

        if zero_based in include_omit_spans:
            end = include_omit_spans[zero_based]
            command = "\n".join(lines[zero_based : end + 1])
            pruned, name_count = _prune_include_omit_command(
                command, dead_variable_names
            )
            if name_count:
                stats["include_omit_names_removed"] += name_count
                delete_lines.update(range(line_no + 1, end + 2))
                if pruned:
                    replacements[line_no] = pruned
                else:
                    delete_lines.add(line_no)
                    stats["include_omit_commands_removed"] += 1
            continue
        diagnostic = _DIAGNOSTIC_COMMAND_RE.match(code_line)
        if diagnostic:
            start = _extend_guarded_diagnostic_up(
                lines, code_lines, line_no
            )
            delete_lines.update(range(start, diagnostic_spans[zero_based] + 2))
            stats["diagnostics_removed"] += 1
            continue

        if zero_based in custom_spans:
            end = custom_spans[zero_based]
            command = _mask_comments_preserve_layout(
                "\n".join(lines[zero_based : end + 1]), mask_strings=True
            )
            payload = command[custom_head.match(command).end():]
            if _names_deleted_declaration(
                payload, visible, deleted_declarations,
                namespace_contexts.get(line_no, ""), strict_opens.get(line_no, ()),
                private_index,
            ):
                start = _extend_guarded_diagnostic_up(lines, code_lines, line_no)
                delete_lines.update(range(start, end + 2))
                stats["custom_commands_removed"] += 1
            continue

        if zero_based in eval_spans:
            end = eval_spans[zero_based]
            command = _mask_comments_preserve_layout(
                "\n".join(lines[zero_based : end + 1]), mask_strings=True
            )
            payload = command[_EVAL_COMMAND_RE.match(command).end():]
            if _names_deleted_declaration(
                payload, visible, deleted_declarations,
                namespace_contexts.get(line_no, ""), strict_opens.get(line_no, ()),
                private_index,
            ):
                start = _extend_guarded_diagnostic_up(lines, code_lines, line_no)
                delete_lines.update(range(start, end + 2))
                stats["evals_removed"] += 1
            continue

        if zero_based in open_private_spans:
            end = open_private_spans[zero_based]
            pruned = _prune_open_private_command(
                "\n".join(lines[zero_based : end + 1]), project_declarations, deleted_declarations,
            )
            if pruned is not None:
                delete_lines.update(range(line_no + 1, end + 2))
                if pruned:
                    replacements[line_no] = pruned
                else:
                    delete_lines.add(line_no)
                stats["open_commands_removed" if not pruned else "open_declarations_removed"] += 1
            continue

        if zero_based in selective_open_spans:
            end = selective_open_spans[zero_based]
            command = "\n".join(lines[zero_based : end + 1])
            selective_open = _SELECTIVE_OPEN_COMMAND_RE.match(
                "\n".join(code_lines[zero_based : end + 1])
            )
            if selective_open is None:
                continue
            namespace = selective_open.group("namespace")
            payload = selective_open.group("targets")
            namespace_candidates = _namespace_name_candidates(
                namespace, namespace_contexts.get(line_no, "")
            )
            removals: list[tuple[int, int]] = []
            remaining = 0
            for match in _IDENT_RE.finditer(payload):
                token = match.group(0)
                resolved = next(
                    (
                        f"{candidate}.{token}"
                        for candidate in namespace_candidates
                        if f"{candidate}.{token}" in project_declarations
                    ),
                    None,
                )
                if resolved in deleted_declarations:
                    removals.append(
                        (
                            selective_open.start("targets") + match.start(),
                            selective_open.start("targets") + match.end(),
                        )
                    )
                else:
                    # Kept project targets and imported/unresolved targets must
                    # remain. Ambiguity therefore fails closed into the warm
                    # certification build rather than guessing.
                    remaining += 1
            if removals:
                stats["open_declarations_removed"] += len(removals)
                delete_lines.update(range(line_no + 1, end + 2))
                if remaining:
                    pruned = [
                        line.rstrip()
                        for line in _remove_text_spans(command, removals).split("\n")
                    ]
                    pruned = [line for index, line in enumerate(pruned)
                              if index == 0 or line.strip()]
                    if len(pruned) > 1 and pruned[-1].strip() == ")":
                        pruned[-2:] = [pruned[-2] + ")"]
                    replacements[line_no] = "\n".join(pruned)
                else:
                    delete_lines.add(line_no)
                    stats["open_commands_removed"] += 1
            continue

        opened = (
            _PLAIN_OPEN_COMMAND_RE.match("\n".join(code_lines[zero_based : open_spans[zero_based] + 1]))
            if zero_based in open_spans else None
        )
        if opened:
            span_end = open_spans[zero_based]
            tokens = opened.group("names").split()
            # ``open scoped`` and ``open ... in`` have different semantics;
            # preserve them unless a complete Lean command node models them.
            if tokens and (tokens[0] == "scoped" or tokens[-1] == "in"
                           or "hiding" in tokens or "renaming" in tokens):
                continue
            # Lean opens the names in order, each relative to the ones before
            # it: in `open DraismaVargas.Infrastructure GluingDatum` the second
            # is `DraismaVargas.Infrastructure.GluingDatum`
            # (PALOMAR-2026-10-09-000009). An earlier name a live later one
            # is reached through stays, even if it is dead itself.
            lexical = namespace_contexts.get(line_no, "")
            before = tuple(open_contexts.get(line_no, ()))
            within: list[str] = []
            decisions: list[list] = []
            for namespace in tokens:
                members, imported = _resolve_namespace_provenance(
                    namespace, project_declarations, imported_namespaces, lexical,
                    before + tuple(within),
                )
                alone, _ = _resolve_namespace_provenance(
                    namespace, project_declarations, imported_namespaces, lexical, before,
                )
                dead = bool(members) and not imported and not (members & visible_kept)
                through_earlier = bool((members - alone) & visible_kept)
                decisions.append([namespace, dead, through_earlier])
                # Only namespaces that exist are opened: adding every
                # candidate doubled `within` per name, and a 12-name `open`
                # never finished (PALOMAR-2026-10-12-000002).
                within += [
                    opened for opened in _existing_namespaces(
                        namespace, project_declarations, imported_namespaces, lexical,
                        before + tuple(within))
                    if opened not in within
                ]
            for index, (_namespace, dead, through_earlier) in enumerate(decisions):
                if through_earlier and not dead:
                    for earlier in decisions[:index]:
                        earlier[1] = False
            retained = [namespace for namespace, dead, _ in decisions if not dead]
            removed = len(decisions) - len(retained)
            if removed:
                stats["open_namespaces_removed"] += removed
                delete_lines.update(range(line_no + 1, span_end + 2))
                if retained:
                    replacements[line_no] = (
                        f"{opened.group('indent')}open {' '.join(retained)}"
                    )
                else:
                    delete_lines.add(line_no)
                    stats["open_commands_removed"] += 1
            continue

        if zero_based in export_spans:
            end = export_spans[zero_based]
            command = "\n".join(lines[zero_based : end + 1])
            pruned, target_count = _prune_export_command(
                command,
                project_declarations,
                deleted_declarations,
                kept_declarations,
                namespace_contexts.get(line_no, ""),
            )
            if target_count:
                delete_lines.update(range(line_no + 1, end + 2))
                if pruned:
                    stats["export_targets_removed"] += target_count
                    replacements[line_no] = pruned
                else:
                    delete_lines.add(line_no)
                    stats["exports_removed"] += 1

    if not delete_lines and not replacements:
        return file_text, stats

    rendered = [
        replacements.get(line_no, line)
        for line_no, line in enumerate(lines, 1)
        if line_no not in delete_lines
    ]
    return _collapse_blank_runs("\n".join(rendered)), stats


_MODULE_COMPONENT_PATTERN = r"(?:«[^»]+»|[^\s.]+)"
_IMPORT_RE = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\s+"
    rf"({_MODULE_COMPONENT_PATTERN}(?:\.{_MODULE_COMPONENT_PATTERN})*)",
    re.MULTILINE,
)


def _source_imports(file_text: str) -> list[tuple[str, int, int]]:
    """Return import names and inclusive zero-based source line spans.

    Lean permits a newline (and comments) between `import` and the module.
    Parse the complete masked source so graph visibility, stubs, and import
    removal all agree on those wrapped commands.
    """
    masked = _mask_comments_preserve_layout(file_text, mask_strings=True)
    return [
        (match.group(1), masked.count("\n", 0, match.start()),
         masked.count("\n", 0, match.end()))
        for match in _IMPORT_RE.finditer(masked)
    ]


def import_only_stub(file_text: str) -> str:
    """Return a valid dead-module stub containing only its import preamble.

    Keeping arbitrary non-declaration scaffolding is unsafe when every source
    declaration was dropped: a surviving `variable (p : Parser ...)`,
    `attribute`, or `open scoped` command may reference one of those deleted
    declarations. Preserve only Lean's file preamble commands (`prelude`,
    `module`, and imports). Public imports require the `module` marker, so it
    is retained verbatim.
    """
    kept: list[str] = []
    lines = file_text.split("\n")
    code_lines = _mask_comments_preserve_layout(
        file_text, mask_strings=True
    ).split("\n")
    import_lines = {
        line for _, start, end in _source_imports(file_text)
        for line in range(start, end + 1)
    }
    for line_no, (line, code_line) in enumerate(zip(lines, code_lines, strict=True)):
        # `module` and `prelude` are header commands only at column zero. A
        # declaration body can legally contain an indented term whose identifier
        # is literally `module`; stripping whitespace here would copy that term
        # into the stub and produce `unexpected identifier; expected command`.
        # Match against comment/string-masked source as well: prose such as
        # "import of the downstream module" inside a module doc comment is not
        # a Lean import command and must never leak into a generated stub.
        # `rstrip("\r")`: a CRLF file's header line is `module\r`
        # (PALOMAR-2026-10-13-000008 lost it, and `public import` with it).
        if code_line.rstrip("\r") in {"prelude", "module"} or line_no in import_lines:
            kept.append(line)
    return "\n".join(kept) + ("\n" if kept else "")


def plan_stripped_sources(
    originals: dict[str, str],
    rows: list[DeclRange],
    module_paths: dict[str, str],
    *,
    preserve_command_files: set[str] | None = None,
    retain_exact_files: set[str] | None = None,
    anonymous_example_ranges: dict[str, list[DeclRange]] | None = None,
    all_project_declarations: set[str] | None = None,
    imported_namespaces: set[str] | None = None,
    syntax: dict[str, Any] | None = None,
) -> tuple[dict[str, str], dict[str, Any]]:
    """Plan the complete declaration/source-command strip without I/O.

    Returns the desired source of every file plus a summary. The caller
    (engine.py) writes the changed files and certifies them with a build.

    ``syntax`` maps paths to Lean's own analysis of the file (frontend.py).
    A file with a usable analysis is edited from it (syntax_edit.py): command
    spans and kinds, scopes and the constants names denote all come from
    Lean. Every other file takes the regex path below.
    """

    from lean_strip._pipeline.preprocessing import syntax_edit

    syntax = syntax or {}

    preserved_commands = set(preserve_command_files or ())
    retained_files = set(retain_exact_files or ())
    examples = {
        path: list(example_rows)
        for path, example_rows in (anonymous_example_ranges or {}).items()
        if path in originals and path not in retained_files
    }
    by_path: dict[str, list[DeclRange]] = {}
    unresolved_drops = 0
    for row in rows:
        if row["start_line"] is None:
            continue
        path = module_paths.get(row["module"])
        if not path or path not in originals:
            if not row["keep"]:
                unresolved_drops += 1
            continue
        by_path.setdefault(path, []).append(row)
    for path, example_rows in examples.items():
        by_path.setdefault(path, []).extend(example_rows)

    desired = dict(originals)
    declaration_drop_files: set[str] = set()
    stubbed_files: list[str] = []
    stub_paths: set[str] = set()
    command_preserved_files: list[str] = []
    lean_files = {
        path for path, analysis in syntax.items()
        if path in originals and path not in retained_files
        and syntax_edit.usable(analysis, originals[path])
    }
    lean_rows: dict[str, list[DeclRange]] = {}
    for path, file_rows in by_path.items():
        if path in retained_files or all(row["keep"] for row in file_rows):
            continue
        declaration_drop_files.add(path)
        if file_has_kept_decl(file_rows) or path in preserved_commands:
            if path in lean_files:
                lean_rows[path] = file_rows  # planned with the dead commands below
            else:
                desired[path] = strip_source(originals[path], file_rows)
            if not file_has_kept_decl(file_rows):
                command_preserved_files.append(path.removeprefix("/testbed/"))
        else:
            stub = syntax_edit.header_stub(syntax.get(path), originals[path])
            desired[path] = stub if stub is not None else import_only_stub(originals[path])
            stubbed_files.append(module_to_relpath(file_rows[0]["module"]))
            stub_paths.add(path)

    project_declarations = frozenset(
        {*(all_project_declarations or ()), *(str(row["name"]) for row in rows)})
    kept_declarations = {
        str(row["name"])
        for row in rows
        if row["keep"]
    }
    dead_command_cleanup = {
        **dict.fromkeys(_DEAD_COMMAND_STAT_KEYS, 0),
        "files_changed": 0,
    }
    imported = set(imported_namespaces or ()) | export_alias_namespaces(originals)
    # An identically named namespace in an unrelated module cannot make this
    # file's `open` valid. Scope only command cleanup to its import closure;
    # the declaration keep-set and dependency graph remain unchanged.
    import_graph, resolved_paths = build_module_import_graph(
        originals, "/testbed/", known_module_paths=module_paths
    )
    custom_commands = project_command_atoms(originals)
    path_modules = {path: module for module, path in resolved_paths.items()}
    kept_by_module: dict[str, set[str]] = {}
    names_by_module: dict[str, set[str]] = {}
    for row in rows:
        names_by_module.setdefault(str(row["module"]), set()).add(str(row["name"]))
        if row["keep"]:
            kept_by_module.setdefault(str(row["module"]), set()).add(str(row["name"]))
    # Range-less/generated declarations may have no source module in this
    # plan. Their visibility is unknown, not evidence that the namespace died.
    unmapped_kept = set().union(*(
        names for module, names in kept_by_module.items()
        if module not in resolved_paths
    ))
    has_duplicate_names = len({str(row["name"]) for row in rows}) < len({decl_id(row) for row in rows})
    lean_context = syntax_edit.Context(
        project_declarations=project_declarations,
        deleted=project_declarations - kept_declarations,
        kept=kept_declarations,
        imported_namespaces=imported,
        custom_commands=frozenset(custom_commands),
    )
    lean_edited: list[str] = []
    lean_fallback: dict[str, str] = {}
    for path, content in list(desired.items()):
        if path in retained_files:
            continue
        module = path_modules.get(path)
        visible_kept = (
            unmapped_kept.union(*(
                kept_by_module.get(imported_module, set())
                for imported_module in _closure(import_graph, {module})
            ))
            if module is not None else kept_declarations
        )
        if path in lean_files and path not in stub_paths:
            context = lean_context
            if has_duplicate_names:
                context = syntax_edit.Context(
                    project_declarations=project_declarations,
                    deleted=project_declarations - visible_kept,
                    kept=visible_kept,
                    imported_namespaces=imported,
                    custom_commands=frozenset(custom_commands),
                )
            planned = syntax_edit.plan_file(
                syntax[path], lean_rows.get(path, []), context, visible_kept=visible_kept,
            )
            if planned is not None:
                cleaned, cleanup = planned
                lean_edited.append(path.removeprefix("/testbed/"))
                # Declarations and dead commands go in one edit here; count
                # the file as cleaned up only for the latter.
                if any(cleanup.values()):
                    dead_command_cleanup["files_changed"] += 1
                desired[path] = cleaned
                for key, value in cleanup.items():
                    dead_command_cleanup[key] += value
                continue
            lean_fallback[path.removeprefix("/testbed/")] = "a dropped declaration lies in no Lean command"
            if path in lean_rows:
                content = desired[path] = strip_source(originals[path], lean_rows[path])
        cleaned, cleanup = remove_dead_commands(
            content,
            project_declarations,
            visible_kept,
            imported,
            visible_kept_declarations=visible_kept,
            custom_commands=custom_commands,
            module=module,
            # A file of unknown module resolves against every project name.
            visible_declarations=(
                set().union(*(names_by_module.get(m, set())
                              for m in _closure(import_graph, {module})))
                if module is not None else None
            ),
        )
        if cleaned != content:
            dead_command_cleanup["files_changed"] += 1
            desired[path] = cleaned
        for key, value in cleanup.items():
            dead_command_cleanup[key] += value

    changed = sum(originals.get(path) != content for path, content in desired.items())
    return desired, {
        "stripped_files": len(declaration_drop_files),
        "source_files_changed": changed,
        "stub_files": sorted(stubbed_files),
        "command_preserved_files": sorted(command_preserved_files),
        "files_written_this_iter": changed,
        "unresolved_drops": unresolved_drops,
        "anonymous_examples_removed": sum(len(rows) for rows in examples.values()),
        "anonymous_example_files": sorted(
            path.removeprefix("/testbed/")
            for path, example_rows in examples.items()
            if example_rows
        ),
        "dead_command_cleanup": dead_command_cleanup,
        "stub_paths": sorted(stub_paths),
        "lean_edited_files": sorted(lean_edited),
        "lean_fallback_files": lean_fallback,
    }


def remove_imports_of(file_text: str, deleted_modules: set[str]) -> str:
    """Drop `import <module>` lines (incl. `public import`) for any module in
    `deleted_modules`. Used to prune hub files after deleting modules."""
    if not deleted_modules:
        return file_text
    removed_lines = {
        line for module, start, end in _source_imports(file_text)
        if module in deleted_modules
        for line in range(start, end + 1)
    }
    return "\n".join(
        line for line_no, line in enumerate(file_text.split("\n"))
        if line_no not in removed_lines
    )


# ---------------------------------------------------------------------------
# Module-level (import-graph) stripping, run before declaration-level
# stripping. Modules outside the import closure of the live declarations'
# owners are deleted whole. Every kept module keeps its full import closure,
# preserving its build-time environment for implicit inputs such as bare
# `grind`, which searches the whole imported environment.
# ---------------------------------------------------------------------------

def derive_source_root(mod_path: dict[str, str]) -> str | None:
    """Infer the source-root prefix (e.g. `/testbed/src/`) from any
    module->path pair, so we can name modules for files (incl. import hubs)
    that have no declarations and thus aren't in the decl graph."""
    roots = derive_source_roots(mod_path)
    return roots[0] if roots else None


def derive_source_roots(mod_path: dict[str, str]) -> list[str]:
    """Infer every source-root prefix represented by resolved module paths."""

    roots: set[str] = set()
    for mod, path in mod_path.items():
        tail = module_to_relpath(mod)
        if path.endswith("/" + tail):
            roots.add(path[: -len(tail)])
        elif path.endswith(tail):
            roots.add(path[: -len(tail)])
    return sorted(roots, key=lambda root: (-len(root), root))


def namespace_anchor_roots(
    originals: dict[str, str],
    decls: list[DeclRange],
    keep: set[DeclId],
    module_paths: dict[str, str],
    imported_namespaces: set[str] | None = None,
) -> set[DeclId]:
    """Declarations to keep so that every surviving `open X` still finds `X`.

    Lean rejects `open X` unless namespace `X` exists at that point; a file's
    own later declarations do not count. PALOMAR-2026-10-11-000009 imports a
    `NamespaceAnchor` module only so that `open _root_.SubdiffusiveProcess.Section8`
    is legal before the file defines into that namespace; the strip deleted the
    anchor and kept the `open`, since the file's own members keep it alive.
    So: where a file keeps members of `X` itself but none of the members its
    imports provide survive, keep one of those.
    """

    keep = DeclarationIndex(decls).select(keep)
    imported = set(imported_namespaces or ())
    import_graph, resolved = build_module_import_graph(
        originals, "/testbed/", known_module_paths=module_paths
    )
    path_modules = {path: module for module, path in resolved.items()}
    module_of: dict[DeclId, str] = {}
    by_namespace: dict[str, list[DeclId]] = {}
    for decl in decls:
        name = str(decl["name"])
        module_of[decl_id(decl)] = str(decl["module"])
        parts = name.split(".")
        for end in range(1, len(parts)):
            by_namespace.setdefault(".".join(parts[:end]), []).append(decl_id(decl))
    anchors: set[DeclId] = set()
    for path, text in originals.items():
        module = path_modules.get(path)
        if module is None or "open" not in text:
            continue
        closure: set[str] | None = None
        namespaces, _opens = _source_namespace_resolution_contexts(text)
        for line_no, code_line in enumerate(_mask_comments_preserve_layout(text).split("\n"), 1):
            match = _PLAIN_OPEN_COMMAND_RE.match(code_line.rstrip("\r"))
            if match is None:
                continue
            for token in match.group("names").split():
                for namespace in _namespace_name_candidates(token, namespaces.get(line_no, "")):
                    members = by_namespace.get(namespace, [])
                    if namespace in imported or not any(
                        module_of[name] == module and name in keep for name in members
                    ):
                        continue
                    if closure is None:
                        closure = _closure(import_graph, {module}) - {module}
                    provided = sorted(name for name in members if module_of[name] in closure)
                    if provided and not any(name in keep for name in provided):
                        anchors.add(provided[0])
    return anchors


def build_module_import_graph(
    originals: dict[str, str],
    source_root: str,
    *,
    known_module_paths: dict[str, str] | None = None,
) -> tuple[dict[str, set[str]], dict[str, str]]:
    """Return the project import graph across every resolved source root.

    graph maps each module to the set of project modules it imports (incl. via
    `public import`). ``known_module_paths`` handles layouts where the entry
    module is at the repository root but library modules live under ``src/``.
    Longest-root matching prevents those files from being named ``src.Foo``.
    Covers import-hub modules that carry no declarations.
    """

    roots = {source_root}
    roots.update(derive_source_roots(known_module_paths or {}))
    imported_by_relpath: dict[str, set[str]] = {}
    imports_by_path = {
        path: {module for module, _, _ in _source_imports(source)}
        for path, source in originals.items()
    }
    for imports in imports_by_path.values():
        for imported in imports:
            imported_by_relpath.setdefault(
                module_to_relpath(imported), set()
            ).add(imported)

    mod_to_path: dict[str, str] = {}
    for path in originals:
        if not path.endswith(".lean"):
            continue
        matching_roots = [root for root in roots if path.startswith(root)]
        if not matching_roots:
            continue
        root = max(matching_roots, key=len)
        relative_path = path[len(root):]
        rendered_candidates = imported_by_relpath.get(relative_path, set())
        mod = (
            next(iter(rendered_candidates))
            if len(rendered_candidates) == 1
            else relative_path[:-len(".lean")].replace("/", ".")
        )
        mod_to_path[mod] = path
    for mod, path in (known_module_paths or {}).items():
        if path in originals:
            mod_to_path = {
                existing_mod: existing_path
                for existing_mod, existing_path in mod_to_path.items()
                if existing_path != path or existing_mod == mod
            }
            mod_to_path[mod] = path
    mods = set(mod_to_path)
    graph: dict[str, set[str]] = {}
    for mod, path in mod_to_path.items():
        graph[mod] = imports_by_path[path] & mods
    return graph, mod_to_path


def _closure(graph: dict[str, set[str]], seed: set[str]) -> set[str]:
    seen: set[str] = set()
    stack = list(seed)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(graph.get(m, ()))
    return seen


def module_keep_set(
    graph: dict[str, set[str]], root_modules: set[str]
) -> set[str]:
    """Modules to keep: the downward import-closure of the root modules —
    everything they transitively need to build. This is import-closed (every
    kept module's imports are also kept), so deleting the complement leaves no
    dangling imports among kept modules. The entry module (which nothing
    imports) is kept separately by `plan_protected_module_prune`.

    We deliberately do NOT add upward "ancestors": a dead module typically
    imports shared base modules that ARE in the closure, which would make it a
    false ancestor and keep almost everything."""
    return _closure(graph, root_modules & set(graph))


def declaration_dependency_closure(
    decls: list[DeclRange],
    deps: Dependencies,
    roots: set[DeclId],
) -> set[DeclId]:
    """Return the project-declaration closure of ``roots`` only.

    This intentionally differs from :func:`compute_keep_set`: no roots are
    added implicitly (in particular not every ``meta`` declaration), so the
    caller alone decides which declarations make a module live. Required
    elaboration environments remain protected by the source import closure of
    every module reached here; engine.py then checks that no protected
    declaration was pruned and certifies the result with the final builds.
    """

    index = DeclarationIndex(decls)
    names = index.identities
    roots = index.select(roots)
    deps = index.dependencies(deps)
    seen: set[DeclId] = set()
    stack = [name for name in roots if name in names]
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        stack.extend(dep for dep in deps.get(name, ()) if dep in names)
    return seen


def _ensure_imports(file_text: str, modules: set[str]) -> str:
    """Add missing ordinary imports without otherwise rewriting a hub file."""

    if not modules:
        return file_text
    lines = file_text.splitlines()
    existing: set[str] = set()
    last_import: int | None = None
    for index, line in enumerate(lines):
        match = _IMPORT_RE.match(line)
        if match:
            existing.add(match.group(1))
            last_import = index
    missing = sorted(modules - existing)
    if not missing:
        return file_text

    additions = [f"import {module}" for module in missing]
    if last_import is not None:
        insert_at = last_import + 1
    else:
        # ``module``/``prelude`` must remain the first source command. Hub
        # files normally already have imports; this handles a hub with none.
        header_commands = [
            index
            for index, line in enumerate(lines)
            if line in {"module", "prelude"}
        ]
        insert_at = max(header_commands, default=-1) + 1
    lines[insert_at:insert_at] = additions
    rendered = "\n".join(lines)
    return rendered + ("\n" if file_text.endswith("\n") else "")


def remap_decl_ranges_after_source_rewrite(
    decls: list[DeclRange],
    originals: dict[str, str],
    rewritten: dict[str, str],
    module_paths: dict[str, str],
) -> list[DeclRange]:
    """Move declaration ranges across line-only source rewrites.

    Module pruning can replace one umbrella import with many explicit imports.
    Declaration graph ranges were collected before that rewrite, so every
    later declaration in the file shifts. Map retained source lines through
    the exact diff and fail closed if either end of a declaration range was
    changed rather than merely moved.
    """

    line_maps: dict[str, dict[int, int]] = {}
    for path, source in rewritten.items():
        original = originals.get(path)
        if original is None or original == source:
            continue
        mapping: dict[int, int] = {}
        matcher = difflib.SequenceMatcher(
            None,
            original.splitlines(),
            source.splitlines(),
            autojunk=False,
        )
        for original_start, rewritten_start, size in matcher.get_matching_blocks():
            for offset in range(size):
                mapping[original_start + offset + 1] = rewritten_start + offset + 1
        line_maps[path] = mapping

    remapped: list[DeclRange] = []
    for decl in decls:
        start = decl.get("start_line")
        end = decl.get("end_line")
        path = module_paths.get(decl["module"])
        mapping = line_maps.get(path or "")
        if start is None or end is None or mapping is None:
            remapped.append(decl)
            continue
        new_start = mapping.get(int(start))
        new_end = mapping.get(int(end))
        if new_start is None or new_end is None:
            raise ValueError(
                "source rewrite changed declaration text for "
                f"{decl['name']} at {path}:{start}-{end}"
            )
        remapped.append(
            {**decl, "start_line": new_start, "end_line": new_end}
        )
    return remapped


def plan_protected_module_prune(
    originals: dict[str, str],
    decls: list[DeclRange],
    deps: Dependencies,
    protected_names: set[DeclId],
    entry_module: str,
    *,
    extra_keep_modules: set[str] | None = None,
    known_module_paths: dict[str, str] | None = None,
    collapse_entry_import_hubs: bool = False,
) -> tuple[dict[str, str], dict[str, Any]]:
    """Plan member-local module deletion from protected declaration roots.

    ``originals`` must contain exactly the project's Lean sources. The
    live declaration closure determines candidate owner modules; their complete
    source-import closure is retained to preserve implicit elaboration inputs.
    The entry module is always kept. When it is a declaration-free umbrella,
    imports of deleted branches are removed and imports of protected owner
    modules are ensured directly, so an obsolete re-export cannot make a whole
    branch live.

    The returned source mapping omits deleted files and includes deterministic
    import rewrites. engine.py applies the plan; the final builds certify it.
    """

    entry_tail = module_to_relpath(entry_module)
    entry_path = (known_module_paths or {}).get(entry_module)
    if entry_path is None:
        entry_paths = [
            path
            for path in originals
            if path == entry_tail or path.endswith("/" + entry_tail)
        ]
        if len(entry_paths) != 1:
            raise ValueError(
                f"expected exactly one source for entry module {entry_module!r}, "
                f"found {entry_paths}"
            )
        entry_path = entry_paths[0]
    source_root = entry_path[: -len(entry_tail)]
    graph, module_paths = build_module_import_graph(
        originals,
        source_root,
        known_module_paths=known_module_paths,
    )
    if entry_module not in graph:
        raise ValueError(f"entry module {entry_module!r} absent from source graph")

    # A name two modules declare has a row per copy (olean.py); both stay live.
    index = DeclarationIndex(decls)
    missing = sorted(str(value) for value in protected_names if not index.resolve(value))
    protected_names = index.select(protected_names)
    owners_by_name = {decl_id(decl): {decl["module"]} for decl in decls}
    if missing:
        raise ValueError(f"protected declarations have no source owner: {missing}")

    live_declarations = declaration_dependency_closure(
        decls,
        deps,
        protected_names,
    )
    protected_modules = {module for name in protected_names for module in owners_by_name[name]}
    live_modules = {module for name in live_declarations for module in owners_by_name.get(name, ())}
    explicit_keep_modules = set(extra_keep_modules or ())
    unknown_keep_modules = explicit_keep_modules - set(graph)
    if unknown_keep_modules:
        raise ValueError(
            "explicit keep modules absent from source graph: "
            f"{sorted(unknown_keep_modules)}"
        )
    declaration_modules = set().union(*owners_by_name.values()) if owners_by_name else set()
    elided_entry_import_hubs: set[str] = set()
    graph_for_keep = graph
    if collapse_entry_import_hubs and entry_module in live_modules:
        elided_entry_import_hubs = {
            imported
            for imported in graph.get(entry_module, set())
            if imported not in declaration_modules
            and imported not in explicit_keep_modules
            and bool(graph.get(imported))
        }
        if elided_entry_import_hubs:
            graph_for_keep = {
                module: set(imports) for module, imports in graph.items()
            }
            graph_for_keep[entry_module] -= elided_entry_import_hubs

    keep_modules = module_keep_set(
        graph_for_keep, live_modules | explicit_keep_modules
    )
    keep_modules.add(entry_module)
    deleted_modules = set(graph) - keep_modules

    planned = {
        path: source
        for module, path in module_paths.items()
        if module in keep_modules
        for source in [originals[path]]
    }
    rewritten_modules: set[str] = set()
    for module in sorted(keep_modules):
        path = module_paths.get(module)
        if path is None:
            continue
        original_ended_with_newline = planned[path].endswith("\n")
        updated = remove_imports_of(planned[path], deleted_modules)
        # A declaration-free umbrella is a presentation/build root, not a
        # semantic root. Make its protected exports explicit after removing
        # dead intermediary hubs.
        if module == entry_module and entry_module not in live_modules:
            updated = _ensure_imports(
                updated, protected_modules - {entry_module}
            )
        elif module == entry_module and elided_entry_import_hubs:
            updated = _ensure_imports(updated, live_modules - {entry_module})
        if original_ended_with_newline and updated and not updated.endswith("\n"):
            updated += "\n"
        if updated != planned[path]:
            rewritten_modules.add(module)
            planned[path] = updated

    report: dict[str, Any] = {
        "schema": "protected_root_module_prune_v1",
        "entry_module": entry_module,
        "protected_modules": sorted(protected_modules),
        "explicit_keep_modules": sorted(explicit_keep_modules),
        "protected_declarations": sorted({name for _module, name in protected_names}),
        "protected_declaration_identities": identity_rows(protected_names),
        "live_declaration_count": len(live_declarations),
        "live_declarations": sorted({name for _module, name in live_declarations}),
        "live_declaration_identities": identity_rows(live_declarations),
        "live_modules": sorted(live_modules),
        "kept_modules": sorted(keep_modules),
        "deleted_modules": sorted(deleted_modules),
        "deleted_files": sorted(
            module_paths[module] for module in deleted_modules
        ),
        "rewritten_modules": sorted(rewritten_modules),
        "entry_is_semantic_root": entry_module in live_modules,
        "collapse_entry_import_hubs": collapse_entry_import_hubs,
        "elided_entry_import_hubs": sorted(elided_entry_import_hubs),
    }
    return planned, report
