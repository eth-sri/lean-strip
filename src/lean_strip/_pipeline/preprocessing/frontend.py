"""Lean's own parse, scopes and name resolution of project sources.

The strip decides what to keep from exact Lean data, but it edits source
text. Every edit that goes beyond deleting a declaration's range (a dead
`open`, an `attribute` or `export` target, a `variable` binder and the
`include`/`omit` naming it, an `#eval` of a deleted declaration) needs to know
where a command ends and what its names denote. Re-implementing that in Python
regexes was the source of nearly every editing bug found on the Palomar
registry, so the Lean script here asks Lean instead.

For each file it elaborates the file the way `lean` does, reusing the built
`.olean` files of its imports, and reports per top-level command: the exact
source range and syntax kind, the scope before it (namespace, `open`
declarations, `variable` binders), the syntax tree, the project constants its
elaborated terms denote (from the info trees, so an overloaded name reports
the alternative Lean chose), the local variables they denote, and Lean's own
`resolveGlobalName`/`resolveNamespace` answer for every identifier. Theorems
are elaborated with `debug.byAsSorry` and the kernel check is skipped: a later
command only sees a theorem's statement, so proofs need not be replayed.

Only files the strip changes are analysed, one Lean process per file (an
imported environment is large), several in parallel. A file the pass cannot
analyse (header error, timeout, crash) keeps the Python editing logic.
"""

from __future__ import annotations

import json
import shlex
import time
from bisect import bisect_right
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from typing import Any, Iterable, Iterator


_FRONTEND_LEAN = r"""
import Lean
open Lean Elab Frontend

/-! Lean's own view of source files, for lean-strip's source editing.

`main PROJECT_MODULES JOB...` takes jobs `path<TAB>module<TAB>full|header`,
optionally with `<TAB>setup` (the `.setup.json` Lake compiled the file with,
for its options), and prints JSON lines for each:

* `{"file", "module"}` first;
* `{"header": tree, "r": range}`: the module header (`module`, `import`s);
* in `full` mode, one object per top-level command: `c` index, `k` syntax
  kind, `r` range, the scope before it (`ns` namespace, and for commands that
  are not declarations `o` the open declarations and `v` the `variable`
  binders in scope with their names), and for commands that are not
  declarations `t` the syntax tree, `f` the project constants its elaborated
  terms mention (by term range), `l` the local variables its terms denote,
  and `e` its first error;
* `{"done", "ok", "ms", "import_ms"}` last (`fatal` when the header failed).

Ranges are `[line, column, endLine, endColumn]`, lines from 1 and columns in
codepoints from 0. A tree's identifiers carry Lean's own name resolution in
the scope of their command: `g` the global constants (`resolveGlobalName`,
with the field accesses that remain) and `n` the namespaces
(`resolveNamespace`). Theorems are elaborated with `debug.byAsSorry` (see
`isTheorem`), and nothing goes through the kernel.
-/

abbrev Ranges := Array (Nat × Nat)

def rangeJson (fm : FileMap) (stx : Syntax) : Json :=
  match stx.getRange? (canonicalOnly := false) with
  | some r =>
    let s := fm.toPosition r.start
    let e := fm.toPosition r.stop
    Json.arr #[toJson s.line, toJson s.column, toJson e.line, toJson e.column]
  | none => Json.null

def byteRange? (stx : Syntax) : Option (Nat × Nat) :=
  stx.getRange? (canonicalOnly := false) |>.map fun r => (r.start.byteIdx, r.stop.byteIdx)

def within (outer : Nat × Nat) (stx : Syntax) : Bool :=
  match byteRange? stx with
  | some (s, e) => outer.1 ≤ s && e ≤ outer.2
  | none => false

/-- Commands lean-strip never edits inside: the tree omits their children,
and the references their elaboration produces are not reported. -/
def isDeclarationKind (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Command.declaration || k == ``Parser.Command.mutual
    || k.toString.endsWith ".lemma"

structure TreeState where
  nodes : Nat := 0
  skipped : Ranges := #[]

partial def treeJson (env : Environment) (fm : FileMap) (scope : Command.Scope)
    (isCommand : SyntaxNodeKind → Bool) (budget : Nat) (stx : Syntax) :
    StateT TreeState IO Json := do
  modify fun s => { s with nodes := s.nodes + 1 }
  match stx with
  | .missing => return Json.null
  | .atom _ val => return Json.mkObj [("a", val), ("r", rangeJson fm stx)]
  | .ident _ _ id _ =>
    let globals := ResolveName.resolveGlobalName env scope.opts scope.currNamespace scope.openDecls id
      |>.map (fun (c, fields) => Json.arr #[toJson c.toString, toJson fields])
    let namespaces := ResolveName.resolveNamespace env scope.currNamespace scope.openDecls id
    return Json.mkObj [("i", id.toString), ("r", rangeJson fm stx),
      ("g", Json.arr globals.toArray), ("n", Json.arr (namespaces.map (toJson ·.toString)).toArray)]
  | .node _ kind args =>
    let base := [("k", toJson kind.toString), ("r", rangeJson fm stx)]
    let base := if isCommand kind then base ++ [("cmd", Json.bool true)] else base
    if isDeclarationKind kind then
      if let some r := byteRange? stx then
        modify fun s => { s with skipped := s.skipped.push r }
      return Json.mkObj (base ++ [("decl", Json.bool true), ("dk", toJson stx[1].getKind.toString)])
    if (← get).nodes > budget then
      return Json.mkObj (base ++ [("big", Json.bool true)])
    let children ← args.mapM (treeJson env fm scope isCommand budget)
    return Json.mkObj (base ++ [("c", Json.arr children)])

/-- Project constants and local variables that the terms a command elaborated
inside its own range denote, by term range. -/
def references (fm : FileMap) (isProject : Name → Bool) (command : Nat × Nat)
    (skipped : Ranges) (trees : PersistentArray InfoTree) : IO (Array Json × Array Json) := do
  let consts ← IO.mkRef (#[] : Array Json)
  let locals ← IO.mkRef (#[] : Array Json)
  let seen ← IO.mkRef (({} : Std.HashSet String))
  let push (out : IO.Ref (Array Json)) (j : Json) : IO Unit := do
    let key := j.compress
    unless (← seen.get).contains key do
      seen.modify (·.insert key)
      out.modify (·.push j)
  for tree in trees do
    tree.visitM' (m := IO) (preNode := fun ctx info _ => do
      if skipped.any (within · info.stx) then
        return false
      if !within command info.stx then
        return true
      match info with
      | .ofTermInfo ti =>
        let e := (instantiateMVarsCore ctx.mctx ti.expr).1
        if let .fvar fvarId := e then
          if let some decl := ti.lctx.find? fvarId then
            push locals (Json.arr #[rangeJson fm ti.stx, toJson decl.userName.toString])
        else
          let names := e.foldConsts (#[] : Array Name) fun c acc =>
            if isProject c && !acc.contains c then acc.push c else acc
          unless names.isEmpty do
            push consts (Json.arr #[rangeJson fm ti.stx, Json.arr (names.map (toJson ·.toString))])
      | .ofFieldInfo fi =>
        if isProject fi.projName then
          push consts (Json.arr #[rangeJson fm fi.stx, Json.arr #[toJson fi.projName.toString]])
      | _ => pure ()
      return true)
  return (← consts.get, ← locals.get)

def openDeclJson : OpenDecl → Json
  | .simple ns except => Json.mkObj [("s", ns.toString), ("x", Json.arr (except.map (toJson ·.toString)).toArray)]
  | .explicit id declName => Json.mkObj [("e", id.toString), ("d", declName.toString)]

/-- The names a bracketed binder declares: `(a b : T)`, `{a}`, `⦃a⦄`, `[inst : C]`. -/
def binderNames (binder : Syntax) : Array String :=
  binder[1].getArgs.filterMap fun s => if s.isIdent then some s.getId.toString else none

def firstError (msgs : MessageLog) : IO (Option String) := do
  for msg in msgs.toList do
    if msg.severity == MessageSeverity.error then
      let text ← msg.data.toString
      return some s!"{msg.pos.line}:{msg.pos.column}: {(text.take 400).toString}"
  return none

def emit (j : Json) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn j.compress
  out.flush

/-- Whether a command is a theorem (possibly behind `… in` prefixes). Its
proof cannot change what later commands see: a theorem's section variables
come from its statement. So it is elaborated with `debug.byAsSorry`. A
definition's body can include variables, so definitions are elaborated in full. -/
partial def isTheorem (stx : Syntax) : Bool :=
  let kind := stx.getKind
  if kind == ``Parser.Command.in then isTheorem stx[2]
  else if kind == ``Parser.Command.declaration then
    stx[1].getKind == ``Parser.Command.theorem || stx[1].getKind == ``Parser.Command.example
  else kind.toString.endsWith ".lemma"

def setScopeOptions (opts : Options) : FrontendM Unit :=
  modify fun s => { s with commandState := { s.commandState with
    scopes := match s.commandState.scopes with
      | scope :: rest => { scope with opts } :: rest
      | [] => [] } }

/-- `Frontend.processCommand`, with theorems elaborated as `sorry`. -/
def processOneCommand : FrontendM Bool := do
  updateCmdPos
  let cmdState ← getCommandState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace,
                 openDecls := scope.openDecls }
  let (cmd, ps, messages) :=
    Parser.parseCommand (← getInputContext) pmctx (← getParserState) cmdState.messages
  modify fun s => { s with commands := s.commands.push cmd }
  setParserState ps
  setMessages messages
  if isTheorem cmd then
    setScopeOptions (scope.opts.insert `debug.byAsSorry (DataValue.ofBool true))
    elabCommandAtFrontend cmd
    setScopeOptions scope.opts
  else
    elabCommandAtFrontend cmd
  return Parser.isTerminalCommand cmd

partial def commandLoop (isProject : Name → Bool) (index : Nat) : FrontendM Unit := do
  let before ← getCommandState
  let scope := before.scopes.head!
  let done ← processOneCommand
  let after ← getCommandState
  let stx := (← get).commands.back!
  let fm := (← read).inputCtx.fileMap
  let kind := stx.getKind
  let mut fields := [("c", toJson index), ("k", toJson kind.toString), ("r", rangeJson fm stx),
    ("ns", toJson scope.currNamespace.toString)]
  if isDeclarationKind kind then
    fields := fields ++ [("decl", Json.bool true), ("dk", toJson stx[1].getKind.toString)]
  else if kind != ``Parser.Command.eoi then
    let isCommand (k : SyntaxNodeKind) : Bool :=
      match Parser.getParserCategory? after.env `command with
      | some cat => cat.kinds.contains k
      | none => false
    -- Names resolve in the scope and environment before the command.
    let (tree, ts) ← (treeJson before.env fm scope isCommand 20000 stx).run {}
    let (consts, locals) ← references fm isProject ((byteRange? stx).getD (0, 0)) ts.skipped
      after.infoState.trees
    fields := fields ++ [
      ("o", Json.arr (scope.openDecls.map openDeclJson).toArray),
      ("v", Json.arr (scope.varDecls.map fun b =>
        Json.arr #[rangeJson fm b.raw, Json.arr ((binderNames b.raw).map toJson)])),
      ("t", tree), ("f", Json.arr consts), ("l", Json.arr locals)]
  if let some err ← firstError after.messages then
    fields := fields ++ [("e", toJson err)]
  emit (Json.mkObj fields)
  -- The next command needs only the scope and environment.
  modify fun s => { s with commandState := { s.commandState with
    messages := {}, infoState := { s.commandState.infoState with trees := {} } } }
  unless done do
    commandLoop isProject (index + 1)

def readLines (path : String) : IO (Array String) := do
  return ((← IO.FS.readFile path).splitOn "\n" |>.filter (!·.isEmpty)).toArray

/-- The options and module flag Lake compiled the file with (its `.setup.json`). -/
def lakeSetup (path : String) : IO (Options × Bool) := do
  if path.isEmpty || !(← System.FilePath.pathExists path) then
    return ({}, false)
  let .ok json := Json.parse (← IO.FS.readFile path) | return ({}, false)
  let isModule := (json.getObjValAs? Bool "isModule").toOption.getD false
  let options := match json.getObjVal? "options" with
    | .ok value => match fromJson? (α := LeanOptions) value with
      | .ok options => options.toOptions
      | .error _ => {}
    | .error _ => {}
  return (options, isModule)

unsafe def processFile (projectModules : NameHashSet) (path moduleName mode setupPath : String) : IO Unit := do
  let started ← IO.monoMsNow
  let finish (ok : Bool) (extra : List (String × Json)) : IO Unit := do
    emit (Json.mkObj ([("done", toJson path), ("ok", Json.bool ok),
      ("ms", toJson ((← IO.monoMsNow) - started))] ++ extra))
  emit (Json.mkObj [("file", path), ("module", moduleName)])
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let headerTree ← (treeJson (← mkEmptyEnvironment) inputCtx.fileMap { header := "" }
    (fun _ => false) 100000 header).run' {}
  emit (Json.mkObj [("header", headerTree), ("r", rangeJson inputCtx.fileMap header)])
  if mode == "header" then
    return (← finish true [])
  enableInitializersExecution
  let (lakeOptions, lakeModule) ← lakeSetup setupPath
  let opts : Options := lakeOptions
    |>.insert `maxHeartbeats (DataValue.ofNat 0)
    |>.insert `Elab.async (DataValue.ofBool false)
    |>.insert `debug.skipKernelTC (DataValue.ofBool true)
    |>.insert `warningAsError (DataValue.ofBool false)
  let headerSyntax : HeaderSyntax := header
  let (env, messages) ← processHeaderCore headerSyntax.startPos headerSyntax.imports
    (headerSyntax.isModule || lakeModule) opts messages inputCtx (mainModule := moduleName.toName)
  if messages.hasErrors then
    return (← finish false [("fatal", toJson ((← firstError messages).getD "header error"))])
  let isProject (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some idx => projectModules.contains env.header.moduleNames[idx]!
    | none => true  -- declared by this file
  let imported ← IO.monoMsNow
  let commandState := Command.mkState env messages opts
  let state : Frontend.State := { commandState, parserState, cmdPos := parserState.pos }
  discard <| (commandLoop isProject 1 |>.run { inputCtx }).run state
  finish true [("import_ms", toJson (imported - started))]

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let projectFile :: jobs := args
    | IO.eprintln "usage: PROJECT_MODULES_FILE PATH<TAB>MODULE<TAB>MODE..."; return 2
  let projectModules : NameHashSet :=
    (← readLines projectFile).foldl (fun s m => s.insert m.toName) {}
  for job in jobs do
    match job.splitOn "\t" with
    | [path, moduleName, mode] => processFile projectModules path moduleName mode ""
    | [path, moduleName, mode, setup] => processFile projectModules path moduleName mode setup
    | _ => IO.eprintln s!"invalid job: {job}"; return 2
  return 0
""".strip()

_FRONTEND_PATH = "/tmp/_lean_strip_frontend.lean"
_FRONTEND_MODULES_PATH = "/tmp/_lean_strip_frontend_modules.txt"

# Seconds one file may take before the strip falls back to the Python logic.
DEFAULT_FILE_TIMEOUT = 1800


@dataclass(frozen=True)
class Node:
    """A syntax tree node; ``start``/``end`` are offsets into the file text."""

    kind: str = ""
    start: int | None = None
    end: int | None = None
    atom: str | None = None
    ident: str | None = None
    # Lean's `resolveGlobalName` (constant, remaining field accesses) and
    # `resolveNamespace` for an identifier, in the scope of its command.
    globals: tuple[tuple[str, tuple[str, ...]], ...] = ()
    namespaces: tuple[str, ...] = ()
    children: tuple["Node", ...] = ()
    command: bool = False
    declaration: bool = False
    # A subtree the script left out (too large to report).
    big: bool = False

    @property
    def span(self) -> tuple[int, int] | None:
        if self.start is None or self.end is None:
            return None
        return self.start, self.end

    def walk(self) -> Iterator["Node"]:
        yield self
        for child in self.children:
            yield from child.walk()

    def idents(self) -> list["Node"]:
        return [node for node in self.walk() if node.ident is not None and node.span]

    def atoms(self) -> list[str]:
        return [node.atom for node in self.walk() if node.atom is not None]

    def child(self, index: int) -> "Node":
        return self.children[index] if 0 <= index < len(self.children) else Node()


@dataclass(frozen=True)
class Binder:
    """A `variable` binder in scope: its source span and the names it binds."""

    start: int
    end: int
    names: tuple[str, ...]


@dataclass(frozen=True)
class Reference:
    """Project constants a term elaborated at ``start:end`` denotes."""

    start: int
    end: int
    constants: tuple[str, ...]


@dataclass(frozen=True)
class LocalReference:
    """A term at ``start:end`` that denotes the local variable ``name``."""

    start: int
    end: int
    name: str


@dataclass(frozen=True)
class Command:
    index: int
    kind: str
    start: int
    end: int
    namespace: str
    declaration: bool
    opens: tuple[str, ...] = ()
    variables: tuple[Binder, ...] = ()
    tree: Node | None = None
    references: tuple[Reference, ...] = ()
    locals: tuple[LocalReference, ...] = ()
    error: str | None = None


@dataclass
class FileSyntax:
    """Lean's view of one source file, as offsets into ``text``."""

    path: str
    module: str
    text: str
    mode: str
    header: Node | None = None
    commands: list[Command] = field(default_factory=list)
    # Time inside Lean for the whole file, and for its imports alone.
    seconds: float = 0.0
    import_seconds: float = 0.0


class _Offsets:
    """Lean positions (1-based line, codepoint column) as offsets into ``text``.

    Lean reads CRLF files with normalized line endings; columns before the
    line end are the same either way.
    """

    def __init__(self, text: str) -> None:
        self.text = text
        self.line_starts = [0]
        self.line_starts.extend(index + 1 for index, char in enumerate(text) if char == "\n")

    def offset(self, line: int, column: int) -> int:
        if line < 1:
            return 0
        if line > len(self.line_starts):
            return len(self.text)
        start = self.line_starts[line - 1]
        following = self.line_starts[line] - 1 if line < len(self.line_starts) else len(self.text)
        return min(start + column, following)

    def span(self, value: Any) -> tuple[int, int] | None:
        if not isinstance(value, list) or len(value) != 4:
            return None
        start = self.offset(int(value[0]), int(value[1]))
        end = self.offset(int(value[2]), int(value[3]))
        return start, end

    def line_column(self, offset: int) -> tuple[int, int]:
        line = bisect_right(self.line_starts, offset)
        return line, offset - self.line_starts[line - 1]


def _node(data: Any, offsets: _Offsets) -> Node:
    if not isinstance(data, dict):
        return Node()
    span = offsets.span(data.get("r"))
    start, end = span if span else (None, None)
    if "a" in data:
        return Node(start=start, end=end, atom=str(data["a"]))
    if "i" in data:
        return Node(
            start=start, end=end, ident=str(data["i"]),
            globals=tuple((str(name), tuple(fields)) for name, fields in data.get("g", ())),
            namespaces=tuple(str(name) for name in data.get("n", ())),
        )
    return Node(
        kind=str(data.get("k", "")), start=start, end=end,
        children=tuple(_node(child, offsets) for child in data.get("c", ())),
        command=bool(data.get("cmd")), declaration=bool(data.get("decl")),
        big=bool(data.get("big")),
    )


def _command(data: dict[str, Any], offsets: _Offsets) -> Command | None:
    span = offsets.span(data.get("r"))
    if span is None:
        return None
    variables = []
    for binder_range, names in data.get("v", ()):
        binder_span = offsets.span(binder_range)
        if binder_span:
            variables.append(Binder(*binder_span, tuple(str(name) for name in names)))
    references = []
    for term_range, constants in data.get("f", ()):
        term_span = offsets.span(term_range)
        if term_span:
            references.append(Reference(*term_span, tuple(str(name) for name in constants)))
    local_references = []
    for term_range, name in data.get("l", ()):
        term_span = offsets.span(term_range)
        if term_span:
            local_references.append(LocalReference(*term_span, str(name)))
    opens = tuple(
        str(entry["s"]) for entry in data.get("o", ()) if isinstance(entry, dict) and "s" in entry
    )
    return Command(
        index=int(data.get("c", 0)), kind=str(data.get("k", "")),
        start=span[0], end=span[1],
        namespace="" if data.get("ns") == "[anonymous]" else str(data.get("ns", "")),
        declaration=bool(data.get("decl")),
        opens=opens, variables=tuple(variables),
        tree=_node(data["t"], offsets) if isinstance(data.get("t"), dict) else None,
        references=tuple(references), locals=tuple(local_references),
        error=data.get("e"),
    )


def parse_frontend_output(
    lines: Iterable[str], texts: dict[str, str],
) -> tuple[dict[str, FileSyntax], dict[str, str]]:
    """Parse the script's JSON lines against the texts Lean read.

    Returns the analysed files and, for every other file the output mentions,
    why it has no analysis. A file without its closing ``done`` record (a
    crash or a timeout) is a failure, never a partial analysis.
    """

    results: dict[str, FileSyntax] = {}
    failures: dict[str, str] = {}
    current: FileSyntax | None = None
    offsets: _Offsets | None = None
    for line in lines:
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            data = json.loads(line)
        except json.JSONDecodeError:
            continue
        if not isinstance(data, dict):
            continue
        if "file" in data:
            path = str(data["file"])
            if path not in texts:
                current = offsets = None
                continue
            current = FileSyntax(path=path, module=str(data.get("module", "")),
                                 text=texts[path], mode="header")
            offsets = _Offsets(texts[path])
            failures[path] = "incomplete output"
        elif current is None or offsets is None:
            continue
        elif "header" in data:
            current.header = _node(data["header"], offsets)
        elif "done" in data:
            if data.get("ok") is True:
                results[current.path] = current
                failures.pop(current.path, None)
                current.seconds = float(data.get("ms", 0)) / 1000
                current.import_seconds = float(data.get("import_ms", 0)) / 1000
            else:
                failures[current.path] = str(data.get("fatal", "failed"))
            current = offsets = None
        elif "c" in data:
            command = _command(data, offsets)
            if command is not None:
                current.commands.append(command)
                current.mode = "full"
    return results, failures


@dataclass(frozen=True)
class FrontendJob:
    path: str
    module: str
    # "full" elaborates the file; "header" only parses its header.
    mode: str = "full"

    @property
    def setup(self) -> str:
        """The `.setup.json` Lake compiled the module with (its options)."""

        relative = "/".join(
            component[1:-1] if component.startswith("«") and component.endswith("»") else component
            for component in _split_module(self.module)
        )
        return f"/testbed/.lake/build/ir/{relative}.setup.json"


def _split_module(module: str) -> list[str]:
    """Components of a module name, keeping «quoted» components whole."""

    components, current, quoted = [], "", False
    for char in module:
        if char == "«":
            quoted = True
        elif char == "»":
            quoted = False
        if char == "." and not quoted:
            components.append(current)
            current = ""
        else:
            current += char
    components.append(current)
    return components


def _install_frontend_script(env: Any, project_modules: Iterable[str]) -> None:
    env.write_file_bytes(_FRONTEND_PATH, (_FRONTEND_LEAN + "\n").encode("utf-8"))
    env.write_file_bytes(
        _FRONTEND_MODULES_PATH,
        ("\n".join(sorted(set(project_modules))) + "\n").encode("utf-8"),
    )


# What `lake env` sets for `lean`; read once rather than per process.
_LAKE_ENVIRONMENT = ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH")
_LAKE_ENVIRONMENT_PATH = "/tmp/_lean_strip_lake_env.sh"


def _lean_command(env: Any) -> str:
    """How to start the project's `lean` with Lake's environment.

    `lake env` costs most of a second per process, so its variables are
    saved once to a shell file that each process sources. The values stay
    in the shell: passed through Python, the workspace's path mapping would
    rewrite host paths outside the project, such as the `.lake/packages` a
    scratch copy links to. `lake env lean` stays the fallback.
    """

    exports = "".join(
        f'case "${name}" in *"\'"*) exit 3;; esac; '
        f"printf \"export {name}='%s'\\n\" \"${name}\"; "
        for name in _LAKE_ENVIRONMENT
    )
    result = env.execute(
        "cd /testbed && lake env sh -c "
        + shlex.quote(f'test -n "$LEAN_PATH" && test -x "$LEAN_SYSROOT/bin/lean" && {{ {exports}}}')
        + f" > {_LAKE_ENVIRONMENT_PATH}",
        timeout=600,
    )
    if result.get("returncode") != 0:
        return "lake env lean"
    return f'. {_LAKE_ENVIRONMENT_PATH} && "$LEAN_SYSROOT/bin/lean"'


def _run_batch(
    env: Any, lean: str, jobs: list[FrontendJob], texts: dict[str, str], timeout: float,
) -> tuple[dict[str, FileSyntax], dict[str, str], float]:
    # Jobs go on the command line, where the workspace maps logical paths.
    arguments = " ".join(
        shlex.quote(f"{job.path}\t{job.module}\t{job.mode}\t{job.setup}") for job in jobs
    )
    started = time.perf_counter()
    result = env.execute_stream(
        f"cd /testbed && {lean} --run {_FRONTEND_PATH} {_FRONTEND_MODULES_PATH} {arguments}",
        timeout=timeout,
    )
    elapsed = time.perf_counter() - started
    results, failures = parse_frontend_output(
        result.get("output", "").splitlines(), {job.path: texts[job.path] for job in jobs},
    )
    for job in jobs:
        if job.path not in results and job.path not in failures:
            output = result.get("output", "")
            failures[job.path] = (
                "timed out" if result.get("timed_out")
                else f"exit {result.get('returncode')}: {output[-300:].strip()}"
            )
        elif job.path in failures and result.get("timed_out"):
            failures[job.path] = "timed out"
    return results, failures, elapsed


# Characters of job arguments per process. A command line is one `bash -c`
# argument, which Linux limits to 128 KiB (after workspace paths are mapped).
_MAX_JOB_ARGUMENTS = 16_000


def _header_batches(jobs: list[FrontendJob]) -> list[list[FrontendJob]]:
    """Header jobs, several per process but within the command-line limit."""

    batches: list[list[FrontendJob]] = []
    size = _MAX_JOB_ARGUMENTS
    for job in jobs:
        length = len(job.path) + len(job.module) + len(job.setup) + 16
        if size + length > _MAX_JOB_ARGUMENTS:
            batches.append([])
            size = 0
        batches[-1].append(job)
        size += length
    return batches


def analyze_sources(
    env: Any,
    jobs: list[FrontendJob],
    texts: dict[str, str],
    project_modules: Iterable[str],
    *,
    workers: int = 8,
    timeout: float = DEFAULT_FILE_TIMEOUT,
    progress: Any = None,
) -> tuple[dict[str, FileSyntax], dict[str, Any]]:
    """Run the Lean pass on ``jobs`` against the built project in ``env``.

    ``texts`` holds the exact source of every job's file as it is on disk.
    Each full job runs in its own Lean process, ``workers`` at a time; header
    jobs share one process. Returns the analyses and a report with the
    failures and timings.
    """

    started = time.perf_counter()
    full = sorted((job for job in jobs if job.mode == "full"), key=lambda job: job.path)
    header = sorted((job for job in jobs if job.mode != "full"), key=lambda job: job.path)
    batches = [[job] for job in full] + _header_batches(header)
    analyses: dict[str, FileSyntax] = {}
    failures: dict[str, str] = {}
    process_seconds: dict[str, float] = {}
    if batches:
        _install_frontend_script(env, project_modules)
        lean = _lean_command(env)
        done = 0
        with ThreadPoolExecutor(max_workers=max(1, workers)) as pool:
            futures = [
                pool.submit(_run_batch, env, lean, batch, texts,
                            timeout if batch[0].mode == "full" else max(timeout, 600))
                for batch in batches
            ]
            for batch, future in zip(batches, futures):
                try:
                    results, batch_failures, elapsed = future.result()
                except Exception as error:  # a crashed runner only costs that batch
                    results, batch_failures, elapsed = {}, {
                        job.path: f"runner error: {error}" for job in batch
                    }, 0.0
                analyses.update(results)
                failures.update(batch_failures)
                if batch[0].mode == "full":
                    process_seconds[batch[0].path] = round(elapsed, 2)
                done += 1
                if progress is not None:
                    progress(f"Lean pass: {done}/{len(batches)} file(s)")
    seconds = sorted(process_seconds.values())
    report = {
        "files_requested": len(jobs),
        "files_elaborated": len(full),
        "files_header_only": len(header),
        "files_analyzed": len(analyses),
        "failures": {path.removeprefix("/testbed/"): reason for path, reason in sorted(failures.items())},
        "commands_with_errors": sum(
            1 for analysis in analyses.values() for command in analysis.commands if command.error
        ),
        "wall_seconds": round(time.perf_counter() - started, 1),
        # Inside Lean: importing the built dependencies, then the file itself.
        "import_seconds_total": round(sum(a.import_seconds for a in analyses.values()), 1),
        "elaboration_seconds_total": round(
            sum(a.seconds - a.import_seconds for a in analyses.values() if a.mode == "full"), 1
        ),
        "process_seconds_total": round(sum(seconds), 1),
        "process_seconds_median": seconds[len(seconds) // 2] if seconds else 0.0,
        "process_seconds_max": seconds[-1] if seconds else 0.0,
        "slowest_files": [
            path.removeprefix("/testbed/")
            for path, _ in sorted(process_seconds.items(), key=lambda item: -item[1])[:5]
        ],
    }
    return analyses, report
