"""Internal .olean reader for the canonical preprocessing dependency graph.

Lean loads compiled declarations and ranges; this is one evidence layer, never
an independently published dependency graph. Use dependency_graph for graphs.
"""
from __future__ import annotations

import shlex
import time
from collections import deque
from typing import Any

from .identity import Dependencies

# Lean 4 script that emits the project's declaration dependency graph, so the
# keep-set (transitive forward closure of the seed signatures) can be computed
# in Python (see strip.compute_keep_set — testable, and re-expandable during
# the rebuild-recovery loop). Emits three record kinds:
#
#   DECL\tname\tmodule\tstartLine\tstartCol\tendLine\tendCol\tkind\tmetaFlag
#   DEP\tmodule\tname\ttargetModule\tdep            (one record per edge)
#   EXTNS\tnamespace
#
# Only declarations with a source range are emitted; auto-generated
# .rec/.eq_1/.match_n/etc. have none and are folded into their source owner.
#
# metaFlag is "meta" if the decl is parsing/elaboration machinery (its type
# mentions Lean.ParserDescr / Macro / Syntax — i.e. a `notation`/`macro`/`elab`
# declaration). Such decls are force-kept: they're used implicitly at parse
# time, never appear in any term's foldConsts, and dropping them yields
# non-recoverable "elaboration function ... not implemented" errors.
#
# DEP edges are the project-local names appearing in a decl's type/value Expr
# (via Expr.foldConsts over the full type and value), each mapped to its nearest
# emitted source owner, plus structural edges (ctor->inductive, rec->family,
# inductive->ctors) so seeding any member pulls its whole family. Range-less
# auxiliaries a term references (`foo._proof_1`, `match_n`, `grind`/`omega`
# auxiliary theorems) are followed into their own type and value, so a lemma
# used only inside one is still a dependency of the declaration.
#
# EXTNS lists namespace prefixes that also contain declarations from outside
# the project modules, i.e. namespaces the project extends rather than owns.
#
# findDeclarationRanges?'s command range INCLUDES the leading docstring, so
# deleting a drop-decl's [start,end] line span removes its docstring too, and
# keeping a decl keeps its docstring — no orphaning. Standalone `@[attr]` lines
# above the keyword are NOT in the range; the caller extends drop-deletions
# upward over them.
_DUMP_KEEP_LEAN = r"""
import Lean
open Lean Meta

/-- The ranged project declarations reachable from the range-less project
constant `n` (`foo._proof_1`, `foo.match_1`, a `grind`/`omega` auxiliary, ...)
through its type and value, following further range-less constants.
Memoized; a constant on the current path counts as empty, which cuts cycles. -/
partial def auxOwners (env : Environment) (isProject : Name → Bool)
    (ranged : NameHashSet) (owner? : Name → Option Name)
    (memo : IO.Ref (Std.HashMap Name (Array Name))) (n : Name) : IO (Array Name) := do
  if let some cached := (← memo.get)[n]? then
    return cached
  memo.modify (·.insert n #[])
  let some cinfo := env.find? n | return #[]
  let exprs := match cinfo with
    | .defnInfo val   => #[val.type, val.value]
    | .thmInfo val    => #[val.type, val.value]
    | .opaqueInfo val => #[val.type, val.value]
    | info            => #[info.type]
  let consts := exprs.foldl
    (fun acc e => e.foldConsts acc fun c acc => if isProject c && c != n then acc.push c else acc) #[]
  -- Each owner once, in order of first occurrence. Concatenating the
  -- auxiliaries' lists as they are repeats an owner once per path to it, and
  -- the paths through auxiliaries that share auxiliaries are exponentially
  -- many: the range-less LRAT step lemmas behind PALOMAR-2026-10-22-000009's
  -- `pairing8Refutation` would have given it a list of about 10^104 names.
  let mut out : Array Name := #[]
  let mut seen : NameHashSet := {}
  for c in consts do
    if ranged.contains c then
      if !seen.contains c then
        seen := seen.insert c
        out := out.push c
    else
      if let some owner := owner? c then
        if !seen.contains owner then
          seen := seen.insert owner
          out := out.push owner
      for owner in (← auxOwners env isProject ranged owner? memo c) do
        if !seen.contains owner then
          seen := seen.insert owner
          out := out.push owner
  memo.modify (·.insert n out)
  return out

unsafe def dumpModule (moduleArgs importArgs : List String) : IO Unit := do
  let imports := (importArgs.map fun s => { module := s.toName : Import }).toArray
  let env ← importModules imports {} 0
  let loadedModules := env.header.moduleNames
  let projModNames : NameHashSet :=
    moduleArgs.foldl (fun names module =>
      let moduleName := module.toName
      if loadedModules.contains moduleName then names.insert moduleName else names) {}

  -- Several roots share this environment when the batch imports cleanly. Each
  -- root's output must equal what an environment of its own import closure
  -- gives, and the two can differ only where a name is declared by more than
  -- one loaded module and one of them is a project module: the shared
  -- environment credits it to one copy, which a root's own environment may
  -- not load. A root whose closure contains such a module is reported as
  -- ISOLATE and is run again in a process of its own.
  let batched := importArgs.length > 1
  let mut moduleIdx : Std.HashMap Name Nat := {}
  let mut moduleIdxByString : Std.HashMap String Nat := {}
  for i in [0:env.header.moduleNames.size] do
    moduleIdx := moduleIdx.insert env.header.moduleNames[i]! i
    moduleIdxByString := moduleIdxByString.insert env.header.moduleNames[i]!.toString i
  let mut ambiguousModules : NameHashSet := {}
  let mut ambiguousConsts : NameHashSet := {}
  if batched then
    for i in [0:env.header.moduleNames.size] do
      let declarer := env.header.moduleNames[i]!
      if let some data := env.header.moduleData[i]? then
        for cname in data.constNames do
          if let some idx := env.getModuleIdxFor? cname then
            let credited := env.header.moduleNames[idx]!
            if credited != declarer && (projModNames.contains credited || projModNames.contains declarer) then
              ambiguousModules := (ambiguousModules.insert credited).insert declarer
              ambiguousConsts := ambiguousConsts.insert cname
  -- The modules a root's own environment loads, and whether one of them is
  -- ambiguous in this one.
  let closureOf (start : Nat) : NameHashSet × Bool := Id.run do
    let mut seen : NameHashSet := {}
    let mut touchesAmbiguous := false
    let mut stack : Array Nat := #[start]
    while !stack.isEmpty do
      let i := stack[stack.size - 1]!
      stack := stack.pop
      let modName := env.header.moduleNames[i]!
      if seen.contains modName then continue
      seen := seen.insert modName
      if ambiguousModules.contains modName then touchesAmbiguous := true
      if let some data := env.header.moduleData[i]? then
        for imp in data.imports do
          if let some j := moduleIdx[imp.module]? then
            stack := stack.push j
    return (seen, touchesAmbiguous)

  -- Types that mark a decl as parsing/elaboration machinery (notation/macro).
  let metaConsts : List Name :=
    [`Lean.ParserDescr, `Lean.TrailingParserDescr, `Lean.Macro,
     `Lean.MacroM, `Lean.Syntax, `Lean.TSyntax, `Lean.ParserDescr.Parser]

  let coreCtx : Core.Context := { fileName := "<dump_keep>", fileMap := default }
  let coreState : Core.State := { env := env }
  let action : CoreM (Array (Name × Name × ConstantInfo × String) × NameHashSet × Std.HashSet Name) := do
    -- Namespace commands do not have declaration nodes. Record every namespace
    -- prefix backed by at least one declaration outside the selected project
    -- modules. The source cleanup uses this provenance to distinguish a
    -- project-owned namespace from a project extension of an imported namespace
    -- such as `Topology` or `Function`.
    let mut importedNamespaces : Std.HashSet Name := {}
    for (name, _) in env.constants.toList do
      let isProject := match env.getModuleIdxFor? name with
        | none => false
        | some modIdx =>
          let modName := env.header.moduleNames[modIdx]!
          projModNames.contains modName
      -- An ambiguous name is reported by the isolated roots' own runs.
      if !isProject && !ambiguousConsts.contains name then
        let mut namespaceName := name.getPrefix
        while !namespaceName.isAnonymous do
          importedNamespaces := importedNamespaces.insert namespaceName
          namespaceName := namespaceName.getPrefix

    -- Pass 1: nodes = project decls that have a SOURCE RANGE. This is the key
    -- filter: it INCLUDES `private`/internal declarations (which carry a range
    -- and are referenced through dependency chains we must follow), while
    -- excluding compiler-generated decls (`.rec`/`.eq_1`/`.match_n`/...) which
    -- have no range. Filtering on `isInternal` instead (as before) silently
    -- dropped every private helper, severing dependency paths and making the
    -- closure badly incomplete.
    -- Names more than one project module declares (see below).
    let mut declaredOnce : NameHashSet := {}
    let mut dupNames : NameHashSet := {}
    for i in [0:env.header.moduleNames.size] do
      if projModNames.contains env.header.moduleNames[i]! then
        if let some data := env.header.moduleData[i]? then
          for cname in data.constNames do
            if declaredOnce.contains cname then
              dupNames := dupNames.insert cname
            else
              declaredOnce := declaredOnce.insert cname
    let mut dupModules : NameHashSet := {}
    if !dupNames.isEmpty then
      for i in [0:env.header.moduleNames.size] do
        let modName := env.header.moduleNames[i]!
        if projModNames.contains modName then
          if let some data := env.header.moduleData[i]? then
            if data.constNames.any dupNames.contains then
              dupModules := dupModules.insert modName

    let mut nodes : Array (Name × Name × ConstantInfo × String) := #[]
    let mut projNameSet : NameHashSet := {}
    for (name, cinfo) in env.constants.toList do
      match env.getModuleIdxFor? name with
      | none => pure ()
      | some modIdx =>
        let modName := env.header.moduleNames[modIdx]!
        if projModNames.contains modName && !dupNames.contains name then
          match ← findDeclarationRanges? name with
          | some dr =>
            let r := dr.range
            let rangeStr := s!"{r.pos.line}\t{r.pos.column}\t{r.endPos.line}\t{r.endPos.column}"
            nodes := nodes.push (name, modName, cinfo, rangeStr)
            projNameSet := projNameSet.insert name
          | none => pure ()

    -- A theorem two modules both declare is merged at import when the two
    -- statements agree (Lean compares types, not proofs): `env` credits the
    -- first module but may hold another module's proof. Every copy is still in
    -- its own module's data, with its own proof and range, so each becomes a
    -- node of its own module and the strip sees what each proof uses
    -- (PALOMAR-2026-09-28-000003).
    for i in [0:env.header.moduleNames.size] do
      let modName := env.header.moduleNames[i]!
      if !projModNames.contains modName || !dupModules.contains modName then continue
      let some modIdx := env.getModuleIdx? modName | continue
      let some data := env.header.moduleData[i]? | continue
      let ranges : NameMap DeclarationRanges := (declRangeExt.getModuleEntries env modIdx).foldl
        (fun acc (n, r) => acc.insert n r) {}
      for cname in data.constNames, cinfo in data.constants do
        if !dupNames.contains cname then continue
        if let some dr := ranges.find? cname then
          let r := dr.range
          let rangeStr := s!"{r.pos.line}\t{r.pos.column}\t{r.endPos.line}\t{r.endPos.column}"
          nodes := nodes.push (cname, modName, cinfo, rangeStr)
          projNameSet := projNameSet.insert cname

    return (nodes, projNameSet, importedNamespaces)
  let ((nodes, projNameSet, importedNamespaces), _) ← action.toIO coreCtx coreState

  -- Pass 2: emit DECL + DEP for each node of each root.
  let isProjectConstant (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | none => false
    | some modIdx =>
      let ownerModule := env.header.moduleNames[modIdx]!
      projModNames.contains ownerModule
  let mut nodesByModule : Std.HashMap String (Array (Name × Name × ConstantInfo × String)) := {}
  for node in nodes do
    let key := node.2.1.toString
    nodesByModule := nodesByModule.insert key (((nodesByModule[key]?).getD #[]).push node)
  for root in importArgs do
    -- `none`: this environment is the root's own, and everything it loads counts.
    let mut rootClosure : Option NameHashSet := none
    if batched then
      match moduleIdxByString[root]? with
      | none =>
        IO.println s!"ISOLATE\t{root}"
        continue
      | some idx =>
        let (closure, touchesAmbiguous) := closureOf idx
        if touchesAmbiguous then
          IO.println s!"ISOLATE\t{root}"
          continue
        rootClosure := some closure
    let closure? := rootClosure
    let inClosure (n : Name) : Bool :=
      match closure? with
      | none => true
      | some closure =>
        match env.getModuleIdxFor? n with
        | none => false
        | some modIdx => closure.contains env.header.moduleNames[modIdx]!
    -- A prefix only another root's closure declares is no owner here.
    let rec findSourceOwner? (n : Name) : Option Name :=
      if projNameSet.contains n && inClosure n then
        some n
      else if n.isAnonymous then
        none
      else
        findSourceOwner? n.getPrefix
    let auxMemo ← IO.mkRef ({} : Std.HashMap Name (Array Name))
    for (name, modName, cinfo, rangeStr) in (nodesByModule[root]?).getD #[] do
      let kind := match cinfo with
        | .thmInfo _    => "theorem"
        | .defnInfo _   => "def"
        | .axiomInfo _  => "axiom"
        | .opaqueInfo _ => "opaque"
        | .ctorInfo _   => "ctor"
        | .recInfo _    => "rec"
        | .inductInfo _ => "inductive"
        | .quotInfo _   => "quot"
      let isMeta := cinfo.type.foldConsts false (fun n acc => acc || metaConsts.contains n)
      let metaFlag := if isMeta then "meta" else "normal"
      IO.println s!"DECL\t{name}\t{modName}\t{rangeStr}\t{kind}\t{metaFlag}"
      -- Project constants referenced by the type and value. A range-less one
      -- (`name._proof_1`, a `match` or `grind` auxiliary) folds to its ranged
      -- owner, and its own body is followed too: a lemma used only inside such
      -- an auxiliary is a dependency of `name` that the term itself never names.
      let exprs := match cinfo with
        | .defnInfo val   => #[cinfo.type, val.value]
        | .thmInfo val    => #[cinfo.type, val.value]
        | .opaqueInfo val => #[cinfo.type, val.value]
        | _               => #[cinfo.type]
      let consts := exprs.foldl
        (fun acc e => e.foldConsts acc fun n acc => if isProjectConstant n then acc.push n else acc) #[]
      let mut refs : Array Name := #[]
      for n in consts do
        if projNameSet.contains n then
          refs := refs.push n
        else
          if let some owner := findSourceOwner? n then
            refs := refs.push owner
          refs := refs ++ (← auxOwners env isProjectConstant projNameSet findSourceOwner? auxMemo n)
      let mut seen : NameHashSet := {}
      let mut unique : Array Name := #[]
      for ref in refs do
        if ref != name && !seen.contains ref then
          seen := seen.insert ref
          unique := unique.push ref
      refs := unique
      refs := match cinfo with
        | .ctorInfo val   => refs.push val.induct
        | .recInfo val    => refs ++ val.all.toArray
        | .inductInfo val => refs ++ val.ctors.toArray
        | _               => refs
      -- One record per edge. Lean names may contain quoted components with
      -- spaces (for example ``«Adic spaces»``), so a whitespace-separated
      -- dependency payload is not a lossless wire format.
      for ref in refs do
        if let some idx := env.getModuleIdxFor? ref then
          IO.println s!"DEP\t{modName}\t{name}\t{env.header.moduleNames[idx]!}\t{ref}"
  for ns in importedNamespaces do
    IO.println s!"EXTNS\t{ns}"

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let (moduleArgs, importArgs) ←
    match args with
    | ["--modules-file", path] => do
      let content ← IO.FS.readFile path
      let modules := content.splitOn "\n" |>.filter (fun s => !s.isEmpty)
      pure (modules, modules)
    | ["--modules-file", projectPath, "--roots-file", rootsPath] => do
      let projectContent ← IO.FS.readFile projectPath
      let rootsContent ← IO.FS.readFile rootsPath
      let modules := projectContent.splitOn "\n" |>.filter (fun s => !s.isEmpty)
      let roots := rootsContent.splitOn "\n" |>.filter (fun s => !s.isEmpty)
      pure (modules, roots)
    | _ => pure (args, args)
  -- A process owns exactly one environment, for all of its roots: imported
  -- .olean regions are retained for the process lifetime even after the
  -- Environment is no longer used.
  if importArgs.isEmpty then
    throw <| IO.userError "expected at least one root module"
  dumpModule moduleArgs importArgs
""".strip()

# Logical scratch paths (mapped to the local workspace) for the script and its
# module list.
_DUMP_KEEP_PATH = "/tmp/_dump_keep.lean"
_DUMP_KEEP_MODULES_PATH = "/tmp/_dump_keep_modules.txt"
_DUMP_KEEP_ROOT_PATH = "/tmp/_dump_keep_root.txt"

# Roots per Lean process. Each process imports Mathlib and its other
# dependencies once, so one process per root costs a full import per module
# (PALOMAR-2026-10-27-000003: 3,940 modules at 4-29 s each exceeded the
# budget). A batch's environment is the union of its roots' closures, which is
# no larger than the whole project's.
_ROOTS_PER_PROCESS = 128

# One declaration: name, module, source range, kind, meta flag. Other layers
# add a `keep` bool; anonymous-example rows use the same shape.
DeclRange = dict[str, Any]


def _install_dump_keep_script(env: Any, *, timeout: float) -> None:
    """Write the keep-graph Lean script into the workspace scratch directory."""
    cmd = f"cat > {_DUMP_KEEP_PATH} << 'LEANDUMPKEEP_EOF'\n{_DUMP_KEEP_LEAN}\nLEANDUMPKEEP_EOF"
    result = env.execute(cmd, timeout=timeout)
    if result.get("returncode", 1) != 0 or result.get("timed_out"):
        raise DeclGraphExtractionError(
            returncode=result.get("returncode"), timed_out=result.get("timed_out"),
            diagnostics=result.get("output", "")[-4000:], declarations=0,
        )


class DeclGraphExtractionError(RuntimeError):
    """Keep the subprocess failure distinct from a genuinely empty graph."""

    def __init__(self, *, returncode, timed_out, diagnostics, declarations, root_module=None):
        self.details = {
            "returncode": returncode, "timed_out": bool(timed_out),
            "diagnostics": diagnostics, "partial_declarations": declarations,
            "root_module": root_module,
            "failure_kind": "timeout" if timed_out else "killed" if returncode in (137, -9) else "process_error",
        }
        super().__init__(
            f"Lean graph extraction {self.details['failure_kind']} "
            f"(root={root_module!r}, rc={returncode}, partial declarations={declarations}): {diagnostics[-2000:]}"
        )


def read_olean_declarations(
    env: Any, modules: list[str], *, timeout: int = 3600,
) -> tuple[list[DeclRange], Dependencies, set[str]]:
    """Run the keep-graph Lean script; return declarations, edges, namespaces.

    `decls` is one DeclRange per project decl (with a `meta` bool). `deps` maps
    each (module, name) identity to the project identities it references.
    `imported_namespaces` contains exact namespace prefixes with at least one
    declaration owned outside the selected project modules. The caller computes
    the keep-set in Python (strip.compute_keep_set).

    `modules` is the non-empty list of project modules to import and scan.
    Roots run in batches, one fresh Lean process per batch with the complete
    project-module list; the process releases its imported .olean regions on
    exit. Each root's records are those of an environment of its own import
    closure. A root that a shared environment cannot answer for (the Lean
    script reports it as ISOLATE) runs again alone, and a batch that fails
    is split in halves, so a failure is reported for the single root that
    fails alone. A failed batch contributes nothing. Output is streamed; all
    processes and script setup share one timeout. No graph is returned unless
    every root succeeds within that budget.

    Requires `lake build` to have succeeded so .olean files exist.
    Raises DeclGraphExtractionError if the query fails.
    """
    modules = list(dict.fromkeys(modules))
    if not modules:
        return [], {}, set()
    deadline = time.monotonic() + timeout
    decls: list[DeclRange] = []
    deps: Dependencies = {}
    imported_namespaces: set[str] = set()

    def remaining(root_module: str | None = None, pending: int = 0) -> float:
        seconds = deadline - time.monotonic()
        if seconds <= 0:
            raise DeclGraphExtractionError(
                returncode=None, timed_out=True, diagnostics="overall extraction timeout exhausted",
                declarations=len(decls) + pending, root_module=root_module,
            )
        return seconds

    _install_dump_keep_script(env, timeout=remaining())

    payload = ("\n".join(modules) + "\n").encode("utf-8")
    env.write_file_bytes(_DUMP_KEEP_MODULES_PATH, payload)
    lean_command = (
        f"lean --run {_DUMP_KEEP_PATH} "
        f"--modules-file {_DUMP_KEEP_MODULES_PATH} "
        f"--roots-file {_DUMP_KEEP_ROOT_PATH}"
    )
    # One invocation per batch releases Lean's imports on exit. The workspace
    # cancels the entire Lake/Lean process group if the shared budget expires.
    cmd = "cd /testbed && lake env sh -c " + shlex.quote("exec " + lean_command)
    queue = deque(
        modules[index:index + _ROOTS_PER_PROCESS]
        for index in range(0, len(modules), _ROOTS_PER_PROCESS)
    )
    while queue:
        batch = queue.popleft()
        batch_decls: list[DeclRange] = []
        batch_deps: list[tuple[tuple[str, str], tuple[str, str]]] = []
        batch_namespaces: set[str] = set()
        isolated: list[str] = []
        diagnostics: list[str] = []

        def consume_line(line: str) -> None:
            line = line.rstrip("\r\n")
            parts = line.split("\t")
            if parts and parts[0] == "DECL" and len(parts) == 9:
                _, name, module, sl, sc, el, ec, kind, meta = parts
                try:
                    batch_decls.append({
                        "name": name, "module": module,
                        "start_line": int(sl), "start_col": int(sc),
                        "end_line": int(el), "end_col": int(ec),
                        "kind": kind, "meta": meta == "meta",
                    })
                except ValueError:
                    diagnostics.append(line)
            elif parts and parts[0] == "DEP" and len(parts) == 5:
                batch_deps.append(((parts[1], parts[2]), (parts[3], parts[4])))
            elif parts and parts[0] == "EXTNS" and len(parts) == 2:
                batch_namespaces.add(parts[1])
            elif parts and parts[0] == "ISOLATE" and len(parts) == 2:
                isolated.append(parts[1])
            elif line:
                diagnostics.append(line)
            if len(diagnostics) > 200:
                del diagnostics[:-200]

        root_module = batch[0] if len(batch) == 1 else None
        env.write_file_bytes(_DUMP_KEEP_ROOT_PATH, ("\n".join(batch) + "\n").encode("utf-8"))
        result = env.execute_stream(
            cmd,
            timeout=remaining(root_module),
            on_output=consume_line,
            capture_output=False,
        )
        failed = result.get("returncode", 1) != 0 or result.get("timed_out")
        if failed and len(batch) > 1 and not result.get("timed_out"):
            half = len(batch) // 2
            queue.extendleft([batch[half:], batch[:half]])
            continue
        if failed:
            detail = "\n".join(diagnostics)[-4000:] or result.get("output", "")[-4000:]
            raise DeclGraphExtractionError(
                returncode=result.get("returncode"), timed_out=result.get("timed_out"),
                diagnostics=detail, declarations=len(decls) + len(batch_decls), root_module=root_module,
            )
        if len(batch) == 1 and isolated:
            raise DeclGraphExtractionError(
                returncode=result.get("returncode"), timed_out=False,
                diagnostics=f"a single root was reported as ISOLATE: {isolated}",
                declarations=len(decls), root_module=root_module,
            )
        unknown = set(isolated) - set(batch)
        if unknown:
            raise DeclGraphExtractionError(
                returncode=result.get("returncode"), timed_out=False,
                diagnostics=f"ISOLATE for modules outside the batch: {sorted(unknown)}",
                declarations=len(decls), root_module=root_module,
            )
        remaining(root_module, len(batch_decls))
        decls.extend(batch_decls)
        for source, target in batch_deps:
            deps.setdefault(source, set()).add(target)
        imported_namespaces |= batch_namespaces
        queue.extendleft([root] for root in reversed(list(dict.fromkeys(isolated))))
    return decls, deps, imported_namespaces
