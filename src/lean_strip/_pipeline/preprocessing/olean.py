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
  -- gives. The two can differ only at a name more than one loaded module
  -- declares where one of them is a project module: the shared environment
  -- credits one copy (and may hold another's value), which a root's own
  -- environment may not load. Such names are classified after pass 1; a root
  -- whose closure contains a module that makes its answer differ is reported
  -- as ISOLATE and is run again in a process of its own.
  let batched := importArgs.length > 1
  let mut moduleIdx : Std.HashMap Name Nat := {}
  let mut moduleIdxByString : Std.HashMap String Nat := {}
  for i in [0:env.header.moduleNames.size] do
    moduleIdx := moduleIdx.insert env.header.moduleNames[i]! i
    moduleIdxByString := moduleIdxByString.insert env.header.moduleNames[i]!.toString i
  -- name -> (credited module, the other declaring modules with their copies),
  -- for names with a project module among their declarers
  let mut ambiguous : Std.HashMap Name (Name × Array (Name × ConstantInfo)) := {}
  if batched then
    let mut declaredAgain : Std.HashMap Name (Name × Array (Name × ConstantInfo)) := {}
    for i in [0:env.header.moduleNames.size] do
      let declarer := env.header.moduleNames[i]!
      if let some data := env.header.moduleData[i]? then
        for cname in data.constNames, cinfo in data.constants do
          if let some idx := env.getModuleIdxFor? cname then
            let credited := env.header.moduleNames[idx]!
            if credited != declarer then
              let (_, copies) := (declaredAgain[cname]?).getD (credited, #[])
              declaredAgain := declaredAgain.insert cname (credited, copies.push (declarer, cinfo))
    for (cname, (credited, copies)) in declaredAgain.toList do
      if projModNames.contains credited || copies.any (fun (declarer, _) => projModNames.contains declarer) then
        ambiguous := ambiguous.insert cname (credited, copies)

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
      -- Ambiguous names are added after pass 2, from the roots that load them.
      if !isProject && !ambiguous.contains name then
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

  -- Classify the ambiguous names. Modules come after their imports in every
  -- environment, and the first declarer loaded is credited. So a declarer
  -- that imports the credited module never takes the credit from it, and a
  -- root whose closure holds no other declarer sees the name credited as
  -- here. Whether the rest of what a root sees agrees is checked per name;
  -- where it does, only the declarers that do not import the credited module
  -- set a root apart, and otherwise every declarer does:
  -- * credited to a dependency module, with at most one project copy or
  --   none with a range: the name is an imported constant wherever it is
  --   credited as here, and is never a node.
  -- * credited to a project module: its value must be the credited copy (a
  --   root of the credited module loads no other), and either every project
  --   copy has a range, so that each environment finds one, or none does
  --   and every copy is the same constant, whose body auxOwners follows.
  -- A name every copy of which is the same range-less constant (`foo.eq_1`,
  -- `foo.congr_simp`, which Lean realizes in each module that first needs
  -- them) sets no root apart at all if it is a project constant in every
  -- environment, or if being one changes nothing: no prefix is a project
  -- declaration (no source owner) and its body names no project or ambiguous
  -- constant (no auxiliary owners). It is never a node or an edge target
  -- either way. Its namespaces count as imported for every root that loads
  -- a dependency copy: a dependency declares a constant in them. (In a
  -- root's own environment that depends on which copy import order credits,
  -- PALOMAR-2026-10-27-000003, where a root loading both would otherwise run
  -- alone.)
  let sameConstant (a b : ConstantInfo) : Bool :=
    a.levelParams == b.levelParams && a.type == b.type && a.value? == b.value?
  let copyIn (modName cname : Name) : Option ConstantInfo := do
    let i ← moduleIdx[modName]?
    let data ← env.header.moduleData[i]?
    let j ← data.constNames.findIdx? (· == cname)
    data.constants[j]?
  let hasRange (modName cname : Name) : Bool := Id.run do
    let some modIdx := env.getModuleIdx? modName | return false
    return (declRangeExt.getModuleEntries env modIdx).any (·.1 == cname)
  let imports (start target : Name) : Bool := Id.run do
    let some first := moduleIdx[start]? | return false
    let mut seen : NameHashSet := {}
    let mut stack : Array Nat := #[first]
    while !stack.isEmpty do
      let i := stack[stack.size - 1]!
      stack := stack.pop
      let modName := env.header.moduleNames[i]!
      if seen.contains modName then continue
      if modName == target then return true
      seen := seen.insert modName
      if let some data := env.header.moduleData[i]? then
        for imp in data.imports do
          if let some j := moduleIdx[imp.module]? then
            stack := stack.push j
    return false
  let mut separating : NameHashSet := {}
  -- Names credited to a dependency module: a root that loads them sees an
  -- imported declaration, whose namespaces count as imported.
  let mut importedAmbiguous : Array (Name × Name) := #[]
  -- Inert names whose namespaces are not imported otherwise: name and its
  -- dependency declarers.
  let mut inertNames : Array (Name × Array Name) := #[]
  for (cname, (credited, copies)) in ambiguous.toList do
    let some shared := env.find? cname | do
      for (declarer, _) in copies do
        separating := separating.insert declarer
      separating := separating.insert credited
    let creditedSame := match copyIn credited cname with
      | some own => sameConstant shared own
      | none => false
    let allSame := creditedSame && copies.all (fun (_, copy) => sameConstant shared copy)
    let projectCopies := copies.filter (fun (declarer, _) => projModNames.contains declarer)
    let generated := !isAuxRecursor env cname && !isNoConfusion env cname
    let creditedProject := projModNames.contains credited
    let projectDeclarers := (if creditedProject then #[credited] else #[]) ++ projectCopies.map (·.1)
    let ranged := projectDeclarers.map (hasRange · cname)
    let benign := generated && allSame && creditedProject && projectCopies.size == copies.size
      && ranged.all (!·)
    if benign then continue
    let prefixes := Id.run do
      let mut out : Array Name := #[]
      let mut namespaceName := cname.getPrefix
      while !namespaceName.isAnonymous do
        out := out.push namespaceName
        namespaceName := namespaceName.getPrefix
      return out
    let body := match shared.value? with
      | some value => #[shared.type, value]
      | none => #[shared.type]
    let named := body.foldl (fun acc e => e.foldConsts acc fun c acc => acc.push c) #[]
    let inert := generated && allSame && ranged.all (!·) && !projNameSet.contains cname
      && prefixes.all (fun p => !projNameSet.contains p)
      && named.all (fun c => !ambiguous.contains c && !(match env.getModuleIdxFor? c with
        | some modIdx => projModNames.contains env.header.moduleNames[modIdx]!
        | none => false))
    if inert then
      if !prefixes.all importedNamespaces.contains then
        let declarers := #[credited] ++ copies.map (·.1)
        inertNames := inertNames.push (cname, declarers.filter (!projModNames.contains ·))
      continue
    let consistent := generated && if creditedProject then
        creditedSame && (ranged.all id || (ranged.all (!·) && allSame))
      else
        projectCopies.size ≤ 1 || ranged.all (!·)
    if consistent then
      for (declarer, _) in copies do
        if !imports declarer credited then
          separating := separating.insert declarer
      if !creditedProject then
        importedAmbiguous := importedAmbiguous.push (cname, credited)
    else
      for (declarer, _) in copies do
        separating := separating.insert declarer
      separating := separating.insert credited
  -- The modules a root's own environment loads, and whether one of them sets
  -- it apart from this one.
  let closureOf (start : Nat) : NameHashSet × Bool := Id.run do
    let mut seen : NameHashSet := {}
    let mut separated := false
    let mut stack : Array Nat := #[start]
    while !stack.isEmpty do
      let i := stack[stack.size - 1]!
      stack := stack.pop
      let modName := env.header.moduleNames[i]!
      if seen.contains modName then continue
      seen := seen.insert modName
      if separating.contains modName then separated := true
      if let some data := env.header.moduleData[i]? then
        for imp in data.imports do
          if let some j := moduleIdx[imp.module]? then
            stack := stack.push j
    return (seen, separated)

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
  let mut loadedImportedAmbiguous : NameHashSet := {}
  for root in importArgs do
    -- `none`: this environment is the root's own, and everything it loads counts.
    let mut rootClosure : Option NameHashSet := none
    if batched then
      match moduleIdxByString[root]? with
      | none =>
        IO.println s!"ISOLATE\t{root}"
        continue
      | some idx =>
        let (closure, separated) := closureOf idx
        if separated then
          IO.println s!"ISOLATE\t{root}"
          continue
        rootClosure := some closure
        for (cname, credited) in importedAmbiguous do
          if closure.contains credited then
            loadedImportedAmbiguous := loadedImportedAmbiguous.insert cname
        for (cname, otherDeclarers) in inertNames do
          if otherDeclarers.any closure.contains then
            loadedImportedAmbiguous := loadedImportedAmbiguous.insert cname
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
  let mut importedNamespaces := importedNamespaces
  for cname in importedAmbiguous.map (·.1) ++ inertNames.map (·.1) do
    if loadedImportedAmbiguous.contains cname then
      let mut namespaceName := cname.getPrefix
      while !namespaceName.isAnonymous do
        importedNamespaces := importedNamespaces.insert namespaceName
        namespaceName := namespaceName.getPrefix
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
