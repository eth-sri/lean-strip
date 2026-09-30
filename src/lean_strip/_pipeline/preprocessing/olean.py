"""Internal .olean reader for the canonical preprocessing dependency graph.

Lean loads compiled declarations and ranges; this is one evidence layer, never
an independently published dependency graph. Use dependency_graph for graphs.
"""
from __future__ import annotations

import shlex
from typing import Any

# Lean 4 script that emits the project's declaration dependency graph, so the
# keep-set (transitive forward closure of the seed signatures) can be computed
# in Python (see strip.compute_keep_set — testable, and re-expandable during
# the rebuild-recovery loop). Emits three record kinds:
#
#   DECL\tname\tmodule\tstartLine\tstartCol\tendLine\tendCol\tkind\tmetaFlag
#   DEP\tname\tdep            (one record per edge)
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
# inductive->ctors) so seeding any member pulls its whole family.
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
  let imports := (importArgs.map fun s => { module := s.toName : Import }).toArray
  let env ← importModules imports {} 0
  let loadedModules := env.header.moduleNames
  let projModNames : NameHashSet :=
    moduleArgs.foldl (fun names module =>
      let moduleName := module.toName
      if loadedModules.contains moduleName then names.insert moduleName else names) {}

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
      if !isProject then
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
    let mut nodes : Array (Name × Name × ConstantInfo × String) := #[]
    let mut projNameSet : NameHashSet := {}
    for (name, cinfo) in env.constants.toList do
      match env.getModuleIdxFor? name with
      | none => pure ()
      | some modIdx =>
        let modName := env.header.moduleNames[modIdx]!
        if projModNames.contains modName then
          match ← findDeclarationRanges? name with
          | some dr =>
            let r := dr.range
            let rangeStr := s!"{r.pos.line}\t{r.pos.column}\t{r.endPos.line}\t{r.endPos.column}"
            nodes := nodes.push (name, modName, cinfo, rangeStr)
            projNameSet := projNameSet.insert name
          | none => pure ()

    return (nodes, projNameSet, importedNamespaces)
  let ((nodes, projNameSet, importedNamespaces), _) ← action.toIO coreCtx coreState

  -- Pass 2: emit DECL + DEP for each node.
  for (name, modName, cinfo, rangeStr) in nodes do
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
    let isProjectConstant (n : Name) : Bool :=
      match env.getModuleIdxFor? n with
      | none => false
      | some modIdx =>
        let ownerModule := env.header.moduleNames[modIdx]!
        projModNames.contains ownerModule
    let rec findSourceOwner? (n : Name) : Option Name :=
      if projNameSet.contains n then
        some n
      else if n.isAnonymous then
        none
      else
        findSourceOwner? n.getPrefix
    let findRefs (e : Expr) (acc : Array Name) : Array Name :=
      e.foldConsts acc fun n acc =>
        if !isProjectConstant n then
          acc
        else
          match findSourceOwner? n with
          | some owner =>
            if owner != name then acc.push owner else acc
          | none => acc
    let mut refs := findRefs cinfo.type #[]
    refs := match cinfo with
      | .defnInfo val   => findRefs val.value refs
      | .thmInfo val    => findRefs val.value refs
      | .opaqueInfo val => findRefs val.value refs
      | _               => refs
    refs := match cinfo with
      | .ctorInfo val   => refs.push val.induct
      | .recInfo val    => refs ++ val.all.toArray
      | .inductInfo val => refs ++ val.ctors.toArray
      | _               => refs
    -- One record per edge. Lean names may contain quoted components with
    -- spaces (for example ``«Adic spaces»``), so a whitespace-separated
    -- dependency payload is not a lossless wire format.
    for ref in refs do
      IO.println s!"DEP\t{name}\t{ref}"
  for ns in importedNamespaces do
    IO.println s!"EXTNS\t{ns}"
""".strip()

# Logical scratch paths (mapped to the local workspace) for the script and its
# module list.
_DUMP_KEEP_PATH = "/tmp/_dump_keep.lean"
_DUMP_KEEP_MODULES_PATH = "/tmp/_dump_keep_modules.txt"

# One declaration: name, module, source range, kind, meta flag. Other layers
# add a `keep` bool; anonymous-example rows use the same shape.
DeclRange = dict[str, Any]


def _install_dump_keep_script(env: Any) -> None:
    """Write the keep-graph Lean script into the workspace scratch directory."""
    cmd = f"cat > {_DUMP_KEEP_PATH} << 'LEANDUMPKEEP_EOF'\n{_DUMP_KEEP_LEAN}\nLEANDUMPKEEP_EOF"
    env.execute(cmd)


class DeclGraphExtractionError(RuntimeError):
    """Keep the subprocess failure distinct from a genuinely empty graph."""

    def __init__(self, *, returncode, timed_out, diagnostics, declarations):
        self.details = {
            "returncode": returncode, "timed_out": bool(timed_out),
            "diagnostics": diagnostics, "partial_declarations": declarations,
            "failure_kind": "timeout" if timed_out else "killed" if returncode in (137, -9) else "process_error",
        }
        super().__init__(
            f"Lean graph extraction {self.details['failure_kind']} "
            f"(rc={returncode}, partial declarations={declarations}): {diagnostics[-2000:]}"
        )


def read_olean_declarations(
    env: Any, modules: list[str], *, timeout: int = 3600,
) -> tuple[list[DeclRange], dict[str, set[str]], set[str]]:
    """Run the keep-graph Lean script; return declarations, edges, namespaces.

    `decls` is one DeclRange per project decl (with a `meta` bool). `deps` maps
    each decl name to the set of project-local names it references.
    `imported_namespaces` contains exact namespace prefixes with at least one
    declaration owned outside the selected project modules. The caller computes
    the keep-set in Python (strip.compute_keep_set).

    `modules` is the non-empty list of project modules to import and scan.
    Output is streamed so the full dump never has to be held as one string.

    Requires `lake build` to have succeeded so .olean files exist.
    Raises DeclGraphExtractionError if the query fails.
    """
    _install_dump_keep_script(env)
    decls: list[DeclRange] = []
    deps: dict[str, set[str]] = {}
    imported_namespaces: set[str] = set()
    diagnostics: list[str] = []

    def consume_line(line: str) -> None:
        line = line.rstrip("\r\n")
        parts = line.split("\t")
        if parts and parts[0] == "DECL" and len(parts) == 9:
            _, name, module, sl, sc, el, ec, kind, meta = parts
            try:
                decls.append({
                    "name": name, "module": module,
                    "start_line": int(sl), "start_col": int(sc),
                    "end_line": int(el), "end_col": int(ec),
                    "kind": kind, "meta": meta == "meta",
                })
            except ValueError:
                diagnostics.append(line)
        elif parts and parts[0] == "DEP" and len(parts) == 3:
            deps.setdefault(parts[1], set()).add(parts[2])
        elif parts and parts[0] == "EXTNS" and len(parts) == 2:
            imported_namespaces.add(parts[1])
        elif line:
            diagnostics.append(line)
        if len(diagnostics) > 200:
            del diagnostics[:-200]

    payload = ("\n".join(modules) + "\n").encode("utf-8")
    env.write_file_bytes(_DUMP_KEEP_MODULES_PATH, payload)
    lean_command = (
        f"lean --run {_DUMP_KEEP_PATH} "
        f"--modules-file {_DUMP_KEEP_MODULES_PATH}"
    )
    cmd = "cd /testbed && lake env sh -c " + shlex.quote("exec " + lean_command)
    result = env.execute_stream(
        cmd,
        timeout=timeout,
        on_output=consume_line,
        capture_output=False,
    )

    if result.get("returncode", 1) != 0 or result.get("timed_out"):
        detail = "\n".join(diagnostics)[-4000:] or result.get("output", "")[-4000:]
        raise DeclGraphExtractionError(
            returncode=result.get("returncode"), timed_out=result.get("timed_out"),
            diagnostics=detail, declarations=len(decls),
        )
    return decls, deps, imported_namespaces
