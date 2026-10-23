"""Where the constants the comparator compares exactly were realized.

`lake comparator` (and the standalone comparator before it) compares a
solution to its challenge constant by constant. A protected theorem or
definition is a target: only its statement (a definition's type) is compared,
and walked. Every other constant the walk reaches is compared *exactly*, value
included, and its value is walked too (Lake's `Check/Compare.lean`,
`Compare.loop`). So a definition a protected statement mentions is compared
with its body, and a theorem that body uses is compared with its proof.

Such a proof refers to compiler-generated constants by name, and some of those
names are numbered: the auxiliary theorems a proof abstracts are
`foo._proof_1`, `foo._proof_2`, ... from a per-declaration counter. Realizing
a constant, such as the equation lemma `bar.eq_1` that `rw [bar]` needs,
advances that counter of the declaration that realizes it, and a constant is
realized only where the environment does not have it yet. In the original
tree some earlier declaration may have realized `bar.eq_1` (and stored it in
its module); if the strip deletes that declaration, `foo` realizes it itself,
its later `_proof_N` shift, and the comparator rejects `foo`
(PALOMAR-2026-10-20-000013: `cursor_guard_projection`, which the strip
dropped, had realized `walkEvents.eq_1` for `operationBudget_bound`).

This module computes the comparator's exact-comparison closure from the
built environment and, for each generated (range-less) project constant in
it, the declaration that realized it: the first declaration, in source order,
of the module storing it whose terms reach it. A constant made together with
a declaration (`foo._proof_1`, `foo.match_1`, `Foo.rec`) counts as made by
that declaration too; only reserved names (`bar.eq_1`, `bar.induct`, ...) are
realized at their first use alone. Rooting those declarations keeps every such
constant realized where it was. Other influences of deleted code on a
compared proof (a simp lemma tried but unused, say) are not modelled; the
comparator run at the end still judges the result.
"""
from __future__ import annotations

import shlex
from typing import Any, Iterable

from lean_strip._pipeline.preprocessing.strip import _private_owner_and_display

# Kernel built-ins both comparators start the walk from (`primitiveTargets`
# and `builtinTargets`); `Quot*` only when `Quot.sound` is permitted.
PRIMITIVE_TARGETS = (
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat",
    "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
)
QUOT_TARGETS = ("Quot", "Quot.mk", "Quot.lift", "Quot.ind")

_COMPARATOR_CLOSURE_LEAN = r"""
import Lean
open Lean

/-- The constants `Compare.loop` walks on from `info`: a target's type only,
anything else's type, value and inductive structure (`runForUsedConsts`). -/
def usedConsts (info : ConstantInfo) (full : Bool) : Array Name := Id.run do
  let mut out := info.type.getUsedConstants
  if !full then
    return out
  match info with
  | .defnInfo v   => out := out ++ v.value.getUsedConstants
  | .thmInfo v    => out := out ++ v.value.getUsedConstants
  | .opaqueInfo v => out := out ++ v.value.getUsedConstants
  | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v   => out := out.push v.induct
  | .recInfo v    =>
    for rule in v.rules do
      out := (out.push rule.ctor) ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return out

/-- The range-less project constants reachable from `n`'s terms through
range-less project constants. Memoized; a constant on the current path counts
as empty, which cuts cycles. -/
partial def reach (env : Environment) (isProject : Name → Bool) (ranged : NameHashSet)
    (memo : IO.Ref (Std.HashMap Name (Array Name))) (n : Name) : IO (Array Name) := do
  if let some cached := (← memo.get)[n]? then
    return cached
  memo.modify (·.insert n #[])
  let some info := env.find? n | return #[]
  let mut out : Array Name := #[]
  let mut seen : NameHashSet := {}
  for c in usedConsts info true do
    if c != n && isProject c && !ranged.contains c then
      for d in #[c] ++ (← reach env isProject ranged memo c) do
        if !seen.contains d then
          seen := seen.insert d
          out := out.push d
  memo.modify (·.insert n out)
  return out

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let some path := args.head? | throw <| IO.userError "usage: <input file>"
  let rows := ((← IO.FS.readFile path).splitOn "\n").filterMap fun line =>
    match line.splitOn "\t" with
    | [tag, value] => some (tag, value)
    | _ => none
  let field (tag : String) : List String := rows.filterMap fun (t, v) => if t == tag then some v else none
  let some entry := (field "ENTRY").head? | throw <| IO.userError "no ENTRY"
  let env ← importModules #[{ module := entry.toName }] {} 0
  let projectModules : NameHashSet :=
    (field "PROJECT").foldl (fun s m => s.insert m.toName) {}
  let moduleOf? (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx]!
  let isProject (n : Name) : Bool :=
    match moduleOf? n with
    | some m => projectModules.contains m
    | none => false
  -- `Compare.loop`, run on the solution's side alone.
  let theoremTargets : NameHashSet := (field "THM").foldl (fun s n => s.insert n.toName) {}
  let definitionTargets : NameHashSet := (field "DEF").foldl (fun s n => s.insert n.toName) {}
  let mut worklist : Array Name := ((field "PRIM").map String.toName).toArray
  for t in field "THM" do
    if let some info := env.find? t.toName then
      worklist := worklist ++ info.type.getUsedConstants
  worklist := worklist ++ ((field "DEF").map String.toName).toArray
  let mut checked : NameHashSet := {}
  let mut order : Array Name := #[]
  while !worklist.isEmpty do
    let n := worklist.back!
    worklist := worklist.pop
    if checked.contains n then
      continue
    checked := checked.insert n
    order := order.push n
    let some info := env.find? n | continue
    let target := theoremTargets.contains n || definitionTargets.contains n
    for c in usedConsts info (!target) do
      if !checked.contains c then
        worklist := worklist.push c
  -- Declaration ranges of the project modules.
  let mut ranged : NameHashSet := {}
  let mut rangedOf : Std.HashMap Name (Array (Name × Nat × Nat)) := {}
  for i in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if !projectModules.contains modName then continue
    let some modIdx := env.getModuleIdx? modName | continue
    let mut entries := #[]
    for (n, r) in declRangeExt.getModuleEntries env modIdx do
      ranged := ranged.insert n
      entries := entries.push (n, r.range.pos.line, r.range.pos.column)
    rangedOf := rangedOf.insert modName entries
  let mut generated : NameHashSet := {}
  for n in order do
    if let some m := moduleOf? n then
      if projectModules.contains m then
        let isRanged := ranged.contains n
        IO.println s!"CMP\t{n}\t{m}\t{if isRanged then 1 else 0}"
        if !isRanged then
          generated := generated.insert n
  -- Every project module storing a generated constant of the closure: the
  -- ranged declarations reaching each, with their positions.
  let memo ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  for i in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if !projectModules.contains modName then continue
    let some data := env.header.moduleData[i]? | continue
    let stored : NameHashSet := data.constNames.foldl (fun s n => if generated.contains n then s.insert n else s) {}
    if stored.isEmpty then continue
    let entries := rangedOf.getD modName #[]
    let position : Std.HashMap Name (Nat × Nat) :=
      entries.foldl (fun m (n, line, col) => m.insert n (line, col)) {}
    -- A constant made together with its declaration (`foo._proof_1`,
    -- `foo.match_1`, `Foo.rec`) is there from that declaration on; only a
    -- reserved name (`bar.eq_1`, `bar.induct`, ...) waits for its first use.
    for g in data.constNames do
      if !stored.contains g || isReservedName env g then continue
      let mut owner := g.getPrefix
      while !owner.isAnonymous && !position.contains owner do
        owner := owner.getPrefix
      if let some (line, col) := position[owner]? then
        IO.println s!"REACH\t{g}\t{modName}\t{owner}\t{line}\t{col}"
    for (decl, line, col) in entries do
      let some info := env.find? decl | continue
      let mut seen : NameHashSet := {}
      for c in usedConsts info true do
        if c == decl || !isProject c || ranged.contains c then continue
        for g in #[c] ++ (← reach env isProject ranged memo c) do
          if stored.contains g && !seen.contains g then
            seen := seen.insert g
            IO.println s!"REACH\t{g}\t{modName}\t{decl}\t{line}\t{col}"
""".strip()

_SCRIPT_PATH = "/tmp/_comparator_closure.lean"
_INPUT_PATH = "/tmp/_comparator_closure.txt"


def closure_input(
    entry_module: str,
    project_modules: Iterable[str],
    theorem_names: Iterable[str],
    definition_names: Iterable[str],
    permitted_axioms: Iterable[str],
) -> str:
    """The script's input: the comparator's targets as `Check.lean` builds them."""

    axioms = list(permitted_axioms)
    primitives = list(PRIMITIVE_TARGETS) + (list(QUOT_TARGETS) if "Quot.sound" in axioms else [])
    lines = [f"ENTRY\t{entry_module}"]
    lines += [f"PROJECT\t{module}" for module in sorted(set(project_modules))]
    # Permitted axioms are theorem targets too (`targets := theoremNames ++ legalAxioms`).
    lines += [f"THM\t{name}" for name in [*theorem_names, *axioms]]
    lines += [f"DEF\t{name}" for name in definition_names]
    lines += [f"PRIM\t{name}" for name in primitives]
    return "\n".join(lines) + "\n"


def parse_closure_output(output: str) -> tuple[dict[str, tuple[str, bool]], list[tuple[str, str, str, int, int]]]:
    """``CMP`` rows as {name: (module, ranged)}, ``REACH`` rows as tuples."""

    compared: dict[str, tuple[str, bool]] = {}
    reach: list[tuple[str, str, str, int, int]] = []
    for line in output.splitlines():
        parts = line.rstrip("\r").split("\t")
        if parts[0] == "CMP" and len(parts) == 4:
            compared[parts[1]] = (parts[2], parts[3] == "1")
        elif parts[0] == "REACH" and len(parts) == 6:
            reach.append((parts[1], parts[2], parts[3], int(parts[4]), int(parts[5])))
    return compared, reach


def realization_sites(
    reach: Iterable[tuple[str, str, str, int, int]],
) -> dict[str, dict[str, str]]:
    """{generated constant: {module storing it: the declaration that realized it}}.

    A constant is realized at its first need, so in each module storing it the
    realizing declaration is the first, in source order, whose terms reach it.
    """

    first: dict[tuple[str, str], tuple[int, int, str]] = {}
    for generated, module, decl, line, col in reach:
        key = (generated, module)
        candidate = (line, col, decl)
        if key not in first or candidate < first[key]:
            first[key] = candidate
    sites: dict[str, dict[str, str]] = {}
    for (generated, module), (_line, _col, decl) in sorted(first.items()):
        sites.setdefault(generated, {})[module] = decl
    return sites


def _named_under(generated: str, decl: str) -> bool:
    """Whether ``generated`` is named under ``decl``, private prefixes aside
    (`_private.M.0.foo._proof_1` is generated under `foo`)."""

    return _source_name(generated).startswith(_source_name(decl) + ".")


def _source_name(name: str) -> str:
    return _private_owner_and_display(name)[1]


def plan_realization_roots(
    compared: dict[str, tuple[str, bool]],
    sites: dict[str, dict[str, str]],
    declared: set[str],
) -> dict[str, Any]:
    """The declarations to root so the compared constants keep their names.

    Every realization site of a generated constant in the closure is rooted
    (most are the declaration it is named under, which the strip keeps
    anyway). A generated constant the scan finds no site for is reported:
    nothing in its module's terms reaches it, so the strip cannot tell what
    realized it, and the comparator stays the judge.
    """

    generated = sorted(name for name, (_module, ranged) in compared.items() if not ranged)
    roots = {decl for by_module in sites.values() for decl in by_module.values() if decl in declared}
    elsewhere = {
        name: sorted(set(by_module.values()))
        for name, by_module in sorted(sites.items())
        if any(not _named_under(name, decl) for decl in by_module.values())
    }
    return {
        "roots": roots,
        "report": {
            "compared_project_constants": len(compared),
            "compared_generated_constants": len(generated),
            "realized_by_other_declarations": elsewhere,
            "unsited_generated_constants": [name for name in generated if name not in sites],
            "site_roots": sorted(roots),
        },
    }


def collect_comparator_closure(
    env: Any,
    *,
    entry_module: str,
    project_modules: Iterable[str],
    theorem_names: Iterable[str],
    definition_names: Iterable[str],
    permitted_axioms: Iterable[str],
    timeout: int,
) -> tuple[dict[str, tuple[str, bool]], list[tuple[str, str, str, int, int]]]:
    """Run the closure script in the built workspace; raise when it fails."""

    env.write_text(_SCRIPT_PATH, _COMPARATOR_CLOSURE_LEAN + "\n")
    env.write_text(_INPUT_PATH, closure_input(
        entry_module, project_modules, theorem_names, definition_names, permitted_axioms,
    ))
    command = "cd /testbed && lake env lean --run " + " ".join(
        shlex.quote(arg) for arg in (_SCRIPT_PATH, _INPUT_PATH)
    )
    result = env.execute(command, timeout=timeout)
    if result["returncode"] != 0:
        raise RuntimeError(
            "comparator closure query failed (rc="
            f"{result['returncode']}): {result['output'][-2000:]}"
        )
    return parse_closure_output(result["output"])
