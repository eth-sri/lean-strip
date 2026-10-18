"""The Lean-side pass (frontend.py) and the edits decided from it (syntax_edit.py).

The tests run on a recorded analysis of the small project in ``SOURCES``
(tests/fixtures/frontend.json), so they need no Lean. With LEAN_STRIP_E2E=1
they also run on a fresh analysis; LEAN_STRIP_RECORD=1 rewrites the fixture.
"""

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from lean_strip._pipeline.preprocessing import frontend, olean, strip, syntax_edit

FIXTURE = Path(__file__).parent / "fixtures" / "frontend.json"
TOOLCHAIN = "leanprover/lean4:v4.33.0\n"
LAKEFILE = 'name = "fx"\ndefaultTargets = ["Fx"]\n[[lean_lib]]\nname = "Fx"\nglobs = ["Fx.+"]\n'

SOURCES = {
    "Fx/Defs.lean": """import Lean
open Lean Elab Command

namespace G
class Dead (α : Type) : Prop where
  out : True
def t : True := trivial
end G

namespace P.Cylinders
def borderProjection (n : Nat) : Nat := n
def kept (n : Nat) : Nat := n
end P.Cylinders

namespace Knight
def below (n : Nat) : Nat := n
structure Scheme where
  below : Nat
def scheme (d : Nat) : Scheme := ⟨d⟩
namespace SourceLayerCarrier
def ownerEquiv (d : Nat) : Nat := d
end SourceLayerCarrier
namespace GradeCutBoundary
def ownerEquiv (d : Bool) : Bool := d
end GradeCutBoundary
end Knight

namespace FunctionField
def IsCanonical (k : Nat) : Prop := k = k
namespace Chart
def IsCanonical (k : Bool) : Prop := k = k
end Chart
end FunctionField

namespace TauCeti
namespace ApproximationNumber
def approximationSingularValue : Nat := 0
def approximationSingularValue_antitone : Nat := 1
def approximationSingularValue_add_le : Nat := 2
end ApproximationNumber
namespace DavisKahan.ExactSinTheta
export TauCeti.ApproximationNumber (
  approximationSingularValue approximationSingularValue_antitone
  approximationSingularValue_add_le
)
def dropped : Nat := 0
end DavisKahan.ExactSinTheta
end TauCeti

namespace RamificationTheory.HilbertRamification.ValuationSubring
def decompositionGroup : Nat := 0
end RamificationTheory.HilbertRamification.ValuationSubring
namespace LocalCFT.HilbertRamification.ValuationSubring
def dead : Nat := 0
end LocalCFT.HilbertRamification.ValuationSubring

/-- A command that resolves its argument (so Lean reports what it names). -/
elab "audit_standard_axioms " n:ident : command => do
  discard <| liftCoreM <| realizeGlobalConstNoOverloadWithInfo n

/-- A command that never resolves its argument. -/
syntax (name := auditQuiet) "#audit_quiet " ident : command
@[command_elab auditQuiet] def elabAuditQuiet : CommandElab := fun _ => pure ()
""",
    "Fx/Uses.lean": """import Fx.Defs

namespace G
variable {B : Type} [Add B] [Dead B]
theorem t2 : True := trivial
end G

namespace P.Theorem
open Cylinders
variable (G : Nat) (h : borderProjection G = 0) (k : kept G = 0)
attribute [simp] borderProjection kept
theorem t : True := trivial
end P.Theorem

namespace Knight.Rows
open SourceLayerCarrier GradeCutBoundary
variable (D : Nat) (hmatch : ownerEquiv D = D)
variable (hfield : (scheme D).below = D)
include hmatch hfield
theorem t : True := trivial
end Knight.Rows

namespace FunctionField
open Chart
section Canonical
variable (k : Nat) (hW : IsCanonical k)
include hW
omit hW in
theorem s : True := trivial
end Canonical
theorem t : True := trivial
end FunctionField

namespace TauCeti
open DavisKahan.ExactSinTheta
theorem t : approximationSingularValue = 0 := rfl
end TauCeti

namespace LocalCFT
open RamificationTheory
open HilbertRamification.ValuationSubring
def toDecomp := decompositionGroup
end LocalCFT

namespace M
open P.Cylinders G
  Knight
open TauCeti.ApproximationNumber (approximationSingularValue
  approximationSingularValue_antitone
  approximationSingularValue_add_le)
def f := 1
end M

open G in
theorem openIn : True := trivial
""",
    "Fx/Commands.lean": """import Fx.Defs

namespace E
def mcsOrder (n : Nat) : Nat := n
def p3 : Nat := 3
private def ctrls3 : List Nat := [1]
def keepMe : Nat := 1
-- example graph
#eval mcsOrder p3
#eval mcsOrder 3
#eval
  mcsOrder p3
/-- info: [1] -/
#guard_msgs in
#eval ctrls3.map id
#check p3
#print axioms keepMe
open P.Cylinders in
#eval borderProjection 2
audit_standard_axioms E.p3
audit_standard_axioms E.keepMe
#audit_quiet E.p3
#audit_quiet keepMe
end E
""",
    "Fx/Decls.lean": """import Fx.Defs

namespace D
/-- A dropped lemma with an attribute line. -/
@[simp]
theorem dropped_simp : 1 = 1 := rfl

set_option maxHeartbeats 400 in
theorem dropped_in : True := trivial

open G in
theorem dropped_open : True := trivial

theorem kept_one : True := trivial

mutual
def evenD : Nat → Bool
  | 0 => true
  | n+1 => oddD n
def oddD : Nat → Bool
  | 0 => false
  | n+1 => evenD n
end

structure Pt where
  x : Nat
  y : Nat

theorem dropped_trailing : True := trivial -- trailing comment

example : True := trivial

attribute [local simp] dropped_simp in
theorem kept_two : True := trivial
end D
""",
    "Fx/ModDefs.lean": "module\r\n\r\npublic section\r\npublic def modX : Nat := 1\r\nend\r\n",
    "Fx/Crlf.lean": "module\r\npublic import Fx.ModDefs\r\n\r\npublic section\r\ntheorem crlfT : True := trivial\r\nend\r\n",
}
MODULES = {path[:-5].replace("/", "."): f"/testbed/{path}" for path in SOURCES}
ORIGINALS = {f"/testbed/{path}": text for path, text in SOURCES.items()}


def record(root: Path) -> dict:
    """Build ``SOURCES`` at ``root``; run the Lean pass and the declaration dump."""

    for relative, text in {**SOURCES, "lean-toolchain": TOOLCHAIN, "lakefile.toml": LAKEFILE}.items():
        (root / relative).parent.mkdir(parents=True, exist_ok=True)
        (root / relative).write_bytes(text.encode())
    subprocess.run(["lake", "build"], cwd=root, check=True, capture_output=True)
    (root / "frontend.lean").write_text(frontend._FRONTEND_LEAN)
    (root / "dump.lean").write_text(olean._DUMP_KEEP_LEAN)
    (root / "modules.txt").write_text("\n".join(MODULES) + "\n")
    jobs = [
        f"{root}/{path}\t{module}\tfull\t{root}/.lake/build/ir/{path[:-5]}.setup.json"
        for module, path in ((m, p.removeprefix("/testbed/")) for m, p in MODULES.items())
    ]
    run = lambda *argv: subprocess.run(  # noqa: E731
        ["lake", "env", "lean", "--run", *argv], cwd=root, check=True, capture_output=True, text=True,
    ).stdout
    analysis = []
    for line in run("frontend.lean", "modules.txt", *jobs).splitlines():
        if not line.startswith("{"):
            continue
        data = json.loads(line.replace(f"{root}/", "/testbed/"))
        assert "fatal" not in data, data
        for timing in ("ms", "import_ms"):
            if timing in data:
                data[timing] = 0
        analysis.append(json.dumps(data, ensure_ascii=False, sort_keys=True))
    declarations, namespaces = [], set()
    for line in run("dump.lean", "--modules-file", "modules.txt").splitlines():
        parts = line.split("\t")
        if parts[0] == "DECL" and len(parts) == 9:
            _, name, module, sl, sc, el, ec, kind, meta = parts
            declarations.append({"name": name, "module": module, "start_line": int(sl),
                                 "start_col": int(sc), "end_line": int(el), "end_col": int(ec),
                                 "kind": kind, "meta": meta == "meta"})
        elif parts[0] == "EXTNS" and len(parts) == 2:
            namespaces.add(parts[1])
    project_namespaces = {d["name"].rsplit(".", 1)[0] for d in declarations if "." in d["name"]}
    return {
        "toolchain": TOOLCHAIN.strip(),
        "analysis": analysis,
        "declarations": sorted(declarations, key=lambda d: (d["module"], d["start_line"], d["name"])),
        "imported_namespaces": sorted(namespaces & project_namespaces),
    }


def _live_enabled() -> bool:
    return os.environ.get("LEAN_STRIP_E2E") == "1" and shutil.which("lake") is not None


@pytest.fixture(scope="module", params=["recorded", "live"])
def data(request, tmp_path_factory):
    if request.param == "live":
        if not _live_enabled():
            pytest.skip("set LEAN_STRIP_E2E=1 (needs Lean/Lake on PATH)")
        payload = record(tmp_path_factory.mktemp("fx"))
        if os.environ.get("LEAN_STRIP_RECORD") == "1":
            FIXTURE.parent.mkdir(exist_ok=True)
            FIXTURE.write_text(json.dumps(payload, ensure_ascii=False, indent=0) + "\n")
    else:
        payload = json.loads(FIXTURE.read_text())
    analyses, failures = frontend.parse_frontend_output(payload["analysis"], ORIGINALS)
    assert not failures
    return analyses, payload["declarations"], set(payload["imported_namespaces"])


def _plan(data, dropped, *, lean=True, syntax=None):
    analyses, declarations, imported = data
    rows = [{**row, "keep": not any(row["name"] == name or row["name"].startswith(name + ".")
                                    for name in dropped)}
            for row in declarations]
    examples = {}
    for path, analysis in analyses.items():
        for command in analysis.commands:
            if analysis.text[command.start:command.end].startswith("example"):
                (line, col), (end_line, end_col) = (
                    frontend._Offsets(analysis.text).line_column(command.start),
                    frontend._Offsets(analysis.text).line_column(command.end),
                )
                examples.setdefault(path, []).append({
                    "name": f"__anonymous_example__.{line}", "module": "", "keep": False, "meta": False,
                    "start_line": line, "start_col": col, "end_line": end_line, "end_col": end_col,
                    "kind": "example"})
    desired, summary = strip.plan_stripped_sources(
        ORIGINALS, rows, MODULES,
        anonymous_example_ranges=examples,
        all_project_declarations={row["name"] for row in declarations},
        imported_namespaces=imported,
        syntax=(syntax if syntax is not None else analyses) if lean else None,
    )
    return desired, summary


def _text(desired, module):
    return desired[MODULES[module]]


def test_the_lean_view_has_commands_scopes_and_references(data):
    analyses, _, _ = data
    uses = analyses[MODULES["Fx.Uses"]]
    text = uses.text
    by_text = {text[c.start:c.end].split("\n")[0]: c for c in uses.commands}
    hfield = by_text["variable (hfield : (scheme D).below = D)"]
    assert hfield.namespace == "Knight.Rows"
    assert set(hfield.opens) == {"Knight.SourceLayerCarrier", "Knight.GradeCutBoundary"}
    constants = {c for reference in hfield.references for c in reference.constants}
    # The field `.below` is the structure's projection, not the global `Knight.below`.
    assert constants == {"Knight.scheme", "Knight.Scheme.below"}
    opened = by_text["open HilbertRamification.ValuationSubring"]
    (name,) = opened.tree.idents()
    assert set(name.namespaces) == {
        "LocalCFT.HilbertRamification.ValuationSubring",
        "RamificationTheory.HilbertRamification.ValuationSubring",
    }
    assert by_text["omit hW in"].kind == "Lean.Parser.Command.in"
    assert [b.names for b in by_text["omit hW in"].variables][-2:] == [("k",), ("hW",)]


def test_a_binder_goes_exactly_when_the_overload_lean_chose_goes(data):
    # PALOMAR-2026-10-07-000001: `ownerEquiv` from two opened namespaces; Lean
    # chose `SourceLayerCarrier.ownerEquiv`.
    desired, _ = _plan(data, {"Knight.GradeCutBoundary.ownerEquiv"})
    uses = _text(desired, "Fx.Uses")
    assert "variable (D : Nat) (hmatch : ownerEquiv D = D)" in uses
    assert "include hmatch hfield" in uses
    desired, summary = _plan(data, {"Knight.SourceLayerCarrier.ownerEquiv"})
    uses = _text(desired, "Fx.Uses")
    assert "variable (D : Nat)\n" in uses and "hmatch" not in uses
    assert "include hfield\n" in uses
    assert "Fx/Uses.lean" in summary["lean_edited_files"]


def test_an_unused_binder_of_a_deleted_overload_goes_with_its_include_and_omit(data):
    # PALOMAR-2026-08-27-000009: `FunctionField.IsCanonical` deleted while
    # `Chart.IsCanonical` survives through `open Chart`.
    desired, _ = _plan(data, {"FunctionField.IsCanonical"})
    uses = _text(desired, "Fx.Uses")
    assert "hW" not in uses
    assert "variable (k : Nat)\ntheorem s : True := trivial\nend Canonical" in uses


def test_a_field_access_is_not_a_global_name(data):
    # PALOMAR-2026-10-07-000001: `(scheme D).below` survives a deleted `Knight.below`.
    desired, _ = _plan(data, {"Knight.below"})
    assert "variable (hfield : (scheme D).below = D)" in _text(desired, "Fx.Uses")


def test_names_resolve_through_open(data):
    # PALOMAR-2026-09-20-000007: `borderProjection` reached through `open Cylinders`.
    desired, summary = _plan(data, {"P.Cylinders.borderProjection"})
    uses = _text(desired, "Fx.Uses")
    assert "variable (G : Nat) (k : kept G = 0)" in uses
    assert "attribute [simp] kept\n" in uses
    assert "open P.Cylinders (" not in uses and "borderProjection" not in uses
    assert summary["dead_command_cleanup"]["variable_binders_removed"] == 1


def test_a_core_class_is_not_a_deleted_project_class(data):
    # PALOMAR-2026-09-14-000002: `[Add B]` is core's `Add`; `[Dead B]` is the project's.
    desired, _ = _plan(data, {"G.Dead"})
    assert "variable {B : Type} [Add B]\n" in _text(desired, "Fx.Uses")


def test_export_targets_and_alias_namespaces(data):
    # PALOMAR-2026-09-17-000001: `ExactSinTheta` holds export aliases, so its
    # `open` survives the deletion of its only declaration.
    # PALOMAR-2026-09-18-000005 / -10-05-000003: multi-line target lists.
    dropped = {"TauCeti.DavisKahan.ExactSinTheta.dropped",
               "TauCeti.ApproximationNumber.approximationSingularValue_antitone",
               "TauCeti.ApproximationNumber.approximationSingularValue_add_le"}
    desired, _ = _plan(data, dropped)
    assert "export TauCeti.ApproximationNumber (\n  approximationSingularValue\n)" in _text(desired, "Fx.Defs")
    uses = _text(desired, "Fx.Uses")
    assert "open DavisKahan.ExactSinTheta\n" in uses
    assert "open TauCeti.ApproximationNumber (approximationSingularValue)\n" in uses


def test_an_open_reaching_a_live_namespace_through_an_earlier_open_survives(data):
    # PALOMAR-2026-10-06-000009: Lean opens both `…ValuationSubring` namespaces.
    desired, _ = _plan(data, {"LocalCFT.HilbertRamification.ValuationSubring.dead"})
    assert "open HilbertRamification.ValuationSubring\n" in _text(desired, "Fx.Uses")


def test_dead_namespaces_leave_multiline_and_prefix_opens(data):
    # PALOMAR-2026-09-13-000001: the namespace list continued on a second line.
    desired, summary = _plan(data, {"G"})
    uses = _text(desired, "Fx.Uses")
    assert "open P.Cylinders\n  Knight\n" in uses
    # `open G in` would fail on the vanished namespace; the theorem stays.
    assert "\ntheorem openIn : True := trivial\n" in uses and "open G" not in uses
    assert summary["dead_command_cleanup"]["open_namespaces_removed"] >= 2


def test_commands_naming_deleted_declarations_go(data):
    # PALOMAR-2026-10-04-000009 (`#eval mcsOrder p3`), -10-01-000014 (a private
    # `ctrls3` under `#guard_msgs`), -10-04-000004 and -09-12-000002 (project
    # check commands).
    desired, summary = _plan(data, {"E.p3", "_private.Fx.Commands.0.E.ctrls3"})
    commands = _text(desired, "Fx.Commands")
    assert "p3" not in commands and "ctrls3" not in commands and "info: [1]" not in commands
    assert "#eval mcsOrder 3" in commands and "-- example graph" in commands
    assert "#check" not in commands and "#print" not in commands
    assert "open P.Cylinders in\n#eval borderProjection 2" in commands
    assert "audit_standard_axioms E.keepMe" in commands and "#audit_quiet keepMe" in commands
    cleanup = summary["dead_command_cleanup"]
    assert cleanup["evals_removed"] == 3 and cleanup["custom_commands_removed"] == 2
    assert cleanup["diagnostics_removed"] == 2


def test_declarations_go_with_their_whole_command(data):
    dropped = {"D.dropped_simp", "D.dropped_in", "D.dropped_open", "D.evenD", "D.oddD",
               "D.dropped_trailing"}
    desired, _ = _plan(data, dropped)
    decls = _text(desired, "Fx.Decls")
    assert decls == (
        "import Fx.Defs\n\nnamespace D\n\ntheorem kept_one : True := trivial\n\n"
        "structure Pt where\n  x : Nat\n  y : Nat\n\ntheorem kept_two : True := trivial\nend D\n"
    )


def test_a_dead_module_stub_is_its_header_verbatim(data):
    # PALOMAR-2026-10-13-000008: CRLF line ends and `module` survive.
    desired, summary = _plan(data, {"crlfT"})
    assert _text(desired, "Fx.Crlf") == "module\r\npublic import Fx.ModDefs\r\n"
    assert "/testbed/Fx/Crlf.lean" in summary["stub_paths"]


def test_a_declaration_that_failed_here_keeps_the_regex_path(data):
    analyses, _, _ = data
    uses = analyses[MODULES["Fx.Uses"]]
    broken = frontend.FileSyntax(
        path=uses.path, module=uses.module, text=uses.text, mode=uses.mode, header=uses.header,
        commands=[
            frontend.Command(**{**command.__dict__, "error": "1:0: elaboration differs"})
            if command.declaration else command
            for command in uses.commands
        ],
    )
    assert not syntax_edit.usable(broken, uses.text)
    assert not syntax_edit.usable(uses, uses.text + "\n")
    _, summary = _plan(data, {"Knight.below"}, syntax={**analyses, uses.path: broken})
    assert "Fx/Uses.lean" not in summary["lean_edited_files"]


def test_output_without_its_closing_record_is_a_failure():
    text = "theorem t : True := trivial\n"
    lines = [
        '{"file": "/testbed/A.lean", "module": "A"}',
        '{"header": null, "r": null}',
        '{"c": 1, "k": "Lean.Parser.Command.declaration", "r": [1, 0, 1, 27], "ns": "[anonymous]", "decl": true}',
    ]
    analyses, failures = frontend.parse_frontend_output(lines, {"/testbed/A.lean": text})
    assert analyses == {} and failures == {"/testbed/A.lean": "incomplete output"}
    analyses, failures = frontend.parse_frontend_output(
        lines + ['{"done": "/testbed/A.lean", "ok": true, "ms": 5}'], {"/testbed/A.lean": text})
    assert failures == {} and analyses["/testbed/A.lean"].commands[0].end == 27


def test_positions_are_codepoints_and_crlf_safe():
    offsets = frontend._Offsets("αβ\r\nγ := 1\r\n")
    assert offsets.offset(1, 2) == 2 and offsets.offset(2, 1) == 5
    assert offsets.offset(9, 0) == len("αβ\r\nγ := 1\r\n")


def test_jobs_name_the_setup_lake_compiled_with():
    job = frontend.FrontendJob("/testbed/A/«B.c».lean", "A.«B.c»")
    assert job.setup == "/testbed/.lake/build/ir/A/B.c.setup.json"


def test_a_header_stub_keeps_the_header_lines_only():
    text = "/- c -/\nmodule\n\n-- note\npublic import\n  A.B\nimport C\n\ntheorem t : True := trivial\n"
    offsets = frontend._Offsets(text)
    span = lambda line, col, end_line, end_col: (offsets.offset(line, col), offsets.offset(end_line, end_col))  # noqa: E731
    node = lambda kind, sp, **kw: frontend.Node(kind=kind, start=sp[0], end=sp[1], **kw)  # noqa: E731
    header = node("Lean.Parser.Module.header", span(2, 0, 7, 8), children=(
        frontend.Node(atom="module", start=span(2, 0, 2, 6)[0], end=span(2, 0, 2, 6)[1]),
        node("Lean.Parser.Module.import", span(5, 0, 6, 5)),
        node("Lean.Parser.Module.import", span(7, 0, 7, 8)),
    ))
    analysis = frontend.FileSyntax(path="/testbed/A.lean", module="A", text=text, mode="header", header=header)
    assert syntax_edit.header_stub(analysis, text) == "module\npublic import\n  A.B\nimport C\n"
    assert syntax_edit.header_stub(analysis, text + " ") is None


def test_header_jobs_share_processes_within_the_command_line_limit():
    jobs = [frontend.FrontendJob(f"/testbed/{'x' * 200}{i}.lean", f"M{i}", "header") for i in range(300)]
    batches = frontend._header_batches(jobs)
    assert len(batches) > 1 and sum(map(len, batches)) == 300
