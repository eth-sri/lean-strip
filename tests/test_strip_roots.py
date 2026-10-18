import time
from lean_strip._pipeline.preprocessing import strip


def _decl(name, start, end):
    return {"name": name, "module": "M", "start_line": start, "end_line": end}


def test_implicitly_used_kinds_are_force_kept():
    # PALOMAR-2026-10-05-000002: `deriving instance … in` was dropped as unused,
    # which deleted the prefix the next declaration's `deriving Repr` needed.
    source = "\n".join([
        "deriving instance Repr for ModuleDoc in",      # 1
        "inductive Content where",                       # 2
        "  | doc : ModuleDoc → Content",                 # 3
        "deriving Repr",                                 # 4
        'infixl:65 " +ᵥ " => vadd',                      # 5
        "simproc reduceFoo (foo _) := fun _ => pure .continue",  # 6
        "def helper : Nat := 1",                         # 7
    ])
    decls = [
        _decl("instReprModuleDoc", 1, 1),
        _decl("Content", 2, 4),
        _decl("«term_+ᵥ_»", 5, 5),
        _decl("reduceFoo", 6, 6),
        _decl("helper", 7, 7),
    ]
    kept = strip.detect_force_keep_kinds(decls, {"M.lean": source}, {"M": "M.lean"})
    assert kept == {"instReprModuleDoc", "«term_+ᵥ_»", "reduceFoo"}


def test_custom_simps_projections_are_force_kept():
    # PALOMAR-2026-10-04-000011: `Dihomotopy.Simps.apply` is looked up by name.
    source = "def Simps.apply (F : Dihomotopy f₀ f₁) : I × X → Y := F\ndef other := 1"
    decls = [_decl("Dihomotopy.Simps.apply", 1, 1), _decl("Dihomotopy.other", 2, 2)]
    kept = strip.detect_force_keep_kinds(decls, {"M.lean": source}, {"M": "M.lean"})
    assert kept == {"Dihomotopy.Simps.apply"}


def test_eval_naming_a_deleted_declaration_goes_with_it():
    # PALOMAR-2026-10-04-000009: `#eval mcsOrder p3` outlived `def p3`.
    source = "\n".join([
        "namespace G",
        "def mcsOrder (n : Nat) : Nat := n",
        "-- example graph",
        "#eval mcsOrder p3",
        "#eval mcsOrder 3",
        "#eval",
        "  mcsOrder c4",
        "end G",
    ])
    project = {"G.mcsOrder", "G.p3", "G.c4"}
    text, stats = strip.remove_dead_commands(source, project, {"G.mcsOrder"})
    assert "p3" not in text and "c4" not in text
    assert "#eval mcsOrder 3" in text
    assert stats["evals_removed"] == 2


def test_open_reaching_a_live_namespace_through_an_earlier_open_survives():
    # PALOMAR-2026-10-06-000009: the nearest candidate namespace is dead, but
    # Lean also opens `RamificationTheory.HilbertRamification.ValuationSubring`.
    source = "\n".join([
        "namespace LocalCFT",
        "open RamificationTheory",
        "open HilbertRamification.ValuationSubring",
        "def toDecomp := decompositionGroup",
        "end LocalCFT",
    ])
    project = {
        "LocalCFT.toDecomp",
        "LocalCFT.HilbertRamification.ValuationSubring.dead",
        "RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup",
    }
    kept = project - {"LocalCFT.HilbertRamification.ValuationSubring.dead"}
    text, stats = strip.remove_dead_commands(source, project, kept)
    assert "open HilbertRamification.ValuationSubring" in text
    assert stats["open_namespaces_removed"] == 0


def test_open_whose_every_candidate_is_dead_is_removed():
    source = "namespace A\nopen Gone\ndef x := 1\nend A"
    project = {"A.x", "A.Gone.y", "Gone.z"}
    text, stats = strip.remove_dead_commands(source, project, {"A.x"})
    assert "open Gone" not in text
    assert stats["open_commands_removed"] == 1


def test_multiline_selective_open_drops_deleted_targets():
    # PALOMAR-2026-10-05-000003: the target list continued over three lines and
    # kept naming deleted lemmas, which made the whole `open` fail.
    source = "\n".join([
        "open Vis (rayPt rayPt_fst",
        "  rayPt_mem_segment hseg",
        "  eventually_not_mem_boundary)",
        "def DirFree := rayPt",
        "open Vis (rayPt_mem_segment)",
    ])
    project = {"DirFree", "Vis.rayPt", "Vis.rayPt_fst", "Vis.rayPt_mem_segment",
               "Vis.hseg", "Vis.eventually_not_mem_boundary"}
    kept = {"DirFree", "Vis.rayPt", "Vis.rayPt_fst", "Vis.hseg"}
    text, stats = strip.remove_dead_commands(source, project, kept)
    assert text.split("\n")[:3] == [
        "open Vis (rayPt rayPt_fst",
        "  hseg)",
        "def DirFree := rayPt",
    ]
    assert "rayPt_mem_segment" not in text and "eventually_not_mem_boundary" not in text
    assert stats["open_declarations_removed"] == 3
    assert stats["open_commands_removed"] == 1


def test_duplicate_full_names_across_files_are_detected_through_namespaces():
    # PALOMAR-2026-09-30-000031: two modules, never imported together, both
    # declare `NumberField.mem_integer_of_subset`.
    originals = {
        "A.lean": "namespace NumberField\ntheorem mem_integer_of_subset : True := trivial\nend NumberField",
        "B.lean": "namespace NumberField\n\ntheorem mem_integer_of_subset : True := trivial\nend NumberField",
        "C.lean": "theorem NumberField.other : True := trivial\nprivate theorem helper : True := trivial",
        "D.lean": "namespace Foo\nprivate theorem helper : True := trivial\ntheorem other : True := trivial\nend Foo",
    }
    assert strip.detect_duplicate_declaration_files(originals) == {"A.lean", "B.lean"}


def test_quoted_names_link_across_modules_without_imports():
    # PALOMAR-2026-09-27-000005: `#engine_certify` resolves
    # `FourColor.contractProg` by name in the module that uses the command.
    gen = "\n".join([
        "def certify : CommandElabM Unit := do",
        "  let some c ← resolveConst? `FourColor.contractProg | throwError \"missing\"",
        "  let d := ``FourColor.other",
        "  pure ()",
    ])
    decls = [
        {"name": "certify", "module": "Gen", "start_line": 1, "end_line": 4},
        {"name": "FourColor.contractProg", "module": "CfContract", "start_line": 1, "end_line": 1},
        {"name": "FourColor.other", "module": "CfContract", "start_line": 2, "end_line": 2},
    ]
    originals = {"/testbed/Gen.lean": gen,
                 "/testbed/CfContract.lean": "def FourColor.contractProg := 1\ndef FourColor.other := 2"}
    mod_path = {"Gen": "/testbed/Gen.lean", "CfContract": "/testbed/CfContract.lean"}
    deps = strip.augment_deps_with_source(decls, {}, originals, mod_path)
    assert {"FourColor.contractProg", "FourColor.other"} <= deps["certify"]



def test_declarations_an_attribute_command_generates_are_roots():
    # PALOMAR-2026-10-16-000006: `reassoc` generates `pD_idem_assoc` with the
    # command as its range; dropping it deleted the command, so `pD_idem`
    # lost its simp attribute and `by simp` stopped working.
    source = "\n".join([
        "structure PairData where",
        "  pD_idem : True",
        "namespace PairData",
        "attribute [reassoc (attr := simp)] pD_idem",
        "attribute [local simp] pD_idem in",
        "theorem t : True := trivial",
        "end PairData",
    ])
    decls = [_decl("PairData", 1, 2), _decl("PairData.pD_idem_assoc", 4, 4),
             _decl("PairData.t", 5, 6)]
    roots = strip.detect_automation_tagged(decls, {"M.lean": source}, {"M": "M.lean"})
    assert "PairData.pD_idem_assoc" in roots
    assert "PairData.t" not in roots


def test_attribute_targets_resolve_through_the_enclosing_namespace():
    # PALOMAR-2026-09-28-000001: other namespaces also declare the theorem, so
    # a bare-name guess left `attribute [local instance 2000] ...` unrooted.
    source = "\n".join([
        "namespace FiniteAbelianGlobalReciprocity",
        "theorem ideleClassGroupIsMulCommutative : True := trivial",
        "attribute [local instance 2000] ideleClassGroupIsMulCommutative",
        "end FiniteAbelianGlobalReciprocity",
    ])
    decls = [
        {"name": "FiniteAbelianGlobalReciprocity.ideleClassGroupIsMulCommutative"},
        {"name": "ClassFieldTheory.Global.ideleClassGroupIsMulCommutative"},
    ]
    roots = strip.detect_attribute_command_roots(decls, {"Definitions.lean": source})
    assert roots == {"FiniteAbelianGlobalReciprocity.ideleClassGroupIsMulCommutative"}


def test_multiline_export_closing_on_an_unindented_line_is_pruned():
    # PALOMAR-2026-09-18-000005: the `)` of a long export list sat in column 0.
    source = "\n".join([
        "namespace ExactSinTheta",
        "export TauCeti.ApproximationNumber (",
        "  approximationSingularValue approximationSingularValue_antitone",
        "  approximationSingularValue_add_le",
        ")",
        "def x := approximationSingularValue",
        "end ExactSinTheta",
    ])
    project = {"TauCeti.ApproximationNumber.approximationSingularValue",
               "TauCeti.ApproximationNumber.approximationSingularValue_antitone",
               "TauCeti.ApproximationNumber.approximationSingularValue_add_le", "ExactSinTheta.x"}
    kept = {"TauCeti.ApproximationNumber.approximationSingularValue", "ExactSinTheta.x"}
    text, stats = strip.remove_dead_commands(source, project, kept)
    assert "approximationSingularValue_antitone" not in text and "_add_le" not in text
    assert "export TauCeti.ApproximationNumber (" in text and stats["export_targets_removed"] == 2


def test_project_commands_and_dotted_evals_naming_deleted_declarations_go():
    # PALOMAR-2026-10-04-000004: `audit_standard_axioms Foo.thm` after `Foo.thm`
    # was dropped; PALOMAR-2026-10-01-000014: `#eval ctrls3.map f`.
    # PALOMAR-2026-10-04-000004 writes the atom with a trailing space.
    originals = {"Audit.lean": 'elab "audit_standard_axioms " n:ident : command => pure ()'}
    atoms = strip.project_command_atoms(originals)
    assert atoms == {"audit_standard_axioms"}
    source = "\n".join([
        "audit_standard_axioms Foo.main",
        "audit_standard_axioms Foo.extra",
        "/-- info: [1] -/",
        "#guard_msgs in",
        "#eval ctrls3.map id",
    ])
    project = {"Foo.main", "Foo.extra", "ctrls3"}
    text, stats = strip.remove_dead_commands(source, project, {"Foo.main"}, custom_commands=atoms)
    assert text.strip() == "audit_standard_axioms Foo.main"
    assert stats["custom_commands_removed"] == 1 and stats["evals_removed"] == 1


def test_verbatim_files_keep_what_their_examples_use():
    # PALOMAR-2026-09-29-000002: a retained Examples.lean used a lemma from
    # another file only inside an anonymous `example`.
    text = "\n".join([
        "namespace Disc",
        "example : True := by simpa using (tail_firstTerm (f := id))",
        "open Other",
        "example : True := helper",
        "end Disc",
    ])
    declarations = {"Disc.tail_firstTerm", "Other.helper", "Disc.unused"}
    assert strip.file_text_references(text, declarations) == {"Disc.tail_firstTerm", "Other.helper"}


def test_variable_binders_are_not_pruned_by_last_component_guesses():
    # PALOMAR-2026-09-14-000002: Mathlib's `Semiring` is not the deleted
    # project declaration `Foo.Semiring`.
    source = "\n".join([
        "namespace G",
        "variable {B : Type} [Semiring B] [Dead B]",
        "theorem t : True := trivial",
        "end G",
    ])
    project = {"G.t", "Other.Semiring", "G.Dead"}
    text, _ = strip.remove_dead_commands(source, project, {"G.t"})
    assert "variable {B : Type} [Semiring B]" in text and "Dead" not in text


def test_variable_and_attribute_targets_resolve_through_opens():
    # PALOMAR-2026-09-20-000007: `borderProjection` reached through
    # `open Cylinders` was deleted, but its binder stayed and the warm build
    # elaborated it as an auto-bound implicit.
    source = "\n".join([
        "namespace P.Theorem",
        "open Cylinders",
        "variable (G : Nat) (h : borderProjection G = 0) (k : kept G = 0)",
        "attribute [simp] borderProjection kept",
        "theorem t : True := trivial",
        "end P.Theorem",
    ])
    project = {"P.Cylinders.borderProjection", "P.Cylinders.kept", "P.Theorem.t"}
    text, stats = strip.remove_dead_commands(
        source, project, {"P.Cylinders.kept", "P.Theorem.t"}
    )
    assert "variable (G : Nat) (k : kept G = 0)" in text
    assert "attribute [simp] kept" in text
    assert "borderProjection" not in text
    assert stats["variable_binders_removed"] == 1


def test_check_commands_from_dependencies_naming_deleted_declarations_go():
    # PALOMAR-2026-09-12-000002: Mathlib's `assert_no_sorry` and a project's
    # `#audit_axioms` named theorems the strip removed.
    source = "\n".join([
        "assert_no_sorry FD.full",
        "assert_no_sorry FD.kept",
        "#audit_axioms closedCalibration",
        "#exit",
    ])
    project = {"FD.full", "FD.kept", "closedCalibration"}
    text, stats = strip.remove_dead_commands(source, project, {"FD.kept"})
    assert text.strip().split("\n") == ["assert_no_sorry FD.kept", "#exit"]
    assert stats["custom_commands_removed"] == 2


def test_multiline_open_drops_dead_namespaces_on_continuation_lines():
    # PALOMAR-2026-09-13-000001: `TitsMixedAction` sat on the second line.
    source = "\n".join([
        "namespace M",
        "open C1 TitsLinear",
        "  TitsMixedAction BlockTrace",
        "open Live hiding gone",
        "def f := 1",
        "end M",
    ])
    project = {"M.f", "C1.a", "TitsLinear.b", "TitsMixedAction.c", "BlockTrace.d", "Live.e", "Live.gone"}
    kept = {"M.f", "C1.a", "TitsLinear.b", "BlockTrace.d", "Live.e"}
    text, stats = strip.remove_dead_commands(source, project, kept)
    assert "open C1 TitsLinear BlockTrace" in text and "TitsMixedAction" not in text
    assert "open Live hiding gone" in text
    assert stats["open_namespaces_removed"] == 1


def test_check_commands_resolve_names_through_open():
    # PALOMAR-2026-09-13-000002: `#audit_axioms foo` after `end Ns` and `open Ns`.
    source = "\n".join([
        "namespace Ns",
        "theorem foo : True := trivial",
        "end Ns",
        "open Ns",
        "#audit_axioms foo",
    ])
    text, stats = strip.remove_dead_commands(source, {"Ns.foo"}, set())
    assert "#audit_axioms" not in text and stats["custom_commands_removed"] == 1


def test_check_commands_naming_deleted_private_declarations_go():
    # PALOMAR-2026-10-01-000014: `private def ctrls3`, used by `#eval ctrls3.map f`.
    source = "\n".join([
        "/-- info: [1] -/",
        "#guard_msgs in",
        "#eval ctrls3.map id",
        "#eval keepMe",
    ])
    private_dead = "_private.Av.Kernel.0.ctrls3"
    private_live = "_private.Av.Kernel.0.keepMe"
    text, stats = strip.remove_dead_commands(source, {private_dead, private_live}, {private_live},
                                             module="Av.Kernel")
    assert text.strip() == "#eval keepMe" and stats["evals_removed"] == 1
    # Another module's private `ctrls3` is invisible here: nothing is removed.
    text, stats = strip.remove_dead_commands(source, {private_dead}, set(), module="Other")
    assert stats["evals_removed"] == 0


def test_noncomputable_section_end_keeps_the_namespace():
    # Review finding: `end` of `noncomputable section` popped `namespace A`.
    text = "namespace A\nnoncomputable section\ndef x := 1\nend\ndef y := 2\nend A\n"
    namespaces, _ = strip._source_namespace_resolution_contexts(text)
    assert namespaces[5] == "A"


def test_selective_and_hiding_opens_do_not_resolve_removals():
    # Review finding: after `open Foo (a)`, `#eval b` is not `Foo.b`.
    source = "open Foo (a)\n#eval b\nopen Bar hiding c\n#eval c\n"
    text, stats = strip.remove_dead_commands(source, {"Foo.a", "Foo.b", "Bar.c"}, {"Foo.a"})
    assert stats["evals_removed"] == 0


def test_removals_only_see_imported_declarations():
    source = "#eval gone\n"
    text, stats = strip.remove_dead_commands(source, {"gone"}, set(), visible_declarations=set())
    assert stats["evals_removed"] == 0


def test_verbatim_references_follow_dotted_projections():
    # Review finding: `my_lemma.symm` did not root `my_lemma`.
    text = "namespace N\nexample := my_lemma.symm\nexample := Foo.bar.le\nend N\n"
    assert strip.file_text_references(text, {"N.my_lemma", "Foo.bar", "N.unused"}) == {"N.my_lemma", "Foo.bar"}


def test_opens_of_namespaces_holding_export_aliases_survive():
    # PALOMAR-2026-09-17-000001: `ExactSinTheta` holds only aliases exported
    # from `TauCeti.ApproximationNumber`; pruning its `open` broke every use.
    exporter = "\n".join([
        "namespace TauCeti",
        "namespace DavisKahan.ExactSinTheta",
        "export TauCeti.ApproximationNumber (",
        "  approximationSingularValue)",
        "end DavisKahan.ExactSinTheta",
        "end TauCeti",
    ])
    user = "\n".join([
        "namespace TauCeti",
        "open DavisKahan.ExactSinTheta",
        "theorem t : approximationSingularValue = 0 := rfl",
        "end TauCeti",
    ])
    aliases = strip.export_alias_namespaces({"/testbed/A.lean": exporter, "/testbed/B.lean": user})
    assert "TauCeti.DavisKahan.ExactSinTheta" in aliases
    kept = {"TauCeti.ApproximationNumber.approximationSingularValue", "TauCeti.t"}
    project = kept | {"TauCeti.DavisKahan.ExactSinTheta.dropped"}
    text, _ = strip.remove_dead_commands(user, project, kept, aliases)
    assert "open DavisKahan.ExactSinTheta" in text
    pruned, _ = strip.remove_dead_commands(user, project, kept, set())
    assert "open DavisKahan.ExactSinTheta" not in pruned  # what happened without the aliases


def test_open_private_drops_names_whose_declarations_were_deleted():
    # PALOMAR-2026-10-08-000003: `open private … exists_mul_sqrt_le_pow …` named
    # a private lemma the strip removed; Batteries then fails the command.
    source = "\n".join([
        "namespace ImprovedExponents",
        "open private levelsOf_le exists_mul_sqrt_le_pow from ThreeSumApsp.Sec4.Corollary31",
        "theorem t : True := trivial",
        "end ImprovedExponents",
    ])
    mod = "_private.ThreeSumApsp.Sec4.Corollary31.0.ThreeSumApsp.Corollary31."
    project = {mod + "levelsOf_le", mod + "exists_mul_sqrt_le_pow", "ImprovedExponents.t"}
    text, _ = strip.remove_dead_commands(source, project, project - {mod + "exists_mul_sqrt_le_pow"})
    assert "open private levelsOf_le from ThreeSumApsp.Sec4.Corollary31" in text
    gone, _ = strip.remove_dead_commands(source, project, {"ImprovedExponents.t"})
    assert "open private" not in gone
    kept, _ = strip.remove_dead_commands(source, project, project)
    assert kept == source


def test_field_accesses_are_not_global_names():
    # PALOMAR-2026-10-07-000001: `(GradeCutBoundary.scheme D j).below` is a
    # field; a deleted declaration `Knight.below` must not take the binder.
    source = "\n".join([
        "namespace Knight.Rows",
        "variable (hmatch : ∀ d : (scheme D).below c, (.inl d) = d)",
        "include hmatch",
        "theorem t : True := trivial",
        "end Knight.Rows",
    ])
    project = {"Knight.below", "Knight.inl", "Knight.scheme", "Knight.Rows.t"}
    text, _ = strip.remove_dead_commands(source, project, {"Knight.scheme", "Knight.Rows.t"})
    assert "variable (hmatch" in text and "include hmatch" in text


def test_overloaded_names_are_deleted_only_when_every_candidate_is():
    # PALOMAR-2026-10-07-000001: three opened namespaces have an `ownerEquiv`;
    # Lean picks the one that type-checks, and only an unused one was deleted.
    source = "\n".join([
        "namespace Knight.Rows",
        "open SourceLayerCarrier GradeCutBoundary",
        "variable (hmatch : ownerEquiv D = e)",
        "include hmatch",
        "theorem t : ownerEquiv D = e := hmatch",
        "end Knight.Rows",
    ])
    project = {"Knight.SourceLayerCarrier.ownerEquiv", "Knight.GradeCutBoundary.ownerEquiv", "Knight.Rows.t"}
    text, _ = strip.remove_dead_commands(source, project, project - {"Knight.SourceLayerCarrier.ownerEquiv"})
    assert "variable (hmatch" in text
    gone, _ = strip.remove_dead_commands(source, project, {"Knight.Rows.t"})
    assert "variable (hmatch" not in gone and "include hmatch" not in gone


def test_unused_binders_with_an_overloaded_deleted_name_go():
    # PALOMAR-2026-08-27-000009: `FunctionField.IsCanonical` was deleted and
    # `Chart.IsCanonical` survives through `open Chart`; nothing uses `hW` any
    # more, and keeping it made Lean take `Chart.IsCanonical`, which fails.
    source = "\n".join([
        "namespace FunctionField",
        "open Chart",
        "section Canonical",
        "variable {W : Divisor k K} (hW : IsCanonical k K W)",
        "include hW",
        "end Canonical",
        "theorem t : True := trivial",
        "end FunctionField",
    ])
    project = {"FunctionField.IsCanonical", "FunctionField.Chart.IsCanonical", "FunctionField.t"}
    text, _ = strip.remove_dead_commands(source, project, project - {"FunctionField.IsCanonical"})
    assert "hW" not in text and "variable {W : Divisor k K}" in text


def test_dead_module_stubs_keep_a_crlf_module_header():
    # PALOMAR-2026-10-13-000008 uses CRLF line endings: `module\r` was not
    # recognised, and the stub's `public import` then needed `module`.
    source = "module\r\npublic import A.B\r\n\r\npublic section\r\ntheorem t : True := trivial\r\n"
    stub = strip.import_only_stub(source)
    assert stub.split("\n")[:2] == ["module\r", "public import A.B\r"]


def test_an_open_keeps_the_imported_anchor_of_its_namespace():
    # PALOMAR-2026-10-11-000009: `open _root_.S.Section8` needs the namespace to
    # exist; only the imported `NamespaceAnchor` provided it before the file
    # defined into it.
    originals = {
        "/testbed/S/Anchor.lean": "namespace S.Section8\ntheorem anchor : True := trivial\nend S.Section8\n",
        "/testbed/S/Use.lean": "\n".join([
            "import S.Anchor",
            "open _root_.S.Section8",
            "def S.Section8.solution : Nat := 1",
            "",
        ]),
    }
    decls = [{"name": "S.Section8.anchor", "module": "S.Anchor"},
             {"name": "S.Section8.solution", "module": "S.Use"}]
    paths = {"S.Anchor": "/testbed/S/Anchor.lean", "S.Use": "/testbed/S/Use.lean"}
    assert strip.namespace_anchor_roots(originals, decls, {"S.Section8.solution"}, paths) == {"S.Section8.anchor"}
    # Not needed once the file keeps nothing of the namespace itself.
    assert strip.namespace_anchor_roots(originals, decls, set(), paths) == set()


def test_selective_opens_whose_list_starts_on_the_next_line_are_pruned():
    # PALOMAR-2026-10-11-000001: `scaledPoint` was deleted but stayed in the
    # list, and Lean then rejected the whole `open`.
    source = "\n".join([
        "namespace K.Scaling",
        "open K.SectionTwo",
        "  (scaledPoint scaledCoefficient",
        "    scaledDrift)",
        "theorem t : True := trivial",
        "end K.Scaling",
    ])
    project = {"K.SectionTwo.scaledPoint", "K.SectionTwo.scaledCoefficient", "K.SectionTwo.scaledDrift", "K.Scaling.t"}
    text, _ = strip.remove_dead_commands(source, project, project - {"K.SectionTwo.scaledPoint"})
    assert "scaledPoint" not in text and "scaledCoefficient" in text and "scaledDrift)" in text


def test_open_names_resolve_relative_to_earlier_names_in_the_same_command():
    # PALOMAR-2026-10-09-000009: `GluingDatum` is `D.Infrastructure.GluingDatum`
    # through the name before it, and its `incidentEdges` is live.
    source = "\n".join([
        "namespace D.Count.Pendant",
        "open D.Infrastructure GluingDatum",
        "theorem t : True := trivial",
        "end D.Count.Pendant",
    ])
    project = {"D.Infrastructure.helper", "D.Infrastructure.GluingDatum.incidentEdges",
               "D.GluingDatum.unused", "D.Count.Pendant.t"}
    kept = {"D.Infrastructure.GluingDatum.incidentEdges", "D.Count.Pendant.t"}
    text, _ = strip.remove_dead_commands(source, project, kept)
    # `D.Infrastructure` itself has nothing live, but `GluingDatum` needs it.
    assert "open D.Infrastructure GluingDatum" in text



def test_a_long_open_resolves_in_linear_time():
    # PALOMAR-2026-10-12-000002: every name of a 12-name `open` added all its
    # candidates under all earlier ones, doubling the scope per name; the
    # strip ran for hours. Only namespaces that exist are opened.
    names = [f"N{i}" for i in range(40)]
    source = "\n".join(["namespace P", "open " + " ".join(names), "theorem t : True := trivial", "end P"])
    project = {f"P.{name}.x" for name in names} | {f"P.{name}.{other}.y" for name in names[:5] for other in names}
    project.add("P.t")
    kept = {"P.t", "P.N7.x"}
    started = time.perf_counter()
    text, stats = strip.remove_dead_commands(source, project, kept)
    assert time.perf_counter() - started < 5
    assert "open N7\ntheorem t" in text


def test_open_renaming_roots_the_renamed_declarations():
    # PALOMAR-2026-10-13-000010: deleting a renamed declaration made Lean
    # reject the `open`, and with it every use of the new name.
    sources = {
        "A.lean": "namespace Proj.Sources\ntheorem tiling : True := trivial\ntheorem other : True := trivial\nend Proj.Sources\n",
        "B.lean": "\n".join([
            "namespace Proj.Product",
            "open _root_.Proj.Sources renaming tiling → tiling",
            "open Sources renaming other -> other'",
            "theorem use : True := tiling",
            "end Proj.Product",
        ]),
    }
    decls = [{"name": n, "module": "A", "start_line": 2, "end_line": 2}
             for n in ("Proj.Sources.tiling", "Proj.Sources.other")]
    assert strip.detect_open_renaming_roots(decls, sources) == {
        "Proj.Sources.tiling", "Proj.Sources.other"}


def test_names_quoted_in_run_cmd_are_roots():
    # PALOMAR-2026-10-10-000001: a `run_cmd` axiom audit over quoted theorem
    # names; the strip dropped the theorems and ``Paper.x failed.
    source = "\n".join([
        "namespace Paper",
        "theorem main : True := trivial",
        "theorem unused : True := trivial",
        "end Paper",
        "",
        "run_cmd do",
        "  for name in [",
        "    ``Paper.main,",
        "    `Paper.unused] do",
        "    pure ()",
        "",
        "theorem after : True := trivial",
        "#eval ``Paper.after",
    ])
    decls = [_decl("Paper.main", 2, 2), _decl("Paper.unused", 3, 3), _decl("after", 12, 12)]
    assert strip.detect_run_command_roots(decls, {"M.lean": source}) == {"Paper.main", "Paper.unused"}


def test_code_called_in_run_cmd_is_a_root():
    # PALOMAR-2026-10-11-000009: `run_cmd` calls a project metaprogram that
    # re-issues declarations; the strip dropped it ("Unknown identifier").
    source = "\n".join([
        "namespace Proj.EventTransport",
        "def run (x : Nat) : Lean.CoreM Nat := pure x",
        "def St : Nat := 0",
        "end Proj.EventTransport",
        "",
        "namespace Proj.Paper",
        "def helper : Nat := 1",
        "open Lean Elab Command in",
        "run_cmd liftCoreM do",
        "  let (log, _) ← _root_.Proj.EventTransport.run helper",
        "  logInfo m!\"{log.St}\"",
        "end Proj.Paper",
    ])
    decls = [_decl("Proj.EventTransport.run", 2, 2), _decl("Proj.EventTransport.St", 3, 3),
             _decl("Proj.Paper.helper", 7, 7)]
    assert strip.detect_run_command_roots(decls, {"M.lean": source}) == {
        "Proj.EventTransport.run", "Proj.Paper.helper"}
