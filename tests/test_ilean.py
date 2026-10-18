import json

from lean_strip._pipeline.preprocessing import ilean


def _reference(module, name):
    return json.dumps({"c": {"m": module, "n": name}})


def test_targets_used_by_a_shadowed_declaration_are_reported():
    # PALOMAR-2026-10-10-000001: the project redeclares mathlib's
    # `HasIndepIncrements.isGaussianProcess`; import attributes the name to
    # mathlib, so the graph has no node for the project copy, whose text stays.
    module = "BrownianMotion.Gaussian.BrownianMotion"
    lemma = "ProbabilityTheory.incrementsToRestrict_increments_ofFin'_ae_eq_restrict"
    copy = "ProbabilityTheory.HasIndepIncrements.isGaussianProcess"
    document = {
        "module": module,
        "version": max(ilean.SUPPORTED_ILEAN_VERSIONS),
        "references": {
            _reference(module, lemma): {"definition": [128, 6, 128, 60],
                                        "usages": [[160, 12, 160, 60, copy]]},
            _reference(module, "ProbabilityTheory.unused"): {"definition": [10, 0, 10, 5],
                                                             "usages": [[20, 0, 20, 5]]},
            # `#eval`'s generated owner is not a declaration either.
            _reference(module, "ProbabilityTheory.evaluated"): {
                "definition": [12, 0, 12, 5], "usages": [[30, 0, 30, 5, f"_private.{module}.0._eval"]]},
        },
    }
    decls = [{"name": lemma, "module": module, "start_line": 129, "start_col": 0, "end_line": 140, "end_col": 11},
             {"name": "ProbabilityTheory.unused", "module": module,
              "start_line": 11, "start_col": 0, "end_line": 11, "end_col": 5},
             {"name": "ProbabilityTheory.evaluated", "module": module,
              "start_line": 13, "start_col": 0, "end_line": 13, "end_col": 5}]
    _deps, report = ilean.union_ilean_documents([("x.ilean", document)], decls, {}, modules={module})
    assert report["shadowed_owner_targets"] == [lemma]
    # A usage with no named owner (`#check`, a `variable`) is not a shadowed declaration.
    assert "ProbabilityTheory.unused" in report["owner_unresolved_targets"]
    assert "ProbabilityTheory.unused" not in report["shadowed_owner_targets"]
