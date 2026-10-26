"""Realization sites of the constants the comparator compares exactly.

PALOMAR-2026-10-20-000013: `cursor_guard_projection` realized
`walkEvents.eq_1` in `ForestCursorTraversal`; the strip dropped it, so the
compared `operationBudget_bound` realized the lemma itself, its `_proof_1_N`
shifted by one and the comparator rejected it.
"""

from pathlib import Path

import pytest

from lean_strip import engine
from lean_strip._pipeline.preprocessing import comparator_closure as cc


def test_the_first_declaration_reaching_a_constant_in_its_module_realized_it():
    reach = [
        ("W.walkEvents.eq_1", "C.Traversal", "C.Traversal.later_use", 40, 0),
        ("W.walkEvents.eq_1", "C.Traversal", "C.Traversal.cursor_guard_projection", 12, 0),
        ("W.walkEvents.eq_1", "C.Traversal", "C.Traversal.cursor_guard_projection", 12, 0),
        # The same name realized independently in a module that does not see
        # the first one has a site of its own.
        ("W.walkEvents.eq_1", "C.Other", "C.Other.use", 3, 2),
        ("W.walkEvents.eq_1", "C.Other", "C.Other.first", 3, 0),
    ]
    assert cc.realization_sites(reach) == {
        "W.walkEvents.eq_1": {
            "C.Traversal": "C.Traversal.cursor_guard_projection",
            "C.Other": "C.Other.first",
        },
    }


def test_sites_are_rooted_and_those_of_other_declarations_reported():
    compared = {
        "C.Charging.operationBudget_bound": ("C.Charging", True),
        "_private.C.Charging.0.C.Charging.operationBudget_bound._proof_1_4": ("C.Charging", False),
        "W.walkEvents.eq_1": ("C.Traversal", False),
        "W.walkEvents.eq_def": ("W", False),
    }
    sites = {
        "_private.C.Charging.0.C.Charging.operationBudget_bound._proof_1_4": {
            "C.Charging": "C.Charging.operationBudget_bound",
        },
        "W.walkEvents.eq_1": {"C.Traversal": "C.Traversal.cursor_guard_projection"},
    }
    declared = {"C.Charging.operationBudget_bound", "C.Traversal.cursor_guard_projection"}
    plan = cc.plan_realization_roots(compared, sites, declared)
    assert plan["roots"] == declared
    report = plan["report"]
    # A private helper named under its own declaration is not "other".
    assert report["realized_by_other_declarations"] == {
        "W.walkEvents.eq_1": ["C.Traversal.cursor_guard_projection"],
    }
    assert report["unsited_generated_constants"] == ["W.walkEvents.eq_def"]
    assert report["compared_project_constants"] == 4
    assert report["compared_generated_constants"] == 3


def test_a_site_the_graph_has_no_node_for_is_not_rooted():
    plan = cc.plan_realization_roots(
        {"W.f.eq_1": ("M", False)}, {"W.f.eq_1": {"M": "M.unknown"}}, {"M.known"},
    )
    assert plan["roots"] == set()


def test_input_names_the_targets_as_the_comparator_builds_them():
    text = cc.closure_input("Sol", ["B", "A", "A"], ["thm"], ["dfn"], ["propext", "Quot.sound"])
    lines = text.splitlines()
    assert lines[0] == "ENTRY\tSol"
    assert lines[1:3] == ["PROJECT\tA", "PROJECT\tB"]
    # Permitted axioms are theorem targets: only their type is walked.
    assert [line for line in lines if line.startswith("THM")] == [
        "THM\tthm", "THM\tpropext", "THM\tQuot.sound",
    ]
    assert "DEF\tdfn" in lines
    assert "PRIM\tQuot.lift" in lines and "PRIM\tNat.add" in lines
    without_quot = cc.closure_input("Sol", [], ["thm"], [], ["propext"])
    assert "PRIM\tQuot.lift" not in without_quot.splitlines()


def test_output_parsing_ignores_other_lines():
    compared, reach = cc.parse_closure_output(
        "warning: something\n"
        "CMP\tA.f\tA\t1\n"
        "CMP\tA.f.eq_1\tB\t0\r\n"
        "REACH\tA.f.eq_1\tB\tB.site\t7\t2\n"
        "REACH\tbroken\n"
    )
    assert compared == {"A.f": ("A", True), "A.f.eq_1": ("B", False)}
    assert reach == [("A.f.eq_1", "B", "B.site", 7, 2)]


class _NoLean:
    def execute(self, *_args, **_kwargs):
        raise AssertionError("a theorem-only config must not run the closure query")

    write_text = execute


def _settings(**names) -> engine.StripSettings:
    return engine.StripSettings(
        entry_module="Sol", build_target="+Sol", protected={"thm"},
        diagnostics_dir=Path("."), **names,
    )


def test_theorem_only_configs_do_not_run_the_query():
    roots, report = engine._comparator_realization_roots(
        _NoLean(), _settings(theorem_names=("thm",)), [], set(), 60,
    )
    assert roots == set() and report is None


class _FakeLean:
    def __init__(self, output: str, returncode: int = 0) -> None:
        self.output, self.returncode, self.files = output, returncode, {}

    def write_text(self, path, text):
        self.files[path] = text

    def execute(self, command, timeout=None):
        return {"output": self.output, "returncode": self.returncode}


def test_definition_configs_root_the_sites():
    ws = _FakeLean(
        "CMP\tW.walkEvents.eq_1\tTraversal\t0\n"
        "REACH\tW.walkEvents.eq_1\tTraversal\tcursor_guard_projection\t12\t0\n"
    )
    decls = [{"name": "cursor_guard_projection", "module": "Traversal"}]
    roots, report = engine._comparator_realization_roots(
        ws, _settings(theorem_names=("thm",), definition_names=("dfn",)), decls, {"Sol"}, 60,
    )
    assert roots == {("Traversal", "cursor_guard_projection")}
    assert report["realized_by_other_declarations"] == {
        "W.walkEvents.eq_1": ["cursor_guard_projection"],
    }
    assert "DEF\tdfn" in ws.files[cc._INPUT_PATH]
    assert "PROJECT\tTraversal" in ws.files[cc._INPUT_PATH]


def test_a_failed_query_fails_the_run():
    with pytest.raises(engine.StripFailure) as failure:
        engine._comparator_realization_roots(
            _FakeLean("boom", returncode=1),
            _settings(definition_names=("dfn",)), [], set(), 60,
        )
    assert failure.value.stage == "comparator_closure"
