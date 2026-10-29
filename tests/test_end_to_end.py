"""End-to-end runs on tiny Lake projects; they need Lean, so they are opt-in.

    LEAN_STRIP_E2E=1 pytest tests/test_end_to_end.py
"""

import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

from lean_strip import cli

pytestmark = pytest.mark.skipif(
    os.environ.get("LEAN_STRIP_E2E") != "1" or shutil.which("lake") is None,
    reason="set LEAN_STRIP_E2E=1 (needs Lean/Lake on PATH)",
)

TOOLCHAIN = "leanprover/lean4:v4.33.0\n"
COMPARATOR = {"challenge_module": "Challenge", "solution_module": "Solution",
              "theorem_names": ["main_thm"], "permitted_axioms": []}


def _project(root: Path, files: dict[str, str], comparator: dict = COMPARATOR) -> Path:
    for relative, text in {"lean-toolchain": TOOLCHAIN,
                           "comparator.json": json.dumps(comparator), **files}.items():
        (root / relative).parent.mkdir(parents=True, exist_ok=True)
        (root / relative).write_text(text)
    git = ["git", "-c", "user.email=t@t", "-c", "user.name=t"]
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(["git", "add", "-A"], cwd=root, check=True)
    subprocess.run([*git, "commit", "-qm", "init"], cwd=root, check=True)
    return root


def _digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(p for p in root.rglob("*") if p.is_file() and ".lake" not in p.parts):
        digest.update(path.relative_to(root).as_posix().encode() + path.read_bytes())
    return digest.hexdigest()


def test_vendored_path_dependency_is_left_untouched(tmp_path):
    root = _project(tmp_path, {
        "lakefile.toml": 'name = "proj"\ndefaultTargets = ["Lib", "Solution"]\n'
                         '[[require]]\nname = "Dep"\npath = "vendor/Dep"\n'
                         '[[lean_lib]]\nname = "Lib"\n[[lean_lib]]\nname = "Solution"\n'
                         '[[lean_lib]]\nname = "Challenge"\n',
        "vendor/Dep/lean-toolchain": TOOLCHAIN,
        "vendor/Dep/lakefile.toml": 'name = "Dep"\n[[lean_lib]]\nname = "Dep"\n',
        "vendor/Dep/Dep.lean": "import Dep.Basic\n",
        "vendor/Dep/Dep/Basic.lean": "def depUsed : Nat := 1\ndef depUnused : Nat := 5\n",
        "vendor/Dep/README.md": "# Dep\n",
        "Lib.lean": "import Lib.A\n",
        "Lib/A.lean": "import Dep.Basic\ndef used : Nat := depUsed + 1\ndef unused : Nat := 3\n",
        "Solution.lean": "import Lib.A\ntheorem main_thm : used = 2 := rfl\n",
        "Challenge.lean": "import Lib.A\ntheorem main_thm : used = 2 := sorry\n",
        "README.md": "# Project\n",
    }, comparator={**COMPARATOR, "definition_names": ["depUsed"]})  # a dependency's definition
    vendored = _digest(root / "vendor")

    assert cli.main([str(root), "--jobs", "2", "--quiet", "--retain-lean-only"]) == 0

    assert _digest(root / "vendor") == vendored
    assert not (root / "README.md").exists()
    assert "unused" not in (root / "Lib/A.lean").read_text()
    report = json.loads((root / ".lean-strip/report.json").read_text())
    assert report["totals"]["files"]["before"] == 3
    assert report["lakefile"]["lake_build"]["ok"]
    assert report["engine_report"]["seed_from_dependencies"] == ["depUsed"]


def test_entry_module_is_resolved_exactly_despite_a_second_solution_file(tmp_path):
    # PALOMAR-2026-09-28-000004 had `Solution.lean` and `PaperN/PartI/Solution.lean`.
    root = _project(tmp_path, {
        "lakefile.toml": 'name = "dup"\n[[lean_lib]]\nname = "Lib"\n[[lean_lib]]\nname = "Solution"\n'
                         '[[lean_lib]]\nname = "Challenge"\n[[lean_lib]]\nname = "Paper"\n'
                         'globs = ["Paper.+"]\n',
        "Lib/A.lean": "def used : Nat := 2\ndef unused : Nat := 3\n",
        "Solution.lean": "import Lib.A\ntheorem main_thm : used = 2 := rfl\n",
        "Challenge.lean": "import Lib.A\ntheorem main_thm : used = 2 := sorry\n",
        "Paper/Solution.lean": "theorem other : True := trivial\n",
    })

    assert cli.main([str(root), "--jobs", "2", "--quiet"]) == 0

    assert "unused" not in (root / "Lib/A.lean").read_text()
    assert (root / "Solution.lean").exists() and not (root / "Paper/Solution.lean").exists()


def test_dump_follows_auxiliary_constants(tmp_path):
    # A `grind` proof references its lemmas only from `tg._proof_1`, which has
    # no source range; the dump must still attribute them to `tg`.
    from lean_strip._pipeline.preprocessing import olean

    root = tmp_path
    (root / "AuxT").mkdir()
    (root / "lean-toolchain").write_text(TOOLCHAIN)
    (root / "lakefile.toml").write_text('name = "auxtest"\n[[lean_lib]]\nname = "AuxT"\n')
    (root / "AuxT/Basic.lean").write_text(
        "def f (n : Nat) : Nat := n + 1\n"
        "@[grind =] theorem f_eq (n : Nat) : f n = n + 1 := rfl\n"
        "theorem tg (n : Nat) : 0 < f n := by grind\n"
    )
    subprocess.run(["lake", "build", "AuxT.Basic"], cwd=root, check=True, capture_output=True)
    (root / "dump.lean").write_text(olean._DUMP_KEEP_LEAN)
    (root / "mods.txt").write_text("AuxT.Basic\n")
    out = subprocess.run(["lake", "env", "lean", "--run", "dump.lean", "--modules-file", "mods.txt"],
                         cwd=root, check=True, capture_output=True, text=True).stdout
    edges = {tuple(line.split("\t")[1:]) for line in out.splitlines() if line.startswith("DEP\t")}
    assert ("AuxT.Basic", "tg", "AuxT.Basic", "f_eq") in edges and ("AuxT.Basic", "tg", "AuxT.Basic", "f") in edges


def test_edits_come_from_lean_and_build_without_repairs(tmp_path, monkeypatch):
    # The regex path leaves `open G in` in front of a kept definition once
    # every declaration of `G` is gone, and the build then fails on the
    # unknown namespace; Lean's view removes the prefix.
    monkeypatch.setenv("LEAN_STRIP_NO_BUILD_FALLBACK", "1")
    root = _project(tmp_path, {
        "lakefile.toml": 'name = "ev"\n[[lean_lib]]\nname = "Lib"\n[[lean_lib]]\nname = "Solution"\n'
                         '[[lean_lib]]\nname = "Challenge"\n',
        "Lib/A.lean": "def G.gone : Nat := 3\nopen G in\ndef used : Nat := 2\n",
        "Solution.lean": "import Lib.A\ntheorem main_thm : used = 2 := rfl\n",
        "Challenge.lean": "import Lib.A\ntheorem main_thm : used = 2 := sorry\n",
    })

    assert cli.main([str(root), "--jobs", "2", "--quiet"]) == 0

    text = (root / "Lib/A.lean").read_text()
    assert "gone" not in text and "open G" not in text and "def used : Nat := 2" in text
    report = json.loads((root / ".lean-strip/report.json").read_text())["engine_report"]
    assert report["lean_syntax"]["files_analyzed"] >= 1 and not report["lean_syntax"]["failures"]
    assert "Lib/A.lean" in report["strip"]["lean_edited_files"]


# `site` and `site2` realize `f.eq_1` and `g.eq_2` in Lib.B. The comparator
# compares `t` exactly (its value included: `main_thm` states something about
# `h`, whose body uses `t`); had the strip dropped the sites, `t` would realize
# the lemmas itself and its `_proof_N` would shift (PALOMAR-2026-10-20-000013).
_REALIZATION_FILES = {
    "Lib/A.lean": "module\n\n@[expose] public section\n\n"
                  "def f (n : Nat) : Nat :=\n  if h : n = 0 then 1 else f (n - 1) + 2\n"
                  "termination_by n\ndecreasing_by omega\n\n"
                  "def g : Nat → Nat\n  | 0 => 1\n  | n + 1 => g n + 2\n",
    "Lib/B.lean": "module\n\npublic import Lib.A\n\n@[expose] public section\n\n"
                  "theorem site (n : Nat) : f (n + 1) = f n + 2 := by rw [f]; simp\n\n"
                  "theorem site2 (n : Nat) : g (n + 1) = g n + 2 := by rw [g]\n\n"
                  "theorem unused_here : g 0 = 1 := rfl\n",
    "Lib/C.lean": "module\n\npublic import Lib.B\n\n@[expose] public section\n\n"
                  "theorem t (n : Nat) (h : n > 2) : f n ≥ 2 ∧ g (n + 1) ≥ 2 ∧ n > 1 := by\n"
                  "  rw [f, g]\n  exact ⟨by split <;> omega, by omega, by omega⟩\n\n"
                  "def h (n : Nat) (hn : n > 2) : Fin (n + 1) := ⟨0, by have := (t n hn).2.2; omega⟩\n",
    "Solution.lean": "module\n\npublic import Lib.C\n\n@[expose] public section\n\n"
                     "theorem main_thm (n : Nat) (hn : n > 2) : (h n hn).val = 0 := rfl\n",
    "Challenge.lean": "module\n\npublic import Lib.C\n\n@[expose] public section\n\n"
                      "theorem main_thm (n : Nat) (hn : n > 2) : (h n hn).val = 0 := sorry\n",
    "lakefile.toml": 'name = "real"\n[[lean_lib]]\nname = "Lib"\n[[lean_lib]]\nname = "Solution"\n'
                     '[[lean_lib]]\nname = "Challenge"\n',
}


def test_closure_query_finds_realization_sites(tmp_path):
    from lean_strip._pipeline.preprocessing import comparator_closure as cc

    root = tmp_path
    for relative, text in {"lean-toolchain": TOOLCHAIN, **_REALIZATION_FILES}.items():
        (root / relative).parent.mkdir(parents=True, exist_ok=True)
        (root / relative).write_text(text)
    subprocess.run(["lake", "build", "Solution"], cwd=root, check=True, capture_output=True)
    (root / "closure.lean").write_text(cc._COMPARATOR_CLOSURE_LEAN)
    (root / "input.txt").write_text(cc.closure_input(
        "Solution", ["Lib.A", "Lib.B", "Lib.C", "Solution"], ["main_thm"], ["g"], ["propext"]))
    out = subprocess.run(["lake", "env", "lean", "--run", "closure.lean", "input.txt"],
                         cwd=root, check=True, capture_output=True, text=True).stdout
    compared, reach = cc.parse_closure_output(out)
    # `h` is compared with its body, so `t` is compared with its proof; `g`
    # is a definition target, so only its type is walked.
    assert compared["t"] == ("Lib.C", True) and compared["h"] == ("Lib.C", True)
    assert "unused_here" not in compared
    sites = cc.realization_sites(reach)
    assert sites["f.eq_1"] == {"Lib.B": "site"}
    assert sites["g.eq_2"] == {"Lib.B": "site2"}


@pytest.mark.parametrize("definitions", [["g"], []])
def test_definition_configs_keep_realization_sites(tmp_path, definitions):
    comparator = {**COMPARATOR, "definition_names": definitions, "permitted_axioms": ["propext"]}
    root = _project(tmp_path, _REALIZATION_FILES, comparator=comparator)

    assert cli.main([str(root), "--jobs", "2", "--quiet", "--skip-comparator"]) == 0

    text = (root / "Lib/B.lean").read_text()
    report = json.loads((root / ".lean-strip/report.json").read_text())["engine_report"]
    assert "unused_here" not in text
    if definitions:
        assert "theorem site " in text and "theorem site2 " in text
        assert {"site", "site2"} <= set(report["comparator_closure"]["site_roots"])
    else:
        # A theorem-only config keeps the strip it had.
        assert "theorem site " not in text and "comparator_closure" not in report


def test_duplicate_theorems_keep_separate_kernel_and_source_dependencies(tmp_path):
    from lean_strip._pipeline.preprocessing.dependency_graph import collect_dependency_graph
    from lean_strip._pipeline.preprocessing.identity import decl_id
    from lean_strip.workspace import LocalWorkspace

    (tmp_path / "lean-toolchain").write_text(TOOLCHAIN)
    (tmp_path / "lakefile.toml").write_text(
        'name = "duplicates"\n[[lean_lib]]\nname = "A"\n[[lean_lib]]\nname = "B"\n'
    )
    originals = {
        f"/testbed/{module}.lean": (
            f"axiom only{module} : True\n"
            f"theorem shared : True := only{module}\n"
        )
        for module in ("A", "B")
    }
    for path, source in originals.items():
        (tmp_path / Path(path).name).write_text(source)
    subprocess.run(["lake", "build", "A", "B"], cwd=tmp_path, check=True, capture_output=True)
    workspace = LocalWorkspace(tmp_path, tmp_path.parent / (tmp_path.name + "-scratch"),
                               default_timeout=120, lean_threads=2)
    graph = collect_dependency_graph(workspace, originals, modules=["A", "B"])
    assert {decl_id(row) for row in graph.declarations} == {
        (module, name) for module in ("A", "B") for name in ("shared", f"only{module}")
    }
    for layer in ("kernel", "ilean", "source_text"):
        assert graph.edge_layers[layer] == {
            ((module, "shared"), (module, f"only{module}")) for module in ("A", "B")
        }

    # Exercise the engine's name-only comparator input as well: the entry
    # environment selects A's physical provider for protection. The graph
    # retains B's copy and its edges even when module pruning removes B.
    from lean_strip import engine
    from lean_strip._pipeline.preprocessing.identity import identity_rows

    diagnostics = tmp_path / "diagnostics"
    console = cli._Console(tmp_path / "pipeline.log", quiet=True)
    try:
        graph_only = engine.run_strip(workspace, engine.StripSettings(
            entry_module="A", build_target="A", protected={"shared"},
            diagnostics_dir=diagnostics, graph_only=True,
        ), console.stage)
        assert graph_only.report["protected_declaration_identities"] == identity_rows({("A", "shared")})
        graph_export = json.loads((diagnostics / "dependency-graph.json").read_text())
        assert graph_export["policies"]["production"]["removed"] == []
        result = engine.run_strip(workspace, engine.StripSettings(
            entry_module="A", build_target="A", protected={"shared"},
            diagnostics_dir=diagnostics,
        ), console.stage)
    finally:
        console.log_file.close()
    assert result.report["protected_declaration_identities"] == identity_rows({("A", "shared")})
    assert result.report["kept_declaration_identities"] == identity_rows({("A", "onlyA"), ("A", "shared")})
    exported = json.loads((diagnostics / "dependency-graph.json").read_text())
    state = exported["policies"]["production"]
    assert [decl_id(exported["nodes"][i]) for i in state["removed"]] == [("B", "onlyB"), ("B", "shared")]
    assert [decl_id(exported["nodes"][i]) for i in state["protected"]] == [("A", "shared")]



def test_isolated_olean_roots_preserve_imported_and_duplicate_dependencies(tmp_path):
    from lean_strip._pipeline.preprocessing import olean
    from lean_strip.workspace import LocalWorkspace

    (tmp_path / "lean-toolchain").write_text(TOOLCHAIN)
    (tmp_path / "lakefile.toml").write_text(
        'name = "isolated"\n[[lean_lib]]\nname = "A"\n[[lean_lib]]\nname = "B"\n'
        '[[lean_lib]]\nname = "Base"\n'
    )
    for name, source in {
        "Base": "axiom onlyBase : True\n",
        "A": "import Base\ntheorem shared : True := onlyBase\n",
        "B": "axiom onlyB : True\ntheorem shared : True := onlyB\n",
    }.items():
        (tmp_path / f"{name}.lean").write_text(source)
    subprocess.run(["lake", "build", "A", "B"], cwd=tmp_path, check=True, capture_output=True)
    ws = LocalWorkspace(tmp_path, tmp_path.parent / (tmp_path.name + "-scratch"),
                        default_timeout=120, lean_threads=2)
    decls, dependencies, _namespaces = olean.read_olean_declarations(ws, ["A", "B", "Base"], timeout=120)
    assert {(row["module"], row["name"]) for row in decls} == {
        ("A", "shared"), ("B", "shared"), ("B", "onlyB"), ("Base", "onlyBase"),
    }
    assert dependencies == {
        ("A", "shared"): {("Base", "onlyBase")},
        ("B", "shared"): {("B", "onlyB")},
    }


def test_batched_olean_roots_equal_one_process_per_root(tmp_path, monkeypatch):
    from lean_strip._pipeline.preprocessing import olean
    from lean_strip.workspace import LocalWorkspace

    (tmp_path / "lean-toolchain").write_text(TOOLCHAIN)
    sources = {
        "Base": "axiom onlyBase : True\ndef Base.value : Nat := 1\n",
        "Mid": "import Base\ntheorem Base.mid : Base.value = 1 := rfl\n",
        "Top": "import Mid\ntheorem top : Base.value = 1 := Base.mid\n",
        # Homonym definitions do not import together; the batch splits.
        "DefA": "def clash : Nat := 1\ntheorem usesA : clash = 1 := rfl\n",
        "DefB": "def clash : Nat := 2\ntheorem usesB : clash = 2 := rfl\n",
        # A homonym theorem may be merged at import; its roots are isolated.
        "ThmA": "import Base\ntheorem shared : True := onlyBase\n",
        "ThmB": "axiom onlyB : True\ntheorem shared : True := onlyB\n",
        "Free": "import Base\ntheorem free : Base.value = 1 := rfl\n",
    }
    (tmp_path / "lakefile.toml").write_text(
        'name = "batched"\n' + "".join(f'[[lean_lib]]\nname = "{name}"\n' for name in sources)
    )
    for name, source in sources.items():
        (tmp_path / f"{name}.lean").write_text(source)
    subprocess.run(["lake", "build", *sources], cwd=tmp_path, check=True, capture_output=True)
    ws = LocalWorkspace(tmp_path, tmp_path.parent / (tmp_path.name + "-scratch"),
                        default_timeout=120, lean_threads=2)

    batches = []
    write_file_bytes = ws.write_file_bytes

    def record_batch(path, payload):
        if path == olean._DUMP_KEEP_ROOT_PATH:
            batches.append(payload.decode().splitlines())
        return write_file_bytes(path, payload)

    monkeypatch.setattr(ws, "write_file_bytes", record_batch)

    def extract():
        decls, dependencies, namespaces = olean.read_olean_declarations(ws, list(sources), timeout=300)
        return sorted(map(sorted, map(dict.items, decls))), dependencies, namespaces

    batched = extract()
    assert batches[0] == list(sources)
    # The clash splits the first batch; the halves without it import cleanly
    # and the merged theorem's modules come back alone.
    names = list(sources)
    assert batches[1:3] == [names[:4], names[4:]]
    assert batches[3:] == [["ThmA"], ["ThmB"]]
    monkeypatch.setattr(olean, "_ROOTS_PER_PROCESS", 1)
    assert batched == extract()
    _decls, dependencies, _namespaces = batched
    assert dependencies[("ThmA", "shared")] == {("Base", "onlyBase")}
    assert dependencies[("ThmB", "shared")] == {("ThmB", "onlyB")}
    assert dependencies[("DefB", "usesB")] == {("DefB", "clash")}
    assert ("Mid", "Base.mid") in dependencies[("Top", "top")]
