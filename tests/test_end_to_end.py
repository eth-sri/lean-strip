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
    edges = {tuple(line.split("\t")[1:3]) for line in out.splitlines() if line.startswith("DEP\t")}
    assert ("tg", "f_eq") in edges and ("tg", "f") in edges


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
