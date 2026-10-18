import tomllib
from pathlib import Path

from lean_strip import lakefile

TEMPLATE_TOML = """\
name = "proj"
defaultTargets = ["Foo", "Solution", "Challenge", "demo"]

[[require]]
name = "mathlib"
scope = "leanprover-community"

[[lean_lib]]
name = "Foo"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Challenge"

[[lean_exe]]
name = "demo"
root = "Main"
"""


def _plan(tmp_path: Path, name: str, text: str, existed: set[str], surviving: set[str]):
    (tmp_path / name).write_text(text)
    return lakefile.plan(tmp_path, existed, surviving)


def test_toml_deleted_umbrella_root_builds_submodules(tmp_path):
    existed = {"Foo.lean", "Foo/A.lean", "Foo/B.lean", "Solution.lean", "Challenge.lean", "Main.lean"}
    surviving = {"Foo/A.lean", "Solution.lean", "Challenge.lean", "Main.lean"}
    edit = _plan(tmp_path, "lakefile.toml", TEMPLATE_TOML, existed, surviving)
    config = tomllib.loads(edit.text)
    assert config["lean_lib"][0]["globs"] == ["Foo.+"]
    assert "roots" not in config["lean_lib"][0]
    assert config["defaultTargets"] == ["Foo", "Solution", "Challenge", "demo"]
    assert not edit.unresolved


def test_toml_removes_executable_and_default_target(tmp_path):
    existed = {"Foo.lean", "Solution.lean", "Challenge.lean", "Main.lean"}
    surviving = {"Foo.lean", "Solution.lean", "Challenge.lean"}
    edit = _plan(tmp_path, "lakefile.toml", TEMPLATE_TOML, existed, surviving)
    config = tomllib.loads(edit.text)
    assert "lean_exe" not in config
    assert config["defaultTargets"] == ["Foo", "Solution", "Challenge"]
    assert any("demo" in change for change in edit.changes)


def test_toml_drops_glob_over_emptied_directory(tmp_path):
    text = TEMPLATE_TOML.replace('name = "Foo"\n', 'name = "Foo"\nglobs = ["Foo.+", "Bar.*"]\n')
    existed = {"Foo/A.lean", "Bar.lean", "Bar/X.lean", "Solution.lean", "Challenge.lean", "Main.lean"}
    surviving = {"Bar/X.lean", "Solution.lean", "Challenge.lean", "Main.lean"}
    edit = _plan(tmp_path, "lakefile.toml", text, existed, surviving)
    assert tomllib.loads(edit.text)["lean_lib"][0]["globs"] == ["Bar.+"]


def test_toml_unchanged_when_everything_survives(tmp_path):
    existed = surviving = {"Foo.lean", "Solution.lean", "Challenge.lean", "Main.lean"}
    edit = _plan(tmp_path, "lakefile.toml", TEMPLATE_TOML, existed, surviving)
    assert edit.text is None and not edit.changes


def test_toml_src_dir_and_explicit_roots(tmp_path):
    text = 'name = "p"\nsrcDir = "src"\n\n[[lean_lib]]\nname = "Lib"\nroots = ["Lib", "Extra"]\n'
    existed = {"src/Lib.lean", "src/Lib/A.lean", "src/Extra.lean"}
    surviving = {"src/Lib/A.lean", "src/Extra.lean"}
    edit = _plan(tmp_path, "lakefile.toml", text, existed, surviving)
    library = tomllib.loads(edit.text)["lean_lib"][0]
    assert library["roots"] == ["Lib", "Extra"]
    assert library["globs"] == ["Lib.+", "Extra"]


LAKEFILE_LEAN = """\
import Lake
open Lake DSL

package proj where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib Foo where
  -- the main library

lean_lib «Solution»

lean_lib Bar where
  globs := #[.submodules `Bar, `Baz]

@[default_target]
lean_exe demo where
  root := `Main
"""


def test_lean_rewrites_root_glob_and_exe(tmp_path):
    existed = {"Foo.lean", "Foo/A.lean", "Solution.lean", "Bar/X.lean", "Baz.lean", "Main.lean"}
    surviving = {"Foo/A.lean", "Solution.lean", "Baz.lean"}
    edit = _plan(tmp_path, "lakefile.lean", LAKEFILE_LEAN, existed, surviving)
    text = edit.text
    assert "lean_lib Foo where\n  globs := #[.submodules `Foo]\n  -- the main library" in text
    assert "globs := #[`Baz]" in text
    assert "lean_exe" not in text and "root := `Main" not in text
    assert "lean_lib «Solution»\n" in text
    assert not edit.unresolved


def test_lean_adds_where_to_bare_declaration(tmp_path):
    existed = {"Solution.lean", "Solution/A.lean"}
    surviving = {"Solution/A.lean"}
    edit = _plan(tmp_path, "lakefile.lean", LAKEFILE_LEAN, existed, surviving)
    assert "lean_lib «Solution» where\n  globs := #[.submodules `Solution]\n" in edit.text


def test_lean_dynamic_globs_are_reported_not_guessed(tmp_path):
    text = "import Lake\nopen Lake DSL\n\npackage p\n\nlean_lib Foo where\n  globs := allGlobs\n  roots := myRoots ++ #[`Foo]\n"
    existed = {"Foo.lean"}
    edit = _plan(tmp_path, "lakefile.lean", text, existed, set())
    assert edit.text is None
    assert edit.unresolved


def test_lean_brace_declaration(tmp_path):
    text = "import Lake\nopen Lake DSL\n\npackage «P» {\n}\n\n@[default_target]\nlean_lib «OneMfld» {\n  -- options\n}\n"
    edit = _plan(tmp_path, "lakefile.lean", text, {"OneMfld.lean", "OneMfld/A.lean"}, {"OneMfld/A.lean"})
    assert "lean_lib «OneMfld» {\n  globs := #[.submodules `OneMfld]\n  -- options\n}" in edit.text


def test_toml_default_target_naming_a_deleted_module(tmp_path):
    # PALOMAR-2026-10-01-000009: `defaultTargets = ["VCG.Main"]` is a module.
    text = ('name = "vcg"\ndefaultTargets = ["VCG.Main"]\n\n[[lean_lib]]\nname = "VCG"\n\n'
            '[[lean_lib]]\nname = "Solution"\n')
    existed = {"VCG.lean", "VCG/Main.lean", "VCG/Core.lean", "Solution.lean"}
    surviving = {"VCG.lean", "VCG/Core.lean", "Solution.lean"}
    edit = _plan(tmp_path, "lakefile.toml", text, existed, surviving)
    assert tomllib.loads(edit.text)["defaultTargets"] == ["VCG"]
    assert "defaultTargets: module VCG.Main was deleted; building library VCG instead" in edit.changes


def test_lean_indented_declaration_keeps_its_field_column(tmp_path):
    # PALOMAR-2026-09-15-000002 indents `lean_lib` under `@[default_target]`.
    text = ("import Lake\nopen Lake DSL\n\npackage p where\n  version := v!\"0.1.0\"\n\n"
            "@[default_target]\n  lean_lib Katz where\n    roots := #[`Katz.A, `Katz.B,\n      `Solution]\n")
    existed = {"Katz/A.lean", "Katz/B.lean", "Solution.lean"}
    surviving = {"Katz/A.lean", "Solution.lean"}
    edit = _plan(tmp_path, "lakefile.lean", text, existed, surviving)
    assert "  lean_lib Katz where\n    globs := #[`Katz.A, `Solution]\n    roots := #[" in edit.text


def test_toml_default_target_module_of_an_unbuildable_library_is_dropped(tmp_path):
    # PALOMAR-2026-10-01-000009: `lean_lib VCG` has no `VCG.lean`; only the module
    # `VCG.Main` was a default target, and the strip deleted it.
    text = ('name = "vcg"\ndefaultTargets = ["VCG.Main"]\n\n[[lean_lib]]\nname = "VCG"\n\n'
            '[[lean_lib]]\nname = "Solution"\n')
    existed = {"VCG/Main.lean", "VCG/Core.lean", "Solution.lean"}
    surviving = {"VCG/Core.lean", "Solution.lean"}
    edit = _plan(tmp_path, "lakefile.toml", text, existed, surviving)
    assert tomllib.loads(edit.text)["defaultTargets"] == []


def test_lean_globs_under_a_computed_src_dir_are_left_alone(tmp_path):
    # Review finding: `srcDir := srcPath` made `Foo.+` look empty and dropped it.
    text = ("import Lake\nopen Lake DSL\n\npackage p\n\ndef srcPath : FilePath := \"src\"\n\n"
            "lean_lib Foo where\n  srcDir := srcPath\n  globs := #[.submodules `Foo]\n")
    existed = {"src/Foo/A.lean", "src/Foo/B.lean"}
    edit = _plan(tmp_path, "lakefile.lean", text, existed, {"src/Foo/A.lean"})
    assert edit.text is None


def test_prefers_lakefile_lean_like_lake(tmp_path):
    (tmp_path / "lakefile.toml").write_text('name = "p"\n[[lean_lib]]\nname = "Foo"\n')
    edit = _plan(tmp_path, "lakefile.lean", "import Lake\nopen Lake DSL\npackage p\nlean_lib Foo\n",
                 {"Foo.lean", "Foo/A.lean"}, {"Foo/A.lean"})
    assert edit.path == "lakefile.lean"


def test_path_dependencies_are_found_transitively(tmp_path):
    # Review finding: `vendor/A` requiring `../B` left B to be stripped as project code.
    (tmp_path / "vendor/A/Inner").mkdir(parents=True)
    (tmp_path / "vendor/B").mkdir(parents=True)
    (tmp_path / "lakefile.toml").write_text('name = "p"\n[[require]]\nname = "A"\npath = "vendor/A"\n')
    (tmp_path / "vendor/A/lakefile.toml").write_text(
        'name = "A"\n[[require]]\nname = "B"\npath = "../B"\n[[require]]\nname = "I"\npath = "Inner"\n')
    (tmp_path / "vendor/A/Inner/lakefile.toml").write_text('name = "I"\n')
    (tmp_path / "vendor/B/lakefile.toml").write_text('name = "B"\n')
    assert lakefile.path_dependencies(tmp_path) == ("vendor/A", "vendor/B")
