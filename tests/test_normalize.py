import os

from lean_strip._pipeline import palomar_normalize as normalize


def test_local_imports_resolve_like_lean_not_by_suffix(tmp_path):
    # A vendored file whose path ends like a Mathlib module it imports
    # (PALOMAR-2026-10-06-000001): the Mathlib import is not local.
    root = tmp_path / "proj"
    vendored = root / "Proofs" / "PNT" / "Mathlib" / "Algebra" / "Support.lean"
    user = root / "Proofs" / "PNT" / "Smooth.lean"
    mathlib = tmp_path / "mathlib" / "Mathlib" / "Algebra" / "Support.lean"
    for path in (vendored, user, mathlib):
        path.parent.mkdir(parents=True, exist_ok=True)
    vendored.write_text("import Mathlib.Algebra.Support\n")
    user.write_text("import PNT.Mathlib.Algebra.Support\n")
    mathlib.write_text("")
    env = {"LEAN_SRC_PATH": os.pathsep.join([str(root), str(root / "Proofs"), str(tmp_path / "mathlib")])}

    modules = normalize.local_import_modules([vendored, user], root, env)

    assert modules == ("PNT.Mathlib.Algebra.Support",)


def test_module_paths_follow_the_search_path_and_never_guess():
    # PALOMAR-2026-09-28-000004: `Solution.lean` and `PaperN/PartI/Solution.lean`.
    from lean_strip._pipeline.preprocessing import strip

    paths = ["/testbed/Solution.lean", "/testbed/PaperN/PartI/Solution.lean", "/testbed/src/Lib/A.lean"]
    exact = strip.resolve_module_paths({"Solution", "Lib.A", "PaperN.PartI.Solution"}, paths,
                                       ["/testbed", "/testbed/src"])
    assert exact == {"Solution": "/testbed/Solution.lean", "Lib.A": "/testbed/src/Lib/A.lean",
                     "PaperN.PartI.Solution": "/testbed/PaperN/PartI/Solution.lean"}
    guessed = strip.resolve_module_paths({"Solution", "Lib.A"}, paths)
    assert guessed == {"Lib.A": "/testbed/src/Lib/A.lean"}


def test_closure_follows_imports_through_src_dirs(tmp_path, monkeypatch):
    # PALOMAR-2026-09-18-000005: `lean --src-deps` reported `Lib/Mod.lean` for a
    # library with `srcDir = "Lib"`, whose file is `Lib/Lib/Mod.lean`.
    root = tmp_path
    (root / "Lib" / "Lib").mkdir(parents=True)
    solution = root / "Solution.lean"
    solution.write_text("import Lib.Mod\n")
    module = root / "Lib" / "Lib" / "Mod.lean"
    module.write_text("def x := 1\n")

    class Result:
        stdout = f"{root}/Lib/Mod.lean\n"  # what `--src-deps` printed

    monkeypatch.setattr(normalize.subprocess, "run", lambda *a, **k: Result())
    env = {"LEAN_SRC_PATH": os.pathsep.join([str(root), str(root / "Lib")])}
    assert normalize.direct_local_dependencies(solution, root, env) == (module,)


def test_own_modules_win_over_same_named_vendored_files(tmp_path):
    # PALOMAR-2026-09-25-000018: `import Main` is the project's `Main.lean`,
    # not `vendor/leancert/Main.lean`, although that came first on the path.
    root = tmp_path / "repo"
    (root / "vendor" / "leancert").mkdir(parents=True)
    (root / "lakefile.toml").write_text('name = "z"\n\n[[require]]\nname = "leancert"\npath = "vendor/leancert"\n')
    (root / "vendor" / "leancert" / "lakefile.toml").write_text('name = "leancert"\n')
    (root / "vendor" / "leancert" / "Main.lean").write_text("def cli := 1\n")
    own_main = root / "Main.lean"
    own_main.write_text("theorem proof : True := trivial\n")
    solution = root / "Solution.lean"
    solution.write_text("import Main\n")
    env = {"LEAN_SRC_PATH": os.pathsep.join([str(root / "vendor" / "leancert"), str(root)])}
    assert normalize.local_import_modules([solution, own_main], root, env) == ("Main",)


def test_glob_libraries_are_left_alone_by_isolation(tmp_path):
    # PALOMAR-2026-10-11-000009: the kept modules of `.andSubmodules` spelled
    # out as ~5000 roots exceeded Lean's maximum recursion depth.
    lakefile = "\n".join([
        "import Lake",
        "open Lake DSL",
        "",
        "package SubdiffusiveProcess",
        "",
        "@[default_target]",
        "lean_lib SubdiffusiveProcess where",
        "  globs := #[.andSubmodules `SubdiffusiveProcess]",
        "  leanOptions := #[⟨`autoImplicit, false⟩]",
        "",
        "lean_lib SubdiffusiveProcessAudit where",
        "  globs := #[.submodules `SubdiffusiveProcessAudit]",
        "",
        "lean_lib Narrow where",
        "  globs := #[.one `Narrow.A]",
        "",
    ])
    (tmp_path / "lakefile.lean").write_text(lakefile)
    roots = ("SubdiffusiveProcessAudit.ProcessConvergence.Solution",
             "SubdiffusiveProcessAudit.ProcessConvergence.Challenge",
             *(f"SubdiffusiveProcess.Module{i}" for i in range(5000)))
    report = normalize.synchronize_lakefile_lean_roots(tmp_path, roots)
    assert report["status"] == "unchanged"
    assert (tmp_path / "lakefile.lean").read_text() == lakefile
    # A `.one` glob does not cover submodules, so that library is still narrowed.
    report = normalize.synchronize_lakefile_lean_roots(tmp_path, ("Narrow.A.B",))
    assert report["status"] == "rewritten" and "roots := #[`Narrow.A.B]" in (tmp_path / "lakefile.lean").read_text()


def test_quoted_module_components_are_compared_in_canonical_form():
    # PALOMAR-2026-10-28-000009 imports
    # `«ChromaticPolynomial».ConstantOnConnectedComponents`; the lakefile's
    # library is `ChromaticPolynomial`, and isolation found no library for it.
    from lean_strip._pipeline.palomar_normalize import canonical_module_name

    assert canonical_module_name("«ChromaticPolynomial».ConstantOnConnectedComponents") == \
        "ChromaticPolynomial.ConstantOnConnectedComponents"
    assert canonical_module_name("Foo.«Adic spaces».Bar") == "Foo.«Adic spaces».Bar"
    assert canonical_module_name("Mathlib.Data.Nat") == "Mathlib.Data.Nat"
    assert canonical_module_name("«A.B».C") == "«A.B».C"


def test_computed_roots_and_concatenated_globs_use_lakes_configuration(tmp_path, monkeypatch):
    # Sol P18: the owner is GS even though GSCayleyCharts has no GS. prefix.
    text = '''import Lake
open Lake DSL
package gs
def gsRoots : Array Lean.Name := #[`GS, `GSCayleyCharts]
lean_lib GS where
  roots := gsRoots
  globs := #[.submodules `GS] ++ gsRoots.map Glob.one
lean_lib Solution
lean_lib Challenge
'''
    path = tmp_path / "lakefile.lean"
    path.write_text(text)
    monkeypatch.setattr(normalize, "evaluated_libraries", lambda root: [
        {"name": "GS", "roots": ["GS", "GSCayleyCharts"],
         "globs": ["GS.+", "GS", "GSCayleyCharts"]},
        {"name": "Solution", "roots": ["Solution"], "globs": ["Solution"]},
        {"name": "Challenge", "roots": ["Challenge"], "globs": ["Challenge"]},
    ])
    report = normalize.synchronize_lakefile_lean_roots(tmp_path, ("GSCayleyCharts", "Solution"))
    assert report["status"] == "unchanged"
    assert path.read_text() == text


def test_computed_fields_are_replaced_whole_when_narrowing(tmp_path, monkeypatch):
    text = '''import Lake
open Lake DSL
package p
lean_lib Other where
  roots := chooseRoots
  globs := #[.one `Other] ++
    chooseMoreGlobs
'''
    path = tmp_path / "lakefile.lean"
    path.write_text(text)
    monkeypatch.setattr(normalize, "evaluated_libraries", lambda root: [
        {"name": "Other", "roots": ["Other"], "globs": ["Other"]},
    ])
    report = normalize.synchronize_lakefile_lean_roots(tmp_path, ("Other.Kept",))
    rewritten = path.read_text()
    assert report["status"] == "rewritten"
    assert "roots := #[`Other.Kept]" in rewritten
    assert "chooseRoots" not in rewritten
    assert "chooseMoreGlobs" not in rewritten
    assert "globs :=" not in rewritten


def test_evaluated_configuration_still_rejects_ambiguous_owners(tmp_path, monkeypatch):
    import pytest
    path = tmp_path / "lakefile.lean"
    text = 'import Lake\nopen Lake DSL\npackage p\nlean_lib A\nlean_lib B\n'
    path.write_text(text)
    monkeypatch.setattr(normalize, "evaluated_libraries", lambda root: [
        {"name": name, "roots": ["Shared"], "globs": ["Shared.*"]} for name in ["A", "B"]
    ])
    with pytest.raises(ValueError, match="exactly one lean_lib"):
        normalize.synchronize_lakefile_lean_roots(tmp_path, ("Shared.X",))
    assert path.read_text() == text
