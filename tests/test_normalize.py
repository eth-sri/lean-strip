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
