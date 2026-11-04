"""A declaration-free entry re-exports what the comparator checks, not support roots."""

from lean_strip._pipeline.preprocessing import strip


def _decl(module, name, line=1):
    return dict(name=name, module=module, kind="theorem", meta=False,
                start_line=line, start_col=0, end_line=line, end_col=50)


def _plan(a_imports_b, **kwargs):
    originals = {
        "/testbed/A.lean": ("import B\n" if a_imports_b else "") + "theorem main : True := trivial\n",
        "/testbed/B.lean": "theorem helper : True := trivial\n",
        "/testbed/Hub.lean": "import A\nimport B\n",
        "/testbed/Entry.lean": "import Hub\n",
    }
    paths = {module: f"/testbed/{module}.lean" for module in ("A", "B", "Hub", "Entry")}
    decls = [_decl("A", "main"), _decl("B", "helper")]
    roots = {("A", "main"), ("B", "helper")}
    planned, report = strip.plan_protected_module_prune(
        originals, decls, {}, roots, "Entry", known_module_paths=paths, **kwargs,
    )
    return planned["/testbed/Entry.lean"], report


def test_umbrella_imports_the_owner_of_every_protected_root():
    entry, report = _plan(a_imports_b=True)
    assert entry == "import A\nimport B\n"
    assert report["deleted_modules"] == ["Hub"]


def test_umbrella_skips_a_support_root_its_imports_already_reach():
    # PALOMAR-2026-10-18-000023: a `macro` body names `NormalizerLean.Basic`
    # declarations; the sweeps that built the October set did not import
    # their owner from `Solution/Part3.lean`, which reaches it anyway.
    entry, report = _plan(a_imports_b=True, support_names={("B", "helper")})
    assert entry == "import A\n"
    assert report["protected_modules"] == ["A", "B"]
    assert report["support_modules"] == ["B"]


def test_umbrella_still_imports_a_support_root_nothing_else_reaches():
    entry, _report = _plan(a_imports_b=False, support_names={("B", "helper")})
    assert entry == "import A\nimport B\n"


def test_notation_body_roots_are_reported_apart():
    source = "def helper : Nat := 0\n@[simp] def tagged : Nat := 0\nnotation \"h\" => helper + tagged\n"
    decls = [dict(name="helper", module="M", start_line=1, end_line=1),
             dict(name="tagged", module="M", start_line=2, end_line=2)]
    roots = strip.collect_implicit_dependency_roots(decls, {"/testbed/M.lean": source},
                                                    {"M": "/testbed/M.lean"})
    assert roots["notation_body_only"] == {("M", "helper")}
    assert {("M", "helper"), ("M", "tagged")} <= roots["implicit_kinds"] | roots["attributed"]
