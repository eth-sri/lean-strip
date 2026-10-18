from lean_strip import cli


def test_a_package_src_dir_applies_to_every_library(tmp_path):
    # PALOMAR-2026-10-08-000005 sets `srcDir := "lean"` on the package.
    (tmp_path / "lakefile.lean").write_text("\n".join([
        "import Lake",
        "open Lake DSL",
        "",
        "package matrixMultiplicationAllFields where",
        '  version := v!"0.1.0"',
        '  srcDir := "lean"',
        "",
        "@[default_target]",
        "lean_lib OAI",
        "",
        "lean_lib ComparatorAudit",
        "",
    ]))
    (tmp_path / "lean" / "ComparatorAudit").mkdir(parents=True)
    (tmp_path / "lean" / "ComparatorAudit" / "Solution.lean").write_text("")
    assert cli._module_source(tmp_path, "ComparatorAudit.Solution") == "lean/ComparatorAudit/Solution.lean"
    assert {src for src, _roots in cli._lake_libraries(tmp_path)} == {"lean"}


def test_a_library_src_dir_still_counts_without_a_package_one(tmp_path):
    (tmp_path / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\n\npackage p\n\nlean_lib Lib where\n  srcDir := "src"\n')
    assert cli._lake_libraries(tmp_path) == [("src", ["Lib"])]


def test_line_endings_are_normalized_for_the_strip_and_restored_on_apply(tmp_path):
    # PALOMAR-2026-10-13-000008 uses CRLF: the strip sees LF, the repository
    # keeps CRLF, and an untouched file is not reported as changed.
    repo, work = tmp_path / "repo", tmp_path / "work"
    for root in (repo, work):
        root.mkdir()
        (root / "A.lean").write_bytes(b"module\r\npublic import B\r\n\r\ntheorem a : True := trivial\r\n")
        (root / "B.lean").write_bytes("﻿theorem b : True := trivial\n".encode())
        (root / "Mixed.lean").write_bytes(b"theorem m : True := trivial\r\ntheorem n : True := trivial\n")
    styles = cli._normalize_text(work)
    assert styles == {"A.lean": (True, False), "B.lean": (False, True)}
    assert (work / "A.lean").read_text() == "module\npublic import B\n\ntheorem a : True := trivial\n"
    assert (work / "Mixed.lean").read_bytes() == (repo / "Mixed.lean").read_bytes()
    final = {f"/testbed/{name}": (work / name).read_bytes().decode() for name in ("A.lean", "B.lean", "Mixed.lean")}
    final["/testbed/A.lean"] = "module\npublic import B\n"
    applied = cli._apply_to_repository(repo, final, "Challenge.lean", tmp_path / "backup", styles=styles)
    assert applied["changed"] == ["A.lean"]
    assert (repo / "A.lean").read_bytes() == b"module\r\npublic import B\r\n"
    assert (repo / "B.lean").read_bytes() == "﻿theorem b : True := trivial\n".encode()
