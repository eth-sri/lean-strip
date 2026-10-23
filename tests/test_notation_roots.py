from lean_strip._pipeline.preprocessing.notation_roots import detect_notation_body_roots


def _decl(name, start, end):
    return {"name": name, "module": "M", "start_line": start, "end_line": end}


def test_names_in_a_kept_notation_body_are_roots():
    # PALOMAR-2026-10-22-000019: `local notation "r" => D.rank ∘ g` with `D` a
    # section variable; the strip deleted `SquareCrosscutData.rank` and the
    # notation failed its quotation precheck.
    source = "\n".join([
        "namespace P",
        "structure SquareCrosscutData (N : Nat) where",
        "  x : Nat",
        "def SquareCrosscutData.rank (D : SquareCrosscutData N) : Nat := D.x",
        "def window (n : Nat) : Nat := n",
        "def unused : Nat := 0",
        "section",
        "variable (n : Nat)",
        "variable (D : SquareCrosscutData (112*n+1))",
        "local notation \"g\" => window n",
        "local notation \"r\" =>",
        "  D.rank",
        "end",
        "end P",
    ])
    decls = [_decl("P.SquareCrosscutData", 2, 3), _decl("P.SquareCrosscutData.rank", 4, 4),
             _decl("P.window", 5, 5), _decl("P.unused", 6, 6)]
    assert detect_notation_body_roots(decls, {"M.lean": source}) == {
        "P.SquareCrosscutData.rank", "P.window"}
