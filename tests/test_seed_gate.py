from lean_strip.engine import _generated_owner


def test_generated_helpers_are_seeded_through_their_declaration():
    # PALOMAR-2026-10-21-000010 lists `…literalSourcePar._proof_1` among its
    # protected theorems; it has no source range, so the declaration it is
    # named under is seeded instead.
    declared = {"P.literalSourcePar", "P.kernel", "P.kernel.field"}
    assert _generated_owner("P.literalSourcePar._proof_1", declared) == "P.literalSourcePar"
    assert _generated_owner("P.kernel.match_2", declared) == "P.kernel"
    assert _generated_owner("P.kernel.field._proof_3", declared) == "P.kernel.field"
    # Not generated, or no declared owner: still unresolved.
    assert _generated_owner("P.literalSourcePar.real_lemma", declared) is None
    assert _generated_owner("Q.other._proof_1", declared) is None
    assert _generated_owner("P.literalSourcePar", declared) is None
