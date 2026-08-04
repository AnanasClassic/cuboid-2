from src.symbolic_reduction import verify


def test_all_symbolic_certificates():
    result = verify()
    assert result["normalization"] == "verified"
    assert result["resultant_equals_F"] == "verified"
    assert result["F_degrees"] == {"s": 16, "a": 10, "total": 17}
    assert result["degenerate_rational_locus"] == [[-1, 2], [1, 2]]

