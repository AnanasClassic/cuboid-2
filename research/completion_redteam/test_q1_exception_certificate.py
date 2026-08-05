"""Regression test for the exact Q1 exceptional-locus certificate."""

from q1_exception_certificate import verify


def test_q1_exception_certificate() -> None:
    payload = verify()
    assert payload["status"] == "MACHINE-VERIFIED"
    assert payload["rational_roots_with_multiplicity"] == {
        "-1": 40,
        "0": 44,
        "1": 100,
    }
    assert all(
        not fibre["admissible"] for fibre in payload["boundary_fibres"].values()
    )
