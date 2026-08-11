import json
from pathlib import Path
import subprocess
import sys

import pytest

from research.proof_simplification_2 import richelot_isogeny_descent as target_b


ROOT = Path(__file__).resolve().parents[1]


def test_richelot_isogeny_descent_certificate_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research/proof_simplification_2/richelot_isogeny_descent.json"
        ).read_text()
    )
    assert target_b.verify() == expected
    assert expected["schema"] == 2
    assert expected["target"] == "B"
    assert expected["status"] == "PASS"
    assert (
        expected["richelot_geometry"]["correct_target_curve"]
        == "V^2=2*(2*t^2-4*t+1)*(4*t^4+4*t^2+5)"
    )


def test_optional_old_descent_cannot_overwrite_canonical_artifact():
    """Replay mode must require a separately named, noncanonical transcript."""

    script = (
        ROOT
        / "research/proof_simplification_2/richelot_isogeny_descent.py"
    )
    canonical = script.with_suffix(".json")
    before = canonical.read_bytes()
    result = subprocess.run(
        [sys.executable, str(script), "--replay-full-descent"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 2
    assert "requires an explicit noncanonical --output" in result.stderr
    assert canonical.read_bytes() == before


def test_bad_prime_set_is_recomputed_from_exact_discriminants(monkeypatch):
    """The Selmer set must fail if the source discriminant support changes."""

    audit = target_b.verify_bad_prime_support()
    assert audit["source_polynomial_discriminant"] == 2**14 * 5**2 * 17
    assert audit["target_polynomial_discriminant"] == 2**47 * 5 * 17**2
    assert audit["complete_finite_bad_prime_set"] == [2, 5, 17]

    original = target_b.sp.discriminant

    def corrupt_source_discriminant(polynomial, variable):
        value = original(polynomial, variable)
        if target_b.sp.Poly(polynomial, variable).degree() == 5:
            return 3 * value
        return value

    monkeypatch.setattr(
        target_b.sp,
        "discriminant",
        corrupt_source_discriminant,
    )
    with pytest.raises(
        target_b.CertificateFailure,
        match="source discriminant",
    ):
        target_b.verify_bad_prime_support()
