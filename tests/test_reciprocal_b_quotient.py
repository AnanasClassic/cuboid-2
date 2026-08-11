import json
from pathlib import Path

from research.symbolic_algebra.reciprocal_b_quotient import verify


ROOT = Path(__file__).resolve().parents[1]


def test_reciprocal_b_quotient_certificate_matches_artifact():
    expected = json.loads((ROOT / "artifacts" / "reciprocal_b_quotient.json").read_text())
    assert verify() == expected
