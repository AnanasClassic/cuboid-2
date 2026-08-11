import json
from pathlib import Path

from research.compact_signed_square.reciprocal_quotient.derive import verify


ROOT = Path(__file__).resolve().parents[1]


def test_reciprocal_quotient_certificate_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research/compact_signed_square/reciprocal_quotient/reciprocal_quotient.json"
        ).read_text()
    )
    assert verify() == expected
