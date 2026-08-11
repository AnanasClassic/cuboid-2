import json
from pathlib import Path

from research.proof_simplification_2.richelot_isogeny_descent import verify


ROOT = Path(__file__).resolve().parents[1]


def test_richelot_isogeny_descent_certificate_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research/proof_simplification_2/richelot_isogeny_descent.json"
        ).read_text()
    )
    assert verify() == expected
