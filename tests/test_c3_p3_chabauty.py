import json
from pathlib import Path

from research.proof_simplification_2.c3_p3_chabauty import verify


ROOT = Path(__file__).resolve().parents[1]


def test_c3_p3_chabauty_certificate_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research/proof_simplification_2/c3_p3_chabauty.json"
        ).read_text()
    )
    assert verify() == expected
