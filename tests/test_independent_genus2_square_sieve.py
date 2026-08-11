import json
from pathlib import Path

from research.compact_signed_square.independent_genus2_square_sieve import verify


ROOT = Path(__file__).resolve().parents[1]


def test_independent_genus2_square_sieve_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research/compact_signed_square/independent_genus2_square_sieve.json"
        ).read_text()
    )
    assert verify() == expected
