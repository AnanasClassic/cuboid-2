import json
from pathlib import Path

from research.arithmetic_geometry.new_three_square_character_covers import verify


ROOT = Path(__file__).resolve().parents[1]


def test_three_square_character_cover_certificate_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research/arithmetic_geometry/new_three_square_character_covers.json"
        ).read_text()
    )
    assert verify() == expected
