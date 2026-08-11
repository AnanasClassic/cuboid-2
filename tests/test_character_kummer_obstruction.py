import json
from pathlib import Path

from research.arithmetic_geometry.character_kummer_obstruction import verify


ROOT = Path(__file__).resolve().parents[1]


def test_character_kummer_obstruction_certificate_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research/arithmetic_geometry/character_kummer_obstruction.json"
        ).read_text()
    )
    assert verify() == expected
