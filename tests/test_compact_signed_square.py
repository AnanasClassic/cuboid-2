import json
from pathlib import Path

from research.compact_signed_square.compact_signed_square import verify


ROOT = Path(__file__).resolve().parents[1]


def test_compact_signed_square_certificate_matches_artifact():
    expected = json.loads(
        (
            ROOT
            / "research"
            / "compact_signed_square"
            / "compact_signed_square.json"
        ).read_text()
    )
    assert verify() == expected
