import json
from pathlib import Path

from research.arithmetic_geometry.low_degree_transport import verify


ROOT = Path(__file__).resolve().parents[1]


def test_low_degree_transport_certificate_matches_artifact():
    expected = json.loads(
        (ROOT / "research/arithmetic_geometry/low_degree_transport.json").read_text()
    )
    assert verify() == expected
