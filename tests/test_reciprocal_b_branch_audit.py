import json
from pathlib import Path

from research.arithmetic_geometry.reciprocal_b_branch_audit import verify


ROOT = Path(__file__).resolve().parents[1]


def test_reciprocal_b_branch_certificate_matches_artifact():
    expected = json.loads(
        (ROOT / "artifacts" / "reciprocal_b_branch_audit.json").read_text()
    )
    assert verify() == expected
