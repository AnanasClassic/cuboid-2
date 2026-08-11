import json
from pathlib import Path

from research.arithmetic_geometry.product_squareclass_valuation import verify


ROOT = Path(__file__).resolve().parents[1]


def test_product_squareclass_valuation_matches_artifact():
    expected = json.loads(
        (ROOT / "research/arithmetic_geometry/product_squareclass_valuation.json").read_text()
    )
    assert verify() == expected
