import json
from pathlib import Path

from research.arithmetic_geometry.product_genus2_p7_formal_log import verify


ROOT = Path(__file__).resolve().parents[1]


def test_product_genus2_p7_formal_log_matches_artifact():
    expected = json.loads(
        (ROOT / "research/arithmetic_geometry/product_genus2_p7_formal_log.json").read_text()
    )
    assert verify() == expected
