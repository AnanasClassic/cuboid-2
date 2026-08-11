import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]


def test_product_genus2_two_descent_matches_artifact():
    pytest.importorskip("cypari2")
    from research.arithmetic_geometry.product_genus2_two_descent import verify

    expected = json.loads(
        (ROOT / "research/arithmetic_geometry/product_genus2_two_descent.json").read_text()
    )
    assert verify() == expected
