import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]


def test_c041_structure_certificate_matches_artifact():
    pytest.importorskip("cypari2")
    from research.proof_simplification.c041_structure import verify

    expected = json.loads(
        (
            ROOT
            / "research/proof_simplification/c041_structure.json"
        ).read_text()
    )
    assert verify() == expected
