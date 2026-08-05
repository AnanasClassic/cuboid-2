import json
from pathlib import Path

from research.arithmetic_geometry.e_model_dihedral_descent import verify


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = (
    ROOT / "research" / "arithmetic_geometry" / "e_model_dihedral_V.json"
)


def test_direct_v_descent_matches_exact_artifact():
    actual = verify()
    assert actual == json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert actual["base_point"] == {"q": "6", "A": "6/7", "V": "-36"}
    assert actual["status"] == "MACHINE-VERIFIED"
    assert "does not identify" in actual["logical_scope"]
