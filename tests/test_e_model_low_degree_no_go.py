import hashlib
import json
from pathlib import Path

from research.arithmetic_geometry.e_model_low_degree_no_go import verify


ROOT = Path(__file__).resolve().parents[1]
FROZEN = (
    ROOT
    / "research"
    / "arithmetic_geometry"
    / "e_model_low_degree_no_go.json"
)


def test_low_degree_transport_no_go_certificate():
    frozen = json.loads(FROZEN.read_text(encoding="utf-8"))
    without_checksum = dict(frozen)
    claimed_checksum = without_checksum.pop("sha256_without_checksum")
    canonical = json.dumps(
        without_checksum, sort_keys=True, separators=(",", ":")
    ).encode()
    assert claimed_checksum == hashlib.sha256(canonical).hexdigest()

    payload = verify()
    assert payload == frozen
    assert payload["shift_family"]["only_rational_shift_with_common_C_factor"] == (
        "c=2"
    )
    assert payload["shift_family"]["common_factor_for_symbolic_q0"] == "C^6"
    assert payload["shift_family"]["primitive_degrees_for_every_rational_q0"] == {
        "r": 8,
        "C": 12,
        "total": 12,
    }
    assert min(
        point["line_pencil_degree"]
        for point in payload["rational_singularities"]["affine"]
        + [payload["rational_singularities"]["projective_infinity"]]
    ) == 8
    assert payload["degree_two_q_map_obstruction"]["conclusion"] == (
        "q does not factor through any QQ-defined degree-2 genus-zero quotient."
    )
    assert payload["q_map_passport"]["ramification_sum"] == 20
    assert payload["q_map_passport"]["riemann_hurwitz_genus"] == 1
    assert "No normalization" in payload["logical_scope"]["not_proved"]
