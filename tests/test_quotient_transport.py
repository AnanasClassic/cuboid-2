import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKPOINT = (
    ROOT / "research" / "quotient_transport" / "compact_v.json"
)
INVARIANT = (
    ROOT / "research" / "quotient_transport" / "invariant_compact_v.json"
)
EXCEPTIONS = (
    ROOT / "research" / "quotient_transport" / "transport_exceptions.json"
)


def _load_and_check(path: Path):
    payload = json.loads(path.read_text(encoding="utf-8"))
    without_checksum = dict(payload)
    claimed = without_checksum.pop("sha256_without_checksum")
    canonical = json.dumps(
        without_checksum, sort_keys=True, separators=(",", ":")
    ).encode()
    assert claimed == hashlib.sha256(canonical).hexdigest()
    return payload


def test_A_degree_nine_checkpoint_artifact():
    payload = _load_and_check(CHECKPOINT)
    assert payload["status"] == "MACHINE-VERIFIED"
    assert payload["degrees"] == {
        "numerator": {"q": 206, "A": 9, "terms": 2070},
        "denominator": {"q": 207, "A": 9, "terms": 2080},
    }
    assert payload["certificates"]["cross_multiplication_mod_H"][
        "exact_pseudo_remainder_terms"
    ] == []
    assert payload["base_point"]["V"] == "-36"
    assert "does not identify" in payload["logical_scope"]


def test_invariant_subresultant_artifact():
    payload = _load_and_check(INVARIANT)
    assert payload["status"] == "MACHINE-VERIFIED"
    assert payload["degrees"] == {
        "numerator": {"q": 100, "A": 9, "terms": 1010},
        "denominator": {"q": 101, "A": 9, "terms": 1020},
    }
    assert payload["certificates"]["cross_multiplication_mod_H"][
        "exact_pseudo_remainder_terms"
    ] == []
    assert payload["base_point"]["V"] == "-36"
    assert payload["exceptional_locus"]["equation"] == "denominator(q,A)=0"
    assert "does not identify" in payload["logical_scope"]


def test_transport_exception_classification():
    payload = _load_and_check(EXCEPTIONS)
    assert payload["status"] == "MACHINE-VERIFIED"
    assert set(payload["U_exceptional_resultant"]["only_rational_U_values"]) == {
        "-2",
        "-1",
        "2",
    }
    assert set(payload["q_chart_resultant"]["only_rational_q_values"]) == {
        "-10/3",
        "-2",
        "2",
    }
    assert payload["rational_U_fibres"]["U=-2"]["lift"]["admissible"] is False
    assert payload["rational_U_fibres"]["U=2"]["lift"]["admissible"] is False
    assert payload["rational_U_fibres"]["U=-1"]["rational_A_points"] == []
    assert payload["pseudo_denominator_certificate"][
        "exact_pseudo_remainder_terms"
    ] == []
    assert payload["admissible_denominator_theorem"]["q"] == "X+1/X>2"
    assert "nonzero at every H-point" in payload[
        "admissible_denominator_theorem"
    ]["conclusion"]
