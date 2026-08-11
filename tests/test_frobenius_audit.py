import hashlib
import json
from pathlib import Path

from research.frobenius_audit.candidate_544c_check import (
    CERTIFIED_TRACES,
    verify as verify_candidate,
)
from research.frobenius_audit.candidate_544c_rank_descent import (
    verify as verify_candidate_rank,
)
from research.frobenius_audit.frobenius_burnside import verify


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "research" / "frobenius_audit" / "frobenius_fingerprint.json"
CANDIDATE_ARTIFACT = (
    ROOT / "research" / "frobenius_audit" / "candidate_544c_check.json"
)
RANK_ARTIFACT = (
    ROOT
    / "research"
    / "frobenius_audit"
    / "candidate_544c_rank_descent.json"
)
RANK_PROOF = (
    ROOT / "research" / "frobenius_audit" / "candidate_544c_rank_proof.md"
)


def _checksum(payload):
    without_checksum = dict(payload)
    claimed = without_checksum.pop("sha256_without_checksum")
    canonical = json.dumps(
        without_checksum, sort_keys=True, separators=(",", ":")
    ).encode()
    return claimed, hashlib.sha256(canonical).hexdigest()


def test_frobenius_artifact_checksum_scope_and_table():
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert _checksum(payload)[0] == _checksum(payload)[1]
    assert payload["good_reduction_certificate"]["excluded_primes"] == [
        2,
        3,
        5,
        17,
        43,
        47,
    ]
    assert "does not identify" in payload["scope"]
    traces = {record["p"]: record["trace"] for record in payload["traces"]}
    assert traces == {
        7: -2,
        11: -4,
        13: 2,
        19: -4,
        23: -6,
        29: 8,
        31: 2,
        37: 4,
        41: -2,
        53: -6,
        59: -4,
        61: 4,
        67: -4,
        71: 6,
        73: -6,
        79: 10,
        83: 12,
        89: -10,
        97: -10,
    }
    for record in payload["traces"]:
        assert 2 * record["E_points"] == (
            record["C_points"] + record["frobenius_tau_fixed"]
        )
        assert record["trace"] ** 2 <= 4 * record["p"]


def test_full_exact_recomputation_matches_artifact():
    assert verify(97) == json.loads(ARTIFACT.read_text(encoding="utf-8"))


def test_544c_candidate_checksum_traces_and_logical_scope():
    payload = json.loads(CANDIDATE_ARTIFACT.read_text(encoding="utf-8"))
    assert _checksum(payload)[0] == _checksum(payload)[1]
    assert payload["candidate_class"] == "544.c"
    assert len(payload["trace_matches"]) == len(CERTIFIED_TRACES) == 19
    for row in payload["trace_matches"]:
        expected = CERTIFIED_TRACES[row["p"]]
        assert row["certified_quotient_trace"] == expected
        assert row["E1_trace"] == expected
        assert row["E2_trace"] == expected
    assert payload["all_certified_traces_match_both_models"] is True
    assert "isomorphic or isogenous" in payload["logical_status"]["not_proved"][0]
    assert payload["external_candidate_metadata_only"]["reported_rank"] == 1
    assert "External metadata only" in payload[
        "external_candidate_metadata_only"
    ]["reported_generators_status"]
    assert "candidate guidance only" in payload[
        "external_candidate_metadata_only"
    ]["warning"]


def test_full_exact_544c_candidate_recomputation_matches_artifact():
    assert verify_candidate() == json.loads(
        CANDIDATE_ARTIFACT.read_text(encoding="utf-8")
    )


def test_544c_elementary_rank_descent_artifact_and_proof_scope():
    payload = json.loads(RANK_ARTIFACT.read_text(encoding="utf-8"))
    assert _checksum(payload)[0] == _checksum(payload)[1]
    assert payload["descent_images"]["sizes"] == [4, 2]
    assert payload["rank"] == 1
    assert payload["torsion_certificate"]["torsion_subgroup"] == "Z/2Z"
    assert payload["non_torsion_certificate"]["2P"] == ["25/16", "-3/64"]
    assert payload["external_data_used"] is False
    proof = RANK_PROOF.read_text(encoding="utf-8")
    assert "2^r=\\frac{AB}{4}" in proof
    assert "does not transport them to the cuboid quotient" in proof


def test_full_exact_544c_rank_descent_recomputation_matches_artifact():
    assert verify_candidate_rank() == json.loads(
        RANK_ARTIFACT.read_text(encoding="utf-8")
    )
