import json
from pathlib import Path

from research.global_descent.inert_prime_power_family import verify as verify_axis
from research.global_descent.new_inert_pair_endpoint import verify as verify_inert_pair
from research.global_descent.new_local_A_B_audit import verify as verify_local_ab
from research.global_descent.new_two_prime_family import verify as verify_two_prime


ROOT = Path(__file__).resolve().parents[1]


def _artifact(name):
    return json.loads(
        (ROOT / "research" / "global_descent" / f"{name}.json").read_text()
    )


def test_prime_power_axis_certificate_matches_artifact():
    actual = verify_axis()
    assert actual == _artifact("inert_prime_power_family")
    assert len(actual["branches"]) == 10
    assert "omega(pq)>=2" in actual["stronger_obstruction"]


def test_local_a_b_audit_matches_artifact():
    actual = verify_local_ab()
    assert actual == _artifact("new_local_A_B_audit")
    assert actual["nonuniformity_witness"]["quadratic_pair_at_3"] == [0, 0]
    assert actual["nonuniformity_witness"]["quadratic_pair_at_5"] == [0, 2]


def test_two_prime_family_certificate_matches_artifact():
    actual = verify_two_prime()
    assert actual == _artifact("new_two_prime_family")
    assert actual["exceptional_primes_from_exact_endpoint_certificates"] == [5, 13]
    assert all(row["n_1_checked_exactly"] for row in actual["exceptional_prime_power_certificates"])


def test_inert_pair_endpoint_certificate_matches_artifact():
    actual = verify_inert_pair()
    assert actual == _artifact("new_inert_pair_endpoint")
    lemma = actual["negative_e2_e6_2_sylow_lemma"]
    assert "m,n odd" in actual["remaining_branches"]["negative"][0]
    assert "Legendre symbol -1" in lemma["consequences"][2]
