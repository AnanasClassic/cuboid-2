#!/usr/bin/env sage -python
"""Rigorous finite Mordell--Weil sieve for the three square characters.

Assuming a certified transport from the normalization of ``H(q,A)=0`` to a
genus-one curve ``E0``, this script transfers the certified basis

    E1(Q) = <P=(0,2)> + <T=(1,0)>,
    E1: y^2=x^3-5*x+4,

to ``E0`` and tests every reduction of ``n*P+e*T`` at each selected good
prime.  The necessary conditions are

    q+2 is a square, q-2 is a square, epsilon*V is a square,
    V=N(q,A)/D(q,A), epsilon in {+1,-1}.

Zeros are accepted as squares.  Poles, indeterminate transport points, and
denominator-zero reductions are *also* accepted, because rejecting any such
reduction would be unsound.  Thus an empty generalized-CRT intersection is a
genuine exhaustive finite certificate.  A nonempty intersection is reported
only as an incomplete residual congruence set, never as evidence of absence.

This script excludes only the generic open locus represented by the certified
transport.  Projective/birational exceptional points must be closed by the
separate exact exceptional-locus audit before deriving the cuboid conjecture.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
from pathlib import Path

from sage.all import EllipticCurve, GF, QQ, ZZ, prime_range, proof, version  # type: ignore


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from research.mw_square_sieve.core import CongruenceSet, intersect_congruences


DEFAULT_MW = ROOT / "research" / "frobenius_audit" / "sage_candidate_mw_basis.json"
DEFAULT_V = ROOT / "research" / "quotient_transport" / "invariant_compact_v.json"
DEFAULT_OUTPUT = Path(__file__).with_name("mw_character_sieve.json")


def canonical_sha256(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def verify_embedded_checksum(payload: dict[str, object]) -> None:
    claimed = payload.get("sha256_without_checksum")
    if claimed is None:
        return
    body = dict(payload)
    del body["sha256_without_checksum"]
    if canonical_sha256(body) != claimed:
        raise AssertionError("input artifact checksum mismatch")


def rational_mod(value, field):
    value = QQ(value)
    denominator = ZZ(value.denominator())
    if denominator % field.characteristic() == 0:
        raise ZeroDivisionError("rational coefficient has bad denominator")
    return field(ZZ(value.numerator())) / field(denominator)


def point_mod(point, curve_finite, field):
    return curve_finite([rational_mod(value, field) for value in point])


def polynomial_value_mod(polynomial, coordinates, field):
    answer = field(0)
    for powers, coefficient in polynomial.dict().items():
        term = rational_mod(coefficient, field)
        for coordinate, power in zip(coordinates, powers):
            term *= coordinate ** int(power)
        answer += term
    return answer


def sparse_bivariate_value(terms, first, second, field):
    """Evaluate integer sparse terms in variables ``(q,A)``."""

    answer = field(0)
    first_powers = [field(1)]
    second_powers = [field(1)]
    max_first = max(int(term["powers"][0]) for term in terms)
    max_second = max(int(term["powers"][1]) for term in terms)
    for _ in range(max_first):
        first_powers.append(first_powers[-1] * first)
    for _ in range(max_second):
        second_powers.append(second_powers[-1] * second)
    for term in terms:
        first_power, second_power = map(int, term["powers"])
        answer += (
            field(ZZ(term["coefficient"]))
            * first_powers[first_power]
            * second_powers[second_power]
        )
    return answer


def square_or_zero(value) -> bool:
    return value == 0 or bool(value.is_square())


def parse_transport(path: Path):
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("status") != "WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED":
        raise AssertionError("transport is not certified")
    if data.get("candidate_exact_match") != "544.c_E1":
        raise AssertionError("transport does not identify the quotient with candidate E1")

    source_curve = EllipticCurve(QQ, [QQ(value) for value in data["weierstrass_ainvs"]])
    transport = data["transport_on_weierstrass"]
    ring = source_curve.ambient_space().coordinate_ring()
    q_num = ring(transport["q_numerator"])
    a_num = ring(transport["A_numerator"])
    denominator = ring(transport["common_affine_denominator"])
    if q_num.total_degree() != denominator.total_degree():
        raise AssertionError("q numerator and denominator have unequal projective degree")
    if a_num.total_degree() != denominator.total_degree():
        raise AssertionError("A numerator and denominator have unequal projective degree")
    return data, source_curve, q_num, a_num, denominator


def verify_mw_certificate(path: Path, candidate_curve) -> dict[str, object]:
    data = json.loads(path.read_text(encoding="utf-8"))
    expected_ainvs = [str(value) for value in candidate_curve.a_invariants()]
    if data.get("curve_ainvs") != expected_ainvs:
        raise AssertionError("Mordell--Weil certificate is not bound to candidate E1")
    if data.get("rank_bounds") != [1, 1] or data.get("rank_proof_true") != 1:
        raise AssertionError("Mordell--Weil certificate does not prove rank one")
    if not data.get("gens_certain"):
        raise AssertionError("Mordell--Weil generators were not certified")
    if data.get("P_full_saturation", {}).get("index") != 1:
        raise AssertionError("P=(0,2) is not certified saturated")
    if data.get("P") != "(0 : 2 : 1)":
        raise AssertionError("Mordell--Weil certificate names an unexpected P")
    if data.get("gens_proof_true") != ["(0 : 2 : 1)"]:
        raise AssertionError("certified generator list is not exactly P=(0,2)")
    if candidate_curve.torsion_subgroup().order() != 2:
        raise AssertionError("candidate E1 does not have the expected torsion")
    return data


def reduction_conditions(
    point,
    field,
    q_num,
    a_num,
    affine_denominator,
    v_numerator_terms,
    v_denominator_terms,
):
    coordinates = list(point)
    denominator_value = polynomial_value_mod(affine_denominator, coordinates, field)
    if denominator_value == 0:
        return {
            +1: True,
            -1: True,
            "reason": "transport_denominator_zero_allowed",
        }
    q_value = polynomial_value_mod(q_num, coordinates, field) / denominator_value
    a_value = polynomial_value_mod(a_num, coordinates, field) / denominator_value
    if not square_or_zero(q_value + 2) or not square_or_zero(q_value - 2):
        return {+1: False, -1: False, "reason": "q_square_character_rejected"}

    v_denominator = sparse_bivariate_value(v_denominator_terms, q_value, a_value, field)
    if v_denominator == 0:
        return {
            +1: True,
            -1: True,
            "reason": "V_denominator_zero_allowed",
        }
    v_numerator = sparse_bivariate_value(v_numerator_terms, q_value, a_value, field)
    v_value = v_numerator / v_denominator
    return {
        +1: square_or_zero(v_value),
        -1: square_or_zero(-v_value),
        "reason": "finite_values",
    }


def prime_condition(
    prime: int,
    source_curve,
    source_P,
    source_T,
    q_num,
    a_num,
    affine_denominator,
    v_data,
):
    field = GF(prime)
    curve_finite = source_curve.change_ring(field)
    if curve_finite.discriminant() == 0:
        raise ValueError("bad reduction of elliptic curve")
    point_P = point_mod(source_P, curve_finite, field)
    point_T = point_mod(source_T, curve_finite, field)
    if 2 * point_T != curve_finite(0):
        raise AssertionError("the rational two-torsion did not reduce to two-torsion")
    order = int(point_P.order())
    if order <= 0:
        raise AssertionError("invalid order of reduced free generator")

    allowed = {(epsilon, torsion): set() for epsilon in (+1, -1) for torsion in (0, 1)}
    reasons: dict[str, int] = {}
    for torsion in (0, 1):
        point = torsion * point_T
        for residue in range(order):
            condition = reduction_conditions(
                point,
                field,
                q_num,
                a_num,
                affine_denominator,
                v_data["numerator"],
                v_data["denominator"],
            )
            reasons[str(condition["reason"])] = reasons.get(str(condition["reason"]), 0) + 1
            for epsilon in (+1, -1):
                if condition[epsilon]:
                    allowed[(epsilon, torsion)].add(residue)
            point += point_P
        if point != torsion * point_T:
            raise AssertionError("enumeration did not return after ord(P mod p) steps")
    return {
        "prime": prime,
        "order_P": order,
        "curve_cardinality": int(curve_finite.cardinality()),
        "allowed": allowed,
        "reason_counts": reasons,
    }


def serialized_congruence(state: CongruenceSet, output_limit: int) -> dict[str, object]:
    ordered = sorted(state.residues)
    payload: dict[str, object] = {
        "modulus": state.modulus,
        "survivor_count": len(ordered),
        "survivors_sha256": canonical_sha256(ordered),
    }
    if len(ordered) <= output_limit:
        payload["residues"] = ordered
        payload["residues_complete"] = True
    else:
        payload["residue_prefix"] = ordered[:output_limit]
        payload["residues_complete"] = False
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--mw-certificate", type=Path, default=DEFAULT_MW)
    parser.add_argument("--v-artifact", type=Path, default=DEFAULT_V)
    parser.add_argument("--prime-bound", type=int, default=200)
    parser.add_argument("--primes", help="comma-separated override")
    parser.add_argument("--max-survivors", type=int, default=2_000_000)
    parser.add_argument("--output-residue-limit", type=int, default=20_000)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    proof.all(True)
    transport_data, source_curve, q_num, a_num, affine_den = parse_transport(args.transport)
    candidate = EllipticCurve(QQ, [0, 0, 0, -5, 4])
    mw_data = verify_mw_certificate(args.mw_certificate, candidate)
    isomorphism = source_curve.isomorphism_to(candidate)
    inverse_isomorphism = isomorphism.inverse()
    source_P = inverse_isomorphism(candidate(0, 2))
    source_T = inverse_isomorphism(candidate(1, 0))
    if isomorphism(source_P) != candidate(0, 2) or isomorphism(source_T) != candidate(1, 0):
        raise AssertionError("basis transport through the exact isomorphism failed")

    v_data = json.loads(args.v_artifact.read_text(encoding="utf-8"))
    verify_embedded_checksum(v_data)
    if v_data.get("status") != "MACHINE-VERIFIED" or v_data.get("variables") != ["q", "A"]:
        raise AssertionError("compact V artifact is not certified in variables q,A")

    if args.primes:
        primes = [int(value) for value in args.primes.split(",") if value.strip()]
    else:
        primes = [int(value) for value in prime_range(3, args.prime_bound + 1)]
    if any(value <= 2 or not ZZ(value).is_prime() for value in primes):
        raise ValueError("all sieve primes must be odd primes")

    states = {
        (epsilon, torsion): CongruenceSet.all_integers()
        for epsilon in (+1, -1)
        for torsion in (0, 1)
    }
    prime_records = []
    skipped_primes = []
    overflow = None
    for prime in primes:
        try:
            local = prime_condition(
                prime,
                source_curve,
                source_P,
                source_T,
                q_num,
                a_num,
                affine_den,
                v_data,
            )
        except (ArithmeticError, TypeError, ValueError, ZeroDivisionError) as error:
            skipped_primes.append({"prime": prime, "reason": repr(error)})
            continue

        before = {str(key): len(value.residues) for key, value in states.items()}
        try:
            next_states = {}
            for key, state in tuple(states.items()):
                next_states[key] = intersect_congruences(
                    state,
                    local["order_P"],
                    local["allowed"][key],
                    max_survivors=args.max_survivors,
                )
        except OverflowError as error:
            overflow = {"prime": prime, "reason": str(error)}
            break
        states = next_states
        after = {str(key): len(value.residues) for key, value in states.items()}
        prime_records.append(
            {
                "prime": prime,
                "order_P": local["order_P"],
                "curve_cardinality": local["curve_cardinality"],
                "allowed_counts": {
                    str(key): len(value) for key, value in local["allowed"].items()
                },
                "reason_counts": local["reason_counts"],
                "survivors_before": before,
                "survivors_after": after,
            }
        )
        if all(not state.residues for state in states.values()):
            break

    empty = all(not state.residues for state in states.values())
    if empty:
        status = "GENERIC_OPEN_EXCLUDED_BY_EXHAUSTIVE_FINITE_MW_SIEVE"
    elif overflow is not None:
        status = "COMPUTATIONAL_LIMIT_NO_MATHEMATICAL_CONCLUSION"
    else:
        status = "INCOMPLETE_FINITE_SIEVE_NONEMPTY_RESIDUAL_CLASSES"

    result = {
        "schema": 1,
        "status": status,
        "logical_scope": (
            "Necessary square-character conditions on the certified generic open "
            "elliptic quotient. Even an empty result requires the separately "
            "certified projective/birational exceptional-locus audit and exact "
            "reverse lift before concluding the cuboid conjecture."
        ),
        "soundness": {
            "global_parameterization": "every E1(Q) point is n*(0,2)+e*(1,0)",
            "finite_conditions": ["q+2 square", "q-2 square", "epsilon*V square"],
            "zeros": "accepted",
            "poles_and_zero_denominator_reductions": "accepted, never rejected",
            "empty_intersection_implication": (
                "no rational point in the transported generic open locus can "
                "satisfy all three square characters"
            ),
            "nonempty_intersection_implication": "none beyond the displayed necessary classes",
        },
        "sage_version": version(),
        "python_version": platform.python_version(),
        "inputs": {
            "transport": str(args.transport),
            "transport_sha256": hashlib.sha256(args.transport.read_bytes()).hexdigest(),
            "mw_certificate": str(args.mw_certificate),
            "mw_certificate_sha256": hashlib.sha256(args.mw_certificate.read_bytes()).hexdigest(),
            "compact_V": str(args.v_artifact),
            "compact_V_sha256": hashlib.sha256(args.v_artifact.read_bytes()).hexdigest(),
        },
        "source_curve_ainvs": [str(value) for value in source_curve.a_invariants()],
        "candidate_curve": "y^2=x^3-5*x+4",
        "basis_on_source_curve": {
            "P": str(source_P),
            "T": str(source_T),
            "rank_bounds": mw_data["rank_bounds"],
            "P_saturation_index": mw_data["P_full_saturation"]["index"],
        },
        "prime_records": prime_records,
        "skipped_primes": skipped_primes,
        "overflow": overflow,
        "residual_classes": {
            f"epsilon={epsilon},torsion={torsion}": serialized_congruence(
                states[(epsilon, torsion)], args.output_residue_limit
            )
            for epsilon in (+1, -1)
            for torsion in (0, 1)
        },
        "exceptional_loci_still_external": [
            "base points and denominator-zero points of the projective transport",
            "q=+/-2 and T=0,infinity boundary fibers",
            "Q1(T,A)=0 inverse-subresultant fibers",
            "B=+/-1 and b=-1 charts",
            "final exact R0=R1 lift verification",
        ],
    }
    result["sha256_without_checksum"] = canonical_sha256(result)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("CERT status =", status, flush=True)
    print("CERT primes_used =", [item["prime"] for item in prime_records], flush=True)
    for key, state in states.items():
        print(
            f"CERT epsilon_torsion={key} modulus={state.modulus} survivors={len(state.residues)}",
            flush=True,
        )
    print("CERT output =", args.output, flush=True)


if __name__ == "__main__":
    main()
