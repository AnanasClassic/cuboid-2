#!/usr/bin/env sage -python
"""Exact reverse lift of one Mordell--Weil point to a quadratic factor.

This is the mandatory converse check after the finite MW sieve.  Given
``(n,e,epsilon)``, it evaluates the exact transported functions on
``n*P+e*T``, adjoins the two *rational* character roots, reconstructs
``T,z,s,B,b,a``, and directly divides ``P_s`` by ``x^2+a*x+b``.  Every sign
choice is tested.  A genuine lift also yields and directly multiplies a
quartic-by-sextic factorization of the original ``Q_{p,q}(t)``.

The generic formula ``B=-Q0/Q1`` is intentionally not used when ``Q1=0``;
such a point is emitted as an unresolved exceptional fiber and must be solved
from the original two equations in B.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from sage.all import EllipticCurve, PolynomialRing, QQ, ZZ, proof, version  # type: ignore


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from research.mw_square_sieve.sage_mw_character_sieve import (
    DEFAULT_MW,
    DEFAULT_V,
    canonical_sha256,
    parse_transport,
    sparse_bivariate_value,
    verify_embedded_checksum,
    verify_mw_certificate,
)


QUOTIENT = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_name("reconstructed_lift.json")


def rational_square_root(value):
    value = QQ(value)
    if value < 0 or not value.is_square():
        return None
    return QQ(value.sqrt())


def normalized_quintic(x, s):
    return (
        x**5
        + (2 + s) * (3 - 2 * s) * x**4
        + (1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4) * x**3
        - s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4) * x**2
        - s**3 * (1 + 2 * s) * (-2 + 3 * s) * x
        - s**5
    )


def original_Q(t, p, q):
    return (
        t**10
        + (2 * q**2 + p**2) * (3 * q**2 - 2 * p**2) * t**8
        + (q**8 + 10 * p**2 * q**6 + 4 * p**4 * q**4 - 14 * p**6 * q**2 + p**8)
        * t**6
        - p**2
        * q**2
        * (q**8 - 14 * p**2 * q**6 + 4 * p**4 * q**4 + 10 * p**6 * q**2 + p**8)
        * t**4
        - p**6 * q**6 * (q**2 + 2 * p**2) * (-2 * q**2 + 3 * p**2) * t**2
        - p**10 * q**10
    )


def direct_B_fiber(T_value, A_value):
    """Solve the original two remainder equations in B at fixed T,A.

    This is the denominator-zero branch omitted by ``B=-Q0/Q1``.  Returning
    ``None`` means both remainder numerators vanish identically and a
    positive-dimensional fiber would need separate analysis.
    """

    if T_value == 1:
        return [], {"status": "BOUNDARY_T_EQUALS_ONE"}
    z_value = QQ((1 + T_value) / (1 - T_value))
    s_value = z_value**2
    B_ring = PolynomialRing(QQ, "B")
    B = B_ring.gen()
    fraction_field = B_ring.fraction_field()
    x_ring = PolynomialRing(fraction_field, "x")
    x = x_ring.gen()
    a_function = fraction_field(A_value) / (1 - B)
    b_function = (1 + B) / (1 - B)
    P_s = normalized_quintic(x, s_value)
    divisor = x**2 + a_function * x + b_function
    _, remainder = P_s.quo_rem(divisor)
    r0 = B_ring(remainder[0].numerator())
    r1 = B_ring(remainder[1].numerator())
    if r0 == 0 and r1 == 0:
        return None, {
            "status": "POSITIVE_DIMENSIONAL_DIRECT_B_FIBER",
            "T": str(T_value),
            "A": str(A_value),
        }
    fiber_gcd = r0.gcd(r1).monic()
    roots = [QQ(root) for root, _multiplicity in fiber_gcd.roots(QQ)]
    for root in roots:
        if root == 1:
            continue
        if remainder[0](root) != 0 or remainder[1](root) != 0:
            raise AssertionError("direct B-fiber root does not kill both remainders")
    roots = [root for root in roots if root != 1]
    return roots, {
        "status": "DIRECT_B_FIBER_SOLVED_EXACTLY",
        "T": str(T_value),
        "A": str(A_value),
        "remainder_numerator_gcd": str(fiber_gcd),
        "rational_B_roots": [str(root) for root in roots],
        "all_rational_roots_complete": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--torsion", type=int, choices=(0, 1), required=True)
    parser.add_argument("--epsilon", type=int, choices=(-1, 1), required=True)
    parser.add_argument("--mw-certificate", type=Path, default=DEFAULT_MW)
    parser.add_argument("--v-artifact", type=Path, default=DEFAULT_V)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    proof.all(True)
    transport_data, source_curve, q_num, a_num, affine_den = parse_transport(args.transport)
    candidate = EllipticCurve(QQ, [0, 0, 0, -5, 4])
    verify_mw_certificate(args.mw_certificate, candidate)
    inverse_isomorphism = source_curve.isomorphism_to(candidate).inverse()
    source_P = inverse_isomorphism(candidate(0, 2))
    source_T = inverse_isomorphism(candidate(1, 0))
    point = args.n * source_P + args.torsion * source_T
    coordinates = list(point)
    denominator = affine_den(*coordinates)

    result: dict[str, object] = {
        "schema": 1,
        "sage_version": version(),
        "input": {
            "n": args.n,
            "torsion": args.torsion,
            "epsilon": args.epsilon,
            "transport": str(args.transport),
            "transport_sha256": hashlib.sha256(args.transport.read_bytes()).hexdigest(),
        },
        "point_on_transport_curve": str(point),
        "lifts": [],
    }
    if denominator == 0:
        result["status"] = "EXCEPTIONAL_TRANSPORT_DENOMINATOR_ZERO"
        result["required_action"] = "classify this projective transport fiber directly"
    else:
        q_value = QQ(q_num(*coordinates) / denominator)
        A_value = QQ(a_num(*coordinates) / denominator)
        root_plus = rational_square_root(q_value + 2)
        root_minus = rational_square_root(q_value - 2)
        result["q"] = str(q_value)
        result["A"] = str(A_value)
        result["r_plus"] = None if root_plus is None else str(root_plus)
        result["r_minus"] = None if root_minus is None else str(root_minus)
        if root_plus is None or root_minus is None:
            result["status"] = "REJECTED_Q_CHARACTER_NOT_RATIONAL_SQUARE"
        else:
            v_data = json.loads(args.v_artifact.read_text(encoding="utf-8"))
            verify_embedded_checksum(v_data)
            v_denominator = sparse_bivariate_value(v_data["denominator"], q_value, A_value, QQ)
            if v_denominator == 0:
                result["status"] = "EXCEPTIONAL_COMPACT_V_DENOMINATOR_ZERO"
                result["required_action"] = "apply the certified compact-V exceptional-locus audit"
            else:
                v_value = QQ(
                    sparse_bivariate_value(v_data["numerator"], q_value, A_value, QQ)
                    / v_denominator
                )
                signed_v_root = rational_square_root(args.epsilon * v_value)
                result["V"] = str(v_value)
                result["signed_V_root"] = (
                    None if signed_v_root is None else str(signed_v_root)
                )
                if signed_v_root is None:
                    result["status"] = "REJECTED_SIGNED_V_NOT_RATIONAL_SQUARE"
                else:
                    quotient = json.loads(QUOTIENT.read_text(encoding="utf-8"))
                    verify_embedded_checksum(quotient)
                    Q0_terms = quotient["linear_subresultant"]["Q0_terms"]
                    Q1_terms = quotient["linear_subresultant"]["Q1_terms"]
                    polynomial_x = PolynomialRing(QQ, "x")
                    x = polynomial_x.gen()
                    polynomial_t = PolynomialRing(QQ, "t")
                    t = polynomial_t.gen()
                    unresolved_q1 = False
                    genuine = False
                    for sign_plus in (+1, -1):
                        for sign_minus in (+1, -1):
                            rp = sign_plus * root_plus
                            rm = sign_minus * root_minus
                            T_value = QQ((rp + rm) / 2)
                            inverse_T = QQ((rp - rm) / 2)
                            if T_value * inverse_T != 1:
                                raise AssertionError("character roots did not reconstruct inverse T")
                            q_check = T_value**2 + T_value ** (-2)
                            if q_check != q_value:
                                raise AssertionError("reconstructed T does not recover q")
                            Q1_value = sparse_bivariate_value(Q1_terms, T_value, A_value, QQ)
                            if Q1_value == 0:
                                B_candidates, direct_audit = direct_B_fiber(T_value, A_value)
                                result["lifts"].append(direct_audit)
                                if B_candidates is None:
                                    unresolved_q1 = True
                                    continue
                            else:
                                Q0_value = sparse_bivariate_value(
                                    Q0_terms, T_value, A_value, QQ
                                )
                                B_candidates = [QQ(-Q0_value / Q1_value)]

                            for B_value in B_candidates:
                                if T_value == 1 or B_value == 1:
                                    result["lifts"].append(
                                        {
                                            "status": "BOUNDARY_T_OR_B_EQUALS_ONE",
                                            "T": str(T_value),
                                            "B": str(B_value),
                                        }
                                    )
                                    continue
                                z_value = QQ((1 + T_value) / (1 - T_value))
                                s_value = z_value**2
                                b_value = QQ((1 + B_value) / (1 - B_value))
                                a_value = QQ(A_value / (1 - B_value))
                                if z_value == 0 or s_value == 1 or b_value == 0:
                                    result["lifts"].append(
                                        {
                                            "status": "INADMISSIBLE_BOUNDARY_PARAMETER",
                                            "T": str(T_value),
                                            "B": str(B_value),
                                            "z": str(z_value),
                                            "s": str(s_value),
                                            "b": str(b_value),
                                        }
                                    )
                                    continue
                                if a_value == 0 or a_value**2 / b_value != v_value:
                                    result["lifts"].append(
                                        {
                                            "status": "V_RECONSTRUCTION_MISMATCH",
                                            "T": str(T_value),
                                            "B": str(B_value),
                                        }
                                    )
                                    continue
                                signed_b_root = rational_square_root(args.epsilon * b_value)
                                if signed_b_root is None:
                                    result["lifts"].append(
                                        {
                                            "status": "SIGNED_B_NOT_SQUARE_AFTER_RECONSTRUCTION",
                                            "T": str(T_value),
                                            "B": str(B_value),
                                        }
                                    )
                                    continue

                                P_s = normalized_quintic(x, s_value)
                                divisor = x**2 + a_value * x + b_value
                                cubic, remainder = P_s.quo_rem(divisor)
                                if remainder != 0:
                                    result["lifts"].append(
                                        {
                                            "status": "SPURIOUS_QUOTIENT_POINT_REMAINDER_NONZERO",
                                            "T": str(T_value),
                                            "B": str(B_value),
                                            "remainder": str(remainder),
                                        }
                                    )
                                    continue

                                ratio = abs(z_value)
                                p_integer = ZZ(abs(ratio.numerator()))
                                q_integer = ZZ(ratio.denominator())
                                if p_integer <= 0 or q_integer <= 0 or p_integer == q_integer:
                                    raise AssertionError(
                                        "a purported genuine lift is not admissible p,q"
                                    )
                                quartic = polynomial_t(
                                    t**4
                                    + a_value * q_integer**4 * t**2
                                    + b_value * q_integer**8
                                )
                                sextic = polynomial_t(
                                    q_integer**12 * cubic(t**2 / q_integer**4)
                                )
                                Q_original = polynomial_t(
                                    original_Q(t, p_integer, q_integer)
                                )
                                if quartic * sextic != Q_original:
                                    raise AssertionError("direct Q factor multiplication failed")
                                genuine = True
                                result["lifts"].append(
                                    {
                                        "status": "GENUINE_QUADRATIC_FACTOR_LIFT",
                                        "T": str(T_value),
                                        "B": str(B_value),
                                        "z": str(z_value),
                                        "s": str(s_value),
                                        "a": str(a_value),
                                        "b": str(b_value),
                                        "signed_b_root": str(signed_b_root),
                                        "normalized_divisor": str(divisor),
                                        "normalized_cubic_cofactor": str(cubic),
                                        "p": str(p_integer),
                                        "q_integer": str(q_integer),
                                        "Q_quartic_factor": str(quartic),
                                        "Q_sextic_factor": str(sextic),
                                        "direct_multiplication": "VERIFIED_EXACTLY",
                                    }
                                )
                    if genuine:
                        result["status"] = "GENUINE_QUADRATIC_FACTOR_LIFT_FOUND"
                    elif unresolved_q1:
                        result["status"] = "POSITIVE_DIMENSIONAL_Q1_ZERO_FIBER_REMAINS"
                    else:
                        result["status"] = "NO_GENUINE_LIFT_FROM_THIS_MW_POINT"

    result["sha256_without_checksum"] = canonical_sha256(result)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("CERT status =", result["status"], flush=True)
    print("CERT output =", args.output, flush=True)


if __name__ == "__main__":
    main()
