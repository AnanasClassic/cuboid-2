#!/usr/bin/env python3
"""Exact rational classification of the compact-V exceptional loci.

There are three possible losses in the invariant transport:

* division by the coefficient L in ``L(U,A) W + C(U,A)``;
* the Mobius chart ``U=2(q+6)/(q-2)``;
* pseudo-reduction in A, whose multiplier is ``lc_A(H)^10``.

This script computes exact resultants and their complete QQ-factorizations.
Only linear factors can support a QQ-rational U or q.  Those fibres are then
specialized and checked directly, including reverse substitution in the
original remainder equations R1=R0=0.  Thus the classification of rational
exceptional points is complete; the high-degree irreducible geometric
orbits are recorded but are not individually normalized.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from collections import defaultdict
from pathlib import Path

import sympy as sp
from sympy.polys.domains import QQ, ZZ


ROOT = Path(__file__).resolve().parents[2]
GENUS4 = ROOT / "artifacts" / "genus4_quotient.json"
COMPACT = Path(__file__).with_name("invariant_compact_v.json")
DEFAULT_OUTPUT = Path(__file__).with_name("transport_exceptions.json")

s, x, a, b = sp.symbols("s x a b")
U, W, q, A = sp.symbols("U W q A")
COEFFICIENT_RING = ZZ.poly_ring(q)


def sparse_to_poly(
    terms: list[dict[str, object]], variables: tuple[sp.Symbol, ...]
) -> sp.Poly:
    return sp.Poly.from_dict(
        {
            tuple(int(power) for power in term["powers"]): int(term["coefficient"])
            for term in terms
        },
        variables,
        domain=ZZ,
    )


def sparse(poly: sp.Poly) -> list[dict[str, object]]:
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in poly.terms()
    ]


def polynomial_digest(poly: sp.Poly) -> str:
    canonical = json.dumps(
        sparse(poly), sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(canonical).hexdigest()


def as_polynomial_in_A(poly: sp.Poly) -> sp.Poly:
    coefficients: defaultdict[int, dict[tuple[int], int]] = defaultdict(dict)
    for (q_degree, a_degree), coefficient in poly.terms():
        coefficients[a_degree][(q_degree,)] = int(coefficient)
    return sp.Poly.from_dict(
        {
            (a_degree,): COEFFICIENT_RING.new(coefficient)
            for a_degree, coefficient in coefficients.items()
        },
        (A,),
        domain=COEFFICIENT_RING,
    )


def mobius_U_to_q(poly: sp.Poly, common_degree: int) -> sp.Poly:
    transformed = sp.Integer(0)
    for (u_degree, a_degree), coefficient in poly.terms():
        transformed += (
            int(coefficient)
            * (2 * (q + 6)) ** u_degree
            * (q - 2) ** (common_degree - u_degree)
            * A**a_degree
        )
    return sp.Poly(sp.expand(transformed), q, A, domain=ZZ)


def mobius_q_to_U(poly: sp.Poly, common_degree: int) -> sp.Poly:
    transformed = sp.Integer(0)
    for (q_degree, a_degree), coefficient in poly.terms():
        transformed += (
            int(coefficient)
            * (2 * (U + 6)) ** q_degree
            * (U - 2) ** (common_degree - q_degree)
            * A**a_degree
        )
    return sp.Poly(sp.expand(transformed), U, A, domain=ZZ).primitive()[1]


def factor_records(
    factorization: list[tuple[sp.Expr, int]], variable: sp.Symbol
) -> list[dict[str, object]]:
    records = []
    for factor, exponent in factorization:
        poly = sp.Poly(factor, variable, domain=ZZ).primitive()[1]
        records.append(
            {
                "degree": int(poly.degree()),
                "exponent": int(exponent),
                "irreducible_over_QQ": True,
                "terms": sparse(poly),
                "sha256_sparse": polynomial_digest(poly),
            }
        )
    records.sort(key=lambda item: (item["degree"], item["sha256_sparse"]))
    return records


def monic_gcd_at_U(
    value: sp.Rational, H_U: sp.Poly, L: sp.Poly, C: sp.Poly
) -> sp.Poly:
    specialized = [
        sp.Poly(poly.as_expr().subs(U, value), A, domain=QQ)
        for poly in (H_U, L, C)
    ]
    answer = sp.gcd(sp.gcd(specialized[0], specialized[1]), specialized[2])
    return answer.monic()


def factorization_remainders() -> tuple[sp.Expr, sp.Expr]:
    c4 = (2 + s) * (3 - 2 * s)
    c3 = 1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4
    c2 = -s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4)
    c1 = -s**3 * (1 + 2 * s) * (-2 + 3 * s)
    c0 = -s**5
    u = -3 * a**2 + 2 * a * c4 - c3
    v = a**4 - c4 * a**3 + c3 * a**2 - c2 * a + c1
    m = c4 - 2 * a
    n = a**3 - c4 * a**2 + c3 * a - c2
    return (
        sp.expand(b**2 + u * b + v),
        sp.expand(m * b**2 + n * b + c0),
    )


def specialized_factor(poly: sp.Poly, q_value: sp.Rational) -> sp.Expr:
    value = sp.Poly(poly.as_expr().subs(q, q_value), A, domain=QQ)
    return sp.factor(value.monic().as_expr())


def verify() -> dict[str, object]:
    started = time.monotonic()
    genus4 = json.loads(GENUS4.read_text(encoding="utf-8"))
    compact = json.loads(COMPACT.read_text(encoding="utf-8"))
    H_q = sparse_to_poly(genus4["elliptic_plane_model"]["terms"], (q, A))
    D = sparse_to_poly(compact["denominator"], (q, A))
    linear = compact["certificates"]["linear_subresultant"]
    L = sparse_to_poly(linear["L_terms"], (U, A))
    C = sparse_to_poly(linear["C_terms"], (U, A))
    H_U = mobius_q_to_U(H_q, 8)

    # The saturated rational locus H_U=L=C=0 can only lie over a rational
    # root of Res_A(H_U,L).  Complete QQ factorization is therefore a finite,
    # exact completeness certificate for possible rational U-coordinates.
    resultant_U = sp.Poly(
        sp.resultant(H_U.as_expr(), L.as_expr(), A), U, domain=ZZ
    )
    content_U, factors_U = sp.factor_list(resultant_U.as_expr())
    signature_U = sorted(
        (int(sp.degree(factor, U)), int(exponent))
        for factor, exponent in factors_U
    )
    assert signature_U == [
        (1, 4),
        (1, 10),
        (1, 48),
        (2, 16),
        (15, 2),
        (68, 1),
        (70, 1),
    ]
    linear_U = {
        str(sp.solve(sp.Poly(factor, U).as_expr(), U)[0])
        for factor, _ in factors_U
        if sp.degree(factor, U) == 1
    }
    assert linear_U == {"-2", "-1", "2"}

    gcd_U_minus_2 = monic_gcd_at_U(-2, H_U, L, C)
    gcd_U_minus_1 = monic_gcd_at_U(-1, H_U, L, C)
    gcd_U_plus_2 = monic_gcd_at_U(2, H_U, L, C)
    assert sp.factor(gcd_U_minus_2.as_expr()) == (A - 2) ** 5
    assert sp.factor(7 * gcd_U_minus_1.as_expr()) == 7 * A**2 + 44 * A + 28
    assert sp.factor(gcd_U_plus_2.as_expr()) == (A - 2) ** 6
    radical_U_minus_2 = sp.Poly(
        sp.sqf_part(gcd_U_minus_2.as_expr()), A, domain=QQ
    ).monic()
    radical_U_minus_1 = sp.Poly(
        sp.sqf_part(gcd_U_minus_1.as_expr()), A, domain=QQ
    ).monic()
    radical_U_plus_2 = sp.Poly(
        sp.sqf_part(gcd_U_plus_2.as_expr()), A, domain=QQ
    ).monic()
    assert radical_U_minus_2.as_expr() == A - 2
    assert sp.factor(7 * radical_U_minus_1.as_expr()) == 7 * A**2 + 44 * A + 28
    assert radical_U_plus_2.as_expr() == A - 2
    discriminant_U_minus_1 = sp.discriminant(
        7 * gcd_U_minus_1.as_expr(), A
    )
    assert discriminant_U_minus_1 == 1152
    assert sp.sqrt(discriminant_U_minus_1).is_rational is False

    # Direct lifting at the only rational (U,A) points of the exceptional
    # scheme.  U=-2 forces s=-1 and U=2 forces s=1.
    R1, R0 = factorization_remainders()
    lift_data: dict[str, object] = {}
    for u_value, s_value, label in [(-2, -1, "U=-2"), (2, 1, "U=2")]:
        # A=2 means a=b+1 on the b!=-1 chart.
        r1_b = sp.factor(R1.subs({s: s_value, a: b + 1}))
        r0_b = sp.factor(R0.subs({s: s_value, a: b + 1}))
        common_b = sp.factor(
            sp.gcd(sp.Poly(r1_b, b), sp.Poly(r0_b, b)).as_expr()
        )
        if s_value == -1:
            assert r1_b == r0_b == (b - 1) ** 4
            assert common_b == (b - 1) ** 4
        else:
            assert r1_b == r0_b == (b - 1) ** 3 * (b + 1)
            assert common_b == (b - 1) ** 3 * (b + 1)
        assert R1.subs({s: s_value, a: 2, b: 1}) == 0
        assert R0.subs({s: s_value, a: 2, b: 1}) == 0
        lift_data[label] = {
            "forced_s": str(s_value),
            "A": "2",
            "common_b_polynomial_before_b_plus_1_saturation": str(common_b),
            "valid_A_chart_lift": {"a": "2", "b": "1"},
            "b_signed_square": "b=1=1^2",
            "admissible": False,
            "reason": "s=-1 is not positive" if s_value == -1 else "s=1 is excluded",
        }

    # The b=-1 point at s=1 lies outside A=2a/(b+1), and is retained rather
    # than silently divided away.  It too has the excluded parameter s=1.
    b_minus_r1 = sp.factor(R1.subs({s: 1, b: -1}))
    b_minus_r0 = sp.factor(R0.subs({s: 1, b: -1}))
    b_minus_gcd = sp.factor(
        sp.gcd(sp.Poly(b_minus_r1, a), sp.Poly(b_minus_r0, a)).as_expr()
    )
    assert b_minus_gcd == a

    # Transform L to the q chart and classify every rational q-coordinate of
    # H=Lq=0.  The factorization is complete over QQ.
    L_q = mobius_U_to_q(L, 21)
    resultant_q = sp.Poly(
        sp.resultant(H_q.as_expr(), L_q.as_expr(), A), q, domain=ZZ
    )
    content_q, factors_q = sp.factor_list(resultant_q.as_expr())
    signature_q = sorted(
        (int(sp.degree(factor, q)), int(exponent))
        for factor, exponent in factors_q
    )
    assert signature_q == [
        (1, 4),
        (1, 10),
        (1, 100),
        (2, 16),
        (15, 2),
        (68, 1),
        (70, 1),
    ]
    linear_q = {
        str(sp.solve(sp.Poly(factor, q).as_expr(), q)[0])
        for factor, _ in factors_q
        if sp.degree(factor, q) == 1
    }
    assert linear_q == {"-10/3", "-2", "2"}

    # Exact pseudo-division identity for the final displayed denominator.
    # The pre-reduction V numerator and denominator have the exact constant
    # gcd 32 in the preferred derivation.  Reproduce that normalization before
    # comparing with the saved primitive denominator.
    C_q = mobius_U_to_q(C, 21)
    unreduced_numerator = sp.Poly(A**2, q, A, domain=ZZ) * (2 * L_q - C_q)
    unreduced_denominator = 4 * L_q
    raw_gcd = sp.gcd(unreduced_numerator, unreduced_denominator)
    assert raw_gcd.as_expr() == 32
    raw_denominator = unreduced_denominator.exquo(raw_gcd)
    leading = sp.Poly(H_q.as_expr(), A).LC()
    relation = sp.Poly(
        sp.expand(leading**10 * raw_denominator.as_expr() - 2**24 * D.as_expr()),
        q,
        A,
        domain=ZZ,
    )
    assert as_polynomial_in_A(relation).prem(as_polynomial_in_A(H_q)).is_zero
    leading_poly = sp.Poly(leading, q, domain=ZZ)
    leading_factors = sp.factor_list(leading_poly.as_expr())[1]
    assert len(leading_factors) == 1
    assert sp.degree(leading_factors[0][0], q) == 8
    assert leading_factors[0][1] == 1
    assert all(int(coefficient) > 0 for coefficient in leading_poly.all_coeffs())

    # Exact special fibres of the final denominator chart.
    expected_fibres = {
        sp.Rational(-2): {
            "H": (A - 2) ** 10,
            "gcd": (A - 2) ** 5,
        },
        sp.Rational(-10, 3): {
            "H": -(
                (A**2 - 7 * A - 26)
                * (7 * A**2 + 44 * A + 28) ** 2
                * (A**4 - A**3 + 4 * A**2 - 4 * A + 16)
            ),
            "gcd": 7 * A**2 + 44 * A + 28,
        },
        sp.Rational(2): {
            "H": A**3 * (A - 6) * (A**2 - 12 * A + 4) ** 3,
            "gcd": A**3 * (A**2 - 12 * A + 4) ** 3,
        },
    }
    fibre_payload: dict[str, object] = {}
    for q_value, expected in expected_fibres.items():
        h_value = sp.Poly(H_q.as_expr().subs(q, q_value), A, domain=QQ).monic()
        d_value = sp.Poly(D.as_expr().subs(q, q_value), A, domain=QQ).monic()
        fibre_gcd = sp.gcd(h_value, d_value).monic()
        assert sp.Poly(expected["H"], A, domain=QQ).monic() == h_value
        assert sp.Poly(expected["gcd"], A, domain=QQ).monic() == fibre_gcd
        fibre_payload[str(q_value)] = {
            "H_factorization": str(sp.factor(h_value.as_expr())),
            "gcd_H_denominator": str(sp.factor(fibre_gcd.as_expr())),
        }

    # For an admissible z>0, z!=1, T=(z-1)/(z+1) has 0<T^2<1,
    # hence q=T^2+T^-2>2.  The only rational L-chart values are <=2 and
    # lc_A(H)>0 for q>0.  Therefore the final denominator never vanishes on
    # an admissible rational-square parameter.
    admissible_denominator_theorem = {
        "T": "(z-1)/(z+1)",
        "X": "T^2 lies in (0,1) for z>0, z!=1",
        "q": "X+1/X>2",
        "rational_L_chart_q_values": sorted(linear_q),
        "leading_coefficient_positive_for_q_positive": True,
        "conclusion": (
            "denominator(q,A) is nonzero at every H-point arising from an "
            "admissible rational square parameter"
        ),
    }

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "inputs": {
            "genus4_quotient_checksum": genus4["sha256_without_checksum"],
            "invariant_compact_v_checksum": compact["sha256_without_checksum"],
        },
        "U_exceptional_resultant": {
            "degree": int(resultant_U.degree()),
            "content": str(content_U),
            "sha256_sparse": polynomial_digest(resultant_U),
            "factors": factor_records(factors_U, U),
            "only_rational_U_values": sorted(linear_U),
        },
        "rational_U_fibres": {
            "U=-2": {
                "gcd_H_L_C": str(sp.factor(gcd_U_minus_2.as_expr())),
                "radical_A_support": str(radical_U_minus_2.as_expr()),
                "lift": lift_data["U=-2"],
            },
            "U=-1": {
                "gcd_H_L_C": str(
                    sp.factor(7 * gcd_U_minus_1.as_expr())
                ),
                "radical_A_support": str(
                    sp.factor(7 * radical_U_minus_1.as_expr())
                ),
                "A_discriminant": str(discriminant_U_minus_1),
                "rational_A_points": [],
                "s_equation": "s^2+s+1=0",
                "admissible": False,
            },
            "U=2": {
                "gcd_H_L_C": str(sp.factor(gcd_U_plus_2.as_expr())),
                "radical_A_support": str(radical_U_plus_2.as_expr()),
                "lift": lift_data["U=2"],
            },
        },
        "separate_b_minus_1_chart": {
            "s": "1",
            "gcd_in_a": str(b_minus_gcd),
            "point": {"a": "0", "b": "-1"},
            "admissible": False,
            "reason": "s=1 is excluded",
        },
        "q_chart_resultant": {
            "degree": int(resultant_q.degree()),
            "content": str(content_q),
            "sha256_sparse": polynomial_digest(resultant_q),
            "factors": factor_records(factors_q, q),
            "only_rational_q_values": sorted(linear_q),
        },
        "pseudo_denominator_certificate": {
            "identity_mod_H": "2^24*D = lc_A(H)^10*(4*Lq/32)",
            "pre_reduction_constant_gcd": "32",
            "exact_pseudo_remainder_terms": [],
            "lc_A_H_terms": sparse(leading_poly),
            "lc_A_H_irreducible_degree": 8,
            "lc_A_H_all_coefficients_positive": True,
        },
        "denominator_special_fibres": fibre_payload,
        "q_equals_2_boundary": {
            "equation": "q=X+1/X=2 implies X=1 and T=+/-1",
            "inverse_images": ["z=0", "z=infinity"],
            "admissible": False,
        },
        "admissible_denominator_theorem": admissible_denominator_theorem,
        "geometric_scope": (
            "The irreducible degree-2,15,68,70 U-orbits are exported exactly. "
            "They contain no Q-rational U and hence no Q-rational factor data. "
            "Their individual algebraic lifts are not classified here."
        ),
        "reference_runtime_seconds_python_flint": round(
            time.monotonic() - started, 3
        ),
    }
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("rational H_U=L=C exceptional locus: complete")
    print("rational final-denominator locus: complete")
    print("admissible square-parameter denominator nonvanishing: PROVED")
    print("runtime seconds:", payload["reference_runtime_seconds_python_flint"])
    print("wrote", args.output.relative_to(ROOT))


if __name__ == "__main__":
    main()
