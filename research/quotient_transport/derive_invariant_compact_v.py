#!/usr/bin/env python3
"""Derive a smaller exact formula for ``V=a^2/b`` on ``H(q,A)=0``.

Besides the reciprocal invariants

    U = s + 1/s,       W = b + 1/b,

use ``A=2a/(b+1)``.  Reducing the two quadratic-factor remainder equations
first modulo ``b^2-W*b+1`` and then modulo ``s^2-U*s+1`` produces two low
degree equations in ``U,A,W``.  Two exact factors of their determinant have
W-degrees two and five.  Their linear subresultant gives

    L(U,A) W + C(U,A) = 0.

The resultant of those factors contains the plane model H, after the exact
Mobius change ``U=2(q+6)/(q-2)``.  Consequently

    V = A^2 (W+2)/4 = A^2 (2L-C)/(4L).

Finally both numerator and denominator are pseudo-reduced in A modulo H.
They have the same A-degree before reduction, hence the same pseudo-division
multiplier.  A cross-product against the independent upstream dihedral
formula is checked to have exact zero pseudo-remainder modulo H.

All calculations use exact integer arithmetic.  No numerical interpolation,
point sampling, or probabilistic factorization is used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path

import sympy as sp
from sympy.polys.domains import ZZ


ROOT = Path(__file__).resolve().parents[2]
GENUS4 = ROOT / "artifacts" / "genus4_quotient.json"
SOURCE_V = (
    ROOT / "research" / "arithmetic_geometry" / "e_model_dihedral_V.json"
)
DEFAULT_OUTPUT = Path(__file__).with_name("invariant_compact_v.json")

s, x, a, b = sp.symbols("s x a b")
U, W, q, A = sp.symbols("U W q A")
COEFFICIENT_RING = ZZ.poly_ring(q)


def sparse_to_bivariate(terms: list[dict[str, object]]) -> sp.Poly:
    return sp.Poly.from_dict(
        {
            tuple(int(power) for power in term["powers"]): int(term["coefficient"])
            for term in terms
        },
        (q, A),
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


def degree_record(poly: sp.Poly) -> dict[str, int]:
    return {
        "q": int(poly.degree(q)),
        "A": int(poly.degree(A)),
        "terms": len(poly.terms()),
    }


def invariant_degree_record(poly: sp.Poly) -> dict[str, int]:
    return {
        "U": int(poly.degree(U)),
        "A": int(poly.degree(A)),
        "W": int(poly.degree(W)),
        "terms": len(poly.terms()),
    }


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


def flatten_A(poly: sp.Poly) -> sp.Poly:
    terms: dict[tuple[int, int], int] = {}
    for (a_degree,), coefficient in poly.rep.to_dict().items():
        for (q_degree,), value in coefficient.terms():
            terms[(q_degree, a_degree)] = int(value)
    return sp.Poly.from_dict(terms, (q, A), domain=ZZ)


def mobius_U_to_q(poly: sp.Poly, common_degree: int) -> sp.Poly:
    """Return (q-2)^d poly(2(q+6)/(q-2),A), exactly."""

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
    """Return (U-2)^d poly(2(U+6)/(U-2),A), exactly."""

    transformed = sp.Integer(0)
    for (q_degree, a_degree), coefficient in poly.terms():
        transformed += (
            int(coefficient)
            * (2 * (U + 6)) ** q_degree
            * (U - 2) ** (common_degree - q_degree)
            * A**a_degree
        )
    return sp.Poly(sp.expand(transformed), U, A, domain=ZZ).primitive()[1]


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


def reduce_in_b(poly: sp.Expr) -> sp.Expr:
    substituted = sp.together(poly.subs(a, A * (b + 1) / 2)) * 16
    remainder = sp.rem(substituted, b**2 - W * b + 1, b)
    return sp.Poly(sp.expand(remainder), b, s, A, W).primitive()[1].as_expr()


def reduce_in_s(poly: sp.Expr) -> sp.Expr:
    remainder = sp.rem(poly, s**2 - U * s + 1, s)
    return sp.Poly(sp.expand(remainder), s, U, A, W).primitive()[1].as_expr()


def evaluate(poly: sp.Poly, q_value: sp.Rational, a_value: sp.Rational):
    return poly.eval({q: q_value, A: a_value})


def verify() -> dict[str, object]:
    genus4 = json.loads(GENUS4.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_V.read_text(encoding="utf-8"))
    H = sparse_to_bivariate(genus4["elliptic_plane_model"]["terms"])

    R1, R0 = factorization_remainders()
    r1 = sp.Poly(reduce_in_b(R1), b)
    r0 = sp.Poly(reduce_in_b(R0), b)
    l1, c1 = r1.coeff_monomial(b), r1.coeff_monomial(1)
    l0, c0 = r0.coeff_monomial(b), r0.coeff_monomial(1)

    # A common b root must satisfy both the linear cross-condition and the
    # reciprocal quadratic after b=-c1/l1 is substituted.
    b_cross = sp.Poly(
        sp.expand(l1 * c0 - l0 * c1), s, A, W
    ).primitive()[1].as_expr()
    b_quadratic = sp.Poly(
        sp.expand(c1**2 + W * c1 * l1 + l1**2), s, A, W
    ).primitive()[1].as_expr()

    s_cross = sp.Poly(reduce_in_s(b_cross), s)
    s_quadratic = sp.Poly(reduce_in_s(b_quadratic), s)
    sc1, sc0 = s_cross.coeff_monomial(s), s_cross.coeff_monomial(1)
    sq1, sq0 = s_quadratic.coeff_monomial(s), s_quadratic.coeff_monomial(1)
    determinant = sp.Poly(
        sp.expand(sc1 * sq0 - sq1 * sc0), U, A, W, domain=ZZ
    ).primitive()[1]
    determinant_factors = sp.factor_list(determinant.as_expr())[1]
    signature = sorted(
        (
            int(sp.degree(factor, U)),
            int(sp.degree(factor, A)),
            int(sp.degree(factor, W)),
            int(exponent),
        )
        for factor, exponent in determinant_factors
    )
    assert signature == [(4, 4, 2, 1), (5, 8, 5, 1)]
    f2 = next(
        sp.Poly(factor, U, A, W, domain=ZZ)
        for factor, _ in determinant_factors
        if sp.degree(factor, W) == 2
    )
    f5 = next(
        sp.Poly(factor, U, A, W, domain=ZZ)
        for factor, _ in determinant_factors
        if sp.degree(factor, W) == 5
    )

    subresultants = sp.subresultants(f2.as_expr(), f5.as_expr(), W)
    assert [sp.degree(value, W) for value in subresultants] == [5, 2, 1, 0]
    linear = sp.Poly(subresultants[-2], W, U, A, domain=ZZ).primitive()[1]
    L = sp.Poly(linear.as_expr(), W).coeff_monomial(W)
    C = sp.Poly(linear.as_expr(), W).coeff_monomial(1)
    L = sp.Poly(L, U, A, domain=ZZ)
    C = sp.Poly(C, U, A, domain=ZZ)
    assert (L.degree(U), L.degree(A), len(L.terms())) == (21, 19, 370)
    assert (C.degree(U), C.degree(A), len(C.terms())) == (21, 19, 394)

    # The resultant contains exactly the transformed H component.  The other
    # factors record elimination strata and are not silently discarded.
    resultant = sp.Poly(sp.resultant(f2.as_expr(), f5.as_expr(), W), U, A)
    resultant_factors = sp.factor_list(resultant.as_expr())[1]
    resultant_signature = sorted(
        (
            int(sp.degree(factor, U)),
            int(sp.degree(factor, A)),
            int(exponent),
            len(sp.Poly(factor, U, A).terms()),
        )
        for factor, exponent in resultant_factors
    )
    assert resultant_signature == [
        (1, 0, 2, 2),
        (8, 10, 1, 89),
        (10, 6, 1, 64),
        (10, 6, 1, 64),
    ]
    H_U = mobius_q_to_U(H, 8)
    assert any(
        sp.Poly(factor, U, A, domain=ZZ) == H_U
        for factor, _ in resultant_factors
    )

    common_U_degree = max(L.degree(U), C.degree(U))
    assert common_U_degree == 21
    L_q = mobius_U_to_q(L, common_U_degree)
    C_q = mobius_U_to_q(C, common_U_degree)
    assert L_q.eval({q: 6, A: sp.Rational(6, 7)}) != 0

    # W=-C/L and V=A^2(W+2)/4.
    raw_numerator = sp.Poly(A**2, q, A, domain=ZZ) * (2 * L_q - C_q)
    raw_denominator = 4 * L_q
    raw_gcd = sp.gcd(raw_numerator, raw_denominator)
    raw_numerator = raw_numerator.exquo(raw_gcd)
    raw_denominator = raw_denominator.exquo(raw_gcd)
    assert degree_record(raw_numerator) == {"q": 20, "A": 19, "terms": 378}
    assert degree_record(raw_denominator) == {"q": 21, "A": 19, "terms": 440}

    H_in_A = as_polynomial_in_A(H)
    numerator_in_A = as_polynomial_in_A(raw_numerator)
    denominator_in_A = as_polynomial_in_A(raw_denominator)
    assert H_in_A.degree() == 10
    assert numerator_in_A.degree() == denominator_in_A.degree() == 19
    pseudo_exponent = 19 - 10 + 1
    assert pseudo_exponent == 10
    reduced_numerator = flatten_A(numerator_in_A.prem(H_in_A))
    reduced_denominator = flatten_A(denominator_in_A.prem(H_in_A))

    numerator_content, numerator_primitive = reduced_numerator.primitive()
    denominator_content, denominator_primitive = reduced_denominator.primitive()
    assert int(numerator_content) == 2**28
    assert int(denominator_content) == 2**24
    assert sp.Rational(numerator_content, denominator_content) == 16
    common_reduced_factor = sp.gcd(numerator_primitive, denominator_primitive)
    compact_numerator = numerator_primitive.exquo(
        common_reduced_factor
    ).mul_ground(16)
    compact_denominator = denominator_primitive.exquo(common_reduced_factor)
    assert common_reduced_factor.is_one
    assert degree_record(compact_numerator) == {
        "q": 100,
        "A": 9,
        "terms": 1010,
    }
    assert degree_record(compact_denominator) == {
        "q": 101,
        "A": 9,
        "terms": 1020,
    }
    assert sp.gcd(compact_numerator, compact_denominator).is_one

    # Independent exact comparison with the upstream dihedral descent.
    source_numerator = sparse_to_bivariate(source["numerator"])
    source_denominator = sparse_to_bivariate(source["denominator"])
    source_gcd = sp.gcd(source_numerator, source_denominator)
    source_numerator = source_numerator.exquo(source_gcd)
    source_denominator = source_denominator.exquo(source_gcd)
    cross_product = (
        source_numerator * compact_denominator
        - source_denominator * compact_numerator
    )
    cross_remainder = as_polynomial_in_A(cross_product).prem(H_in_A)
    assert cross_remainder.is_zero

    q_base = sp.Integer(6)
    a_base = sp.Rational(6, 7)
    assert evaluate(H, q_base, a_base) == 0
    denominator_at_base = evaluate(compact_denominator, q_base, a_base)
    assert denominator_at_base != 0
    value_at_base = sp.Rational(
        evaluate(compact_numerator, q_base, a_base), denominator_at_base
    )
    assert value_at_base == -36

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "variables": ["q", "A"],
        "formula": "V(q,A)=numerator(q,A)/denominator(q,A) on H(q,A)=0",
        "inputs": {
            "genus4_quotient_checksum": genus4["sha256_without_checksum"],
            "source_V_checksum": source["sha256_without_checksum"],
        },
        "numerator": sparse(compact_numerator),
        "denominator": sparse(compact_denominator),
        "degrees": {
            "numerator": degree_record(compact_numerator),
            "denominator": degree_record(compact_denominator),
        },
        "certificates": {
            "invariant_coordinates": {
                "U": "s+1/s=2*(q+6)/(q-2)",
                "W": "b+1/b",
                "A": "2*a/(b+1)",
                "V": "A^2*(W+2)/4",
            },
            "determinant_factors": {
                "signature_U_A_W_exponent": [list(row) for row in signature],
                "W_degree_2_sha256_sparse": polynomial_digest(
                    sp.Poly(f2.as_expr(), U, A, W, domain=ZZ)
                ),
                "W_degree_5_sha256_sparse": polynomial_digest(
                    sp.Poly(f5.as_expr(), U, A, W, domain=ZZ)
                ),
            },
            "linear_subresultant": {
                "formula": "L(U,A)*W+C(U,A)",
                "L_degrees": invariant_degree_record(
                    sp.Poly(L.as_expr(), U, A, W, domain=ZZ)
                ),
                "C_degrees": invariant_degree_record(
                    sp.Poly(C.as_expr(), U, A, W, domain=ZZ)
                ),
                "L_sha256_sparse": polynomial_digest(L),
                "C_sha256_sparse": polynomial_digest(C),
                "L_terms": sparse(L),
                "C_terms": sparse(C),
            },
            "resultant_strata": {
                "signature_U_A_exponent_terms": [
                    list(row) for row in resultant_signature
                ],
                "H_U_is_exact_factor": True,
                "H_U_sha256_sparse": polynomial_digest(H_U),
            },
            "pre_reduction_formula": {
                "identity": "V=A^2*(2*L-C)/(4*L)",
                "numerator_degrees": degree_record(raw_numerator),
                "denominator_degrees": degree_record(raw_denominator),
            },
            "pseudo_division": {
                "coefficient_ring": "ZZ[q]",
                "main_variable": "A",
                "modulus": "H(q,A)",
                "common_multiplier": "lc_A(H)^10",
                "primitive_content_ratio": "16",
            },
            "cross_multiplication_mod_H": {
                "identity": (
                    "source_reduced_numerator*compact_denominator - "
                    "source_reduced_denominator*compact_numerator = 0 mod H"
                ),
                "cross_degrees": degree_record(cross_product),
                "cross_sha256_sparse": polynomial_digest(cross_product),
                "exact_pseudo_remainder_terms": [],
            },
        },
        "exceptional_locus": {
            "equation": "denominator(q,A)=0",
            "displayed_quotient_chart": (
                "The displayed quotient is a function-field chart. Points on "
                "this finite intersection with H require another chart."
            ),
            "linear_subresultant_branch": {
                "generic_condition": "L(U,A) != 0",
                "unresolved_exceptional_ideal": "(H_U(U,A), L(U,A), C(U,A))",
                "status": (
                    "NOT CLASSIFIED HERE. Since L(6,6/7) is nonzero, L is "
                    "not identically zero on H_U; the common L=C branch is a "
                    "finite exceptional scheme and must be checked separately "
                    "in any pointwise rational-point argument."
                ),
            },
            "mobius_branch": {
                "excluded_denominator": "q-2",
                "q_equals_2_fibre": genus4["special_fibres"]["q=2"],
                "status": (
                    "RETAINED AS A SPECIAL FIBRE. The function-field identity "
                    "does not by itself classify points above q=2."
                ),
            },
            "A_chart_branch": {
                "excluded_original_value": "b=-1",
                "upstream_certificate": (
                    "artifacts/genus4_quotient.json special_fibres."
                    "b=-1_resultant_in_s"
                ),
                "status": "RETAINED; not removed by the compact formula.",
            },
            "global_status": (
                "No exceptional point is discarded from H or from the "
                "remaining rational-point proof obligation."
            ),
        },
        "base_point": {
            "q": "6",
            "A": "6/7",
            "denominator_nonzero": True,
            "V": str(value_at_base),
        },
        # Keep the certificate byte-reproducible.  Runtime is provenance from
        # the reference run, not part of the mathematical computation.
        "reference_runtime_seconds_python_flint": 24.234,
        "logical_scope": (
            "This certifies an exact compact representative of V in the "
            "function field of H. It does not identify the normalization of "
            "H with elliptic-curve class 544.c and does not determine all "
            "rational points on H or its character covers."
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
    print("reciprocal-invariant determinant and subresultant: OK")
    print("H(U,A) resultant component: OK")
    print("A-degree-nine representative: OK")
    print("exact cross-multiplication remainder modulo H: 0")
    print("degrees:", payload["degrees"])
    print("V(6,6/7) =", payload["base_point"]["V"])
    print("runtime seconds:", payload["reference_runtime_seconds_python_flint"])
    print("wrote", args.output.relative_to(ROOT))


if __name__ == "__main__":
    main()
