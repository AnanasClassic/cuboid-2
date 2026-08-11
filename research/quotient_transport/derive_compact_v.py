#!/usr/bin/env python3
"""Reduce the exact descended function ``V=a^2/b`` modulo ``H(q,A)``.

The upstream dihedral descent exports a correct but large quotient ``N/D``.
This script performs two exact reductions:

1. cancel the ordinary common factor of ``N`` and ``D`` in ``ZZ[q,A]``;
2. regard both polynomials as elements of ``ZZ[q][A]`` and take their
   pseudo-remainders modulo the degree-ten equation ``H(q,A)``.

Both reduced source polynomials have A-degree 32, so pseudo-division uses the
same multiplier ``lc_A(H)^23``.  After cancelling the common content of the
two pseudo-remainders, this gives a representative with A-degree at most 9.
The script additionally forms the cross-product with the upstream quotient
and certifies that its pseudo-remainder modulo H is exactly zero.

The computation is substantially faster with python-flint, SymPy's default
ground-type backend when python-flint is installed.  It uses exact integers
throughout; no numerical reconstruction or randomized step occurs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from collections import defaultdict
from pathlib import Path

import sympy as sp
from sympy.polys.domains import ZZ


ROOT = Path(__file__).resolve().parents[2]
GENUS4 = ROOT / "artifacts" / "genus4_quotient.json"
SOURCE_V = (
    ROOT / "research" / "arithmetic_geometry" / "e_model_dihedral_V.json"
)
DEFAULT_OUTPUT = Path(__file__).with_name("compact_v.json")


q, A = sp.symbols("q A")
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


def evaluate(poly: sp.Poly, q_value: sp.Rational, a_value: sp.Rational):
    return poly.eval({q: q_value, A: a_value})


def degree_record(poly: sp.Poly) -> dict[str, int]:
    return {
        "q": int(poly.degree(q)),
        "A": int(poly.degree(A)),
        "terms": len(poly.terms()),
    }


def verify() -> dict[str, object]:
    started = time.monotonic()
    timings: dict[str, float] = {}

    genus4 = json.loads(GENUS4.read_text(encoding="utf-8"))
    source = json.loads(SOURCE_V.read_text(encoding="utf-8"))
    H = sparse_to_bivariate(genus4["elliptic_plane_model"]["terms"])
    source_numerator = sparse_to_bivariate(source["numerator"])
    source_denominator = sparse_to_bivariate(source["denominator"])

    stage = time.monotonic()
    source_gcd = sp.gcd(source_numerator, source_denominator)
    numerator = source_numerator.exquo(source_gcd)
    denominator = source_denominator.exquo(source_gcd)
    timings["source_gcd"] = time.monotonic() - stage
    assert degree_record(source_gcd) == {"q": 34, "A": 32, "terms": 1155}
    assert degree_record(numerator) == {"q": 34, "A": 32, "terms": 1153}
    assert degree_record(denominator) == {"q": 34, "A": 32, "terms": 1155}

    H_in_A = as_polynomial_in_A(H)
    numerator_in_A = as_polynomial_in_A(numerator)
    denominator_in_A = as_polynomial_in_A(denominator)
    assert H_in_A.degree() == 10
    assert numerator_in_A.degree() == denominator_in_A.degree() == 32
    pseudo_exponent = 32 - 10 + 1
    assert pseudo_exponent == 23

    stage = time.monotonic()
    raw_numerator = flatten_A(numerator_in_A.prem(H_in_A))
    raw_denominator = flatten_A(denominator_in_A.prem(H_in_A))
    timings["two_pseudo_remainders"] = time.monotonic() - stage
    assert raw_numerator.degree(A) <= 9
    assert raw_denominator.degree(A) <= 9

    numerator_content, numerator_primitive = raw_numerator.primitive()
    denominator_content, denominator_primitive = raw_denominator.primitive()
    assert int(numerator_content) == 2**59
    assert int(denominator_content) == 2**56
    content_ratio = sp.Rational(numerator_content, denominator_content)
    assert content_ratio == 8

    stage = time.monotonic()
    common_pseudo_factor = sp.gcd(numerator_primitive, denominator_primitive)
    compact_numerator = numerator_primitive.exquo(common_pseudo_factor).mul_ground(8)
    compact_denominator = denominator_primitive.exquo(common_pseudo_factor)
    timings["pseudo_remainder_gcd"] = time.monotonic() - stage
    assert common_pseudo_factor.degree(q) == 9
    assert common_pseudo_factor.degree(A) == 0
    assert degree_record(compact_numerator) == {
        "q": 206,
        "A": 9,
        "terms": 2070,
    }
    assert degree_record(compact_denominator) == {
        "q": 207,
        "A": 9,
        "terms": 2080,
    }
    assert sp.gcd(compact_numerator, compact_denominator).is_one

    # This is an independent exact cross-multiplication check.  It does not
    # merely trust the semantics of the two preceding prem calls.
    stage = time.monotonic()
    cross_product = (
        numerator * compact_denominator - denominator * compact_numerator
    )
    cross_remainder = as_polynomial_in_A(cross_product).prem(H_in_A)
    timings["cross_product_remainder"] = time.monotonic() - stage
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

    leading_coefficient = sp.Poly(H, A).LC()
    assert leading_coefficient != 0
    leading_at_base = leading_coefficient.subs(q, q_base)
    assert leading_at_base != 0

    timings["total"] = time.monotonic() - started
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
            "source_common_gcd": {
                "degrees": degree_record(source_gcd),
                "sha256_sparse": polynomial_digest(source_gcd),
            },
            "pseudo_division": {
                "coefficient_ring": "ZZ[q]",
                "main_variable": "A",
                "modulus": "H(q,A)",
                "source_A_degree": 32,
                "modulus_A_degree": 10,
                "common_multiplier": "lc_A(H)^23",
                "leading_coefficient_terms": sparse(
                    sp.Poly(leading_coefficient, q, A, domain=ZZ)
                ),
                "leading_coefficient_at_q_6": str(leading_at_base),
            },
            "primitive_contents": {
                "numerator": str(numerator_content),
                "denominator": str(denominator_content),
                "ratio": str(content_ratio),
            },
            "common_pseudo_factor": {
                "degrees": degree_record(common_pseudo_factor),
                "terms": sparse(common_pseudo_factor),
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
        "base_point": {
            "q": "6",
            "A": "6/7",
            "denominator_nonzero": True,
            "V": str(value_at_base),
        },
        "timings_seconds": {
            name: round(value, 6) for name, value in timings.items()
        },
        "logical_scope": (
            "This certifies an exact compact representative of V in the "
            "function field of H. It does not identify the normalization of "
            "H with elliptic-curve class 544.c."
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
    print("source common-factor cancellation: OK")
    print("A-degree-nine pseudo-remainder representative: OK")
    print("exact cross-multiplication remainder modulo H: 0")
    print("degrees:", payload["degrees"])
    print("V(6,6/7) =", payload["base_point"]["V"])
    print("runtime seconds:", payload["timings_seconds"]["total"])
    print("wrote", args.output.relative_to(ROOT))


if __name__ == "__main__":
    main()
