#!/usr/bin/env python3
"""Direct exact descent of V=a^2/b to the H(q,A) quotient.

This avoids inversion in Sage's tower of algebraic function fields.  Put

    V(T,A) = A^2 Q1(T,A)^2 / (Q1(T,A)^2-Q0(T,A)^2).

On the curve F(T,A)=G(T^2,A)=0 it is invariant under the dihedral generators
T -> -T and T -> 1/T.  We certify those statements by exact polynomial
division, then average first over +/-T and then over X=T^2 -> 1/X.  The final
palindromic numerator and denominator are rewritten exactly in
q=X+1/X using the recurrence S_k=q*S_{k-1}-S_{k-2}.

The exported rational function is intentionally not reduced modulo H and need
not be lowest terms.  It is nevertheless a direct, checkable expression in
Q(q,A), with no normalization or opaque function-field inversion.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
INPUT = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_name("e_model_dihedral_V.json")


def load_poly(data, key: str, variables: tuple[sp.Symbol, ...]) -> sp.Poly:
    return sp.Poly.from_dict(
        {
            tuple(term["powers"]): sp.Integer(term["coefficient"])
            for term in data[key]
        },
        gens=variables,
    )


def negate_first(poly: sp.Poly) -> sp.Poly:
    return sp.Poly.from_dict(
        {
            (first, second): (-1) ** first * coefficient
            for (first, second), coefficient in poly.terms()
        },
        gens=poly.gens,
    )


def reciprocal(poly: sp.Poly, degree: int) -> sp.Poly:
    return sp.Poly.from_dict(
        {
            (degree - first, second): coefficient
            for (first, second), coefficient in poly.terms()
        },
        gens=poly.gens,
    )


def even_T_to_X(poly: sp.Poly, X: sp.Symbol, A: sp.Symbol) -> sp.Poly:
    assert all(first % 2 == 0 for (first, _), _ in poly.terms())
    return sp.Poly.from_dict(
        {
            (first // 2, second): coefficient
            for (first, second), coefficient in poly.terms()
        },
        gens=(X, A),
    )


def chebyshev_trace_coefficients(max_degree: int) -> list[dict[int, int]]:
    """Coefficients of S_k(q)=X^k+X^-k, S_0=2."""

    traces: list[dict[int, int]] = [{0: 2}, {1: 1}]
    for _ in range(2, max_degree + 1):
        current: defaultdict[int, int] = defaultdict(int)
        for degree, coefficient in traces[-1].items():
            current[degree + 1] += coefficient
        for degree, coefficient in traces[-2].items():
            current[degree] -= coefficient
        traces.append({degree: value for degree, value in current.items() if value})
    return traces[: max_degree + 1]


def palindromic_to_q(poly: sp.Poly) -> dict[tuple[int, int], int]:
    X, _A = poly.gens
    total_degree = poly.degree(X)
    assert total_degree % 2 == 0
    half = total_degree // 2
    terms = {(i, j): int(c) for (i, j), c in poly.terms()}
    assert all(terms.get((i, j), 0) == terms.get((total_degree - i, j), 0)
               for i in range(total_degree + 1)
               for j in range(poly.degree(_A) + 1))
    traces = chebyshev_trace_coefficients(half)
    answer: defaultdict[tuple[int, int], int] = defaultdict(int)
    # Central coefficient is not multiplied by S_0=2.
    for (i, a_degree), coefficient in terms.items():
        if i == half:
            answer[(0, a_degree)] += coefficient
    for k in range(1, half + 1):
        for a_degree in range(poly.degree(_A) + 1):
            coefficient = terms.get((half + k, a_degree), 0)
            if not coefficient:
                continue
            for q_degree, trace_coefficient in traces[k].items():
                answer[(q_degree, a_degree)] += coefficient * trace_coefficient
    return {powers: value for powers, value in answer.items() if value}


def verify_laurent_expansion(
    palindromic: sp.Poly,
    in_q: dict[tuple[int, int], int],
) -> None:
    """Check X^-d P(X)=F(X+X^-1) coefficient by coefficient."""

    X, A = palindromic.gens
    half = palindromic.degree(X) // 2
    expected: defaultdict[tuple[int, int], int] = defaultdict(int)
    for (x_degree, a_degree), coefficient in palindromic.terms():
        expected[(x_degree - half, a_degree)] += int(coefficient)

    expanded: defaultdict[tuple[int, int], int] = defaultdict(int)
    for (q_degree, a_degree), coefficient in in_q.items():
        # (X+X^-1)^q_degree.
        for choose_inverse in range(q_degree + 1):
            exponent = q_degree - 2 * choose_inverse
            expanded[(exponent, a_degree)] += coefficient * int(
                sp.binomial(q_degree, choose_inverse)
            )
    expected_clean = {powers: value for powers, value in expected.items() if value}
    expanded_clean = {powers: value for powers, value in expanded.items() if value}
    assert expanded_clean == expected_clean


def sparse(terms: dict[tuple[int, int], int]) -> list[dict[str, object]]:
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in sorted(terms.items(), reverse=True)
    ]


def evaluate(terms: dict[tuple[int, int], int], q_value, a_value):
    return sum(
        sp.Integer(coefficient) * q_value**q_degree * a_value**a_degree
        for (q_degree, a_degree), coefficient in terms.items()
    )


def verify() -> dict[str, object]:
    data = json.loads(INPUT.read_text())
    T, A, X = sp.symbols("T A X")
    Q0 = load_poly(data["linear_subresultant"], "Q0_terms", (T, A))
    Q1 = load_poly(data["linear_subresultant"], "Q1_terms", (T, A))
    numerator = sp.Poly(A**2, T, A) * Q1**2
    denominator = Q1**2 - Q0**2
    common_degree = max(numerator.degree(T), denominator.degree(T))
    assert common_degree == 68

    # F(T,A)=G(T^2,A).
    F = sp.Poly.from_dict(
        {
            (2 * term["powers"][0], term["powers"][1]): sp.Integer(term["coefficient"])
            for term in data["genus4_model"]["terms"]
        },
        gens=(T, A),
    )
    assert F.degree(T) == 32

    numerator_minus = negate_first(numerator)
    denominator_minus = negate_first(denominator)
    minus_cross = numerator * denominator_minus - numerator_minus * denominator
    minus_remainder = sp.rem(minus_cross, F, T)
    assert minus_remainder == 0

    numerator_star_T = reciprocal(numerator, common_degree)
    denominator_star_T = reciprocal(denominator, common_degree)
    inverse_cross = numerator * denominator_star_T - numerator_star_T * denominator
    assert inverse_cross == 0

    # Average over T -> -T and cancel the inexpensive polynomial gcd.
    numerator_pm = numerator * denominator_minus + numerator_minus * denominator
    denominator_pm = sp.Poly(2, T, A) * denominator * denominator_minus
    numerator_X = even_T_to_X(numerator_pm, X, A)
    denominator_X = even_T_to_X(denominator_pm, X, A)
    first_gcd = sp.gcd(numerator_X, denominator_X)
    numerator_X = numerator_X.exquo(first_gcd)
    denominator_X = denominator_X.exquo(first_gcd)
    x_degree = max(numerator_X.degree(X), denominator_X.degree(X))
    assert x_degree == 68

    numerator_star_X = reciprocal(numerator_X, x_degree)
    denominator_star_X = reciprocal(denominator_X, x_degree)
    G = sp.Poly.from_dict(
        {
            tuple(term["powers"]): sp.Integer(term["coefficient"])
            for term in data["genus4_model"]["terms"]
        },
        gens=(X, A),
    )
    inverse_X_cross = (
        numerator_X * denominator_star_X
        - numerator_star_X * denominator_X
    )
    assert sp.rem(inverse_X_cross, G, X) == 0
    numerator_pal = numerator_X * denominator_star_X + numerator_star_X * denominator_X
    denominator_pal = sp.Poly(2, X, A) * denominator_X * denominator_star_X
    assert numerator_pal.degree(X) == denominator_pal.degree(X) == 136

    numerator_q = palindromic_to_q(numerator_pal)
    denominator_q = palindromic_to_q(denominator_pal)
    verify_laurent_expansion(numerator_pal, numerator_q)
    verify_laurent_expansion(denominator_pal, denominator_q)

    q_base = sp.Integer(6)
    a_base = sp.Rational(6, 7)
    numerator_at_base = evaluate(numerator_q, q_base, a_base)
    denominator_at_base = evaluate(denominator_q, q_base, a_base)
    assert denominator_at_base != 0
    value_at_base = sp.factor(numerator_at_base / denominator_at_base)

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "artifact_checksum": data["sha256_without_checksum"],
        "formula": "V(q,A)=numerator(q,A)/denominator(q,A) on H(q,A)=0",
        "variables": ["q", "A"],
        "numerator": sparse(numerator_q),
        "denominator": sparse(denominator_q),
        "degrees": {
            "numerator_q": max(power[0] for power in numerator_q),
            "numerator_A": max(power[1] for power in numerator_q),
            "denominator_q": max(power[0] for power in denominator_q),
            "denominator_A": max(power[1] for power in denominator_q),
            "numerator_terms": len(numerator_q),
            "denominator_terms": len(denominator_q),
        },
        "certificates": {
            "T_to_minus_T": (
                "numerator(T)*denominator(-T)-numerator(-T)*denominator(T) "
                "has exact remainder 0 modulo F(T,A)=G(T^2,A)"
            ),
            "T_to_inverse_T": (
                "after multiplying by T^68, the reciprocal cross-product is identically 0"
            ),
            "X_to_inverse_X_after_first_average": (
                "the reciprocal cross-product has exact remainder 0 modulo G(X,A)"
            ),
            "palindromic_rewrite": (
                "both Laurent expansions after q=X+X^-1 agree coefficient-by-coefficient"
            ),
            "first_average_gcd": str(first_gcd.as_expr()),
        },
        "base_point": {
            "q": "6",
            "A": "6/7",
            "V": str(value_at_base),
        },
        "logical_scope": (
            "This gives V as an exact rational function on the normalization of H. "
            "It does not identify that normalization with either 544.c model."
        ),
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(encoded).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("dihedral invariance modulo G(T^2,A): OK")
    print("palindromic rewrite through q=X+1/X: OK")
    print("degrees/terms:", payload["degrees"])
    print("V(6,6/7)=", payload["base_point"]["V"])
    try:
        displayed_output = args.output.relative_to(ROOT)
    except ValueError:
        displayed_output = args.output
    print("wrote", displayed_output)


if __name__ == "__main__":
    main()
