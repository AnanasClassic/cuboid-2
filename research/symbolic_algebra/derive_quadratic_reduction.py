#!/usr/bin/env python3
"""Exact derivation of the quadratic-factor obstruction.

This script deliberately starts from the normalized quintic and performs the
polynomial division, linear elimination, resultant calculation, and all
degenerate-fibre checks in exact SymPy arithmetic.  It can also export every
polynomial as a coefficient dictionary for independent consumers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


s, a, b, x = sp.symbols("s a b x")
p, q, t = sp.symbols("p q t", nonzero=True)

c4 = (2 + s) * (3 - 2 * s)
c3 = 1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4
c2 = -s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4)
c1 = -s**3 * (1 + 2 * s) * (-2 + 3 * s)
c0 = -s**5

P = x**5 + c4 * x**4 + c3 * x**3 + c2 * x**2 + c1 * x + c0
D = x**2 + a * x + b
remainder = sp.rem(P, D, x)
R1 = sp.Poly(remainder, x).coeff_monomial(x)
R0 = sp.Poly(remainder, x).coeff_monomial(1)

# The b^2 coefficients are 1 in R1 and c4-2a in R0.
E = sp.expand(R0 - (c4 - 2 * a) * R1)
L = sp.Poly(E, b).coeff_monomial(b)
C = sp.Poly(E, b).coeff_monomial(1)
U1 = sp.Poly(R1, b).coeff_monomial(b)
U0 = sp.Poly(R1, b).coeff_monomial(1)

# On L != 0, b=-C/L.  Clearing precisely L^2 from R1 gives F.
F = sp.expand(C**2 - U1 * C * L + U0 * L**2)

H = (
    32768 * s**21
    - 1573888 * s**20
    + 17845256 * s**19
    - 25552432 * s**18
    - 164061982 * s**17
    + 516056006 * s**16
    + 96206522 * s**15
    - 2381234573 * s**14
    + 3001419440 * s**13
    + 2266872188 * s**12
    - 8848608460 * s**11
    + 6526416706 * s**10
    + 3706299882 * s**9
    - 9219354518 * s**8
    + 5021608234 * s**7
    + 1048464803 * s**6
    - 2603612444 * s**5
    + 1276740780 * s**4
    - 231674112 * s**3
    - 7745280 * s**2
    + 5345280 * s
    + 110592
)


def coefficient_records(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    """Canonical descending coefficient records for a multivariate polynomial."""
    records: list[dict[str, object]] = []
    for exponents, coefficient in sp.Poly(poly, *variables).terms():
        records.append({"exponents": list(exponents), "coefficient": int(coefficient)})
    return records


def exact_checks() -> dict[str, object]:
    original_q = (
        t**10
        + (2 * q**2 + p**2) * (3 * q**2 - 2 * p**2) * t**8
        + (q**8 + 10 * p**2 * q**6 + 4 * p**4 * q**4 - 14 * p**6 * q**2 + p**8) * t**6
        - p**2
        * q**2
        * (q**8 - 14 * p**2 * q**6 + 4 * p**4 * q**4 + 10 * p**6 * q**2 + p**8)
        * t**4
        - p**6 * q**6 * (q**2 + 2 * p**2) * (-2 * q**2 + 3 * p**2) * t**2
        - p**10 * q**10
    )
    normalized_q = q**20 * P.subs({s: p**2 / q**2, x: t**2 / q**4})
    assert sp.cancel(original_q - normalized_q) == 0

    # Exact reciprocal identity induced by p <-> q.
    assert sp.cancel(P + s**5 * x**5 * P.subs({s: 1 / s, x: 1 / x}, simultaneous=True)) == 0

    assert sp.Poly(R1, b).degree() == 2
    assert sp.Poly(R0, b).degree() == 2
    assert sp.Poly(E, b).degree() == 1
    assert sp.expand(E - (L * b + C)) == 0
    assert sp.expand(R1 - (b**2 + U1 * b + U0)) == 0

    resultant = sp.factor(sp.resultant(C, L, a))
    expected_resultant = 64 * (s - 1) ** 3 * (s + 1) ** 3 * H
    assert sp.expand(resultant - expected_resultant) == 0

    # H has no rational root.  Its leading coefficient is nonzero modulo 13,
    # and its affine values modulo 13 are all nonzero.  The leading-coefficient
    # check also handles a rational root whose denominator is divisible by 13.
    h_poly = sp.Poly(H, s)
    values_mod_13 = [int(h_poly.eval(i) % 13) for i in range(13)]
    assert int(h_poly.LC() % 13) != 0
    assert all(values_mod_13)

    gcd_at_one = sp.monic(sp.gcd(sp.Poly(L.subs(s, 1), a), sp.Poly(C.subs(s, 1), a))).as_expr()
    gcd_at_minus_one = sp.monic(
        sp.gcd(sp.Poly(L.subs(s, -1), a), sp.Poly(C.subs(s, -1), a))
    ).as_expr()
    assert sp.expand(gcd_at_one - (a - 2)) == 0
    assert sp.expand(gcd_at_minus_one - (a - 2) ** 3) == 0
    assert sp.factor(R1.subs({s: 1, a: 2})) == (b - 1) ** 2
    assert sp.factor(R1.subs({s: -1, a: 2})) == (b - 1) ** 2

    # Direct algebraic reverse implication, represented as polynomial identities:
    # if L != 0, F=0 and b=-C/L, then R1=R0=0.
    reconstructed_r1 = sp.factor(R1.subs(b, -C / L))
    reconstructed_e = sp.factor(E.subs(b, -C / L))
    assert sp.factor(reconstructed_r1 - F / L**2) == 0
    assert reconstructed_e == 0

    payload: dict[str, object] = {
        "schema": 1,
        "variables": {
            "P": ["s", "x"],
            "R1_R0_L_C_U1_U0_F": ["s", "a", "b"],
            "H": ["s"],
        },
        "polynomials": {
            "P": coefficient_records(P, (s, x)),
            "R1": coefficient_records(R1, (s, a, b)),
            "R0": coefficient_records(R0, (s, a, b)),
            "L": coefficient_records(L, (s, a)),
            "C": coefficient_records(C, (s, a)),
            "U1": coefficient_records(U1, (s, a)),
            "U0": coefficient_records(U0, (s, a)),
            "F": coefficient_records(F, (s, a)),
            "H": coefficient_records(H, (s,)),
        },
        "degrees": {
            "F_in_s": int(sp.degree(F, s)),
            "F_in_a": int(sp.degree(F, a)),
            "F_total": int(sp.Poly(F, s, a).total_degree()),
            "F_terms": len(sp.Poly(F, s, a).terms()),
        },
        "resultant_identity": "Res_a(C,L)=64*(s-1)^3*(s+1)^3*H(s)",
        "normalization_identity": "Q_{p,q}(t)=q^20*P_{(p/q)^2}(t^2/q^4)",
        "reciprocal_identity": "P_s(x)=-s^5*x^5*P_{1/s}(1/x)",
        "H_values_mod_13": values_mod_13,
        "rational_degenerate_s_a_b": [[1, 2, 1], [-1, 2, 1]],
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = exact_checks()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
