#!/usr/bin/env python3
"""Exact symbolic identities for Sharipov's second cuboid polynomial.

The module reconstructs the 2+3 remainder equations from the polynomial,
rather than treating the formulas in arXiv:2601.07899 as input.  Running the
file checks every central identity and can export the canonical polynomials.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp


p, q, t, r, s, x, a, b = sp.symbols("p q t r s x a b")


def Q_pq() -> sp.Expr:
    return sp.expand(
        t**10
        + (2 * q**2 + p**2) * (3 * q**2 - 2 * p**2) * t**8
        + (q**8 + 10 * p**2 * q**6 + 4 * p**4 * q**4 - 14 * p**6 * q**2 + p**8) * t**6
        - p**2 * q**2 * (q**8 - 14 * p**2 * q**6 + 4 * p**4 * q**4 + 10 * p**6 * q**2 + p**8) * t**4
        - p**6 * q**6 * (q**2 + 2 * p**2) * (-2 * q**2 + 3 * p**2) * t**2
        - p**10 * q**10
    )


def P_s() -> sp.Expr:
    return sp.expand(
        x**5
        + (2 + s) * (3 - 2 * s) * x**4
        + (1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4) * x**3
        - s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4) * x**2
        - s**3 * (1 + 2 * s) * (-2 + 3 * s) * x
        - s**5
    )


def remainder_data() -> dict[str, sp.Expr]:
    P = P_s()
    D = x**2 + a * x + b
    remainder = sp.Poly(sp.rem(P, D, x), x)
    R1 = sp.expand(remainder.coeff_monomial(x))
    R0 = sp.expand(remainder.coeff_monomial(1))
    u = sp.expand(R1.coeff(b, 1))
    v = sp.expand(R1.coeff(b, 0))
    m = sp.expand(R0.coeff(b, 2))
    n = sp.expand(R0.coeff(b, 1))
    L = sp.expand(n - m * u)
    C = sp.expand(m * v + s**5)
    F = sp.expand(C**2 + u * L * C + v * L**2)
    return {"R1": R1, "R0": R0, "u": u, "v": v, "m": m, "n": n, "L": L, "C": C, "F": F}


def verify() -> dict[str, object]:
    P = P_s()
    data = remainder_data()

    # Weighted normalization, first with r=p/q and then s=r^2, x=t^2/q^4.
    normalized = sp.expand(Q_pq().subs({p: r * q, t: q**2 * sp.Symbol("u")}) / q**20)
    uvar = sp.Symbol("u")
    expected = sp.expand(P.subs({s: r**2, x: uvar**2}))
    assert sp.expand(normalized - expected) == 0

    assert sp.expand(data["R1"] - (b**2 + data["u"] * b + data["v"])) == 0
    assert sp.expand(data["R0"] - (data["m"] * b**2 + data["n"] * b - s**5)) == 0
    assert sp.expand(
        data["R0"] - (data["L"] * b - data["C"]) - data["m"] * data["R1"]
    ) == 0
    assert sp.expand(sp.resultant(data["R1"], data["R0"], b) - data["F"]) == 0

    # Exact p<->q / reciprocal-polynomial identity.
    reciprocal = P.subs({s: 1 / s, x: 1 / x}, simultaneous=True)
    assert sp.factor(P + s**5 * x**5 * reciprocal) == 0

    assert sp.Poly(data["F"], s, a).degree(s) == 16
    assert sp.Poly(data["F"], s, a).degree(a) == 10
    assert sp.Poly(data["F"], s, a).total_degree() == 17
    assert sp.factor(data["F"].subs(s, 1)) == -a**4 * (a - 2) ** 6

    res_degenerate = sp.factor(sp.resultant(data["L"], data["C"], s))
    factors = sp.factor_list(res_degenerate, a)
    assert any(sp.expand(factor - (a - 2)) == 0 and exponent == 6 for factor, exponent in factors[1])
    other = sp.cancel(res_degenerate / (a - 2) ** 6)
    assert sp.Poly(other, a, domain=sp.QQ).degree() == 21
    assert sp.Poly(other, a, domain=sp.QQ).is_irreducible
    gcd_at_a2 = sp.factor(sp.gcd(sp.Poly(data["L"].subs(a, 2), s), sp.Poly(data["C"].subs(a, 2), s)).as_expr())
    assert sp.expand(gcd_at_a2 / (2 * (s - 1) ** 2 * (s + 1))) == 1

    return {
        "sympy_version": sp.__version__,
        "normalization": "verified",
        "remainder": "verified",
        "resultant_equals_F": "verified",
        "reciprocal_identity": "P_s(x) = -s^5*x^5*P_(1/s)(1/x)",
        "F_degrees": {"s": 16, "a": 10, "total": 17},
        "degenerate_rational_locus": [[-1, 2], [1, 2]],
    }


def export(path: Path) -> None:
    data = remainder_data()
    payload = {
        "schema": 1,
        "variables": ["s", "a", "b"],
        **{name: str(expr) for name, expr in data.items()},
        "verification": verify(),
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--export", type=Path)
    args = parser.parse_args()
    result = verify()
    if args.export:
        export(args.export)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
