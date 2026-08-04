#!/usr/bin/env python3
"""Exact reciprocal quotient and square-condition reduction for the 2+3 case.

The quotient invariant used here is V=a^2/b.  It is fixed by
    (s,a,b) -> (1/s,a/b,1/b),
and gives a substantially cleaner elimination than a+a/b.  No assertion in
this file treats a rational point of the quotient as a rational lift.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from src.symbolic_reduction import remainder_data


s, a, b, U, V = sp.symbols("s a b U V")


def quotient_data() -> dict[str, sp.Expr]:
    data = remainder_data()
    r1, r0 = data["R1"], data["R0"]

    # For V != 0, b=a^2/V.  Multiplication by V^2 clears exactly the
    # denominators of the two equations.
    g1 = sp.expand(sp.cancel(V**2 * r1.subs(b, a**2 / V)))
    g0 = sp.expand(sp.cancel(V**2 * r0.subs(b, a**2 / V)))
    raw_resultant = sp.expand(sp.resultant(g1, g0, a))
    reciprocal_plane = sp.cancel(raw_resultant / (s**8 * V**8))

    # reciprocal_plane/s^12 is a symmetric Laurent polynomial in s.  Express
    # it uniquely through U=s+1/s using T_k(U)=s^k+s^-k.
    chebyshev = [sp.Integer(2), U]
    for _ in range(2, 13):
        chebyshev.append(sp.expand(U * chebyshev[-1] - chebyshev[-2]))

    quotient = 0
    for v_degree in range(11):
        coefficient = sp.Poly(reciprocal_plane, V).coeff_monomial(V**v_degree)
        coefficient_poly = sp.Poly(coefficient, s)
        transformed = coefficient_poly.coeff_monomial(s**12)
        for k in range(1, 13):
            upper = coefficient_poly.coeff_monomial(s ** (12 + k))
            lower = coefficient_poly.coeff_monomial(s ** (12 - k))
            assert upper == lower
            transformed += upper * chebyshev[k]
        quotient += transformed * V**v_degree
    quotient = sp.expand(quotient)

    return {
        "g1": g1,
        "g0": g0,
        "raw_resultant": raw_resultant,
        "reciprocal_plane": reciprocal_plane,
        "quotient": quotient,
    }


def records(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    return [
        {"exponents": list(exponents), "coefficient": int(coefficient)}
        for exponents, coefficient in sp.Poly(poly, *variables).terms()
    ]


def verify() -> dict[str, object]:
    data = remainder_data()
    qdata = quotient_data()
    quotient = qdata["quotient"]

    assert sp.expand(
        qdata["raw_resultant"]
        - s**20 * V**8 * quotient.subs(U, s + 1 / s)
    ) == 0
    assert sp.Poly(quotient, U, V).degree(U) == 12
    assert sp.Poly(quotient, U, V).degree(V) == 10
    assert sp.Poly(quotient, U, V).total_degree() == 14
    assert len(sp.Poly(quotient, U, V).terms()) == 97
    assert sp.Poly(quotient, U, V).is_irreducible

    # The V=0 substitution used above is illegal.  It means a=0 and is handled
    # directly on the original remainder equations.
    f_at_a_zero = sp.factor(data["F"].subs(a, 0))
    expected_a_zero = (
        4
        * s**4
        * (s - 1) ** 4
        * (s**4 + 12 * s**3 + 26 * s**2 + 12 * s + 1)
        * (3 * s**4 - 36 * s**3 - 82 * s**2 - 36 * s + 3)
    )
    assert sp.expand(f_at_a_zero - expected_a_zero) == 0
    # The first quartic is positive for s>0.  The second has no rational root:
    # the rational-root candidates are +/-1, +/-3, +/-1/3.
    second = 3 * s**4 - 36 * s**3 - 82 * s**2 - 36 * s + 3
    candidates = [1, -1, 3, -3, sp.Rational(1, 3), sp.Rational(-1, 3)]
    assert all(second.subs(s, candidate) != 0 for candidate in candidates)

    assert sp.factor(quotient.subs(U, 2)) == V**4 * (V - 4) ** 6
    assert sp.factor(quotient.subs(U, -2)) == (V - 4) ** 10

    payload: dict[str, object] = {
        "schema": 1,
        "involution": ["s->1/s", "a->a/b", "b->1/b"],
        "invariants": {"U": "s+1/s", "V": "a^2/b"},
        "resultant_identity": "Res_a(g1,g0)=s^20*V^8*G(s+1/s,V)",
        "G_degrees": {"U": 12, "V": 10, "total": 14, "terms": 97},
        "G": records(quotient, (U, V)),
        "exception_a_zero": "no admissible rational s; only s=1 can occur",
        "necessary_square_conditions": [
            "U-2 is a rational square",
            "U+2 is a rational square",
            "V is a rational square or the negative of a rational square",
        ],
        "lifting_caveat": (
            "A rational point of G need not lift to rational s,a,b. "
            "The quotient equation is used only as a necessary obstruction."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = verify()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
