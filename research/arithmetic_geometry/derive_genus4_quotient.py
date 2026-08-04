#!/usr/bin/env python3
"""Derive exact plane models for the square-pullback reciprocal quotient.

The smooth curve of interest is the normalization of the quadratic-factor
curve after ``s=z^2``, modulo

    (z,a,b) |-> (1/z, a/b, 1/b).

The script constructs a birational plane model G(X,A)=0, the residual
bielliptic quotient H(q,A)=0, and an exact generic lift based on the linear
subresultant in B.  All arithmetic is over QQ.  The sparse coefficient output
is written to ``artifacts/genus4_quotient.json``.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / "artifacts" / "genus4_quotient.json"

s, x, a, b = sp.symbols("s x a b")
T, B, A, X, q, U = sp.symbols("T B A X q U")

c4 = (2 + s) * (3 - 2 * s)
c3 = 1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4
c2 = -s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4)
c1 = -s**3 * (1 + 2 * s) * (-2 + 3 * s)
c0 = -s**5
P = sp.expand(x**5 + c4 * x**4 + c3 * x**3 + c2 * x**2 + c1 * x + c0)

u = -3 * a**2 + 2 * a * c4 - c3
v = a**4 - c4 * a**3 + c3 * a**2 - c2 * a + c1
m = c4 - 2 * a
n = a**3 - c4 * a**2 + c3 * a - c2
R1 = sp.expand(b**2 + u * b + v)
R0 = sp.expand(m * b**2 + n * b + c0)


def sparse(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in sp.Poly(poly, *variables).terms()
    ]


def primitive_numerator(expr: sp.Expr, variables: tuple[sp.Symbol, ...]) -> sp.Expr:
    numerator = sp.together(expr).as_numer_denom()[0]
    return sp.Poly(sp.expand(numerator), *variables).primitive()[1].as_expr()


def main() -> None:
    reciprocal = sp.cancel(
        P + s**5 * x**5 * P.subs({s: 1 / s, x: 1 / x}, simultaneous=True)
    )
    assert reciprocal == 0

    # Mobius coordinates linearize the lifted reciprocal involution:
    # tau_+ : (T,B,A) -> (-T,-B,A).
    z_of_T = (1 + T) / (1 - T)
    substitutions = {
        s: z_of_T**2,
        b: (1 + B) / (1 - B),
        a: A / (1 - B),
    }
    H1 = primitive_numerator(R1.subs(substitutions), (B, T, A))
    H0 = primitive_numerator(R0.subs(substitutions), (B, T, A))
    assert sp.degree(H1, B) == 4 and sp.degree(H0, B) == 4

    resultant = sp.resultant(H1, H0, B)
    content, factors = sp.factor_list(resultant)
    assert content == 2**14
    factor_signature = sorted(
        (sp.degree(factor, T), sp.degree(factor, A), exponent)
        for factor, exponent in factors
    )
    assert factor_signature == [(0, 1, 6), (1, 0, 4), (1, 0, 40), (32, 10, 1)]
    desired_T = next(factor for factor, _ in factors if sp.degree(factor, A) == 10)
    assert all(power_T % 2 == 0 for (power_T, _), _ in sp.Poly(desired_T, T, A).terms())

    # X=T^2 is invariant.  G is the genus-four quotient's plane model.
    G = sum(
        coefficient * X ** (power_T // 2) * A**power_A
        for (power_T, power_A), coefficient in sp.Poly(desired_T, T, A).terms()
    )
    G = sp.Poly(sp.expand(G), X, A).primitive()[1].as_expr()
    assert (sp.degree(G, X), sp.degree(G, A)) == (16, 10)
    assert len(sp.factor_list(G)[1]) == 1
    assert sp.expand(G - X**16 * G.subs(X, 1 / X)) == 0

    # The residual involution is X -> 1/X.  Put q=X+1/X and write
    # G=X^8 H(q,A).  The normalization of H is the elliptic quotient E.
    polynomial_X = sp.Poly(G, X)
    coefficients_X = [polynomial_X.coeff_monomial(X**i) for i in range(17)]
    assert all(coefficients_X[i] == coefficients_X[16 - i] for i in range(17))
    chebyshev = [sp.Integer(2), q]
    for _ in range(2, 9):
        chebyshev.append(sp.expand(q * chebyshev[-1] - chebyshev[-2]))
    H = coefficients_X[8] + sum(
        coefficients_X[8 + k] * chebyshev[k] for k in range(1, 9)
    )
    H = sp.Poly(sp.expand(H), q, A).primitive()[1].as_expr()
    assert (sp.degree(H, q), sp.degree(H, A)) == (8, 10)
    assert sp.expand(G - X**8 * H.subs(q, X + 1 / X)) == 0
    assert len(sp.factor_list(H)[1]) == 1

    # Relation to the original reciprocal invariant U=s+1/s and to
    # v=z+1/z on the genus-four double cover of E.
    U_of_q = 2 * (q + 6) / (q - 2)
    U_of_X = 2 * (X**2 + 6 * X + 1) / (X - 1) ** 2
    assert sp.cancel(U_of_q.subs(q, X + 1 / X) - U_of_X) == 0
    assert sp.cancel((z_of_T**2 + z_of_T**-2) - U_of_X.subs(X, T**2)) == 0
    assert sp.cancel(U_of_q + 2 - 4 * (q + 2) / (q - 2)) == 0

    # Exact special fibres controlling the six branch points of v^2=U+2.
    fibre_q_minus_2 = sp.factor(H.subs(q, -2))
    fibre_q_plus_2 = sp.factor(H.subs(q, 2))
    assert fibre_q_minus_2 == 2**16 * (A - 2) ** 10
    assert fibre_q_plus_2 == 2**27 * A**3 * (A - 6) * (A**2 - 12 * A + 4) ** 3

    # Generic inverse: the penultimate subresultant is Q1(T,A)B+Q0(T,A).
    subresultants = sp.subresultants(H1, H0, B)
    linear = sp.Poly(subresultants[-2], B).primitive()[1]
    assert linear.degree() == 1
    Q1 = sp.expand(linear.coeff_monomial(B))
    Q0 = sp.expand(linear.coeff_monomial(1))

    # The b=-1 chart exception.  It has no real s>0 point except s=1,
    # because the residual degree-16 polynomial has strictly positive
    # coefficients.
    R1_bminus = sp.expand(R1.subs(b, -1))
    R0_bminus = sp.expand(R0.subs(b, -1))
    exceptional_resultant = sp.factor(sp.resultant(R1_bminus, R0_bminus, a))
    positive_factor = sp.cancel(exceptional_resultant / (2 * (s - 1) ** 4))
    assert sp.Poly(positive_factor, s).degree() == 16
    assert all(coefficient > 0 for coefficient in sp.Poly(positive_factor, s).all_coeffs())

    payload: dict[str, object] = {
        "schema": 1,
        "coordinates": {
            "T": "(z-1)/(z+1)",
            "B": "(b-1)/(b+1)",
            "A": "2*a/(b+1)=a*(1-B)",
            "X": "T^2",
            "q": "X+1/X",
            "U": "s+1/s=2*(q+6)/(q-2)",
        },
        "forward_map": ["X=((z-1)/(z+1))^2", "A=2*a/(b+1)"],
        "generic_lift": [
            "choose T with T^2=X",
            "B=-Q0(T,A)/Q1(T,A)",
            "z=(1+T)/(1-T)",
            "b=(1+B)/(1-B)",
            "a=A/(1-B)",
        ],
        "genus4_model": {"variables": ["X", "A"], "terms": sparse(G, (X, A))},
        "elliptic_plane_model": {"variables": ["q", "A"], "terms": sparse(H, (q, A))},
        "linear_subresultant": {
            "formula": "Q1(T,A)*B+Q0(T,A)",
            "Q1_terms": sparse(Q1, (T, A)),
            "Q0_terms": sparse(Q0, (T, A)),
        },
        "maps": {
            "bielliptic": "q=X+1/X",
            "double_cover": "v^2=U+2=4*(q+2)/(q-2)",
            "residual_involution": "X->1/X",
        },
        "special_fibres": {
            "q=-2": str(fibre_q_minus_2),
            "q=2": str(fibre_q_plus_2),
            "b=-1_resultant_in_s": str(exceptional_resultant),
        },
    }
    encoded_without_checksum = json.dumps(payload, indent=2, sort_keys=True).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(encoded_without_checksum).hexdigest()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    print("G(X,A): degree", sp.degree(G, X), "x", sp.degree(G, A),
          "with", len(sp.Poly(G, X, A).terms()), "terms")
    print("H(q,A): degree", sp.degree(H, q), "x", sp.degree(H, A),
          "with", len(sp.Poly(H, q, A).terms()), "terms")
    print("G=X^8 H(X+1/X,A): OK")
    print("generic subresultant lift: OK")
    print("branch fibres q=+/-2 and b=-1 exception: OK")
    print("wrote", OUTPUT.relative_to(ROOT))


if __name__ == "__main__":
    main()
