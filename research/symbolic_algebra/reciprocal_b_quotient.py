#!/usr/bin/env python3
"""Exact reciprocal quotient in the invariants U=s+1/s and W=b+1/b.

For a genuine quadratic factor ``x^2+a*x+b`` the remainder equations
``R1=R0=0`` hold.  Eliminating ``a`` and then adjoining the two reciprocal
quadratics for ``s`` and ``b`` produces a perfect square ``K(U,W)^2``.  The
square/signed-square arithmetic becomes especially transparent on K:

    s=z^2     => U+2=(z+1/z)^2 and U-2=(z-1/z)^2,
    b= c^2    => W+2=(c+1/c)^2,
    b=-c^2    => 2-W=(c+1/c)^2.

Only the forward implication is used.  A rational point on K need not lift
to rational factorization data.
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


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "artifacts" / "reciprocal_b_quotient.json"

s, a, b, U, W, v, r, w, h = sp.symbols("s a b U W v r w h")


def records(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    return [
        {"exponents": list(exponents), "coefficient": str(coefficient)}
        for exponents, coefficient in sp.Poly(poly, *variables).terms()
    ]


def quotient_data() -> dict[str, sp.Expr]:
    data = remainder_data()
    projection = sp.resultant(data["R1"], data["R0"], a)
    eliminate_b = sp.resultant(projection, b**2 - W * b + 1, b)
    eliminate_s = sp.resultant(eliminate_b, s**2 - U * s + 1, s)

    content, factors = sp.factor_list(eliminate_s)
    assert content == 1 and len(factors) == 1 and factors[0][1] == 2
    quotient = sp.Poly(factors[0][0], U, W).primitive()[1].as_expr()
    if sp.Poly(quotient, U, W).LC() < 0:
        quotient = -quotient
    assert sp.expand(eliminate_s - quotient**2) == 0

    return {
        "projection": projection,
        "eliminate_b": eliminate_b,
        "eliminate_s": eliminate_s,
        "quotient": quotient,
    }


def verify() -> dict[str, object]:
    qdata = quotient_data()
    quotient = qdata["quotient"]
    poly = sp.Poly(quotient, U, W)
    assert (poly.degree(U), poly.degree(W), len(poly.terms())) == (20, 10, 150)
    assert poly.is_irreducible

    special_fibres = {
        "U=2": sp.factor(quotient.subs(U, 2)),
        "U=-2": sp.factor(quotient.subs(U, -2)),
        "W=2": sp.factor(quotient.subs(W, 2)),
        "W=-2": sp.factor(quotient.subs(W, -2)),
    }
    assert special_fibres["U=2"] == -(W - 2) ** 6 * (W + 2) ** 4
    assert special_fibres["U=-2"] == -(W - 2) ** 10
    assert special_fibres["W=2"] == (
        -256
        * (U - 2) ** 6
        * (U + 1) ** 4
        * (U + 2) ** 2
        * (U**3 - 3 * U**2 - 4 * U + 16) ** 2
    )
    assert special_fibres["W=-2"] == (
        -4
        * (U - 2) ** 4
        * (
            U**8
            + 6 * U**7
            + 55 * U**6
            + 172 * U**5
            + 182 * U**4
            - 64 * U**3
            - 192 * U**2
            - 128
        )
        ** 2
    )

    cover_substitutions = {
        "square_parameter_plus": {U: v**2 - 2},
        "square_parameter_minus": {U: r**2 + 2},
        "positive_constant": {W: w**2 - 2},
        "negative_constant": {W: 2 - w**2},
        "simultaneous_positive": {U: v**2 - 2, W: w**2 - 2},
        "simultaneous_negative": {U: v**2 - 2, W: 2 - w**2},
    }
    cover_variables = {
        "square_parameter_plus": (v, W),
        "square_parameter_minus": (r, W),
        "positive_constant": (U, w),
        "negative_constant": (U, w),
        "simultaneous_positive": (v, w),
        "simultaneous_negative": (v, w),
    }
    cover_data: dict[str, object] = {}
    for name, substitution in cover_substitutions.items():
        pulled_back = sp.expand(quotient.subs(substitution))
        variables = cover_variables[name]
        pulled_poly = sp.Poly(pulled_back, *variables)
        factors = sp.factor_list(pulled_back)[1]
        assert len(factors) == 1 and factors[0][1] == 1
        cover_data[name] = {
            "variables": [str(variable) for variable in variables],
            "degrees": [pulled_poly.degree(variable) for variable in variables],
            "total_degree": pulled_poly.total_degree(),
            "terms": len(pulled_poly.terms()),
            "irreducible_over_Q": True,
        }

    # The product-character quotients of the two V4 covers.
    product_positive = sp.together(
        quotient.subs(W, h**2 / (U + 2) - 2)
    ).as_numer_denom()[0]
    product_negative = sp.together(
        quotient.subs(W, 2 - h**2 / (U + 2))
    ).as_numer_denom()[0]
    for name, product in [
        ("product_positive", product_positive),
        ("product_negative", product_negative),
    ]:
        factors = sp.factor_list(product)[1]
        assert len(factors) == 1 and factors[0][1] == 1
        product_poly = sp.Poly(product, U, h)
        cover_data[name] = {
            "variables": ["U", "h"],
            "degrees": [product_poly.degree(U), product_poly.degree(h)],
            "total_degree": product_poly.total_degree(),
            "terms": len(product_poly.terms()),
            "irreducible_over_Q": True,
        }

    payload: dict[str, object] = {
        "schema": 1,
        "invariants": {"U": "s+1/s", "W": "b+1/b"},
        "perfect_square_identity": (
            "Res_s(Res_b(Res_a(R1,R0),b^2-W*b+1),s^2-U*s+1)=K(U,W)^2"
        ),
        "K": records(quotient, (U, W)),
        "K_degrees": {"U": 20, "W": 10, "terms": 150},
        "special_fibres": {key: str(value) for key, value in special_fibres.items()},
        "necessary_covers": {
            "positive_b": [
                "K(U,W)=0",
                "U+2 is a square",
                "U-2 is a square",
                "W+2 is a square",
            ],
            "negative_b": [
                "K(U,W)=0",
                "U+2 is a square",
                "U-2 is a square",
                "2-W is a square",
            ],
        },
        "full_cover_equations": {
            "common": ["K(U,W)=0", "v^2=U+2", "r^2=U-2"],
            "positive_b": "w^2=W+2",
            "negative_b": "w^2=2-W",
        },
        "cover_models": cover_data,
        "lifting_caveat": (
            "K=0 and the square conditions are necessary only; every surviving "
            "point must be lifted back through R1=R0=0."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(rendered, encoding="utf-8")
    print("perfect-square reciprocal elimination: OK")
    print("K(U,W): bidegree (20,10), 150 terms, irreducible over Q")
    print("positive/negative V4 cover equations: OK")
    print("wrote", args.output.resolve().relative_to(ROOT))


if __name__ == "__main__":
    main()
