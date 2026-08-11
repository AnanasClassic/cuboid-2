#!/usr/bin/env python3
"""Exact low-resource birational transport from C8 to E1.

The three quartics below were recovered from a low-degree Riemann--Roch
calculation, but this certificate does not trust that calculation.  It checks
their image equation, reconstructs the inverse from two elementary
subresultants, verifies exact multiplication-back, and exhausts every
rational denominator-zero factor.  Only exact SymPy arithmetic over QQ is
used; no normalization command is needed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
QUOTIENT = (
    Path(__file__).parents[1]
    / "compact_signed_square"
    / "reciprocal_quotient"
    / "reciprocal_quotient.json"
)
x, y, U, V = sp.symbols("x y U V")

E = y**2 - x**3 + 5 * x - 4

f1 = (
    511 * x**4
    + 24 * x**3 * y
    - 3430 * x**3
    - 2186 * x**2 * y
    - 3677 * x**2
    + 4524 * x * y
    + 26438 * x
    - 2982 * y
    - 22214
)
f2 = (
    535 * x**4
    + 24 * x**3 * y
    - 3140 * x**3
    - 1579 * x**2 * y
    + 1380 * x**2
    + 3636 * x * y
    + 9346 * x
    - 2391 * y
    - 9307
)
f3 = (
    583 * x**4
    + 24 * x**3 * y
    - 715 * x**3
    - 293 * x**2 * y
    - 3476 * x**2
    + 2857 * x * y
    + 9529 * x
    - 3491 * y
    - 7107
)

def sparse(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in sp.Poly(poly, *variables).terms()
    ]


def load_c8() -> tuple[sp.Expr, dict[str, object]]:
    source = json.loads(QUOTIENT.read_text(encoding="utf-8"))
    c8 = sp.Poly.from_dict(
        {
            tuple(int(power) for power in record["powers"]): sp.Integer(
                record["coefficient"]
            )
            for record in source["C8_terms"]
        },
        (U, V),
        domain=sp.ZZ,
    ).as_expr()
    return c8, source


def primitive(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> sp.Expr:
    item = sp.Poly(sp.expand(poly), *variables, domain=sp.QQ)
    _, item = item.clear_denoms(convert=True)
    _, item = item.primitive()
    if item.LC() < 0:
        item = -item
    return item.as_expr()


def exact_division(
    numerator: sp.Expr, denominator: sp.Expr, variables: tuple[sp.Symbol, ...]
) -> sp.Expr:
    quotient, remainder = sp.div(
        sp.Poly(numerator, *variables), sp.Poly(denominator, *variables)
    )
    assert remainder.is_zero
    return quotient.as_expr()


def v2(value: sp.Rational) -> int:
    value = sp.Rational(value)
    numerator = abs(int(value.p))
    denominator = abs(int(value.q))

    def valuation(integer: int) -> int:
        answer = 0
        while integer and integer % 2 == 0:
            integer //= 2
            answer += 1
        return answer

    return valuation(numerator) - valuation(denominator)


def inverse_subresultant(c8: sp.Expr) -> tuple[sp.Expr, sp.Expr, dict[str, object]]:
    g_u = sp.expand(f1 - 2 * U * f3)
    g_v = sp.expand(f2 - V * f3)
    projection = sp.resultant(g_u, g_v, y)
    r5 = primitive(
        exact_division(
            projection, (x - 2) * (576 * x - 352225), (x, U, V)
        ),
        (x, U, V),
    )
    assert sp.degree(r5, x) == 5

    g_u_poly = sp.Poly(g_u, y)
    a1 = g_u_poly.coeff_monomial(y)
    b1 = g_u_poly.coeff_monomial(1)
    curve_after_y = sp.expand(b1**2 - a1**2 * (x**3 - 5 * x + 4))
    e6 = primitive(
        exact_division(
            curve_after_y,
            (576 * x - 352225) * (x**2 - 5),
            (x, U),
        ),
        (x, U),
    )
    assert sp.degree(e6, x) == 6

    subresultants = sp.subresultants(e6, r5, x)
    degrees = [int(sp.degree(item, x)) for item in subresultants]
    assert degrees == [6, 5, 4, 3, 2, 1, 0]
    linear = primitive(subresultants[-2], (x, U, V))
    linear_poly = sp.Poly(linear, x)
    A = sp.expand(linear_poly.coeff_monomial(x))
    B = sp.expand(linear_poly.coeff_monomial(1))
    assert (len(sp.Poly(A, U, V).terms()), len(sp.Poly(B, U, V).terms())) == (65, 65)
    assert (sp.degree(A, U), sp.degree(A, V)) == (12, 5)
    assert (sp.degree(B, U), sp.degree(B, V)) == (12, 5)

    d1 = 1331 * U**2 - 12 * U - 1444
    d2 = 256 * U**3 + 48 * U**2 - 729 * U + 361
    last = subresultants[-1]
    last_quotient = sp.cancel(last / (d1 * d2**2 * c8))
    assert sp.denom(last_quotient) == 1
    assert sp.Poly(last_quotient, U, V).total_degree() == 0
    assert last_quotient != 0

    # Exact multiplication-back, without forming the enormous raw rational
    # inverse.  The pseudo-remainders are A^d times evaluation at x=-B/A.
    r5_back = sp.prem(r5, A * x + B, x)
    e6_back = sp.prem(e6, A * x + B, x)
    assert sp.expand(sp.rem(r5_back, c8, V)) == 0
    assert sp.expand(sp.rem(e6_back, c8, V)) == 0

    g_v_poly = sp.Poly(g_v, y)
    a2 = g_v_poly.coeff_monomial(y)
    b2 = g_v_poly.coeff_monomial(1)
    delta = sp.expand(a1 * b2 - a2 * b1)
    assert sp.expand(delta - projection) == 0
    assert sp.expand(
        curve_after_y
        - exact_division(
            curve_after_y,
            (576 * x - 352225) * (x**2 - 5),
            (x, U),
        )
        * (576 * x - 352225)
        * (x**2 - 5)
    ) == 0

    # With x=-B/A and y=-b1/a1, the first displayed identity is exactly the
    # cleared V roundtrip and the second is exactly a1^2*E(x,y).  Since the
    # R5 and E6 pseudo-remainders vanish modulo C8, both vanish away from the
    # separately classified removed factors.
    y_formal = -b1 / a1
    assert sp.factor(sp.together(a1 * g_u.subs(y, y_formal))) == 0
    assert sp.factor(sp.together(a1 * g_v.subs(y, y_formal) - delta)) == 0
    assert sp.factor(
        sp.together(a1**2 * E.subs(y, y_formal) - curve_after_y)
    ) == 0

    return A, B, {
        "projection_resultant": "(x-2)*(576*x-352225)*R5",
        "R5_degree_x": 5,
        "elliptic_substitution_numerator": (
            "-(576*x-352225)*(x^2-5)*E6 up to primitive sign"
        ),
        "E6_degree_x": 6,
        "subresultant_degrees": degrees,
        "last_subresultant": (
            "nonzero_constant*(1331*U^2-12*U-1444)*"
            "(256*U^3+48*U^2-729*U+361)^2*C8"
        ),
        "inverse": "x=-B/A; y=-b1(x,U)/a1(x,U)",
        "multiplication_back": {
            "prem_R5_by_Ax_plus_B_is_zero_mod_C8": True,
            "prem_E6_by_Ax_plus_B_is_zero_mod_C8": True,
            "cleared_U_roundtrip": "a1*(f1-2*U*f3)(x,-b1/a1)=0",
            "cleared_V_roundtrip": (
                "a1*(f2-V*f3)(x,-b1/a1)=Res_y(gU,gV), up to sign"
            ),
            "cleared_E1": (
                "a1^2*E1(x,-b1/a1)=b1^2-a1^2*(x^3-5*x+4)"
            ),
        },
        "A_terms": sparse(A, (U, V)),
        "B_terms": sparse(B, (U, V)),
    }


def verify() -> dict[str, object]:
    c8, quotient = load_c8()
    assert quotient["status"] == "MACHINE-VERIFIED"

    # Forward map E1 -> C8.
    forward_num = sp.together(
        c8.subs({U: f1 / (2 * f3), V: f2 / f3}, simultaneous=True)
    ).as_numer_denom()[0]
    assert sp.expand(sp.rem(forward_num, E, y)) == 0

    # The only rational affine zero of f3 is the removable base -4P.
    f3_resultant = sp.factor(sp.resultant(E, f3, y))
    expected_f3_resultant = -(
        (576 * x - 352225) * (x**2 - 5) * (x**2 - x - 1) ** 3
    )
    assert sp.expand(f3_resultant - expected_f3_resultant) == 0
    assert sp.Poly(x**2 - 5, x).is_irreducible
    assert sp.Poly(x**2 - x - 1, x).is_irreducible

    A, B, inverse_record = inverse_subresultant(c8)

    # At O, ord_O(x)=-2 and ord_O(y)=-3.  The unique largest-pole monomial
    # of every fi is 24*x^3*y, so the exact projective limit is (1/2,1).
    for item in (f1, f2, f3):
        weighted = [
            (2 * exponents[0] + 3 * exponents[1], exponents, coefficient)
            for exponents, coefficient in sp.Poly(item, x, y).terms()
        ]
        maximum = max(weight for weight, _, _ in weighted)
        leaders = [entry for entry in weighted if entry[0] == maximum]
        assert leaders == [(9, (3, 1), 24)]
    assert c8.subs({U: sp.Rational(1, 2), V: 1}) == 0

    # A=0 is the only inverse x-denominator.  Its complete projection to the
    # U-line has only four rational candidates; direct fibres exclude each.
    d1 = 1331 * U**2 - 12 * U - 1444
    d2 = 256 * U**3 + 48 * U**2 - 729 * U + 361
    d8 = (
        1000 * U**8
        - 4312 * U**7
        + 1720 * U**6
        + 7260 * U**5
        - 677 * U**4
        - 3257 * U**3
        - 983 * U**2
        - 107 * U
        - 4
    )
    expected_exception = (
        -256
        * U**2
        * (U - 1) ** 8
        * (U + 1) ** 4
        * (2 * U - 1) ** 18
        * d1**5
        * d2**8
        * d8**2
    )
    exception_resultant = sp.resultant(c8, A, V)
    assert sp.expand(exception_resultant - expected_exception) == 0
    assert all(sp.Poly(item, U).is_irreducible for item in (d1, d2, d8))

    fibre_0 = sp.factor(c8.subs(U, 0))
    fibre_1 = sp.factor(c8.subs(U, 1))
    fibre_minus_1 = sp.factor(c8.subs(U, -1))
    fibre_half = sp.factor(c8.subs(U, sp.Rational(1, 2)))
    assert fibre_0 == 31 * V**4 + 48 * V**3 - 46 * V**2 + 12 * V - 1
    assert sp.Poly(fibre_0, V).is_irreducible
    assert fibre_1 == -(V - 1) ** 4 * (V + 3) ** 2
    assert fibre_minus_1 == -(V + 1) ** 3 * (V**3 - 69 * V**2 - 117 * V - 79)
    assert sp.Poly(V**3 - 69 * V**2 - 117 * V - 79, V).is_irreducible
    half_quintic = V**5 + 37 * V**4 - 23 * V**3 - 206 * V**2 + 241 * V - 71
    assert sp.expand(fibre_half + (V - 1) * half_quintic / 4) == 0
    assert sp.Poly(half_quintic, V).is_irreducible

    # The y-inverse denominator a1 is also closed exactly.  If a1=0 and the
    # cleared V roundtrip holds, then either a2=0 or b1=0.  The simultaneous
    # coefficient locus on C8 has rational x only 2 and 352225/576.  In the
    # second case b1=0 forces the same two values by Res_y(f1,f3).
    af1, af2, af3 = (sp.diff(item, y) for item in (f1, f2, f3))
    u_coeff = af1 / (2 * af3)
    v_coeff = af2 / af3
    simultaneous_num = sp.together(
        c8.subs({U: u_coeff, V: v_coeff}, simultaneous=True)
    ).as_numer_denom()[0]
    simultaneous_factors = sp.factor_list(primitive(simultaneous_num, (x,)))[1]
    assert {(str(item), exponent) for item, exponent in simultaneous_factors[:2]} == {
        (str(x - 2), 3),
        (str(576 * x - 352225), 1),
    }
    degree_19 = [item for item, exponent in simultaneous_factors if sp.degree(item, x) == 19]
    assert len(degree_19) == 1
    assert sp.Poly(degree_19[0], x).is_irreducible
    assert sp.Poly(af3, x).is_irreducible

    r13 = sp.factor(sp.resultant(f1, f3, y))
    r13_cubic = 3 * x**3 + x**2 - 19 * x + 16
    assert r13 == (
        (x - 2) * (576 * x - 352225) * (x**2 - 5) * r13_cubic
    )
    assert sp.Poly(r13_cubic, x).is_irreducible

    # Removed x-factors.  x=2 would require y^2=2; x^2=5 has no rational
    # x.  The remaining x-value gives +/-4P and is checked exactly.
    assert (x**3 - 5 * x + 4).subs(x, 2) == 2
    x4 = sp.Rational(352225, 576)
    y4 = sp.Rational(209039023, 13824)
    assert E.subs({x: x4, y: y4}) == E.subs({x: x4, y: -y4}) == 0
    plus_values = [item.subs({x: x4, y: y4}) for item in (f1, f2, f3)]
    plus_u = sp.factor(plus_values[0] / (2 * plus_values[2]))
    plus_v = sp.factor(plus_values[1] / plus_values[2])
    plus_uv = sp.factor(plus_u * plus_v)
    assert plus_u == sp.Rational(2507654733463, 5773889467838)
    assert plus_v == sp.Rational(2739947416519, 3008594206519)
    assert plus_uv == sp.Rational(
        463025952454585106023, 1170651014355312270398
    )
    assert v2(plus_uv) == -1

    minus_values = [item.subs({x: x4, y: -y4}) for item in (f1, f2, f3)]
    assert minus_values == [0, 0, 0]
    slope = (3 * x4**2 - 5) / (-2 * y4)
    derivatives = [
        sp.diff(item, x).subs({x: x4, y: -y4})
        + sp.diff(item, y).subs({x: x4, y: -y4}) * slope
        for item in (f1, f2, f3)
    ]
    limit_u = sp.factor(derivatives[0] / (2 * derivatives[2]))
    limit_v = sp.factor(derivatives[1] / derivatives[2])
    limit_uv = sp.factor(limit_u * limit_v)
    assert limit_u == sp.Rational(
        731754020216156986855, 1316366220366073678142
    )
    assert limit_v == sp.Rational(
        678770002969523258551, 632597885616799462855
    )
    assert limit_uv == sp.Rational(
        59409766391312609246463879655380631,
        99603489008786736151209561658227902,
    )
    assert v2(limit_uv) == -1

    assert sp.factor(u_coeff.subs(x, 2)) == -1
    assert sp.factor(v_coeff.subs(x, 2)) == -1
    assert sp.factor(u_coeff.subs(x, x4)) == plus_u
    assert sp.factor(v_coeff.subs(x, x4)) == plus_v
    plus_fibre_factors = sp.factor_list(sp.Poly(c8.subs(U, plus_u), V))[1]
    limit_fibre_factors = sp.factor_list(sp.Poly(c8.subs(U, limit_u), V))[1]
    assert [(item.degree(), exponent) for item, exponent in plus_fibre_factors] == [
        (1, 1),
        (5, 1),
    ]
    assert [(item.degree(), exponent) for item, exponent in limit_fibre_factors] == [
        (1, 1),
        (5, 1),
    ]
    assert plus_fibre_factors[0][0].as_expr() == 3008594206519 * V - 2739947416519
    assert limit_fibre_factors[0][0].as_expr() == (
        632597885616799462855 * V - 678770002969523258551
    )
    assert plus_fibre_factors[1][0].is_irreducible
    assert limit_fibre_factors[1][0].is_irreducible

    # The common removed projection/base value x=x4 is audited against the
    # inverse linear equation itself.  The resultant has only the previously
    # closed U-values plus the actual +4P and removable -4P values.
    removed_linear = sp.expand(352225 * A + 576 * B)
    removed_resultant = sp.resultant(c8, removed_linear, V)
    plus_linear = 5773889467838 * U - 2507654733463
    limit_linear = 1316366220366073678142 * U - 731754020216156986855
    expected_removed_resultant = (
        -256
        * plus_linear
        * limit_linear
        * U**2
        * (U + 1) ** 4
        * (U - 1) ** 8
        * (2 * U - 1) ** 16
        * d1**5
        * d2**8
        * d8**2
    )
    assert sp.expand(removed_resultant - expected_removed_resultant) == 0

    # Exact common-base ideal: the forward base is only -4P.
    base_groebner = sp.groebner([E, f1, f2, f3], y, x, order="lex")
    expected_base = sp.groebner(
        [13824 * y + 209039023, 576 * x - 352225], y, x, order="lex"
    )
    assert base_groebner == expected_base

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "theorem": (
            "The irreducible reciprocal quotient C8 is birational over QQ "
            "to E1: y^2=x^3-5*x+4.  Explicit maps, inverse subresultants, "
            "and every rational denominator exception are certified."
        ),
        "quotient_checksum": quotient["sha256_without_checksum"],
        "E1": "y^2=x^3-5*x+4",
        "forward": {"U": "f1/(2*f3)", "V": "f2/f3"},
        "f1_terms": sparse(f1, (x, y)),
        "f2_terms": sparse(f2, (x, y)),
        "f3_terms": sparse(f3, (x, y)),
        "forward_identity": "numerator(C8(f1/(2f3),f2/f3)) is zero modulo E1",
        "inverse_subresultant": inverse_record,
        "point_at_infinity": {
            "E1_point": "O",
            "pole_orders": "ord_O(x)=-2, ord_O(y)=-3",
            "common_unique_leading_monomial": "24*x^3*y in f1,f2,f3",
            "C8_image": ["1/2", "1"],
            "C8_identity_verified": True,
        },
        "forward_denominator": {
            "resultant_E_f3": str(f3_resultant),
            "unique_rational_affine_zero": "-4P=(352225/576,-209039023/13824)",
            "extension_at_minus_4P": {"U": str(limit_u), "V": str(limit_v)},
            "extension_UV_v2": -1,
            "point_at_O": ["1/2", "1"],
        },
        "inverse_denominator": {
            "resultant_C8_A": str(sp.factor(exception_resultant)),
            "rational_U_candidates": ["0", "1", "-1", "1/2"],
            "fibres": {
                "U=0": str(fibre_0),
                "U=1": str(fibre_1),
                "U=-1": str(fibre_minus_1),
                "U=1/2": str(fibre_half),
            },
            "classification": (
                "U=0 has no rational V.  At U=1, V=1 is UV=1 boundary "
                "and V=-3 has UV<0.  At U=-1, V=-1 is UV=1 boundary and "
                "the other cubic is irreducible.  At U=1/2, V=1 gives "
                "UV=1/2, not a rational square; the quintic is irreducible."
            ),
            "admissible_square_character_points": [],
        },
        "inverse_y_denominator": {
            "function": "a1=coefficient_y(f1-2*U*f3)",
            "simultaneous_a1_a2_C8_x_factors": [
                "(x-2)^3",
                "576*x-352225",
                "irreducible degree 19",
            ],
            "Res_y(f1,f3)": str(r13),
            "rational_cases": {
                "x=2": "(U,V)=(-1,-1), hence UV=1 boundary",
                "x=352225/576": (
                    "the only rational V is the +4P value; UV has v2=-1"
                ),
            },
            "admissible_rational_zeros": [],
        },
        "removed_projection_factors": {
            "x=2": "requires y^2=2",
            "x^2=5": "no rational x",
            "plus_4P": {"U": str(plus_u), "V": str(plus_v), "UV_v2": -1},
            "minus_4P": {"U": str(limit_u), "V": str(limit_v), "UV_v2": -1},
            "x4_inverse_resultant": str(sp.factor(removed_resultant)),
        },
        "logical_scope": (
            "This proves the characteristic-zero transport for the compact "
            "reciprocal quotient C8 and bypasses the original H-normalization "
            "problem.  It does not prove C025 as stated, nor classify the "
            "rational points satisfying all three square characters."
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
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("C8 <-> E1 exact birational transport: OK")
    print("all rational forward/inverse denominator exceptions: classified")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
