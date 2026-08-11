#!/usr/bin/env python3
"""Simplify the common product square character on the explicit E1 model.

After translating E1 by its rational 2-torsion point, the common character
``1-U*V`` is twice a very small function times a square.  The scalar 2 is
part of the identity and must not be discarded.  This script proves the
identity in ``QQ(E1)`` and audits every rational zero or denominator used in
the square-class simplification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp

try:
    from research.arithmetic_geometry.low_degree_transport import f1, f2, f3
except ModuleNotFoundError:  # direct execution from this directory
    from low_degree_transport import f1, f2, f3


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
TRANSPORT = Path(__file__).with_name("low_degree_transport.json")
X, Y = sp.symbols("X Y")

E = Y**2 - X**3 + 5 * X - 4
old_x = (X - 3) / (X - 1)
old_y = 2 * Y / (X - 1) ** 2

L = 2 * X + Y - 2
M = X**2 + 2 * Y - 1
kummer = (Y + 2) / X
F = (X + 1) * L * M

D0 = (
    593 * X**5
    - 201 * X**4
    + 903 * X**3 * Y
    - 880 * X**3
    + 1977 * X**2 * Y
    + 4384 * X**2
    - 5779 * X * Y
    - 12953 * X
    + 3091 * Y
    + 9057
)
P = 2062 * X**3 - 1055 * X**2 - 8634 * X + 7723
Q = 593 * X**2 + 1807 * X - 3758
g = (P - Q * Y) / ((X - 3) * D0)


def zero_in_function_field(expr: sp.Expr) -> bool:
    numerator = sp.together(expr).as_numer_denom()[0]
    return sp.expand(sp.rem(numerator, E, Y)) == 0


def v2(value: sp.Rational) -> int:
    value = sp.Rational(value)

    def valuation(integer: int) -> int:
        answer = 0
        integer = abs(integer)
        while integer and integer % 2 == 0:
            integer //= 2
            answer += 1
        return answer

    return valuation(int(value.p)) - valuation(int(value.q))


def old_point(x_value: sp.Expr, y_value: sp.Expr) -> tuple[sp.Expr, sp.Expr]:
    return (
        sp.factor((x_value - 3) / (x_value - 1)),
        sp.factor(2 * y_value / (x_value - 1) ** 2),
    )


def direct_uv(old_x_value: sp.Expr, old_y_value: sp.Expr) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    substitution = {sp.Symbol("x"): old_x_value, sp.Symbol("y"): old_y_value}
    # f1,f2,f3 use the canonical symbols from low_degree_transport.  Matching
    # by name keeps this helper independent of their module-level aliases.
    values = [item.subs(substitution) for item in (f1, f2, f3)]
    u_value = sp.factor(values[0] / (2 * values[2]))
    v_value = sp.factor(values[1] / values[2])
    return u_value, v_value, sp.factor(u_value * v_value)


def verify() -> dict[str, object]:
    transport = json.loads(TRANSPORT.read_text(encoding="utf-8"))
    assert transport["status"] == "MACHINE-VERIFIED"

    # Translation by T=(1,0) is an involution of the same Weierstrass model.
    old_curve = sp.Symbol("y") ** 2 - sp.Symbol("x") ** 3 + 5 * sp.Symbol("x") - 4
    assert zero_in_function_field(
        old_curve.subs(
            {sp.Symbol("x"): old_x, sp.Symbol("y"): old_y}, simultaneous=True
        )
    )
    assert sp.factor((old_x - 3) / (old_x - 1) - X) == 0
    assert sp.factor(2 * old_y / (old_x - 1) ** 2 - Y) == 0

    u_function = sp.cancel(
        f1.subs({sp.Symbol("x"): old_x, sp.Symbol("y"): old_y}, simultaneous=True)
        / (
            2
            * f3.subs(
                {sp.Symbol("x"): old_x, sp.Symbol("y"): old_y}, simultaneous=True
            )
        )
    )
    v_function = sp.cancel(
        f2.subs({sp.Symbol("x"): old_x, sp.Symbol("y"): old_y}, simultaneous=True)
        / f3.subs(
            {sp.Symbol("x"): old_x, sp.Symbol("y"): old_y}, simultaneous=True
        )
    )
    assert sp.factor(sp.denom(u_function) - D0) == 0
    assert sp.factor(sp.denom(v_function) - D0) == 0

    assert zero_in_function_field(M - L * kummer)
    assert zero_in_function_field(1 - u_function * v_function - 2 * F * g**2)

    d0_resultant = sp.factor(sp.resultant(E, D0, Y))
    expected_d0_resultant = (
        (X - 1)
        * (351649 * X - 350497)
        * (X**2 - 5) ** 3
        * (X**2 - X - 1)
    )
    assert sp.expand(d0_resultant - expected_d0_resultant) == 0
    assert sp.Poly(X**2 - 5, X).is_irreducible
    assert sp.Poly(X**2 - X - 1, X).is_irreducible

    l_resultant = sp.factor(sp.resultant(E, L, Y))
    m_resultant = sp.factor(sp.resultant(E, M, Y))
    assert l_resultant == -X * (X - 3) * (X - 1)
    assert m_resultant == (X - 3) * (X - 1) * (X**2 - 5)
    assert (X**3 - 5 * X + 4).subs(X, -1) == 8

    # Direct values at every rational exceptional point of the displayed
    # formulas.  Values at translated O=(1,0) and the removable -4P base are
    # supplied independently by the transport certificate.
    direct = {
        "translated_(3,4)": direct_uv(0, 2),
        "translated_(3,-4)": direct_uv(0, -2),
        "translated_(0,2)": direct_uv(3, 4),
        "translated_(0,-2)": direct_uv(3, -4),
    }
    assert direct["translated_(3,4)"] == (1, 1, 1)
    assert direct["translated_(3,-4)"] == (65, sp.Rational(181, 5), 2353)
    assert direct["translated_(0,2)"] == (-1, -1, 1)
    assert direct["translated_(0,-2)"] == (
        sp.Rational(71, 125),
        sp.Rational(43, 25),
        sp.Rational(3053, 3125),
    )
    assert v2(sp.Rational(3053, 3125)) == 0
    assert sp.factorint(3125)[5] == 5  # an odd 5-adic valuation proves nonsquare

    assert (L.subs({X: 3, Y: 4}), M.subs({X: 3, Y: 4}), F.subs({X: 3, Y: 4})) == (
        8,
        16,
        512,
    )
    assert D0.subs({X: 3, Y: 4}) == 225424
    assert (P - Q * Y).subs({X: 3, Y: 4}) == 0
    assert (L.subs({X: 1, Y: 0}), M.subs({X: 1, Y: 0}), F.subs({X: 1, Y: 0})) == (
        0,
        0,
        0,
    )
    assert D0.subs({X: 1, Y: 0}) == 0
    assert (P - Q * Y).subs({X: 1, Y: 0}) == 96

    translated_base_x = sp.Rational(350497, 351649)
    translated_base_y = -sp.Rational(16920528, 208527857)
    assert E.subs({X: translated_base_x, Y: translated_base_y}) == 0
    assert D0.subs({X: translated_base_x, Y: translated_base_y}) == 0
    base_uv = sp.Rational(
        59409766391312609246463879655380631,
        99603489008786736151209561658227902,
    )
    assert v2(base_uv) == -1
    assert transport["forward_denominator"]["extension_UV_v2"] == -1

    # Rational zeros of F: X=-1 has no rational Y; the L and M resultants
    # leave precisely the points below.  Each is boundary or already fails
    # the common rational-square condition.
    rational_f_zeros = {
        "(0,2)": direct["translated_(0,2)"][2],
        "(1,0)": sp.Rational(1, 2),
        "(3,-4)": direct["translated_(3,-4)"][2],
    }
    assert rational_f_zeros == {"(0,2)": 1, "(1,0)": sp.Rational(1, 2), "(3,-4)": 2353}

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "transport_checksum": transport["sha256_without_checksum"],
        "coordinates": {
            "translation": "X=(x-3)/(x-1), Y=2*y/(x-1)^2",
            "inverse": "x=(X-3)/(X-1), y=2*Y/(X-1)^2",
            "curve": "Y^2=X^3-5*X+4",
        },
        "small_functions": {
            "L": "2*X+Y-2",
            "M": "X^2+2*Y-1",
            "k": "(Y+2)/X",
            "F": "(X+1)*L*M",
            "function_field_identity": "M=L*k",
            "squareclass_form": "F=L^2*(X+1)*(Y+2)/X",
        },
        "exact_identity": "1-U*V=2*F*g^2",
        "warning": "The scalar 2 is essential and is not a square in QQ.",
        "g": "(P-Q*Y)/((X-3)*D0)",
        "P": str(P),
        "Q": str(Q),
        "D0": str(D0),
        "consequence": (
            "At every admissible point outside the audited exceptional set, "
            "1-U*V is a rational square iff 2*(X+1)*(Y+2)/X is a rational square."
        ),
        "denominator_audit": {
            "resultant_E_D0": str(d0_resultant),
            "rational_D0_points": [
                "translated O=(1,0)",
                "translated -4P=(350497/351649,-16920528/208527857)",
            ],
            "translated_O": {"U": "1/2", "V": "1", "UV": "1/2"},
            "translated_minus_4P": {"UV": str(base_uv), "UV_v2": -1},
            "X=3": {
                "(3,4)": {"U": "1", "V": "1", "UV": "1", "status": "boundary"},
                "(3,-4)": {"U": "65", "V": "181/5", "UV": "2353", "status": "nonsquare"},
            },
            "X=0": {
                "(0,2)": {"U": "-1", "V": "-1", "UV": "1", "status": "boundary"},
                "(0,-2)": {"U": "71/125", "V": "43/25", "UV": "3053/3125", "status": "nonsquare"},
            },
            "old_T=(1,0)": {"U": "1", "V": "1", "UV": "1", "status": "boundary"},
        },
        "F_zero_audit": {
            "Res(E,L)": str(l_resultant),
            "Res(E,M)": str(m_resultant),
            "X=-1": "Y^2=8 has no rational solution",
            "rational_points": {
                "(0,2)": "UV=1 boundary",
                "(1,0)": "UV=1/2 nonsquare",
                "(3,-4)": "UV=2353 nonsquare",
            },
        },
        "logical_scope": (
            "This is an exact square-class reduction for the common product "
            "character.  It does not classify the resulting double cover."
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
    print("1-U*V = 2*F*g^2 on E1: OK")
    print("all rational zeros and denominators: classified")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
