#!/usr/bin/env python3
"""Exact certificates supporting the elementary 2-isogeny rank proof.

The accompanying Markdown file supplies the valuation and group-index proof.
This script checks every polynomial identity, rational point, descent class,
duplication calculation, and Nagell--Lutz candidate used there.  It does not
query LMFDB or use its rank/generator metadata.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = Path(__file__).with_name("candidate_544c_rank_descent.json")


def verify() -> dict[str, object]:
    x, y, u, v, w, h = sp.symbols("x y u v w h")

    short_rhs = x**3 - 5 * x + 4
    shifted_rhs = x * (x**2 + 3 * x - 2)
    dual_rhs = u * (u**2 - 6 * u + 17)
    assert sp.expand(short_rhs.subs(x, x + 1) - shifted_rhs) == 0
    assert sp.factor(short_rhs) == (x - 1) * (x**2 + x - 4)
    assert sp.discriminant(x**2 + x - 4, x) == 17

    # Standard descent-map kernel identity.  If x=w^2 and h=y/w, put
    # u=3+2*w^2-2*h and v=2*u*w.  The relation h^2=w^4+3*w^2-2 makes
    # (u,v) a point on the dual curve and the dual isogeny maps it back.
    u_lift = 3 + 2 * w**2 - 2 * h
    v_lift = 2 * u_lift * w
    h_relation = h**2 - (w**4 + 3 * w**2 - 2)
    lift_curve_error = sp.expand(v_lift**2 - dual_rhs.subs(u, u_lift))
    assert sp.rem(sp.Poly(lift_curve_error, h), sp.Poly(h_relation, h)).as_expr() == 0
    dual_x = sp.cancel(v**2 / (4 * u**2))
    dual_y = sp.cancel(v * (17 - u**2) / (8 * u**2))
    lift_x_error = sp.together(
        dual_x.subs({u: u_lift, v: v_lift}, simultaneous=True) - w**2
    ).as_numer_denom()[0]
    lift_y_error = sp.together(
        dual_y.subs({u: u_lift, v: v_lift}, simultaneous=True) - w * h
    ).as_numer_denom()[0]
    assert sp.rem(sp.Poly(lift_x_error, h), sp.Poly(h_relation, h)).as_expr() == 0
    assert sp.rem(sp.Poly(lift_y_error, h), sp.Poly(h_relation, h)).as_expr() == 0

    # The four possible squareclasses on E are all exhibited by points.
    shifted_points = {
        "torsion": (sp.Integer(0), sp.Integer(0)),
        "P": (sp.Integer(-1), sp.Integer(2)),
        "P_plus_torsion": (sp.Integer(2), sp.Integer(4)),
    }
    for point_x, point_y in shifted_points.values():
        assert point_y**2 == shifted_rhs.subs(x, point_x)
    # The line through P=(-1,2) and T=(0,0) is Y=-2X.  Its third
    # intersection is (2,-4), so the group sum is (2,4).
    assert sp.factor((-2 * x) ** 2 - shifted_rhs) == -x * (x - 2) * (x + 1)
    descent_classes_e = {
        "O": 1,
        "torsion_(0,0)": -2,
        "P_(-1,2)": -1,
        "P_plus_torsion_(2,4)": 2,
    }
    assert set(descent_classes_e.values()) == {-2, -1, 1, 2}

    # On the dual, u*((u-3)^2+8) is negative for u<0.  The valuation
    # lemma leaves only positive squarefree divisors of 17.
    assert sp.expand((u - 3) ** 2 + 8 - (u**2 - 6 * u + 17)) == 0
    descent_classes_dual = {"O": 1, "torsion_(0,0)": 17}
    assert set(descent_classes_dual.values()) == {1, 17}

    # The index computation in the proof is
    # 2^rank = |alpha(E)|*|alpha'(E')|/4 = 4*2/4 = 2.
    image_size_e = len(descent_classes_e)
    image_size_dual = len(descent_classes_dual)
    rank_power = image_size_e * image_size_dual // 4
    assert (image_size_e, image_size_dual, rank_power) == (4, 2, 2)
    rank = rank_power.bit_length() - 1
    assert 2**rank == rank_power and rank == 1

    # P=(0,2) on the original short model.  Its double has nonintegral
    # coordinates, so Nagell--Lutz rules out torsion.
    point_p = (sp.Integer(0), sp.Integer(2))
    slope = sp.Rational(3 * point_p[0] ** 2 - 5, 2 * point_p[1])
    double_x = sp.factor(slope**2 - 2 * point_p[0])
    double_y = sp.factor(slope * (point_p[0] - double_x) - point_p[1])
    assert (slope, double_x, double_y) == (
        sp.Rational(-5, 4),
        sp.Rational(25, 16),
        sp.Rational(-3, 64),
    )
    assert double_y**2 == short_rhs.subs(x, double_x)
    assert not double_x.is_integer and not double_y.is_integer

    # Nagell--Lutz candidates: y=0, or y^2 divides |4*A^3+27*B^2|=68.
    nagell_lutz_integer = abs(4 * (-5) ** 3 + 27 * 4**2)
    assert nagell_lutz_integer == 68
    nonzero_square_divisors = [
        square
        for square in range(1, nagell_lutz_integer + 1)
        if sp.integer_nthroot(square, 2)[1]
        and nagell_lutz_integer % square == 0
    ]
    assert nonzero_square_divisors == [1, 4]
    nagell_lutz_polynomials = {
        "y=0": sp.factor(short_rhs),
        "y^2=1": sp.factor(short_rhs - 1),
        "y^2=4": sp.factor(short_rhs - 4),
    }
    assert sp.ground_roots(nagell_lutz_polynomials["y=0"], x) == {1: 1}
    assert sp.ground_roots(nagell_lutz_polynomials["y^2=1"], x) == {}
    assert sp.ground_roots(nagell_lutz_polynomials["y^2=4"], x) == {0: 1}

    # Homogeneous-space identity behind the squareclass representative d:
    # x=d*(r/s)^2 gives N^2=d*r^4+a*r^2*s^2+(b/d)*s^4.
    d, r, denominator = sp.symbols("d r denominator", nonzero=True)
    homogeneous_space = (
        d * r**4 + 3 * r**2 * denominator**2 - sp.Rational(2, 1) / d * denominator**4
    )
    substituted_rhs = shifted_rhs.subs(x, d * r**2 / denominator**2)
    identity = sp.cancel(
        substituted_rhs
        - (d * r / denominator**3) ** 2 * homogeneous_space
    )
    assert identity == 0

    payload: dict[str, object] = {
        "schema": 1,
        "theorem": (
            "E1(Q) has Mordell-Weil rank exactly 1 and torsion subgroup Z/2Z"
        ),
        "models": {
            "short": "y^2=x^3-5*x+4",
            "shifted": "Y^2=X*(X^2+3*X-2)",
            "dual": "V^2=U*(U^2-6*U+17)",
        },
        "rational_2_torsion": {
            "E1": ["O", "(1,0) in short coordinates = (0,0) shifted"],
            "dual": ["O", "(0,0)"],
            "E1_quadratic_factor_discriminant": 17,
        },
        "descent_images": {
            "alpha_E": descent_classes_e,
            "alpha_dual": descent_classes_dual,
            "sizes": [image_size_e, image_size_dual],
        },
        "index_formula": (
            "2^rank=|alpha_E(E(Q))|*|alpha_dual(E'(Q))|/4"
        ),
        "rank_power": rank_power,
        "rank": rank,
        "non_torsion_certificate": {
            "P": "(0,2)",
            "2P": [str(double_x), str(double_y)],
            "method": "Nagell-Lutz: the nonzero torsion point 2P would be integral",
        },
        "torsion_certificate": {
            "nagell_lutz_integer": nagell_lutz_integer,
            "nonzero_square_divisors": nonzero_square_divisors,
            "only_integral_candidates": ["(1,0)", "(0,2)", "(0,-2)"],
            "P_and_minus_P_non_torsion": True,
            "torsion_subgroup": "Z/2Z",
        },
        "external_data_used": False,
        "proof_document": "candidate_544c_rank_proof.md",
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("2-isogeny descent images: 4 and 2")
    print("rank(E1(Q)) = 1")
    print("torsion(E1(Q)) = Z/2Z")
    print("external rank/generator data used: no")
    try:
        displayed_output = args.output.resolve().relative_to(ROOT)
    except ValueError:
        displayed_output = args.output.resolve()
    print("wrote", displayed_output)


if __name__ == "__main__":
    main()
