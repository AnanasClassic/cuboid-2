#!/usr/bin/env python3
"""Exact offline checks for the candidate isogeny class 544.c.

The certified Frobenius fingerprint singles out the two short models

    E1: y^2 = x^3 - 5*x + 4,
    E2: y^2 = x^3 + 5*x + 18

as an offline candidate.  This script checks every certified trace directly
and certifies an explicit rational 2-isogeny and its dual.  These checks do
*not* identify the repository's abstract quotient E with either model.  Rank
and generator data obtained from LMFDB remain external candidate metadata.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
FINGERPRINT = Path(__file__).with_name("frobenius_fingerprint.json")
DEFAULT_OUTPUT = Path(__file__).with_name("candidate_544c_check.json")

CERTIFIED_TRACES = {
    7: -2,
    11: -4,
    13: 2,
    19: -4,
    23: -6,
    29: 8,
    31: 2,
    37: 4,
    41: -2,
    53: -6,
    59: -4,
    61: 4,
    67: -4,
    71: 6,
    73: -6,
    79: 10,
    83: 12,
    89: -10,
    97: -10,
}


def elliptic_trace(p: int, coefficient_a: int, coefficient_b: int) -> int:
    """Return a_p by an exact Legendre-symbol point count."""

    discriminant = -16 * (4 * coefficient_a**3 + 27 * coefficient_b**2)
    assert discriminant % p
    character_sum = 0
    for x_value in range(p):
        value = (x_value**3 + coefficient_a * x_value + coefficient_b) % p
        if value:
            legendre = pow(value, (p - 1) // 2, p)
            assert legendre in (1, p - 1)
            character_sum += 1 if legendre == 1 else -1
    # #E(F_p)=p+1+sum_x chi(f(x)), hence a_p=-sum_x chi(f(x)).
    return -character_sum


def reduce_mod_curve(
    expression: sp.Expr,
    ordinate: sp.Symbol,
    right_hand_side: sp.Expr,
) -> sp.Expr:
    """Reduce the numerator of a rational identity modulo y^2=f(x)."""

    numerator = sp.together(expression).as_numer_denom()[0]
    remainder = sp.rem(
        sp.Poly(sp.expand(numerator), ordinate),
        sp.Poly(ordinate**2 - right_hand_side, ordinate),
    )
    return sp.factor(remainder.as_expr())


def isogeny_certificate() -> dict[str, object]:
    x, y, u, v = sp.symbols("x y u v")

    # Short models and shifts to put the rational 2-torsion at (0,0):
    # x_short=x+1 on E1 and u_short=u-2 on E2.
    e1_short = x**3 - 5 * x + 4
    e2_short = u**3 + 5 * u + 18
    e1 = x**3 + 3 * x**2 - 2 * x
    e2 = u**3 - 6 * u**2 + 17 * u
    assert sp.expand(e1_short.subs(x, x + 1) - e1) == 0
    assert sp.expand(e2_short.subs(u, u - 2) - e2) == 0
    assert sp.factor(e1) == x * (x**2 + 3 * x - 2)
    assert sp.factor(e2) == u * (u**2 - 6 * u + 17)

    # Standard 2-isogeny for y^2=x^3+a*x^2+b*x:
    # (x,y) |-> (y^2/x^2, y*(b-x^2)/x^2).
    phi_u = sp.cancel(y**2 / x**2)
    phi_v = sp.cancel(y * (-2 - x**2) / x**2)
    assert reduce_mod_curve(phi_v**2 - e2.subs(u, phi_u), y, e1) == 0

    # Applying the same construction to E2 gives a curve
    # v^2=u^3+12*u^2-32*u, which maps back to E1 by (x,y)=(u/4,v/8).
    dual_x = sp.cancel(v**2 / (4 * u**2))
    dual_y = sp.cancel(v * (17 - u**2) / (8 * u**2))
    assert reduce_mod_curve(dual_y**2 - e1.subs(x, dual_x), v, e2) == 0

    # Exact duality: both compositions equal the duplication morphism.
    phi_then_dual_x = sp.cancel(
        dual_x.subs({u: phi_u, v: phi_v}, simultaneous=True)
    )
    phi_then_dual_y = sp.cancel(
        dual_y.subs({u: phi_u, v: phi_v}, simultaneous=True)
    )
    e1_slope = (3 * x**2 + 6 * x - 2) / (2 * y)
    e1_double_x = sp.cancel(e1_slope**2 - 3 - 2 * x)
    e1_double_y = sp.cancel(-y + e1_slope * (x - e1_double_x))
    assert reduce_mod_curve(phi_then_dual_x - e1_double_x, y, e1) == 0
    assert reduce_mod_curve(phi_then_dual_y - e1_double_y, y, e1) == 0

    dual_then_phi_u = sp.cancel(
        phi_u.subs({x: dual_x, y: dual_y}, simultaneous=True)
    )
    dual_then_phi_v = sp.cancel(
        phi_v.subs({x: dual_x, y: dual_y}, simultaneous=True)
    )
    e2_slope = (3 * u**2 - 12 * u + 17) / (2 * v)
    e2_double_u = sp.cancel(e2_slope**2 + 6 - 2 * u)
    e2_double_v = sp.cancel(-v + e2_slope * (u - e2_double_u))
    assert reduce_mod_curve(dual_then_phi_u - e2_double_u, v, e2) == 0
    assert reduce_mod_curve(dual_then_phi_v - e2_double_v, v, e2) == 0

    # Translation back to the two short models.  The exact rational point
    # check is useful, but it is not a proof that the point generates E(Q).
    phi_short_x = sp.cancel(phi_u.subs({x: x - 1, y: y}) - 2)
    phi_short_y = sp.cancel(phi_v.subs({x: x - 1, y: y}))
    dual_short_x = sp.cancel(dual_x.subs({u: u + 2, v: v}) + 1)
    dual_short_y = sp.cancel(dual_y.subs({u: u + 2, v: v}))
    assert phi_short_x.subs({x: 0, y: 2}) == 2
    assert phi_short_y.subs({x: 0, y: 2}) == -6
    assert e1_short.subs(x, 0) == 2**2
    assert e2_short.subs(u, 2) == (-6) ** 2

    return {
        "shifted_models": {
            "E1": "Y^2=X^3+3*X^2-2*X, with X=x-1 and Y=y",
            "E2": "V^2=U^3-6*U^2+17*U, with U=u+2 and V=v",
        },
        "kernels": {
            "phi": "{O,(X,Y)=(0,0)} = {O,(x,y)=(1,0)}",
            "dual": "{O,(U,V)=(0,0)} = {O,(u,v)=(-2,0)}",
        },
        "phi_shifted": {
            "U": str(phi_u),
            "V": str(phi_v),
        },
        "dual_shifted": {
            "X": str(dual_x),
            "Y": str(dual_y),
        },
        "phi_short": {
            "u": str(phi_short_x),
            "v": str(phi_short_y),
        },
        "dual_short": {
            "x": str(dual_short_x),
            "y": str(dual_short_y),
        },
        "duality": ["dual(phi(P))=[2]P on E1", "phi(dual(Q))=[2]Q on E2"],
        "checked_rational_points": {
            "E1_point": "(0,2)",
            "phi_image_on_E2": "(2,-6)",
        },
    }


def verify() -> dict[str, object]:
    fingerprint = json.loads(FINGERPRINT.read_text(encoding="utf-8"))
    fingerprint_traces = {
        int(record["p"]): int(record["trace"])
        for record in fingerprint["traces"]
    }
    assert fingerprint_traces == CERTIFIED_TRACES

    models = {
        "E1": {"equation": "y^2=x^3-5*x+4", "A": -5, "B": 4},
        "E2": {"equation": "y^2=x^3+5*x+18", "A": 5, "B": 18},
    }
    trace_rows = []
    for prime, certified_trace in CERTIFIED_TRACES.items():
        traces = {
            name: elliptic_trace(prime, model["A"], model["B"])
            for name, model in models.items()
        }
        assert traces == {"E1": certified_trace, "E2": certified_trace}
        trace_rows.append(
            {
                "p": prime,
                "certified_quotient_trace": certified_trace,
                "E1_trace": traces["E1"],
                "E2_trace": traces["E2"],
            }
        )

    discriminants = {
        name: -16 * (4 * model["A"] ** 3 + 27 * model["B"] ** 2)
        for name, model in models.items()
    }
    assert discriminants == {"E1": 1088, "E2": -147968}

    payload: dict[str, object] = {
        "schema": 1,
        "candidate_class": "544.c",
        "models": models,
        "displayed_model_discriminants": discriminants,
        "certified_trace_source_checksum": fingerprint["sha256_without_checksum"],
        "trace_matches": trace_rows,
        "all_certified_traces_match_both_models": True,
        "isogeny_certificate": isogeny_certificate(),
        "logical_status": {
            "proved_offline": [
                "both displayed models have every certified quotient trace",
                "the displayed models are linked by the explicit rational 2-isogeny",
                "the displayed dual compositions are multiplication by 2",
            ],
            "not_proved": [
                "the abstract reciprocal quotient E is isomorphic or isogenous to 544.c",
                "the Mordell-Weil rank of the abstract quotient E",
                "completeness of any proposed generator set for E(Q)",
            ],
        },
        "external_candidate_metadata_only": {
            "source": "LMFDB candidate lookup, not consumed by this offline proof",
            "reported_isogeny_class": "544.c",
            "reported_rank": 1,
            "reported_generators_status": (
                "External metadata only; no database generator claim is "
                "imported as a theorem or used in this certificate."
            ),
            "rational_points_checked_offline_not_generator_certificates": {
                "E1": "(0,2)",
                "E2": "(2,-6)=phi(0,2)",
            },
            "warning": (
                "Database rank/generator metadata is candidate guidance only. "
                "It cannot be transported to the quotient until an exact "
                "birational map or another proof of identification is supplied."
            ),
        },
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
    print("all 19 certified traces match E1 and E2: OK")
    print("explicit 2-isogeny, dual, and both [2] compositions: OK")
    print("quotient identification and rank deliberately remain unproved")
    try:
        displayed_output = args.output.resolve().relative_to(ROOT)
    except ValueError:
        displayed_output = args.output.resolve()
    print("wrote", displayed_output)


if __name__ == "__main__":
    main()
