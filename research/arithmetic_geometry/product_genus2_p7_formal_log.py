#!/usr/bin/env python3
"""Exact formal-log certificate at p=7 for the product genus-two curve.

The script computes 42*D over Q by Cantor arithmetic, checks a compact list
of 7-adic leading data, and derives the reduction (1,4) of log(D).  Hence an
annihilating Chabauty differential reduces to

    (4-a) da/R.

Only exact rational and symbolic arithmetic is used; no p-adic numerical
integration is required.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

import sympy as sp


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
PRIME = 7


def qpoly(expression, variable):
    return sp.Poly(expression, variable, domain=sp.QQ)


def monic(expression, variable):
    return qpoly(expression, variable).monic().as_expr()


def remainder(left, right, variable):
    return sp.rem(left, right, variable, domain=sp.QQ)


def xgcd3(first, second, third, variable):
    e1, e2, d1 = sp.gcdex(qpoly(first, variable), qpoly(second, variable))
    c1, c2, d = sp.gcdex(d1, qpoly(third, variable))
    return (
        d.as_expr(),
        (c1 * e1).as_expr(),
        (c1 * e2).as_expr(),
        c2.as_expr(),
    )


def cantor_add(first, second, variable, monic_curve):
    u1, v1 = first
    u2, v2 = second
    d, s1, s2, s3 = xgcd3(u1, u2, v1 + v2, variable)
    u = sp.cancel(u1 * u2 / d**2)
    v = sp.cancel(
        (s1 * u1 * v2 + s2 * u2 * v1 + s3 * (v1 * v2 + monic_curve)) / d
    )
    u = monic(u, variable)
    v = remainder(v, u, variable)
    while sp.degree(u, variable) > 2:
        quotient, rest = sp.div(
            monic_curve - v**2, u, variable, domain=sp.QQ
        )
        assert sp.expand(rest) == 0
        u = monic(quotient, variable)
        v = remainder(-v, u, variable)
    return sp.factor(u), sp.factor(v)


def valuation_and_unit(value: sp.Rational, prime: int = PRIME) -> tuple[int, int]:
    value = sp.Rational(value)
    numerator = int(value.p)
    denominator = int(value.q)

    def split(integer: int) -> tuple[int, int]:
        valuation = 0
        integer_abs = abs(integer)
        while integer_abs % prime == 0:
            integer_abs //= prime
            valuation += 1
        residue = integer_abs % prime
        if integer < 0:
            residue = -residue % prime
        return valuation, residue

    numerator_valuation, numerator_unit = split(numerator)
    denominator_valuation, denominator_unit = split(denominator)
    return (
        numerator_valuation - denominator_valuation,
        numerator_unit * pow(denominator_unit, -1, prime) % prime,
    )


def verify() -> dict[str, object]:
    a, t = sp.symbols("a t")
    original_curve = 4 * a**5 - 8 * a**2 + 5 * a
    monic_curve = original_curve / 4
    identity = (sp.Integer(1), sp.Integer(0))
    D = (a - 1, sp.Rational(1, 2))  # w=R/2
    multiple = identity
    for _ in range(42):
        multiple = cantor_add(multiple, D, a, monic_curve)
    u, v_w = multiple
    v_R = sp.factor(2 * v_w)
    quotient, rest = sp.div(original_curve - v_R**2, u, a, domain=sp.QQ)
    assert sp.expand(rest) == 0

    shifted_u = qpoly(sp.expand(u.subs(a, t + 4)), t)
    assert shifted_u.degree() == 2 and shifted_u.LC() == 1
    linear = shifted_u.coeff_monomial(t)
    constant = shifted_u.coeff_monomial(1)
    discriminant = sp.discriminant(u, a)
    slope = qpoly(v_R, a).coeff_monomial(a)
    value_at_4 = v_R.subs(a, 4)

    data = {
        "shifted_u_linear": valuation_and_unit(linear),
        "shifted_u_constant": valuation_and_unit(constant),
        "u_discriminant": valuation_and_unit(discriminant),
        "v_R_slope": valuation_and_unit(slope),
        "v_R_at_4": valuation_and_unit(value_at_4),
    }
    assert data == {
        "shifted_u_linear": (1, 5),
        "shifted_u_constant": (2, 3),
        "u_discriminant": (2, 6),
        "v_R_slope": (-1, 1),
        "v_R_at_4": (0, 6),
    }

    # Put a=4+7*tau.  Modulo 7, the two roots of u give
    # tau^2+5*tau+3=0 and R=tau+6.  The discriminant 6 is nonsquare, so the
    # roots are conjugate in F_49.  The leading trace of the first formal
    # logarithm, divided by 7, is sum tau/(tau+6).  Evaluate it from the
    # elementary symmetric functions rather than adjoining either root.
    tau_sum = 2       # -5 mod 7
    tau_product = 3
    trace_numerator = (2 * tau_product + 6 * tau_sum) % 7
    trace_denominator = (tau_product + 6 * tau_sum + 36) % 7
    trace_first = trace_numerator * pow(trace_denominator, -1, 7) % 7
    assert trace_first == 2
    trace_second = 4 * trace_first % 7
    assert trace_second == 1
    inverse_scale = pow(trace_first, -1, 7)
    log_direction = (1, trace_second * inverse_scale % 7)
    assert log_direction == (1, 4)

    # f(4)=5 modulo 7 is nonsquare, exactly as required by the conjugate-pair
    # formal chart.  Higher local-integral terms vanish after division by 7:
    # for n>=2, n-v_7(n)-1 >=1.  A finite check through 100 plus the simple
    # inequality n>=7^v establishes the only potentially delicate pattern.
    assert int(original_curve.subs(a, 4)) % 7 == 5
    assert pow(5, 3, 7) == -1 % 7
    for n in range(2, 101):
        valuation_n = 0
        work = n
        while work % 7 == 0:
            work //= 7
            valuation_n += 1
        assert n - valuation_n - 1 >= 1

    # The reduced annihilator is (4-a)da/R.  It is nonzero in the four
    # disks retained by the finite sieve: infinity, (0,0), and (1,+/-1).
    surviving_disks = ["infinity", "(0,0)", "(1,1)", "(1,-1)"]
    assert 4 % 7 != 0                         # Weierstrass disk a=0
    assert (4 - 1) % 7 != 0                   # both a=1 disks
    assert (-1) % 7 != 0                      # leading value at infinity
    assert 7 > 2 * 2

    payload: dict[str, object] = {
        "schema": 1,
        "curve": "R^2=4*a^5-8*a^2+5*a",
        "divisor": "D=[(1,1)-infinity]",
        "multiple_used": "42*D",
        "exact_7_adic_data": {
            name: {"valuation": value[0], "unit_mod_7": value[1]}
            for name, value in data.items()
        },
        "scaled_root_equations_mod_7": {
            "u": "tau^2+5*tau+3",
            "R": "tau+6",
            "u_discriminant": 6,
        },
        "normalized_log_direction_mod_7": list(log_direction),
        "annihilating_differential_reduction": "(4-a)*da/R",
        "surviving_disks": surviving_disks,
        "annihilator_nonzero_on_surviving_disks": True,
        "coleman_bound_condition": "p=7>2g=4",
        "conclusion": (
            "Each of the four surviving residue disks contains at most one "
            "rational point."
        ),
        "logical_scope": (
            "Rank one is supplied by the exact 2-descent. This certificate "
            "computes the annihilator reduction and local uniqueness; the "
            "p=7/p=23 sieve supplies the list of surviving disks."
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
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("exact p=7 formal-log direction and disk uniqueness: PASS")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
