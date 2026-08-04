#!/usr/bin/env python3
"""Exact diagnostics for normalizing the singular elliptic plane model H(q,A).

This does not claim that the discriminant quartic is birational to H.  In
fact, the final assertion records a rational point of H that does not lift to
that quartic, preventing precisely that tempting but false identification.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
q, A = sp.symbols("q A")


def model() -> sp.Expr:
    artifact = json.loads((ROOT / "artifacts/genus4_quotient.json").read_text())
    return sp.expand(
        sum(
            int(term["coefficient"])
            * q ** term["powers"][0]
            * A ** term["powers"][1]
            for term in artifact["elliptic_plane_model"]["terms"]
        )
    )


def initial_total(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> tuple[int, sp.Expr]:
    terms = sp.Poly(poly, *variables).terms()
    multiplicity = min(sum(powers) for powers, _ in terms)
    initial = 0
    for powers, coefficient in terms:
        if sum(powers) == multiplicity:
            monomial = coefficient
            for variable, power in zip(variables, powers, strict=True):
                monomial *= variable**power
            initial += monomial
    return multiplicity, sp.expand(initial)


def main() -> None:
    H = model()
    cubic = 43 * q**3 + 11870 * q**2 - 50684 * q + 51496
    degree_15 = (
        q**15 + 998*q**14 + 328436*q**13 + 33879288*q**12
        - 630955568*q**11 - 64836634912*q**10 - 1365887807936*q**9
        - 13883961380480*q**8 - 77464295435520*q**7
        - 230515638316544*q**6 - 255656791073792*q**5
        + 398271926396928*q**4 + 1443280969068544*q**3
        + 1224232979505152*q**2 - 174483284901888*q
        - 495592577400832
    )
    discriminant = sp.factor(sp.discriminant(H, A))
    expected_without_constant = (
        (q - 2)**27 * (q + 2)**20 * (3*q + 10)**4
        * (5*q**2 + 28*q + 52)**12 * cubic**3 * degree_15**2
    )
    quotient = sp.cancel(discriminant / expected_without_constant)
    assert quotient.is_Integer and quotient != 0

    assert sp.factor(H.subs(q, -2)) == 2**16 * (A - 2)**10
    assert sp.factor(H.subs(q, 2)) == 2**27 * A**3 * (A - 6) * (A**2 - 12*A + 4)**3
    assert H.subs({q: 6, A: sp.Rational(6, 7)}) == 0
    assert (sp.diff(H, q).subs({q: 6, A: sp.Rational(6, 7)}),
            sp.diff(H, A).subs({q: 6, A: sp.Rational(6, 7)})) != (0, 0)

    # Rational affine singularities and tangent cones.
    u, v = sp.symbols("u v")
    multiplicity, tangent = initial_total(H.subs({q: -2 + u, A: 2 + v}), (u, v))
    assert multiplicity == 2 and sp.factor(tangent) == 2**40 * u**2
    multiplicity, tangent = initial_total(H.subs({q: 2 + u, A: v}), (u, v))
    assert multiplicity == 3 and sp.factor(tangent) == -3 * 2**28 * v * (u + 8*v)**2

    # Total-degree projective closure: the two rational points at infinity have
    # multiplicities 10 and 8.  The first has a sixfold rational tangent A=2.
    degree = sp.Poly(H, q, A).total_degree()
    Q, Y, Z = sp.symbols("Q Y Z")
    homogeneous = sum(
        coefficient * Q**powers[0] * Y**powers[1] * Z**(degree - sum(powers))
        for powers, coefficient in sp.Poly(H, q, A).terms()
    )
    mult_q, tangent_q = initial_total(homogeneous.subs(Q, 1), (Y, Z))
    mult_a, _ = initial_total(homogeneous.subs(Y, 1), (Q, Z))
    assert (mult_q, mult_a) == (10, 8)
    assert sp.factor(tangent_q).has((Y - 2*Z)**6)

    # First two weighted stages at (-2,2).  Put u=v^5(-1/4096+v*y).
    y = sp.symbols("y")
    local = sp.expand(H.subs({q: -2 + v**5*(-sp.Rational(1, 4096) + v*y), A: 2 + v}))
    local_poly = sp.Poly(local, v, y)
    v_order = min(powers[0] for powers, _ in local_poly.terms())
    initial_y = sum(
        coefficient * y**powers[1]
        for powers, coefficient in local_poly.terms()
        if powers[0] == v_order
    )
    assert v_order == 12
    assert sp.expand(initial_y - 4096 * (2**28*y**2 - 147456*y + 19)) == 0
    assert sp.factor(sp.discriminant(initial_y, y)) == 2**52 * 5

    # The squarefree discriminant cover is an explicit genus-one quartic, but
    # it is not H with q preserved: the smooth H-point q=6 gives a nonsquare.
    quartic_value_at_6 = ((q - 2) * cubic).subs(q, 6)
    assert quartic_value_at_6 == 736000
    integer_value = int(quartic_value_at_6)
    assert math.isqrt(integer_value) ** 2 != integer_value

    print("Disc_A(H) squarefree part = (q-2)*(43q^3+11870q^2-50684q+51496)")
    print("rational singularity and infinity tangent data: OK")
    print("(-2,2) second weighted split is over Q(sqrt(5)): OK")
    print("discriminant quartic is not H with q preserved: certified by q=6")


if __name__ == "__main__":
    main()
