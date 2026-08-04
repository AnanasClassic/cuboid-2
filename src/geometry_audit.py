#!/usr/bin/env python3
"""Exact audit of the two-root curve and its reciprocal quotients.

This script uses only exact SymPy polynomial arithmetic.  It does not attempt
to compute a Weierstrass model or a Mordell--Weil group.  Its purpose is to
certify the identities and local Newton data used in the Riemann--Hurwitz
calculations documented by ``main()``.
"""

from __future__ import annotations

import sympy as sp


s, x, a, b, d, y, c = sp.symbols("s x a b d y c")

c4 = (2 + s) * (3 - 2 * s)
c3 = 1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4
c2 = -s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4)
c1 = -s**3 * (1 + 2 * s) * (-2 + 3 * s)
c0 = -s**5

P = sp.expand(x**5 + c4 * x**4 + c3 * x**3 + c2 * x**2 + c1 * x + c0)


def homogeneous_part(poly: sp.Expr, variables: tuple[sp.Symbol, ...], degree: int) -> sp.Expr:
    """Return the indicated ordinary-total-degree homogeneous part."""

    result = 0
    for powers, coeff in sp.Poly(sp.expand(poly), *variables).terms():
        if sum(powers) == degree:
            monomial = coeff
            for variable, power in zip(variables, powers, strict=True):
                monomial *= variable**power
            result += monomial
    return sp.expand(result)


def minimum_weight_part(
    poly: sp.Expr,
    variables: tuple[sp.Symbol, ...],
    weights: tuple[int, ...],
) -> tuple[int, sp.Expr]:
    """Return the minimum weighted degree and corresponding initial form."""

    terms = sp.Poly(sp.expand(poly), *variables).terms()
    minimum = min(sum(power * weight for power, weight in zip(powers, weights, strict=True))
                  for powers, _ in terms)
    result = 0
    for powers, coeff in terms:
        if sum(power * weight for power, weight in zip(powers, weights, strict=True)) == minimum:
            monomial = coeff
            for variable, power in zip(variables, powers, strict=True):
                monomial *= variable**power
            result += monomial
    return minimum, sp.expand(result)


def main() -> None:
    # Reciprocal identity and the induced involution on quadratic factors.
    reciprocal = sp.together(P + s**5 * x**5 * P.subs({s: 1 / s, x: 1 / x}, simultaneous=True))
    assert sp.cancel(reciprocal) == 0

    divisor = x**2 + a * x + b
    remainder = sp.Poly(sp.rem(P, divisor, x), x)
    r1 = sp.expand(remainder.coeff_monomial(x))
    r0 = sp.expand(remainder.coeff_monomial(1))

    u = -3 * a**2 + 2 * a * c4 - c3
    v = a**4 - c4 * a**3 + c3 * a**2 - c2 * a + c1
    m = c4 - 2 * a
    n = a**3 - c4 * a**2 + c3 * a - c2
    assert sp.expand(r1 - (b**2 + u * b + v)) == 0
    assert sp.expand(r0 - (m * b**2 + n * b - s**5)) == 0

    # On r1=0, r0-m*r1 = L*b-C.  Thus b=C/L off L=0.
    L = sp.expand(n - m * u)
    C = sp.expand(m * v + s**5)
    assert sp.expand(r0 - m * r1 - (L * b - C)) == 0
    F = sp.expand(C**2 + u * L * C + v * L**2)
    assert sp.expand(F - sp.resultant(r1, r0, b)) == 0
    # This rational smooth point descends to a rational point on the
    # genus-one reciprocal quotient, making that quotient elliptic.
    point_061 = {s: 0, a: 6}
    assert F.subs(point_061) == 0
    assert (L.subs(point_061), C.subs(point_061)) == (-216, -216)
    assert sp.diff(F, a).subs(point_061) == -216

    discriminant = sp.factor(sp.discriminant(P, x))
    sextic = s**6 + 15 * s**5 - 1585 * s**4 + 3052 * s**3 - 1585 * s**2 + 15 * s + 1
    expected_discriminant = 2**11 * s**9 * (s - 1)**12 * (s + 1)**4 * sextic
    assert sp.expand(discriminant - expected_discriminant) == 0
    assert sp.discriminant(sextic, s) == -120976582094426834375000000
    assert all(sextic.subs(s, value) != 0 for value in (0, 1, -1))

    # s=1: one simple root near x=1 and four analytic roots near x=-1.
    # With s=1+d and x=-1+y, the degree-four tangent cone has four
    # distinct slopes y=c*d.
    at_one = sp.expand(P.subs({s: 1 + d, x: -1 + y}, simultaneous=True))
    tangent_one = homogeneous_part(at_one, (d, y), 4)
    expected_one = -2 * (y**4 - 8 * d**2 * y**2 - 12 * d**3 * y - 4 * d**4)
    assert sp.expand(tangent_one - expected_one) == 0
    slope_quartic = c**4 - 8 * c**2 - 12 * c - 4
    assert sp.discriminant(slope_quartic, c) == -11008  # -2^8*43, hence separable.
    assert sp.factor(P.subs(s, 1)) == (x - 1) * (x + 1) ** 4

    # s=-1: x=-1 is a fivefold root and y^5+64*d is the first Newton face.
    at_minus_one = sp.expand(P.subs({s: -1 + d, x: -1 + y}, simultaneous=True))
    weight_minus_one, initial_minus_one = minimum_weight_part(at_minus_one, (d, y), (5, 1))
    assert weight_minus_one == 5
    assert sp.expand(initial_minus_one - (y**5 + 64 * d)) == 0
    assert sp.factor(P.subs(s, -1)) == (x + 1) ** 5

    # s=0: two roots stay nonzero, one small root is analytic, and the
    # remaining two small roots have x=s^2(1 +/- 4*sqrt(s)+...).
    assert sp.factor(P.subs(s, 0)) == x**3 * (x**2 + 6 * x + 1)
    near_s_squared = sp.expand(P.subs(x, s**2 * (1 + y)))
    weight_zero, initial_zero = minimum_weight_part(near_s_squared, (s, y), (2, 1))
    assert weight_zero == 12
    assert sp.expand(initial_zero - s**5 * (16 * s - y**2)) == 0

    # Riemann--Hurwitz for the degree-10 two-subset resolvent C -> P^1_s.
    # Six simple discriminant roots and s=0/infinity have transposition
    # inertia (contribution 3 each); s=-1 has two 5-cycles (contribution 8).
    ramification_c = 6 * 3 + 3 + 8 + 3
    genus_c = 1 + (-2 * 10 + ramification_c) // 2
    assert ramification_c == 32 and genus_c == 7

    # The reciprocal involution fixes ten normalization points over s=1 and
    # two over s=-1.  Its quotient therefore has genus one.
    reciprocal_fixed = 10 + 2
    quotient_genus = (2 * genus_c - 2 - reciprocal_fixed) // 4 + 1
    assert quotient_genus == 1

    # Adjoining z with z^2=s branches at four odd-order zeros of s and,
    # reciprocally, four odd-order poles.  The square pullback has genus 17.
    square_branch_points = 4 + 4
    square_genus = 2 * genus_c - 1 + square_branch_points // 2
    assert square_genus == 17

    # The two lifts z -> +/- 1/z have 20 and 4 fixed points, respectively.
    quotient_plus = (2 * square_genus - 2 - 20) // 4 + 1
    quotient_minus = (2 * square_genus - 2 - 4) // 4 + 1
    assert (quotient_plus, quotient_minus) == (4, 8)

    print("reciprocal identity: OK")
    print("remainder/resultant identities: OK")
    print("disc_x(P_s) =", discriminant)
    print("local Newton data at s=1,-1,0: OK")
    print("genus(C), genus(C/<tau>) =", genus_c, quotient_genus)
    print("square-pullback genus and lifted-quotient genera =", square_genus, quotient_plus, quotient_minus)


if __name__ == "__main__":
    main()
