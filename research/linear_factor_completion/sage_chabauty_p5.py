#!/usr/bin/env sage -python
"""Independent Sage certificate for the local part of the 1+4 proof.

This script does not call Magma.  It proves the following exact conditional
statement for

    C : w^2 = t^5 + 21*t^4 + 26*t^3 + 10*t^2 + 5*t + 1.

If ``rank J_C(Q) <= 1``, then

    C(Q) = {infinity, (-1,0), (0,+/-1), (1,+/-8)}.

The rank hypothesis is deliberately *not* hidden in the script.  Sage 10.9
has Coleman integration for hyperelliptic curves but no genus-2 2-Selmer
implementation.  The published Magma ``RankBound(J)=1`` and the independently
computed LMFDB record 11008.a.176128.1 supply that remaining input.

The certificate is especially short at p=5: C(F_5) has exactly six points,
and the six known rational points reduce bijectively to them.  The script
computes the Coleman annihilator from the provably infinite divisor
[(0,1)-infinity] and checks that its reduction has no zero at any of the six
points.  Hence the Coleman function has at most one zero in every residue
disc, while every disc already contains one of the known rational points.

Run with SageMath 10.9 (the pinned repository CI image) as

    sage -python research/linear_factor_completion/sage_chabauty_p5.py
"""

from __future__ import annotations

import platform

from sage.all import GF, HyperellipticCurve, PolynomialRing, Qp, QQ, gcd, version


P = 5
PRECISION = 24


def cert(label: str, value) -> None:
    print(f"CERT {label} = {value}", flush=True)


def curve_cardinality_over_prime_power(f, prime: int, degree: int) -> int:
    """Return #C(F_(prime^degree)) by exact point enumeration."""

    if degree == 1:
        field = GF(prime)
    else:
        field = GF(prime**degree, name=f"a{prime}_{degree}")
    ring = PolynomialRing(field, "x")
    curve = HyperellipticCurve(ring(f))
    return len(curve.points())


def jacobian_cardinality(f, prime: int) -> int:
    """Recover #J(F_p) from #C(F_p) and #C(F_(p^2))."""

    n1 = curve_cardinality_over_prime_power(f, prime, 1)
    n2 = curve_cardinality_over_prime_power(f, prime, 2)
    a1 = prime + 1 - n1
    # If L_p(T)=1-a1*T+a2*T^2-p*a1*T^3+p^2*T^4, then
    # #C(F_(p^2))=p^2+1-(a1^2-2*a2).
    numerator = n2 - prime**2 - 1 + a1**2
    assert numerator % 2 == 0
    a2 = numerator // 2
    return 1 - a1 + a2 - prime * a1 + prime**2


def main() -> None:
    cert("sage_version", version())
    cert("python_version", platform.python_version())

    rational_ring = PolynomialRing(QQ, "t")
    t = rational_ring.gen()
    f = t**5 + 21 * t**4 + 26 * t**3 + 10 * t**2 + 5 * t + 1
    quartic = t**4 + 20 * t**3 + 6 * t**2 + 4 * t + 1
    assert f == (t + 1) * quartic
    assert quartic.is_irreducible()
    assert f.discriminant() == -(2**24) * 43
    cert("curve", f"w^2={f}")
    cert("good_reduction_prime", P)

    # Exact isomorphism to the simplified model of LMFDB 11008.a.176128.1.
    # t=-(2X+1)/(2X-1), Y=(X-1/2)^3*w.
    function_field = rational_ring.fraction_field()
    X = function_field.gen()
    t_of_X = -(2 * X + 1) / (2 * X - 1)
    simplified = 16 * X**5 + 8 * X**4 - 8 * X**3 - 4 * X**2 + 1
    assert ((X - QQ(1) / 2) ** 6 * f(t_of_X) - simplified).numerator() == 0
    cert("lmfdb_model", "Y^2=16*X^5+8*X^4-8*X^3-4*X^2+1")
    cert("lmfdb_label", "11008.a.176128.1")

    curve_q = HyperellipticCurve(f)
    infinity_q = curve_q(QQ(1), QQ(0), QQ(0))
    generator_point_q = curve_q(QQ(0), QQ(1), QQ(1))
    known_q = [
        infinity_q,
        curve_q(QQ(-1), QQ(0), QQ(1)),
        curve_q(QQ(0), QQ(1), QQ(1)),
        curve_q(QQ(0), QQ(-1), QQ(1)),
        curve_q(QQ(1), QQ(8), QQ(1)),
        curve_q(QQ(1), QQ(-8), QQ(1)),
    ]
    assert len(set(known_q)) == 6

    # The rational torsion injects into both good reductions.  The exact
    # orders 22 and 28 therefore bound it by gcd(22,28)=2.
    order_j3 = jacobian_cardinality(f, 3)
    order_j5 = jacobian_cardinality(f, 5)
    assert order_j3 == 22
    assert order_j5 == 28
    assert gcd(order_j3, order_j5) == 2
    jacobian_q = curve_q.jacobian()
    jacobian_points_q = jacobian_q(QQ)
    divisor = jacobian_points_q(generator_point_q)
    zero_divisor = divisor - divisor
    assert divisor != zero_divisor
    assert 2 * divisor != zero_divisor
    cert("torsion_order_divides", 2)
    cert("generator_divisor_infinite", True)

    # Enumerate C(F_5) independently of any rational-point search.
    field5 = GF(5)
    ring5 = PolynomialRing(field5, "t")
    curve5 = HyperellipticCurve(ring5(f))
    points5 = list(curve5.points())
    assert len(points5) == 6
    finite5 = {
        (field5(point[0] / point[2]), field5(point[1] / point[2] ** 3))
        for point in points5
        if point[2] != 0
    }
    expected_finite5 = {
        (field5(-1), field5(0)),
        (field5(0), field5(1)),
        (field5(0), field5(-1)),
        (field5(1), field5(8)),
        (field5(1), field5(-8)),
    }
    assert finite5 == expected_finite5
    assert sum(point[2] == 0 for point in points5) == 1
    cert("C_F5_cardinality", len(points5))
    cert("C_F5_finite_points", sorted((int(x), int(y)) for x, y in finite5))

    # Verify that the six known rational points reduce bijectively to C(F_5).
    reduced_known = {
        curve5(field5(point[0]), field5(point[1]), field5(point[2]))
        for point in known_q
    }
    assert reduced_known == set(points5)
    cert("known_points_cover_all_residue_discs", True)

    # Coleman log of D=[(0,1)-infinity].  Only the first two entries are the
    # holomorphic basis omega_0=dt/(2w), omega_1=t*dt/(2w).
    padics = Qp(P, PRECISION)
    padic_ring = PolynomialRing(padics, "t")
    curve_p = HyperellipticCurve(padic_ring(f))
    infinity_p = curve_p(padics(1), padics(0), padics(0))
    generator_point_p = curve_p(padics(0), padics(1), padics(1))
    integrals = curve_p.coleman_integrals_on_basis(infinity_p, generator_point_p)
    assert len(integrals) == 4
    integral_0, integral_1 = integrals[0], integrals[1]
    assert integral_0 != 0 or integral_1 != 0

    common_valuation = min(integral_0.valuation(), integral_1.valuation())
    scale = padics(P) ** common_valuation
    coefficient_0 = integral_1 / scale
    coefficient_1 = -integral_0 / scale
    assert min(coefficient_0.valuation(), coefficient_1.valuation()) == 0
    assert coefficient_0.precision_absolute() >= 2
    assert coefficient_1.precision_absolute() >= 2
    residue_0 = field5(coefficient_0.residue())
    residue_1 = field5(coefficient_1.residue())
    cert("coleman_integrals_holomorphic", (integral_0, integral_1))
    cert("coleman_common_valuation", common_valuation)
    cert("annihilator_mod_5", f"({int(residue_0)}+{int(residue_1)}*t)dt/(2w)")

    # eta=(coefficient_0+coefficient_1*t)dt/(2w).  At a finite
    # Weierstrass point dt/(2w)=dw/f'(t), so the same numerator criterion
    # applies.  At infinity omega_0 has a double zero and omega_1 is a unit,
    # so eta is nonzero there exactly when coefficient_1 is nonzero.
    for x_coordinate in (field5(-1), field5(0), field5(1)):
        assert residue_0 + residue_1 * x_coordinate != 0
    assert residue_1 != 0
    cert("annihilator_nonzero_at_all_C_F5_points", True)

    # The exact conclusion uses only the external rank upper bound.  Since D
    # is infinite, rank<=1 makes D span J(Q) tensor Q_5; eta therefore
    # annihilates J(Q).  Every F_5 residue disc has a known rational zero,
    # and eta has unit derivative throughout every disc, so each disc contains
    # at most one rational zero of the Coleman function.
    cert("required_external_rank_upper_bound", 1)
    cert("conditional_rational_point_set", [str(point) for point in known_q])
    cert("status", "PASS_CONDITIONAL_ONLY_ON_RANK_BOUND_1")


if __name__ == "__main__":
    main()
