#!/usr/bin/env python3
"""Exact audit of direct p=3 Chabauty on the genus-three curve.

The curve is

    C3: r^2 = 4*u^8 - 8*u^2 + 5.

The rank-two Chabauty annihilator is pulled back from

    D+: R^2 = 4*a^5 - 8*a^2 + 5*a

under a=u^2, R=u*r.  This certificate computes its coefficient ratio
modulo 27 from exact rational Cantor arithmetic for 11*D, then proves the
Weierstrass reductions of its Coleman primitives in all six residue disks.

Plain Strassmann has one extra Q_3 zero in each affine disk.  A small
integral Mordell--Weil lattice refinement removes exactly those four zeros:
the already needed good-reduction data at 7 prove that the unknown odd index
of D is prime to 3, while the first p=3 logarithm coordinate has valuation
two.  A rational point in an affine disk must therefore satisfy
a-1 in 9*Z_3, where a=u^2.  On that smaller disk the Coleman primitive is
linear modulo 3.  This proves the desired rational-point classification
without the old p=23 sieve or p=7 Coleman calculation.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from math import gcd
import os
from pathlib import Path
import sys

import sympy as sp

ROOT = Path(
    os.environ.get(
        "CUBOID_REPO_ROOT",
        Path(__file__).resolve().parents[2],
    )
).resolve()
sys.path.insert(0, str(ROOT))

from research.arithmetic_geometry.product_genus2_p7_formal_log import (
    cantor_add,
    qpoly,
    valuation_and_unit,
)
from research.arithmetic_geometry.product_genus2_square_sieve import (
    all_reduced_divisors,
    divisor_order,
    point_divisor,
)


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
PRIME = 3


def rational_residue(value: sp.Expr, modulus: int) -> int:
    """Return the exact residue of a rational number with unit denominator."""

    value = sp.Rational(value)
    numerator = int(value.p)
    denominator = int(value.q)
    assert gcd(denominator, modulus) == 1
    return numerator % modulus * pow(denominator % modulus, -1, modulus) % modulus


def valuation(integer: int, prime: int = PRIME) -> int:
    """Return v_p(integer), with the zero case excluded by callers."""

    assert integer
    integer = abs(integer)
    answer = 0
    while integer % prime == 0:
        integer //= prime
        answer += 1
    return answer


def c3_points_mod_3() -> dict[str, object]:
    """Enumerate the six points of C3(F_3) exactly."""

    rows: list[list[object]] = []
    affine_count = 0
    for u_value in range(PRIME):
        rhs = (
            4 * pow(u_value, 8, PRIME) - 8 * u_value**2 + 5
        ) % PRIME
        roots = [
            r_value
            for r_value in range(PRIME)
            if r_value * r_value % PRIME == rhs
        ]
        affine_count += len(roots)
        if roots:
            rows.append([u_value, roots])
    # The even-degree model has two rational infinities because its leading
    # coefficient is 4=2^2.
    assert affine_count == 4
    assert rows == [[1, [1, 2]], [2, [1, 2]]]
    return {
        "cardinality": affine_count + 2,
        "affine_rows": rows,
        "infinity_points": 2,
        "known_Q_points_cover_all_disks": True,
    }


def multiple_11D_data() -> tuple[sp.Expr, sp.Expr, dict[str, object]]:
    """Compute 11*[(1,1)-infinity] and its exact p=3 leading data."""

    a, t = sp.symbols("a t")
    original_curve = 4 * a**5 - 8 * a**2 + 5 * a
    monic_curve = original_curve / 4
    divisor = (a - 1, sp.Rational(1, 2))  # w=R/2
    multiple = (sp.Integer(1), sp.Integer(0))
    for _ in range(11):
        multiple = cantor_add(multiple, divisor, a, monic_curve)
    mumford_u, mumford_v_w = multiple
    mumford_v_R = sp.factor(2 * mumford_v_w)

    quotient, remainder = sp.div(
        original_curve - mumford_v_R**2,
        mumford_u,
        a,
        domain=sp.QQ,
    )
    assert sp.expand(remainder) == 0
    assert quotient != 0

    shifted_u = qpoly(sp.expand(mumford_u.subs(a, 1 + t)), t)
    assert shifted_u.degree() == 2 and shifted_u.LC() == 1
    b = shifted_u.coeff_monomial(t)
    c = shifted_u.coeff_monomial(1)
    discriminant = sp.factor(b**2 - 4 * c)

    shifted_v = qpoly(sp.expand(mumford_v_R.subs(a, 1 + t)), t)
    assert shifted_v.degree() == 1
    slope = shifted_v.coeff_monomial(t)
    value_at_center = shifted_v.coeff_monomial(1)
    root_center = -b / 2
    R_at_root_center = sp.factor(slope * root_center + value_at_center)
    half_R_difference_squared = sp.factor(slope**2 * discriminant / 4)

    exact_data = {
        "shifted_u_linear": valuation_and_unit(b, PRIME),
        "shifted_u_constant": valuation_and_unit(c, PRIME),
        "u_discriminant": valuation_and_unit(discriminant, PRIME),
        "v_R_slope": valuation_and_unit(slope, PRIME),
        "v_R_at_a_1": valuation_and_unit(value_at_center, PRIME),
        "R_at_root_center": valuation_and_unit(R_at_root_center, PRIME),
        "half_R_difference_squared": valuation_and_unit(
            half_R_difference_squared, PRIME
        ),
    }
    assert exact_data == {
        "shifted_u_linear": (1, 2),
        "shifted_u_constant": (2, 1),
        "u_discriminant": (4, 1),
        "v_R_slope": (-2, 2),
        "v_R_at_a_1": (-1, 2),
        "R_at_root_center": (3, 2),
        "half_R_difference_squared": (0, 1),
    }

    # The discriminant is 3^4 times a 3-adic unit congruent to 1, so it has
    # a square root in Q_3.  The two roots lie over a=1 and their R-values
    # reduce to +1 and -1: the central R-value is divisible by 3, while half
    # their difference is a unit whose square is 1 modulo 3.
    return mumford_u, mumford_v_R, {
        "multiple": "11*D",
        "D": "[(1,1)-infinity]",
        "D_mod_3_order": 11,
        "exact_data": {
            name: {"valuation": pair[0], "unit_mod_3": pair[1]}
            for name, pair in exact_data.items()
        },
        "reduced_support": ["(1,1)", "(1,-1)"],
        "reduction_is_principal": "(1,1)+(1,-1)-2*infinity=divisor(a-1)",
    }


def annihilator_ratio(mumford_u: sp.Expr) -> dict[str, object]:
    """Compute lambda=log_1(D)/log_0(D) modulo 27 exactly."""

    a, t = sp.symbols("a t")
    original_curve = 4 * a**5 - 8 * a**2 + 5 * a
    shifted_u = qpoly(sp.expand(mumford_u.subs(a, 1 + t)), t)
    b = shifted_u.coeff_monomial(t)
    c = shifted_u.coeff_monomial(1)

    # If t_+,t_- are the two roots of shifted_u, then the logarithm of 11D
    # is H_j(t_+)-H_j(t_-), where
    # H_j(t)=integral_0^t (1+s)^j ds/sqrt(F(1+s)).
    # Divide by t_+-t_-.  For powers 1,2,3 the difference quotients are
    # 1, -b, b^2-c.
    inverse_root = sp.series(
        1 / sp.sqrt(original_curve.subs(a, 1 + t)),
        t,
        0,
        4,
    ).removeO()
    difference_quotients = [None, sp.Integer(1), -b, b**2 - c]
    truncated_logs: list[sp.Expr] = []
    primitives: list[sp.Expr] = []
    for power in (0, 1):
        integrand = sp.series(
            (1 + t) ** power * inverse_root,
            t,
            0,
            3,
        ).removeO()
        primitive = sp.expand(sp.integrate(integrand, t))
        primitives.append(primitive)
        coefficients = [
            primitive.coeff(t, degree) for degree in range(1, 4)
        ]
        truncated = sp.factor(
            sum(
                coefficients[degree - 1] * difference_quotients[degree]
                for degree in range(1, 4)
            )
        )
        assert valuation_and_unit(truncated, PRIME)[0] == 0
        truncated_logs.append(truncated)

    assert primitives == [
        t - sp.Rational(9, 4) * t**2 + sp.Rational(115, 24) * t**3,
        t - sp.Rational(7, 4) * t**2 + sp.Rational(79, 24) * t**3,
    ]

    # The inverse square-root coefficients are 3-integral.  Integration can
    # lose only v_3(n), while the nth power-difference quotient has valuation
    # at least n-1 because v_3(b)>=1 and v_3(c)>=2.  Hence every omitted term
    # n>=4 has valuation at least n-1-v_3(n)>=3.
    for degree in range(4, 2000):
        assert degree - 1 - valuation(degree) >= 3

    log_0, log_1 = truncated_logs
    ratio = sp.factor(log_1 / log_0)
    ratio_mod_27 = rational_residue(ratio, 27)
    assert ratio_mod_27 == 7
    delta = sp.factor(ratio - 1)
    assert valuation_and_unit(delta, PRIME) == (1, 2)
    assert rational_residue(delta / 3, 3) == 2

    return {
        "basis": ["da/R", "a*da/R"],
        "logarithm_direction": "[log_0(D),log_1(D)]",
        "primitive_truncations": [str(item) for item in primitives],
        "tail_after_difference_quotient": "3^3*Z_3",
        "lambda_definition": "log_1(D)/log_0(D)",
        "lambda_mod_27": ratio_mod_27,
        "lambda_minus_1": {
            "valuation": 1,
            "unit_mod_3": 2,
        },
        "log_0_11D_valuation": 2,
        "log_0_D_valuation": 2,
        "valuation_reason": (
            "The root difference has valuation 2 and the divided first "
            "logarithm is a unit; 11 is a 3-adic unit."
        ),
        "D_plus_annihilator": "(lambda-a)*da/R",
        "C3_pullback_annihilator": "(lambda-u^2)*du/r (up to a unit scalar)",
    }


def affine_disk_audit() -> dict[str, object]:
    """Prove the degree-two Weierstrass reduction in four affine disks."""

    t, z, delta, delta_unit = sp.symbols("t z delta delta_unit")
    u = sp.symbols("u")
    c3_rhs = 4 * u**8 - 8 * u**2 + 5
    records: list[dict[str, object]] = []

    for center_u in (1, -1):
        local_inverse_r = sp.series(
            1 / sp.sqrt(c3_rhs.subs(u, center_u + t)),
            t,
            0,
            4,
        ).removeO()
        integrand = sp.series(
            (1 + delta - (center_u + t) ** 2) * local_inverse_r,
            t,
            0,
            4,
        ).removeO()
        primitive = sp.expand(sp.integrate(integrand, t))

        normalized = sp.expand(
            primitive.subs({t: 3 * z, delta: 3 * delta_unit}) / 9
        )
        # Only degrees <=3 were expanded.  Modulo 3, delta_unit=2 and all
        # terms except the displayed linear/quadratic terms vanish.
        truncated_reduction = sp.Poly(
            normalized.subs(delta_unit, 2),
            z,
            domain=sp.QQ,
        )
        reduced_coefficients = {
            degree: rational_residue(
                truncated_reduction.coeff_monomial(z**degree),
                3,
            )
            for degree in range(1, 5)
        }
        expected_quadratic = sp.expand(2 * z - center_u * z**2)
        expected_coefficients = {
            degree: int(expected_quadratic.coeff(z, degree)) % 3
            for degree in range(1, 5)
        }
        assert reduced_coefficients == expected_coefficients

        # Tail control after substituting t=3z and dividing by 9.
        # Terms containing delta have valuation at least
        # n-1-v_3(n), hence vanish mod 3 for n>=2.  The remaining terms
        # have valuation n-2-v_3(n); n=2,3 were computed explicitly and the
        # cubic coefficient vanishes mod 3, while all n>=4 vanish uniformly.
        for degree in range(2, 2000):
            assert degree - 1 - valuation(degree) >= 1
        for degree in range(4, 2000):
            assert degree - 2 - valuation(degree) >= 1

        second_root = 2 if center_u == 1 else 1
        reduced = sp.Poly(expected_quadratic, z, modulus=3)
        assert reduced.eval(0) == 0
        assert reduced.eval(second_root) == 0
        derivative = reduced.diff()
        assert derivative.eval(0) % 3 != 0
        assert derivative.eval(second_root) % 3 != 0

        records.append(
            {
                "u_center": center_u,
                "r_centers": [1, -1],
                "local_parameter": f"u-({center_u})=3*z",
                "normalized_primitive_reduction": str(expected_quadratic),
                "simple_zero_classes_z_mod_3": [0, second_root],
                "second_zero_u_mod_9": (
                    center_u + 3 * second_root
                ) % 9,
                "zeros_per_r_disk": 2,
            }
        )

    return {
        "records": records,
        "weierstrass_degree_per_affine_disk": 2,
        "total_affine_disks": 4,
        "total_affine_coleman_zeros": 8,
        "conclusion": (
            "Each affine disk contains its known rational point and one "
            "additional simple Q_3 Coleman zero."
        ),
    }


def infinity_disk_audit() -> dict[str, object]:
    """Prove uniqueness in each of the two infinity residue disks."""

    t, z, lam = sp.symbols("t z lambda")
    # With t=1/u and s=r*t^4, one has
    # s^2=4-8*t^6+5*t^8 and
    # (lambda-u^2)du/r=(1-lambda*t^2)dt/s.
    infinity_rhs = 4 - 8 * t**6 + 5 * t**8
    records = []
    for sign in (1, -1):
        inverse_s = sign * sp.series(
            1 / sp.sqrt(infinity_rhs),
            t,
            0,
            9,
        ).removeO()
        integrand = sp.series(
            (1 - lam * t**2) * inverse_s,
            t,
            0,
            9,
        ).removeO()
        primitive = sp.integrate(integrand, t)
        leading = sp.expand(primitive).coeff(t, 1)
        assert rational_residue(leading, 3) != 0
        # After t=3z and division by 3, every degree n>=2 has valuation
        # n-1-v_3(n)>=1.
        for degree in range(2, 2000):
            assert degree - 1 - valuation(degree) >= 1
        records.append(
            {
                "infinity_branch": "+2" if sign == 1 else "-2",
                "local_parameter": "t=1/u=3*z",
                "normalized_linear_coefficient_mod_3": rational_residue(
                    leading, 3
                ),
                "zeros_in_disk": 1,
            }
        )
    return {
        "records": records,
        "total_infinity_coleman_zeros": 2,
        "conclusion": "Each infinity disk contains only its known point.",
    }


def prime_7_index_audit() -> dict[str, object]:
    """Prove that the unknown odd Mordell--Weil index is prime to 3."""

    divisors = all_reduced_divisors(7)
    D_mod_7 = point_divisor(1, 1, 7)
    jacobian_order = len(divisors)
    D_order = divisor_order(D_mod_7, 7)
    assert jacobian_order == 42
    assert D_order == 21

    # Write J(Q)=Z*G+<T> and D=mG after the standard torsion shift.  The
    # 2-descent proves m odd.  If r=ord(G mod 7), then r|42 and
    # r/gcd(r,m)=21.  Exhaust the exact divisibility possibilities without
    # assuming G or m.
    possible_orders: set[int] = set()
    possible_pairs: list[list[int]] = []
    for order in range(1, jacobian_order + 1):
        if jacobian_order % order:
            continue
        for odd_m in range(1, 2 * jacobian_order + 1, 2):
            if order // gcd(order, odd_m) == D_order:
                possible_orders.add(order)
                possible_pairs.append([order, odd_m % 21])
    assert possible_orders == {21}
    assert all(gcd(residue, 21) == 1 for _, residue in possible_pairs)

    return {
        "J_F7_order": jacobian_order,
        "D_mod_7_order": D_order,
        "possible_order_of_G_mod_7": [21],
        "unknown_index": "D=mG with m odd",
        "conclusion": "gcd(m,21)=1, in particular 3 does not divide m",
        "scope": (
            "Only the finite group order and the order of D are used.  No "
            "p=7 square-abscissa table, sieve class, or formal logarithm is used."
        ),
    }


def rational_lattice_refinement() -> dict[str, object]:
    """Remove the four extra Coleman zeros for rational points."""

    x, z, delta, delta_unit = sp.symbols("x z delta delta_unit")
    a = sp.symbols("a")
    original_curve = 4 * a**5 - 8 * a**2 + 5 * a
    records: list[dict[str, object]] = []

    for R_sign in (1, -1):
        inverse_R = R_sign * sp.series(
            1 / sp.sqrt(original_curve.subs(a, 1 + x)),
            x,
            0,
            5,
        ).removeO()
        first_log_primitive = sp.expand(
            sp.integrate(sp.series(inverse_R, x, 0, 5).removeO(), x)
        )
        assert rational_residue(first_log_primitive.coeff(x, 1), 3) != 0

        # For x in 3Z_3, H_0(x)=x*(unit+3Z_3), so v_3(H_0(x))=v_3(x).
        # A rational divisor difference is nG+eT.  T has zero logarithm,
        # v_3(log_0(G))=v_3(log_0(D))=2 because 3 does not divide m, and
        # n is integral.  Therefore a rational point must have x in 9Z_3.
        annihilator_integrand = sp.series(
            (delta - x) * inverse_R,
            x,
            0,
            5,
        ).removeO()
        annihilator_primitive = sp.expand(
            sp.integrate(annihilator_integrand, x)
        )
        normalized = sp.expand(
            annihilator_primitive.subs(
                {x: 9 * z, delta: 3 * delta_unit}
            )
            / 27
        )
        reduction_coefficients = {
            degree: rational_residue(
                sp.Poly(
                    normalized.subs(delta_unit, 2),
                    z,
                    domain=sp.QQ,
                ).coeff_monomial(z**degree),
                3,
            )
            for degree in range(1, 6)
        }
        expected_linear = 2 * R_sign % 3
        assert reduction_coefficients[1] == expected_linear
        assert all(
            reduction_coefficients[degree] == 0
            for degree in range(2, 6)
        )

        # Uniform tails.  A delta term of primitive degree n has valuation
        # at least 2n-2-v_3(n) after x=9z and division by 27.  A term from
        # the factor -x has valuation at least 2n-3-v_3(n), n>=2.
        for degree in range(2, 2000):
            assert 2 * degree - 2 - valuation(degree) >= 1
            assert 2 * degree - 3 - valuation(degree) >= 1

        records.append(
            {
                "D_plus_center": f"(1,{R_sign})",
                "local_coordinate": "x=a-1",
                "first_log": "H_0(x)=x*unit for x in 3*Z_3",
                "rational_lattice_constraint": "x in 9*Z_3",
                "refined_parameter": "x=9*z",
                "normalized_annihilator_reduction": (
                    f"{expected_linear}*z over F_3"
                ),
                "rational_zero": "z=0 only",
            }
        )

    return {
        "records": records,
        "argument": (
            "For Q in the same affine disk as P, log_0([Q-P]) is an "
            "integral multiple of log_0(G), hence lies in 9*Z_3.  The local "
            "first integral is x times a unit, so x=a(Q)-1 lies in 9*Z_3. "
            "The annihilating primitive is then z times a unit."
        ),
        "conclusion": (
            "The additional Coleman zero has a-1 congruent to 3 modulo 9 "
            "and cannot be rational.  Every rational affine point has a=1."
        ),
    }


def verify() -> dict[str, object]:
    """Return the canonical exact certificate."""

    def checked_artifact(relative_path: str) -> dict[str, object]:
        """Load a canonical dependency and verify its embedded checksum."""

        path = ROOT / relative_path
        payload = json.loads(path.read_text(encoding="utf-8"))
        checksum = payload.pop("sha256_without_checksum")
        canonical = json.dumps(
            payload, sort_keys=True, separators=(",", ":")
        ).encode()
        assert hashlib.sha256(canonical).hexdigest() == checksum
        payload["sha256_without_checksum"] = checksum
        return payload

    elliptic_rank = checked_artifact(
        "research/frobenius_audit/candidate_544c_rank_descent.json"
    )
    genus_two_rank = checked_artifact(
        "research/proof_simplification_2/richelot_isogeny_descent.json"
    )
    quotient_structure = checked_artifact(
        "research/proof_simplification/c041_structure.json"
    )
    assert elliptic_rank["rank"] == 1
    assert elliptic_rank["non_torsion_certificate"]["P"] == "(0,2)"
    assert genus_two_rank["rank_inequality"]["rank"] == 1
    assert (
        genus_two_rank["rank_inequality"]["torsion"]
        == "Z/2Z generated by T"
    )
    assert (
        genus_two_rank["descent"]["generalized_descent_function"][
            "D_T_images_independent"
        ]
        is True
    )
    assert (
        genus_two_rank["conservatism"][
            "existing_full_descent_is_a_logical_dependency"
        ]
        is False
    )
    assert (
        quotient_structure["quotients"]["jacobian_isogeny"]
        == "Jac(C3) ~ E1 x Jac(D+) over Q"
    )

    u, a = sp.symbols("u a")
    c3_rhs = 4 * u**8 - 8 * u**2 + 5
    d_plus_rhs = 4 * a**5 - 8 * a**2 + 5 * a
    assert int(sp.discriminant(c3_rhs, u)) % 3 != 0
    assert int(sp.discriminant(d_plus_rhs, a)) % 3 != 0

    points = c3_points_mod_3()
    assert points["cardinality"] == 6
    assert len(all_reduced_divisors(3)) == 22
    assert divisor_order(point_divisor(1, 1, 3), 3) == 11
    mumford_u, _, multiple_data = multiple_11D_data()
    annihilator = annihilator_ratio(mumford_u)
    affine = affine_disk_audit()
    infinity = infinity_disk_audit()
    index_at_7 = prime_7_index_audit()
    lattice = rational_lattice_refinement()

    payload: dict[str, object] = {
        "schema": 1,
        "status": "PASS",
        "curve": "C3: r^2=4*u^8-8*u^2+5",
        "prime": 3,
        "rank_inputs": {
            "Jac_C3_isogeny": "Jac(C3) ~ E1 x Jac(D+) over Q",
            "rank_E1_Q": 1,
            "rank_Jac_D_plus_Q": 1,
            "rank_Jac_C3_Q": 2,
            "annihilator_dimension": 1,
            "primitive_generator_assumed": False,
            "reason": (
                "Both non-torsion factor logarithms are nonzero; the "
                "prime-to-3 quotient isogeny separates their tangent directions."
            ),
            "checked_artifacts": [
                "research/frobenius_audit/candidate_544c_rank_descent.json",
                "research/proof_simplification_2/richelot_isogeny_descent.json",
                "research/proof_simplification/c041_structure.json",
            ],
            "good_reduction_at_3": True,
        },
        "finite_reduction": points,
        "formal_log_input": multiple_data,
        "annihilator": annihilator,
        "affine_disks": affine,
        "infinity_disks": infinity,
        "raw_coleman_zero_count": {
            "known_rational_points": 6,
            "affine_zeros": 8,
            "infinity_zeros": 2,
            "total": 10,
            "additional_Q3_zeros": 4,
        },
        "prime_7_index_audit": index_at_7,
        "rational_lattice_refinement": lattice,
        "rational_points": [
            "infinity_+",
            "infinity_-",
            "(1,1)",
            "(1,-1)",
            "(-1,1)",
            "(-1,-1)",
        ],
        "target_A_conclusion": (
            "SUCCESS.  Direct p=3 Chabauty plus the integral Mordell--Weil "
            "lattice refinement proves that C3(Q) consists exactly of the "
            "two infinities and (u,r)=(+/-1,+/-1)."
        ),
        "proof_dependency_change": {
            "removed": [
                "p=23 Mordell--Weil sieve",
                "p=7 square-abscissa class tables",
                "exact 42D p=7 formal logarithm",
                "p=7 Coleman differential and disk bound",
                "coefficient comparison modulo 21/231",
            ],
            "retained": [
                "rank Jac(D+)(Q)=1 from the Richelot isogeny descent",
                "#J(F7)=42 and ord(D mod 7)=21 for rank and 3-saturation",
            ],
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
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print("direct p=3 genus-three Chabauty audit: PASS")
    print("four raw extra Q_3 zeros; integral MW lattice removes all four")
    print("Target A replacement: SUCCESS")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
