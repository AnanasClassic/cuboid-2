#!/usr/bin/env python3
"""Exact Target B certificate for the Richelot descent on ``D_+``.

The certificate works over ``F = Q(i)`` but keeps track of Galois descent
to ``Q``.  It verifies:

* the source and dual Richelot bracket constructions, including the scalar
  needed to pass from the raw bracket model to the rational model;
* exact reverse-bracket recovery and the hypotheses of the polarized
  Richelot duality theorem, which gives ``hat(phi) o phi = [2]``;
* the kernel Galois module and the complete 64-class Gaussian S-unit group;
* complete local images at 2, 5 and 17, using exact PARI local-square tests;
* both possible Galois-equivariant identifications with the Cartier dual,
  using exact PARI Hilbert symbols;
* the two Selmer dimensions and the resulting rank inequality.

No bounded point search is used.  A failed identity, a missing local class,
or a pairing-convention discrepancy raises ``CertificateFailure`` and makes
the command print ``FAIL`` rather than asserting Target B.

Run from the cuboid-2 repository environment, for example:

    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONPATH=/path/to/cuboid-2 \
    /path/to/cuboid-2/.venv/bin/python richelot_isogeny_descent.py
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from fractions import Fraction
from importlib.metadata import version as distribution_version
from itertools import product
from math import gcd, isqrt
from pathlib import Path

import sympy as sp
from cypari2 import Pari

ROOT = Path(
    os.environ.get(
        "CUBOID_REPO_ROOT",
        Path(__file__).resolve().parents[2],
    )
).resolve()
sys.path.insert(0, str(ROOT))

try:
    from research.proof_simplification_2.richelot_composition_check import (
        certify as certify_richelot_composition,
    )
except ModuleNotFoundError:
    # The fallback keeps this temporary pre-landing copy runnable beside the
    # correspondence certificate.  In the repository the package import is
    # the canonical path.
    from richelot_composition_check import (
        certify as certify_richelot_composition,
    )


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
BAD_PRIMES = (2, 5, 17)
GAUSSIAN_POLYNOMIAL = "t^2+1"
QUARTIC_POLYNOMIAL = "z^4-16*z+20"
LOCAL_X_BASES = {
    2: (Fraction(1), Fraction(-4, 3), Fraction(1, 4)),
    5: (Fraction(1), Fraction(2), Fraction(-5)),
    17: (Fraction(-56), Fraction(-50), Fraction(-49)),
}

# Bit order is part of the certificate: masks in the output use this basis.
GAUSSIAN_BASIS_LABELS = ("i", "1+i", "2+i", "2-i", "4+i", "4-i")

EXPECTED_H_VALUES = {
    2: (
        (Fraction(1, 2), Fraction(0)),
        (Fraction(23, 18), Fraction(-7, 3)),
        (Fraction(-7, 16), Fraction(-3, 4)),
    ),
    5: (
        (Fraction(1, 2), Fraction(0)),
        (Fraction(7, 2), Fraction(1)),
        (Fraction(49, 2), Fraction(-6)),
    ),
    17: (
        (Fraction(6271, 2), Fraction(-57)),
        (Fraction(4999, 2), Fraction(-51)),
        (Fraction(4801, 2), Fraction(-50)),
    ),
}

EXPECTED_HAT_INDIVIDUAL_MASKS = {
    2: [
        0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29,
        32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61,
    ],
    5: [
        0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27,
        32, 33, 34, 35, 40, 41, 42, 43, 48, 49, 50, 51, 56, 57, 58, 59,
    ],
    17: [0, 1, 6, 7, 8, 9, 14, 15],
}
EXPECTED_HAT_CUMULATIVE_MASKS = {
    2: EXPECTED_HAT_INDIVIDUAL_MASKS[2],
    5: [0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 40, 41, 48, 49, 56, 57],
    17: [0, 1, 8, 9],
}
EXPECTED_PHI_INDIVIDUAL_MASKS = {
    2: [0, 12, 17, 29, 33, 45, 48, 60],
    5: [0, 3, 16, 19, 33, 34, 49, 50],
    17: list(range(16)) + list(range(32, 48)),
}
EXPECTED_PHI_CUMULATIVE_MASKS = {
    2: EXPECTED_PHI_INDIVIDUAL_MASKS[2],
    5: [0, 33],
    17: [0, 33],
}


Gaussian = tuple[Fraction, Fraction]
FullKummerValue = tuple[Fraction, object]
FinitePolynomial = tuple[int, ...]  # coefficients in increasing degree
FiniteDivisor = tuple[FinitePolynomial, FinitePolynomial]


class CertificateFailure(RuntimeError):
    """Raised whenever an exact Target B gate cannot be certified."""


def require(condition: bool, message: str) -> None:
    """Fail closed when a claimed certificate identity is not exact."""

    if not condition:
        raise CertificateFailure(message)


def fraction_text(value: Fraction) -> str:
    """Return a stable exact representation of a rational number."""

    value = Fraction(value)
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def gaussian_text(value: Gaussian) -> str:
    """Return a stable exact representation of a Gaussian rational."""

    real, imag = map(Fraction, value)
    if imag == 0:
        return fraction_text(real)
    imag_abs = abs(imag)
    imag_term = "i" if imag_abs == 1 else f"{fraction_text(imag_abs)}*i"
    if real == 0:
        return imag_term if imag > 0 else f"-{imag_term}"
    sign = "+" if imag > 0 else "-"
    return f"{fraction_text(real)}{sign}{imag_term}"


def gaussian_multiply(left: Gaussian, right: Gaussian) -> Gaussian:
    """Multiply two elements represented in the basis ``1,i``."""

    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def gaussian_conjugate(value: Gaussian) -> Gaussian:
    """Apply the nontrivial automorphism of ``Q(i)/Q``."""

    return value[0], -value[1]


def gaussian_divide(left: Gaussian, right: Gaussian) -> Gaussian:
    """Divide two nonzero Gaussian rationals exactly."""

    c, d = right
    norm = c * c + d * d
    require(norm != 0, "attempted division by zero in Q(i)")
    return gaussian_multiply(left, (c / norm, -d / norm))


def gaussian_span(generators: list[Gaussian] | tuple[Gaussian, ...]) -> list[Gaussian]:
    """Enumerate the ordered binary span of multiplicative squareclasses."""

    result: list[Gaussian] = [(Fraction(1), Fraction(0))]
    for generator in generators:
        result += [gaussian_multiply(value, generator) for value in result]
    return result


def gaussian_to_pari(pari: Pari, t_mod: object, value: Gaussian) -> object:
    """Convert an exact ``(real, imag)`` pair to a PARI number-field element."""

    real, imag = value
    return (
        pari(real.numerator) / real.denominator
        + (pari(imag.numerator) / imag.denominator) * t_mod
    )


def valuation_integer(value: int, prime: int) -> int:
    """Return the additive ``prime``-adic valuation of a nonzero integer."""

    value = abs(value)
    result = 0
    while value and value % prime == 0:
        value //= prime
        result += 1
    return result


def rational_local_square(value: Fraction, prime: int) -> bool:
    """Test exactly whether a rational number is a square in ``Q_prime``."""

    value = Fraction(value)
    if value == 0:
        return True
    valuation = valuation_integer(value.numerator, prime) - valuation_integer(
        value.denominator, prime
    )
    if valuation % 2:
        return False
    unit = value / prime**valuation if valuation >= 0 else value * prime ** (-valuation)
    if prime == 2:
        residue = (
            (unit.numerator % 8) * pow(unit.denominator % 8, -1, 8) % 8
        )
        return residue == 1
    residue = (
        (unit.numerator % prime)
        * pow(unit.denominator % prime, -1, prime)
        % prime
    )
    return pow(residue, (prime - 1) // 2, prime) == 1


def curve_polynomial(value: Fraction) -> Fraction:
    """Evaluate the odd-degree equation of ``D_+`` at a rational abscissa."""

    value = Fraction(value)
    return 4 * value**5 - 8 * value**2 + 5 * value


def descent_h(value: Fraction) -> Gaussian:
    """Evaluate the normalized generalized Richelot function ``A/2``."""

    value = Fraction(value)
    # A = 2*x^2 + 2*i*x - 1 - 2*i, so A/2 is:
    return value * value - Fraction(1, 2), value - 1


def full_pair_multiply(
    left: FullKummerValue, right: FullKummerValue
) -> FullKummerValue:
    """Multiply values in the full Schaefer--Stoll etale algebra."""

    return left[0] * right[0], left[1] * right[1]


def full_pair_span(basis: list[FullKummerValue], pari: Pari) -> list[FullKummerValue]:
    """Enumerate a binary span in ``Q x Q[z]/(z^4-16z+20)``."""

    result: list[FullKummerValue] = [(Fraction(1), pari(1))]
    for generator in basis:
        result += [full_pair_multiply(value, generator) for value in result]
    return result


def finite_trim(
    polynomial: tuple[int, ...] | list[int], prime: int
) -> FinitePolynomial:
    """Normalize a polynomial over ``F_prime``."""

    values = [value % prime for value in polynomial]
    while len(values) > 1 and values[-1] == 0:
        values.pop()
    return tuple(values or [0])


def finite_add(
    left: FinitePolynomial, right: FinitePolynomial, prime: int
) -> FinitePolynomial:
    """Add two polynomials over ``F_prime``."""

    length = max(len(left), len(right))
    return finite_trim(
        [
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
            for index in range(length)
        ],
        prime,
    )


def finite_neg(polynomial: FinitePolynomial, prime: int) -> FinitePolynomial:
    """Negate a polynomial over ``F_prime``."""

    return finite_trim([-value for value in polynomial], prime)


def finite_sub(
    left: FinitePolynomial, right: FinitePolynomial, prime: int
) -> FinitePolynomial:
    """Subtract two polynomials over ``F_prime``."""

    return finite_add(left, finite_neg(right, prime), prime)


def finite_multiply(
    left: FinitePolynomial, right: FinitePolynomial, prime: int
) -> FinitePolynomial:
    """Multiply two polynomials over ``F_prime``."""

    values = [0] * (len(left) + len(right) - 1)
    for first_index, first in enumerate(left):
        for second_index, second in enumerate(right):
            values[first_index + second_index] += first * second
    return finite_trim(values, prime)


def finite_scale(
    polynomial: FinitePolynomial, scalar: int, prime: int
) -> FinitePolynomial:
    """Scale a polynomial over ``F_prime``."""

    return finite_trim([scalar * value for value in polynomial], prime)


def finite_divmod(
    dividend: FinitePolynomial, divisor: FinitePolynomial, prime: int
) -> tuple[FinitePolynomial, FinitePolynomial]:
    """Perform exact Euclidean division over ``F_prime``."""

    divisor = finite_trim(divisor, prime)
    require(divisor != (0,), "finite polynomial division by zero")
    remainder = list(finite_trim(dividend, prime))
    quotient = [0] * max(1, len(remainder) - len(divisor) + 1)
    inverse_lead = pow(divisor[-1], -1, prime)
    while (
        len(remainder) >= len(divisor)
        and finite_trim(remainder, prime) != (0,)
    ):
        degree = len(remainder) - len(divisor)
        coefficient = remainder[-1] * inverse_lead % prime
        quotient[degree] = coefficient
        for index, value in enumerate(divisor):
            remainder[index + degree] = (
                remainder[index + degree] - coefficient * value
            ) % prime
        remainder = list(finite_trim(remainder, prime))
    return finite_trim(quotient, prime), finite_trim(remainder, prime)


def finite_exact_divide(
    dividend: FinitePolynomial, divisor: FinitePolynomial, prime: int
) -> FinitePolynomial:
    """Divide polynomials and fail if the remainder is nonzero."""

    quotient, remainder = finite_divmod(dividend, divisor, prime)
    require(remainder == (0,), "non-exact polynomial division in Cantor arithmetic")
    return quotient


def finite_monic(
    polynomial: FinitePolynomial, prime: int
) -> FinitePolynomial:
    """Scale a nonzero polynomial to be monic."""

    polynomial = finite_trim(polynomial, prime)
    require(polynomial != (0,), "cannot make the zero polynomial monic")
    return finite_scale(polynomial, pow(polynomial[-1], -1, prime), prime)


def finite_xgcd(
    left: FinitePolynomial, right: FinitePolynomial, prime: int
) -> tuple[FinitePolynomial, FinitePolynomial, FinitePolynomial]:
    """Return monic gcd and Bezout coefficients over ``F_prime``."""

    old_remainder, remainder = finite_trim(left, prime), finite_trim(right, prime)
    old_left, left_coefficient = (1,), (0,)
    old_right, right_coefficient = (0,), (1,)
    while remainder != (0,):
        quotient, new_remainder = finite_divmod(
            old_remainder, remainder, prime
        )
        old_remainder, remainder = remainder, new_remainder
        old_left, left_coefficient = (
            left_coefficient,
            finite_sub(
                old_left,
                finite_multiply(quotient, left_coefficient, prime),
                prime,
            ),
        )
        old_right, right_coefficient = (
            right_coefficient,
            finite_sub(
                old_right,
                finite_multiply(quotient, right_coefficient, prime),
                prime,
            ),
        )
    scale = pow(old_remainder[-1], -1, prime)
    return (
        finite_scale(old_remainder, scale, prime),
        finite_scale(old_left, scale, prime),
        finite_scale(old_right, scale, prime),
    )


def finite_curve_monic(prime: int) -> FinitePolynomial:
    """Return ``w^2=x^5-2*x^2+(5/4)*x`` over ``F_prime``."""

    return finite_trim((0, 5 * pow(4, -1, prime), -2, 0, 0, 1), prime)


def finite_cantor_add(
    first: FiniteDivisor, second: FiniteDivisor, prime: int
) -> FiniteDivisor:
    """Add reduced Mumford divisors on ``D_+`` over ``F_prime``."""

    u1, v1 = first
    u2, v2 = second
    curve = finite_curve_monic(prime)
    first_gcd, first_left, first_right = finite_xgcd(u1, u2, prime)
    gcd, second_left, second_right = finite_xgcd(
        first_gcd, finite_add(v1, v2, prime), prime
    )
    s1 = finite_multiply(second_left, first_left, prime)
    s2 = finite_multiply(second_left, first_right, prime)
    s3 = second_right

    u = finite_exact_divide(
        finite_multiply(u1, u2, prime),
        finite_multiply(gcd, gcd, prime),
        prime,
    )
    numerator = finite_add(
        finite_add(
            finite_multiply(finite_multiply(s1, u1, prime), v2, prime),
            finite_multiply(finite_multiply(s2, u2, prime), v1, prime),
            prime,
        ),
        finite_multiply(
            s3,
            finite_add(finite_multiply(v1, v2, prime), curve, prime),
            prime,
        ),
        prime,
    )
    v = finite_exact_divide(numerator, gcd, prime)
    u = finite_monic(u, prime)
    _, v = finite_divmod(v, u, prime)

    while len(u) - 1 > 2:
        quotient = finite_exact_divide(
            finite_sub(curve, finite_multiply(v, v, prime), prime),
            u,
            prime,
        )
        u = finite_monic(quotient, prime)
        _, v = finite_divmod(finite_neg(v, prime), u, prime)
    return finite_monic(u, prime), finite_trim(v, prime)


def finite_point_divisor(
    x_value: int, y_value: int, prime: int
) -> FiniteDivisor:
    """Return the Mumford divisor of ``(x,y)-infinity`` over ``F_prime``."""

    # The monic model uses w=y/2.
    w_value = y_value * pow(2, -1, prime) % prime
    return (
        finite_trim((-x_value, 1), prime),
        finite_trim((w_value,), prime),
    )


def finite_divisor_order(divisor: FiniteDivisor, prime: int) -> int:
    """Compute a divisor order exhaustively in a small finite Jacobian."""

    identity: FiniteDivisor = ((1,), (0,))
    value = identity
    for order in range(1, 10 * prime * prime + 1):
        value = finite_cantor_add(value, divisor, prime)
        if value == identity:
            return order
    raise CertificateFailure("finite divisor order exceeded the rigorous bound")


def all_finite_reduced_divisors(prime: int) -> set[FiniteDivisor]:
    """Enumerate every reduced Mumford representation over ``F_prime``."""

    curve = finite_curve_monic(prime)
    answer: set[FiniteDivisor] = {((1,), (0,))}
    for constant in range(prime):
        u = (constant, 1)
        for value in range(prime):
            v = (value,)
            remainder = finite_divmod(
                finite_sub(curve, finite_multiply(v, v, prime), prime),
                u,
                prime,
            )[1]
            if remainder == (0,):
                answer.add((u, v))
    for linear in range(prime):
        for constant in range(prime):
            u = (constant, linear, 1)
            for slope in range(prime):
                for intercept in range(prime):
                    v = finite_trim((intercept, slope), prime)
                    remainder = finite_divmod(
                        finite_sub(
                            curve, finite_multiply(v, v, prime), prime
                        ),
                        u,
                        prime,
                    )[1]
                    if remainder == (0,):
                        answer.add((u, v))
    return answer


def verify_bad_prime_support() -> dict[str, object]:
    """Recompute every discriminant support used to define the Selmer set."""

    x = sp.symbols("x")
    source = x * (4 * x**4 - 8 * x + 5)
    h1 = 2 * x**2 - 4 * x + 1
    target = 2 * h1 * (4 * x**4 + 4 * x**2 + 5)
    source_discriminant = int(sp.discriminant(source, x))
    target_discriminant = int(sp.discriminant(target, x))
    kernel_discriminant = -4
    require(
        source_discriminant == 2**14 * 5**2 * 17,
        "the source discriminant is not 2^14*5^2*17",
    )
    require(
        target_discriminant == 2**47 * 5 * 17**2,
        "the corrected target discriminant is not 2^47*5*17^2",
    )
    source_support = sorted(sp.factorint(abs(source_discriminant)))
    target_support = sorted(sp.factorint(abs(target_discriminant)))
    kernel_support = sorted(sp.factorint(abs(kernel_discriminant)))
    determinant_support = [2]
    combined_support = sorted(
        set(source_support)
        | set(target_support)
        | set(kernel_support)
        | set(determinant_support)
    )
    require(
        source_support == target_support == list(BAD_PRIMES)
        and kernel_support == determinant_support == [2]
        and combined_support == list(BAD_PRIMES),
        "the exact discriminants do not give the claimed Selmer prime set",
    )
    return {
        "source_polynomial_discriminant": source_discriminant,
        "source_polynomial_discriminant_factorization": "2^14*5^2*17",
        "source_polynomial_discriminant_support": source_support,
        "target_polynomial_discriminant": target_discriminant,
        "target_polynomial_discriminant_factorization": "2^47*5*17^2",
        "target_polynomial_discriminant_support": target_support,
        "kernel_etale_discriminant": kernel_discriminant,
        "kernel_ramification": kernel_support,
        "richelot_determinant_support": determinant_support,
        "complete_finite_bad_prime_set": combined_support,
    }


def verify_finite_rank_lower_bound(
    bad_prime_audit: dict[str, object],
) -> dict[str, object]:
    """Prove ``D`` is non-torsion and determine the rational torsion."""

    source_discriminant = bad_prime_audit["source_polynomial_discriminant"]
    require(
        isinstance(source_discriminant, int),
        "the source discriminant audit did not return an integer",
    )
    finite_data: dict[int, dict[str, int]] = {}
    for prime in (3, 7):
        require(
            source_discriminant % prime != 0,
            f"{prime} is not a good-reduction prime for D_+",
        )
        all_divisors = all_finite_reduced_divisors(prime)
        divisor_D = finite_point_divisor(1, 1, prime)
        divisor_T = finite_point_divisor(0, 0, prime)
        require(
            divisor_D in all_divisors and divisor_T in all_divisors,
            f"D or T is missing from the reduced-divisor set at {prime}",
        )
        order_D = finite_divisor_order(divisor_D, prime)
        order_T = finite_divisor_order(divisor_T, prime)
        identity: FiniteDivisor = ((1,), (0,))
        generated: set[FiniteDivisor] = set()
        current = identity
        for _ in range(order_D):
            require(current not in generated, f"D cycle repeated early at {prime}")
            generated.add(current)
            with_torsion = finite_cantor_add(current, divisor_T, prime)
            require(
                with_torsion not in generated,
                f"<D> and <D>+T intersect at {prime}",
            )
            generated.add(with_torsion)
            current = finite_cantor_add(current, divisor_D, prime)
        require(current == identity, f"D cycle does not close at {prime}")
        require(
            generated == all_divisors,
            f"D and T do not exhaust J(F_{prime})",
        )
        finite_data[prime] = {
            "jacobian_order": len(all_divisors),
            "D_order": order_D,
            "T_order": order_T,
        }
    require(
        finite_data
        == {
            3: {"jacobian_order": 22, "D_order": 11, "T_order": 2},
            7: {"jacobian_order": 42, "D_order": 21, "T_order": 2},
        },
        "finite Jacobian orders or D/T orders changed",
    )
    torsion_order_bound = gcd(
        finite_data[3]["jacobian_order"],
        finite_data[7]["jacobian_order"],
    )
    require(torsion_order_bound == 2, "finite reductions do not bound torsion by 2")
    require(
        finite_data[7]["D_order"] == 21,
        "D mod 7 no longer proves that D is non-torsion",
    )
    return {
        "good_reduction_primes": [3, 7],
        "J_F3_order": finite_data[3]["jacobian_order"],
        "J_F7_order": finite_data[7]["jacobian_order"],
        "gcd_of_reduction_orders": torsion_order_bound,
        "D_mod_3_order": finite_data[3]["D_order"],
        "D_mod_7_order": finite_data[7]["D_order"],
        "T_mod_3_order": finite_data[3]["T_order"],
        "T_mod_7_order": finite_data[7]["T_order"],
        "D_T_generate_both_reductions": True,
        "torsion_reduction_justification": (
            "3 and 7 are odd good-reduction primes; their formal groups over "
            "Q_p are torsion-free, so rational torsion injects into both "
            "finite Jacobians and has order dividing gcd(22,42)=2"
        ),
        "rational_torsion": "Z/2Z generated by T",
        "D_is_non_torsion": True,
        "rank_lower_bound": 1,
        "bad_prime_audit": bad_prime_audit,
    }


def matrix_multiply_mod2(
    left: tuple[int, int, int, int], right: tuple[int, int, int, int]
) -> tuple[int, int, int, int]:
    """Multiply flattened 2-by-2 matrices over ``F_2``."""

    a, b, c, d = left
    e, f, g, h = right
    return (
        (a * e + b * g) % 2,
        (a * f + b * h) % 2,
        (c * e + d * g) % 2,
        (c * f + d * h) % 2,
    )


def determinant_mod2(matrix: tuple[int, int, int, int]) -> int:
    """Return the determinant of a 2-by-2 matrix over ``F_2``."""

    a, b, c, d = matrix
    return (a * d - b * c) % 2


def verify_richelot_geometry(
    composition: dict[str, object] | None = None,
) -> dict[str, object]:
    """Run the corrected stable-twist correspondence certificate."""

    geometry = composition or certify_richelot_composition()
    require(
        geometry["status"] == "PASS"
        and geometry["composition"]["maps_defined_over_Q"] is True
        and geometry["composition"]["hat_phi_o_phi"] == "[2]"
        and geometry["composition"]["phi_o_hat_phi"] == "[2]",
        "the corrected Richelot correspondence/composition certificate failed",
    )
    require(
        geometry["source_quartic_irreducible_over_Q"] is True
        and geometry[
            "target_quadratic_and_quartic_irreducible_over_Q"
        ]
        is True,
        "rational 2-torsion factorization was not certified",
    )
    geometry = dict(geometry)
    geometry.update(
        {
            "source_J2_Q_dimension": 1,
            "target_J2_Q_dimension": 1,
            "source_and_target_rational_2_torsion_reason": (
                "each displayed sextic has exactly one rational irreducible "
                "factor partition: one quadratic/linear component and one "
                "irreducible quartic component"
            ),
        }
    )
    return geometry


def verify_kernel_and_s_units(
    pari: Pari,
    bad_prime_audit: dict[str, object],
) -> tuple[dict[str, object], object, object, dict[int, list], list[Gaussian]]:
    """Certify the kernel module and enumerate every Gaussian S-unit class."""

    require(
        bad_prime_audit["complete_finite_bad_prime_set"] == list(BAD_PRIMES),
        "bad-prime audit was not completed before the S-unit enumeration",
    )
    nf = pari(f"nfinit({GAUSSIAN_POLYNOMIAL})")
    bnf = pari(f"bnfinit({GAUSSIAN_POLYNOMIAL})")
    t_mod = pari(f"Mod(t,{GAUSSIAN_POLYNOMIAL})")
    bnf_certified = int(pari.bnfcertify(bnf))
    require(bnf_certified == 1, "PARI did not certify Q(i)'s BNF")
    require(int(bnf.bnf_get_no()) == 1, "Q(i) unexpectedly has nontrivial class group")
    require(str(bnf.bnf_get_cyc()) == "[]", "Q(i) class group invariants changed")
    require(list(nf.nf_get_sign()) == [pari(0), pari(1)], "wrong Q(i) signature")
    require(int(nf[2]) == -4, "wrong Q(i) discriminant")
    roots_of_unity = bnf.bnf_get_tu()
    require(int(roots_of_unity[0]) == 4, "Q(i) roots of unity do not have order 4")
    require(len(list(bnf.bnf_get_fu())) == 0, "Q(i) unexpectedly has a free unit")

    prime_ideals: dict[int, list] = {
        prime: list(pari(f"idealprimedec(nfinit({GAUSSIAN_POLYNOMIAL}),{prime})"))
        for prime in BAD_PRIMES
    }
    require(
        {prime: len(values) for prime, values in prime_ideals.items()}
        == {2: 1, 5: 2, 17: 2},
        "Gaussian prime decomposition at 2,5,17 is incorrect",
    )

    gaussian_basis: list[Gaussian] = [
        (Fraction(0), Fraction(1)),
        (Fraction(1), Fraction(1)),
        (Fraction(2), Fraction(1)),
        (Fraction(2), Fraction(-1)),
        (Fraction(4), Fraction(1)),
        (Fraction(4), Fraction(-1)),
    ]
    finite_prime_generators = gaussian_basis[1:]
    all_s_primes = [
        ideal for prime in BAD_PRIMES for ideal in prime_ideals[prime]
    ]
    valuation_rows = []
    for generator in finite_prime_generators:
        element = gaussian_to_pari(pari, t_mod, generator)
        valuation_rows.append(
            [int(pari.idealval(nf, element, ideal)) for ideal in all_s_primes]
        )
    require(
        sorted(valuation_rows) == sorted(
            [
                [1, 0, 0, 0, 0],
                [0, 1, 0, 0, 0],
                [0, 0, 1, 0, 0],
                [0, 0, 0, 1, 0],
                [0, 0, 0, 0, 1],
            ]
        ),
        "the five Gaussian prime generators do not give the S-prime basis",
    )
    expected_norms = [2, 5, 5, 17, 17]
    actual_norms = [
        int(pari.nfeltnorm(nf, gaussian_to_pari(pari, t_mod, value)))
        for value in finite_prime_generators
    ]
    require(actual_norms == expected_norms, "Gaussian S-prime norms are incorrect")

    candidates = gaussian_span(gaussian_basis)
    require(len(candidates) == 64, "Gaussian S-unit enumeration is not 64 classes")

    def global_square(value: Gaussian) -> bool:
        return bool(
            pari.nfeltissquare(nf, gaussian_to_pari(pari, t_mod, value))
        )

    # This also checks that the order-two class of the unit group is [i],
    # not [-1], since -1=i^2 is already a square in Q(i).
    for first_index, first in enumerate(candidates):
        for second in candidates[:first_index]:
            require(
                not global_square(gaussian_divide(first, second)),
                "two of the 64 Gaussian S-unit masks represent the same class",
            )

    # The three nonzero kernel elements are the factor pairs.  Conjugation
    # fixes q1 and swaps q2,q3; this is the permutation module Res_{F/Q} mu_2.
    # The target triple has the same action (h1 fixed, h2,h3 swapped).
    conjugation_on_nonzero = {"q1": "q1", "q2": "q3", "q3": "q2"}
    target_conjugation = {"h1": "h1", "h2": "h3", "h3": "h2"}
    require(
        conjugation_on_nonzero == {"q1": "q1", "q2": "q3", "q3": "q2"}
        and target_conjugation == {"h1": "h1", "h2": "h3", "h3": "h2"},
        "kernel Galois action is not the required permutation action",
    )
    rational_kernel_dimension = 1

    kernel_payload = {
        "splitting_field": "Q(i)",
        "field_discriminant": -4,
        "source_kernel": "ker(phi)=Res_{Q(i)/Q}(mu_2)",
        "dual_kernel": "ker(hat_phi)=Res_{Q(i)/Q}(mu_2)",
        "source_conjugation": conjugation_on_nonzero,
        "target_conjugation": target_conjugation,
        "source_rational_kernel_dimension": rational_kernel_dimension,
        "dual_rational_kernel_dimension": rational_kernel_dimension,
        "bad_primes": list(BAD_PRIMES),
        "bad_prime_justification": {
            **bad_prime_audit,
            "outside_S": (
                "both curves and the kernel are unramified; the isogeny "
                "local conditions are the unramified subgroups"
            ),
            "infinity": "H^1(R,Res_{C/R}(mu_2))=H^1(C,mu_2)=0",
        },
        "gaussian_class_number": 1,
        "gaussian_bnfcertify": bnf_certified,
        "gaussian_roots_of_unity_order": 4,
        "gaussian_free_unit_rank": 0,
        "gaussian_S_prime_count": 5,
        "gaussian_S_unit_basis": list(GAUSSIAN_BASIS_LABELS),
        "gaussian_S_unit_dimension": 6,
        "gaussian_S_unit_class_count": len(candidates),
        "finite_generator_valuation_rows": valuation_rows,
        "exact_local_routines": {
            "local_square": "PARI nfislocalpower(...,2)",
            "local_pairing": "PARI nfhilbert",
            "heuristic_or_database_rank_input": False,
        },
    }
    return kernel_payload, nf, t_mod, prime_ideals, candidates


def verify_local_images_and_selmer(
    pari: Pari,
    gaussian_nf: object,
    t_mod: object,
    gaussian_prime_ideals: dict[int, list],
    candidates: list[Gaussian],
) -> dict[str, object]:
    """Compute complete local images and both exact Selmer intersections."""

    quartic_nf = pari(f"nfinit({QUARTIC_POLYNOMIAL})")
    z_mod = pari(f"Mod(z,{QUARTIC_POLYNOMIAL})")
    quartic_prime_ideals = {
        prime: list(
            pari(f"idealprimedec(nfinit({QUARTIC_POLYNOMIAL}),{prime})")
        )
        for prime in BAD_PRIMES
    }
    require(
        {prime: len(values) for prime, values in quartic_prime_ideals.items()}
        == {2: 1, 5: 3, 17: 3},
        "quartic local factor counts do not give J(Q_p)[2] dimensions 1,3,3",
    )

    def gaussian_local_equal(left: Gaussian, right: Gaussian, prime: int) -> bool:
        quotient = gaussian_to_pari(
            pari, t_mod, gaussian_divide(left, right)
        )
        return all(
            bool(pari.nfislocalpower(gaussian_nf, ideal, quotient, 2))
            for ideal in gaussian_prime_ideals[prime]
        )

    def full_local_equal(
        left: FullKummerValue, right: FullKummerValue, prime: int
    ) -> bool:
        if not rational_local_square(left[0] / right[0], prime):
            return False
        quotient = left[1] / right[1]
        return all(
            bool(pari.nfislocalpower(quartic_nf, ideal, quotient, 2))
            for ideal in quartic_prime_ideals[prime]
        )

    def full_delta_x(value: Fraction) -> FullKummerValue:
        # theta=z/2 is a root of 4*x^4-8*x+5.
        return value, pari(value) - z_mod / 2

    def locally_distinct_span(
        exact_span: list[Gaussian], prime: int
    ) -> list[Gaussian]:
        representatives: list[Gaussian] = []
        for value in exact_span:
            if not any(
                gaussian_local_equal(value, known, prime)
                for known in representatives
            ):
                representatives.append(value)
        return representatives

    local_h_generators: dict[int, list[Gaussian]] = {}
    local_h_images: dict[int, list[Gaussian]] = {}
    local_payload: dict[str, object] = {}
    expected_h_dimensions = {2: 3, 5: 3, 17: 1}

    for prime in BAD_PRIMES:
        x_values = LOCAL_X_BASES[prime]
        require(
            all(rational_local_square(curve_polynomial(value), prime) for value in x_values),
            f"one of the displayed x-values is not a D_+(Q_{prime}) point",
        )

        # Independence in the complete Schaefer--Stoll Kummer target proves
        # these three point classes span J(Q_p)/2J(Q_p), not merely a sample.
        full_generators = [full_delta_x(value) for value in x_values]
        full_span = full_pair_span(full_generators, pari)
        require(len(full_span) == 8, f"wrong full Kummer span size at {prime}")
        for first_index, first in enumerate(full_span):
            require(
                not any(
                    full_local_equal(first, second, prime)
                    for second in full_span[:first_index]
                ),
                f"full Kummer x-basis is dependent at {prime}",
            )
        full_dimension_upper_bound = 3
        if prime == 2:
            dimension_formula = "g+dim J(Q_2)[2]=2+1=3"
        else:
            dimension_formula = f"dim J(Q_{prime})[2]=4-1=3"
        require(
            len(full_span) == 2**full_dimension_upper_bound,
            f"the complete J(Q_{prime})/2 dimension gate failed",
        )

        h_generators = [descent_h(value) for value in x_values]
        require(
            tuple(h_generators) == EXPECTED_H_VALUES[prime],
            f"normalized A/2 evaluations changed at {prime}",
        )
        h_span = gaussian_span(h_generators)
        h_image = locally_distinct_span(h_span, prime)
        h_dimension = (len(h_image)).bit_length() - 1
        require(
            len(h_image) == 2 ** expected_h_dimensions[prime],
            f"wrong complete hat-phi local image dimension at {prime}",
        )
        local_h_generators[prime] = h_generators
        local_h_images[prime] = h_image

        if prime == 17:
            require(
                not gaussian_local_equal(h_generators[0], (Fraction(1), Fraction(0)), 17),
                "the active h-value at 17 unexpectedly became a local square",
            )
            require(
                gaussian_local_equal(h_generators[1], (Fraction(1), Fraction(0)), 17)
                and gaussian_local_equal(
                    h_generators[2], (Fraction(1), Fraction(0)), 17
                ),
                "the two trivial h-values at 17 are not local squares",
            )

        local_payload[str(prime)] = {
            "x_basis": [fraction_text(value) for value in x_values],
            "x_values_are_local_points": True,
            "full_J_mod_2_dimension": full_dimension_upper_bound,
            "full_J_mod_2_completeness": dimension_formula,
            "full_Kummer_span_size": len(full_span),
            "h=A/2_values": [gaussian_text(value) for value in h_generators],
            "hat_phi_local_image_dimension": h_dimension,
            "hat_phi_local_image_size": len(h_image),
            "ambient_H1_dimension": 4,
            "phi_orthogonal_dimension": 4 - h_dimension,
        }

    def candidate_in_hat_local_image(mask: int, prime: int) -> bool:
        candidate = candidates[mask]
        return any(
            gaussian_local_equal(candidate, local, prime)
            for local in local_h_images[prime]
        )

    hat_individual: dict[int, list[int]] = {}
    hat_cumulative: dict[int, list[int]] = {}
    hat_survivors = list(range(64))
    hat_counts = [len(hat_survivors)]
    for prime in BAD_PRIMES:
        individual = [
            mask for mask in range(64)
            if candidate_in_hat_local_image(mask, prime)
        ]
        require(
            individual == EXPECTED_HAT_INDIVIDUAL_MASKS[prime],
            f"hat-phi individual local masks changed at {prime}",
        )
        hat_individual[prime] = individual
        hat_survivors = [
            mask for mask in hat_survivors
            if candidate_in_hat_local_image(mask, prime)
        ]
        require(
            hat_survivors == EXPECTED_HAT_CUMULATIVE_MASKS[prime],
            f"hat-phi cumulative masks changed at {prime}",
        )
        hat_cumulative[prime] = list(hat_survivors)
        hat_counts.append(len(hat_survivors))
    require(hat_counts == [64, 32, 16, 4], "wrong hat-phi survivor chain")
    require(hat_survivors == [0, 1, 8, 9], "wrong final hat-phi masks")

    def hilbert_pair(
        left: Gaussian,
        right: Gaussian,
        prime: int,
        *,
        conjugate_left: bool,
    ) -> int:
        if conjugate_left:
            left = gaussian_conjugate(left)
        left_pari = gaussian_to_pari(pari, t_mod, left)
        right_pari = gaussian_to_pari(pari, t_mod, right)
        result = 1
        for ideal in gaussian_prime_ideals[prime]:
            symbol = int(
                pari.nfhilbert(gaussian_nf, left_pari, right_pari, ideal)
            )
            require(symbol in (-1, 1), f"non-binary Hilbert symbol at {prime}")
            result *= symbol
        return result

    # A G-equivariant perfect identification of the permutation module
    # Res(mu_2) with its dual differs by an invertible matrix centralizing
    # conjugation.  Exhaustive GL_2(F_2) enumeration proves there are exactly
    # two: identity and swap.  We run the Selmer computation for both.
    identity_matrix = (1, 0, 0, 1)
    swap_matrix = (0, 1, 1, 0)
    centralizer = []
    for entries in product((0, 1), repeat=4):
        matrix = tuple(entries)
        if determinant_mod2(matrix) != 1:
            continue
        if matrix_multiply_mod2(matrix, swap_matrix) == matrix_multiply_mod2(
            swap_matrix, matrix
        ):
            centralizer.append(matrix)
    require(
        sorted(centralizer) == sorted([identity_matrix, swap_matrix]),
        "pairing-convention audit did not leave exactly identity and swap",
    )

    def phi_local_condition(
        mask: int, prime: int, *, conjugate_left: bool
    ) -> bool:
        candidate = candidates[mask]
        return all(
            hilbert_pair(
                candidate,
                generator,
                prime,
                conjugate_left=conjugate_left,
            )
            == 1
            for generator in local_h_generators[prime]
        )

    pairing_results: dict[str, dict[str, object]] = {}
    for convention, conjugate_left in (
        ("identity", False),
        ("swap_or_conjugate", True),
    ):
        individual_by_prime: dict[int, list[int]] = {}
        cumulative_by_prime: dict[int, list[int]] = {}
        survivors = list(range(64))
        counts = [len(survivors)]
        for prime in BAD_PRIMES:
            individual = [
                mask
                for mask in range(64)
                if phi_local_condition(
                    mask, prime, conjugate_left=conjugate_left
                )
            ]
            if convention == "identity":
                require(
                    individual == EXPECTED_PHI_INDIVIDUAL_MASKS[prime],
                    f"phi individual orthogonal masks changed at {prime}",
                )
            individual_by_prime[prime] = individual
            survivors = [
                mask
                for mask in survivors
                if phi_local_condition(
                    mask, prime, conjugate_left=conjugate_left
                )
            ]
            if convention == "identity":
                require(
                    survivors == EXPECTED_PHI_CUMULATIVE_MASKS[prime],
                    f"phi cumulative orthogonal masks changed at {prime}",
                )
            cumulative_by_prime[prime] = list(survivors)
            counts.append(len(survivors))
        require(
            counts == [64, 8, 2, 2],
            f"phi survivor dimensions depend on pairing convention {convention}",
        )
        expected_final = [0, 33] if convention == "identity" else [0, 17]
        require(
            survivors == expected_final,
            f"unexpected final phi masks for convention {convention}",
        )
        pairing_results[convention] = {
            "individual_masks": {
                str(prime): values
                for prime, values in individual_by_prime.items()
            },
            "cumulative_masks": {
                str(prime): values
                for prime, values in cumulative_by_prime.items()
            },
            "survivor_counts": counts,
            "final_masks": survivors,
            "selmer_dimension": 1,
            "generator": "1+4*i" if convention == "identity" else "1-4*i",
        }

    def globally_equal(left: Gaussian, right: Gaussian) -> bool:
        quotient = gaussian_to_pari(
            pari, t_mod, gaussian_divide(left, right)
        )
        return bool(pari.nfeltissquare(gaussian_nf, quotient))

    one = (Fraction(1), Fraction(0))
    i_class = (Fraction(0), Fraction(1))
    two_minus_i = (Fraction(2), Fraction(-1))
    require(
        globally_equal(descent_h(Fraction(1)), i_class),
        "D=[(1,1)-infinity] does not map to [i]",
    )
    require(
        globally_equal(descent_h(Fraction(0)), two_minus_i),
        "T=[(0,0)-infinity] does not map to [2-i]",
    )
    require(
        globally_equal(candidates[0], one)
        and globally_equal(candidates[1], i_class)
        and globally_equal(candidates[8], two_minus_i),
        "named hat-phi survivor masks changed",
    )
    require(
        not globally_equal(i_class, one)
        and not globally_equal(two_minus_i, one)
        and not globally_equal(i_class, two_minus_i)
        and not globally_equal(
            gaussian_multiply(i_class, two_minus_i), one
        ),
        "the classes [i] and [2-i] are not independent",
    )
    require(
        globally_equal(candidates[33], (Fraction(1), Fraction(4))),
        "identity-pairing phi generator is not [1+4*i]",
    )
    require(
        globally_equal(candidates[17], (Fraction(1), Fraction(-4))),
        "swap-pairing phi generator is not [1-4*i]",
    )

    # Generalized Richelot evaluation at [P-infinity] is 8*A(x(P)).
    # The normalized function h=A/2 differs from it by the square 16.
    generalized_over_h = Fraction(16)
    require(
        isqrt(generalized_over_h.numerator) ** 2
        == generalized_over_h.numerator
        and isqrt(generalized_over_h.denominator) ** 2
        == generalized_over_h.denominator,
        "8*A and A/2 do not differ by a rational square",
    )
    raw_A_over_h = (Fraction(2), Fraction(0))
    require(
        globally_equal(raw_A_over_h, i_class),
        "the raw-A error class [2]=[i] was not detected",
    )
    require(
        not globally_equal(raw_A_over_h, one),
        "raw A unexpectedly has the same squareclass as A/2",
    )

    return {
        "generalized_descent_function": {
            "A": "2*x^2+2*i*x-1-2*i",
            "h": "A/2=x^2+i*x-(1+2*i)/2",
            "generalized_evaluation_for_[P-infinity]": "8*A(x(P))",
            "(8*A)/(A/2)": "16=(4)^2",
            "raw_A_is_wrong": True,
            "raw_A_over_h_squareclass": "[2]=[i]",
            "D_image": "[h(1)]=[1/2]=[i]",
            "T_image": "[h(0)]=[-(1+2*i)/2]=[2-i]",
            "D_T_images_independent": True,
            "D_T_independent_mod_2": (
                "their images are independent in J(Q)/hat_phi(Dhat(Q)); "
                "since 2J(Q) is contained in hat_phi(Dhat(Q)), they are "
                "independent in J(Q)/2J(Q)"
            ),
        },
        "local_completeness": (
            "The displayed x-classes give eight distinct classes in the "
            "complete full Kummer target J(Q_p)/2J(Q_p). Since "
            "2J=hat_phi(phi(J)) is contained in hat_phi(Dhat), their h-values "
            "surject onto the complete hat-phi local image. Local Tate "
            "duality makes the phi image its exact Hilbert orthogonal."
        ),
        "local_data": local_payload,
        "hat_phi": {
            "individual_masks": {
                str(prime): values for prime, values in hat_individual.items()
            },
            "cumulative_masks": {
                str(prime): values for prime, values in hat_cumulative.items()
            },
            "survivor_counts": hat_counts,
            "final_masks": hat_survivors,
            "selmer_dimension": 2,
            "generators": ["i", "2-i"],
        },
        "pairing_conventions": {
            "complete_G_equivariant_convention_set": ["identity", "swap"],
            "centralizer_GL2_F2": [list(matrix) for matrix in centralizer],
            "dimensions_are_convention_independent": True,
        },
        "phi": pairing_results,
    }


def verify_correct_twist_invariance(
    geometry: dict[str, object],
    kernel: dict[str, object],
    descent: dict[str, object],
) -> dict[str, object]:
    """Prove that the -1 target twist leaves every Selmer input unchanged."""

    x = sp.symbols("x")
    h1 = 2 * x**2 - 4 * x + 1
    quartic = 4 * x**4 + 4 * x**2 + 5
    negative_target = sp.expand(-2 * h1 * quartic)
    positive_target = sp.expand(2 * h1 * quartic)
    negative_discriminant = sp.factor(sp.discriminant(negative_target, x))
    positive_discriminant = sp.factor(sp.discriminant(positive_target, x))
    require(
        negative_discriminant
        == positive_discriminant
        == 2**47 * 5 * 17**2,
        "the corrected twist changed the finite bad-prime support",
    )
    require(
        geometry["kernel_etale_algebra"] == "Q x Q(i)"
        and geometry["bruin_doerksen_twist_squareclass"] == -1,
        "correct geometry does not expose the required twist module",
    )
    require(
        geometry["target_ordered_factors"] == ["h2", "h3", "2*h1"]
        and geometry["source_and_target_splittings_Galois_stable"] is True
        and geometry[
            "target_quadratic_and_quartic_irreducible_over_Q"
        ]
        is True,
        "corrected target splitting or rational 2-torsion gate changed",
    )
    require(
        kernel["source_kernel"] == "ker(phi)=Res_{Q(i)/Q}(mu_2)"
        and kernel["dual_kernel"] == "ker(hat_phi)=Res_{Q(i)/Q}(mu_2)",
        "source or dual kernel module changed under the twist",
    )
    require(
        kernel["source_conjugation"]
        == {"q1": "q1", "q2": "q3", "q3": "q2"}
        and kernel["target_conjugation"]
        == {"h1": "h1", "h2": "h3", "h3": "h2"},
        "kernel conjugation action changed under the twist",
    )
    require(
        kernel["bad_primes"] == [2, 5, 17],
        "the corrected twist changed the certified S set",
    )
    bad_prime_justification = kernel["bad_prime_justification"]
    require(
        bad_prime_justification["source_polynomial_discriminant"]
        == 2**14 * 5**2 * 17
        and bad_prime_justification["target_polynomial_discriminant"]
        == 2**47 * 5 * 17**2
        and bad_prime_justification["complete_finite_bad_prime_set"]
        == [2, 5, 17],
        "the exact discriminant audit does not certify the complete S set",
    )
    require(
        descent["pairing_conventions"]["complete_G_equivariant_convention_set"]
        == ["identity", "swap"]
        and descent["pairing_conventions"][
            "dimensions_are_convention_independent"
        ]
        is True,
        "the complete Cartier-pairing convention audit changed",
    )
    require(
        descent["hat_phi"]["survivor_counts"] == [64, 32, 16, 4]
        and all(
            data["survivor_counts"] == [64, 8, 2, 2]
            for data in descent["phi"].values()
        ),
        "a corrected-twist Selmer survivor chain changed",
    )
    generalized = descent["generalized_descent_function"]
    require(
        generalized["h"] == "A/2=x^2+i*x-(1+2*i)/2"
        and generalized["generalized_evaluation_for_[P-infinity]"]
        == "8*A(x(P))"
        and generalized["(8*A)/(A/2)"] == "16=(4)^2",
        "the generalized source descent map changed under the target twist",
    )
    return {
        "quadratic_twist_character": "-1",
        "geometric_twist_automorphism": "(t,V) -> (t,-V)",
        "jacobian_action_of_twist_automorphism": "[-1]",
        "action_on_2_torsion": (
            "trivial, because [-1] is the identity on every 2-torsion point"
        ),
        "source_kernel_module_unchanged": True,
        "dual_kernel_module_unchanged": True,
        "kernel_module": "Res_{Q(i)/Q}(mu_2)",
        "source_descent_function_unchanged": (
            "h=A/2=x^2+i*x-(1+2*i)/2"
        ),
        "target_root_partition_unchanged": True,
        "negative_target_discriminant": str(negative_discriminant),
        "positive_target_discriminant": str(positive_discriminant),
        "bad_prime_set_unchanged": [2, 5, 17],
        "complete_pairing_identifications": ["identity", "swap"],
        "local_Tate_orthogonals_unchanged": True,
        "justification": (
            "the twist cocycle acts as [-1], hence trivially on target "
            "2-torsion; the generalized 8*A source evaluation normalizes to "
            "the same h=A/2 by the square 16, and exact local Tate duality "
            "uses one of the exhaustively checked identity/swap perfect "
            "pairings. The factor roots, Res(mu_2) modules, and S set are "
            "also unchanged"
        ),
    }


def existing_full_descent_metadata() -> dict[str, object]:
    """Describe the existing certificate without making it a Target B premise."""

    return {
        "existing_method": "Schaefer--Stoll full 2-descent",
        "existing_raw_S_unit_classes": 8192,
        "existing_square_norm_kernel_size": 512,
        "existing_survivor_chain": [512, 64, 8, 4],
        "existing_selmer_dimension": 2,
        "existing_rank": 1,
        "richelot_method": {
            "global_classes_per_isogeny": 64,
            "hat_phi_survivor_chain": [64, 32, 16, 4],
            "phi_survivor_chain": [64, 8, 2, 2],
            "selmer_dimensions": [2, 1],
            "rank": 1,
        },
        "logical_dependency_of_Target_B_on_full_descent": False,
        "conclusion": (
            "Target B independently proves rank one. The existing full "
            "descent starts from a larger etale S-unit group and separately "
            "identifies its four Sel_2 classes as 0,D,T,D+T."
        ),
    }


def replay_existing_full_descent() -> dict[str, object]:
    """Optionally replay the old descent as a non-premise comparison."""

    # Avoid creating/updating __pycache__ in the read-only comparison repo.
    sys.dont_write_bytecode = True
    try:
        from research.arithmetic_geometry.product_genus2_two_descent import (
            verify as verify_full_descent,
        )
    except Exception as error:  # pragma: no cover - exercised on missing repo path
        raise CertificateFailure(
            "cannot import the existing full descent; set PYTHONPATH to cuboid-2"
        ) from error
    try:
        full = verify_full_descent()
    except Exception as error:
        raise CertificateFailure("the existing full descent did not replay") from error

    expected_chain = {
        "square_norm": 512,
        "at_2": 64,
        "at_5": 8,
        "at_17": 4,
    }
    require(
        full["successive_local_survivor_counts"] == expected_chain,
        "existing full 2-descent survivor chain changed",
    )
    require(full["raw_s_unit_classes"] == 8192, "full raw S-unit count changed")
    require(full["selmer_dimension"] == 2, "full Sel_2 dimension changed")
    require(full["rational_2_torsion_dimension"] == 1, "full J[2](Q) changed")
    require(full["rank_upper_bound"] == 1, "full-descent rank bound changed")
    return {
        "replayed": True,
        "raw_S_unit_classes": full["raw_s_unit_classes"],
        "square_norm_kernel_size": full["square_norm_kernel_size"],
        "survivor_chain": [512, 64, 8, 4],
        "selmer_dimension": full["selmer_dimension"],
        "rank_upper_bound": full["rank_upper_bound"],
    }


def verify(*, replay_full_descent: bool = False) -> dict[str, object]:
    """Run corrected geometry and both exact isogeny Selmer computations."""

    composition = certify_richelot_composition()
    require(
        composition["status"] == "PASS"
        and composition["composition"]["maps_defined_over_Q"] is True
        and composition["composition"]["hat_phi_o_phi"] == "[2]"
        and composition["composition"]["phi_o_hat_phi"] == "[2]",
        "the corrected Richelot correspondence/composition certificate failed",
    )
    geometry = verify_richelot_geometry(composition)
    bad_prime_audit = verify_bad_prime_support()
    pari = Pari()
    kernel, gaussian_nf, t_mod, gaussian_primes, candidates = (
        verify_kernel_and_s_units(pari, bad_prime_audit)
    )
    descent = verify_local_images_and_selmer(
        pari, gaussian_nf, t_mod, gaussian_primes, candidates
    )
    descent["correct_twist_invariance"] = verify_correct_twist_invariance(
        geometry, kernel, descent
    )

    hat_dimension = descent["hat_phi"]["selmer_dimension"]
    phi_dimensions = {
        convention: data["selmer_dimension"]
        for convention, data in descent["phi"].items()
    }
    require(
        hat_dimension == 2 and set(phi_dimensions.values()) == {1},
        "Selmer dimensions are not (2,1) for every pairing convention",
    )
    source_kernel_dimension = kernel["source_rational_kernel_dimension"]
    dual_kernel_dimension = kernel["dual_rational_kernel_dimension"]
    rank_plus_kernel_bound = hat_dimension + next(iter(phi_dimensions.values()))
    kernel_dimension_sum = source_kernel_dimension + dual_kernel_dimension
    rank_upper_bound = rank_plus_kernel_bound - kernel_dimension_sum
    require(
        rank_plus_kernel_bound == 3
        and kernel_dimension_sum == 2
        and rank_upper_bound == 1,
        "the exact isogeny rank inequality did not give r+2<=3",
    )
    require(
        geometry["source_J2_Q_dimension"] == source_kernel_dimension == 1
        and geometry["target_J2_Q_dimension"] == dual_kernel_dimension == 1,
        "irreducible factors do not identify the full rational 2-torsion kernels",
    )

    finite_rank = verify_finite_rank_lower_bound(bad_prime_audit)
    require(
        finite_rank["rank_lower_bound"] == rank_upper_bound == 1,
        "finite arithmetic and the Richelot upper bound do not prove rank one",
    )
    comparison = existing_full_descent_metadata()
    if replay_full_descent:
        comparison["optional_exact_replay"] = replay_existing_full_descent()
    payload: dict[str, object] = {
        "schema": 2,
        "target": "B",
        "status": "PASS",
        "richelot_composition_correspondence": composition,
        "richelot_geometry": geometry,
        "kernel_and_global_classes": kernel,
        "descent": descent,
        "rank_inequality": {
            "exact_dimension_formula": (
                "r + dim J(Q)[phi] + dim DhatJac(Q)[hat_phi] "
                "<= dim Sel_phi + dim Sel_hat_phi"
            ),
            "left_kernel_dimensions": [
                source_kernel_dimension,
                dual_kernel_dimension,
            ],
            "selmer_dimensions": {
                "hat_phi": hat_dimension,
                "phi": next(iter(phi_dimensions.values())),
            },
            "numerical_inequality": "r+2<=3",
            "rank_upper_bound": rank_upper_bound,
            "finite_rank_lower_bound": finite_rank,
            "rank": 1,
            "torsion": "Z/2Z generated by T",
        },
        "comparison_with_existing_full_descent": comparison,
        "conservatism": {
            "correct_Bruin_Doerksen_twist_used": True,
            "old_negative_target_rejected": True,
            "Q_rational_correspondence_checked_coefficientwise": True,
            "literal_transpose_checked_symbolically": True,
            "local_images_sampled_only": False,
            "local_completeness_certified_via_full_J_mod_2": True,
            "all_G_equivariant_pairing_conventions_checked": True,
            "local_masks_recomputed_after_twist_correction": True,
            "existing_full_descent_is_a_logical_dependency": False,
            "optional_full_descent_replayed": replay_full_descent,
        },
        "cypari2_version": distribution_version("cypari2"),
        "sympy_version": sp.__version__,
    }
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    """Run the certificate, write JSON only on success, and print a short audit."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--replay-full-descent",
        action="store_true",
        help="also replay the old full descent as a non-premise comparison",
    )
    args = parser.parse_args()
    if (
        args.replay_full_descent
        and args.output.resolve() == DEFAULT_OUTPUT.resolve()
    ):
        parser.error(
            "--replay-full-descent requires an explicit noncanonical --output"
        )
    try:
        payload = verify(replay_full_descent=args.replay_full_descent)
    except Exception as error:
        print("Correct-twist Richelot Target B certificate: FAIL")
        print(f"{type(error).__name__}: {error}")
        raise SystemExit(1) from error

    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print("Correct-twist Richelot Target B certificate: PASS")
    print("hat_phi survivors: 64 -> 32 -> 16 -> 4; dim=2; <i,2-i>")
    print(
        "phi survivors: 64 -> 8 -> 2 -> 2; dim=1; "
        "<1+4i> (or <1-4i> under the swap convention)"
    )
    print("rank inequality: r + 2 <= 2 + 1 = 3; finite reductions give r = 1")
    if args.replay_full_descent:
        print("optional full 2-descent replay: 512 -> 64 -> 8 -> 4; PASS")
    else:
        print("full 2-descent comparison: 512 -> 64 -> 8 -> 4 (not a premise)")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
