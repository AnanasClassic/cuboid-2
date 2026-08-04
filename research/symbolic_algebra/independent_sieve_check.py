#!/usr/bin/env python3
"""Independent normalized-model check of the seven-prime density certificate.

Unlike src/modular_sieve.py, this implementation works with P_s directly and
uses the reciprocal identity for the projective class at infinity.  Agreement
between the two implementations catches normalization and projectivization
errors, not merely loop errors.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product


PRIMES = (41, 61, 71, 73, 83, 89, 97)
EXPECTED_RESIDUAL_COUNTS = (22, 34, 28, 38, 40, 50, 42)


def normalized_quintic(s: int, ell: int) -> list[int]:
    """Coefficients of P_s, low degree first, in F_ell."""
    return [
        -s**5,
        -s**3 * (1 + 2 * s) * (-2 + 3 * s),
        -s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4),
        1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4,
        (2 + s) * (3 - 2 * s),
        1,
    ]


def remainder(poly: list[int], a: int, b: int, ell: int) -> tuple[int, int]:
    r0 = r1 = 0
    for coefficient in reversed(poly):
        r0, r1 = (-b * r1 + coefficient) % ell, (r0 - a * r1) % ell
    return r0, r1


def has_quadratic_divisor(poly: list[int], ell: int) -> bool:
    return any(remainder(poly, a, b, ell) == (0, 0) for a, b in product(range(ell), repeat=2))


def residual_projective_classes(ell: int) -> list[int | None]:
    """Return residual ratios r=p/q; None denotes q=0.

    For finite r, s=r^2.  For r=infinity, swap p and q and use s=0.
    The exact reciprocal identity is
        P_s(x) = -s^5*x^5*P_{1/s}(1/x),
    so the swap preserves the existence and degree of a quadratic factor.
    """
    residual: list[int | None] = []
    for r in list(range(ell)) + [None]:
        parameter = 0 if r is None else r * r % ell
        if has_quadratic_divisor(normalized_quintic(parameter, ell), ell):
            residual.append(r)
    return residual


def main() -> None:
    counts = tuple(len(residual_projective_classes(ell)) for ell in PRIMES)
    assert counts == EXPECTED_RESIDUAL_COUNTS
    residual_density = Fraction(1)
    for ell, count in zip(PRIMES, counts, strict=True):
        residual_density *= Fraction(count, ell + 1)
    excluded_density = 1 - residual_density
    assert residual_density == Fraction(88825, 13657329)
    assert excluded_density == Fraction(13568504, 13657329)
    print("primes:", PRIMES)
    print("residual counts:", counts)
    print("residual density:", residual_density)
    print("excluded density:", excluded_density)
    print("excluded decimal: %.12f" % float(excluded_density))


if __name__ == "__main__":
    main()
