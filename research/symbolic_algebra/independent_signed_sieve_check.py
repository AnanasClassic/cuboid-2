#!/usr/bin/env python3
"""Independent factorization-based check of the signed-square sieve.

The production certificate exhausts monic quadratic remainders.  This checker
instead factors each quintic over the finite field and enumerates degree-two
subproducts of its irreducible-factor multiset.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from src.modular_sieve import cuboid_quintic, projective_classes
from src.signed_square_sieve import sign_certificate


X = sp.Symbol("X")
PRIMES = [
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
    43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137,
]


def degree_two_constants(poly: list[int], ell: int) -> set[int]:
    expression = sum(coefficient * X**degree for degree, coefficient in enumerate(poly))
    _, factors = sp.factor_list(expression, modulus=ell)
    constants: set[int] = set()
    linear_constants: list[int] = []

    for factor, multiplicity in factors:
        polynomial = sp.Poly(factor, X, modulus=ell).monic()
        degree = polynomial.degree()
        constant = int(polynomial.TC()) % ell
        if degree == 2:
            constants.add(constant)
        elif degree == 1:
            linear_constants.extend([constant] * multiplicity)

    for first in range(len(linear_constants)):
        for second in range(first + 1, len(linear_constants)):
            constants.add(linear_constants[first] * linear_constants[second] % ell)
    return constants


def independent_classes(ell: int) -> tuple[set[tuple[int, int]], set[tuple[int, int]]]:
    squares = {value * value % ell for value in range(ell)}
    negatives = {-value % ell for value in squares}
    plus: set[tuple[int, int]] = set()
    minus: set[tuple[int, int]] = set()
    for pair in projective_classes(ell):
        constants = degree_two_constants(cuboid_quintic(*pair, ell), ell)
        if constants & squares:
            plus.add(pair)
        if constants & negatives:
            minus.add(pair)
    return plus, minus


def main() -> None:
    plus_density = Fraction(1)
    minus_density = Fraction(1)
    both_density = Fraction(1)
    for ell in PRIMES:
        certificate = sign_certificate(ell)
        plus, minus = independent_classes(ell)
        assert plus == {tuple(pair) for pair in certificate["plus_classes"]}
        assert minus == {tuple(pair) for pair in certificate["minus_classes"]}
        plus_density *= Fraction(len(plus), ell + 1)
        minus_density *= Fraction(len(minus), ell + 1)
        both_density *= Fraction(len(plus & minus), ell + 1)

    residual = plus_density + minus_density - both_density
    assert residual == Fraction(13169, 3917894203948032)
    print("independent signed-square factorization check: OK")
    print("residual density:", residual)
    print("excluded density:", 1 - residual)


if __name__ == "__main__":
    main()
