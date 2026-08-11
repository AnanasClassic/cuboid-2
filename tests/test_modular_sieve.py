from fractions import Fraction

import sympy as sp

from src.modular_sieve import (
    combined_density,
    cuboid_quintic,
    has_monic_quadratic_divisor,
    prime_certificate,
    projective_classes,
)


PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
CERTIFICATES = {ell: prime_certificate(ell) for ell in PRIMES}


def factorization_has_degree_two_divisor(poly, ell):
    """Independent criterion using SymPy's finite-field factorization."""
    X = sp.Symbol("X")
    expression = sum(coefficient * X**degree for degree, coefficient in enumerate(poly))
    _, factors = sp.factor_list(expression, modulus=ell)
    linear_multiplicity = sum(exponent for factor, exponent in factors if sp.degree(factor, X) == 1)
    return linear_multiplicity >= 2 or any(sp.degree(factor, X) == 2 for factor, _ in factors)


def test_projective_class_count_and_endpoints():
    for ell in PRIMES:
        classes = projective_classes(ell)
        assert len(classes) == ell + 1
        assert len(set(classes)) == ell + 1
        # p=0 or q=0 has an obvious degree-two divisor and cannot obstruct.
        assert has_monic_quadratic_divisor(cuboid_quintic(0, 1, ell), ell)
        assert has_monic_quadratic_divisor(cuboid_quintic(1, 0, ell), ell)


def test_bruteforce_certificates_against_finite_field_factorization():
    for ell in PRIMES:
        certificate = CERTIFICATES[ell]
        obstructed = {tuple(pair) for pair in certificate["obstructed_classes"]}
        independently_obstructed = {
            pair
            for pair in projective_classes(ell)
            if not factorization_has_degree_two_divisor(cuboid_quintic(*pair, ell), ell)
        }
        assert obstructed == independently_obstructed


def test_exact_combined_density():
    excluded, residual = combined_density([CERTIFICATES[ell] for ell in PRIMES])
    assert excluded == Fraction(5689139917, 5689253052)
    assert residual == Fraction(113135, 5689253052)
