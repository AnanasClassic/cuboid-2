from fractions import Fraction

from src.signed_square_sieve import combined_density, sign_certificate


PRIMES = [
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
    43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137,
]


def test_sign_counts_and_density_through_137():
    certificates = [sign_certificate(prime) for prime in PRIMES]
    counts = {
        certificate["prime"]: (
            certificate["plus_count"],
            certificate["minus_count"],
            certificate["both_count"],
        )
        for certificate in certificates
    }
    assert counts[43] == (20, 12, 4)
    assert counts[67] == (40, 20, 12)
    assert counts[71] == (8, 24, 4)
    assert counts[83] == (24, 24, 8)

    excluded, residual = combined_density(certificates)
    assert residual == Fraction(13169, 3917894203948032)
    assert excluded == Fraction(3917894203934863, 3917894203948032)


def test_zero_parameter_survives_every_finite_prime():
    for prime in PRIMES:
        certificate = sign_certificate(prime)
        assert [0, 1] in certificate["both_classes"]
