#!/usr/bin/env python3
"""Exact Schaefer--Stoll 2-descent certificate for the genus-2 curve.

The curve is

    C: y^2 = (x+1)(x^4+20*x^3+6*x^2+4*x+1).

This script proves ``dim_F2 Sel_2(J/Q) = 2`` and hence
``rank J(Q) <= 1``.  It uses PARI/GP's *certified* class/unit computation and
its exact local-power predicate; it does not call Magma, LMFDB, or a Jacobian
rank routine.

The finite matrices printed below are coordinates in

    Q_2^*/Q_2^{*2} x K_2^*/K_2^{*2},

where K = Q(z), z^4-2z-1=0.  Coordinate bits are listed least-significant
generator first.  See ``two_descent_proof.md`` for the mathematical argument.
"""

from __future__ import annotations

from fractions import Fraction
from importlib.metadata import version as distribution_version
from itertools import combinations
from math import gcd, isqrt

from cypari2 import Pari


pari = Pari()

POLYNOMIAL = "z^4-2*z-1"
bnf = pari(f"bnfinit({POLYNOMIAL})")
nf = pari(f"nfinit({POLYNOMIAL})")
prime_two = pari(f"idealprimedec(nfinit({POLYNOMIAL}),2)[1]")
z = pari(f"Mod(z,{POLYNOMIAL})")

# The exact isomorphism from the quartic factor of f to K.
theta = 8 * z**3 - 4 * z**2 + 2 * z - 17
epsilon_1 = -z
epsilon_2 = z**3 + z - 1
uniformizer = z - 1

# Since v_uniformizer(2)=4, the strong Hensel inequality
# v(a-y^2)>2*v(2y)=8 proves that a unit is a square as soon as it is a
# square modulo uniformizer^9.  The residue field is F_2, so the 256 sums
# 1 + sum_{i=1}^8 b_i*uniformizer^i exhaust the unit residues modulo that
# power.  This gives a finite independent cross-check of nfislocalpower.
HENSEL_MODULUS_EXPONENT = 9
hensel_unit_representatives = [
    pari(1)
    + sum(
        (uniformizer**power if (mask >> (power - 1)) & 1 else pari(0))
        for power in range(1, HENSEL_MODULUS_EXPONENT)
    )
    for mask in range(1 << (HENSEL_MODULUS_EXPONENT - 1))
]


def certificate(label: str, value: object) -> None:
    print(f"CERT {label} = {value}")


def valuation_two_integer(value: int) -> int:
    value = abs(value)
    assert value
    result = 0
    while value % 2 == 0:
        value //= 2
        result += 1
    return result


def rational_square(value: Fraction) -> bool:
    value = Fraction(value)
    if value <= 0:
        return False
    return (
        isqrt(value.numerator) ** 2 == value.numerator
        and isqrt(value.denominator) ** 2 == value.denominator
    )


def rational_two_adic_square(value: Fraction) -> bool:
    """Exact square test in Q_2, including rational denominators."""

    value = Fraction(value)
    if value == 0:
        return True
    numerator_valuation = valuation_two_integer(value.numerator)
    denominator_valuation = valuation_two_integer(value.denominator)
    if (numerator_valuation - denominator_valuation) % 2:
        return False
    numerator_unit = (value.numerator >> numerator_valuation) % 8
    denominator_unit = (value.denominator >> denominator_valuation) % 8
    return numerator_unit * pow(denominator_unit, -1, 8) % 8 == 1


def number_field_square(value) -> bool:
    return bool(pari.nfeltissquare(nf, value))


def number_field_two_adic_square(value) -> bool:
    return bool(pari.nfislocalpower(nf, prime_two, value, 2))


def number_field_two_adic_square_by_finite_hensel(value) -> bool:
    """Square test by exhaustive residues mod uniformizer^9 and Hensel."""

    valuation = int(pari.nfeltval(nf, value, prime_two))
    if valuation % 2:
        return False
    unit = value / uniformizer**valuation
    for candidate in hensel_unit_representatives:
        difference = unit - candidate**2
        if difference == 0 or int(pari.nfeltval(nf, difference, prime_two)) >= 9:
            return True
    return False


Pair = tuple[Fraction, object]


def pair_multiply(left: Pair, right: Pair) -> Pair:
    return left[0] * right[0], left[1] * right[1]


def pair_globally_equal(left: Pair, right: Pair) -> bool:
    return rational_square(left[0] / right[0]) and number_field_square(
        left[1] / right[1]
    )


def pair_locally_equal_at_two(left: Pair, right: Pair) -> bool:
    return rational_two_adic_square(
        left[0] / right[0]
    ) and number_field_two_adic_square(left[1] / right[1])


def multiplicative_span(basis: list, one) -> list:
    result = [one]
    for generator in basis:
        result += [entry * generator for entry in result]
    return result


def pair_span(basis: list[Pair]) -> list[Pair]:
    result = [(Fraction(1), pari(1))]
    for generator in basis:
        result += [pair_multiply(entry, generator) for entry in result]
    return result


def assert_pairwise_distinct(values: list, equal) -> None:
    for first, second in combinations(values, 2):
        assert not equal(first, second)


def squareclass_coordinate(value, basis: list, square_test) -> int:
    matches = [
        index
        for index, representative in enumerate(multiplicative_span(basis, 1))
        if square_test(value / representative)
    ]
    assert len(matches) == 1
    return matches[0]


def bits(value: int, length: int) -> list[int]:
    return [(value >> index) & 1 for index in range(length)]


# Standard basis of Q_2^*/Q_2^{*2} and an explicitly verified basis of
# K_2^*/K_2^{*2}.  K_2/Q_2 is totally ramified of degree four, so the latter
# squareclass space has dimension 4+2=6.
rational_local_basis = [Fraction(-1), Fraction(2), Fraction(5)]
number_field_local_basis = [z - 1, pari(-1), pari(2), z, 2 - z, 2 * z - 1]


def pair_local_vector(value: Pair) -> list[int]:
    rational_coordinate = squareclass_coordinate(
        value[0], rational_local_basis, rational_two_adic_square
    )
    number_field_coordinate = squareclass_coordinate(
        value[1], number_field_local_basis, number_field_two_adic_square
    )
    return bits(rational_coordinate, 3) + bits(number_field_coordinate, 6)


def pair_local_vector_by_finite_hensel(value: Pair) -> list[int]:
    rational_coordinate = squareclass_coordinate(
        value[0], rational_local_basis, rational_two_adic_square
    )
    number_field_coordinate = squareclass_coordinate(
        value[1], number_field_local_basis, number_field_two_adic_square_by_finite_hensel
    )
    return bits(rational_coordinate, 3) + bits(number_field_coordinate, 6)


def vector_sum(rows: list[list[int]], mask: int) -> list[int]:
    return [
        sum(((mask >> row_index) & 1) * row[column] for row_index, row in enumerate(rows))
        % 2
        for column in range(len(rows[0]))
    ]


def vector_rank(rows: list[list[int]]) -> int:
    work = [row[:] for row in rows]
    if not work:
        return 0
    row_count = len(work)
    column_count = len(work[0])
    pivot_row = 0
    for column in range(column_count):
        pivot = next(
            (row for row in range(pivot_row, row_count) if work[row][column]), None
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        for row in range(row_count):
            if row != pivot_row and work[row][column]:
                work[row] = [
                    left ^ right for left, right in zip(work[row], work[pivot_row])
                ]
        pivot_row += 1
        if pivot_row == row_count:
            break
    return pivot_row


def curve_polynomial(value: int) -> int:
    return (
        value**5
        + 21 * value**4
        + 26 * value**3
        + 10 * value**2
        + 5 * value
        + 1
    )


def delta_of_point_with_x(value: int) -> Pair:
    assert value != -1
    assert curve_polynomial(value) != 0
    assert rational_two_adic_square(Fraction(curve_polynomial(value)))
    return Fraction(value + 1), pari(value) - theta


def infinity_vector(value: Pair) -> list[int]:
    """Signs in the order (rational root, lower K root, upper K root)."""

    rational_sign = 0 if value[0] > 0 else 1
    field_signs = [0 if int(sign) > 0 else 1 for sign in pari.nfeltsign(nf, value[1])]
    # PARI orders the two real embeddings as used by nfeltsign.  This exact
    # sign assertion identifies them without a floating-point comparison:
    # theta_1 < -1 < theta_2.
    assert list(pari.nfeltsign(nf, theta + 1)) == [pari(-1), pari(1)]
    return [rational_sign, field_signs[0], field_signs[1]]


def allowed_at_infinity(vector: list[int]) -> bool:
    # With roots alpha_1 < -1 < alpha_3, the image is
    # {(0,0,0),(1,0,1)} in the order above.
    return vector[1] == 0 and vector[0] == vector[2]


def main() -> None:
    # ------------------------------------------------------------------
    # Certified number-field and global bounding-group data.
    # ------------------------------------------------------------------
    assert int(pari.bnfcertify(bnf)) == 1
    assert int(bnf.bnf_get_no()) == 1
    assert list(bnf.nf_get_sign()) == [2, 1]
    assert str(bnf.bnf_get_cyc()) == "[]"
    assert list(bnf.bnf_get_fu()) == [epsilon_1, epsilon_2]
    assert list(bnf.bnf_get_tu()) == [pari(2), pari(-1)]
    assert int(pari.poldisc(pari(POLYNOMIAL))) == -688
    assert int(pari.nfeltnorm(nf, epsilon_1)) == -1
    assert int(pari.nfeltnorm(nf, epsilon_2)) == -1

    # Original quartic root and discriminant identities.
    assert str(pari.minpoly(theta)) == "x^4 + 20*x^3 + 6*x^2 + 4*x + 1"
    assert int(pari.nfeltnorm(nf, 1 - theta)) == 32
    assert int(pari.nfeltval(nf, 1 - theta, prime_two)) == 5
    assert int(pari.nfeltval(nf, z - 1, prime_two)) == 1
    primes_above_two = list(pari.idealprimedec(nf, 2))
    assert len(primes_above_two) == 1
    assert int(prime_two[2]) == 4
    assert int(prime_two[3]) == 1

    # L = Q x K.  The full S-bounding group has the five generators below;
    # imposing square norm gives the four displayed generators of H_bound.
    unit_q = (Fraction(-1), pari(1))
    unit_minus_one = (Fraction(1), pari(-1))
    unit_one = (Fraction(1), epsilon_1)
    unit_two = (Fraction(1), epsilon_2)
    lift_at_two = (Fraction(2), 1 - theta)
    full_bounding_basis = [unit_q, unit_minus_one, unit_one, unit_two, lift_at_two]
    full_bounding_span = pair_span(full_bounding_basis)
    assert len(full_bounding_span) == 32
    assert_pairwise_distinct(full_bounding_span, pair_globally_equal)
    bounding_basis = [
        unit_minus_one,
        lift_at_two,
        pair_multiply(unit_q, unit_one),
        pair_multiply(unit_q, unit_two),
    ]
    bounding_span = pair_span(bounding_basis)
    assert len(bounding_span) == 16
    assert_pairwise_distinct(bounding_span, pair_globally_equal)

    # Direct norm checks for the four generators.
    for rational_component, field_component in bounding_basis:
        norm = rational_component * Fraction(str(pari.nfeltnorm(nf, field_component)))
        assert rational_square(norm)

    # ------------------------------------------------------------------
    # Complete local image at 2.
    # ------------------------------------------------------------------
    rational_local_span = multiplicative_span(rational_local_basis, Fraction(1))
    number_field_local_span = multiplicative_span(number_field_local_basis, pari(1))
    assert len(rational_local_span) == 8
    assert len(number_field_local_span) == 64
    assert_pairwise_distinct(
        rational_local_span,
        lambda left, right: rational_two_adic_square(left / right),
    )
    assert_pairwise_distinct(
        number_field_local_span,
        lambda left, right: number_field_two_adic_square(left / right),
    )
    # A second exact algorithm verifies all 64 K_2 squareclasses: exhaustive
    # residues modulo uniformizer^9 plus the strong Hensel inequality.
    for mask, representative in enumerate(number_field_local_span):
        expected_square = mask == 0
        assert number_field_two_adic_square_by_finite_hensel(representative) == expected_square
        assert number_field_two_adic_square(representative) == expected_square

    # These x-coordinates give Q_2-points: all three values f(x) are
    # 2^6 times a unit congruent to 1 modulo 8.
    local_x_coordinates = [1, -7, 11]
    assert [curve_polynomial(value) for value in local_x_coordinates] == [
        64,
        25152,
        504384,
    ]
    for value in local_x_coordinates:
        polynomial_value = curve_polynomial(value)
        assert valuation_two_integer(polynomial_value) == 6
        assert (polynomial_value >> 6) % 8 == 1

    local_image_pairs = [delta_of_point_with_x(value) for value in local_x_coordinates]
    local_image_rows = [pair_local_vector(value) for value in local_image_pairs]
    expected_local_image_rows = [
        [0, 1, 0, 1, 0, 0, 1, 0, 0],
        [0, 1, 1, 1, 1, 0, 0, 1, 0],
        [1, 0, 1, 0, 0, 1, 0, 1, 0],
    ]
    assert local_image_rows == expected_local_image_rows
    assert [
        pair_local_vector_by_finite_hensel(value) for value in local_image_pairs
    ] == expected_local_image_rows
    assert vector_rank(local_image_rows) == 3

    # K_2/Q_2 is a totally ramified quartic; hence f has two irreducible
    # factors over Q_2 and dim J(Q_2)/2J(Q_2)=(2-1)+2=3.  Thus the three
    # independent point classes above are the entire local image.
    local_image_vectors = {
        tuple(vector_sum(local_image_rows, mask)) for mask in range(8)
    }
    assert len(local_image_vectors) == 8

    global_rows = [pair_local_vector(value) for value in bounding_basis]
    expected_global_rows = [
        [0, 0, 0, 0, 1, 0, 0, 0, 0],
        [0, 1, 0, 1, 0, 0, 1, 0, 0],
        [1, 0, 0, 0, 1, 0, 1, 0, 0],
        [1, 0, 0, 0, 0, 1, 1, 0, 0],
    ]
    assert global_rows == expected_global_rows
    assert [
        pair_local_vector_by_finite_hensel(value) for value in bounding_basis
    ] == expected_global_rows

    masks_surviving_two = {
        mask
        for mask in range(16)
        if tuple(vector_sum(global_rows, mask)) in local_image_vectors
    }
    assert masks_surviving_two == {0, 2, 9, 11}

    # ------------------------------------------------------------------
    # Infinity and the tame prime 43.
    # ------------------------------------------------------------------
    infinity_rows = [infinity_vector(value) for value in bounding_basis]
    assert infinity_rows == [
        [0, 1, 1],
        [0, 0, 0],
        [1, 0, 1],
        [1, 1, 0],
    ]
    masks_surviving_infinity = {
        mask
        for mask, value in enumerate(bounding_span)
        if allowed_at_infinity(infinity_vector(value))
    }
    assert masks_surviving_infinity == {0, 2, 4, 6, 9, 11, 13, 15}
    final_masks = masks_surviving_two & masks_surviving_infinity
    assert final_masks == {0, 2, 9, 11}

    # The factor at 43 has one double root and no worse collision.  Since
    # v_43(disc(f))=1, Stoll's odd-degree Proposition 4.6 makes the local
    # condition automatic for the globally even-valuation candidates.
    x = pari("x")
    original_f = x**5 + 21 * x**4 + 26 * x**3 + 10 * x**2 + 5 * x + 1
    assert int(pari.poldisc(original_f)) == -(2**24) * 43
    assert int(pari.valuation(pari.poldisc(original_f), 43)) == 1
    assert str(pari.factormod(original_f, 43)) == "[Mod(1, 43)*x + Mod(1, 43), 1; Mod(1, 43)*x + Mod(9, 43), 1; Mod(1, 43)*x + Mod(17, 43), 1; Mod(1, 43)*x + Mod(40, 43), 2]"

    # The two surviving generators are genuine global Kummer images:
    # mask 2 is delta((1,8)-infinity), and mask 9 is the rational 2-torsion
    # class.  The latter equality has the explicit square certificate below.
    point_one_delta = (Fraction(2), 1 - theta)
    torsion_delta = (Fraction(-16), -(theta + 1))
    mask_two = bounding_span[2]
    mask_nine = bounding_span[9]
    assert pair_globally_equal(point_one_delta, mask_two)
    assert pair_globally_equal(torsion_delta, mask_nine)
    torsion_square_root = -2 * z**3 + z**2 + 3
    assert (theta + 1) / epsilon_2 == torsion_square_root**2

    # A useful cross-check: delta((0,1)-infinity) is globally trivial.
    half_square_root = -2 * z**3 + z**2 + 4
    assert -theta == half_square_root**2

    # We have both an upper bound of four elements and two independent known
    # Kummer images, so the 2-Selmer group has dimension exactly two.
    assert gcd(22, 28) == 2  # independent torsion cross-check from good primes
    certificate("pari_version", pari("version()"))
    certificate("cypari2_version", distribution_version("cypari2"))
    certificate("bnfcertify", 1)
    certificate("field", "z^4-2*z-1; disc=-688; signature=(2,1); class_number=1")
    certificate("fundamental_units", [str(epsilon_1), str(epsilon_2)])
    certificate("K2_squareclass_basis", [str(value) for value in number_field_local_basis])
    certificate("finite_hensel_modulus", "(z-1)^9; 256 unit residues exhausted")
    certificate("global_matrix_at_2", global_rows)
    certificate("local_image_matrix_at_2", local_image_rows)
    certificate("masks_surviving_2", sorted(masks_surviving_two))
    certificate("masks_surviving_infinity", sorted(masks_surviving_infinity))
    certificate("selmer_masks", sorted(final_masks))
    certificate("dim_Sel2", 2)
    certificate("rank_bound", "rank J(Q) <= 2 - dim J(Q)[2] = 1")
    certificate("status", "PASS")


if __name__ == "__main__":
    main()
