#!/usr/bin/env python3
"""Exact Schaefer--Stoll 2-descent for the product genus-two curve.

Curve:

    D_+ : R^2 = a*(4*a^4 - 8*a + 5).

The script enumerates the complete S-unit square-norm kernel in
Q x Q[z]/(z^4-16z+20), and intersects it with exact local Kummer images at
2, 5 and 17.  The prime 17 is deliberately explicit: omitting it leaves an
eight-element false upper bound.

Requires cypari2.  PARI's certified class/unit computation is invoked; no
Magma, database rank, or bounded point search is used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from importlib.metadata import version as distribution_version
from math import isqrt
from pathlib import Path

from cypari2 import Pari


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
POLYNOMIAL = "z^4-16*z+20"
BAD_PRIMES = (2, 5, 17)
LOCAL_X_BASES = {
    2: (Fraction(1), Fraction(-4, 3), Fraction(1, 4)),
    5: (Fraction(1), Fraction(2), Fraction(-5)),
    17: (Fraction(-56), Fraction(-50), Fraction(-49)),
}


Pair = tuple[Fraction, object]


def rational_square(value: Fraction) -> bool:
    value = Fraction(value)
    return (
        value > 0
        and isqrt(value.numerator) ** 2 == value.numerator
        and isqrt(value.denominator) ** 2 == value.denominator
    )


def valuation_integer(value: int, prime: int) -> int:
    value = abs(value)
    result = 0
    while value and value % prime == 0:
        value //= prime
        result += 1
    return result


def rational_local_square(value: Fraction, prime: int) -> bool:
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
        return (
            (unit.numerator % 8) * pow(unit.denominator % 8, -1, 8) % 8 == 1
        )
    residue = (
        (unit.numerator % prime)
        * pow(unit.denominator % prime, -1, prime)
        % prime
    )
    return pow(residue, (prime - 1) // 2, prime) == 1


def pair_multiply(left: Pair, right: Pair) -> Pair:
    return left[0] * right[0], left[1] * right[1]


def pair_span(basis: list[Pair], pari: Pari) -> list[Pair]:
    result: list[Pair] = [(Fraction(1), pari(1))]
    for generator in basis:
        result += [pair_multiply(value, generator) for value in result]
    return result


def curve_polynomial(value: Fraction) -> Fraction:
    value = Fraction(value)
    return 4 * value**5 - 8 * value**2 + 5 * value


def verify() -> dict[str, object]:
    pari = Pari()
    nf = pari(f"nfinit({POLYNOMIAL})")
    bnf = pari(f"bnfinit({POLYNOMIAL})")
    z = pari(f"Mod(z,{POLYNOMIAL})")

    assert int(pari.bnfcertify(bnf)) == 1
    assert int(bnf.bnf_get_no()) == 1
    assert list(nf.nf_get_sign()) == [pari(0), pari(2)]
    assert str(bnf.bnf_get_cyc()) == "[]"
    assert int(pari.poldisc(pari(POLYNOMIAL))) == 2**14 * 17
    assert int(nf[2]) == 2**4 * 17
    assert int(nf[3]) == 32
    torsion_data = bnf.bnf_get_tu()
    assert int(torsion_data[0]) == 4
    torsion_generator = torsion_data[1]
    fundamental_units = list(bnf.bnf_get_fu())
    assert len(fundamental_units) == 1

    prime_ideals: dict[int, list] = {
        prime: list(pari(f"idealprimedec(nfinit({POLYNOMIAL}),{prime})"))
        for prime in BAD_PRIMES
    }
    assert {prime: len(values) for prime, values in prime_ideals.items()} == {
        2: 1,
        5: 3,
        17: 3,
    }
    all_s_primes = [
        ideal for prime in BAD_PRIMES for ideal in prime_ideals[prime]
    ]
    s_unit_data = pari.bnfsunit(bnf, all_s_primes)
    s_unit_generators = [
        pari(f"Mod({entry},{POLYNOMIAL})") for entry in list(s_unit_data[0])
    ]
    assert len(s_unit_generators) == 7

    # Four Q S-unit classes and nine K S-unit classes give the full raw
    # 13-dimensional group.  The K torsion generator has order four, hence
    # represents the nontrivial torsion class modulo squares; -1 itself is
    # a square in K and must not be used here.
    rational_basis = [Fraction(-1), Fraction(2), Fraction(5), Fraction(17)]
    field_basis = [torsion_generator] + fundamental_units + s_unit_generators
    raw_basis: list[Pair] = [
        (entry, pari(1)) for entry in rational_basis
    ] + [(Fraction(1), entry) for entry in field_basis]
    assert len(raw_basis) == 13
    raw_span = pair_span(raw_basis, pari)
    assert len(raw_span) == 8192

    norm_kernel: list[tuple[int, Pair]] = []
    for mask, value in enumerate(raw_span):
        norm = value[0] * Fraction(str(pari.nfeltnorm(nf, value[1])))
        if rational_square(norm):
            norm_kernel.append((mask, value))
    assert len(norm_kernel) == 512

    def local_equal(left: Pair, right: Pair, prime: int) -> bool:
        if not rational_local_square(left[0] / right[0], prime):
            return False
        quotient = left[1] / right[1]
        return all(
            bool(pari.nfislocalpower(nf, ideal, quotient, 2))
            for ideal in prime_ideals[prime]
        )

    def delta_x(value: Fraction) -> Pair:
        # theta=z/2 is a root of 4*a^4-8*a+5.
        return Fraction(value), pari(value) - z / 2

    local_counts = [len(norm_kernel)]
    survivors = norm_kernel
    local_basis_masks: dict[str, list[str]] = {}
    for prime in BAD_PRIMES:
        local_generators = [delta_x(value) for value in LOCAL_X_BASES[prime]]
        # The displayed x-values really are local points.
        assert all(
            rational_local_square(curve_polynomial(value), prime)
            for value in LOCAL_X_BASES[prime]
        )
        local_image = pair_span(local_generators, pari)
        assert len(local_image) == 8
        # Completeness, not merely independence: over Q_2 the quartic is one
        # factor, so dim J(Q_2)/2J(Q_2)=g+dim J(Q_2)[2]=2+1=3.  At odd p,
        # the quartic has three Q_p factors (the three prime ideals above p),
        # so f=a*g has four factors and dim J(Q_p)[2]=4-1=3.
        local_dimension = 3
        assert len(local_image) == 2**local_dimension
        # Exact pairwise distinction certifies that the three Kummer values
        # span the full three-dimensional local image used in the descent.
        for first_index, first in enumerate(local_image):
            assert not any(
                local_equal(first, second, prime)
                for second in local_image[:first_index]
            )
        survivors = [
            entry
            for entry in survivors
            if any(local_equal(entry[1], local, prime) for local in local_image)
        ]
        local_counts.append(len(survivors))
        local_basis_masks[str(prime)] = [str(value) for value in LOCAL_X_BASES[prime]]

    assert local_counts == [512, 64, 8, 4]
    final_masks = [mask for mask, _ in survivors]
    assert final_masks == [0, 96, 276, 372]

    def globally_equal(left: Pair, right: Pair) -> bool:
        return rational_square(left[0] / right[0]) and bool(
            pari.nfeltissquare(nf, left[1] / right[1])
        )

    identity = (Fraction(1), pari(1))
    D = delta_x(Fraction(1))
    # The Kummer value at the rational Weierstrass point a=0 is
    # (g(0), -theta)=(5,-z/2).
    T = (Fraction(5), -z / 2)
    named_values = {
        "identity": identity,
        "D": D,
        "T": T,
        "D_plus_T": pair_multiply(D, T),
    }
    expected_named_masks = {
        "identity": 0,
        "D": 96,
        "T": 372,
        "D_plus_T": 276,
    }
    named_masks: dict[str, int] = {}
    for name, named_value in named_values.items():
        matches = [
            mask
            for mask, survivor in survivors
            if globally_equal(survivor, named_value)
        ]
        assert len(matches) == 1
        named_masks[name] = matches[0]
    assert named_masks == expected_named_masks
    assert named_masks["D"] ^ named_masks["T"] == named_masks["D_plus_T"]

    # The rational factor a gives exactly one rational 2-torsion dimension.
    # Since the four Selmer classes are precisely 0,D,T,D+T, D and T are
    # independent modulo 2.  Thus rank <= 1; D is non-torsion (its reduction
    # has order 21 at 7 in the companion finite-group certificate), so rank=1.
    payload: dict[str, object] = {
        "schema": 1,
        "curve": "R^2=4*a^5-8*a^2+5*a",
        "etale_algebra": "Q x Q[z]/(z^4-16*z+20)",
        "defining_polynomial_discriminant": str(2**14 * 17),
        "field_discriminant": str(2**4 * 17),
        "power_order_index": 32,
        "class_number": 1,
        "field_signature": [0, 2],
        "roots_of_unity_order": 4,
        "bad_prime_set": list(BAD_PRIMES),
        "raw_s_unit_dimension": 13,
        "raw_s_unit_classes": 8192,
        "square_norm_kernel_size": 512,
        "local_x_bases": local_basis_masks,
        "successive_local_survivor_counts": {
            "square_norm": 512,
            "at_2": 64,
            "at_5": 8,
            "at_17": 4,
        },
        "prime_17_is_essential": True,
        "local_image_completeness": {
            "2": "dimension g+dim J(Q_2)[2]=2+1=3",
            "5": "dimension dim J(Q_5)[2]=4-1=3",
            "17": "dimension dim J(Q_17)[2]=4-1=3",
        },
        "final_masks": final_masks,
        "named_masks": named_masks,
        "selmer_dimension": 2,
        "rational_2_torsion_dimension": 1,
        "rank_upper_bound": 1,
        "D_and_T_independent_mod_2": True,
        "rank": 1,
        "torsion": "Z/2Z generated by T",
        "sha_2": 0,
        "rank_dependency": (
            "The rank lower bound and torsion bound use the companion exact "
            "finite-group certificate: #J(F_3)=22, #J(F_7)=42, and "
            "ord(D mod 7)=21."
        ),
        "cypari2_version": distribution_version("cypari2"),
        "theorem": (
            "Sel_2(J/Q)=<D,T> has dimension 2, J(Q) has rank 1 and "
            "torsion Z/2Z, and D,T are independent modulo 2."
        ),
        "logical_scope": (
            "This script alone proves Selmer dimension 2, D/T independence, "
            "and rank <=1. Rank=1, torsion Z/2Z, and Sha[2]=0 additionally "
            "use the explicitly named finite-group certificate."
        ),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("genus-two Schaefer--Stoll 2-descent: PASS")
    print("survivors 512 -> 64 -> 8 -> 4")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
