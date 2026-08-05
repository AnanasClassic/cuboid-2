#!/usr/bin/env python3
"""Exact Frobenius fingerprints for the reciprocal genus-one quotient.

Let ``C`` be the normalization of the degree-ten cover whose geometric fibre
over ``s`` is the set of two-element subsets of the five roots of ``P_s``.
The reciprocal identity induces

    tau: (s, {r1,r2}) -> (1/s, {1/r1,1/r2}).

At every prime of good reduction considered here, the normalization of
``C/<tau>`` is the elliptic quotient ``E``.  The finite-set Burnside identity

    #E(F_p) = (#Fix(Frob_p on C) + #Fix(Frob_p*tau on C))/2

reduces its point count to exact root computations in F_p and F_{p^2}.

This file deliberately uses a small, pure-Python implementation of F_{p^2}
instead of Sage, Magma, or python-flint.  SymPy is used only for independent
factor-degree cross-checks and integer discriminants.  No curve is identified
from these traces, and no rank conclusion is made from them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import warnings
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Iterable

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = Path(__file__).with_name("frobenius_fingerprint.json")

s_symbol, x_symbol = sp.symbols("s x")
H6_EXPR = (
    s_symbol**6
    + 15 * s_symbol**5
    - 1585 * s_symbol**4
    + 3052 * s_symbol**3
    - 1585 * s_symbol**2
    + 15 * s_symbol
    + 1
)
SLOPE_EXPR = x_symbol**4 - 8 * x_symbol**2 - 12 * x_symbol - 4


Element = tuple[int, int]


@dataclass(frozen=True)
class Fp2:
    """The field F_p[u]/(u^2-d), with ``d`` the least nonsquare."""

    p: int
    d: int

    @classmethod
    def create(cls, p: int) -> "Fp2":
        assert p > 2 and sp.isprime(p)
        d = next(value for value in range(2, p) if pow(value, (p - 1) // 2, p) == p - 1)
        return cls(p=p, d=d)

    @property
    def zero(self) -> Element:
        return (0, 0)

    @property
    def one(self) -> Element:
        return (1, 0)

    def scalar(self, value: int) -> Element:
        return (value % self.p, 0)

    def add(self, left: Element, right: Element) -> Element:
        return ((left[0] + right[0]) % self.p, (left[1] + right[1]) % self.p)

    def neg(self, value: Element) -> Element:
        return ((-value[0]) % self.p, (-value[1]) % self.p)

    def sub(self, left: Element, right: Element) -> Element:
        return ((left[0] - right[0]) % self.p, (left[1] - right[1]) % self.p)

    def mul(self, left: Element, right: Element) -> Element:
        a, b = left
        c, e = right
        return ((a * c + self.d * b * e) % self.p, (a * e + b * c) % self.p)

    def square(self, value: Element) -> Element:
        return self.mul(value, value)

    def pow(self, value: Element, exponent: int) -> Element:
        assert exponent >= 0
        result = self.one
        base = value
        while exponent:
            if exponent & 1:
                result = self.mul(result, base)
            base = self.square(base)
            exponent >>= 1
        return result

    def inv(self, value: Element) -> Element:
        a, b = value
        norm = (a * a - self.d * b * b) % self.p
        assert norm
        inverse_norm = pow(norm, -1, self.p)
        return (a * inverse_norm % self.p, -b * inverse_norm % self.p)

    def frobenius(self, value: Element) -> Element:
        # Since d is a nonsquare, u^p=-u.
        return (value[0], -value[1] % self.p)

    def norm(self, value: Element) -> int:
        return (value[0] * value[0] - self.d * value[1] * value[1]) % self.p

    def elements(self) -> Iterable[Element]:
        return ((a, b) for a in range(self.p) for b in range(self.p))


def add(field: Fp2, *values: Element) -> Element:
    result = field.zero
    for value in values:
        result = field.add(result, value)
    return result


def mul(field: Fp2, *values: Element) -> Element:
    result = field.one
    for value in values:
        result = field.mul(result, value)
    return result


def powers(field: Fp2, value: Element, top: int) -> list[Element]:
    result = [field.one]
    for _ in range(top):
        result.append(field.mul(result[-1], value))
    return result


def p_coefficients(field: Fp2, parameter: Element) -> list[Element]:
    """Coefficients of P_s from constant through leading."""

    one = field.one
    two = field.scalar(2)
    three = field.scalar(3)
    four = field.scalar(4)
    ten = field.scalar(10)
    fourteen = field.scalar(14)
    s0, s1, s2, s3, s4, s5 = powers(field, parameter, 5)

    c4 = mul(field, add(field, two, s1), field.sub(three, mul(field, two, s1)))
    c3 = add(
        field,
        one,
        mul(field, ten, s1),
        mul(field, four, s2),
        field.neg(mul(field, fourteen, s3)),
        s4,
    )
    c2 = field.neg(
        mul(
            field,
            s1,
            add(
                field,
                one,
                field.neg(mul(field, fourteen, s1)),
                mul(field, four, s2),
                mul(field, ten, s3),
                s4,
            ),
        )
    )
    c1 = field.neg(
        mul(
            field,
            s3,
            add(field, one, mul(field, two, s1)),
            add(field, field.neg(two), mul(field, three, s1)),
        )
    )
    c0 = field.neg(s5)
    return [c0, c1, c2, c3, c4, one]


def h6(field: Fp2, parameter: Element) -> Element:
    coefficients = [1, 15, -1585, 3052, -1585, 15, 1]
    return evaluate(field, [field.scalar(value) for value in coefficients], parameter)


def slope_coefficients(field: Fp2) -> list[Element]:
    return [
        field.scalar(-4),
        field.scalar(-12),
        field.scalar(-8),
        field.zero,
        field.one,
    ]


def evaluate(field: Fp2, coefficients: list[Element], value: Element) -> Element:
    result = field.zero
    for coefficient in reversed(coefficients):
        result = field.add(field.mul(result, value), coefficient)
    return result


def derivative(field: Fp2, coefficients: list[Element]) -> list[Element]:
    return [field.mul(field.scalar(index), coefficient) for index, coefficient in enumerate(coefficients[1:], 1)]


def poly_trim(field: Fp2, polynomial: list[Element]) -> list[Element]:
    result = list(polynomial)
    while len(result) > 1 and result[-1] == field.zero:
        result.pop()
    return result


def poly_sub(field: Fp2, left: list[Element], right: list[Element]) -> list[Element]:
    size = max(len(left), len(right))
    result = [field.zero] * size
    for index in range(size):
        left_value = left[index] if index < len(left) else field.zero
        right_value = right[index] if index < len(right) else field.zero
        result[index] = field.sub(left_value, right_value)
    return poly_trim(field, result)


def poly_mul(field: Fp2, left: list[Element], right: list[Element]) -> list[Element]:
    result = [field.zero] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            index = left_index + right_index
            result[index] = field.add(
                result[index], field.mul(left_value, right_value)
            )
    return poly_trim(field, result)


def poly_divmod(
    field: Fp2,
    numerator: list[Element],
    denominator: list[Element],
) -> tuple[list[Element], list[Element]]:
    denominator = poly_trim(field, denominator)
    assert denominator != [field.zero]
    remainder = poly_trim(field, numerator)
    if len(remainder) < len(denominator):
        return [field.zero], remainder
    quotient = [field.zero] * (len(remainder) - len(denominator) + 1)
    inverse_leading = field.inv(denominator[-1])
    while remainder != [field.zero] and len(remainder) >= len(denominator):
        shift = len(remainder) - len(denominator)
        coefficient = field.mul(remainder[-1], inverse_leading)
        quotient[shift] = coefficient
        subtraction = [field.zero] * shift + [
            field.mul(coefficient, value) for value in denominator
        ]
        remainder = poly_sub(field, remainder, subtraction)
    return poly_trim(field, quotient), remainder


def poly_monic(field: Fp2, polynomial: list[Element]) -> list[Element]:
    polynomial = poly_trim(field, polynomial)
    if polynomial == [field.zero]:
        return polynomial
    inverse_leading = field.inv(polynomial[-1])
    return [field.mul(coefficient, inverse_leading) for coefficient in polynomial]


def poly_gcd(field: Fp2, left: list[Element], right: list[Element]) -> list[Element]:
    left = poly_trim(field, left)
    right = poly_trim(field, right)
    while right != [field.zero]:
        _, remainder = poly_divmod(field, left, right)
        left, right = right, remainder
    return poly_monic(field, left)


def poly_mod(
    field: Fp2,
    polynomial: list[Element],
    modulus: list[Element],
) -> list[Element]:
    return poly_divmod(field, polynomial, modulus)[1]


def poly_powmod(
    field: Fp2,
    base: list[Element],
    exponent: int,
    modulus: list[Element],
) -> list[Element]:
    result = [field.one]
    base = poly_mod(field, base, modulus)
    while exponent:
        if exponent & 1:
            result = poly_mod(field, poly_mul(field, result, base), modulus)
        base = poly_mod(field, poly_mul(field, base, base), modulus)
        exponent >>= 1
    return result


def extension_root_count(
    field: Fp2,
    coefficients: list[Element],
    extension_degree: int,
) -> int:
    """Number of distinct roots in F_{p^extension_degree}."""

    x_polynomial = [field.zero, field.one]
    frobenius_polynomial = poly_powmod(
        field,
        x_polynomial,
        field.p**extension_degree,
        coefficients,
    )
    gcd = poly_gcd(
        field,
        coefficients,
        poly_sub(field, frobenius_polynomial, x_polynomial),
    )
    return len(gcd) - 1


def norm_one_root_count(field: Fp2, coefficients: list[Element]) -> int:
    """Number of roots satisfying r^(p+1)=1."""

    powered = poly_powmod(
        field,
        [field.zero, field.one],
        field.p + 1,
        coefficients,
    )
    gcd = poly_gcd(
        field,
        coefficients,
        poly_sub(field, powered, [field.one]),
    )
    return len(gcd) - 1


def roots_in_fp2(field: Fp2, coefficients: list[Element]) -> list[Element]:
    return [value for value in field.elements() if evaluate(field, coefficients, value) == field.zero]


def roots_in_fp(roots: list[Element]) -> list[Element]:
    return [root for root in roots if root[1] == 0]


def choose_two(number: int) -> int:
    return number * (number - 1) // 2


def factor_degree_pair_count(coefficients: list[int], p: int) -> int:
    """Independent SymPy factor-degree count for a squarefree polynomial."""

    poly = sp.Poly(
        sum(value * x_symbol**index for index, value in enumerate(coefficients)),
        x_symbol,
        modulus=p,
    )
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", SymPyDeprecationWarning)
        _, factors = sp.factor_list(poly, modulus=p)
    assert all(exponent == 1 for _, exponent in factors)
    n1 = sum(1 for factor, _ in factors if factor.degree() == 1)
    n2 = sum(1 for factor, _ in factors if factor.degree() == 2)
    return choose_two(n1) + n2


def generic_rational_fibre(field: Fp2, parameter: int) -> int:
    coefficients = p_coefficients(field, field.scalar(parameter))
    assert len(poly_gcd(field, coefficients, derivative(field, coefficients))) == 1
    n1 = extension_root_count(field, coefficients, 1)
    n_fp2 = extension_root_count(field, coefficients, 2)
    count = choose_two(n1) + (n_fp2 - n1) // 2
    integer_coefficients = [coefficient[0] for coefficient in coefficients]
    assert count == factor_degree_pair_count(integer_coefficients, field.p)
    return count


def h6_rational_fibre(field: Fp2, parameter: int) -> int:
    coefficients = p_coefficients(field, field.scalar(parameter))
    repeated = poly_gcd(field, coefficients, derivative(field, coefficients))
    assert len(repeated) == 2 and repeated[0][1] == 0
    n1 = extension_root_count(field, coefficients, 1) - 1
    n_fp2 = extension_root_count(field, coefficients, 2) - 1
    # One place from the colliding pair, one mixed inertia orbit for each
    # fixed remaining root, and the stable pairs of the remaining cubic.
    return 1 + n1 + choose_two(n1) + (n_fp2 - n1) // 2


def zero_or_infinity_fibre(p: int) -> int:
    # At s=0, inertia fixes A,B,C and swaps D,E.  Frobenius either fixes or
    # swaps A,B according as x^2+6x+1 (discriminant 32) splits.
    split = pow(32 % p, (p - 1) // 2, p) == 1
    return 7 if split else 3


def one_fibre(field: Fp2) -> int:
    coefficients = slope_coefficients(field)
    assert len(poly_gcd(field, coefficients, derivative(field, coefficients))) == 1
    n1 = extension_root_count(field, coefficients, 1)
    n_fp2 = extension_root_count(field, coefficients, 2)
    # One rational branch near +1 and four branches near -1 with residues
    # given by the slope quartic.
    count = n1 + choose_two(n1) + (n_fp2 - n1) // 2
    integer_coefficients = [-4, -12, -8, 0, 1]
    poly = sp.Poly(
        sum(value * x_symbol**index for index, value in enumerate(integer_coefficients)),
        x_symbol,
        modulus=field.p,
    )
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", SymPyDeprecationWarning)
        _, factors = sp.factor_list(poly, modulus=field.p)
    factor_count = sum(1 for factor, _ in factors if factor.degree() == 1)
    factor_count += choose_two(sum(1 for factor, _ in factors if factor.degree() == 1))
    factor_count += sum(1 for factor, _ in factors if factor.degree() == 2)
    assert count == factor_count
    return count


def minus_one_fibre(p: int) -> int:
    # A 5-cycle has two orbits on unordered pairs; Frobenius fixes both for
    # p=+/-1 mod 5 and exchanges them for p=+/-2 mod 5.
    return 2 if p % 5 in (1, 4) else 0


def count_c(field: Fp2) -> tuple[int, dict[str, int]]:
    p = field.p
    counts = {
        "infinity": zero_or_infinity_fibre(p),
        "s=0": zero_or_infinity_fibre(p),
        "s=1": one_fibre(field),
        "s=-1": minus_one_fibre(p),
        "h6": 0,
        "generic": 0,
    }
    for parameter in range(p):
        if parameter in (0, 1, p - 1):
            continue
        if h6(field, field.scalar(parameter)) == field.zero:
            counts["h6"] += h6_rational_fibre(field, parameter)
        else:
            counts["generic"] += generic_rational_fibre(field, parameter)
    return sum(counts.values()), counts


def reciprocal_action(field: Fp2, root: Element) -> Element:
    """The action r -> 1/r^p on a root above a norm-one parameter."""

    assert root != field.zero
    return field.inv(field.frobenius(root))


def stable_pairs_under_reciprocal_frobenius(field: Fp2, roots: list[Element]) -> int:
    root_set = set(roots)
    permutation = {root: reciprocal_action(field, root) for root in roots}
    assert set(permutation.values()) == root_set
    direct = sum(
        1
        for left, right in combinations(roots, 2)
        if {permutation[left], permutation[right]} == {left, right}
    )
    fixed = sum(1 for root in roots if permutation[root] == root)
    formula = choose_two(fixed) + (len(roots) - fixed) // 2
    assert direct == formula
    return direct


def twisted_generic_fibre(field: Fp2, parameter: Element) -> int:
    coefficients = p_coefficients(field, parameter)
    assert len(poly_gcd(field, coefficients, derivative(field, coefficients))) == 1
    n_fp2 = extension_root_count(field, coefficients, 2)
    fixed = norm_one_root_count(field, coefficients)
    count = choose_two(fixed) + (n_fp2 - fixed) // 2
    # Direct root and two-subset enumeration is retained as an independent
    # cross-check at the small primes, while the exact gcd method scales.
    if field.p <= 13:
        roots = roots_in_fp2(field, coefficients)
        assert count == stable_pairs_under_reciprocal_frobenius(field, roots)
    return count


def twisted_h6_fibre(field: Fp2, parameter: Element) -> int:
    coefficients = p_coefficients(field, parameter)
    repeated = poly_gcd(field, coefficients, derivative(field, coefficients))
    assert len(repeated) == 2
    double_root = field.neg(repeated[0])
    assert reciprocal_action(field, double_root) == double_root
    n_fp2_remaining = extension_root_count(field, coefficients, 2) - 1
    fixed_remaining = norm_one_root_count(field, coefficients) - 1
    # The colliding pair gives one fixed normalization place.  The three
    # mixed inertia orbits transform like the remaining roots.
    return (
        1
        + fixed_remaining
        + choose_two(fixed_remaining)
        + (n_fp2_remaining - fixed_remaining) // 2
    )


def count_frobenius_tau(field: Fp2) -> tuple[int, dict[str, int]]:
    norm_one = [value for value in field.elements() if value != field.zero and field.norm(value) == 1]
    assert len(norm_one) == field.p + 1
    counts = {"s=1": 0, "s=-1": 0, "h6": 0, "generic": 0}
    for parameter in norm_one:
        if parameter == field.one:
            counts["s=1"] += one_fibre(field)
        elif parameter == field.neg(field.one):
            counts["s=-1"] += minus_one_fibre(field.p)
        elif h6(field, parameter) == field.zero:
            counts["h6"] += twisted_h6_fibre(field, parameter)
        else:
            counts["generic"] += twisted_generic_fibre(field, parameter)
    return sum(counts.values()), counts


def bad_prime_certificate() -> dict[str, object]:
    h6_discriminant = int(sp.discriminant(H6_EXPR, s_symbol))
    slope_discriminant = int(sp.discriminant(SLOPE_EXPR, x_symbol))
    h6_at_one = int(H6_EXPR.subs(s_symbol, 1))
    h6_at_minus_one = int(H6_EXPR.subs(s_symbol, -1))
    # Inverting 120 is a conservative, fully transparent way to keep the
    # order of the splitting-field group (a subgroup of S_5) invertible.
    # We therefore make no good-reduction claim at p=3 in this certificate,
    # even though the same combinatorial special-fibre count can be run there.
    splitting_group_order_bound = 120
    controlling_integer = abs(
        splitting_group_order_bound
        * h6_discriminant
        * slope_discriminant
        * h6_at_one
        * h6_at_minus_one
    )
    factors = {
        str(int(prime)): int(exponent)
        for prime, exponent in sp.factorint(controlling_integer).items()
    }
    assert {int(prime) for prime in factors} == {2, 3, 5, 17, 43, 47}
    return {
        "h6_discriminant": h6_discriminant,
        "slope_quartic_discriminant": slope_discriminant,
        "h6_at_1": h6_at_one,
        "h6_at_minus_1": h6_at_minus_one,
        "splitting_group_order_bound": splitting_group_order_bound,
        "controlling_integer_factorization": factors,
        "excluded_primes": sorted(int(prime) for prime in factors),
        "reason": (
            "Outside these primes the branch sections 0, infinity, +/-1 and "
            "the six roots of H6 stay disjoint and separable; the local "
            "indices 2 and 5 are tame, the slope quartic at s=1 is separable, "
            "and the order of the splitting-field group divides the inverted "
            "bound 120. Exclusion does not assert that every listed prime is "
            "a prime of actual bad reduction."
        ),
    }


def trace_record(p: int) -> dict[str, object]:
    field = Fp2.create(p)
    count_c_value, c_breakdown = count_c(field)
    count_twisted, twisted_breakdown = count_frobenius_tau(field)
    assert (count_c_value + count_twisted) % 2 == 0
    count_e = (count_c_value + count_twisted) // 2
    trace = p + 1 - count_e
    assert trace * trace <= 4 * p
    return {
        "p": p,
        "fp2_nonsquare": field.d,
        "C_points": count_c_value,
        "C_breakdown": c_breakdown,
        "frobenius_tau_fixed": count_twisted,
        "frobenius_tau_breakdown": twisted_breakdown,
        "E_points": count_e,
        "trace": trace,
        "hasse_verified": True,
    }


def verify(bound: int = 97) -> dict[str, object]:
    certificate = bad_prime_certificate()
    bad_primes = set(certificate["excluded_primes"])
    good_primes = [int(p) for p in list(sp.primerange(3, bound + 1)) if int(p) not in bad_primes]
    records = [trace_record(p) for p in good_primes]
    expected = {
        7: -2,
        11: -4,
        13: 2,
        19: -4,
        23: -6,
        29: 8,
        31: 2,
        37: 4,
        41: -2,
        53: -6,
        59: -4,
        61: 4,
        67: -4,
        71: 6,
        73: -6,
        79: 10,
        83: 12,
        89: -10,
        97: -10,
    }
    if bound == 97:
        assert {record["p"]: record["trace"] for record in records} == expected

    payload: dict[str, object] = {
        "schema": 1,
        "curve": "E = normalization of C/<tau>",
        "tau": "(s,{r1,r2})->(1/s,{1/r1,1/r2})",
        "burnside_identity": (
            "#E(F_p)=(#Fix(Frob_p on C)+#Fix(Frob_p*tau on C))/2"
        ),
        "scope": (
            "Exact good-prime Frobenius fingerprint only; it does not identify "
            "a Weierstrass model, prove an isomorphism/isogeny, or determine rank."
        ),
        "method": {
            "Fp_root_count": "deg gcd(P,X^p-X)",
            "Fp2_root_count": "deg gcd(P,X^(p^2)-X)",
            "norm_one_root_count": "deg gcd(P,X^(p+1)-1)",
            "cross_checks": [
                "SymPy factor degrees for every generic rational fibre",
                "direct Fp2 root/two-subset enumeration for p<=13",
                "Burnside integrality",
                "Hasse bound for every reported trace",
            ],
        },
        "good_reduction_certificate": certificate,
        "bound": bound,
        "traces": records,
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=97)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify(args.bound)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("good primes:", ",".join(str(record["p"]) for record in payload["traces"]))
    print("traces:", ",".join(str(record["trace"]) for record in payload["traces"]))
    print("Burnside integrality and Hasse bounds: OK")
    try:
        displayed_output = args.output.resolve().relative_to(ROOT)
    except ValueError:
        displayed_output = args.output.resolve()
    print("wrote", displayed_output)


if __name__ == "__main__":
    main()
