#!/usr/bin/env python3
"""Independent compact replay of the genus-two p=7/p=23 sieve.

This deliberately does not import the primary finite-Jacobian certificate.
It uses SymPy polynomials for Cantor arithmetic and obtains #J(F_p)
independently from exhaustive counts of C(F_p) and C(F_{p^2}).
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")
x = sp.symbols("x")


def poly(expression, prime):
    return sp.Poly(expression, x, modulus=prime)


def monic(value):
    return value.monic()


def key(divisor, prime):
    u, v = divisor
    coefficients_u = tuple(int(entry) % prime for entry in u.all_coeffs())
    coefficients_v = tuple(int(entry) % prime for entry in v.all_coeffs())
    return coefficients_u, coefficients_v


def curve_poly(prime):
    return poly(x**5 - 2 * x**2 + (5 * pow(4, -1, prime)) * x, prime)


def xgcd(left, right):
    if right.is_zero:
        assert left.LC() == 1
        return left, left.one, left.zero
    if left.is_zero:
        assert right.LC() == 1
        return right, right.zero, right.one
    first, second, gcd = sp.gcdex(left, right)
    scale = gcd.LC()
    return gcd.monic(), first.exquo_ground(scale), second.exquo_ground(scale)


def cantor_add(first, second, prime):
    f = curve_poly(prime)
    u1, v1 = first
    u2, v2 = second
    d1, e1, e2 = xgcd(u1, u2)
    d, c1, c2 = xgcd(d1, v1 + v2)
    s1, s2, s3 = c1 * e1, c1 * e2, c2
    u = monic((u1 * u2).exquo(d * d))
    numerator = s1 * u1 * v2 + s2 * u2 * v1 + s3 * (v1 * v2 + f)
    v = numerator.exquo(d).rem(u)
    while u.degree() > 2:
        u = monic((f - v * v).exquo(u))
        v = (-v).rem(u)
    return monic(u), v


def point_divisor(a, original_R, prime):
    inverse_two = pow(2, -1, prime)
    return poly(x - a, prime), poly(original_R * inverse_two, prime)


def divisor_order(divisor, prime):
    identity = (poly(1, prime), poly(0, prime))
    current = identity
    for order in range(1, 2 * prime**2 + 100):
        current = cantor_add(current, divisor, prime)
        if key(current, prime) == key(identity, prime):
            return order
    raise AssertionError("order bound exceeded")


def least_nonsquare(prime):
    squares = {value * value % prime for value in range(prime)}
    return next(value for value in range(2, prime) if value not in squares)


def fp2_mul(left, right, nonsquare, prime):
    a, b = left
    c, d = right
    return ((a * c + nonsquare * b * d) % prime, (a * d + b * c) % prime)


def fp2_add(left, right, prime):
    return ((left[0] + right[0]) % prime, (left[1] + right[1]) % prime)


def fp2_scale(value, scalar, prime):
    return (value[0] * scalar % prime, value[1] * scalar % prime)


def fp2_pow(value, exponent, nonsquare, prime):
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = fp2_mul(result, value, nonsquare, prime)
        value = fp2_mul(value, value, nonsquare, prime)
        exponent //= 2
    return result


def curve_value_fp2(value, nonsquare, prime):
    fifth = fp2_pow(value, 5, nonsquare, prime)
    square = fp2_mul(value, value, nonsquare, prime)
    return fp2_add(
        fp2_add(fifth, fp2_scale(square, -2, prime), prime),
        fp2_scale(value, 5 * pow(4, -1, prime), prime),
        prime,
    )


def curve_counts_and_jacobian_order(prime):
    nonsquare = least_nonsquare(prime)
    elements = [(a, b) for a in range(prime) for b in range(prime)]
    square_root_counts = {value: 0 for value in elements}
    for value in elements:
        square = fp2_mul(value, value, nonsquare, prime)
        square_root_counts[square] += 1
    count_p2 = 1 + sum(
        square_root_counts[curve_value_fp2(value, nonsquare, prime)]
        for value in elements
    )

    count_p = 1
    for a in range(prime):
        rhs = (a**5 - 2 * a**2 + 5 * pow(4, -1, prime) * a) % prime
        count_p += sum(root * root % prime == rhs for root in range(prime))
    a1 = prime + 1 - count_p
    numerator = count_p2 - prime**2 - 1 + a1**2
    assert numerator % 2 == 0
    a2 = numerator // 2
    jacobian_order = 1 - a1 + a2 - prime * a1 + prime**2
    return count_p, count_p2, jacobian_order


def certificate_at_prime(prime):
    identity = (poly(1, prime), poly(0, prime))
    D = point_divisor(1, 1, prime)
    T = point_divisor(0, 0, prime)
    order_D = divisor_order(D, prime)
    assert divisor_order(T, prime) == 2
    table = {}
    current = identity
    for exponent in range(order_D):
        table[key(current, prime)] = (exponent, 0)
        with_torsion = cantor_add(current, T, prime)
        table[key(with_torsion, prime)] = (exponent, 1)
        current = cantor_add(current, D, prime)
    assert key(current, prime) == key(identity, prime)
    count_p, count_p2, jacobian_order = curve_counts_and_jacobian_order(prime)
    assert len(table) == 2 * order_D == jacobian_order

    square_a = {value * value % prime for value in range(prime)}
    classes = {(0, 0)}
    for a in square_a:
        rhs = (4 * a**5 - 8 * a**2 + 5 * a) % prime
        for original_R in range(prime):
            if original_R * original_R % prime == rhs:
                classes.add(table[key(point_divisor(a, original_R, prime), prime)])
    return {
        "C_Fp": count_p,
        "C_Fp2": count_p2,
        "J_Fp": jacobian_order,
        "D_order": order_D,
        "square_classes": [list(pair) for pair in sorted(classes)],
    }


def verify():
    at_3 = certificate_at_prime(3)
    at_7 = certificate_at_prime(7)
    at_23 = certificate_at_prime(23)
    assert at_3["J_Fp"] == 22 and at_3["D_order"] == 11
    assert at_7["J_Fp"] == 42 and at_7["D_order"] == 21
    assert at_23["J_Fp"] == 462 and at_23["D_order"] == 231
    assert {tuple(pair) for pair in at_7["square_classes"]} == {
        (0, 0), (1, 0), (20, 0), (5, 0), (16, 0), (0, 1)
    }
    p23 = {tuple(pair) for pair in at_23["square_classes"]}
    projection = {(exponent % 21, bit) for exponent, bit in p23}
    compatible = {tuple(pair) for pair in at_7["square_classes"]} & projection
    assert compatible == {(0, 0), (1, 0), (20, 0), (0, 1)}

    payload = {
        "schema": 1,
        "implementation": "independent SymPy Cantor arithmetic plus F_p2 point counts",
        "at_3": at_3,
        "at_7": at_7,
        "at_23": at_23,
        "compatible_classes": [list(pair) for pair in sorted(compatible)],
        "status": "PASS",
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("independent compact genus-two sieve: PASS")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
