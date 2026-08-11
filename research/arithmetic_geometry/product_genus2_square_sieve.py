#!/usr/bin/env python3
"""Exact finite Jacobian and two-prime square-abscissa sieve.

All polynomial and Cantor arithmetic below is implemented over finite prime
fields with Python integers.  The computation is exhaustive, not random.
It proves the p=7 and p=23 Mordell--Weil sieve statement used in the final
rational-point classification.  Crucially, the index of <D,T> in J(Q) is
allowed to be an unknown odd integer; the compatibility lemma eliminates it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


Poly = tuple[int, ...]                 # coefficients, low degree first
Divisor = tuple[Poly, Poly]            # reduced Mumford pair (u,v)


def trim(poly: tuple[int, ...] | list[int], prime: int) -> Poly:
    values = [value % prime for value in poly]
    while len(values) > 1 and values[-1] == 0:
        values.pop()
    return tuple(values or [0])


def p_add(left: Poly, right: Poly, prime: int) -> Poly:
    length = max(len(left), len(right))
    return trim(
        [
            (left[index] if index < len(left) else 0)
            + (right[index] if index < len(right) else 0)
            for index in range(length)
        ],
        prime,
    )


def p_neg(poly: Poly, prime: int) -> Poly:
    return trim([-value for value in poly], prime)


def p_sub(left: Poly, right: Poly, prime: int) -> Poly:
    return p_add(left, p_neg(right, prime), prime)


def p_mul(left: Poly, right: Poly, prime: int) -> Poly:
    values = [0] * (len(left) + len(right) - 1)
    for i, first in enumerate(left):
        for j, second in enumerate(right):
            values[i + j] += first * second
    return trim(values, prime)


def p_scale(poly: Poly, scalar: int, prime: int) -> Poly:
    return trim([scalar * value for value in poly], prime)


def p_divmod(dividend: Poly, divisor: Poly, prime: int) -> tuple[Poly, Poly]:
    divisor = trim(divisor, prime)
    assert divisor != (0,)
    remainder = list(trim(dividend, prime))
    quotient = [0] * max(1, len(remainder) - len(divisor) + 1)
    inverse_lead = pow(divisor[-1], -1, prime)
    while len(remainder) >= len(divisor) and trim(remainder, prime) != (0,):
        degree = len(remainder) - len(divisor)
        coefficient = remainder[-1] * inverse_lead % prime
        quotient[degree] = coefficient
        for index, value in enumerate(divisor):
            remainder[index + degree] = (
                remainder[index + degree] - coefficient * value
            ) % prime
        remainder = list(trim(remainder, prime))
    return trim(quotient, prime), trim(remainder, prime)


def p_exact_div(dividend: Poly, divisor: Poly, prime: int) -> Poly:
    quotient, remainder = p_divmod(dividend, divisor, prime)
    assert remainder == (0,)
    return quotient


def p_monic(poly: Poly, prime: int) -> Poly:
    poly = trim(poly, prime)
    assert poly != (0,)
    return p_scale(poly, pow(poly[-1], -1, prime), prime)


def p_xgcd(left: Poly, right: Poly, prime: int) -> tuple[Poly, Poly, Poly]:
    old_r, r = trim(left, prime), trim(right, prime)
    old_s, s = (1,), (0,)
    old_t, t = (0,), (1,)
    while r != (0,):
        quotient, new_r = p_divmod(old_r, r, prime)
        old_r, r = r, new_r
        old_s, s = s, p_sub(old_s, p_mul(quotient, s, prime), prime)
        old_t, t = t, p_sub(old_t, p_mul(quotient, t, prime), prime)
    scale = pow(old_r[-1], -1, prime)
    return (
        p_scale(old_r, scale, prime),
        p_scale(old_s, scale, prime),
        p_scale(old_t, scale, prime),
    )


def curve_monic(prime: int) -> Poly:
    # w=R/2: w^2=a^5-2a^2+(5/4)a.
    return trim((0, 5 * pow(4, -1, prime), -2, 0, 0, 1), prime)


def curve_original_value(a: int, prime: int) -> int:
    return (4 * a**5 - 8 * a**2 + 5 * a) % prime


def cantor_add(first: Divisor, second: Divisor, prime: int) -> Divisor:
    u1, v1 = first
    u2, v2 = second
    f = curve_monic(prime)

    d1, e1, e2 = p_xgcd(u1, u2, prime)
    d, c1, c2 = p_xgcd(d1, p_add(v1, v2, prime), prime)
    s1 = p_mul(c1, e1, prime)
    s2 = p_mul(c1, e2, prime)
    s3 = c2

    u = p_exact_div(p_mul(u1, u2, prime), p_mul(d, d, prime), prime)
    numerator = p_add(
        p_add(
            p_mul(p_mul(s1, u1, prime), v2, prime),
            p_mul(p_mul(s2, u2, prime), v1, prime),
            prime,
        ),
        p_mul(s3, p_add(p_mul(v1, v2, prime), f, prime), prime),
        prime,
    )
    v = p_exact_div(numerator, d, prime)
    u = p_monic(u, prime)
    _, v = p_divmod(v, u, prime)

    while len(u) - 1 > 2:
        quotient = p_exact_div(p_sub(f, p_mul(v, v, prime), prime), u, prime)
        u = p_monic(quotient, prime)
        _, v = p_divmod(p_neg(v, prime), u, prime)
    return p_monic(u, prime), trim(v, prime)


def point_divisor(a: int, original_R: int, prime: int) -> Divisor:
    w = original_R * pow(2, -1, prime) % prime
    return trim((-a, 1), prime), trim((w,), prime)


def divisor_neg(divisor: Divisor, prime: int) -> Divisor:
    return divisor[0], p_neg(divisor[1], prime)


def divisor_order(divisor: Divisor, prime: int) -> int:
    identity: Divisor = ((1,), (0,))
    value = identity
    for order in range(1, 10 * prime * prime + 1):
        value = cantor_add(value, divisor, prime)
        if value == identity:
            return order
    raise AssertionError("order bound exceeded")


def all_reduced_divisors(prime: int) -> set[Divisor]:
    f = curve_monic(prime)
    answer: set[Divisor] = {((1,), (0,))}
    # degree one u=x+c, v=d
    for c in range(prime):
        u = (c, 1)
        for d in range(prime):
            v = (d,)
            if p_divmod(p_sub(f, p_mul(v, v, prime), prime), u, prime)[1] == (0,):
                answer.add((u, v))
    # degree two u=x^2+b*x+c, v=d*x+e
    for b in range(prime):
        for c in range(prime):
            u = (c, b, 1)
            for d in range(prime):
                for e in range(prime):
                    v = trim((e, d), prime)
                    if p_divmod(
                        p_sub(f, p_mul(v, v, prime), prime), u, prime
                    )[1] == (0,):
                        answer.add((u, v))
    return answer


def sqrt_residues(value: int, prime: int) -> list[int]:
    return [root for root in range(prime) if root * root % prime == value % prime]


def finite_certificate(prime: int) -> dict[str, object]:
    identity: Divisor = ((1,), (0,))
    D = point_divisor(1, 1, prime)
    T = point_divisor(0, 0, prime)
    order_D = divisor_order(D, prime)
    assert divisor_order(T, prime) == 2

    table: dict[Divisor, tuple[int, int]] = {}
    current = identity
    for exponent in range(order_D):
        assert current not in table
        table[current] = (exponent, 0)
        with_torsion = cantor_add(current, T, prime)
        assert with_torsion not in table
        table[with_torsion] = (exponent, 1)
        current = cantor_add(current, D, prime)
    assert current == identity

    all_divisors = all_reduced_divisors(prime)
    assert set(table) == all_divisors

    square_a = {value * value % prime for value in range(prime)}
    square_point_rows: list[dict[str, int | str]] = [
        {"a": "infinity", "R": "infinity", "D_exponent": 0, "T_bit": 0}
    ]
    square_classes = {(0, 0)}
    for a in sorted(square_a):
        for original_R in sqrt_residues(curve_original_value(a, prime), prime):
            divisor = point_divisor(a, original_R, prime)
            exponent, torsion_bit = table[divisor]
            square_classes.add((exponent, torsion_bit))
            square_point_rows.append(
                {
                    "a": a,
                    "R": original_R,
                    "D_exponent": exponent,
                    "T_bit": torsion_bit,
                }
            )

    return {
        "prime": prime,
        "jacobian_order": len(all_divisors),
        "D_order": order_D,
        "T_order": 2,
        "D_T_generate_reduction": len(table) == len(all_divisors),
        "square_abscissa_classes": [list(pair) for pair in sorted(square_classes)],
        "square_abscissa_points": square_point_rows,
    }


def verify() -> dict[str, object]:
    at_3 = finite_certificate(3)
    at_7 = finite_certificate(7)
    at_23 = finite_certificate(23)
    assert at_3["jacobian_order"] == 22
    assert at_3["D_order"] == 11
    assert at_7["jacobian_order"] == 42
    assert at_7["D_order"] == 21
    assert at_23["jacobian_order"] == 462
    assert at_23["D_order"] == 231

    classes_7 = {tuple(pair) for pair in at_7["square_abscissa_classes"]}
    classes_23 = {tuple(pair) for pair in at_23["square_abscissa_classes"]}
    expected_7 = {(0, 0), (1, 0), (20, 0), (5, 0), (16, 0), (0, 1)}
    expected_23_e0 = {
        0,
        1,
        230,
        9,
        222,
        44,
        187,
        51,
        180,
        67,
        164,
        108,
        123,
    }
    expected_23 = {(value, 0) for value in expected_23_e0} | {(0, 1)}
    assert classes_7 == expected_7
    assert classes_23 == expected_23

    projection_23_mod_21 = {
        (exponent % 21, bit) for exponent, bit in classes_23
    }
    expected_projection_e0 = {0, 1, 20, 2, 19, 3, 18, 4, 17, 9, 12}
    assert projection_23_mod_21 == {
        (value, 0) for value in expected_projection_e0
    } | {(0, 1)}
    compatible = classes_7 & projection_23_mod_21
    assert compatible == {(0, 0), (1, 0), (20, 0), (0, 1)}
    assert (5, 0) not in projection_23_mod_21
    assert (16, 0) not in projection_23_mod_21

    # Index-independent compatibility lemma.  The exact group computations
    # give J(F_p)=<Dbar> direct-sum <Tbar>, with |Dbar|=N.  If D=mG and m is
    # odd, ord(m*Gbar)=N and ord(Gbar)|2N force ord(Gbar)=N and gcd(m,N)=1.
    # Since 21 divides 231, n/m has compatible D-coordinates modulo 21.
    for N, group_order in ((21, 42), (231, 462)):
        possible_r = [
            r
            for r in range(1, group_order + 1)
            if group_order % r == 0
            and any(
                m % 2 == 1
                and r // __import__("math").gcd(r, m) == N
                for m in range(1, 2 * group_order + 1, 2)
            )
        ]
        assert possible_r == [N]

    payload: dict[str, object] = {
        "schema": 1,
        "curve": "R^2=4*a^5-8*a^2+5*a",
        "D": "[(1,1)-infinity]",
        "T": "[(0,0)-infinity]",
        "finite_certificates": {"7": at_7, "23": at_23},
        "torsion_and_rank_lower_bound_check": {
            "J_F3_order": 22,
            "J_F7_order": 42,
            "gcd": 2,
            "D_mod_7_order": 21,
            "conclusion": "rational torsion divides 2 and D is non-torsion",
        },
        "p23_projection_mod_21_e0": sorted(expected_projection_e0),
        "compatible_classes_mod_7": [list(pair) for pair in sorted(compatible)],
        "excluded_p7_extra_classes": [[5, 0], [16, 0]],
        "odd_index_handled": True,
        "odd_index_lemma": (
            "Writing J(Q)=Z*G+<T> and D=mG after a torsion shift, mod-2 "
            "independence makes m odd. Full orders at 7 and 23 make m "
            "invertible modulo 21 and 231, so the local D-coordinates of "
            "any rational class agree modulo 21."
        ),
        "mw_sieve_conclusion": (
            "A rational point with square abscissa reduces at 7 to one of "
            "infinity, (0,0), or (1,+/-1)."
        ),
        "logical_scope": (
            "The finite sieve restricts residue disks. The companion p=7 "
            "formal-log certificate proves uniqueness in the four surviving "
            "disks."
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
    print("p=7/p=23 index-independent square-abscissa sieve: PASS")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
