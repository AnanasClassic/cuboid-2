#!/usr/bin/env python3
"""Pure-Python exact checks supporting the Sage p=5 Chabauty certificate.

This file needs only SymPy.  It deliberately leaves the Jacobian rank
calculation to the separate exact certificate ``two_descent_rank.py``.
"""

from __future__ import annotations

from math import gcd

import sympy as sp


def cert(label: str, value) -> None:
    print(f"CERT {label} = {value}")


def first_nonsquare(prime: int) -> int:
    return next(
        value
        for value in range(2, prime)
        if pow(value, (prime - 1) // 2, prime) == prime - 1
    )


def fp2_multiply(
    left: tuple[int, int], right: tuple[int, int], prime: int, nonsquare: int
) -> tuple[int, int]:
    """Multiply in F_p[u]/(u^2-nonsquare)."""

    return (
        (left[0] * right[0] + left[1] * right[1] * nonsquare) % prime,
        (left[0] * right[1] + left[1] * right[0]) % prime,
    )


def fp2_power(
    value: tuple[int, int], exponent: int, prime: int, nonsquare: int
) -> tuple[int, int]:
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = fp2_multiply(result, value, prime, nonsquare)
        value = fp2_multiply(value, value, prime, nonsquare)
        exponent //= 2
    return result


def evaluate_fp2(
    coefficients: tuple[int, ...], value: tuple[int, int], prime: int, nonsquare: int
) -> tuple[int, int]:
    result = (0, 0)
    for coefficient in reversed(coefficients):
        result = fp2_multiply(result, value, prime, nonsquare)
        result = ((result[0] + coefficient) % prime, result[1])
    return result


def curve_cardinality_fp(coefficients: tuple[int, ...], prime: int) -> int:
    """Count the odd-degree model y^2=f(x), including infinity."""

    total = 1
    for x_coordinate in range(prime):
        value = sum(
            coefficient * pow(x_coordinate, power, prime)
            for power, coefficient in enumerate(coefficients)
        ) % prime
        if value == 0:
            character = 0
        else:
            character = 1 if pow(value, (prime - 1) // 2, prime) == 1 else -1
        total += 1 + character
    return total


def curve_cardinality_fp2(coefficients: tuple[int, ...], prime: int) -> int:
    """Count the odd-degree model over F_(p^2), including infinity."""

    nonsquare = first_nonsquare(prime)
    field_order = prime**2
    character_sum = 0
    for first in range(prime):
        for second in range(prime):
            value = evaluate_fp2(coefficients, (first, second), prime, nonsquare)
            if value == (0, 0):
                character = 0
            else:
                character = (
                    1
                    if fp2_power(value, (field_order - 1) // 2, prime, nonsquare)
                    == (1, 0)
                    else -1
                )
            character_sum += character
    return field_order + 1 + character_sum


def jacobian_cardinality(coefficients: tuple[int, ...], prime: int) -> int:
    n1 = curve_cardinality_fp(coefficients, prime)
    n2 = curve_cardinality_fp2(coefficients, prime)
    a1 = prime + 1 - n1
    numerator = n2 - prime**2 - 1 + a1**2
    assert numerator % 2 == 0
    a2 = numerator // 2
    return 1 - a1 + a2 - prime * a1 + prime**2


def main() -> None:
    t, x, s, y, U, V = sp.symbols("t x s y U V")
    f = t**5 + 21 * t**4 + 26 * t**3 + 10 * t**2 + 5 * t + 1
    quartic = t**4 + 20 * t**3 + 6 * t**2 + 4 * t + 1
    assert sp.expand((t + 1) * quartic) == f
    assert sp.factor(sp.discriminant(f, t)) == -(2**24) * 43
    assert sp.factor(sp.discriminant(quartic, t)) == -(2**16) * 43
    for t_value, w_values in {
        -1: (0,),
        0: (-1, 1),
        1: (-8, 8),
    }.items():
        for w_value in w_values:
            assert f.subs(t, t_value) == w_value**2

    # Exact isomorphism to the public LMFDB simplified model.
    t_of_x = -(2 * x + 1) / (2 * x - 1)
    lmfdb_f = 16 * x**5 + 8 * x**4 - 8 * x**3 - 4 * x**2 + 1
    assert sp.cancel((x - sp.Rational(1, 2)) ** 6 * f.subs(t, t_of_x) - lmfdb_f) == 0
    cert("lmfdb_isomorphism", "PASS")

    coefficients = (1, 5, 10, 26, 21, 1)
    counts = {
        "C_F3": curve_cardinality_fp(coefficients, 3),
        "C_F9": curve_cardinality_fp2(coefficients, 3),
        "J_F3": jacobian_cardinality(coefficients, 3),
        "C_F5": curve_cardinality_fp(coefficients, 5),
        "C_F25": curve_cardinality_fp2(coefficients, 5),
        "J_F5": jacobian_cardinality(coefficients, 5),
    }
    assert counts == {
        "C_F3": 6,
        "C_F9": 14,
        "J_F3": 22,
        "C_F5": 6,
        "C_F25": 30,
        "J_F5": 28,
    }
    assert gcd(counts["J_F3"], counts["J_F5"]) == 2

    points_f5 = {
        (x_coordinate, w_coordinate)
        for x_coordinate in range(5)
        for w_coordinate in range(5)
        if (
            w_coordinate**2
            - sum(
                coefficient * x_coordinate**power
                for power, coefficient in enumerate(coefficients)
            )
        )
        % 5
        == 0
    }
    expected_finite_f5 = {(4, 0), (0, 1), (0, 4), (1, 3), (1, 2)}
    assert points_f5 == expected_finite_f5
    assert len(points_f5) + 1 == counts["C_F5"]
    cert("finite_field_counts", counts)
    cert("known_reductions_cover_C_F5", sorted(points_f5))

    # Reconstruct the exact quotient polynomial from the normalized root
    # equation, avoiding the digit-loss errors in arXiv's HTML rendering.
    root_equation = (
        s**2 * y**5
        + (-2 * s**3 - s**2 + 6 * s) * y**4
        + (s**4 - 14 * s**3 + 4 * s**2 + 10 * s + 1) * y**3
        + (-s**4 - 10 * s**3 - 4 * s**2 + 14 * s - 1) * y**2
        + (-6 * s**3 + s**2 + 2 * s) * y
        - s**2
    )
    first_resultant = sp.resultant(root_equation, s**2 - U * s + 1, s)
    double_resultant = sp.factor(sp.resultant(first_resultant, y**2 - V * y + 1, y))
    quotient = (
        U**4 * V
        - 2 * U**4
        + 4 * U**3 * V**2
        - 8 * U**3 * V
        - 10 * U**2 * V**3
        - 108 * U**2 * V**2
        - 192 * U**2 * V
        - 128 * U**2
        + 4 * U * V**4
        - 8 * U * V**3
        + V**5
        - 2 * V**4
        + 64 * V**3
        + 384 * V**2
        + 768 * V
        + 512
    )
    assert double_resultant == quotient**2

    U_of_t = 2 * (t**5 + 6 * t**4 + 30 * t**3 + 16 * t**2 + 9 * t + 2) / (
        t * (t - 1) ** 2 * (t**2 + 6 * t + 1)
    )
    V_of_t = 2 * (t**4 + 36 * t**3 + 22 * t**2 + 4 * t + 1) / (
        (t - 1) ** 2 * (t**2 + 6 * t + 1)
    )
    assert sp.cancel(quotient.subs({U: U_of_t, V: V_of_t})) == 0
    assert sp.factor(U_of_t**2 - 4) == (
        16
        * (t + 1) ** 5
        * quartic
        / (t**2 * (t - 1) ** 4 * (t**2 + 6 * t + 1) ** 2)
    )
    assert sp.factor(V_of_t**2 - 4) == (
        256
        * t**2
        * (t + 1)
        * quartic
        / ((t - 1) ** 4 * (t**2 + 6 * t + 1) ** 2)
    )

    assert sp.cancel(U_of_t.subs(t, -1)) == -2
    assert sp.cancel(V_of_t.subs(t, -1)) == 2
    assert sp.limit(U_of_t, t, sp.oo) == 2
    assert sp.limit(V_of_t, t, sp.oo) == 2
    assert sp.Poly(t**2 + 6 * t + 1, t).discriminant() == 32
    assert sp.sqrt(32).is_rational is False
    assert sp.cancel(sp.together(U_of_t)).as_numer_denom()[0].subs(t, 0) != 0
    assert sp.cancel(sp.together(U_of_t)).as_numer_denom()[0].subs(t, 1) != 0
    cert("quotient_and_square_identities", "PASS")
    cert("exceptional_lifts", {"infinity": 1, "-1": -1, "0": None, "1": None})
    cert("rank_bound_supplied_by", "two_descent_rank.py: rank J_C(Q) <= 1")
    cert("status", "PASS")


if __name__ == "__main__":
    main()
