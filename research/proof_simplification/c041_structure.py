#!/usr/bin/env python3
"""Exact structural audit for attempted simplifications of C041.

This certificate deliberately proves structural facts, not a replacement for
the square-abscissa theorem.  It checks:

* the complete geometric automorphism group of
  C3: r^2 = 4*u^8 - 8*u^2 + 5;
* its elliptic and genus-two quotients and the elliptic quotient's exact
  birational identification with E1;
* absolute simplicity of Jac(D+) by good reduction at 3;
* the absence of nontrivial Q-rational endomorphisms, using the incompatible
  Frobenius fields at 3 and 13;
* the rational Richelot neighbour of D+; and
* the finite-field obstruction to replacing the existing 7/23 sieve by the
  most obvious direct Chabauty argument on C3.

Only exact SymPy and PARI arithmetic is used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp
from cypari2 import Pari


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def fp2_curve_count(prime: int, polynomial) -> tuple[int, int]:
    """Count an odd-degree hyperelliptic curve over F_p and F_(p^2)."""

    squares = {value * value % prime for value in range(prime)}
    nonsquare = next(value for value in range(2, prime) if value not in squares)

    def add(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
        return (
            (left[0] + right[0]) % prime,
            (left[1] + right[1]) % prime,
        )

    def multiply(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
        return (
            (left[0] * right[0] + nonsquare * left[1] * right[1]) % prime,
            (left[0] * right[1] + left[1] * right[0]) % prime,
        )

    def power(value: tuple[int, int], exponent: int) -> tuple[int, int]:
        result = (1, 0)
        while exponent:
            if exponent & 1:
                result = multiply(result, value)
            value = multiply(value, value)
            exponent //= 2
        return result

    def scale(value: tuple[int, int], scalar: int) -> tuple[int, int]:
        return value[0] * scalar % prime, value[1] * scalar % prime

    def evaluate(value: tuple[int, int]) -> tuple[int, int]:
        result = (0, 0)
        for coefficient in reversed(polynomial):
            result = add(multiply(result, value), (coefficient % prime, 0))
        return result

    count_p = 1
    for value in range(prime):
        rhs = sum(
            coefficient * pow(value, degree, prime)
            for degree, coefficient in enumerate(polynomial)
        ) % prime
        count_p += 1 if rhs == 0 else 2 if rhs in squares else 0

    count_p2 = 1
    for first in range(prime):
        for second in range(prime):
            rhs = evaluate((first, second))
            if rhs == (0, 0):
                count_p2 += 1
            elif power(rhs, (prime * prime - 1) // 2) == (1, 0):
                count_p2 += 2
    return count_p, count_p2


def jacobian_weil_polynomial(
    prime: int, count_p: int, count_p2: int, variable: sp.Symbol
) -> tuple[sp.Expr, int, int, int]:
    """Recover the genus-two Weil polynomial and #J(F_p)."""

    first_trace = prime + 1 - count_p
    numerator = count_p2 - prime**2 - 1 + first_trace**2
    assert numerator % 2 == 0
    second_coefficient = numerator // 2
    polynomial = (
        variable**4
        - first_trace * variable**3
        + second_coefficient * variable**2
        - prime * first_trace * variable
        + prime**2
    )
    jacobian_order = (
        1
        - first_trace
        + second_coefficient
        - prime * first_trace
        + prime**2
    )
    return sp.expand(polynomial), first_trace, second_coefficient, jacobian_order


def absolute_simplicity_record(
    prime: int, count_p: int, count_p2: int
) -> dict[str, object]:
    """Certify absolute simplicity from exact Frobenius-root ratios."""

    T, z = sp.symbols("T z")
    weil, first_trace, second_coefficient, jacobian_order = (
        jacobian_weil_polynomial(prime, count_p, count_p2, T)
    )
    assert sp.Poly(weil, T).is_irreducible
    assert second_coefficient % prime != 0  # ordinary reduction

    ratio_resultant = sp.factor(sp.resultant(weil, weil.subs(T, z * T), T))
    diagonal = prime**4 * (z - 1) ** 4
    off_diagonal = sp.cancel(ratio_resultant / diagonal)
    assert sp.denom(off_diagonal) == 1

    # If a quotient of two roots were a root of unity of order n, then
    # phi(n) <= 16 because it lies in the compositum of two quartic fields.
    # The elementary bound phi(n) >= sqrt(n/2) reduces the exhaustive list to
    # n <= 512.  Every corresponding cyclotomic gcd is checked exactly.
    tested_orders = [
        order for order in range(2, 513) if int(sp.totient(order)) <= 16
    ]
    nontrivial_gcds = []
    off_diagonal_poly = sp.Poly(off_diagonal, z, domain=sp.QQ)
    for order in tested_orders:
        gcd = sp.gcd(
            off_diagonal_poly,
            sp.Poly(sp.cyclotomic_poly(order, z), z, domain=sp.QQ),
        )
        if gcd.degree() > 0:
            nontrivial_gcds.append({"order": order, "gcd": str(gcd.as_expr())})
    assert not nontrivial_gcds

    real_subfield_polynomial = sp.expand(
        z**2 - first_trace * z + second_coefficient - 2 * prime
    )
    return {
        "prime": prime,
        "C_Fp": count_p,
        "C_Fp2": count_p2,
        "J_Fp": jacobian_order,
        "weil_polynomial": str(weil),
        "ordinary": True,
        "weil_polynomial_irreducible": True,
        "ratio_resultant": str(ratio_resultant),
        "off_diagonal_root_of_unity_orders": [],
        "cyclotomic_orders_tested": tested_orders,
        "absolutely_simple_reduction": True,
        "real_frobenius_subfield_polynomial": str(real_subfield_polynomial),
        "real_frobenius_subfield_discriminant": int(
            sp.discriminant(real_subfield_polynomial, z)
        ),
    }


def automorphism_audit() -> dict[str, object]:
    """Solve the complete PGL2 branch-stabilizer equations."""

    u, alpha, beta, gamma, lam, inverse_det = sp.symbols(
        "u alpha beta gamma lambda inverse_det"
    )
    branch = 4 * u**8 - 8 * u**2 + 5

    # Chart d=1.  Saturating by det=alpha-beta*gamma removes singular
    # matrices.  Equality is allowed up to the scalar lambda.
    transformed = (
        4 * (alpha * u + beta) ** 8
        - 8 * (alpha * u + beta) ** 2 * (gamma * u + 1) ** 6
        + 5 * (gamma * u + 1) ** 8
        - lam * branch
    )
    equations = sp.Poly(sp.expand(transformed), u).all_coeffs()
    chart_finite = sp.groebner(
        equations + [inverse_det * (alpha - beta * gamma) - 1],
        inverse_det,
        lam,
        alpha,
        beta,
        gamma,
        order="lex",
    )
    expected_finite = sp.groebner(
        [
            inverse_det - alpha,
            lam - 1,
            alpha**2 - 1,
            beta,
            gamma,
        ],
        inverse_det,
        lam,
        alpha,
        beta,
        gamma,
        order="lex",
    )
    assert chart_finite == expected_finite

    # Chart d=0, normalized by c=1.  Invertibility is beta != 0.
    transformed_infinite = (
        4 * (alpha * u + beta) ** 8
        - 8 * (alpha * u + beta) ** 2 * u**6
        + 5 * u**8
        - lam * branch
    )
    equations_infinite = sp.Poly(sp.expand(transformed_infinite), u).all_coeffs()
    chart_infinite = sp.groebner(
        equations_infinite + [inverse_det * beta - 1],
        inverse_det,
        lam,
        alpha,
        beta,
        order="lex",
    )
    assert len(chart_infinite.polys) == 1
    assert chart_infinite.polys[0].as_expr() == 1

    return {
        "branch_polynomial": str(branch),
        "finite_chart_saturated_groebner_basis": [
            str(sp.factor(item.as_expr())) for item in chart_finite.polys
        ],
        "infinite_chart_saturated_groebner_basis": ["1"],
        "PGL2_branch_stabilizer": ["u", "-u"],
        "geometric_curve_automorphism_group": "C2 x C2",
        "curve_automorphisms": [
            "(u,r)->(u,r)",
            "(u,r)->(u,-r)",
            "(u,r)->(-u,r)",
            "(u,r)->(-u,-r)",
        ],
        "valid_over": "Qbar (hence no extra automorphisms over any extension)",
    }


def quotient_audit() -> dict[str, object]:
    """Verify both quotient maps and the elliptic birational model."""

    u, r, a, R, t, m, x, y = sp.symbols("u r a R t m x y")
    c3_rhs = 4 * u**8 - 8 * u**2 + 5
    elliptic_quartic_rhs = 4 * a**4 - 8 * a + 5
    genus_two_rhs = 4 * a**5 - 8 * a**2 + 5 * a
    assert sp.expand(elliptic_quartic_rhs.subs(a, u**2) - c3_rhs) == 0
    assert sp.expand(genus_two_rhs.subs(a, u**2) - u**2 * c3_rhs) == 0

    # At t=a-1, write r=1+4t+m*t^2.  The residual quadratic in t has
    # discriminant equal to the E1 equation after x=2-m/2.
    quartic_shifted = sp.expand(elliptic_quartic_rhs.subs(a, 1 + t))
    residual = sp.factor(
        ((1 + 4 * t + m * t**2) ** 2 - quartic_shifted) / t**2
    )
    expected_residual = (
        (m**2 - 4) * t**2 + (8 * m - 16) * t + 2 * m - 8
    )
    assert sp.expand(residual - expected_residual) == 0
    discriminant = sp.factor(sp.discriminant(expected_residual, t))
    assert sp.expand(
        discriminant + 8 * (m - 2) * (m**2 - 10 * m + 8)
    ) == 0
    e1_x = 2 - m / 2
    discriminant_root = (
        2 * (m**2 - 4) * t + (8 * m - 16)
    )
    e1_y = discriminant_root / 8
    assert sp.expand(
        e1_y**2 - (e1_x**3 - 5 * e1_x + 4)
        - (discriminant_root**2 - discriminant) / 64
    ) == 0
    inverse_m = 4 - 2 * x
    inverse_t = sp.factor(
        4 * (y - inverse_m + 2) / (inverse_m**2 - 4)
    )
    assert sp.factor(
        inverse_t
        - (8 * y - (8 * inverse_m - 16))
        / (2 * (inverse_m**2 - 4))
    ) == 0

    # Differential splitting:
    # E0 pullback da/r = 2u du/r; D+ pullbacks da/R and a da/R are
    # 2 du/r and 2u^2 du/r.
    return {
        "C3": "r^2=4*u^8-8*u^2+5",
        "elliptic_quotient": {
            "involution": "(u,r)->(-u,r)",
            "map": "a=u^2, r=r",
            "curve": "r^2=4*a^4-8*a+5",
            "birational_E1": {
                "t": "a-1",
                "m": "(r-1-4*t)/t^2",
                "x": "2-m/2",
                "y": "((m^2-4)*t+4*m-8)/4",
                "inverse_m": "4-2*x",
                "inverse_t": "4*(y-m+2)/(m^2-4)",
                "E1": "y^2=x^3-5*x+4",
            },
        },
        "genus_two_quotient": {
            "involution": "(u,r)->(-u,-r)",
            "map": "a=u^2, R=u*r",
            "curve": "R^2=4*a^5-8*a^2+5*a",
        },
        "differential_decomposition": {
            "elliptic_factor": "span(u*du/r)",
            "genus_two_factor": "span(du/r,u^2*du/r)",
        },
        "jacobian_isogeny": "Jac(C3) ~ E1 x Jac(D+) over Q",
        "prym_of_C3_to_E1": "Jac(D+) up to Q-isogeny",
    }


def richelot_audit() -> dict[str, object]:
    """Construct the rational Richelot neighbour and show it does not split."""

    a = sp.symbols("a")
    imaginary = sp.I
    first = a
    second = 2 * a**2 + 2 * imaginary * a - 1 - 2 * imaginary
    third = 2 * a**2 - 2 * imaginary * a - 1 + 2 * imaginary
    original = a * (4 * a**4 - 8 * a + 5)
    assert sp.expand(first * second * third - original) == 0

    coefficient_matrix = sp.Matrix(
        [
            [0, 1, 0],
            [2, 2 * imaginary, -1 - 2 * imaginary],
            [2, -2 * imaginary, -1 + 2 * imaginary],
        ]
    )
    determinant = sp.expand(coefficient_matrix.det())
    assert determinant == -8 * imaginary

    def bracket(left: sp.Expr, right: sp.Expr) -> sp.Expr:
        return sp.expand(sp.diff(left, a) * right - left * sp.diff(right, a))

    brackets = [
        bracket(second, third),
        bracket(third, first),
        bracket(first, second),
    ]
    product = sp.expand(sp.prod(brackets))
    quotient = sp.factor(product / determinant)
    expected_quotient = -(
        2 * a**2 - 4 * a + 1
    ) * (4 * a**4 + 4 * a**2 + 5) / 2
    assert sp.expand(quotient - expected_quotient) == 0
    integral_dual = sp.factor(4 * quotient)
    assert sp.expand(
        integral_dual
        + 2
        * (2 * a**2 - 4 * a + 1)
        * (4 * a**4 + 4 * a**2 + 5)
    ) == 0
    assert sp.Poly(4 * a**4 + 4 * a**2 + 5, a).is_irreducible

    return {
        "quadratic_splitting_field": "Q(i)",
        "quadratic_factors": [str(first), str(second), str(third)],
        "determinant": str(determinant),
        "brackets": [str(sp.factor(item)) for item in brackets],
        "rational_dual_curve": f"Y^2={integral_dual}",
        "dual_factor_degrees_over_Q": [2, 4],
        "conclusion": (
            "A rational (2,2)-Richelot isogeny exists, but absolute "
            "simplicity of Jac(D+) implies that the target is not an "
            "elliptic product; this does not simplify the rank or point problem."
        ),
    }


def direct_c3_finite_audit() -> dict[str, object]:
    """Count the direct genus-three reductions at the two tempting primes."""

    def count(prime: int) -> tuple[int, list[list[object]]]:
        rows: list[list[object]] = []
        total = 2  # two rational points at infinity; leading coefficient is 4
        for u_value in range(prime):
            rhs = (4 * pow(u_value, 8, prime) - 8 * u_value**2 + 5) % prime
            roots = [
                r_value
                for r_value in range(prime)
                if r_value * r_value % prime == rhs
            ]
            total += len(roots)
            if roots:
                rows.append([u_value, roots])
        return total, rows

    count_3, rows_3 = count(3)
    count_7, rows_7 = count(7)
    assert count_3 == 6
    assert rows_3 == [[1, [1, 2]], [2, [1, 2]]]
    assert count_7 == 10
    assert rows_7 == [[1, [1, 6]], [3, [2, 5]], [4, [2, 5]], [6, [1, 6]]]
    return {
        "C3_F3": count_3,
        "C3_F3_affine_points": rows_3,
        "C3_F7": count_7,
        "C3_F7_affine_points": rows_7,
        "known_Q_points": "two infinities and (u,r)=(+/-1,+/-1)",
        "p3_obstruction": (
            "All six residue disks are known, but the rank-two Chabauty "
            "annihilator reduces to a multiple of (1-u^2)du/r, which "
            "vanishes in the four affine disks; moreover 3 <= 2g.  A new "
            "exact exceptional-disk calculation would still be required."
        ),
        "p7_obstruction": (
            "The four additional disks u=+/-3 with r=+/-2 are precisely "
            "unoccupied square-abscissa disks.  The existing p=23 "
            "Mordell-Weil sieve is what removes them."
        ),
    }


def verify() -> dict[str, object]:
    pari = Pari()
    automorphisms = automorphism_audit()
    quotients = quotient_audit()

    # D+: R^2 = 4a^5-8a^2+5a.  Scaling R by 2 gives the monic model used
    # for point counts, without changing either count in odd characteristic.
    polynomial = (0, 5, -8, 0, 0, 4)
    count_3 = fp2_curve_count(3, polynomial)
    count_13 = fp2_curve_count(13, polynomial)
    assert count_3 == (6, 14)
    assert count_13 == (16, 162)
    reduction_3 = absolute_simplicity_record(3, *count_3)
    reduction_13 = absolute_simplicity_record(13, *count_13)
    assert reduction_3["J_Fp"] == 22
    assert reduction_13["J_Fp"] == 196

    T = sp.symbols("T")
    weil_3, _, _, _ = jacobian_weil_polynomial(3, *count_3, T)
    weil_13, _, _, _ = jacobian_weil_polynomial(13, *count_13, T)
    pari_weil_3 = pari(str(weil_3).replace("T", "x").replace("**", "^"))
    pari_weil_13 = pari(str(weil_13).replace("T", "x").replace("**", "^"))
    assert list(pari.polgalois(pari_weil_3))[:3] == [
        pari(8),
        pari(-1),
        pari(3),
    ]
    assert list(pari.polgalois(pari_weil_13))[:3] == [
        pari(8),
        pari(-1),
        pari(3),
    ]
    subfields_3 = list(pari.nfsubfields(pari_weil_3))
    subfields_13 = list(pari.nfsubfields(pari_weil_13))
    quadratic_3 = [entry for entry in subfields_3 if int(pari.poldegree(entry[0])) == 2]
    quadratic_13 = [
        entry for entry in subfields_13 if int(pari.poldegree(entry[0])) == 2
    ]
    assert len(quadratic_3) == len(quadratic_13) == 1
    assert str(quadratic_3[0][0]) == "x^2 - 6*x + 6"
    assert str(quadratic_13[0][0]) == "x^2 - 26*x + 140"

    simplicity = {
        "good_reduction_at_3": reduction_3,
        "good_reduction_at_13": reduction_13,
        "geometric_simplicity": (
            "The reduction at 3 is absolutely simple, so Jac(D+) is "
            "absolutely/geometrically simple over Q."
        ),
        "consequences": [
            "not Q-isogenous to a product of elliptic curves",
            "not geometrically isogenous to a product of elliptic curves",
            "D+ has no degree-two elliptic quotient over any extension",
            "no Richelot isogeny from Jac(D+) can have an elliptic-product target",
        ],
        "Q_rational_endomorphisms": {
            "p3_frobenius_field_galois_group": "D4",
            "p13_frobenius_field_galois_group": "D4",
            "p3_unique_quadratic_subfield": "Q(sqrt(3))",
            "p13_unique_quadratic_subfield": "Q(sqrt(29))",
            "intersection": "Q",
            "conclusion": "End_Q(Jac(D+)) tensor Q = Q",
            "scope": (
                "This rules out rational RM/correspondences.  It does not "
                "by itself determine every geometric endomorphism of the "
                "absolutely simple surface."
            ),
        },
    }

    payload: dict[str, object] = {
        "schema": 1,
        "status": "PASS",
        "proof_status": (
            "Structural negative result only; the existing C041 proof is retained."
        ),
        "automorphisms": automorphisms,
        "quotients": quotients,
        "genus_two_jacobian": simplicity,
        "richelot": richelot_audit(),
        "direct_C3_chabauty": direct_c3_finite_audit(),
        "overall_conclusion": (
            "The genus-three quotient decomposition exposes E1 and Jac(D+) "
            "but does not remove the geometrically simple genus-two Prym. "
            "No proof-quality replacement for the existing descent, 7/23 "
            "sieve, and p=7 Coleman step is obtained."
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
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("C041 structural simplification audit: PASS")
    print("Aut(C3)_Qbar = C2 x C2; Jac(D+) geometrically simple")
    print("no proof dependency replaced")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
