#!/usr/bin/env python3
"""Exact second-layer and positivity certificates for two prime powers.

The lowest Newton endpoints in ``new_inert_pair_endpoint.py`` only give
congruences modulo the base primes.  Here the gap to the next coefficient is
used as well.  The resulting prime-power divisibilities, together with exact
positive-coefficient charts for the full projection, close every nonuniform
branch when p and q are powers of distinct inert primes.
"""

from __future__ import annotations

from collections import defaultdict
from hashlib import sha256
import json
from math import comb
from pathlib import Path

import sympy as sp

try:
    from research.global_descent.new_inert_pair_endpoint import P, P_s, Q, a, b, s, x
except ModuleNotFoundError:  # Allow direct ``python path/to/script.py`` replay.
    from new_inert_pair_endpoint import P, P_s, Q, a, b, s, x


def projection() -> sp.Expr:
    remainder = sp.Poly(sp.rem(P_s(), x**2 + a*x + b, x), x)
    return sp.resultant(
        remainder.coeff_monomial(x), remainder.coeff_monomial(1), a
    )


def normalized_branch(
    resultant: sp.Expr, sign: int, u: int, v: int
) -> sp.Poly:
    numerator = sp.together(
        resultant.subs(
            {s: P**2/Q**2, b: sign*P**(2*u)/Q**(2*v)}
        )
    ).as_numer_denom()[0]
    branch = sp.Poly(numerator, P, Q).primitive()[1]
    minimum_p = min(powers[0] for powers, _ in branch.terms())
    minimum_q = min(powers[1] for powers, _ in branch.terms())
    return sp.Poly(
        sp.cancel(branch.as_expr() / (P**minimum_p * Q**minimum_q)), P, Q
    )


def endpoint(branch: sp.Poly, variable: sp.Symbol) -> sp.Poly:
    index = 0 if variable == P else 1
    other = Q if variable == P else P
    terms = branch.terms()
    minimum = min(powers[index] for powers, _ in terms)
    expression = sum(
        coefficient * other**powers[1-index]
        for powers, coefficient in terms
        if powers[index] == minimum
    )
    return sp.Poly(expression, other)


def exponent_gap(branch: sp.Poly, variable: sp.Symbol) -> int:
    index = 0 if variable == P else 1
    exponents = sorted({powers[index] for powers, _ in branch.terms()})
    return exponents[1] - exponents[0]


def factor_multiplicity(poly: sp.Poly, factor: sp.Poly) -> int:
    multiplicity = 0
    remainder = poly
    while True:
        quotient, residual = sp.div(remainder, factor)
        if not residual.is_zero:
            return multiplicity
        multiplicity += 1
        remainder = quotient


def divide_exact_power(
    poly: sp.Poly, factor: sp.Poly, multiplicity: int
) -> sp.Poly:
    quotient = poly
    for _ in range(multiplicity):
        quotient, remainder = sp.div(quotient, factor)
        assert remainder.is_zero
    return quotient


def coefficient_summary(coefficients: dict[tuple[int, int], int]) -> dict[str, object]:
    nonzero = sorted(
        (i, j, int(value))
        for (i, j), value in coefficients.items()
        if value
    )
    encoded = json.dumps(nonzero, separators=(",", ":")).encode()
    values = [value for _, _, value in nonzero]
    return {
        "terms": len(nonzero),
        "degree_first": max(i for i, _, _ in nonzero),
        "degree_second": max(j for _, j, _ in nonzero),
        "minimum_coefficient": str(min(values)),
        "maximum_coefficient": str(max(values)),
        "all_coefficients_strictly_positive": all(value > 0 for value in values),
        "coefficient_sha256": sha256(encoded).hexdigest(),
    }


def shifted_even_coefficients(branch: sp.Poly) -> dict[tuple[int, int], int]:
    """Coefficients after P^2=U+9 and Q^2=V+9."""
    output: defaultdict[tuple[int, int], int] = defaultdict(int)
    for (power_p, power_q), coefficient in branch.terms():
        assert power_p % 2 == 0 and power_q % 2 == 0
        degree_u = power_p // 2
        degree_v = power_q // 2
        for i in range(degree_u + 1):
            factor_u = comb(degree_u, i) * 9**(degree_u-i)
            for j in range(degree_v + 1):
                factor_v = comb(degree_v, j) * 9**(degree_v-j)
                output[(i, j)] += int(coefficient) * factor_u * factor_v
    return dict(output)


def convolve(left: list[int], right: list[int]) -> list[int]:
    output = [0] * (len(left) + len(right) - 1)
    for i, left_value in enumerate(left):
        for j, right_value in enumerate(right):
            output[i+j] += left_value * right_value
    return output


def bounded_chart_coefficients(
    branch: sp.Poly, bound_after_p_shift: list[int]
) -> dict[tuple[int, int], int]:
    """Return the exact chart coefficients for the positive e=6 branch.

    With p=U+3 and B(p) represented by ``bound_after_p_shift``, use

        q = (3 + B(p) W)/(1+W).

    The returned dictionary is the coefficient table of
    (1+W)^deg_Q(F) F(U+3,q).
    """
    degree_q = branch.degree(Q)
    degree_p = branch.degree(P)

    shifted_p_powers = [[1]]
    for _ in range(degree_p):
        shifted_p_powers.append(convolve(shifted_p_powers[-1], [3, 1]))

    bound_powers = [[1]]
    for _ in range(degree_q):
        bound_powers.append(
            convolve(bound_powers[-1], bound_after_p_shift)
        )

    product_cache: dict[tuple[int, int], list[int]] = {}
    output: defaultdict[tuple[int, int], int] = defaultdict(int)
    for (power_p, power_q), coefficient in branch.terms():
        for chosen_bound in range(power_q + 1):
            key = (power_p, chosen_bound)
            if key not in product_cache:
                product_cache[key] = convolve(
                    shifted_p_powers[power_p], bound_powers[chosen_bound]
                )
            base = (
                int(coefficient)
                * comb(power_q, chosen_bound)
                * 3**(power_q-chosen_bound)
            )
            for residual in range(degree_q-power_q + 1):
                power_w = chosen_bound + residual
                multiplier = base * comb(degree_q-power_q, residual)
                for power_u, value in enumerate(product_cache[key]):
                    output[(power_u, power_w)] += multiplier * value
    return dict(output)


def verify() -> dict[str, object]:
    resultant = projection()
    canonical = {
        (sign, u, v): normalized_branch(resultant, sign, u, v)
        for sign in (1, -1)
        for u, v in ((3, 4), (4, 3), (0, 3), (3, 0), (0, 4), (4, 0))
    }

    # Reversing the Newton pair is exactly P<->Q after boundary monomials
    # are stripped.  Thus it suffices to certify one orientation below.
    for sign in (1, -1):
        for u, v in ((3, 4), (0, 3), (0, 4)):
            swapped = sp.Poly(
                canonical[(sign, u, v)].as_expr().subs(
                    {P: Q, Q: P}, simultaneous=True
                ),
                P,
                Q,
            )
            assert canonical[(sign, v, u)] == swapped

    endpoint_records = []
    expected_multiplicities = {
        (3, 4): (2, 1),
        (0, 3): (1, 2),
        (0, 4): (1, 1),
    }
    for sign in (1, -1):
        for u, v in ((3, 4), (0, 3), (0, 4)):
            branch = canonical[(sign, u, v)]
            exponent = 2*abs(u-v)
            endpoint_p = endpoint(branch, P)
            endpoint_q = endpoint(branch, Q)
            multiplicity_p = factor_multiplicity(
                endpoint_p, sp.Poly(Q**exponent-sign, Q)
            )
            multiplicity_q = factor_multiplicity(
                endpoint_q, sp.Poly(P**exponent-sign, P)
            )
            assert (multiplicity_p, multiplicity_q) == expected_multiplicities[(u, v)]
            cofactor_p = divide_exact_power(
                endpoint_p, sp.Poly(Q**exponent-sign, Q), multiplicity_p
            )
            cofactor_q = divide_exact_power(
                endpoint_q, sp.Poly(P**exponent-sign, P), multiplicity_q
            )
            # The remaining cofactors are signed pure powers of the opposite
            # variable.  Since gcd(p,q)=1, they contribute no p- or q-adic
            # valuation; this is what makes the displayed divisibilities
            # consequences of the two-step coefficient gap.
            assert len(cofactor_p.terms()) == len(cofactor_q.terms()) == 1
            assert abs(int(cofactor_p.LC())) == abs(int(cofactor_q.LC())) == 1
            assert exponent_gap(branch, P) == exponent_gap(branch, Q) == 2
            endpoint_records.append(
                {
                    "sign": sign,
                    "u": u,
                    "v": v,
                    "e": exponent,
                    "P_endpoint": str(sp.factor(endpoint_p.as_expr())),
                    "Q_endpoint": str(sp.factor(endpoint_q.as_expr())),
                    "P_target_multiplicity": multiplicity_p,
                    "Q_target_multiplicity": multiplicity_q,
                    "P_endpoint_target_cofactor": str(cofactor_p.as_expr()),
                    "Q_endpoint_target_cofactor": str(cofactor_q.as_expr()),
                    "next_exponent_gap_P": 2,
                    "next_exponent_gap_Q": 2,
                }
            )

    positivity = {}
    for label, key in {
        "negative_e6": (-1, 0, 3),
        "positive_e8": (1, 0, 4),
        "negative_e8": (-1, 0, 4),
    }.items():
        summary = coefficient_summary(shifted_even_coefficients(canonical[key]))
        assert summary["all_coefficients_strictly_positive"]
        positivity[label] = {
            "substitution": "P^2=U+9, Q^2=V+9",
            **summary,
        }

    positive_e6 = canonical[(1, 0, 3)]
    charts = {
        "R_not_3": {
            "bound": "B(p)=p^2+p+1",
            "bound_after_p_equals_U_plus_3": [13, 7, 1],
        },
        "R_equals_3": {
            "bound": "B(p)=3*(p^2-1)",
            "bound_after_p_equals_U_plus_3": [24, 18, 3],
        },
    }
    for record in charts.values():
        coefficients = bounded_chart_coefficients(
            positive_e6, record["bound_after_p_equals_U_plus_3"]
        )
        summary = coefficient_summary(coefficients)
        assert summary["all_coefficients_strictly_positive"]
        record.update(
            {
                "substitution": "p=U+3, q=(3+B(p)*W)/(1+W)",
                "clearing_factor": "(1+W)^24",
                **summary,
            }
        )

    return {
        "schema": 1,
        "status": "EXACT_SECOND_LAYER_AND_POSITIVITY_CERTIFICATE",
        "scope": (
            "p=L^m and q=R^n, where L,R are distinct odd inert primes; "
            "all nonuniform local pairs u,v in {0,3,4}"
        ),
        "endpoint_records": endpoint_records,
        "second_layer_divisibilities_for_orientation_shown": {
            "e=2, (u,v)=(3,4)": [
                "p divides q^2-sign",
                "q^2 divides p^2-sign",
            ],
            "e=6, (u,v)=(0,3)": [
                "p^2 divides q^6-sign",
                "q divides p^6-sign",
            ],
            "e=8, (u,v)=(0,4)": [
                "p^2 divides q^8-sign",
                "q^2 divides p^8-sign",
            ],
            "reverse_orientation": "swap p and q",
            "reason": (
                "the next exponent is two larger; a simple target therefore "
                "absorbs p^2, while a squared target absorbs p"
            ),
        },
        "e2_elementary_elimination": {
            "positive": (
                "If p|(q^2-1) and q^2|(p^2-1), then p>q.  Since p is an "
                "odd prime power, all of p divides one of q-1,q+1, forcing "
                "p=q+1, impossible for odd p,q."
            ),
            "negative": (
                "If p|(q^2+1) and q^2|(p^2+1), put c=(q^2+1)/p.  Then "
                "p>q, 1<=c<=q-1, and q^2|p+c.  For c=1, p+c=q^2+2; "
                "for c>=2, 0<p+c<q^2, both contradictions."
            ),
        },
        "full_projection_positive_coefficients": positivity,
        "positive_e6_size_bounds": {
            "R_not_3": (
                "q|p^6-1 and q=R^n.  For R!=3, all R-adic valuation lies "
                "in one of Phi_1,Phi_2,Phi_3,Phi_6, so q<=p^2+p+1."
            ),
            "R_equals_3": (
                "LTE gives v_3(p^6-1)=v_3(p^2-1)+1, so q<=3*(p^2-1)."
            ),
        },
        "positive_e6_bounded_charts": charts,
        "conclusion": (
            "Every nonuniform branch is nonzero.  Together with the existing "
            "uniform-pair exclusion, no quadratic factor exists when p and q "
            "are powers of distinct inert primes."
        ),
        "scope_warning": (
            "This does not treat general p,q with several prime divisors, "
            "because one global factor may select different local Newton pairs."
        ),
    }


if __name__ == "__main__":
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(verify(), indent=2, sort_keys=True) + "\n")
    print("second endpoint layers and full-projection positivity: exact")
    print("all nonuniform branches for two inert prime powers: closed")
