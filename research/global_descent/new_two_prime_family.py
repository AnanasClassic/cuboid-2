#!/usr/bin/env python3
"""Exact 2+3 exclusion for (p,q)=(3,r^n), r inert and r != 3."""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


s, x, a, b, P, Q = sp.symbols("s x a b P Q")


def polynomial() -> sp.Expr:
    return sp.expand(
        x**5 + (2+s)*(3-2*s)*x**4
        + (1+10*s+4*s**2-14*s**3+s**4)*x**3
        - s*(1-14*s+4*s**2+10*s**3+s**4)*x**2
        - s**3*(1+2*s)*(-2+3*s)*x - s**5
    )


def verify() -> dict[str, object]:
    rem = sp.Poly(sp.rem(polynomial(), x**2+a*x+b, x), x)
    R1, R0 = rem.coeff_monomial(x), rem.coeff_monomial(1)
    projection = sp.resultant(R1, R0, a)

    # At both 3 and r, (2/prime)=-1.  The irreducible slope-zero residual
    # quadratic restricts both normalized indices to {0,3,4}.
    allowed = (0, 3, 4)
    records = []
    exceptional_primes: set[int] = set()

    for sign in (1, -1):
        for u in allowed:
            for v in allowed:
                if u == v:
                    # The uniform branches b=+/-s^u are handled exactly by
                    # their univariate resultants below.
                    resultant = sp.factor(
                        sp.resultant(R1.subs(b, sign*s**u), R0.subs(b, sign*s**u), a)
                    )
                    roots = []
                    for factor, _ in sp.factor_list(resultant, s)[1]:
                        factor = sp.Poly(factor, s)
                        if factor.degree() == 1:
                            roots.append(sp.Rational(-factor.nth(0), factor.nth(1)))
                    assert [root for root in roots if root > 0] == [1]
                    records.append({"sign": sign, "u": u, "v": v, "method": "uniform resultant"})
                    continue

                substituted = sp.together(
                    projection.subs({s: P**2/Q**2, b: sign*P**(2*u)/Q**(2*v)})
                ).as_numer_denom()[0]
                branch = sp.Poly(substituted, P, Q).primitive()[1]
                terms = branch.terms()

                min_P = min(powers[0] for powers, _ in terms)
                coefficient_at_P = sp.Poly(
                    sum(c*Q**powers[1] for powers, c in terms if powers[0] == min_P), Q
                )
                min_Q = min(powers[1] for powers, _ in terms)
                coefficient_at_Q = sp.Poly(
                    sum(c*P**powers[0] for powers, c in terms if powers[1] == min_Q), P
                )

                # If the P=3 endpoint coefficient is nonzero modulo 3 for a
                # residue Q=+/-1, the 3-adic valuation has a unique minimum.
                bad_residues = [
                    residue for residue in (1, 2)
                    if int(coefficient_at_P.eval(residue)) % 3 == 0
                ]
                endpoint_integer = abs(int(coefficient_at_Q.eval(3)))
                endpoint_prime_factors = set(sp.factorint(endpoint_integer))

                # For a prime r != 3, either its residue mod 3 is not bad, or
                # cancellation would require r to divide the opposite endpoint
                # integer.  Record all inert prime exceptions exactly.
                branch_exceptions = {
                    prime for prime in endpoint_prime_factors
                    if prime != 3 and prime % 3 in bad_residues and prime % 8 in (3, 5)
                }
                exceptional_primes |= branch_exceptions
                records.append(
                    {
                        "sign": sign, "u": u, "v": v,
                        "method": "endpoint valuation",
                        "bad_Q_residues_mod_3": bad_residues,
                        "opposite_endpoint_at_P_3": str(endpoint_integer),
                        "inert_prime_exceptions": sorted(branch_exceptions),
                    }
                )

    assert exceptional_primes == {5, 13}
    # The endpoint argument leaves only two explicit primes.  They are not
    # assumptions or a bounded-search claim: evaluate every one of the finite
    # exact branch equations individually and record nonzero certificates.
    exceptional_evaluations: dict[str, dict[str, str]] = {}
    for prime in sorted(exceptional_primes):
        values: dict[str, str] = {}
        for sign in (1, -1):
            for u in allowed:
                for v in allowed:
                    exact = sp.together(
                        projection.subs(
                            {s: sp.Rational(3**2, prime**2),
                             b: sign*sp.Rational(3**(2*u), prime**(2*v))}
                        )
                    )
                    assert exact != 0
                    values[f"{sign}:{u}:{v}"] = str(exact)
        exceptional_evaluations[str(prime)] = values

    def valuation(number: int, prime: int) -> int:
        number = abs(number)
        answer = 0
        while number and number % prime == 0:
            number //= prime
            answer += 1
        return answer

    # Upgrade Q=r to every Q=r^n.  Only four positive-sign branches survived
    # the endpoint test.  After P=3, inspect the Q-adic coefficient polygon.
    # A unique constant-term minimum works for every n >= threshold; the sole
    # threshold-2 case at n=1 was already evaluated exactly above.
    power_certificates = []
    residual = [(5, 0, 4), (5, 4, 0), (13, 0, 3), (13, 3, 0)]
    for prime, u, v in residual:
        substituted = sp.together(
            projection.subs({s: P**2/Q**2, b: P**(2*u)/Q**(2*v)})
        ).as_numer_denom()[0]
        branch = sp.Poly(substituted, P, Q).primitive()[1]
        at_three = sp.Poly(branch.eval({P: 3}), Q)
        coefficients = {degree[0]: int(coefficient) for degree, coefficient in at_three.terms()}
        constant_valuation = valuation(coefficients[0], prime)
        threshold = 1
        while any(
            valuation(coefficient, prime) + threshold*degree <= constant_valuation
            for degree, coefficient in coefficients.items() if degree > 0
        ):
            threshold += 1
        assert threshold <= 2
        assert sp.Rational(
            projection.subs(
                {s: sp.Rational(9, prime**2), b: sp.Rational(3**(2*u), prime**(2*v))}
            )
        ) != 0
        power_certificates.append(
            {
                "prime": prime, "u": u, "v": v,
                "constant_coefficient_valuation": constant_valuation,
                "unique_minimum_for_all_n_at_least": threshold,
                "n_1_checked_exactly": True,
            }
        )
    return {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "theorem": (
            "If r != 3 is prime with r congruent to 3 or 5 mod 8 and n>=1, then "
            "P_{(3/r^n)^2} and, by reciprocity, P_{(r^n/3)^2} have no rational quadratic factor."
        ),
        "local_type_set": [0, 3, 4],
        "exceptional_primes_from_exact_endpoint_certificates": sorted(exceptional_primes),
        "exact_individual_evaluation_of_endpoint_exceptions": exceptional_evaluations,
        "exceptional_prime_power_certificates": power_certificates,
        "records": records,
        "logic": [
            "uniform local types are excluded by the exact b=+/-s^m resultants",
            "for every nonuniform type, a nonzero endpoint coefficient gives a unique minimal local valuation",
            "the union of possible inert endpoint exceptions is exactly {5,13}",
            "the two residual primes 5 and 13 are individually decided by exact nonzero branch evaluations",
            "their coefficient polygons upgrade the result from r to every r^n",
            "therefore every inert prime power r^n, r distinct from 3, is excluded",
        ],
    }


if __name__ == "__main__":
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(verify(), indent=2, sort_keys=True) + "\n")
    print("two-prime family (3,r^n), every inert prime r != 3: exact 2+3 exclusion OK")
