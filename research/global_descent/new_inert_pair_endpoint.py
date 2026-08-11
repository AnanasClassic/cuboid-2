#!/usr/bin/env python3
"""Exact endpoint conditions for two inert prime powers."""

from __future__ import annotations

import json
from pathlib import Path

import sympy as sp


s, x, a, b, P, Q = sp.symbols("s x a b P Q")


def P_s() -> sp.Expr:
    return sp.expand(
        x**5 + (2+s)*(3-2*s)*x**4
        + (1+10*s+4*s**2-14*s**3+s**4)*x**3
        - s*(1-14*s+4*s**2+10*s**3+s**4)*x**2
        - s**3*(1+2*s)*(-2+3*s)*x - s**5
    )


def strip_variable_power(poly: sp.Poly, variable: sp.Symbol) -> sp.Poly:
    minimum = min(powers[0] for powers, _ in poly.terms())
    return sp.Poly(sp.cancel(poly.as_expr()/variable**minimum), variable)


def verify() -> dict[str, object]:
    remainder = sp.Poly(sp.rem(P_s(), x**2+a*x+b, x), x)
    R1 = remainder.coeff_monomial(x)
    R0 = remainder.coeff_monomial(1)
    projection = sp.resultant(R1, R0, a)

    allowed = (0, 3, 4)
    records = []
    for sign in (1, -1):
        for u in allowed:
            for v in allowed:
                if u == v:
                    continue
                numerator = sp.together(
                    projection.subs({s: P**2/Q**2, b: sign*P**(2*u)/Q**(2*v)})
                ).as_numer_denom()[0]
                branch = sp.Poly(numerator, P, Q).primitive()[1]
                terms = branch.terms()
                minimum_P = min(powers[0] for powers, _ in terms)
                minimum_Q = min(powers[1] for powers, _ in terms)
                endpoint_P = sp.Poly(
                    sum(c*Q**powers[1] for powers, c in terms if powers[0] == minimum_P), Q
                )
                endpoint_Q = sp.Poly(
                    sum(c*P**powers[0] for powers, c in terms if powers[1] == minimum_Q), P
                )
                endpoint_P = strip_variable_power(endpoint_P, Q)
                endpoint_Q = strip_variable_power(endpoint_Q, P)

                exponent = 2*abs(u-v)
                target_Q = Q**exponent - sign
                target_P = P**exponent - sign
                sqf_Q = sp.Poly(endpoint_P.sqf_part(), Q).monic()
                sqf_P = sp.Poly(endpoint_Q.sqf_part(), P).monic()
                assert sp.expand(sqf_Q.as_expr() - target_Q) == 0
                assert sp.expand(sqf_P.as_expr() - target_P) == 0
                strengthened_negative_conditions = None
                if sign == -1 and exponent in (2, 6):
                    strengthened_negative_conditions = [
                        "m and n are odd",
                        "Legendre(L/R)=-1",
                        "Legendre(R/L)=-1",
                        "L=R=5 (mod 8)",
                    ]
                elif sign == -1 and exponent == 8:
                    strengthened_negative_conditions = [
                        "impossible for inert L,R: x^(8n)=-1 requires element order divisible by 16"
                    ]
                records.append(
                    {
                        "sign_of_b": sign,
                        "u": u,
                        "v": v,
                        "e": exponent,
                        "P_endpoint_squarefree": str(sp.factor(sqf_Q.as_expr())),
                        "Q_endpoint_squarefree": str(sp.factor(sqf_P.as_expr())),
                        "necessary_congruences_for_p=L^m_q=R^n": [
                            f"R^({exponent}*n) == {sign} (mod L)",
                            f"L^({exponent}*m) == {sign} (mod R)",
                        ],
                        "strengthened_negative_conditions": strengthened_negative_conditions,
                    }
                )

    # Endpoint no-go: for either sign-positive branch and any distinct primes,
    # m=R-1, n=L-1 satisfy both conditions by Fermat, for every e.
    for L, R in ((3, 5), (5, 11), (11, 13)):
        for exponent in (2, 6, 8):
            assert pow(R, exponent*(L-1), L) == 1
            assert pow(L, exponent*(R-1), R) == 1

    # Negative conditions with e=2 and e=6 genuinely survive reciprocity.
    for exponent in (2, 6):
        assert pow(13, exponent, 5) == 4
        assert pow(5, exponent, 13) == 12
    assert sp.legendre_symbol(13, 5) == -1
    assert sp.legendre_symbol(5, 13) == -1

    # Passing endpoints is only necessary.  The standard negative survivor
    # (5,13,1,1) is not a zero of the full projection in any of its four
    # e=2/e=6 branches.
    endpoint_survivor_full_projection = {}
    for u, v in ((3, 4), (4, 3), (0, 3), (3, 0)):
        value = sp.factor(
            projection.subs(
                {s: sp.Rational(5**2, 13**2),
                 b: -sp.Rational(5**(2*u), 13**(2*v))}
            )
        )
        assert value != 0
        endpoint_survivor_full_projection[f"u={u},v={v}"] = str(value)

    # Even with m=n=1 the other positive systems are nonempty.
    assert pow(13, 6, 3) == 1 and pow(3, 6, 13) == 1
    assert pow(5, 8, 3) == 1 and pow(3, 8, 5) == 1

    # If x^8=-1 mod L then x has order divisible by 16.  Hence 16|(L-1),
    # impossible for an inert prime L == 3 or 5 mod 8.  This eliminates both
    # negative branches with |u-v|=4.

    return {
        "schema": 1,
        "status": "MACHINE-VERIFIED_ENDPOINT_IDENTITIES",
        "setup": {
            "p": "L^m", "q": "R^n",
            "prime_conditions": "L,R distinct odd primes; (2/L)=(2/R)=-1",
            "local_indices": [0, 3, 4],
        },
        "records": records,
        "exact_residual_system": {
            "positive_b": "R^(e*n)=1 mod L and L^(e*m)=1 mod R",
            "negative_b": "R^(e*n)=-1 mod L and L^(e*m)=-1 mod R",
            "e": "2*|u-v| in {2,6,8}",
        },
        "rigorous_eliminations": [
            "negative b with e=8 is impossible: it would require 16|(L-1) and 16|(R-1)",
            "for m=n=1, positive b with e=2 is impossible for distinct odd primes (order by size)",
            "every negative branch requires L=R=5 mod 8 because -1 must be a quadratic residue",
            "for negative e=2 or e=6, m,n are odd and (L/R)=(R/L)=-1",
        ],
        "negative_e2_e6_2_sylow_lemma": {
            "statement": (
                "x^(e*n)=-1 with e=2 or 6 at an inert prime forces the "
                "2-primary component of ord(x) to have order 4"
            ),
            "consequences": [
                "the prime is 5 mod 8",
                "x is a quadratic nonresidue",
                "therefore n is odd and the underlying base has Legendre symbol -1",
                "applying at both primes gives m,n odd and (L/R)=(R/L)=-1",
            ],
            "reciprocity_consistency": (
                "L,R are 1 mod 4, so quadratic reciprocity makes the two symbols equal"
            ),
        },
        "no_go_certificates": [
            "for positive b, m=R-1 and n=L-1 satisfy every endpoint system by Fermat",
            "for negative b, (L,R,m,n)=(5,13,1,1) satisfies both e=2 and e=6 systems",
            "already at m=n=1, (L,R)=(3,13) survives positive e=6 and (3,5) survives positive e=8",
            "therefore endpoint coefficients plus quadratic reciprocity do not prove the general inert-pair family",
        ],
        "remaining_branches": {
            "positive": ["e=2", "e=6", "e=8"],
            "negative": [
                "e=2 with L,R=5 mod 8, m,n odd, (L/R)=(R/L)=-1",
                "e=6 with L,R=5 mod 8, m,n odd, (L/R)=(R/L)=-1",
            ],
        },
        "endpoint_survivor_warning": {
            "statement": (
                "satisfying the endpoint congruences is necessary only; it "
                "does not produce a zero of the full resultant or a quadratic factor"
            ),
            "example_5_13_full_projection_nonzero": endpoint_survivor_full_projection,
        },
    }


if __name__ == "__main__":
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(verify(), indent=2, sort_keys=True) + "\n")
    print("all 12 inert-pair endpoint factorizations: canonical congruence systems OK")
    print("negative e=8 eliminated; exact residual systems remain for e=2,6 and positive e=8")
