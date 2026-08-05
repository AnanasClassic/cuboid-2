#!/usr/bin/env python3
"""Exact exclusion of the 2+3 split for a prime-power family.

Let one of ``p,q`` be 1 and the other be ``ell**k``, where ``ell`` is any
prime.  The five Newton-polygon root valuations force the normalized
constant of a hypothetical monic quadratic factor to be one of

    b in {+/-s**m : 0 <= m <= 4}.

For each of these ten branches this script computes, from scratch, the exact
resultant of the two remainder equations with respect to ``a``.  Its only
positive rational zero is s=1, which is inadmissible.  This is an unbounded
infinite-family theorem; no search bound or numerical root isolation is used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")

s, x, a, b = sp.symbols("s x a b")


def P_s() -> sp.Expr:
    return sp.expand(
        x**5
        + (2 + s) * (3 - 2 * s) * x**4
        + (1 + 10*s + 4*s**2 - 14*s**3 + s**4) * x**3
        - s * (1 - 14*s + 4*s**2 + 10*s**3 + s**4) * x**2
        - s**3 * (1 + 2*s) * (-2 + 3*s) * x
        - s**5
    )


def remainder_equations() -> tuple[sp.Expr, sp.Expr]:
    remainder = sp.Poly(sp.rem(P_s(), x**2 + a*x + b, x), x)
    return (
        sp.expand(remainder.coeff_monomial(x)),
        sp.expand(remainder.coeff_monomial(1)),
    )


def sylvester_resultant(f: sp.Expr, g: sp.Expr) -> sp.Expr:
    """Compute Res_a(f,g) directly as a Sylvester determinant."""
    fp, gp = sp.Poly(f, a), sp.Poly(g, a)
    m, n = fp.degree(), gp.degree()
    f_coefficients = fp.all_coeffs()
    g_coefficients = gp.all_coeffs()
    rows = []
    for shift in range(n):
        rows.append([0]*shift + f_coefficients + [0]*(n - 1 - shift))
    for shift in range(m):
        rows.append([0]*shift + g_coefficients + [0]*(m - 1 - shift))
    return sp.expand(sp.det(sp.Matrix(rows)))


def verify() -> dict[str, object]:
    R1, R0 = remainder_equations()
    branches: dict[str, object] = {}

    for exponent in range(5):
        for sign in (1, -1):
            value = sign * s**exponent
            branch_R1 = sp.expand(R1.subs(b, value))
            branch_R0 = sp.expand(R0.subs(b, value))
            resultant = sp.factor(sp.resultant(branch_R1, branch_R0, a))
            # Independent construction of the same elimination polynomial.
            assert sp.expand(resultant - sylvester_resultant(branch_R1, branch_R0)) == 0
            constant, factors = sp.factor_list(resultant, s)
            reconstructed = constant * sp.prod(
                factor**multiplicity for factor, multiplicity in factors
            )
            assert sp.expand(resultant - reconstructed) == 0

            # A rational root of an integer polynomial factor must occur as a
            # linear factor over QQ.  The complete exact factorization has no
            # positive rational linear root other than 1 (and possibly 0,
            # which is outside s>0).  This check is stronger and cleaner than
            # numerical root isolation.
            rational_roots: set[sp.Rational] = set()
            factor_data: list[dict[str, object]] = []
            for factor, multiplicity in factors:
                poly = sp.Poly(factor, s, domain=sp.QQ)
                if poly.degree() == 1:
                    rational_roots.add(
                        sp.Rational(-poly.nth(0), poly.nth(1))
                    )
                else:
                    # All nonlinear residual factors are monic with constant
                    # term 1.  The rational-root theorem reduces their
                    # rational roots to +/-1, checked directly.  Thus the
                    # no-rational-root conclusion does not rely on accepting
                    # an opaque CAS irreducibility claim.
                    integral = sp.Poly(poly.clear_denoms(convert=True)[1], s)
                    assert abs(integral.LC()) == 1
                    assert abs(integral.TC()) == 1
                    assert integral.eval(1) != 0 and integral.eval(-1) != 0
                factor_data.append(
                    {
                        "polynomial": str(factor),
                        "multiplicity": int(multiplicity),
                        "degree": int(poly.degree()),
                    }
                )

            positive_roots = sorted(root for root in rational_roots if root > 0)
            assert positive_roots == [sp.Integer(1)]

            label = f"{'+' if sign > 0 else '-'}s^{exponent}"
            branches[label] = {
                "b": str(value),
                "resultant_constant": str(constant),
                "factorization": factor_data,
                "positive_rational_roots": [str(root) for root in positive_roots],
            }

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "theorem": (
            "If {p,q}={1,ell^k}, k>=1, and ell is any prime, "
            "then P_(p/q)^2 has no rational quadratic factor."
        ),
        "stronger_obstruction": (
            "For every hypothetical quadratic factor and every ell|pq, "
            "v_ell(b)=m_ell*v_ell(s) with m_ell in {0,1,2,3,4}; "
            "the indices m_ell cannot all be equal.  Hence every "
            "counterexample has omega(pq)>=2 and nonuniform local pair type."
        ),
        "valuation_input": {
            "root_valuations": "{0,0,2k,4k,4k}",
            "all_pair_sums": "v_ell(B)/k in {0,2,4,6,8}",
            "normalization": "b=B/q^8",
            "resulting_ten_branches": ["+/-s^m for m=0,1,2,3,4"],
        },
        "logic": [
            "a genuine quadratic divisor makes both exact remainders zero",
            "hence the corresponding resultant in a must vanish",
            "the complete QQ factorization in every branch has only s=1 as a positive rational zero",
            "s=1 is impossible because k>=1 and ell>1",
        ],
        "certificates": [
            "each resultant agrees exactly with a directly built 7x7 Sylvester determinant",
            "each displayed factorization multiplies exactly back to the resultant",
            "each nonlinear factor is monic with constant +/-1 and is nonzero at +/-1",
        ],
        "branches": branches,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(encoded).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    payload = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("ten prime-power branches: exact resultant factorization OK")
    print("only positive rational resultant root: s=1 (inadmissible)")
    try:
        shown = args.output.resolve().relative_to(ROOT)
    except ValueError:
        shown = args.output.resolve()
    print("wrote", shown)


if __name__ == "__main__":
    main()
