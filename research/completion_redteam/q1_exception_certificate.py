#!/usr/bin/env python3
"""Close the exceptional ``Q1(T,A)=0`` branch of the generic B-lift.

The genus-four artifact gives

    F_T(T,A) = G(T^2,A)

and a generic inverse whose penultimate subresultant is

    Q1(T,A) B + Q0(T,A).

At ``Q1=0`` that displayed inverse cannot be used.  This script eliminates
``A`` exactly, factors the resultant completely over ``QQ``, multiplies the
factorization back, and proves that its only rational roots in ``T`` are
``-1,0,1``.  These are precisely the inadmissible Mobius-chart boundaries.
No claim about an admissible point is inferred from a one-way resultant: the
resultant is used only to constrain the rational T-coordinate of an assumed
common zero.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_name("q1_exception_certificate.json")


def sparse(poly: sp.Poly) -> list[dict[str, object]]:
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in poly.terms()
    ]


def load_poly(
    records: list[dict[str, object]], variables: tuple[sp.Symbol, ...]
) -> sp.Poly:
    return sp.Poly.from_dict(
        {
            tuple(int(power) for power in record["powers"]): sp.Integer(
                record["coefficient"]
            )
            for record in records
        },
        variables,
        domain=sp.ZZ,
    )


def verify() -> dict[str, object]:
    source = json.loads(SOURCE.read_text(encoding="utf-8"))
    source_checksum = source.pop("sha256_without_checksum")
    rendered_source = json.dumps(source, indent=2, sort_keys=True).encode()
    assert hashlib.sha256(rendered_source).hexdigest() == source_checksum

    T, A = sp.symbols("T A")
    G_X = load_poly(source["genus4_model"]["terms"], (sp.Symbol("X"), A))
    F_T = sp.Poly(
        sum(
            coefficient * T ** (2 * x_degree) * A**a_degree
            for (x_degree, a_degree), coefficient in G_X.terms()
        ),
        T,
        A,
        domain=sp.ZZ,
    )
    Q1 = load_poly(source["linear_subresultant"]["Q1_terms"], (T, A))
    assert (F_T.degree(T), F_T.degree(A)) == (32, 10)
    assert (Q1.degree(T), Q1.degree(A)) == (34, 8)

    resultant = sp.Poly(
        sp.resultant(F_T.as_expr(), Q1.as_expr(), A), T, domain=sp.ZZ
    )
    content, raw_factors = sp.factor_list(resultant.as_expr(), T)
    factors = [(sp.Poly(factor, T, domain=sp.ZZ), exponent)
               for factor, exponent in raw_factors]

    # A complete exact factorization certificate, not a root search.
    reconstructed = sp.Poly(content, T, domain=sp.ZZ)
    for factor, exponent in factors:
        assert factor.is_irreducible
        reconstructed *= factor**exponent
    assert reconstructed == resultant

    signature = sorted((factor.degree(), int(exponent)) for factor, exponent in factors)
    assert signature == [
        (1, 40),
        (1, 44),
        (1, 100),
        (2, 4),
        (2, 4),
        (2, 28),
        (8, 5),
        (8, 5),
        (8, 12),
        (60, 2),
    ]

    rational_roots: dict[sp.Rational, int] = {}
    factor_records: list[dict[str, object]] = []
    for factor, exponent in factors:
        record: dict[str, object] = {
            "degree": int(factor.degree()),
            "exponent": int(exponent),
            "irreducible_over_QQ": True,
            "terms": sparse(factor),
        }
        if factor.degree() == 1:
            root = -sp.Rational(factor.nth(0), factor.nth(1))
            rational_roots[root] = int(exponent)
            record["rational_root"] = str(root)
        else:
            # An irreducible QQ-polynomial of degree > 1 has no QQ root.
            record["rational_root"] = None
        factor_records.append(record)
    assert rational_roots == {sp.Rational(-1): 40, sp.Rational(0): 44,
                              sp.Rational(1): 100}

    # Record the exact common A-fibres.  They are not needed to discard the
    # points, since their T-coordinate is already inadmissible, but prevent a
    # hidden claim that the resultant roots were necessarily common zeros.
    fibre_records: dict[str, object] = {}
    expected_gcds = {
        -1: A**3,
        0: (A - 2) ** 3
        * (361 * A**4 - 5272 * A**3 + 16504 * A**2 - 19168 * A + 7696)
        / 361,
        1: A**3 * (A - 6) * (A**2 - 12 * A + 4) ** 2,
    }
    boundary = {
        -1: {"z": "0", "s": "0", "reason": "p=0 boundary; s is not positive"},
        0: {"z": "1", "s": "1", "reason": "excluded p=q parameter"},
        1: {"z": "infinity", "s": "infinity", "reason": "q=0 projective boundary"},
    }
    for value in (-1, 0, 1):
        f_special = sp.Poly(F_T.as_expr().subs(T, value), A, domain=sp.QQ)
        q1_special = sp.Poly(Q1.as_expr().subs(T, value), A, domain=sp.QQ)
        common = sp.gcd(f_special, q1_special).monic()
        assert sp.cancel(common.as_expr() - expected_gcds[value]) == 0
        fibre_records[str(value)] = {
            "common_A_gcd": str(sp.factor(common.as_expr())),
            **boundary[value],
            "admissible": False,
        }

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "source": str(SOURCE.relative_to(ROOT)),
        "source_checksum": source_checksum,
        "construction": "F_T(T,A)=G(T^2,A); eliminate A from F_T and Q1",
        "degrees": {
            "F_T_in_T_A": [32, 10],
            "Q1_in_T_A": [34, 8],
            "resultant_in_T": int(resultant.degree()),
        },
        "resultant_content": str(content),
        "resultant_sha256_sparse": hashlib.sha256(
            json.dumps(sparse(resultant), sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "factorization": factor_records,
        "factorization_multiplication_back": True,
        "rational_roots_with_multiplicity": {
            str(root): exponent for root, exponent in sorted(rational_roots.items())
        },
        "rational_root_completeness": (
            "Every factor is certified irreducible over QQ; every nonlinear "
            "factor therefore has no rational root."
        ),
        "boundary_fibres": fibre_records,
        "theorem": (
            "If F_T(T,A)=Q1(T,A)=0 with T,A rational, then T is -1, 0, or 1; "
            "all three values are inadmissible cuboid boundaries."
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
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("Q1 exceptional rational T-values: -1, 0, 1")
    print("all three are inadmissible boundaries")
    print("resultant factorization multiplication-back: OK")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
