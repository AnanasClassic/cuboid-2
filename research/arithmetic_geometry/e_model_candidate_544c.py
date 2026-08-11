#!/usr/bin/env python3
"""Exact algebra for the two 544.c candidate models.

Good-prime traces can determine an isogeny class but cannot choose an
isomorphism class inside it.  This script verifies that the two proposed
models have different j-invariants and writes an explicit degree-two isogeny
between them.  It does *not* identify the normalization of H with either one.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def invariants(a: int, b: int) -> dict[str, str]:
    discriminant = -16 * (4 * a**3 + 27 * b**2)
    j = sp.factor(sp.Rational(1728 * 4 * a**3, 4 * a**3 + 27 * b**2))
    return {"discriminant": str(discriminant), "j": str(j)}


def verify() -> dict[str, object]:
    x, y = sp.symbols("x y")
    e1_rhs = x**3 - 5 * x + 4
    X = sp.factor(x - 2 / (x - 1))
    Y = sp.factor(-y * ((x - 1) ** 2 + 2) / (x - 1) ** 2)
    e2_rhs = X**3 + 5 * X + 18
    isogeny_identity = sp.factor(
        sp.together((Y**2 - e2_rhs).subs(y**2, e1_rhs))
    )
    assert isogeny_identity == 0

    e1 = invariants(-5, 4)
    e2 = invariants(5, 18)
    assert e1 == {"discriminant": "1088", "j": "216000/17"}
    assert e2 == {"discriminant": "-147968", "j": "27000/289"}
    assert e1["j"] != e2["j"]

    assert e1_rhs.subs(x, 1) == 0
    assert e1_rhs.subs(x, 0) == 2**2
    assert (x**3 + 5 * x + 18).subs(x, -2) == 0
    assert (x**3 + 5 * x + 18).subs(x, 2) == 6**2

    payload: dict[str, object] = {
        "schema": 1,
        "status": "CANDIDATE_ISOGENY_VERIFIED; IDENTIFICATION_WITH_H_OPEN",
        "E1": {
            "equation": "y^2=x^3-5*x+4",
            **e1,
            "rational_2_torsion": "(1,0)",
            "reported_rank_one_point_checked": "(0,2)",
        },
        "E2": {
            "equation": "Y^2=X^3+5*X+18",
            **e2,
            "rational_2_torsion": "(-2,0)",
            "reported_rank_one_point_checked": "(2,6)",
        },
        "degree_two_isogeny_E1_to_E2": {
            "exceptional_kernel_point": "(1,0)",
            "X": str(X),
            "Y": str(Y),
            "verification": (
                "substitute y^2=x^3-5*x+4 into "
                "Y^2-(X^3+5*X+18); exact result 0"
            ),
        },
        "logical_limit": (
            "Matching Frobenius traces with 544.c proves at most an isogeny "
            "fingerprint until conductor completeness is certified; even an "
            "isogeny-class proof would not choose E1 versus E2 because their "
            "j-invariants differ. An exact H-normalization map or exact "
            "j-invariant is still required."
        ),
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
    print("E1 j=216000/17; E2 j=27000/289: non-isomorphic")
    print("explicit degree-two isogeny E1 -> E2: verified")
    print("identification of normalization(H): OPEN")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
