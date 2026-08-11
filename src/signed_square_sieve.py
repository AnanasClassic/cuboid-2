#!/usr/bin/env python3
"""Exact finite-field sieve using the signed-square constant theorem.

If the integral quintic H_{p,q}(X) has a monic quadratic factor
X^2+A*X+B, the Newton-polygon theorem proved in
``notes/signed_square_descent.md`` gives one global choice

    B = +d^2  or  B = -d^2.

The sign is fixed over the integers and therefore must be respected at every
odd reduction prime.  This script records, for every projective parameter
class, whether a quadratic divisor with square or negative-square constant
exists.  CRT and inclusion--exclusion then give the exact density of the
union of the two globally sign-consistent residual families.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.modular_sieve import (
    cuboid_quintic,
    is_prime,
    projective_classes,
    remainder_by_monic_quadratic,
)


def sign_certificate(ell: int) -> dict[str, object]:
    if ell == 2 or not is_prime(ell):
        raise ValueError("ell must be an odd prime")

    squares = {value * value % ell for value in range(ell)}
    negative_squares = {-value % ell for value in squares}
    plus: list[list[int]] = []
    minus: list[list[int]] = []
    both: list[list[int]] = []

    for p, q in projective_classes(ell):
        polynomial = cuboid_quintic(p, q, ell)
        has_plus = False
        has_minus = False
        for coefficient in range(ell):
            for constant in range(ell):
                if remainder_by_monic_quadratic(
                    polynomial, coefficient, constant, ell
                ) != (0, 0):
                    continue
                has_plus = has_plus or constant in squares
                has_minus = has_minus or constant in negative_squares
                if has_plus and has_minus:
                    break
            if has_plus and has_minus:
                break

        pair = [p, q]
        if has_plus:
            plus.append(pair)
        if has_minus:
            minus.append(pair)
        if has_plus and has_minus:
            both.append(pair)

    payload: dict[str, object] = {
        "prime": ell,
        "projective_class_count": ell + 1,
        "plus_classes": plus,
        "minus_classes": minus,
        "both_classes": both,
        "plus_count": len(plus),
        "minus_count": len(minus),
        "both_count": len(both),
        "union_count": len(plus) + len(minus) - len(both),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def combined_density(certificates: list[dict[str, object]]) -> tuple[Fraction, Fraction]:
    plus = Fraction(1)
    minus = Fraction(1)
    both = Fraction(1)
    for certificate in certificates:
        total = int(certificate["projective_class_count"])
        plus *= Fraction(int(certificate["plus_count"]), total)
        minus *= Fraction(int(certificate["minus_count"]), total)
        both *= Fraction(int(certificate["both_count"]), total)
    residual = plus + minus - both
    return 1 - residual, residual


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", nargs="*", type=int)
    parser.add_argument("--scan-through", type=int, default=97)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    primes = args.primes
    if primes is None:
        primes = [
            candidate
            for candidate in range(3, args.scan_through + 1)
            if is_prime(candidate)
        ]
    if any(prime == 2 or not is_prime(prime) for prime in primes):
        raise SystemExit("all moduli must be odd primes")

    certificates = [sign_certificate(prime) for prime in primes]
    excluded, residual = combined_density(certificates)
    report = {
        "schema": 1,
        "theorem": "quadratic constant B has one fixed sign: B=+d^2 or B=-d^2",
        "certificates": certificates,
        "excluded_density_among_primitive_pairs": [
            excluded.numerator,
            excluded.denominator,
        ],
        "residual_density_among_primitive_pairs": [
            residual.numerator,
            residual.denominator,
        ],
        "excluded_density_decimal": float(excluded),
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
