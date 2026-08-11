#!/usr/bin/env python3
"""Exact finite-field sieve for quadratic factors of the cuboid quintic.

For a primitive integer pair (p, q), write Q_{p,q}(t)=H_{p,q}(t^2).
If H has a monic quadratic factor over Q, Gauss's lemma gives a monic
quadratic factor over Z.  Its reduction modulo every prime is still monic
of degree two.  Hence a projective residue class for which H has no monic
quadratic divisor is an unconditional local obstruction.

The implementation deliberately uses only Python integers.  It exhausts all
projective classes and all monic quadratics, so every emitted certificate can
be replayed without a computer-algebra system.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from itertools import product
from pathlib import Path


def cuboid_quintic(p: int, q: int, ell: int) -> list[int]:
    """Return H_{p,q}(X), low coefficient first, modulo ell."""
    p %= ell
    q %= ell
    p2, q2 = p * p % ell, q * q % ell
    p4, q4 = p2 * p2 % ell, q2 * q2 % ell
    p6, q6 = p4 * p2 % ell, q4 * q2 % ell
    p8, q8 = p4 * p4 % ell, q4 * q4 % ell
    p10, q10 = p8 * p2 % ell, q8 * q2 % ell

    c4 = (2 * q2 + p2) * (3 * q2 - 2 * p2)
    c3 = q8 + 10 * p2 * q6 + 4 * p4 * q4 - 14 * p6 * q2 + p8
    c2 = -p2 * q2 * (q8 - 14 * p2 * q6 + 4 * p4 * q4 + 10 * p6 * q2 + p8)
    c1 = -p6 * q6 * (q2 + 2 * p2) * (-2 * q2 + 3 * p2)
    c0 = -p10 * q10
    return [c0 % ell, c1 % ell, c2 % ell, c3 % ell, c4 % ell, 1]


def remainder_by_monic_quadratic(poly: list[int], a: int, b: int, ell: int) -> tuple[int, int]:
    """Return remainder r0+r1*X modulo X^2+aX+b over F_ell."""
    r0 = 0
    r1 = 0
    # Horner evaluation in F_ell[X]/(X^2+aX+b).
    for coefficient in reversed(poly):
        # (r0+r1 X)X = -b*r1 + (r0-a*r1)X.
        r0, r1 = (-b * r1 + coefficient) % ell, (r0 - a * r1) % ell
    return r0, r1


def has_monic_quadratic_divisor(poly: list[int], ell: int) -> bool:
    return any(
        remainder_by_monic_quadratic(poly, a, b, ell) == (0, 0)
        for a, b in product(range(ell), repeat=2)
    )


def projective_classes(ell: int) -> list[tuple[int, int]]:
    """Canonical P^1(F_ell): (r,1) for r in F_ell, plus (1,0)."""
    return [(r, 1) for r in range(ell)] + [(1, 0)]


def prime_certificate(ell: int) -> dict[str, object]:
    obstructed: list[list[int]] = []
    admissible: list[list[int]] = []
    for p, q in projective_classes(ell):
        target = obstructed if not has_monic_quadratic_divisor(cuboid_quintic(p, q, ell), ell) else admissible
        target.append([p, q])
    payload: dict[str, object] = {
        "prime": ell,
        "projective_class_count": ell + 1,
        "obstructed_classes": obstructed,
        "residual_classes": admissible,
        "obstructed_count": len(obstructed),
        "residual_count": len(admissible),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def combined_density(certificates: list[dict[str, object]]) -> tuple[Fraction, Fraction]:
    """Return (excluded, residual) density among primitive integer pairs."""
    residual = Fraction(1, 1)
    for cert in certificates:
        residual *= Fraction(int(cert["residual_count"]), int(cert["projective_class_count"]))
    return 1 - residual, residual


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", nargs="*", type=int, default=[3, 5, 7, 11, 13, 17, 19])
    parser.add_argument("--scan-through", type=int)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    primes = args.primes
    if args.scan_through is not None:
        primes = [n for n in range(2, args.scan_through + 1) if is_prime(n)]
    if any(not is_prime(ell) for ell in primes):
        raise SystemExit("all moduli must be prime")

    certificates = [prime_certificate(ell) for ell in primes]
    excluded, residual = combined_density(certificates)
    report = {
        "schema": 1,
        "certificates": certificates,
        "excluded_density_among_primitive_pairs": [excluded.numerator, excluded.denominator],
        "residual_density_among_primitive_pairs": [residual.numerator, residual.denominator],
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
