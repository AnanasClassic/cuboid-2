#!/usr/bin/env python3
"""Exact triage of the q-projection of the singular plane model H(q,A).

This does not normalize H and does not infer ramification indices from the
plane discriminant.  Its purpose is narrower: certify the input degree, a
rational smooth point used by the Sage Riemann--Roch route, and the complete
factorization of Disc_A(H).  The many factors show that a Belyi claim cannot
be read directly from this singular plane model; they do not rule out
cancellation after normalization.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
INPUT = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def verify() -> dict[str, object]:
    data = json.loads(INPUT.read_text())
    q, A = sp.symbols("q A")
    H = sp.Poly.from_dict(
        {
            tuple(term["powers"]): sp.Integer(term["coefficient"])
            for term in data["elliptic_plane_model"]["terms"]
        },
        gens=(q, A),
    ).as_expr()
    assert sp.degree(H, q) == 8 and sp.degree(H, A) == 10
    point = {q: sp.Integer(6), A: sp.Rational(6, 7)}
    assert H.subs(point) == 0
    gradient = (sp.diff(H, q).subs(point), sp.diff(H, A).subs(point))
    assert gradient != (0, 0)

    discriminant = sp.discriminant(H, A)
    content, factors = sp.factor_list(discriminant, q)
    assert sp.degree(discriminant, q) == 114
    signature = sorted((sp.degree(factor, q), exponent) for factor, exponent in factors)
    assert signature == [(1, 4), (1, 20), (1, 27), (2, 12), (3, 3), (15, 2)]
    assert all(sp.Poly(factor, q).is_irreducible for factor, _ in factors)
    assert all(
        sp.gcd(first, second) == 1
        for index, (first, _) in enumerate(factors)
        for second, _ in factors[index + 1 :]
    )

    special = {
        "q=-2": sp.factor(H.subs(q, -2)),
        "q=2": sp.factor(H.subs(q, 2)),
        "q=-10/3": sp.factor(H.subs(q, sp.Rational(-10, 3))),
    }
    assert special["q=-2"] == 2**16 * (A - 2) ** 10
    assert special["q=2"] == 2**27 * A**3 * (A - 6) * (A**2 - 12 * A + 4) ** 3

    payload: dict[str, object] = {
        "schema": 1,
        "artifact_checksum": data["sha256_without_checksum"],
        "degree_q": 8,
        "degree_A": 10,
        "rational_smooth_point": {
            "q": "6",
            "A": "6/7",
            "gradient": [str(value) for value in gradient],
        },
        "discriminant_in_A": {
            "degree_q": 114,
            "content": str(content),
            "factors": [
                {
                    "polynomial": str(factor),
                    "degree": int(sp.degree(factor, q)),
                    "exponent": int(exponent),
                    "irreducible_over_Q": True,
                }
                for factor, exponent in factors
            ],
            "pairwise_coprime": True,
        },
        "special_fibres": {name: str(value) for name, value in special.items()},
        "conclusion": {
            "proved": (
                "The singular plane discriminant has 23 distinct geometric "
                "roots, so it does not by itself supply a three-branch-point "
                "or Belyi certificate."
            ),
            "not_proved": (
                "Plane discriminant roots and exponents may disappear or "
                "change after normalization; no assertion that the normalized "
                "q-map is non-Belyi, and no genus or rational-point result, "
                "is made here."
            ),
        },
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
    print("H degree (q,A): (8,10); rational smooth point (6,6/7): OK")
    print("Disc_A(H) factor degrees/exponents: 1^27,1^20,1^4,2^12,3^3,15^2")
    print("plane discriminant alone gives no Belyi certificate")
    print("wrote", args.output.relative_to(ROOT))


if __name__ == "__main__":
    main()
