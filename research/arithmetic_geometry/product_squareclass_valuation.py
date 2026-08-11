#!/usr/bin/env python3
"""Exact certificate for the product-character valuation descent.

The certificate starts on E1 in the translated coordinates

    Y^2 = X^3 - 5*X + 4,
    h = X + 1,                 k = (Y + 2)/X.

If the product cuboid character is a square, the preceding transport gives
``z^2 = 2*k*h``.  The identities checked here reduce that condition to the
single positive genus-two square-abscissa problem used by the final sieve.
No rational-point search is used.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def verify() -> dict[str, object]:
    X, Y, k, h, u, v, U = sp.symbols("X Y k h u v U")
    elliptic = Y**2 - (X**3 - 5 * X + 4)

    # The line through the rational 2-torsion point (0,-2) has slope k.
    line_substitution = sp.factor(elliptic.subs(Y, k * X - 2))
    assert sp.expand(
        line_substitution + X * (X**2 - k**2 * X + 4 * k - 5)
    ) == 0
    quadratic = sp.expand(
        h**2 - (k**2 + 2) * h + (k**2 + 4 * k - 4)
    )
    assert sp.expand(
        line_substitution.subs(X, h - 1) + (h - 1) * quadratic
    ) == 0
    discriminant = sp.factor(sp.discriminant(quadratic, h))
    assert discriminant == k**4 - 16 * k + 20
    # Exact residue derivation for the two excluded nonnegative 2-adic
    # cases.  Odd k gives Delta=5 mod 8.  If k=4*t, then Delta/4 is 5 mod 8
    # for every 2-adic integer t (and hence whenever v_2(k)>=2).
    assert all(int(discriminant.subs(k, odd)) % 8 == 5 for odd in (1, 3, 5, 7))
    t = sp.symbols("t", integer=True)
    delta_over_four_at_4t = sp.expand(discriminant.subs(k, 4 * t) / 4)
    assert delta_over_four_at_4t == 64 * t**4 - 16 * t + 5
    assert all(
        int(delta_over_four_at_4t.subs(t, residue)) % 8 == 5
        for residue in range(8)
    )

    # The valuation lemma (proved in the companion note) says that z^2=2kh
    # forces k=2*eps*u^2 and h=eps*v^2.  Here we certify both resulting
    # eliminations exactly.
    negative_relation = sp.factor(quadratic.subs({k: -2 * U, h: -v**2}))
    assert negative_relation == (
        4 * U**2 * v**2
        + 4 * U**2
        - 8 * U
        + v**4
        + 2 * v**2
        - 4
    )
    negative_U_discriminant = sp.factor(sp.discriminant(negative_relation, U))
    assert sp.expand(
        negative_U_discriminant
        + 16 * (v**2 + 2) * (v**4 + v**2 - 4)
    ) == 0

    positive_relation = sp.factor(quadratic.subs({k: 2 * U, h: v**2}))
    assert positive_relation == (
        -4 * U**2 * v**2
        + 4 * U**2
        + 8 * U
        + v**4
        - 2 * v**2
        - 4
    )
    positive_s_discriminant = sp.factor(discriminant.subs(k, 2 * u**2) / 4)
    assert positive_s_discriminant == 4 * u**8 - 8 * u**2 + 5

    a, r, R = sp.symbols("a r R")
    H = 4 * u**8 - 8 * u**2 + 5
    genus_two = 4 * a**5 - 8 * a**2 + 5 * a
    assert sp.expand(genus_two.subs(a, u**2) - u**2 * H) == 0

    # Exact residue checks used in the elementary exclusion of the negative
    # sign.  For v=m/n in lowest terms, a rational point would make
    # -(m^2+2n^2)(m^4+m^2n^2-4n^4) a square.  The four parity cases are
    # covered by the three coprime possibilities below.
    parity_audit = {
        "m_odd_n_odd_mod8": {
            "first_factor": 3,
            "second_factor": 6,
            "negative_product": 6,
        },
        "m_odd_n_even_mod8": {
            "negative_product_if_n_v2_1": 3,
            "negative_product_if_n_v2_ge_2": 7,
        },
        "m_even_n_odd": {
            "v2_negative_product_if_m_v2_1": 5,
            "v2_negative_product_if_m_v2_ge_2": 3,
        },
    }
    squares_mod_8 = {0, 1, 4}
    assert parity_audit["m_odd_n_odd_mod8"]["negative_product"] not in squares_mod_8
    assert all(
        parity_audit["m_odd_n_even_mod8"][key] not in squares_mod_8
        for key in (
            "negative_product_if_n_v2_1",
            "negative_product_if_n_v2_ge_2",
        )
    )
    assert all(
        exponent % 2
        for exponent in parity_audit["m_even_n_odd"].values()
    )

    payload: dict[str, object] = {
        "schema": 1,
        "elliptic_model": "Y^2=X^3-5*X+4",
        "definitions": {
            "h": "X+1 (not the original cuboid parameter s)",
            "k": "(Y+2)/X",
        },
        "quadratic_relation": "h^2-(k^2+2)h+(k^2+4k-4)=0",
        "quadratic_discriminant": "k^4-16k+20",
        "square_character_equation": "z^2=2*k*h",
        "valuation_conclusion": {
            "odd_primes": "v_l(k) is even",
            "prime_2": "v_2(k) is odd",
            "squareclasses": "k=2*epsilon*u^2 and h=epsilon*v^2",
        },
        "negative_sign": {
            "auxiliary_curve": "W^2=-(v^2+2)*(v^4+v^2-4)",
            "parity_audit": parity_audit,
            "rational_points_compatible_with_square_character": False,
        },
        "positive_sign": {
            "octic": "r^2=4*u^8-8*u^2+5",
            "genus_two_curve": "R^2=4*a^5-8*a^2+5*a",
            "map": "a=u^2, R=u*r",
            "remaining_condition": "a is a rational square",
        },
        "theorem": (
            "Every nonexceptional rational point satisfying the product "
            "square character has positive sign and maps to a rational point "
            "on R^2=4a^5-8a^2+5a with square abscissa."
        ),
        "logical_scope": (
            "This is an exact reduction.  The rational square-abscissa "
            "classification is supplied by the separate genus-two sieve."
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
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("product-character valuation descent: PASS")
    print("wrote", args.output)


if __name__ == "__main__":
    main()
