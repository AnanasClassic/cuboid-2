#!/usr/bin/env python3
"""Exact lightweight audit of the three characters and 2-isogeny class.

This script deliberately does not normalize H or assume that its
normalization is the candidate curve E1.  It checks two separate statements:

1. every nonzero product of q+2, q-2 and epsilon*V has a nonempty odd
   divisor on the normalization of H, for either epsilon;
2. on the candidate E1, the standard 2-isogeny Kummer function x-1 has an
   even divisor.

Consequently, conditional on a future identification with E1, the Kummer
class cannot be a constant times a nontrivial product of the three cuboid
characters modulo squares.  This rules out only a direct square-class
identity; it is not a rational-point classification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from functools import reduce
from itertools import product
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
COVER = Path(__file__).with_name("new_three_square_character_covers.json")
DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def symmetric_difference(parts: list[set[str]]) -> set[str]:
    return reduce(set.__xor__, parts, set())


def character_supports(
    basis: tuple[set[str], set[str], set[str]],
) -> dict[str, set[str]]:
    answer: dict[str, set[str]] = {}
    for bits in product((0, 1), repeat=3):
        if bits == (0, 0, 0):
            continue
        answer["".join(str(bit) for bit in bits)] = symmetric_difference(
            [basis[index] for index, bit in enumerate(bits) if bit]
        )
    return answer


def is_zero(expr: sp.Expr) -> bool:
    return sp.factor(sp.cancel(expr)) == 0


def verify() -> dict[str, object]:
    cover = json.loads(COVER.read_text(encoding="utf-8"))
    assert cover["schema"] == 2

    q, T, B, A, X = sp.symbols("q T B A X")
    U = 2 * (q + 6) / (q - 2)
    assert is_zero((q - 2) / (U - 2) - (q - 2) ** 2 / 16)
    assert is_zero(
        (q + 2) / ((U + 2) * (U - 2)) - (q - 2) ** 2 / 64
    )

    q_T = T**2 + T**-2
    V = A**2 / (1 - B**2)
    W = 2 * (1 + B**2) / (1 - B**2)
    negative_basis_root = A * T / (2 * B * (T**2 + 1))
    assert is_zero(V / (W + 2) - (A / 2) ** 2)
    assert is_zero(
        negative_basis_root**2 - (-V) / ((q_T + 2) * (2 - W))
    )
    # These are the two deck transformations used to form E.
    assert is_zero(
        negative_basis_root.subs({T: -T, B: -B}, simultaneous=True)
        - negative_basis_root
    )
    assert is_zero(
        negative_basis_root.subs(T, 1 / T) - negative_basis_root
    )

    Zb = {"Z_AC", "Z_BC"}
    Zn = {"Z_AB", "Z_DE"}
    L = {"L_minus_1_1", "L_minus_1_2"}
    M = {f"M_plus_1_mixed_{index}" for index in range(1, 5)}
    N = {f"N_plus_1_negative_{index}" for index in range(1, 7)}
    Z = Zb | Zn

    U_plus = Z | L
    U_minus = Z | M | N
    q_plus = U_plus ^ U_minus
    q_minus = U_minus
    V_support = Zb | M
    two_minus_W_support = Zb | L | N

    # This is the divisor-parity form of [-V]=[q+2]+[2-W].  Multiplication
    # by the constant -1 does not change the divisor of V.
    assert q_plus ^ two_minus_W_support == V_support

    literal_supports = character_supports((q_plus, q_minus, V_support))
    literal_degrees = {
        bits: len(support) for bits, support in literal_supports.items()
    }
    expected_degrees = {
        "001": 6,
        "010": 14,
        "011": 8,
        "100": 12,
        "101": 10,
        "110": 6,
        "111": 8,
    }
    assert literal_degrees == expected_degrees
    assert all(literal_degrees.values())

    positive_table = cover["characters_positive"]
    assert all(
        set(positive_table[bits]["branch_support"]) == support
        for bits, support in literal_supports.items()
    )
    negative_stored_supports = character_supports(
        (q_plus, q_minus, two_minus_W_support)
    )
    negative_table = cover["characters_negative"]
    assert all(
        set(negative_table[bits]["branch_support"]) == support
        for bits, support in negative_stored_supports.items()
    )
    assert negative_table["001"]["label"] == "2-W"
    assert set(negative_table["101"]["branch_support"]) == V_support
    assert cover["character_bases"]["negative"] == {
        "stored_basis": ["q+2", "q-2", "2-W"],
        "physical_basis": ["q+2", "q-2", "-V"],
        "square_class_relation_on_E": "[-V]=[q+2]+[2-W]",
        "physical_to_stored_bits": "(a,b,c)->(a+c,b,c)",
        "literal_minus_V_stored_bits": "101",
        "reason_cover_is_unchanged": "q+2 is already a square on the full cover",
    }

    # Candidate E1 in shifted coordinates.  X has its only affine zero at
    # T_2=(0,0).  Since X^2+3X-2 is a unit there, the equation makes that
    # zero double; on a monic cubic Weierstrass model X has its standard
    # double pole at O.  Hence div(X)=2(T_2)-2(O).
    shifted_rhs = X * (X**2 + 3 * X - 2)
    assert shifted_rhs.subs(X, 0) == 0
    assert (X**2 + 3 * X - 2).subs(X, 0) == -2
    assert sp.Poly(shifted_rhs, X).degree() == 3
    assert sp.Poly(shifted_rhs, X).LC() == 1

    points = {
        "P": (sp.Integer(-1), sp.Integer(2)),
        "T": (sp.Integer(0), sp.Integer(0)),
        "P_plus_T": (sp.Integer(2), sp.Integer(4)),
    }
    assert all(
        y_value**2 == shifted_rhs.subs(X, x_value)
        for x_value, y_value in points.values()
    )
    alpha_parity_table = {
        f"n_mod_2={n},e={e}": (-1) ** n * (-2) ** e
        for n, e in product((0, 1), repeat=2)
    }
    assert alpha_parity_table == {
        "n_mod_2=0,e=0": 1,
        "n_mod_2=0,e=1": -2,
        "n_mod_2=1,e=0": -1,
        "n_mod_2=1,e=1": 2,
    }

    payload: dict[str, object] = {
        "schema": 1,
        "theorem": (
            "Every nontrivial product of q+2, q-2 and epsilon*V is "
            "ramified on the normalization of H, for epsilon=+1 or -1."
        ),
        "cover_source_checksum": cover["sha256_without_checksum"],
        "global_square_class_identities": {
            "q_minus_2": "(q-2)/(U-2)=(q-2)^2/16",
            "q_plus_2": "(q+2)/((U+2)(U-2))=(q-2)^2/64",
            "positive_V": "V/(W+2)=(A/2)^2",
            "negative_basis": (
                "(-V)/((q+2)(2-W))=(A*T/(2*B*(T^2+1)))^2"
            ),
        },
        "literal_basis": ["q+2", "q-2", "epsilon*V"],
        "literal_character_branch_degrees": literal_degrees,
        "all_nontrivial_literal_characters_ramified": True,
        "negative_basis_audit": {
            "stored_basis": ["q+2", "q-2", "2-W"],
            "physical_basis": ["q+2", "q-2", "-V"],
            "relation": "[-V]=[q+2]+[2-W]",
            "literal_minus_V_stored_bits": "101",
            "full_cover_unchanged": True,
        },
        "candidate_E1_kummer": {
            "model": "Y^2=X*(X^2+3*X-2), X=x-1",
            "function": "X",
            "divisor": "2*(T)-2*(O)",
            "divisor_is_even": True,
            "alpha_nP_plus_eT": "(-1)^n*(-2)^e",
            "parity_table": alpha_parity_table,
        },
        "conditional_corollary": (
            "After any exact identification of normalization(H) with E1, "
            "the standard unramified 2-isogeny Kummer class is not a "
            "constant times any nontrivial product of the three cuboid "
            "characters modulo squares."
        ),
        "logical_scope": (
            "The ramification theorem is unconditional and does not assume "
            "C025. The comparison with E1 is conditional on C025 and rules "
            "out only a direct function-field square-class identity; it "
            "does not classify rational points."
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
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print("all seven literal signed-V characters are ramified: OK")
    print("negative-b basis correction [-V]=[q+2]+[2-W]: OK")
    print("direct unramified 2-isogeny Kummer identity: EXCLUDED")
    try:
        displayed_output = args.output.resolve().relative_to(ROOT)
    except ValueError:
        displayed_output = args.output.resolve()
    print("wrote", displayed_output)


if __name__ == "__main__":
    main()
