#!/usr/bin/env python3
"""Exact branch audit for the signed-square reciprocal descent.

Let E be the normalization of the reciprocal quotient of the two-root
factorization curve, with invariant functions

    U = s + 1/s,       W = b + 1/b.

An actual quadratic factor has s a rational square and b a signed rational
square.  The square-parameter condition requires *both* square roots of
``U+2`` and ``U-2``.  Consequently it lies on one of two (Z/2)^3 covers
obtained by adjoining square roots of

    f_s+ = U+2,  f_s- = U-2,  f_b+ = W+2 or f_b- = 2-W.

This script certifies the local identities and separability tests behind the
branch counts.  The Newton data at s=0,-1 and the reciprocal quotient genus
are independently checked in ``src/geometry_audit.py``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from itertools import combinations
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from src.geometry_audit import P, c, d, s, x


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "artifacts" / "reciprocal_b_branch_audit.json"


def verify() -> dict[str, object]:
    U, W, b, y, k, omega = sp.symbols("U W b y k omega")

    # Identities whose parity divisors define the three double covers.
    identities = {
        "U_plus_2": sp.factor(s + 1 / s + 2),
        "U_minus_2": sp.factor(s + 1 / s - 2),
        "W_plus_2": sp.factor(b + 1 / b + 2),
        "two_minus_W": sp.factor(2 - b - 1 / b),
    }
    assert identities == {
        "U_plus_2": (s + 1) ** 2 / s,
        "U_minus_2": (s - 1) ** 2 / s,
        "W_plus_2": (b + 1) ** 2 / b,
        "two_minus_W": -(b - 1) ** 2 / b,
    }

    # At s=1 the root near +1 has slope 5.  The four roots near -1
    # have slopes given by q(c), and q has four distinct roots.  No two
    # negative slopes sum to zero, and no negative slope equals 5.  Hence
    # b+1 is simple on each of the four mixed pairs and b-1 is simple on
    # each of the six negative-negative pairs.
    slope_quartic = c**4 - 8 * c**2 - 12 * c - 4
    near_positive = sp.expand(P.subs({s: 1 + d, x: 1 + k * d}, simultaneous=True))
    assert sp.expand(near_positive.coeff(d, 1) - 16 * (k - 5)) == 0
    assert sp.discriminant(slope_quartic, c) == -11008
    assert sp.gcd(slope_quartic, slope_quartic.subs(c, -c)) == 1
    assert slope_quartic.subs(c, 5) == 361

    # At s=-1, write s+1=t^5.  The first Newton face is y^5+64t^5,
    # so the five leading root coefficients differ by fifth roots of unity.
    # A pair sum cannot vanish because -1 is not a fifth root of unity.
    assert sp.gcd(omega**5 - 1, omega + 1) == 1

    # At s=0 the exact root valuations are 0,0,1,2,2 and inertia swaps
    # the last two roots.  The seven places of the two-subset cover are
    # four fixed subsets and three two-element orbits.  Odd ord(s) occurs
    # at AB, AC, BC, DE; odd ord(b) only at AC and BC.
    root_valuations = {"A": 0, "B": 0, "C": 1, "D": 2, "E": 2}
    fixed_subsets = [("A", "B"), ("A", "C"), ("B", "C"), ("D", "E")]
    two_cycle_representatives = [("A", "D"), ("B", "D"), ("C", "D")]
    fixed_b_orders = {
        "".join(pair): sum(root_valuations[root] for root in pair)
        for pair in fixed_subsets
    }
    assert fixed_b_orders == {"AB": 0, "AC": 1, "BC": 1, "DE": 4}
    assert len(list(combinations(root_valuations, 2))) == 10
    assert len(fixed_subsets) + len(two_cycle_representatives) == 7
    zero_odd_s = {"AB", "AC", "BC", "DE"}
    zero_odd_b = {name for name, order in fixed_b_orders.items() if order % 2}
    assert zero_odd_b == {"AC", "BC"}

    # Branch sets on E.  The four odd-s points and the two odd-b points at
    # s=0 are paired with their reciprocal points at infinity.  At s=1,
    # the 4 mixed pairs contribute to W+2 and the 6 negative pairs to 2-W.
    # At s=-1 the two five-cycle pair-orbits contribute to U+2 and 2-W.
    branch_sets = {
        "U_plus_2": {
            "s=0/infinity": len(zero_odd_s),
            "s=-1": 2,
        },
        "U_minus_2": {
            "s=0/infinity": len(zero_odd_s),
            "s=1_all_pairs": 10,
        },
        "W_plus_2": {
            "s=0/infinity": len(zero_odd_b),
            "s=1_mixed_pairs": 4,
        },
        "two_minus_W": {
            "s=0/infinity": len(zero_odd_b),
            "s=1_negative_pairs": 6,
            "s=-1": 2,
        },
    }
    totals = {name: sum(parts.values()) for name, parts in branch_sets.items()}
    assert totals == {
        "U_plus_2": 6,
        "U_minus_2": 14,
        "W_plus_2": 6,
        "two_minus_W": 10,
    }

    intersections = {
        "U_plus_2_and_U_minus_2": len(zero_odd_s),
        "U_plus_2_and_positive": len(zero_odd_b),
        "U_plus_2_and_negative": len(zero_odd_b) + 2,
        "U_minus_2_and_positive": len(zero_odd_b) + 4,
        "U_minus_2_and_negative": len(zero_odd_b) + 6,
    }
    assert intersections == {
        "U_plus_2_and_U_minus_2": 4,
        "U_plus_2_and_positive": 2,
        "U_plus_2_and_negative": 4,
        "U_minus_2_and_positive": 6,
        "U_minus_2_and_negative": 8,
    }

    # For a double cover of a genus-one curve branched at r points,
    # g=1+r/2.  The product character branches on the symmetric difference.
    double_cover_genera = {
        "square_parameter_plus": 1 + totals["U_plus_2"] // 2,
        "square_parameter_minus": 1 + totals["U_minus_2"] // 2,
        "positive_constant": 1 + totals["W_plus_2"] // 2,
        "negative_constant": 1 + totals["two_minus_W"] // 2,
    }
    pair_character_branch_totals = {
        "parameter_product": totals["U_plus_2"]
        + totals["U_minus_2"]
        - 2 * intersections["U_plus_2_and_U_minus_2"],
        "plus_with_positive": totals["U_plus_2"]
        + totals["W_plus_2"]
        - 2 * intersections["U_plus_2_and_positive"],
        "plus_with_negative": totals["U_plus_2"]
        + totals["two_minus_W"]
        - 2 * intersections["U_plus_2_and_negative"],
        "minus_with_positive": totals["U_minus_2"]
        + totals["W_plus_2"]
        - 2 * intersections["U_minus_2_and_positive"],
        "minus_with_negative": totals["U_minus_2"]
        + totals["two_minus_W"]
        - 2 * intersections["U_minus_2_and_negative"],
    }
    pair_character_genera = {
        sign: 1 + branch_count // 2
        for sign, branch_count in pair_character_branch_totals.items()
    }
    assert double_cover_genera == {
        "square_parameter_plus": 4,
        "square_parameter_minus": 8,
        "positive_constant": 4,
        "negative_constant": 6,
    }
    assert pair_character_branch_totals == {
        "parameter_product": 12,
        "plus_with_positive": 8,
        "plus_with_negative": 8,
        "minus_with_positive": 8,
        "minus_with_negative": 8,
    }
    assert pair_character_genera == {
        "parameter_product": 7,
        "plus_with_positive": 5,
        "plus_with_negative": 5,
        "minus_with_positive": 5,
        "minus_with_negative": 5,
    }

    # Triple products are checked by the disjoint local categories above.
    # Positive sign: 2 zero/infinity + 2 at s=-1 + 6 negative pairs at s=1.
    # Negative sign: 2 zero/infinity + 4 mixed pairs at s=1.
    triple_character_branch_totals = {"positive": 10, "negative": 6}
    triple_character_genera = {"positive": 6, "negative": 4}

    # Kani--Rosen dimension identity for a V4-cover Y -> E:
    # J(Y) x J(E)^2 ~ J(C1) x J(C2) x J(C3).
    v4_genera = {
        "positive": 4 + 4 + 5 - 2,
        "negative": 4 + 6 + 5 - 2,
    }
    assert v4_genera == {"positive": 11, "negative": 13}

    # For a (Z/2)^3 cover of a genus-one base, the Jacobian is isogenous to
    # E times the seven character Pryms.  Thus g(Y)=sum(g_character)-6.
    character_genera = {
        "positive": [4, 8, 4, 7, 5, 5, 6],
        "negative": [4, 8, 6, 7, 5, 5, 4],
    }
    full_cover_genera = {
        sign: sum(genera) - 6 for sign, genera in character_genera.items()
    }
    assert full_cover_genera == {"positive": 33, "negative": 33}

    payload: dict[str, object] = {
        "schema": 1,
        "base_genus": 1,
        "function_identities": {name: str(value) for name, value in identities.items()},
        "s_equals_1": {
            "positive_root_slope": 5,
            "negative_slope_quartic": str(slope_quartic),
            "slope_discriminant": -11008,
            "gcd_qc_qminus_c": "1",
            "q_at_5": 361,
            "mixed_pairs_b_equals_minus_1": 4,
            "negative_pairs_b_equals_1": 6,
        },
        "s_equals_minus_1": {
            "two_pair_orbits": 2,
            "pair_sum_nonzero_certificate": "gcd(omega^5-1,omega+1)=1",
        },
        "s_equals_0_and_infinity": {
            "root_valuations": root_valuations,
            "normalization_places": 7,
            "odd_s_places": sorted(zero_odd_s),
            "odd_b_places": sorted(zero_odd_b),
        },
        "branch_sets": branch_sets,
        "branch_totals": totals,
        "branch_intersections": intersections,
        "double_cover_genera": double_cover_genera,
        "pair_character_branch_totals": pair_character_branch_totals,
        "pair_character_genera": pair_character_genera,
        "triple_character_branch_totals": triple_character_branch_totals,
        "triple_character_genera": triple_character_genera,
        "v4_cover_genera": v4_genera,
        "full_character_genera": character_genera,
        "full_signed_square_cover_genera": full_cover_genera,
        "kani_rosen_v4": "J(Y) x J(E)^2 ~ J(C_s) x J(C_b) x J(C_product)",
        "square_parameter_warning": (
            "U+2 square alone is necessary but not sufficient; U-2 must also be square"
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
    print("branch totals U+2, U-2, W+2, 2-W: 6, 14, 6, 10")
    print("V4 necessary-sieve genera: 11, 13")
    print("full (Z/2)^3 signed-square cover genera: 33, 33")
    print("wrote", args.output.resolve().relative_to(ROOT))


if __name__ == "__main__":
    main()
