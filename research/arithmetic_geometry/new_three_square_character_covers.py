#!/usr/bin/env python3
"""Exact character decomposition of the full square/signed-square cover.

This is deliberately separate from ``reciprocal_b_branch_audit.py``.  That
script certifies the local branch data for U+2, W+2 and 2-W.  Here we use its
certificate, add the *second* square needed to recover a rational T (or z),
and change to the q-coordinate of ``genus4_quotient.json``.

Notation
--------

    U = s + 1/s,
    q = T^2 + T^(-2),
    U = 2(q+6)/(q-2),
    V = a^2/b.

An admissible rational square parameter requires both q+2 and q-2 to be
squares.  The single condition U+2=square is only a necessary quotient
condition and does not by itself recover rational s=z^2.

For a signed-square constant term, V is a square (b>0 branch) or -V is a
square (b<0 branch).  Its square class agrees respectively with W+2 or 2-W,
where W=b+1/b.  Thus the exact branch certificate for W can be reused for V.

The full cover is generically a (Z/2Z)^3-cover of the elliptic normalization
E.  This script exports all seven character double covers, their exact branch
supports and genera, the total genus, the Kani--Rosen/Prym dimension identity,
and the generic inverse back to (s,a,b).

No Mordell--Weil rank or rational-point completeness claim is made here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import product
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
GENUS4 = ROOT / "artifacts" / "genus4_quotient.json"
BRANCH = ROOT / "artifacts" / "reciprocal_b_branch_audit.json"
DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def sparse_to_poly(
    terms: list[dict[str, object]], variables: tuple[sp.Symbol, ...]
) -> sp.Poly:
    return sp.Poly.from_dict(
        {
            tuple(int(e) for e in term["powers"]): sp.Integer(term["coefficient"])
            for term in terms
        },
        gens=variables,
    )


def symmetric_difference(*sets: set[str]) -> set[str]:
    answer: set[str] = set()
    for subset in sets:
        answer ^= subset
    return answer


def verify() -> dict[str, object]:
    genus4 = json.loads(GENUS4.read_text())
    branch = json.loads(BRANCH.read_text())

    q, U, W, a, b, A, B, T, X = sp.symbols("q U W a b A B T X")

    # Exact changes of coordinates and square-class identities.
    U_of_q = 2 * (q + 6) / (q - 2)
    identities = {
        "q_minus_2_over_U_minus_2": sp.factor(
            (q - 2) / (U_of_q - 2)
        ),
        "q_plus_2_over_product_U_pm_2": sp.factor(
            (q + 2) / ((U_of_q + 2) * (U_of_q - 2))
        ),
        "q_squared_minus_4_over_U_plus_2": sp.factor(
            (q**2 - 4) / (U_of_q + 2)
        ),
        "V_over_W_plus_2": sp.factor(
            (a**2 / b) / (b + 1 / b + 2)
        ),
        "minus_V_over_2_minus_W": sp.factor(
            (-a**2 / b) / (2 - b - 1 / b)
        ),
        "V_in_AB_chart": sp.factor(
            (A**2 / (1 - B**2)).subs(
                {A: 2 * a / (b + 1), B: (b - 1) / (b + 1)},
                simultaneous=True,
            )
        ),
    }
    expected = {
        "q_minus_2_over_U_minus_2": (q - 2) ** 2 / 16,
        "q_plus_2_over_product_U_pm_2": (q - 2) ** 2 / 64,
        "q_squared_minus_4_over_U_plus_2": (q - 2) ** 2 / 4,
        "V_over_W_plus_2": a**2 / (b + 1) ** 2,
        "minus_V_over_2_minus_W": a**2 / (b - 1) ** 2,
        "V_in_AB_chart": a**2 / b,
    }
    assert all(sp.cancel(identities[name] - value) == 0 for name, value in expected.items())

    # Check the q-model and the two successive quotient identities from the
    # saved exact artifact.  This also fixes which q is being used here.
    G = sparse_to_poly(
        genus4["genus4_model"]["terms"], (X, A)
    ).as_expr()
    H = sparse_to_poly(
        genus4["elliptic_plane_model"]["terms"], (q, A)
    ).as_expr()
    assert sp.cancel(G - X**8 * H.subs(q, X + 1 / X)) == 0
    assert sp.cancel(
        (T**2 + T**-2 + 2) - (T + T**-1) ** 2
    ) == 0
    assert sp.cancel(
        (T**2 + T**-2 - 2) - (T - T**-1) ** 2
    ) == 0
    assert sp.cancel(
        (X - X**-1) ** 2 - ((X + X**-1) ** 2 - 4)
    ) == 0

    # The branch audit uses atomic normalization places, not merely plane
    # intersection multiplicities.  Zb is the two-place subset at s=0/infty
    # where ord(b) is odd; Zn are the other two odd-s places.
    Zb = {"Z_AC", "Z_BC"}
    Zn = {"Z_AB", "Z_DE"}
    L = {"L_minus_1_1", "L_minus_1_2"}
    M = {f"M_plus_1_mixed_{i}" for i in range(1, 5)}
    N = {f"N_plus_1_negative_{i}" for i in range(1, 7)}
    Z = Zb | Zn

    U_plus = Z | L
    U_minus = Z | M | N
    V_positive = Zb | M
    V_negative = Zb | L | N

    assert len(U_plus) == branch["branch_totals"]["U_plus_2"] == 6
    assert len(V_positive) == branch["branch_totals"]["W_plus_2"] == 6
    assert len(V_negative) == branch["branch_totals"]["two_minus_W"] == 10
    # U-2 is the missing square.  Its ten s=1 fixed branches and four
    # zero/infinity branches give 14; this is also the genus-7 -> genus-1
    # reciprocal double cover via Riemann--Hurwitz.
    assert len(U_minus) == 14

    # Change F_2-basis from (U+2,U-2, signed V) to
    # (q+2,q-2,signed V).  Square classes:
    # [q+2]=[U+2]+[U-2], [q-2]=[U-2].
    q_plus = symmetric_difference(U_plus, U_minus)
    q_minus = U_minus
    assert len(q_plus) == 12
    assert len(q_minus) == 14
    assert symmetric_difference(q_plus, q_minus) == U_plus
    square_pullback_union = q_plus | q_minus
    assert len(square_pullback_union) == 16
    square_pullback_genus = 1 + len(square_pullback_union)
    assert square_pullback_genus == 17
    # V4 Kani--Rosen check for adjoining sqrt(q+2) and sqrt(q-2).
    assert square_pullback_genus + 2 == 7 + 8 + 4

    def characters(v_branch: set[str]) -> dict[str, dict[str, object]]:
        basis = [q_plus, q_minus, v_branch]
        names = ["q+2", "q-2", "signed_V"]
        result: dict[str, dict[str, object]] = {}
        for bits in product((0, 1), repeat=3):
            if bits == (0, 0, 0):
                continue
            support = symmetric_difference(
                *(basis[i] for i, bit in enumerate(bits) if bit)
            )
            label = " * ".join(names[i] for i, bit in enumerate(bits) if bit)
            branch_degree = len(support)
            assert branch_degree % 2 == 0
            genus = 1 + branch_degree // 2
            result["".join(str(bit) for bit in bits)] = {
                "label": label,
                "equation": f"Y^2=({label})",
                "branch_degree": branch_degree,
                "branch_support": sorted(support),
                "genus": genus,
                "prym_dimension": genus - 1,
                "geometry": "bielliptic; non-hyperelliptic by Castelnuovo-Severi",
            }
        return result

    chars_positive = characters(V_positive)
    chars_negative = characters(V_negative)

    expected_positive = {
        "100": 7,  # q+2
        "010": 8,  # q-2
        "001": 4,  # V
        "110": 4,  # q^2-4
        "101": 6,
        "011": 5,
        "111": 5,
    }
    expected_negative = {
        "100": 7,
        "010": 8,
        "001": 6,  # -V
        "110": 4,
        "101": 4,
        "011": 5,
        "111": 5,
    }
    assert {key: value["genus"] for key, value in chars_positive.items()} == expected_positive
    assert {key: value["genus"] for key, value in chars_negative.items()} == expected_negative

    # For an elementary 2-cover of a genus-one base, every branch place has
    # inertia order two.  The union is Z | L | M | N, of degree 16, hence
    # 2g(Y)-2 = 2^(3-1)*16 and g(Y)=33.  Equivalently, the seven Prym
    # dimensions plus dim J(E)=1 add to 33.
    branch_union = Z | L | M | N
    assert len(branch_union) == 16

    def total_genus(chars: dict[str, dict[str, object]]) -> int:
        via_pryms = 1 + sum(int(item["prym_dimension"]) for item in chars.values())
        via_hurwitz = 1 + 2 * len(branch_union)
        assert via_pryms == via_hurwitz == 33
        # Equivalent Kani--Rosen dimension check:
        # J(Y) x J(E)^6 ~ product_{chi != 1} J(C_chi).
        assert 33 + 6 == sum(int(item["genus"]) for item in chars.values())
        return via_pryms

    total_positive = total_genus(chars_positive)
    total_negative = total_genus(chars_negative)

    # Load the exact generic B-lift.  We do not expand V(q,A): on the full
    # T-cover the following much smaller conic is exactly equivalent to the
    # signed-V square condition:
    #
    #   C^2 = eps*(1-B^2),  y=A/C,  y^2=eps*V.
    Q0 = sparse_to_poly(
        genus4["linear_subresultant"]["Q0_terms"], (T, A)
    )
    Q1 = sparse_to_poly(
        genus4["linear_subresultant"]["Q1_terms"], (T, A)
    )
    assert Q0.degree(T) == Q1.degree(T) == 34
    assert Q0.degree(A) == 9 and Q1.degree(A) == 8

    source_hashes = {
        "genus4_quotient": genus4["sha256_without_checksum"],
        "reciprocal_b_branch_audit": branch["sha256_without_checksum"],
    }

    payload: dict[str, object] = {
        "schema": 1,
        "status": {
            "cover_and_character_decomposition": "MACHINE-VERIFIED",
            "branch_input": "MACHINE-VERIFIED by reciprocal_b_branch_audit.py",
            "mordell_weil_ranks": "OPEN",
            "rational_points": "OPEN",
        },
        "source_hashes": source_hashes,
        "square_class_identities": {
            name: str(sp.factor(value)) for name, value in identities.items()
        },
        "base": {
            "curve": "normalization E of H(q,A)=0",
            "genus": 1,
            "q": "T^2+T^(-2)",
            "U": "2*(q+6)/(q-2)",
            "V": "a^2/b=A^2/(1-B^2)",
        },
        "full_cover": {
            "equations_over_E": [
                "r_plus^2=q+2",
                "r_minus^2=q-2",
                "y^2=epsilon*V, epsilon in {+1,-1}",
            ],
            "group_generic": "(Z/2Z)^3",
            "genus_positive": total_positive,
            "genus_negative": total_negative,
            "branch_union_degree": len(branch_union),
            "compact_open_model": [
                "G(T^2,A)=0",
                "Q1(T,A)*B+Q0(T,A)=0",
                "C^2=epsilon*(1-B^2)",
            ],
            "generic_inverse": [
                "q=T^2+T^(-2)",
                "z=(1+T)/(1-T)",
                "s=z^2",
                "b=(1+B)/(1-B)",
                "a=A/(1-B)",
                "c=a/y; then b=c^2 for epsilon=+1 and b=-c^2 for epsilon=-1",
            ],
            "inverse_from_character_roots": [
                "T=(r_plus+r_minus)/2",
                "T^(-1)=(r_plus-r_minus)/2",
                "the product is 1 because r_plus^2-r_minus^2=4",
            ],
        },
        "square_parameter_pullback_before_signed_V": {
            "equations_over_E": ["r_plus^2=q+2", "r_minus^2=q-2"],
            "group_generic": "(Z/2Z)^2",
            "genus": square_pullback_genus,
            "character_genera": {
                "q+2": 7,
                "q-2": 8,
                "q^2-4": 4,
            },
            "kani_rosen": (
                "J(C_square) x J(E)^2 ~ J(C_{q+2}) x "
                "J(C_{q-2}) x J(C_{q^2-4}); 17+2=7+8+4"
            ),
        },
        "characters_positive": chars_positive,
        "characters_negative": chars_negative,
        "prym_decomposition": {
            "isogeny": "J(Y_epsilon) x J(E)^6 ~ product_{chi != 0} J(C_chi)",
            "dimension_check": "33+6=39=sum of the seven character genera",
            "rank_consequence": "rank J(Y)=rank J(E)+sum rank Prym(C_chi/E)",
        },
        "explicit_low_genus_model": {
            "character": "(q+2)*(q-2)=q^2-4",
            "genus": 4,
            "plane_equation": "G(X,A)=0 from artifacts/genus4_quotient.json",
            "map_to_E": ["q=X+1/X", "r=X-1/X", "r^2=q^2-4"],
            "generic_inverse": "X=(q+r)/2; the other sheet is 1/X=(q-r)/2",
            "jacobian_isogeny": "J(G) ~ J(E) x Prym(G/E), with Prym dimension 3",
            "extra_automorphism_search": (
                "only X->1/X is certified; no further Prym splitting is claimed"
            ),
        },
        "exceptional_divisors": [
            "q=2 / T=+1 or -1 (z=0 or infinity; inadmissible boundary)",
            "q=-2 has no rational r_minus because r_minus^2=-4",
            "T=0 or infinity corresponds to z=+1 or -1 and s=1",
            "Q1(T,A)=0: the linear subresultant inverse is undefined and H1=H0 must be solved directly",
            "B=+1 is the b=infinity chart boundary; B=-1 gives b=0",
            "b=-1 is the omitted B=infinity chart; its positive-s branch was separately excluded except s=1",
            "A=0 or y=0: the c=a/y reconstruction degenerates; a=0 was separately excluded for admissible s",
            "all projective points and all resultant-only points still require normalization/lift checks",
        ],
        "rank_blocker": {
            "statement": (
                "Every character curve has genus at least 4 and is bielliptic. "
                "It cannot also be hyperelliptic: independent degree-two maps "
                "to E and P1 would contradict Castelnuovo-Severi for genus >=4."
            ),
            "needed_certificate": [
                "an explicit normalized model for at least one character curve",
                "a rigorous Mordell-Weil rank bound for its dimension-3-to-7 Prym",
                "generator saturation and a Chabauty/Mordell-Weil-sieve completeness certificate",
                "transport of every surviving point through the exceptional-divisor lift audit",
            ],
            "available_sympy_scope": (
                "exact polynomial identities and branch/Prym dimensions only; "
                "no certified higher-dimensional Prym Mordell-Weil rank algorithm"
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
    print("full signed-square covers: (Z/2)^3, genus 33 for both signs")
    print("positive character genera: 7,8,4,4,6,5,5")
    print("negative character genera: 7,8,6,4,4,5,5")
    print("Mordell-Weil ranks and rational points: OPEN")
    try:
        display_path = args.output.resolve().relative_to(ROOT)
    except ValueError:
        display_path = args.output.resolve()
    print("wrote", display_path)


if __name__ == "__main__":
    main()
