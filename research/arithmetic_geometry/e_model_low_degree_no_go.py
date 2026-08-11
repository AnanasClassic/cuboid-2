#!/usr/bin/env python3
"""Low-complexity exact obstructions to shortcuts for normalizing ``H``.

This certificate deliberately does not normalize the singular plane curve.
It checks four narrower statements which are useful when searching for an
explicit elliptic transport:

* ``C=A-c, r=(q-q0)C`` has a common exceptional factor only for the rational
  shift ``c=2``; after removing it the degree is still twelve for every
  rational ``q0``;
* the rational singularities of that degree-twelve model do not give a
  degree-two or degree-three line pencil;
* the unique rational, unramified point in the fibre ``q=6`` prevents ``q``
  from factoring through a degree-two map defined over ``QQ``;
* the already audited local inertia data give the exact degree-ten passport
  of the normalized ``q``-map.

All polynomial calculations are over ``ZZ`` or ``QQ``.  The passport step is
a deduction from the local normalization inputs already proved in
``src/geometry_audit.py``; it is not a replacement normalization algorithm.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
INPUT = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def _load_H() -> tuple[sp.Symbol, sp.Symbol, sp.Poly, str]:
    data = json.loads(INPUT.read_text(encoding="utf-8"))
    q, A = sp.symbols("q A")
    H = sp.Poly.from_dict(
        {
            tuple(term["powers"]): sp.Integer(term["coefficient"])
            for term in data["elliptic_plane_model"]["terms"]
        },
        (q, A),
        domain=sp.ZZ,
    )
    return q, A, H, data["sha256_without_checksum"]


def _tangent_cone(
    polynomial: sp.Poly,
    first: sp.Symbol,
    second: sp.Symbol,
    point: tuple[sp.Rational, sp.Rational],
    local_first: sp.Symbol,
    local_second: sp.Symbol,
) -> tuple[int, sp.Expr]:
    translated = sp.Poly(
        sp.expand(
            polynomial.as_expr().subs(
                {
                    first: point[0] + local_first,
                    second: point[1] + local_second,
                }
            )
        ),
        local_first,
        local_second,
        domain=sp.QQ,
    )
    multiplicity = min(sum(monomial) for monomial, _ in translated.terms())
    cone = sum(
        coefficient
        * local_first ** monomial[0]
        * local_second ** monomial[1]
        for monomial, coefficient in translated.terms()
        if sum(monomial) == multiplicity
    )
    return multiplicity, sp.factor(cone)


def _induced_partition(root_permutation: tuple[int, ...]) -> list[int]:
    two_subsets = list(combinations(range(5), 2))
    index = {subset: position for position, subset in enumerate(two_subsets)}
    induced = []
    for subset in two_subsets:
        image = tuple(sorted(root_permutation[root] for root in subset))
        induced.append(index[image])
    unseen = set(range(len(two_subsets)))
    lengths: list[int] = []
    while unseen:
        start = next(iter(unseen))
        current = start
        length = 0
        while current in unseen:
            unseen.remove(current)
            current = induced[current]
            length += 1
        lengths.append(length)
    return sorted(lengths, reverse=True)


def _sparse_digest(polynomial: sp.Poly) -> str:
    terms = [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in polynomial.terms()
    ]
    encoded = json.dumps(terms, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def verify() -> dict[str, object]:
    q, A, H, artifact_checksum = _load_H()
    C, r, q0 = sp.symbols("C r q0")
    assert H.degree_list() == (8, 10)

    # The coefficient of q^8 first makes the rational shift c=2 unique.
    leading_q = sp.Poly(H.as_expr(), q).LC()
    quartic = sp.Poly(
        sp.exquo(leading_q, (A - 2) ** 6), A, domain=sp.ZZ
    )
    expected_quartic = sp.Poly(
        361 * A**4
        - 5272 * A**3
        + 16504 * A**2
        - 19168 * A
        + 7696,
        A,
        domain=sp.ZZ,
    )
    assert quartic == expected_quartic
    assert quartic.is_irreducible
    quartic_discriminant = sp.discriminant(quartic.as_expr(), A)
    assert quartic_discriminant == -45088768000000000000

    # Build C^8 H(q0+r/C,C+2) term by term, without introducing a rational
    # expression.  Keeping q0 indeterminate proves the assertion uniformly.
    shifted_expression = sp.Integer(0)
    for (q_degree, a_degree), coefficient in H.terms():
        shifted_expression += (
            coefficient
            * (q0 * C + r) ** q_degree
            * C ** (8 - q_degree)
            * (C + 2) ** a_degree
        )
    shifted = sp.Poly(
        sp.expand(shifted_expression), C, r, q0, domain=sp.ZZ
    )
    minimum_c_order = min(powers[0] for powers, _ in shifted.terms())
    assert minimum_c_order == 6
    reduced = shifted.exquo(sp.Poly(C**6, C, r, q0, domain=sp.ZZ))
    reduced_in_r_c = sp.Poly(
        reduced.as_expr(), r, C, domain=sp.ZZ.poly_ring(q0)
    )
    assert max(sum(powers) for powers, _ in reduced_in_r_c.terms()) == 12
    # This coefficient is independent of q0, so specialization cannot lower
    # the total degree.
    assert reduced_in_r_c.coeff_monomial(r**8 * C**4) == 361

    J = sp.Poly(reduced.as_expr().subs(q0, 0), r, C, domain=sp.ZZ).primitive()[1]
    J_shifted = sp.Poly(
        reduced.as_expr().subs(q0, -2), r, C, domain=sp.ZZ
    ).primitive()[1]
    assert (J.degree(r), J.degree(C), J.total_degree(), len(J.terms())) == (
        8,
        12,
        12,
        78,
    )
    assert (
        J_shifted.degree(r),
        J_shifted.degree(C),
        J_shifted.total_degree(),
        len(J_shifted.terms()),
    ) == (8, 12, 12, 63)
    assert J.is_irreducible

    # Any affine singularity must occur at an r-root common to these three
    # resultants.  Factoring their gcd leaves only r=0,-4 as rational roots.
    derivative_r = J.diff(r)
    derivative_C = J.diff(C)
    resultant_polynomials = [
        sp.Poly(sp.resultant(first.as_expr(), second.as_expr(), C), r)
        for first, second in (
            (J, derivative_r),
            (J, derivative_C),
            (derivative_r, derivative_C),
        )
    ]
    common_r = sp.gcd(
        sp.gcd(resultant_polynomials[0], resultant_polynomials[1]),
        resultant_polynomials[2],
    ).primitive()[1]
    _, common_factors = sp.factor_list(common_r.as_expr(), r)
    factor_records = []
    rational_r_values: set[sp.Rational] = set()
    for factor_expression, exponent in common_factors:
        factor = sp.Poly(factor_expression, r, domain=sp.ZZ).primitive()[1]
        assert factor.is_irreducible
        if factor.degree() == 1:
            rational_r_values.add(-sp.Rational(factor.nth(0), factor.nth(1)))
        factor_records.append(
            {
                "polynomial": str(factor.as_expr()),
                "degree": int(factor.degree()),
                "exponent": int(exponent),
            }
        )
    assert sorted((item["degree"], item["exponent"]) for item in factor_records) == [
        (1, 7),
        (1, 13),
        (2, 1),
        (2, 7),
        (2, 9),
        (15, 1),
    ]
    assert rational_r_values == {sp.Rational(-4), sp.Rational(0)}

    affine_singularities = []
    local_u, local_v = sp.symbols("u v")
    expected_affine = {
        sp.Rational(0): {
            "C": sp.Rational(0),
            "gcd": C,
            "multiplicity": 2,
            "tangent": 2**40 * (local_u + 2 * local_v) ** 2,
        },
        sp.Rational(-4): {
            "C": sp.Rational(-2),
            "gcd": (C + 2) ** 2,
            "multiplicity": 3,
            "tangent": -805306368 * local_v * (local_u - 18 * local_v) ** 2,
        },
    }
    for r_value in sorted(rational_r_values):
        gcd_in_C = sp.gcd(
            sp.gcd(
                sp.Poly(J.as_expr().subs(r, r_value), C),
                sp.Poly(derivative_r.as_expr().subs(r, r_value), C),
            ),
            sp.Poly(derivative_C.as_expr().subs(r, r_value), C),
        ).primitive()[1]
        expected = expected_affine[r_value]
        assert sp.Poly(gcd_in_C, C).monic() == sp.Poly(
            expected["gcd"], C
        ).monic()
        multiplicity, tangent = _tangent_cone(
            J,
            r,
            C,
            (r_value, expected["C"]),
            local_u,
            local_v,
        )
        assert multiplicity == expected["multiplicity"]
        assert sp.expand(tangent - expected["tangent"]) == 0
        affine_singularities.append(
            {
                "r": str(r_value),
                "C": str(expected["C"]),
                "multiplicity": multiplicity,
                "tangent_cone": str(tangent),
                "line_pencil_degree": 12 - multiplicity,
            }
        )

    # Rational projective boundary of the ordinary total-degree closure.
    Z = sp.symbols("Z")
    homogeneous_J = J.homogenize(Z)
    top_form = sp.Poly(homogeneous_J.as_expr().subs(Z, 0), r, C)
    infinity_octic = top_form.exquo(sp.Poly(C**4, r, C)).primitive()[1]
    _, infinity_factors = sp.factor_list(infinity_octic.as_expr(), r, C)
    assert len(infinity_factors) == 1
    assert sp.Poly(infinity_factors[0][0], r, C).total_degree() == 8
    assert infinity_factors[0][1] == 1
    c, z = sp.symbols("c z")
    infinity_chart = sp.Poly(
        homogeneous_J.as_expr().subs({r: 1, C: c, Z: z}), c, z
    )
    infinity_multiplicity, infinity_tangent = _tangent_cone(
        infinity_chart, c, z, (sp.Rational(0), sp.Rational(0)), c, z
    )
    expected_infinity_tangent = (
        361 * c**4
        - 2384 * c**3 * z
        - 6464 * c**2 * z**2
        - 4864 * c * z**3
        - 1024 * z**4
    )
    assert infinity_multiplicity == 4
    assert sp.expand(infinity_tangent - expected_infinity_tangent) == 0
    _, tangent_factors = sp.factor_list(infinity_tangent, c, z)
    assert len(tangent_factors) == 1
    assert sp.Poly(tangent_factors[0][0], c, z).total_degree() == 4
    assert tangent_factors[0][1] == 1

    # Classify the C=0 failure of the inverse q=r/C.  Six q=infinity points
    # are roots of this irreducible sextic; the other four have the preceding
    # irreducible tangent quartic.  The r=C=0 branches are over QQ(sqrt(5)).
    boundary_sextic = sp.Poly(
        sp.cancel(-J.as_expr().subs(C, 0) / (1024 * r**2)), r
    )
    expected_boundary_sextic = sp.Poly(
        r**6
        - 128 * r**5
        + 1024 * r**4
        + 327680 * r**3
        - 1048576 * r**2
        - 134217728 * r
        - 1073741824,
        r,
    )
    assert boundary_sextic == expected_boundary_sextic
    assert boundary_sextic.is_irreducible
    y, edge_parameter = sp.symbols("y edge_parameter")
    repeated_edge = sp.Poly(
        sp.expand(
            H.as_expr().subs(
                {
                    q: -2 + C**5 * edge_parameter,
                    A: 2 + C,
                }
            )
        ),
        C,
        edge_parameter,
    )
    repeated_edge_order = min(powers[0] for powers, _ in repeated_edge.terms())
    repeated_edge_coefficient = sp.Poly(
        sum(
            coefficient * edge_parameter ** powers[1]
            for powers, coefficient in repeated_edge.terms()
            if powers[0] == repeated_edge_order
        ),
        edge_parameter,
    )
    assert repeated_edge_order == 10
    assert repeated_edge_coefficient == sp.Poly(
        65536 * (4096 * edge_parameter + 1) ** 2, edge_parameter
    )
    local_minus_two = sp.Poly(
        sp.expand(
            H.as_expr().subs(
                {
                    q: -2 + C**5 * (-sp.Rational(1, 4096) + C * y),
                    A: 2 + C,
                }
            )
        ),
        C,
        y,
    )
    first_order = min(powers[0] for powers, _ in local_minus_two.terms())
    first_coefficient = sp.Poly(
        sum(
            coefficient * y ** powers[1]
            for powers, coefficient in local_minus_two.terms()
            if powers[0] == first_order
        ),
        y,
    )
    expected_local_coefficient = sp.Poly(
        4096 * (2**28 * y**2 - 147456 * y + 19), y
    )
    assert first_order == 12
    assert first_coefficient == expected_local_coefficient
    inner_discriminant = sp.discriminant(
        2**28 * y**2 - 147456 * y + 19, y
    )
    assert inner_discriminant == 5 * 2**28

    # The fibre q=6 gives a purely geometric obstruction to any q-preserving
    # degree-two quotient, independently of the candidate 544.c models.
    cubic_factor = 7 * A**3 - 114 * A**2 + 500 * A - 88
    sextic_factor = (
        4769 * A**6
        - 79372 * A**5
        + 331260 * A**4
        - 458400 * A**3
        + 230640 * A**2
        - 30912 * A
        + 3136
    )
    expected_q6 = 65536 * (7 * A - 6) * cubic_factor * sextic_factor
    q6 = sp.Poly(H.as_expr().subs(q, 6), A)
    assert sp.expand(q6.as_expr() - expected_q6) == 0
    assert sp.Poly(cubic_factor, A).is_irreducible
    assert sp.Poly(sextic_factor, A).is_irreducible
    derivative_at_point = sp.diff(H.as_expr(), A).subs(
        {q: 6, A: sp.Rational(6, 7)}
    )
    assert derivative_at_point == sp.Rational(137438953472000000, 823543)

    # Exact branch-value conversion and permutation combinatorics.  The local
    # inertia generators (5-cycle at s=-1; transpositions at s=0/infinity and
    # at H6=0; fixed-point quotient at s=1) are the inputs audited by
    # src/geometry_audit.py and research/frobenius_audit/README.md.
    s, U = sp.symbols("s U")
    h6 = (
        s**6
        + 15 * s**5
        - 1585 * s**4
        + 3052 * s**3
        - 1585 * s**2
        + 15 * s
        + 1
    )
    reciprocal_cubic = U**3 + 15 * U**2 - 1588 * U + 3022
    assert sp.cancel(h6 - s**3 * reciprocal_cubic.subs(U, s + 1 / s)) == 0
    collision_cubic = 43 * q**3 + 11870 * q**2 - 50684 * q + 51496
    assert sp.cancel(
        (q - 2) ** 3
        * reciprocal_cubic.subs(U, 2 * (q + 6) / (q - 2))
        + 2 * collision_cubic
    ) == 0
    assert sp.Poly(collision_cubic, q).is_irreducible
    assert sp.discriminant(collision_cubic, q) != 0
    five_cycle_partition = _induced_partition((1, 2, 3, 4, 0))
    transposition_partition = _induced_partition((1, 0, 2, 3, 4))
    identity_partition = _induced_partition((0, 1, 2, 3, 4))
    assert five_cycle_partition == [5, 5]
    assert transposition_partition == [2, 2, 2, 1, 1, 1, 1]
    assert identity_partition == [1] * 10
    ramification_sum = (
        sum(length - 1 for length in five_cycle_partition)
        + 4 * sum(length - 1 for length in transposition_partition)
    )
    assert ramification_sum == 20
    genus = 1 + (-2 * 10 + ramification_sum) // 2
    assert genus == 1

    payload: dict[str, object] = {
        "schema": 1,
        "status": "MACHINE-VERIFIED",
        "artifact_checksum": artifact_checksum,
        "shift_family": {
            "leading_q_coefficient": str(sp.factor(leading_q)),
            "residual_quartic_irreducible": True,
            "residual_quartic_discriminant": str(quartic_discriminant),
            "only_rational_shift_with_common_C_factor": "c=2",
            "common_factor_for_symbolic_q0": "C^6",
            "primitive_degrees_for_every_rational_q0": {
                "r": 8,
                "C": 12,
                "total": 12,
            },
            "noncancelling_degree_twelve_coefficient": "coeff(r^8*C^4)=361",
            "q0=0_terms": len(J.terms()),
            "q0=-2_terms": len(J_shifted.terms()),
            "J_sha256_sparse": _sparse_digest(J),
        },
        "rational_singularities": {
            "resultant_gcd_factors": factor_records,
            "affine": affine_singularities,
            "projective_infinity": {
                "point": "[r:C:Z]=[1:0:0]",
                "multiplicity": infinity_multiplicity,
                "tangent_cone": str(infinity_tangent),
                "tangent_cone_irreducible": True,
                "line_pencil_degree": 12 - infinity_multiplicity,
            },
            "conclusion": (
                "Every line pencil based at a rational singular point has "
                "degree at least 8; it does not produce a degree-2 or degree-3 map."
            ),
        },
        "C_equals_zero_boundary": {
            "irreducible_q_infinity_sextic": str(boundary_sextic.as_expr()),
            "remaining_q_infinity_tangent_quartic": str(infinity_tangent),
            "q=-2_repeated_edge": str(repeated_edge_coefficient.as_expr()),
            "q=-2_first_simple_edge_after_repeated_edge": str(
                first_coefficient.as_expr()
            ),
            "q=-2_inner_discriminant": str(inner_discriminant),
            "conclusion": (
                "The C=0 and projective boundary supports no rational "
                "normalization point: the two q=-2 branches require sqrt(5), "
                "and the ten q=infinity branches lie in irreducible degree-6 "
                "and degree-4 orbits."
            ),
        },
        "degree_two_q_map_obstruction": {
            "q=6_factorization": str(sp.factor(q6.as_expr())),
            "irreducible_factor_degrees": [1, 3, 6],
            "unique_rational_point": "(q,A)=(6,6/7)",
            "H_A_at_point": str(derivative_at_point),
            "proof": (
                "A QQ-defined degree-2 map has a QQ-defined deck involution. "
                "The unique rational point P in the q=6 fibre is unramified, "
                "so the involution would send P to a distinct rational point "
                "with the same q-value, contradicting uniqueness."
            ),
            "conclusion": (
                "q does not factor through any QQ-defined degree-2 genus-zero quotient."
            ),
        },
        "q_map_passport": {
            "degree": 10,
            "q=-2": "5^2",
            "q=2": "2^3 1^4",
            "q=infinity": "1^10",
            "collision_branch_polynomial": str(collision_cubic),
            "at_each_collision_root": "2^3 1^4",
            "ramification_sum": ramification_sum,
            "riemann_hurwitz_genus": genus,
            "local_input_scope": (
                "Uses the exact local inertia forms already audited in "
                "src/geometry_audit.py; this script independently checks the "
                "reciprocal branch-value conversion and induced two-subset cycles."
            ),
        },
        "logical_scope": {
            "proved": (
                "These statements rule out the proposed shifted-monomial degree "
                "drop, rational-singularity line pencils, and every q-preserving "
                "degree-two elliptic-coordinate shortcut."
            ),
            "not_proved": (
                "No normalization of H, birational map to E1/E2, degree-three "
                "map, or rational-point classification is supplied."
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
    print("unique shifted-monomial common factor C^6; total degree 12: OK")
    print("rational singularity and boundary audit: OK")
    print("degree-two q-map obstruction at q=6: OK")
    print("degree-ten q-map passport: OK")
    try:
        displayed_output = args.output.relative_to(ROOT)
    except ValueError:
        displayed_output = args.output
    print("wrote", displayed_output)


if __name__ == "__main__":
    main()
