#!/usr/bin/env python3
"""Exact compact model for the full signed-square ``2+3`` locus.

For ``epsilon`` equal to ``+1`` or ``-1`` put

    s = z^2,  b = epsilon*z^4*k^2,  a = z^2*k*y.

After harmless powers of ``z`` are removed from the two remainder
equations, eliminating ``y`` produces a sparse plane curve
``Q_epsilon(z,k)=0``.  This script proves that the penultimate subresultant
recovers ``y`` at every admissible rational point and closes its complete
denominator-zero locus.  It also certifies two deliberately limited no-go
results: no additional toric symmetry of the sparse projection model and no
additional automorphism of the genus-four model induced by independent
Möbius changes of its two displayed coordinates.

The script uses exact arithmetic over QQ throughout.  It does not classify
the rational points of ``Q_epsilon`` and therefore does not prove C010.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")

s, a, b, z, k, y, d, v = sp.symbols("s a b z k y d v")
X, A, q = sp.symbols("X A q")


def sparse(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> list[dict[str, object]]:
    return [
        {"powers": list(powers), "coefficient": str(coefficient)}
        for powers, coefficient in sp.Poly(poly, *variables).terms()
    ]


def load_sparse(
    records: list[dict[str, object]], variables: tuple[sp.Symbol, ...]
) -> sp.Expr:
    return sp.Poly.from_dict(
        {
            tuple(int(power) for power in record["powers"]): sp.Integer(
                record["coefficient"]
            )
            for record in records
        },
        variables,
        domain=sp.ZZ,
    ).as_expr()


def remainder_equations() -> tuple[sp.Expr, sp.Expr]:
    c4 = (2 + s) * (3 - 2 * s)
    c3 = 1 + 10 * s + 4 * s**2 - 14 * s**3 + s**4
    c2 = -s * (1 - 14 * s + 4 * s**2 + 10 * s**3 + s**4)
    c1 = -s**3 * (1 + 2 * s) * (-2 + 3 * s)
    c0 = -s**5
    u = -3 * a**2 + 2 * a * c4 - c3
    quartic = a**4 - c4 * a**3 + c3 * a**2 - c2 * a + c1
    m = c4 - 2 * a
    n = a**3 - c4 * a**2 + c3 * a - c2
    return sp.expand(b**2 + u * b + quartic), sp.expand(m * b**2 + n * b + c0)


def compact_equations(epsilon: int) -> tuple[sp.Expr, sp.Expr]:
    assert epsilon in (-1, 1)
    r1, r0 = remainder_equations()
    substitution = {
        s: z**2,
        b: epsilon * z**4 * k**2,
        a: z**2 * k * y,
    }
    f1 = sp.cancel(sp.expand(r1.subs(substitution, simultaneous=True)) / z**4)
    f0 = sp.cancel(sp.expand(r0.subs(substitution, simultaneous=True)) / z**6)
    assert sp.denom(f1) == sp.denom(f0) == 1
    assert (sp.degree(f1, y), len(sp.Poly(f1, z, k, y).terms())) == (4, 27)
    assert (sp.degree(f0, y), len(sp.Poly(f0, z, k, y).terms())) == (3, 19)
    return sp.expand(f1), sp.expand(f0)


def expected_lift(epsilon: int) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    ell = (
        k**10 * z**2
        + 6 * k**6 * z**4
        - k**6 * z**2
        - 2 * k**6
        + epsilon * (2 * k**4 * z**4 + k**4 * z**2 - 6 * k**4 - z**2)
    )
    middle = (
        k**6 * (z**8 + 10 * z**6 + 4 * z**4 - 14 * z**2 + 1)
        - k**2 * (z**8 - 14 * z**6 + 4 * z**4 + 10 * z**2 + 1)
    )
    boundary = (
        2 * k**8 * z**6
        + k**8 * z**4
        - 6 * k**8 * z**2
        + 6 * z**6
        - z**4
        - 2 * z**2
    )
    l1 = -z**2 * ell
    l0 = k * (epsilon * middle - boundary)
    return sp.expand(l1), sp.expand(l0), sp.expand(ell)


def phi32() -> sp.Expr:
    return (
        z**32
        - 77 * z**30
        - 1725 * z**28
        + 125174 * z**26
        + 6766 * z**24
        - 1187796 * z**22
        + 1420733 * z**20
        + 1862827 * z**18
        - 4451294 * z**16
        + 1862827 * z**14
        + 1420733 * z**12
        - 1187796 * z**10
        + 6766 * z**8
        + 125174 * z**6
        - 1725 * z**4
        - 77 * z**2
        + 1
    )


def compact_model(epsilon: int) -> tuple[sp.Expr, dict[str, object]]:
    f1, f0 = compact_equations(epsilon)
    subresultants = sp.subresultants(f1, f0, y)
    assert [sp.degree(item, y) for item in subresultants] == [4, 3, 2, 1, 0]

    resultant = sp.expand(subresultants[-1])
    _, factors = sp.factor_list(resultant)
    candidates = [
        factor
        for factor, exponent in factors
        if exponent == 1 and (sp.degree(factor, z), sp.degree(factor, k)) == (16, 20)
    ]
    assert len(candidates) == 1
    q_model = candidates[0]
    target_coefficient = -epsilon
    current_coefficient = sp.Poly(q_model, z, k).coeff_monomial(z**8 * k**20)
    q_model = sp.expand(target_coefficient * q_model / current_coefficient)
    assert sp.expand(resultant + epsilon * z**20 * k**12 * q_model) == 0
    assert len(sp.Poly(q_model, z, k).terms()) == 71
    assert sp.Poly(q_model, z, k).is_irreducible

    linear = sp.Poly(subresultants[-2], y).primitive()[1].as_expr()
    l1, l0, ell = expected_lift(epsilon)
    assert sp.expand(linear - (l1 * y + l0)) == 0

    inverse_checks: dict[str, object] = {}
    for name, equation, degree in (("F1", f1, 4), ("F0", f0, 3)):
        cleared, denominator = sp.together(
            l1**degree * equation.subs(y, -l0 / l1)
        ).as_numer_denom()
        assert denominator == 1
        quotient, remainder = sp.div(
            sp.Poly(sp.expand(cleared), z, k), sp.Poly(q_model, z, k)
        )
        assert remainder.is_zero
        inverse_checks[name] = {
            "clearing_power": degree,
            "divisible_by_Q": True,
            "quotient_degrees": [int(quotient.degree(z)), int(quotient.degree(k))],
            "quotient_terms": len(quotient.terms()),
        }

    phi = phi32()
    expected_exception = (
        2**20
        * z**24
        * (z - 1) ** 12
        * (z + 1) ** 12
        * (z**2 - z + 1) ** 4
        * (z**2 + z + 1) ** 4
        * (z**2 + 1) ** 12
        * phi**4
    )
    exception_resultant = sp.resultant(q_model, ell, k)
    assert sp.expand(exception_resultant - expected_exception) == 0
    assert sp.Poly(phi, z).LC() == sp.Poly(phi, z).TC() == 1
    assert phi.subs(z, 1) == phi.subs(z, -1) == 512

    # The rational-root theorem is enough for Phi: it is monic with constant
    # one, and neither of its only possible rational roots +/-1 is a root.
    # The three quadratic factors have negative discriminant.
    assert [
        sp.discriminant(item, z)
        for item in (z**2 - z + 1, z**2 + z + 1, z**2 + 1)
    ] == [-3, -3, -4]

    return q_model, {
        "epsilon": epsilon,
        "substitution": {
            "s": "z^2",
            "b": f"{epsilon}*z^4*k^2",
            "a": "z^2*k*y",
        },
        "scaled_equations": {
            "F1": "R1(z^2,z^2*k*y,epsilon*z^4*k^2)/z^4",
            "F0": "R0(z^2,z^2*k*y,epsilon*z^4*k^2)/z^6",
            "F1_degrees_z_k_y": [int(sp.degree(f1, z)), int(sp.degree(f1, k)), 4],
            "F0_degrees_z_k_y": [int(sp.degree(f0, z)), int(sp.degree(f0, k)), 3],
            "F1_terms": len(sp.Poly(f1, z, k, y).terms()),
            "F0_terms": len(sp.Poly(f0, z, k, y).terms()),
        },
        "resultant_identity": "Res_y(F1,F0)=-epsilon*z^20*k^12*Q_epsilon",
        "Q_degrees_z_k": [16, 20],
        "Q_terms": sparse(q_model, (z, k)),
        "Q_irreducible_over_QQ": True,
        "linear_subresultant": {
            "formula": "L1*y+L0",
            "L1_terms": sparse(l1, (z, k)),
            "L0_terms": sparse(l0, (z, k)),
            "ell_terms": sparse(ell, (z, k)),
            "inverse": "y=-L0/L1",
        },
        "inverse_divisibility": inverse_checks,
        "exception_resultant_verified": True,
    }


def convex_hull(points: set[tuple[int, int]]) -> list[tuple[int, int]]:
    ordered = sorted(points)

    def cross(
        origin: tuple[int, int], left: tuple[int, int], right: tuple[int, int]
    ) -> int:
        return (left[0] - origin[0]) * (right[1] - origin[1]) - (
            left[1] - origin[1]
        ) * (right[0] - origin[0])

    lower: list[tuple[int, int]] = []
    for point in ordered:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], point) <= 0:
            lower.pop()
        lower.append(point)
    upper: list[tuple[int, int]] = []
    for point in reversed(ordered):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], point) <= 0:
            upper.pop()
        upper.append(point)
    return lower[:-1] + upper[:-1]


def support_symmetries(
    coefficients: dict[tuple[int, int], sp.Integer]
) -> list[dict[str, object]]:
    support = set(coefficients)
    vertices = convex_hull(support)
    count = len(vertices)
    p0 = sp.Matrix(vertices[0])
    source = sp.Matrix.hstack(sp.Matrix(vertices[1]) - p0, sp.Matrix(vertices[2]) - p0)
    assert source.det() != 0
    candidates: list[dict[str, object]] = []
    seen: set[tuple[int, ...]] = set()
    for reverse in (False, True):
        for shift in range(count):
            targets = [
                vertices[(shift + (-index if reverse else index)) % count]
                for index in range(count)
            ]
            w0 = sp.Matrix(targets[0])
            target = sp.Matrix.hstack(
                sp.Matrix(targets[1]) - w0, sp.Matrix(targets[2]) - w0
            )
            matrix = target * source.inv()
            translation = w0 - matrix * p0
            if any(value.q != 1 for value in list(matrix) + list(translation)):
                continue
            m = tuple(int(matrix[row, column]) for row in range(2) for column in range(2))
            shift_vector = (int(translation[0]), int(translation[1]))
            signature = (*m, *shift_vector)
            if signature in seen:
                continue

            def transform(point: tuple[int, int]) -> tuple[int, int]:
                return (
                    m[0] * point[0] + m[1] * point[1] + shift_vector[0],
                    m[2] * point[0] + m[3] * point[1] + shift_vector[1],
                )

            if {transform(point) for point in support} != support:
                continue
            seen.add(signature)
            ratios = {
                point: sp.Rational(coefficients[transform(point)], coefficients[point])
                for point in support
            }
            coefficient_preserving = len(set(ratios.values())) == 1
            candidates.append(
                {
                    "matrix": [[m[0], m[1]], [m[2], m[3]]],
                    "translation": list(shift_vector),
                    "coefficient_preserving_without_scaling": coefficient_preserving,
                    "ratios": ratios,
                }
            )
    return candidates


def toric_no_go() -> dict[str, object]:
    r1, r0 = remainder_equations()
    projection = sp.resultant(r1, r0, a)
    records: dict[str, object] = {}
    expected_vertices = [
        (0, 9),
        (2, 7),
        (10, 3),
        (16, 1),
        (20, 0),
        (20, 1),
        (18, 3),
        (10, 7),
        (4, 9),
        (0, 10),
    ]
    for epsilon in (1, -1):
        projection_eps = sp.Poly(projection.subs(b, epsilon * d), s, d).primitive()[1]
        assert projection_eps.is_irreducible
        coefficients = {powers: sp.Integer(value) for powers, value in projection_eps.terms()}
        vertices = convex_hull(set(coefficients))
        assert vertices == expected_vertices
        # These three support points have difference determinant one.  Thus
        # the affine exponent lattice is saturated; a coefficient-preserving
        # exponent symmetry cannot acquire extra root-of-unity torus scalings.
        lattice_basis_points = ((20, 1), (20, 0), (19, 2))
        assert all(point in coefficients for point in lattice_basis_points)
        assert sp.det(
            sp.Matrix(
                [
                    [0, -1],
                    [-1, 1],
                ]
            )
        ) == -1

        # If a primitive direction (alpha,beta) had width < 8, the vertical
        # unit edges force |beta|<8, while the vertices (20,0),(0,10) force
        # |20*alpha-10*beta|<8.  Hence beta=2*alpha; primitivity then gives
        # +/- (1,2), whose width is exactly 8.
        values = [first + 2 * second for first, second in vertices]
        assert max(values) - min(values) == 8

        symmetries = support_symmetries(coefficients)
        assert len(symmetries) == 4
        valid = [item for item in symmetries if item["coefficient_preserving_without_scaling"]]
        assert {
            (
                tuple(tuple(row) for row in item["matrix"]),
                tuple(item["translation"]),
            )
            for item in valid
        } == {
            (((1, 0), (0, 1)), (0, 0)),
            (((-1, 0), (0, -1)), (20, 10)),
        }

        # The two remaining polygon symmetries cannot be repaired by torus
        # scalings.  For a scaled monomial symmetry the coefficient ratios
        # must be exponential-affine in the exponent, hence multiplicative
        # on every exponent parallelogram.  This explicit parallelogram fails.
        failed_witnesses: list[str] = []
        p, t, qpoint, rpoint = (12, 4), (2, 8), (4, 9), (10, 3)
        assert (p[0] + t[0], p[1] + t[1]) == (
            qpoint[0] + rpoint[0],
            qpoint[1] + rpoint[1],
        )
        for item in symmetries:
            if item["coefficient_preserving_without_scaling"]:
                continue
            ratios = item["ratios"]
            difference = sp.factor(
                ratios[p] * ratios[t] - ratios[qpoint] * ratios[rpoint]
            )
            assert difference == -sp.Rational(64, 85)
            failed_witnesses.append(str(difference))

        sheared = sp.cancel(projection_eps.as_expr().subs(d, s**2 * v) / s**16)
        assert sp.denom(sheared) == 1
        assert (sp.degree(sheared, s), sp.degree(sheared, v)) == (8, 10)
        assert len(sp.Poly(sheared, s, v).terms()) == 71
        assert sp.Poly(sheared, s, v).is_irreducible
        assert sp.expand(
            sheared - s**8 * v**10 * sheared.subs({s: 1 / s, v: 1 / v}, simultaneous=True)
        ) == 0
        records[str(epsilon)] = {
            "newton_vertices": [list(item) for item in vertices],
            "lattice_width": 8,
            "minimum_direction": [1, 2],
            "minimum_width_model": "d=s^2*v gives bidegree (8,10)",
            "support_symmetries": 4,
            "affine_exponent_lattice_saturated": True,
            "coefficient_compatible_toric_symmetries": [
                "identity", "(s,d)->(1/s,1/d) after monomial clearing"
            ],
            "scaled_symmetry_failure_witnesses": failed_witnesses,
        }
    return {
        "scope": (
            "Complete only for Laurent-monomial coordinate changes preserving "
            "the Newton support; it does not determine the abstract automorphism group."
        ),
        "signs": records,
    }


def genus4_mobius_no_go() -> dict[str, object]:
    genus4 = json.loads((ROOT / "artifacts" / "genus4_quotient.json").read_text())
    g_model = load_sparse(genus4["genus4_model"]["terms"], (X, A))
    h_model = load_sparse(genus4["elliptic_plane_model"]["terms"], (q, A))
    assert sp.expand(g_model - X**8 * h_model.subs(q, X + 1 / X)) == 0
    assert (sp.degree(g_model, X), sp.degree(g_model, A)) == (16, 10)

    cubic = 43 * q**3 + 11870 * q**2 - 50684 * q + 51496
    degree_15 = (
        q**15
        + 998 * q**14
        + 328436 * q**13
        + 33879288 * q**12
        - 630955568 * q**11
        - 64836634912 * q**10
        - 1365887807936 * q**9
        - 13883961380480 * q**8
        - 77464295435520 * q**7
        - 230515638316544 * q**6
        - 255656791073792 * q**5
        + 398271926396928 * q**4
        + 1443280969068544 * q**3
        + 1224232979505152 * q**2
        - 174483284901888 * q
        - 495592577400832
    )
    discriminant_factors = [
        (3 * q + 10, 4),
        (q + 2, 20),
        (q - 2, 27),
        (5 * q**2 + 28 * q + 52, 12),
        (cubic, 3),
        (degree_15, 2),
    ]
    expected = sp.prod(factor**exponent for factor, exponent in discriminant_factors)
    discriminant = sp.discriminant(h_model, A)
    constant = sp.cancel(discriminant / expected)
    assert constant.is_Integer and constant != 0
    for index, (left, _) in enumerate(discriminant_factors):
        for right, _ in discriminant_factors[index + 1 :]:
            assert sp.gcd(sp.Poly(left, q), sp.Poly(right, q)).degree() == 0

    q_discriminant_degree = sum(
        sp.degree(factor, q) * exponent for factor, exponent in discriminant_factors
    )
    assert q_discriminant_degree == 114
    # Disc_A(c*f)=c^(2n-2) Disc_A(f), n=10.  The affine X=0 order is
    # 8*(2n-2)-114=30; the binary section has degree 16*(2n-2)=288,
    # so infinity has the same order 30.  The ramified q-fibres +/-2 double
    # their respective exponents.
    multiplicity_strata = {"X=1": 54, "X=-1": 40, "X=0": 30, "X=infinity": 30}
    assert 8 * 18 - q_discriminant_degree == 30
    assert 16 * 18 - (30 + 2 * q_discriminant_degree) == 30
    assert len(set(multiplicity_strata.values())) == 3
    assert all(exponent not in (30, 40, 54) for _, exponent in discriminant_factors[::])

    fibre_minus = sp.factor(g_model.subs(X, -1))
    fibre_plus = sp.factor(g_model.subs(X, 1))
    assert fibre_minus == 2**16 * (A - 2) ** 10
    assert fibre_plus == 2**27 * A**3 * (A - 6) * (A**2 - 12 * A + 4) ** 3

    return {
        "scope": (
            "Automorphisms induced by independent PGL2(Q) changes of X and A only; "
            "nonlinear or non-ambient automorphisms are not excluded."
        ),
        "binary_discriminant_degree": 288,
        "unique_multiplicity_strata": multiplicity_strata,
        "X_transformations_remaining": ["X", "1/X"],
        "special_fibres": {
            "X=-1": str(fibre_minus),
            "X=1": str(fibre_plus),
        },
        "A_transformation_argument": (
            "The X=-1 fibre fixes A=2.  In the X=1 fibre, A=6 is the unique "
            "multiplicity-one root and A=0 is the only rational multiplicity-three "
            "root.  A rational Mobius map fixing 0,2,6 is the identity."
        ),
        "ambient_mobius_automorphisms": ["identity", "(X,A)->(1/X,A)"],
    }


def verify() -> dict[str, object]:
    models: dict[str, object] = {}
    q_models: dict[int, sp.Expr] = {}
    for epsilon, label in ((1, "positive"), (-1, "negative")):
        q_model, record = compact_model(epsilon)
        q_models[epsilon] = q_model
        models[label] = record
    assert sp.expand(q_models[-1] + q_models[1].subs(k, sp.I * k)) == 0

    phi = phi32()
    payload: dict[str, object] = {
        "schema": 1,
        "status": {
            "compact_model_and_reverse_lift": "MACHINE-VERIFIED",
            "rational_points": "OPEN",
            "C010": "OPEN",
        },
        "theorem": (
            "For epsilon=+/-1, admissible rational signed-square factors are "
            "equivalent to finite rational points Q_epsilon(z,k)=0 with "
            "z>0, z!=1, k!=0; the inverse is y=-L0/L1 and then "
            "s=z^2, b=epsilon*z^4*k^2, a=z^2*k*y."
        ),
        "models": models,
        "twist_identity": "Q_-(z,k)=-Q_+(z,i*k)",
        "exception": {
            "resultant": (
                "2^20*z^24*(z-1)^12*(z+1)^12*(z^2-z+1)^4*"
                "(z^2+z+1)^4*(z^2+1)^12*Phi32(z)^4"
            ),
            "Phi32_terms": sparse(phi, (z,)),
            "Phi32_at_plus_minus_1": 512,
            "rational_exception_values": ["-1", "0", "1"],
            "admissible_exception_values": [],
            "proof": (
                "The three quadratics have negative discriminant. Phi32 is monic "
                "with constant 1, so its only possible rational roots are +/-1; "
                "both values give 512."
            ),
        },
        "admissibility": {
            "required": ["z is rational and positive", "z!=1", "k is rational and nonzero"],
            "boundary": {
                "z=0": "s=0",
                "z=+/-1": "s=1",
                "k=0": "b=0",
            },
            "projective_note": (
                "Positive finite p/q gives finite nonzero z and k. Projective "
                "points of the plane closure are not asserted to be factor points."
            ),
        },
        "toric_no_go": toric_no_go(),
        "genus4_mobius_no_go": genus4_mobius_no_go(),
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = verify()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("compact signed-square models: bidegree (16,20), 71 terms")
    print("linear reverse lift and all rational denominator exceptions: OK")
    print("toric and ambient-Mobius no-go certificates: OK")
    if args.output:
        print("wrote", args.output)


if __name__ == "__main__":
    main()
