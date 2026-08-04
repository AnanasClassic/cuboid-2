#!/usr/bin/env python3
"""Exact SageMath probe for the reciprocal genus-one quotient.

This script deliberately reconstructs the curve from the committed sparse
artifact.  It uses the function field (hence the normalization, rather than
the singular plane model), constructs a rational place, and obtains a plane
cubic from Riemann--Roch spaces L(2P) and L(3P).

Run with::

    sage -python scripts/sage_elliptic_probe.py
"""

from __future__ import annotations

import json
import platform
import time
from pathlib import Path

from sage.all import (  # type: ignore
    FunctionField,
    Matrix,
    PolynomialRing,
    QQ,
    ZZ,
    EllipticCurve_from_cubic,
    lcm,
    version,
)


ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "artifacts" / "genus4_quotient.json"


def announce(label: str, value) -> None:
    print(f"CERT {label} = {value}", flush=True)


def constant_relation_matrix(field, elements):
    """Matrix over QQ whose right kernel is the constant relations."""

    degree = field.degree()
    coordinates = []
    denominators = []
    for element in elements:
        coeffs = list(element)
        coeffs += [field.base_field()(0)] * (degree - len(coeffs))
        coordinates.append(coeffs)
        denominators.extend(c.denominator() for c in coeffs)

    common_denominator = lcm(denominators)
    numerators = []
    max_degree = 0
    for coeffs in coordinates:
        row = []
        for coeff in coeffs:
            cleared = coeff * common_denominator
            numerator = cleared.numerator()
            denominator = cleared.denominator()
            numerator = numerator / denominator[0]
            row.append(numerator)
            if numerator:
                max_degree = max(max_degree, numerator.degree())
        numerators.append(row)

    rows = []
    for coordinate in range(degree):
        for power in range(max_degree + 1):
            rows.append(
                [QQ(numerators[column][coordinate][power]) for column in range(len(elements))]
            )
    return Matrix(QQ, rows)


def independent_over_constants(field, elements) -> bool:
    matrix = constant_relation_matrix(field, elements)
    return matrix.rank() == len(elements)


def main() -> None:
    start = time.monotonic()
    announce("sage_version", version())
    announce("python_version", platform.python_version())
    announce("artifact", ARTIFACT.relative_to(ROOT))

    data = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    K = FunctionField(QQ, "q")
    q = K.gen()
    R = PolynomialRing(K, "A")
    A = R.gen()
    H = R(0)
    for term in data["elliptic_plane_model"]["terms"]:
        q_power, a_power = term["powers"]
        H += ZZ(term["coefficient"]) * q**q_power * A**a_power

    announce("H_degree_A", H.degree())
    announce("H_terms", len(data["elliptic_plane_model"]["terms"]))
    point_value = sum(
        ZZ(term["coefficient"])
        * QQ(6) ** term["powers"][0]
        * (QQ(6) / 7) ** term["powers"][1]
        for term in data["elliptic_plane_model"]["terms"]
    )
    announce("H_point_6_6over7", point_value)
    if point_value != 0:
        raise AssertionError("the chosen rational base point is not on H")

    L = K.extension(H, "alpha")
    alpha = L.gen()
    announce("function_field_degree", L.degree())
    announce("normalization_genus", L.genus())
    if L.genus() != 1:
        raise AssertionError("the reciprocal quotient normalization must have genus 1")

    order = L.maximal_order()
    ideal = order.ideal(q - 6, alpha - QQ(6) / 7)
    place = ideal.place()
    announce("base_place_degree", place.degree())
    divisor = place.divisor()

    basis_2 = (2 * divisor).basis_function_space()
    basis_3 = (3 * divisor).basis_function_space()
    announce("dim_L2P", len(basis_2))
    announce("dim_L3P", len(basis_3))
    announce("basis_L2P", basis_2)
    announce("basis_L3P", basis_3)
    if len(basis_2) != 2 or len(basis_3) != 3:
        raise AssertionError("unexpected genus-one Riemann--Roch dimensions")

    one = L(1)
    x_candidates = [f for f in basis_2 if f != one]
    if not x_candidates:
        raise AssertionError("L(2P) did not expose a nonconstant function")
    x = x_candidates[0]
    y_candidates = [f for f in basis_3 if independent_over_constants(L, [one, x, f])]
    if not y_candidates:
        raise AssertionError("L(3P) did not expose a third independent function")
    y = y_candidates[0]
    announce("rr_x", x)
    announce("rr_y", y)

    monomials = [one, x, y, x**2, x * y, x**3, y**2]
    relation_matrix = constant_relation_matrix(L, monomials)
    kernel = relation_matrix.right_kernel()
    announce("cubic_relation_kernel_dimension", kernel.dimension())
    if kernel.dimension() != 1:
        raise AssertionError("expected a unique cubic relation")
    relation = list(kernel.basis()[0])
    if sum((relation[i] * monomials[i] for i in range(7)), L(0)) != 0:
        raise AssertionError("exported cubic relation does not vanish in the function field")
    announce("cubic_relation_coefficients", relation)

    S = PolynomialRing(QQ, names=("X", "Y", "Z"))
    X, Y, Z = S.gens()
    c0, c1, c2, c3, c4, c5, c6 = relation
    cubic = c0 * Z**3 + c1 * X * Z**2 + c2 * Y * Z**2 + c3 * X**2 * Z
    cubic += c4 * X * Y * Z + c5 * X**3 + c6 * Y**2 * Z
    announce("plane_cubic", cubic)
    if cubic(X=0, Y=1, Z=0) != 0:
        raise AssertionError("expected rational point at infinity is absent")

    morphism = EllipticCurve_from_cubic(cubic, [0, 1, 0], morphism=True)
    curve = morphism.codomain()
    minimal = curve.global_minimal_model()
    announce("weierstrass_model", curve)
    announce("minimal_model", minimal)
    announce("minimal_ainvs", minimal.a_invariants())
    announce("minimal_discriminant", minimal.discriminant())
    announce("minimal_conductor", minimal.conductor())
    announce("torsion_subgroup", minimal.torsion_subgroup())
    try:
        announce("rank_bounds", minimal.rank_bounds())
    except (AttributeError, RuntimeError, ValueError) as error:
        announce("rank_bounds_unavailable", repr(error))
    try:
        announce("rank_exact", minimal.rank(proof=True))
    except (RuntimeError, ValueError) as error:
        announce("rank_exact_unavailable", repr(error))
    try:
        announce("generators", minimal.gens(proof=True))
    except (RuntimeError, ValueError) as error:
        announce("generators_unavailable", repr(error))
    announce("elapsed_seconds", round(time.monotonic() - start, 3))


if __name__ == "__main__":
    main()
