#!/usr/bin/env sage -python
"""Exact Sage route from H(q,A) to a Weierstrass model with q,A,V.

The two earlier probes call ``FunctionField.genus()`` before exposing useful
intermediate data.  On the degree-10 and degree-8 presentations that call can
spend hours computing maximal orders/differents.  This probe deliberately does
*not* call ``genus()``.  It has separately timed stages and uses the certified
rational point (q,A)=(6,6/7) to construct L(2P), L(3P), a plane cubic and then
a Weierstrass model.

The invariant V=a^2/b is supplied by ``e_model_dihedral_descent.py`` as a
direct rational function N(q,A)/D(q,A).  That script verifies the T -> -T and
T -> 1/T cross-products exactly and rewrites the palindromic result through
q=T^2+T^-2 coefficient by coefficient.  This probe checks the artifact hash
and transports V by composition after transporting q and A.  It never inverts
Q1 in a tower of algebraic function fields; Sage 10.9 required more than 1200
seconds for that unnecessary xgcd.

Run in SageMath 10.8 with, for example,

    sage -python research/arithmetic_geometry/e_model_sage_transport.py \
        --output research/arithmetic_geometry/e_model_certificate.json

Use ``--stop-after descent`` to certify V without constructing maximal orders.
Use ``--skip-v-descent`` for a q,A-only normalization/Riemann--Roch run that
does not even read the (large) direct-V artifact.  In that mode every emitted
status says explicitly that V descent and transport were skipped.
No claim is emitted for a stage that times out or raises an exception.
"""

from __future__ import annotations

import argparse
import json
import platform
import signal
import time
from contextlib import contextmanager
from pathlib import Path

from sage.all import (  # type: ignore
    EllipticCurve,
    EllipticCurve_from_cubic,
    FunctionField,
    Matrix,
    PolynomialRing,
    QQ,
    ZZ,
    lcm,
    version,
)


ROOT = Path(__file__).resolve().parents[2]
ARTIFACT = ROOT / "artifacts" / "genus4_quotient.json"
DIHEDRAL_V_ARTIFACT = Path(__file__).with_name("e_model_dihedral_V.json")
DEFAULT_OUTPUT = Path(__file__).with_name("e_model_certificate.json")


class StageTimeout(RuntimeError):
    pass


def cert(label: str, value) -> None:
    print(f"CERT {label} = {value}", flush=True)


@contextmanager
def timed_stage(name: str, timeout_seconds: int):
    started = time.monotonic()

    def alarm_handler(_signum, _frame):
        raise StageTimeout(f"stage {name!r} exceeded {timeout_seconds} seconds")

    old_handler = signal.signal(signal.SIGALRM, alarm_handler)
    signal.alarm(timeout_seconds)
    cert("stage_start", name)
    try:
        yield
    except StageTimeout as error:
        cert("blocker_stage", name)
        cert("blocker_reason", repr(error))
        cert("blocker_elapsed_seconds", round(time.monotonic() - started, 3))
        raise
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
        cert(f"stage_{name}_elapsed_seconds", round(time.monotonic() - started, 3))


def build_H(data, q, A, polynomial_ring):
    H = polynomial_ring(0)
    for term in data["elliptic_plane_model"]["terms"]:
        q_power, a_power = term["powers"]
        H += ZZ(term["coefficient"]) * q**q_power * A**a_power
    return H


def evaluate_sparse(terms, first, second):
    value = first.parent()(0)
    for term in terms:
        first_power, second_power = term["powers"]
        value += ZZ(term["coefficient"]) * first**first_power * second**second_power
    return value


def constant_relation_matrix(field, elements):
    """Return the QQ-matrix of constant linear relations among elements."""

    degree = field.degree()
    coordinates = []
    denominators = []
    for element in elements:
        coeffs = list(field(element))
        coeffs += [field.base_field()(0)] * (degree - len(coeffs))
        coordinates.append(coeffs)
        denominators.extend(c.denominator() for c in coeffs)

    common_denominator = lcm(denominators) if denominators else field.base_field()(1)
    numerators = []
    max_degree = 0
    for coeffs in coordinates:
        row = []
        for coeff in coeffs:
            cleared = coeff * common_denominator
            numerator = cleared.numerator()
            denominator = cleared.denominator()
            # ``cleared`` is a rational function in the base generator.  Its
            # remaining denominator must be constant after the common lcm.
            if denominator.degree() != 0:
                raise AssertionError("nonconstant denominator survived lcm clearing")
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
    return constant_relation_matrix(field, elements).rank() == len(elements)


def rational_xy_representation(field, f, x, y, max_degree: int = 18):
    """Find f=-(N0(x)+N1(x)y)/D(x) by exact QQ-linear algebra."""

    for degree in range(max_degree + 1):
        powers = [x**i for i in range(degree + 1)]
        elements = [f * power for power in powers]
        elements += powers
        elements += [y * power for power in powers]
        kernel = constant_relation_matrix(field, elements).right_kernel()
        block = degree + 1
        for relation in kernel.basis():
            denominator = list(relation[:block])
            if all(coefficient == 0 for coefficient in denominator):
                continue
            numerator_0 = list(relation[block : 2 * block])
            numerator_1 = list(relation[2 * block : 3 * block])
            D = sum((denominator[i] * x**i for i in range(block)), field(0))
            N0 = sum((numerator_0[i] * x**i for i in range(block)), field(0))
            N1 = sum((numerator_1[i] * x**i for i in range(block)), field(0))
            if D == 0:
                continue
            if f * D + N0 + N1 * y != 0:
                raise AssertionError("candidate x,y representation does not verify")
            return {
                "degree_bound": degree,
                "D_coefficients": [str(value) for value in denominator],
                "N0_coefficients": [str(value) for value in numerator_0],
                "N1_coefficients": [str(value) for value in numerator_1],
                "formula": "f=-(N0(x)+N1(x)*y)/D(x)",
            }
    raise RuntimeError(f"no x,y representation found through degree {max_degree}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--stop-after",
        choices=("descent", "place", "cubic", "transport", "all"),
        default="all",
    )
    parser.add_argument("--stage-timeout", type=int, default=1800)
    parser.add_argument("--representation-degree", type=int, default=18)
    parser.add_argument(
        "--skip-v-descent",
        action="store_true",
        help="run normalization/RR for q,A only; emit no V transport claim",
    )
    args = parser.parse_args()
    if args.skip_v_descent and args.stop_after == "descent":
        parser.error("--skip-v-descent is incompatible with --stop-after descent")
    args.output.parent.mkdir(parents=True, exist_ok=True)

    total_started = time.monotonic()
    cert("sage_version", version())
    cert("python_version", platform.python_version())
    cert("artifact", ARTIFACT.relative_to(ROOT))
    data = json.loads(ARTIFACT.read_text(encoding="utf-8"))

    certificate = {
        "schema": 1,
        "sage_version": version(),
        "artifact_checksum": data["sha256_without_checksum"],
        "status": "IN_PROGRESS",
    }

    with timed_stage("field", args.stage_timeout):
        K = FunctionField(QQ, "A")
        A0 = K.gen()
        R = PolynomialRing(K, "q")
        q0 = R.gen()
        H = build_H(data, q0, A0, R)
        cert("H_degree_over_QQ_A", H.degree())
        irreducible = H.is_irreducible()
        cert("H_irreducible_over_QQ_A", irreducible)
        if H.degree() != 8 or not irreducible:
            raise AssertionError("unexpected degree-eight presentation")
        L = K.extension(H, "q_original")
        qL = L.gen()
        AL = L(L.base_field().gen())
        direct_point_value = sum(
            ZZ(term["coefficient"])
            * QQ(6) ** term["powers"][0]
            * (QQ(6) / 7) ** term["powers"][1]
            for term in data["elliptic_plane_model"]["terms"]
        )
        cert("H_at_6_6over7", direct_point_value)
        if direct_point_value != 0:
            raise AssertionError("(q,A)=(6,6/7) is not on H")

    with timed_stage("descent_V", args.stage_timeout):
        # Never invert Q1 in the algebraic T-extension.  Sage 10.9 spent the
        # full 1200-second stage in that xgcd.  The independent SymPy script
        # e_model_dihedral_descent.py exports a direct N(q,A)/D(q,A), verified
        # by exact dihedral cross-products and Laurent coefficients.
        direct_V = None
        if args.skip_v_descent:
            cert("V_descent", "SKIPPED_BY_CLI; q,A normalization only")
            certificate["V_descent"] = "SKIPPED_BY_CLI"
        else:
            direct_V = json.loads(DIHEDRAL_V_ARTIFACT.read_text(encoding="utf-8"))
            direct_checksum = direct_V.pop("sha256_without_checksum")
            canonical = json.dumps(direct_V, sort_keys=True, separators=(",", ":")).encode()
            import hashlib

            if hashlib.sha256(canonical).hexdigest() != direct_checksum:
                raise AssertionError("dihedral V artifact checksum mismatch")
            if direct_V["artifact_checksum"] != data["sha256_without_checksum"]:
                raise AssertionError("dihedral V artifact was built from another quotient")
            if direct_V["status"] != "MACHINE-VERIFIED":
                raise AssertionError("dihedral V artifact is not certified")
            direct_V["sha256_without_checksum"] = direct_checksum
            cert("V_direct_formula", direct_V["formula"])
            cert("V_direct_formula_degrees", direct_V["degrees"])
            cert("V_direct_formula_checksum", direct_checksum)
            certificate["V_descent"] = (
                "direct dihedral N(q,A)/D(q,A); no Sage function-field inversion"
            )
            certificate["V_direct_formula_artifact"] = str(
                DIHEDRAL_V_ARTIFACT.relative_to(ROOT)
            )
            certificate["V_direct_formula_checksum"] = direct_checksum

    if args.stop_after == "descent":
        certificate["status"] = "V_DESCENT_CERTIFIED"
        args.output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
        cert("output", args.output)
        return

    with timed_stage("monic_integral_model", args.stage_timeout):
        M, from_M, to_M = L.monic_integral_model("beta")
        qM = to_M(qL)
        AM = to_M(AL)
        if from_M(qM) != qL or from_M(AM) != AL:
            raise AssertionError("monic-integral isomorphism does not round-trip q,A")
        cert("monic_integral_polynomial", M.polynomial())
        cert("monic_integral_roundtrip_q_A", "OK")

    with timed_stage("rational_place", args.stage_timeout):
        order = M.maximal_order()
        ideal = order.ideal(qM - QQ(6), AM - QQ(6) / 7)
        place = ideal.place()
        cert("base_place", place)
        cert("base_place_degree", place.degree())
        if place.degree() != 1:
            raise AssertionError("the chosen base place is not rational")
        if (qM - 6).valuation(place) <= 0 or (AM - QQ(6) / 7).valuation(place) <= 0:
            raise AssertionError("q,A do not specialize correctly at the chosen place")

    if args.stop_after == "place":
        certificate["status"] = "RATIONAL_PLACE_CERTIFIED"
        args.output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
        cert("output", args.output)
        return

    with timed_stage("riemann_roch_cubic", args.stage_timeout):
        divisor = place.divisor()
        basis_2 = (2 * divisor).basis_function_space()
        basis_3 = (3 * divisor).basis_function_space()
        cert("dim_L2P", len(basis_2))
        cert("dim_L3P", len(basis_3))
        if len(basis_2) != 2 or len(basis_3) != 3:
            raise AssertionError("Riemann--Roch dimensions are not 2 and 3")
        one = M(1)
        x_candidates = [function for function in basis_2 if function != one]
        if not x_candidates:
            raise AssertionError("L(2P) has no exposed nonconstant function")
        x_rr = x_candidates[0]
        y_candidates = [
            function
            for function in basis_3
            if independent_over_constants(M, [one, x_rr, function])
        ]
        if not y_candidates:
            raise AssertionError("L(3P) has no third independent function")
        y_rr = y_candidates[0]
        cert("rr_x", x_rr)
        cert("rr_y", y_rr)

        monomials = [one, x_rr, y_rr, x_rr**2, x_rr * y_rr, x_rr**3, y_rr**2]
        relation_kernel = constant_relation_matrix(M, monomials).right_kernel()
        cert("cubic_relation_kernel_dimension", relation_kernel.dimension())
        if relation_kernel.dimension() != 1:
            raise AssertionError("the seven RR monomials do not have one relation")
        relation = list(relation_kernel.basis()[0])
        if sum((relation[i] * monomials[i] for i in range(7)), M(0)) != 0:
            raise AssertionError("cubic relation does not vanish in M")

        S = PolynomialRing(QQ, names=("X", "Y", "Z"))
        Xc, Yc, Zc = S.gens()
        c0, c1, c2, c3, c4, c5, c6 = relation
        cubic = c0 * Zc**3 + c1 * Xc * Zc**2 + c2 * Yc * Zc**2
        cubic += c3 * Xc**2 * Zc + c4 * Xc * Yc * Zc
        cubic += c5 * Xc**3 + c6 * Yc**2 * Zc
        cert("plane_cubic", cubic)
        if cubic(Xc=0, Yc=1, Zc=0) != 0:
            raise AssertionError("RR pole place is not [0:1:0] on the cubic")
        cubic_to_E = EllipticCurve_from_cubic(cubic, [0, 1, 0], morphism=True)
        E = cubic_to_E.codomain()
        E_to_cubic = cubic_to_E.inverse()
        cert("weierstrass_model", E)
        cert("weierstrass_ainvs", E.a_invariants())
        cert("cubic_to_weierstrass", cubic_to_E)
        cert("weierstrass_to_cubic", E_to_cubic)
        certificate["plane_cubic"] = str(cubic)
        certificate["weierstrass_ainvs"] = [str(value) for value in E.a_invariants()]
        certificate["cubic_to_weierstrass"] = str(cubic_to_E)
        certificate["weierstrass_to_cubic"] = str(E_to_cubic)

        # Good-prime traces only identify the isogeny class 544.c.  They do
        # not distinguish these two non-isomorphic curves.  The cubic's exact
        # j-invariant and an explicit Sage isomorphism do distinguish them.
        candidates = {
            "544.c_E1": EllipticCurve(QQ, [0, 0, 0, -5, 4]),
            "544.c_E2": EllipticCurve(QQ, [0, 0, 0, 5, 18]),
        }
        candidate_data = {
            name: {
                "ainvs": [str(value) for value in curve.a_invariants()],
                "j": str(curve.j_invariant()),
                "isomorphic_to_RR_curve": bool(E.is_isomorphic(curve)),
            }
            for name, curve in candidates.items()
        }
        cert("RR_curve_j", E.j_invariant())
        cert("544c_candidate_comparison", candidate_data)
        matches = [name for name, item in candidate_data.items() if item["isomorphic_to_RR_curve"]]
        cert("544c_isomorphic_match_count", len(matches))
        certificate["544c_candidate_comparison"] = candidate_data
        certificate["RR_curve_j"] = str(E.j_invariant())
        if len(matches) == 1:
            matched_name = matches[0]
            matched_curve = candidates[matched_name]
            E_to_candidate = E.isomorphism_to(matched_curve)
            candidate_to_E = E_to_candidate.inverse()
            cert("544c_exact_match", matched_name)
            cert("RR_weierstrass_to_544c", E_to_candidate)
            cert("544c_to_RR_weierstrass", candidate_to_E)
            certificate["544c_exact_match"] = matched_name
            certificate["RR_weierstrass_to_544c"] = str(E_to_candidate)
            certificate["544c_to_RR_weierstrass"] = str(candidate_to_E)
        else:
            cert("544c_exact_match", "NONE_OR_AMBIGUOUS; trace fingerprint not promoted")
            certificate["544c_exact_match"] = None

    if args.stop_after == "cubic":
        certificate["status"] = "WEIERSTRASS_MODEL_CERTIFIED"
        args.output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
        cert("output", args.output)
        return

    with timed_stage("transport_q_A_V", args.stage_timeout):
        transported = {}
        for name, function in (("q", qM), ("A", AM)):
            representation = rational_xy_representation(
                M,
                function,
                x_rr,
                y_rr,
                max_degree=args.representation_degree,
            )
            cert(f"{name}_xy_representation", representation)
            transported[name] = representation
        if direct_V is None:
            transported["V"] = {"status": "SKIPPED_BY_CLI; no transport claim"}
        else:
            transported["V"] = {
                "formula": direct_V["formula"],
                "numerator_terms": direct_V["degrees"]["numerator_terms"],
                "denominator_terms": direct_V["degrees"]["denominator_terms"],
                "artifact": str(DIHEDRAL_V_ARTIFACT.relative_to(ROOT)),
                "composition": (
                    "substitute the verified transported q(x,y),A(x,y) into "
                    "the direct dihedral numerator/denominator"
                ),
            }
        certificate["transport_via_cubic_coordinates"] = transported
        certificate["transport_interpretation"] = (
            "Apply the stored inverse Weierstrass-to-cubic morphism, set "
            "x=X/Z and y=Y/Z, then evaluate the verified q,A formulas"
            + (
                "; V was deliberately omitted by --skip-v-descent."
                if direct_V is None
                else " and compose them with the certified direct V(q,A) formula."
            )
        )
        if certificate.get("544c_exact_match") is not None:
            certificate["transport_from_544c_candidate"] = (
                "First apply the stored 544c_to_RR_weierstrass isomorphism, "
                "then weierstrass_to_cubic, set x=X/Z,y=Y/Z, and evaluate "
                + (
                    "the q,A formulas; V was deliberately omitted."
                    if direct_V is None
                    else "the q,A,V formulas."
                )
            )

    if args.stop_after == "transport":
        certificate["status"] = (
            "Q_A_TRANSPORT_CERTIFIED_V_SKIPPED"
            if direct_V is None
            else "Q_A_V_TRANSPORT_CERTIFIED"
        )
        args.output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
        cert("output", args.output)
        return

    with timed_stage("elliptic_arithmetic", args.stage_timeout):
        minimal = E.global_minimal_model()
        cert("minimal_model", minimal)
        cert("minimal_ainvs", minimal.a_invariants())
        cert("minimal_discriminant", minimal.discriminant())
        cert("minimal_conductor", minimal.conductor())
        cert("torsion_subgroup", minimal.torsion_subgroup())
        certificate["minimal_ainvs"] = [str(value) for value in minimal.a_invariants()]
        certificate["minimal_discriminant"] = str(minimal.discriminant())
        certificate["minimal_conductor"] = str(minimal.conductor())
        certificate["torsion_subgroup"] = str(minimal.torsion_subgroup())
        try:
            rank_bounds = minimal.rank_bounds()
            cert("rank_bounds", rank_bounds)
            certificate["rank_bounds"] = [int(value) for value in rank_bounds]
        except (AttributeError, RuntimeError, ValueError) as error:
            cert("rank_bounds_unavailable", repr(error))
            certificate["rank_bounds_status"] = repr(error)
        try:
            generators = minimal.gens(proof=True)
            cert("generators_proof_true", generators)
            certificate["generators_proof_true"] = [str(value) for value in generators]
        except (RuntimeError, ValueError) as error:
            cert("generators_unavailable", repr(error))
            certificate["generators_status"] = repr(error)

    certificate["status"] = (
        "WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED_V_SKIPPED"
        if direct_V is None
        else "WEIERSTRASS_AND_TRANSPORT_CERTIFIED"
    )
    certificate["elapsed_seconds"] = round(time.monotonic() - total_started, 3)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n")
    cert("output", args.output)
    cert("elapsed_seconds", certificate["elapsed_seconds"])


if __name__ == "__main__":
    main()
