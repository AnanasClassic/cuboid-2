#!/usr/bin/env sage -python
"""Verify a Singular |3P| cubic and transport q,A to Weierstrass form.

Input is the exact transcript emitted by ``e_model_singular_rr_cubic.py``.
This stage only works with the smooth cubic already certified by Singular's
two projective composition checks.  It never constructs a function field and
never calls ``FunctionField.maximal_order()``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from pathlib import Path

from sage.all import (  # type: ignore
    Curve,
    EllipticCurve,
    EllipticCurve_from_cubic,
    ProjectiveSpace,
    QQ,
    sage_eval,
    version,
)


ROOT = Path(__file__).resolve().parents[2]
ARTIFACT = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_name("e_model_singular_cubic_certificate.json")


def transcript_certificates(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line.startswith("CERT ") or "=" not in line:
            continue
        key, value = line[5:].split("=", 1)
        values[key.strip()] = value.strip()
    return values


def evaluate_polynomial(expression: str, ring, variables):
    locals_map = {str(variable): variable for variable in variables}
    value = sage_eval(expression, locals=locals_map)
    return ring(value)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--transcript", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    transcript = args.transcript.read_text(encoding="utf-8")
    if "BLOCKER " in transcript:
        raise RuntimeError("Singular transcript contains a BLOCKER marker")
    certs = transcript_certificates(transcript)
    required_status = {
        "target_projective_composition": "OK",
        "source_projective_composition": "OK",
        "q_A_projective_roundtrip": "OK",
        "singular_rr_cubic_finished": "OK",
    }
    for key, expected in required_status.items():
        if certs.get(key) != expected:
            raise RuntimeError(f"Singular transcript lacks {key}={expected}")
    required_values = {
        "rational_smooth_point": "[6:6/7:1]",
        "dim_L2P": "2",
        "dim_L3P": "3",
        "homogeneous_degree": "18",
        "singular_random_seed": "1",
    }
    for key, expected in required_values.items():
        if certs.get(key) != expected:
            raise RuntimeError(f"Singular transcript lacks {key}={expected}")
    finite_projective_loci = (
        "source_base_locus_ring_dimension",
        "inverse_base_locus_ring_dimension",
        "affine_denominator_divisor_ring_dimension",
    )
    for key in finite_projective_loci:
        if key not in certs or int(certs[key]) > 1:
            raise RuntimeError(f"Singular did not certify finite exceptional locus {key}")
    if "affine_normalization_component_count" in certs:
        if certs["affine_normalization_component_count"] != "1":
            raise RuntimeError("affine normalization did not have one component")
        if certs.get("affine_normap_q_A_roundtrip") != "OK":
            raise RuntimeError("optional norid,normap q,A round trip failed")
    required_expressions = ["cubic", "inverse_map_1", "inverse_map_2", "inverse_map_3"]
    missing = [key for key in required_expressions if key not in certs]
    if missing:
        raise RuntimeError(f"Singular transcript lacks expressions: {missing}")

    P2 = ProjectiveSpace(QQ, 2, names=("X", "Y", "W"))
    R = P2.coordinate_ring()
    X, Y, W = R.gens()
    cubic = evaluate_polynomial(certs["cubic"], R, (X, Y, W))
    inverse_map = [
        evaluate_polynomial(certs[f"inverse_map_{index}"], R, (X, Y, W))
        for index in range(1, 4)
    ]
    if cubic.total_degree() != 3 or not cubic.is_homogeneous():
        raise AssertionError("Singular image is not a homogeneous cubic")
    if len({value.total_degree() for value in inverse_map}) != 1:
        raise AssertionError("inverse projective coordinates have unequal degrees")
    cubic_ideal = R.ideal(cubic)
    if cubic_ideal.reduce(inverse_map[2]) == 0:
        raise AssertionError("the affine q,A denominator vanishes identically")

    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    artifact_without_checksum = dict(artifact)
    claimed_artifact_checksum = artifact_without_checksum.pop("sha256_without_checksum")
    recomputed_artifact_checksum = hashlib.sha256(
        json.dumps(artifact_without_checksum, indent=2, sort_keys=True).encode()
    ).hexdigest()
    if recomputed_artifact_checksum != claimed_artifact_checksum:
        raise AssertionError("quotient artifact checksum is invalid")
    if artifact["sha256_without_checksum"] != certs.get("artifact_sha256"):
        raise AssertionError("Singular transcript used another quotient artifact")
    total_degree = max(
        sum(map(int, term["powers"]))
        for term in artifact["elliptic_plane_model"]["terms"]
    )
    q_projective, a_projective, z_projective = inverse_map
    H_after_inverse = R(0)
    for term in artifact["elliptic_plane_model"]["terms"]:
        q_power, a_power = map(int, term["powers"])
        z_power = total_degree - q_power - a_power
        H_after_inverse += (
            QQ(term["coefficient"])
            * q_projective**q_power
            * a_projective**a_power
            * z_projective**z_power
        )
    if cubic_ideal.reduce(H_after_inverse) != 0:
        raise AssertionError("independent Sage check of H(psi)=0 failed")

    cubic_curve = Curve(cubic, P2)
    if cubic_curve.is_singular():
        raise AssertionError("the |3P| image cubic is geometrically singular")
    geometric_genus = (cubic.total_degree() - 1) * (cubic.total_degree() - 2) // 2
    if geometric_genus != 1:
        raise AssertionError("a smooth plane cubic must have geometric genus one")

    # P=None is intentional: |3P| supplies a rational flex, and Sage's
    # documented constructor finds a rational flex when no point is supplied.
    cubic_to_E = EllipticCurve_from_cubic(cubic, P=None, morphism=True)
    E = cubic_to_E.codomain()
    E_to_cubic = cubic_to_E.inverse()
    weierstrass_coordinates_on_cubic = list(cubic_to_E.defining_polynomials())
    cubic_coordinates_on_E = list(E_to_cubic.defining_polynomials())
    if {value.total_degree() for value in weierstrass_coordinates_on_cubic} != {1}:
        raise AssertionError("P=None did not produce a linear flex transformation")
    if {value.total_degree() for value in cubic_coordinates_on_E} != {1}:
        raise AssertionError("inverse flex transformation is not linear")

    # Independently verify Sage's two projective compositions.  Because both
    # transformations are linear, these maps have no projective base locus.
    cubic_roundtrip = [
        R(value(*weierstrass_coordinates_on_cubic))
        for value in cubic_coordinates_on_E
    ]
    cubic_roundtrip_minors = (
        cubic_roundtrip[0] * Y - cubic_roundtrip[1] * X,
        cubic_roundtrip[0] * W - cubic_roundtrip[2] * X,
        cubic_roundtrip[1] * W - cubic_roundtrip[2] * Y,
    )
    if any(cubic_ideal.reduce(value) != 0 for value in cubic_roundtrip_minors):
        raise AssertionError("cubic -> Weierstrass -> cubic composition failed")

    E_ambient_ring = E.ambient_space().coordinate_ring()
    EX, EY, EZ = E_ambient_ring.gens()
    E_equation = E_ambient_ring(E.defining_polynomial())
    E_ideal = E_ambient_ring.ideal(E_equation)
    if cubic_ideal.reduce(R(E_equation(*weierstrass_coordinates_on_cubic))) != 0:
        raise AssertionError("cubic-to-Weierstrass map does not land on E")
    if E_ideal.reduce(E_ambient_ring(cubic(*cubic_coordinates_on_E))) != 0:
        raise AssertionError("Weierstrass-to-cubic map does not land on cubic")
    weierstrass_roundtrip = [
        E_ambient_ring(value(*cubic_coordinates_on_E))
        for value in weierstrass_coordinates_on_cubic
    ]
    weierstrass_roundtrip_minors = (
        weierstrass_roundtrip[0] * EY - weierstrass_roundtrip[1] * EX,
        weierstrass_roundtrip[0] * EZ - weierstrass_roundtrip[2] * EX,
        weierstrass_roundtrip[1] * EZ - weierstrass_roundtrip[2] * EY,
    )
    if any(E_ideal.reduce(value) != 0 for value in weierstrass_roundtrip_minors):
        raise AssertionError("Weierstrass -> cubic -> Weierstrass composition failed")

    # The Singular inverse is [Q:B:Z].  Thus q=Q/Z and A=B/Z on the original
    # affine chart.  Keeping numerator and denominator separately retains the
    # Z=0 exceptional divisor instead of silently deleting it.
    inverse_on_E = [
        polynomial(*cubic_coordinates_on_E) for polynomial in inverse_map
    ]
    q_num, a_num, affine_den = inverse_on_E

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
    matches = [name for name, item in candidate_data.items() if item["isomorphic_to_RR_curve"]]
    if len(matches) > 1:
        raise AssertionError("cubic is ambiguously isomorphic to both non-isomorphic candidates")

    output = {
        "schema": 1,
        "status": "WEIERSTRASS_Q_A_TRANSPORT_CERTIFIED",
        "sage_version": version(),
        "python_version": platform.python_version(),
        "singular_transcript": str(args.transcript),
        "singular_transcript_sha256": hashlib.sha256(transcript.encode()).hexdigest(),
        "artifact_checksum": certs.get("artifact_sha256"),
        "homogeneous_polynomial_sha256": certs.get("homogeneous_polynomial_sha256"),
        "cubic": str(cubic),
        "cubic_smooth": True,
        "geometric_genus": int(geometric_genus),
        "geometric_genus_certificate": (
            "smooth plane curve of degree 3: (d-1)(d-2)/2=1"
        ),
        "weierstrass_ainvs": [str(value) for value in E.a_invariants()],
        "weierstrass_j": str(E.j_invariant()),
        "cubic_to_weierstrass": str(cubic_to_E),
        "weierstrass_to_cubic": str(E_to_cubic),
        "cubic_weierstrass_maps_linear": True,
        "cubic_weierstrass_projective_compositions": "VERIFIED_MODULO_IDEALS",
        "inverse_cubic_to_original_projective": [str(value) for value in inverse_map],
        "independent_H_after_inverse_remainder": "0",
        "transport_on_weierstrass": {
            "q_numerator": str(q_num),
            "A_numerator": str(a_num),
            "common_affine_denominator": str(affine_den),
            "q_formula": "q=q_numerator/common_affine_denominator",
            "A_formula": "A=A_numerator/common_affine_denominator",
            "exceptional_divisor": "common_affine_denominator=0 is retained",
            "singular_affine_denominator_divisor": certs.get(
                "affine_denominator_divisor"
            ),
            "singular_inverse_base_locus": certs.get("inverse_base_locus"),
            "singular_source_base_locus": certs.get("source_base_locus"),
            "exceptional_loci_certified_projectively_finite": True,
            "exceptional_loci_scope": (
                "The exact saturated ideals are retained.  Their individual "
                "closed points/branches must be classified before a global "
                "rational-point statement is made."
            ),
        },
        "candidate_comparison": candidate_data,
        "candidate_exact_match": matches[0] if len(matches) == 1 else None,
        "scope": (
            "Singular certified both projective birational compositions; Sage "
            "certified cubic smoothness and its Weierstrass transformation. "
            "This does not classify rational points on the elliptic curve or "
            "on any square-value cover."
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print("CERT cubic_smooth=True")
    print("CERT weierstrass_ainvs=" + str(E.a_invariants()))
    print("CERT candidate_exact_match=" + str(output["candidate_exact_match"]))
    print("CERT output=" + str(args.output))


if __name__ == "__main__":
    main()
