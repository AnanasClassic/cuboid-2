#!/usr/bin/env python3
"""Emit an exact Singular Riemann--Roch route from H(q,A) to a cubic.

This is the projective follow-up to ``e_model_singular_normalize.py``.  It
does not ask Sage's function-field implementation for a maximal order.
Instead, Singular's characteristic-zero ``brillnoether.lib`` computes
``L(2P)`` and ``L(3P)`` on the original (possibly singular) plane curve via
the Gorenstein adjoint ideal.  The complete linear system ``|3P|`` maps the
normalization to a plane cubic.  ``invertBirMap`` then exports the inverse
homogeneous map, which transports the original q and A functions.

The generated program deliberately verifies both projective compositions.
Those identities are identities on dense opens; base loci and the divisor
where the third inverse coordinate vanishes must still be retained when
classifying rational points.

Generate and run with a fixed Singular random seed, for example::

    python research/arithmetic_geometry/e_model_singular_rr_cubic.py \
      --output /tmp/e_model_rr_cubic.sing
    Singular --random=1 -q /tmp/e_model_rr_cubic.sing \
      | tee /tmp/e_model_rr_cubic.log
    sage -python research/arithmetic_geometry/e_model_sage_from_singular_cubic.py \
      --transcript /tmp/e_model_rr_cubic.log \
      --output /tmp/e_model_from_singular.json

No certificate is claimed merely by generating the input.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ARTIFACT = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_name("e_model_singular_rr_cubic.sing")


def monomial(variable: str, power: int) -> str:
    if power == 0:
        return ""
    if power == 1:
        return variable
    return f"{variable}^{power}"


def term_string(coefficient: int, powers: tuple[int, ...], variables: tuple[str, ...]) -> str:
    factors = [
        monomial(variable, power)
        for variable, power in zip(variables, powers, strict=True)
        if power
    ]
    if not factors:
        return str(coefficient)
    body = "*".join(factors)
    if coefficient == 1:
        return body
    if coefficient == -1:
        return "-" + body
    return f"{coefficient}*{body}"


def affine_polynomial(terms: list[dict]) -> str:
    pieces = [
        term_string(
            int(term["coefficient"]),
            tuple(map(int, term["powers"])),
            ("q", "A"),
        )
        for term in terms
    ]
    return "+".join(pieces).replace("+-", "-")


def homogeneous_polynomial(terms: list[dict]) -> tuple[str, int]:
    total_degree = max(sum(map(int, term["powers"])) for term in terms)
    pieces: list[str] = []
    for term in terms:
        q_power, a_power = map(int, term["powers"])
        z_power = total_degree - q_power - a_power
        pieces.append(
            term_string(
                int(term["coefficient"]),
                (q_power, a_power, z_power),
                ("Q", "B", "Z"),
            )
        )
    return "+".join(pieces).replace("+-", "-"), total_degree


def singular_source(
    affine: str,
    polynomial: str,
    total_degree: int,
    artifact_checksum: str,
    polynomial_checksum: str,
    include_affine_normalization_cross_check: bool,
) -> str:
    normalization_prefix = ""
    normalization_suffix = ""
    if include_affine_normalization_cross_check:
        normalization_prefix = f'''
print("CERT stage_start=affine_normalization_cross_check");
ring RAff = 0,(q,A),dp;
poly hAffine = {affine};
ideal affineInput = hAffine;
// H is independently certified irreducible over QQ.  Match the standalone
// normalization input and avoid repeating a minimal-prime decomposition.
list nor = normal(affineInput,"withDelta","isPrim");
if (size(nor[1]) != 1)
{{
  print("BLOCKER affine_normalization_not_one_component");
  exit;
}}
def Rnorm = nor[1][1];
setring Rnorm;
if (size(normap) < 2)
{{
  print("BLOCKER affine_normap_has_fewer_than_two_images");
  exit;
}}
print("CERT affine_normalization_component_count=1");
print("CERT affine_norid="+string(norid));
print("CERT affine_normap="+string(normap));
'''
        normalization_suffix = '''

// Independent affine-function cross-check through normal.lib's explicit map.
// This does not pretend that the affine normalization contains the points at
// infinity; the projective map and exceptional divisor remain recorded above.
setring Rnorm;
ideal normGB = std(norid);
map projectiveToNormalization = RP2,normap[1],normap[2],1;
ideal phiNorm = projectiveToNormalization(phi);
map cubicToNormalization = RC,phiNorm;
ideal psiNorm = cubicToNormalization(inverseMap);
ideal normalRoundtrip =
  psiNorm[1]-normap[1]*psiNorm[3],
  psiNorm[2]-normap[2]*psiNorm[3];
if (size(NF(normalRoundtrip,normGB)) != 0)
{
  print("BLOCKER affine_normap_q_A_roundtrip_failed");
  exit;
}
ideal cubicOnNormalization = cubicToNormalization(cubicIdeal);
if (size(NF(cubicOnNormalization,normGB)) != 0)
{
  print("BLOCKER cubic_does_not_vanish_through_normap");
  exit;
}
print("CERT affine_normap_q_A_roundtrip=OK");
'''

    return f'''// Generated exactly by e_model_singular_rr_cubic.py.
// Run Singular with --random=1: RiemannRochBN chooses an auxiliary form.
LIB "brillnoether.lib";
LIB "paraplanecurves.lib";
LIB "normal.lib";
option(redSB);
short=0;
system("--random",1);
print("CERT singular_random_seed=1");
print("BEGIN_SINGULAR_VERSION");
system("--version");
print("END_SINGULAR_VERSION");
{normalization_prefix}

ring RP2 = 0,(Q,B,Z),dp;
poly H = {polynomial};
ideal C = H;
ideal P = Q-6*Z,7*B-6*Z;
ideal Pstd = std(P);
print("CERT artifact_sha256={artifact_checksum}");
print("CERT homogeneous_polynomial_sha256={polynomial_checksum}");
print("CERT homogeneous_degree={total_degree}");
if (reduce(H,Pstd) != 0)
{{
  print("BLOCKER rational_point_not_on_curve");
  exit;
}}
poly dQ = diff(H,Q);
poly dB = diff(H,B);
poly dZ = diff(H,Z);
if ((reduce(dQ,Pstd)==0) && (reduce(dB,Pstd)==0) && (reduce(dZ,Pstd)==0))
{{
  print("BLOCKER rational_point_not_smooth");
  exit;
}}
print("CERT rational_smooth_point=[6:6/7:1]");

print("CERT stage_start=RiemannRoch_L2P");
list RR2 = RiemannRochBN(C,P^2,ideal(1));
print("CERT dim_L2P="+string(size(RR2[1])));
if (size(RR2[1]) != 2)
{{
  print("BLOCKER dim_L2P_not_2");
  exit;
}}
print("BEGIN_RR2_NUMERATORS");
RR2[1];
print("END_RR2_NUMERATORS");
print("CERT RR2_common_denominator="+string(RR2[2]));

print("CERT stage_start=RiemannRoch_L3P");
list RR3 = RiemannRochBN(C,P^3,ideal(1));
print("CERT dim_L3P="+string(size(RR3[1])));
if (size(RR3[1]) != 3)
{{
  print("BLOCKER dim_L3P_not_3");
  exit;
}}
ideal phi = RR3[1];
export(C,phi);
print("BEGIN_RR3_NUMERATORS");
phi;
print("END_RR3_NUMERATORS");
print("CERT RR3_common_denominator="+string(RR3[2]));
print("CERT RR3_numerator_degree="+string(deg(phi[1])));
if ((deg(phi[1]) != deg(phi[2])) || (deg(phi[1]) != deg(phi[3])))
{{
  print("BLOCKER RR3_generators_not_same_degree");
  exit;
}}
ideal sourceBaseLocus = sat(C+phi,maxideal(1));
print("CERT source_base_locus="+string(minbase(std(sourceBaseLocus))));
print("CERT source_base_locus_ring_dimension="+string(dim(std(sourceBaseLocus))));
if (dim(std(sourceBaseLocus)) > 1)
{{
  print("BLOCKER source_base_locus_not_projectively_finite");
  exit;
}}

print("CERT stage_start=invert_L3P_map");
def Rraw = invertBirMap(phi,C);
setring Rraw;
ideal Jraw = J;
ideal psiraw = psi;
export(Jraw,psiraw);

// Give the cubic coordinates stable names before emitting a transcript.
ring RC = 0,(X,Y,W),dp;
ideal cubicIdeal = fetch(Rraw,Jraw);
ideal inverseMap = fetch(Rraw,psiraw);
export(cubicIdeal,inverseMap);
ideal cubicGB = std(cubicIdeal);
ideal cubicMin = minbase(cubicGB);
if ((size(cubicMin) != 1) || (deg(cubicMin[1]) != 3))
{{
  print("BLOCKER image_not_principal_plane_cubic");
  print("CERT image_minbase="+string(cubicMin));
  exit;
}}
if (size(inverseMap) != 3)
{{
  print("BLOCKER inverse_map_not_three_coordinates");
  exit;
}}
print("CERT cubic="+string(cubicMin[1]));
print("CERT inverse_map_1="+string(inverseMap[1]));
print("CERT inverse_map_2="+string(inverseMap[2]));
print("CERT inverse_map_3="+string(inverseMap[3]));
ideal targetBaseLocus = sat(cubicIdeal+inverseMap,maxideal(1));
ideal affineDenominatorDivisor =
  sat(cubicIdeal+ideal(inverseMap[3]),maxideal(1));
print("CERT inverse_base_locus="+string(minbase(std(targetBaseLocus))));
print("CERT inverse_base_locus_ring_dimension="+string(dim(std(targetBaseLocus))));
print("CERT affine_denominator_divisor="
  +string(minbase(std(affineDenominatorDivisor))));
print("CERT affine_denominator_divisor_ring_dimension="
  +string(dim(std(affineDenominatorDivisor))));
if (dim(std(targetBaseLocus)) > 1)
{{
  print("BLOCKER inverse_base_locus_not_projectively_finite");
  exit;
}}
if (dim(std(affineDenominatorDivisor)) > 1)
{{
  print("BLOCKER affine_denominator_divisor_not_projectively_finite");
  exit;
}}
if (size(NF(ideal(inverseMap[3]),cubicGB)) == 0)
{{
  print("BLOCKER affine_denominator_identically_zero");
  exit;
}}

// Verify H(psi)=0 and phi(psi)=[X:Y:W] on the cubic.
map fromPlane = RP2,inverseMap;
ideal planeEquationAfterInverse = fromPlane(C);
if (size(NF(planeEquationAfterInverse,cubicGB)) != 0)
{{
  print("BLOCKER inverse_does_not_land_on_H");
  exit;
}}
ideal phiPsi = fromPlane(phi);
ideal targetMinors =
  phiPsi[1]*Y-phiPsi[2]*X,
  phiPsi[1]*W-phiPsi[3]*X,
  phiPsi[2]*W-phiPsi[3]*Y;
if (size(NF(targetMinors,cubicGB)) != 0)
{{
  print("BLOCKER target_projective_composition_failed");
  exit;
}}
print("CERT target_projective_composition=OK");

// Verify psi(phi)=[Q:B:Z] on H.  These are dense-open identities; the
// projective base loci are not discarded by this check.
setring RP2;
map fromCubic = RC,phi;
ideal psiPhi = fromCubic(inverseMap);
ideal sourceMinors =
  psiPhi[1]*B-psiPhi[2]*Q,
  psiPhi[1]*Z-psiPhi[3]*Q,
  psiPhi[2]*Z-psiPhi[3]*B;
if (size(NF(sourceMinors,std(C))) != 0)
{{
  print("BLOCKER source_projective_composition_failed");
  exit;
}}
print("CERT source_projective_composition=OK");
if (size(NF(ideal(psiPhi[3]),std(C))) == 0)
{{
  print("BLOCKER q_A_roundtrip_denominator_identically_zero");
  exit;
}}
print("CERT q_A_projective_roundtrip=OK");
{normalization_suffix}
print("CERT singular_rr_cubic_finished=OK");
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--metadata", type=Path)
    parser.add_argument(
        "--include-affine-normalization-cross-check",
        action="store_true",
        help=(
            "also run normal.lib in the same Singular process and verify the "
            "cubic/inverse map through norid,normap"
        ),
    )
    args = parser.parse_args()

    data = json.loads(args.artifact.read_text(encoding="utf-8"))
    terms = data["elliptic_plane_model"]["terms"]
    affine = affine_polynomial(terms)
    polynomial, total_degree = homogeneous_polynomial(terms)
    polynomial_checksum = hashlib.sha256(polynomial.encode()).hexdigest()
    source = singular_source(
        affine,
        polynomial,
        total_degree,
        data["sha256_without_checksum"],
        polynomial_checksum,
        args.include_affine_normalization_cross_check,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source, encoding="utf-8")
    print(f"generated {args.output}")
    print(f"homogeneous polynomial sha256 {polynomial_checksum}")
    print("status INPUT_GENERATED_NOT_EXECUTED")

    if args.metadata:
        try:
            source_artifact = str(args.artifact.resolve().relative_to(ROOT.resolve()))
        except ValueError:
            source_artifact = str(args.artifact)
        payload = {
            "schema": 1,
            "status": "INPUT_GENERATED_NOT_EXECUTED",
            "source_artifact": source_artifact,
            "source_artifact_checksum": data["sha256_without_checksum"],
            "homogeneous_degree": total_degree,
            "homogeneous_polynomial_sha256": polynomial_checksum,
            "singular_input_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "singular_random_seed_required": 1,
            "includes_affine_normalization_cross_check": (
                args.include_affine_normalization_cross_check
            ),
            "normalization_claim": False,
            "weierstrass_claim": False,
        }
        args.metadata.parent.mkdir(parents=True, exist_ok=True)
        args.metadata.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
