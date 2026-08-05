#!/usr/bin/env python3
"""Emit an exact Singular ``normal.lib`` input for a chart of H(q,A)=0.

This is a fallback for Sage's function-field ``maximal_order()`` route.  It
does not claim that normalization has succeeded: the generated Singular run
must finish, report exactly one component, and preserve its ``norid`` and
``normap`` output before any normalization claim is made.

The ordinary projective closure uses coordinates [Q:B:Z] and total
homogenization degree 18.  The three supported charts and their maps back to
the original affine functions are

    affine:      q = q,   A = A
    Q_nonzero:   q = 1/z, A = a/z
    B_nonzero:   q = u/z, A = 1/z.

The two infinity charts are deliberately both available: normalizing only the
affine chart is enough for its function field, but is not a certificate for
the points above the projective boundary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ARTIFACT = ROOT / "artifacts" / "genus4_quotient.json"
DEFAULT_OUTPUT = Path(__file__).with_name("e_model_singular_affine.sing")


def monomial(variable: str, power: int) -> str:
    if power == 0:
        return ""
    if power == 1:
        return variable
    return f"{variable}^{power}"


def term_string(coefficient: int, powers: tuple[int, int], variables: tuple[str, str]) -> str:
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


def polynomial_string(terms: list[dict], chart: str) -> tuple[str, tuple[str, str], str]:
    total_degree = max(sum(map(int, term["powers"])) for term in terms)
    pieces: list[str] = []

    if chart == "affine":
        variables = ("q", "A")
        interpretation = "q=q; A=A"
        for term in terms:
            powers = tuple(map(int, term["powers"]))
            pieces.append(term_string(int(term["coefficient"]), powers, variables))
    elif chart == "Q_nonzero":
        # Q=1, a=B/Q, z=Z/Q in the total homogenization H^h(Q,B,Z).
        variables = ("a", "z")
        interpretation = "q=1/z; A=a/z"
        for term in terms:
            q_power, a_power = map(int, term["powers"])
            z_power = total_degree - q_power - a_power
            pieces.append(
                term_string(
                    int(term["coefficient"]),
                    (a_power, z_power),
                    variables,
                )
            )
    elif chart == "B_nonzero":
        # B=1, u=Q/B, z=Z/B in the total homogenization H^h(Q,B,Z).
        variables = ("u", "z")
        interpretation = "q=u/z; A=1/z"
        for term in terms:
            q_power, a_power = map(int, term["powers"])
            z_power = total_degree - q_power - a_power
            pieces.append(
                term_string(
                    int(term["coefficient"]),
                    (q_power, z_power),
                    variables,
                )
            )
    else:  # pragma: no cover - argparse enforces the choices.
        raise ValueError(chart)

    polynomial = "+".join(pieces).replace("+-", "-")
    return polynomial, variables, interpretation


def singular_source(
    polynomial: str,
    variables: tuple[str, str],
    chart: str,
    interpretation: str,
    artifact_checksum: str,
    polynomial_checksum: str,
) -> str:
    first, second = variables
    return f'''// Generated exactly by e_model_singular_normalize.py.
// No normalization claim is valid unless this program exits successfully.
LIB "normal.lib";
option(redSB);
ring base = 0,({first},{second}),dp;
poly f = {polynomial};
ideal input_ideal = f;
print("CERT chart={chart}");
print("CERT affine_function_interpretation={interpretation}");
print("CERT source_artifact_sha256={artifact_checksum}");
print("CERT chart_polynomial_sha256={polynomial_checksum}");
print("CERT input_degree="+string(deg(f)));
print("CERT input_size="+string(size(f)));
// H is independently certified irreducible over QQ.  Telling normal.lib
// that the ideal is prime avoids recomputing a costly minimal-prime
// decomposition; the returned normalization is still checked below.
list nor = normal(input_ideal,"withDelta","isPrim");
int component_count = size(nor[1]);
print("CERT normalization_component_count="+string(component_count));
print("BEGIN_MODULE_GENERATORS");
nor[2];
print("END_MODULE_GENERATORS");
print("BEGIN_DELTA_DATA");
nor[3];
print("END_DELTA_DATA");
if (component_count != 1)
{{
  print("BLOCKER expected_one_component");
  exit;
}}
def normalized_ring = nor[1][1];
setring normalized_ring;
print("CERT normalization_ring_activated");
print("CERT norid_size="+string(size(norid)));
print("CERT normap_size="+string(size(normap)));
print("BEGIN_NORID");
norid;
print("END_NORID");
print("BEGIN_NORMAP");
normap;
print("END_NORMAP");
ideal norid_standard_basis = std(norid);
print("CERT norid_standard_basis_size="+string(size(norid_standard_basis)));
print("BEGIN_NORID_STANDARD_BASIS");
norid_standard_basis;
print("END_NORID_STANDARD_BASIS");
print("CERT singular_normalization_finished");
'''


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument(
        "--chart",
        choices=("affine", "Q_nonzero", "B_nonzero"),
        default="affine",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--metadata",
        type=Path,
        help="optional JSON certificate for the generated, not yet executed, input",
    )
    args = parser.parse_args()

    data = json.loads(args.artifact.read_text(encoding="utf-8"))
    terms = data["elliptic_plane_model"]["terms"]
    polynomial, variables, interpretation = polynomial_string(terms, args.chart)
    polynomial_checksum = hashlib.sha256(polynomial.encode()).hexdigest()
    source = singular_source(
        polynomial,
        variables,
        args.chart,
        interpretation,
        data["sha256_without_checksum"],
        polynomial_checksum,
    )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source, encoding="utf-8")
    print(f"generated {args.output}")
    print(f"chart polynomial sha256 {polynomial_checksum}")
    print("status INPUT_GENERATED_NOT_EXECUTED")

    if args.metadata:
        metadata = {
            "schema": 1,
            "status": "INPUT_GENERATED_NOT_EXECUTED",
            "chart": args.chart,
            "variables": list(variables),
            "affine_function_interpretation": interpretation,
            "source_artifact": str(args.artifact),
            "source_artifact_checksum": data["sha256_without_checksum"],
            "chart_polynomial_sha256": polynomial_checksum,
            "singular_input_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "normalization_claim": False,
        }
        args.metadata.parent.mkdir(parents=True, exist_ok=True)
        args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
