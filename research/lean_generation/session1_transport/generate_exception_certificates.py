#!/usr/bin/env python3
"""Generate exact sparse Bézout certificates for transport exceptions.

The regular inverse reconstructs ``x=-B/A``.  Two exceptional calculations
remain:

* ``C8=A=0`` for the inverse denominator;
* ``C8=352225*A+576*B=0`` for the removed forward base ``x=352225/576``.

Both are univariate gcd computations in ``V`` over ``QQ(U)``.  Clearing the
coefficient denominators gives exact integer Bézout identities.  The emitted
Lean file stores only sparse coefficient lists; Lean's transparent sparse
normalizer checks the two identities independently.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import sympy as sp

from research.arithmetic_geometry.low_degree_transport import U, V, load_c8
from research.lean_generation.session1_transport.generate_transport_certificates import (
    SOURCE,
    lean_sparse_string,
    load_sparse,
    sparse,
)


ROOT = Path(__file__).resolve().parents[3]
OUTPUT = Path(__file__).with_name("transport_exception_certificates.json")
LEAN_OUTPUT = (
    ROOT
    / "lean"
    / "Cuboid2"
    / "QuadraticReduction"
    / "TransportExceptionData.lean"
)


def bezout_certificate(
    left: sp.Expr, right: sp.Expr
) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Return integral ``P,Q,R`` with ``P*left+Q*right=R(U)``."""

    coefficient_field = sp.QQ.frac_field(U)
    p, q, gcd = sp.gcdex(
        sp.Poly(left, V, domain=coefficient_field),
        sp.Poly(right, V, domain=coefficient_field),
    )
    assert gcd == 1
    denominators = [
        sp.denom(coefficient)
        for polynomial in (p, q)
        for coefficient in polynomial.all_coeffs()
    ]
    common = sp.lcm(denominators)
    p_integer = sp.cancel(p.as_expr() * common)
    q_integer = sp.cancel(q.as_expr() * common)
    resultant_factor = sp.Poly(common, U, domain=sp.ZZ).as_expr()
    # Supplying the domain verifies that clearing really left integral
    # coefficients (the expressions otherwise retain a QQ domain tag).
    p_integer = sp.Poly(p_integer, U, V, domain=sp.ZZ).as_expr()
    q_integer = sp.Poly(q_integer, U, V, domain=sp.ZZ).as_expr()
    assert sp.expand(
        p_integer * left + q_integer * right - resultant_factor
    ) == 0
    return p_integer, q_integer, resultant_factor


def verify() -> dict[str, object]:
    """Compute both exception certificates and attach a stable checksum."""

    source = json.loads(SOURCE.read_text(encoding="utf-8"))
    inverse = source["inverse_subresultant"]
    a_coefficient = load_sparse(inverse["A_terms"], (U, V))
    b_coefficient = load_sparse(inverse["B_terms"], (U, V))
    c8, _ = load_c8()
    removed_linear = sp.expand(352225 * a_coefficient + 576 * b_coefficient)

    a_left, a_right, a_factor = bezout_certificate(c8, a_coefficient)
    r_left, r_right, r_factor = bezout_certificate(c8, removed_linear)

    payload: dict[str, object] = {
        "schema": 1,
        "status": "EXACT-INTEGER-BEZOUT-CERTIFICATES",
        "C8_terms": sparse(c8, (U, V)),
        "A_exception": {
            "left_terms": sparse(a_left, (U, V)),
            "right_terms": sparse(a_right, (U, V)),
            "factor_terms": sparse(a_factor, (U, V)),
            "factorization": str(sp.factor(a_factor)),
        },
        "removed_linear_terms": sparse(removed_linear, (U, V)),
        "removed_exception": {
            "left_terms": sparse(r_left, (U, V)),
            "right_terms": sparse(r_right, (U, V)),
            "factor_terms": sparse(r_factor, (U, V)),
            "factorization": str(sp.factor(r_factor)),
        },
    }
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(canonical).hexdigest()
    return payload


def write_lean_data(payload: dict[str, object]) -> None:
    """Write compact parsed sparse lists consumed by the Lean checker."""

    definitions = [
        ("transportExceptionC8Terms", payload["C8_terms"]),
        (
            "transportExceptionABezoutLeftTerms",
            payload["A_exception"]["left_terms"],
        ),
        (
            "transportExceptionABezoutRightTerms",
            payload["A_exception"]["right_terms"],
        ),
        (
            "transportExceptionAFactorTerms",
            payload["A_exception"]["factor_terms"],
        ),
        (
            "transportExceptionRemovedLinearTerms",
            payload["removed_linear_terms"],
        ),
        (
            "transportExceptionRemovedBezoutLeftTerms",
            payload["removed_exception"]["left_terms"],
        ),
        (
            "transportExceptionRemovedBezoutRightTerms",
            payload["removed_exception"]["right_terms"],
        ),
        (
            "transportExceptionRemovedFactorTerms",
            payload["removed_exception"]["factor_terms"],
        ),
    ]
    lines = [
        "import Cuboid2.QuadraticReduction.TransportCertificateData",
        "",
        "/-!",
        "# Generated exact exceptional-transport coefficient data",
        "",
        "Generated by",
        "`research/lean_generation/session1_transport/generate_exception_certificates.py`.",
        f"Certificate checksum: `{payload['sha256_without_checksum']}`.",
        "-/",
        "",
        "namespace Cuboid2",
        "",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 100000",
        "",
    ]
    for name, records in definitions:
        lines.extend(
            [
                f"/-- Generated sparse terms for `{name}`. -/",
                f"def {name} : List TransportUVTerm :=",
                f'  transportParseUVTerms "{lean_sparse_string(records)}"',
                "",
            ]
        )
    lines.extend(["end Cuboid2", ""])
    LEAN_OUTPUT.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    """Generate JSON and Lean data for both exception certificates."""

    payload = verify()
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    write_lean_data(payload)
    print("wrote", OUTPUT)
    print("wrote", LEAN_OUTPUT)
    print("checksum", payload["sha256_without_checksum"])


if __name__ == "__main__":
    main()
