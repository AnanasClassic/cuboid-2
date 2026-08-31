#!/usr/bin/env python3
"""Compare the independent trace with the original external `11D` calculation."""

from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

import sympy as sp


REPOSITORY_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPOSITORY_ROOT))

from research.proof_simplification_2.c3_p3_chabauty import (  # noqa: E402
    multiple_11D_data,
)

from generate_dplus_cantor import generate  # noqa: E402


DIRECT_DPLUS_ARTIFACT = (
    REPOSITORY_ROOT
    / "research/proof_simplification_3/dplus_p3_square_abscissa.json"
)


def sympy_coefficients(
    value: sp.Expr, variable: sp.Symbol
) -> tuple[Fraction, ...]:
    """Convert a rational SymPy polynomial to low-to-high exact coefficients."""

    polynomial = sp.Poly(value, variable, domain=sp.QQ)
    return tuple(
        Fraction(int(coefficient.p), int(coefficient.q))
        for coefficient in reversed(polynomial.all_coeffs())
    )


def encoded_coefficients(values: object) -> tuple[Fraction, ...]:
    """Decode one coefficient array from the canonical trace payload."""

    if not isinstance(values, list) or not all(
        isinstance(value, str) for value in values
    ):
        raise RuntimeError("malformed coefficient array in generated trace")
    return tuple(Fraction(value) for value in values)


def main() -> None:
    """Fail unless the sources and direct artifact agree on the same `11D`."""

    variable = sp.Symbol("a")
    external_u, external_v, metadata = multiple_11D_data()
    payload = generate()
    final = payload.get("final")
    if not isinstance(final, dict):
        raise RuntimeError("generated trace has no final pair")
    if (
        sympy_coefficients(external_u, variable)
        != encoded_coefficients(final.get("u"))
        or sympy_coefficients(external_v, variable)
        != encoded_coefficients(final.get("v"))
    ):
        raise RuntimeError("external and generated `11D` Mumford pairs differ")
    if metadata.get("multiple") != "11*D":
        raise RuntimeError("external source returned unexpected multiple metadata")

    direct_artifact = json.loads(DIRECT_DPLUS_ARTIFACT.read_text(encoding="utf-8"))
    direct_checksum = direct_artifact.pop("sha256_without_checksum", None)
    direct_canonical = json.dumps(
        direct_artifact, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    if hashlib.sha256(direct_canonical).hexdigest() != direct_checksum:
        raise RuntimeError("direct D+ artifact checksum does not verify")
    direct_logarithm = direct_artifact.get("D_plus_logarithm")
    if (
        not isinstance(direct_logarithm, dict)
        or direct_logarithm.get("multiple_11D") != metadata
    ):
        raise RuntimeError("direct D+ artifact uses different `11D` metadata")
    print("external source and direct D+ artifact `11D` agreement: PASS")


if __name__ == "__main__":
    main()
