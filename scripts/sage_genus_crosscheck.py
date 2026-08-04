#!/usr/bin/env python3
"""Independent exact genus cross-check using the degree-eight presentation.

The main Sage probe views H as a degree-ten polynomial in A over QQ(q).  This
script swaps the variables, makes the degree-eight function-field presentation
monic and integral with explicit isomorphisms, and computes the genus there.
"""

from __future__ import annotations

import json
import time
from pathlib import Path

from sage.all import FunctionField, PolynomialRing, QQ, ZZ, version  # type: ignore


ROOT = Path(__file__).resolve().parents[1]


def cert(label: str, value) -> None:
    print(f"CERT {label} = {value}", flush=True)


def main() -> None:
    started = time.monotonic()
    cert("sage_version", version())
    artifact = json.loads(
        (ROOT / "artifacts" / "genus4_quotient.json").read_text(encoding="utf-8")
    )

    K = FunctionField(QQ, "A")
    A = K.gen()
    R = PolynomialRing(K, "q")
    q = R.gen()
    H = R(0)
    for term in artifact["elliptic_plane_model"]["terms"]:
        q_power, a_power = term["powers"]
        H += ZZ(term["coefficient"]) * q**q_power * A**a_power

    cert("degree_over_QQ_A", H.degree())
    cert("irreducible_over_QQ_A", H.is_irreducible())
    if H.degree() != 8 or not H.is_irreducible():
        raise AssertionError("unexpected degree-eight function-field presentation")

    L = K.extension(H, "q_original")
    M, from_M, to_M = L.monic_integral_model("beta")
    cert("monic_integral_polynomial", M.polynomial())
    if not M.polynomial().is_monic():
        raise AssertionError("monic_integral_model did not return a monic equation")
    if from_M(to_M(L.gen())) != L.gen():
        raise AssertionError("extension-generator map does not round-trip")
    if from_M(to_M(L(L.base_field().gen()))) != L(L.base_field().gen()):
        raise AssertionError("base-generator map does not round-trip")
    cert("isomorphism_roundtrip", "OK")

    genus = M.genus()
    cert("normalization_genus", genus)
    if genus != 1:
        raise AssertionError("the reciprocal quotient normalization must have genus 1")
    cert("elapsed_seconds", round(time.monotonic() - started, 3))


if __name__ == "__main__":
    main()
