#!/usr/bin/env sage -python
"""Proof-mode Sage certificate for the Mordell--Weil basis of candidate E1.

This script concerns only the independently proved candidate curve

    E1: y^2 = x^3 - 5*x + 4.

It does not identify E1 with the reciprocal cuboid quotient.  Its purpose is
to certify whether P=(0,2), used in the elementary rank proof, generates the
free part rather than merely a finite-index subgroup.
"""

from __future__ import annotations

import json
import platform
from pathlib import Path

from sage.all import EllipticCurve, QQ, proof, version  # type: ignore


OUTPUT = Path(__file__).with_name("sage_candidate_mw_basis.json")


def main() -> None:
    proof.all(True)
    E = EllipticCurve(QQ, [0, 0, 0, -5, 4])
    P = E(0, 2)
    T = E(1, 0)

    rank_bounds = E.rank_bounds()
    rank = E.rank(proof=True)
    generators = E.gens(proof=True)
    generators_certain = E.gens_certain()
    saturated_points, saturation_index, saturation_regulator = E.saturation(
        [P], max_prime=-1
    )

    if rank_bounds != (1, 1) or rank != 1:
        raise AssertionError("proof-mode rank certificate is not exactly one")
    if not generators_certain:
        raise AssertionError("Sage does not certify its generator list")
    if saturation_index != 1:
        raise AssertionError("P=(0,2) does not generate a saturated subgroup")
    if E.torsion_subgroup().order() != 2 or 2 * T != E(0):
        raise AssertionError("unexpected rational torsion")

    payload = {
        "schema": 1,
        "logical_scope": (
            "Proof-mode arithmetic of candidate E1 only; no identification "
            "with the cuboid quotient is asserted."
        ),
        "sage_version": version(),
        "python_version": platform.python_version(),
        "curve_ainvs": [str(value) for value in E.a_invariants()],
        "rank_bounds": [int(value) for value in rank_bounds],
        "rank_proof_true": int(rank),
        "gens_proof_true": [str(point) for point in generators],
        "gens_certain": bool(generators_certain),
        "P": str(P),
        "P_full_saturation": {
            "points": [str(point) for point in saturated_points],
            "index": int(saturation_index),
            "regulator": str(saturation_regulator),
            "max_prime": -1,
        },
        "torsion": str(E.torsion_subgroup()),
    }
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print("CERT rank_bounds =", rank_bounds, flush=True)
    print("CERT rank_proof_true =", rank, flush=True)
    print("CERT gens_proof_true =", generators, flush=True)
    print("CERT gens_certain =", generators_certain, flush=True)
    print("CERT saturation_index_P =", saturation_index, flush=True)
    print("CERT output =", OUTPUT, flush=True)


if __name__ == "__main__":
    main()
