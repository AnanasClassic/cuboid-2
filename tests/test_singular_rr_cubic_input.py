from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "research" / "arithmetic_geometry" / "e_model_singular_rr_cubic.py"
FROZEN_INPUT = ROOT / "research" / "arithmetic_geometry" / "e_model_singular_rr_cubic.sing"
FROZEN_METADATA = (
    ROOT / "research" / "arithmetic_geometry" / "e_model_singular_rr_cubic_input.json"
)
CHECKSUM_MANIFEST = (
    ROOT
    / "research"
    / "arithmetic_geometry"
    / "e_model_singular_transport_checksums.sha256"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_frozen_singular_rr_input_is_reproducible(tmp_path: Path) -> None:
    generated = tmp_path / "rr.sing"
    metadata = tmp_path / "rr.json"
    subprocess.run(
        [
            sys.executable,
            str(GENERATOR),
            "--output",
            str(generated),
            "--metadata",
            str(metadata),
        ],
        cwd=ROOT,
        check=True,
    )
    assert generated.read_bytes() == FROZEN_INPUT.read_bytes()

    frozen = json.loads(FROZEN_METADATA.read_text(encoding="utf-8"))
    fresh = json.loads(metadata.read_text(encoding="utf-8"))
    assert fresh == frozen
    assert frozen["status"] == "INPUT_GENERATED_NOT_EXECUTED"
    assert frozen["normalization_claim"] is False
    assert frozen["weierstrass_claim"] is False
    assert frozen["singular_random_seed_required"] == 1
    assert frozen["singular_input_sha256"] == sha256(FROZEN_INPUT)


def test_singular_rr_input_contains_all_certificate_guards() -> None:
    source = FROZEN_INPUT.read_text(encoding="utf-8")
    required = [
        "rational_point_not_smooth",
        "dim_L2P_not_2",
        "dim_L3P_not_3",
        "source_base_locus_not_projectively_finite",
        "image_not_principal_plane_cubic",
        "inverse_does_not_land_on_H",
        "target_projective_composition_failed",
        "source_projective_composition_failed",
        "affine_denominator_identically_zero",
        "inverse_base_locus_not_projectively_finite",
        "affine_denominator_divisor_not_projectively_finite",
        "q_A_roundtrip_denominator_identically_zero",
        "CERT q_A_projective_roundtrip=OK",
        'system("--random",1)',
        'system("--version")',
    ]
    for marker in required:
        assert marker in source

    assert "FunctionField" not in source
    assert "maximal_order" not in source


def test_optional_normalization_cross_check_uses_norid_and_normap(tmp_path: Path) -> None:
    generated = tmp_path / "normal_rr.sing"
    metadata = tmp_path / "normal_rr.json"
    subprocess.run(
        [
            sys.executable,
            str(GENERATOR),
            "--include-affine-normalization-cross-check",
            "--output",
            str(generated),
            "--metadata",
            str(metadata),
        ],
        cwd=ROOT,
        check=True,
    )
    source = generated.read_text(encoding="utf-8")
    assert 'normal(affineInput,"withDelta","isPrim")' in source
    assert "map projectiveToNormalization = RP2,normap[1],normap[2],1" in source
    assert "CERT affine_normap_q_A_roundtrip=OK" in source
    assert "BLOCKER cubic_does_not_vanish_through_normap" in source
    data = json.loads(metadata.read_text(encoding="utf-8"))
    assert data["includes_affine_normalization_cross_check"] is True


def test_frozen_transport_checksum_manifest() -> None:
    for line in CHECKSUM_MANIFEST.read_text(encoding="utf-8").splitlines():
        expected, relative = line.split("  ", 1)
        assert sha256(ROOT / relative) == expected
