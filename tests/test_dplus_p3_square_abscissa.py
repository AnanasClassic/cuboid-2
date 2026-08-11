"""Regression and negative tests for the direct D+ square-abscissa proof."""

from __future__ import annotations

import ast
import json
from pathlib import Path
import subprocess
import sys

import pytest

from research.proof_simplification_3 import dplus_p3_square_abscissa as direct


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "research/proof_simplification_3/dplus_p3_square_abscissa.py"
ARTIFACT = SCRIPT.with_suffix(".json")


def test_certificate_matches_canonical_artifact():
    """The checked-in JSON is the exact current theorem output."""

    expected = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert direct.verify() == expected
    assert expected["status"] == "PASS"
    assert expected["success_level"] == "B"


def test_source_contains_no_optimization_sensitive_assert():
    """Every executable proof gate must survive python -O."""

    tree = ast.parse(SCRIPT.read_text(encoding="utf-8"))
    assert not any(isinstance(node, ast.Assert) for node in ast.walk(tree))


def test_normal_and_optimized_artifacts_are_identical(tmp_path: Path):
    """Optimized Python cannot remove a certificate obligation."""

    normal = tmp_path / "normal.json"
    optimized = tmp_path / "optimized.json"
    common = [str(SCRIPT), "--output"]
    first = subprocess.run(
        [sys.executable, *common, str(normal)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    second = subprocess.run(
        [sys.executable, "-O", *common, str(optimized)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert first.returncode == 0, first.stderr
    assert second.returncode == 0, second.stderr
    assert normal.read_bytes() == optimized.read_bytes()


def test_malformed_rank_artifact_is_rejected(tmp_path: Path):
    """Rank metadata is a pinned premise, not a best-effort input."""

    broken = tmp_path / "rank.json"
    broken.write_text('{"schema":1,', encoding="utf-8")
    with pytest.raises(direct.CertificateFailure, match="not valid JSON"):
        direct.checked_rank_artifact(broken)


def test_recomputed_but_unpinned_rank_artifact_is_rejected(tmp_path: Path):
    """A forged self-consistent digest cannot replace the pinned descent."""

    payload = {"schema": 1, "rank": 1}
    import hashlib

    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    payload["sha256_without_checksum"] = hashlib.sha256(encoded).hexdigest()
    path = tmp_path / "rank.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(direct.CertificateFailure, match="not the pinned version"):
        direct.checked_rank_artifact(path)


def test_p7_saturation_cannot_be_silently_dropped():
    """The unknown Mordell-Weil index still requires the small p=7 lemma."""

    with pytest.raises(direct.CertificateFailure, match="requires the p=7"):
        direct.verify(use_p7_saturation=False)


def test_a_is_not_accepted_as_zero_disk_uniformizer():
    """The Weierstrass disk must use R as its local parameter."""

    with pytest.raises(direct.CertificateFailure, match="valid uniformizer"):
        direct.certify_zero_disk(parameter="a")


def test_truncated_infinity_tail_is_not_accepted(monkeypatch):
    """Low-degree coefficients without the universal tail theorem do not prove uniqueness."""

    expected = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    annihilator = expected["D_plus_logarithm"]["annihilator"]
    monkeypatch.setattr(
        direct.exact,
        "certify_universal_integer_lemmas",
        lambda: {"status": "FAIL"},
    )
    with pytest.raises(direct.CertificateFailure, match="tail proof failed"):
        direct.certify_infinity_disk(annihilator)


def test_non_square_3adic_unit_class_is_rejected():
    """The a=2 residue disks exist on D+ but cannot have square abscissa."""

    with pytest.raises(direct.CertificateFailure, match="cannot reduce to 2"):
        direct.square_unit_residue(2)
    classification = direct.certify_square_disk_classification()
    assert classification["non_square_unit_disks_excluded"] == [
        "(2,1)",
        "(2,-1)",
    ]


def test_all_four_known_points_are_explicit():
    """The theorem output includes infinity and all three affine points."""

    result = direct.verify()
    assert result["known_points_checked"] == [
        "infinity",
        "(0,0)",
        "(1,1)",
        "(1,-1)",
    ]
