"""Negative and optimization-mode tests for the hardened Target A certificate."""

from __future__ import annotations

import ast
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest


HERE = Path(__file__).resolve().parent
ROOT = Path(__file__).resolve().parents[1]
REPOSITORY_ROOT = Path(os.environ.get("CUBOID_REPO_ROOT", ROOT)).resolve()
LOCAL_MODULE_PATH = HERE / "c3_p3_chabauty.py"
MODULE_PATH = (
    LOCAL_MODULE_PATH
    if LOCAL_MODULE_PATH.exists()
    else ROOT / "research/proof_simplification_2/c3_p3_chabauty.py"
)
LOCAL_ARTIFACT_PATH = HERE / "c3_p3_chabauty.json"
ARTIFACT_PATH = (
    LOCAL_ARTIFACT_PATH
    if LOCAL_ARTIFACT_PATH.exists()
    else ROOT / "research/proof_simplification_2/c3_p3_chabauty.json"
)
os.environ.setdefault("CUBOID_REPO_ROOT", str(REPOSITORY_ROOT))
LOCAL_CORRECTED_TARGET_B = (
    HERE.parent / "correct_twist/final_default_repo_venv.json"
)
if LOCAL_CORRECTED_TARGET_B.exists():
    # In the repository the corrected artifact is already at its canonical
    # path.  This exact-pin-preserving override is only for the isolated copy.
    os.environ.setdefault(
        "CUBOID_TARGET_B_ARTIFACT",
        str(LOCAL_CORRECTED_TARGET_B),
    )

SPEC = importlib.util.spec_from_file_location("hardened_target_a", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("cannot load hardened Target A module")
TARGET_A = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = TARGET_A
SPEC.loader.exec_module(TARGET_A)


def artifact_with_checksum(**fields: object) -> tuple[dict[str, object], str]:
    """Return an artifact plus its exact embedded canonical checksum."""

    payload = dict(fields)
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    checksum = hashlib.sha256(canonical).hexdigest()
    payload["sha256_without_checksum"] = checksum
    return payload, checksum


def test_c3_p3_chabauty_certificate_matches_artifact():
    """Retain the original positive canonical-artifact regression test."""

    expected = json.loads(ARTIFACT_PATH.read_text(encoding="utf-8"))
    assert TARGET_A.verify() == expected


def test_source_contains_no_python_assert_statement():
    """Proof gates must remain present when the interpreter is optimized."""

    tree = ast.parse(MODULE_PATH.read_text(encoding="utf-8"))
    assert not any(isinstance(node, ast.Assert) for node in ast.walk(tree))


def test_normal_and_optimized_certificates_are_identical(tmp_path: Path):
    """The complete certificate must be invariant under ``python -O``."""

    normal_output = tmp_path / "normal.json"
    optimized_output = tmp_path / "optimized.json"
    environment = {
        **os.environ,
        "CUBOID_REPO_ROOT": str(REPOSITORY_ROOT),
        "PYTHONDONTWRITEBYTECODE": "1",
    }
    normal = subprocess.run(
        [
            sys.executable,
            str(MODULE_PATH),
            "--output",
            str(normal_output),
        ],
        env=environment,
        text=True,
        capture_output=True,
        check=False,
    )
    optimized = subprocess.run(
        [
            sys.executable,
            "-O",
            str(MODULE_PATH),
            "--output",
            str(optimized_output),
        ],
        env=environment,
        text=True,
        capture_output=True,
        check=False,
    )
    assert normal.returncode == 0, normal.stderr
    assert optimized.returncode == 0, optimized.stderr
    assert normal_output.read_bytes() == optimized_output.read_bytes()


def test_require_and_imported_helper_gate_survive_python_optimized():
    """A false local gate and a corrupt imported output must fail under ``-O``."""

    program = f"""
import importlib.util
import os
import pathlib
import sys
os.environ["CUBOID_REPO_ROOT"] = {str(REPOSITORY_ROOT)!r}
path = pathlib.Path({str(MODULE_PATH)!r})
spec = importlib.util.spec_from_file_location("optimized_negative_target_a", path)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
failures = 0
try:
    module.require(False, "sentinel")
except module.CertificateFailure:
    failures += 1
module.imported_point_divisor = lambda *args: ((1,), (0,))
try:
    module.checked_point_divisor(1, 1, 3)
except module.CertificateFailure:
    failures += 1
raise SystemExit(0 if failures == 2 else 9)
"""
    result = subprocess.run(
        [sys.executable, "-O", "-c", program],
        env={
            **os.environ,
            "PYTHONDONTWRITEBYTECODE": "1",
        },
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr


def test_dependency_rejects_malformed_json(tmp_path: Path):
    """Malformed JSON must fail before any mathematical conclusion is read."""

    path = tmp_path / "broken.json"
    path.write_text('{"schema": 1,', encoding="utf-8")
    contract = TARGET_A.ArtifactContract("0" * 64, status="PASS", target="B")
    with pytest.raises(TARGET_A.CertificateFailure, match="not valid JSON"):
        TARGET_A.checked_artifact("broken.json", contract, root=tmp_path)


def test_dependency_rejects_duplicate_keys(tmp_path: Path):
    """Duplicate metadata keys must not be silently accepted by the JSON parser."""

    path = tmp_path / "duplicate.json"
    path.write_text(
        '{"schema":1,"schema":1,"status":"PASS","target":"B",'
        '"sha256_without_checksum":"' + "0" * 64 + '"}',
        encoding="utf-8",
    )
    contract = TARGET_A.ArtifactContract("0" * 64, status="PASS", target="B")
    with pytest.raises(TARGET_A.CertificateFailure, match="repeats JSON key"):
        TARGET_A.checked_artifact("duplicate.json", contract, root=tmp_path)


def test_dependency_rejects_status_fail_even_with_matching_digest(tmp_path: Path):
    """A self-consistent checksum cannot turn ``status=FAIL`` into a premise."""

    payload, checksum = artifact_with_checksum(
        schema=1,
        status="FAIL",
        target="B",
    )
    path = tmp_path / "status_fail.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    contract = TARGET_A.ArtifactContract(
        checksum,
        status="PASS",
        target="B",
    )
    with pytest.raises(TARGET_A.CertificateFailure, match="not status PASS"):
        TARGET_A.checked_artifact("status_fail.json", contract, root=tmp_path)


@pytest.mark.parametrize(
    "fields, message",
    [
        ({"schema": 2, "status": "PASS", "target": "B"}, "wrong schema"),
        ({"schema": 1, "status": "PASS"}, "wrong target"),
        ({"schema": 1, "status": "PASS", "target": "A"}, "wrong target"),
    ],
)
def test_dependency_rejects_wrong_schema_or_target(
    tmp_path: Path,
    fields: dict[str, object],
    message: str,
):
    """Schema and target are proof inputs, not decorative output fields."""

    payload, checksum = artifact_with_checksum(**fields)
    path = tmp_path / "wrong_contract.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    contract = TARGET_A.ArtifactContract(
        checksum,
        status="PASS",
        target="B",
    )
    with pytest.raises(TARGET_A.CertificateFailure, match=message):
        TARGET_A.checked_artifact("wrong_contract.json", contract, root=tmp_path)


def test_dependency_rejects_recomputed_unpinned_digest(tmp_path: Path):
    """Recomputing an embedded checksum does not satisfy the immutable pin."""

    payload, checksum = artifact_with_checksum(
        schema=1,
        status="PASS",
        target="B",
        altered=True,
    )
    path = tmp_path / "unpinned.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    assert checksum != "f" * 64
    contract = TARGET_A.ArtifactContract(
        "f" * 64,
        status="PASS",
        target="B",
    )
    with pytest.raises(TARGET_A.CertificateFailure, match="not the pinned version"):
        TARGET_A.checked_artifact("unpinned.json", contract, root=tmp_path)


def test_imported_valuation_output_is_independently_checked(monkeypatch):
    """A plausible-looking but wrong imported valuation pair must be rejected."""

    monkeypatch.setattr(
        TARGET_A,
        "imported_valuation_and_unit",
        lambda value, prime: (0, 1),
    )
    with pytest.raises(TARGET_A.CertificateFailure, match="mismatch"):
        TARGET_A.checked_valuation_and_unit(3, 3)


def test_imported_reduced_divisors_are_validated(monkeypatch):
    """A malformed finite divisor set must not reach the group-order proof."""

    monkeypatch.setattr(
        TARGET_A,
        "imported_all_reduced_divisors",
        lambda prime: {((1,), (0,)), ((0,), (0,))},
    )
    with pytest.raises(TARGET_A.CertificateFailure):
        TARGET_A.checked_all_reduced_divisors(3, 22)


def test_universal_tail_lemmas_extend_far_beyond_old_cutoff():
    """The instantiated lemmas work at arbitrary large degrees."""

    certificate = TARGET_A.certify_universal_integer_lemmas()
    assert certificate["status"] == "PASS"
    assert TARGET_A.universal_v3_le_n_minus_2(3**100)
    assert TARGET_A.universal_v3_le_n_minus_4(10**50)


def test_h0_certificate_is_universal_not_truncated():
    """The lattice step explicitly certifies the full ``3Z_3`` disk."""

    a, x = TARGET_A.sp.symbols("a x")
    curve = 4 * a**5 - 8 * a**2 + 5 * a
    certificate = TARGET_A.certify_h0_unit(curve, a, x, 1)
    assert certificate["status"] == "PASS"
    assert certificate["domain"] == "all x in 3*Z_3"
    assert "every n>=2" in certificate["tail"]


def test_canonical_certificate_retains_shorter_rank_contract():
    """Canonical Target A uses the shorter already-validated rank premise."""

    payload = TARGET_A.verify()
    assert payload["rank_inputs"]["genus_two_rank_source"] == "legacy"
    selected = payload["rank_inputs"]["dependency_contracts"][-1]
    assert selected == {
        "schema": 1,
        "status": "PASS",
        "target": "rank Jac(D+)(Q)=1 and D,T independent modulo 2",
        "path": TARGET_A.OLD_SCHAEFER_STOLL_PATH,
        "checksum": TARGET_A.OLD_SCHAEFER_STOLL_CHECKSUM,
        "legacy_metadata_adapter": True,
    }


def test_richelot_rank_source_is_explicit_only():
    """The larger Richelot alternative remains available when named."""

    _, _, _, contracts = TARGET_A.checked_dependencies("richelot")
    selected = contracts[-1]
    assert selected["path"] == TARGET_A.TARGET_B_PATH
    assert selected["legacy_metadata_adapter"] is False


def test_richelot_rank_source_cannot_overwrite_canonical_artifact():
    """Richelot comparison mode must require a separately named transcript."""

    before = ARTIFACT_PATH.read_bytes()
    result = subprocess.run(
        [sys.executable, str(MODULE_PATH), "--rank-source", "richelot"],
        cwd=REPOSITORY_ROOT,
        env={
            **os.environ,
            "CUBOID_REPO_ROOT": str(REPOSITORY_ROOT),
            "PYTHONDONTWRITEBYTECODE": "1",
        },
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 2
    assert "requires an explicit noncanonical --output" in result.stderr
    assert ARTIFACT_PATH.read_bytes() == before
