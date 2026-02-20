"""
Phase 4d: Differential Testing — Pytest wrapper

Parametrized tests comparing Python qphysics.py against Lean oracle predictions.
Each oracle test case becomes a separate pytest test for clear failure reporting.

Supports both xz-plane cases (theta_rad) and general 3D cases (theta_s, phi_s,
theta_o, phi_o) added by #211.

Also includes a bug-detection test that verifies the harness catches intentional
formula errors (validates the testing infrastructure itself).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

# Add project root for imports
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))
sys.path.insert(0, str(project_root / "scripts"))

import qphysics  # noqa: E402
from differential_test import compute_python_prediction  # noqa: E402

ORACLE_PATH = project_root / "tests" / "oracle_predictions.json"
TOLERANCE = 1e-6


def load_oracle_cases() -> list[dict]:
    """Load oracle test cases from JSON."""
    with open(ORACLE_PATH) as f:
        return json.load(f)


# Parametrize over all oracle test cases, split by experiment type
oracle_cases = load_oracle_cases()
spin_cases = [c for c in oracle_cases if c.get("experiment") != "03"]
doubleslit_cases = [c for c in oracle_cases if c.get("experiment") == "03"]


# --- Spin measurement tests (Experiments 01, 01b, edge, 3d) ---


@pytest.mark.parametrize(
    "case",
    spin_cases,
    ids=[c["label"] for c in spin_cases],
)
def test_prob_up_matches_oracle(case: dict) -> None:
    """P(+) from Python matches Lean oracle within tolerance."""
    python = compute_python_prediction(case)

    assert abs(python["prob_up"] - case["prob_up"]) <= TOLERANCE, (
        f"prob_up divergence for {case['label']}: "
        f"oracle={case['prob_up']:.10f} python={python['prob_up']:.10f}"
    )


@pytest.mark.parametrize(
    "case",
    spin_cases,
    ids=[c["label"] for c in spin_cases],
)
def test_prob_down_matches_oracle(case: dict) -> None:
    """P(-) from Python matches Lean oracle within tolerance."""
    python = compute_python_prediction(case)

    assert abs(python["prob_down"] - case["prob_down"]) <= TOLERANCE, (
        f"prob_down divergence for {case['label']}: "
        f"oracle={case['prob_down']:.10f} python={python['prob_down']:.10f}"
    )


@pytest.mark.parametrize(
    "case",
    spin_cases,
    ids=[c["label"] for c in spin_cases],
)
def test_expectation_matches_oracle(case: dict) -> None:
    """Expectation value from Python matches Lean oracle within tolerance."""
    python = compute_python_prediction(case)

    assert abs(python["expectation"] - case["expectation"]) <= TOLERANCE, (
        f"expectation divergence for {case['label']}: "
        f"oracle={case['expectation']:.10f} python={python['expectation']:.10f}"
    )


# --- DoubleSlit tests (Experiment 03) ---


@pytest.mark.parametrize(
    "case",
    doubleslit_cases,
    ids=[c["label"] for c in doubleslit_cases],
)
def test_doubleslit_matches_oracle(case: dict) -> None:
    """DoubleSlit Python computation matches Lean oracle within tolerance."""
    python = compute_python_prediction(case)

    for field, python_val in python.items():
        oracle_val = case[field]
        assert abs(python_val - oracle_val) <= TOLERANCE, (
            f"{field} divergence for {case['label']}: "
            f"oracle={oracle_val:.10f} python={python_val:.10f}"
        )


class TestBugDetection:
    """Verify the differential testing harness detects intentional bugs.

    These tests use unittest.mock.patch to inject buggy implementations
    into qphysics, then run the actual differential harness to confirm
    it reports divergences. This validates the testing infrastructure itself.
    """

    def test_harness_catches_wrong_expectation(self) -> None:
        """Patch expectation_value to return wrong sign — harness must detect it."""
        from differential_test import run_differential_tests

        original = qphysics.expectation_value

        def buggy_expectation(psi, obs):
            return -original(psi, obs)  # Sign flip

        with patch.object(qphysics, "expectation_value", side_effect=buggy_expectation):
            total, divergences, details = run_differential_tests(tolerance=1e-6)

        # Harness should detect divergences at non-trivial angles
        assert divergences > 0, (
            "Harness failed to detect sign-flipped expectation_value. "
            f"Ran {total} comparisons but found 0 divergences."
        )

    def test_harness_catches_wrong_state_prep(self) -> None:
        """Patch create_tilted_state to use wrong angle — harness must detect it."""
        from differential_test import run_differential_tests

        original_create = qphysics.create_tilted_state

        def buggy_create(theta):
            return original_create(theta + 0.5)  # Offset angle by 0.5 rad

        with patch.object(qphysics, "create_tilted_state", side_effect=buggy_create):
            total, divergences, details = run_differential_tests(tolerance=1e-6)

        assert divergences > 0, (
            "Harness failed to detect angle-offset bug in create_tilted_state. "
            f"Ran {total} comparisons but found 0 divergences."
        )

    def test_harness_passes_with_correct_code(self) -> None:
        """Unpatched qphysics should produce 0 divergences (sanity check)."""
        from differential_test import run_differential_tests

        total, divergences, _ = run_differential_tests(tolerance=1e-6)

        assert (
            divergences == 0
        ), f"Expected 0 divergences with correct code, got {divergences}/{total}"

    # --- DoubleSlit bug detection (Experiment 03) ---

    def test_harness_catches_coupling_sign_flip(self) -> None:
        """Flip a sign in coupling_decomposition — harness must detect it."""
        from differential_test import run_differential_tests

        original = qphysics.coupling_decomposition

        def buggy_coupling(U0, U1, a0, b0, a1, b1):
            result = original(U0, U1, a0, b0, a1, b1)
            result["re"] = U0 * a0 + U1 * a1  # Bug: + instead of -
            return result

        with patch.object(
            qphysics, "coupling_decomposition", side_effect=buggy_coupling
        ):
            total, divergences, details = run_differential_tests(tolerance=1e-6)

        coupling_divs = [d for d in details if "coupling" in d["label"]]
        assert len(coupling_divs) > 0, (
            "Harness failed to detect sign-flipped coupling_decomposition. "
            f"Ran {total} comparisons but found 0 coupling divergences."
        )

    def test_harness_catches_visibility_inversion(self) -> None:
        """Swap numerator terms in visibility — harness must detect it."""
        from differential_test import run_differential_tests

        def buggy_visibility(Imax, Imin):
            return (Imin - Imax) / (Imax + Imin)  # Bug: swapped numerator

        with patch.object(qphysics, "visibility", side_effect=buggy_visibility):
            total, divergences, details = run_differential_tests(tolerance=1e-6)

        vis_divs = [d for d in details if "visibility" in d["label"]]
        assert len(vis_divs) > 0, (
            "Harness failed to detect inverted visibility formula. "
            f"Ran {total} comparisons but found 0 visibility divergences."
        )

    def test_harness_catches_decay_constant_wrong_op(self) -> None:
        """Use addition instead of multiplication in decay_constant — harness must detect it."""
        from differential_test import run_differential_tests

        def buggy_decay(U1, d):
            return U1 + d  # Bug: + instead of *

        with patch.object(qphysics, "decay_constant", side_effect=buggy_decay):
            total, divergences, details = run_differential_tests(tolerance=1e-6)

        decay_divs = [d for d in details if "decay_constant" in d["label"]]
        assert len(decay_divs) > 0, (
            "Harness failed to detect wrong operator in decay_constant. "
            f"Ran {total} comparisons but found 0 decay_constant divergences."
        )
