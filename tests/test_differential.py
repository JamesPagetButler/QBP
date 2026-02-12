"""
Phase 4d: Differential Testing — Pytest wrapper

Parametrized tests comparing Python qphysics.py against Lean oracle predictions.
Each oracle test case becomes a separate pytest test for clear failure reporting.

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

import qphysics  # noqa: E402

ORACLE_PATH = project_root / "tests" / "oracle_predictions.json"
TOLERANCE = 1e-6


def load_oracle_cases() -> list[dict]:
    """Load oracle test cases from JSON."""
    with open(ORACLE_PATH) as f:
        return json.load(f)


# Parametrize over all oracle test cases
oracle_cases = load_oracle_cases()


@pytest.mark.parametrize(
    "case",
    oracle_cases,
    ids=[c["label"] for c in oracle_cases],
)
def test_prob_up_matches_oracle(case: dict) -> None:
    """P(+) from Python matches Lean oracle within tolerance."""
    theta = case["theta_rad"]
    psi = qphysics.create_tilted_state(theta)
    exp_val = qphysics.expectation_value(psi, qphysics.SPIN_Z)
    python_prob_up = (1 + exp_val) / 2.0

    assert abs(python_prob_up - case["prob_up"]) <= TOLERANCE, (
        f"prob_up divergence at theta={theta:.6f}: "
        f"oracle={case['prob_up']:.10f} python={python_prob_up:.10f}"
    )


@pytest.mark.parametrize(
    "case",
    oracle_cases,
    ids=[c["label"] for c in oracle_cases],
)
def test_prob_down_matches_oracle(case: dict) -> None:
    """P(-) from Python matches Lean oracle within tolerance."""
    theta = case["theta_rad"]
    psi = qphysics.create_tilted_state(theta)
    exp_val = qphysics.expectation_value(psi, qphysics.SPIN_Z)
    python_prob_down = (1 - exp_val) / 2.0

    assert abs(python_prob_down - case["prob_down"]) <= TOLERANCE, (
        f"prob_down divergence at theta={theta:.6f}: "
        f"oracle={case['prob_down']:.10f} python={python_prob_down:.10f}"
    )


@pytest.mark.parametrize(
    "case",
    oracle_cases,
    ids=[c["label"] for c in oracle_cases],
)
def test_expectation_matches_oracle(case: dict) -> None:
    """Expectation value from Python matches Lean oracle within tolerance."""
    theta = case["theta_rad"]
    psi = qphysics.create_tilted_state(theta)
    python_exp = qphysics.expectation_value(psi, qphysics.SPIN_Z)

    assert abs(python_exp - case["expectation"]) <= TOLERANCE, (
        f"expectation divergence at theta={theta:.6f}: "
        f"oracle={case['expectation']:.10f} python={python_exp:.10f}"
    )


class TestBugDetection:
    """Verify the differential testing harness detects intentional bugs.

    These tests use unittest.mock.patch to inject buggy implementations
    into qphysics, then run the actual differential harness to confirm
    it reports divergences. This validates the testing infrastructure itself.
    """

    def test_harness_catches_wrong_expectation(self) -> None:
        """Patch expectation_value to return wrong sign — harness must detect it."""
        sys.path.insert(0, str(project_root / "scripts"))
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
        sys.path.insert(0, str(project_root / "scripts"))
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
        sys.path.insert(0, str(project_root / "scripts"))
        from differential_test import run_differential_tests

        total, divergences, _ = run_differential_tests(tolerance=1e-6)

        assert (
            divergences == 0
        ), f"Expected 0 divergences with correct code, got {divergences}/{total}"
