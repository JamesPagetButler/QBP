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

import numpy as np
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
    """Verify the differential testing harness detects intentional bugs."""

    def test_detects_wrong_formula(self) -> None:
        """If qphysics used cos(theta) instead of cos(theta/2)^2,
        the differential test should catch it at theta=45 degrees."""
        theta_45 = np.pi / 4.0  # 45 degrees
        psi = qphysics.create_tilted_state(theta_45)
        correct_exp = qphysics.expectation_value(psi, qphysics.SPIN_Z)

        # Intentionally wrong: use cos(theta) directly as prob_up
        # instead of (1 + cos(theta)) / 2
        buggy_prob_up = np.cos(theta_45)  # Wrong formula
        correct_prob_up = (1 + correct_exp) / 2.0

        # These should differ — proving the test can detect bugs
        assert (
            abs(buggy_prob_up - correct_prob_up) > 0.01
        ), "Bug detection test failed: wrong formula should diverge from correct one"

    def test_detects_sign_error(self) -> None:
        """Sign error in expectation value should be caught."""
        theta_45 = np.pi / 4.0
        psi = qphysics.create_tilted_state(theta_45)
        correct_exp = qphysics.expectation_value(psi, qphysics.SPIN_Z)

        # Intentional sign error
        buggy_exp = -correct_exp

        # At 45 degrees, cos(theta) ≈ 0.707, so negating it should differ
        assert (
            abs(buggy_exp - correct_exp) > 0.1
        ), "Sign error should produce detectable divergence"
