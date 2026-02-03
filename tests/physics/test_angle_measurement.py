# tests/physics/test_angle_measurement.py
"""
Physics validation tests for angle-dependent spin measurements.

These tests validate the quantum mechanical prediction:
P(+) = (1 + cos(theta))/2

where P(+) is the probability of measuring spin-up along an axis
at angle theta from the particle's spin direction.
"""

import numpy as np
import pytest
import sys
import os

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src import qphysics


class TestAngleDependentMeasurement:
    """Test suite for angle-dependent measurement probabilities."""

    NUM_PARTICLES = 100000
    SIGMA_THRESHOLD = 3.0  # Maximum allowed deviation in standard deviations

    def _calculate_deviation_sigma(self, measured_prob, expected_prob, n):
        """Calculate deviation from expected in units of standard deviation."""
        if expected_prob == 0 or expected_prob == 1:
            # Edge cases: perfect alignment
            return 0 if measured_prob == expected_prob else float("inf")
        std_dev = np.sqrt(expected_prob * (1 - expected_prob) / n)
        return abs(measured_prob - expected_prob) / std_dev

    def _run_angle_test(self, angle_deg, seed):
        """Run measurement test at a specific angle."""
        theta = np.radians(angle_deg)

        # Create state at angle theta from Z-axis (in XZ plane)
        state = qphysics.create_state_from_vector(
            [np.sin(theta), 0, np.cos(theta)]
        )

        # Measure against Z-axis
        outcomes = qphysics.measure_batch(
            state, qphysics.SPIN_Z, self.NUM_PARTICLES, seed
        )

        measured_prob = np.sum(outcomes == 1) / self.NUM_PARTICLES
        expected_prob = (1 + np.cos(theta)) / 2

        return measured_prob, expected_prob

    def test_angle_0_degrees(self):
        """Test measurement when state is aligned with observable (theta=0)."""
        measured, expected = self._run_angle_test(0, seed=100)
        # At 0 degrees, P(+) = 1, all measurements should be +1
        assert measured == expected == 1.0

    def test_angle_180_degrees(self):
        """Test measurement when state is anti-aligned with observable (theta=180)."""
        measured, expected = self._run_angle_test(180, seed=101)
        # At 180 degrees, P(+) = 0, all measurements should be -1
        assert measured == expected == 0.0

    def test_angle_90_degrees(self):
        """Test measurement when state is perpendicular to observable (theta=90)."""
        measured, expected = self._run_angle_test(90, seed=102)
        # At 90 degrees, P(+) = 0.5
        deviation = self._calculate_deviation_sigma(measured, expected, self.NUM_PARTICLES)
        assert deviation < self.SIGMA_THRESHOLD, (
            f"90° test failed: measured {measured:.4f}, expected {expected:.4f}, "
            f"deviation {deviation:.2f}σ"
        )

    @pytest.mark.parametrize(
        "angle_deg,seed",
        [
            (30, 103),
            (45, 104),
            (60, 105),
            (120, 106),
            (135, 107),
            (150, 108),
        ],
    )
    def test_intermediate_angles(self, angle_deg, seed):
        """Test measurement at various intermediate angles."""
        measured, expected = self._run_angle_test(angle_deg, seed)
        deviation = self._calculate_deviation_sigma(measured, expected, self.NUM_PARTICLES)
        assert deviation < self.SIGMA_THRESHOLD, (
            f"{angle_deg}° test failed: measured {measured:.4f}, expected {expected:.4f}, "
            f"deviation {deviation:.2f}σ"
        )

    def test_reproducibility_with_seed(self):
        """Test that results are reproducible with the same seed."""
        results1 = qphysics.measure_batch(
            qphysics.create_state_from_vector([1, 0, 1]),
            qphysics.SPIN_Z,
            1000,
            seed=42,
        )
        results2 = qphysics.measure_batch(
            qphysics.create_state_from_vector([1, 0, 1]),
            qphysics.SPIN_Z,
            1000,
            seed=42,
        )
        np.testing.assert_array_equal(results1, results2)

    def test_cosine_relationship(self):
        """Test that probability follows cos(theta) relationship across angles."""
        angles = [0, 30, 45, 60, 90, 120, 135, 150, 180]
        deviations = []

        for i, angle_deg in enumerate(angles):
            measured, expected = self._run_angle_test(angle_deg, seed=200 + i)
            if 0 < expected < 1:  # Skip edge cases for deviation calc
                deviation = self._calculate_deviation_sigma(
                    measured, expected, self.NUM_PARTICLES
                )
                deviations.append(deviation)

        # All non-edge-case deviations should be within threshold
        assert all(d < self.SIGMA_THRESHOLD for d in deviations), (
            f"Some angles exceed {self.SIGMA_THRESHOLD}σ threshold: {deviations}"
        )
