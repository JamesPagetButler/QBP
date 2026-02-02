"""
Unit Tests: Quaternion Operations

These tests verify the mathematical correctness of quaternion operations.
While not direct physics tests, they are foundational for all physics simulations.

Mathematical Reference:
- Hamilton's quaternion algebra (1843)
- q = w + xi + yj + zk where i² = j² = k² = ijk = -1
"""

import numpy as np
import pytest

from viz.quaternion_rotation import (
    quaternion_multiply,
    quaternion_conjugate,
    rotate_vector_by_quaternion,
    axis_angle_to_quaternion,
)


class TestQuaternionAlgebra:
    """Test fundamental quaternion algebraic properties."""

    def test_quaternion_multiplication_identity(self, tolerance):
        """
        Test: q * 1 = q (identity element)

        The quaternion (1, 0, 0, 0) is the multiplicative identity.
        """
        q = np.array([0.5, 0.5, 0.5, 0.5])  # Arbitrary unit quaternion
        identity = np.array([1.0, 0.0, 0.0, 0.0])

        result = quaternion_multiply(q, identity)

        assert np.allclose(result, q, atol=tolerance)

    def test_quaternion_multiplication_conjugate(self, tolerance):
        """
        Test: q * q̄ = |q|² (quaternion times its conjugate gives norm squared)

        For a unit quaternion, q * q̄ = 1.
        """
        # Unit quaternion (normalized)
        q = np.array([0.5, 0.5, 0.5, 0.5])
        q_conj = quaternion_conjugate(q)

        result = quaternion_multiply(q, q_conj)

        # Should give (1, 0, 0, 0) for unit quaternion
        expected = np.array([1.0, 0.0, 0.0, 0.0])
        assert np.allclose(result, expected, atol=tolerance)

    def test_quaternion_conjugate_involution(self, tolerance):
        """
        Test: (q̄)̄ = q (conjugate is an involution)
        """
        q = np.array([1.0, 2.0, 3.0, 4.0])

        result = quaternion_conjugate(quaternion_conjugate(q))

        assert np.allclose(result, q, atol=tolerance)

    def test_quaternion_multiplication_non_commutative(self):
        """
        Test: q₁ * q₂ ≠ q₂ * q₁ in general (non-commutativity)

        This is a fundamental property that distinguishes quaternions from
        complex numbers and is essential for representing 3D rotations.
        """
        q1 = np.array([0.0, 1.0, 0.0, 0.0])  # Pure i
        q2 = np.array([0.0, 0.0, 1.0, 0.0])  # Pure j

        result_12 = quaternion_multiply(q1, q2)
        result_21 = quaternion_multiply(q2, q1)

        # i * j = k, but j * i = -k
        assert not np.allclose(result_12, result_21)

    def test_hamilton_relations(self, tolerance):
        """
        Test: i² = j² = k² = ijk = -1 (Hamilton's fundamental relations)

        Physical significance: These relations encode the structure of 3D rotations.
        """
        i = np.array([0.0, 1.0, 0.0, 0.0])
        j = np.array([0.0, 0.0, 1.0, 0.0])
        k = np.array([0.0, 0.0, 0.0, 1.0])
        minus_one = np.array([-1.0, 0.0, 0.0, 0.0])

        # i² = -1
        assert np.allclose(quaternion_multiply(i, i), minus_one, atol=tolerance)

        # j² = -1
        assert np.allclose(quaternion_multiply(j, j), minus_one, atol=tolerance)

        # k² = -1
        assert np.allclose(quaternion_multiply(k, k), minus_one, atol=tolerance)

        # ijk = -1
        ij = quaternion_multiply(i, j)
        ijk = quaternion_multiply(ij, k)
        assert np.allclose(ijk, minus_one, atol=tolerance)


class TestAxisAngleConversion:
    """Test conversion between axis-angle and quaternion representations."""

    def test_zero_rotation(self, tolerance):
        """
        Test: Zero angle gives identity quaternion.
        """
        axis = [0, 0, 1]
        angle = 0.0

        q = axis_angle_to_quaternion(axis, angle)

        expected = np.array([1.0, 0.0, 0.0, 0.0])
        assert np.allclose(q, expected, atol=tolerance)

    def test_180_degree_rotation(self, tolerance, pi):
        """
        Test: 180° rotation around z-axis gives q = (0, 0, 0, 1).
        """
        axis = [0, 0, 1]
        angle = pi

        q = axis_angle_to_quaternion(axis, angle)

        # cos(π/2) = 0, sin(π/2) = 1
        expected = np.array([0.0, 0.0, 0.0, 1.0])
        assert np.allclose(q, expected, atol=tolerance)

    def test_quaternion_is_normalized(self, tolerance, pi):
        """
        Test: Resulting quaternion should always be unit length.
        """
        test_cases = [
            ([1, 0, 0], pi / 4),
            ([0, 1, 0], pi / 3),
            ([1, 1, 1], pi / 6),
            ([3, 4, 0], 2.5),
        ]

        for axis, angle in test_cases:
            q = axis_angle_to_quaternion(axis, angle)
            norm = np.linalg.norm(q)
            assert np.isclose(
                norm, 1.0, atol=tolerance
            ), f"Failed for axis={axis}, angle={angle}"
