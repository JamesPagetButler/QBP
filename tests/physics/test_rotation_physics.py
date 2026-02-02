"""
Physics Validation Tests: 3D Rotations

RULE 5 COMPLIANCE: Link Tests to Reality

These tests verify that our quaternion implementation correctly reproduces
physically observable rotation phenomena. Each test corresponds to a
real-world experiment or measurement.

Physical Context:
- Quaternions encode rotations in SO(3), the group of 3D rotations
- A rotation by angle θ around axis n̂ is represented by q = cos(θ/2) + sin(θ/2)(n̂·σ)
- The "sandwich product" q·v·q⁻¹ rotates vector v

Experimental References:
- Euler's rotation theorem (1775): Any rotation can be described by an axis and angle
- Gimbal lock in aerospace navigation: Quaternions avoid this singularity
"""

import numpy as np
import pytest

from viz.quaternion_rotation import (
    rotate_vector_by_quaternion,
    axis_angle_to_quaternion,
)


class TestRotationPhysics:
    """
    Physics validation tests for quaternion rotations.

    Each test simulates a physically realizable measurement.
    """

    def test_rotation_preserves_vector_length(self, tolerance, pi):
        """
        PHYSICAL LAW: Rotations preserve distances (isometry).

        Experimental analog: A rigid rod rotated in space maintains its length.
        This is measurable with a ruler before and after rotation.

        Mathematical basis: Quaternion rotation is an orthogonal transformation.
        """
        v = np.array([3.0, 4.0, 0.0])  # Length = 5
        original_length = np.linalg.norm(v)

        # Various rotations
        test_rotations = [
            ([0, 0, 1], pi / 4),  # 45° around z
            ([1, 0, 0], pi / 2),  # 90° around x
            ([1, 1, 1], 2 * pi / 3),  # 120° around diagonal
        ]

        for axis, angle in test_rotations:
            q = axis_angle_to_quaternion(axis, angle)
            v_rotated = rotate_vector_by_quaternion(v, q)
            new_length = np.linalg.norm(v_rotated)

            assert np.isclose(
                original_length, new_length, atol=tolerance
            ), f"Length changed from {original_length} to {new_length} for rotation {axis}, {angle}"

    def test_90_degree_rotation_z_axis(self, tolerance, pi):
        """
        PHYSICAL EXPERIMENT: Rotate a pointer 90° counterclockwise (viewed from above).

        Setup: Arrow pointing along +x axis, rotate around +z axis by 90°.
        Expected result: Arrow now points along +y axis.

        This can be verified with a physical arrow on a turntable.
        """
        v = np.array([1.0, 0.0, 0.0])  # Pointing +x
        axis = [0, 0, 1]  # z-axis
        angle = pi / 2  # 90°

        q = axis_angle_to_quaternion(axis, angle)
        v_rotated = rotate_vector_by_quaternion(v, q)

        expected = np.array([0.0, 1.0, 0.0])  # Should point +y
        assert np.allclose(v_rotated, expected, atol=tolerance)

    def test_180_degree_rotation_reverses_perpendicular(self, tolerance, pi):
        """
        PHYSICAL EXPERIMENT: Flip an arrow 180° around a perpendicular axis.

        Setup: Arrow pointing +x, rotate 180° around z-axis.
        Expected: Arrow now points -x.

        Verifiable by flipping any physical object half a turn.
        """
        v = np.array([1.0, 0.0, 0.0])
        axis = [0, 0, 1]
        angle = pi  # 180°

        q = axis_angle_to_quaternion(axis, angle)
        v_rotated = rotate_vector_by_quaternion(v, q)

        expected = np.array([-1.0, 0.0, 0.0])
        assert np.allclose(v_rotated, expected, atol=tolerance)

    def test_360_degree_rotation_returns_to_start(self, tolerance, pi):
        """
        PHYSICAL EXPERIMENT: Full rotation returns to starting position.

        Setup: Any vector, rotate 360° around any axis.
        Expected: Vector unchanged.

        This is the fundamental periodicity of SO(3).
        """
        v = np.array([1.0, 2.0, 3.0])
        axis = [1, 1, 0]  # Arbitrary axis
        angle = 2 * pi  # 360°

        q = axis_angle_to_quaternion(axis, angle)
        v_rotated = rotate_vector_by_quaternion(v, q)

        assert np.allclose(v_rotated, v, atol=tolerance)

    def test_rotation_around_parallel_axis_unchanged(self, tolerance, pi):
        """
        PHYSICAL EXPERIMENT: Rotating around an axis parallel to the vector leaves it unchanged.

        Setup: Arrow pointing +z, rotate around +z axis by any angle.
        Expected: Arrow still points +z.

        Like spinning a pencil around its own axis.
        """
        v = np.array([0.0, 0.0, 1.0])  # Pointing +z
        axis = [0, 0, 1]  # z-axis (parallel to v)

        for angle in [pi / 6, pi / 3, pi / 2, pi, 3 * pi / 2]:
            q = axis_angle_to_quaternion(axis, angle)
            v_rotated = rotate_vector_by_quaternion(v, q)

            assert np.allclose(
                v_rotated, v, atol=tolerance
            ), f"Failed for angle={angle}"

    def test_composition_of_rotations(self, tolerance, pi):
        """
        PHYSICAL EXPERIMENT: Two successive rotations equal one combined rotation.

        Setup: Rotate 90° around z, then 90° around x.
        Verify: This equals a single rotation (computed via quaternion multiplication).

        This tests the group structure of SO(3) via quaternions.
        """
        v = np.array([1.0, 0.0, 0.0])

        # First rotation: 90° around z
        q1 = axis_angle_to_quaternion([0, 0, 1], pi / 2)
        # Second rotation: 90° around x
        q2 = axis_angle_to_quaternion([1, 0, 0], pi / 2)

        # Apply sequentially
        v_after_q1 = rotate_vector_by_quaternion(v, q1)
        v_sequential = rotate_vector_by_quaternion(v_after_q1, q2)

        # Apply as composed quaternion (note: q2 * q1 for sequential application)
        from viz.quaternion_rotation import quaternion_multiply

        q_composed = quaternion_multiply(q2, q1)
        v_composed = rotate_vector_by_quaternion(v, q_composed)

        assert np.allclose(v_sequential, v_composed, atol=tolerance)


class TestSpinorBehavior:
    """
    Tests for spin-1/2 behavior relevant to quantum mechanics.

    PHYSICAL CONTEXT: In quantum mechanics, spin-1/2 particles (electrons, protons)
    require a 720° rotation to return to their original state, not 360°.
    This is encoded in the quaternion double-cover of SO(3).
    """

    def test_720_degree_rotation_quaternion_identity(self, tolerance, pi):
        """
        QUANTUM PHENOMENON: Spinor requires 720° rotation for identity.

        While the VECTOR returns to original after 360°, the QUATERNION
        itself only returns to +1 after 720°. After 360°, q → -q.

        This is the mathematical basis for fermionic statistics.

        Experimental verification: Neutron interferometry experiments
        (Werner et al., 1975) confirmed this 4π periodicity.
        """
        axis = [0, 0, 1]

        # 360° rotation
        q_360 = axis_angle_to_quaternion(axis, 2 * pi)
        # Should be close to -1 (i.e., [-1, 0, 0, 0])
        expected_360 = np.array([-1.0, 0.0, 0.0, 0.0])
        assert np.allclose(
            q_360, expected_360, atol=tolerance
        ), f"360° gave {q_360}, expected {expected_360}"

        # 720° rotation
        q_720 = axis_angle_to_quaternion(axis, 4 * pi)
        # Should be back to +1 (i.e., [1, 0, 0, 0])
        expected_720 = np.array([1.0, 0.0, 0.0, 0.0])
        assert np.allclose(
            q_720, expected_720, atol=tolerance
        ), f"720° gave {q_720}, expected {expected_720}"
