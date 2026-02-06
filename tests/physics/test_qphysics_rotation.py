# tests/physics/test_qphysics_rotation.py
"""
Tests for the rotation functions in qphysics.py

These tests verify:
1. create_rotation() produces correct rotation quaternions
2. rotate_observable() correctly rotates measurement axes
3. rotate_state() correctly rotates quantum states
4. create_tilted_state() produces states at correct angles

Physical validation: Rotation quaternions must satisfy:
- Half-angle formula: q = cos(θ/2) + sin(θ/2) * axis
- Unit norm: |q| = 1
- Rotation formula: v' = q * v * q⁻¹ rotates v by θ around axis
"""

import numpy as np
import pytest
import sys
import os

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src import qphysics


class TestCreateRotation:
    """Tests for the create_rotation function."""

    def test_identity_rotation(self):
        """Rotation by 0 should give identity quaternion."""
        q = qphysics.create_rotation(0, [0, 0, 1])
        # Identity quaternion is (1, 0, 0, 0)
        assert np.isclose(q.w, 1.0, atol=1e-10)
        assert np.isclose(q.x, 0.0, atol=1e-10)
        assert np.isclose(q.y, 0.0, atol=1e-10)
        assert np.isclose(q.z, 0.0, atol=1e-10)

    def test_90_degree_rotation_z(self):
        """90° rotation around z-axis."""
        q = qphysics.create_rotation(np.pi / 2, [0, 0, 1])
        # q = cos(45°) + sin(45°) * k = (√2/2, 0, 0, √2/2)
        sqrt2_2 = np.sqrt(2) / 2
        assert np.isclose(q.w, sqrt2_2, atol=1e-10)
        assert np.isclose(q.x, 0.0, atol=1e-10)
        assert np.isclose(q.y, 0.0, atol=1e-10)
        assert np.isclose(q.z, sqrt2_2, atol=1e-10)

    def test_180_degree_rotation(self):
        """180° rotation around y-axis."""
        q = qphysics.create_rotation(np.pi, [0, 1, 0])
        # q = cos(90°) + sin(90°) * j = (0, 0, 1, 0)
        assert np.isclose(q.w, 0.0, atol=1e-10)
        assert np.isclose(q.x, 0.0, atol=1e-10)
        assert np.isclose(q.y, 1.0, atol=1e-10)
        assert np.isclose(q.z, 0.0, atol=1e-10)

    def test_360_degree_rotation_gives_minus_identity(self):
        """360° rotation gives -1 (SU(2) double cover)."""
        q = qphysics.create_rotation(2 * np.pi, [0, 0, 1])
        # After 360°, q = -1 = (-1, 0, 0, 0)
        assert np.isclose(q.w, -1.0, atol=1e-10)
        assert np.isclose(q.x, 0.0, atol=1e-10)
        assert np.isclose(q.y, 0.0, atol=1e-10)
        assert np.isclose(q.z, 0.0, atol=1e-10)

    def test_unit_norm(self):
        """Rotation quaternion should have unit norm."""
        test_cases = [
            (np.pi / 4, [1, 0, 0]),
            (np.pi / 3, [0, 1, 0]),
            (np.pi / 6, [0, 0, 1]),
            (2.5, [1, 1, 1]),  # Arbitrary angle and axis
        ]
        for angle, axis in test_cases:
            q = qphysics.create_rotation(angle, axis)
            norm = np.sqrt(q.w**2 + q.x**2 + q.y**2 + q.z**2)
            assert np.isclose(norm, 1.0, atol=1e-10), f"Failed for angle={angle}, axis={axis}"

    def test_axis_normalization(self):
        """Non-unit axis should be normalized automatically."""
        q1 = qphysics.create_rotation(np.pi / 2, [0, 0, 1])
        q2 = qphysics.create_rotation(np.pi / 2, [0, 0, 5])  # Same direction, different magnitude
        assert np.isclose(q1.w, q2.w, atol=1e-10)
        assert np.isclose(q1.z, q2.z, atol=1e-10)

    def test_zero_axis_raises(self):
        """Zero axis should raise ValueError."""
        with pytest.raises(ValueError, match="cannot be zero"):
            qphysics.create_rotation(np.pi / 2, [0, 0, 0])


class TestRotateObservable:
    """Tests for the rotate_observable function."""

    def test_no_rotation(self):
        """Zero rotation leaves observable unchanged."""
        O = qphysics.SPIN_Z
        O_rotated = qphysics.rotate_observable(O, 0, [0, 1, 0])
        assert np.isclose(O_rotated.x, O.x, atol=1e-10)
        assert np.isclose(O_rotated.y, O.y, atol=1e-10)
        assert np.isclose(O_rotated.z, O.z, atol=1e-10)

    def test_90_degree_rotation_z_to_x(self):
        """Rotating SPIN_Z by 90° around y-axis should give SPIN_X."""
        O_rotated = qphysics.rotate_observable(qphysics.SPIN_Z, np.pi / 2, [0, 1, 0])
        # Z rotated 90° around Y → X
        assert np.isclose(O_rotated.x, 1.0, atol=1e-10)
        assert np.isclose(O_rotated.y, 0.0, atol=1e-10)
        assert np.isclose(O_rotated.z, 0.0, atol=1e-10)

    def test_90_degree_rotation_x_to_y(self):
        """Rotating SPIN_X by 90° around z-axis should give SPIN_Y."""
        O_rotated = qphysics.rotate_observable(qphysics.SPIN_X, np.pi / 2, [0, 0, 1])
        # X rotated 90° around Z → Y
        assert np.isclose(O_rotated.x, 0.0, atol=1e-10)
        assert np.isclose(O_rotated.y, 1.0, atol=1e-10)
        assert np.isclose(O_rotated.z, 0.0, atol=1e-10)

    def test_180_degree_rotation_reverses(self):
        """180° rotation reverses the observable direction."""
        O_rotated = qphysics.rotate_observable(qphysics.SPIN_Z, np.pi, [1, 0, 0])
        # Z rotated 180° around X → -Z
        assert np.isclose(O_rotated.x, 0.0, atol=1e-10)
        assert np.isclose(O_rotated.y, 0.0, atol=1e-10)
        assert np.isclose(O_rotated.z, -1.0, atol=1e-10)

    def test_result_is_pure_quaternion(self):
        """Rotated observable should have zero real part."""
        O_rotated = qphysics.rotate_observable(qphysics.SPIN_Z, 1.234, [1, 1, 0])
        assert np.isclose(O_rotated.w, 0.0, atol=1e-10)


class TestRotateState:
    """Tests for the rotate_state function."""

    def test_rotate_z_state_by_90_around_y(self):
        """Rotating z-aligned state by 90° around y gives x-aligned state."""
        psi = qphysics.create_state_from_vector([0, 0, 1])  # |+z⟩
        psi_rotated = qphysics.rotate_state(psi, np.pi / 2, [0, 1, 0])
        # Should now point along x
        vec = qphysics.get_state_vector(psi_rotated)
        assert np.isclose(vec[0], 1.0, atol=1e-10)  # x
        assert np.isclose(vec[1], 0.0, atol=1e-10)  # y
        assert np.isclose(vec[2], 0.0, atol=1e-10)  # z

    def test_rotated_state_is_normalized(self):
        """Rotated state should remain normalized."""
        psi = qphysics.create_state_from_vector([1, 1, 1])
        psi_rotated = qphysics.rotate_state(psi, 1.5, [1, 0, 1])
        norm = psi_rotated.norm()
        assert np.isclose(norm, 1.0, atol=1e-10)

    def test_rotated_state_is_pure(self):
        """Rotated state should remain a pure quaternion."""
        psi = qphysics.create_state_from_vector([1, 0, 0])
        psi_rotated = qphysics.rotate_state(psi, np.pi / 3, [0, 1, 0])
        assert np.isclose(psi_rotated.w, 0.0, atol=1e-10)


class TestCreateTiltedState:
    """Tests for the create_tilted_state convenience function."""

    def test_zero_tilt_gives_z_state(self):
        """θ=0 should give state along +z."""
        psi = qphysics.create_tilted_state(0)
        vec = qphysics.get_state_vector(psi)
        assert np.isclose(vec[0], 0.0, atol=1e-10)  # x
        assert np.isclose(vec[1], 0.0, atol=1e-10)  # y
        assert np.isclose(vec[2], 1.0, atol=1e-10)  # z

    def test_90_tilt_gives_x_state(self):
        """θ=90° should give state along +x."""
        psi = qphysics.create_tilted_state(np.pi / 2)
        vec = qphysics.get_state_vector(psi)
        assert np.isclose(vec[0], 1.0, atol=1e-10)  # x
        assert np.isclose(vec[1], 0.0, atol=1e-10)  # y
        assert np.isclose(vec[2], 0.0, atol=1e-10)  # z

    def test_180_tilt_gives_minus_z_state(self):
        """θ=180° should give state along -z."""
        psi = qphysics.create_tilted_state(np.pi)
        vec = qphysics.get_state_vector(psi)
        assert np.isclose(vec[0], 0.0, atol=1e-10)  # x
        assert np.isclose(vec[1], 0.0, atol=1e-10)  # y
        assert np.isclose(vec[2], -1.0, atol=1e-10)  # z

    def test_60_tilt_gives_correct_components(self):
        """θ=60° should give (sin 60°, 0, cos 60°) = (√3/2, 0, 0.5)."""
        psi = qphysics.create_tilted_state(np.pi / 3)
        vec = qphysics.get_state_vector(psi)
        assert np.isclose(vec[0], np.sqrt(3) / 2, atol=1e-10)  # x = sin(60°)
        assert np.isclose(vec[1], 0.0, atol=1e-10)  # y
        assert np.isclose(vec[2], 0.5, atol=1e-10)  # z = cos(60°)

    def test_tilted_state_is_normalized(self):
        """Tilted state should be a unit quaternion."""
        for theta in [0, np.pi / 6, np.pi / 4, np.pi / 3, np.pi / 2, np.pi]:
            psi = qphysics.create_tilted_state(theta)
            norm = psi.norm()
            assert np.isclose(norm, 1.0, atol=1e-10), f"Failed for theta={theta}"


class TestRotationAndMeasurement:
    """Integration tests: rotation functions with measurement."""

    def test_tilted_state_expectation_value(self):
        """Expectation value of tilted state against z should equal cos(θ)."""
        test_angles = [0, 30, 45, 60, 90, 120, 150, 180]

        for angle_deg in test_angles:
            theta = np.radians(angle_deg)
            psi = qphysics.create_tilted_state(theta)
            exp_val = qphysics.expectation_value(psi, qphysics.SPIN_Z)

            expected = np.cos(theta)
            assert np.isclose(exp_val, expected, atol=1e-10), (
                f"Failed at {angle_deg}°: got {exp_val}, expected {expected}"
            )

    def test_rotated_observable_equivalent_to_tilted_state(self):
        """Rotating observable should give same expectation as tilting state."""
        theta = np.pi / 4  # 45°

        # Method 1: Tilt state, measure along z
        psi_tilted = qphysics.create_tilted_state(theta)
        exp1 = qphysics.expectation_value(psi_tilted, qphysics.SPIN_Z)

        # Method 2: Keep state along z, rotate observable
        psi_z = qphysics.create_state_from_vector([0, 0, 1])
        O_rotated = qphysics.rotate_observable(qphysics.SPIN_Z, theta, [0, 1, 0])
        exp2 = qphysics.expectation_value(psi_z, O_rotated)

        # Both should give cos(θ)
        assert np.isclose(exp1, np.cos(theta), atol=1e-10)
        assert np.isclose(exp2, np.cos(theta), atol=1e-10)
        assert np.isclose(exp1, exp2, atol=1e-10)
