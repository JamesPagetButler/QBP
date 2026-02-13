# tests/physics/test_general_3d_measurement.py
"""
Physics validation tests for generalized 3D measurement (#211).

Validates that the quaternion formalism reproduces the standard QM result
P(+) = cos²(γ/2) for arbitrary state and measurement directions on the
Bloch sphere, not just the xz-plane restriction of Experiments 01/01b.

Also verifies equivalence between:
1. Direct spherical parameterization: ψ(θ,φ) = sinθ cosφ·i + sinθ sinφ·j + cosθ·k
2. Rotation from z-axis: ψ = q·k·q⁻¹ with appropriate rotation quaternion
3. Standard QM rotation matrices: P(+) = |⟨↑|R(θ,φ)|↑⟩|²
"""

import numpy as np
import pytest
import sys
import os

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src import qphysics


class TestGeneralStateCreation:
    """Test create_general_state covers the full Bloch sphere."""

    def test_phi_zero_matches_tilted(self):
        """φ=0 should recover create_tilted_state (xz-plane)."""
        for theta in [0, 0.5, 1.0, np.pi / 2, np.pi]:
            general = qphysics.create_general_state(theta, 0.0)
            tilted = qphysics.create_tilted_state(theta)
            assert (
                np.abs(general - tilted) < 1e-14
            ), f"Mismatch at θ={theta}: general={general}, tilted={tilted}"

    def test_unit_quaternion(self):
        """All general states should be unit quaternions."""
        for theta in np.linspace(0, np.pi, 10):
            for phi in np.linspace(0, 2 * np.pi, 10):
                psi = qphysics.create_general_state(theta, phi)
                assert abs(np.abs(psi) - 1.0) < 1e-14

    def test_pure_quaternion(self):
        """All general states should be pure (scalar part = 0)."""
        for theta in np.linspace(0, np.pi, 10):
            for phi in np.linspace(0, 2 * np.pi, 10):
                psi = qphysics.create_general_state(theta, phi)
                assert abs(psi.w) < 1e-14

    def test_poles(self):
        """θ=0 → spin-up (k), θ=π → spin-down (-k), regardless of φ."""
        for phi in [0, np.pi / 4, np.pi / 2, np.pi, 3 * np.pi / 2]:
            up = qphysics.create_general_state(0, phi)
            assert abs(up.x) < 1e-14
            assert abs(up.y) < 1e-14
            assert abs(up.z - 1.0) < 1e-14

            down = qphysics.create_general_state(np.pi, phi)
            assert abs(down.x) < 1e-14
            assert abs(down.y) < 1e-14
            assert abs(down.z + 1.0) < 1e-14

    def test_equator_points(self):
        """θ=π/2 gives equatorial states in the xy-plane of the Bloch sphere."""
        # φ=0 → i (spin-x)
        psi = qphysics.create_general_state(np.pi / 2, 0)
        assert abs(psi.x - 1.0) < 1e-14
        assert abs(psi.y) < 1e-14

        # φ=π/2 → j (spin-y)
        psi = qphysics.create_general_state(np.pi / 2, np.pi / 2)
        assert abs(psi.x) < 1e-14
        assert abs(psi.y - 1.0) < 1e-14

        # φ=π → -i
        psi = qphysics.create_general_state(np.pi / 2, np.pi)
        assert abs(psi.x + 1.0) < 1e-14
        assert abs(psi.y) < 1e-14


class TestGeneral3DMeasurement:
    """Test P(+) = cos²(γ/2) for arbitrary state/observable pairs."""

    NUM_PARTICLES = 100000
    SIGMA_THRESHOLD = 4.0  # Slightly looser for 3D grid (many tests)

    def _expected_prob(self, theta_s, phi_s, theta_o, phi_o):
        """Compute expected P(+) analytically from spherical coordinates."""
        cos_gamma = np.sin(theta_s) * np.sin(theta_o) * np.cos(phi_s - phi_o) + np.cos(
            theta_s
        ) * np.cos(theta_o)
        # Clamp for numerical safety
        cos_gamma = max(-1.0, min(1.0, cos_gamma))
        return (1 + cos_gamma) / 2

    def _sigma(self, measured, expected, n):
        """Standard deviation of measured from expected."""
        if expected == 0 or expected == 1:
            return 0 if measured == expected else float("inf")
        std = np.sqrt(expected * (1 - expected) / n)
        return abs(measured - expected) / std

    @pytest.mark.parametrize(
        "theta_s,phi_s,theta_o,phi_o,seed",
        [
            # Same direction → P(+) = 1
            (0, 0, 0, 0, 300),
            (np.pi / 4, np.pi / 3, np.pi / 4, np.pi / 3, 301),
            # Opposite → P(+) = 0
            (0, 0, np.pi, 0, 302),
            (np.pi / 3, np.pi / 4, 2 * np.pi / 3, np.pi + np.pi / 4, 303),
            # Orthogonal → P(+) = 0.5
            (0, 0, np.pi / 2, 0, 304),
            (0, 0, np.pi / 2, np.pi / 2, 305),
            # General 3D angles
            (np.pi / 6, np.pi / 4, np.pi / 3, np.pi / 2, 306),
            (np.pi / 4, np.pi, 3 * np.pi / 4, 0, 307),
            (np.pi / 3, np.pi / 6, np.pi / 2, np.pi / 3, 308),
            (2 * np.pi / 3, np.pi / 4, np.pi / 6, 5 * np.pi / 4, 309),
            # y-axis states (j component, previously untested)
            (np.pi / 2, np.pi / 2, 0, 0, 310),
            (np.pi / 2, np.pi / 2, np.pi / 2, 0, 311),
        ],
    )
    def test_probability_matches_cos_sq(self, theta_s, phi_s, theta_o, phi_o, seed):
        """P(+) should match cos²(γ/2) for arbitrary directions."""
        psi = qphysics.create_general_state(theta_s, phi_s)
        obs = qphysics.create_general_state(theta_o, phi_o)

        expected = self._expected_prob(theta_s, phi_s, theta_o, phi_o)
        outcomes = qphysics.measure_batch(psi, obs, self.NUM_PARTICLES, seed)
        measured = np.sum(outcomes == 1) / self.NUM_PARTICLES

        if 0 < expected < 1:
            deviation = self._sigma(measured, expected, self.NUM_PARTICLES)
            assert deviation < self.SIGMA_THRESHOLD, (
                f"State ({theta_s:.2f},{phi_s:.2f}) obs ({theta_o:.2f},{phi_o:.2f}): "
                f"measured {measured:.4f}, expected {expected:.4f}, {deviation:.1f}σ"
            )
        else:
            assert abs(measured - expected) < 1e-10

    def test_angle_between_states(self):
        """angle_between_states should return the correct angle γ."""
        psi = qphysics.create_general_state(0, 0)  # spin-up z
        obs = qphysics.create_general_state(np.pi / 2, 0)  # spin-x
        gamma = qphysics.angle_between_states(psi, obs)
        assert abs(gamma - np.pi / 2) < 1e-10

        # Same direction → γ = 0
        gamma = qphysics.angle_between_states(psi, psi)
        assert abs(gamma) < 1e-10

        # Opposite → γ = π
        obs_opp = qphysics.create_general_state(np.pi, 0)
        gamma = qphysics.angle_between_states(psi, obs_opp)
        assert abs(gamma - np.pi) < 1e-10


class TestRotationEquivalence:
    """Verify that rotation from z-axis matches direct parameterization."""

    def test_rotation_matches_parameterization(self):
        """q·k·q⁻¹ should equal ψ(θ,φ) for all (θ,φ)."""
        spin_up = qphysics.SPIN_Z

        for theta in np.linspace(0.1, np.pi - 0.1, 8):
            for phi in np.linspace(0, 2 * np.pi - 0.01, 8):
                # Direct parameterization
                direct = qphysics.create_general_state(theta, phi)

                # Rotation approach: rotate k by θ about axis perpendicular
                # to both k and the target direction
                # Rotation axis = (-sin(φ), cos(φ), 0)
                rot_axis = [-np.sin(phi), np.cos(phi), 0]
                rotated = qphysics.rotate_state(spin_up, theta, rot_axis)

                # Compare components
                assert (
                    abs(direct.x - rotated.x) < 1e-10
                ), f"i-component mismatch at θ={theta:.2f}, φ={phi:.2f}"
                assert (
                    abs(direct.y - rotated.y) < 1e-10
                ), f"j-component mismatch at θ={theta:.2f}, φ={phi:.2f}"
                assert (
                    abs(direct.z - rotated.z) < 1e-10
                ), f"k-component mismatch at θ={theta:.2f}, φ={phi:.2f}"

    def test_measurement_invariant_under_rotation(self):
        """Rotating both state and observable by same amount preserves P(+)."""
        psi = qphysics.create_general_state(np.pi / 4, np.pi / 6)
        obs = qphysics.create_general_state(np.pi / 3, np.pi / 2)

        original_exp = qphysics.expectation_value(psi, obs)

        # Rotate both by same angle about same axis
        for axis in [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1]]:
            angle = np.pi / 5
            psi_rot = qphysics.rotate_state(psi, angle, axis)
            obs_rot = qphysics.rotate_observable(obs, angle, axis)
            rotated_exp = qphysics.expectation_value(psi_rot, obs_rot)
            assert abs(original_exp - rotated_exp) < 1e-10, (
                f"Expectation value changed under rotation about {axis}: "
                f"{original_exp:.6f} → {rotated_exp:.6f}"
            )


class TestStandardQMEquivalence:
    """Verify quaternion P(+) matches standard QM rotation matrix calculation."""

    def _standard_qm_prob_up(self, theta_s, phi_s, theta_o, phi_o):
        """Calculate P(+) using standard QM 2x2 matrix formalism.

        |↑⟩_n = cos(α/2)|↑⟩ + e^{iβ} sin(α/2)|↓⟩
        P(+) = |⟨↑_O|ψ⟩|²
        """
        # State spinor: |ψ⟩ = cos(θ_s/2)|↑⟩ + e^{iφ_s} sin(θ_s/2)|↓⟩
        psi_up = np.cos(theta_s / 2)
        psi_down = np.exp(1j * phi_s) * np.sin(theta_s / 2)

        # Observable eigenstate: |↑_O⟩ = cos(α/2)|↑⟩ + e^{iβ} sin(α/2)|↓⟩
        obs_up = np.cos(theta_o / 2)
        obs_down = np.exp(1j * phi_o) * np.sin(theta_o / 2)

        # P(+) = |⟨↑_O|ψ⟩|²
        inner = np.conj(obs_up) * psi_up + np.conj(obs_down) * psi_down
        return float(abs(inner) ** 2)

    @pytest.mark.parametrize(
        "theta_s,phi_s,theta_o,phi_o",
        [
            (0, 0, 0, 0),
            (np.pi, 0, 0, 0),
            (np.pi / 2, 0, 0, 0),
            (np.pi / 2, np.pi / 2, 0, 0),
            (np.pi / 4, np.pi / 3, np.pi / 3, np.pi / 2),
            (np.pi / 6, np.pi / 4, np.pi / 2, np.pi),
            (2 * np.pi / 3, np.pi / 4, np.pi / 6, 5 * np.pi / 4),
            (np.pi / 3, 0, 2 * np.pi / 3, np.pi),
            (np.pi / 2, np.pi / 4, np.pi / 2, 3 * np.pi / 4),
            (np.pi / 4, np.pi, 3 * np.pi / 4, 0),
        ],
    )
    def test_matches_standard_qm(self, theta_s, phi_s, theta_o, phi_o):
        """Quaternion P(+) should match standard QM matrix P(+) exactly."""
        # Quaternion formalism
        psi = qphysics.create_general_state(theta_s, phi_s)
        obs = qphysics.create_general_state(theta_o, phi_o)
        quat_exp = qphysics.expectation_value(psi, obs)
        quat_prob = (1 + quat_exp) / 2

        # Standard QM
        std_prob = self._standard_qm_prob_up(theta_s, phi_s, theta_o, phi_o)

        assert abs(quat_prob - std_prob) < 1e-10, (
            f"Quaternion P(+)={quat_prob:.10f} != Standard QM P(+)={std_prob:.10f} "
            f"at state=({theta_s:.2f},{phi_s:.2f}), obs=({theta_o:.2f},{phi_o:.2f})"
        )
