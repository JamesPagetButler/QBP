# tests/physics/test_double_slit.py
"""
Physics validation tests for double-slit interference experiment.

Organized in two stages matching the implementation plan:
- Stage 1: Decay-focused tests (1D along z, simple geometry)
- Stage 2: Full double-slit interference pattern tests

Ground truth: research/03_double_slit_expected_results.md
Acceptance criteria: §6.1 (11 criteria)
"""

import numpy as np
import pytest
import sys
import os

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src.simulation.analytical_double_slit import (
    SlitParameters,
    fraunhofer_pattern,
    which_path_pattern,
    fringe_visibility,
    fringe_positions,
)
from src.simulation.wave_propagation import (
    SimulationConfig,
    SlitConfig,
    TransverseGrid,
    create_transverse_grid,
    create_initial_wavepacket,
    create_barrier_potential_1d,
    create_single_slit_potential,
    bpm_step,
    propagate,
    far_field_intensity,
    compute_eta,
)


# ---------------------------------------------------------------------------
# Analytical baseline tests
# ---------------------------------------------------------------------------


class TestAnalyticalBaseline:
    """Tests for the analytical (exact) double-slit formulas."""

    # Standard parameters (natural units for testing)
    PARAMS = SlitParameters(d=1.0e-6, a=0.1e-6, wavelength=0.05e-9, L=1.0)

    def test_fraunhofer_peak_at_center(self):
        """Scenario A: maximum intensity at x=0."""
        x = np.linspace(-1e-3, 1e-3, 10000)
        I = fraunhofer_pattern(x, self.PARAMS)
        center_idx = len(x) // 2
        assert I[center_idx] == pytest.approx(1.0, abs=0.01)

    def test_fraunhofer_fringe_positions(self):
        """AC #1: fringe maxima at x_n = nλL/d, within 1%."""
        # Odd grid size ensures x=0 is exactly on the grid
        x = np.linspace(-3e-4, 3e-4, 1000001)
        I = fraunhofer_pattern(x, self.PARAMS)

        dx_expected = self.PARAMS.fringe_spacing  # 50μm

        # Find local maxima
        maxima_x = []
        for i in range(1, len(I) - 1):
            if I[i] > I[i - 1] and I[i] > I[i + 1] and I[i] > 0.1:
                maxima_x.append(x[i])

        # Check fringe orders n = -2 to +2 (central region, envelope ≈ flat)
        for n in range(-2, 3):
            x_pred = n * dx_expected
            distances = [abs(x_m - x_pred) for x_m in maxima_x]
            min_dist = min(distances)
            assert min_dist < 0.01 * dx_expected, (
                f"Fringe n={n} at x={x_pred:.2e}m not found within 1% "
                f"of Δx={dx_expected:.2e}m (closest: {min_dist:.2e}m)"
            )

    def test_fraunhofer_cos2_shape(self):
        """AC #2: intensity follows cos²(πxd/λL), R² > 0.99."""
        x = np.linspace(-2e-3, 2e-3, 10000)
        I_sim = fraunhofer_pattern(x, self.PARAMS)

        # Theoretical: cos²(πxd/λL) × sinc²(πxa/λL), normalized
        alpha = np.pi * x * self.PARAMS.d / (self.PARAMS.wavelength * self.PARAMS.L)
        beta = x * self.PARAMS.a / (self.PARAMS.wavelength * self.PARAMS.L)
        I_theory = np.cos(alpha) ** 2 * np.sinc(beta) ** 2
        I_theory /= np.max(I_theory)

        # R² computation
        ss_res = np.sum((I_sim - I_theory) ** 2)
        ss_tot = np.sum((I_sim - np.mean(I_sim)) ** 2)
        r_squared = 1 - ss_res / ss_tot

        assert r_squared > 0.99, f"R² = {r_squared:.4f}, expected > 0.99"

    def test_fringe_spacing(self):
        """AC #3: fringe spacing matches λL/d within 1%."""
        # Odd grid ensures x=0 is on grid
        x = np.linspace(-2e-4, 2e-4, 1000001)
        I = fraunhofer_pattern(x, self.PARAMS)

        # Find maxima positions
        maxima_x = []
        for i in range(1, len(I) - 1):
            if I[i] > I[i - 1] and I[i] > I[i + 1] and I[i] > 0.5:
                maxima_x.append(x[i])

        assert len(maxima_x) >= 3, f"Only {len(maxima_x)} maxima found"

        # Compute consecutive spacings
        spacings = np.diff(sorted(maxima_x))

        # Filter out any anomalous double-spacings (> 1.5× expected)
        expected_spacing = self.PARAMS.fringe_spacing
        good_spacings = [s for s in spacings if s < 1.5 * expected_spacing]

        assert len(good_spacings) >= 2, "Not enough valid spacings found"

        mean_spacing = np.mean(good_spacings)

        assert (
            abs(mean_spacing - expected_spacing) / expected_spacing < 0.01
        ), f"Spacing {mean_spacing:.4e} vs expected {expected_spacing:.4e}"

    def test_which_path_no_fringes(self):
        """AC #4: Scenario B shows no interference fringes.

        The which-path pattern is a smooth sinc² envelope with no rapid
        oscillations at the fringe frequency. We verify this by checking
        the central region where interference fringes would be most visible.
        """
        # Use the central region at fringe-resolving resolution
        x = np.linspace(-3e-4, 3e-4, 100000)
        I = which_path_pattern(x, self.PARAMS)
        V = fringe_visibility(I)

        assert V < 0.01, f"Which-path visibility V = {V:.4f}, expected < 0.01"

    def test_scenario_a_high_visibility(self):
        """AC #5: Scenario A fringe visibility V > 0.95."""
        x = np.linspace(-2e-3, 2e-3, 100000)
        I = fraunhofer_pattern(x, self.PARAMS)
        V = fringe_visibility(I)

        assert V > 0.95, f"Scenario A visibility V = {V:.4f}, expected > 0.95"

    @pytest.mark.parametrize(
        "factor,param",
        [
            (2.0, "wavelength"),
            (2.0, "L"),
            (2.0, "d"),
        ],
    )
    def test_parameter_sensitivity(self, factor, param):
        """AC #6: fringe spacing scales correctly with λ, L, d."""
        # Baseline
        baseline_spacing = self.PARAMS.fringe_spacing

        # Modified parameter
        kwargs = {
            "d": self.PARAMS.d,
            "a": self.PARAMS.a,
            "wavelength": self.PARAMS.wavelength,
            "L": self.PARAMS.L,
        }
        kwargs[param] *= factor
        modified = SlitParameters(**kwargs)
        modified_spacing = modified.fringe_spacing

        # Expected scaling: Δx ∝ λ, Δx ∝ L, Δx ∝ 1/d
        if param in ("wavelength", "L"):
            expected_ratio = factor
        else:  # d
            expected_ratio = 1.0 / factor

        actual_ratio = modified_spacing / baseline_spacing

        assert abs(actual_ratio - expected_ratio) / expected_ratio < 0.01, (
            f"Scaling for {param}×{factor}: expected ratio {expected_ratio:.2f}, "
            f"got {actual_ratio:.4f}"
        )


# ---------------------------------------------------------------------------
# Stage 1: Decay-focused tests (1D along z)
# ---------------------------------------------------------------------------


class TestStage1Decay:
    """
    Stage 1 tests: validate coupled equations and decay mechanism.

    Uses small grids and short propagation for fast testing.
    No slit geometry — just barrier scattering.
    """

    # Small config for fast testing
    CONFIG = SimulationConfig(
        Nx=1024,
        X_max=20.0,
        dz=0.01,
        Nz_steps=5000,
        k0=20.0,
        hbar=1.0,
        mass=0.5,
        device="cpu",
    )

    def test_free_propagation_norm(self):
        """
        Test 1a: Free propagation preserves norm.
        No potential → norm must be exactly conserved.
        """
        grid = create_transverse_grid(self.CONFIG)
        psi0, psi1 = create_initial_wavepacket(grid, k0=20.0, sigma=2.0, eta0=0.1)

        result = propagate(psi0, psi1, grid, self.CONFIG)

        # Check norm conservation
        for norm in result.norm_history:
            assert (
                abs(norm - 1.0) < 1e-6
            ), f"Norm drifted to {norm:.10f} during free propagation"

    def test_free_propagation_no_psi1_generation(self):
        """
        Test 1e (partial): Free propagation with η₀=0, U₁=0.
        ψ₁ must remain exactly zero.
        """
        grid = create_transverse_grid(self.CONFIG)
        psi0, psi1 = create_initial_wavepacket(grid, k0=20.0, sigma=2.0, eta0=0.0)

        result = propagate(psi0, psi1, grid, self.CONFIG)

        psi1_norm = np.sum(np.abs(result.detector_psi1) ** 2) * grid.dx
        assert psi1_norm < 1e-14, f"Spurious ψ₁ in free propagation: {psi1_norm:.2e}"

    def test_quaternionic_barrier_coupling(self):
        """
        Test 1b: Quaternionic barrier generates ψ₁ from ψ₀.
        A localized U₁ should transfer probability from ψ₀ to ψ₁.
        """
        grid = create_transverse_grid(self.CONFIG)
        psi0, psi1 = create_initial_wavepacket(grid, k0=20.0, sigma=2.0, eta0=0.0)

        # Strong static barrier covering more of the domain
        U0_static = np.zeros(self.CONFIG.Nx)
        U1_static = 10.0 * np.exp(-(((grid.x - 0.0) / 5.0) ** 2))

        result = propagate(
            psi0,
            psi1,
            grid,
            self.CONFIG,
            U0_static=U0_static,
            U1_static=U1_static,
        )

        # ψ₁ should be generated (any nonzero amount proves coupling works)
        eta_final = compute_eta(result.detector_psi0, result.detector_psi1, grid.dx)
        assert eta_final > 1e-4, f"Barrier failed to generate ψ₁: η = {eta_final:.6e}"

    def test_u1_zero_control(self):
        """
        Test 1e: U₁=0 control — no coupling, ψ₁ stays zero.
        AC #11.
        """
        grid = create_transverse_grid(self.CONFIG)
        psi0, psi1 = create_initial_wavepacket(grid, k0=20.0, sigma=2.0, eta0=0.0)

        # Standard potential only, no quaternionic coupling
        U0_static = 5.0 * np.exp(-(((grid.x - 0.0) / 2.0) ** 2))
        U1_static = np.zeros(self.CONFIG.Nx)

        result = propagate(
            psi0,
            psi1,
            grid,
            self.CONFIG,
            U0_static=U0_static,
            U1_static=U1_static,
        )

        psi1_norm = np.sum(np.abs(result.detector_psi1) ** 2) * grid.dx
        assert psi1_norm < 1e-14, f"ψ₁ generated with U₁=0: {psi1_norm:.2e}"

    def test_norm_conservation_with_barrier(self):
        """
        Test 1f: Total probability conserved through quaternionic barrier.
        AC #10.
        """
        grid = create_transverse_grid(self.CONFIG)
        psi0, psi1 = create_initial_wavepacket(grid, k0=20.0, sigma=2.0, eta0=0.1)

        U0_static = np.zeros(self.CONFIG.Nx)
        U1_static = 2.0 * np.exp(-(((grid.x - 0.0) / 3.0) ** 2))

        result = propagate(
            psi0,
            psi1,
            grid,
            self.CONFIG,
            U0_static=U0_static,
            U1_static=U1_static,
        )

        # All norms should be close to 1.0
        for norm in result.norm_history:
            assert abs(norm - 1.0) < 1e-4, f"Norm drifted to {norm:.10f}"

    def test_decay_rate_increases_with_u1(self):
        """
        Test 1d: Decay rate κ increases monotonically with U₁.
        AC #8.

        We measure the transfer ratio (how much ψ₁ is generated)
        for different U₁ values. Higher U₁ → more transfer.
        """
        grid = create_transverse_grid(self.CONFIG)
        u1_values = [0.5, 1.0, 2.0, 4.0]
        eta_finals = []

        for u1 in u1_values:
            psi0, psi1 = create_initial_wavepacket(grid, k0=20.0, sigma=2.0, eta0=0.0)
            U0_static = np.zeros(self.CONFIG.Nx)
            U1_static = u1 * np.exp(-(((grid.x - 0.0) / 3.0) ** 2))

            result = propagate(
                psi0,
                psi1,
                grid,
                self.CONFIG,
                U0_static=U0_static,
                U1_static=U1_static,
            )

            eta = compute_eta(result.detector_psi0, result.detector_psi1, grid.dx)
            eta_finals.append(eta)

        # Monotonically increasing
        for i in range(len(eta_finals) - 1):
            assert eta_finals[i + 1] > eta_finals[i], (
                f"η not monotonic: U₁={u1_values[i]} → η={eta_finals[i]:.6f}, "
                f"U₁={u1_values[i+1]} → η={eta_finals[i+1]:.6f}"
            )


# ---------------------------------------------------------------------------
# Stage 2: Full double-slit interference tests
# ---------------------------------------------------------------------------


class TestStage2Interference:
    """
    Stage 2 tests: validate full double-slit interference pattern.

    These tests use the BPM solver with slit geometry.
    """

    # Config for double-slit (larger grid, more steps)
    CONFIG = SimulationConfig(
        Nx=2048,
        X_max=15.0,
        dz=0.02,
        Nz_steps=10000,
        k0=30.0,
        hbar=1.0,
        mass=0.5,
        device="cpu",
    )

    SLIT = SlitConfig(
        separation=2.0,  # d
        width=0.3,  # a
        barrier_height=100.0,  # high barrier
        U1_strength=0.0,  # start with no quaternionic coupling
        z_position=50.0,  # slit at z=50
        z_thickness=1.0,  # thin slit
    )

    def test_complex_double_slit_fringes(self):
        """
        Test 2a: BPM with U₁=0 reproduces interference fringes.

        The complex baseline (Scenario A) must show oscillating intensity
        consistent with double-slit interference.
        """
        grid = create_transverse_grid(self.CONFIG)
        psi0, psi1 = create_initial_wavepacket(
            grid, k0=self.CONFIG.k0, sigma=3.0, eta0=0.0
        )

        result = propagate(psi0, psi1, grid, self.CONFIG, slit=self.SLIT)

        x, I_total, I_psi0, I_psi1 = far_field_intensity(result)

        # Should have oscillating intensity (fringes)
        # Check visibility > 0.3 (moderate threshold for numerical simulation)
        V = fringe_visibility(I_total)
        assert V > 0.3, f"No clear fringes in complex BPM: visibility V = {V:.4f}"

    def test_which_path_low_visibility(self):
        """
        Test 2c: Which-path scenario has low visibility.

        Simulate two independent single-slit propagations using the slit
        geometry (barrier only applied at the correct z position) and
        sum intensities incoherently.
        """
        grid = create_transverse_grid(self.CONFIG)

        # Propagate through upper slit only
        psi0_1, psi1_1 = create_initial_wavepacket(
            grid, k0=self.CONFIG.k0, sigma=3.0, eta0=0.0
        )

        def upper_slit_potential(g, z):
            return create_single_slit_potential(g, self.SLIT, z, which_slit=1)

        result1 = propagate(
            psi0_1,
            psi1_1,
            grid,
            self.CONFIG,
            potential_func=upper_slit_potential,
        )

        # Propagate through lower slit only
        psi0_2, psi1_2 = create_initial_wavepacket(
            grid, k0=self.CONFIG.k0, sigma=3.0, eta0=0.0
        )

        def lower_slit_potential(g, z):
            return create_single_slit_potential(g, self.SLIT, z, which_slit=2)

        result2 = propagate(
            psi0_2,
            psi1_2,
            grid,
            self.CONFIG,
            potential_func=lower_slit_potential,
        )

        # Incoherent sum of intensities (no cross-term)
        I_which = (
            np.abs(result1.detector_psi0) ** 2 + np.abs(result2.detector_psi0) ** 2
        )
        V = fringe_visibility(I_which)

        # Which-path should have low fringe visibility
        # Using 0.3 threshold (BPM diffraction from finite slits may
        # produce some structure, but not double-slit interference fringes)
        assert V < 0.3, f"Which-path visibility too high: V = {V:.4f}"

    def test_quaternionic_with_norm_conservation(self):
        """
        Test 2d + AC #10: Full quaternionic propagation through slits
        conserves total probability.
        """
        slit_q = SlitConfig(
            separation=self.SLIT.separation,
            width=self.SLIT.width,
            barrier_height=self.SLIT.barrier_height,
            U1_strength=2.0,  # quaternionic coupling at slits
            z_position=self.SLIT.z_position,
            z_thickness=self.SLIT.z_thickness,
        )

        grid = create_transverse_grid(self.CONFIG)
        psi0, psi1 = create_initial_wavepacket(
            grid, k0=self.CONFIG.k0, sigma=3.0, eta0=0.1
        )

        result = propagate(psi0, psi1, grid, self.CONFIG, slit=slit_q)

        # Norm conservation
        for norm in result.norm_history:
            assert (
                abs(norm - 1.0) < 1e-3
            ), f"Norm drifted in quaternionic propagation: {norm:.6f}"

    def test_detector_convergence(self):
        """
        Test 2e / AC #9: Scenario C matches Scenario A at detector.

        With sufficient propagation distance, the quaternionic components
        should not significantly affect the far-field pattern.
        """
        grid = create_transverse_grid(self.CONFIG)

        # Scenario A (complex baseline)
        psi0_a, psi1_a = create_initial_wavepacket(
            grid, k0=self.CONFIG.k0, sigma=3.0, eta0=0.0
        )
        result_a = propagate(psi0_a, psi1_a, grid, self.CONFIG, slit=self.SLIT)
        _, I_a, _, _ = far_field_intensity(result_a)

        # Scenario C (quaternionic, small η₀)
        slit_c = SlitConfig(
            separation=self.SLIT.separation,
            width=self.SLIT.width,
            barrier_height=self.SLIT.barrier_height,
            U1_strength=1.0,
            z_position=self.SLIT.z_position,
            z_thickness=self.SLIT.z_thickness,
        )
        psi0_c, psi1_c = create_initial_wavepacket(
            grid, k0=self.CONFIG.k0, sigma=3.0, eta0=0.01
        )
        result_c = propagate(psi0_c, psi1_c, grid, self.CONFIG, slit=slit_c)
        _, I_c, _, _ = far_field_intensity(result_c)

        # Normalize both for comparison
        I_a_norm = I_a / (np.sum(I_a) * grid.dx) if np.sum(I_a) > 0 else I_a
        I_c_norm = I_c / (np.sum(I_c) * grid.dx) if np.sum(I_c) > 0 else I_c

        # The difference should be small
        max_diff = np.max(np.abs(I_a_norm - I_c_norm))
        assert max_diff < 0.1, f"Scenario C deviates from A: max diff = {max_diff:.6f}"
