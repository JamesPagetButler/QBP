# tests/physics/test_3d_extensibility.py
"""
3D Extensibility Validation Tests (Step -1 Gate)

These tests verify that the coupled quaternionic Schrödinger equations
extend correctly to 3D before committing to the 2D BPM implementation.

Test A: Symbolic unitarity proof — verify ∂ρ/∂t + ∇·J = 0 in 3D
Test B: 1D radial propagation — verify spherical symmetry is preserved

Both tests must PASS before proceeding to implementation.

Physics reference: Adler (1995) Ch. 2; Davies & McKellar (1989) §3.
Ground truth: research/03_double_slit_expected_results.md §3.3
"""

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Test A: Symbolic Unitarity Proof
# ---------------------------------------------------------------------------


class TestSymbolicUnitarity:
    """
    Verify the continuity equation ∂ρ/∂t + ∇·J = 0 holds in 3D
    for the coupled quaternionic Schrödinger system.

    The coupled equations (from ground truth §3.3):
        iℏ ∂ψ₀/∂t = -(ℏ²/2m)∇²ψ₀ + U₀·ψ₀ - U₁·ψ₁*
        iℏ ∂ψ₁/∂t = -(ℏ²/2m)∇²ψ₁ + U₀·ψ₁ + U₁·ψ₀*

    Probability density: ρ = |ψ₀|² + |ψ₁|²

    The proof decomposes into:
    1. Potential terms cancel in ∂ρ/∂t (algebraic — verified symbolically)
    2. Kinetic terms form ∇·J via Green's identity (verified symbolically)
    """

    def test_u0_potential_conserves_probability(self):
        """
        Standard potential U₀ (real) conserves probability.

        U₀ contribution to ∂ρ/∂t from both equations:
          ψ₀*(-i/ℏ)(U₀ψ₀) + c.c. + ψ₁*(-i/ℏ)(U₀ψ₁) + c.c.
        For real U₀, each pair gives:
          (-i/ℏ)U₀|ψ|² + (i/ℏ)U₀|ψ|² = 0
        """
        import sympy as sp
        from sympy import I

        hbar = sp.Symbol("hbar", real=True, positive=True)
        U0 = sp.Symbol("U0", real=True)
        # Use plain symbols for wavefunction components (not Functions)
        a, b, c, d = sp.symbols("a b c d", real=True)

        psi0 = a + I * b
        psi0c = a - I * b
        psi1 = c + I * d
        psi1c = c - I * d

        # U₀ contribution from ψ₀ equation + conjugate
        u0_from_psi0 = psi0c * (-I / hbar) * U0 * psi0 + psi0 * (I / hbar) * U0 * psi0c
        # U₀ contribution from ψ₁ equation + conjugate
        u0_from_psi1 = psi1c * (-I / hbar) * U0 * psi1 + psi1 * (I / hbar) * U0 * psi1c

        total = sp.expand(u0_from_psi0 + u0_from_psi1)

        assert total == 0, f"Real U₀ terms don't cancel: {total}"

    def test_u1_coupling_conserves_probability(self):
        """
        Quaternionic coupling U₁ (real) conserves total probability.

        The sign structure (-U₁ψ₁* in eq 1, +U₁ψ₀* in eq 2) ensures
        exact cancellation of coupling contributions to ∂ρ/∂t.

        From ψ₀ equation: ψ₀*(-i/ℏ)(-U₁ψ₁*) + c.c. = (iU₁/ℏ)(ψ₀*ψ₁* - ψ₀ψ₁)
        From ψ₁ equation: ψ₁*(-i/ℏ)(U₁ψ₀*) + c.c. = (-iU₁/ℏ)(ψ₁*ψ₀* - ψ₁ψ₀)
        Sum = 0 (since ψ₀*ψ₁* = (ψ₁ψ₀)* and the terms are mutual conjugates)
        """
        import sympy as sp
        from sympy import I

        hbar = sp.Symbol("hbar", real=True, positive=True)
        U1 = sp.Symbol("U1", real=True)
        a, b, c, d = sp.symbols("a b c d", real=True)

        psi0 = a + I * b
        psi0c = a - I * b
        psi1 = c + I * d
        psi1c = c - I * d

        # Coupling from ψ₀ equation: potential term is -U₁·ψ₁*
        coupling_0 = psi0c * (-I / hbar) * (-U1 * psi1c) + psi0 * (I / hbar) * (
            -U1 * psi1
        )

        # Coupling from ψ₁ equation: potential term is +U₁·ψ₀*
        coupling_1 = psi1c * (-I / hbar) * (U1 * psi0c) + psi1 * (I / hbar) * (
            U1 * psi0
        )

        total = sp.expand(coupling_0 + coupling_1)

        assert total == 0, f"U₁ coupling terms don't cancel: {total}"

    def test_complex_u0_with_imaginary_part(self):
        """
        Verify that complex U₀ with imaginary part does NOT conserve
        probability (sanity check — complex potentials model absorption).
        This confirms our algebra is not trivially zero.
        """
        import sympy as sp
        from sympy import I

        hbar = sp.Symbol("hbar", real=True, positive=True)
        U0_re = sp.Symbol("U0_re", real=True)
        U0_im = sp.Symbol("U0_im", real=True)
        U0 = U0_re + I * U0_im
        U0c = U0_re - I * U0_im

        a, b = sp.symbols("a b", real=True)
        psi0 = a + I * b
        psi0c = a - I * b

        # U₀ contribution from ψ₀ equation only
        contrib = psi0c * (-I / hbar) * U0 * psi0 + psi0 * (I / hbar) * U0c * psi0c
        contrib = sp.expand(contrib)

        # Should NOT be zero when U0_im ≠ 0
        # Expected: (2/ℏ)·U0_im·(a² + b²)
        assert contrib != 0, "Complex U₀ contribution should not vanish"
        # Check it has the expected form
        expected = 2 * U0_im * (a**2 + b**2) / hbar
        assert (
            sp.expand(contrib - expected) == 0
        ), f"Unexpected form: got {contrib}, expected {expected}"

    def test_greens_identity_holds(self):
        """
        Verify Green's identity: ψ*∇²ψ - ψ∇²ψ* = ∇·(ψ*∇ψ - ψ∇ψ*)

        This identity ensures the kinetic terms in ∂ρ/∂t form a divergence ∇·J.
        We verify the x-component; y and z follow by symmetry.
        """
        import sympy as sp
        from sympy import Function, diff, conjugate

        x, y, z = sp.symbols("x y z", real=True)
        f = Function("f")(x, y, z)
        fc = conjugate(f)

        # Verify for each spatial direction
        for coord in [x, y, z]:
            # LHS: d/d(coord) [f* df/d(coord) - f df*/d(coord)]
            lhs = diff(fc * diff(f, coord) - f * diff(fc, coord), coord)
            # RHS: f* d²f/d(coord)² - f d²f*/d(coord)²
            rhs = fc * diff(f, coord, 2) - f * diff(fc, coord, 2)

            diff_result = sp.expand(lhs - rhs)
            assert (
                diff_result == 0
            ), f"Green's identity failed for {coord}: {diff_result}"

    def test_continuity_equation_complete(self):
        """
        Compositional proof: combining the above results proves ∂ρ/∂t + ∇·J = 0.

        Structure of the proof:
        1. ∂ρ/∂t = (kinetic terms) + (U₀ terms) + (U₁ terms)
        2. U₀ terms = 0 (test_u0_potential_conserves_probability)
        3. U₁ terms = 0 (test_u1_coupling_conserves_probability)
        4. Kinetic terms = Σ_j (iℏ/2m)[ψ_j* ∇²ψ_j - ψ_j ∇²ψ_j*]
        5. By Green's identity (test_greens_identity_holds):
           ψ*∇²ψ - ψ∇²ψ* = ∇·(ψ*∇ψ - ψ∇ψ*)
        6. Therefore kinetic terms = -∇·J where:
           J = (ℏ/2mi)Σ_j [ψ_j* ∇ψ_j - ψ_j ∇ψ_j*]

        This is the standard probability current extended to the coupled system.
        The 3D extension works because:
        - Laplacian naturally generalizes to 3D
        - Potential cancellation is algebraic (no spatial dependence)
        - Green's identity holds in any number of dimensions

        Numerical verification that potential cancellation holds for
        random complex wavefunction values (not just symbolic zeros).
        """
        import random

        random.seed(42)

        hbar = 1.0

        for _ in range(100):
            # Random wavefunction components
            a = random.gauss(0, 1)
            b = random.gauss(0, 1)
            c = random.gauss(0, 1)
            d = random.gauss(0, 1)
            U0 = random.gauss(0, 1)  # real U₀
            U1 = random.gauss(0, 1)  # real U₁

            psi0 = complex(a, b)
            psi1 = complex(c, d)

            # ∂ρ/∂t contribution from potentials:
            # From ψ₀ eq: ψ₀*(-i/ℏ)(U₀ψ₀ - U₁ψ₁*) + c.c.
            term0 = np.conj(psi0) * (-1j / hbar) * (U0 * psi0 - U1 * np.conj(psi1))
            term0 += psi0 * (1j / hbar) * (U0 * np.conj(psi0) - U1 * psi1)

            # From ψ₁ eq: ψ₁*(-i/ℏ)(U₀ψ₁ + U₁ψ₀*) + c.c.
            term1 = np.conj(psi1) * (-1j / hbar) * (U0 * psi1 + U1 * np.conj(psi0))
            term1 += psi1 * (1j / hbar) * (U0 * np.conj(psi1) + U1 * psi0)

            total = term0 + term1

            assert (
                abs(total) < 1e-14
            ), f"Potential contribution to ∂ρ/∂t is nonzero: {total}"


# ---------------------------------------------------------------------------
# Test B: 1D Radial Propagation
# ---------------------------------------------------------------------------


class TestRadialPropagation:
    """
    1D radial propagation test for 3D extensibility.

    Verify that the coupled quaternionic Schrödinger equations preserve
    spherical symmetry in 3D by solving on a 1D radial grid.

    Key insight: Using φ(r) = r·ψ(r), the 3D radial Schrödinger equation
    becomes equivalent to a 1D problem. Rotational symmetry is exact.
    """

    # Physical parameters (natural units: ℏ=1, m=0.5)
    HBAR = 1.0
    MASS = 0.5
    NR = 512
    R_MAX = 30.0
    DT = 0.005
    N_STEPS = 2000

    def _create_radial_grid(self):
        """Create 1D radial grid, excluding r=0."""
        dr = self.R_MAX / self.NR
        r = np.linspace(dr, self.R_MAX, self.NR)
        return r, dr

    def _gaussian_packet(self, r, r0, sigma):
        """Spherically symmetric Gaussian wavepacket φ(r) = r·ψ(r)."""
        return np.exp(-((r - r0) ** 2) / (2 * sigma**2))

    def _normalize_radial(self, phi, dr):
        """Normalize: 4π∫|φ|² dr = 1."""
        norm_sq = 4 * np.pi * np.sum(np.abs(phi) ** 2) * dr
        return phi / np.sqrt(norm_sq) if norm_sq > 0 else phi

    def _compute_norm(self, phi0, phi1, dr):
        """Total probability: 4π∫(|φ₀|² + |φ₁|²) dr."""
        return 4 * np.pi * np.sum(np.abs(phi0) ** 2 + np.abs(phi1) ** 2) * dr

    def _split_step_radial(self, phi0, phi1, U0, U1, r, dr, dt):
        """
        Split-step propagation for radial wavefunctions φ = r·ψ.

        For φ(r) = r·ψ(r), the radial equation has the same form as 1D:
            iℏ ∂φ/∂t = -(ℏ²/2m) ∂²φ/∂r² + V(r)·φ

        Split-step: half kinetic → full potential → half kinetic
        Uses Discrete Sine Transform (DST-I) for Dirichlet BCs.
        """
        from scipy.fft import dst, idst

        N = len(r)

        # Kinetic step using DST (Dirichlet boundary conditions)
        # DST-I modes: k_n = π·n / (R_max + dr), n = 1, ..., N
        k = np.pi * np.arange(1, N + 1) / (self.R_MAX + dr)
        kinetic_half = np.exp(-1j * self.HBAR * k**2 * dt / (4 * self.MASS))

        def apply_kinetic(phi):
            """Apply half kinetic step via DST."""
            phi_k = dst(phi.real, type=1) + 1j * dst(phi.imag, type=1)
            phi_k *= kinetic_half
            return idst(phi_k.real, type=1) + 1j * idst(phi_k.imag, type=1)

        # Half kinetic step
        phi0 = apply_kinetic(phi0)
        phi1 = apply_kinetic(phi1)

        # Full potential step (exact 2×2 matrix exponential)
        phi0, phi1 = self._potential_step(phi0, phi1, U0, U1, dt)

        # Half kinetic step
        phi0 = apply_kinetic(phi0)
        phi1 = apply_kinetic(phi1)

        return phi0, phi1

    def _potential_step(self, phi0, phi1, U0, U1, dt):
        """
        Exact potential step for the coupled system.

        The coupled potential equations:
            iℏ dφ₀/dt = U₀φ₀ - U₁φ₁*
            iℏ dφ₁/dt = U₀φ₁ + U₁φ₀*

        For real U₀ and U₁, solved as:
        1. Apply U₀ phase rotation to both components
        2. Apply U₁ coupling rotation (handles conjugation mixing)
        """
        # Step 1: U₀ phase rotation
        phase = np.exp(-1j * U0 * dt / self.HBAR)
        phi0 = phi0 * phase
        phi1 = phi1 * phase

        # Step 2: U₁ coupling
        # The coupling equations (after removing U₀):
        #   dφ₀/dt = (-i/ℏ)(-U₁ φ₁*) = (iU₁/ℏ) φ₁*
        #   dφ₁/dt = (-i/ℏ)(U₁ φ₀*)  = (-iU₁/ℏ) φ₀*
        #
        # Write φ₀ = p + iq, φ₁ = r + is:
        #   dp/dt = (U₁/ℏ)s,  dq/dt = (U₁/ℏ)r
        #   dr/dt = -(U₁/ℏ)q, ds/dt = -(U₁/ℏ)p
        #
        # This is a rotation with angle θ = U₁·dt/ℏ:
        theta = U1 * dt / self.HBAR
        cos_t = np.cos(theta)
        sin_t = np.sin(theta)

        p = phi0.real.copy()
        q = phi0.imag.copy()
        r = phi1.real.copy()
        s = phi1.imag.copy()

        p_new = cos_t * p + sin_t * s
        q_new = cos_t * q + sin_t * r
        r_new = cos_t * r - sin_t * q
        s_new = cos_t * s - sin_t * p

        return p_new + 1j * q_new, r_new + 1j * s_new

    def test_free_propagation_norm_conservation(self):
        """Free propagation (U₀=0, U₁=0): total probability conserved."""
        r, dr = self._create_radial_grid()

        phi0 = self._gaussian_packet(r, r0=10.0, sigma=2.0).astype(complex)
        phi1 = np.zeros_like(phi0, dtype=complex)
        phi0 = self._normalize_radial(phi0, dr)

        U0 = np.zeros_like(r)
        U1 = np.zeros_like(r)

        initial_norm = self._compute_norm(phi0, phi1, dr)

        for _ in range(self.N_STEPS):
            phi0, phi1 = self._split_step_radial(phi0, phi1, U0, U1, r, dr, self.DT)

        final_norm = self._compute_norm(phi0, phi1, dr)

        assert abs(final_norm - initial_norm) < 1e-6, (
            f"Norm not conserved: initial={initial_norm:.10f}, "
            f"final={final_norm:.10f}, diff={abs(final_norm - initial_norm):.2e}"
        )

    def test_no_spurious_psi1_generation(self):
        """With ψ₁=0 and U₁=0, ψ₁ must remain zero throughout."""
        r, dr = self._create_radial_grid()

        phi0 = self._gaussian_packet(r, r0=10.0, sigma=2.0).astype(complex)
        phi1 = np.zeros_like(phi0, dtype=complex)
        phi0 = self._normalize_radial(phi0, dr)

        U0 = np.zeros_like(r)
        U1 = np.zeros_like(r)

        for _ in range(self.N_STEPS):
            phi0, phi1 = self._split_step_radial(phi0, phi1, U0, U1, r, dr, self.DT)

        psi1_norm = 4 * np.pi * np.sum(np.abs(phi1) ** 2) * dr

        assert psi1_norm < 1e-14, f"Spurious ψ₁ generated: |ψ₁|² = {psi1_norm:.2e}"

    def test_quaternionic_barrier_generates_psi1(self):
        """U₁ barrier should generate ψ₁ from initially zero ψ₁."""
        r, dr = self._create_radial_grid()

        phi0 = self._gaussian_packet(r, r0=10.0, sigma=2.0).astype(complex)
        phi1 = np.zeros_like(phi0, dtype=complex)
        phi0 = self._normalize_radial(phi0, dr)

        U0 = -2.0 * np.exp(-(((r - 15.0) / 2.0) ** 2))
        U1 = 1.0 * np.exp(-(((r - 15.0) / 1.5) ** 2))

        for _ in range(self.N_STEPS):
            phi0, phi1 = self._split_step_radial(phi0, phi1, U0, U1, r, dr, self.DT)

        psi1_norm = 4 * np.pi * np.sum(np.abs(phi1) ** 2) * dr

        assert (
            psi1_norm > 1e-6
        ), f"U₁ coupling failed to generate ψ₁: |ψ₁|² = {psi1_norm:.2e}"

    def test_barrier_norm_conservation(self):
        """Total probability conserved through quaternionic barrier."""
        r, dr = self._create_radial_grid()

        phi0 = self._gaussian_packet(r, r0=10.0, sigma=2.0).astype(complex)
        phi1 = np.zeros_like(phi0, dtype=complex)
        phi0 = self._normalize_radial(phi0, dr)

        U0 = -2.0 * np.exp(-(((r - 15.0) / 2.0) ** 2))
        U1 = 1.0 * np.exp(-(((r - 15.0) / 1.5) ** 2))

        initial_norm = self._compute_norm(phi0, phi1, dr)

        for _ in range(self.N_STEPS):
            phi0, phi1 = self._split_step_radial(phi0, phi1, U0, U1, r, dr, self.DT)

        final_norm = self._compute_norm(phi0, phi1, dr)

        assert abs(final_norm - initial_norm) < 1e-4, (
            f"Norm not conserved through barrier: "
            f"initial={initial_norm:.10f}, final={final_norm:.10f}, "
            f"diff={abs(final_norm - initial_norm):.2e}"
        )

    def test_spherical_symmetry_preserved(self):
        """
        Spherically symmetric initial conditions stay spherically symmetric.

        Since we use a 1D radial grid, rotational symmetry is exact by
        construction. We verify the solver preserves smoothness (no
        numerical artifacts that would break symmetry in a 3D embedding).
        """
        r, dr = self._create_radial_grid()

        phi0 = self._gaussian_packet(r, r0=12.0, sigma=3.0).astype(complex)
        phi1 = np.zeros_like(phi0, dtype=complex)
        phi0 = self._normalize_radial(phi0, dr)

        U0 = -1.5 * np.exp(-(((r - 15.0) / 2.5) ** 2))
        U1 = 0.5 * np.exp(-(((r - 15.0) / 2.0) ** 2))

        for _ in range(self.N_STEPS):
            phi0, phi1 = self._split_step_radial(phi0, phi1, U0, U1, r, dr, self.DT)

        # Check smoothness: second derivative of density should be bounded
        density = np.abs(phi0) ** 2 + np.abs(phi1) ** 2
        d2_density = np.diff(density, 2) / dr**2
        max_density = max(np.max(density), 1e-30)
        roughness = np.max(np.abs(d2_density)) * dr**2 / max_density

        assert (
            roughness < 100
        ), f"Excessive roughness (possible symmetry breaking): {roughness:.2f}"

        # Boundary condition: φ(r_min) should be small (φ = r·ψ → 0 as r → 0)
        assert (
            np.abs(phi0[0]) < 0.1
        ), f"Boundary condition violated: φ₀(r_min) = {np.abs(phi0[0]):.4f}"

    def test_u1_zero_control(self):
        """Control: with U₁=0, ψ₁ stays zero. Equations decouple."""
        r, dr = self._create_radial_grid()

        phi0 = self._gaussian_packet(r, r0=10.0, sigma=2.0).astype(complex)
        phi1 = np.zeros_like(phi0, dtype=complex)
        phi0 = self._normalize_radial(phi0, dr)

        U0 = -2.0 * np.exp(-(((r - 15.0) / 2.0) ** 2))
        U1 = np.zeros_like(r)

        for _ in range(self.N_STEPS):
            phi0, phi1 = self._split_step_radial(phi0, phi1, U0, U1, r, dr, self.DT)

        psi1_norm = 4 * np.pi * np.sum(np.abs(phi1) ** 2) * dr

        assert psi1_norm < 1e-14, f"ψ₁ generated with U₁=0: {psi1_norm:.2e}"

    def test_decay_dynamics_consistent(self):
        """
        After passing through a quaternionic barrier, ψ₁ should be
        generated and then propagate freely. Total norm conserved.
        """
        r, dr = self._create_radial_grid()

        phi0 = self._gaussian_packet(r, r0=5.0, sigma=2.0).astype(complex)
        phi1 = np.zeros_like(phi0, dtype=complex)
        phi0 = self._normalize_radial(phi0, dr)

        U0 = np.zeros_like(r)
        U1 = 3.0 * np.exp(-(((r - 12.0) / 1.0) ** 2))

        norms = []
        for step in range(self.N_STEPS):
            phi0, phi1 = self._split_step_radial(phi0, phi1, U0, U1, r, dr, self.DT)
            if step % 100 == 0:
                psi1_norm = 4 * np.pi * np.sum(np.abs(phi1) ** 2) * dr
                norms.append(psi1_norm)

        # ψ₁ should have been generated
        assert norms[-1] > 1e-6, f"No ψ₁ generation: final norm = {norms[-1]:.2e}"

        # Total norm conserved
        total_norm = self._compute_norm(phi0, phi1, dr)
        assert abs(total_norm - 1.0) < 1e-3, f"Total norm drifted: {total_norm:.6f}"
