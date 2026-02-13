# Experiment 03: Double-Slit — Design Alternatives & Advanced Options

This document preserves all design alternatives discussed during Sprint 3 Phase 2
planning (Claude–Gemini collaboration, 4 rounds + James's feedback). These are
retained for potential future use if the simpler choices prove insufficient.

## 1. Wavefunction Formalism

### Chosen: Symplectic Decomposition (ψ = ψ₀ + ψ₁·j)

Two complex components ψ₀, ψ₁ track the (1,i) and (j,k) subspaces.
Implemented in `src/simulation/wave_propagation.py`.

### Alternative: Full Four-Component Quaternionic (ψ = σ₀·1 + ϕ₁·i + ϕ₂·j + ϕ₃·k)

Adler's original formulation uses four real-valued component functions.
- **Pro:** More general; doesn't assume the j-k coupling has a specific structure
- **Pro:** Could reveal effects that the symplectic decomposition masks
- **Con:** Tensor product fails due to quaternion non-commutativity (Issue #249)
- **Con:** More expensive (4 real arrays vs 2 complex arrays per grid point)
- **When to revisit:** If symplectic results show anomalies in the j-k subspace
  that suggest the decomposition is too restrictive

### Alternative: Complex Subspace C(1,i) Only (ψ = α·1 + β·i)

Guaranteed by Moretti-Oppio theorem to match standard QM exactly.
- **Pro:** Mathematically rigorous, avoids tensor product problem entirely
- **Con:** Cannot test quaternionic deviations at all — it IS standard QM
- **When to use:** As a validation baseline (effectively Scenario A)

**Source:** Pre-sprint research Issue #249

---

## 2. Numerical Method

### Chosen: Beam Propagation Method (BPM) with Split-Step Fourier

Z-marching scheme: propagate ψ(x) from z to z+dz.
Algorithm: half diffraction (FFT) → full potential (exact 2×2 matrix exp) → half diffraction.

### Alternative: Full 2D Time-Dependent Schrödinger Equation (TDSE)

Solve iℏ∂ψ/∂t = Hψ on a full (x, z) grid evolving in time.
- **Pro:** More general — captures time-dependent phenomena, reflections, resonances
- **Pro:** Natural for studying transient dynamics (e.g., wavepacket arrival time)
- **Con:** Memory intensive — must store entire 2D grid (Nx × Nz × 2 complex arrays)
- **Con:** Nx=4096, Nz=20000 would require ~5 GB per wavefunction component
- **When to revisit:** If BPM's paraxial approximation proves insufficient, or if
  time-dependent effects (arrival time distributions, transient interference buildup)
  become scientifically interesting

### Alternative: Crank-Nicolson Finite Difference

Implicit time-stepping scheme, unconditionally stable.
- **Pro:** Better stability for large time steps
- **Pro:** Handles absorbing boundary conditions naturally
- **Con:** Requires solving tridiagonal systems at each step
- **Con:** Less efficient than FFT for periodic/smooth problems
- **When to revisit:** If FFT boundary artifacts become problematic

**Ground truth §9.2:** "Use split-step Fourier method or Crank-Nicolson for time evolution"

### Alternative: Higher-Order Splitting (Forest-Ruth, Yoshida)

Fourth-order symplectic integrators instead of second-order Strang splitting.
- **Pro:** O(dz⁴) error per step vs O(dz²) — can use larger step sizes
- **Con:** More FFTs per step (3 instead of 2)
- **When to revisit:** If norm conservation degrades at large U₁ values

**Source:** Claude–Gemini collaboration Round 2

---

## 3. Dimensionality

### Chosen: 2D (transverse x + propagation z)

James's key insight: interference forms along x, decay occurs along z,
and these dynamics are coupled. Cannot be separated into independent 1D problems.

### Alternative: 1D Along z Only (Plan v1, rejected)

The original plan attempted 1D propagation.
- **Why rejected:** Misses the entire transverse interference pattern
- **James's correction:** "A proper double-slit simulation requires 2D"

### Alternative: Full 3D (x, y, z)

Add the second transverse dimension.
- **Pro:** Physical reality is 3D
- **Pro:** Could reveal asymmetries between x and y directions
- **Con:** Memory scales as Nx × Ny × 2 complex arrays per z-slice
- **Con:** For double slits oriented along y-axis, the y-dimension is separable
  (plane wave in y), so 2D captures the essential physics
- **When to revisit:** For circular apertures, or if slit geometry breaks y-symmetry

### Alternative: 3D+t Full Evolution

Time-dependent 3D Schrödinger equation on a full spacetime grid.
- **Pro:** Most general possible treatment
- **Con:** Computationally prohibitive (Nx × Ny × Nz × Nt)
- **When to revisit:** Only with significantly more compute resources

**Source:** Plan revision from v1 → v2, James's feedback

---

## 4. 3D Extensibility Testing

### Chosen: 1D Radial Solver (φ(r) = r·ψ(r))

Uses DST-I for Dirichlet BCs. Rotational symmetry exact by construction.

### Alternative: 3D Cartesian Grid

- **Why rejected:** Introduces cubic anisotropy from the finite-difference stencil
- **Problem:** Cannot distinguish numerical anisotropy from theoretical failure
- **Gemini's insight:** "Any failure in the radial solver is definitively the
  theory's fault, not a numerical artifact"

**Source:** Gemini critique during Step -1 planning

---

## 5. GPU Acceleration Strategy

### Chosen: PyTorch + ROCm with CPU Fallback

GPU path for RX 9070 XT (16GB GDDR6, ~16 TFLOPS).
CPU path via NumPy for when GPU is unavailable.

**Current status:** GPU available (RX 9070 XT with ROCm).

### Alternative: CuPy (CUDA/ROCm)

- **Pro:** Drop-in NumPy replacement, less overhead than PyTorch
- **Con:** Less ecosystem support, fewer debugging tools
- **When to revisit:** If PyTorch overhead becomes measurable

### Alternative: JAX

- **Pro:** Functional paradigm, auto-differentiation, XLA compilation
- **Pro:** Could enable gradient-based optimization of parameters
- **Con:** ROCm support less mature than PyTorch
- **When to revisit:** If we need to optimize U₁ or other parameters via gradient descent

### Alternative: Batched GPU Parameter Sweeps

Run all 18 U₁ × η₀ combinations simultaneously as a batch on GPU.
- **Pro:** Amortizes GPU kernel launch overhead
- **Pro:** Can achieve near-100% GPU utilization
- **Con:** Requires 18× memory per z-slice
- **When to revisit:** When GPU actually works; currently running sequentially on CPU

**Source:** Plan §Step 5: "18 combinations, parallelized on GPU"

---

## 6. Decay Physics Model

### Chosen: Interaction-Driven Decay at Slit Boundaries

U₁ localised at slit openings generates ψ₁ via coupling.
Beyond slits, ψ₁ may propagate as evanescent modes.

### Alternative: Free-Space Exponential Decay (Original Ground Truth)

ψ₁ decays spontaneously during free propagation, even with U₁ = 0.
- **Why problematic:** The coupled equations show both ψ₀ and ψ₁ satisfy
  identical Schrödinger equations when U₁ = 0. Free-space decay is
  mathematically contradictory.
- **Resolution (Gemini Round 3):** Decay occurs because the slit interaction
  projects ψ₁ into evanescent modes that naturally decay in free space.
  The decay is a CONSEQUENCE of the boundary condition, not a free-space effect.

### Two Possible Simulation Outcomes (Ground Truth §4.3.2)

**(a) QBP Prediction — Evanescent Decay:**
η(r) decays exponentially beyond slits. Novel effect.
Acceptance criterion #7: R² > 0.95 vs exp(-2κr) fit.

**(b) Standard Scattering — Constant η:**
η(r) ≈ η_exit = constant beyond slits.
Standard QM scattering behavior. Would fail AC #7.

**The simulation discriminates between (a) and (b).**

**Source:** Ground truth §4.3.2, Gemini review sessions

---

## 7. Potential Step Implementation

### Chosen: Lie-Trotter Splitting (U₀ phase then U₁ coupling)

Two sequential operations per step. O(dz²) splitting error.

### Alternative: Exact Joint Exponential

Compute exp(-i(H_U0 + H_U1)dz/ℏ) as a single matrix exponential.
- **Pro:** No splitting error from separating U₀ and U₁
- **Pro:** Exact for constant potentials
- **Con:** Requires diagonalizing a 2×2 matrix at each x-point per step
- **Con:** More expensive than two sequential operations
- **When to revisit:** If splitting error degrades results at large U₁

### Alternative: Euler Forward Step

ψ(z+dz) = ψ(z) - i·H·ψ(z)·dz/ℏ
- **Why rejected:** Not unitary — norm drifts
- **From transcript:** "Exact matrix exponential for the potential step
  (not Euler) — handles the nonlinear coupling correctly and is
  unconditionally stable"

**Source:** Claude–Gemini collaboration Round 1

---

## 8. Scale Separation Strategy

### Chosen: Single BPM Domain (near-field + far-field in one propagation)

Propagate from z=0 through slits to detector in one continuous BPM run.

### Alternative: Near-Field Box + Far-Field FFT

- Use BPM only in a small box around the slits (near-field diffraction)
- Extract the transmitted wave at the exit face
- Apply Fraunhofer/Fresnel transform analytically for far-field propagation
- **Pro:** Much faster — only need ~100 z-steps for the slit region, then one FFT
- **Pro:** Avoids accumulating numerical error over 20000 z-steps
- **Con:** More complex implementation
- **Con:** Assumes no quaternionic effects in the far field (may not be true!)
- **When to revisit:** If the full BPM run is too slow, or for production runs
  with physical-unit parameters

**Source:** Claude–Gemini Round 1: "scale separation solved — near-field
numerical box around slits, far-field from FFT"

---

## 9. Experimental Design: Where to Look for Quaternionic Effects

### Chosen: Double-Slit with Adler Decay (Sprint 3)

Tests whether quaternionic components decay during spatial propagation.
Expected to match standard QM at detector (by Moretti-Oppio theorem).

### Stronger Alternative: Spin-Path Coupling (Future Sprint)

Pre-sprint research (#250) found:
- **Weak** physical motivation for quaternions in pure spatial superposition
- **Strong** motivation for spin-path coupling (where quaternionic structure
  naturally appears in internal degrees of freedom)
- Spin-Gerlach interferometers or spin-orbit coupling experiments would be
  more likely to reveal genuine quaternionic effects
- **Deferred to:** Future sprint (possibly Sprint 5 or 6)

### Stronger Alternative: Multi-Particle Entanglement (Sprint 6: Bell's Theorem)

- Moretti-Oppio theorem does NOT cover multi-particle systems
- Tensor product problem (#249) means QQM may genuinely diverge from QM
- This is where quaternionic effects are most likely to be observable
- **The PR-Box Problem:** Unrestricted QQM violates information causality (arXiv:0911.1761)
- **Deferred to:** Sprint 6

### Key Insight from Pre-Sprint Research

"Pure double-slit is a reformulation exercise, not a divergence test."
The real tests come from multi-particle entanglement and spin-path coupling.
But the double-slit validates our simulation infrastructure and the decay mechanism.

**Source:** Pre-sprint research Issues #249, #250, #251

---

## 10. Testing Strategy

### Chosen: Two-Stage with Hard Gate

Stage 1 (decay only, no slits) → HARD GATE → Stage 2 (full interference).
James's direction.

### Alternative: Single Monolithic Test Suite

- **Why rejected:** Can't isolate whether failures are in decay physics or
  interference pattern formation
- **James's reasoning:** "Start with decay-focused tests, then move to interference"

### Alternative: Three-Stage with Convergence Analysis

Stage 1 (decay) → Stage 2 (interference) → Stage 3 (convergence analysis).
- Stage 3 would systematically verify that C→A as U₁→0 with quantified
  convergence rates
- **When to revisit:** Phase 3 (Analysis) is the natural place for Stage 3

**Source:** Plan revision based on James's feedback

---

## 11. Parameters Not Yet Explored

These parameter regimes are available but not exercised in Sprint 3 Phase 2:

| Parameter | Current Range | Untested Range | Why Interesting |
|-----------|--------------|----------------|-----------------|
| U₁ | 0–10 (natural units) | 10⁻¹⁵–10⁻³ eV (physical units) | Kaiser neutron bound ≈ 10⁻¹² eV |
| Nx | 1024–2048 | 4096–8192 | Grid convergence study |
| dz | 0.01–0.02 | 0.001–0.005 | Step size convergence |
| Nz_steps | 5000–10000 | 50000–100000 | Longer propagation distances |
| η₀ | 0.01–0.5 | 0.001, 0.9, 0.99 | Extreme quaternionic fractions |
| Slit geometry | d=2.0, a=0.3 | Variable d/a ratio | Diffraction regime study |
| Particle energy | k₀=20–30 | Variable | Energy-dependent decay rates |

---

## 12. Visualization Options (Phase 3+)

### Implemented: CSV Output Only (Phase 2)

### Advanced Options Discussed:

1. **Component-wise decay plot** (Priority 1)
   - α₀², β₀², α₁², β₁² vs distance from slits
   - Blue for (1,i) components; red/orange for (j,k)

2. **Convergence plot**
   - |Scenario C - Scenario A| vs propagation distance
   - Shows where quaternionic effects become undetectable

3. **Fringe visibility vs distance**
   - V(r) showing visibility increase from V < 1 to V → 1

4. **Interactive slider** for η₀
   - Shows decay dynamics effect in real-time
   - Could use D3.js (existing infrastructure from proof viz)

5. **2D propagation heatmap**
   - |ψ₀(x,z)|² and |ψ₁(x,z)|² as 2D colormaps
   - Requires storing snapshots (already supported via snapshot_interval)

**Source:** Ground truth §9.4, Plan §Visualization

---

## Summary: When to Upgrade

| Trigger | Upgrade To |
|---------|-----------|
| BPM paraxial assumption breaks | Full 2D TDSE |
| Norm conservation degrades at large U₁ | Higher-order splitting (Yoshida) |
| GPU becomes available (ROCm update) | Batched parameter sweeps |
| Need physical-unit parameters | Near-field box + far-field FFT |
| Need spin-path coupling | Full four-component quaternionic |
| Need multi-particle effects | Tensor product formulation (Sprint 6) |
| Need gradient optimization | JAX backend |
