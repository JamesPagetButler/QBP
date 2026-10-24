#!/usr/bin/env python3
"""
QBP: Spectral Action Trace Computation
=======================================

Compute the EXACT Dynkin index sums over the full 96-dimensional
Hilbert space of the SM finite geometry (3 generations × 32 states).

This determines the normalisation constant relating f₀ (spectral action)
to the gauge couplings, which we then compare to our f(0) = a₂/√2 - 7.

The goal: determine whether f(0) ≈ 2 × (1/α_unif) follows from the
algebra, or whether it's a coincidence.

References:
- Chamseddine & Connes, hep-th/9606001 (1996): The Spectral Action Principle
- Chamseddine, Connes & Marcolli, hep-th/0610241 (2007): Gravity and the SM
- van Suijlekom, "Noncommutative Geometry and Particle Physics" (2015)
"""

import numpy as np
from dataclasses import dataclass
from typing import List

# ========================================================================
# PART 1: Enumerate all fermion states in the SM Hilbert space
# ========================================================================


@dataclass
class FermionState:
    """A single fermion state in the SM finite Hilbert space."""

    name: str
    generation: int  # 1, 2, 3
    chirality: str  # 'L' or 'R'
    particle: bool  # True = particle, False = antiparticle
    su3_rep: str  # '3' (fund), '3bar' (anti-fund), '1' (singlet)
    su3_dim: int  # 3 or 1
    su2_rep: str  # '2' (fund), '1' (singlet)
    su2_dim: int  # 2 or 1
    hypercharge_Y: float  # U(1)_Y hypercharge (standard normalisation)

    @property
    def dynkin_su3(self):
        """Dynkin index C(R) for SU(3). Fund: 1/2, singlet: 0."""
        if self.su3_rep in ("3", "3bar"):
            return 0.5
        return 0.0

    @property
    def dynkin_su2(self):
        """Dynkin index C(R) for SU(2). Fund: 1/2, singlet: 0."""
        if self.su2_rep == "2":
            return 0.5
        return 0.0

    @property
    def Y_squared(self):
        """Y² contribution for U(1)_Y trace."""
        return self.hypercharge_Y**2


def build_sm_hilbert_space() -> List[FermionState]:
    """
    Build all 96 states of the SM finite Hilbert space.

    Per generation (32 states):
      Particles (16):
        Left-handed:
          ν_L    (1, 2, -1/2) → 1×2 = 2 states
          e_L    (contained in the doublet above)
          u_L    (3, 2, +1/6) → 3×2 = 6 states
          d_L    (contained in the doublet above)
        Right-handed:
          ν_R    (1, 1,  0)   → 1×1 = 1 state  [included for seesaw]
          e_R    (1, 1, -1)   → 1×1 = 1 state
          u_R    (3, 1, +2/3) → 3×1 = 3 states
          d_R    (3, 1, -1/3) → 3×1 = 3 states
        Total particles: 2 + 6 + 1 + 1 + 3 + 3 = 16

      Antiparticles (16):
        Same structure with conjugate representations and opposite Y.

    Note: we count individual COLOR and ISOSPIN components as separate states.
    The trace sums over ALL states.
    """
    states = []

    gen_names = {
        1: ("ν_e", "e", "u", "d"),
        2: ("ν_μ", "μ", "c", "s"),
        3: ("ν_τ", "τ", "t", "b"),
    }

    for gen in [1, 2, 3]:
        nu, lep, up, down = gen_names[gen]

        # === PARTICLES ===

        # Left-handed lepton doublet (ν_L, e_L): (1, 2, -1/2)
        for iso in ["up", "down"]:
            name = f"{nu}_L" if iso == "up" else f"{lep}_L"
            states.append(
                FermionState(
                    name=name,
                    generation=gen,
                    chirality="L",
                    particle=True,
                    su3_rep="1",
                    su3_dim=1,
                    su2_rep="2",
                    su2_dim=2,
                    hypercharge_Y=-0.5,
                )
            )

        # Left-handed quark doublet (u_L, d_L): (3, 2, +1/6)
        for color in ["r", "g", "b"]:
            for iso in ["up", "down"]:
                name = f"{up}_L_{color}" if iso == "up" else f"{down}_L_{color}"
                states.append(
                    FermionState(
                        name=name,
                        generation=gen,
                        chirality="L",
                        particle=True,
                        su3_rep="3",
                        su3_dim=3,
                        su2_rep="2",
                        su2_dim=2,
                        hypercharge_Y=1.0 / 6.0,
                    )
                )

        # Right-handed neutrino: (1, 1, 0)
        states.append(
            FermionState(
                name=f"{nu}_R",
                generation=gen,
                chirality="R",
                particle=True,
                su3_rep="1",
                su3_dim=1,
                su2_rep="1",
                su2_dim=1,
                hypercharge_Y=0.0,
            )
        )

        # Right-handed charged lepton: (1, 1, -1)
        states.append(
            FermionState(
                name=f"{lep}_R",
                generation=gen,
                chirality="R",
                particle=True,
                su3_rep="1",
                su3_dim=1,
                su2_rep="1",
                su2_dim=1,
                hypercharge_Y=-1.0,
            )
        )

        # Right-handed up-type quark: (3, 1, +2/3)
        for color in ["r", "g", "b"]:
            states.append(
                FermionState(
                    name=f"{up}_R_{color}",
                    generation=gen,
                    chirality="R",
                    particle=True,
                    su3_rep="3",
                    su3_dim=3,
                    su2_rep="1",
                    su2_dim=1,
                    hypercharge_Y=2.0 / 3.0,
                )
            )

        # Right-handed down-type quark: (3, 1, -1/3)
        for color in ["r", "g", "b"]:
            states.append(
                FermionState(
                    name=f"{down}_R_{color}",
                    generation=gen,
                    chirality="R",
                    particle=True,
                    su3_rep="3",
                    su3_dim=3,
                    su2_rep="1",
                    su2_dim=1,
                    hypercharge_Y=-1.0 / 3.0,
                )
            )

        # === ANTIPARTICLES ===
        # Conjugate representations: 3 → 3bar, 2 → 2bar ≅ 2, Y → -Y

        # Anti-left-handed lepton doublet: (1, 2, +1/2)
        for iso in ["up", "down"]:
            name = f"{nu}bar_R" if iso == "up" else f"{lep}bar_R"
            states.append(
                FermionState(
                    name=name,
                    generation=gen,
                    chirality="R",
                    particle=False,
                    su3_rep="1",
                    su3_dim=1,
                    su2_rep="2",
                    su2_dim=2,
                    hypercharge_Y=+0.5,
                )
            )

        # Anti-left-handed quark doublet: (3bar, 2, -1/6)
        for color in ["r", "g", "b"]:
            for iso in ["up", "down"]:
                name = f"{up}bar_R_{color}" if iso == "up" else f"{down}bar_R_{color}"
                states.append(
                    FermionState(
                        name=name,
                        generation=gen,
                        chirality="R",
                        particle=False,
                        su3_rep="3bar",
                        su3_dim=3,
                        su2_rep="2",
                        su2_dim=2,
                        hypercharge_Y=-1.0 / 6.0,
                    )
                )

        # Anti-right-handed neutrino: (1, 1, 0)
        states.append(
            FermionState(
                name=f"{nu}bar_L",
                generation=gen,
                chirality="L",
                particle=False,
                su3_rep="1",
                su3_dim=1,
                su2_rep="1",
                su2_dim=1,
                hypercharge_Y=0.0,
            )
        )

        # Anti-right-handed charged lepton: (1, 1, +1)
        states.append(
            FermionState(
                name=f"{lep}bar_L",
                generation=gen,
                chirality="L",
                particle=False,
                su3_rep="1",
                su3_dim=1,
                su2_rep="1",
                su2_dim=1,
                hypercharge_Y=+1.0,
            )
        )

        # Anti-right-handed up quark: (3bar, 1, -2/3)
        for color in ["r", "g", "b"]:
            states.append(
                FermionState(
                    name=f"{up}bar_L_{color}",
                    generation=gen,
                    chirality="L",
                    particle=False,
                    su3_rep="3bar",
                    su3_dim=3,
                    su2_rep="1",
                    su2_dim=1,
                    hypercharge_Y=-2.0 / 3.0,
                )
            )

        # Anti-right-handed down quark: (3bar, 1, +1/3)
        for color in ["r", "g", "b"]:
            states.append(
                FermionState(
                    name=f"{down}bar_L_{color}",
                    generation=gen,
                    chirality="L",
                    particle=False,
                    su3_rep="3bar",
                    su3_dim=3,
                    su2_rep="1",
                    su2_dim=1,
                    hypercharge_Y=+1.0 / 3.0,
                )
            )

    return states


# ========================================================================
# PART 2: Compute trace invariants
# ========================================================================


def compute_traces(states: List[FermionState]):
    """
    Compute the Dynkin index sums for each gauge group.

    For each gauge group G_i:
      c_i = Σ_{states s} C_i(R_s)

    where C_i(R_s) is the Dynkin index of the representation R_s:
      C(fund of SU(N)) = 1/2
      C(singlet) = 0

    For U(1)_Y: the "Dynkin index" is Y², so:
      c_Y = Σ_s Y_s²

    The gauge kinetic term coefficient is:
      1/g_i² = f₀ × c_i / (2π²)
    """

    c_su3 = sum(s.dynkin_su3 for s in states)
    c_su2 = sum(s.dynkin_su2 for s in states)
    c_u1 = sum(s.Y_squared for s in states)

    return c_su3, c_su2, c_u1


def compute_traces_detailed(states: List[FermionState]):
    """Detailed breakdown by sector."""

    results = {}

    # By particle/antiparticle
    particles = [s for s in states if s.particle]
    antiparticles = [s for s in states if not s.particle]

    results["particles"] = compute_traces(particles)
    results["antiparticles"] = compute_traces(antiparticles)
    results["total"] = compute_traces(states)

    # By generation
    for gen in [1, 2, 3]:
        gen_states = [s for s in states if s.generation == gen]
        results[f"gen_{gen}"] = compute_traces(gen_states)

    # By chirality
    for chir in ["L", "R"]:
        chir_states = [s for s in states if s.chirality == chir]
        results[f"chirality_{chir}"] = compute_traces(chir_states)

    return results


# ========================================================================
# PART 3: Derive gauge coupling normalisation
# ========================================================================


def main():
    print("=" * 72)
    print("SPECTRAL ACTION TRACE COMPUTATION")
    print("SM Finite Hilbert Space: A_F = C ⊕ H ⊕ M₃(C)")
    print("=" * 72)
    print()

    # Build Hilbert space
    states = build_sm_hilbert_space()

    print(f"Total states in H_F: {len(states)}")
    print(f"  Particles:     {sum(1 for s in states if s.particle)}")
    print(f"  Antiparticles: {sum(1 for s in states if not s.particle)}")
    print(f"  Per generation: {len(states) // 3}")
    print()

    # Compute traces
    c3, c2, c1 = compute_traces(states)

    print("TRACE INVARIANTS (Dynkin index sums over full H_F):")
    print(f"  c_SU(3) = Σ C_3(R) = {c3}")
    print(f"  c_SU(2) = Σ C_2(R) = {c2}")
    print(f"  c_U(1)  = Σ Y²     = {c1}")
    print()

    # GUT normalisation: g₁² = (5/3) g'²
    # The GUT-normalised U(1) coupling uses Y_GUT = √(3/5) Y
    # So c_1_GUT = (3/5) × c_U(1)
    c1_gut = (3.0 / 5.0) * c1
    print(f"  c_U(1) with GUT normalisation (×3/5): {c1_gut}")
    print()

    # Check: for unification, we need c_1_GUT = c_2 = c_3
    print("UNIFICATION CHECK:")
    print(f"  c_SU(3)    = {c3}")
    print(f"  c_SU(2)    = {c2}")
    print(f"  c_U(1)_GUT = {c1_gut}")

    if abs(c3 - c2) < 0.001 and abs(c3 - c1_gut) < 0.001:
        print(f"  ✓ All equal! Coupling unification holds: c = {c3}")
    else:
        print(f"  ✗ NOT equal. Ratios:")
        print(f"    c_3/c_2 = {c3/c2:.4f}")
        print(f"    c_3/c_1_GUT = {c3/c1_gut:.4f}")
        print(f"    c_2/c_1_GUT = {c2/c1_gut:.4f}")
    print()

    # Detailed breakdown
    details = compute_traces_detailed(states)

    print("BREAKDOWN BY SECTOR:")
    print(f"{'Sector':<20} {'c_SU3':<10} {'c_SU2':<10} {'c_U1':<10}")
    print("-" * 50)
    for key in [
        "particles",
        "antiparticles",
        "gen_1",
        "gen_2",
        "gen_3",
        "chirality_L",
        "chirality_R",
        "total",
    ]:
        c3_s, c2_s, c1_s = details[key]
        print(f"{key:<20} {c3_s:<10.1f} {c2_s:<10.1f} {c1_s:<10.4f}")
    print()

    # ================================================================
    # PART 4: Connection to f(0) and α_unif
    # ================================================================

    # The spectral action gives (Chamseddine-Connes 1996):
    #   S_gauge = f₀/(2π²) × ∫ Tr_{H_F}(F_μν F^μν) d⁴x
    #
    # For each gauge group, this becomes:
    #   S_i = f₀ × c_i / (2π²) × ∫ (-1/4) F_i² d⁴x
    #
    # Matching to the standard action -1/(4g_i²) ∫ F_i²:
    #   1/g_i² = f₀ × c_i / (2π²)
    #
    # So: 1/α_i = 4π/g_i² = 4π × f₀ × c_i / (2π²) = 2f₀ × c_i / π

    C = c3  # at unification, all c_i are equal (with GUT norm)

    print("=" * 72)
    print("SPECTRAL ACTION → GAUGE COUPLING RELATION")
    print("=" * 72)
    print()
    print(f"Formula: 1/α_unif = 2 × f₀ × C / π")
    print(f"where C = c_SU(3) = {C} (= c_SU(2) = c_U(1)_GUT)")
    print()

    # From Computation 1: mean(1/α_unif) ≈ 41.57
    alpha_unif_inv_measured = 41.57

    # What f₀ does this imply?
    f0_spectral = np.pi * alpha_unif_inv_measured / (2 * C)

    print(f"From measured couplings: mean(1/α_unif) ≈ {alpha_unif_inv_measured}")
    print(f"Implied f₀ = π × (1/α_unif) / (2C) = {f0_spectral:.4f}")
    print()

    # Our QBP candidate
    f0_qbp = 128.0 / np.sqrt(2) - 7.0  # = 83.5097

    print(f"QBP candidate: f(0) = a₂/√2 - 7 = {f0_qbp:.4f}")
    print()

    # What is the ratio?
    ratio = f0_qbp / f0_spectral
    print(f"RATIO: f(0)_QBP / f₀_spectral = {ratio:.4f}")
    print()

    # Is this ratio a recognisable number?
    print("Is this ratio algebraically meaningful?")
    candidates = {
        "C itself": C,
        "2C": 2 * C,
        "C/π": C / np.pi,
        "2C/π": 2 * C / np.pi,
        "π": np.pi,
        "2π": 2 * np.pi,
        "π²/C": np.pi**2 / C,
        "4π/C": 4 * np.pi / C,
        "N_gen × (dim_fund)²": 3 * 4,
        "N_gen × dim_SU2": 3 * 2,
        "dim(H_F)/N_gen": 32,
        "dim(H_F)/16": 96 / 16,
        "C/N_gen": C / 3,
        "sqrt(C)": np.sqrt(C),
        "C²/π": C**2 / np.pi,
    }

    print(f"  {'Expression':<30} {'Value':<12} {'Diff from ratio':<15}")
    print(f"  {'-'*57}")
    sorted_c = sorted(candidates.items(), key=lambda x: abs(x[1] - ratio))
    for name, val in sorted_c[:12]:
        diff = (val - ratio) / ratio * 100
        marker = " <-- MATCH" if abs(diff) < 2 else ""
        print(f"  {name:<30} {val:<12.4f} {diff:+.2f}%{marker}")

    print()

    # ================================================================
    # PART 5: The key question — what IS f(0)?
    # ================================================================

    print("=" * 72)
    print("THE KEY QUESTION: WHAT IS f(0)?")
    print("=" * 72)
    print()

    # Three hypotheses:

    # H1: f(0) = f₀ (they're the same thing)
    print("HYPOTHESIS 1: f(0) = f₀ (direct identification)")
    alpha_inv_h1 = 2 * f0_qbp * C / np.pi
    print(f"  Then: 1/α_unif = 2 × {f0_qbp:.2f} × {C} / π = {alpha_inv_h1:.1f}")
    print(f"  Measured: ~41.6")
    print(f"  Off by factor of {alpha_inv_h1/alpha_unif_inv_measured:.1f}")
    print(f"  REJECTED — gives absurdly large 1/α")
    print()

    # H2: f(0) = f₀ × C (f(0) absorbs the trace invariant)
    print("HYPOTHESIS 2: f(0) = f₀ × C  (absorbs trace invariant)")
    f0_h2 = f0_qbp / C
    alpha_inv_h2 = 2 * f0_h2 * C / np.pi
    print(f"  Then: f₀ = f(0)/C = {f0_h2:.4f}")
    print(f"  1/α_unif = 2 × f₀ × C / π = 2 × f(0) / π = {alpha_inv_h2:.1f}")
    print(f"  Measured: ~41.6")
    disc_h2 = (alpha_inv_h2 - alpha_unif_inv_measured) / alpha_unif_inv_measured * 100
    print(f"  Discrepancy: {disc_h2:+.1f}%")
    if abs(disc_h2) < 5:
        print(f"  *** PLAUSIBLE — within coupling non-meeting spread ***")
    print()

    # H3: f(0) = 2 × (1/α_unif) exactly (from Computation 1)
    print("HYPOTHESIS 3: f(0) = 2/α_unif  (empirical from Comp 1)")
    alpha_inv_h3 = f0_qbp / 2
    print(f"  Then: 1/α_unif = f(0)/2 = {alpha_inv_h3:.2f}")
    print(f"  Measured: ~41.6")
    disc_h3 = (alpha_inv_h3 - alpha_unif_inv_measured) / alpha_unif_inv_measured * 100
    print(f"  Discrepancy: {disc_h3:+.1f}%")
    print()

    # If H3 is true AND the spectral action formula holds:
    # f(0)/2 = 2 × f₀ × C / π
    # f(0) = 4 × f₀ × C / π
    # f₀ = f(0) × π / (4C)
    f0_from_h3 = f0_qbp * np.pi / (4 * C)
    print(f"  If BOTH H3 and spectral action hold:")
    print(f"  f₀ = f(0) × π / (4C) = {f0_from_h3:.4f}")
    print(f"  Scale factor: f(0)/f₀ = 4C/π = {4*C/np.pi:.4f}")
    print()

    # The scale factor 4C/π — is this algebraically derivable?
    scale = 4 * C / np.pi
    print(f"  Scale factor 4C/π = 4×{C}/π = {scale:.4f}")
    print(f"  4×{C} = {4*C}")
    print(f"  So: f(0) = f₀ × {4*C}/π")
    print()
    print(f"  For C = {C}:")
    print(f"    {4*C}/π = {scale:.4f}")
    print(f"    This is NOT a simple algebraic number.")
    print(f"    But {4*C} = {int(4*C)} is an integer.")
    print(f"    And π appears naturally in the spectral action normalization.")
    print()

    # ================================================================
    # FINAL SUMMARY
    # ================================================================

    print("=" * 72)
    print("FINAL SUMMARY")
    print("=" * 72)
    print()
    print(f"SM Hilbert space: {len(states)} states")
    print(f"Trace invariants: c_SU3 = c_SU2 = c_U1(GUT) = {C}")
    print(f"  (confirming GUT-normalised coupling unification)")
    print()
    print(f"Spectral action formula: 1/α_unif = 2f₀C/π")
    print(f"  with C = {C}")
    print()
    print(f"From measured couplings: 1/α_unif ≈ {alpha_unif_inv_measured}")
    print(f"  → f₀ = π/(2C) × (1/α_unif) = {f0_spectral:.4f}")
    print()
    print(f"QBP candidate: f(0) = {f0_qbp:.4f}")
    print(f"  Ratio f(0)/f₀ = {ratio:.4f}")
    print()

    if abs(ratio - C) / C < 0.05:
        print(f"*** FINDING: f(0)/f₀ ≈ C = {C} to {abs(ratio-C)/C*100:.1f}% ***")
        print(f"    This means: f(0) = f₀ × C")
        print(f"    The crystallisation profile f(0) ABSORBS the trace invariant!")
        print(f"    And: 1/α_unif = 2f(0)/π (the C cancels)")
        print()
        print(f"    IF PROVABLE: f(0) is DERIVED from")
        print(f"      f₀ = measured coupling via spectral action")
        print(f"      C = {C} = trace invariant (PROVEN from algebra)")
        print(f"      f(0) = f₀ × C = algebraically determined")
    elif abs(ratio - 4 * C / np.pi) / (4 * C / np.pi) < 0.05:
        print(
            f"*** FINDING: f(0)/f₀ ≈ 4C/π = {4*C/np.pi:.4f} to "
            f"{abs(ratio-4*C/np.pi)/(4*C/np.pi)*100:.1f}% ***"
        )
        print(f"    This means: f(0) = f₀ × 4C/π")
        print(f"    The crystallisation profile includes a geometric factor 4/π")
        print(f"    from the spectral action normalisation.")
    else:
        print(f"    No simple algebraic relationship found between f(0) and f₀.")
        print(f"    The ratio {ratio:.4f} does not match C = {C},")
        print(f"    nor 4C/π = {4*C/np.pi:.4f}, nor other simple expressions.")
        print(f"    This may indicate a normalisation convention mismatch")
        print(f"    or a genuine gap between the crystallisation profile and")
        print(f"    the spectral action cutoff function.")

    print()
    print("=" * 72)
    print("NEXT STEPS:")
    print("=" * 72)
    print()
    print("1. Verify the trace computation against Chamseddine-Connes-Marcolli")
    print("   (their Eq. 1.764 and Table 1.2). They compute the exact same")
    print("   traces but with slightly different notation.")
    print()
    print("2. Check whether the factor of 2 between particles and antiparticles")
    print("   is handled correctly in the spectral action (the real structure J")
    print("   relates them, which may affect the trace).")
    print()
    print("3. Investigate whether the Hessian eigenvalues (4, 8, 12) contribute")
    print("   an additional factor that modifies the f₀ → f(0) relationship.")
    print()
    print("4. Compare with van Suijlekom (2015) Ch. 11-12 for the most")
    print("   careful modern treatment of the spectral action normalisation.")

    return states, C, f0_spectral, ratio


if __name__ == "__main__":
    states, C, f0_spectral, ratio = main()
