# experiments/03_double_slit/simulate.py
"""
Double-Slit Interference Simulation (Experiment 03)

This experiment validates QBP predictions for double-slit interference
with quaternionic wavefunctions. Three scenarios:

  A: Complex baseline (standard QM) — analytical
  B: Which-path detection (no interference) — analytical
  C: Full quaternionic dynamics (Adler decay) — 2D BPM

Ground truth: research/03_double_slit_expected_results.md
Sprint 3 | Phase 2: Implementation

Usage:
    python experiments/03_double_slit/simulate.py
"""

import numpy as np
import pandas as pd
import sys
import os
from datetime import datetime

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from src.simulation.analytical_double_slit import (
    SlitParameters,
    fraunhofer_pattern,
    which_path_pattern,
    fringe_visibility,
)
from src.simulation.wave_propagation import (
    SimulationConfig,
    SlitConfig,
    create_transverse_grid,
    create_initial_wavepacket,
    propagate,
    far_field_intensity,
    compute_eta,
)


# ---------------------------------------------------------------------------
# Default parameters
# ---------------------------------------------------------------------------

# Physical parameters (natural units for BPM)
BPM_CONFIG = SimulationConfig(
    Nx=2048,
    X_max=15.0,
    dz=0.02,
    Nz_steps=10000,
    k0=30.0,
    hbar=1.0,
    mass=0.5,
    device="cpu",
    snapshot_interval=1000,
)

BPM_SLIT = SlitConfig(
    separation=2.0,
    width=0.3,
    barrier_height=100.0,
    U1_strength=0.0,  # set per scenario
    z_position=50.0,
    z_thickness=1.0,
)

# Analytical parameters (SI units)
ANALYTICAL_PARAMS = SlitParameters(
    d=1.0e-6,  # 1 μm slit separation
    a=0.1e-6,  # 0.1 μm slit width
    wavelength=0.05e-9,  # 0.05 nm electron wavelength
    L=1.0,  # 1 m screen distance
)

# U₁ values for parameter sweep
U1_VALUES = [0.0, 0.5, 1.0, 2.0, 5.0, 10.0]

# Initial quaternionic fractions
ETA0_VALUES = [0.01, 0.1, 0.5]


# ---------------------------------------------------------------------------
# Scenario runners
# ---------------------------------------------------------------------------


def run_scenario_a():
    """
    Scenario A: Complex baseline (no quaternionic components).

    Uses analytical Fraunhofer formula. No BPM needed.
    """
    print("\n--- Scenario A: Complex Baseline (Analytical) ---")

    x = np.linspace(-5e-3, 5e-3, 10001)
    I = fraunhofer_pattern(x, ANALYTICAL_PARAMS)
    V = fringe_visibility(I)

    print(f"  Fringe spacing: {ANALYTICAL_PARAMS.fringe_spacing*1e6:.1f} μm")
    print(f"  Visibility: {V:.4f}")
    print(f"  Grid points: {len(x)}")

    rows = []
    for xi, Ii in zip(x, I):
        rows.append(
            {
                "scenario": "A",
                "U1_strength": 0.0,
                "eta0": 0.0,
                "x_position": xi,
                "intensity_total": Ii,
                "intensity_psi0": Ii,
                "intensity_psi1": 0.0,
            }
        )

    return pd.DataFrame(rows), V


def run_scenario_b():
    """
    Scenario B: Which-path detection (incoherent sum).

    Uses analytical formula. No BPM needed.
    Visibility measured in central region (fringe-scale resolution).
    """
    print("\n--- Scenario B: Which-Path (Analytical) ---")

    x = np.linspace(-5e-3, 5e-3, 10001)
    I = which_path_pattern(x, ANALYTICAL_PARAMS)

    # Measure visibility in central region at fringe scale
    x_central = np.linspace(-3e-4, 3e-4, 100000)
    I_central = which_path_pattern(x_central, ANALYTICAL_PARAMS)
    V = fringe_visibility(I_central)

    print(f"  Visibility: {V:.6f}")

    rows = []
    for xi, Ii in zip(x, I):
        rows.append(
            {
                "scenario": "B",
                "U1_strength": 0.0,
                "eta0": 0.0,
                "x_position": xi,
                "intensity_total": Ii,
                "intensity_psi0": Ii,
                "intensity_psi1": 0.0,
            }
        )

    return pd.DataFrame(rows), V


def run_scenario_c(u1_strength, eta0, config=None, slit=None):
    """
    Scenario C: Full quaternionic propagation via BPM.

    Args:
        u1_strength: quaternionic coupling strength
        eta0: initial quaternionic fraction
        config: simulation config (default: BPM_CONFIG)
        slit: slit config (default: BPM_SLIT)

    Returns:
        (fringe_df, decay_df, visibility)
    """
    if config is None:
        config = BPM_CONFIG
    if slit is None:
        slit = SlitConfig(
            separation=BPM_SLIT.separation,
            width=BPM_SLIT.width,
            barrier_height=BPM_SLIT.barrier_height,
            U1_strength=u1_strength,
            z_position=BPM_SLIT.z_position,
            z_thickness=BPM_SLIT.z_thickness,
        )

    grid = create_transverse_grid(config)
    psi0, psi1 = create_initial_wavepacket(grid, k0=config.k0, sigma=3.0, eta0=eta0)

    result = propagate(psi0, psi1, grid, config, slit=slit)

    # Intensity at detector
    x, I_total, I_psi0, I_psi1 = far_field_intensity(result)
    V = fringe_visibility(I_total)

    # Norm check
    final_norm = result.norm_history[-1] if result.norm_history else 1.0

    print(
        f"  U₁={u1_strength:.1f}, η₀={eta0:.2f}: "
        f"V={V:.4f}, η_final={result.decay_curve[-1][1]:.6f}, "
        f"norm={final_norm:.8f}"
    )

    # Fringe data
    fringe_rows = []
    for xi, It, I0, I1 in zip(x, I_total, I_psi0, I_psi1):
        fringe_rows.append(
            {
                "scenario": "C",
                "U1_strength": u1_strength,
                "eta0": eta0,
                "x_position": xi,
                "intensity_total": It,
                "intensity_psi0": I0,
                "intensity_psi1": I1,
            }
        )

    # Decay data
    decay_rows = []
    for z_val, eta_val in result.decay_curve:
        decay_rows.append(
            {
                "U1_strength": u1_strength,
                "eta0": eta0,
                "z": z_val,
                "eta_fraction": eta_val,
            }
        )

    return pd.DataFrame(fringe_rows), pd.DataFrame(decay_rows), V


# ---------------------------------------------------------------------------
# Main orchestration
# ---------------------------------------------------------------------------


def main():
    """Run all scenarios and save results."""
    print("=" * 70)
    print("DOUBLE-SLIT INTERFERENCE SIMULATION")
    print("Experiment 03 — Sprint 3 Phase 2")
    print("=" * 70)
    print(f"Started: {datetime.now().isoformat()}")
    print(
        f"BPM config: Nx={BPM_CONFIG.Nx}, Nz={BPM_CONFIG.Nz_steps}, "
        f"dz={BPM_CONFIG.dz}"
    )
    print(f"Device: {BPM_CONFIG.device}")

    all_fringe_dfs = []
    all_decay_dfs = []
    summary_rows = []

    # Scenario A
    df_a, V_a = run_scenario_a()
    all_fringe_dfs.append(df_a)
    summary_rows.append(
        {
            "scenario": "A",
            "U1_strength": 0.0,
            "eta0": 0.0,
            "visibility": V_a,
            "norm_final": 1.0,
        }
    )

    # Scenario B
    df_b, V_b = run_scenario_b()
    all_fringe_dfs.append(df_b)
    summary_rows.append(
        {
            "scenario": "B",
            "U1_strength": 0.0,
            "eta0": 0.0,
            "visibility": V_b,
            "norm_final": 1.0,
        }
    )

    # Scenario C: parameter sweep
    print("\n--- Scenario C: Quaternionic BPM (Parameter Sweep) ---")
    for u1 in U1_VALUES:
        for eta0 in ETA0_VALUES:
            fringe_df, decay_df, V_c = run_scenario_c(u1, eta0)
            all_fringe_dfs.append(fringe_df)
            all_decay_dfs.append(decay_df)
            summary_rows.append(
                {
                    "scenario": "C",
                    "U1_strength": u1,
                    "eta0": eta0,
                    "visibility": V_c,
                    "norm_final": fringe_df["intensity_total"].sum(),
                }
            )

    # Combine and save
    output_dir = "results/03_double_slit"
    os.makedirs(output_dir, exist_ok=True)
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")

    # Fringe CSV
    fringe_df = pd.concat(all_fringe_dfs, ignore_index=True)
    fringe_path = os.path.join(output_dir, f"fringe_data_{timestamp}.csv")
    fringe_df.to_csv(fringe_path, index=False)
    print(f"\nFringe data: {fringe_path} ({len(fringe_df)} rows)")

    # Decay CSV
    if all_decay_dfs:
        decay_df = pd.concat(all_decay_dfs, ignore_index=True)
        decay_path = os.path.join(output_dir, f"decay_data_{timestamp}.csv")
        decay_df.to_csv(decay_path, index=False)
        print(f"Decay data: {decay_path} ({len(decay_df)} rows)")

    # Summary
    summary_df = pd.DataFrame(summary_rows)
    summary_path = os.path.join(output_dir, f"summary_{timestamp}.csv")
    summary_df.to_csv(summary_path, index=False)
    print(f"Summary: {summary_path}")

    # Print summary table
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"\n{'Scenario':<12} {'U₁':<8} {'η₀':<8} {'Visibility':<12}")
    print("-" * 40)
    for _, row in summary_df.iterrows():
        print(
            f"{row['scenario']:<12} {row['U1_strength']:<8.1f} "
            f"{row['eta0']:<8.2f} {row['visibility']:<12.4f}"
        )

    # Checks
    print("\n" + "=" * 70)
    print("ACCEPTANCE CRITERIA CHECKS")
    print("=" * 70)

    checks = [
        ("AC #5: Scenario A visibility > 0.95", V_a > 0.95, f"V_A = {V_a:.4f}"),
        ("AC #4: Scenario B visibility < 0.01", V_b < 0.01, f"V_B = {V_b:.6f}"),
    ]

    all_passed = True
    for name, passed, detail in checks:
        status = "PASS" if passed else "FAIL"
        print(f"  [{status}] {name} ({detail})")
        if not passed:
            all_passed = False

    print("\n" + "=" * 70)
    if all_passed:
        print("ALL CHECKS PASSED")
    else:
        print("SOME CHECKS FAILED")
    print("=" * 70)
    print(f"Completed: {datetime.now().isoformat()}")

    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
