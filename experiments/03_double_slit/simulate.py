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

import json
import numpy as np
import pandas as pd
import sys
import os
from dataclasses import dataclass
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
    far_field_from_bpm,
    FarFieldResult,
    compute_eta,
)
from src.simulation.si_conversion import (
    V_Z_CODE,
    compute_scales,
    convert_position,
    convert_potential,
)


# ---------------------------------------------------------------------------
# Default parameters
# ---------------------------------------------------------------------------
#
# BPM parameters use natural units (ℏ=1, m=0.5) for numerical convenience.
# The physics is scale-invariant; what matters is the dimensionless ratios:
#   - k0 * slit_width ≈ 9 (several wavelengths per slit → Fraunhofer regime)
#   - barrier_height / kinetic_energy ≈ 3.3 (opaque barrier)
#   - U1_strength / kinetic_energy = 0–0.33 (coupling sweep)
#   - Total propagation = Nz*dz = 200 units (>> slit region, far-field reached)
#
# Analytical parameters use SI units for direct comparison with literature
# (Kaiser 1984 neutron bound: ~10⁻¹² eV; Procopio 2017 photon bound).
#
# See docs/design/experiment_03_alternatives.md for parameter space discussion.
#

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

# U₁ values for parameter sweep (BPM code units)
#
# ACCELERATED TEST VALUES — the BPM domain (~32 nm) is too small for
# physical U₁ values (10⁻¹⁵ to 10⁻³ eV) to produce visible effects.
# Physical L_decay at U₁ = 10⁻⁶ eV is ~9.6 mm >> 32 nm domain.
#
# SI mapping (via convert_potential with V_Z_CODE = 40.0):
#   U1_code=0.5  → 30.1 eV    U1_code=5.0  → 300.8 eV
#   U1_code=1.0  → 60.2 eV    U1_code=10.0 → 601.7 eV
#   U1_code=2.0  → 120.3 eV
#
# The physics is scale-invariant: decay, monotonicity, norm conservation,
# and U₁=0 control behavior are identical at any U₁ scale.
# See ground truth §4.3.3 for physical SI worked examples.
#
# Rotation angle per step: θ = U₁·dz/ℏ. At max U₁=10, dz=0.02:
#   θ_max = 0.2 rad/step (< π/4 ≈ 0.785, no aliasing risk).
U1_VALUES = [0.0, 0.5, 1.0, 2.0, 5.0, 10.0]

# Initial quaternionic fractions
ETA0_VALUES = [0.01, 0.1, 0.5]

# ---------------------------------------------------------------------------
# SI conversion scales
# ---------------------------------------------------------------------------
# Electron with 0.05 nm de Broglie wavelength (matches analytical params).
# Note: BPM uses k0=30 not the default K0_CODE=20 — but the scale factors
# are particle properties, not BPM parameters. The BPM k0 only controls the
# number of grid points per wavelength (resolution), not the physical scale.
M_ELECTRON = 9.109_383_7015e-31  # kg (CODATA 2018)
LAMBDA_ELECTRON = 0.05e-9  # m (de Broglie wavelength)
SI_SCALES = compute_scales(M_ELECTRON, LAMBDA_ELECTRON)


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
                "U1_strength_eV": 0.0,
                "eta0": 0.0,
                "x_position_m": xi,
                "intensity_total_normalized": Ii,
                "intensity_psi0_normalized": Ii,
                "intensity_psi1_normalized": 0.0,
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
                "U1_strength_eV": 0.0,
                "eta0": 0.0,
                "x_position_m": xi,
                "intensity_total_normalized": Ii,
                "intensity_psi0_normalized": Ii,
                "intensity_psi1_normalized": 0.0,
            }
        )

    return pd.DataFrame(rows), V


@dataclass
class ScenarioCResult:
    """Results from a Scenario C (BPM + far-field FFT) run."""

    fringe_df: pd.DataFrame
    decay_df: pd.DataFrame
    visibility: float
    norm_final: float
    farfield_fringe_df: pd.DataFrame
    visibility_farfield: float


def run_scenario_c(u1_strength, eta0, config=None, slit=None):
    """
    Scenario C: Full quaternionic propagation via BPM.

    Args:
        u1_strength: quaternionic coupling strength
        eta0: initial quaternionic fraction
        config: simulation config (default: BPM_CONFIG)
        slit: slit config (default: BPM_SLIT)

    Returns:
        ScenarioCResult with near-field, far-field, and decay data.
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

    # Near-field intensity at BPM exit plane
    x, I_total, I_psi0, I_psi1 = far_field_intensity(result)
    V = fringe_visibility(I_total)

    # Far-field: Fraunhofer FFT of exit-plane amplitudes
    # The QBP visibility reduction (ΔV) is similar in near-field and far-field
    # (~8% relative). This is expected: the Fraunhofer transform is linear and
    # preserves the relative fringe contrast degradation from quaternionic coupling.
    dx_si = grid.dx * SI_SCALES.L0  # code units → SI metres
    slit_sep_si = slit.separation * SI_SCALES.L0
    ff_result = far_field_from_bpm(
        psi0=result.detector_psi0,
        psi1=result.detector_psi1,
        dx_si=dx_si,
        lambda_si=SI_SCALES.lambda_si,
        screen_distance=ANALYTICAL_PARAMS.L,  # 1.0 m — same as analytical
        pad_factor=4,
        slit_separation_si=slit_sep_si,
    )
    V_farfield = fringe_visibility(ff_result.I_total)

    # Norm check
    final_norm = result.norm_history[-1] if result.norm_history else 1.0

    print(
        f"  U₁={u1_strength:.1f}, η₀={eta0:.2f}: "
        f"V_nf={V:.4f}, V_ff={V_farfield:.4f}, "
        f"η_final={result.decay_curve[-1][1]:.6f}, "
        f"norm={final_norm:.8f}"
    )

    # Convert U1 to SI (eV) at output boundary
    u1_eV = convert_potential(u1_strength, SI_SCALES)

    # Near-field fringe data — convert x_position from code units to SI metres
    fringe_rows = []
    for xi, It, I0, I1 in zip(x, I_total, I_psi0, I_psi1):
        fringe_rows.append(
            {
                "scenario": "C",
                "U1_strength_eV": u1_eV,
                "eta0": eta0,
                "x_position_m": convert_position(xi, SI_SCALES),
                "intensity_total_normalized": It,
                "intensity_psi0_normalized": I0,
                "intensity_psi1_normalized": I1,
            }
        )

    # Far-field fringe data (already in SI metres from FFT)
    farfield_rows = []
    for xi, It, I0, I1 in zip(
        ff_result.x_screen, ff_result.I_total, ff_result.I_psi0, ff_result.I_psi1
    ):
        farfield_rows.append(
            {
                "U1_strength_eV": u1_eV,
                "eta0": eta0,
                "x_position_m": xi,
                "intensity_total_normalized": It,
                "intensity_psi0_normalized": I0,
                "intensity_psi1_normalized": I1,
            }
        )

    # Decay data — convert z from code units to SI metres
    decay_rows = []
    for z_val, eta_val in result.decay_curve:
        decay_rows.append(
            {
                "U1_strength_eV": u1_eV,
                "eta0": eta0,
                "z_m": convert_position(z_val, SI_SCALES),
                "eta_fraction": eta_val,
            }
        )

    return ScenarioCResult(
        fringe_df=pd.DataFrame(fringe_rows),
        decay_df=pd.DataFrame(decay_rows),
        visibility=V,
        norm_final=final_norm,
        farfield_fringe_df=pd.DataFrame(farfield_rows),
        visibility_farfield=V_farfield,
    )


# ---------------------------------------------------------------------------
# Main orchestration
# ---------------------------------------------------------------------------


def main():
    """Run all scenarios and save results.

    Output format v3.0: near-field BPM data (Expected vs QBP) in a single
    self-describing CSV with a ``regime`` column.  Far-field analytical
    data goes to a separate file (different method, spatial scale, grid).
    """
    print("=" * 70)
    print("DOUBLE-SLIT INTERFERENCE SIMULATION")
    print("Experiment 03 — Sprint 3 Phase 2 (v3 format)")
    print("=" * 70)
    print(f"Started: {datetime.now().isoformat()}")
    print(
        f"BPM config: Nx={BPM_CONFIG.Nx}, Nz={BPM_CONFIG.Nz_steps}, "
        f"dz={BPM_CONFIG.dz}"
    )
    print(f"Device: {BPM_CONFIG.device}")

    nearfield_fringe_dfs = []
    farfield_qbp_dfs = []
    decay_dfs = []
    summary_rows = []

    # -----------------------------------------------------------------
    # Near-field BPM runs + far-field Fraunhofer FFT
    # -----------------------------------------------------------------

    # Expected: BPM at U₁=0 (standard QM prediction)
    print("\n--- Expected (BPM at U₁=0) ---")
    for eta0 in ETA0_VALUES:
        r = run_scenario_c(0.0, eta0)
        r.fringe_df["regime"] = "expected"
        r.fringe_df = r.fringe_df.drop(columns=["scenario"])
        r.farfield_fringe_df["regime"] = "expected"
        r.decay_df["regime"] = "expected"
        nearfield_fringe_dfs.append(r.fringe_df)
        farfield_qbp_dfs.append(r.farfield_fringe_df)
        decay_dfs.append(r.decay_df)
        summary_rows.append(
            {
                "regime": "expected",
                "U1_strength_eV": 0.0,
                "eta0": eta0,
                "visibility": r.visibility,
                "visibility_farfield": r.visibility_farfield,
                "norm_final": r.norm_final,
            }
        )

    # QBP: BPM at U₁>0 (quaternionic coupling active)
    print("\n--- QBP (BPM at U₁>0) ---")
    for u1 in U1_VALUES[1:]:  # skip 0.0
        for eta0 in ETA0_VALUES:
            r = run_scenario_c(u1, eta0)
            r.fringe_df["regime"] = "qbp"
            r.fringe_df = r.fringe_df.drop(columns=["scenario"])
            r.farfield_fringe_df["regime"] = "qbp"
            r.decay_df["regime"] = "qbp"
            nearfield_fringe_dfs.append(r.fringe_df)
            farfield_qbp_dfs.append(r.farfield_fringe_df)
            decay_dfs.append(r.decay_df)
            summary_rows.append(
                {
                    "regime": "qbp",
                    "U1_strength_eV": convert_potential(u1, SI_SCALES),
                    "eta0": eta0,
                    "visibility": r.visibility,
                    "visibility_farfield": r.visibility_farfield,
                    "norm_final": r.norm_final,
                }
            )

    # -----------------------------------------------------------------
    # Grid alignment assertion — all BPM runs share identical x-grids
    # -----------------------------------------------------------------
    x_ref = nearfield_fringe_dfs[0]["x_position_m"].values
    for i, df in enumerate(nearfield_fringe_dfs[1:], 1):
        x_check = df["x_position_m"].values
        assert np.array_equal(
            x_ref, x_check
        ), f"Grid mismatch in run {i}: all BPM runs must share identical x-grids"
    print(
        f"\n  Grid alignment verified: {len(nearfield_fringe_dfs)} runs, "
        f"{len(x_ref)} points each"
    )

    # -----------------------------------------------------------------
    # Far-field analytical reference (separate file)
    # -----------------------------------------------------------------
    df_a, V_a = run_scenario_a()
    df_b, V_b = run_scenario_b()
    farfield_df = pd.concat(
        [
            df_a[["scenario", "x_position_m", "intensity_total_normalized"]],
            df_b[["scenario", "x_position_m", "intensity_total_normalized"]],
        ],
        ignore_index=True,
    )
    summary_rows.append(
        {
            "regime": "farfield_A",
            "U1_strength_eV": 0.0,
            "eta0": 0.0,
            "visibility": V_a,
            "norm_final": 1.0,
        }
    )
    summary_rows.append(
        {
            "regime": "farfield_B",
            "U1_strength_eV": 0.0,
            "eta0": 0.0,
            "visibility": V_b,
            "norm_final": 1.0,
        }
    )

    # -----------------------------------------------------------------
    # Save — versioned output directory
    # -----------------------------------------------------------------
    output_dir = "results/03_double_slit/v3"
    os.makedirs(output_dir, exist_ok=True)
    timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")

    # Near-field fringe CSV (primary data file)
    nearfield_df = pd.concat(nearfield_fringe_dfs, ignore_index=True)
    cols = ["regime"] + [c for c in nearfield_df.columns if c != "regime"]
    nearfield_df = nearfield_df[cols]
    nearfield_path = os.path.join(output_dir, f"results_nearfield_{timestamp}.csv")
    nearfield_df.to_csv(nearfield_path, index=False)
    print(f"\nNear-field data: {nearfield_path} ({len(nearfield_df)} rows)")

    # Far-field analytical CSV
    farfield_path = os.path.join(output_dir, f"results_farfield_{timestamp}.csv")
    farfield_df.to_csv(farfield_path, index=False)
    print(f"Far-field analytical: {farfield_path} ({len(farfield_df)} rows)")

    # Far-field QBP CSV (BPM + Fraunhofer FFT)
    farfield_qbp_df = pd.concat(farfield_qbp_dfs, ignore_index=True)
    cols_ff = ["regime"] + [c for c in farfield_qbp_df.columns if c != "regime"]
    farfield_qbp_df = farfield_qbp_df[cols_ff]
    farfield_qbp_path = os.path.join(
        output_dir, f"results_farfield_qbp_{timestamp}.csv"
    )
    farfield_qbp_df.to_csv(farfield_qbp_path, index=False)
    print(f"Far-field QBP: {farfield_qbp_path} ({len(farfield_qbp_df)} rows)")

    # Decay CSV
    if decay_dfs:
        all_decay_df = pd.concat(decay_dfs, ignore_index=True)
        all_decay_df.insert(0, "regime", all_decay_df.pop("regime"))
        decay_path = os.path.join(output_dir, f"decay_{timestamp}.csv")
        all_decay_df.to_csv(decay_path, index=False)
        print(f"Decay data: {decay_path} ({len(all_decay_df)} rows)")

    # Summary CSV
    summary_df = pd.DataFrame(summary_rows)
    summary_path = os.path.join(output_dir, f"summary_{timestamp}.csv")
    summary_df.to_csv(summary_path, index=False)
    print(f"Summary: {summary_path}")

    # Metadata JSON (v3.0)
    metadata = {
        "format_version": "3.0",
        "unit_convention": "hbar=1 natural units (c=1 reserved for relativistic extensions)",
        "particle": "electron",
        "mass_kg": SI_SCALES.mass_si,
        "lambda_m": SI_SCALES.lambda_si,
        "L0_m": SI_SCALES.L0,
        "E0_J": SI_SCALES.E0,
        "T0_s": SI_SCALES.T0,
        "v_z_si_m_per_s": SI_SCALES.v_z_si,
        "k_si_per_m": SI_SCALES.k_si,
        "V_Z_CODE": V_Z_CODE,
        "BPM_k0": BPM_CONFIG.k0,
        "BPM_hbar": BPM_CONFIG.hbar,
        "BPM_mass": BPM_CONFIG.mass,
        "conversion_applied": True,
        "conversion_library": "src/simulation/si_conversion.py",
        "timestamp": timestamp,
        "datasets": {
            "nearfield": {
                "regime_values": ["expected", "qbp"],
                "method": "BPM",
                "description": "expected=U1=0 (standard QM), qbp=U1>0 (quaternionic coupling)",
                "spatial_scale": "nm",
                "grid_points": BPM_CONFIG.Nx,
            },
            "farfield_analytical": {
                "scenario_values": ["A", "B"],
                "method": "analytical (Fraunhofer)",
                "spatial_scale": "mm",
                "grid_points": 10001,
            },
            "farfield_qbp": {
                "regime_values": ["expected", "qbp"],
                "method": "BPM + Fraunhofer FFT (hybrid)",
                "description": "BPM through slit region, then Fraunhofer FFT to detector plane",
                "pad_factor": 4,
                "screen_distance_m": ANALYTICAL_PARAMS.L,
                "spatial_scale": "mm",
                "grid_points": BPM_CONFIG.Nx * 4,
            },
        },
        "comparison_valid_between": "nearfield regime='expected' vs regime='qbp'",
        "WARNING": "Do NOT compare nearfield to farfield — different methods, scales, and grids",
        "column_units": {
            "x_position_m": "metres",
            "U1_strength_eV": "electron-volts",
            "z_m": "metres",
            "intensity_total_normalized": "dimensionless (normalized)",
            "intensity_psi0_normalized": "dimensionless (normalized)",
            "intensity_psi1_normalized": "dimensionless (normalized)",
            "eta_fraction": "dimensionless",
            "visibility": "dimensionless",
            "norm_final": "dimensionless",
        },
    }
    metadata_path = os.path.join(output_dir, f"metadata_{timestamp}.json")
    with open(metadata_path, "w") as f:
        json.dump(metadata, f, indent=2)
        f.write("\n")
    print(f"Metadata: {metadata_path}")

    # -----------------------------------------------------------------
    # Print summary table
    # -----------------------------------------------------------------
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"\n{'Regime':<14} {'U₁ (eV)':<14} {'η₀':<8} {'Visibility':<12}")
    print("-" * 48)
    for _, row in summary_df.iterrows():
        print(
            f"{row['regime']:<14} {row['U1_strength_eV']:<14.4e} "
            f"{row['eta0']:<8.2f} {row['visibility']:<12.4f}"
        )

    # -----------------------------------------------------------------
    # Acceptance criteria checks
    # -----------------------------------------------------------------
    print("\n" + "=" * 70)
    print("ACCEPTANCE CRITERIA CHECKS")
    print("=" * 70)

    # Far-field QBP sanity check: V(U1=0) should be high (near 1.0)
    ff_expected_rows = [r for r in summary_rows if r["regime"] == "expected"]
    V_ff_u1_zero = max(r["visibility_farfield"] for r in ff_expected_rows)

    checks = [
        ("AC #5: Scenario A visibility > 0.95", V_a > 0.95, f"V_A = {V_a:.4f}"),
        ("AC #4: Scenario B visibility < 0.01", V_b < 0.01, f"V_B = {V_b:.6f}"),
        (
            "AC #7: Far-field BPM+FFT U1=0 visibility > 0.55",
            V_ff_u1_zero > 0.55,
            f"V_ff(U1=0) = {V_ff_u1_zero:.4f}",
        ),
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
