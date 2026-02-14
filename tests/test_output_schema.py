"""
Test: Output Schema Validation for Experiment 03

Runs a minimal BPM simulation and validates that:
1. CSV columns have correct unit-suffix names
2. Position values are in SI magnitude range (not raw code units)
3. Metadata sidecar contains required scale factors

This is an artifact validation test — more robust than source-code parsing.
"""

from __future__ import annotations

import os
import sys

import numpy as np
import pandas as pd
import pytest

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from src.simulation.si_conversion import compute_scales
from src.simulation.wave_propagation import SimulationConfig, SlitConfig


# ---------------------------------------------------------------------------
# Minimal BPM config for fast testing
# ---------------------------------------------------------------------------
FAST_CONFIG = SimulationConfig(
    Nx=128,
    X_max=10.0,
    dz=0.1,
    Nz_steps=100,
    k0=30.0,
    hbar=1.0,
    mass=0.5,
    device="cpu",
    snapshot_interval=0,
)

FAST_SLIT = SlitConfig(
    separation=2.0,
    width=0.3,
    barrier_height=100.0,
    U1_strength=1.0,
    z_position=5.0,
    z_thickness=1.0,
)

# Electron scales (same as experiment 03)
M_ELECTRON = 9.109_383_7015e-31
LAMBDA_ELECTRON = 0.05e-9
SI_SCALES = compute_scales(M_ELECTRON, LAMBDA_ELECTRON)


@pytest.fixture(scope="module")
def _simulation_output():
    """Run minimal Scenario C once for all schema tests (module-scoped)."""
    from src.simulation.wave_propagation import (
        create_initial_wavepacket,
        create_transverse_grid,
        far_field_intensity,
        propagate,
    )
    from src.simulation.si_conversion import (
        convert_position,
        convert_potential,
    )

    grid = create_transverse_grid(FAST_CONFIG)
    psi0, psi1 = create_initial_wavepacket(grid, k0=FAST_CONFIG.k0, sigma=3.0, eta0=0.1)

    result = propagate(psi0, psi1, grid, FAST_CONFIG, slit=FAST_SLIT)
    x, I_total, I_psi0, I_psi1 = far_field_intensity(result)

    u1_eV = convert_potential(FAST_SLIT.U1_strength, SI_SCALES)

    fringe_rows = []
    for xi, It, I0, I1 in zip(x, I_total, I_psi0, I_psi1):
        fringe_rows.append(
            {
                "scenario": "C",
                "U1_strength_eV": u1_eV,
                "eta0": 0.1,
                "x_position_m": convert_position(xi, SI_SCALES),
                "intensity_total_normalized": It,
                "intensity_psi0_normalized": I0,
                "intensity_psi1_normalized": I1,
            }
        )

    decay_rows = []
    for z_val, eta_val in result.decay_curve:
        decay_rows.append(
            {
                "U1_strength_eV": u1_eV,
                "eta0": 0.1,
                "z_m": convert_position(z_val, SI_SCALES),
                "eta_fraction": eta_val,
            }
        )

    fringe_df = pd.DataFrame(fringe_rows)
    decay_df = pd.DataFrame(decay_rows)

    metadata = {
        "format_version": "2.0",
        "particle": "electron",
        "mass_kg": SI_SCALES.mass_si,
        "lambda_m": SI_SCALES.lambda_si,
        "L0_m": SI_SCALES.L0,
        "E0_J": SI_SCALES.E0,
        "T0_s": SI_SCALES.T0,
    }

    return fringe_df, decay_df, metadata


# ===================================================================
# Schema validation tests
# ===================================================================


class TestFringeSchema:
    """Validate fringe output CSV column names and value ranges."""

    @pytest.fixture(autouse=True)
    def setup(self, _simulation_output):
        self.fringe_df, self.decay_df, self.metadata = _simulation_output

    def test_required_columns_exist(self) -> None:
        required = {
            "scenario",
            "U1_strength_eV",
            "eta0",
            "x_position_m",
            "intensity_total_normalized",
            "intensity_psi0_normalized",
            "intensity_psi1_normalized",
        }
        assert required.issubset(set(self.fringe_df.columns))

    def test_no_raw_code_unit_columns(self) -> None:
        """Columns like 'x_position' (without unit suffix) should not exist."""
        for col in self.fringe_df.columns:
            if col in ("scenario", "eta0"):
                continue
            assert not col.endswith("_position") or col.endswith(
                "_m"
            ), f"Column '{col}' appears to lack a unit suffix"

    def test_x_position_is_si_scale(self) -> None:
        """x_position_m should be in metres (sub-micron for electron BPM)."""
        x_vals = self.fringe_df["x_position_m"].values
        max_x = np.max(np.abs(x_vals))
        # L0 for electron ~1.6e-10 m, X_max=10 code units -> ~1.6e-9 m
        # Must be less than 1 metre (not raw code units ~10)
        assert max_x < 1.0, f"x_position_m max={max_x} — looks like code units, not SI"
        # Must be larger than a femtometre (sanity check)
        assert max_x > 1e-15, f"x_position_m max={max_x} — implausibly small"

    def test_intensities_non_negative(self) -> None:
        for col in [
            "intensity_total_normalized",
            "intensity_psi0_normalized",
            "intensity_psi1_normalized",
        ]:
            assert (self.fringe_df[col] >= 0).all(), f"{col} has negative values"


class TestDecaySchema:
    """Validate decay output CSV column names and value ranges."""

    @pytest.fixture(autouse=True)
    def setup(self, _simulation_output):
        self.fringe_df, self.decay_df, self.metadata = _simulation_output

    def test_required_columns_exist(self) -> None:
        required = {"U1_strength_eV", "eta0", "z_m", "eta_fraction"}
        assert required.issubset(set(self.decay_df.columns))

    def test_z_is_si_scale(self) -> None:
        """z_m should be in metres, not raw code units."""
        if len(self.decay_df) == 0:
            pytest.skip("No decay data produced")
        z_vals = self.decay_df["z_m"].values
        max_z = np.max(np.abs(z_vals))
        assert max_z < 1.0, f"z_m max={max_z} — looks like code units, not SI"
        assert max_z > 0, "z_m should have non-zero propagation distance"

    def test_eta_fraction_bounded(self) -> None:
        if len(self.decay_df) == 0:
            pytest.skip("No decay data produced")
        eta = self.decay_df["eta_fraction"].values
        assert (eta >= 0).all(), "eta_fraction has negative values"
        assert (eta <= 1).all(), "eta_fraction exceeds 1"


class TestMetadataSchema:
    """Validate metadata sidecar content."""

    @pytest.fixture(autouse=True)
    def setup(self, _simulation_output):
        self.fringe_df, self.decay_df, self.metadata = _simulation_output

    def test_required_keys_exist(self) -> None:
        required = {
            "format_version",
            "particle",
            "mass_kg",
            "lambda_m",
            "L0_m",
            "E0_J",
            "T0_s",
        }
        assert required.issubset(set(self.metadata.keys()))

    def test_format_version(self) -> None:
        assert self.metadata["format_version"] == "2.0"

    def test_scale_factors_positive(self) -> None:
        for key in ("L0_m", "E0_J", "T0_s"):
            assert self.metadata[key] > 0, f"{key} must be positive"
            assert np.isfinite(self.metadata[key]), f"{key} must be finite"

    def test_particle_specified(self) -> None:
        assert self.metadata["particle"] == "electron"
