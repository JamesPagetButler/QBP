"""
Tests for src/simulation/si_conversion.py

Verifies the two-layer SI conversion framework:
  Layer 1: BPM natural units <-> SI (ScaleFactors, conversion functions)
  Layer 2: Quaternionic derived quantities (MODEL-DEPENDENT)

Includes:
  - Unit tests (deterministic, known-value)
  - Property-based tests (hypothesis: algebraic invariants)
  - Cross-language verification (Lean 4 oracle test vectors)
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np
import pandas as pd
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.simulation.si_conversion import (
    C_SI,
    EV_IN_JOULES,
    HBAR_CODE,
    HBAR_SI,
    K0_CODE,
    M_CODE,
    V_Z_CODE,
    QuaternionicQuantities,
    ScaleFactors,
    annotate_columns,
    compute_quaternionic_quantities,
    compute_scales,
    convert_energy,
    convert_energy_to_code,
    convert_length_to_code,
    convert_position,
    convert_potential,
)

# ---------------------------------------------------------------------------
# Test particles
# ---------------------------------------------------------------------------
M_ELECTRON = 9.109_383_7015e-31  # kg
LAMBDA_ELEC = 5.0e-11  # m

M_NEUTRON = 1.674_927_498_04e-27  # kg
LAMBDA_NEUT = 1.8e-10  # m

RTOL = 1e-12


# ===================================================================
# V_Z_CODE canonical value
# ===================================================================


class TestVZCode:
    """V_Z_CODE must equal hbar_code * k0_code / m_code = 40."""

    def test_value(self) -> None:
        assert V_Z_CODE == pytest.approx(40.0, rel=RTOL)

    def test_composition(self) -> None:
        assert V_Z_CODE == pytest.approx(HBAR_CODE * K0_CODE / M_CODE, rel=RTOL)


# ===================================================================
# ScaleFactors computation
# ===================================================================


class TestComputeScales:
    """compute_scales returns a ScaleFactors dataclass with correct values."""

    def test_returns_scale_factors(self) -> None:
        result = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        assert isinstance(result, ScaleFactors)

    def test_electron_L0_positive_finite(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        assert sc.L0 > 0
        assert np.isfinite(sc.L0)

    def test_electron_E0_positive_finite(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        assert sc.E0 > 0
        assert np.isfinite(sc.E0)

    def test_T0_equals_hbar_over_E0(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        assert sc.T0 == pytest.approx(HBAR_SI / sc.E0, rel=RTOL)

    def test_traceability_fields(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        assert sc.mass_si == M_ELECTRON
        assert sc.lambda_si == LAMBDA_ELEC

    def test_zero_mass_raises(self) -> None:
        with pytest.raises(ValueError, match="Mass must be positive"):
            compute_scales(0.0, LAMBDA_ELEC)

    def test_negative_wavelength_raises(self) -> None:
        with pytest.raises(ValueError, match="Wavelength must be positive"):
            compute_scales(M_ELECTRON, -1e-10)

    def test_matches_dict_version(self) -> None:
        """ScaleFactors must match the dict-based version in test_si_defining_constants."""
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        k_si = 2 * math.pi / LAMBDA_ELEC
        L0_expected = K0_CODE * LAMBDA_ELEC / (2 * math.pi)
        E0_expected = HBAR_SI**2 * M_CODE / (M_ELECTRON * L0_expected**2 * HBAR_CODE**2)
        T0_expected = HBAR_SI / E0_expected
        v_z_expected = HBAR_SI * k_si / M_ELECTRON

        assert sc.L0 == pytest.approx(L0_expected, rel=RTOL)
        assert sc.E0 == pytest.approx(E0_expected, rel=RTOL)
        assert sc.T0 == pytest.approx(T0_expected, rel=RTOL)
        assert sc.v_z_si == pytest.approx(v_z_expected, rel=RTOL)
        assert sc.k_si == pytest.approx(k_si, rel=RTOL)


# ===================================================================
# Output conversion (Code -> SI)
# ===================================================================


class TestOutputConversion:
    """Code-to-SI conversion functions."""

    def test_convert_position(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        x_si = convert_position(1.0, sc)
        assert x_si == pytest.approx(sc.L0, rel=RTOL)

    def test_convert_position_round_trip(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        x_code = 3.7
        x_si = convert_position(x_code, sc)
        x_back = convert_length_to_code(x_si, sc)
        assert x_back == pytest.approx(x_code, rel=RTOL)

    def test_convert_potential_electron(self) -> None:
        """U_code=10 at electron scale should give ~60.2 eV per code unit * 10 * 40."""
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        U_eV = convert_potential(10.0, sc)
        # Expected: 10 * 40 * E0 / eV
        expected = 10.0 * V_Z_CODE * sc.E0 / EV_IN_JOULES
        assert U_eV == pytest.approx(expected, rel=RTOL)

    def test_convert_energy(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        E_si = convert_energy(1.0, sc)
        assert E_si == pytest.approx(sc.E0, rel=RTOL)

    def test_convert_energy_round_trip(self) -> None:
        sc = compute_scales(M_NEUTRON, LAMBDA_NEUT)
        E_code = 5.5
        E_si = convert_energy(E_code, sc)
        E_back = convert_energy_to_code(E_si, sc)
        assert E_back == pytest.approx(E_code, rel=RTOL)


# ===================================================================
# Input conversion (SI -> Code)
# ===================================================================


class TestInputConversion:
    """SI-to-code conversion functions."""

    def test_convert_length_to_code(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        val_code = convert_length_to_code(sc.L0, sc)
        assert val_code == pytest.approx(1.0, rel=RTOL)

    def test_convert_energy_to_code(self) -> None:
        sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)
        val_code = convert_energy_to_code(sc.E0, sc)
        assert val_code == pytest.approx(1.0, rel=RTOL)


# ===================================================================
# Column annotation
# ===================================================================


class TestAnnotateColumns:
    """annotate_columns renames columns with unit suffixes."""

    def test_renames_matching_columns(self) -> None:
        df = pd.DataFrame({"x_position": [1, 2], "intensity": [0.5, 0.6]})
        result = annotate_columns(df, {"x_position": "m", "intensity": "normalized"})
        assert "x_position_m" in result.columns
        assert "intensity_normalized" in result.columns
        assert "x_position" not in result.columns

    def test_ignores_missing_columns(self) -> None:
        df = pd.DataFrame({"x_position": [1, 2]})
        result = annotate_columns(df, {"x_position": "m", "nonexistent": "eV"})
        assert "x_position_m" in result.columns
        assert len(result.columns) == 1

    def test_does_not_modify_original(self) -> None:
        df = pd.DataFrame({"x_position": [1, 2]})
        _ = annotate_columns(df, {"x_position": "m"})
        assert "x_position" in df.columns


# ===================================================================
# Layer 2: Quaternionic quantities (MODEL-DEPENDENT)
# ===================================================================


class TestQuaternionicQuantities:
    """Quaternionic derived quantities computation."""

    def test_compute_basic(self) -> None:
        U1_si = 1e-18  # 1 aJ
        E_kin_si = 1e-17  # 10 aJ
        v_g_si = 1e6  # 1 Mm/s
        qq = compute_quaternionic_quantities(U1_si, E_kin_si, v_g_si)
        assert isinstance(qq, QuaternionicQuantities)
        assert qq.L_Q > 0
        assert qq.zeta > 0

    def test_zeta_is_dimensionless(self) -> None:
        U1_si = 5e-18
        E_kin_si = 1e-17
        v_g_si = 1e6
        qq = compute_quaternionic_quantities(U1_si, E_kin_si, v_g_si)
        assert qq.zeta == pytest.approx(U1_si / E_kin_si, rel=RTOL)

    def test_L_Q_formula(self) -> None:
        U1_si = 2e-18
        E_kin_si = 1e-17
        v_g_si = 1e6
        qq = compute_quaternionic_quantities(U1_si, E_kin_si, v_g_si)
        expected = math.pi * HBAR_SI * v_g_si / U1_si
        assert qq.L_Q == pytest.approx(expected, rel=RTOL)

    def test_zero_U1_raises(self) -> None:
        with pytest.raises(ValueError, match="U1_si must be positive"):
            compute_quaternionic_quantities(0.0, 1e-17, 1e6)

    def test_zero_E_kin_raises(self) -> None:
        with pytest.raises(ValueError, match="E_kin_si must be positive"):
            compute_quaternionic_quantities(1e-18, 0.0, 1e6)

    def test_zero_v_g_raises(self) -> None:
        with pytest.raises(ValueError, match="v_g_si must be positive"):
            compute_quaternionic_quantities(1e-18, 1e-17, 0.0)

    def test_negative_v_g_raises(self) -> None:
        with pytest.raises(ValueError, match="v_g_si must be positive"):
            compute_quaternionic_quantities(1e-18, 1e-17, -1e6)


# ===================================================================
# Physical constants
# ===================================================================


class TestPhysicalConstants:
    """Verify exact 2019 SI redefinition values."""

    def test_c_si_exact(self) -> None:
        assert C_SI == 299_792_458

    def test_c_si_type(self) -> None:
        assert isinstance(C_SI, int)


# ===================================================================
# Property-based tests (hypothesis)
#
# These mirror the algebraic properties proven in Lean 4:
#   proofs/QBP/Units/ScaleFactors.lean
#
# Lean proves on ideal Reals; hypothesis verifies on IEEE 754 floats.
# ===================================================================

# Strategy for physically reasonable particle masses [kg]
# Range: electron mass to uranium atom mass
st_mass = st.floats(
    min_value=1e-31, max_value=1e-24, allow_nan=False, allow_infinity=False
)

# Strategy for physically reasonable de Broglie wavelengths [m]
# Range: hard X-ray to thermal neutron
st_wavelength = st.floats(
    min_value=1e-12, max_value=1e-8, allow_nan=False, allow_infinity=False
)

# Strategy for code-unit values (typical BPM range).
# Excludes subnormals and near-zero values (|x| < 1e-250) that underflow
# when multiplied by scale factors (~1e-23), causing IEEE 754 precision loss.
st_code_value = st.floats(
    min_value=-1e6,
    max_value=1e6,
    allow_nan=False,
    allow_infinity=False,
    allow_subnormal=False,
).filter(lambda x: x == 0.0 or abs(x) > 1e-250)


class TestPropertyRoundTrip:
    """Round-trip: SI→Code→SI and Code→SI→Code must preserve values.

    Mirrors Lean theorems: position_round_trip, energy_round_trip
    """

    @given(x_code=st_code_value, m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_position_round_trip(
        self, x_code: float, m_si: float, lam_si: float
    ) -> None:
        """code→SI→code preserves value. Lean proves exact on Reals;
        IEEE 754 round-trip error bounded by ~1e-12 for normal values."""
        sc = compute_scales(m_si, lam_si)
        x_si = convert_position(x_code, sc)
        x_back = convert_length_to_code(x_si, sc)
        assert x_back == pytest.approx(x_code, rel=1e-12, abs=1e-300)

    @given(E_code=st_code_value, m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_energy_round_trip(self, E_code: float, m_si: float, lam_si: float) -> None:
        """code→SI→code preserves value. Lean proves exact on Reals;
        IEEE 754 round-trip error bounded by ~1e-12 for normal values."""
        sc = compute_scales(m_si, lam_si)
        E_si = convert_energy(E_code, sc)
        E_back = convert_energy_to_code(E_si, sc)
        assert E_back == pytest.approx(E_code, rel=1e-12, abs=1e-300)


class TestPropertyLinearity:
    """Conversion functions are linear: f(a+b) = f(a) + f(b), f(αx) = αf(x).

    Mirrors Lean theorems: position_linear, energy_linear, position_scaling
    """

    @given(x1=st_code_value, x2=st_code_value, m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_position_additive(
        self, x1: float, x2: float, m_si: float, lam_si: float
    ) -> None:
        """f(x1+x2) = f(x1) + f(x2). Tolerance relaxed to 1e-10 to account
        for catastrophic cancellation when x1 ≈ -x2 (inherent to IEEE 754,
        not a code bug — Lean proves this exactly on Reals)."""
        sc = compute_scales(m_si, lam_si)
        sum_then_convert = convert_position(x1 + x2, sc)
        convert_then_sum = convert_position(x1, sc) + convert_position(x2, sc)
        assert sum_then_convert == pytest.approx(
            convert_then_sum, rel=1e-10, abs=1e-300
        )

    @given(E1=st_code_value, E2=st_code_value, m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_energy_additive(
        self, E1: float, E2: float, m_si: float, lam_si: float
    ) -> None:
        """f(E1+E2) = f(E1) + f(E2). Same cancellation tolerance as position."""
        sc = compute_scales(m_si, lam_si)
        convert_then_sum = convert_energy(E1, sc) + convert_energy(E2, sc)
        result = convert_energy(E1 + E2, sc)
        assert result == pytest.approx(convert_then_sum, rel=1e-10, abs=1e-300)

    @given(
        alpha=st.floats(
            min_value=-1e3, max_value=1e3, allow_nan=False, allow_infinity=False
        ),
        x=st_code_value,
        m_si=st_mass,
        lam_si=st_wavelength,
    )
    @settings(max_examples=200)
    def test_position_scaling(
        self, alpha: float, x: float, m_si: float, lam_si: float
    ) -> None:
        sc = compute_scales(m_si, lam_si)
        scaled_then_convert = convert_position(alpha * x, sc)
        convert_then_scale = alpha * convert_position(x, sc)
        assert scaled_then_convert == pytest.approx(
            convert_then_scale, rel=1e-14, abs=1e-300
        )


class TestPropertyPositivity:
    """All scale factors are positive for positive inputs.

    Mirrors Lean theorems: L0_pos, E0_pos
    """

    @given(m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_scale_factors_positive(self, m_si: float, lam_si: float) -> None:
        sc = compute_scales(m_si, lam_si)
        assert sc.L0 > 0, f"L0 = {sc.L0}"
        assert sc.E0 > 0, f"E0 = {sc.E0}"
        assert sc.T0 > 0, f"T0 = {sc.T0}"
        assert sc.v_z_si > 0, f"v_z_si = {sc.v_z_si}"
        assert sc.k_si > 0, f"k_si = {sc.k_si}"

    @given(m_si=st_mass, lam_si=st_wavelength)
    @settings(max_examples=200)
    def test_scale_factors_finite(self, m_si: float, lam_si: float) -> None:
        sc = compute_scales(m_si, lam_si)
        assert np.isfinite(sc.L0)
        assert np.isfinite(sc.E0)
        assert np.isfinite(sc.T0)
        assert np.isfinite(sc.v_z_si)
        assert np.isfinite(sc.k_si)


class TestPropertyZero:
    """Zero maps to zero for all conversion functions.

    Mirrors Lean theorems: position_zero, energy_zero
    """

    @given(m_si=st_mass, lam_si=st_wavelength)
    def test_position_zero(self, m_si: float, lam_si: float) -> None:
        sc = compute_scales(m_si, lam_si)
        assert convert_position(0.0, sc) == 0.0

    @given(m_si=st_mass, lam_si=st_wavelength)
    def test_energy_zero(self, m_si: float, lam_si: float) -> None:
        sc = compute_scales(m_si, lam_si)
        assert convert_energy(0.0, sc) == 0.0


class TestPropertyVZInvariant:
    """V_Z_CODE = hbar_code * k0_code / m_code = 40 exactly.

    Mirrors Lean theorem: v_z_code_eq_40
    """

    def test_v_z_code_structural_invariant(self) -> None:
        """V_Z_CODE must be computed from its constituent parameters, not hardcoded."""
        computed = HBAR_CODE * K0_CODE / M_CODE
        assert V_Z_CODE == computed  # exact equality, not approx
        assert computed == 40.0


# ===================================================================
# Cross-language verification (Lean 4 oracle)
#
# Python results must match Lean's Float oracle within IEEE 754
# tolerance (< 1e-15 relative error).
#
# Test vectors generated by: lake exe gen_test_vectors
# Source of truth: proofs/QBP/Units/ScaleFactors.lean (algebraic proofs)
# ===================================================================

FIXTURE_PATH = Path(__file__).parent / "fixtures" / "si_test_vectors.json"


def _find_particle(vectors: list, particle: str) -> dict:
    """Find a particle entry in test vectors, with clear error on missing."""
    for entry in vectors:
        if entry["particle"] == particle:
            return entry
    raise ValueError(
        f"Particle '{particle}' not found in test vectors. "
        f"Available: {[e['particle'] for e in vectors]}"
    )


@pytest.mark.skipif(not FIXTURE_PATH.exists(), reason="Lean test vectors not generated")
class TestCrossLanguageLean:
    """Verify Python agrees with Lean 4 oracle on test vectors."""

    @pytest.fixture(autouse=True)
    def load_vectors(self) -> None:
        with open(FIXTURE_PATH) as f:
            self.vectors = json.load(f)

    def test_v_z_code_matches_lean(self) -> None:
        lean_val = float(self.vectors["v_z_code"])
        assert V_Z_CODE == pytest.approx(lean_val, rel=1e-15)

    def test_hbar_si_matches_lean(self) -> None:
        lean_val = float(self.vectors["hbar_SI"])
        assert HBAR_SI == pytest.approx(lean_val, rel=1e-15)

    def test_eV_matches_lean(self) -> None:
        lean_val = float(self.vectors["eV_in_J"])
        assert EV_IN_JOULES == pytest.approx(lean_val, rel=1e-15)

    def test_electron_scale_factors(self) -> None:
        lean = _find_particle(self.vectors["scale_factors"], "electron")
        sc = compute_scales(float(lean["mass_si"]), float(lean["lambda_si"]))
        assert sc.L0 == pytest.approx(float(lean["L0"]), rel=1e-15)
        assert sc.E0 == pytest.approx(float(lean["E0"]), rel=1e-15)
        assert sc.T0 == pytest.approx(float(lean["T0"]), rel=1e-15)
        assert sc.v_z_si == pytest.approx(float(lean["v_z_si"]), rel=1e-15)
        assert sc.k_si == pytest.approx(float(lean["k_si"]), rel=1e-15)

    def test_neutron_scale_factors(self) -> None:
        lean = _find_particle(self.vectors["scale_factors"], "neutron")
        sc = compute_scales(float(lean["mass_si"]), float(lean["lambda_si"]))
        assert sc.L0 == pytest.approx(float(lean["L0"]), rel=1e-15)
        assert sc.E0 == pytest.approx(float(lean["E0"]), rel=1e-15)
        assert sc.T0 == pytest.approx(float(lean["T0"]), rel=1e-15)
        assert sc.v_z_si == pytest.approx(float(lean["v_z_si"]), rel=1e-15)
        assert sc.k_si == pytest.approx(float(lean["k_si"]), rel=1e-15)

    def test_electron_round_trips(self) -> None:
        lean = _find_particle(self.vectors["round_trips"], "electron")
        lean_sf = _find_particle(self.vectors["scale_factors"], "electron")
        sc = compute_scales(float(lean_sf["mass_si"]), float(lean_sf["lambda_si"]))

        x_code = float(lean["position_code"])
        x_si = convert_position(x_code, sc)
        assert x_si == pytest.approx(float(lean["position_si"]), rel=1e-15)

        E_code = float(lean["energy_code"])
        E_si = convert_energy(E_code, sc)
        assert E_si == pytest.approx(float(lean["energy_si"]), rel=1e-15)

        U_code = float(lean["potential_code"])
        U_eV = convert_potential(U_code, sc)
        assert U_eV == pytest.approx(float(lean["potential_eV"]), rel=1e-15)

    def test_neutron_round_trips(self) -> None:
        lean = _find_particle(self.vectors["round_trips"], "neutron")
        lean_sf = _find_particle(self.vectors["scale_factors"], "neutron")
        sc = compute_scales(float(lean_sf["mass_si"]), float(lean_sf["lambda_si"]))

        x_code = float(lean["position_code"])
        x_si = convert_position(x_code, sc)
        assert x_si == pytest.approx(float(lean["position_si"]), rel=1e-15)

        E_code = float(lean["energy_code"])
        E_si = convert_energy(E_code, sc)
        assert E_si == pytest.approx(float(lean["energy_si"]), rel=1e-15)

        U_code = float(lean["potential_code"])
        U_eV = convert_potential(U_code, sc)
        assert U_eV == pytest.approx(float(lean["potential_eV"]), rel=1e-15)
