"""
Tests for src/simulation/si_conversion.py

Verifies the two-layer SI conversion framework:
  Layer 1: BPM natural units <-> SI (ScaleFactors, conversion functions)
  Layer 2: Quaternionic derived quantities (MODEL-DEPENDENT)
"""

from __future__ import annotations

import math

import numpy as np
import pandas as pd
import pytest

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
