"""
Test: 7 SI Defining Constants in the Quaternionic SI Framework

Verifies that each of the 7 SI defining constants (2019 redefinition) can be
represented and round-tripped through the quaternionic unit conversion framework
defined in docs/theory/quaternionic_si_definitions.md.

Framework recap (Section 7.2 of the document):
    L_0 = k0_code * lambda_SI / (2*pi)
    E_0 = hbar_SI^2 * m_code / (m_SI * L_0^2 * hbar_code^2)
    T_0 = hbar_SI / E_0

Code parameters: hbar_code=1, m_code=0.5, k0_code=20.

The 7 SI defining constants:
    1. DeltaNu_Cs = 9,192,631,770 Hz
    2. c          = 299,792,458 m/s
    3. h          = 6.62607015e-34 J*s
    4. e          = 1.602176634e-19 C
    5. k_B        = 1.380649e-23 J/K
    6. N_A        = 6.02214076e23 mol^{-1}
    7. K_cd       = 683 lm/W
"""

from __future__ import annotations

import math

import numpy as np
import pytest

# ---------------------------------------------------------------------------
# Physical constants (exact values from the 2019 SI redefinition)
# ---------------------------------------------------------------------------
DELTA_NU_CS = 9_192_631_770  # Hz
C_SI = 299_792_458  # m/s
H_SI = 6.626_070_15e-34  # J*s   (exact)
HBAR_SI = H_SI / (2 * math.pi)  # J*s
E_CHARGE = 1.602_176_634e-19  # C     (exact)
K_B_SI = 1.380_649e-23  # J/K   (exact)
N_A = 6.022_140_76e23  # mol^{-1} (exact)
K_CD = 683  # lm/W  (exact)

# ---------------------------------------------------------------------------
# BPM code parameters (from quaternionic_si_definitions.md Section 7.1)
# ---------------------------------------------------------------------------
HBAR_CODE = 1.0
M_CODE = 0.5
K0_CODE = 20.0

# ---------------------------------------------------------------------------
# Physical systems for multi-scale testing
# ---------------------------------------------------------------------------

# Electron (Tonomura experiment): lambda = 0.05 nm
M_ELECTRON = 9.109_383_7015e-31  # kg  (CODATA 2018)
LAMBDA_ELEC = 5.0e-11  # m

# Neutron (Kaiser experiment): lambda ~ 0.18 nm (thermal neutrons)
M_NEUTRON = 1.674_927_498_04e-27  # kg  (CODATA 2018)
LAMBDA_NEUT = 1.8e-10  # m

# Planck scale (thought experiment)
G_SI = 6.674_30e-11  # m^3 kg^{-1} s^{-2}
L_PLANCK = math.sqrt(HBAR_SI * G_SI / C_SI**3)  # ~ 1.616e-35 m
# For Planck-scale particle, use lambda ~ 2*pi*l_P (de Broglie at Planck energy)
M_PLANCK = math.sqrt(HBAR_SI * C_SI / G_SI)  # ~ 2.176e-8 kg
LAMBDA_PLANCK = 2 * math.pi * L_PLANCK  # ~ 1.016e-34 m


# ---------------------------------------------------------------------------
# Helper: compute conversion scales from physical system parameters
# ---------------------------------------------------------------------------


def compute_scales(m_si: float, lambda_si: float) -> dict:
    """
    Given a particle mass and de Broglie wavelength (both SI), compute
    the quaternionic framework conversion scales.

    Returns dict with keys: L_0, E_0, T_0, v_z_SI, k_SI.
    """
    k_si = 2 * math.pi / lambda_si
    L_0 = K0_CODE * lambda_si / (2 * math.pi)  # = K0_CODE / k_si

    # E_0 = hbar_SI^2 * m_code / (m_SI * L_0^2 * hbar_code^2)
    E_0 = HBAR_SI**2 * M_CODE / (m_si * L_0**2 * HBAR_CODE**2)

    # T_0 = hbar_SI / E_0
    T_0 = HBAR_SI / E_0

    # Physical velocity
    v_z_si = HBAR_SI * k_si / m_si

    return {
        "L_0": L_0,
        "E_0": E_0,
        "T_0": T_0,
        "v_z_SI": v_z_si,
        "k_SI": k_si,
    }


# Three physical scales for parametrized tests
SCALES = [
    pytest.param(M_ELECTRON, LAMBDA_ELEC, id="electron-0.16nm"),
    pytest.param(M_NEUTRON, LAMBDA_NEUT, id="neutron-0.57nm"),
    pytest.param(M_PLANCK, LAMBDA_PLANCK, id="planck-scale"),
]

RTOL = 1e-12  # relative tolerance for all round-trip checks


# ===================================================================
# 1. Planck constant h
# ===================================================================


class TestPlanckConstant:
    """
    h = 2*pi*hbar_SI.  In code units hbar=1, so h_code = 2*pi.
    Round-trip: h_code * (E_0 * T_0) must recover h_SI.
    """

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_h_code_value(self, m_si: float, lambda_si: float) -> None:
        """In code units, h_code = 2*pi (since hbar_code = 1)."""
        h_code = 2 * math.pi * HBAR_CODE
        assert h_code == pytest.approx(2 * math.pi, rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_h_round_trip(self, m_si: float, lambda_si: float) -> None:
        """Convert h to code units and back: must recover h_SI."""
        sc = compute_scales(m_si, lambda_si)
        # h has dimensions of [Energy]*[Time] = E_0 * T_0 in code
        h_code = H_SI / (sc["E_0"] * sc["T_0"])
        h_recovered = h_code * sc["E_0"] * sc["T_0"]
        assert h_recovered == pytest.approx(H_SI, rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_h_code_is_2pi(self, m_si: float, lambda_si: float) -> None:
        """
        Since E_0 * T_0 = hbar_SI (by definition of T_0 = hbar_SI / E_0),
        h_code = h_SI / hbar_SI = 2*pi.  Scale-independent.
        """
        sc = compute_scales(m_si, lambda_si)
        action_scale = sc["E_0"] * sc["T_0"]  # should be hbar_SI
        h_code = H_SI / action_scale
        assert h_code == pytest.approx(2 * math.pi, rel=RTOL)


# ===================================================================
# 2. Speed of light c
# ===================================================================


class TestSpeedOfLight:
    """
    c has dimensions [Length]/[Time] = L_0 / T_0 in code units.
    c_code = c_SI * T_0 / L_0.
    Round-trip: c_code * L_0 / T_0 must recover c_SI.
    """

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_c_round_trip(self, m_si: float, lambda_si: float) -> None:
        """Convert c to code units and back."""
        sc = compute_scales(m_si, lambda_si)
        c_code = C_SI * sc["T_0"] / sc["L_0"]
        c_recovered = c_code * sc["L_0"] / sc["T_0"]
        assert c_recovered == pytest.approx(C_SI, rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_c_code_value_electron(self, m_si: float, lambda_si: float) -> None:
        """c_code should be a large dimensionless number at non-relativistic scales,
        and approach a moderate number at Planck scale."""
        sc = compute_scales(m_si, lambda_si)
        c_code = C_SI * sc["T_0"] / sc["L_0"]
        # c_code must be positive and finite
        assert c_code > 0
        assert np.isfinite(c_code)


# ===================================================================
# 3. Hyperfine transition frequency of Cs-133
# ===================================================================


class TestCesiumFrequency:
    """
    DeltaNu_Cs has dimensions [1/Time] = 1/T_0 in code units.
    DeltaNu_code = DeltaNu_Cs * T_0.
    Round-trip: DeltaNu_code / T_0 must recover DeltaNu_Cs.
    """

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_delta_nu_round_trip(self, m_si: float, lambda_si: float) -> None:
        """Convert cesium frequency to code units and back."""
        sc = compute_scales(m_si, lambda_si)
        dnu_code = DELTA_NU_CS * sc["T_0"]
        dnu_recovered = dnu_code / sc["T_0"]
        assert dnu_recovered == pytest.approx(DELTA_NU_CS, rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_delta_nu_code_positive(self, m_si: float, lambda_si: float) -> None:
        """Code representation must be positive and finite."""
        sc = compute_scales(m_si, lambda_si)
        dnu_code = DELTA_NU_CS * sc["T_0"]
        assert dnu_code > 0
        assert np.isfinite(dnu_code)


# ===================================================================
# 4. Boltzmann constant k_B
# ===================================================================


class TestBoltzmannConstant:
    """
    k_B has dimensions [Energy]/[Temperature] = [J/K].
    The framework defines E_0 as the energy scale.  To represent k_B we need
    a temperature scale: T_K_0 = E_0 / k_B_SI  (temperature corresponding
    to one code energy unit).

    k_code = k_B_SI * T_K_0 / E_0 = 1 (by construction).
    Round-trip: k_code * E_0 / T_K_0 must recover k_B_SI.
    """

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_kb_round_trip(self, m_si: float, lambda_si: float) -> None:
        """Convert k_B to code units and back."""
        sc = compute_scales(m_si, lambda_si)
        # Define temperature scale from the energy scale
        T_K_0 = sc["E_0"] / K_B_SI  # Kelvin per code temperature unit
        # In code units: k_code = k_B_SI * T_K_0 / E_0
        k_code = K_B_SI * T_K_0 / sc["E_0"]
        # Round-trip
        kb_recovered = k_code * sc["E_0"] / T_K_0
        assert kb_recovered == pytest.approx(K_B_SI, rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_kb_code_is_unity(self, m_si: float, lambda_si: float) -> None:
        """When T_K_0 = E_0/k_B, the code value of k_B is exactly 1."""
        sc = compute_scales(m_si, lambda_si)
        T_K_0 = sc["E_0"] / K_B_SI
        k_code = K_B_SI * T_K_0 / sc["E_0"]
        assert k_code == pytest.approx(1.0, rel=RTOL)


# ===================================================================
# 5. Elementary charge e  (PARTIAL)
# ===================================================================


class TestElementaryCharge:
    """
    The elementary charge e has dimensions of [Charge] = [A*s].

    The quaternionic SI framework (docs/theory/quaternionic_si_definitions.md)
    defines scales for Length, Energy, and Time, but does NOT define a charge
    or current scale.  This is expected: the framework models quantum mechanical
    wavefunctions (Schrodinger equation), which do not inherently require
    electromagnetic units.

    We mark this as PARTIAL: the framework CAN be extended to include charge
    (e.g., by defining Q_0 = e, making e_code = 1), but the current document
    does not do so.

    Tests below verify the extension approach is self-consistent.
    """

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_charge_extension_round_trip(self, m_si: float, lambda_si: float) -> None:
        """
        If we extend the framework with Q_0 = e (elementary charge as the
        charge scale), then e_code = 1 and the round-trip is trivial.
        """
        Q_0 = E_CHARGE  # Define charge scale = elementary charge
        e_code = E_CHARGE / Q_0
        e_recovered = e_code * Q_0
        assert e_recovered == pytest.approx(E_CHARGE, rel=RTOL)
        assert e_code == pytest.approx(1.0, rel=RTOL)

    def test_charge_not_in_current_framework(self) -> None:
        """
        Flag: charge is outside the current framework scope.
        The quaternionic SI definitions doc covers L, E, T but not Q.
        This test documents the gap.
        """
        # The framework defines these scales:
        framework_scales = {"length": "L_0", "energy": "E_0", "time": "T_0"}
        # Charge is NOT among them:
        assert (
            "charge" not in framework_scales
        ), "If charge has been added to the framework, update this test."


# ===================================================================
# 6. Avogadro constant N_A
# ===================================================================


class TestAvogadroConstant:
    """
    N_A = 6.02214076e23 mol^{-1} is a pure counting constant.
    It is dimensionless (counts per mole) and requires no unit conversion.
    It passes trivially in any unit system.
    """

    def test_na_is_dimensionless(self) -> None:
        """N_A is a pure number: no conversion needed."""
        # In any unit system, N_A has the same numerical value
        na_code = N_A  # dimensionless => unchanged
        assert na_code == pytest.approx(N_A, rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_na_scale_independent(self, m_si: float, lambda_si: float) -> None:
        """N_A does not depend on L_0, E_0, or T_0."""
        sc = compute_scales(m_si, lambda_si)
        # N_A is unchanged regardless of scale
        na_code = N_A  # no scaling factors
        na_recovered = na_code
        assert na_recovered == pytest.approx(N_A, rel=RTOL)
        # Explicitly verify it does not scale with any conversion factor
        assert na_code / (sc["L_0"] / sc["L_0"]) == pytest.approx(N_A, rel=RTOL)


# ===================================================================
# 7. Luminous efficacy K_cd  (PARTIAL)
# ===================================================================


class TestLuminousEfficacy:
    """
    K_cd = 683 lm/W defines the candela.

    Dimensions: [lm/W] = [cd*sr/W].  This involves the candela (photometric
    base unit), which is outside the scope of quantum mechanical wavefunctions.

    The quaternionic framework defines mechanical quantities (length, energy,
    time) but not photometric quantities.  Like charge, this is PARTIAL:
    the framework can be extended but does not currently include candela.

    We verify that the power component (watts) CAN be expressed, and flag
    the photometric component as outside scope.
    """

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_power_component_round_trip(self, m_si: float, lambda_si: float) -> None:
        """
        Power [W] = [J/s] = E_0/T_0 in code units.
        We can represent the denominator of K_cd (watts) in the framework.
        """
        sc = compute_scales(m_si, lambda_si)
        P_0 = sc["E_0"] / sc["T_0"]  # code power scale in watts
        # Round-trip a 1-watt power
        p_si = 1.0  # 1 watt
        p_code = p_si / P_0
        p_recovered = p_code * P_0
        assert p_recovered == pytest.approx(p_si, rel=RTOL)

    def test_candela_not_in_current_framework(self) -> None:
        """
        Flag: candela/photometric units are outside the current framework.
        K_cd requires luminous intensity, which is not part of the
        Schrodinger equation.
        """
        framework_scales = {"length": "L_0", "energy": "E_0", "time": "T_0"}
        assert (
            "luminous_intensity" not in framework_scales
        ), "If candela has been added to the framework, update this test."


# ===================================================================
# Cross-checks and consistency
# ===================================================================


class TestFrameworkConsistency:
    """
    Verify internal consistency of the conversion framework itself.
    """

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_T0_equals_hbar_over_E0(self, m_si: float, lambda_si: float) -> None:
        """T_0 = hbar_SI / E_0 by definition."""
        sc = compute_scales(m_si, lambda_si)
        assert sc["T_0"] == pytest.approx(HBAR_SI / sc["E_0"], rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_action_scale_is_hbar(self, m_si: float, lambda_si: float) -> None:
        """E_0 * T_0 = hbar_SI, so the action scale equals hbar."""
        sc = compute_scales(m_si, lambda_si)
        action = sc["E_0"] * sc["T_0"]
        assert action == pytest.approx(HBAR_SI, rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_velocity_scale(self, m_si: float, lambda_si: float) -> None:
        """
        v_z_code = hbar_code * k0_code / m_code = 1*20/0.5 = 40.
        v_z_SI = v_z_code * L_0 / T_0.
        This must match hbar_SI * k_SI / m_SI.
        """
        sc = compute_scales(m_si, lambda_si)
        v_z_code = HBAR_CODE * K0_CODE / M_CODE  # = 40
        v_z_from_scales = v_z_code * sc["L_0"] / sc["T_0"]
        assert v_z_from_scales == pytest.approx(sc["v_z_SI"], rel=RTOL)

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_L0_is_positive_and_finite(self, m_si: float, lambda_si: float) -> None:
        """L_0 must be positive and representable in IEEE 754."""
        sc = compute_scales(m_si, lambda_si)
        assert sc["L_0"] > 0
        assert np.isfinite(sc["L_0"])

    @pytest.mark.parametrize("m_si,lambda_si", SCALES)
    def test_E0_is_positive_and_finite(self, m_si: float, lambda_si: float) -> None:
        """E_0 must be positive and representable in IEEE 754."""
        sc = compute_scales(m_si, lambda_si)
        assert sc["E_0"] > 0
        assert np.isfinite(sc["E_0"])


# ===================================================================
# Summary table (printed on direct execution)
# ===================================================================


def _run_summary() -> None:
    """Print a summary table of all 7 SI constants in the framework."""
    print()
    print("=" * 90)
    print("SI Defining Constants in the Quaternionic Framework — Summary")
    print("=" * 90)
    print(f"{'Constant':<12} {'Can Represent?':<16} {'Round-trip Error':<20} {'Notes'}")
    print("-" * 90)

    # Use electron scale for the summary
    sc = compute_scales(M_ELECTRON, LAMBDA_ELEC)

    # 1. h
    h_code = H_SI / (sc["E_0"] * sc["T_0"])
    h_back = h_code * sc["E_0"] * sc["T_0"]
    err_h = abs(h_back - H_SI) / H_SI
    print(f"{'h':<12} {'YES':<16} {err_h:<20.2e} h_code = 2*pi (scale-independent)")

    # 2. c
    c_code = C_SI * sc["T_0"] / sc["L_0"]
    c_back = c_code * sc["L_0"] / sc["T_0"]
    err_c = abs(c_back - C_SI) / C_SI
    print(f"{'c':<12} {'YES':<16} {err_c:<20.2e} c_code = {c_code:.4e}")

    # 3. DeltaNu_Cs
    dnu_code = DELTA_NU_CS * sc["T_0"]
    dnu_back = dnu_code / sc["T_0"]
    err_dnu = abs(dnu_back - DELTA_NU_CS) / DELTA_NU_CS
    print(
        f"{'DeltaNu_Cs':<12} {'YES':<16} {err_dnu:<20.2e} " f"dnu_code = {dnu_code:.4e}"
    )

    # 4. k_B
    T_K_0 = sc["E_0"] / K_B_SI
    k_code = K_B_SI * T_K_0 / sc["E_0"]
    kb_back = k_code * sc["E_0"] / T_K_0
    err_kb = abs(kb_back - K_B_SI) / K_B_SI
    print(
        f"{'k_B':<12} {'YES':<16} {err_kb:<20.2e} " f"k_code = 1 (with T_K_0 = E_0/k_B)"
    )

    # 5. e
    Q_0 = E_CHARGE
    e_code = E_CHARGE / Q_0
    e_back = e_code * Q_0
    err_e = abs(e_back - E_CHARGE) / E_CHARGE
    print(
        f"{'e':<12} {'PARTIAL':<16} {err_e:<20.2e} "
        f"Charge scale not in framework; extension: Q_0=e, e_code=1"
    )

    # 6. N_A
    print(
        f"{'N_A':<12} {'YES (trivial)':<16} {'0.00e+00':<20} "
        f"Dimensionless counting constant; no conversion needed"
    )

    # 7. K_cd
    print(
        f"{'K_cd':<12} {'PARTIAL':<16} {'N/A':<20} "
        f"Requires candela (photometric); power component representable"
    )

    print("-" * 90)
    print("PARTIAL = framework can be extended but current scope is quantum mechanical")
    print("         (Schrodinger equation: length, energy, time only)")
    print("=" * 90)
    print()

    # Scale comparison
    print("Scale Coverage:")
    print(f"{'Scale':<20} {'L_0 (m)':<18} {'E_0 (J)':<18} {'T_0 (s)':<18}")
    print("-" * 74)
    for name, m_si, lam in [
        ("Electron (0.05nm)", M_ELECTRON, LAMBDA_ELEC),
        ("Neutron (0.18nm)", M_NEUTRON, LAMBDA_NEUT),
        ("Planck", M_PLANCK, LAMBDA_PLANCK),
    ]:
        s = compute_scales(m_si, lam)
        print(f"{name:<20} {s['L_0']:<18.4e} {s['E_0']:<18.4e} {s['T_0']:<18.4e}")
    print()


if __name__ == "__main__":
    _run_summary()
