"""
SI Conversion Library for the QBP Beam Propagation Method

Project convention: ℏ = c = 1 (standard HEP natural units).
c does not appear in the current non-relativistic BPM, but the convention
is established now for forward compatibility with relativistic (galactic-scale)
extensions.  C_SI = 299_792_458 m/s is provided for SI recovery.

Two-layer unit conversion framework:

Layer 1: Standard BPM natural units <-> SI
    BPM internals use natural units (hbar=1, m=0.5, k0=20) for numerical
    stability — this is standard practice in production physics codes
    (MEEP, LAMMPS, Quantum ESPRESSO; Agrawal Ch. 2.4; Saleh & Teich).
    SI conversion happens at output boundaries via {L_0, E_0, T_0} scales.

Layer 2: Quaternionic derived quantities (MODEL-DEPENDENT)
    L_Q and zeta are derived from the algebraic structure but have NOT yet
    been validated against peer-reviewed experiments. They must be treated
    as model-dependent predictions until experimental confirmation is documented.

See docs/conventions/units.md for the full architecture description.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

# ---------------------------------------------------------------------------
# BPM code parameters (from quaternionic_si_definitions.md Section 7.1)
# ---------------------------------------------------------------------------
HBAR_CODE = 1.0
M_CODE = 0.5
K0_CODE = 20.0

# ---------------------------------------------------------------------------
# Structural invariant: v_z absorption factor (canonical single source of truth)
# ---------------------------------------------------------------------------
# Both BPM split-step components (diffraction and potential) absorb
# v_z_code = hbar_code * k0_code / m_code identically.  This is the
# Jacobian of the time->space propagation transformation.  If this
# invariant breaks, the BPM violates unitarity.
V_Z_CODE: float = HBAR_CODE * K0_CODE / M_CODE  # = 40.0

# ---------------------------------------------------------------------------
# Physical constants (exact values from the 2019 SI redefinition)
# ---------------------------------------------------------------------------
H_SI = 6.626_070_15e-34  # J*s  (exact)
HBAR_SI = H_SI / (2 * math.pi)  # J*s
EV_IN_JOULES = 1.602_176_634e-19  # J per eV (exact)
C_SI = 299_792_458  # m/s  (exact, defines the metre)


# ---------------------------------------------------------------------------
# Layer 1: Standard BPM <-> SI Conversion
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ScaleFactors:
    """Conversion scales between BPM natural units and SI.

    These are computed from a source particle's mass and de Broglie wavelength.
    All fields carry SI units except mass_si and lambda_si which are the
    traceability inputs.
    """

    mass_si: float  # source particle mass [kg]
    lambda_si: float  # source de Broglie wavelength [m]
    L0: float  # length scale [m per code unit]
    E0: float  # energy scale [J per code unit]
    T0: float  # time scale [s per code unit]
    v_z_si: float  # longitudinal velocity [m/s]
    k_si: float  # wavenumber [1/m]


def compute_scales(m_si: float, lambda_si: float) -> ScaleFactors:
    """Compute SI conversion scales from particle mass and de Broglie wavelength.

    This is pure arithmetic — no grids or arrays are allocated.

    Args:
        m_si: Particle rest mass in kg.  Must be positive.
        lambda_si: de Broglie wavelength in metres.  Must be positive.

    Returns:
        ScaleFactors dataclass with all conversion coefficients.

    Raises:
        ValueError: if m_si or lambda_si is non-positive.
    """
    if m_si <= 0:
        raise ValueError(f"Mass must be positive, got {m_si}")
    if lambda_si <= 0:
        raise ValueError(f"Wavelength must be positive, got {lambda_si}")

    k_si = 2 * math.pi / lambda_si
    L0 = K0_CODE * lambda_si / (2 * math.pi)

    # E_0 = hbar_SI^2 * m_code / (m_SI * L_0^2 * hbar_code^2)
    E0 = HBAR_SI**2 * M_CODE / (m_si * L0**2 * HBAR_CODE**2)

    # T_0 = hbar_SI / E_0
    T0 = HBAR_SI / E0

    # Physical velocity
    v_z_si = HBAR_SI * k_si / m_si

    return ScaleFactors(
        mass_si=m_si,
        lambda_si=lambda_si,
        L0=L0,
        E0=E0,
        T0=T0,
        v_z_si=v_z_si,
        k_si=k_si,
    )


# ---------------------------------------------------------------------------
# Output conversion (Code -> SI)
# ---------------------------------------------------------------------------


def convert_position(x_code: float, scales: ScaleFactors) -> float:
    """Convert position from code units to SI metres."""
    return x_code * scales.L0


def convert_potential(U_code: float, scales: ScaleFactors) -> float:
    """Convert potential from code units to SI electron-volts.

    The BPM propagates in z (space) rather than t (time).  This converts
    the Schrödinger time-derivative to a spatial derivative, absorbing the
    longitudinal velocity v_z into every potential term.  Therefore
    U_physical = U_code * v_z_code * E_0.  Dividing by eV gives electron-volts.

    Derivation: see docs/conventions/units.md § "V_Z_CODE Derivation".
    Proven correct: PR #323 (3 independent tests).
    """
    # V_Z_CODE factor: Jacobian of time→space propagation (see module docstring)
    return U_code * V_Z_CODE * scales.E0 / EV_IN_JOULES


def convert_energy(E_code: float, scales: ScaleFactors) -> float:
    """Convert energy from code units to SI joules."""
    return E_code * scales.E0


# ---------------------------------------------------------------------------
# Input conversion (SI -> Code)
# ---------------------------------------------------------------------------


def convert_length_to_code(val_m: float, scales: ScaleFactors) -> float:
    """Convert length from SI metres to code units."""
    return val_m / scales.L0


def convert_energy_to_code(val_J: float, scales: ScaleFactors) -> float:
    """Convert energy from SI joules to code units."""
    return val_J / scales.E0


# ---------------------------------------------------------------------------
# Column annotation
# ---------------------------------------------------------------------------


def annotate_columns(df, unit_map: dict[str, str]):
    """Rename DataFrame columns by appending unit suffixes.

    Args:
        df: Input pandas DataFrame.
        unit_map: Mapping from current column name to unit suffix string.
            Example: {"x_position": "m", "potential": "eV"}
            Result:  x_position -> x_position_m, potential -> potential_eV

    Returns:
        DataFrame with renamed columns. Original DataFrame is not modified.
    """
    rename = {
        col: f"{col}_{suffix}" for col, suffix in unit_map.items() if col in df.columns
    }
    return df.rename(columns=rename)


# ---------------------------------------------------------------------------
# Layer 2: Quaternionic Derived Quantities (MODEL-DEPENDENT)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class QuaternionicQuantities:
    """Quaternionic derived physical quantities.

    MODEL-DEPENDENT — these quantities are derived from the quaternionic
    algebraic structure but have NOT yet been validated against peer-reviewed
    experiments. They must be treated as model-dependent predictions until
    experimental confirmation is documented.

    Experimental grounding requirement:
        1. An experiment produces data where L_Q or zeta appears as measurable
        2. The measurement is published in peer-reviewed literature
        3. The result has been independently reproduced

    Until then, these are labeled MODEL-DEPENDENT in code and documentation.
    """

    L_Q: float  # Quaternionic beat length [m]: pi * hbar * v_g / U1
    zeta: float  # Quaternionic coupling parameter [dimensionless]: U1 / E_kin


def compute_quaternionic_quantities(
    U1_si: float, E_kin_si: float, v_g_si: float
) -> QuaternionicQuantities:
    """Compute derived quaternionic quantities from SI inputs.

    These are model-dependent predictions motivated by the quaternionic
    algebra. Their status as meaningful physical units depends on
    experimental validation (see docs/conventions/units.md).

    Args:
        U1_si: Quaternionic coupling strength in joules.
        E_kin_si: Kinetic energy in joules.
        v_g_si: Group velocity in m/s.

    Returns:
        QuaternionicQuantities with L_Q [m] and zeta [dimensionless].

    Raises:
        ValueError: if U1_si, E_kin_si, or v_g_si is non-positive.
    """
    if U1_si <= 0:
        raise ValueError(f"U1_si must be positive, got {U1_si}")
    if E_kin_si <= 0:
        raise ValueError(f"E_kin_si must be positive, got {E_kin_si}")
    if v_g_si <= 0:
        raise ValueError(f"v_g_si must be positive, got {v_g_si}")

    L_Q = math.pi * HBAR_SI * v_g_si / U1_si
    zeta = U1_si / E_kin_si

    return QuaternionicQuantities(L_Q=L_Q, zeta=zeta)
