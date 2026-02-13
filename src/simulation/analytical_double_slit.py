# src/simulation/analytical_double_slit.py
"""
Analytical Double-Slit Baselines (CPU only)

Exact closed-form solutions for Scenarios A and B, used as reference
baselines for the numerical BPM solver.

Physics reference: research/03_double_slit_expected_results.md §4.1, §4.2
"""

import numpy as np
from dataclasses import dataclass


@dataclass
class SlitParameters:
    """Physical parameters for double-slit experiment."""

    d: float  # slit separation (m)
    a: float  # slit width (m)
    wavelength: float  # de Broglie wavelength (m)
    L: float  # propagation distance to detector (m)

    @property
    def k(self) -> float:
        """Wavenumber k = 2π/λ."""
        return 2 * np.pi / self.wavelength

    @property
    def fringe_spacing(self) -> float:
        """Predicted fringe spacing Δx = λL/d."""
        return self.wavelength * self.L / self.d


def fraunhofer_pattern(x: np.ndarray, params: SlitParameters) -> np.ndarray:
    """
    Scenario A: Fraunhofer double-slit intensity pattern.

    I(x) = 4A² · cos²(πxd/λL) · sinc²(πxa/λL)

    where the cos² term gives interference fringes and the sinc² gives
    the single-slit diffraction envelope.

    Args:
        x: detector positions (m)
        params: slit parameters

    Returns:
        Normalized intensity I(x) (peak = 1.0)
    """
    # Interference term: cos²(πxd/λL)
    alpha = np.pi * x * params.d / (params.wavelength * params.L)
    interference = np.cos(alpha) ** 2

    # Single-slit envelope: sinc²(πxa/λL)
    # np.sinc(x) = sin(πx)/(πx), so we pass xa/(λL)
    beta = x * params.a / (params.wavelength * params.L)
    envelope = np.sinc(beta) ** 2

    pattern = interference * envelope

    # Normalize to peak = 1
    peak = np.max(pattern)
    if peak > 0:
        pattern /= peak

    return pattern


def which_path_pattern(x: np.ndarray, params: SlitParameters) -> np.ndarray:
    """
    Scenario B: Incoherent sum (which-path detection).

    I(x) = A² · sinc²(πxa/λL)

    No interference fringes — just the single-slit envelope.
    With which-path detection, the cross-term vanishes.

    Args:
        x: detector positions (m)
        params: slit parameters

    Returns:
        Normalized intensity I(x) (peak = 1.0)
    """
    beta = x * params.a / (params.wavelength * params.L)
    pattern = np.sinc(beta) ** 2

    peak = np.max(pattern)
    if peak > 0:
        pattern /= peak

    return pattern


def fringe_visibility(
    intensity: np.ndarray, x: np.ndarray = None, expected_spacing: float = None
) -> float:
    """
    Compute interference fringe visibility V = (I_max - I_min) / (I_max + I_min).

    Measures the contrast of rapid oscillations (interference fringes), not
    the slow single-slit diffraction envelope. Uses the central region where
    the envelope is approximately flat.

    Strategy:
    - Use central 20% of the array (near x=0) where envelope ≈ 1
    - Find adjacent local max-min pairs
    - Compute per-pair visibility and average

    Args:
        intensity: 1D intensity array
        x: optional position array (for diagnostics)
        expected_spacing: optional expected fringe spacing (not used in computation)

    Returns:
        Visibility V ∈ [0, 1]
    """
    N = len(intensity)
    # Use central 20% where envelope is flat
    start = int(N * 0.4)
    end = int(N * 0.6)
    central = intensity[start:end]

    if len(central) < 5:
        return 0.0

    # Find local maxima and minima
    max_vals = []
    min_vals = []
    max_idx = []
    min_idx = []

    for i in range(1, len(central) - 1):
        if central[i] > central[i - 1] and central[i] > central[i + 1]:
            max_vals.append(central[i])
            max_idx.append(i)
        if central[i] < central[i - 1] and central[i] < central[i + 1]:
            min_vals.append(central[i])
            min_idx.append(i)

    if not max_vals or not min_vals:
        return 0.0

    # Compute per-pair visibility for adjacent max-min pairs
    # This isolates fringe contrast from envelope modulation
    visibilities = []
    all_extrema = sorted(
        [(i, "max", v) for i, v in zip(max_idx, max_vals)]
        + [(i, "min", v) for i, v in zip(min_idx, min_vals)],
        key=lambda x: x[0],
    )

    for j in range(len(all_extrema) - 1):
        idx1, type1, val1 = all_extrema[j]
        idx2, type2, val2 = all_extrema[j + 1]

        # Only consider adjacent max-min pairs (not max-max or min-min)
        if type1 == type2:
            continue

        I_hi = max(val1, val2)
        I_lo = min(val1, val2)

        if I_hi + I_lo > 0:
            visibilities.append((I_hi - I_lo) / (I_hi + I_lo))

    if not visibilities:
        return 0.0

    return float(np.mean(visibilities))


def fringe_positions(params: SlitParameters, n_max: int = 10) -> np.ndarray:
    """
    Predicted positions of interference maxima.

    x_n = n·λL/d,  n = 0, ±1, ±2, ...

    Args:
        params: slit parameters
        n_max: maximum fringe order

    Returns:
        Array of fringe positions (m)
    """
    n = np.arange(-n_max, n_max + 1)
    return n * params.fringe_spacing


def minima_positions(params: SlitParameters, n_max: int = 10) -> np.ndarray:
    """
    Predicted positions of interference minima.

    x_n = (n + 1/2)·λL/d

    Args:
        params: slit parameters
        n_max: maximum fringe order

    Returns:
        Array of minima positions (m)
    """
    n = np.arange(-n_max, n_max + 1)
    return (n + 0.5) * params.fringe_spacing
