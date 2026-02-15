# src/simulation/wave_propagation.py
"""
2D Beam Propagation Method (BPM) Solver

Propagates coupled quaternionic wavefunctions ψ₀, ψ₁ through a double-slit
geometry using the split-step Fourier method.

The solver marches along z (propagation direction), computing transverse
diffraction (via FFT in x) and potential interactions at each z-step.

Physics reference: research/03_double_slit_expected_results.md §3.3
Algorithm: Split-step BPM (half diffraction → full potential → half diffraction)

Unit architecture: BPM internals use natural units (ℏ=1, m=0.5).
SI conversion happens at the output boundary via si_conversion.py.
See docs/conventions/units.md for the two-layer architecture.

Device strategy:
- GPU (PyTorch + ROCm) when available — primary compute path
- CPU (NumPy) fallback — slower but functional
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Optional


# ---------------------------------------------------------------------------
# Try importing PyTorch; fall back to NumPy-only mode
# ---------------------------------------------------------------------------
try:
    import torch

    HAS_TORCH = True
except (ImportError, OSError):
    # OSError: libgomp or ROCm libs not found
    HAS_TORCH = False


# ---------------------------------------------------------------------------
# Configuration dataclasses
# ---------------------------------------------------------------------------


@dataclass
class SimulationConfig:
    """Configuration for BPM propagation."""

    Nx: int = 4096  # transverse grid points
    X_max: float = 20.0  # half-domain width (natural units)
    dz: float = 0.05  # propagation step size
    Nz_steps: int = 20000  # number of propagation steps
    k0: float = 20.0  # central wavenumber
    hbar: float = 1.0  # reduced Planck constant
    mass: float = 0.5  # particle mass
    device: str = "auto"  # 'cuda', 'cpu', or 'auto'
    snapshot_interval: int = 0  # save snapshots every N steps (0 = no snapshots)

    def __post_init__(self):
        if self.device == "auto":
            if HAS_TORCH and torch.cuda.is_available():
                self.device = "cuda"
            else:
                self.device = "cpu"


@dataclass
class SlitConfig:
    """Double-slit geometry and potential configuration."""

    separation: float  # d: distance between slit centers
    width: float  # a: width of each slit
    barrier_height: float  # U₀: barrier wall height
    U1_strength: float  # U₁: quaternionic coupling strength
    z_position: float  # z-location of slit plane
    z_thickness: float  # thickness of slit region along z


@dataclass
class TransverseGrid:
    """Precomputed transverse grid and propagators."""

    x: np.ndarray  # position array (Nx,)
    dx: float  # grid spacing
    kx: np.ndarray  # momentum array (Nx,)
    diffraction_half: np.ndarray  # exp(-i·kx²·dz/(4m·k0/ℏ)) for half step


@dataclass
class PropagationResult:
    """Results from BPM propagation."""

    detector_psi0: np.ndarray  # ψ₀(x) at final z
    detector_psi1: np.ndarray  # ψ₁(x) at final z
    x: np.ndarray  # transverse grid
    config: SimulationConfig
    norm_history: list  # total norm at each z
    decay_curve: list  # (z, η) pairs where η = |ψ₁|²/|ψ|²
    snapshots: Optional[dict] = None  # {step: (psi0, psi1)} if requested


# ---------------------------------------------------------------------------
# Grid setup
# ---------------------------------------------------------------------------


def create_transverse_grid(config: SimulationConfig) -> TransverseGrid:
    """
    Create the transverse (x) grid and precompute the diffraction propagator.

    The diffraction propagator in k-space is:
        exp(-i · ℏ·kx² · dz / (4·mass))

    This is the half-step propagator for the split-step method.
    The factor of 4 (not 2) is because we apply two half-steps per full step.
    """
    dx = 2 * config.X_max / config.Nx
    x = np.linspace(-config.X_max, config.X_max - dx, config.Nx)

    # Momentum grid (FFT convention)
    kx = 2 * np.pi * np.fft.fftfreq(config.Nx, d=dx)

    # Half-step diffraction propagator
    # From iℏ∂ψ/∂z = -(ℏ²/2m)∂²ψ/∂x² (paraxial approx in BPM)
    # → exp(-i·ℏ·kx²·dz/(4m)) for half step
    diffraction_half = np.exp(-1j * config.hbar * kx**2 * config.dz / (4 * config.mass))

    return TransverseGrid(x=x, dx=dx, kx=kx, diffraction_half=diffraction_half)


# ---------------------------------------------------------------------------
# Potential construction
# ---------------------------------------------------------------------------


def create_slit_potential(
    grid: TransverseGrid,
    slit: SlitConfig,
    z: float,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Compute U₀(x) and U₁(x) at a given z position.

    The slit geometry:
    - Barrier (U₀ = barrier_height) everywhere except the two slit openings
    - Slits centered at x = ±d/2, each of width a
    - U₁ is nonzero only in the slit openings (quaternionic coupling region)
    - Potentials are nonzero only within the slit z-thickness

    Args:
        grid: transverse grid
        slit: slit configuration
        z: current z position

    Returns:
        (U0, U1) arrays of shape (Nx,)
    """
    x = grid.x
    Nx = len(x)

    # Check if we're in the slit region along z
    z_start = slit.z_position - slit.z_thickness / 2
    z_end = slit.z_position + slit.z_thickness / 2
    in_slit_region = z_start <= z <= z_end

    if not in_slit_region:
        return np.zeros(Nx), np.zeros(Nx)

    # Slit openings: x ∈ [d/2 - a/2, d/2 + a/2] and [-d/2 - a/2, -d/2 + a/2]
    half_d = slit.separation / 2
    half_a = slit.width / 2

    slit1 = (x >= (half_d - half_a)) & (x <= (half_d + half_a))
    slit2 = (x >= (-half_d - half_a)) & (x <= (-half_d + half_a))
    in_slit = slit1 | slit2

    # U₀: barrier everywhere except slits
    U0 = np.where(in_slit, 0.0, slit.barrier_height)

    # U₁: quaternionic coupling only at slit openings
    U1 = np.where(in_slit, slit.U1_strength, 0.0)

    return U0, U1


def create_single_slit_potential(
    grid: TransverseGrid,
    slit: SlitConfig,
    z: float,
    which_slit: int,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Create potential with only one slit open (for which-path simulation).

    Args:
        grid: transverse grid
        slit: slit configuration (defines both slits, we open only one)
        z: current z position
        which_slit: 1 for upper slit (+d/2), 2 for lower slit (-d/2)

    Returns:
        (U0, U1) arrays
    """
    x = grid.x
    Nx = len(x)

    z_start = slit.z_position - slit.z_thickness / 2
    z_end = slit.z_position + slit.z_thickness / 2
    in_slit_region = z_start <= z <= z_end

    if not in_slit_region:
        return np.zeros(Nx), np.zeros(Nx)

    half_d = slit.separation / 2
    half_a = slit.width / 2

    if which_slit == 1:
        # Only upper slit open
        open_slit = (x >= (half_d - half_a)) & (x <= (half_d + half_a))
    else:
        # Only lower slit open
        open_slit = (x >= (-half_d - half_a)) & (x <= (-half_d + half_a))

    U0 = np.where(open_slit, 0.0, slit.barrier_height)
    U1 = np.where(open_slit, slit.U1_strength, 0.0)

    return U0, U1


def create_barrier_potential_1d(
    x: np.ndarray,
    center: float,
    width: float,
    U1_strength: float,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Create a simple 1D quaternionic barrier for Stage 1 testing.

    U₀ = 0 (no standard potential)
    U₁ = U1_strength within the barrier region

    Args:
        x: spatial grid
        center: barrier center position
        width: barrier width (Gaussian sigma)
        U1_strength: peak quaternionic coupling

    Returns:
        (U0, U1) arrays
    """
    U0 = np.zeros_like(x)
    U1 = U1_strength * np.exp(-(((x - center) / width) ** 2))
    return U0, U1


# ---------------------------------------------------------------------------
# Initial wavepacket
# ---------------------------------------------------------------------------


def create_initial_wavepacket(
    grid: TransverseGrid,
    k0: float,
    sigma: float,
    eta0: float = 0.0,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Create initial wavepacket.

    ψ₀(x) = A · exp(-x²/(4σ²)) · exp(ik₀x)  (Gaussian with forward momentum)
    ψ₁(x) = √(η₀/(1-η₀)) · ψ₀(x)           (if η₀ > 0)

    The quaternionic fraction η₀ = |ψ₁|²/(|ψ₀|²+|ψ₁|²).

    Args:
        grid: transverse grid
        k0: central wavenumber (forward momentum)
        sigma: Gaussian width
        eta0: initial quaternionic fraction (0 = pure complex)

    Returns:
        (psi0, psi1) complex arrays of shape (Nx,)
    """
    x = grid.x

    # Gaussian envelope with forward momentum
    psi0 = np.exp(-(x**2) / (4 * sigma**2)) * np.exp(1j * k0 * x)

    # Normalize
    norm = np.sqrt(np.sum(np.abs(psi0) ** 2) * grid.dx)
    psi0 = psi0 / norm

    # Quaternionic component
    if eta0 > 0 and eta0 < 1:
        # η₀ = |ψ₁|²/(|ψ₀|²+|ψ₁|²)
        # If ψ₁ = α·ψ₀, then η₀ = α²/(1+α²), so α = √(η₀/(1-η₀))
        alpha = np.sqrt(eta0 / (1 - eta0))
        psi1 = alpha * psi0.copy()
        # Re-normalize total
        total_norm = np.sqrt(np.sum(np.abs(psi0) ** 2 + np.abs(psi1) ** 2) * grid.dx)
        psi0 /= total_norm
        psi1 /= total_norm
    else:
        psi1 = np.zeros_like(psi0)

    return psi0, psi1


# ---------------------------------------------------------------------------
# BPM propagation step
# ---------------------------------------------------------------------------


def _diffraction_step(psi: np.ndarray, propagator: np.ndarray) -> np.ndarray:
    """Apply half diffraction step in k-space."""
    psi_k = np.fft.fft(psi)
    psi_k *= propagator
    return np.fft.ifft(psi_k)


def _potential_step(
    psi0: np.ndarray,
    psi1: np.ndarray,
    U0: np.ndarray,
    U1: np.ndarray,
    dz: float,
    hbar: float,
) -> tuple[np.ndarray, np.ndarray]:
    """
    Exact potential step for the coupled quaternionic system.

    Derived from the quaternionic Hamiltonian H = U₀ + U₁·j acting on
    ψ = ψ₀ + ψ₁·j via left multiplication:

        H·ψ = (U₀·ψ₀ − U₁·ψ₁*) + (U₀·ψ₁ + U₁·ψ₀*)·j

    where the conjugation arises from j·z = z*·j for complex z, giving
    j·ψ₁·j = −ψ₁*. This yields the coupled equations:

        iℏ dψ₀/dz = U₀·ψ₀ − U₁·ψ₁*
        iℏ dψ₁/dz = U₀·ψ₁ + U₁·ψ₀*

    Solved in two stages:
    1. U₀ phase rotation: exp(−iU₀·dz/ℏ) applied to both components
    2. U₁ coupling rotation: SO(4) rotation in (Re ψ₀, Im ψ₀, Re ψ₁, Im ψ₁)
       space, preserving |ψ₀|² + |ψ₁|² pointwise

    Args:
        psi0, psi1: wavefunctions
        U0, U1: potentials (real arrays)
        dz: propagation step size
        hbar: ℏ

    Returns:
        (psi0_new, psi1_new)
    """
    # Stage 1: U₀ phase rotation
    phase = np.exp(-1j * U0 * dz / hbar)
    psi0 = psi0 * phase
    psi1 = psi1 * phase

    # Stage 2: U₁ coupling
    # Real/imaginary decomposition to handle conjugation:
    # dp/dz = (U₁/ℏ)s,  dq/dz = (U₁/ℏ)r
    # dr/dz = -(U₁/ℏ)q, ds/dz = -(U₁/ℏ)p
    theta = U1 * dz / hbar
    cos_t = np.cos(theta)
    sin_t = np.sin(theta)

    p = psi0.real.copy()
    q = psi0.imag.copy()
    r = psi1.real.copy()
    s = psi1.imag.copy()

    p_new = cos_t * p + sin_t * s
    q_new = cos_t * q + sin_t * r
    r_new = cos_t * r - sin_t * q
    s_new = cos_t * s - sin_t * p

    return p_new + 1j * q_new, r_new + 1j * s_new


def bpm_step(
    psi0: np.ndarray,
    psi1: np.ndarray,
    U0: np.ndarray,
    U1: np.ndarray,
    grid: TransverseGrid,
    config: SimulationConfig,
) -> tuple[np.ndarray, np.ndarray]:
    """
    One full BPM z-step: half diffraction → full potential → half diffraction.

    Args:
        psi0, psi1: current wavefunctions (Nx,)
        U0, U1: potentials at current z (Nx,)
        grid: transverse grid with precomputed propagator
        config: simulation config

    Returns:
        (psi0_new, psi1_new) after one z-step
    """
    prop = grid.diffraction_half

    # Half diffraction
    psi0 = _diffraction_step(psi0, prop)
    psi1 = _diffraction_step(psi1, prop)

    # Full potential
    psi0, psi1 = _potential_step(psi0, psi1, U0, U1, config.dz, config.hbar)

    # Half diffraction
    psi0 = _diffraction_step(psi0, prop)
    psi1 = _diffraction_step(psi1, prop)

    return psi0, psi1


# ---------------------------------------------------------------------------
# GPU-accelerated BPM (PyTorch)
# ---------------------------------------------------------------------------


def _to_torch(arr, device):
    """Convert numpy array to torch tensor on device."""
    if not HAS_TORCH:
        raise RuntimeError("PyTorch not available")
    return torch.from_numpy(arr).to(device)


def _to_numpy(tensor):
    """Convert torch tensor to numpy array."""
    return tensor.detach().cpu().numpy()


def bpm_step_torch(
    psi0: "torch.Tensor",
    psi1: "torch.Tensor",
    U0: "torch.Tensor",
    U1: "torch.Tensor",
    prop: "torch.Tensor",
    dz: float,
    hbar: float,
) -> tuple:
    """
    GPU-accelerated BPM step using PyTorch.

    Same algorithm as bpm_step but using torch tensors for GPU computation.
    """
    # Half diffraction
    psi0 = torch.fft.ifft(torch.fft.fft(psi0) * prop)
    psi1 = torch.fft.ifft(torch.fft.fft(psi1) * prop)

    # U₀ phase rotation
    phase = torch.exp(-1j * U0 * dz / hbar)
    psi0 = psi0 * phase
    psi1 = psi1 * phase

    # U₁ coupling
    theta = U1 * dz / hbar
    cos_t = torch.cos(theta)
    sin_t = torch.sin(theta)

    p = psi0.real.clone()
    q = psi0.imag.clone()
    r = psi1.real.clone()
    s = psi1.imag.clone()

    psi0 = torch.complex(cos_t * p + sin_t * s, cos_t * q + sin_t * r)
    psi1 = torch.complex(cos_t * r - sin_t * q, cos_t * s - sin_t * p)

    # Half diffraction
    psi0 = torch.fft.ifft(torch.fft.fft(psi0) * prop)
    psi1 = torch.fft.ifft(torch.fft.fft(psi1) * prop)

    return psi0, psi1


# ---------------------------------------------------------------------------
# Full propagation
# ---------------------------------------------------------------------------


def propagate(
    psi0_init: np.ndarray,
    psi1_init: np.ndarray,
    grid: TransverseGrid,
    config: SimulationConfig,
    slit: Optional[SlitConfig] = None,
    U0_static: Optional[np.ndarray] = None,
    U1_static: Optional[np.ndarray] = None,
    potential_func: Optional[object] = None,
) -> PropagationResult:
    """
    Propagate wavefunctions from z=0 to z=Nz_steps*dz.

    Supports three modes:
    1. Static potential: U0_static, U1_static applied at every z-step
    2. Slit geometry: potentials computed from SlitConfig at each z
    3. Custom: potential_func(grid, z) → (U0, U1) called at each z

    Args:
        psi0_init, psi1_init: initial wavefunctions
        grid: transverse grid
        config: simulation config
        slit: optional slit geometry (if None, use static potentials)
        U0_static: optional static U₀(x) potential
        U1_static: optional static U₁(x) potential
        potential_func: optional callable(grid, z) → (U0, U1)

    Returns:
        PropagationResult with detector fields and diagnostics
    """
    use_gpu = config.device == "cuda" and HAS_TORCH and torch.cuda.is_available()

    if use_gpu:
        if potential_func is not None:
            raise NotImplementedError(
                "GPU propagation does not support potential_func. "
                "Use device='cpu' or pass slit/U0_static/U1_static instead."
            )
        return _propagate_gpu(
            psi0_init, psi1_init, grid, config, slit, U0_static, U1_static
        )
    else:
        return _propagate_cpu(
            psi0_init,
            psi1_init,
            grid,
            config,
            slit,
            U0_static,
            U1_static,
            potential_func,
        )


def _propagate_cpu(
    psi0_init,
    psi1_init,
    grid,
    config,
    slit,
    U0_static,
    U1_static,
    potential_func=None,
):
    """CPU propagation using NumPy."""
    psi0 = psi0_init.copy()
    psi1 = psi1_init.copy()

    norm_history = []
    decay_curve = []
    snapshots = {} if config.snapshot_interval > 0 else None

    for step in range(config.Nz_steps):
        z = step * config.dz

        # Get potentials
        if potential_func is not None:
            U0, U1 = potential_func(grid, z)
        elif slit is not None:
            U0, U1 = create_slit_potential(grid, slit, z)
        elif U0_static is not None:
            U0 = U0_static
            U1 = U1_static if U1_static is not None else np.zeros_like(U0_static)
        else:
            U0 = np.zeros(config.Nx)
            U1 = np.zeros(config.Nx)

        # BPM step
        psi0, psi1 = bpm_step(psi0, psi1, U0, U1, grid, config)

        # Diagnostics (every 100 steps to avoid overhead)
        if step % 100 == 0 or step == config.Nz_steps - 1:
            norm0 = np.sum(np.abs(psi0) ** 2) * grid.dx
            norm1 = np.sum(np.abs(psi1) ** 2) * grid.dx
            total_norm = norm0 + norm1
            eta = norm1 / total_norm if total_norm > 0 else 0.0

            norm_history.append(total_norm)
            decay_curve.append((z, eta))

        # Snapshots
        if snapshots is not None and step % config.snapshot_interval == 0:
            snapshots[step] = (psi0.copy(), psi1.copy())

    return PropagationResult(
        detector_psi0=psi0,
        detector_psi1=psi1,
        x=grid.x,
        config=config,
        norm_history=norm_history,
        decay_curve=decay_curve,
        snapshots=snapshots,
    )


def _propagate_gpu(
    psi0_init,
    psi1_init,
    grid,
    config,
    slit,
    U0_static,
    U1_static,
):
    """GPU propagation using PyTorch."""
    device = config.device

    # Transfer to GPU
    psi0 = _to_torch(psi0_init.astype(np.complex128), device)
    psi1 = _to_torch(psi1_init.astype(np.complex128), device)
    prop = _to_torch(grid.diffraction_half, device)
    dx = grid.dx

    # Precompute static potentials on GPU if applicable
    if slit is None and U0_static is not None:
        U0_gpu = _to_torch(U0_static.astype(np.float64), device)
        U1_gpu = _to_torch(
            (U1_static if U1_static is not None else np.zeros_like(U0_static)).astype(
                np.float64
            ),
            device,
        )
    else:
        U0_gpu = None
        U1_gpu = None

    norm_history = []
    decay_curve = []
    snapshots = {} if config.snapshot_interval > 0 else None

    for step in range(config.Nz_steps):
        z = step * config.dz

        # Get potentials
        if slit is not None:
            U0_np, U1_np = create_slit_potential(grid, slit, z)
            U0_t = _to_torch(U0_np, device)
            U1_t = _to_torch(U1_np, device)
        elif U0_gpu is not None:
            U0_t = U0_gpu
            U1_t = U1_gpu
        else:
            U0_t = torch.zeros(config.Nx, device=device, dtype=torch.float64)
            U1_t = torch.zeros(config.Nx, device=device, dtype=torch.float64)

        # BPM step
        psi0, psi1 = bpm_step_torch(
            psi0, psi1, U0_t, U1_t, prop, config.dz, config.hbar
        )

        # Diagnostics
        if step % 100 == 0 or step == config.Nz_steps - 1:
            norm0 = torch.sum(torch.abs(psi0) ** 2).item() * dx
            norm1 = torch.sum(torch.abs(psi1) ** 2).item() * dx
            total_norm = norm0 + norm1
            eta = norm1 / total_norm if total_norm > 0 else 0.0

            norm_history.append(total_norm)
            decay_curve.append((z, eta))

        # Snapshots
        if snapshots is not None and step % config.snapshot_interval == 0:
            snapshots[step] = (_to_numpy(psi0), _to_numpy(psi1))

    return PropagationResult(
        detector_psi0=_to_numpy(psi0),
        detector_psi1=_to_numpy(psi1),
        x=grid.x,
        config=config,
        norm_history=norm_history,
        decay_curve=decay_curve,
        snapshots=snapshots,
    )


# ---------------------------------------------------------------------------
# Analysis utilities
# ---------------------------------------------------------------------------


def far_field_intensity(result: PropagationResult) -> tuple:
    """
    Compute far-field intensity from propagation result.

    Returns:
        (x, I_total, I_psi0, I_psi1)
    """
    I_psi0 = np.abs(result.detector_psi0) ** 2
    I_psi1 = np.abs(result.detector_psi1) ** 2
    I_total = I_psi0 + I_psi1

    return result.x, I_total, I_psi0, I_psi1


def compute_eta(psi0: np.ndarray, psi1: np.ndarray, dx: float) -> float:
    """Compute quaternionic fraction η = ∫|ψ₁|²dx / ∫(|ψ₀|²+|ψ₁|²)dx."""
    norm0 = np.sum(np.abs(psi0) ** 2) * dx
    norm1 = np.sum(np.abs(psi1) ** 2) * dx
    total = norm0 + norm1
    return norm1 / total if total > 0 else 0.0
