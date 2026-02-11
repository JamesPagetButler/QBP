# qphysics API Reference

**Module:** `src/qphysics.py`

The computational core of the Quaternion-Based Physics (QBP) framework. Implements the three axioms and measurement postulate using NumPy quaternion arithmetic.

## Dependencies

```python
import numpy as np
import quaternion  # numpy-quaternion library
```

---

## Axiom 1: Quaternionic States

Physical quantum states are represented as **pure unit quaternions** (zero real part, norm = 1).

### `create_state(a, b, c, d) -> np.quaternion`

Create a normalized quaternion state from four components.

| Parameter | Type | Description |
|-----------|------|-------------|
| `a` | float | Scalar (real) component |
| `b` | float | i component |
| `c` | float | j component |
| `d` | float | k component |

**Returns:** Unit quaternion representing the state ψ.

**Example:**
```python
# Create spin-z state (equivalent to |↑⟩)
psi = create_state(0, 0, 0, 1)  # Normalized automatically
```

### `create_state_from_vector(vec) -> np.quaternion`

Create a pure quaternion state aligned with a 3D direction.

| Parameter | Type | Description |
|-----------|------|-------------|
| `vec` | list or ndarray | 3D vector [x, y, z] |

**Returns:** Pure unit quaternion with zero scalar part.

**Example:**
```python
# Spin along +x axis
psi_x = create_state_from_vector([1, 0, 0])  # Returns i

# Spin tilted 45° between x and z
psi_45 = create_state_from_vector([1, 0, 1])  # Normalized
```

### `get_state_vector(psi) -> np.ndarray`

Extract the vector (imaginary) part of a quaternion state.

| Parameter | Type | Description |
|-----------|------|-------------|
| `psi` | np.quaternion | The state quaternion |

**Returns:** 3D array [x, y, z].

---

## Axiom 2: Quaternionic Observables

Physical observables are represented as **pure quaternions** (zero real part).

### `create_observable(vec) -> np.quaternion`

Create a pure quaternion observable from a measurement axis.

| Parameter | Type | Description |
|-----------|------|-------------|
| `vec` | list or ndarray | 3D vector defining measurement axis |

**Returns:** Pure quaternion representing observable O.

**Example:**
```python
# Measurement along diagonal axis
O_diag = create_observable([1, 1, 0])
```

### Pre-defined Observables

| Name | Value | Description |
|------|-------|-------------|
| `SPIN_X` | `np.quaternion(0, 1, 0, 0)` | Measurement along x-axis (≡ i) |
| `SPIN_Y` | `np.quaternion(0, 0, 1, 0)` | Measurement along y-axis (≡ j) |
| `SPIN_Z` | `np.quaternion(0, 0, 0, 1)` | Measurement along z-axis (≡ k) |

These correspond to the Pauli spin operators σₓ, σᵧ, σᵤ.

---

## Axiom 3: Quaternionic Evolution

Time evolution under a Hamiltonian.

### `evolve_state(psi_initial, hamiltonian, time) -> np.quaternion`

Evolve a state through time under a given Hamiltonian.

| Parameter | Type | Description |
|-----------|------|-------------|
| `psi_initial` | np.quaternion | Initial state ψ(0) |
| `hamiltonian` | np.quaternion | Hamiltonian H (must be pure) |
| `time` | float | Evolution time t |

**Returns:** Final state ψ(t).

**Formula:** ψ(t) = exp(-Ht) · ψ(0)

**Example:**
```python
# Spin precession under magnetic field along z
psi = SPIN_X  # Start with spin-x
H = SPIN_Z    # Field along z
psi_evolved = evolve_state(psi, H, t=np.pi/2)
```

---

## Measurement Postulate

The QBP measurement rule: expectation value = dot product of vector parts.

### `expectation_value(psi, observable) -> float`

Compute the expectation value ⟨O⟩ for a state and observable.

| Parameter | Type | Description |
|-----------|------|-------------|
| `psi` | np.quaternion | The quantum state |
| `observable` | np.quaternion | The observable (must be pure) |

**Returns:** Scalar in [-1, 1].

**Formula:** ⟨O⟩ = vec(ψ) · vec(O) / |vec(O)|

**Example:**
```python
psi = SPIN_X
exp_z = expectation_value(psi, SPIN_Z)  # = 0 (orthogonal)
exp_x = expectation_value(psi, SPIN_X)  # = 1 (aligned)
```

### `measure(psi, observable, seed=None) -> tuple[int, np.quaternion]`

Perform a single projective measurement.

| Parameter | Type | Description |
|-----------|------|-------------|
| `psi` | np.quaternion | State to measure |
| `observable` | np.quaternion | Measurement observable |
| `seed` | int or None | Random seed for reproducibility |

**Returns:** Tuple of (outcome, collapsed_state) where:
- `outcome`: +1 (spin up) or -1 (spin down)
- `collapsed_state`: Post-measurement state (eigenstate of observable)

**Probabilities:**
- P(+1) = (1 + ⟨O⟩) / 2
- P(-1) = (1 - ⟨O⟩) / 2

**Example:**
```python
psi = SPIN_X
outcome, psi_new = measure(psi, SPIN_Z, seed=42)
# outcome is +1 or -1 with 50% probability each
# psi_new is either SPIN_Z or -SPIN_Z
```

### `measure_batch(psi, observable, n, seed=None) -> np.ndarray`

Perform n measurements efficiently (vectorized).

| Parameter | Type | Description |
|-----------|------|-------------|
| `psi` | np.quaternion | State to measure |
| `observable` | np.quaternion | Measurement observable |
| `n` | int | Number of measurements |
| `seed` | int or None | Random seed |

**Returns:** Array of n outcomes (+1 or -1).

**Note:** Does not return collapsed states (more efficient for statistics).

**Example:**
```python
# Run 10000 trials for statistical analysis
outcomes = measure_batch(SPIN_X, SPIN_Z, n=10000, seed=123)
freq_up = np.mean(outcomes == 1)  # Should be ≈ 0.5
```

---

## Rotation Operations

Quaternion rotation for angle-dependent measurements (Sprint 2+).

### `create_rotation(theta, axis) -> np.quaternion`

Create a rotation quaternion using the half-angle formula.

| Parameter | Type | Description |
|-----------|------|-------------|
| `theta` | float | Rotation angle in radians |
| `axis` | list or ndarray | 3D unit vector for rotation axis |

**Returns:** Unit quaternion q = cos(θ/2) + sin(θ/2)·axis

**The Half-Angle:** The θ/2 reflects the SU(2) double-cover of SO(3). A 2π rotation gives q = -1, meaning the state acquires a sign flip. A full 4π rotation is needed to return to the original state.

**Example:**
```python
# Rotation by 90° about y-axis
q = create_rotation(np.pi/2, [0, 1, 0])
```

### `rotate_observable(observable, theta, axis) -> np.quaternion`

Rotate an observable by angle θ about an axis.

| Parameter | Type | Description |
|-----------|------|-------------|
| `observable` | np.quaternion | Observable to rotate (must be pure) |
| `theta` | float | Rotation angle in radians |
| `axis` | list or ndarray | Rotation axis |

**Returns:** Rotated observable O' = q·O·q⁻¹

**Example:**
```python
# Tilt measurement axis by 60° from z toward x
O_tilted = rotate_observable(SPIN_Z, np.pi/3, [0, 1, 0])
# Result: cos(60°)·k + sin(60°)·i
```

### `rotate_state(psi, theta, axis) -> np.quaternion`

Rotate a quantum state by angle θ about an axis.

| Parameter | Type | Description |
|-----------|------|-------------|
| `psi` | np.quaternion | State to rotate |
| `theta` | float | Rotation angle in radians |
| `axis` | list or ndarray | Rotation axis |

**Returns:** Rotated state ψ' = q·ψ·q⁻¹ (normalized pure quaternion).

### `create_tilted_state(theta) -> np.quaternion`

Create a spin state tilted from z-axis toward x-axis.

| Parameter | Type | Description |
|-----------|------|-------------|
| `theta` | float | Tilt angle in radians from z-axis |

**Returns:** ψ(θ) = sin(θ)·i + cos(θ)·k

**Physical meaning:**
- θ = 0 → spin along +z
- θ = π/2 → spin along +x
- θ = π → spin along -z

**Example:**
```python
# State at 45° from z
psi_45 = create_tilted_state(np.pi/4)

# Measure along z-axis
prob_up = (1 + expectation_value(psi_45, SPIN_Z)) / 2
# = (1 + cos(45°)) / 2 ≈ 0.854 = cos²(22.5°)
```

---

## Quick Reference: The Half-Angle Formula

For a spin state at angle θ from the measurement axis:

```
P(+) = cos²(θ/2)
P(-) = sin²(θ/2)
```

This arises naturally from:
1. Quaternion rotation: q = cos(θ/2) + sin(θ/2)·ĵ
2. Observable transformation: O_θ = q·k·q⁻¹ = cos(θ)·k + sin(θ)·î
3. Expectation value: ⟨O_θ⟩ = cos(θ)
4. Born rule: P(+) = (1 + cos θ)/2 = cos²(θ/2)

---

## Usage Example: Angle-Dependent Measurement

```python
from qphysics import SPIN_Z, rotate_observable, expectation_value, measure_batch
import numpy as np

# Prepare spin-z state
psi = SPIN_Z

# Measure at various angles from z-axis
for angle_deg in [0, 30, 45, 60, 90]:
    theta = np.radians(angle_deg)

    # Rotate the observable (measurement axis)
    O_theta = rotate_observable(SPIN_Z, theta, [0, 1, 0])

    # Compute expectation and predicted probability
    exp_val = expectation_value(psi, O_theta)
    p_theory = np.cos(theta/2)**2

    # Run simulation
    outcomes = measure_batch(psi, O_theta, n=10000)
    p_measured = np.mean(outcomes == 1)

    print(f"θ={angle_deg:3d}°: P(+) theory={p_theory:.4f}, measured={p_measured:.4f}")
```

Output:
```
θ=  0°: P(+) theory=1.0000, measured=1.0000
θ= 30°: P(+) theory=0.9330, measured=0.9312
θ= 45°: P(+) theory=0.8536, measured=0.8548
θ= 60°: P(+) theory=0.7500, measured=0.7489
θ= 90°: P(+) theory=0.5000, measured=0.4967
```
