# Unit Conventions for QBP Simulations

## Overview

QBP simulations use a **two-layer unit architecture**: BPM internals operate in natural units for numerical stability, while all outputs are converted to SI at the boundary. This is standard practice in production physics codes.

**Project convention: ℏ = c = 1** (standard HEP natural units, following Furey's algebraic realism framework). The speed of light `c` does not appear in the current non-relativistic BPM, but the convention is established now for forward compatibility with relativistic (galactic-scale) extensions.

`C_SI = 299_792_458 m/s` (exact, 2019 SI redefinition) is provided in `si_conversion.py` for SI recovery when relativistic terms are introduced.

**Evidence from established codebases:**

| Code | Domain | Internal Units | SI at Boundary? |
|------|--------|----------------|-----------------|
| MEEP | Electrodynamics | c=1 natural units | Yes — all output in SI |
| LAMMPS | Molecular Dynamics | Multiple unit systems | Yes — `units real` etc. |
| Quantum ESPRESSO | DFT | Rydberg atomic units | Yes — output in eV, Angstroms |

**Textbook references:**
- Agrawal, *Nonlinear Fiber Optics*, Ch. 2.4 — normalized BPM propagation
- Saleh & Teich, *Fundamentals of Photonics*, Ch. 5 — paraxial wave equation normalization

---

## Layer 1: BPM Natural Units <-> SI

### Internal Parameters

The BPM solver uses these natural-unit constants:

| Parameter | Symbol | Code Value | Purpose |
|-----------|--------|------------|---------|
| Reduced Planck constant | `hbar_code` | 1.0 | Sets action scale |
| Particle mass | `m_code` | 0.5 | Sets dispersion relation |
| Central wavenumber | `k0_code` | 20.0 | Sets unit-convention length scale |

These are **not** physical values — they define a convenient coordinate system where the split-step BPM propagator has well-conditioned numerics.

### K0_CODE vs BPM k0

`K0_CODE = 20.0` is a **unit-convention constant** that defines the meaning of "1 code length unit" in the SI conversion framework. It appears in the scale factor formula: `L₀ = K0_CODE × λ / (2π)`.

This is distinct from the BPM simulation parameter `k0` (e.g., `BPM_CONFIG.k0 = 30.0`), which controls the number of grid points per wavelength — a **resolution** parameter. The simulation `k0` can be tuned freely for numerical convergence without affecting the physical scale of the output, because SI conversion always uses `K0_CODE`.

### The v_z Structural Invariant

Both BPM split-step components (diffraction and potential) absorb the longitudinal velocity:

```
v_z_code = hbar_code * k0_code / m_code = 1.0 * 20.0 / 0.5 = 40.0
```

This is the Jacobian of the time-to-space propagation transformation. If this invariant breaks, the BPM violates unitarity. `V_Z_CODE` is defined as the **canonical single source of truth** in `src/simulation/si_conversion.py`.

### V_Z_CODE Derivation

The standard Schrödinger equation propagates in time:

```
iℏ ∂ψ/∂t = Ĥψ = [(-ℏ²/2m)∂²/∂x² + V(x)]ψ
```

The BPM propagates in z (space) instead of t (time). Using z = v_z × t:

```
∂/∂t = v_z × ∂/∂z
```

Substituting:

```
iℏ v_z ∂ψ/∂z = [(-ℏ²/2m)∂²/∂x² + V(x)]ψ
```

Dividing both sides by v_z:

```
iℏ ∂ψ/∂z = [(-ℏ²/2m v_z)∂²/∂x² + V(x)/v_z]ψ
```

Both the kinetic and potential terms absorb 1/v_z identically. In code units with ℏ=1, m=0.5, k0=20:

```
v_z_code = ℏ_code × k0_code / m_code = 1.0 × 20.0 / 0.5 = 40.0
```

This is why `convert_potential` multiplies by V_Z_CODE: the potential in the BPM has already been divided by v_z_code, so recovering the physical potential requires multiplying it back.

**Proven correct:** PR #323, verified by 3 independent tests in `tests/test_si_defining_constants.py`.

### Scale Factors {L_0, E_0, T_0}

Given a physical particle (mass `m_SI`, de Broglie wavelength `lambda_SI`):

```
L_0 = k0_code * lambda_SI / (2 * pi)     [m per code unit]
E_0 = hbar_SI^2 * m_code / (m_SI * L_0^2 * hbar_code^2)    [J per code unit]
T_0 = hbar_SI / E_0                       [s per code unit]
```

These are computed via `si_conversion.compute_scales(m_si, lambda_si)` which returns a `ScaleFactors` dataclass. **Never compute scale factors inline** — always use the library function.

### Conversion Functions

**Output (Code -> SI):**

| Function | Conversion | Output Units |
|----------|------------|-------------|
| `convert_position(x_code, scales)` | `x_code * L_0` | metres |
| `convert_potential(U_code, scales)` | `U_code * V_Z_CODE * E_0 / eV` | electron-volts |
| `convert_energy(E_code, scales)` | `E_code * E_0` | joules |

**Input (SI -> Code):**

| Function | Conversion | Input Units |
|----------|------------|------------|
| `convert_length_to_code(val_m, scales)` | `val_m / L_0` | metres |
| `convert_energy_to_code(val_J, scales)` | `val_J / E_0` | joules |

---

## Layer 2: Quaternionic Derived Quantities (MODEL-DEPENDENT)

The quaternionic algebra motivates two derived quantities:

| Quantity | Symbol | Formula | Units |
|----------|--------|---------|-------|
| Quaternionic beat length | `L_Q` | `pi * hbar_SI * v_g / U1` | metres |
| Quaternionic coupling parameter | `zeta` | `U1 / E_kin` | dimensionless |

### MODEL-DEPENDENT Status

These quantities are model-dependent predictions derived from the algebraic structure but have **NOT** been validated against peer-reviewed experiments. They are labeled `MODEL-DEPENDENT` in code and documentation.

**Requirements for promotion to established status:**
1. An experiment produces data where L_Q or zeta appears as a measurable quantity
2. The measurement is published in peer-reviewed literature
3. The result has been independently reproduced

Until all three conditions are met, these remain model-dependent predictions.

Computed via `si_conversion.compute_quaternionic_quantities(U1_si, E_kin_si, v_g_si)`.

---

## CSV Column Naming Convention

All output CSV columns use snake_case with unit suffixes:

| Column Name | Unit | Description |
|-------------|------|-------------|
| `x_position_m` | metres | Transverse position |
| `z_m` | metres | Propagation distance |
| `U1_strength_eV` | electron-volts | Quaternionic coupling strength |
| `intensity_total_normalized` | dimensionless | Normalized total intensity |
| `intensity_psi0_normalized` | dimensionless | Normalized psi0 intensity |
| `intensity_psi1_normalized` | dimensionless | Normalized psi1 intensity |
| `eta_fraction` | dimensionless | Quaternionic fraction |
| `visibility` | dimensionless | Fringe visibility |

**Why snake_case suffixes?**
- Preserves pandas dot-notation access: `df.x_position_m`
- Machine-readable: no brackets or spaces to escape
- Self-documenting: the unit is part of the column name

Use `si_conversion.annotate_columns(df, unit_map)` to apply suffixes programmatically.

---

## Metadata Sidecar

Each simulation run produces a `metadata_{timestamp}.json` alongside the CSV files:

```json
{
  "format_version": "2.0",
  "particle": "electron",
  "mass_kg": 9.10938e-31,
  "lambda_m": 5e-11,
  "L0_m": 1.591e-10,
  "E0_J": 2.412e-19,
  "T0_s": 4.378e-16,
  "V_Z_CODE": 40.0,
  "column_units": { ... }
}
```

This ensures any downstream consumer can trace the conversion back to physical parameters.

---

## Enforcement

### In Code

All SI conversions **must** use `src/simulation/si_conversion.py`. Inline or ad-hoc conversion code is a review failure. New conversion functions go into the library with tests, not into experiment scripts.

### In Issues

The experiment issue template includes a "Conversion Library Usage" Definition of Done gate (see `.github/ISSUE_TEMPLATE/experiment.yml`).

### In Reviews

The CONTRIBUTING.md review checklist includes a "Unit Consistency Verification" step. PRs that bypass the conversion library are flagged.

### In CI

`tests/test_output_schema.py` validates that simulation output has correct column names, SI magnitude ranges, and metadata.
