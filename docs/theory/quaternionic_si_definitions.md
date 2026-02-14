# Quaternionic SI Definitions

*Research deliverable for #319 | Sprint 3 PIVOT-S3-001 resolution*
*Status: REVISED DRAFT — incorporates Gemini Theory Team review*

---

## 1. Motivation

Sprint 3 Phase 3 revealed that the QBP simulation mixes unit systems:
- Analytical scenarios use SI (metres, joules)
- BPM simulation uses natural units (hbar=1, m=0.5)
- No defined mapping between them

This document establishes SI definitions for all quaternionic quantities, enabling consistent cross-scenario comparison. The definitions must be valid from Planck scale (~1.6e-35 m) to cosmological scale (~8.8e26 m) — a span of ~62 orders of magnitude.

---

## 2. KEY FINDING: BPM Code Has Absorbed v_z Factor

**This section was promoted from the original Section 5.2 per Theory Team review. It is the most important finding.**

### 2.1 The Issue

The BPM potential step (`wave_propagation.py`, lines 354-362) computes:

```python
phase = np.exp(-1j * U0 * dz / hbar)   # Line 354 — U0 phase rotation
theta = U1 * dz / hbar                  # Line 362 — U1 coupling angle
```

The BPM propagates in **space** (z), not time. The relationship between temporal and spatial Schrodinger evolution is:

```
Time domain:    theta_t = U * dt / hbar        [J]*[s]/[J*s] = dimensionless  ✓
Spatial domain: theta_z = U * dz / (hbar * v_z) [J]*[m]/([J*s]*[m/s]) = dimensionless  ✓
```

where `v_z = hbar * k0 / m` is the longitudinal group velocity.

**The code uses the time-domain formula for spatial propagation.** In SI dimensions:

```
theta_code = U * dz / hbar = [J] * [m] / [J*s] = [m/s]  ← NOT dimensionless
```

### 2.2 Two Valid Interpretations

**Option A — Code has a dimensional bug:** U0 and U1 should be divided by v_z. The code parameters are in energy units but the formula is wrong.

**Option B — Code parameters absorb v_z:** The code is correct if we redefine what U0_code and U1_code mean. They are NOT energies. They are **spatial coupling frequencies** with dimensions of 1/length:

```
U_code = U_phys / (hbar * v_z) = U_phys * m / (hbar^2 * k0)
```

In the code's natural units (hbar=1, m=0.5, k0=20):
```
U_code = U_phys / (1 * 1 * 20 / 0.5) = U_phys / 40
U_phys = U_code * 40  (in code energy units)
```

**We adopt Option B.** The code produces physically meaningful results — the theta values are effectively dimensionless in the code's natural unit system. But the parameter names are misleading: `U1_strength` is a spatial coupling frequency, not an energy.

### 2.3 Consequence: Two Distinct Quantities

| Symbol | Name | Dimensions | Code value (U1=10) | Meaning |
|--------|------|------------|---------------------|---------|
| U1_code | Spatial coupling frequency | L^(-1) | 10 | Rate of quaternionic rotation per unit propagation length |
| U1_phys | Physical coupling energy | Energy [J] | 400 (natural) | Energy in the quaternionic Hamiltonian |

The kinetic energy: `E_k = hbar^2 * k0^2 / (2m) = 1 * 400 / 1 = 400 (natural)`.
So U1_code = 10 gives U1_phys/E_k = 400/400 = 1.0 — the coupling energy equals the kinetic energy.

---

## 3. Scale Coverage: Planck to Cosmological

### 3.1 Design Requirement

The QBP theory investigates whether quantum mechanics has quaternionic structure at a fundamental level. If quaternionic effects exist, they operate at whatever scale the Hamiltonian acts. Our unit definitions must therefore be valid across all physically relevant scales.

### 3.2 Planck Units as Universal Anchor

Planck units set all fundamental constants to unity (hbar = c = G = k_B = 1):

| Planck Quantity | Symbol | SI Value |
|-----------------|--------|----------|
| Planck length | l_P | 1.616e-35 m |
| Planck time | t_P | 5.391e-44 s |
| Planck mass | m_P | 2.176e-8 kg |
| Planck energy | E_P | 1.956e9 J (1.22e28 eV) |
| Planck temperature | T_P | 1.417e32 K |

### 3.3 Scale Map

| Regime | Characteristic Length | Planck Lengths | SI (m) | Relevant Physics |
|--------|---------------------|----------------|--------|------------------|
| Planck | l_P | 1 | 1.6e-35 | Quantum gravity; QBP → QGP? |
| Nuclear | fm | ~6e19 | 1e-15 | Strong force; quark confinement |
| Atomic | Bohr radius | ~3e24 | 5.3e-11 | Electron orbitals; QBP double-slit |
| Molecular | nm | ~6e25 | 1e-9 | Chemistry; decoherence threshold |
| Mesoscopic | um | ~6e28 | 1e-6 | Optical double-slit (Young) |
| Human | m | ~6e34 | 1 | Laboratory apparatus |
| Planetary | Earth radius | ~4e41 | 6.4e6 | Gravitational decoherence |
| Stellar | AU | ~9e44 | 1.5e11 | Solar system dynamics |
| Galactic | kpc | ~2e54 | 1e20 | Large-scale structure |
| Cosmological | Observable universe | ~5e61 | 8.8e26 | Horizon-scale effects |

Total range: ~62 orders of magnitude in length.

### 3.4 Implications for QBP Definitions

All quaternionic quantities are defined in terms of SI base units (m, kg, s, J). The conversion formulas use only:
- Fundamental constants: hbar, c, G (when needed), k_B (when needed)
- Physical parameters: particle mass m, wavenumber k, potential energy U

**No formula in this document contains a hardcoded numerical scale.** The length scale L_0 is derived from the physical system being modeled, not assumed. This ensures the definitions remain valid whether:
- Modeling electron diffraction (L_0 ~ 0.16 nm)
- Modeling neutron interferometry (L_0 ~ 0.01 nm)
- Modeling Planck-scale thought experiments (L_0 ~ l_P)
- Modeling cosmological quaternionic effects (L_0 ~ Mpc, if applicable)

### 3.5 Numerical Representation

IEEE 754 double-precision floats span exponents ~1e-308 to ~1e+308 (~617 orders of magnitude), which comfortably covers the 62 orders needed. No special numerical types are required for scale coverage. The risk is in **relative precision** at extreme ratios — for example, computing U1_phys/E_Planck for a sub-eV coupling energy requires ~37 significant digits if done naively. In practice, all computations should be done in the natural scale of the experiment, converting to/from SI only at input/output boundaries.

---

## 4. Real Double-Slit Experiment (SI Reference)

Before defining quaternionic extensions, we anchor to measured reality.

### 4.1 Typical Apparatus Parameters

| Parameter | Symbol | Light (Young) | Electrons (Tonomura) | SI Unit |
|-----------|--------|---------------|----------------------|---------|
| Slit width | a | 20 um (2.0e-5 m) | 62 nm (6.2e-8 m) | m |
| Slit separation | d | 200 um (2.0e-4 m) | ~100 nm | m |
| Wavelength | lambda | 500 nm (5.0e-7 m) | 0.05 nm (5e-11 m) | m |
| Detector distance | L | 1.0 m | 1.5 m | m |
| Fringe spacing | dx | lambda*L/d = 2.5e-3 m | ~0.75 mm | m |

**Source:** https://en.wikipedia.org/wiki/Double-slit_experiment
**Ref:** Tonomura, A. et al. (1989). "Demonstration of single-electron buildup of an interference pattern." *Am. J. Phys.* 57(2), 117-120.

### 4.2 Standard QM Intensity Formula (SI)

The double-slit intensity pattern at detector position x (in metres):

```
I(x) = I_0 * cos^2(pi*d*x / (lambda*L)) * (sin(beta)/beta)^2
```

where:
- `I_0`: peak intensity [W/m^2]
- `beta = pi*a*x / (lambda*L)`: diffraction parameter [dimensionless]
- `d`: slit separation [m]
- `a`: slit width [m]
- `lambda`: de Broglie wavelength [m]
- `L`: detector distance [m]
- `x`: transverse position at detector [m]

### 4.3 Key Measurable Quantities (SI)

| Quantity | Formula | SI Unit |
|----------|---------|---------|
| Fringe spacing | dx = lambda*L/d | m |
| Visibility | V = (I_max - I_min)/(I_max + I_min) | dimensionless |
| Peak positions | x_m = m*lambda*L/d (m = 0, +/-1, ...) | m |
| Missing orders | when m*a/d = integer | dimensionless |

---

## 5. Quaternionic Quantity Definitions (SI)

### 5.1 The Coupled Schrodinger Equation

Starting from the quaternionic Schrodinger equation (Adler 1988, 1995):

```
ih_bar * d(psi)/dt = H * psi
```

With symplectic decomposition psi = psi_0 + psi_1*j and potential U = U_0 + U_1*j:

```
ih_bar * d(psi_0)/dt = [-h_bar^2/(2m) * nabla^2 + U_0] psi_0  -  U_1 * psi_1*
ih_bar * d(psi_1)/dt = [-h_bar^2/(2m) * nabla^2 + U_0] psi_1  +  U_1 * psi_0*
```

The sign asymmetry (-U_1 in first, +U_1 in second) arises from j^2 = -1.

### 5.2 SI Dimensions of Each Quantity

| Symbol | Name | SI Dimensions | SI Unit | Derivation |
|--------|------|---------------|---------|------------|
| psi_0 | Complex wavefunction | L^(-d/2) | m^(-1/2) (1D), m^(-3/2) (3D) | From integral(|psi|^2)dx = 1 |
| psi_1 | Quaternionic wavefunction | L^(-d/2) | m^(-1/2) (1D), m^(-3/2) (3D) | Same as psi_0 (components of same vector) |
| U_0 | Standard potential | Energy | J (joules) | Diagonal Hamiltonian term |
| U_1 | Quaternionic coupling energy | Energy | J (joules) | Off-diagonal Hamiltonian term (same dimensions as U_0) |
| eta_0 | Initial mixing ratio | Dimensionless | 1 | eta_0 = |psi_1|^2 / |psi_0|^2 |
| kappa | Quaternionic decay constant | L^(-1) | m^(-1) | kappa = |U_1| / (h_bar * v) |
| L_decay | Quaternionic coherence length | L | m | L_decay = 1/kappa = h_bar*v/|U_1| |

### 5.3 Dimensional Analysis Verification

**Coupling term:** U_1 * psi_1* must match ih_bar * d(psi)/dt = [J*s] * [1/s] * [m^(-d/2)] = [J] * [m^(-d/2)]
- U_1 * psi_1* = [J] * [m^(-d/2)] ✓

**Decay constant:** kappa = |U_1| / (h_bar * v) = [J] / ([J*s] * [m/s]) = [J] / [J*m] = [m^(-1)] ✓

**Coherence length:** L_decay = h_bar * v / |U_1| = [J*s] * [m/s] / [J] = [m] ✓

**Rotation angle (time domain):** theta_t = U_1 * dt / h_bar = [J] * [s] / [J*s] = dimensionless ✓

**Rotation angle (spatial domain):** theta_z = U_1 * dz / (h_bar * v_z) = [J] * [m] / ([J*s] * [m/s]) = dimensionless ✓

### 5.4 Why psi_0 and psi_1 Must Have Identical Dimensions

The total probability density is rho = |psi_0|^2 + |psi_1|^2. If psi_0 and psi_1 had different dimensions, this sum would be dimensionally invalid. Since integral(rho * dV) = 1 (dimensionless probability), both components must have dimensions of L^(-d/2).

This is a structural requirement of the symplectic decomposition: psi = psi_0 + psi_1*j is a single element of a quaternionic module, so its components must share dimensions.

---

## 6. Experimental Bounds on U_1 (SI)

| Experiment | Bound on |U_1| | SI (Joules) | Reference |
|------------|-----------------|-------------|-----------|
| Kaiser (1984) neutron interferometry | << 3e-11 eV | << 4.8e-30 J | Kaiser et al., Phys. Rev. A |
| Procopio (2017) photon test | < 2e-9 eV | < 3.2e-28 J | Procopio et al., Nature Comms |

**Physical interpretation (Feynman):** At the Procopio bound (|U_1| ~ 3.2e-28 J), an electron with lambda = 0.05 nm traversing a 1 m flight path accumulates a quaternionic rotation of:

```
theta = U_1 * L / (hbar * v_z)
      = 3.2e-28 * 1 / (1.055e-34 * 1.456e7)
      ≈ 0.21 radians
```

This is large enough to be detectable. The null result means either:
1. The real U_1 is much smaller than the bound, or
2. The quaternionic "charge" of electrons is zero for this interaction

---

## 7. BPM Code-to-SI Conversion

### 7.1 Current Code Units

The BPM simulation (wave_propagation.py) uses:

| Code Parameter | Value | Meaning |
|---------------|-------|---------|
| hbar | 1.0 | Reduced Planck constant |
| mass | 0.5 | Particle mass |
| k0 | 20.0 | Central wavenumber |
| dz | 0.05 | Propagation step |
| X_max | 20.0 | Half-domain width |
| Nx | 4096 | Grid points |

Derived: v_z = hbar * k0 / mass = 1 * 20 / 0.5 = **40** (code velocity units)

### 7.2 Conversion Framework

To convert code values to physical SI requires defining the **length scale** L_0 (what 1 code unit of length corresponds to in metres). L_0 is determined by the physical system:

```
L_0 = k0_code / k_SI = k0_code * lambda_SI / (2*pi)
```

From L_0, we derive three conversion factors:

```
Length:  x_SI = x_code * L_0
Energy:  E_0 = hbar_SI^2 / (m_SI * L_0^2)  * (1 / hbar_code^2) * m_code
Time:    T_0 = hbar_SI / E_0
```

**Potential conversion** (accounting for absorbed v_z from Section 2):

```
U_phys_SI = U_code * hbar_SI^2 * k0_code / (m_SI * L_0^2)
```

This is equivalent to: `U_phys_SI = U_code * v_z_code * E_0`.

### 7.3 Worked Example: Electrons (Tonomura Experiment)

Physical system: m_SI = 9.109e-31 kg, lambda = 0.05 nm = 5e-11 m

```
k_SI   = 2*pi/lambda = 1.257e11 m^(-1)
L_0    = 20 / 1.257e11 = 1.591e-10 m  (≈ 0.16 nm)

E_0    = (1.055e-34)^2 * 0.5 / (9.109e-31 * (1.591e-10)^2 * 1)
       = 5.563e-69 / 2.307e-50
       = 2.412e-19 J  (≈ 1.506 eV)

v_z_SI = hbar_SI * k_SI / m_SI = 1.456e7 m/s  (4.9% of c)
E_k_SI = hbar_SI^2 * k_SI^2 / (2*m_SI) = 9.647e-17 J  (≈ 602 eV)
```

**Potential conversion (corrected):**

```
U_phys_SI = U_code * hbar_SI^2 * 20 / (9.109e-31 * (1.591e-10)^2)
          = U_code * 9.648e-18 J
          = U_code * 60.3 eV
```

| U1_code | U1_phys (natural) | U1_phys (SI) | U1/E_k | vs Procopio (2e-9 eV) |
|---------|-------------------|--------------|--------|------------------------|
| 10 | 400 | 603 eV | 1.00 | 3e11 x above bound |
| 1 | 40 | 60.3 eV | 0.10 | 3e10 x above bound |
| 0.5 | 20 | 30.2 eV | 0.05 | 1.5e10 x above bound |
| 1e-5 | 4e-4 | 6.0e-4 eV | 1e-6 | 3e5 x above bound |
| 3.3e-11 | 1.3e-9 | 2.0e-9 eV | 3.3e-12 | AT bound |

**Key insight:** The simulation's U1_code range (0-10) corresponds to 0-603 eV in physical energy — **11 orders of magnitude above** the experimental bound. The previous draft incorrectly computed this as U1_code * 9.59e-9 eV (wrong by a factor of ~6.3e9 due to a missing L_0 in the conversion formula).

This is scientifically valid for a theoretical investigation of quaternionic mechanics, but must be clearly stated: the simulation explores a regime already experimentally excluded for electrons. It demonstrates the *mechanism* of quaternionic coupling, not a realistic parameter range.

---

## 8. Octonionic Extension (R -> C -> H -> O)

### 8.1 Dimensional Analysis Under Algebra Changes

Moving up the division algebra chain:
- R (reals): standard classical mechanics
- C (complex): standard quantum mechanics
- H (quaternions): quaternionic QM (current QBP)
- O (octonions): octonionic QM (if needed)

**The dimensional analysis is invariant under algebra changes.** Energy is defined by the Hamiltonian's relationship to time translation (E <-> d/dt). Regardless of the algebra, the "coupling potential" must have dimensions of energy to appear in the Hamiltonian.

### 8.2 Structural Changes

| Property | C | H | O |
|----------|---|---|---|
| Commutativity | Yes | No | No |
| Associativity | Yes | Yes | No |
| Tensor products | Standard | Non-trivial (Moretti-Oppio) | Broken |
| U_1 dimensions | Energy | Energy | Energy |

### 8.3 Non-Associativity Caveat for Octonions

**The loss of associativity at O is not merely algebraic — it breaks the standard Hilbert space formulation.** Specifically:
- The expression `(A * B) * psi ≠ A * (B * psi)` means operator composition is ambiguous
- Standard quantum mechanics requires an associative algebra of observables
- Octonionic QM would require an alternative formulation (e.g., exceptional Jordan algebras, J_3(O))

This does NOT change the dimensional analysis (energy is still energy), but it means the coupled Schrodinger equation (Section 5.1) cannot be directly extended to O by simple substitution of basis elements. A new mathematical framework would be required.

### 8.4 When Octonionic Extension Is Needed

Extend to octonions if:
1. The quaternionic model predicts phenomena that require non-associative operations (e.g., triple products of states)
2. The division algebra structure of the Standard Model (Furey's program: C tensor H tensor O) demands it for particle content
3. Specific experimental signatures are predicted that differ between H and O

**Current assessment:** Not needed for the double-slit experiment. The quaternionic extension (H) is sufficient for single-particle interference. Octonionic extension may be relevant for multi-particle entanglement experiments (future sprints).

---

## 9. Summary: SI Definitions Table

| Quantity | Symbol | SI Unit | Code Dimensions | Conversion |
|----------|--------|---------|-----------------|------------|
| Length | x | m | natural length | x_SI = x_code * L_0 |
| Slit width | a | m | natural length | a_SI = a_code * L_0 |
| Slit separation | d | m | natural length | d_SI = d_code * L_0 |
| Wavelength | lambda | m | natural length | lambda_SI = 2*pi*L_0/k0_code |
| Detector distance | L | m | natural length | L_SI = L_prop * L_0 |
| Standard potential | U_0 | J | 1/length (absorbed v_z) | U0_SI = U0_code * hbar_SI^2 * k0_code / (m_SI * L_0^2) |
| Quaternionic coupling | U_1 | J | 1/length (absorbed v_z) | U1_SI = U1_code * hbar_SI^2 * k0_code / (m_SI * L_0^2) |
| Mixing ratio | eta_0 | dimensionless | dimensionless | eta_0 (same) |
| Decay constant | kappa | m^(-1) | 1/length | kappa_SI = kappa_code / L_0 |
| Coherence length | L_decay | m | natural length | L_decay_SI = L_decay_code * L_0 |
| Visibility | V | dimensionless | dimensionless | V (same) |
| Probability density | |psi|^2 | m^(-d) | 1/length^d | rho_SI = rho_code / L_0^d |

### 9.1 Scale-Independent Conversion Protocol

The length scale L_0 is **not a constant** — it is determined by the physical system:

```
L_0 = k0_code * lambda_SI / (2*pi)
```

For any particle with de Broglie wavelength lambda_SI:

| Particle/System | lambda_SI | L_0 | Energy Scale E_0 |
|-----------------|-----------|-----|-------------------|
| Electron (Tonomura) | 5e-11 m | 1.59e-10 m | 1.51 eV |
| Neutron (Kaiser) | 1.8e-10 m | 5.73e-10 m | 0.025 eV (thermal) |
| Photon (Procopio, 810nm) | 8.1e-7 m | 2.58e-6 m | 1.53 eV |
| Planck-scale particle | 1.0e-34 m | 3.18e-34 m | ~E_Planck |

The formulas in this document work identically at every row — only L_0 changes. No hardcoded numerical scales.

---

## 10. Open Questions

1. **BPM code naming:** Should `U1_strength` be renamed to `kappa_coupling` (or similar) to reflect that it is a spatial frequency, not an energy? Or should the code be fixed to divide by v_z so that U1 can be entered in energy units? (See Section 2.)

2. **Physical length scale for Sprint 3:** Which experimental setup should define L_0 for the double-slit simulation? Electron diffraction (Tonomura, L_0 = 0.16 nm) is the natural choice for the current experiment.

3. **Multi-slit consistency:** When the slit region has both U_0 (barrier) and U_1 (coupling), are their relative magnitudes physically meaningful? Currently U_0 = 30 and U_1 = 0-10 (code units), both as spatial frequencies.

4. **Observable predictions (SI):** What specific measurement would distinguish QBP from standard QM? The visibility reduction DeltaV as a function of U_1 is the candidate:
   - "For electrons with E_k = 602 eV through [apparatus], QBP predicts V = X, QM predicts V = Y."
   - But at experimentally allowed U_1 (< 2e-9 eV), the effect is U1_phys/E_k ~ 3e-12, giving a visibility change of order ~10^(-24) — undetectable with current technology.

5. **Cosmological regime:** If quaternionic coupling exists at very low energy scales (e.g., dark energy ~ 2e-3 eV), would accumulated rotation over cosmological path lengths produce detectable effects? This requires L_0 >> laboratory scales.

---

## 11. References

1. Adler, S.L. (1988). "Scattering and decay theory for quaternionic quantum mechanics." *Phys. Rev. D* 37, 3654.
2. Adler, S.L. (1995). *Quaternionic Quantum Mechanics and Quantum Fields.* Oxford University Press.
3. Kaiser, R. et al. (1984). Neutron interferometric bounds on quaternionic quantum mechanics.
4. Procopio, L.M. et al. (2017). "Single-photon test of hyper-complex quantum theories using a metamaterial." *Nature Communications* 8, 15044.
5. Tonomura, A. et al. (1989). "Demonstration of single-electron buildup of an interference pattern." *Am. J. Phys.* 57(2), 117-120.
6. Furey, C. (2016). "Standard model physics from an algebra?" PhD thesis, University of Waterloo.
7. Double-slit experiment. Wikipedia. https://en.wikipedia.org/wiki/Double-slit_experiment
8. NIST. "Planck units." https://physics.nist.gov/cuu/Constants/
