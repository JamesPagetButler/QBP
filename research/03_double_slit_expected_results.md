# Experiment 03: Double-Slit — Expected Results (Ground Truth)

**Sprint 3 | Phase 1: Ground Truth**
**Last updated:** 2026-02-12 (Option B: full quaternionic dynamics with Adler decay)

This document defines the quantitative predictions for the double-slit interference experiment using the QBP formalism. Unlike a pure C(1,i) reformulation exercise, Sprint 3 initializes wavefunctions with quaternionic j,k components and tests Adler's prediction that these components decay exponentially during propagation. The interference pattern at the detector must still match standard QM.

## 1. Experimental Setup

| Parameter | Symbol | Description |
|-----------|--------|-------------|
| Slit separation | d | Distance between slit centers |
| Slit width | a | Width of each slit (a << d for point-source approximation) |
| Screen distance | L | Distance from slits to detector screen (L >> d) |
| Wavelength | λ | de Broglie wavelength λ = h/p |
| Wave number | k | k = 2π/λ |
| Screen position | x | Position on detector screen (x=0 at center) |
| Quaternionic coupling | U₁ | Strength of quaternionic potential at slits (real-valued, free parameter, localized to slit region) |

**Conditions:**
- **Scenario A:** No which-path information (interference), complex initial state
- **Scenario B:** Which-path detection (no interference)
- **Scenario C:** No which-path information, quaternionic initial state (j,k components present)

Scenario C is the genuinely new QBP test. Scenarios A and B establish the baseline.

## 2. Empirical Anchor

**Data type:** Quantitative-moderate (fringe spacing, visibility) + Constraint-based (quaternionic deviations)

### Key Measured Values

| Quantity | Measured Value | Uncertainty | Source | Year | DOI / Identifier |
|----------|---------------|-------------|--------|------|------------------|
| Double-slit interference pattern | Fringes observed at single-electron level | Qualitative (buildup confirms wave behavior) | Tonomura, A. et al. | 1989 | Am. J. Phys. 57, 117 |
| Fringe spacing | Δx = λL/d confirmed for electrons | ~1% (apparatus-dependent) | Jönsson, C. | 1961 | Z. Phys. 161, 454 |
| Quaternionic phase deviation | < 1:30,000 of complex phase | Upper bound (null result) | Kaiser, H., George, E.A. & Werner, S.A. | 1984 | Phys. Rev. A 29, 2276 |
| Quaternionic phase angle | θ = 0.03° ± 0.13° | Consistent with zero | Procopio, L.M. et al. | 2017 | Nat. Commun. 8, 15044 |

### Experimental Confidence

| Factor | Assessment |
|--------|------------|
| Replication status | Standard double-slit: replicated thousands of times with electrons, neutrons, photons, even molecules. Quaternionic null results: two independent experiments (Kaiser 1984, Procopio 2017) using different particles and techniques. |
| Measurement precision | Fringe positions: ~1% for electron experiments. Quaternionic bounds: extremely precise null results (1:30,000 for neutrons, sub-degree for photons). |
| Relevance to QBP test | Direct — Scenarios A/B test standard interference; Scenario C tests whether quaternionic deviations exist within the experimental bounds. |

### What "Matching Reality" Means

For this experiment, "matching reality" has two components:

**Standard QM baseline (Scenarios A & B):** The simulation must reproduce the textbook double-slit interference pattern — fringe spacing Δx = λL/d, visibility V ≈ 1.0 for coherent sources, V ≈ 0 with which-path detection. These results have been replicated in laboratories worldwide since Jönsson (1961) and most famously demonstrated at the single-particle level by Tonomura et al. (1989). Matching means: fringe positions within 1% of predicted values, intensity pattern fitting cos²(πxd/λL) with R² > 0.99.

**Quaternionic dynamics (Scenario C):** The Adler decay prediction — that j,k components decay exponentially during spatial propagation — has not been directly measured. However, the null results of Kaiser et al. (1984) and Procopio et al. (2017) set stringent upper bounds on observable quaternionic effects. "Matching reality" here means: (1) the far-field interference pattern must be indistinguishable from the standard QM result (within the Kaiser/Procopio bounds), and (2) the decay dynamics must be consistent with Adler's (1988, 1995) theoretical framework. The simulation explores what happens *between* source and detector, where no experimental data currently exists.

### Null Results and Constraints

| Constraint | Bound | Source | Year | DOI / Identifier |
|-----------|-------|--------|------|------------------|
| Quaternionic phase in neutron interferometry | < 1:30,000 of complex phase | Kaiser, H., George, E.A. & Werner, S.A. | 1984 | Phys. Rev. A 29, 2276 |
| Quaternionic phase angle in single-photon test | θ = 0.03° ± 0.13° (consistent with zero) | Procopio, L.M. et al. | 2017 | Nat. Commun. 8, 15044 |

**Parameter-space mapping:** These null results constrain the quaternionic coupling U₁:
- **Kaiser bound:** A phase deviation < 1:30,000 over a neutron interferometer path length (~cm scale) implies |U₁| << ℏv/L_path, where v is the neutron velocity. For thermal neutrons (v ≈ 2200 m/s, L_path ≈ 0.05 m): |U₁| << ℏ × 2200 / 0.05 ≈ 5 × 10⁻³⁰ J ≈ 3 × 10⁻¹¹ eV.
- **Procopio bound:** θ = 0.03° ± 0.13° is consistent with zero quaternionic phase at optical wavelengths, giving a comparable or tighter bound.

Our simulation treats U₁ as a free parameter scanned over a range that includes values both within and far above these experimental bounds. The simulation must show: (1) for U₁ within the Kaiser/Procopio bounds, the far-field pattern is indistinguishable from standard QM; (2) for artificially large U₁, the decay dynamics are qualitatively visible and follow the predicted form.

## 3. QBP Formalism: Full Quaternionic Approach

### 3.1 Why Full Quaternions, Not Just C(1,i)

Pre-Sprint Research (#249-#253) identified the complex subspace C(1,i) as a safe restriction where QBP trivially reproduces standard QM. However, restricting to C(1,i) from the start tests nothing quaternionic — it is standard QM in quaternionic notation.

**Sprint 3 adopts Option B:** Start with genuine quaternionic states and observe the dynamics.

The scientific question is not "does QBP reproduce standard QM?" (Moretti-Oppio already guarantees this for elementary systems) but rather: **what happens to quaternionic structure during spatial propagation through a double slit?**

Adler (1995) predicts that j,k components exhibit exponential spatial decay. Sprint 3 tests this prediction directly.

### 3.2 Symplectic Decomposition

Following Adler (1995) and Davies & McKellar (1989), a quaternionic wavefunction is decomposed as:

```
ψ(x) = ψ₀(x) + ψ₁(x)·j
```

where ψ₀(x) and ψ₁(x) are complex-valued functions (living in C(1,i)).

- **ψ₀(x):** The complex component — carries the standard QM content
- **ψ₁(x):** The quaternionic component — carries the j,k content

The full quaternionic expansion is:
```
ψ(x) = α₀(x)·1 + β₀(x)·i + α₁(x)·j + β₁(x)·k
```

where ψ₀ = α₀ + β₀·i and ψ₁ = α₁ + β₁·i.

### 3.3 Derivation: QBP Axioms → Coupled Equations

This subsection derives the working equations from QBP's axiomatic framework, rather than simply citing Adler.

**Step 1: Quaternionic Schrödinger Equation**

The QBP framework extends standard QM by allowing the wavefunction and potential to be quaternion-valued. The time evolution is governed by the quaternionic Schrödinger equation (Adler 1995, Ch. 2):

```
iℏ ∂ψ/∂t = Hψ = -(ℏ²/2m)∇²ψ + Uψ
```

where ψ(x,t) is a quaternion-valued wavefunction and U(x) is a quaternion-valued potential. Note that i (the imaginary unit in the Schrödinger equation) acts by **left multiplication** — this is a convention choice that determines the complex subspace C(1,i).

**Step 2: Decompose the potential**

The quaternionic potential is decomposed as:

```
U(x) = U₀(x) + U₁(x)·j
```

where U₀(x) ∈ C(1,i) is the standard complex potential (barrier walls, slit geometry) and U₁(x) ∈ C(1,i) is the quaternionic coupling strength. For the double-slit experiment, U₁(x) is nonzero only in the slit region — it is the genuinely new physics.

**Step 3: Substitute the symplectic decomposition**

Insert ψ = ψ₀ + ψ₁·j and U = U₀ + U₁·j into Hψ = -(ℏ²/2m)∇²ψ + Uψ:

```
Uψ = (U₀ + U₁·j)(ψ₀ + ψ₁·j)
    = U₀·ψ₀ + U₀·ψ₁·j + U₁·j·ψ₀ + U₁·j·ψ₁·j
```

The critical step uses the quaternion algebra identities j·z = z*·j for any z ∈ C(1,i), and j·j = -1:

```
U₁·j·ψ₀ = U₁·ψ₀*·j
U₁·j·ψ₁·j = U₁·ψ₁*·j·j = -U₁·ψ₁*
```

Therefore:

```
Uψ = (U₀·ψ₀ - U₁·ψ₁*) + (U₀·ψ₁ + U₁·ψ₀*)·j
```

**Step 4: Separate complex and quaternionic parts**

Since i(ψ₀ + ψ₁·j) = iψ₀ + iψ₁·j (left multiplication by i commutes with j on the right), the LHS separates cleanly. Matching the 1-part and j-part on both sides:

```
iℏ ∂ψ₀/∂t = -(ℏ²/2m)∇²ψ₀ + U₀·ψ₀ - U₁·ψ₁*
iℏ ∂ψ₁/∂t = -(ℏ²/2m)∇²ψ₁ + U₀·ψ₁ + U₁·ψ₀*
```

These are two coupled complex Schrödinger equations (Adler 1988, Eqs. 42-43; Davies & McKellar 1989, Eq. 7).

**Key features:**
- U₀ is the standard complex potential (barrier walls, slit geometry)
- U₁ is the quaternionic potential coupling (free parameter, localized at slits)
- The asterisk denotes complex conjugation — arising from j·z = z*·j
- The coupling terms -U₁·ψ₁\* and +U₁·ψ₀\* mix the complex and quaternionic sectors
- The sign asymmetry (-U₁ in the first equation, +U₁ in the second) follows from j² = -1
- When U₁ = 0, the equations decouple into two independent standard Schrödinger equations

### 3.4 Born Rule (Full Quaternionic)

The probability density uses the full quaternionic norm:

```
P(x) = |ψ(x)|² = |ψ₀(x)|² + |ψ₁(x)|²
     = α₀(x)² + β₀(x)² + α₁(x)² + β₁(x)²
```

This is equivalent to the standard quaternionic inner product: P(x) = Re(ψ̄(x)·ψ(x)) where ψ̄ is the quaternionic conjugate. The cross-terms between ψ₀ and ψ₁ vanish because they live in orthogonal quaternionic subspaces (the 1,i and j,k planes). This reduces to the standard Born rule when ψ₁ = 0.

## 4. Quantitative Predictions

### 4.1 Scenario A: Complex Baseline (No Which-Path, No j,k)

This scenario uses ψ₁ = 0 throughout, serving as the baseline that must match standard QM exactly.

Each slit acts as a point source:

```
ψ₁ˢˡⁱᵗ(x) = A · exp(ikr₁),   ψ₂ˢˡⁱᵗ(x) = A · exp(ikr₂)
```

Total wavefunction (superposition):
```
ψ₀(x) = A · [exp(ikr₁) + exp(ikr₂)]
ψ₁(x) = 0
```

**Intensity pattern:**

```
I(x) = |ψ₀(x)|² = 2A² · [1 + cos(k(r₁ - r₂))]
```

**Far-field approximation** (L >> d, r₁ - r₂ ≈ xd/L):

```
I(x) = 4A² · cos²(πxd / λL)
```

**Fringe spacing:** Δx = λL / d

**Maxima:** x_n = nλL/d, n = 0, ±1, ±2, ...

**Minima:** x_n = (n + 1/2)λL/d

### 4.2 Scenario B: With Which-Path Detection (No Interference)

Measurement at the slits collapses the superposition. The intensity is the incoherent sum of single-slit patterns:

```
I(x) = (1/2)|ψ₁ˢˡⁱᵗ(x)|² + (1/2)|ψ₂ˢˡⁱᵗ(x)|²
```

For point sources: I(x) = A² (uniform, no fringes).

For finite slit width a:
```
I(x) = A² · sinc²(πxa / λL)
```

The interference cross-term vanishes because the paths are distinguishable.

### 4.3 Scenario C: Quaternionic Dynamics (The New QBP Test)

**This is the genuinely quaternionic scenario.** Initialize the wavefunction with nonzero j,k components and observe what happens during propagation.

#### 4.3.1 Initial State

At the source (before the slits), the electron has a quaternionic wavefunction:

```
ψ(x, t=0) = ψ₀(x, 0) + ψ₁(x, 0)·j
```

where ψ₁(x, 0) ≠ 0. The initial quaternionic fraction is parameterized by:

```
η = ∫|ψ₁|² dx / ∫|ψ|² dx
```

where η ∈ (0, 1) controls how "quaternionic" the initial state is. We test η = 0.01, 0.1, 0.5.

#### 4.3.2 Two Propagation Regimes

The physics of Scenario C involves two distinct regimes with different dynamics:

**Regime 1: Slit region (U₁ ≠ 0)**

In the slit region, the quaternionic potential U₁ is nonzero. The full coupled equations (§3.3) are active:

```
iℏ ∂ψ₀/∂t = -(ℏ²/2m)∇²ψ₀ + U₀·ψ₀ - U₁·ψ₁*
iℏ ∂ψ₁/∂t = -(ℏ²/2m)∇²ψ₁ + U₀·ψ₁ + U₁·ψ₀*
```

The coupling terms mix the ψ₀ and ψ₁ sectors. When an incoming quaternionic wavefunction (with nonzero ψ₁) encounters the slit potential, the interaction acts as a boundary condition that projects the transmitted wave into the eigenmodes of the post-slit free-space Hamiltonian.

For ψ₀, the standard complex component, the eigenmodes are propagating plane waves with real wavevector k = √(2mE)/ℏ.

For ψ₁, the quaternionic component, the situation is different. The coupling term U₁·ψ₀* in the slit region generates ψ₁ components whose energy-momentum relation is modified by the interaction. When these components are projected onto the free-space basis (regime 2), they include evanescent modes — solutions with imaginary wavevector that decay exponentially beyond the slit region.

This is analogous to quantum tunneling: a particle encountering a potential barrier acquires evanescent components in the classically forbidden region. Here, the quaternionic potential at the slits creates "quaternionically forbidden" modes in ψ₁ that decay beyond the interaction region.

**Regime 2: Free space (U₁ = 0)**

Beyond the slits, U₁ = 0 and the coupled equations decouple:

```
iℏ ∂ψ₀/∂t = -(ℏ²/2m)∇²ψ₀    [standard free-particle SE]
iℏ ∂ψ₁/∂t = -(ℏ²/2m)∇²ψ₁    [identical equation]
```

**Both components satisfy the same Schrödinger equation.** In free space, there is no mechanism that selects one component for decay over the other. The dynamics are symmetric.

However, the *solutions* differ because the *boundary conditions* set by the slit interaction (regime 1) are different for each component:
- **ψ₀** exits the slits in propagating modes (real wavevector) → carries the standard interference pattern to the detector
- **ψ₁** exits the slits predominantly in evanescent modes (imaginary wavevector) → decays exponentially with distance from the slits

**The decay is not caused by free-space propagation.** It is caused by the slit interaction projecting ψ₁ into evanescent modes. Free space merely preserves this evanescent character.

**Important consequence:** In the limit U₁ → 0, there is no coupling at the slits, no evanescent projection, and ψ₁ propagates normally alongside ψ₀. This is acceptance criterion #11 and serves as a control test.

#### 4.3.3 Decay Length Estimate

The decay of the evanescent ψ₁ modes beyond the slit region is characterized by a decay constant κ that depends on the slit interaction strength and particle energy.

**Derivation sketch** (following Adler 1988, §IV; see also Davies & McKellar 1989, §3):

In the slit region, the coupled system has eigenmodes with modified dispersion relations. For a particle with energy E incident on a quaternionic potential of strength U₁, the ψ₁ transmission coefficient includes evanescent contributions with:

```
κ = Im(k₁)
```

where k₁ is the complex wavevector of ψ₁ in the slit region. From the modified dispersion relation (Adler 1988, Eq. 48):

```
ℏ²k₁²/2m = E - U₀ ± i|U₁|
```

The imaginary part of U₁ gives an imaginary contribution to k₁². For |U₁| << E:

```
κ ≈ m|U₁| / (ℏ²k)  where k = √(2mE)/ℏ
```

This can be rewritten as:

```
κ ≈ |U₁| / (ℏv)  where v = ℏk/m is the particle velocity
```

**Decay length:** L_decay = 1/κ = ℏv/|U₁|

Physical interpretation: faster particles (larger v) have longer decay lengths — the evanescent ψ₁ components persist farther from the slits. This is intuitive: a higher-energy particle spends less time in the slit interaction region, so the evanescent projection is weaker.

The quaternionic fraction at distance r beyond the slits scales as:

```
η(r) ≈ η_slit · exp(-2κr)
```

where η_slit is the quaternionic fraction immediately after the slit interaction (set by U₁ and the slit geometry).

For any physical U₁ consistent with the Kaiser/Procopio bounds and macroscopic propagation distance L >> L_decay, the decay is complete: η(L) ≈ 0.

#### 4.3.4 Predicted Interference Pattern (Scenario C)

At the detector screen (distance L from slits):

1. **ψ₀ component** produces the standard interference pattern: I₀(x) = 4A₀² · cos²(πxd/λL)
2. **ψ₁ component** has decayed exponentially: |ψ₁(x)|² ≈ 0 at the detector (for L >> L_decay)
3. **Total intensity** converges to the standard pattern: I(x) → I₀(x)

The full two-slit expression decomposes as (cf. §3.4 Born rule):

```
P(x) = |ψ₀,slit1(x) + ψ₀,slit2(x)|² + |ψ₁,slit1(x) + ψ₁,slit2(x)|²
```

where subscripts denote (component, slit). There are no cross-terms between ψ₀ and ψ₁ because they live in orthogonal quaternionic subspaces. Near the slits, the ψ₁ interference term adds an incoherent background that reduces fringe visibility. At the detector (after ψ₁ decay), only the ψ₀ term contributes and visibility approaches 1.0.

**The complex subspace C(1,i) is dynamically selected** — not by fiat, but by the slit interaction boundary conditions. This is the central prediction of Scenario C.

#### 4.3.5 What Sprint 3 Actually Tests

The scientifically interesting measurements are not at the detector (where everything matches standard QM), but **during propagation**:

1. **Decay curve:** Plot η(r) = |ψ₁|²/|ψ|² as a function of distance from slits. Should follow exp(-2κr).
2. **Component-wise intensity:** Plot each component (α₀², β₀², α₁², β₁²) vs position. The j,k components should visibly decay while the 1,i components carry the interference pattern.
3. **Convergence:** At what distance does the interference pattern become indistinguishable from standard QM? This defines the "quaternionic coherence length."
4. **Parameter dependence:** How does the decay rate depend on η_slit, U₁, and particle energy?

**Note on measurement feasibility:** These are *simulation* measurements — the simulation has direct access to the four quaternionic components (α₀, β₀, α₁, β₁) at every grid point. A real experiment cannot measure component-wise intensities mid-flight without introducing a measurement interaction that would disturb the state. The simulation serves as a theoretical laboratory that probes dynamics inaccessible to current experimental techniques. The experimentally observable prediction remains the far-field interference pattern at the detector.

### 4.4 Single-Slit Envelope (Finite Slit Width)

For finite slit width a, all scenarios are modulated by the single-slit diffraction envelope:

```
I(x) → I(x) · sinc²(πxa / λL)
```

The envelope has zeros at x = nλL/a.

## 5. Simulation Parameters

### 5.1 Default Configuration

| Parameter | Value | Rationale |
|-----------|-------|-----------|
| d | 1.0 μm | Typical electron double-slit |
| a | 0.1 μm | a << d (point-source approximation valid) |
| L | 1.0 m | Far-field condition L >> d |
| λ | 0.05 nm | Electron de Broglie wavelength |
| k | 1.257 × 10¹¹ m⁻¹ | k = 2π/λ |
| Δx | 50 μm | Predicted fringe spacing = λL/d |

### 5.2 Quaternionic Parameters (Scenario C)

| Parameter | Values to Test | Description |
|-----------|---------------|-------------|
| η₀ | 0.01, 0.1, 0.5 | Initial quaternionic fraction |
| U₁ | Scan: 0, 10⁻¹⁵, 10⁻¹², 10⁻⁹, 10⁻⁶, 10⁻³ eV | Quaternionic potential strength (0 = control; 10⁻¹² eV ≈ Kaiser bound) |
| N_grid | 1000+ | Spatial grid points for propagation |

**Note on U₁:** The quaternionic potential strength is unknown experimentally. Experimental upper bounds (Kaiser 1984 neutron interferometry: 1:30,000; Procopio 2017 photon: θ = 0.03°) constrain it to be extremely small. In simulation, we treat U₁ as a free parameter and show that the physics (decay → standard QM convergence) is qualitatively the same for any U₁ > 0.

### 5.3 Parameter Sensitivity Tests

| Test | Variation | Expected Effect |
|------|-----------|-----------------|
| Double λ | λ → 2λ | Δx → 2Δx (fringe spacing) |
| Double L | L → 2L | Δx → 2Δx |
| Double d | d → 2d | Δx → Δx/2 |
| Double η₀ | η₀ → 2η₀ | Decay curve shifts up but same κ |
| Increase U₁ | U₁ → 10·U₁ | Faster decay (larger κ) |

## 6. Success Criteria

### 6.1 Quantitative Acceptance Criteria

**Baseline (Scenarios A & B):**

| # | Criterion | Tolerance |
|---|-----------|-----------|
| 1 | Scenario A fringe maxima at x_n = nλL/d | Within 1% of predicted positions |
| 2 | Scenario A intensity follows cos²(πxd/λL) | R² > 0.99 vs analytical curve |
| 3 | Scenario A fringe spacing matches λL/d | Within 1% |
| 4 | Scenario B shows no fringes | Visibility V < 0.01 |
| 5 | Fringe visibility V ≈ 1.0 for Scenario A (point sources) | V > 0.95 |
| 6 | Parameter sensitivity: Δx scales correctly with λ, L, d | Within 1% |

**Quaternionic dynamics (Scenario C):**

| # | Criterion | Tolerance |
|---|-----------|-----------|
| 7 | ψ₁ components decay exponentially with distance | R² > 0.95 vs exp(-2κr) fit |
| 8 | Decay rate κ increases with U₁ | Monotonic relationship verified |
| 9 | At detector, Scenario C matches Scenario A | Difference < 10⁻⁴ |
| 10 | Total probability conserved throughout propagation | |ψ₀|² + |ψ₁|² constant to < 10⁻⁶ |
| 11 | In limit U₁ → 0, ψ₁ propagates without decay (no coupling) | Control test |

### 6.2 Fringe Visibility

```
V = (I_max - I_min) / (I_max + I_min)
```

- Scenario A: V = 1.0 (complex baseline)
- Scenario B: V = 0.0 (which-path)
- Scenario C at detector: V → 1.0 (after j,k decay)
- Scenario C near slits: V < 1.0 (j,k components add incoherent background)

## 7. Falsification Criteria

### 7.1 Baseline Falsification (Must Match Standard QM)

| Scenario | QBP Prediction | Standard QM | Match Required? |
|----------|---------------|-------------|-----------------|
| A: No which-path | cos²(πxd/λL) fringes | cos²(πxd/λL) fringes | **MUST match** |
| B: With which-path | No fringes | No fringes | **MUST match** |
| C: At detector | Same as Scenario A | cos²(πxd/λL) fringes | **MUST match** |

If QBP predicts different interference patterns at the detector than standard QM, this would **falsify QBP**.

**Primary falsification test:** If Scenario C produces an interference pattern at the detector that deviates from Scenario A by more than the tolerance in acceptance criterion #9 (difference > 10⁻⁴), QBP's claim that C(1,i) is dynamically selected is falsified.

### 7.2 Quaternionic Dynamics Falsification

| Prediction | Expected | Would Falsify If... |
|-----------|----------|-------------------|
| j,k decay | Exponential with distance | Non-exponential, or growth |
| Probability conservation | |ψ|² = const | Total probability changes |
| U₁ → 0 limit | No decay (standard QM) | Decay without coupling |
| Convergence | Detector matches standard QM | Persistent j,k contribution at detector |

### 7.3 Null Hypothesis Value

If all predictions hold (expected), Sprint 3 confirms:
1. Quaternionic dynamics reduce to standard QM at macroscopic distances (Adler's decay)
2. The complex subspace C(1,i) is dynamically selected, not imposed by hand
3. The reduction is smooth and parameterized by (U₁, distance)
4. Single-particle spatial interference is not where QQM diverges from standard QM
5. The true divergence test remains multi-particle entanglement (Sprint 6: Bell's Theorem)

## 8. What This Experiment Does NOT Test

1. **The value of U₁** — We treat it as a free parameter. Determining U₁ from experiment requires specialized apparatus (neutron interferometry, photon tests).
2. **Multi-particle entanglement** — The tensor product problem (#249) means QQM may diverge from standard QM for entangled states. This is Sprint 6.
3. **Spin-path coupling** — Where quaternionic structure naturally appears in internal degrees of freedom. Candidate for Sprint 3 extension or future sprint.
4. **Relativistic effects** — Adler (1988) shows quaternionic effects may persist in the relativistic (Klein-Gordon) case. Our simulation is non-relativistic.

## 9. Implementation Notes for Phase 2

### 9.1 Two-Layer Simulation Architecture

The simulation has two layers:

**Layer 1: Complex baseline** (validates infrastructure)
- Standard complex wavefunctions: ψ₀(x) only, ψ₁ = 0
- Must exactly reproduce textbook double-slit
- Uses `create_state(α₀, β₀, 0, 0)` from qphysics.py

**Layer 2: Quaternionic propagation** (tests Adler's decay)
- Full quaternionic wavefunctions: ψ₀(x) + ψ₁(x)·j
- Propagate via coupled Schrödinger equations (§3.3, Step 4)
- Track all four components (α₀, β₀, α₁, β₁) at each grid point

**Note on normalization:** Position-space wavefunctions satisfy ∫|ψ(x)|²dx = 1 over the spatial grid. This differs from the unit-quaternion normalization in qphysics.py (|ψ|² = 1 at a point). Phase 2 will need per-grid-point unnormalized quaternions with the overall wavefunction normalized.

### 9.2 Propagation Method

For 1D spatial propagation (sufficient for far-field double-slit):

1. Discretize x on a grid with spacing δx
2. Use split-step Fourier method or Crank-Nicolson for time evolution
3. At each time step, evolve ψ₀ and ψ₁ according to coupled equations
4. In free space (U₁ = 0), equations decouple — propagate independently
5. In the slit region (if modeling U₁ ≠ 0), use the full coupled system

### 9.3 Measurement in QBP (Scenario B)

For which-path detection:
1. Measurement at the slits projects the quaternionic state onto a slit eigenstate
2. Both ψ₀ and ψ₁ components collapse for the measured slit
3. After measurement, propagate only the single-slit state
4. The j,k components of the single-slit state still decay during propagation to the detector

### 9.4 Visualization (Phase 3)

Sprint 3 Phase 3 should implement:
- **Component-wise decay plot** (HIGH PRIORITY): α₀², β₀², α₁², β₁² vs distance from slits. Blue for 1,i components, red/orange for j,k. This directly visualizes Adler's decay.
- **Convergence plot:** Difference between Scenario C and Scenario A intensity patterns as a function of propagation distance
- **Fringe visibility vs distance:** V(r) showing how visibility increases from V < 1 (near slits, j,k background) to V → 1 (at detector, after decay)
- **Parameter exploration:** Interactive slider for η₀ showing effect on decay dynamics

## 10. Proof-of-Concept: Free-Space Quaternionic Propagation

Before implementing the full double-slit simulation, Phase 2 should first build a minimal proof-of-concept:

1. Initialize a quaternionic Gaussian wavepacket with η₀ = 0.1
2. Propagate in free space (no slits, no potential)
3. Verify: ψ₀ spreads as a standard Gaussian, ψ₁ remains (no coupling in free space)
4. Add a simple quaternionic barrier (U₁ ≠ 0 in a finite region)
5. Verify: ψ₁ is generated/modified by the barrier, then decays beyond it
6. Measure decay rate and compare with theoretical κ

This proof-of-concept validates the propagation infrastructure before the full double-slit geometry.

## 11. References

1. **Adler, S.L.** (1988). "Scattering and decay theory for quaternionic quantum mechanics." *Phys. Rev. D* 37, 3654.
2. **Adler, S.L.** (1995). *Quaternionic Quantum Mechanics and Quantum Fields*. Oxford University Press.
3. **Davies, A.J. & McKellar, B.H.J.** (1989). "Nonrelativistic quaternionic quantum mechanics in one dimension." *Phys. Rev. A* 40, 4209.
4. **De Leo, S. & Ducati, G.** (2012). "Quaternionic potentials in non-relativistic quantum mechanics." arXiv:1012.4613.
5. **Moretti, V. & Oppio, M.** (2017). "Quantum theory in quaternionic Hilbert space." arXiv:1709.09246.
6. **Kaiser, H., George, E.A. & Werner, S.A.** (1984). "Neutron interferometric search for quaternions in quantum mechanics." *Phys. Rev. A* 29, 2276.
7. **Procopio, L.M. et al.** (2017). "Single-photon test of hyper-complex quantum theories using a metamaterial." *Nature Communications* 8, 15044.
8. **Tonomura, A. et al.** (1989). "Demonstration of single-electron buildup of an interference pattern." *Am. J. Phys.* 57, 117.

---

**Review tier:** Tier 3 (theory-critical)

**Knowledge graph:** Concepts `concept:complex-subspace`, `concept:tensor-product-problem`, `concept:jk-decay`, `concept:symplectic-decomposition`, `concept:quaternionic-schrodinger` are linked to this ground truth.
