# Experiment 03: Double-Slit — Expected Results (Ground Truth)

**Sprint 3 | Phase 1: Ground Truth**
**Last updated:** 2026-02-12 (reworked based on Pre-Sprint Research #255 and Research Sprint 1R #211)

This document defines the quantitative predictions for the double-slit interference experiment using the QBP formalism, establishing the ground truth that Phase 2 simulations must reproduce.

## 1. Experimental Setup

| Parameter | Symbol | Description |
|-----------|--------|-------------|
| Slit separation | d | Distance between slit centers |
| Slit width | a | Width of each slit (a << d for point-source approximation) |
| Screen distance | L | Distance from slits to detector screen (L >> d) |
| Wavelength | λ | de Broglie wavelength λ = h/p |
| Wave number | k | k = 2π/λ |
| Screen position | x | Position on detector screen (x=0 at center) |

**Conditions:**
- **Scenario A:** No which-path information (interference)
- **Scenario B:** Which-path detection (no interference)

## 2. QBP Formalism: Complex Subspace Approach

### 2.1 Theoretical Foundation

Based on Pre-Sprint Research (#249-#253, documented in DESIGN_RATIONALE §10):

**Key decision:** Sprint 3 adopts the **complex subspace C(1,i)** of ℍ. Wavefunctions are restricted to:

```
ψ(x) = α(x)·1 + β(x)·i
```

where α(x), β(x) are real-valued functions. This is isomorphic to standard complex QM: ψ(x) = α(x) + iβ(x).

**Rationale:**
1. Moretti-Oppio theorem guarantees standard QM results for elementary systems
2. Avoids the tensor product problem that makes "full QQM" for spatial superposition mathematically problematic
3. Adler's scattering theory shows intrinsically quaternionic terms (j, k components) exhibit exponential spatial decay — at the detector screen, only complex (1, i) components survive
4. This is a **reformulation exercise**, not a divergence test

**Consequence:** QBP predictions for pure double-slit MUST match standard QM exactly. Any divergence would **falsify** QBP.

### 2.2 Born Rule in C(1,i)

The probability density is:

```
P(x) = |ψ(x)|² = α(x)² + β(x)²
```

This is identical to the standard complex Born rule.

## 3. Quantitative Predictions

### 3.1 Scenario A: No Which-Path Information (Interference)

**Wavefunction at detector screen:**

Each slit acts as a point source. The path lengths from slit 1 and slit 2 to screen position x are r₁ and r₂ respectively.

```
ψ₁(x) = A · exp(ikr₁) = A · [cos(kr₁) + i·sin(kr₁)]
ψ₂(x) = A · exp(ikr₂) = A · [cos(kr₂) + i·sin(kr₂)]
```

The total wavefunction is the superposition:

```
ψ(x) = ψ₁(x) + ψ₂(x)
```

Therefore:
```
α(x) = A · [cos(kr₁) + cos(kr₂)]
β(x) = A · [sin(kr₁) + sin(kr₂)]
```

**Intensity pattern:**

```
I(x) = α(x)² + β(x)²
     = 2A² · [1 + cos(k(r₁ - r₂))]
     = 4A² · cos²(k(r₁ - r₂)/2)
```

**Far-field approximation** (L >> d, small angle):

```
r₁ - r₂ ≈ xd/L
```

Therefore:

```
I(x) = 4A² · cos²(πxd / λL)
```

**Fringe spacing** (distance between adjacent maxima):

```
Δx = λL / d
```

**Maxima locations:**

```
x_n = nλL/d,  where n = 0, ±1, ±2, ...
```

**Minima locations:**

```
x_n = (n + 1/2)λL/d,  where n = 0, ±1, ±2, ...
```

**Central maximum:** At x = 0, I(0) = 4A² (maximum intensity).

### 3.2 Scenario B: With Which-Path Detection (No Interference)

When a detector determines which slit the electron traverses, the superposition collapses. The electron is found at slit 1 with probability 1/2 or slit 2 with probability 1/2.

**Intensity pattern:**

```
I(x) = (1/2)|ψ₁(x)|² + (1/2)|ψ₂(x)|²
     = (1/2)A² + (1/2)A²
     = A²
```

This is a **uniform distribution** (no fringes). The interference cross-term cos(k(r₁ - r₂)) vanishes because the paths are distinguishable.

**In QBP terms:** Measurement at the slits projects the quaternionic state onto one of the slit eigenstates, setting either ψ₁ or ψ₂ to zero. The cross-term (cos(kr₁)cos(kr₂) + sin(kr₁)sin(kr₂)) disappears.

### 3.3 Single-Slit Envelope (Finite Slit Width)

For finite slit width a, the intensity is modulated by the single-slit diffraction envelope:

```
I(x) = 4A² · cos²(πxd / λL) · sinc²(πxa / λL)
```

where sinc(u) = sin(u)/u. The envelope has zeros at x = nλL/a.

## 4. Simulation Parameters

### 4.1 Default Configuration

| Parameter | Value | Rationale |
|-----------|-------|-----------|
| d | 1.0 μm | Typical electron double-slit |
| a | 0.1 μm | a << d (point-source approximation valid) |
| L | 1.0 m | Far-field condition L >> d |
| λ | 0.05 nm | Electron at ~500 eV (de Broglie) |
| k | 1.257 × 10¹¹ m⁻¹ | k = 2π/λ |
| Δx | 50 μm | Predicted fringe spacing = λL/d |

### 4.2 Parameter Sensitivity Tests

The simulation must verify that fringe spacing scales correctly:

| Test | Variation | Expected Δx Change |
|------|-----------|-------------------|
| Double λ | λ → 2λ | Δx → 2Δx |
| Double L | L → 2L | Δx → 2Δx |
| Double d | d → 2d | Δx → Δx/2 |

## 5. Success Criteria

### 5.1 Quantitative Acceptance Criteria

| # | Criterion | Tolerance |
|---|-----------|-----------|
| 1 | Scenario A fringe maxima at x_n = nλL/d | Within 1% of predicted positions |
| 2 | Scenario A intensity follows cos²(πxd/λL) | R² > 0.99 vs analytical curve |
| 3 | Scenario A fringe spacing matches λL/d | Within 1% |
| 4 | Scenario B shows no fringes (uniform distribution) | Visibility V < 0.01 |
| 5 | Fringe visibility V = (I_max - I_min)/(I_max + I_min) ≈ 1.0 for Scenario A | V > 0.95 |
| 6 | Parameter sensitivity tests pass | Correct scaling within 1% |
| 7 | Results match standard complex QM to machine precision | Difference < 10⁻⁶ |

### 5.2 Fringe Visibility

Fringe visibility is defined as:

```
V = (I_max - I_min) / (I_max + I_min)
```

- Scenario A (point sources, no decoherence): V = 1.0
- Scenario B (which-path detection): V = 0.0
- Finite slit width reduces V at large x (envelope effect)

## 6. Falsification Criteria

**Pre-registered (from Pre-Sprint Research #251):**

| Scenario | QBP Prediction | Standard QM | Match Required? |
|----------|---------------|-------------|-----------------|
| No which-path | cos²(πxd/λL) fringes | cos²(πxd/λL) fringes | **MUST match** |
| With which-path | Uniform distribution | Uniform distribution | **MUST match** |
| Fringe spacing | Δx = λL/d | Δx = λL/d | **MUST match** |
| Fringe visibility | V = 1.0 (ideal) | V = 1.0 (ideal) | **MUST match** |

**Falsification criterion:** If QBP predicts different interference patterns than standard QM for pure double-slit, this would **falsify QBP**, since standard QM matches experimental reality.

**Null hypothesis value:** If QBP matches QM exactly (expected), we confirm:
1. Quaternionic reformulation is consistent for spatial interference
2. Single-particle spatial interference is not where QQM diverges from standard QM
3. The true divergence test remains multi-particle entanglement (Sprint 6: Bell's Theorem)

## 7. What This Experiment Does NOT Test

Based on Pre-Sprint Research findings:

1. **Intrinsically quaternionic superposition** — The C(1,i) restriction means j,k components are absent by construction. Testing their spatial decay (Adler 1995) requires a different experimental setup.
2. **Multi-particle entanglement** — The tensor product problem (#249) means QQM may diverge from standard QM for entangled states. This is Sprint 6.
3. **Spin-path coupling** — Where quaternionic structure naturally appears. Recommended for future sprints.

## 8. Implementation Notes for Phase 2

### 8.1 QBP-Specific Implementation

The simulation should:
1. Represent ψ(x) as quaternion with only (1, i) components: `create_state(α(x), β(x), 0, 0)`
2. Compute intensity via quaternion norm: `|ψ(x)|²`
3. Verify j,k components remain zero throughout propagation
4. Compare against an independent standard complex QM calculation

### 8.2 Measurement in QBP

For Scenario B (which-path detection):
1. Model the measurement as a quaternionic observable at each slit
2. Use the existing `measure()` function from qphysics.py
3. After measurement, propagate only the collapsed single-slit state

### 8.3 Visualization Concepts (from #253)

Sprint 3 Phase 3 should implement:
- Component-wise intensity plot showing α(x)² and β(x)² separately
- Side-by-side comparison: QBP vs standard QM (should be identical)
- Fringe visibility as a function of partial which-path information

## 9. References

1. **Adler, S.L.** (1995). *Quaternionic Quantum Mechanics and Quantum Fields*. Oxford University Press.
2. **Moretti, V. & Oppio, M.** (2017). "Quantum theory in quaternionic Hilbert space." arXiv:1709.09246
3. **McKague, M.** (2009). "Quaternionic quantum mechanics allows non-local boxes." arXiv:0911.1761
4. **Tonomura, A. et al.** (1989). "Demonstration of single-electron buildup of an interference pattern." Am. J. Phys. 57, 117.

---

**Review tier:** Tier 3 (theory-critical)

**Knowledge graph:** Concepts `concept:complex-subspace`, `concept:tensor-product-problem`, `concept:jk-decay` are linked to this ground truth.
