# Experiment 03: Double-Slit — Phase 3 Visualization Results

**Analysis Date:** 2026-02-15 23:48:09
**Data Source:** `results/03_double_slit/`
**Sprint:** 3 (SI Redo)

---

## 1. Key Scientific Finding

**Outcome (b) confirmed: Step-change in η, NOT exponential Adler decay.**

The BPM simulation produces a discrete step-change in the quaternionic component
η at the coupling region, rather than the exponential decay predicted by Adler's
trace dynamics. This is a genuine physics result: the BPM's SO(4) rotation is
coherent and unitary, while Adler decay requires environmental decoherence that
the BPM does not model. Ground truth §4.3.2 anticipated this outcome.

The step-change is proportional to U₁ coupling strength and occurs precisely
at the spatial region where the coupling potential is active.

---

## 2. Visibility Results

### 2.1 BPM Visibility Table

| U₁ (eV) | η₀ | Visibility V | Norm (final) |
|----------|-----|-------------|-------------|
|       0.00 |  0.01 | 0.552870 | 1.0000000000023117 |
|       0.00 |  0.10 | 0.552870 | 1.0000000000023279 |
|       0.00 |  0.50 | 0.552870 | 1.0000000000023230 |
|      30.08 |  0.01 | 0.552770 | 1.0000000000023168 |
|      30.08 |  0.10 | 0.552770 | 1.0000000000023292 |
|      30.08 |  0.50 | 0.552770 | 1.0000000000023190 |
|      60.16 |  0.01 | 0.552472 | 1.0000000000023157 |
|      60.16 |  0.10 | 0.552472 | 1.0000000000023266 |
|      60.16 |  0.50 | 0.552472 | 1.0000000000023226 |
|     120.33 |  0.01 | 0.551289 | 1.0000000000023137 |
|     120.33 |  0.10 | 0.551289 | 1.0000000000023250 |
|     120.33 |  0.50 | 0.551289 | 1.0000000000023224 |
|     300.82 |  0.01 | 0.543329 | 1.0000000000023106 |
|     300.82 |  0.10 | 0.543329 | 1.0000000000023177 |
|     300.82 |  0.50 | 0.543329 | 1.0000000000023124 |
|     601.65 |  0.01 | 0.510061 | 1.0000000000023010 |
|     601.65 |  0.10 | 0.510061 | 1.0000000000023139 |
|     601.65 |  0.50 | 0.510061 | 1.0000000000023050 |

### 2.2 Comparison with Analytical Baselines

| Scenario | Description | Visibility |
|----------|-------------|-----------|
| A | Full interference (analytical) | 1.000000 |
| B | Which-path (analytical) | 0.000000 |
| C (U₁=0) | BPM baseline | 0.552870 |
| C (U₁=602 eV) | BPM max coupling | 0.510061 |

**V reduction:** 0.552870 → 0.510061 (7.7% decrease)

The BPM baseline V ≈ 0.553 (vs analytical V = 1.0) is expected: the BPM
propagates over ~32 nm (near-field), while the analytical result assumes
Fraunhofer far-field conditions (mm scale).

---

## 3. Hero Detector Plots

### 3.1 Fringe Overlay — Expected vs QBP

![Hero Fringe Overlay](hero_fringe_overlay.png)

**Caption:** Full nearfield detector pattern comparing the Expected baseline (U₁ = 0 eV,
teal) with the QBP coupling case (U₁ = 602 eV, crimson). Both curves share
the same detector x-axis in nm. The reduction in peak height under quaternionic coupling
is visible as lower fringe contrast in the crimson curve.

### 3.2 Zoomed Fringes (±0.05 nm)

![Hero Fringe Zoomed](hero_fringe_zoomed.png)

**Caption:** Zoomed view of ±0.05 nm around the detector centre, showing ~12 individual
fringes at ~8.5 pm spacing. The shaded amber region highlights the intensity difference
between Expected and QBP curves. Constructive and destructive peaks are clearly resolved.

### 3.3 Three-Panel Comparison (A/B/C)

![Fringe Comparison](fringe_comparison.png)

**Caption:** Three-panel comparison of double-slit intensity patterns.
- **Top (A):** Far-field analytical with full interference (V = 1.0).
- **Middle (B):** Far-field analytical with which-path information (V = 0.0).
- **Bottom (C):** Near-field BPM simulation at nm scale.

**Note:** Panels 1–2 use mm x-axis (far-field); Panel 3 uses nm x-axis (near-field).

### 3.4 Residual Analysis

![Residual](residual.png)

**Caption:** Residual intensity I_QBP − I_Expected across the full detector. Non-zero
spatial structure demonstrates the quaternionic coupling signal.

| Metric | Value |
|--------|-------|
| Max residual | +0.025205 |
| Min residual | -0.034104 |
| RMS residual | 0.007311 |
| Pattern | Oscillatory (modulates fringe peaks) |

The residual is not flat noise — it shows systematic oscillatory structure aligned with
the fringe pattern, confirming that the QBP coupling preferentially suppresses fringe
peaks. This is the expected signature of quaternionic decoherence: the coupling transfers
energy from coherent fringe maxima to the diffuse background.

---

## 4. η₀-Independence Analysis

![η₀ Independence](eta0_independence.png)

**Caption:** Small multiples showing fringe visibility V vs initial quaternionic
fraction η₀ for each coupling strength U₁. Visibility is identical to ~14 decimal
places across all η₀ values (max difference: 8.33e-15). This confirms that
ψ₁ ∝ ψ₀ at initialization — the quaternionic component's relative weight does
not affect the interference pattern.

This addresses housekeeping issue #334.

---

## 5. η(z) Step-Change Characterization

![η Decay](eta_decay.png)

**Caption:** Quaternionic component Δη = η(z) − η₀ vs propagation distance z (nm),
for η₀ = 0.5. The step-change at the coupling region (shaded) demonstrates
outcome (b): the unitary BPM produces a coherent rotation in SO(4) quaternion
space, not the dissipative exponential decay of Adler's trace dynamics. The
context strip below shows where the coupling potential U₁(z) is active.

### Step-Change Table (η₀ = 0.5)

| U₁ (eV) | z_jump (nm) | η_before | η_after | Δη |
|----------|-------------|----------|---------|-----|
|       0.00 |     0.00 | 0.500000 | 0.500000 | +0.000000 |
|      30.08 |     7.96 | 0.500000 | 0.500062 | +0.000062 |
|      60.16 |     7.96 | 0.500000 | 0.500123 | +0.000123 |
|     120.33 |     7.96 | 0.500000 | 0.500246 | +0.000246 |
|     300.82 |     7.96 | 0.500000 | 0.500617 | +0.000617 |
|     601.65 |     7.96 | 0.500000 | 0.501248 | +0.001248 |

---

## 6. Norm Conservation

| Metric | Value |
|--------|-------|
| Max ‖ψ‖ deviation from 1 | 2.33e-12 |
| Threshold | 10⁻⁸ |
| Status | PASS |

All BPM runs conserve norm to machine precision, confirming the unitary
evolution is correctly implemented.

---

## 7. Acceptance Criteria Verification

| AC | Description | Status | Evidence |
|----|-------------|--------|----------|
| AC #1 | Loads v3 CSVs | PASS | All v3 files loaded |
| AC #2 | Detector fringe overlay (Expected vs QBP) | PASS | See hero_fringe_overlay.png |
| AC #3 | Zoomed fringe ±0.05 nm (~12 fringes) | PASS | See hero_fringe_zoomed.png |
| AC #4 | Residual plot (I_qbp − I_expected) | PASS | See residual.png |
| AC #5 | V(U₁) monotonic decrease | PASS | 0.552870 → 0.510061 |
| AC #6 | Labeled axes, SI units, ≥300 dpi | PASS | All PNGs at 300 dpi |
| AC #7 | RESULTS.md with residual analysis | PASS | See §3.4 |
| AC #8 | VPython loads v3 | PASS | double_slit_viz.py supports v3 |

---

## 8. Cross-References

- **Ground Truth:** `research/03_double_slit_expected_results.md` §9.4
- **Phase 2 (Simulation):** PR #333 (closed #332)
- **Phase 2 Data:** `results/03_double_slit/`
- **Phase 3 Issue:** #342 (hero detector plots)
- **Theme:** `src/viz/theme.py` (Steampunk → Solarpunk)
- **Housekeeping:** #334 (η₀-independence, addressed in §4)

---

*Generated by `analysis/03_double_slit/analyze.py`*
