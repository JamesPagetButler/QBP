# Experiment 01b: Angle-Dependent Measurement Results

**Analysis Date:** 2026-02-10 13:40:47
**Data Source:** `simulation_results_2026-02-06_15-00-02.csv`
**Verdict:** **PASS** ✓

---

## 1. Summary of Findings

This analysis validates the QBP prediction for angle-dependent spin measurement:

$$P(+) = \cos^2(\theta/2) = \frac{1 + \cos\theta}{2}$$

**Key Results:**
- All 9 test angles (0° to 180°) fall within the 3σ acceptance threshold
- Maximum deviation: 1.7500σ (threshold: 3.0σ)
- χ² goodness-of-fit: χ² = 4.9597, p = 0.6649 (df = 7)
- The quaternion-based measurement framework reproduces standard QM predictions exactly

---

## 2. Comparison with Ground Truth

| Angle | Expected P(+) | Measured P(+) | Deviation | Pass |
|-------|---------------|---------------|-----------|------|
|   0° | 1.000000 | 1.000000 | +0.0000σ | ✓ |
|  30° | 0.933013 | 0.933012 | +0.0028σ | ✓ |
|  45° | 0.853553 | 0.853625 | +0.2025σ | ✓ |
|  60° | 0.750000 | 0.749732 | +0.6189σ | ✓ |
|  90° | 0.500000 | 0.499125 | +1.7500σ | ✓ |
| 120° | 0.250000 | 0.249747 | +0.5843σ | ✓ |
| 135° | 0.146447 | 0.146148 | +0.8446σ | ✓ |
| 150° | 0.066987 | 0.067149 | +0.6468σ | ✓ |
| 180° | 0.000000 | 0.000000 | +0.0000σ | ✓ |

**Ground truth reference:** `research/01b_angle_dependent_expected_results.md`

---

## 3. χ² Goodness-of-Fit Test

The χ² test evaluates whether the measured distribution matches the theoretical prediction.

| Metric | Value |
|--------|-------|
| χ² statistic | 4.9597 |
| Degrees of freedom | 7 |
| p-value | 0.6649 |
| Significance level | α = 0.05 |
| Result | PASS (p > 0.05) |

**Interpretation:** The measured data is statistically consistent with the theoretical prediction. The deviations are explained by expected statistical fluctuations.

**Important caveat:** A high p-value indicates the data is *consistent* with the model, but does not *prove* the model is correct. Alternative models could also produce similar results. What we can conclude is that the QBP prediction is not falsified by this experiment.

**Note on deterministic cases:** Angles θ=0° and θ=180° are excluded from the χ² calculation because they have σ=0 (deterministic outcomes). The χ² test requires normally distributed errors, which is not valid when variance is zero. These cases are verified separately as exact matches.

---

## 4. Visualizations

### 4.1 Probability vs Angle

![Probability Curve](probability_vs_angle.png)

The smooth teal curve shows the theoretical prediction P(+) = cos²(θ/2). Brass markers show measured probabilities with error bars (±1σ). All measurements lie on or very close to the theoretical curve.

### 4.2 Deviation Analysis

![Deviation Plot](deviation_analysis.png)

Each point shows how far the measured probability deviates from the prediction, measured in standard deviations (σ). The shaded bands indicate ±1σ (teal), ±2σ (amber), and ±3σ (red) regions. All points fall well within the ±3σ acceptance threshold.

### 4.3 Interactive Bloch Sphere

An interactive 3D visualization is available to explore how the state angle θ affects measurement probability:

```bash
python analysis/01b_angle_dependent/bloch_sphere.py
```

This opens a browser-based VPython visualization showing:
- The Bloch sphere with state vector ψ(θ) and measurement axis
- A slider to sweep θ from 0° to 180°
- Real-time probability calculation P(+) = cos²(θ/2)

---

## 5. Detailed Statistics

### 5.1 Error Bar Derivation

The error bars (σ) come from **binomial statistics**. For N independent trials with success probability p:

$$\sigma = \sqrt{N \cdot p \cdot (1-p)}$$

For example, at θ=90° with p=0.5 and N=1,000,000:
$$\sigma = \sqrt{1,000,000 \times 0.5 \times 0.5} = 500$$

At θ=0° and θ=180°, p=1 or p=0, so σ=0 (deterministic outcomes).

### 5.2 Per-Angle Breakdown

| Angle | N trials | Count(+) | μ (expected) | σ | |Count - μ| |
|-------|----------|----------|--------------|---|------------|
| 0° | 1,000,000 | 1,000,000 | 1,000,000 | 0.0 | 0 |
| 30° | 1,000,000 | 933,012 | 933,012 | 250.0 | 0 |
| 45° | 1,000,000 | 853,625 | 853,553 | 353.6 | 72 |
| 60° | 1,000,000 | 749,732 | 750,000 | 433.0 | 268 |
| 90° | 1,000,000 | 499,125 | 500,000 | 500.0 | 875 |
| 120° | 1,000,000 | 249,747 | 250,000 | 433.0 | 253 |
| 135° | 1,000,000 | 146,148 | 146,446 | 353.6 | 298 |
| 150° | 1,000,000 | 67,149 | 66,987 | 250.0 | 162 |
| 180° | 1,000,000 | 0 | 0 | 0.0 | 0 |

### 5.3 Acceptance Criteria Verification

| Criterion | Status |
|-----------|--------|
| Probability curve matches cos²(θ/2) visually | ✓ PASS |
| χ² test passes (p > 0.05) | ✓ PASS |
| All tested angles within 3σ of prediction | ✓ PASS |
| Figures are publication-quality | ✓ PASS |

---

## 6. Conclusion

**Experiment 01b: PASS**

The QBP framework's angle-dependent measurement prediction has been validated:

1. **Mathematical agreement:** The measured probabilities match P(+) = cos²(θ/2) at all test angles
2. **Statistical significance:** χ² = 4.9597 with p = 0.6649 confirms the data is consistent with theory
3. **Acceptance criteria:** All points within 1.75σ of prediction (threshold: 3σ)

This result confirms that quaternion-based quantum mechanics correctly predicts spin measurement outcomes for arbitrary angles, extending the validation from Experiment 01 (orthogonal case only) to the full angular range.

---

## 7. Cross-References

- **Theory:** `paper/DESIGN_RATIONALE.md` §6.4
- **Ground Truth:** `research/01b_angle_dependent_expected_results.md`
- **Simulation Code:** `experiments/01b_angle_dependent/run_experiment.py`
- **Raw Data:** `results/01b_angle_dependent/`
- **Interactive Visualization:** `analysis/01b_angle_dependent/bloch_sphere.py`

---

*Generated by `analysis/01b_angle_dependent/analyze.py`*
