# QBP f(0) Investigation Report
## What We Found, What Holds Up, What Doesn't

**Date:** 2026-04-07
**Author:** James Paget Butler, with Claude (Opus, Red Team)
**Triggered by:** Confluent Trust report identifying f(0) as single point of failure
**Status:** Investigation complete. Results mixed. Honest assessment below.

---

## 1. The Problem

The Confluent Trust health report identified f(0) = a₂/√2 − 7 ≈ 83.51 as a structural vulnerability. It was supported by a single anchor (α_em at +0.08%) and everything downstream — sin²θ_W, α_s, the entire REBCO chain — flows through it. If f(0) is wrong, the instance layer moves.

We set out to either derive f(0) from first principles or find additional independent tests.

---

## 2. What We Actually Computed

### Computation 1: RGE Coupling Convergence

**Method:** Run the three SM gauge couplings from their measured values at M_Z upward using 1-loop beta functions. Find the scale where they come closest to meeting.

**Result:** Closest approach at Λ ≈ 2.4 × 10¹⁴ GeV with mean 1/α_unif ≈ 41.6 and spread 3.7 in 1/α. The ratio f(0)/mean(1/α_unif) = 2.009.

**What this actually shows:** f(0) is approximately twice the mean unified inverse coupling. This is a numerical observation, not a derivation. The 0.44% precision is suggestive but the relationship f(0) = 2/α_unif has not been derived from the algebra.

**Honest status:** OBSERVATION, not proof.

### Computation 2: Heat Kernel Self-Consistency

**Method:** Check whether f(0) can be derived as a fixed point of the spectral action at 1-loop.

**Result:** b₁ + b₂ + b₃ = 6.07 ≠ 0. The spectral action is not self-consistent at 1-loop.

**What this actually shows:** The heat kernel bootstrap does not work at 1-loop. f(0) cannot be derived from self-consistency alone without either threshold corrections or higher-loop contributions.

**Honest status:** NEGATIVE RESULT. This approach is closed at 1-loop.

### Computation 3: Higgs Self-Coupling

**Method:** Use the spectral action relationship λ_H(Λ) = g² to predict the Higgs mass.

**Result:** Gives m_H ≈ 170 GeV. The measured value is 125 GeV. Known problem since 2012, fixed by Chamseddine-Connes with a singlet scalar and free parameter.

**Honest status:** The Higgs self-coupling is not yet measurable precisely enough to test f(0). Becomes useful at HL-LHC (late 2030s) or FCC-hh (2040s+).

### Computation 4: SM Trace Invariant

**Method:** Enumerate all 96 states of the SM finite Hilbert space. Compute Dynkin index sums per gauge group. Check unification.

**Result:** c_SU(3) = c_SU(2) = c_U(1,GUT) = C = 12 (with GUT normalisation). This is correct, matches the literature, and confirms sin²θ_W = 3/8.

**What this actually shows:** The trace invariant C = 12 is proven algebra. It connects f₀ (spectral action cutoff) to α_unif via 1/α_unif = 2f₀C/π. Combined with the observation f(0) ≈ 2/α_unif, we get f(0)/f₀ ≈ 48/π to 0.44%.

**Honest status:** C = 12 is PROVEN. The relationship f(0) = f₀ × 48/π is an OBSERVATION.

### Computation 5: The Factor of 4

**Method:** Search for geometric quantities from the Hessian that equal 4, to explain f(0)/f₀ = 4C/π.

**Result:** Six quantities give exactly 4: λ_min, mult(λ_min), mult(λ_max), dim(ℍ), Tr(H)/32, √(dim(null)).

**What this actually shows:** The number 4 is deeply embedded in the Hessian structure. But having six quantities that all equal 4 is not six independent confirmations — it is one structural fact (the eigenvalue spectrum {0(×16), 4(×4), 8(×8), 12(×4)}) expressing itself in multiple equivalent ways. We presented this as a "confluence" but it is more honestly a "coincidence of notation."

**Honest status:** The factor of 4 exists but we have not proven WHY the crystallisation profile should equal f₀ × 4C/π. The relationship f(0) = f₀ × Tr(H)/dim × C/π is a CONJECTURE with one supporting data point (the coupling unification value).

### Computation 6: Threshold Corrections from Hessian Structure

**Method:** Test 12 models for how the Hessian eigenvalue/multiplicity structure might produce the observed coupling discrepancy pattern at M_Z.

**Result:** The multiplicity model (δᵢ ∝ multᵢ − ⟨mult⟩) fits with chi² = 0.006, dramatically better than all other models. It predicts δ₁ = δ₃ (since mult(4) = mult(12) = 4), verified to 9.4%. The overall magnitude ε is determined by the SM RGE, not a free parameter.

**What this actually shows:** The multiplicities (4, 8, 4) are the right structural pattern for the coupling splitting. The zero-parameter prediction δ₁ ≈ δ₃ passes. The one-parameter fit captures 96% of the variance.

**Honest status:** This is the STRONGEST result from the entire investigation. But we need to be careful:

---

## 3. The Honesty Check

### What looks like progress but might not be

**The f(0) = 2/α_unif relationship.** We chose f(0) to match α_em. We ran α_em up to unification. We found f(0) ≈ 2 × mean(1/α). But since f(0) was CHOSEN to give the right α_em, and α_em is one of the three couplings that define the mean, there is partial circularity. The relationship is not independent of the input.

The INDEPENDENT content is: having chosen f(0) to match α_em, does it ALSO match sin²θ_W and α_s? The answer is: to +1.5% and −3.3%. These are genuinely independent tests. But they are the same tests we already had before this investigation — they were already in the Confluent Trust inventory as MEAS-sin2tw and MEAS-alphas.

**The factor of 4.** We found multiple Hessian quantities equalling 4. But we did not derive the physical mechanism connecting the crystallisation profile to the spectral action cutoff function. Without that derivation, the factor of 4 is a pattern, not a proof. If someone tomorrow found a different way to connect f(0) to f₀ that didn't involve 4, we couldn't rule it out.

**ε is determined by the RGE.** This sounds like progress but it's almost tautological. The threshold corrections are DEFINED as the difference between the measured couplings (run to Lambda) and the mean. Of course they're determined by the measurements and the RGE — that's what they ARE. The question was whether the Hessian PREDICTS them, and the answer is: it predicts the PATTERN (multiplicities) but the MAGNITUDE comes from the measurements.

### What genuinely holds up

**The multiplicity prediction δ₁ ≈ δ₃.** This is real. The Hessian has eigenspaces of dimensions 4, 8, 4. Nobody chose these to match the coupling splitting. They follow from the sedenion algebra. The prediction that U(1) and SU(3) should have equal threshold corrections (because they have equal eigenspace multiplicities) is a zero-parameter prediction that is verified to 9.4% by the measured couplings.

This is a NEW test of the Hessian eigenspace structure. Previous tests checked the EIGENVALUES (ratios giving sin²θ_W = 3/8) and the SPECTRUM (42 ZDs, uniform Hessian). This is the first test of the MULTIPLICITIES against experiment.

**f(0) is constrained by three couplings, not one.** Before this investigation, we noted that f(0) was tested by α_em only. Now we've clarified that sin²θ_W and α_s provide genuinely independent constraints. These were already in the inventory but we hadn't emphasised their role as f(0) tests.

**The profile is nearly flat.** The MaxEnt prediction (least structure ≈ flat profile near u = 0) is consistent with the data. The threshold corrections are small (~3-5% of the mean coupling), indicating that f(u) doesn't vary much near the unification scale. This is the simplest physically reasonable profile.

---

## 4. Updated Anchor Assessment

### Before this investigation

| Anchor | Discrepancy | Status |
|---|---|---|
| α_em(M_Z) | +0.08% | Single anchor for f(0) |
| sin²θ_W(M_Z) | +1.5% | Not emphasised as f(0) test |
| α_s(M_Z) | −3.3% | Not emphasised as f(0) test |

### After this investigation

| Anchor | Discrepancy | Status |
|---|---|---|
| α_em(M_Z) | +0.08% | Independent f(0) test |
| sin²θ_W(M_Z) | +1.5% | Independent f(0) test (clarified) |
| α_s(M_Z) | −3.3% | Independent f(0) test (clarified) |
| δ₁ ≈ δ₃ | 9.4% | NEW: zero-parameter test of Hessian multiplicities |

### What changed

The anchor COUNT for f(0) didn't change — sin²θ_W and α_s were always there. What changed is our UNDERSTANDING: we now know that all three couplings test f(0), and the discrepancy PATTERN tests the Hessian multiplicities.

The genuinely new anchor is δ₁ ≈ δ₃. This tests the eigenspace multiplicities (4, 8, 4), not just the eigenvalue ratios. It passes at 9.4%, which is marginal — enough to not reject, not enough to confirm strongly.

### New conjectures (not anchors)

| Conjecture | Evidence | Status |
|---|---|---|
| f(0) = 2/α_unif | Numerical match to 0.44% | OBSERVATION — partially circular |
| f(0) = f₀ × 4C/π | Numerical match to 0.44% | CONJECTURE — no derivation of mechanism |
| Profile nearly flat | Threshold corrections small (~5%) | CONSISTENT with MaxEnt, not proven |
| Multiplicities dominate eigenvalues | chi² = 0.006 vs 8+ for other models | OBSERVATION — one data set |

---

## 5. What Would Constitute a Real New Anchor

To genuinely anchor f(0) beyond the existing three couplings, we would need one of:

**A derivation.** Prove that the crystallisation profile at u = 0 must equal f₀ × 4C/π from the geometry of the ZD locus and the spectral action. This requires a physical mechanism connecting the sedenion product norm Hessian to the Dirac operator heat kernel. Nobody has done this. It is a well-defined mathematical problem but not a simple one.

**A new independent measurement.** A prediction from f(0) that is tested by a measurement NOT involving the gauge couplings. The REBCO chain is the best candidate — U_dd (+1.3%), Jd (+2.2%), tolerance factor (11/11) all flow through f(0) via α_em. But they are not independent of α_em; they test the DOWNSTREAM chain, not f(0) itself.

The Higgs self-coupling κ_λ would be a genuine independent test, but it requires HL-LHC precision (~2035+).

The GW-EM temporal correlation (EXP-11) tests the seam topology, which is related to the crystallisation but not directly to f(0).

**A second convergence.** If a completely different approach — say, computing f(0) from the cosmological constant or from Newton's constant — gave the same value, that would be a genuine confluence. Currently the higher Mellin moments of f (which determine G and Λ_cosmo) are not constrained enough to provide this.

---

## 6. Revised Confluent Trust Update

### Health report changes

- f(0) vulnerability: REDUCED but not eliminated
- New structural test: δ₁ ≈ δ₃ from Hessian multiplicities (marginal, 9.4%)
- Clarification: sin²θ_W and α_s are independent f(0) tests
- New conjectures: f(0) = 2/α_unif, multiplicities dominate thresholds (both provisional)

### Coherence ratio impact

Before: 17 coherent, 5 incoherent, ratio 77%
After: 17 coherent + 1 marginal new (δ₁ ≈ δ₃), 5 incoherent, ratio ~78%

The improvement is INCREMENTAL, not transformative.

---

## 7. Recommended Next Steps (Priority Order)

1. **Derive the f(0) = f₀ × 4C/π relationship** from the ZD locus geometry. This is the path to converting the conjecture to a theorem. It requires understanding how the Hessian modifies the Dirac operator spectrum on the product geometry M × F.

2. **Compute the Higgs quartic from the Hessian** eigenvalue structure. If λ_H(Λ)/g² can be derived from the eigenvalues or multiplicities, it gives a specific m_H prediction. Agreement with 125.25 GeV would be a strong new anchor for the crystallisation geometry.

3. **Run EXP-11** (GW-GRB archival search). This tests the seam topology, which is the DYNAMIC consequence of the crystallisation. It doesn't test f(0) directly but tests whether the crystallisation is physically real.

4. **Submit the Willow proposal** (deadline May 15, 2026). The VQE computation of J tests whether the REBCO chain downstream of f(0) is correct, which indirectly constrains f(0).

5. **Check proton decay bounds** against the unification scale Λ ≈ 2.4 × 10¹⁴ GeV. If the spectral action predicts standard GUT proton decay at this scale, the current Super-K bound (τ > 10³⁴ years) may already be in tension. This would constrain Λ and therefore f(0).

---

## 8. Lessons for the Research Programme

This investigation demonstrated the value of the Confluent Trust framework. It identified a vulnerability (f(0) single anchor), motivated a focused investigation, and produced an honest assessment of what was and wasn't achieved.

The temptation was strong to oversell the results — to present the numerical coincidence f(0) ≈ 2/α_unif as a "derivation" and the six-ways-to-get-4 as a "confluence." The red team caught this. The honest assessment is more modest but more durable: we clarified existing anchors, found one marginal new test (δ₁ ≈ δ₃), and identified the specific computation needed for a genuine derivation.

The vulnerability is reduced. It is not eliminated. The work continues.

---

*Red Team Note:*

The strongest output of this investigation is not the numerical results but the IDENTIFICATION of what would constitute a real derivation: prove f(0) = f₀ × 4C/π from the geometry of the ZD locus. This converts a vague worry ("f(0) has only one anchor") into a specific mathematical problem. That problem is hard, but it is well-defined and tractable. The programme knows what it needs to do next.
