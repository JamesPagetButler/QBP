/-
TOOLCHECK T13 — real analysis API QBP uses: `Real.sqrt` (`Real.sq_sqrt`,
`Real.sqrt_pos`, `Real.sqrt_nonneg`), trigonometry (`Real.sin_sq_add_cos_sq`,
`Real.cos_pi`, `Real.pi_pos`), `Real.exp`/`Real.log` (`Real.exp_pos`, `Real.log_exp`),
and derivatives (`HasDerivAt`, `deriv`) — all proved structurally, never by `decide`
(standard §8: ℝ is not decidable).

Used by (QBP, 2026-11-20 grep): `Real.sqrt` 10 files — `QBP/Substrate/RuleFlow.lean`,
`QBP/Foundations/Exp.lean`, `RuleFlowInvariants.lean`, `DeltaLandscape.lean`; trig 8 files —
`Exp.lean`, `QBP/Experiments/General3D.lean`, `QBP/Optics/Fraunhofer.lean`,
`AngleDependent.lean`; `Real.exp`/`Real.log` 4 files — `Exp.lean`, `QBP/Cosmo/SeedMass.lean`,
`FanoChoiceInformation.lean`; `HasDerivAt`/`deriv` 4 files — `RuleFlow.lean`,
`RuleFlowInvariants.lean`, `CrystalHosting.lean`, `Hosting.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Positivity

namespace QBPToolcheck.T13

/-- `√x² = x` direction: `(√x)² = x` for `x ≥ 0`. -/
theorem sqrt_sq_id (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx

/-- `√` of a positive number is positive. -/
theorem sqrt_pos_of (x : ℝ) (hx : 0 < x) : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx

/-- `√` is non-negative. -/
theorem sqrt_nn (x : ℝ) : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x

/-- Pythagorean identity. -/
theorem pyth (θ : ℝ) : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ

/-- `cos π = -1` and `π > 0`. -/
theorem cos_pi_and_pos : Real.cos Real.pi = -1 ∧ 0 < Real.pi := ⟨Real.cos_pi, Real.pi_pos⟩

/-- `exp` is positive and `log ∘ exp = id`. -/
theorem exp_log (x : ℝ) : 0 < Real.exp x ∧ Real.log (Real.exp x) = x :=
  ⟨Real.exp_pos x, Real.log_exp x⟩

/-- `HasDerivAt` of a polynomial, built from the product rule. -/
theorem hasDerivAt_sq (x : ℝ) : HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
  (hasDerivAt_id' x).mul (hasDerivAt_id' x)

/-- `deriv` of `y ↦ y ^ 3` via `deriv_pow`-family simp. -/
theorem deriv_cube (x : ℝ) : deriv (fun y : ℝ => y ^ 3) x = 3 * x ^ 2 := by
  simp

end QBPToolcheck.T13

#print axioms QBPToolcheck.T13.sqrt_sq_id
#print axioms QBPToolcheck.T13.sqrt_pos_of
#print axioms QBPToolcheck.T13.sqrt_nn
#print axioms QBPToolcheck.T13.pyth
#print axioms QBPToolcheck.T13.cos_pi_and_pos
#print axioms QBPToolcheck.T13.exp_log
#print axioms QBPToolcheck.T13.hasDerivAt_sq
#print axioms QBPToolcheck.T13.deriv_cube
