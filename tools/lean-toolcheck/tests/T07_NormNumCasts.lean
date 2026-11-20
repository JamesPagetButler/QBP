/-
TOOLCHECK T07 — `norm_num` (incl. `norm_num [lemmas]` and the `Real.sqrt` extension
path), and the cast tactics `push_cast` / `exact_mod_cast`.

Feature: `norm_num` decides closed numeric (in)equalities in ordered fields — the main way
QBP checks real-number literals, which `decide` cannot (standard §8). `push_cast` moves
`↑` coercions (ℕ → ℤ → ℚ → ℝ) outward; `exact_mod_cast` closes a goal up to casts.

Used by (QBP, 2026-11-20 grep): `norm_num` 36 files — `QBP/Foundations/Breakdown.lean`,
`Alternator.lean`, `SeamSpectrum.lean`, `QBP/Substrate/RuleFlow.lean`; `push_cast`
18 files — `NoAutonomousDynamics.lean`, `Alternator.lean`, `OctonionLaws.lean`,
`OctonionAutBranching.lean`; `exact_mod_cast` 8 files — `Breakdown.lean`,
`OctonionAutBranching.lean`, `SpectralMoments.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace QBPToolcheck.T07

/-- Closed real arithmetic. -/
theorem nn_real : (3 : ℝ) / 4 + 1 / 4 = 1 ∧ (2 : ℝ) ^ 10 = 1024 ∧ (7 : ℝ) / 3 < 3 := by
  norm_num

/-- Integer arithmetic with signs (ℤ). -/
theorem nn_int : (-3 : ℤ) * 5 + 17 = 2 := by norm_num

/-- `Real.sqrt` of a perfect square via `norm_num [lemma]` (QBP's `Real.sq_sqrt` path). -/
theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `Real.sq_sqrt` with a non-negativity side goal discharged by `norm_num`. -/
theorem sq_sqrt_two : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `push_cast` across ℕ → ℝ. -/
theorem cast_push (n : ℕ) : ((n + 1 : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 + 2 * n + 1 := by
  push_cast
  ring

/-- `exact_mod_cast` lifting a ℕ fact into ℝ. -/
theorem cast_lift (n : ℕ) (h : 3 ≤ n) : (3 : ℝ) ≤ n := by
  exact_mod_cast h

end QBPToolcheck.T07

#print axioms QBPToolcheck.T07.nn_real
#print axioms QBPToolcheck.T07.nn_int
#print axioms QBPToolcheck.T07.sqrt_four
#print axioms QBPToolcheck.T07.sq_sqrt_two
#print axioms QBPToolcheck.T07.cast_push
#print axioms QBPToolcheck.T07.cast_lift
