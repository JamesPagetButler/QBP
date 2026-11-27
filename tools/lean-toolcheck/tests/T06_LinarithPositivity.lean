/-
TOOLCHECK T06 — `linarith`, `nlinarith [hints]`, `positivity` over ordered fields (ℝ).

Feature: linear arithmetic over ordered fields (`linarith`), the Positivstellensatz-style
product-of-hypotheses extension with user hints (`nlinarith [sq_nonneg …]`), and the
syntactic positivity prover (`positivity`) for goals `0 < e` / `0 ≤ e`.

Used by (QBP, 2026-11-20 grep): `linarith` 20 files — `QBP/Substrate/RuleFlowInvariants.lean`,
`RuleFlow.lean`, `QBP/Experiments/DoubleSlit.lean`, `QBP/Foundations/SeamSpectrum.lean`;
`nlinarith` 9 files — `QBP/Substrate/RuleFlow.lean`, `Hosting.lean`, `RuleFlowInvariants.lean`;
`positivity` 7 files — `QBP/Foundations/CDAlg.lean`, `SpectralMoments.lean`, `Exp.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

namespace QBPToolcheck.T06

/-- Plain linear reasoning from hypotheses. -/
theorem lin (x y : ℝ) (h₁ : x + y ≤ 3) (h₂ : x - y ≤ 1) : x ≤ 2 := by
  linarith

/-- AM–GM in two variables via `nlinarith` with a square hint. -/
theorem am_gm (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- A norm-squared (sum of four squares) is non-negative. -/
theorem normSq_nonneg (a b c d : ℝ) : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  positivity

/-- Strict positivity with a hypothesis. -/
theorem pos_of (x : ℝ) (hx : 0 < x) : 0 < x ^ 3 + 2 * x := by
  positivity

/-- `nlinarith` closing a product-sign goal from two hypotheses. -/
theorem prod_pos (x y : ℝ) (hx : 1 < x) (hy : 1 < y) : 1 < x * y := by
  nlinarith

end QBPToolcheck.T06

#print axioms QBPToolcheck.T06.lin
#print axioms QBPToolcheck.T06.am_gm
#print axioms QBPToolcheck.T06.normSq_nonneg
#print axioms QBPToolcheck.T06.pos_of
#print axioms QBPToolcheck.T06.prod_pos
