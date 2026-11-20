/-
TOOLCHECK T08 — the `module` tactic (linear-combination normalisation in a module over a
commutative ring), `linear_combination` (goal = Σ cᵢ·hᵢ, checked by `ring`), and `abel`
(additive commutative groups).

Feature: `module` proves equalities of `R`-linear combinations of vectors (`a • x + …`)
by normalising scalars with `ring`; QBP uses it in coordinate modules such as
`CDAlg R n` where there is no ring structure on the vectors that `ring` could use.
`linear_combination e₁ * h₁ + …` closes a ring equation from hypothesis equations.
`abel` normalises sums/differences in an `AddCommGroup`.

Used by (QBP, 2026-11-20 grep): `module` 16 files — `QBP/Foundations/CrystalHosting.lean`,
`QBP/Substrate/RuleFlow.lean`, `QBP/Foundations/InFlightAlgebra.lean`,
`NoAutonomousDynamics.lean`, `QBP/Substrate/Hosting.lean`; `linear_combination` 10 files —
`QBP/Substrate/RuleFlowInvariants.lean`, `CrystalHosting.lean`, `DeltaLandscape.lean`,
`LeftMulDet.lean`; `abel` 16 files — `OctonionLaws.lean`, `CDLifting.lean`, `Alternator.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Data.Real.Basic

namespace QBPToolcheck.T08

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Collecting scalars on a common vector. -/
theorem module_collect (a b : ℝ) (x : V) : a • x + b • x = (a + b) • x := by
  module

/-- A two-vector linear combination with subtraction and nested scalars. -/
theorem module_two (a b : ℝ) (x y : V) :
    a • (x + y) - b • (x - y) = (a - b) • x + (a + b) • y := by
  module

/-- `rw` a vector hypothesis, then `module` (QBP's `rw [ha]; module` shape). -/
theorem module_after_rw (a : ℝ) (x y z : V) (h : z = x + (2 : ℝ) • y) :
    a • z - a • x = (2 * a) • y := by
  rw [h]
  module

/-- `linear_combination` from two hypotheses. -/
theorem lincomb (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  linear_combination (h₁ + h₂) / 2

/-- `abel` in an additive commutative group. -/
theorem abel_rearrange (x y z : V) : (x + y) - (z - x) + z = 2 • x + y := by
  abel

end QBPToolcheck.T08

#print axioms QBPToolcheck.T08.module_collect
#print axioms QBPToolcheck.T08.module_two
#print axioms QBPToolcheck.T08.module_after_rw
#print axioms QBPToolcheck.T08.lincomb
#print axioms QBPToolcheck.T08.abel_rearrange
