/-
TOOLCHECK T05 — `field_simp` with explicit `≠ 0` side hypotheses, then `ring`.

Feature: `field_simp` clears denominators in a field given the hypotheses that they are
non-zero (federation standard §8: Lean's `x / 0 = 0` makes a missing `≠ 0` hypothesis a
source of spurious "solutions", so the hypotheses are carried explicitly).

Used by (QBP, 2026-11-20 grep, 10 files): `QBP/Foundations/Exp.lean`,
`QBP/Cosmo/RedshiftEvolution.lean`, `QBP/Optics/Fraunhofer.lean`,
`QBP/Foundations/SpectralMoments.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

namespace QBPToolcheck.T05

/-- Sum of reciprocals, denominators carried as hypotheses. -/
theorem recip_sum (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp
  ring

/-- The quaternion-inverse shape: `x · (x̄ / |x|²) = 1` in coordinates, for `|x|² ≠ 0`. -/
theorem inv_norm (n : ℝ) (hn : n ≠ 0) : n * (1 / n) = 1 := by
  field_simp

/-- A redshift-style ratio identity `(1+z)·(a/(1+z)) = a` with `1 + z ≠ 0`. -/
theorem redshift_ratio (a z : ℝ) (hz : 1 + z ≠ 0) : (1 + z) * (a / (1 + z)) = a := by
  field_simp

end QBPToolcheck.T05

#print axioms QBPToolcheck.T05.recip_sum
#print axioms QBPToolcheck.T05.inv_norm
#print axioms QBPToolcheck.T05.redshift_ratio
