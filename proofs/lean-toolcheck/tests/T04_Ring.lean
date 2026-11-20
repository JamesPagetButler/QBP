/-
TOOLCHECK T04 — `ring` / `ring_nf` normalisation in commutative (semi)rings: ℝ, ℤ, ℚ,
and a generic `[CommRing R]`.

Feature: `ring` closes commutative-ring identities; `ring_nf` normalises both sides
(QBP uses it to expose a normal form before `linarith`/`simp`). The *associativity and
commutativity of the carrier* is what makes `ring` valid — so it must NOT be used on the
octonion/sedenion products themselves (non-associative), only on their real coordinates.

Used by (QBP, 2026-11-20 grep, 32 files for `ring`, 6 for `ring_nf`): `QBP/Substrate/RuleFlow.lean`,
`QBP/Foundations/CrystalHosting.lean`, `NoAutonomousDynamics.lean`, `Exp.lean`;
`ring_nf`: `OctonionLaws.lean`, `Alternator.lean`, `QBP/Experiments/General3D.lean`,
`AngleDependent.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs

namespace QBPToolcheck.T04

/-- The Brahmagupta–Fibonacci (two-square) identity: the composition law behind ℂ's norm. -/
theorem two_square (a b c d : ℝ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- Euler's four-square identity (ℍ's norm is multiplicative), over a generic `CommRing`. -/
theorem four_square {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2 + b₄ ^ 2) =
      (a₁ * b₁ - a₂ * b₂ - a₃ * b₃ - a₄ * b₄) ^ 2 + (a₁ * b₂ + a₂ * b₁ + a₃ * b₄ - a₄ * b₃) ^ 2 +
        (a₁ * b₃ - a₂ * b₄ + a₃ * b₁ + a₄ * b₂) ^ 2 + (a₁ * b₄ + a₂ * b₃ - a₃ * b₂ + a₄ * b₁) ^ 2 := by
  ring

/-- Signed integer arithmetic (`ℤ`, not `ℕ`: the Nat-truncation trap, standard §7). -/
theorem int_signed (x : ℤ) : (x - 2) * (x + 2) = x ^ 2 - 4 := by ring

/-- `ring` over ℚ with division by a numeral (a field, so `/ 2` is fine). -/
theorem rat_half (q : ℚ) : q / 2 + q / 2 = q := by ring

/-- `ring_nf` used to normalise a hypothesis before closing the goal. -/
theorem ring_nf_hyp (x y : ℝ) (h : (x + y) ^ 2 - (x - y) ^ 2 = 8) : x * y = 2 := by
  ring_nf at h
  linarith

end QBPToolcheck.T04

#print axioms QBPToolcheck.T04.two_square
#print axioms QBPToolcheck.T04.four_square
#print axioms QBPToolcheck.T04.int_signed
#print axioms QBPToolcheck.T04.rat_half
#print axioms QBPToolcheck.T04.ring_nf_hyp
