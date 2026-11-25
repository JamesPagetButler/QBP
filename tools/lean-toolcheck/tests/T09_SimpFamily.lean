/-
TOOLCHECK T09 — the `simp` family: terminal `simp [lemmas]`, `simp only [...]`,
`simpa … using`, `simp … at h ⊢`, `simp_rw`, `dsimp only`, user `@[simp]` lemmas,
and `scoped` simp sets opened with `open scoped … in`. (`attribute [local simp]` moved to
T20: the `attribute` command is outside the pass-file subset, Red Team r2 on PR #824.)

Feature: rewriting with lemma sets. The simp-set *contents* are the most migration-
sensitive thing QBP relies on: PR #491 (the v4.30.0-rc2 → v4.30.0 bump) broke `qJ_sq`
(`QBP/Experiments/DoubleSlit.lean`, then l.68) through a `@[scoped simp]` change, and
v4.31.0's transparency/defeq work changes what `simp`/`dsimp` unfold. This file pins the
shapes QBP uses so a simp-set or transparency change shows up here first.

Used by (QBP, 2026-11-20 grep): `simp only` 33 files — `QBP/Foundations/OctonionLaws.lean`,
`Exp.lean`, `QBP/Substrate/RuleFlow.lean`, `CDAlg.lean`; bare `simp` 39 files; `simpa`
17 files — `CDLifting.lean`, `RuleFlow.lean`, `HolographicSubalgebra.lean`; `simp_rw` —
`Alternator.lean`; `@[simp]` 17 files — `CrystalHosting.lean`, `CDAlg.lean`,
`LocaleDynamics.lean`; `scoped` 11 files — `Exp.lean` (`open scoped Quaternion in`),
`RuleFlow.lean`; the `Quaternion.re_mul`/`imI_mul`… simp set: `DoubleSlit.lean` `qJ_sq`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace QBPToolcheck.T09

/-- A tiny structure with its own simp lemmas (QBP's `CDAlg.coord_add` shape). -/
structure P2 where
  x : ℤ
  y : ℤ

/-- Componentwise addition. -/
def P2.add (p q : P2) : P2 := ⟨p.x + q.x, p.y + q.y⟩

@[simp] theorem P2.add_x (p q : P2) : (p.add q).x = p.x + q.x := rfl
@[simp] theorem P2.add_y (p q : P2) : (p.add q).y = p.y + q.y := rfl

/-- Terminal `simp` using user `@[simp]` lemmas. -/
theorem add_x_comm (p q : P2) : (p.add q).x = (q.add p).x := by
  simp [Int.add_comm]

/-- `simp only` with an explicit lemma list (the federation-preferred form, §10). -/
theorem add_y_only (p q : P2) : (p.add q).y = p.y + q.y := by
  simp only [P2.add_y]

/-- `simpa … using` on a hypothesis. -/
theorem simpa_using (p q : P2) (h : (p.add q).x = 0) : p.x + q.x = 0 := by
  simpa using h

/-- `simp … at h ⊢`. -/
theorem simp_at (p q : P2) (h : (p.add q).y = 5) : p.y + q.y = 5 := by
  simp at h ⊢
  exact h

/-- `simp_rw` under a binder. -/
theorem simp_rw_binder (f : ℕ → P2) : (∀ n, ((f n).add (f n)).x = 2 * (f n).x) := by
  simp_rw [P2.add_x]
  intro n
  ring

/-- `dsimp only` unfolding a definition by `rfl`-lemma. -/
theorem dsimp_def (p q : P2) : (p.add q).x = p.x + q.x := by
  dsimp only [P2.add]

/-- A scoped simp lemma inside a namespace. -/
@[scoped simp] theorem neg_neg' (a : ℤ) : - -a = a := Int.neg_neg a

open scoped QBPToolcheck.T09 in
theorem scoped_simp_use (a : ℤ) : - -a + 0 = a := by simp

/-- The `qJ_sq` shape (DoubleSlit.lean): `j * j = -1` in `ℍ[ℝ]` by `ext <;> simp […]`
with Mathlib's `Quaternion.re_mul`/`imI_mul`/… simp set. -/
theorem qJ_sq : (⟨0, 0, 1, 0⟩ : Quaternion ℝ) * ⟨0, 0, 1, 0⟩ = -(1 : Quaternion ℝ) := by
  ext <;> simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_one, Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]

end QBPToolcheck.T09

#print axioms QBPToolcheck.T09.add_x_comm
#print axioms QBPToolcheck.T09.add_y_only
#print axioms QBPToolcheck.T09.simpa_using
#print axioms QBPToolcheck.T09.simp_at
#print axioms QBPToolcheck.T09.simp_rw_binder
#print axioms QBPToolcheck.T09.dsimp_def
#print axioms QBPToolcheck.T09.scoped_simp_use
#print axioms QBPToolcheck.T09.qJ_sq
