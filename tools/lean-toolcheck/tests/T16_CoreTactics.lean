/-
TOOLCHECK T16 — core (Lean / Batteries-level) tactics and declarations QBP relies on:
`omega`, `rcases`/`obtain`/`rintro` patterns, `induction … with`, `constructor`,
`refine ⟨_, ?_⟩`, `calc`, `unfold`, `show`/`change`, `funext`, `split_ifs`, `by_contra`,
`exact absurd`, `noncomputable def`, `structure`, `open … in`,
`namespace`/`section`/`variable`. (`local notation` moved to T20: syntax extension is
outside the pass-file subset, Red Team r2 on PR #824.)

Used by (QBP, 2026-11-20 grep): `omega` 11 files — `QBP/Foundations/OctonionAutBranching.lean`,
`CDAlg.lean`, `TransitionState.lean`; `rcases`/`obtain` 26 files — `NoAutonomousDynamics.lean`,
`CrystalHosting.lean`, `ArtinCore.lean`, `LocaleDynamics.lean`; `induction` 13 files —
`CDLifting.lean`, `G2Transitivity.lean`, `FanoGenesis.lean`; `calc` 10 files; `unfold`
24 files — `QBP/Experiments/DoubleSlit.lean`, `QBP/Optics/Fraunhofer.lean`; `show`/`change`
20 files; `constructor` 20 files; `split_ifs`/`if` 24 files; `noncomputable` 28 files;
`notation` 5 files.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QBPToolcheck.T16

/-- `omega` on `ℕ`/`ℤ`/`Fin` index bounds (QBP's `⟨i, by omega⟩` shape). -/
theorem omega_idx (i : ℕ) (h : i < 4) : 2 * i + 1 < 9 := by omega

theorem omega_int (a b : ℤ) (h₁ : a - b = 3) (h₂ : a + b = 7) : a = 5 := by omega

/-- A `Fin` index built with an `omega` bound. -/
def idx (i : Fin 4) : Fin 8 := ⟨2 * i.val, by omega⟩

/-- `rcases`/`obtain` on existentials and disjunctions; `rintro` patterns. -/
theorem rcases_use (P Q : ℕ → Prop) (h : ∃ n, P n ∨ Q n) : ∃ n, Q n ∨ P n := by
  obtain ⟨n, hp | hq⟩ := h
  · exact ⟨n, Or.inr hp⟩
  · exact ⟨n, Or.inl hq⟩

theorem rintro_use : ∀ p : ℕ × ℕ, p.1 = p.2 → p.2 = p.1 := by
  rintro ⟨a, b⟩ h
  exact h.symm

/-- `induction … with` on `ℕ`. -/
theorem sum_formula (n : ℕ) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.sum_append, List.sum_singleton, mul_add, ih]
    ring

/-- `constructor` / `refine ⟨_, ?_⟩`. -/
theorem and_build (x : ℝ) (hx : 0 < x) : 0 < x ∧ x ≠ 0 := by
  constructor
  · exact hx
  · exact ne_of_gt hx

/-- `calc` chain. -/
theorem calc_chain (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c + 1 :=
  calc a ≤ b := h₁
    _ < c := h₂
    _ < c + 1 := by linarith

/-- A `noncomputable def` over ℝ with `unfold` / `show` / `change`. -/
noncomputable def sq (x : ℝ) : ℝ := x * x

theorem sq_unfold (x : ℝ) : sq x = x ^ 2 := by
  unfold sq
  ring

theorem sq_change (x : ℝ) : sq (-x) = sq x := by
  change (-x) * (-x) = x * x
  ring

/-- `split_ifs` on an `if`. -/
def clampZ (z : ℤ) : ℤ := if z < 0 then 0 else z

theorem clampZ_nonneg (z : ℤ) : 0 ≤ clampZ z := by
  unfold clampZ
  split_ifs with h
  · exact le_refl 0
  · omega

/-- `by_contra` + `absurd`. -/
theorem by_contra_use (n : ℕ) (h : n ≠ 0) : 0 < n := by
  by_contra hn
  exact absurd (Nat.eq_zero_of_not_pos hn) h

/-- A `structure` with a field-projection lemma. -/
structure Pair where
  fst : ℤ
  snd : ℤ

/-- Swap. -/
def Pair.swap (p : Pair) : Pair := ⟨p.snd, p.fst⟩

theorem swap_swap (p : Pair) : p.swap.swap = p := by
  cases p
  rfl

/-- `funext` on functions. -/
theorem funext_use : (fun x : ℕ => x + 0) = (fun x => x) := by
  funext x
  rfl

end QBPToolcheck.T16

#print axioms QBPToolcheck.T16.omega_idx
#print axioms QBPToolcheck.T16.omega_int
#print axioms QBPToolcheck.T16.rcases_use
#print axioms QBPToolcheck.T16.rintro_use
#print axioms QBPToolcheck.T16.sum_formula
#print axioms QBPToolcheck.T16.and_build
#print axioms QBPToolcheck.T16.calc_chain
#print axioms QBPToolcheck.T16.sq_unfold
#print axioms QBPToolcheck.T16.sq_change
#print axioms QBPToolcheck.T16.clampZ_nonneg
#print axioms QBPToolcheck.T16.by_contra_use
#print axioms QBPToolcheck.T16.swap_swap
#print axioms QBPToolcheck.T16.funext_use
