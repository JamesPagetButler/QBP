import QBP.Foundations.Alternator
import QBP.Foundations.CrossProduct

/-!
# QBP.Foundations.NoAutonomousDynamics — Prop 16 of the #473 AC1 ladder

**Research-thread evidence for #473 AC1 v0.4 (PR #631), Proposition 16**
(`docs/foundations/473-ac1-first-link-2026-09-04.md`): *the algebra generates
symmetries, never dynamics toward the vacuum.*  This file is ordinary `QBP.Foundations` material —
pure `CDAlg`/ℝ algebra with no substrate semantics.  Per Prop 2 (Lean policy) it
does **NOT** open `proofs/QBP/Substrate/`, and nothing here authorises such a file.

## What is proved

**Prop 16(i) — every word in one imaginary element lies in `span{1, s}`.**
`GenBy s` is the smallest set containing `1` and `s` and closed under addition,
real scaling, the Cayley–Dickson product and conjugation.  `genBy_mem_span` shows
`GenBy s x → ∃ a b : ℝ, x = a • 1 + b • s` for every imaginary `s` at every level
of the tower.  The engine is the Cayley–Dickson square identity in its imaginary
form `s·s = −N(s)·1` (`CDAlg.imaginary_sq`), so **no normalisation is needed**: the
`N s = 1` hypothesis of the doc's informal statement is dropped and `N s` is
carried through the product case instead (the statement below is strictly more
general than the doc's).  `genBy_unit_imag_eq` is the doc's corollary: with
`N s = 1`, an *imaginary unit* in that span is exactly `±s`.

**Prop 16(ii) — `{1, s, ℓ}` generates a quaternion subalgebra of 𝕊.**
`ℓ := e₈ = e (hiIdx 0)` is the Cayley–Dickson doubling unit of `𝕊 = 𝕆 ⊕ 𝕆ℓ`.
For imaginary `s : CDAlg ℝ 4` put `p := s − s₈·ℓ` (the component of `s` orthogonal
to `ℓ`; `p` is imaginary with `p₈ = 0`).  Then `ℍ_s := span{1, ℓ, p, ℓp}` is closed
under multiplication (`quatSpan_mul_closed`) and conjugation
(`quatSpan_conj_closed`), and every word in `{1, s, ℓ}` lies in it
(`genByPair_ell_mem_quatSpan`).  The multiplication table proved here,

    ℓ² = −1,   p² = −N(p)·1,   (ℓp)² = −N(p)·1,
    pℓ = −ℓp,  ℓ(ℓp) = −p,     (ℓp)ℓ = p,
    p(ℓp) = N(p)·ℓ,            (ℓp)p = −N(p)·ℓ,

is the quaternion table with `i = ℓ`, `j = p/|p|`, `k = ℓp/|p|` — even though 𝕊 is
neither associative nor alternative.  The two genuinely non-obvious rows,
`p(ℓp)` and `(ℓp)p`, come from `assoc_self_ell` (`[x, x, ℓ] = 0` for **every**
sedenion `x`, a 64-case kernel `decide` on `laCoeffZ`) together with the
orthogonality `⟨p, ℓp⟩ = 0`.

Also proved: the Cayley–Dickson coordinate form of the `ℓ`-commutator,
`[s, ℓ] = −2·Im(cdHi s) + 2·Im(cdLo s)·ℓ` (`cdLo_ell_commutator` /
`cdHi_ell_commutator`), i.e. the doc's `[s, ℓ] = −2c + 2aℓ`.

## Numerical counterpart

`analysis/473-dirac-probe/lmaps_check.py` — check (1) "dim span{1,ℓ,p,ℓp} = {4};
closure residual 1e−15".  That script is a numerical flashlight; the theorems below
are what it was pointing at.  (The script's checks (2)–(4) — the shape invariant
`σ = V/(1−b₀²)²` and the attracting map `(s+ℓ)/‖s+ℓ‖` — are *not* formalised here.)

## Scope caveat (read before citing this file)

`GenBy` / `GenByPair` close under `+`, real scaling, `·` and conjugation and
**nothing else**.  Normalisation `x ↦ x/‖x‖` is NOT an algebra operation and is NOT
in these closures, so nothing here contradicts — or addresses — the PR #631 round-3
counter-example `s ↦ (s + ℓ)/‖s + ℓ‖`, which has infinite order and attracts to `ℓ`.
What is proved is the invariant-subspace half of Prop 16(ii): the algebra's own
operations never leave `ℍ_s`.  The "only `±ℓ` are reachable" half of the doc's Prop
16(ii) rests on the shape invariant `σ`, which is not formalised here.

## Completeness

Third layer (NOT formalised; `analysis/473-dirac-probe/generic_maps_check.py`, Red Team round-4 confirmer):
  with an UNFORCED second element t, the maps x ↦ x·t, t·x, [x,t] are linear and skew (R_t, L_t, ad_t);
  their normalised iteration is power iteration onto the top-singular plane — which lies on the zero-divisor
  ridge V = 1 — followed by a period-2 symmetry. Σσ²(R_t) = 16·N(t), so the dominant plane exists exactly
  because the norm is not multiplicative at dim 16; for ℓ, R_ℓ is orthogonal (`N_ell_mul`) and no transient
  exists. So: no autonomous algebraic dynamics toward the vacuum; the only non-symmetric behaviour is a
  linear transient onto the zero-divisor locus.

Zero `sorry`, zero `native_decide`, zero vacuous `True`.  `#print axioms` audit at
the bottom: every result depends only on `{propext, Classical.choice, Quot.sound}`.
-/

namespace QBP.Foundations.NoAutonomousDynamics

open QBP.Foundations.CDAlg

/-! ## 0. Generic helpers (conjugation, negation, single-basis coordinate reads) -/

section Helpers

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Conjugation fixes the unit. -/
@[simp] theorem conj_one : conj (1 : CDAlg R n) = 1 := by
  ext i
  simp only [conj_coord, one_coord]
  by_cases h : i = 0
  · subst h; simp
  · have hv : i.val ≠ 0 := fun hh => h (Fin.ext hh)
    rw [if_neg hv, if_neg h, neg_zero]

/-- Conjugation is additive. -/
theorem conj_add (x y : CDAlg R n) : conj (x + y) = conj x + conj y := by
  ext i; simp only [conj_coord, add_coord]; split_ifs <;> ring

/-- Conjugation is `R`-homogeneous. -/
theorem conj_smul (r : R) (x : CDAlg R n) : conj (r • x) = r • conj x := by
  ext i; simp only [conj_coord, smul_coord]; split_ifs <;> ring

/-- On an IMAGINARY element conjugation is negation. -/
theorem conj_of_imaginary {x : CDAlg R n} (hx : x.coord 0 = 0) : conj x = -x := by
  ext i
  simp only [conj_coord, neg_coord]
  by_cases h : i.val = 0
  · have hi : i = 0 := Fin.ext h
    rw [if_pos h, hi, hx, neg_zero]
  · rw [if_neg h]

/-- `x·(−y) = −(x·y)` (bilinearity). -/
theorem cd_mul_neg_right (x y : CDAlg R n) : x * (-y) = -(x * y) := by
  have h := mul_smul_right (-1 : R) x y
  rwa [neg_one_smul, neg_one_smul] at h

/-- `(−x)·y = −(x·y)` (bilinearity). -/
theorem cd_neg_mul_left (x y : CDAlg R n) : (-x) * y = -(x * y) := by
  have h := mul_smul_left (-1 : R) x y
  rwa [neg_one_smul, neg_one_smul] at h

/-- `m ⊕ (m ⊕ k) = k`. -/
theorem xor_cancel_left (m k : Fin (2^n)) : (m ^^^ (m ^^^ k)) = k := by
  rw [← xor_assoc_fin, xor_self_eq, xor_zero_left]

/-- **Left multiplication by a basis vector, coordinatewise.**
    `(e_m · x)_k = mulCoeff n m (m ⊕ k) · x_{m ⊕ k}` — left multiplication by a
    basis vector is a signed permutation of coordinates. -/
theorem e_mul_coord (m : Fin (2^n)) (x : CDAlg R n) (k : Fin (2^n)) :
    (e m * x).coord k = (mulCoeff n m (m ^^^ k) : R) * x.coord (m ^^^ k) := by
  rw [mul_coord_matrix, Finset.sum_eq_single (m ^^^ k)]
  · rw [xor_xor_cancel m k, e_coord, if_pos rfl, mul_one]
  · intro b _ hb
    have hne : (b ^^^ k) ≠ m := by
      intro h
      apply hb
      rw [← xor_xor_cancel b k, h]
    rw [e_coord, if_neg hne, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Right multiplication by a basis vector, coordinatewise.**
    `(x · e_m)_k = mulCoeff n (m ⊕ k) m · x_{m ⊕ k}`. -/
theorem mul_e_coord (x : CDAlg R n) (m k : Fin (2^n)) :
    (x * e m).coord k = (mulCoeff n (m ^^^ k) m : R) * x.coord (m ^^^ k) := by
  rw [mul_coord_single, Finset.sum_eq_single (m ^^^ k)]
  · rw [xor_xor_cancel m k, e_coord, if_pos rfl, mul_one]
  · intro b _ hb
    have hne : (b ^^^ k) ≠ m := by
      intro h
      apply hb
      rw [← xor_xor_cancel b k, h]
    rw [e_coord, if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `⟨x, e_m⟩ = x_m`. -/
theorem bil_e_right (x : CDAlg R n) (m : Fin (2^n)) : bil x (e m) = x.coord m := by
  rw [bil_def, Finset.sum_eq_single m]
  · rw [e_coord, if_pos rfl, mul_one]
  · intro b _ hb; rw [e_coord, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Every basis vector is a unit for the norm form. -/
theorem N_e (m : Fin (2^n)) : N (e m : CDAlg ℝ n) = 1 := by
  rw [N_def, Finset.sum_eq_single m]
  · rw [e_coord, if_pos rfl]; norm_num
  · intro b _ hb; rw [e_coord, if_neg hb]; norm_num
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The norm form is quadratic-homogeneous: `N (r • x) = r² · N x`. -/
theorem N_smul (r : ℝ) (x : CDAlg ℝ n) : N (r • x) = r^2 * N x := by
  simp only [N_def, smul_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

end Helpers

/-! ## 1. Prop 16(i) — words in ONE imaginary element lie in `span{1, s}` -/

/-- `GenBy s` — the sub-structure generated by `{1, s}`: the smallest predicate
    containing `1` and `s` and closed under addition, real scaling, the
    Cayley–Dickson product and conjugation.  (Negation is derivable, see
    `GenBy.neg`; subtraction follows from `add` + `neg`.) -/
inductive GenBy {n : ℕ} (s : CDAlg ℝ n) : CDAlg ℝ n → Prop
  | one : GenBy s 1
  | self : GenBy s s
  | add {x y} : GenBy s x → GenBy s y → GenBy s (x + y)
  | smul (r : ℝ) {x} : GenBy s x → GenBy s (r • x)
  | mul {x y} : GenBy s x → GenBy s y → GenBy s (x * y)
  | conj {x} : GenBy s x → GenBy s (QBP.Foundations.CDAlg.conj x)

/-- Negation is derivable from `smul (-1)`. -/
theorem GenBy.neg {n : ℕ} {s x : CDAlg ℝ n} (h : GenBy s x) : GenBy s (-x) := by
  have h1 := GenBy.smul (-1 : ℝ) h
  rwa [neg_one_smul] at h1

/-- **Prop 16(i).**  For an IMAGINARY `s` (`s.coord 0 = 0`) at any level `n` of the
    Cayley–Dickson tower, every element generated from `{1, s}` by `+`, real
    scaling, `·` and conjugation lies in the real span of `{1, s}`.

    No normalisation is assumed: the product case carries `N s` (via
    `s·s = −N(s)·1`), so the statement holds for every imaginary `s`, not only
    unit ones.  The generated object is therefore a *commutative, associative*
    2-dimensional subalgebra — ℂ when `N s > 0` — at every level, sedenions
    included. -/
theorem genBy_mem_span {n : ℕ} (s : CDAlg ℝ n) (hs : s.coord 0 = 0) :
    ∀ x, GenBy s x → ∃ a b : ℝ, x = a • (1 : CDAlg ℝ n) + b • s := by
  intro x hx
  induction hx with
  | one => exact ⟨1, 0, by module⟩
  | self => exact ⟨0, 1, by module⟩
  | add _ _ ih1 ih2 =>
      obtain ⟨a1, b1, h1⟩ := ih1
      obtain ⟨a2, b2, h2⟩ := ih2
      exact ⟨a1 + a2, b1 + b2, by rw [h1, h2]; module⟩
  | smul r _ ih =>
      obtain ⟨a, b, h⟩ := ih
      exact ⟨r * a, r * b, by rw [h]; module⟩
  | mul _ _ ih1 ih2 =>
      obtain ⟨a1, b1, h1⟩ := ih1
      obtain ⟨a2, b2, h2⟩ := ih2
      refine ⟨a1 * a2 - b1 * b2 * N s, a1 * b2 + b1 * a2, ?_⟩
      rw [h1, h2]
      simp only [mul_add_left, mul_add_right, mul_smul_left, mul_smul_right,
        cd_one_mul, cd_mul_one]
      rw [imaginary_sq s hs]
      module
  | conj _ ih =>
      obtain ⟨a, b, h⟩ := ih
      refine ⟨a, -b, ?_⟩
      rw [h, conj_add, conj_smul, conj_smul, conj_one, conj_of_imaginary hs]
      module

/-- **Prop 16(i), the doc's corollary.**  For a unit imaginary `s`, the only unit
    imaginary elements generated by `{1, s}` are `s` and `−s`: one-element
    algebraic words can flip a sign, and nothing else. -/
theorem genBy_unit_imag_eq {n : ℕ} (s : CDAlg ℝ n) (hs : s.coord 0 = 0) (hNs : N s = 1)
    (x : CDAlg ℝ n) (hx : GenBy s x) (hx0 : x.coord 0 = 0) (hNx : N x = 1) :
    x = s ∨ x = -s := by
  obtain ⟨a, b, h⟩ := genBy_mem_span s hs x hx
  have hc : x.coord 0 = a * (1 : CDAlg ℝ n).coord 0 + b * s.coord 0 := by
    rw [h]; simp only [add_coord, smul_coord]
  rw [one_coord, if_pos rfl, hs, hx0] at hc
  have ha : a = 0 := by linarith
  rw [ha, zero_smul, zero_add] at h
  have hb : b^2 = 1 := by
    have hn : N x = b^2 * N s := by rw [h, N_smul]
    rw [hNx, hNs, mul_one] at hn
    linarith
  have hfac : (b - 1) * (b + 1) = 0 := by nlinarith [hb]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left; rw [h, show b = 1 by linarith, one_smul]
  · right; rw [h, show b = -1 by linarith, neg_one_smul]

/-! ## 2. Prop 16(ii) — the doubling unit `ℓ` and its multiplication table

`ℓ := e₈ = e (hiIdx 0)` is the Cayley–Dickson doubling unit of `𝕊 = 𝕆 ⊕ 𝕆ℓ`.
Everything in this section is at level `n = 4` (the sedenions). -/

/-- The Cayley–Dickson doubling unit `ℓ = e₈` of `𝕊 = 𝕆 ⊕ 𝕆ℓ`. -/
def ell : CDAlg ℝ 4 := e (hiIdx 0)

theorem ell_coord_zero : ell.coord 0 = 0 := by
  rw [ell, e_coord, if_neg (by decide : ¬((0 : Fin (2^4)) = hiIdx 0))]

theorem ell_coord_hiIdx_zero : ell.coord (hiIdx 0) = 1 := by
  rw [ell, e_coord, if_pos rfl]

theorem N_ell : N ell = 1 := N_e _

/-! ### Kernel-`decide`d integer facts about `mulCoeff 4` at the index `8` -/

/-- `ℓ·ℓ` has coefficient `−1`. -/
theorem mulCoeff_ell_ell : mulCoeff 4 (hiIdx 0) (hiIdx 0) = -1 := by decide

/-- The `L_ℓ ∘ L_ℓ = −id` coefficient identity. -/
theorem mulCoeff_ell_left_sq : ∀ k : Fin (2^4),
    mulCoeff 4 (hiIdx 0) (hiIdx 0 ^^^ k) * mulCoeff 4 (hiIdx 0) k = -1 := by decide

/-- The `R_ℓ ∘ R_ℓ = −id` coefficient identity. -/
theorem mulCoeff_ell_right_sq : ∀ k : Fin (2^4),
    mulCoeff 4 (hiIdx 0 ^^^ k) (hiIdx 0) * mulCoeff 4 k (hiIdx 0) = -1 := by decide

/-- The `R_ℓ ∘ L_ℓ = id` coefficient identity — valid exactly off the two
    coordinates `0` and `8` (on those two it is `−1`, which is why the
    `ℓ`-conjugation law below needs `x₀ = x₈ = 0`). -/
theorem mulCoeff_ell_conj : ∀ k : Fin (2^4), k ≠ 0 → k ≠ hiIdx 0 →
    mulCoeff 4 (hiIdx 0 ^^^ k) (hiIdx 0) * mulCoeff 4 (hiIdx 0) k = 1 := by decide

/-- `L_ℓ` is a signed permutation: every coefficient squares to `1`. -/
theorem mulCoeff_ell_sq_one : ∀ k : Fin (2^4),
    mulCoeff 4 (hiIdx 0) k * mulCoeff 4 (hiIdx 0) k = 1 := by decide

/-- **`[x, x, ℓ] = 0` for every sedenion, at the coefficient level** (64 cases).
    The polarized left alternator of a low-half/high-half basis pair kills `ℓ`. -/
theorem laCoeffZ_lo_hi_ell : ∀ p q : Fin (2^3),
    laCoeffZ 4 (loIdx p) (hiIdx q) (hiIdx 0) = 0 := by decide

/-- Real cast of an integer `mulCoeff` product identity. -/
private theorem cast_two (u v : Int) (c : Int) (h : u * v = c) :
    ((u : ℝ)) * ((v : ℝ)) = (c : ℝ) := by
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2
  exact h2

/-! ### The `ℓ`-linear laws (true for EVERY sedenion `x`) -/

/-- `ℓ² = −1`. -/
theorem ell_sq : ell * ell = -(1 : CDAlg ℝ 4) := by
  rw [ell, e_mul_e, xor_self_eq, mulCoeff_ell_ell, ← one_def]
  push_cast
  module

/-- **`ℓ·(ℓ·x) = −x` for every sedenion `x`.**  (`L_ℓ² = −id`.) -/
theorem ell_ell_mul (x : CDAlg ℝ 4) : ell * (ell * x) = -x := by
  ext k
  rw [ell, e_mul_coord, e_mul_coord, xor_cancel_left, neg_coord, ← mul_assoc,
    cast_two _ _ _ (mulCoeff_ell_left_sq k)]
  push_cast
  ring

/-- **`(x·ℓ)·ℓ = −x` for every sedenion `x`.**  (`R_ℓ² = −id`.) -/
theorem mul_ell_ell (x : CDAlg ℝ 4) : (x * ell) * ell = -x := by
  ext k
  rw [ell, mul_e_coord, mul_e_coord, xor_cancel_left, neg_coord, ← mul_assoc,
    cast_two _ _ _ (mulCoeff_ell_right_sq k)]
  push_cast
  ring

/-- **`(ℓ·x)·ℓ = x`** for `x` orthogonal to both `1` and `ℓ`.  (On the two
    coordinates `0` and `8` the map is `−id` instead, so the hypotheses are
    exactly right, not decorative.) -/
theorem ell_mul_ell {x : CDAlg ℝ 4} (h0 : x.coord 0 = 0) (h8 : x.coord (hiIdx 0) = 0) :
    (ell * x) * ell = x := by
  ext k
  rw [ell, mul_e_coord, e_mul_coord, xor_cancel_left, ← mul_assoc]
  by_cases hk0 : k = 0
  · rw [hk0, h0, mul_zero]
  · by_cases hk8 : k = hiIdx 0
    · rw [hk8, h8, mul_zero]
    · rw [cast_two _ _ _ (mulCoeff_ell_conj k hk0 hk8)]
      push_cast
      ring

/-- `ℓ·x` is imaginary whenever `x₈ = 0`. -/
theorem ell_mul_imaginary {x : CDAlg ℝ 4} (h8 : x.coord (hiIdx 0) = 0) :
    (ell * x).coord 0 = 0 := by
  rw [ell, e_mul_coord, xor_zero_right, h8, mul_zero]

/-- **`L_ℓ` preserves the norm form:** `N (ℓ·x) = N x`. -/
theorem N_ell_mul (x : CDAlg ℝ 4) : N (ell * x) = N x := by
  have hsq : ∀ m : Fin (2^4), ((mulCoeff 4 (hiIdx 0) m : ℝ))^2 = 1 := by
    intro m
    have h2 := cast_two _ _ _ (mulCoeff_ell_sq_one m)
    push_cast at h2
    rw [pow_two]
    exact h2
  have hterm : ∀ k : Fin (2^4), ((ell * x).coord k)^2 = (x.coord (k ^^^ hiIdx 0))^2 := by
    intro k
    rw [ell, e_mul_coord, xor_comm_fin (hiIdx 0) k, mul_pow, hsq, one_mul]
  rw [N_def, N_def, Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
  exact (sum_xor_reindex (hiIdx 0) (fun i => (x.coord i)^2)).symm

/-! ### `[x, x, ℓ] = 0` for every sedenion -/

/-- The polarized left alternator of a Cayley–Dickson cross pair annihilates `ℓ`. -/
theorem laMap_loOf_hiOf_ell (a c : CDAlg ℝ 3) : laMap (loOf a) (hiOf c) ell = 0 := by
  rw [loOf, hiOf, ell, laMap_expand_sums]
  refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun q _ => ?_))
  rw [laMap_e, laCoeffZ_lo_hi_ell]
  simp

/-- **`[x, x, ℓ] = 0` for EVERY sedenion `x`.**  The left alternator of the
    sedenions is nonzero in general (`CDAlg.sedWitX_alternator_ne_zero`), but it
    always vanishes on the doubling unit `ℓ`.  This is what makes the
    `{1, ℓ, p, ℓp}` table below close despite 𝕊 being non-alternative. -/
theorem assoc_self_ell (x : CDAlg ℝ 4) : assoc x x ell = 0 := by
  rw [assoc_self_eq_laMap, loPart_eq_loOf, hiPart_eq_hiOf, laMap_loOf_hiOf_ell]

/-! ### The quaternion table on `{1, ℓ, p, ℓp}` -/

section QuatTable

variable {p : CDAlg ℝ 4}

/-- `p` and `ℓ` anticommute when `p` is imaginary and orthogonal to `ℓ`. -/
theorem p_ell_anticomm (hp0 : p.coord 0 = 0) (hp8 : p.coord (hiIdx 0) = 0) :
    p * ell = -(ell * p) := by
  have hbil : bil p ell = 0 := by rw [ell, bil_e_right]; exact hp8
  have h2 : p * ell + ell * p = 0 :=
    anticomm_of_orthogonal_imaginary hp0 ell_coord_zero hbil
  calc p * ell = (p * ell + ell * p) - ell * p := by abel
    _ = -(ell * p) := by rw [h2]; abel

/-- `p² = −N(p)·1` (the imaginary Cayley–Dickson square). -/
theorem p_sq (hp0 : p.coord 0 = 0) : p * p = (-(N p)) • (1 : CDAlg ℝ 4) :=
  imaginary_sq p hp0

/-- **`p·(ℓp) = N(p)·ℓ`.**  This is the row that is *not* automatic in a
    non-alternative algebra; it follows from `assoc_self_ell` plus `pℓ = −ℓp`. -/
theorem p_mul_ell_p (hp0 : p.coord 0 = 0) (hp8 : p.coord (hiIdx 0) = 0) :
    p * (ell * p) = (N p) • ell := by
  have hass : assoc p p ell = 0 := assoc_self_ell p
  rw [assoc, sub_eq_zero, p_ell_anticomm hp0 hp8, cd_mul_neg_right, p_sq hp0,
    mul_smul_left, cd_one_mul] at hass
  calc p * (ell * p) = -(-(p * (ell * p))) := by abel
    _ = -((-(N p)) • ell) := by rw [← hass]
    _ = (N p) • ell := by module

/-- `p` and `ℓp` are orthogonal. -/
theorem bil_p_ell_p (hp0 : p.coord 0 = 0) (hp8 : p.coord (hiIdx 0) = 0) :
    bil p (ell * p) = 0 := by
  have hq0 : (ell * p).coord 0 = 0 := ell_mul_imaginary hp8
  have h := QBP.Foundations.CrossProduct.reCoord_mul_pure p (ell * p) hq0
  rw [p_mul_ell_p hp0 hp8, smul_coord, ell_coord_zero, mul_zero] at h
  linarith

/-- **`(ℓp)·p = −N(p)·ℓ`.** -/
theorem ell_p_mul_p (hp0 : p.coord 0 = 0) (hp8 : p.coord (hiIdx 0) = 0) :
    (ell * p) * p = -((N p) • ell) := by
  have hq0 : (ell * p).coord 0 = 0 := ell_mul_imaginary hp8
  have h2 : p * (ell * p) + (ell * p) * p = 0 :=
    anticomm_of_orthogonal_imaginary hp0 hq0 (bil_p_ell_p hp0 hp8)
  calc (ell * p) * p = (p * (ell * p) + (ell * p) * p) - p * (ell * p) := by abel
    _ = -((N p) • ell) := by rw [h2, p_mul_ell_p hp0 hp8]; abel

/-- **`(ℓp)² = −N(p)·1`.** -/
theorem ell_p_sq (hp8 : p.coord (hiIdx 0) = 0) :
    (ell * p) * (ell * p) = (-(N p)) • (1 : CDAlg ℝ 4) := by
  rw [imaginary_sq _ (ell_mul_imaginary hp8), N_ell_mul]

end QuatTable

/-! ### The subalgebra `ℍ_s = span{1, ℓ, p, ℓp}` -/

/-- Membership in the real span of `{1, ℓ, p, ℓ·p}`. -/
def InQuatSpan (p x : CDAlg ℝ 4) : Prop :=
  ∃ a b c d : ℝ, x = a • (1 : CDAlg ℝ 4) + b • ell + c • p + d • (ell * p)

/-- **Prop 16(ii), multiplicative closure.**  For imaginary `p` orthogonal to `ℓ`,
    the 4-dimensional space `span{1, ℓ, p, ℓp}` is closed under the sedenion
    product, and the induced table is the quaternion table (`ℓ ↦ i`,
    `p ↦ |p|·j`, `ℓp ↦ |p|·k`). -/
theorem quatSpan_mul_closed {p : CDAlg ℝ 4} (hp0 : p.coord 0 = 0)
    (hp8 : p.coord (hiIdx 0) = 0) {x y : CDAlg ℝ 4}
    (hx : InQuatSpan p x) (hy : InQuatSpan p y) : InQuatSpan p (x * y) := by
  obtain ⟨a1, b1, c1, d1, hx⟩ := hx
  obtain ⟨a2, b2, c2, d2, hy⟩ := hy
  refine ⟨a1 * a2 - b1 * b2 - N p * (c1 * c2 + d1 * d2),
          a1 * b2 + b1 * a2 + N p * (c1 * d2 - d1 * c2),
          a1 * c2 + c1 * a2 - b1 * d2 + d1 * b2,
          a1 * d2 + d1 * a2 + b1 * c2 - c1 * b2, ?_⟩
  rw [hx, hy]
  simp only [mul_add_left, mul_add_right, mul_smul_left, mul_smul_right,
    cd_one_mul, cd_mul_one]
  rw [ell_sq, ell_ell_mul, p_ell_anticomm hp0 hp8, p_sq hp0, p_mul_ell_p hp0 hp8,
    ell_mul_ell hp0 hp8, ell_p_mul_p hp0 hp8, ell_p_sq hp8]
  module

/-- **Prop 16(ii), conjugation closure.**  `span{1, ℓ, p, ℓp}` is a `*`-subalgebra:
    `ℓ`, `p` and `ℓp` are all imaginary, so conjugation negates them. -/
theorem quatSpan_conj_closed {p : CDAlg ℝ 4} (hp0 : p.coord 0 = 0)
    (hp8 : p.coord (hiIdx 0) = 0) {x : CDAlg ℝ 4} (hx : InQuatSpan p x) :
    InQuatSpan p (conj x) := by
  obtain ⟨a, b, c, d, h⟩ := hx
  refine ⟨a, -b, -c, -d, ?_⟩
  rw [h, conj_add, conj_add, conj_add, conj_smul, conj_smul, conj_smul, conj_smul,
    conj_one, conj_of_imaginary ell_coord_zero, conj_of_imaginary hp0,
    conj_of_imaginary (ell_mul_imaginary hp8)]
  module

/-- A coordinate on which all four spanning vectors vanish vanishes on the whole
    span (linearity). -/
theorem inQuatSpan_coord_zero {p x : CDAlg ℝ 4} (hx : InQuatSpan p x) {k : Fin (2^4)}
    (h1 : (1 : CDAlg ℝ 4).coord k = 0) (hl : ell.coord k = 0) (hp : p.coord k = 0)
    (hq : (ell * p).coord k = 0) : x.coord k = 0 := by
  obtain ⟨a, b, c, d, h⟩ := hx
  rw [h]
  simp only [add_coord, smul_coord, h1, hl, hp, hq]
  ring

/-- **Non-vacuity: `ℍ_s` is a PROPER subspace of 𝕊.**  For the imaginary, `ℓ`-
    orthogonal witness `p = e₁`, the sedenion `e₂` is NOT in `span{1, ℓ, e₁, ℓe₁}`
    — so `quatSpan_mul_closed` is a genuine closure statement about a
    4-dimensional subspace of the 16-dimensional algebra, not a vacuous one. -/
theorem quatSpan_proper :
    ¬ InQuatSpan (e (⟨1, by norm_num⟩ : Fin (2^4))) (e (⟨2, by norm_num⟩ : Fin (2^4))) := by
  intro hx
  have h := inQuatSpan_coord_zero hx (k := ⟨2, by norm_num⟩)
    (by rw [one_coord, if_neg (by decide)])
    (by rw [ell, e_coord, if_neg (by decide)])
    (by rw [e_coord, if_neg (by decide)])
    (by rw [ell, e_mul_e, smul_coord, e_coord, if_neg (by decide), mul_zero])
  rw [e_coord, if_pos rfl] at h
  norm_num at h

/-- `GenByPair s t` — the sub-structure generated by `{1, s, t}`. -/
inductive GenByPair {n : ℕ} (s t : CDAlg ℝ n) : CDAlg ℝ n → Prop
  | one : GenByPair s t 1
  | left : GenByPair s t s
  | right : GenByPair s t t
  | add {x y} : GenByPair s t x → GenByPair s t y → GenByPair s t (x + y)
  | smul (r : ℝ) {x} : GenByPair s t x → GenByPair s t (r • x)
  | mul {x y} : GenByPair s t x → GenByPair s t y → GenByPair s t (x * y)
  | conj {x} : GenByPair s t x → GenByPair s t (QBP.Foundations.CDAlg.conj x)

/-- **Prop 16(ii).**  For an imaginary sedenion `s`, write `p := s − s₈·ℓ` for the
    component of `s` orthogonal to the doubling unit `ℓ = e₈`.  Then EVERY word in
    `{1, s, ℓ}` — built with `+`, real scaling, the sedenion product and
    conjugation — lies in the 4-dimensional space `ℍ_s = span{1, ℓ, p, ℓp}`, which
    (by `quatSpan_mul_closed`) carries the quaternion multiplication table.

    So the algebra's operations on the pair `(s, ℓ)` never leave a fixed
    quaternion subalgebra: they generate a compact group of symmetries of `ℍ_s`,
    not a dynamics on `Im 𝕊`. -/
theorem genByPair_ell_mem_quatSpan (s : CDAlg ℝ 4) (hs : s.coord 0 = 0) :
    ∀ x, GenByPair s ell x → InQuatSpan (s - (s.coord (hiIdx 0)) • ell) x := by
  set p : CDAlg ℝ 4 := s - (s.coord (hiIdx 0)) • ell with hp
  have hp0 : p.coord 0 = 0 := by
    rw [hp, sub_coord, smul_coord, ell_coord_zero, hs, mul_zero, sub_zero]
  have hp8 : p.coord (hiIdx 0) = 0 := by
    rw [hp, sub_coord, smul_coord, ell_coord_hiIdx_zero, mul_one, sub_self]
  intro x hx
  induction hx with
  | one => exact ⟨1, 0, 0, 0, by module⟩
  | left => exact ⟨0, s.coord (hiIdx 0), 1, 0, by rw [hp]; module⟩
  | right => exact ⟨0, 1, 0, 0, by module⟩
  | add _ _ ih1 ih2 =>
      obtain ⟨a1, b1, c1, d1, h1⟩ := ih1
      obtain ⟨a2, b2, c2, d2, h2⟩ := ih2
      exact ⟨a1 + a2, b1 + b2, c1 + c2, d1 + d2, by rw [h1, h2]; module⟩
  | smul r _ ih =>
      obtain ⟨a, b, c, d, h⟩ := ih
      exact ⟨r * a, r * b, r * c, r * d, by rw [h]; module⟩
  | mul _ _ ih1 ih2 => exact quatSpan_mul_closed hp0 hp8 ih1 ih2
  | conj _ ih => exact quatSpan_conj_closed hp0 hp8 ih

/-! ## 3. The Cayley–Dickson coordinate form of the `ℓ`-commutator

The doc's `[s, ℓ] = −2c + 2aℓ`, where `s = (a, b)` in the CD pair split and
`c = Im b`.  Stated for every sedenion; the imaginary corollary drops `Im a → a`. -/

/-- `ℓ ⊕ loIdx t = hiIdx t`. -/
theorem ell_xor_lo : ∀ t : Fin (2^3), (hiIdx 0 ^^^ loIdx t) = hiIdx t := by decide

/-- `ℓ ⊕ hiIdx t = loIdx t`. -/
theorem ell_xor_hi : ∀ t : Fin (2^3), (hiIdx 0 ^^^ hiIdx t) = loIdx t := by decide

theorem mulCoeff_comm_hi : ∀ t : Fin (2^3), t ≠ 0 →
    mulCoeff 4 (hiIdx t) (hiIdx 0) - mulCoeff 4 (hiIdx 0) (hiIdx t) = -2 := by decide

theorem mulCoeff_comm_lo : ∀ t : Fin (2^3), t ≠ 0 →
    mulCoeff 4 (loIdx t) (hiIdx 0) - mulCoeff 4 (hiIdx 0) (loIdx t) = 2 := by decide

theorem mulCoeff_comm_lo_zero :
    mulCoeff 4 (loIdx 0) (hiIdx 0) - mulCoeff 4 (hiIdx 0) (loIdx 0) = 0 := by decide

/-- Real cast of an integer `mulCoeff` difference identity. -/
private theorem cast_sub_two (u v : Int) (c : Int) (h : u - v = c) :
    ((u : ℝ)) - ((v : ℝ)) = (c : ℝ) := by
  have h2 := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h2
  exact h2

/-- **Low component of the `ℓ`-commutator:** `cdLo [s, ℓ] = −2·Im(cdHi s)`. -/
theorem cdLo_ell_commutator (s : CDAlg ℝ 4) :
    cdLo (s * ell - ell * s)
      = (-2 : ℝ) • (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3)) := by
  ext t
  rw [cdLo_coord, sub_coord, ell, mul_e_coord, e_mul_coord, ell_xor_lo,
    smul_coord, sub_coord, smul_coord, one_coord, cdHi_coord, cdHi_coord]
  by_cases ht : t = 0
  · rw [ht]
    simp
  · rw [if_neg ht, mul_zero, sub_zero, ← sub_mul,
      cast_sub_two _ _ _ (mulCoeff_comm_hi t ht)]
    push_cast
    ring

/-- **High component of the `ℓ`-commutator:** `cdHi [s, ℓ] = 2·Im(cdLo s)`. -/
theorem cdHi_ell_commutator (s : CDAlg ℝ 4) :
    cdHi (s * ell - ell * s)
      = (2 : ℝ) • (cdLo s - ((cdLo s).coord 0) • (1 : CDAlg ℝ 3)) := by
  ext t
  rw [cdHi_coord, sub_coord, ell, mul_e_coord, e_mul_coord, ell_xor_hi,
    smul_coord, sub_coord, smul_coord, one_coord, cdLo_coord, cdLo_coord]
  by_cases ht : t = 0
  · rw [ht, if_pos rfl, ← sub_mul, cast_sub_two _ _ _ mulCoeff_comm_lo_zero]
    push_cast
    ring
  · rw [if_neg ht, mul_zero, sub_zero, ← sub_mul,
      cast_sub_two _ _ _ (mulCoeff_comm_lo t ht)]
    push_cast
    ring

/-- **The doc's `[s, ℓ] = −2c + 2aℓ`.**  For an IMAGINARY sedenion `s = (a, b)`
    with `c := Im b`, the commutator with `ℓ` has low component `−2c` and high
    component `2a`. -/
theorem cdHi_ell_commutator_imaginary {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) :
    cdHi (s * ell - ell * s) = (2 : ℝ) • cdLo s := by
  rw [cdHi_ell_commutator, cdLo_coord, loIdx_zero, hs, zero_smul, sub_zero]

/-! ## 4. Axiom audit

Every theorem in this file must depend only on `{propext, Classical.choice,
Quot.sound}` — no `sorryAx`, no native-reduction axiom, no user axiom. -/

#print axioms conj_one
#print axioms conj_add
#print axioms conj_smul
#print axioms conj_of_imaginary
#print axioms cd_mul_neg_right
#print axioms cd_neg_mul_left
#print axioms xor_cancel_left
#print axioms e_mul_coord
#print axioms mul_e_coord
#print axioms bil_e_right
#print axioms N_e
#print axioms N_smul
#print axioms GenBy.neg
#print axioms genBy_mem_span
#print axioms genBy_unit_imag_eq
#print axioms ell_coord_zero
#print axioms ell_coord_hiIdx_zero
#print axioms N_ell
#print axioms mulCoeff_ell_ell
#print axioms mulCoeff_ell_left_sq
#print axioms mulCoeff_ell_right_sq
#print axioms mulCoeff_ell_conj
#print axioms mulCoeff_ell_sq_one
#print axioms laCoeffZ_lo_hi_ell
#print axioms ell_sq
#print axioms ell_ell_mul
#print axioms mul_ell_ell
#print axioms ell_mul_ell
#print axioms ell_mul_imaginary
#print axioms N_ell_mul
#print axioms laMap_loOf_hiOf_ell
#print axioms assoc_self_ell
#print axioms p_ell_anticomm
#print axioms p_sq
#print axioms p_mul_ell_p
#print axioms bil_p_ell_p
#print axioms ell_p_mul_p
#print axioms ell_p_sq
#print axioms quatSpan_mul_closed
#print axioms quatSpan_conj_closed
#print axioms inQuatSpan_coord_zero
#print axioms quatSpan_proper
#print axioms genByPair_ell_mem_quatSpan
#print axioms ell_xor_lo
#print axioms ell_xor_hi
#print axioms mulCoeff_comm_hi
#print axioms mulCoeff_comm_lo
#print axioms mulCoeff_comm_lo_zero
#print axioms cdLo_ell_commutator
#print axioms cdHi_ell_commutator
#print axioms cdHi_ell_commutator_imaginary

end QBP.Foundations.NoAutonomousDynamics
