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

**Layer 3 mechanism (§4) — what is and is not special about `ℓ`.**  Three theorems
correcting the attribution flagged by the PR #640 review: (T1) `N (x·t) = N x · N t` for
every `x` and every `t` in either Cayley–Dickson half (`N_mul_right_of_lo`,
`N_mul_right_of_hi`, `rightMul_isometry_of_half`), from the doubling formula `cdLo_mul` /
`cdHi_mul` — so `R_t` is transient-free for a whole 8+8-dimensional set, not just for `ℓ`;
(T2) the trace identity `Σ_k N(e_k·t) = 16·N t` (`sum_N_basis_mul`, and `sum_N_mul_basis`);
(T3) `assoc_self_zero_iff`: `{y | ∀ x, [x,x,y] = 0} = span_ℝ{1, ℓ}` exactly — this, not
orthogonality, is what singles out `ℓ`.

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

Third layer — the mechanism, now FORMALISED in §4 below (numerical origin:
`analysis/473-dirac-probe/generic_maps_check.py`, Red Team round-4 confirmer).  With an
UNFORCED second element t, the maps x ↦ x·t, t·x, [x,t] are linear (R_t, L_t, ad_t); their
normalised iteration is power iteration onto the top-singular subspace — which lies on the
zero-divisor ridge V = 1 — followed by a period-2 symmetry.  Three facts about that picture
are theorems here, and they correct the attribution this file previously carried:

  * **Σσ²(R_t) = 16·N(t)** (`sum_N_basis_mul`; `sum_N_mul_basis` for L_t).  In the basis
    {e_k} the columns of R_t are e_k·t, so the sum is tr(R_tᵀR_t).  For unit t this forces
    Σσᵢ² = 16 = dim 𝕊, so a singular value above 1 requires another below 1: a dominant
    plane can exist only because the norm is not multiplicative at dim 16.
  * **R_t is norm-multiplicative — hence transient-free — for EVERY t in EITHER Cayley–Dickson
    half**, t ∈ 𝕆 (`N_mul_right_of_lo`) or t ∈ 𝕆ℓ (`N_mul_right_of_hi`), packaged as
    `rightMul_isometry_of_half`.  The engine is the doubling formula (a,b)(c,d) =
    (ac − d̄b, da + bc̄), proved here as `cdLo_mul` / `cdHi_mul`, plus 𝕆's norm composition.
    So the absence of a transient does **not** single out ℓ — ℓ is just one point of an
    8-dimensional half (`N_mul_ell`).  The hypothesis is not vacuous: `half_hypothesis_necessary`
    exhibits the failure of composition on the rest of 𝕊.
  * **What DOES single out ℓ is alternator-flatness in the third slot**: `assoc_self_ell` says
    [x, x, ℓ] = 0 for every sedenion x, and `assoc_self_zero_iff` proves the converse —
    {y | ∀x, [x,x,y] = 0} is EXACTLY span_ℝ{1, ℓ}, a 2-dimensional kernel.  (Previously this
    was asserted as a numerical observation; it is now an iff-theorem.)

So: no autonomous algebraic dynamics toward the vacuum; the only non-symmetric behaviour is a
linear transient onto the zero-divisor locus, and it is a property of 𝕊's failure of
composition off 𝕆 ∪ 𝕆ℓ, not of ℓ.

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

/-! ## 4. Layer 3 mechanism: what is and is not special about `ℓ`

Red Team review of PR #640 (finding #2, concurred by Gemini) flagged the previous
docstring for attributing *"`R_t` is orthogonal, hence no transient"* to `ℓ`
specifically.  That attribution is wrong, and this section proves the correct one.

**T1 — orthogonality of `R_t` is a property of BOTH Cayley–Dickson halves, not of `ℓ`.**
The norm form is multiplicative against any `t` lying in a single half of the pair
split `𝕊 = 𝕆 ⊕ 𝕆ℓ`: `N (x·t) = N x · N t` for every `x` whenever `cdHi t = 0`
(`N_mul_right_of_lo`, `t ∈ 𝕆`) or `cdLo t = 0` (`N_mul_right_of_hi`, `t ∈ 𝕆ℓ`),
packaged as `rightMul_isometry_of_half`.  So for nonzero such `t` the map `R_t` is a
similarity (`√N t` times an orthogonal map) — no transient — on a `(8+8)`-dimensional
set of `t`, of which `ℓ` is one point (`N_mul_ell`).  The engine is the Cayley–Dickson doubling formula,
proved here coordinatewise from `mulCoeff 4` (`cdLo_mul` / `cdHi_mul`):

    (a, b)·(c, d) = (a c − d̄ b,  d a + b c̄)

together with 𝕆's norm composition (`CDAlg.octonion_norm_composition`) and
`N (conj z) = N z`.  The hypothesis is not removable: `N` is genuinely
non-multiplicative on 𝕊 (`half_hypothesis_necessary`, from the zero-divisor
witnesses), so the two halves really are the exceptional locus, not the whole algebra.

**T2 — the singular-value sum identity `Σ σ²(R_t) = 16·N(t)`.**  In the basis
`{e_k}` the columns of `R_t : x ↦ x·t` are `R_t e_k = e_k·t`, so
`tr(R_tᵀ R_t) = Σ_k ‖e_k·t‖² = Σ_k N(e_k·t)`.  `sum_N_basis_mul` proves that this
equals `16·N t`; `sum_N_mul_basis` is the same statement for `L_t` (`Σ_k N(t·e_k)`).
The mechanism is `N_basis_mul` / `N_mul_basis`: left- and right-multiplication by a
basis element is a signed permutation of coordinates, hence an isometry.
*Consequence (not formalised — singular values are not defined here):* for a unit `t`
the singular values of `R_t` satisfy `Σ σ_i² = 16 = dim 𝕊`, so if some `σ_i > 1` then
some `σ_j < 1`.  A dominant singular plane can exist only because `N` is not
multiplicative at dimension 16; on the two halves all `σ_i = 1` and there is nothing
to dominate.

**T3 — what IS special about `ℓ`: `[x, x, ℓ] = 0`, and `ℓ` is the only such element.**
`assoc_self_zero_iff` proves that the set of `y ∈ 𝕊` annihilated by every left
alternator, `{y | ∀ x, [x, x, y] = 0}`, is EXACTLY `span_ℝ {1, ℓ}` — a genuine
if-and-only-if, so the kernel has dimension exactly 2.  `⇐` is `assoc_self_ell`
plus `alt_assoc_one_right` and trilinearity; `⇒` polarizes the hypothesis to
`laMap u v y = 0` (`laMap_of_assoc_self_zero`), reads off the basis coefficient
(`coord_laMap_e_e`), and uses the kernel-`decide`d fact that every index outside
`{0, 8}` carries a nonzero cross-alternator coefficient (`laCoeffZ_cross_witness`).

So the correct attribution is: absence of a transient is shared by all of `𝕆 ∪ 𝕆ℓ`;
alternator-flatness in the third slot is what singles out `ℓ` (up to `span{1, ℓ}`). -/

section Layer3

/-! ### Index and structure-constant facts for the pair split (kernel `decide`) -/

/-- Low ⊕ low lands in the low half. -/
theorem loIdx_xor_loIdx : ∀ p q : Fin (2^3), (loIdx p ^^^ loIdx q) = loIdx (p ^^^ q) := by decide

/-- Low ⊕ high lands in the high half. -/
theorem loIdx_xor_hiIdx : ∀ p q : Fin (2^3), (loIdx p ^^^ hiIdx q) = hiIdx (p ^^^ q) := by decide

/-- High ⊕ low lands in the high half. -/
theorem hiIdx_xor_loIdx : ∀ p q : Fin (2^3), (hiIdx p ^^^ loIdx q) = hiIdx (p ^^^ q) := by decide

/-- High ⊕ high lands in the low half. -/
theorem hiIdx_xor_hiIdx : ∀ p q : Fin (2^3), (hiIdx p ^^^ hiIdx q) = loIdx (p ^^^ q) := by decide

/-- Doubling row `(a,0)(c,0) = (ac, 0)` at the coefficient level (64 cases). -/
theorem mulCoeff_lo_lo : ∀ p q : Fin (2^3),
    mulCoeff 4 (loIdx p) (loIdx q) = mulCoeff 3 p q := by decide

/-- Doubling row `(a,0)(0,d) = (0, da)` at the coefficient level (64 cases). -/
theorem mulCoeff_lo_hi : ∀ p q : Fin (2^3),
    mulCoeff 4 (loIdx p) (hiIdx q) = mulCoeff 3 q p := by decide

/-- Doubling row `(0,b)(c,0) = (0, b c̄)` at the coefficient level (64 cases). -/
theorem mulCoeff_hi_lo : ∀ p q : Fin (2^3),
    mulCoeff 4 (hiIdx p) (loIdx q) = conjSign 3 q * mulCoeff 3 p q := by decide

/-- Doubling row `(0,b)(0,d) = (−d̄ b, 0)` at the coefficient level (64 cases). -/
theorem mulCoeff_hi_hi : ∀ p q : Fin (2^3),
    mulCoeff 4 (hiIdx p) (hiIdx q) = -(conjSign 3 q * mulCoeff 3 q p) := by decide

/-- Every sedenion structure constant is `±1` (256 cases) — so left/right
    multiplication by a basis element is a *signed permutation* of coordinates. -/
theorem mulCoeff_four_sq : ∀ i j : Fin (2^4), mulCoeff 4 i j * mulCoeff 4 i j = 1 := by decide

/-! ### The pair split as a `Fintype` bijection, and `N x = N(cdLo x) + N(cdHi x)` -/

/-- The Cayley–Dickson half-split bijection `Fin 8 ⊕ Fin 8 ≃ Fin 16`. -/
def halfEquiv : (Fin (2^3) ⊕ Fin (2^3)) ≃ Fin (2^4) where
  toFun := Sum.elim loIdx hiIdx
  invFun k := if h : k.val < 2^3 then Sum.inl ⟨k.val, h⟩ else Sum.inr ⟨k.val - 2^3, by omega⟩
  left_inv := by decide
  right_inv := by decide

/-- Any sum over `Fin 16` splits as low-half plus high-half. -/
theorem sum_split {M : Type*} [AddCommMonoid M] (f : Fin (2^4) → M) :
    (∑ k, f k) = (∑ p : Fin (2^3), f (loIdx p)) + (∑ q : Fin (2^3), f (hiIdx q)) := by
  rw [← Equiv.sum_comp halfEquiv f, Fintype.sum_sum_type]
  rfl

/-- Coordinatewise conjugation as a signed scaling: `(conj z)_i = conjSign i · z_i`. -/
theorem conj_coord_conjSign {R : Type*} [CommRing R] {n : ℕ} (z : CDAlg R n) (i : Fin (2^n)) :
    (conj z).coord i = ((conjSign n i : Int) : R) * z.coord i := by
  rw [conj_coord, conjSign]
  by_cases h : i.val = 0
  · rw [if_pos h, if_pos h]; push_cast; ring
  · rw [if_neg h, if_neg h]; push_cast; ring

/-- `conj 0 = 0`. -/
theorem cd_conj_zero {R : Type*} [CommRing R] {n : ℕ} : conj (0 : CDAlg R n) = 0 := by
  ext i; rw [conj_coord, zero_coord]; split_ifs <;> simp

/-- `N 0 = 0`. -/
theorem N_zero {n : ℕ} : N (0 : CDAlg ℝ n) = 0 := by
  rw [N_def]; exact Finset.sum_eq_zero (fun i _ => by rw [zero_coord]; ring)

/-- `N (−z) = N z`. -/
theorem N_neg {n : ℕ} (z : CDAlg ℝ n) : N (-z) = N z := by
  rw [N_def, N_def]; exact Finset.sum_congr rfl (fun i _ => by rw [neg_coord]; ring)

/-- `N (conj z) = N z` (conjugation flips signs of imaginary coordinates only). -/
theorem N_conj {n : ℕ} (z : CDAlg ℝ n) : N (conj z) = N z := by
  rw [N_def, N_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [conj_coord]; split_ifs <;> ring

/-- **The norm form is additive over the pair split:** `N x = N(cdLo x) + N(cdHi x)`. -/
theorem N_split (x : CDAlg ℝ 4) : N x = N (cdLo x) + N (cdHi x) := by
  rw [N_def, sum_split (fun k => (x.coord k)^2), N_def, N_def]; rfl

/-! ### The Cayley–Dickson doubling formula on 𝕊 = 𝕆 ⊕ 𝕆 -/

/-- **Doubling formula, low component:** for `x = (a, b)` and `y = (c, d)` in the
    pair split, `cdLo (x·y) = a c − d̄ b`.  Proved coordinatewise from the
    `mulCoeff 4` recursion via the four kernel-`decide`d doubling rows. -/
theorem cdLo_mul (x y : CDAlg ℝ 4) :
    cdLo (x * y) = cdLo x * cdLo y - conj (cdHi y) * cdHi x := by
  ext s
  have h1 : (∑ p : Fin (2^3), (mulCoeff 4 (loIdx p) (loIdx p ^^^ loIdx s) : ℝ)
        * x.coord (loIdx p) * y.coord (loIdx p ^^^ loIdx s))
      = (cdLo x * cdLo y).coord s := by
    rw [mul_coord_single]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [loIdx_xor_loIdx, mulCoeff_lo_lo, cdLo_coord, cdLo_coord]
  have h2 : (∑ q : Fin (2^3), (mulCoeff 4 (hiIdx q) (hiIdx q ^^^ loIdx s) : ℝ)
        * x.coord (hiIdx q) * y.coord (hiIdx q ^^^ loIdx s))
      = -((conj (cdHi y) * cdHi x).coord s) := by
    rw [mul_coord_matrix, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hiIdx_xor_loIdx, mulCoeff_hi_hi, conj_coord_conjSign, cdHi_coord, cdHi_coord]
    push_cast; ring
  rw [cdLo_coord, mul_coord_single, sum_split, h1, h2, sub_coord]
  ring

/-- **Doubling formula, high component:** `cdHi (x·y) = d a + b c̄`. -/
theorem cdHi_mul (x y : CDAlg ℝ 4) :
    cdHi (x * y) = cdHi y * cdLo x + cdHi x * conj (cdLo y) := by
  ext s
  have h1 : (∑ p : Fin (2^3), (mulCoeff 4 (loIdx p) (loIdx p ^^^ hiIdx s) : ℝ)
        * x.coord (loIdx p) * y.coord (loIdx p ^^^ hiIdx s))
      = (cdHi y * cdLo x).coord s := by
    rw [mul_coord_matrix]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [loIdx_xor_hiIdx, mulCoeff_lo_hi, cdHi_coord, cdLo_coord]
    ring
  have h2 : (∑ q : Fin (2^3), (mulCoeff 4 (hiIdx q) (hiIdx q ^^^ hiIdx s) : ℝ)
        * x.coord (hiIdx q) * y.coord (hiIdx q ^^^ hiIdx s))
      = (cdHi x * conj (cdLo y)).coord s := by
    rw [mul_coord_single]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hiIdx_xor_hiIdx, mulCoeff_hi_lo, conj_coord_conjSign, cdHi_coord, cdLo_coord]
    push_cast; ring
  rw [cdHi_coord, mul_coord_single, sum_split, h1, h2, add_coord]

/-! ### T1 — `R_t` is norm-multiplicative for EVERY `t` in either half -/

/-- **T1a.**  If `t` lies in the low Cayley–Dickson half (`t ∈ 𝕆`, i.e. `cdHi t = 0`)
    then `N (x·t) = N x · N t` for EVERY sedenion `x`: right multiplication by `t` is
    a similarity of the norm form, so it has no transient.  Nothing about `ℓ` is used. -/
theorem N_mul_right_of_lo (x t : CDAlg ℝ 4) (ht : cdHi t = 0) : N (x * t) = N x * N t := by
  have hlo : cdLo (x * t) = cdLo x * cdLo t := by
    rw [cdLo_mul, ht, cd_conj_zero, alt_zero_mul, sub_zero]
  have hhi : cdHi (x * t) = cdHi x * conj (cdLo t) := by
    rw [cdHi_mul, ht, alt_zero_mul, zero_add]
  rw [N_split (x * t), hlo, hhi, octonion_norm_composition, octonion_norm_composition,
    N_conj, N_split x, N_split t, ht, N_zero, add_zero]
  ring

/-- **T1b.**  If `t` lies in the high Cayley–Dickson half (`t ∈ 𝕆ℓ`, i.e. `cdLo t = 0`)
    then `N (x·t) = N x · N t` for EVERY sedenion `x`.  `ℓ = e₈` is one point of this
    8-dimensional set (`N_mul_ell`), in no way distinguished. -/
theorem N_mul_right_of_hi (x t : CDAlg ℝ 4) (ht : cdLo t = 0) : N (x * t) = N x * N t := by
  have hlo : cdLo (x * t) = -(conj (cdHi t) * cdHi x) := by
    rw [cdLo_mul, ht, alt_mul_zero, zero_sub]
  have hhi : cdHi (x * t) = cdHi t * cdLo x := by
    rw [cdHi_mul, ht, cd_conj_zero, alt_mul_zero, add_zero]
  rw [N_split (x * t), hlo, hhi, N_neg, octonion_norm_composition, octonion_norm_composition,
    N_conj, N_split x, N_split t, ht, N_zero, zero_add]
  ring

/-- **T1, operator form.**  For every `t` in either Cayley–Dickson half, the linear
    map `R_t : x ↦ x·t` scales the norm form by the constant `N t` — i.e. `R_t` is
    `√N t` times an orthogonal map when `t ≠ 0` (and the zero map when `t = 0`), so its
    normalised iteration has no transient.  The statement itself is the exact quadratic-form
    identity, which holds unconditionally.
    The set of such `t` is `𝕆 ∪ 𝕆ℓ`, of real dimension 8 in each half. -/
theorem rightMul_isometry_of_half (t : CDAlg ℝ 4) (ht : cdHi t = 0 ∨ cdLo t = 0) :
    ∀ x, N (x * t) = N x * N t := by
  rcases ht with h | h
  · exact fun x => N_mul_right_of_lo x t h
  · exact fun x => N_mul_right_of_hi x t h

/-- `ℓ` lies in the high half: `cdLo ℓ = 0`. -/
theorem cdLo_ell : cdLo ell = 0 := by
  ext p
  rw [cdLo_coord, ell, e_coord, if_neg (loIdx_ne_hiIdx p 0), zero_coord]

/-- **`R_ℓ` preserves the norm form** — the `t = ℓ` instance of `N_mul_right_of_hi`,
    NOT a property peculiar to `ℓ`.  (`N_ell_mul` above is the `L_ℓ` counterpart.) -/
theorem N_mul_ell (x : CDAlg ℝ 4) : N (x * ell) = N x := by
  rw [N_mul_right_of_hi x ell cdLo_ell, N_ell, mul_one]

/-- **The half hypothesis in T1 is necessary, not decorative.**  On all of 𝕊 the norm
    form is NOT multiplicative — the zero-divisor witnesses give `x, t` with
    `N (x·t) ≠ N x · N t` — so `𝕆 ∪ 𝕆ℓ` is a genuine exceptional locus for
    `rightMul_isometry_of_half`, and the theorem is not vacuously general. -/
theorem half_hypothesis_necessary : ∃ x t : CDAlg ℝ 4, N (x * t) ≠ N x * N t :=
  QBP.Foundations.CrossProduct.no_sedenion_composition_for_cross

/-! ### T2 — the singular-value sum identity `Σ σ²(R_t) = 16·N(t)` -/

/-- **Left multiplication by a basis element is an isometry:** `N (e_m · x) = N x`.
    (`e_m ·` is a signed permutation of coordinates, `mulCoeff_four_sq`.) -/
theorem N_basis_mul (m : Fin (2^4)) (x : CDAlg ℝ 4) : N (e m * x) = N x := by
  have hsq : ∀ j : Fin (2^4), ((mulCoeff 4 m j : ℝ))^2 = 1 := by
    intro j
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) (mulCoeff_four_sq m j)
    push_cast at h2
    rw [pow_two]; exact h2
  have hterm : ∀ k : Fin (2^4), ((e m * x).coord k)^2 = (x.coord (k ^^^ m))^2 := by
    intro k
    rw [e_mul_coord, xor_comm_fin m k, mul_pow, hsq, one_mul]
  rw [N_def, N_def, Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
  exact (sum_xor_reindex m (fun i => (x.coord i)^2)).symm

/-- **Right multiplication by a basis element is an isometry:** `N (x · e_m) = N x`. -/
theorem N_mul_basis (x : CDAlg ℝ 4) (m : Fin (2^4)) : N (x * e m) = N x := by
  have hsq : ∀ j : Fin (2^4), ((mulCoeff 4 j m : ℝ))^2 = 1 := by
    intro j
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) (mulCoeff_four_sq j m)
    push_cast at h2
    rw [pow_two]; exact h2
  have hterm : ∀ k : Fin (2^4), ((x * e m).coord k)^2 = (x.coord (k ^^^ m))^2 := by
    intro k
    rw [mul_e_coord, xor_comm_fin m k, mul_pow, hsq, one_mul]
  rw [N_def, N_def, Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hterm k)]
  exact (sum_xor_reindex m (fun i => (x.coord i)^2)).symm

/-- **T2 — `Σ σ²(R_t) = 16·N(t)`.**  The columns of the right-multiplication matrix
    `R_t : x ↦ x·t` in the basis `{e_k}` are `R_t e_k = e_k·t`, so this sum is
    `tr(R_tᵀ R_t) = Σ_i σ_i(R_t)²`.  It equals `16·N t = (dim 𝕊)·N t` for EVERY
    sedenion `t` — for unit `t` the singular values therefore satisfy `Σ σ_i² = 16`,
    so a singular value above 1 forces another below 1.  (Singular values themselves
    are not formalised here; the trace identity is the anchor.) -/
theorem sum_N_basis_mul (t : CDAlg ℝ 4) : (∑ k : Fin (2^4), N (e k * t)) = 16 * N t := by
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => N_basis_mul k t), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **T2, left version — `Σ σ²(L_t) = 16·N(t)`**, with `L_t e_k = t·e_k`. -/
theorem sum_N_mul_basis (t : CDAlg ℝ 4) : (∑ k : Fin (2^4), N (t * e k)) = 16 * N t := by
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => N_mul_basis t k), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-! ### T3 — `span{1, ℓ}` is EXACTLY the alternator-flat third slot -/

/-- **Off `span{1, ℓ}` the cross alternator is nonzero (kernel `decide`).**  For every
    basis index `j ∉ {0, 8}` there is a low/high basis pair whose polarized left
    alternator has a nonzero coefficient at `j`. -/
theorem laCoeffZ_cross_witness : ∀ j : Fin (2^4), j ≠ 0 → j ≠ hiIdx 0 →
    ∃ p q : Fin (2^3), laCoeffZ 4 (loIdx p) (hiIdx q) j ≠ 0 := by decide

/-- Polarization: if the diagonal left alternator kills `y` for every `x`, then the
    polarized alternator `laMap u v y` vanishes for every pair `(u, v)`. -/
theorem laMap_of_assoc_self_zero {y : CDAlg ℝ 4} (h : ∀ x, assoc x x y = 0) (u v : CDAlg ℝ 4) :
    laMap u v y = 0 := by
  have hsum := h (u + v)
  rw [assoc_trilinear.add_left, assoc_trilinear.add_mid, assoc_trilinear.add_mid, h u, h v] at hsum
  rw [laMap]
  calc assoc u v y + assoc v u y = 0 + assoc u v y + (assoc v u y + 0) := by abel
    _ = 0 := hsum

/-- Reading off one basis coefficient of `laMap (e i) (e j) y` (trilinearity plus the
    injectivity of `k ↦ i ⊕ j ⊕ k`). -/
theorem coord_laMap_e_e (i j j0 : Fin (2^4)) (y : CDAlg ℝ 4) :
    (laMap (e i) (e j) y).coord (i ^^^ j ^^^ j0) = (laCoeffZ 4 i j j0 : ℝ) * y.coord j0 := by
  conv_lhs => rw [basis_expansion y]
  rw [laMap_trilinear.sum_right, sum_coord, Finset.sum_eq_single j0]
  · rw [laMap_trilinear.smul_right, laMap_e, smul_smul, smul_coord, e_coord, if_pos rfl]
    ring
  · intro b _ hb
    rw [laMap_trilinear.smul_right, laMap_e, smul_smul, smul_coord, e_coord,
      if_neg (fun hh => hb (xor_left_injective (i ^^^ j) hh.symm)), mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- If `[x, x, y] = 0` for every `x`, then every coordinate of `y` outside `{0, 8}`
    vanishes. -/
theorem coord_zero_of_assoc_self_zero {y : CDAlg ℝ 4} (h : ∀ x, assoc x x y = 0) :
    ∀ j : Fin (2^4), j ≠ 0 → j ≠ hiIdx 0 → y.coord j = 0 := by
  intro j hj0 hj8
  obtain ⟨p, q, hpq⟩ := laCoeffZ_cross_witness j hj0 hj8
  have hz := laMap_of_assoc_self_zero h (e (loIdx p)) (e (hiIdx q))
  have hc := congrArg (fun z : CDAlg ℝ 4 => z.coord (loIdx p ^^^ hiIdx q ^^^ j)) hz
  simp only [zero_coord] at hc
  rw [coord_laMap_e_e] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact absurd (by exact_mod_cast h1) hpq
  · exact h1

/-- **T3 — `ℓ` is the unique alternator-flat direction, modulo `1`.**  For a sedenion
    `y`, the left alternator `[x, x, y]` vanishes for EVERY `x` if and only if
    `y ∈ span_ℝ {1, ℓ}`.  So the kernel of `y ↦ [·, ·, y]` on the diagonal is exactly
    2-dimensional: `assoc_self_ell` is not an accident of `e₈`, it is the defining
    property of the doubling unit up to the trivial directions `1` and rescaling. -/
theorem assoc_self_zero_iff (y : CDAlg ℝ 4) :
    (∀ x, assoc x x y = 0) ↔ ∃ a b : ℝ, y = a • (1 : CDAlg ℝ 4) + b • ell := by
  constructor
  · intro h
    refine ⟨y.coord 0, y.coord (hiIdx 0), ?_⟩
    ext k
    rw [add_coord, smul_coord, smul_coord, one_coord, ell, e_coord]
    by_cases hk0 : k = 0
    · rw [hk0, if_pos rfl, if_neg (by decide : ¬((0 : Fin (2^4)) = hiIdx 0))]; ring
    · by_cases hk8 : k = hiIdx 0
      · rw [hk8, if_neg (by decide : ¬(hiIdx (0 : Fin (2^3)) = (0 : Fin (2^4)))), if_pos rfl]
        ring
      · rw [if_neg hk0, if_neg hk8, coord_zero_of_assoc_self_zero h k hk0 hk8]; ring
  · rintro ⟨a, b, rfl⟩ x
    rw [assoc_trilinear.add_right, assoc_trilinear.smul_right, assoc_trilinear.smul_right,
      alt_assoc_one_right, assoc_self_ell, smul_zero, smul_zero, add_zero]

end Layer3

/-! ## 5. Axiom audit

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

#print axioms loIdx_xor_loIdx
#print axioms loIdx_xor_hiIdx
#print axioms hiIdx_xor_loIdx
#print axioms hiIdx_xor_hiIdx
#print axioms mulCoeff_lo_lo
#print axioms mulCoeff_lo_hi
#print axioms mulCoeff_hi_lo
#print axioms mulCoeff_hi_hi
#print axioms mulCoeff_four_sq
#print axioms sum_split
#print axioms conj_coord_conjSign
#print axioms cd_conj_zero
#print axioms N_zero
#print axioms N_neg
#print axioms N_conj
#print axioms N_split
#print axioms cdLo_mul
#print axioms cdHi_mul
#print axioms N_mul_right_of_lo
#print axioms N_mul_right_of_hi
#print axioms rightMul_isometry_of_half
#print axioms cdLo_ell
#print axioms N_mul_ell
#print axioms half_hypothesis_necessary
#print axioms N_basis_mul
#print axioms N_mul_basis
#print axioms sum_N_basis_mul
#print axioms sum_N_mul_basis
#print axioms laCoeffZ_cross_witness
#print axioms laMap_of_assoc_self_zero
#print axioms coord_laMap_e_e
#print axioms coord_zero_of_assoc_self_zero
#print axioms assoc_self_zero_iff

end QBP.Foundations.NoAutonomousDynamics
