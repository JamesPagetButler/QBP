import QBP.Foundations.NoAutonomousDynamics
import QBP.Foundations.DeltaLandscape

/-!
# QBP.Foundations.CrystalHosting — what a crystal (vacuum) hosts

**Research-thread evidence for #473 AC1 (hosting), sub-issue #639, and #634
AC3 / AC4.**  This file is ordinary `QBP.Foundations` material — pure
`CDAlg`/ℝ algebra, no substrate semantics, no `QBP.Substrate` import, and
nothing here authorises such a file.

## Vocabulary

A **vacuum** (in the #473 landscape sense; informally a *crystal*) is an
imaginary sedenion `s : CDAlg ℝ 4` whose two Cayley–Dickson components commute,
`cdLo s * cdHi s = cdHi s * cdLo s`.  By
`CDAlg.sedenion_alternator_vanishes_iff_components_commute` (Alternator.lean,
T2a at 𝕊) that is *exactly* the vanishing of the left alternator
`T_s x = (s·s)·x − s·(s·x)`, i.e. exactly `V(s) = ‖[a, b]‖² = 0` for the
δ-landscape potential of `DeltaLandscape.sedenion_landscape_descends`.  The
predicate is `IsVacuum` below and it is *defined* by the commutator form;
`isVacuum_iff_alternator_flat` proves the two forms agree.

## What is proved

* **T3 / #634 AC3 — Prop 15, the vacuum parametrisation.**
  `vacuum_iff_parametrised` : `s` is a vacuum **iff** there are an imaginary
  octonion direction `u` (a unit, or `0` at the poles) and reals `α, γ, b₀`
  with `cdLo s = α • u` and `cdHi s = b₀ • 1 + γ • u`.  So `a = cdLo s` and
  `Im (cdHi s)` are *parallel*: the vacuum locus is `{(α u, b₀ + γ u)}`.
  `vacuum_norm_parametrised` adds `N s = α² + γ² + b₀²`, which on the unit
  sphere is the doc's `(a, Im b) = √(1 − b₀²)·(cos θ, sin θ)·u`.  The
  *topology* of the quotient (suspension of ℝP¹ ≅ S²) is NOT formalised here —
  only the parametrisation.

* **T1 — every crystal carries a quaternion subalgebra.**
  `vacuum_hosts_quaternion` : for a vacuum `s` there is an octonion direction
  `u` (unit, or `0`) with `cdLo s ∈ ℝ·u`, `Im (cdHi s) ∈ ℝ·u`, and *every*
  word in `{1, s, ℓ}` — built with `+`, real scaling, the sedenion product and
  conjugation — lying in `span_ℝ {1, ℓ, U, ℓU}` for `U := loOf u` the
  low-half embedding of `u`.  `crystal_quaternion_table` proves the four
  generators satisfy the quaternion relations (`U² = ℓ² = (ℓU)² = −1`,
  `Uℓ = −ℓU`, `U(ℓU) = ℓ`, `(ℓU)U = −ℓ`) and
  `crystal_quatSpan_independent` proves `{1, ℓ, U, ℓU}` are linearly
  independent when `u` is a unit — so the hosted algebra is genuinely
  4-dimensional, an isomorphic copy of ℍ, and not a degenerate span.
  At the poles (`u = 0`, i.e. `s ∈ ℝℓ`) the hosted algebra degenerates to
  `span{1, ℓ} ≅ ℂ`; that case is stated, not hidden.

* **T2 — Aut-equivariance of the assignment.**  `CDAut n` is a minimal
  automorphism structure for `CDAlg ℝ n` (which is deliberately *not* a
  `Ring`, so Mathlib's `AlgEquiv` does not apply).  `CDAut.map_re`,
  `CDAut.map_N` : every such automorphism preserves the real part and the norm
  form (proved from the Cayley–Dickson square identity, not assumed).  Hence
  `aut_map_isVacuum` : automorphisms map vacua to vacua; `aut_genByPair` :
  they map words in `{1, s, t}` to words in `{1, φ s, φ t}`; and, for a `φ`
  fixing the doubling unit `ℓ` (the `G₂` factor of `Aut(𝕊) = G₂ × S₃` acts this
  way), `aut_image_quatSpan` : `φ` carries the hosted subalgebra of `s`
  *onto* the hosted subalgebra of `φ s`.  Non-vacuity, twice over: `gradeAut` is
  an explicit **non-identity** automorphism of `CDAlg ℝ 4` (`ℓ ↦ −ℓ`, the ℤ/2 of
  the `S₃` factor, which inhabits the unconditional theorems), and `cdLift`
  lifts any automorphism of 𝕆 to one of 𝕊 that **fixes `ℓ`** (this is how the
  `G₂` factor acts), with `cdLift gradeAut3` an explicit non-identity instance —
  so the `ℓ`-fixing theorems are not statements about the trivial group.
  `Aut(𝕊) = G₂ × S₃` is NOT claimed or used.

* **T4 / #634 AC4 — the local spectrum at a crystal.**
  `left_mul_sq_at_vacuum` : at a vacuum, `s·(s·x) = −N(s)·x` for *every* `x`,
  i.e. `−L_s² = N(s)·id` exactly — the spectrum of `−L_s²` is the single
  degenerate eigenvalue `N(s)`.  `left_mul_sq_scalar_iff_vacuum` shows this
  characterises vacua.  `alternator_expansion_off_vacuum` gives the first-order
  behaviour off the vacuum: for `s = v + ε w` with `v` a vacuum,
  `T_s = ε · laMap v w + ε² · T_w`, so `T_s = O(ε)` with no constant term.
  The transverse Hessian of `V` is NOT attempted.

## Interpretation guardrail (read before citing this file)

The theorems below say **exactly** that a vacuum of the δ-landscape generates a
quaternion subalgebra of 𝕊, that this assignment is natural under algebra
automorphisms, and that the local `−L_s²` spectrum is degenerate there.  They do
**NOT** claim, and must not be cited as claiming, that this quaternion algebra
"is the observer's ℍ" or carries any DERIV-holographic reading — that
interpretation is pending the beekeeper's ruling on ledger flag 3 and is
deliberately absent from every statement here.  No energy, crystallisation or
spacetime semantics appears in any type or theorem statement (layer rule,
`docs/foundations/layer-architecture.md`).

## Completeness

Zero `sorry`, zero `native_decide`, zero vacuous `True`.  `#print axioms` audit
at the bottom: every result depends only on `{propext, Classical.choice,
Quot.sound}`.
-/

namespace QBP.Foundations.CrystalHosting

open QBP.Foundations.CDAlg
open QBP.Foundations.NoAutonomousDynamics

/-! ## 0. The Cayley–Dickson half embeddings `loOf` / `hiOf`

`loOf : 𝕆 → 𝕊` and `hiOf : 𝕆 → 𝕊` are defined in `Alternator.lean` as the two
half embeddings of the pair split `𝕊 = 𝕆 ⊕ 𝕆ℓ`.  This section records their
coordinate behaviour, which the rest of the file needs. -/

section HalfEmbeddings

/-- `hiIdx q` is never the real index. -/
theorem hiIdx_ne_zero : ∀ q : Fin (2^3), hiIdx q ≠ (0 : Fin (2^4)) := by decide

/-- `loIdx p` is the real index exactly when `p` is. -/
theorem loIdx_eq_zero_iff : ∀ p : Fin (2^3), (loIdx p = (0 : Fin (2^4))) ↔ p = 0 := by decide

@[simp] theorem loOf_coord_loIdx (a : CDAlg ℝ 3) (t : Fin (2^3)) :
    (loOf a).coord (loIdx t) = a.coord t := by
  rw [loOf, sum_coord, Finset.sum_eq_single t]
  · rw [smul_coord, e_coord, if_pos rfl, mul_one]
  · intro b _ hb
    rw [smul_coord, e_coord, if_neg (fun h => hb ((loIdx_inj_iff t b).mp h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem loOf_coord_hiIdx (a : CDAlg ℝ 3) (t : Fin (2^3)) :
    (loOf a).coord (hiIdx t) = 0 := by
  rw [loOf, sum_coord]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [smul_coord, e_coord, if_neg (fun h => loIdx_ne_hiIdx b t h.symm), mul_zero]

@[simp] theorem hiOf_coord_hiIdx (b : CDAlg ℝ 3) (t : Fin (2^3)) :
    (hiOf b).coord (hiIdx t) = b.coord t := by
  rw [hiOf, sum_coord, Finset.sum_eq_single t]
  · rw [smul_coord, e_coord, if_pos rfl, mul_one]
  · intro c _ hc
    rw [smul_coord, e_coord, if_neg (fun h => hc ((hiIdx_inj_iff t c).mp h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem hiOf_coord_loIdx (b : CDAlg ℝ 3) (t : Fin (2^3)) :
    (hiOf b).coord (loIdx t) = 0 := by
  rw [hiOf, sum_coord]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  rw [smul_coord, e_coord, if_neg (loIdx_ne_hiIdx t c), mul_zero]

@[simp] theorem cdLo_loOf (a : CDAlg ℝ 3) : cdLo (loOf a) = a := by
  ext p; rw [cdLo_coord, loOf_coord_loIdx]

@[simp] theorem cdHi_loOf (a : CDAlg ℝ 3) : cdHi (loOf a) = 0 := by
  ext q; rw [cdHi_coord, loOf_coord_hiIdx, zero_coord]

@[simp] theorem cdLo_hiOf (b : CDAlg ℝ 3) : cdLo (hiOf b) = 0 := by
  ext p; rw [cdLo_coord, hiOf_coord_loIdx, zero_coord]

@[simp] theorem cdHi_hiOf (b : CDAlg ℝ 3) : cdHi (hiOf b) = b := by
  ext q; rw [cdHi_coord, hiOf_coord_hiIdx]

@[simp] theorem cdLo_zero : cdLo (0 : CDAlg ℝ 4) = 0 := by ext p; rfl

theorem cdLo_neg (x : CDAlg ℝ 4) : cdLo (-x) = -cdLo x := by ext p; rfl
theorem cdHi_neg (x : CDAlg ℝ 4) : cdHi (-x) = -cdHi x := by ext q; rfl
theorem cdLo_sub (x y : CDAlg ℝ 4) : cdLo (x - y) = cdLo x - cdLo y := by ext p; rfl
theorem cdHi_sub (x y : CDAlg ℝ 4) : cdHi (x - y) = cdHi x - cdHi y := by ext q; rfl

@[simp] theorem cdLo_one : cdLo (1 : CDAlg ℝ 4) = 1 := by
  ext p
  rw [cdLo_coord, one_coord, one_coord]
  by_cases h : p = 0
  · rw [if_pos h, if_pos ((loIdx_eq_zero_iff p).mpr h)]
  · rw [if_neg h, if_neg (fun hh => h ((loIdx_eq_zero_iff p).mp hh))]

@[simp] theorem cdHi_one : cdHi (1 : CDAlg ℝ 4) = 0 := by
  ext q; rw [cdHi_coord, one_coord, if_neg (hiIdx_ne_zero q), zero_coord]

@[simp] theorem cdLo_ell' : cdLo ell = 0 := cdLo_ell

@[simp] theorem cdHi_ell : cdHi ell = 1 := by
  rw [ell, cdHi_e_hiIdx]; exact one_def.symm

/-- Two sedenions with equal Cayley–Dickson halves are equal. -/
theorem eq_of_halves {x y : CDAlg ℝ 4} (hlo : cdLo x = cdLo y) (hhi : cdHi x = cdHi y) :
    x = y := by
  ext k
  rcases idx_cases k with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht; exact congrArg (fun z : CDAlg ℝ 3 => z.coord t) hlo
  · subst ht; exact congrArg (fun z : CDAlg ℝ 3 => z.coord t) hhi

/-- The pair split, in `loOf`/`hiOf` form. -/
theorem split_lo_hi (x : CDAlg ℝ 4) : x = loOf (cdLo x) + hiOf (cdHi x) := part_split x

theorem loOf_smul (r : ℝ) (a : CDAlg ℝ 3) : loOf (r • a) = r • loOf a := by
  refine eq_of_halves ?_ ?_
  · rw [cdLo_loOf, cdLo_smul, cdLo_loOf]
  · rw [cdHi_loOf, cdHi_smul, cdHi_loOf, smul_zero]

theorem hiOf_smul' (r : ℝ) (b : CDAlg ℝ 3) : hiOf (r • b) = r • hiOf b := hiOf_smul r b

theorem loOf_add (a a' : CDAlg ℝ 3) : loOf (a + a') = loOf a + loOf a' := by
  refine eq_of_halves ?_ ?_
  · rw [cdLo_loOf, cdLo_add, cdLo_loOf, cdLo_loOf]
  · rw [cdHi_loOf, cdHi_add, cdHi_loOf, cdHi_loOf, add_zero]

theorem loOf_neg (a : CDAlg ℝ 3) : loOf (-a) = -loOf a := by
  refine eq_of_halves ?_ ?_
  · rw [cdLo_loOf, cdLo_neg, cdLo_loOf]
  · rw [cdHi_loOf, cdHi_neg, cdHi_loOf, neg_zero]

theorem hiOf_neg (b : CDAlg ℝ 3) : hiOf (-b) = -hiOf b := by
  refine eq_of_halves ?_ ?_
  · rw [cdLo_hiOf, cdLo_neg, cdLo_hiOf, neg_zero]
  · rw [cdHi_hiOf, cdHi_neg, cdHi_hiOf]

/-- The low-half embedding preserves the norm form. -/
theorem N_loOf (u : CDAlg ℝ 3) : N (loOf u) = N u := by
  rw [N_def, sum_split (fun k => ((loOf u).coord k)^2)]
  have h1 : (∑ p : Fin (2^3), ((loOf u).coord (loIdx p))^2) = N u := by
    rw [N_def]; exact Finset.sum_congr rfl (fun p _ => by rw [loOf_coord_loIdx])
  have h2 : (∑ q : Fin (2^3), ((loOf u).coord (hiIdx q))^2) = 0 :=
    Finset.sum_eq_zero (fun q _ => by rw [loOf_coord_hiIdx]; ring)
  rw [h1, h2, add_zero]

/-- The low-half embedding of an imaginary octonion is imaginary. -/
theorem loOf_coord_zero {u : CDAlg ℝ 3} (hu : u.coord 0 = 0) : (loOf u).coord 0 = 0 := by
  rw [show (0 : Fin (2^4)) = loIdx 0 from loIdx_zero.symm, loOf_coord_loIdx, hu]

/-- The low-half embedding is orthogonal to `ℓ = e₈`. -/
theorem loOf_coord_hi_zero (u : CDAlg ℝ 3) : (loOf u).coord (hiIdx 0) = 0 :=
  loOf_coord_hiIdx u 0

/-- `U · ℓ = hiOf u` — right multiplication by `ℓ` is the CD half shift. -/
theorem loOf_mul_ell (u : CDAlg ℝ 3) : loOf u * ell = hiOf u := by
  refine eq_of_halves ?_ ?_
  · rw [cdLo_mul, cdLo_loOf, cdLo_ell, cdHi_ell, cdHi_loOf, cdLo_hiOf, alt_mul_zero,
      alt_mul_zero, sub_zero]
  · rw [cdHi_mul, cdHi_ell, cdLo_loOf, cdHi_loOf, cdLo_ell, cdHi_hiOf, cd_one_mul,
      alt_zero_mul, add_zero]

/-- `ℓ · U = −hiOf u` for imaginary `u` (the conjugation in the doubling formula). -/
theorem ell_mul_loOf {u : CDAlg ℝ 3} (hu : u.coord 0 = 0) : ell * loOf u = -(hiOf u) := by
  refine eq_of_halves ?_ ?_
  · rw [cdLo_mul, cdLo_ell, cdLo_loOf, cdHi_loOf, cdHi_ell, cd_conj_zero, alt_zero_mul,
      alt_zero_mul, sub_zero, cdLo_neg, cdLo_hiOf, neg_zero]
  · rw [cdHi_mul, cdHi_loOf, cdLo_ell, cdHi_ell, cdLo_loOf, alt_zero_mul, cd_one_mul,
      zero_add, cdHi_neg, cdHi_hiOf, conj_of_imaginary hu]

end HalfEmbeddings

/-! ## 1. Vacua (crystals) and Prop 15 — the parametrisation (#634 AC3) -/

/-- **Vacuum / crystal.**  An imaginary sedenion whose two Cayley–Dickson
    components commute.  By `sedenion_alternator_vanishes_iff_components_commute`
    this is exactly the vanishing of the left alternator `T_s`, i.e. exactly
    `V(s) = ‖[cdLo s, cdHi s]‖² = 0` for the δ-landscape potential. -/
def IsVacuum (s : CDAlg ℝ 4) : Prop :=
  s.coord 0 = 0 ∧ cdLo s * cdHi s = cdHi s * cdLo s

/-- The two characterisations of a vacuum agree: commuting CD components ⇔ the
    left alternator vanishes identically. -/
theorem isVacuum_iff_alternator_flat {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) :
    IsVacuum s ↔ ∀ x, assoc s s x = 0 := by
  constructor
  · rintro ⟨_, hc⟩
    exact (sedenion_alternator_vanishes_iff_components_commute hs).mpr hc
  · intro h
    exact ⟨hs, (sedenion_alternator_vanishes_iff_components_commute hs).mp h⟩

/-! ### Non-vacuity of `IsVacuum`: both sides are realised

Every T1/T2/T4 theorem below is conditioned on `IsVacuum s`, so the predicate
must be neither empty nor universal.  It is neither. -/

/-- **A non-pole crystal exists:** `s = Σ_{a=1}^{15} e_a` is a vacuum (T1 of
    `Alternator.lean`: its alternator vanishes identically). -/
theorem sAll_isVacuum : IsVacuum sAll := ⟨sAll_coord_zero, sAll_components_commute⟩

/-- **The poles are crystals:** `ℓ` itself is a vacuum (its low CD component is
    `0`, so the components commute trivially). -/
theorem ell_isVacuum : IsVacuum ell := by
  refine ⟨ell_coord_zero, ?_⟩
  rw [cdLo_ell, alt_zero_mul, alt_mul_zero]

/-- **Not everything is a crystal:** `s = e₁ + e₁₀` has non-commuting Cayley–
    Dickson components (`Alternator.sedWitX_alternator_ne_zero`), so `IsVacuum`
    is a genuine restriction. -/
theorem sedWitX_not_isVacuum : ¬ IsVacuum sedWitX := by
  intro hv
  exact sedWitX_alternator_ne_zero ((isVacuum_iff_alternator_flat sedWitX_coord_zero).mp hv)

/-- The low component of an imaginary sedenion is an imaginary octonion. -/
theorem cdLo_coord_zero {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : (cdLo s).coord 0 = 0 := by
  rw [cdLo_coord, loIdx_zero, hs]

/-- Conversely: if the low component is imaginary so is `s`. -/
theorem coord_zero_of_cdLo {s : CDAlg ℝ 4} (h : (cdLo s).coord 0 = 0) : s.coord 0 = 0 := by
  rw [cdLo_coord, loIdx_zero] at h; exact h

theorem bil_comm' {n : ℕ} (x y : CDAlg ℝ n) : bil x y = bil y x := by
  rw [bil_def, bil_def]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem N_one' {n : ℕ} : N (1 : CDAlg ℝ n) = 1 := by rw [one_def]; exact N_e 0

/-- **Prop 15 / #634 AC3 — the vacuum parametrisation.**

    A sedenion `s` is a vacuum **iff** its Cayley–Dickson components take the form

      `cdLo s = α • u`,   `cdHi s = b₀ • 1 + γ • u`

    for a single **imaginary octonion direction** `u` (a unit `N u = 1`, or `u = 0`
    at the poles `s ∈ ℝℓ`) and reals `α, γ, b₀`.  Equivalently: `a := cdLo s` and
    `c := Im (cdHi s)` are *parallel*.  This is the geometric form of the
    commuting-components criterion
    (`sedenion_alternator_vanishes_iff_components_commute`), and it is the
    parametrisation of the vacuum manifold.  (The *topology* of the quotient —
    the suspension of ℝP¹, i.e. S² — is not formalised here.) -/
theorem vacuum_iff_parametrised (s : CDAlg ℝ 4) :
    IsVacuum s ↔
      ∃ (u : CDAlg ℝ 3) (α γ b₀ : ℝ),
        u.coord 0 = 0 ∧ (N u = 1 ∨ u = 0) ∧
        cdLo s = α • u ∧ cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • u := by
  constructor
  · rintro ⟨hs, hcomm⟩
    have ha0 : (cdLo s).coord 0 = 0 := cdLo_coord_zero hs
    by_cases ha : cdLo s = 0
    · -- pole-ish case: the low component vanishes; take the direction of `Im (cdHi s)`
      set b₀ : ℝ := (cdHi s).coord 0 with hb₀
      set c : CDAlg ℝ 3 := cdHi s - b₀ • (1 : CDAlg ℝ 3) with hc
      have hc0 : c.coord 0 = 0 := QBP.Foundations.DeltaLandscape.im_coord_zero (cdHi s)
      by_cases hcz : c = 0
      · refine ⟨0, 0, 0, b₀, rfl, Or.inr rfl, by rw [ha]; module, ?_⟩
        have hb : cdHi s = b₀ • (1 : CDAlg ℝ 3) := sub_eq_zero.mp hcz
        rw [hb]; module
      · have hNc : 0 < N c :=
          lt_of_le_of_ne (alt_N_nonneg c) (fun h => hcz ((alt_N_eq_zero_iff c).mp h.symm))
        set r : ℝ := Real.sqrt (N c) with hr
        have hr2 : r^2 = N c := Real.sq_sqrt (le_of_lt hNc)
        have hrpos : 0 < r := Real.sqrt_pos.mpr hNc
        have hrne : r ≠ 0 := ne_of_gt hrpos
        refine ⟨r⁻¹ • c, 0, r, b₀, ?_, Or.inl ?_, ?_, ?_⟩
        · rw [smul_coord, hc0, mul_zero]
        · rw [N_smul, ← hr2]; field_simp
        · rw [ha]; module
        · rw [smul_smul, mul_inv_cancel₀ hrne, one_smul, hc]; module
    · -- generic case: the octonion commutant forces `cdHi s ∈ span{1, cdLo s}`
      have hspan := octonion_commutant ha0 ha hcomm
      have hNa : 0 < N (cdLo s) :=
        lt_of_le_of_ne (alt_N_nonneg _) (fun h => ha ((alt_N_eq_zero_iff _).mp h.symm))
      set r : ℝ := Real.sqrt (N (cdLo s)) with hr
      have hr2 : r^2 = N (cdLo s) := Real.sq_sqrt (le_of_lt hNa)
      have hrpos : 0 < r := Real.sqrt_pos.mpr hNa
      have hrne : r ≠ 0 := ne_of_gt hrpos
      refine ⟨r⁻¹ • cdLo s, r, (bil (cdLo s) (cdHi s) / N (cdLo s)) * r, (cdHi s).coord 0,
        ?_, Or.inl ?_, ?_, ?_⟩
      · rw [smul_coord, ha0, mul_zero]
      · rw [N_smul, ← hr2]; field_simp
      · rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
      · rw [smul_smul, mul_assoc, mul_inv_cancel₀ hrne, mul_one]
        exact hspan
  · rintro ⟨u, α, γ, b₀, hu0, _, hlo, hhi⟩
    refine ⟨?_, ?_⟩
    · refine coord_zero_of_cdLo ?_
      rw [hlo, smul_coord, hu0, mul_zero]
    · simp only [hlo, hhi, mul_add_left, mul_add_right, mul_smul_left, mul_smul_right,
        cd_mul_one, cd_one_mul]
      module

/-- **The norm form in the Prop 15 parametrisation:** `N s = α² + γ² + b₀²`.
    On the unit sphere (`N s = 1`) this is the doc's
    `(a, Im b) = √(1 − b₀²)·(cos θ, sin θ)·u`. -/
theorem vacuum_norm_parametrised {s : CDAlg ℝ 4} {u : CDAlg ℝ 3} {α γ b₀ : ℝ}
    (hu0 : u.coord 0 = 0) (hNu : N u = 1)
    (hlo : cdLo s = α • u) (hhi : cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • u) :
    N s = α^2 + γ^2 + b₀^2 := by
  have hbil : bil (b₀ • (1 : CDAlg ℝ 3)) (γ • u) = 0 := by
    rw [bil_smul_left, bil_smul_right, bil_comm' (1 : CDAlg ℝ 3) u, bil_one_right, hu0]
    ring
  rw [N_split s, hlo, hhi, N_smul, hNu, alt_N_add, hbil, N_smul, N_smul, hNu, N_one']
  ring

/-! ## 2. T1 — every crystal carries a quaternion subalgebra -/

section Hosting

variable {u : CDAlg ℝ 3}

/-- **The quaternion multiplication table on `{1, ℓ, U, ℓU}`, `U = loOf u`.**
    For a *unit imaginary* octonion direction `u`, the four elements
    `1, ℓ, U, ℓU` of 𝕊 satisfy exactly the quaternion relations with
    `i = ℓ`, `j = U`, `k = ℓU`:

      `ℓ² = U² = (ℓU)² = −1`,  `Uℓ = −ℓU`,  `U(ℓU) = ℓ`,  `(ℓU)U = −ℓ`,
      `ℓ(ℓU) = −U`.

    (𝕊 is neither associative nor alternative, so the last three rows are not
    automatic; they come from `assoc_self_ell` via `p_mul_ell_p`.) -/
theorem crystal_quaternion_table (hu0 : u.coord 0 = 0) (hNu : N u = 1) :
    ell * ell = -(1 : CDAlg ℝ 4) ∧
    loOf u * loOf u = -(1 : CDAlg ℝ 4) ∧
    (ell * loOf u) * (ell * loOf u) = -(1 : CDAlg ℝ 4) ∧
    loOf u * ell = -(ell * loOf u) ∧
    loOf u * (ell * loOf u) = ell ∧
    (ell * loOf u) * loOf u = -ell ∧
    ell * (ell * loOf u) = -loOf u := by
  have hU0 : (loOf u).coord 0 = 0 := loOf_coord_zero hu0
  have hU8 : (loOf u).coord (hiIdx 0) = 0 := loOf_coord_hi_zero u
  have hNU : N (loOf u) = 1 := by rw [N_loOf, hNu]
  refine ⟨ell_sq, ?_, ?_, p_ell_anticomm hU0 hU8, ?_, ?_, ell_ell_mul _⟩
  · rw [p_sq hU0, hNU]; module
  · rw [ell_p_sq hU8, hNU]; module
  · rw [p_mul_ell_p hU0 hU8, hNU, one_smul]
  · rw [ell_p_mul_p hU0 hU8, hNU, one_smul]

/-- The low Cayley–Dickson component of a `{1, ℓ, U, ℓU}`-combination. -/
theorem cdLo_quatComb (a b c d : ℝ) (hu0 : u.coord 0 = 0) :
    cdLo (a • (1 : CDAlg ℝ 4) + b • ell + c • loOf u + d • (ell * loOf u))
      = a • (1 : CDAlg ℝ 3) + c • u := by
  rw [ell_mul_loOf hu0, cdLo_add, cdLo_add, cdLo_add, cdLo_smul, cdLo_smul, cdLo_smul,
    cdLo_smul, cdLo_one, cdLo_ell, cdLo_loOf, cdLo_neg, cdLo_hiOf, neg_zero]
  module

/-- The high Cayley–Dickson component of a `{1, ℓ, U, ℓU}`-combination. -/
theorem cdHi_quatComb (a b c d : ℝ) (hu0 : u.coord 0 = 0) :
    cdHi (a • (1 : CDAlg ℝ 4) + b • ell + c • loOf u + d • (ell * loOf u))
      = b • (1 : CDAlg ℝ 3) + (-d) • u := by
  rw [ell_mul_loOf hu0, cdHi_add, cdHi_add, cdHi_add, cdHi_smul, cdHi_smul, cdHi_smul,
    cdHi_smul, cdHi_one, cdHi_ell, cdHi_loOf, cdHi_neg, cdHi_hiOf]
  module

/-- Reading off the real coefficient of a `span{1, u}` relation in 𝕆. -/
theorem coeff_zero_of_span_one_u {r t : ℝ} (hu0 : u.coord 0 = 0)
    (h : r • (1 : CDAlg ℝ 3) + t • u = 0) : r = 0 := by
  have h2 : (r • (1 : CDAlg ℝ 3) + t • u).coord 0 = (0 : CDAlg ℝ 3).coord 0 := by rw [h]
  rw [add_coord, smul_coord, smul_coord, one_coord, if_pos rfl, hu0, mul_one, mul_zero,
    add_zero, zero_coord] at h2
  exact h2

/-- **The hosted subalgebra is genuinely 4-dimensional.**  For a unit imaginary
    direction `u`, the four sedenions `1, ℓ, U, ℓU` (`U = loOf u`) are linearly
    independent over ℝ — so `span{1, ℓ, U, ℓU}` is a 4-dimensional subspace of
    the 16-dimensional 𝕊, i.e. an isomorphic copy of ℍ and not a degenerate
    span. -/
theorem crystal_quatSpan_independent (hu0 : u.coord 0 = 0) (hNu : N u = 1)
    {a b c d : ℝ}
    (h : a • (1 : CDAlg ℝ 4) + b • ell + c • loOf u + d • (ell * loOf u) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hlo : a • (1 : CDAlg ℝ 3) + c • u = 0 := by
    have h2 := cdLo_quatComb (u := u) a b c d hu0
    rw [h, cdLo_zero] at h2; exact h2.symm
  have hhi : b • (1 : CDAlg ℝ 3) + (-d) • u = 0 := by
    have h2 := cdHi_quatComb (u := u) a b c d hu0
    rw [h, cdHi_zero] at h2; exact h2.symm
  have ha : a = 0 := coeff_zero_of_span_one_u hu0 hlo
  have hb : b = 0 := coeff_zero_of_span_one_u hu0 hhi
  have hc : c = 0 := by
    rw [ha, zero_smul, zero_add] at hlo
    have hsq : c^2 = 0 := by
      have := congrArg N hlo
      rw [N_smul, hNu, mul_one, N_zero] at this
      exact this
    exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hsq
  have hd : d = 0 := by
    rw [hb, zero_smul, zero_add] at hhi
    have hsq : (-d)^2 = 0 := by
      have := congrArg N hhi
      rw [N_smul, hNu, mul_one, N_zero] at this
      exact this
    have : -d = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hsq
    linarith
  exact ⟨ha, hb, hc, hd⟩

/-- The Cayley–Dickson components of a member of `span{1, ℓ, U, ℓU}` both lie in
    the octonion plane `span{1, u}`. -/
theorem cdLo_mem_span_one_u (hu0 : u.coord 0 = 0) {x : CDAlg ℝ 4}
    (hx : InQuatSpan (loOf u) x) : ∃ a c : ℝ, cdLo x = a • (1 : CDAlg ℝ 3) + c • u := by
  obtain ⟨a, b, c, d, h⟩ := hx
  exact ⟨a, c, by rw [h, cdLo_quatComb a b c d hu0]⟩

/-- Reading off an imaginary coordinate of a `span{1, u}` element. -/
theorem span_one_u_coord {x : CDAlg ℝ 3} {a c : ℝ}
    (h : x = a • (1 : CDAlg ℝ 3) + c • u) {k : Fin (2^3)} (hk : k ≠ 0) :
    x.coord k = c * u.coord k := by
  rw [h, add_coord, smul_coord, smul_coord, one_coord, if_neg hk, mul_zero, zero_add]

/-- **The hosted subalgebra is a PROPER subspace of 𝕊.**  Whatever the imaginary
    direction `u`, `span{1, ℓ, U, ℓU}` is not all of the 16-dimensional 𝕊: an
    explicit witness outside it is one of `loOf e₁`, `loOf e₂`.  Together with
    `crystal_quatSpan_independent` (exactly 4 independent generators) this makes
    `vacuum_hosts_quaternion` a genuine containment in a 4-dimensional
    subalgebra, not a vacuous one. -/
theorem quatSpan_dir_proper (hu0 : u.coord 0 = 0) :
    ∃ z : CDAlg ℝ 4, ¬ InQuatSpan (loOf u) z := by
  by_contra hcon
  push Not at hcon
  have hi1 : (1 : Fin (2^3)) ≠ 0 := by decide
  have hi2 : (2 : Fin (2^3)) ≠ 0 := by decide
  have hne : (2 : Fin (2^3)) ≠ (1 : Fin (2^3)) := by decide
  obtain ⟨a1, c1, h1⟩ := cdLo_mem_span_one_u hu0 (hcon (loOf (e (1 : Fin (2^3)))))
  obtain ⟨a2, c2, h2⟩ := cdLo_mem_span_one_u hu0 (hcon (loOf (e (2 : Fin (2^3)))))
  rw [cdLo_loOf] at h1 h2
  have k11 : (1 : ℝ) = c1 * u.coord (1 : Fin (2^3)) := by
    have h := span_one_u_coord h1 hi1
    rwa [e_coord, if_pos rfl] at h
  have k12 : (0 : ℝ) = c1 * u.coord (2 : Fin (2^3)) := by
    have h := span_one_u_coord h1 hi2
    rwa [e_coord, if_neg hne] at h
  have k22 : (1 : ℝ) = c2 * u.coord (2 : Fin (2^3)) := by
    have h := span_one_u_coord h2 hi2
    rwa [e_coord, if_pos rfl] at h
  have hc1 : c1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at k11; norm_num at k11
  have hu2 : u.coord (2 : Fin (2^3)) = 0 := (mul_eq_zero.mp k12.symm).resolve_left hc1
  rw [hu2, mul_zero] at k22
  norm_num at k22

/-- Re-basing `InQuatSpan`: if `p` lies in `span{U, ℓU}` then
    `span{1, ℓ, p, ℓp} ⊆ span{1, ℓ, U, ℓU}`. -/
theorem inQuatSpan_of_dir {U p : CDAlg ℝ 4} {α γ : ℝ}
    (hp : p = α • U + γ • (ell * U)) {x : CDAlg ℝ 4} (hx : InQuatSpan p x) :
    InQuatSpan U x := by
  obtain ⟨a, b, c, d, hx⟩ := hx
  have hlp : ell * p = α • (ell * U) - γ • U := by
    rw [hp, mul_add_right, mul_smul_right, mul_smul_right, ell_ell_mul]
    module
  refine ⟨a, b, c * α - d * γ, c * γ + d * α, ?_⟩
  rw [hx, hlp, hp]
  module

/-- **The span in the `u·ℓ` orientation** (the doc's `span{1, u, ℓ, uℓ}`).
    Since `U ℓ = −ℓ U` for imaginary `u` (`loOf_mul_ell` / `ell_mul_loOf`), the
    two orientations span the same 4-dimensional space, so `InQuatSpan (loOf u)`
    may be read either way. -/
theorem inQuatSpan_ell_right (hu0 : u.coord 0 = 0) {x : CDAlg ℝ 4} :
    InQuatSpan (loOf u) x ↔
      ∃ a b c d : ℝ,
        x = a • (1 : CDAlg ℝ 4) + b • ell + c • loOf u + d • (loOf u * ell) := by
  have h : loOf u * ell = -(ell * loOf u) := by
    rw [loOf_mul_ell, ell_mul_loOf hu0, neg_neg]
  constructor
  · rintro ⟨a, b, c, d, hx⟩
    exact ⟨a, b, c, -d, by rw [hx, h]; module⟩
  · rintro ⟨a, b, c, d, hx⟩
    exact ⟨a, b, c, -d, by rw [hx, h]; module⟩

/-! ### The P2′ reading of the hosted algebra (#649)

The two lemmas below carry the whole mathematical content of the P2′ statement.
For a unit imaginary octonion direction `u`, write `U = loOf u` and
`ℂ_u = span_ℝ{1, U}`.  Then

* the hosted quaternion algebra `ℍ_u = span_ℝ{1, ℓ, U, ℓU}` meets the
  Cayley–Dickson **low half** `𝕆 = {x : cdHi x = 0}` in exactly `ℂ_u`
  (`quatSpan_inter_lowHalf`), and
* `ℍ_u` is exactly the Cayley–Dickson double `ℂ_u ⊕ ℂ_u·ℓ` of that `ℂ_u`
  (`quatSpan_eq_cd_double`).

So "the crystal picks out one ℂ inside 𝕆" and "the crystal hosts an ℍ inside 𝕊"
are the *same* datum read at two levels of the tower — a single discrete root,
not a ℂP² of them.  Neither statement identifies `ℂ_u` with any physical
observable; that reading is the (still open) DERIV-holographic flag 3. -/

/-- **P2′ (i) — the hosted algebra meets the CD low half in exactly `ℂ_u`.**
    For a unit imaginary octonion direction `u` (`U = loOf u`), an element of
    `span{1, ℓ, U, ℓU}` has vanishing high Cayley–Dickson component **iff** it
    lies in the plane `span{1, U}` — the copy of ℂ generated by `U`.  In symbols
    `ℍ_u ∩ 𝕆 = ℂ_u`. -/
theorem quatSpan_inter_lowHalf (hu0 : u.coord 0 = 0) (hNu : N u = 1)
    {x : CDAlg ℝ 4} :
    (InQuatSpan (loOf u) x ∧ cdHi x = 0) ↔
      ∃ a c : ℝ, x = a • (1 : CDAlg ℝ 4) + c • loOf u := by
  constructor
  · rintro ⟨⟨a, b, c, d, hx⟩, hhi⟩
    have hb : b • (1 : CDAlg ℝ 3) + (-d) • u = 0 := by
      have h2 := cdHi_quatComb (u := u) a b c d hu0
      rw [← hx, hhi] at h2
      exact h2.symm
    have hb0 : b = 0 := coeff_zero_of_span_one_u hu0 hb
    have hd0 : d = 0 := by
      rw [hb0, zero_smul, zero_add] at hb
      have hsq : (-d) ^ 2 = 0 := by
        have hN := congrArg N hb
        rw [N_smul, hNu, mul_one, N_zero] at hN
        exact hN
      have hneg : -d = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
      linarith
    exact ⟨a, c, by rw [hx, hb0, hd0]; module⟩
  · rintro ⟨a, c, hx⟩
    refine ⟨⟨a, 0, c, 0, by rw [hx]; module⟩, ?_⟩
    rw [hx, cdHi_add, cdHi_smul, cdHi_smul, cdHi_one, cdHi_loOf, smul_zero, smul_zero,
      add_zero]

/-- **P2′ (ii) — the hosted algebra is the Cayley–Dickson double of `ℂ_u` by `ℓ`.**
    Every element of `span{1, ℓ, U, ℓU}` is of the form `z + w·ℓ` with
    `z, w ∈ ℂ_u = span{1, U}`, and conversely every such `z + w·ℓ` lies in the
    span.  This is `ℍ_u = ℂ_u ⊕ ℂ_u·ℓ`, the doubling step ℂ → ℍ, read inside 𝕊. -/
theorem quatSpan_eq_cd_double (hu0 : u.coord 0 = 0) {x : CDAlg ℝ 4} :
    InQuatSpan (loOf u) x ↔
      ∃ a c b d : ℝ, x = (a • (1 : CDAlg ℝ 4) + c • loOf u)
        + (b • (1 : CDAlg ℝ 4) + d • loOf u) * ell := by
  have hexp : ∀ b d : ℝ, (b • (1 : CDAlg ℝ 4) + d • loOf u) * ell
      = b • ell + d • (loOf u * ell) := by
    intro b d
    rw [mul_add_left, mul_smul_left, mul_smul_left, cd_one_mul]
  rw [inQuatSpan_ell_right hu0]
  constructor
  · rintro ⟨a, b, c, d, hx⟩
    exact ⟨a, c, b, d, by rw [hx, hexp]; module⟩
  · rintro ⟨a, c, b, d, hx⟩
    exact ⟨a, b, c, d, by rw [hx, hexp]; module⟩

/-- **T1 — every crystal carries a quaternion subalgebra.**

    Let `s` be a vacuum (crystal): imaginary with commuting Cayley–Dickson
    components.  Then there is a single octonion direction `u` — a *unit*
    imaginary octonion, or `0` exactly at the poles `s ∈ ℝℓ` — such that

    * `cdLo s ∈ ℝ·u`  and  `Im (cdHi s) ∈ ℝ·u`  (the Prop 15 parallelism), and
    * **every** word in `{1, s, ℓ}` — built from the algebra's own operations
      `+`, real scaling, the sedenion product and conjugation — lies in
      `span_ℝ{1, ℓ, U, ℓU}` with `U := loOf u` the low-half embedding of `u`.

    With `crystal_quaternion_table` (the quaternion relations on the generators)
    and `crystal_quatSpan_independent` (4-dimensionality for `N u = 1`), this is
    the statement that the crystal *hosts a copy of ℍ*.

    **Interpretation guardrail:** this says only that the generated subalgebra is
    a quaternion algebra.  No identification of it with "the observer's ℍ", and
    no DERIV-holographic reading, is claimed here (pending the beekeeper's ruling
    on ledger flag 3). -/
theorem vacuum_hosts_quaternion {s : CDAlg ℝ 4} (hv : IsVacuum s) :
    ∃ (u : CDAlg ℝ 3) (α γ b₀ : ℝ),
      u.coord 0 = 0 ∧ (N u = 1 ∨ u = 0) ∧
      cdLo s = α • u ∧ cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • u ∧
      (∀ x, GenByPair s ell x → InQuatSpan (loOf u) x) := by
  obtain ⟨u, α, γ, b₀, hu0, hNu, hlo, hhi⟩ := (vacuum_iff_parametrised s).mp hv
  refine ⟨u, α, γ, b₀, hu0, hNu, hlo, hhi, ?_⟩
  intro x hx
  have hgen := genByPair_ell_mem_quatSpan s hv.1 x hx
  -- `p := s − s₈·ℓ` is `α • U − γ • (ℓ U)`, so its quaternion span re-bases onto `U`
  refine inQuatSpan_of_dir (α := α) (γ := -γ) ?_ hgen
  have hs8 : s.coord (hiIdx 0) = b₀ := by
    have : (cdHi s).coord 0 = b₀ := by
      rw [hhi, add_coord, smul_coord, smul_coord, one_coord, if_pos rfl, hu0, mul_one,
        mul_zero, add_zero]
    rw [← this, cdHi_coord]
  have hplo : cdLo (s - (s.coord (hiIdx 0)) • ell) = α • u := by
    rw [cdLo_sub, cdLo_smul, cdLo_ell, smul_zero, sub_zero, hlo]
  have hphi : cdHi (s - (s.coord (hiIdx 0)) • ell) = γ • u := by
    rw [cdHi_sub, cdHi_smul, cdHi_ell, hhi, hs8]
    module
  rw [split_lo_hi (s - (s.coord (hiIdx 0)) • ell), hplo, hphi, loOf_smul, hiOf_smul,
    ell_mul_loOf hu0]
  module

/-- **The pole case is honest.**  If the direction `u` supplied by
    `vacuum_hosts_quaternion` is `0`, then `s` is a real multiple of `ℓ` and the
    hosted algebra degenerates to `span{1, ℓ} ≅ ℂ`. -/
theorem vacuum_pole_of_dir_zero {s : CDAlg ℝ 4} {α γ b₀ : ℝ}
    (hlo : cdLo s = α • (0 : CDAlg ℝ 3))
    (hhi : cdHi s = b₀ • (1 : CDAlg ℝ 3) + γ • (0 : CDAlg ℝ 3)) :
    s = b₀ • ell := by
  refine eq_of_halves ?_ ?_
  · rw [hlo, cdLo_smul, cdLo_ell, smul_zero, smul_zero]
  · rw [hhi, cdHi_smul, cdHi_ell, smul_zero, add_zero]

end Hosting

/-! ## 3. T2 — automorphisms of `CDAlg ℝ n` and equivariance of the assignment

`CDAlg ℝ n` is deliberately **not** a `Ring` (𝕆 is non-associative, 𝕊 is
non-alternative), so Mathlib's `AlgEquiv` / `AlgHom` do not apply.  `CDAut n`
below is the minimal replacement: an ℝ-linear multiplicative bijection.  Note
that `map_one`, and the preservation of the real part and of the norm form, are
*derived*, not assumed. -/

/-- An ℝ-algebra automorphism of the (non-associative) Cayley–Dickson algebra
    `CDAlg ℝ n`: an ℝ-linear multiplicative bijection. -/
structure CDAut (n : ℕ) where
  /-- The underlying map. -/
  toFun : CDAlg ℝ n → CDAlg ℝ n
  /-- Additivity. -/
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- ℝ-homogeneity. -/
  map_smul : ∀ (r : ℝ) (x), toFun (r • x) = r • toFun x
  /-- Multiplicativity. -/
  map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y
  /-- Bijectivity. -/
  bijective : Function.Bijective toFun

namespace CDAut

instance {n : ℕ} : CoeFun (CDAut n) (fun _ => CDAlg ℝ n → CDAlg ℝ n) := ⟨CDAut.toFun⟩

variable {n : ℕ} (φ : CDAut n)

theorem injective : Function.Injective φ.toFun := φ.bijective.1
theorem surjective : Function.Surjective φ.toFun := φ.bijective.2

theorem map_zero : φ (0 : CDAlg ℝ n) = 0 := by
  have h := φ.map_smul 0 0
  rwa [zero_smul, zero_smul] at h

theorem map_neg (x : CDAlg ℝ n) : φ (-x) = -φ x := by
  have h := φ.map_smul (-1) x
  rwa [neg_one_smul, neg_one_smul] at h

theorem map_sub (x y : CDAlg ℝ n) : φ (x - y) = φ x - φ y := by
  rw [sub_eq_add_neg, φ.map_add, φ.map_neg, ← sub_eq_add_neg]

/-- **`φ 1 = 1` is forced, not assumed.**  `φ 1` is a left identity by
    multiplicativity + surjectivity, and `1` is a two-sided identity. -/
theorem map_one : φ (1 : CDAlg ℝ n) = 1 := by
  have h : ∀ y : CDAlg ℝ n, φ 1 * y = y := by
    intro y
    obtain ⟨z, hz⟩ := φ.surjective y
    rw [← hz, ← φ.map_mul, cd_one_mul]
  have h1 := h 1
  rwa [cd_mul_one] at h1

/-- Conjugation is polynomial in the real part: `x̄ = (2 Re x)·1 − x`. -/
theorem conj_eq_two_re_sub (x : CDAlg ℝ n) :
    conj x = (2 * x.coord 0) • (1 : CDAlg ℝ n) - x := by
  ext i
  rw [conj_coord, sub_coord, smul_coord, one_coord]
  by_cases h : i.val = 0
  · have hi : i = 0 := Fin.ext h
    rw [if_pos h, hi, if_pos rfl, mul_one]; ring
  · have hi : i ≠ 0 := fun hh => h (by rw [hh]; rfl)
    rw [if_neg h, if_neg hi, mul_zero, zero_sub]

/-- **Automorphisms preserve the real part and the norm form.**  Derived from the
    Cayley–Dickson square identity `x·x = (2 Re x)·x − N(x)·1` (`cdAlg_sq_eq`)
    plus injectivity — *not* assumed.  So every `CDAut n` is an isometry of `N`
    fixing `ℝ·1` pointwise on real parts, hence maps imaginary elements to
    imaginary elements. -/
theorem map_re_and_N (x : CDAlg ℝ n) :
    (φ x).coord 0 = x.coord 0 ∧ N (φ x) = N x := by
  have h1 : φ x * φ x = (2 * x.coord 0) • φ x - (N x) • (1 : CDAlg ℝ n) := by
    rw [← φ.map_mul, cdAlg_sq_eq x, φ.map_sub, φ.map_smul, φ.map_smul, φ.map_one]
  have h2 : φ x * φ x = (2 * (φ x).coord 0) • φ x - (N (φ x)) • (1 : CDAlg ℝ n) :=
    cdAlg_sq_eq (φ x)
  have heq : (2 * x.coord 0) • φ x - (N x) • (1 : CDAlg ℝ n)
      = (2 * (φ x).coord 0) • φ x - (N (φ x)) • (1 : CDAlg ℝ n) := h1.symm.trans h2
  set μ : ℝ := 2 * x.coord 0 - 2 * (φ x).coord 0 with hμdef
  set ν : ℝ := N x - N (φ x) with hνdef
  have hkey : μ • φ x = ν • (1 : CDAlg ℝ n) := by
    have hz : μ • φ x - ν • (1 : CDAlg ℝ n) = 0 := by
      rw [hμdef, hνdef, sub_smul, sub_smul,
        show ((2 * x.coord 0) • φ x - (2 * (φ x).coord 0) • φ x)
              - ((N x) • (1 : CDAlg ℝ n) - (N (φ x)) • (1 : CDAlg ℝ n))
            = ((2 * x.coord 0) • φ x - (N x) • (1 : CDAlg ℝ n))
              - ((2 * (φ x).coord 0) • φ x - (N (φ x)) • (1 : CDAlg ℝ n)) from by abel,
        heq, sub_self]
    exact sub_eq_zero.mp hz
  by_cases hμ : μ = 0
  · have hν0 : ν • (1 : CDAlg ℝ n) = 0 := by rw [← hkey, hμ, zero_smul]
    have hν : ν = 0 := by
      have h0 : (ν • (1 : CDAlg ℝ n)).coord 0 = (0 : CDAlg ℝ n).coord 0 := by rw [hν0]
      rw [smul_coord, one_coord, if_pos rfl, mul_one, zero_coord] at h0
      exact h0
    rw [hμdef] at hμ
    rw [hνdef] at hν
    exact ⟨by linarith, by linarith⟩
  · exfalso
    have hphi : φ x = (μ⁻¹ * ν) • (1 : CDAlg ℝ n) := by
      have h2' : μ⁻¹ • (μ • φ x) = μ⁻¹ • (ν • (1 : CDAlg ℝ n)) := by rw [hkey]
      rwa [smul_smul, inv_mul_cancel₀ hμ, one_smul, smul_smul] at h2'
    have hx1 : x = (μ⁻¹ * ν) • (1 : CDAlg ℝ n) := by
      apply φ.injective
      rw [show φ.toFun x = φ x from rfl, hphi, φ.map_smul, φ.map_one]
    have hxc : x.coord 0 = μ⁻¹ * ν := by
      rw [hx1, smul_coord, one_coord, if_pos rfl, mul_one]
    have hyc : (φ x).coord 0 = μ⁻¹ * ν := by
      rw [hphi, smul_coord, one_coord, if_pos rfl, mul_one]
    apply hμ
    rw [hμdef, hxc, hyc]
    ring

theorem map_re (x : CDAlg ℝ n) : (φ x).coord 0 = x.coord 0 := (φ.map_re_and_N x).1
theorem map_N (x : CDAlg ℝ n) : N (φ x) = N x := (φ.map_re_and_N x).2

/-- Automorphisms commute with Cayley–Dickson conjugation (a consequence of
    `map_re`, since `x̄` is polynomial in `Re x` and `x`). -/
theorem map_conj (x : CDAlg ℝ n) : φ (conj x) = conj (φ x) := by
  rw [conj_eq_two_re_sub, conj_eq_two_re_sub, φ.map_sub, φ.map_smul, φ.map_one, φ.map_re x]

/-- Automorphisms intertwine associators. -/
theorem map_assoc (x y z : CDAlg ℝ n) : φ (assoc x y z) = assoc (φ x) (φ y) (φ z) := by
  rw [assoc, assoc, φ.map_sub, φ.map_mul, φ.map_mul, φ.map_mul, φ.map_mul]

end CDAut

/-! ### T2(i) — automorphisms map vacua to vacua -/

/-- The alternator-flatness condition transports along automorphisms:
    `T_{φ s}(φ x) = φ (T_s x)` and `φ` is onto, so `T_s ≡ 0 ⟹ T_{φ s} ≡ 0`. -/
theorem aut_alternator_flat (φ : CDAut 4) {s : CDAlg ℝ 4} (h : ∀ x, assoc s s x = 0) :
    ∀ x, assoc (φ s) (φ s) x = 0 := by
  intro x
  obtain ⟨y, hy⟩ := φ.surjective x
  rw [show φ.toFun y = φ y from rfl] at hy
  rw [← hy, ← φ.map_assoc, h y, φ.map_zero]

/-- **T2(i) — the crystal condition is `Aut`-invariant.**  If `s` is a vacuum and
    `φ` is any ℝ-algebra automorphism of `CDAlg ℝ 4`, then `φ s` is a vacuum.
    (Proved through the alternator characterisation, using that `φ` preserves the
    real part — `CDAut.map_re` — so `φ s` is again imaginary.) -/
theorem aut_map_isVacuum (φ : CDAut 4) {s : CDAlg ℝ 4} (hv : IsVacuum s) :
    IsVacuum (φ s) := by
  have hs0 : (φ s).coord 0 = 0 := by rw [φ.map_re s, hv.1]
  exact (isVacuum_iff_alternator_flat hs0).mpr
    (aut_alternator_flat φ ((isVacuum_iff_alternator_flat hv.1).mp hv))

/-! ### T2(ii) — the generated subalgebra is carried onto the generated subalgebra -/

/-- **Words transport:** every word in `{1, s, t}` is carried by an automorphism
    to a word in `{1, φ s, φ t}`. -/
theorem aut_genByPair (φ : CDAut 4) {s t : CDAlg ℝ 4} :
    ∀ x, GenByPair s t x → GenByPair (φ s) (φ t) (φ x) := by
  intro x hx
  induction hx with
  | one => rw [φ.map_one]; exact GenByPair.one
  | left => exact GenByPair.left
  | right => exact GenByPair.right
  | add _ _ ih1 ih2 => rw [φ.map_add]; exact GenByPair.add ih1 ih2
  | smul r _ ih => rw [φ.map_smul]; exact GenByPair.smul r ih
  | mul _ _ ih1 ih2 => rw [φ.map_mul]; exact GenByPair.mul ih1 ih2
  | conj _ ih => rw [φ.map_conj]; exact GenByPair.conj ih

/-- **T2(ii) — the hosted subalgebra is carried ONTO the hosted subalgebra.**
    For an automorphism `φ` fixing the Cayley–Dickson doubling unit `ℓ` (this is
    how the `G₂` factor of `Aut(𝕊)` acts: `a + bℓ ↦ ψ(a) + ψ(b)ℓ`), the image of
    `span{1, ℓ, p, ℓp}` under `φ` is exactly `span{1, ℓ, φ p, ℓ (φ p)}`. -/
theorem aut_image_quatSpan (φ : CDAut 4) (hφ : φ ell = ell) (p y : CDAlg ℝ 4) :
    InQuatSpan (φ p) y ↔ ∃ x, InQuatSpan p x ∧ φ x = y := by
  constructor
  · rintro ⟨a, b, c, d, hy⟩
    refine ⟨a • (1 : CDAlg ℝ 4) + b • ell + c • p + d • (ell * p), ⟨a, b, c, d, rfl⟩, ?_⟩
    rw [φ.map_add, φ.map_add, φ.map_add, φ.map_smul, φ.map_smul, φ.map_smul, φ.map_smul,
      φ.map_one, hφ, φ.map_mul, hφ, hy]
  · rintro ⟨x, ⟨a, b, c, d, hx⟩, hxy⟩
    refine ⟨a, b, c, d, ?_⟩
    rw [← hxy, hx, φ.map_add, φ.map_add, φ.map_add, φ.map_smul, φ.map_smul, φ.map_smul,
      φ.map_smul, φ.map_one, hφ, φ.map_mul, hφ]

/-- **T2 packaged — `Aut`-equivariance of the hosting assignment.**  For an
    automorphism `φ` of `CDAlg ℝ 4` fixing `ℓ`: `φ s` is again a crystal, and
    `φ` carries the subalgebra generated by `{1, s, ℓ}` into the subalgebra
    generated by `{1, φ s, ℓ}`.  So `s ↦ ⟨1, s, ℓ⟩` is natural in `s`.
    (`Aut(𝕊) = G₂ × S₃` is neither claimed nor used.) -/
theorem aut_hosting_equivariant (φ : CDAut 4) (hφ : φ ell = ell) {s : CDAlg ℝ 4}
    (hv : IsVacuum s) :
    IsVacuum (φ s) ∧ (∀ x, GenByPair s ell x → GenByPair (φ s) ell (φ x)) := by
  refine ⟨aut_map_isVacuum φ hv, fun x hx => ?_⟩
  have h := aut_genByPair φ x hx
  rwa [hφ] at h

/-! ### Non-vacuity of `CDAut 4`: an explicit non-identity automorphism

The Cayley–Dickson *grade* map `(a, b) ↦ (a, −b)` is an algebra automorphism of
`𝕊 = 𝕆 ⊕ 𝕆ℓ` (it is the ℤ/2 inside the `S₃` factor of `Aut(𝕊)`), and it sends
`ℓ ↦ −ℓ`, so it is not the identity.  This keeps every `∀ φ : CDAut 4` statement
above from being about a one-element type. -/

/-- The Cayley–Dickson grade sign: `+1` on the low half `𝕆`, `−1` on `𝕆ℓ`. -/
def hiSign (k : Fin (2^4)) : Int := if k.val < 2^3 then 1 else -1

theorem hiSign_xor : ∀ i j : Fin (2^4), hiSign (i ^^^ j) = hiSign i * hiSign j := by decide

theorem hiSign_sq : ∀ k : Fin (2^4), hiSign k * hiSign k = 1 := by decide

theorem hiSign_hiIdx_zero : hiSign (hiIdx 0) = -1 := by decide

/-- The grade map `(a, b) ↦ (a, −b)`, coordinatewise. -/
def gradeMap (x : CDAlg ℝ 4) : CDAlg ℝ 4 := ⟨fun k => (hiSign k : ℝ) * x.coord k⟩

@[simp] theorem gradeMap_coord (x : CDAlg ℝ 4) (k : Fin (2^4)) :
    (gradeMap x).coord k = (hiSign k : ℝ) * x.coord k := rfl

theorem gradeMap_add (x y : CDAlg ℝ 4) : gradeMap (x + y) = gradeMap x + gradeMap y := by
  ext k; rw [gradeMap_coord, add_coord, add_coord, gradeMap_coord, gradeMap_coord]; ring

theorem gradeMap_smul (r : ℝ) (x : CDAlg ℝ 4) : gradeMap (r • x) = r • gradeMap x := by
  ext k; rw [gradeMap_coord, smul_coord, smul_coord, gradeMap_coord]; ring

theorem gradeMap_mul (x y : CDAlg ℝ 4) : gradeMap (x * y) = gradeMap x * gradeMap y := by
  ext k
  rw [gradeMap_coord, mul_coord, mul_coord, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : (i ^^^ j : Fin (2^4)) = k
  · rw [if_pos h, if_pos h, gradeMap_coord, gradeMap_coord, ← h, hiSign_xor i j]
    push_cast; ring
  · rw [if_neg h, if_neg h, mul_zero]

theorem gradeMap_involutive : Function.Involutive gradeMap := by
  intro x
  ext k
  rw [gradeMap_coord, gradeMap_coord, ← mul_assoc, ← Int.cast_mul, hiSign_sq k]
  norm_num

/-- **An explicit non-identity automorphism of 𝕊.** -/
def gradeAut : CDAut 4 where
  toFun := gradeMap
  map_add := gradeMap_add
  map_smul := gradeMap_smul
  map_mul := gradeMap_mul
  bijective := gradeMap_involutive.bijective

theorem gradeAut_ell : gradeAut ell = -ell := by
  have h : gradeMap ell = -ell := by
    ext k
    rw [gradeMap_coord, neg_coord, ell, e_coord]
    by_cases hk : k = hiIdx 0
    · rw [if_pos hk, hk, hiSign_hiIdx_zero]; norm_num
    · rw [if_neg hk]; ring
  exact h

/-- `CDAut 4` is not the trivial group: `gradeAut ≠ id` (it flips `ℓ`).  So the
    `∀ φ : CDAut 4` theorems above are not statements about a one-element type. -/
theorem gradeAut_ne_id : gradeAut ell ≠ ell := by
  rw [gradeAut_ell]
  intro h
  have h2 : (-ell : CDAlg ℝ 4).coord (hiIdx 0) = (ell : CDAlg ℝ 4).coord (hiIdx 0) := by rw [h]
  rw [neg_coord, ell_coord_hiIdx_zero] at h2
  norm_num at h2

/-! ### The `G₂`-side: octonion automorphisms lifted to `ℓ`-fixing automorphisms of 𝕊

An automorphism `ψ` of 𝕆 lifts to `𝕊 = 𝕆 ⊕ 𝕆ℓ` by acting on both Cayley–Dickson
halves, `a + bℓ ↦ ψ(a) + ψ(b)ℓ`.  This is exactly how the `G₂ = Aut(𝕆)` factor of
`Aut(𝕊)` acts, and every such lift **fixes `ℓ`** — so it satisfies the hypothesis
`hφ : φ ell = ell` of `aut_image_quatSpan` / `aut_hosting_equivariant`.  The
multiplicativity of the lift is the doubling formula (`cdLo_mul`/`cdHi_mul`)
together with `CDAut.map_conj`.

(`Aut(𝕊) ≅ G₂ × S₃` is NOT claimed: we only construct lifts and show they fix `ℓ`.) -/

/-- The half-wise lift of an octonion map to 𝕊. -/
def cdLiftFun (ψ : CDAut 3) (x : CDAlg ℝ 4) : CDAlg ℝ 4 :=
  loOf (ψ (cdLo x)) + hiOf (ψ (cdHi x))

@[simp] theorem cdLo_liftFun (ψ : CDAut 3) (x : CDAlg ℝ 4) :
    cdLo (cdLiftFun ψ x) = ψ (cdLo x) := by
  rw [cdLiftFun, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]

@[simp] theorem cdHi_liftFun (ψ : CDAut 3) (x : CDAlg ℝ 4) :
    cdHi (cdLiftFun ψ x) = ψ (cdHi x) := by
  rw [cdLiftFun, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]

theorem cdLiftFun_add (ψ : CDAut 3) (x y : CDAlg ℝ 4) :
    cdLiftFun ψ (x + y) = cdLiftFun ψ x + cdLiftFun ψ y := by
  rw [cdLiftFun, cdLiftFun, cdLiftFun, cdLo_add, cdHi_add, ψ.map_add, ψ.map_add,
    loOf_add, hiOf_add]
  abel

theorem cdLiftFun_smul (ψ : CDAut 3) (r : ℝ) (x : CDAlg ℝ 4) :
    cdLiftFun ψ (r • x) = r • cdLiftFun ψ x := by
  rw [cdLiftFun, cdLiftFun, cdLo_smul, cdHi_smul, ψ.map_smul, ψ.map_smul, loOf_smul,
    hiOf_smul, smul_add]

/-- **The lift is multiplicative** — the Cayley–Dickson doubling formula plus the
    fact that an automorphism commutes with conjugation (`CDAut.map_conj`). -/
theorem cdLiftFun_mul (ψ : CDAut 3) (x y : CDAlg ℝ 4) :
    cdLiftFun ψ (x * y) = cdLiftFun ψ x * cdLiftFun ψ y := by
  refine eq_of_halves ?_ ?_
  · rw [cdLo_liftFun, cdLo_mul, ψ.map_sub, ψ.map_mul, ψ.map_mul, ψ.map_conj,
      cdLo_mul, cdLo_liftFun, cdLo_liftFun, cdHi_liftFun, cdHi_liftFun]
  · rw [cdHi_liftFun, cdHi_mul, ψ.map_add, ψ.map_mul, ψ.map_mul, ψ.map_conj,
      cdHi_mul, cdHi_liftFun, cdHi_liftFun, cdLo_liftFun, cdLo_liftFun]

theorem cdLiftFun_bijective (ψ : CDAut 3) : Function.Bijective (cdLiftFun ψ) := by
  constructor
  · intro x y h
    have h1 : ψ (cdLo x) = ψ (cdLo y) := by rw [← cdLo_liftFun, ← cdLo_liftFun, h]
    have h2 : ψ (cdHi x) = ψ (cdHi y) := by rw [← cdHi_liftFun, ← cdHi_liftFun, h]
    exact eq_of_halves (ψ.injective h1) (ψ.injective h2)
  · intro z
    obtain ⟨a, ha⟩ := ψ.surjective (cdLo z)
    obtain ⟨b, hb⟩ := ψ.surjective (cdHi z)
    refine ⟨loOf a + hiOf b, eq_of_halves ?_ ?_⟩
    · rw [cdLo_liftFun, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]; exact ha
    · rw [cdHi_liftFun, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]; exact hb

/-- **The `G₂`-style lift of an octonion automorphism to 𝕊.** -/
def cdLift (ψ : CDAut 3) : CDAut 4 where
  toFun := cdLiftFun ψ
  map_add := cdLiftFun_add ψ
  map_smul := cdLiftFun_smul ψ
  map_mul := cdLiftFun_mul ψ
  bijective := cdLiftFun_bijective ψ

theorem loOf_zero : loOf (0 : CDAlg ℝ 3) = 0 :=
  eq_of_halves (by rw [cdLo_loOf, cdLo_zero]) (by rw [cdHi_loOf, cdHi_zero])

theorem hiOf_zero : hiOf (0 : CDAlg ℝ 3) = 0 :=
  eq_of_halves (by rw [cdLo_hiOf, cdLo_zero]) (by rw [cdHi_hiOf, cdHi_zero])

/-- **Every lift fixes the doubling unit `ℓ`** — so `cdLift ψ` satisfies the
    hypothesis of `aut_image_quatSpan` and `aut_hosting_equivariant`. -/
theorem cdLift_ell (ψ : CDAut 3) : cdLift ψ ell = ell := by
  have h : cdLiftFun ψ ell = ell := by
    rw [cdLiftFun, cdLo_ell, cdHi_ell, ψ.map_zero, ψ.map_one, loOf_zero, zero_add,
      hiOf_one]
    rfl
  exact h

/-! #### A concrete non-identity octonion automorphism, and its lift

`𝕆 = ℍ ⊕ ℍ` has its own Cayley–Dickson grade map `(p, q) ↦ (p, −q)`, an
automorphism of 𝕆 of order 2 (an element of `Aut(𝕆) = G₂`).  Its lift is a
non-identity automorphism of 𝕊 that fixes `ℓ` — so the `ℓ`-fixing equivariance
theorems above are not statements about the trivial group. -/

/-- The grade sign of 𝕆 = ℍ ⊕ ℍ: `+1` on the low half, `−1` on the high half. -/
def gradeSign3 (k : Fin (2^3)) : Int := if k.val < 4 then 1 else -1

theorem gradeSign3_xor :
    ∀ i j : Fin (2^3), gradeSign3 (i ^^^ j) = gradeSign3 i * gradeSign3 j := by decide

theorem gradeSign3_sq : ∀ k : Fin (2^3), gradeSign3 k * gradeSign3 k = 1 := by decide

theorem gradeSign3_four : gradeSign3 (4 : Fin (2^3)) = -1 := by decide

/-- The octonion grade map `(p, q) ↦ (p, −q)`. -/
def gradeMap3 (x : CDAlg ℝ 3) : CDAlg ℝ 3 := ⟨fun k => (gradeSign3 k : ℝ) * x.coord k⟩

@[simp] theorem gradeMap3_coord (x : CDAlg ℝ 3) (k : Fin (2^3)) :
    (gradeMap3 x).coord k = (gradeSign3 k : ℝ) * x.coord k := rfl

theorem gradeMap3_add (x y : CDAlg ℝ 3) : gradeMap3 (x + y) = gradeMap3 x + gradeMap3 y := by
  ext k; rw [gradeMap3_coord, add_coord, add_coord, gradeMap3_coord, gradeMap3_coord]; ring

theorem gradeMap3_smul (r : ℝ) (x : CDAlg ℝ 3) : gradeMap3 (r • x) = r • gradeMap3 x := by
  ext k; rw [gradeMap3_coord, smul_coord, smul_coord, gradeMap3_coord]; ring

theorem gradeMap3_mul (x y : CDAlg ℝ 3) : gradeMap3 (x * y) = gradeMap3 x * gradeMap3 y := by
  ext k
  rw [gradeMap3_coord, mul_coord, mul_coord, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : (i ^^^ j : Fin (2^3)) = k
  · rw [if_pos h, if_pos h, gradeMap3_coord, gradeMap3_coord, ← h, gradeSign3_xor i j]
    push_cast; ring
  · rw [if_neg h, if_neg h, mul_zero]

theorem gradeMap3_involutive : Function.Involutive gradeMap3 := by
  intro x
  ext k
  rw [gradeMap3_coord, gradeMap3_coord, ← mul_assoc, ← Int.cast_mul, gradeSign3_sq k]
  norm_num

/-- **A non-identity automorphism of 𝕆** (an order-2 element of `Aut(𝕆) = G₂`). -/
def gradeAut3 : CDAut 3 where
  toFun := gradeMap3
  map_add := gradeMap3_add
  map_smul := gradeMap3_smul
  map_mul := gradeMap3_mul
  bijective := gradeMap3_involutive.bijective

theorem gradeAut3_e_four : gradeAut3 (e (4 : Fin (2^3))) = -(e (4 : Fin (2^3))) := by
  have h : gradeMap3 (e (4 : Fin (2^3))) = -(e (4 : Fin (2^3))) := by
    ext k
    rw [gradeMap3_coord, neg_coord, e_coord]
    by_cases hk : k = (4 : Fin (2^3))
    · rw [if_pos hk, hk, gradeSign3_four]; norm_num
    · rw [if_neg hk]; ring
  exact h

/-- **The `ℓ`-fixing equivariance theorems are not about the trivial group.**
    `cdLift gradeAut3` is an automorphism of 𝕊 that fixes `ℓ` (`cdLift_ell`) and
    is NOT the identity: it negates `loOf e₄`. -/
theorem cdLift_gradeAut3_ne_id :
    cdLift gradeAut3 (loOf (e (4 : Fin (2^3)))) ≠ loOf (e (4 : Fin (2^3))) := by
  have hval : cdLift gradeAut3 (loOf (e (4 : Fin (2^3)))) = -(loOf (e (4 : Fin (2^3)))) := by
    have h : cdLiftFun gradeAut3 (loOf (e (4 : Fin (2^3)))) = -(loOf (e (4 : Fin (2^3)))) := by
      rw [cdLiftFun, cdLo_loOf, cdHi_loOf, gradeAut3_e_four, gradeAut3.map_zero, loOf_neg,
        hiOf_zero, add_zero]
    exact h
  rw [hval]
  intro hcon
  have h2 : (-(loOf (e (4 : Fin (2^3)))) : CDAlg ℝ 4).coord (loIdx 4)
      = (loOf (e (4 : Fin (2^3))) : CDAlg ℝ 4).coord (loIdx 4) := by rw [hcon]
  rw [neg_coord, loOf_coord_loIdx, e_coord, if_pos rfl] at h2
  norm_num at h2

/-! ## 4. T4 — the local spectrum at a crystal (#634 AC4) -/

/-- **T4 — the local spectrum is degenerate at a crystal.**  At a vacuum `s`
    the left alternator vanishes, so the identity `s·(s·x) = −N(s)·x − [s,s,x]`
    (`left_mul_sq_imaginary`) collapses to

      `s·(s·x) = −N(s)·x`  for EVERY `x`,

    i.e. `−L_s² = N(s)·id` *exactly*. -/
theorem left_mul_sq_at_vacuum {s : CDAlg ℝ 4} (hv : IsVacuum s) (x : CDAlg ℝ 4) :
    s * (s * x) = (-(N s)) • x := by
  have h := (isVacuum_iff_alternator_flat hv.1).mp hv
  rw [left_mul_sq_imaginary s x hv.1, h x, sub_zero]

/-- The same statement in the `−L_s²` form: `−L_s² = N(s)·id` at a crystal. -/
theorem neg_left_mul_sq_at_vacuum {s : CDAlg ℝ 4} (hv : IsVacuum s) (x : CDAlg ℝ 4) :
    -(s * (s * x)) = (N s) • x := by
  rw [left_mul_sq_at_vacuum hv x]; module

/-- **Degeneracy of `−L_s²` characterises crystals.**  For imaginary `s`,
    `−L_s²` is the scalar `N(s)·id` **iff** `s` is a vacuum.  (So the degenerate
    local spectrum is not an accident of the vacuum: it is equivalent to it.) -/
theorem left_mul_sq_scalar_iff_vacuum {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) :
    (∀ x, s * (s * x) = (-(N s)) • x) ↔ IsVacuum s := by
  constructor
  · intro h
    refine (isVacuum_iff_alternator_flat hs).mpr (fun x => ?_)
    have hx := left_mul_sq_imaginary s x hs
    rw [h x] at hx
    exact sub_eq_self.mp hx.symm
  · intro hv x
    exact left_mul_sq_at_vacuum hv x

/-- **The local spectrum at a crystal is the single value `N s`.**  Every nonzero
    `x` is an eigenvector of `−L_s²`, and `N s` is the ONLY eigenvalue: there is
    no second eigenvalue to split off. -/
theorem vacuum_eigenvalue_unique {s : CDAlg ℝ 4} (hv : IsVacuum s) {x : CDAlg ℝ 4}
    (hx : x ≠ 0) {lam : ℝ} (h : -(s * (s * x)) = lam • x) : lam = N s := by
  have h1 : (N s) • x = lam • x := by rw [← h, neg_left_mul_sq_at_vacuum hv x]
  have h2 : (N s - lam) • x = 0 := by rw [sub_smul, h1, sub_self]
  have h3 : (N s - lam)^2 * N x = 0 := by rw [← N_smul, h2, N_zero]
  have hNx : N x ≠ 0 := fun hh => hx ((alt_N_eq_zero_iff x).mp hh)
  have h4 : (N s - lam)^2 = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hNx
  have h5 : N s - lam = 0 := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp h4
  linarith

/-- **First order off the vacuum.**  For a vacuum `v` and any direction `w`, the
    left alternator of `s = v + ε w` is EXACTLY

      `T_s = ε · laMap v w + ε² · T_w`,

    with no constant term — so `T_s = O(ε)` as `ε → 0`: the alternator (hence the
    δ-landscape potential `V`) vanishes to first order at a crystal.  (The
    transverse Hessian of `V` is not computed here.) -/
theorem alternator_expansion_off_vacuum {v : CDAlg ℝ 4} (hv : IsVacuum v)
    (w x : CDAlg ℝ 4) (ε : ℝ) :
    assoc (v + ε • w) (v + ε • w) x = ε • (laMap v w x) + (ε^2) • (assoc w w x) := by
  have h0 : assoc v v x = 0 := (isVacuum_iff_alternator_flat hv.1).mp hv x
  simp only [assoc_trilinear.add_left, assoc_trilinear.add_mid, assoc_trilinear.smul_left,
    assoc_trilinear.smul_mid, h0, laMap]
  module

/-! ### The ℤ/2 of the `S₃` side is free

`gradeAut` (`ℓ ↦ −ℓ`) is NOT `ℓ`-fixing, so `aut_hosting_equivariant` does not
apply to it directly.  But the hosted algebra is *generated* by `{1, s, ℓ}`, and
`−ℓ` generates the same algebra (the sign is absorbed by real scaling), so the
hosting assignment is equivariant under `gradeAut` all the same.

The order-3 elements of `S₃` are NOT constructed here — but note *why* that is the
only gap.  In the `S₃ ≅ D₃` description of `Aut(𝕊)/G₂` (Brown 1967; see
`analysis/473-dirac-probe/aut_s3.py`) an element acts on
`Im 𝕊 = Im 𝕆 ⊕ ℝℓ ⊕ (Im 𝕆)ℓ` by a matrix `M ∈ O(2)` on the multiplicity space of
the `7` together with the scalar `det M` on `ℓ`.  The order-3 elements are the
rotations by `±120°`, so they have `det M = +1` and **fix `ℓ`**; it is the three
reflections (`det M = −1`, `gradeAut` among them) that send `ℓ ↦ −ℓ`.  Hence
`aut_hosting_equivariant` covers the order-3 elements *as stated*, as soon as they
are available as terms of `CDAut 4`; only that construction is missing. -/

/-- Words in `{1, s, −t}` are words in `{1, s, t}`: a generator's sign is absorbed
    by the real-scaling constructor. -/
theorem genByPair_neg_right {n : ℕ} {s t : CDAlg ℝ n} :
    ∀ x, GenByPair s (-t) x → GenByPair s t x := by
  intro x hx
  induction hx with
  | one => exact GenByPair.one
  | left => exact GenByPair.left
  | right => rw [← neg_one_smul ℝ t]; exact GenByPair.smul (-1) GenByPair.right
  | add _ _ ih1 ih2 => exact GenByPair.add ih1 ih2
  | smul r _ ih => exact GenByPair.smul r ih
  | mul _ _ ih1 ih2 => exact GenByPair.mul ih1 ih2
  | conj _ ih => exact GenByPair.conj ih

/-- **Hosting is equivariant under the grade automorphism `ℓ ↦ −ℓ`** (the ℤ/2 of
    the `S₃` factor), even though it moves `ℓ`: `gradeAut s` is a crystal and
    every word in `{1, s, ℓ}` is carried to a word in `{1, gradeAut s, ℓ}`. -/
theorem gradeAut_hosting_equivariant {s : CDAlg ℝ 4} (hv : IsVacuum s) :
    IsVacuum (gradeAut s) ∧
      (∀ x, GenByPair s ell x → GenByPair (gradeAut s) ell (gradeAut x)) := by
  refine ⟨aut_map_isVacuum gradeAut hv, fun x hx => ?_⟩
  have h := aut_genByPair gradeAut x hx
  rw [gradeAut_ell] at h
  exact genByPair_neg_right _ h


/-! ## 5. Completeness audit — `#print axioms`

Every theorem in this file must depend on a subset of `{propext, Classical.choice,
Quot.sound}` (`decide`-based lemmas legitimately show fewer).  Anything else (`sorryAx`, a native-reduction axiom, a user axiom)
is a finding. -/

#print axioms hiIdx_ne_zero
#print axioms loIdx_eq_zero_iff
#print axioms loOf_coord_loIdx
#print axioms loOf_coord_hiIdx
#print axioms hiOf_coord_hiIdx
#print axioms hiOf_coord_loIdx
#print axioms cdLo_loOf
#print axioms cdHi_loOf
#print axioms cdLo_hiOf
#print axioms cdHi_hiOf
#print axioms cdLo_zero
#print axioms cdLo_neg
#print axioms cdHi_neg
#print axioms cdLo_sub
#print axioms cdHi_sub
#print axioms cdLo_one
#print axioms cdHi_one
#print axioms cdHi_ell
#print axioms eq_of_halves
#print axioms split_lo_hi
#print axioms loOf_smul
#print axioms loOf_add
#print axioms loOf_neg
#print axioms hiOf_neg
#print axioms N_loOf
#print axioms loOf_coord_zero
#print axioms loOf_coord_hi_zero
#print axioms loOf_mul_ell
#print axioms ell_mul_loOf
#print axioms isVacuum_iff_alternator_flat
#print axioms sAll_isVacuum
#print axioms ell_isVacuum
#print axioms sedWitX_not_isVacuum
#print axioms cdLo_coord_zero
#print axioms coord_zero_of_cdLo
#print axioms bil_comm'
#print axioms N_one'
#print axioms vacuum_iff_parametrised
#print axioms vacuum_norm_parametrised
#print axioms crystal_quaternion_table
#print axioms cdLo_quatComb
#print axioms cdHi_quatComb
#print axioms coeff_zero_of_span_one_u
#print axioms crystal_quatSpan_independent
#print axioms cdLo_mem_span_one_u
#print axioms span_one_u_coord
#print axioms quatSpan_dir_proper
#print axioms inQuatSpan_of_dir
#print axioms inQuatSpan_ell_right
#print axioms quatSpan_inter_lowHalf
#print axioms quatSpan_eq_cd_double
#print axioms vacuum_hosts_quaternion
#print axioms vacuum_pole_of_dir_zero
#print axioms CDAut.map_zero
#print axioms CDAut.map_neg
#print axioms CDAut.map_sub
#print axioms CDAut.map_one
#print axioms CDAut.conj_eq_two_re_sub
#print axioms CDAut.map_re_and_N
#print axioms CDAut.map_re
#print axioms CDAut.map_N
#print axioms CDAut.map_conj
#print axioms CDAut.map_assoc
#print axioms aut_alternator_flat
#print axioms aut_map_isVacuum
#print axioms aut_genByPair
#print axioms aut_image_quatSpan
#print axioms aut_hosting_equivariant
#print axioms hiSign_xor
#print axioms hiSign_sq
#print axioms hiSign_hiIdx_zero
#print axioms gradeMap_add
#print axioms gradeMap_smul
#print axioms gradeMap_mul
#print axioms gradeMap_involutive
#print axioms gradeAut_ell
#print axioms gradeAut_ne_id
#print axioms cdLo_liftFun
#print axioms cdHi_liftFun
#print axioms cdLiftFun_add
#print axioms cdLiftFun_smul
#print axioms cdLiftFun_mul
#print axioms cdLiftFun_bijective
#print axioms loOf_zero
#print axioms hiOf_zero
#print axioms cdLift_ell
#print axioms gradeSign3_xor
#print axioms gradeSign3_sq
#print axioms gradeSign3_four
#print axioms gradeMap3_add
#print axioms gradeMap3_smul
#print axioms gradeMap3_mul
#print axioms gradeMap3_involutive
#print axioms gradeAut3_e_four
#print axioms cdLift_gradeAut3_ne_id
#print axioms left_mul_sq_at_vacuum
#print axioms neg_left_mul_sq_at_vacuum
#print axioms left_mul_sq_scalar_iff_vacuum
#print axioms vacuum_eigenvalue_unique
#print axioms alternator_expansion_off_vacuum
#print axioms genByPair_neg_right
#print axioms gradeAut_hosting_equivariant

end QBP.Foundations.CrystalHosting
