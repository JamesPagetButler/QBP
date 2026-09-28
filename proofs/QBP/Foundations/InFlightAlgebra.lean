/-
  QBP.Foundations.InFlightAlgebra
  ==============================

  The "in-flight ℍ": what the pair `{s, ℓ}` generates inside `𝕊 = CDAlg ℝ 4` at an
  arbitrary IMAGINARY state `s`, and the exact sense in which the left alternator
  of `s` cannot see the `ℓ`-coefficient of `s`.

  Context (issue #688, Red Team round 2).  Two numerically-observed facts were
  handed over for prove-before-encode:

  * **F2.**  `Δ(s) := L_s² + N(s)·id` is blind to `b₀ = (cdHi s).coord 0`, the
    coefficient of the doubling unit `ℓ = e₈` in `s`.  Proved here as
    `assoc_self_add_smul_ell` (alternator form) and `delta_blind_to_ell`
    (`Δ` form).  The honest reading: `L_s²` ALONE is *not* blind — it shifts by
    `(N s − N (s + t•ℓ))•x` (`left_mul_sq_ell_shift`); the `N(s)` counterterm and
    the `L_s²` shift cancel exactly, and what is genuinely `b₀`-independent is the
    left alternator `[s, s, ·]`.

  * **F3.**  For EVERY imaginary `s` the set `{1, s, ℓ, s·ℓ}` spans a subspace of
    𝕊 that is closed under multiplication AND on which multiplication is
    associative — including in the region where 𝕊's own left alternator at `s` is
    nonzero.  Proved here as `inFlightSpan_mul_closed` + `inFlightSpan_assoc`, with
    the non-vacuity payoff `inFlight_associative_even_where_alternator_nonzero`.

  ## Honest scope notes (read before quoting these results)

  1. **`Substrate.Hosting.inFlight_no_quaternion_closure` is correctly STATED but
     over-NAMED.**  Its statement is `¬ ∀ x, s·(s·x) = (−N s)•x`, i.e. the scalar
     local spectrum fails off the vacuum locus — that is true and is what the
     proof establishes.  Its *name* suggests "no quaternion subalgebra closes at
     an in-flight state", which is FALSE: `NoAutonomousDynamics.
     genByPair_ell_mem_quatSpan` already puts every word in `{1, s, ℓ}` inside
     `span{1, ℓ, p, ℓp}` for every imaginary `s`, and this file adds that the span
     is associative.  The in-flight obstruction is the *spectrum* of `L_s`, not the
     existence of a hosted ℍ.

  2. **Dimension is 4 except at the poles.**  `{1, s, ℓ, s·ℓ}` is linearly
     independent iff `pOf s ≠ 0` (`inFlight_independent`), and for a unit imaginary
     `s` that fails exactly at `s = ±ℓ` (`pOf_eq_zero_iff`), where the span
     degenerates to the 2-dimensional `span{1, ℓ} ≅ ℂ`.  So "4-dimensional
     associative subalgebra at every state" is FALSE as literally stated; the
     correct statement is "closed and associative at every imaginary state,
     4-dimensional away from the two poles `±ℓ`".

  3. **No `N s = 1` is needed** for closure, associativity, or `ℓ`-blindness: only
     `s.coord 0 = 0`.  `N s = 1` enters only in `pOf_eq_zero_iff`, to identify the
     degenerate locus with the two poles.  Hypotheses are therefore stated as
     weakly as the proofs allow.

  Layer: Foundations (Mathlib + `QBP.Foundations.*` only; no `QBP.Substrate`, no
  energy/crystallisation semantics in any statement).  Zero `sorry`, zero
  `native_decide`, zero vacuous `True`; `#print axioms` audit at the bottom.
-/
import QBP.Foundations.CrystalHosting

namespace QBP.Foundations.InFlightAlgebra

open QBP.Foundations.CDAlg
open QBP.Foundations.NoAutonomousDynamics
open QBP.Foundations.CrystalHosting

/-! ## 1. F2 — the left alternator is blind to the `ℓ`-coefficient -/

/-- **F2, alternator form.**  Adding any real multiple of the doubling unit
    `ℓ = e₈` to a sedenion leaves its left alternator unchanged:
    `[s + t·ℓ, s + t·ℓ, x] = [s, s, x]` for every `t : ℝ` and every `x : 𝕊`.

    Mechanism: `assoc s s = laMap (loOf (cdLo s)) (hiOf (cdHi s))` only sees the
    Cayley–Dickson cross term, `t·ℓ` moves only `cdHi s` by `t·1`, and the
    `b = 1` row of the polarized cross alternator vanishes identically
    (`CDAlg.laMap_loOf_hiOne`). -/
theorem assoc_self_add_smul_ell (s x : CDAlg ℝ 4) (t : ℝ) :
    assoc (s + t • ell) (s + t • ell) x = assoc s s x := by
  rw [assoc_self_eq_laMap, assoc_self_eq_laMap, loPart_eq_loOf, hiPart_eq_hiOf,
    loPart_eq_loOf, hiPart_eq_hiOf]
  have hlo : cdLo (s + t • ell) = cdLo s := by
    rw [cdLo_add, cdLo_smul, cdLo_ell, smul_zero, add_zero]
  have hhi : cdHi (s + t • ell) = cdHi s + t • (1 : CDAlg ℝ 3) := by
    rw [cdHi_add, cdHi_smul, cdHi_ell]
  rw [hlo, hhi, hiOf_add, hiOf_smul, hiOf_one, laMap_trilinear.add_mid,
    laMap_trilinear.smul_mid, laMap_loOf_hiOne, smul_zero, add_zero]

/-- The operator the Red Team calls `Δ(s)`: `Δ(s) x = s·(s·x) + N(s)·x`, i.e.
    `L_s² + N(s)·id`.  (Definition only — the content is in the theorems below.) -/
def Delta (s x : CDAlg ℝ 4) : CDAlg ℝ 4 := s * (s * x) + (N s) • x

theorem Delta_def (s x : CDAlg ℝ 4) : Delta s x = s * (s * x) + (N s) • x := rfl

/-- **`Δ(s) = −[s, s, ·]` for imaginary `s`** — `CDAlg.left_mul_sq_imaginary`
    rearranged.  So `Δ` is exactly (minus) the left alternator, which is why it is
    `ℓ`-blind while `L_s²` alone is not. -/
theorem delta_eq_neg_assoc (s x : CDAlg ℝ 4) (hs : s.coord 0 = 0) :
    Delta s x = - assoc s s x := by
  rw [Delta_def, left_mul_sq_imaginary s x hs]
  module

/-- **F2, `Δ` form.**  For imaginary `s` and every `t : ℝ`,
    `Δ(s + t·ℓ) = Δ(s)` as operators on 𝕊. -/
theorem delta_blind_to_ell (s x : CDAlg ℝ 4) (t : ℝ) (hs : s.coord 0 = 0) :
    Delta (s + t • ell) x = Delta s x := by
  have hs' : (s + t • ell).coord 0 = 0 := by
    rw [add_coord, smul_coord, ell_coord_zero, mul_zero, add_zero, hs]
  rw [delta_eq_neg_assoc _ x hs', delta_eq_neg_assoc s x hs, assoc_self_add_smul_ell]

/-- **The honest caveat to F2.**  `L_s²` on its own is NOT `ℓ`-blind: the identity
    that holds is
    `(s+tℓ)·((s+tℓ)·x) + N(s+tℓ)·x = s·(s·x) + N(s)·x`,
    so `L_{s+tℓ}² − L_s² = (N s − N (s+tℓ))·id`.  Only the combination
    `L_s² + N(s)·id` (= `−[s,s,·]`) is invariant. -/
theorem left_mul_sq_ell_shift (s x : CDAlg ℝ 4) (t : ℝ) (hs : s.coord 0 = 0) :
    (s + t • ell) * ((s + t • ell) * x) + (N (s + t • ell)) • x
      = s * (s * x) + (N s) • x :=
  delta_blind_to_ell s x t hs

/-! ## 2. The `ℓ`-relation: how `s·ℓ` and `ℓ·s` differ

The Cayley–Dickson doubling formula `(a,b)(c,d) = (ac − d̄b, da + bc̄)` gives, for
`s = (a, b)` with `a` imaginary, `s·ℓ = (−b, a)` and `ℓ·s = (−b̄, ā)`, hence
`s·ℓ + ℓ·s = (−(b + b̄), 0) = −2b₀·1`.  Below this is derived from the polarized
Cayley–Dickson square identity instead of coordinatewise, so it holds verbatim. -/

/-- **`s·ℓ + ℓ·s = −2·b₀·1`** for imaginary `s`, where `b₀ = s.coord (hiIdx 0)`
    is the coefficient of `ℓ` in `s` (equivalently `(cdHi s).coord 0`).
    In particular `s` and `ℓ` anticommute exactly when `b₀ = 0`: `ℓ·s` is NOT
    `−s·ℓ` in general, it is `−2b₀·1 − s·ℓ`. -/
theorem mul_ell_add_ell_mul (s : CDAlg ℝ 4) (hs : s.coord 0 = 0) :
    s * ell + ell * s = (-2 * s.coord (hiIdx 0)) • (1 : CDAlg ℝ 4) := by
  have hb : bil s ell = s.coord (hiIdx 0) := bil_e_right s (hiIdx 0)
  rw [mul_add_mul_comm, hs, ell_coord_zero, hb]
  module

/-- `ℓ·s = −2b₀·1 − s·ℓ` — the explicit relation asked for in #688 T2. -/
theorem ell_mul_eq (s : CDAlg ℝ 4) (hs : s.coord 0 = 0) :
    ell * s = (-2 * s.coord (hiIdx 0)) • (1 : CDAlg ℝ 4) - s * ell :=
  eq_sub_of_add_eq' (mul_ell_add_ell_mul s hs)

/-! ## 3. The `ℓ`-orthogonal part `pOf s`, and the change of basis -/

/-- The component of `s` orthogonal to the doubling unit: `pOf s = s − b₀·ℓ`.
    (Same `p` as in `NoAutonomousDynamics.genByPair_ell_mem_quatSpan`.) -/
def pOf (s : CDAlg ℝ 4) : CDAlg ℝ 4 := s - (s.coord (hiIdx 0)) • ell

theorem pOf_def (s : CDAlg ℝ 4) : pOf s = s - (s.coord (hiIdx 0)) • ell := rfl

theorem pOf_coord_zero {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : (pOf s).coord 0 = 0 := by
  rw [pOf_def, sub_coord, smul_coord, ell_coord_zero, hs, mul_zero, sub_zero]

theorem pOf_coord_hi (s : CDAlg ℝ 4) : (pOf s).coord (hiIdx 0) = 0 := by
  rw [pOf_def, sub_coord, smul_coord, ell_coord_hiIdx_zero, mul_one, sub_self]

theorem s_eq_pOf (s : CDAlg ℝ 4) : s = pOf s + (s.coord (hiIdx 0)) • ell := by
  rw [pOf_def]; module

/-- `s·ℓ = −b₀·1 − ℓ·(pOf s)`: the fourth spanning vector re-expressed in the
    `{1, ℓ, p, ℓp}` basis of `NoAutonomousDynamics.InQuatSpan`. -/
theorem s_mul_ell_eq {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) :
    s * ell = (-(s.coord (hiIdx 0))) • (1 : CDAlg ℝ 4) - ell * pOf s := by
  conv_lhs => rw [s_eq_pOf s]
  rw [mul_add_left, mul_smul_left, ell_sq,
    p_ell_anticomm (pOf_coord_zero hs) (pOf_coord_hi s)]
  module

/-- The triangular change of basis `{1, s, ℓ, sℓ} → {1, ℓ, p, ℓp}`. -/
theorem inFlight_to_quat_basis {s p : CDAlg ℝ 4} {c : ℝ}
    (hsp : s = p + c • ell)
    (hsl : s * ell = (-c) • (1 : CDAlg ℝ 4) - ell * p) (α β γ δ : ℝ) :
    α • (1 : CDAlg ℝ 4) + β • s + γ • ell + δ • (s * ell)
      = (α - δ * c) • (1 : CDAlg ℝ 4) + (β * c + γ) • ell + β • p
        + (-δ) • (ell * p) := by
  rw [hsl, hsp]; module

/-! ## 4. The in-flight span `span{1, s, ℓ, s·ℓ}` -/

/-- Membership in the real span of `{1, s, ℓ, s·ℓ}` — the "in-flight ℍ" of #688. -/
def InFlightSpan (s x : CDAlg ℝ 4) : Prop :=
  ∃ α β γ δ : ℝ, x = α • (1 : CDAlg ℝ 4) + β • s + γ • ell + δ • (s * ell)

theorem inFlightSpan_one (s : CDAlg ℝ 4) : InFlightSpan s 1 := ⟨1, 0, 0, 0, by module⟩
theorem inFlightSpan_self (s : CDAlg ℝ 4) : InFlightSpan s s := ⟨0, 1, 0, 0, by module⟩
theorem inFlightSpan_ell (s : CDAlg ℝ 4) : InFlightSpan s ell := ⟨0, 0, 1, 0, by module⟩
theorem inFlightSpan_mul_ell (s : CDAlg ℝ 4) : InFlightSpan s (s * ell) :=
  ⟨0, 0, 0, 1, by module⟩

/-- `span{1, s, ℓ, sℓ} = span{1, ℓ, p, ℓp}` with `p = pOf s`: the two
    presentations of the in-flight ℍ agree as SETS (triangular change of basis,
    both directions). -/
theorem inFlightSpan_iff_quatSpan {s : CDAlg ℝ 4} (hs : s.coord 0 = 0)
    (x : CDAlg ℝ 4) : InFlightSpan s x ↔ InQuatSpan (pOf s) x := by
  have hsp : s = pOf s + (s.coord (hiIdx 0)) • ell := s_eq_pOf s
  have hsl : s * ell = (-(s.coord (hiIdx 0))) • (1 : CDAlg ℝ 4) - ell * pOf s :=
    s_mul_ell_eq hs
  constructor
  · rintro ⟨α, β, γ, δ, rfl⟩
    exact ⟨α - δ * s.coord (hiIdx 0), β * s.coord (hiIdx 0) + γ, β, -δ,
      inFlight_to_quat_basis hsp hsl α β γ δ⟩
  · rintro ⟨a, b, c, d, rfl⟩
    refine ⟨a - d * s.coord (hiIdx 0), c, b - c * s.coord (hiIdx 0), -d, ?_⟩
    have hp : pOf s = s - (s.coord (hiIdx 0)) • ell := pOf_def s
    have hlp : ell * pOf s = (-(s.coord (hiIdx 0))) • (1 : CDAlg ℝ 4) - s * ell := by
      rw [hsl]; module
    rw [hlp, hp]; module

/-- **F3, closure.**  For every IMAGINARY sedenion `s`, `span{1, s, ℓ, s·ℓ}` is
    closed under the sedenion product.  (No `N s = 1` needed.) -/
theorem inFlightSpan_mul_closed {s x y : CDAlg ℝ 4} (hs : s.coord 0 = 0)
    (hx : InFlightSpan s x) (hy : InFlightSpan s y) : InFlightSpan s (x * y) := by
  rw [inFlightSpan_iff_quatSpan hs] at hx hy ⊢
  exact quatSpan_mul_closed (pOf_coord_zero hs) (pOf_coord_hi s) hx hy

/-! ## 5. Associativity on the span

`NoAutonomousDynamics.quatSpan_mul_closed` gives closure with an explicit
coefficient formula; `quatSpan_mul_expand` states that formula as an EQUATION, and
three applications of it turn associativity into a polynomial identity in the
eight structure coefficients, closed by `module`. -/

/-- The explicit product formula on `span{1, ℓ, p, ℓp}` — the quaternion table
    with `i = ℓ`, `j = p`, `k = ℓp`, `j² = k² = −N(p)`.  (This is the equation
    behind `NoAutonomousDynamics.quatSpan_mul_closed`.) -/
theorem quatSpan_mul_expand {p : CDAlg ℝ 4} (hp0 : p.coord 0 = 0)
    (hp8 : p.coord (hiIdx 0) = 0) (a1 b1 c1 d1 a2 b2 c2 d2 : ℝ) :
    (a1 • (1 : CDAlg ℝ 4) + b1 • ell + c1 • p + d1 • (ell * p))
      * (a2 • (1 : CDAlg ℝ 4) + b2 • ell + c2 • p + d2 • (ell * p))
      = (a1 * a2 - b1 * b2 - N p * (c1 * c2 + d1 * d2)) • (1 : CDAlg ℝ 4)
        + (a1 * b2 + b1 * a2 + N p * (c1 * d2 - d1 * c2)) • ell
        + (a1 * c2 + c1 * a2 - b1 * d2 + d1 * b2) • p
        + (a1 * d2 + d1 * a2 + b1 * c2 - c1 * b2) • (ell * p) := by
  simp only [mul_add_left, mul_add_right, mul_smul_left, mul_smul_right,
    cd_one_mul, cd_mul_one]
  rw [ell_sq, ell_ell_mul, p_ell_anticomm hp0 hp8, p_sq hp0, p_mul_ell_p hp0 hp8,
    ell_mul_ell hp0 hp8, ell_p_mul_p hp0 hp8, ell_p_sq hp8]
  module

/-- **`span{1, ℓ, p, ℓp}` is an ASSOCIATIVE subalgebra of 𝕊** for every imaginary
    `p` orthogonal to `ℓ` — even though 𝕊 itself is neither associative nor
    alternative.  This is the content `quatSpan_mul_closed` (closure only) did not
    yet carry. -/
theorem quatSpan_assoc {p x y z : CDAlg ℝ 4} (hp0 : p.coord 0 = 0)
    (hp8 : p.coord (hiIdx 0) = 0)
    (hx : InQuatSpan p x) (hy : InQuatSpan p y) (hz : InQuatSpan p z) :
    (x * y) * z = x * (y * z) := by
  obtain ⟨a1, b1, c1, d1, rfl⟩ := hx
  obtain ⟨a2, b2, c2, d2, rfl⟩ := hy
  obtain ⟨a3, b3, c3, d3, rfl⟩ := hz
  rw [quatSpan_mul_expand hp0 hp8, quatSpan_mul_expand hp0 hp8,
    quatSpan_mul_expand hp0 hp8, quatSpan_mul_expand hp0 hp8]
  module

/-- **F3, associativity.**  For every IMAGINARY sedenion `s`, multiplication is
    associative on `span{1, s, ℓ, s·ℓ}`. -/
theorem inFlightSpan_assoc {s x y z : CDAlg ℝ 4} (hs : s.coord 0 = 0)
    (hx : InFlightSpan s x) (hy : InFlightSpan s y) (hz : InFlightSpan s z) :
    (x * y) * z = x * (y * z) := by
  rw [inFlightSpan_iff_quatSpan hs] at hx hy hz
  exact quatSpan_assoc (pOf_coord_zero hs) (pOf_coord_hi s) hx hy hz

/-- **F3, headline (honest form).**  At EVERY imaginary state `s` of 𝕊 the set
    `{1, s, ℓ, s·ℓ}` spans a subspace that is closed under multiplication and on
    which multiplication is associative.  Dimension is addressed separately
    (`inFlight_independent` / `pOf_eq_zero_iff`): it is 4 away from `s = ±ℓ`. -/
theorem inFlight_closed_associative {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) :
    (∀ x y, InFlightSpan s x → InFlightSpan s y → InFlightSpan s (x * y))
      ∧ (∀ x y z, InFlightSpan s x → InFlightSpan s y → InFlightSpan s z →
          (x * y) * z = x * (y * z)) :=
  ⟨fun _ _ hx hy => inFlightSpan_mul_closed hs hx hy,
   fun _ _ _ hx hy hz => inFlightSpan_assoc hs hx hy hz⟩

/-! ## 6. Non-vacuity: associative at a state where 𝕊's alternator is NOT zero -/

/-- **The payoff.**  At `s = e₁ + e₁₀` (`CDLifting.sedWitX`, an imaginary sedenion
    whose left alternator is provably nonzero — `CDAlg.sedWitX_alternator_ne_zero`)
    the in-flight span is STILL an associative subalgebra.  So associativity of
    `span{1, s, ℓ, sℓ}` is not a restatement of alternativity, and "in-flight" does
    not mean "no associative 4-algebra closes". -/
theorem inFlight_associative_even_where_alternator_nonzero :
    (∃ x : CDAlg ℝ 4, assoc sedWitX sedWitX x ≠ 0)
      ∧ (∀ x y z : CDAlg ℝ 4, InFlightSpan sedWitX x → InFlightSpan sedWitX y →
          InFlightSpan sedWitX z → (x * y) * z = x * (y * z)) := by
  refine ⟨?_, fun _ _ _ hx hy hz => inFlightSpan_assoc sedWitX_coord_zero hx hy hz⟩
  by_contra hcon
  push Not at hcon
  exact sedWitX_alternator_ne_zero hcon

/-! ## 7. Dimension: 4, except at the two poles `±ℓ` -/

/-- Linear independence of `{1, ℓ, p, ℓp}` for ANY nonzero imaginary `p`
    orthogonal to `ℓ`.  (`CrystalHosting.crystal_quatSpan_independent` covers only
    `p = loOf u` with `N u = 1`; this is the general statement, proved from the
    Cayley–Dickson split `p = (a, c)` with `a`, `c` both imaginary.) -/
theorem quatSpan_independent {p : CDAlg ℝ 4} (hp0 : p.coord 0 = 0)
    (hp8 : p.coord (hiIdx 0) = 0) (hpne : p ≠ 0) {A B C D : ℝ}
    (h : A • (1 : CDAlg ℝ 4) + B • ell + C • p + D • (ell * p) = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hclo : (cdLo p).coord (0 : Fin (2^3)) = 0 := by
    show p.coord (loIdx 0) = 0
    rw [loIdx_zero]; exact hp0
  have hchi : (cdHi p).coord (0 : Fin (2^3)) = 0 := hp8
  -- `ℓ·p = (Im b, −a)` in the CD split
  have hcLo : cdLo (ell * p) = cdHi p := by
    rw [cdLo_mul, cdLo_ell, cdHi_ell, alt_zero_mul, cd_mul_one,
      conj_of_imaginary hchi]
    abel
  have hcHi : cdHi (ell * p) = -(cdLo p) := by
    rw [cdHi_mul, cdLo_ell, cdHi_ell, alt_mul_zero, cd_one_mul,
      conj_of_imaginary hclo]
    abel
  have hlo : A • (1 : CDAlg ℝ 3) + C • cdLo p + D • cdHi p = 0 := by
    have h2 := congrArg cdLo h
    rwa [cdLo_add, cdLo_add, cdLo_add, cdLo_smul, cdLo_smul, cdLo_smul, cdLo_smul,
      cdLo_one, cdLo_ell, hcLo, cdLo_zero, smul_zero, add_zero] at h2
  have hhi : B • (1 : CDAlg ℝ 3) + C • cdHi p + D • (-(cdLo p)) = 0 := by
    have h2 := congrArg cdHi h
    rwa [cdHi_add, cdHi_add, cdHi_add, cdHi_smul, cdHi_smul, cdHi_smul, cdHi_smul,
      cdHi_one, cdHi_ell, hcHi, cdHi_zero, smul_zero, zero_add] at h2
  have hA : A = 0 := by
    have h4 : (A • (1 : CDAlg ℝ 3) + C • cdLo p + D • cdHi p).coord 0
        = (0 : CDAlg ℝ 3).coord 0 := by rw [hlo]
    rwa [add_coord, add_coord, smul_coord, smul_coord, smul_coord, one_coord,
      if_pos rfl, hclo, hchi, zero_coord, mul_one, mul_zero, mul_zero, add_zero,
      add_zero] at h4
  have hB : B = 0 := by
    have h4 : (B • (1 : CDAlg ℝ 3) + C • cdHi p + D • (-(cdLo p))).coord 0
        = (0 : CDAlg ℝ 3).coord 0 := by rw [hhi]
    rwa [add_coord, add_coord, smul_coord, smul_coord, smul_coord, one_coord,
      if_pos rfl, hchi, neg_coord, hclo, zero_coord, mul_one, mul_zero, neg_zero,
      mul_zero, add_zero, add_zero] at h4
  have hCD1 : C • cdLo p + D • cdHi p = 0 := by
    rw [hA, zero_smul, zero_add] at hlo; exact hlo
  have hCD2 : C • cdHi p + (-D) • cdLo p = 0 := by
    rw [hB, zero_smul, zero_add] at hhi
    have hswap : D • (-(cdLo p)) = (-D) • cdLo p := by module
    rwa [hswap] at hhi
  have hbc : bil (cdLo p) (cdHi p) = bil (cdHi p) (cdLo p) := by
    simp only [bil_def]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hn1 : C ^ 2 * N (cdLo p) + 2 * (C * (D * bil (cdLo p) (cdHi p)))
      + D ^ 2 * N (cdHi p) = 0 := by
    have h5 := congrArg N hCD1
    rwa [alt_N_add, N_smul, N_smul, bil_smul_left, bil_smul_right, N_zero] at h5
  have hn2 : C ^ 2 * N (cdHi p) + 2 * (C * (-D * bil (cdHi p) (cdLo p)))
      + (-D) ^ 2 * N (cdLo p) = 0 := by
    have h5 := congrArg N hCD2
    rwa [alt_N_add, N_smul, N_smul, bil_smul_left, bil_smul_right, N_zero] at h5
  rw [← hbc] at hn2
  have hsum : (C ^ 2 + D ^ 2) * (N (cdLo p) + N (cdHi p)) = 0 := by
    linear_combination hn1 + hn2
  have hNp : N p ≠ 0 := fun h0 => hpne ((alt_N_eq_zero_iff p).mp h0)
  have hsq : C ^ 2 + D ^ 2 = 0 := by
    rcases mul_eq_zero.mp hsum with h6 | h7
    · exact h6
    · exact absurd ((N_split p).trans h7) hNp
  have hC : C = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm (by linarith [sq_nonneg D]) (sq_nonneg C))
  have hD : D = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm (by linarith [sq_nonneg C]) (sq_nonneg D))
  exact ⟨hA, hB, hC, hD⟩

/-- **The in-flight span is genuinely 4-dimensional whenever `pOf s ≠ 0`:**
    `{1, s, ℓ, s·ℓ}` is linearly independent over ℝ. -/
theorem inFlight_independent {s : CDAlg ℝ 4} (hs : s.coord 0 = 0)
    (hp : pOf s ≠ 0) {α β γ δ : ℝ}
    (h : α • (1 : CDAlg ℝ 4) + β • s + γ • ell + δ • (s * ell) = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 ∧ δ = 0 := by
  rw [inFlight_to_quat_basis (s_eq_pOf s) (s_mul_ell_eq hs) α β γ δ] at h
  obtain ⟨h1, h2, h3, h4⟩ :=
    quatSpan_independent (pOf_coord_zero hs) (pOf_coord_hi s) hp h
  have hβ : β = 0 := h3
  have hδ : δ = 0 := by linarith
  have hα : α = 0 := by rw [hδ, zero_mul, sub_zero] at h1; exact h1
  have hγ : γ = 0 := by rw [hβ, zero_mul, zero_add] at h2; exact h2
  exact ⟨hα, hβ, hγ, hδ⟩

/-- **The degenerate locus is exactly the two poles.**  For a UNIT imaginary `s`,
    `pOf s = 0` iff `s = ±ℓ`; there `span{1, s, ℓ, sℓ} = span{1, ℓ} ≅ ℂ` and the
    "4-dimensional" reading of F3 fails. -/
theorem pOf_eq_zero_iff {s : CDAlg ℝ 4} (hNs : N s = 1) :
    pOf s = 0 ↔ (s = ell ∨ s = -ell) := by
  constructor
  · intro h0
    have hsc : s = (s.coord (hiIdx 0)) • ell := sub_eq_zero.mp (by rw [← pOf_def]; exact h0)
    have hN : (s.coord (hiIdx 0)) ^ 2 = 1 := by
      have h2 := congrArg N hsc
      rw [N_smul, N_ell, mul_one, hNs] at h2
      exact h2.symm
    have hfac : (s.coord (hiIdx 0) - 1) * (s.coord (hiIdx 0) + 1) = 0 := by
      linear_combination hN
    rcases mul_eq_zero.mp hfac with h1 | h2
    · left
      rw [hsc, show s.coord (hiIdx 0) = 1 by linarith, one_smul]
    · right
      rw [hsc, show s.coord (hiIdx 0) = -1 by linarith]
      module
  · rintro (rfl | rfl)
    · rw [pOf_def, ell_coord_hiIdx_zero, one_smul, sub_self]
    · rw [pOf_def, neg_coord, ell_coord_hiIdx_zero]
      module

/-! ## 8. F4, easy inclusion: the in-flight span lies in `ker Δ(s)`

`Δ(s) = −[s, s, ·]`, and `s` itself lies in the span, so associativity on the span
immediately gives `Δ(s) x = 0` for every `x` in it.  This is the 4-dimensional part
of the Red Team's conjectured `ker Δ(s) = CD(H_s)` (8-dimensional); the remaining
`Im b`-directions are NOT proved here (see the report / #688). -/

/-- **`span{1, s, ℓ, s·ℓ} ⊆ ker Δ(s)`** for imaginary `s`: on the in-flight ℍ the
    local spectrum of `L_s` IS the scalar `−N(s)`, even at a state where it fails
    on all of 𝕊. -/
theorem delta_vanishes_on_inFlightSpan {s x : CDAlg ℝ 4} (hs : s.coord 0 = 0)
    (hx : InFlightSpan s x) : Delta s x = 0 := by
  rw [delta_eq_neg_assoc s x hs, assoc,
    inFlightSpan_assoc hs (inFlightSpan_self s) (inFlightSpan_self s) hx, sub_self,
    neg_zero]

/-- The same in `L_s²` form: `s·(s·x) = −N(s)·x` for `x` in the in-flight span. -/
theorem left_mul_sq_on_inFlightSpan {s x : CDAlg ℝ 4} (hs : s.coord 0 = 0)
    (hx : InFlightSpan s x) : s * (s * x) = (-(N s)) • x := by
  have h := delta_vanishes_on_inFlightSpan hs hx
  rw [Delta_def] at h
  rw [show s * (s * x) = (s * (s * x) + (N s) • x) - (N s) • x by abel, h]
  module

/-! ## 9. Completeness audit — `#print axioms` -/

#print axioms assoc_self_add_smul_ell
#print axioms delta_eq_neg_assoc
#print axioms delta_blind_to_ell
#print axioms left_mul_sq_ell_shift
#print axioms mul_ell_add_ell_mul
#print axioms ell_mul_eq
#print axioms s_mul_ell_eq
#print axioms inFlight_to_quat_basis
#print axioms inFlightSpan_iff_quatSpan
#print axioms inFlightSpan_mul_closed
#print axioms quatSpan_mul_expand
#print axioms quatSpan_assoc
#print axioms inFlightSpan_assoc
#print axioms inFlight_closed_associative
#print axioms inFlight_associative_even_where_alternator_nonzero
#print axioms quatSpan_independent
#print axioms inFlight_independent
#print axioms pOf_eq_zero_iff
#print axioms delta_vanishes_on_inFlightSpan
#print axioms left_mul_sq_on_inFlightSpan

end QBP.Foundations.InFlightAlgebra
