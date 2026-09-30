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

  * **Round-4 core (#688).**  `gradVof s ∈ 𝕆_s`: writing `s = a + b·ℓ` and
    `c = Im b`, both Cayley–Dickson components of the *Foundations closed form* of
    the gradient of `V(s) = N([a, b])` lie in the host quaternion algebra
    `H_s = span{1, a, c, a·c} ⊆ 𝕆`, so `gradVof s` lies in the CD double
    `𝕆_s = H_s ⊕ H_s·ℓ` (`gradVof_components_mem_kernelAlgebra`,
    `gradVof_mem_kernelAlgebra`).  `s` itself is in `𝕆_s`
    (`self_mem_kernelAlgebra`), hence so is every `α • s + β • gradVof s`
    (`smul_self_add_smul_gradV_mem_kernelAlgebra`).  What is **not** proved:
    `gradVof = QBP.Substrate.RuleFlow.gradV` (the bridge lemma, #683 — so no
    statement in this file is a statement about the *rule's* gradient);
    `ker Δ(s) ⊆ CD(H_s)` (the reverse, dimension-8 half); and flow invariance of
    `s ↦ H_s` — an OPEN ODE statement (FLAG-rule-flow-open), NOT a corollary of the
    algebraic membership above.

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
import QBP.Foundations.Artin

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

/-! ### 8b. The three named kernel witnesses

`delta_vanishes_on_inFlightSpan` already covers `1`, `s`, `ℓ` and `s·ℓ`, since all
four are in `InFlightSpan s` by `inFlightSpan_one/self/ell/mul_ell`.  The Red Team
asked for the three named corollaries explicitly, so they are spelled out here
(both in `Δ` form and in the raw alternator form `assoc s s · = 0`). -/

/-- `1 ∈ ker Δ(s)`, i.e. `[s, s, 1] = 0`. -/
theorem one_mem_ker_delta {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : Delta s 1 = 0 :=
  delta_vanishes_on_inFlightSpan hs (inFlightSpan_one s)

/-- `s ∈ ker Δ(s)`, i.e. `[s, s, s] = 0` (third-power associativity at `s`). -/
theorem s_mem_ker_delta {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : Delta s s = 0 :=
  delta_vanishes_on_inFlightSpan hs (inFlightSpan_self s)

/-- `ℓ ∈ ker Δ(s)`, i.e. `[s, s, ℓ] = 0`: the doubling unit is always a kernel
    direction, at every imaginary state. -/
theorem ell_mem_ker_delta {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : Delta s ell = 0 :=
  delta_vanishes_on_inFlightSpan hs (inFlightSpan_ell s)

/-- `s·ℓ ∈ ker Δ(s)` — the fourth in-flight direction. -/
theorem s_mul_ell_mem_ker_delta {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) :
    Delta s (s * ell) = 0 :=
  delta_vanishes_on_inFlightSpan hs (inFlightSpan_mul_ell s)

/-- Alternator form: `[s, s, 1] = 0`. -/
theorem assoc_self_one {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : assoc s s 1 = 0 := by
  have h := one_mem_ker_delta hs
  rwa [delta_eq_neg_assoc _ _ hs, neg_eq_zero] at h

/-- Alternator form: `[s, s, s] = 0`. -/
theorem assoc_self_self {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : assoc s s s = 0 := by
  have h := s_mem_ker_delta hs
  rwa [delta_eq_neg_assoc _ _ hs, neg_eq_zero] at h

/-- Alternator form: `[s, s, ℓ] = 0`. -/
theorem assoc_self_ell {s : CDAlg ℝ 4} (hs : s.coord 0 = 0) : assoc s s ell = 0 := by
  have h := ell_mem_ker_delta hs
  rwa [delta_eq_neg_assoc _ _ hs, neg_eq_zero] at h

/-! ## 9. The kernel algebra `𝕆_s = CD(H_s)` and `∇V(s) ∈ 𝕆_s`

Round-4 finding (issue #688): the Red Team observes numerically that
`ker Δ(s) = CD(H_s)` where, writing `s = a + b·ℓ` in Cayley–Dickson pair
coordinates (`a = cdLo s`, `b = cdHi s`) and `c := Im b`,

    H_s := span_ℝ {1, a, c, a·c} ⊆ 𝕆 = CDAlg ℝ 3,
    𝕆_s := H_s ⊕ H_s·ℓ ⊆ 𝕊 = CDAlg ℝ 4   (the CD double of H_s).

This section proves the **algebraic core** of the associated first-integral claim:
the gradient of the potential `V(s) = N([a, b])` has BOTH Cayley–Dickson components
inside `H_s`, i.e. `∇V(s) ∈ 𝕆_s`.  That is what makes `H_s` a candidate first
integral of the gradient rule — the flow cannot push `s` out of the CD double of
its own host quaternion algebra along the gradient direction.

**Layer discipline.**  `∇V` itself is a `QBP.Substrate.RuleFlow` object
(`RuleFlow.gradV`), and Foundations may not import Substrate.  So the two CD
components of the gradient are re-declared here from the *closed form* that
Substrate proves, namely

    `RuleFlow.cdLo_gradV : cdLo (gradV s) = 2 • (C·b̄ − b̄·C)`
    `RuleFlow.cdHi_gradV : cdHi (gradV s) = 2 • (ā·C − C·ā)`,   `C = comm s = a·b − b·a`.

`gradVlo`/`gradVhi`/`cdComm` below are verbatim copies of those right-hand sides;
`RuleFlow.cdLo_gradV` / `RuleFlow.cdHi_gradV` are exactly the identification
`gradVlo s = cdLo (gradV s)`, `gradVhi s = cdHi (gradV s)`.  Nothing here depends
on the *variational* characterisation of `∇V` — only on its closed form.

**Hypothesis honesty.**  No imaginarity hypothesis on `s` is needed anywhere in
this section: the membership is an identity of the closed form, valid for every
`s : 𝕊`.  (`s.coord 0 = 0` is what the *dynamics* supplies; it is not used.)

**What is NOT proved here.**  The reverse inclusion `ker Δ(s) ⊆ CD(H_s)` — i.e.
that `𝕆_s` is the FULL kernel, dimension 8 — is not established; §8 gives only the
4-dimensional `InFlightSpan s ⊆ ker Δ(s)`.  Nor is invariance of `H_s` along the
flow (that needs the derivative of `s ↦ H_s`, a Substrate-layer statement).  This
section is strictly the membership `∇V(s) ∈ 𝕆_s`. -/

section KernelAlgebra

/-! ### 9.1 The host quaternion algebra `H_s = span{1, a, c, a·c}` -/

/-- Membership in `H = span_ℝ {1, a, c, a·c} ⊆ 𝕆`, the (at most 4-dimensional)
    subspace of the octonions generated by the pair `(a, c)`.  Reuses
    `CDAlg.gen4` / `CDAlg.span4_mul_closed` from the Artin development rather than
    inventing a new span predicate. -/
def InQuatSpanOct (a c x : CDAlg ℝ 3) : Prop := x ∈ Submodule.span ℝ (gen4 a c)

theorem inQuatSpanOct_def (a c x : CDAlg ℝ 3) :
    InQuatSpanOct a c x ↔ x ∈ Submodule.span ℝ (gen4 a c) := Iff.rfl

theorem inQuatSpanOct_one (a c : CDAlg ℝ 3) : InQuatSpanOct a c 1 :=
  one_mem_span_gen4 a c

theorem inQuatSpanOct_left (a c : CDAlg ℝ 3) : InQuatSpanOct a c a :=
  x_mem_span_gen4 a c

theorem inQuatSpanOct_right (a c : CDAlg ℝ 3) : InQuatSpanOct a c c :=
  y_mem_span_gen4 a c

theorem inQuatSpanOct_gen_mul (a c : CDAlg ℝ 3) : InQuatSpanOct a c (a * c) :=
  xy_mem_span_gen4 a c

theorem inQuatSpanOct_add {a c x y : CDAlg ℝ 3}
    (hx : InQuatSpanOct a c x) (hy : InQuatSpanOct a c y) : InQuatSpanOct a c (x + y) :=
  Submodule.add_mem _ hx hy

theorem inQuatSpanOct_sub {a c x y : CDAlg ℝ 3}
    (hx : InQuatSpanOct a c x) (hy : InQuatSpanOct a c y) : InQuatSpanOct a c (x - y) :=
  Submodule.sub_mem _ hx hy

theorem inQuatSpanOct_smul {a c x : CDAlg ℝ 3} (r : ℝ)
    (hx : InQuatSpanOct a c x) : InQuatSpanOct a c (r • x) :=
  Submodule.smul_mem _ _ hx

/-- **`H` is closed under the octonion product** — this is `span4_mul_closed`
    (L4 of the Artin development), not a new fact. -/
theorem inQuatSpanOct_mul {a c x y : CDAlg ℝ 3}
    (hx : InQuatSpanOct a c x) (hy : InQuatSpanOct a c y) : InQuatSpanOct a c (x * y) :=
  span4_mul_closed a c hx hy

/-- **`H` is closed under conjugation**: `x̄ = (2 Re x)·1 − x`. -/
theorem inQuatSpanOct_conj {a c x : CDAlg ℝ 3}
    (hx : InQuatSpanOct a c x) : InQuatSpanOct a c (conj x) := by
  rw [inQuatSpanOct_def, CDAut.conj_eq_two_re_sub]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (one_mem_span_gen4 a c)) hx

/-- **`H` is an ASSOCIATIVE subalgebra of 𝕆** (`assoc_vanishes_on_span4`, C2a):
    products of any three of its elements re-associate.  This is what makes
    `H_s` a *quaternion* algebra rather than merely a 4-dimensional subspace. -/
theorem inQuatSpanOct_assoc {a c x y z : CDAlg ℝ 3}
    (hx : InQuatSpanOct a c x) (hy : InQuatSpanOct a c y) (hz : InQuatSpanOct a c z) :
    (x * y) * z = x * (y * z) := by
  have h : assoc x y z = 0 := assoc_vanishes_on_span4 a c hx hy hz
  rwa [assoc, sub_eq_zero] at h

/-- If `c` is `x` minus a real multiple of `1`, then `x ∈ span{1, a, c, a·c}`.
    (Used to put the *full* high component `b = b₀·1 + c` into `H_s`.) -/
theorem inQuatSpanOct_of_eq_sub_smul_one {a c x : CDAlg ℝ 3} (r : ℝ)
    (h : c = x - r • (1 : CDAlg ℝ 3)) : InQuatSpanOct a c x := by
  have hx : x = r • (1 : CDAlg ℝ 3) + c := by rw [h]; abel
  rw [hx]
  exact inQuatSpanOct_add (inQuatSpanOct_smul r (inQuatSpanOct_one a c))
    (inQuatSpanOct_right a c)

/-! ### 9.2 `c := Im b` and the host algebra of a state -/

/-- `c := Im (cdHi s) = b − b₀·1`, the imaginary part of the high CD component of
    `s`.  (Defined locally rather than via `Exp.imPart`, which is not in this
    file's import cone.) -/
def imHi (s : CDAlg ℝ 4) : CDAlg ℝ 3 := cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3)

theorem imHi_def (s : CDAlg ℝ 4) :
    imHi s = cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3) := rfl

theorem imHi_coord_zero (s : CDAlg ℝ 4) : (imHi s).coord 0 = 0 := by
  rw [imHi_def, sub_coord, smul_coord, one_coord, if_pos rfl, mul_one, sub_self]

theorem cdHi_eq_smul_one_add_imHi (s : CDAlg ℝ 4) :
    cdHi s = ((cdHi s).coord 0) • (1 : CDAlg ℝ 3) + imHi s := by
  rw [imHi_def]; abel

/-- `a = cdLo s ∈ H_s`. -/
theorem cdLo_mem_hostQuat (s : CDAlg ℝ 4) : InQuatSpanOct (cdLo s) (imHi s) (cdLo s) :=
  inQuatSpanOct_left _ _

/-- `c = Im b ∈ H_s`. -/
theorem imHi_mem_hostQuat (s : CDAlg ℝ 4) : InQuatSpanOct (cdLo s) (imHi s) (imHi s) :=
  inQuatSpanOct_right _ _

/-- **`b = cdHi s ∈ H_s`** — the real part `b₀·1` costs nothing, so the FULL high
    component lies in the host algebra generated by `(a, Im b)`. -/
theorem cdHi_mem_hostQuat (s : CDAlg ℝ 4) : InQuatSpanOct (cdLo s) (imHi s) (cdHi s) :=
  inQuatSpanOct_of_eq_sub_smul_one ((cdHi s).coord 0) (imHi_def s)

/-! ### 9.3 The commutator and the closed-form gradient, at Foundations level -/

/-- The Cayley–Dickson commutator `C(s) = [a, b] = a·b − b·a`.  Foundations-level
    copy of `QBP.Substrate.RuleFlow.comm`; `V(s) = N (cdComm s)` there. -/
def cdComm (s : CDAlg ℝ 4) : CDAlg ℝ 3 := cdLo s * cdHi s - cdHi s * cdLo s

theorem cdComm_def (s : CDAlg ℝ 4) : cdComm s = cdLo s * cdHi s - cdHi s * cdLo s := rfl

/-- A real multiple of `1` drops out of a commutator. -/
theorem comm_smul_one_add (x y : CDAlg ℝ 3) (r : ℝ) :
    x * (r • (1 : CDAlg ℝ 3) + y) - (r • (1 : CDAlg ℝ 3) + y) * x = x * y - y * x := by
  rw [mul_add_right, mul_add_left, mul_smul_right, mul_smul_left, cd_mul_one, cd_one_mul]
  abel

/-- **`[a, b] = [a, c]`** — the real part of `b` commutes with everything, so the
    commutator only sees `c = Im b`.  (The cheap sub-step flagged in #688.) -/
theorem cdComm_eq_comm_imHi (s : CDAlg ℝ 4) :
    cdComm s = cdLo s * imHi s - imHi s * cdLo s := by
  rw [cdComm_def, cdHi_eq_smul_one_add_imHi s]
  exact comm_smul_one_add (cdLo s) (imHi s) ((cdHi s).coord 0)

/-- Low CD component of `∇V`, copied verbatim from the closed form proved by
    `QBP.Substrate.RuleFlow.cdLo_gradV`:
    `cdLo (∇V s) = 2·(C·b̄ − b̄·C)` with `C = cdComm s`, `b = cdHi s`. -/
def gradVlo (s : CDAlg ℝ 4) : CDAlg ℝ 3 :=
  (2 : ℝ) • (cdComm s * conj (cdHi s) - conj (cdHi s) * cdComm s)

theorem gradVlo_def (s : CDAlg ℝ 4) :
    gradVlo s = (2 : ℝ) • (cdComm s * conj (cdHi s) - conj (cdHi s) * cdComm s) := rfl

/-- High CD component of `∇V`, copied verbatim from
    `QBP.Substrate.RuleFlow.cdHi_gradV`: `cdHi (∇V s) = 2·(ā·C − C·ā)`. -/
def gradVhi (s : CDAlg ℝ 4) : CDAlg ℝ 3 :=
  (2 : ℝ) • (conj (cdLo s) * cdComm s - cdComm s * conj (cdLo s))

theorem gradVhi_def (s : CDAlg ℝ 4) :
    gradVhi s = (2 : ℝ) • (conj (cdLo s) * cdComm s - cdComm s * conj (cdLo s)) := rfl

/-- The gradient assembled back into a sedenion, `∇V(s) = (gradVlo s, gradVhi s)`.
    Matches `QBP.Substrate.RuleFlow.gradV` by `cdLo_gradV` + `cdHi_gradV`. -/
def gradVof (s : CDAlg ℝ 4) : CDAlg ℝ 4 := loOf (gradVlo s) + hiOf (gradVhi s)

@[simp] theorem cdLo_gradVof (s : CDAlg ℝ 4) : cdLo (gradVof s) = gradVlo s := by
  rw [gradVof, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]

@[simp] theorem cdHi_gradVof (s : CDAlg ℝ 4) : cdHi (gradVof s) = gradVhi s := by
  rw [gradVof, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]

/-! ### 9.4 `C(s) ∈ H_s`, and the main membership -/

/-- **The commutator lies in the host algebra**: `C(s) = [a, b] ∈ H_s`.  Both
    factors are in `H_s` (`cdLo_mem_hostQuat`, `cdHi_mem_hostQuat`) and `H_s` is
    closed under products and differences. -/
theorem cdComm_mem_hostQuat (s : CDAlg ℝ 4) :
    InQuatSpanOct (cdLo s) (imHi s) (cdComm s) := by
  rw [cdComm_def]
  exact inQuatSpanOct_sub
    (inQuatSpanOct_mul (cdLo_mem_hostQuat s) (cdHi_mem_hostQuat s))
    (inQuatSpanOct_mul (cdHi_mem_hostQuat s) (cdLo_mem_hostQuat s))

/-- **Low component of the gradient lies in `H_s`.** -/
theorem gradVlo_mem_hostQuat (s : CDAlg ℝ 4) :
    InQuatSpanOct (cdLo s) (imHi s) (gradVlo s) := by
  have hC := cdComm_mem_hostQuat s
  have hb := inQuatSpanOct_conj (cdHi_mem_hostQuat s)
  rw [gradVlo_def]
  exact inQuatSpanOct_smul _
    (inQuatSpanOct_sub (inQuatSpanOct_mul hC hb) (inQuatSpanOct_mul hb hC))

/-- **High component of the gradient lies in `H_s`.** -/
theorem gradVhi_mem_hostQuat (s : CDAlg ℝ 4) :
    InQuatSpanOct (cdLo s) (imHi s) (gradVhi s) := by
  have hC := cdComm_mem_hostQuat s
  have ha := inQuatSpanOct_conj (cdLo_mem_hostQuat s)
  rw [gradVhi_def]
  exact inQuatSpanOct_smul _
    (inQuatSpanOct_sub (inQuatSpanOct_mul ha hC) (inQuatSpanOct_mul hC ha))

/-- Membership in `𝕆_s = H_s ⊕ H_s·ℓ`, the Cayley–Dickson double of the host
    quaternion algebra: a sedenion `x` is in `𝕆_s` iff BOTH of its CD components
    lie in `H_s`.  (`x = u + v·ℓ` with `u = cdLo x`, `v = cdHi x`.) -/
def InKernelAlgebra (s x : CDAlg ℝ 4) : Prop :=
  InQuatSpanOct (cdLo s) (imHi s) (cdLo x)
    ∧ InQuatSpanOct (cdLo s) (imHi s) (cdHi x)

/-- **Main result (#688 round 4, algebraic core), component form: both Foundations
    gradient components lie in `H_s`.**

    For every sedenion `s = a + b·ℓ`, writing `c = Im b` and
    `H_s = span_ℝ{1, a, c, a·c} ⊆ 𝕆`, the two Foundations closed-form components
    `gradVlo s` and `gradVhi s` both lie in `H_s`; equivalently the sedenion
    `gradVof s = loOf (gradVlo s) + hiOf (gradVhi s)` lies in the CD double
    `𝕆_s = H_s ⊕ H_s·ℓ` (`gradVof_mem_kernelAlgebra`).

    **Scope (PR #689 §I4 C2).**  The statement is about the *Foundations copies*
    `gradVlo` / `gradVhi` (§9.3), NOT about `QBP.Substrate.RuleFlow.gradV`.  They
    are text-identical to the closed form that `RuleFlow.cdLo_gradV` /
    `RuleFlow.cdHi_gradV` prove, but the identification
    `gradVof s = RuleFlow.gradV s` is **not stated in Lean** (bridge lemma owed,
    #683); until it is, nothing here says anything about the rule's gradient.  The
    old name `gradV_mem_kernelAlgebra` is kept as a deprecated alias.

    No hypothesis on `s` is required (in particular not `s.coord 0 = 0` nor
    `N s = 1`): this is an identity of the closed form.

    Mechanism: `b ∈ H_s` because `b = b₀·1 + c`; `ā, b̄ ∈ H_s` because `H_s` is
    conjugation-closed; `C = a·b − b·a ∈ H_s` and then both gradient components
    are ℝ-multiples of differences of products of `C` with `ā`/`b̄` — all inside
    `H_s` by `span4_mul_closed`. -/
theorem gradVof_components_mem_kernelAlgebra (s : CDAlg ℝ 4) :
    InQuatSpanOct (cdLo s) (imHi s) (gradVlo s)
      ∧ InQuatSpanOct (cdLo s) (imHi s) (gradVhi s) :=
  ⟨gradVlo_mem_hostQuat s, gradVhi_mem_hostQuat s⟩

/-- Deprecated alias for `gradVof_components_mem_kernelAlgebra` (renamed
    2026-09-30, PR #689 §I4 C2: the old name read as a claim about
    `RuleFlow.gradV`, which is the OPEN bridge of #683). -/
@[deprecated gradVof_components_mem_kernelAlgebra (since := "2026-09-30")]
theorem gradV_mem_kernelAlgebra (s : CDAlg ℝ 4) :
    InQuatSpanOct (cdLo s) (imHi s) (gradVlo s)
      ∧ InQuatSpanOct (cdLo s) (imHi s) (gradVhi s) :=
  gradVof_components_mem_kernelAlgebra s

/-- The same statement packaged at the sedenion level: `gradVof s ∈ 𝕆_s`
    (`gradVof` is the Foundations copy of the closed-form gradient; the
    identification with `RuleFlow.gradV` is not in Lean — #683). -/
theorem gradVof_mem_kernelAlgebra (s : CDAlg ℝ 4) :
    InKernelAlgebra s (gradVof s) := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_gradVof]; exact gradVlo_mem_hostQuat s
  · rw [cdHi_gradVof]; exact gradVhi_mem_hostQuat s

/-- **`s` itself lies in `𝕆_s`.**  Together with `gradVof_mem_kernelAlgebra` this
    says the state and the Foundations closed-form gradient at that state live in
    the *same* CD double.  (Whether `𝕆_s` is constant along a trajectory is a
    separate, OPEN ODE statement — FLAG-rule-flow-open, #683 — and does not follow
    from this membership.) -/
theorem self_mem_kernelAlgebra (s : CDAlg ℝ 4) : InKernelAlgebra s s :=
  ⟨cdLo_mem_hostQuat s, cdHi_mem_hostQuat s⟩

/-- **`𝕆_s` is closed under `+` and `•`** (it is the CD double of a subspace). -/
theorem inKernelAlgebra_add {s x y : CDAlg ℝ 4}
    (hx : InKernelAlgebra s x) (hy : InKernelAlgebra s y) : InKernelAlgebra s (x + y) := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_add]; exact inQuatSpanOct_add hx.1 hy.1
  · rw [cdHi_add]; exact inQuatSpanOct_add hx.2 hy.2

theorem inKernelAlgebra_smul {s x : CDAlg ℝ 4} (r : ℝ)
    (hx : InKernelAlgebra s x) : InKernelAlgebra s (r • x) := by
  refine ⟨?_, ?_⟩
  · rw [cdLo_smul]; exact inQuatSpanOct_smul r hx.1
  · rw [cdHi_smul]; exact inQuatSpanOct_smul r hx.2

/-- **`α • s + β • gradVof s ∈ 𝕆_s`.**  For every sedenion `s` and all `α β : ℝ`,
    the real combination `α • s + β • gradVof s` lies in `𝕆_s = H_s ⊕ H_s·ℓ`.
    Immediate from `self_mem_kernelAlgebra`, `gradVof_mem_kernelAlgebra` and the
    closure of `𝕆_s` under `+` and `•` (`inKernelAlgebra_add`,
    `inKernelAlgebra_smul`).

    **Scope (PR #689 §I4 C3) — what this does NOT say.**  `gradVof` is the
    Foundations copy of the closed-form gradient: the identification
    `gradVof = RuleFlow.gradV` is not stated in Lean (#683).  So this is not a
    statement about the rule field `F(s)`, and it is not flow invariance —
    that `𝕆_s` is constant along a trajectory is an OPEN ODE statement
    (FLAG-rule-flow-open), not a corollary of this algebraic membership. -/
theorem smul_self_add_smul_gradV_mem_kernelAlgebra (s : CDAlg ℝ 4) (α β : ℝ) :
    InKernelAlgebra s (α • s + β • gradVof s) :=
  inKernelAlgebra_add (inKernelAlgebra_smul α (self_mem_kernelAlgebra s))
    (inKernelAlgebra_smul β (gradVof_mem_kernelAlgebra s))

end KernelAlgebra

/-! ## 10. Completeness audit — `#print axioms` -/

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
#print axioms one_mem_ker_delta
#print axioms s_mem_ker_delta
#print axioms ell_mem_ker_delta
#print axioms s_mul_ell_mem_ker_delta
#print axioms assoc_self_one
#print axioms assoc_self_self
#print axioms assoc_self_ell
#print axioms inQuatSpanOct_mul
#print axioms inQuatSpanOct_conj
#print axioms inQuatSpanOct_assoc
#print axioms cdHi_mem_hostQuat
#print axioms cdComm_eq_comm_imHi
#print axioms cdComm_mem_hostQuat
#print axioms gradVlo_mem_hostQuat
#print axioms gradVhi_mem_hostQuat
#print axioms gradVof_components_mem_kernelAlgebra
#print axioms gradV_mem_kernelAlgebra   -- deprecated alias, audited under both names
#print axioms gradVof_mem_kernelAlgebra
#print axioms self_mem_kernelAlgebra
#print axioms smul_self_add_smul_gradV_mem_kernelAlgebra

end QBP.Foundations.InFlightAlgebra
