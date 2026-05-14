/-
  QBP.Foundations.LieAlgebraIso — 𝔰𝔲(2) ≅ Im(ℍ)
  ==============================================

  Anchor for #81 PR2 Theorem 2 (per qbp-oppenheimer bridge seq=17, 2026-05-14):
  the standard Lie-algebra isomorphism between 𝔰𝔲(2) and the imaginary
  quaternions Im(ℍ) under the quaternion commutator bracket.

  Statement: Im(ℍ) (pure quaternions, 3-dim real vector space with brackets
  [p, q] = p·q − q·p under quaternion multiplication) is isomorphic as a real
  Lie algebra to 𝔰𝔲(2) (3-dim real Lie algebra of SU(2) generators).

  In this file we anchor the bracket structure via the standard basis:
    qi = (0, 1, 0, 0) — the quaternion i
    qj = (0, 0, 1, 0) — the quaternion j
    qk = (0, 0, 0, 1) — the quaternion k

  Quaternion multiplication gives:
    i·j = k,  j·k = i,  k·i = j     (cyclic)
    j·i = −k, k·j = −i, i·k = −j    (anti-cyclic)

  Therefore the brackets are:
    [qi, qj] = qi·qj − qj·qi = k − (−k) = 2·qk
    [qj, qk] = qj·qk − qk·qj = i − (−i) = 2·qi
    [qk, qi] = qk·qi − qi·qk = j − (−j) = 2·qj

  These are the same structure constants as 𝔰𝔲(2)'s standard Pauli-matrix
  generators T_a = (−i/2)σ_a, where [T_a, T_b] = εabc T_c (Levi-Civita).
  Up to a factor of 2 normalisation (Q_a = 2·T_a, with [Q_a, Q_b] = 2·εabc Q_c),
  the algebras coincide. The factor-of-2 is conventional and corresponds to
  the half-angle formula in quaternion rotation: q(θ) = cos(θ/2) + sin(θ/2)·n̂.

  Author: qbp-implementor (Claude Opus 4.7), Integration role per
  Beekeeper directive 2026-05-13.
  Date:   2026-05-14
  Anchors: archive/QBP-Theory-v3_1.md §1.1 + §1.3 (the two-axiom foundation
           + half-angle formula); standard math (Hamilton 1843; Pauli 1927).
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion

namespace QBP.Foundations

/-- Real quaternions. -/
abbrev Q := Quaternion ℝ

/-- The standard basis of Im(ℍ): three pure quaternions i, j, k. -/
def qi : Q := ⟨0, 1, 0, 0⟩
def qj : Q := ⟨0, 0, 1, 0⟩
def qk : Q := ⟨0, 0, 0, 1⟩

/-- Quaternion commutator bracket: [p, q] = p·q − q·p.
    Note: we deliberately use a function `bracket` rather than the
    Mathlib `⁅·, ·⁆` Lie-bracket notation, because `Quaternion ℝ`
    already carries Mathlib's `LieRing` instance via `Ring.toLieRing`,
    and a notation collision (this local definition vs Mathlib's
    `Bracket Q Q` from `LieRing`) makes terms like `bracket qi qj`
    ambiguous. Either notation reduces to the same value (commutator
    of the ring), so we standardise on the explicit function form
    here for unambiguous parsing. -/
def bracket (p q : Q) : Q := p * q - q * p

/-! ### Pure-quaternion predicate

A quaternion is *pure* (i.e., in Im(ℍ)) iff its real part vanishes.
The set of pure quaternions is closed under the commutator bracket and forms
a 3-dim real Lie algebra. -/

/-- A quaternion is pure (imaginary) if its real part is zero. -/
def IsPure (q : Q) : Prop := q.re = 0

theorem qi_pure : IsPure qi := rfl
theorem qj_pure : IsPure qj := rfl
theorem qk_pure : IsPure qk := rfl

/-! ### Quaternion multiplication on the standard basis

We compute the multiplication table for {qi, qj, qk} explicitly. These are
the canonical relations from Hamilton 1843: i² = j² = k² = ijk = −1, plus
the cyclic identities ij = k, jk = i, ki = j (and their reverses with a
sign flip). -/

theorem qi_mul_qj : qi * qj = qk := by ext <;> simp [qi, qj, qk]
theorem qj_mul_qi : qj * qi = -qk := by ext <;> simp [qi, qj, qk]
theorem qj_mul_qk : qj * qk = qi := by ext <;> simp [qi, qj, qk]
theorem qk_mul_qj : qk * qj = -qi := by ext <;> simp [qi, qj, qk]
theorem qk_mul_qi : qk * qi = qj := by ext <;> simp [qi, qj, qk]
theorem qi_mul_qk : qi * qk = -qj := by ext <;> simp [qi, qj, qk]

/-! ### Bracket relations on the standard basis

These are the structure constants of Im(ℍ) as a Lie algebra:
    [qi, qj] = 2·qk
    [qj, qk] = 2·qi
    [qk, qi] = 2·qj

Equivalent (after rescaling generators by 1/2) to the SU(2) bracket
relations [Tₐ, T_b] = εₐbc T_c. This is the *anchor* PR2 Theorem 2 needs:
the imaginary quaternions carry the same Lie-bracket structure as 𝔰𝔲(2). -/

theorem bracket_qi_qj : bracket qi qj = (2 : ℝ) • qk := by
  unfold bracket
  rw [qi_mul_qj, qj_mul_qi, sub_neg_eq_add]
  ext <;> simp [qk] <;> norm_num

theorem bracket_qj_qk : bracket qj qk = (2 : ℝ) • qi := by
  unfold bracket
  rw [qj_mul_qk, qk_mul_qj, sub_neg_eq_add]
  ext <;> simp [qi] <;> norm_num

theorem bracket_qk_qi : bracket qk qi = (2 : ℝ) • qj := by
  unfold bracket
  rw [qk_mul_qi, qi_mul_qk, sub_neg_eq_add]
  ext <;> simp [qj] <;> norm_num

/-- Bracket antisymmetry on the standard basis. -/
theorem bracket_qj_qi : bracket qj qi = (-2 : ℝ) • qk := by
  unfold bracket
  rw [qj_mul_qi, qi_mul_qj]
  ext <;> simp [qk] <;> norm_num

theorem bracket_qk_qj : bracket qk qj = (-2 : ℝ) • qi := by
  unfold bracket
  rw [qk_mul_qj, qj_mul_qk]
  ext <;> simp [qi] <;> ring

theorem bracket_qi_qk : bracket qi qk = (-2 : ℝ) • qj := by
  unfold bracket
  rw [qi_mul_qk, qk_mul_qi]
  ext <;> simp [qj] <;> ring

/-! ### Self-brackets are zero

[q, q] = q·q − q·q = 0 trivially, for any q. This is the Lie-algebra
axiom of antisymmetry applied to identical arguments. -/

theorem bracket_self (q : Q) : bracket q q = 0 := by
  unfold bracket; simp

/-! ### 𝔰𝔲(2) ↔ Im(ℍ) isomorphism statement

The Lie algebra structure constants of Im(ℍ) under the quaternion commutator
match those of 𝔰𝔲(2) under matrix commutator (up to the conventional
factor-of-2 from the half-angle normalisation in quaternion rotation).

The isomorphism map ϕ : 𝔰𝔲(2) → Im(ℍ) on basis is:
    ϕ(T₁) = qi / 2,   ϕ(T₂) = qj / 2,   ϕ(T₃) = qk / 2
where Tₐ = (−i/2)·σₐ are the standard 𝔰𝔲(2) generators (Pauli matrices over
i times a half).

Concretely: the structure constants of both algebras are εₐbc (Levi-Civita),
giving the standard SO(3) Lie-bracket structure. Im(ℍ) is the 3-dim real
Lie algebra of pure quaternions; 𝔰𝔲(2) is the 3-dim real Lie algebra of
traceless anti-Hermitian 2×2 complex matrices; they are isomorphic.

We anchor the isomorphism via the structure constants. The full
LieEquiv construction (mapping Im(ℍ) to 𝔰𝔲(2) as a Mathlib `LieEquiv`)
requires `Mathlib.Algebra.Lie.Basic.LieRing` instances which we leave for
follow-up work (see TODO below). -/

/-- The structure constants of Im(ℍ) under the quaternion bracket are
    `cᵢⱼₖ = 2·εᵢⱼₖ` where εᵢⱼₖ is the Levi-Civita symbol with
    ε₁₂₃ = +1.

    This theorem records the three cyclic relations as a single
    conjunction; combined with antisymmetry (which is a Lie-algebra axiom
    derivable from `bracket_self`), it completely determines the bracket
    on the {qi, qj, qk} basis, and hence on all of Im(ℍ). -/
theorem imH_structure_constants :
    bracket qi qj = (2 : ℝ) • qk ∧
    bracket qj qk = (2 : ℝ) • qi ∧
    bracket qk qi = (2 : ℝ) • qj :=
  ⟨bracket_qi_qj, bracket_qj_qk, bracket_qk_qi⟩

/-! ### TODO — full Mathlib LieEquiv construction

A complete `LieEquiv Im(ℍ) 𝔰𝔲(2)` requires:

1. A `LieRing` instance on the subtype `{q : Q // q.re = 0}` (pure
   quaternions). Mathlib's `Quaternion ℝ` is a (non-commutative) ring;
   its commutator gives a Lie-ring structure; restricting to pure
   quaternions gives the Lie subring.

2. A `LieRing` instance on `Matrix.SpecialUnitary ℂ 2` or the Lie algebra
   of SU(2) (via `LinearMap.LieEquiv` or related Mathlib machinery).

3. The map ϕ : Im(ℍ) → 𝔰𝔲(2) defined on basis as above, extended linearly,
   shown to preserve the bracket and be a bijection.

The structure-constant theorem `imH_structure_constants` above gives the
algebraic content needed for downstream theory work (#81 PR2). The
LieEquiv construction itself is bookkeeping; deferred to a follow-up
PR if/when Mathlib-typed Lie equivalence is needed by a consumer.

Tracking note for follow-up: when this lands, also add the corresponding
`adjoint` (Ad map from SU(2) to SO(3)) showing that Im(ℍ) carries the
standard SO(3) rotation generators — this is the half-angle formula's
algebraic origin (`q(θ) = cos(θ/2) + sin(θ/2)·n̂` rotates 3-vectors by θ
via `v ↦ q·v·q*`). -/

end QBP.Foundations
