/-
  QBP.Foundations.Hurwitz — the {ℝ, ℂ, ℍ, 𝕆} classification (external axiom)
  ==========================================================================

  Anchor for #466 item 6: the normed-division-algebra classification —
  every finite-dimensional normed division algebra over ℝ is one of
  ℝ, ℂ, ℍ, 𝕆; in particular its real dimension is 1, 2, 4 or 8.

  ── STATUS: EXTERNAL-REFERENCE AXIOM, NOT A QBP-PROVED THEOREM ──────────────
  Mathlib (pin c5ea0035, v4.30.0) contains NO Hurwitz/Albert classification
  (search performed 2026-08-21: only Hurwitz *zeta* functions exist).  Per the
  federation Lean standard, the classification is therefore stated as a
  clearly-marked Type-3 published-reference axiom, with the dimension-only
  conclusion (the full isomorphism statement would require fixing concrete
  models of 𝕆, which Mathlib also lacks).

  References (Type 3):
  * A. Hurwitz, "Über die Composition der quadratischen Formen von beliebig
    vielen Variabeln", Nachr. Ges. Wiss. Göttingen (1898) 309–316 —
    composition algebras over ℝ have dimension 1, 2, 4, 8.
  * A. A. Albert, "Absolute valued real algebras", Ann. of Math. 48 (1947)
    495–501 — every finite-dimensional absolute-valued unital real algebra
    is ℝ, ℂ, ℍ or 𝕆 (exactly the hypotheses used below: bilinear
    multiplication, unit, and a norm with ‖xy‖ = ‖x‖·‖y‖; associativity is
    NOT assumed).
  * K. Urbanik & F. B. Wright, "Absolute valued algebras", Proc. AMS 11
    (1960) 861–866 — removes even the finite-dimensionality hypothesis.

  Statement discipline (why this axiom is safe to assume):
  * The hypotheses are exactly Albert's: `A` is a (possibly non-associative)
    unital real algebra — `NonAssocRing` + `Module ℝ` + bilinearity via
    `IsScalarTower`/`SMulCommClass` — that is nontrivial, finite-dimensional,
    and carries an absolute value: a positive-definite, absolutely
    homogeneous, subadditive `N : A → ℝ` with `N (x*y) = N x * N y`.  Under
    these hypotheses the conclusion `dim ∈ {1,2,4,8}` is the published
    classification.  (The norm is passed as an explicit function with its
    axioms as hypotheses, NOT as `[NormedAddCommGroup A]`, to avoid the
    `AddCommGroup` instance diamond with `NonAssocRing` — Mathlib has no
    non-associative normed-ring class.)
  * We do NOT assume associativity (`Ring`) — that would exclude 𝕆 and
    change the theorem (Frobenius' {1,2,4} instead).
  * The three sanity theorems at the bottom verify (with genuine Mathlib
    proofs, no axiom) that the three associative members ℝ, ℂ, ℍ do satisfy
    the hypothesis pattern and land in the dimension set — a consistency
    check that the axiom's statement is well-typed and correctly oriented.

  `#print axioms` on any consumer of `hurwitz_classification` will show the
  axiom by name — that is intended and must be surfaced in audits.
-/
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace QBP.Foundations.Hurwitz

open Module

/-- **[EXTERNAL AXIOM — Hurwitz 1898 / Albert 1947 / Urbanik–Wright 1960.]**

    Every nontrivial finite-dimensional real algebra (unital, possibly
    non-associative) whose norm is strictly multiplicative — a normed
    division algebra — has real dimension 1, 2, 4 or 8 (and is in fact
    isomorphic to ℝ, ℂ, ℍ or 𝕆, a statement we cannot express until a
    Mathlib octonion model exists).

    This is a published classification result NOT yet available in Mathlib;
    it is stated here as a clearly-marked Type-3 external-reference axiom,
    not a QBP-proved theorem.  Do not add hypotheses-weakening variants:
    dropping `Nontrivial` (dim 0), dropping positive-definiteness, or
    strengthening to associativity (Frobenius, {1,2,4}) changes the
    theorem. -/
axiom hurwitz_classification
    (A : Type) [NonAssocRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [Nontrivial A] [FiniteDimensional ℝ A]
    (N : A → ℝ)
    (h_definite : ∀ x : A, N x = 0 ↔ x = 0)
    (h_homog : ∀ (r : ℝ) (x : A), N (r • x) = |r| * N x)
    (h_triangle : ∀ x y : A, N (x + y) ≤ N x + N y)
    (h_mul : ∀ x y : A, N (x * y) = N x * N y) :
    finrank ℝ A = 1 ∨ finrank ℝ A = 2 ∨ finrank ℝ A = 4 ∨ finrank ℝ A = 8

/-! ## Sanity anchors (proved, no axiom): the known members land in {1,2,4,8}

These check the axiom's statement pattern against the three associative
members that Mathlib has concrete models for.  Each proves both the
multiplicative-norm hypothesis and the dimension conclusion. -/

/-- ℝ satisfies the normed-division-algebra hypotheses with dimension 1. -/
theorem real_case :
    (∀ x y : ℝ, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ finrank ℝ ℝ = 1 :=
  ⟨fun x y => norm_mul x y, finrank_self ℝ⟩

/-- ℂ satisfies the normed-division-algebra hypotheses with dimension 2. -/
theorem complex_case :
    (∀ x y : ℂ, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ finrank ℝ ℂ = 2 :=
  ⟨fun x y => norm_mul x y, Complex.finrank_real_complex⟩

/-- ℍ satisfies the normed-division-algebra hypotheses with dimension 4.
    (The quaternion norm is exactly multiplicative: `NormedDivisionRing ℍ`.) -/
theorem quaternion_case :
    (∀ x y : Quaternion ℝ, ‖x * y‖ = ‖x‖ * ‖y‖) ∧
      finrank ℝ (Quaternion ℝ) = 4 :=
  ⟨fun x y => norm_mul x y, Quaternion.finrank_eq_four⟩

/-- **Non-vacuity witness:** the axiom's full hypothesis list is satisfiable —
    ℍ discharges every hypothesis, and the axiom then yields a (true)
    conclusion.  This guards against the failure mode of an axiom whose
    hypotheses are inconsistent (which would make it silently vacuous).
    NOTE: this theorem intentionally depends on `hurwitz_classification`;
    its `#print axioms` lists the axiom by design. -/
theorem quaternion_instantiates_axiom :
    finrank ℝ (Quaternion ℝ) = 1 ∨ finrank ℝ (Quaternion ℝ) = 2 ∨
    finrank ℝ (Quaternion ℝ) = 4 ∨ finrank ℝ (Quaternion ℝ) = 8 :=
  hurwitz_classification (Quaternion ℝ) (fun q => ‖q‖)
    (fun x => norm_eq_zero)
    (fun r x => by
      show ‖r • x‖ = |r| * ‖x‖
      rw [norm_smul, Real.norm_eq_abs])
    (fun x y => norm_add_le x y)
    (fun x y => norm_mul x y)

/-- The dimensions of the three verified members are among {1, 2, 4, 8} —
    the axiom's conclusion is realized on every associative instance. -/
theorem known_members_in_dimension_set :
    (finrank ℝ ℝ ∈ ({1, 2, 4, 8} : Set ℕ)) ∧
    (finrank ℝ ℂ ∈ ({1, 2, 4, 8} : Set ℕ)) ∧
    (finrank ℝ (Quaternion ℝ) ∈ ({1, 2, 4, 8} : Set ℕ)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [finrank_self]; simp
  · rw [Complex.finrank_real_complex]; simp
  · rw [Quaternion.finrank_eq_four]; simp

/-! ## Completeness audit — `#print axioms`

`hurwitz_classification` is an axiom by design (documented above).  The
sanity theorems must be clean. -/

#print axioms hurwitz_classification
#print axioms real_case
#print axioms complex_case
#print axioms quaternion_case
#print axioms known_members_in_dimension_set
#print axioms quaternion_instantiates_axiom  -- lists the axiom, by design

end QBP.Foundations.Hurwitz
