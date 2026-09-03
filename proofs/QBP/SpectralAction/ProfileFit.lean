/-
  QBP.SpectralAction.ProfileFit — the profile-function consistency fit
  ====================================================================

  Anchor for `FIT-zeta-modulated-profile` (CTH inventory; FAULT-S4-005 burn-down,
  #620).  This is a **FIT** (empirical / phenomenological constraint-solve), not a
  forward derivation — the anchor stays `marginal`.  What is genuinely a THEOREM,
  and is proved here to the kernel-clean bar, is the *uniqueness of the fit*: given
  the two moment constraints, the profile coefficients `(A,B)` are forced.

  ## The family and its reduced moments

  The spectral-action profile family is
      `f(u) = (1 − A·u + B·u²)·e^(−u)`,  `u ∈ [0,∞)`.
  Its Chamseddine–Connes reduced moments use the Euler integral
      `∫₀^∞ u^k e^(−u) du = k!`  (`Γ(k+1) = k!`),
  so the `n`-weighted moment of the family reduces algebraically to
      `∫₀^∞ (1 − A u + B u²) u^n e^(−u) du = n! − A·(n+1)! + B·(n+2)!`.
  In the 4-dimensional dictionary (cf. `QBP.Foundations.SpectralMoments`,
  `f₂ = ∫ f du`, `f₄ = ∫ f·u du`, `f₀ = f(0)`):
      f₀ = f(0) = 1,
      f₂ = redMoment A B 0 = 0! − A·1! + B·2! = 1 − A + 2B,
      f₄ = redMoment A B 1 = 1! − A·2! + B·3! = 1 − 2A + 6B.

  ## Scope / honesty (matches the anchor's recorded scope)

  This file proves ONLY the 2×2 linear solve: given the gamma-reduced moment
  polynomials as *definitions*, the constraints `f₂/f₀ = 3` and `f₄ = 0` have the
  unique real solution `(A,B) = (−7, −5/2)`.  It does **NOT** prove:
    * the integral reduction `∫ u^k e^{−u} = k!` for this family (the measure-
      theoretic step; the dilation/scaling machinery lives in `SpectralMoments`);
    * any physics — the constraints `f₂/f₀ = 3`, `f₄ = 0` are *imposed*, not
      derived; the odd-zeta / Connes–Moscovici story does no computational work
      here (indeed `f₄ = 0` is contradicted as a ζ-derivation by CCvS
      γ(−2) = (225/4)ζ(5) ≠ 0 — see the anchor notes / KILLED-f4-... item).
  So `(A,B) = (−7,−5/2)` is the *solved-for target*, not an independent prediction.
  The theorem below is nonetheless a real, non-vacuous statement: it is the
  well-posedness (existence AND uniqueness) of the constraint solve.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.

  Best-practices: ~/Documents/inter/lean-proof-best-practices.md,
  ~/Documents/QBP-implementor/docs/cth/proof-anchor-best-practices.md.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace QBP.SpectralAction.ProfileFit

/-- The zeroth "moment" of the profile family is `f(0)`, not an integral:
    `f(0) = (1 − A·0 + B·0²)·e^0 = 1`.  Independent of `(A,B)`. -/
def profileF0 : ℝ := 1

/-- The gamma-reduced `n`-weighted moment of `f(u) = (1 − A u + B u²) e^{−u}`:
    `∫₀^∞ (1 − A u + B u²) u^n e^{−u} du` reduces, via `∫₀^∞ u^k e^{−u} du = k!`,
    to `n! − A·(n+1)! + B·(n+2)!`.  The integral reduction itself is NOT proved in
    this file (see the module docstring); this is the algebraic value it reduces
    to, and it is what the constraint solve operates on. -/
def redMoment (A B : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) - A * (Nat.factorial (n + 1) : ℝ) + B * (Nat.factorial (n + 2) : ℝ)

/-- `f₂ = redMoment A B 0 = 1 − A + 2B` (the `∫ f du` moment). -/
theorem redMoment_zero (A B : ℝ) : redMoment A B 0 = 1 - A + 2 * B := by
  unfold redMoment
  simp only [Nat.factorial]
  push_cast
  ring

/-- `f₄ = redMoment A B 1 = 1 − 2A + 6B` (the `∫ f·u du` moment). -/
theorem redMoment_one (A B : ℝ) : redMoment A B 1 = 1 - 2 * A + 6 * B := by
  unfold redMoment
  simp only [Nat.factorial]
  push_cast
  ring

/-- **Profile-fit well-posedness (existence + uniqueness).**  For the family
    `f(u) = (1 − A u + B u²) e^{−u}`, the two moment constraints

        `f₂ / f₀ = 3`   and   `f₄ = 0`

    (with `f₀ = 1`, `f₂ = 1 − A + 2B`, `f₄ = 1 − 2A + 6B`) hold **iff**
    `(A, B) = (−7, −5/2)`.  The forward direction is *uniqueness* (a `linarith`
    solve of the 2×2 linear system over ℝ); the reverse is *existence* (the fit is
    consistent).  This is the genuine theorem behind the `marginal` FIT anchor —
    the coefficients are forced by the constraints, not free. -/
theorem profile_uniqueness (A B : ℝ) :
    (redMoment A B 0 / profileF0 = 3 ∧ redMoment A B 1 = 0)
      ↔ (A = -7 ∧ B = -5 / 2) := by
  rw [redMoment_zero, redMoment_one]
  unfold profileF0
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_one] at h1
    refine ⟨by linarith, by linarith⟩
  · rintro ⟨hA, hB⟩
    subst hA; subst hB
    norm_num

/-- Convenience restatement without the (trivial, `f₀ = 1`) division: the pair
    `{f₂ = 3, f₄ = 0}` is solved uniquely by `(A,B) = (−7,−5/2)`. -/
theorem profile_uniqueness' (A B : ℝ) :
    (redMoment A B 0 = 3 ∧ redMoment A B 1 = 0) ↔ (A = -7 ∧ B = -5 / 2) := by
  have h := profile_uniqueness A B
  rwa [profileF0, div_one] at h

/-! ## Completeness audit — `#print axioms` -/

#print axioms redMoment_zero
#print axioms redMoment_one
#print axioms profile_uniqueness
#print axioms profile_uniqueness'

end QBP.SpectralAction.ProfileFit
