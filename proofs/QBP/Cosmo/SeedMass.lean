/-
  QBP.Cosmo.SeedMass — the seed mass M_seed solving S_BH(M) = ln 7
  ===============================================================

  Backing file for the CTH anchor `PROOF-seed-mass-from-ln7`
  (`S_BH_at_M_seed_log_seven`, companions `S_BH_at_M_seed`, `M_seed_pos`,
  `M_seed_arg_nonneg`).

  Claim (from the CTH inventory):
    With the Bekenstein–Hawking entropy `S_BH(M) = 4πG M² / (ℏc)`, the mass
    that solves `S_BH(M) = ln 7` is
        M_seed = √( ln 7 · ℏc / (4πG) ).
    (Numerically M_seed ≈ 0.39 M_Planck ≈ 8.6×10⁻⁹ kg.)  The `ln 7` threshold is
    the Fano-line crystallisation entropy (see `FanoChoiceInformation.lean`).

  ── WHAT IS PROVEN (honesty boundary) ───────────────────────────────────────
  This file proves the *real-analysis identity*: GIVEN the entropy functional
  `S_BH(M) = 4πG M²/(ℏc)` (an explicit definition below — the Bekenstein–Hawking
  area law is the physical INPUT, not something derived here) and the closed
  form for `M_seed`, one has `S_BH(M_seed) = ln 7` exactly, for any positive
  constants `ℏ, c, G`.  The proof carries the positivity/≠0 facts required to
  clear the denominators and to discharge `√·² = ·`.

  What is NOT proven is the physics: that the Bekenstein–Hawking form is the
  correct entropy of the parent body, or that `ln 7` is the physically-realised
  crystallisation threshold.  Those are QBP hypotheses; here they are the
  definition of `S_BH` and the constant on the right-hand side.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace QBP.Cosmo.SeedMass

open Real

/-- **Bekenstein–Hawking entropy functional** `S_BH(M) = 4πG M² / (ℏc)`
    (the area law, in units where `S` is dimensionless — the physical INPUT). -/
noncomputable def S_BH (ℏ c G M : ℝ) : ℝ := 4 * Real.pi * G * M ^ 2 / (ℏ * c)

/-- The argument of the seed-mass square root: `ln 7 · ℏc / (4πG)`. -/
noncomputable def M_seed_arg (ℏ c G : ℝ) : ℝ :=
  Real.log 7 * ℏ * c / (4 * Real.pi * G)

/-- **The seed mass** `M_seed = √( ln 7 · ℏc / (4πG) )`. -/
noncomputable def M_seed (ℏ c G : ℝ) : ℝ := Real.sqrt (M_seed_arg ℏ c G)

/-- `ln 7 > 0` (since `7 > 1`). -/
theorem log_seven_pos : 0 < Real.log 7 := Real.log_pos (by norm_num)

/-- The square-root argument is nonnegative when the constants are positive
    (indeed strictly positive: a product/quotient of positives). -/
theorem M_seed_arg_nonneg (ℏ c G : ℝ) (hℏ : 0 < ℏ) (hc : 0 < c) (hG : 0 < G) :
    0 ≤ M_seed_arg ℏ c G := by
  unfold M_seed_arg
  have hπ : 0 < Real.pi := Real.pi_pos
  positivity

/-- **The seed mass is strictly positive.** -/
theorem M_seed_pos (ℏ c G : ℝ) (hℏ : 0 < ℏ) (hc : 0 < c) (hG : 0 < G) :
    0 < M_seed ℏ c G := by
  unfold M_seed M_seed_arg
  have hπ : 0 < Real.pi := Real.pi_pos
  have hlog : 0 < Real.log 7 := log_seven_pos
  apply Real.sqrt_pos.mpr
  positivity

/-- **The seed mass squared equals its defining argument** (`√a ² = a`,
    valid because the argument is nonnegative). -/
theorem M_seed_sq (ℏ c G : ℝ) (hℏ : 0 < ℏ) (hc : 0 < c) (hG : 0 < G) :
    (M_seed ℏ c G) ^ 2 = M_seed_arg ℏ c G := by
  unfold M_seed
  exact Real.sq_sqrt (M_seed_arg_nonneg ℏ c G hℏ hc hG)

/-- **Value of `S_BH` at the seed mass** — the fully-expanded evaluation
    `S_BH(M_seed) = 4πG · (ln 7 · ℏc / (4πG)) / (ℏc)`.  Companion form of the
    main theorem, before the algebraic cancellation. -/
theorem S_BH_at_M_seed (ℏ c G : ℝ) (hℏ : 0 < ℏ) (hc : 0 < c) (hG : 0 < G) :
    S_BH ℏ c G (M_seed ℏ c G)
      = 4 * Real.pi * G * (M_seed_arg ℏ c G) / (ℏ * c) := by
  unfold S_BH
  rw [M_seed_sq ℏ c G hℏ hc hG]

/-- **Main theorem: `S_BH(M_seed) = ln 7`.**
    Plain reading: the Bekenstein–Hawking entropy evaluated at
    `M_seed = √(ln 7 · ℏc/(4πG))` is exactly `ln 7`, for any positive
    physical constants `ℏ, c, G`. -/
theorem S_BH_at_M_seed_log_seven
    (ℏ c G : ℝ) (hℏ : 0 < ℏ) (hc : 0 < c) (hG : 0 < G) :
    S_BH ℏ c G (M_seed ℏ c G) = Real.log 7 := by
  rw [S_BH_at_M_seed ℏ c G hℏ hc hG]
  unfold M_seed_arg
  have hℏ' : ℏ ≠ 0 := ne_of_gt hℏ
  have hc' : c ≠ 0 := ne_of_gt hc
  have hG' : G ≠ 0 := ne_of_gt hG
  have hπ' : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## Completeness audit — `#print axioms` -/

#print axioms M_seed_arg_nonneg
#print axioms M_seed_pos
#print axioms M_seed_sq
#print axioms S_BH_at_M_seed
#print axioms S_BH_at_M_seed_log_seven

end QBP.Cosmo.SeedMass
