/-
  QBP.Cosmo.RedshiftEvolution — a₀(z) = a₀(0)·(1+z) and the BTFR mass correction
  =============================================================================

  Backing file for two CTH prediction anchors:
    • `PRED-a0-redshift-linear`   (`a0_redshift_evolution`, companions
      `a0_inverse_scale_factor`, `kappa_inverse_mass`)
    • `PRED-btfr-mass-correction` (`btfr_mass_correction`)

  Physical inputs (taken as EXPLICIT definitions/hypotheses — the physics, not
  derived here):
    • Holographic acceleration scale  a₀ = κ_BH = c⁴ / (4 G M).
    • Parent-mass growth              M(a) = M₀ · a   (`PROOF-M-proportional-to-a`),
      with cosmological scale factor `a = 1/(1+z)`.
    • Deep-MOND baryonic Tully–Fisher  v⁴ = G · M_b · a₀.

  ── WHAT IS PROVEN (honesty boundary) ───────────────────────────────────────
  Purely the ALGEBRA that follows from those inputs:
    • `a0_redshift_evolution`  : a₀(z) = a₀(0)·(1+z)  from a₀ = c⁴/(4GM) and
                                 M(1/(1+z)) = M₀/(1+z).
    • `btfr_mass_correction`   : an observer using today's a₀(0) over-estimates
                                 the baryonic mass by (1+z):
                                 M_inferred = M_true·(1+z).
  These are the FORMULAS.  The Lean does NOT assert that nature obeys them — the
  anchors remain PREDICTIONS (and `PRED-a0-redshift-linear` is explicitly a
  late-time / DE-era asymptote; IFU rotation-curve data favour a saturating form
  at z ≳ z_eq — see the anchor's `regime_of_validity`).  Provenance therefore
  stays *prediction*; the Lean's honest footing is `derivation` of the formula.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace QBP.Cosmo.RedshiftEvolution

/-- **Holographic acceleration scale** `a₀(M) = c⁴ / (4 G M)` (the physical
    INPUT: `a₀ = κ_BH`). -/
noncomputable def a0 (c G M : ℝ) : ℝ := c ^ 4 / (4 * G * M)

/-- **Parent-mass growth** `M(a) = M₀ · a` (`PROOF-M-proportional-to-a`). -/
def Mscale (M₀ a : ℝ) : ℝ := M₀ * a

/-! ## 1. `a₀` is inversely proportional to mass, hence to the scale factor -/

/-- **`κ ∝ 1/M`:** the ratio of `a₀` at two masses inverts the masses,
    `a₀(M₁) / a₀(M₂) = M₂ / M₁`.  (`a₀ = κ_BH` falls as `1/M`.) -/
theorem kappa_inverse_mass (c G M₁ M₂ : ℝ)
    (hc : c ≠ 0) (hG : G ≠ 0) (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) :
    a0 c G M₁ / a0 c G M₂ = M₂ / M₁ := by
  unfold a0
  field_simp

/-- **`a₀ ∝ 1/a`:** with `M(a) = M₀·a`, the acceleration scale falls inversely
    with the cosmological scale factor, `a₀(M(a)) = a₀(M₀) / a`. -/
theorem a0_inverse_scale_factor (c G M₀ a : ℝ)
    (hG : G ≠ 0) (hM₀ : M₀ ≠ 0) (ha : a ≠ 0) :
    a0 c G (Mscale M₀ a) = a0 c G M₀ / a := by
  unfold a0 Mscale
  field_simp

/-! ## 2. The redshift law `a₀(z) = a₀(0)·(1+z)` -/

/-- **`a₀(z) = a₀(0)·(1+z)`** (`PRED-a0-redshift-linear`).
    Plain reading: with `a = 1/(1+z)` in `M(a) = M₀·a`, the holographic
    acceleration scale grows linearly in `(1+z)` relative to its present value
    `a₀(0) = a₀(M₀·1)`.  Requires `G, M₀ ≠ 0` and `1+z ≠ 0`. -/
theorem a0_redshift_evolution (c G M₀ z : ℝ)
    (hG : G ≠ 0) (hM₀ : M₀ ≠ 0) (hz : (1 + z) ≠ 0) :
    a0 c G (Mscale M₀ (1 / (1 + z))) = a0 c G (Mscale M₀ 1) * (1 + z) := by
  unfold a0 Mscale
  field_simp

/-! ## 3. The BTFR mass-inference correction -/

/-- **BTFR mass over-estimate `M_inferred = M_true·(1+z)`**
    (`PRED-btfr-mass-correction`).

    Deep-MOND baryonic Tully–Fisher: `v⁴ = G · M_b · a₀`, so `M_b = v⁴/(G·a₀)`.
    An observer measuring the same `v` but assuming today's `a₀(0) = a0_0`
    infers `M_inferred = v⁴/(G·a0_0)`, whereas the true acceleration scale at
    redshift `z` is `a₀(z) = a0_0·(1+z)` (exactly the output of
    `a0_redshift_evolution`), giving `M_true = v⁴/(G·a0_0·(1+z))`.  Hence the
    inferred mass over-estimates the true mass by the factor `(1+z)`.
    Requires `G, a0_0 ≠ 0` and `1+z ≠ 0`. -/
theorem btfr_mass_correction (v G a0_0 z : ℝ)
    (hG : G ≠ 0) (ha : a0_0 ≠ 0) (hz : (1 + z) ≠ 0) :
    v ^ 4 / (G * a0_0) = (v ^ 4 / (G * (a0_0 * (1 + z)))) * (1 + z) := by
  field_simp

/-- **Inverse form `M_true = M_inferred/(1+z)`** — the same identity read as the
    correction to apply to an inferred mass, matching the inventory's
    `M_b(z) = M_b(0)/(1+z)`. -/
theorem btfr_mass_correction_inverse (v G a0_0 z : ℝ)
    (hG : G ≠ 0) (ha : a0_0 ≠ 0) (hz : (1 + z) ≠ 0) :
    v ^ 4 / (G * (a0_0 * (1 + z))) = (v ^ 4 / (G * a0_0)) / (1 + z) := by
  field_simp

/-! ## Completeness audit — `#print axioms` -/

#print axioms kappa_inverse_mass
#print axioms a0_inverse_scale_factor
#print axioms a0_redshift_evolution
#print axioms btfr_mass_correction
#print axioms btfr_mass_correction_inverse

end QBP.Cosmo.RedshiftEvolution
