/-
  QBP.Foundations.QBPHorizonFoundations
  =====================================

  Backing Lean for three CTH proof-anchors (issue #620, FAULT-S4-005 burn-down):

    1. `DERIV-vaidya-accreting-horizon-spacelike`
    2. `DERIV-hubble-half-entropy-factor`
    3. `INSIGHT-s2-dirac-eta-vanishes`

  HONESTY MANDATE (do NOT recreate the over-claim of #472/S4-005).
  These are general-relativity / spectral-geometry claims.  Mathlib does not
  have the ingoing-Vaidya metric, apparent-horizon machinery, or the round-S²
  Dirac operator as first-class objects, so the *physical inputs* enter as
  explicit hypotheses / definitions with their provenance documented.  What is
  proven here is the genuine, non-vacuous MATHEMATICAL core of each claim:

    1. the causal-character sign logic — that the horizon-normal contraction
       `gⁱʲ nᵢ nⱼ` on the r = 2M surface evaluates to `−4·Ṁ`, and that the
       sign of this scalar is exactly what makes the surface spacelike / null /
       timelike under a Lorentzian (−,+,+,+) signature;
    2. the chain-rule ½ factor: `A = c·rH²`, `Ȧ = 2c·rH·ṙH` ⟹ `ṙH/rH = ½·Ȧ/A`,
       and with `S = k·A` (Bekenstein–Hawking), `H = ½·Ṡ/S`;
    3. the finite λ↔−λ cancellation: any spectrum carrying a bijection that
       negates each eigenvalue (⇔ symmetric with equal multiplicities) has
       signed sum (η-invariant) exactly 0.

  Each statement asserts the real fact — none is `True`, none is closed by a
  definitional `rfl` trick.  See the per-theorem docstrings for the precise
  split of "proven outright" vs "assumed as documented hypothesis".
-/
import Mathlib.Data.Real.Sign
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace QBP.Foundations.QBPHorizonFoundations

/-! ## 1. Ingoing-Vaidya accreting horizon is spacelike

The ingoing Vaidya metric is
  `ds² = −(1 − 2M(v)/r) dv² + 2 dv dr + r² dΩ²`.
Its apparent horizon is the surface `Φ(v,r) := r − 2M(v) = 0`, i.e. `r = 2M`,
with normal covector `nᵤ = ∂ᵤΦ = (n_v, n_r) = (−2Ṁ, 1)` (angular parts zero).

The (v,r) block of the metric is `[[−(1−2M/r), 1],[1,0]]`, determinant `−1`, so
the inverse block is `[[0, 1],[1, (1−2M/r)]]`; on the horizon `r = 2M` this is
`gⁱⁿᵛ_vv = 0`, `gⁱⁿᵛ_vr = 1`, `gⁱⁿᵛ_rr = 0`.

PROVENANCE SPLIT.  The specific inverse-metric values on the horizon
(`0, 1, 0`) are the PHYSICAL INPUT — they come from inverting the Vaidya metric,
which is not formalized in current Mathlib.  They enter as the explicit numeric
arguments to `horizonNormSq`.  What is PROVEN OUTRIGHT below is (a) the
contraction of those inputs with the normal `(−2Ṁ, 1)` equals `−4Ṁ`
(`vaidya_horizon_normSq_eq`, by `ring`), and (b) the full causal-character sign
logic (`accreting_horizon_spacelike` etc.). -/

/-- Contraction `gⁱʲ nᵢ nⱼ` of a symmetric 2×2 (contravariant) metric block
`[[gVV, gVR],[gVR, gRR]]` with a covector `n = (nV, nR)`.  This is the squared
Lorentzian norm of the covector `n`. -/
def horizonNormSq (gVV gVR gRR nV nR : ℝ) : ℝ :=
  gVV * nV ^ 2 + 2 * gVR * nV * nR + gRR * nR ^ 2

/-- **The Vaidya horizon-normal identity: ‖n‖² = −4·Ṁ.**  Contracting the
on-horizon inverse metric `(gⁱⁿᵛ_vv, gⁱⁿᵛ_vr, gⁱⁿᵛ_rr) = (0, 1, 0)` with the
apparent-horizon normal `n = (−2·Ṁ, 1)` gives exactly `−4·Ṁ`.  Proven outright
by `ring`; the only physical input is the triple `(0,1,0)` (the inverse Vaidya
metric on `r = 2M`), supplied as explicit arguments. -/
theorem vaidya_horizon_normSq_eq (Mdot : ℝ) :
    horizonNormSq 0 1 0 (-2 * Mdot) 1 = -4 * Mdot := by
  unfold horizonNormSq
  ring

/-- Causal character of a hypersurface, classified by the squared Lorentzian
norm `s` of its normal covector under signature `(−,+,+,+)`:
a hypersurface with **timelike** normal (`s < 0`) is **spacelike**;
a **null** normal (`s = 0`) gives a **null** surface;
a **spacelike** normal (`s > 0`) gives a **timelike** surface. -/
inductive Causal
  | spacelike
  | null
  | timelike
  deriving DecidableEq, Repr

/-- Map the squared-norm of the normal covector to the causal character of the
hypersurface, under Lorentzian signature `(−,+,+,+)` (normal timelike ⟺ surface
spacelike). -/
noncomputable def surfaceCausal (s : ℝ) : Causal :=
  if s < 0 then Causal.spacelike
  else if s = 0 then Causal.null
  else Causal.timelike

/-- **Accretion ⇒ spacelike horizon.**  For `Ṁ > 0`, the horizon-normal squared
norm is `−4Ṁ < 0` (timelike normal), so the apparent horizon is a SPACELIKE
surface.  The sign logic and the `−4Ṁ` value are proven outright; only the
inverse-metric triple `(0,1,0)` is a documented physical input. -/
theorem accreting_horizon_spacelike (Mdot : ℝ) (h : 0 < Mdot) :
    surfaceCausal (horizonNormSq 0 1 0 (-2 * Mdot) 1) = Causal.spacelike := by
  rw [vaidya_horizon_normSq_eq]
  unfold surfaceCausal
  rw [if_pos (by linarith)]

/-- **Static (Ṁ = 0) ⇒ null horizon.**  The horizon-normal squared norm is `0`
(null normal), so the surface is null — recovering the Schwarzschild event
horizon as the stationary limit. -/
theorem static_horizon_null (Mdot : ℝ) (h : Mdot = 0) :
    surfaceCausal (horizonNormSq 0 1 0 (-2 * Mdot) 1) = Causal.null := by
  rw [vaidya_horizon_normSq_eq]
  have hz : -4 * Mdot = 0 := by rw [h]; ring
  unfold surfaceCausal
  rw [if_neg (by rw [hz]; exact lt_irrefl 0), if_pos hz]

/-- **Evaporation (Ṁ < 0) ⇒ timelike horizon.**  The horizon-normal squared
norm is `−4Ṁ > 0` (spacelike normal), so the surface is timelike — the
Hawking-evaporating apparent horizon can be crossed outward. -/
theorem evaporating_horizon_timelike (Mdot : ℝ) (h : Mdot < 0) :
    surfaceCausal (horizonNormSq 0 1 0 (-2 * Mdot) 1) = Causal.timelike := by
  rw [vaidya_horizon_normSq_eq]
  have hpos : (0 : ℝ) < -4 * Mdot := by linarith
  unfold surfaceCausal
  rw [if_neg (by intro he; linarith), if_neg (by intro he; linarith)]

/-! ## 2. Hubble = ½ · entropy rate

For a horizon of areal radius `rH` with area `A = c·rH²` (`c ≠ 0`; on the
Hubble horizon `c = 4π`), differentiating gives `Ȧ = 2c·rH·ṙH`, hence
`ṙH/rH = ½·(Ȧ/A)`.  Identifying `H := ṙH/rH` and, via Bekenstein–Hawking
`S = k·A`, `Ṡ/S = Ȧ/A`, one obtains `H = ½·Ṡ/S`.

PROVENANCE SPLIT.  The defining relations `A = c·rH²` and `Ȧ = 2c·rH·ṙH`
(the area law and its time derivative) enter as explicit hypotheses — the
"time derivative" is the physical/analytic input.  The ½ factor itself, the
algebraic heart of the claim, is PROVEN OUTRIGHT by `field_simp`/`ring`. -/

/-- **Hubble half-area factor.**  Given the area law `A = c·rH²` and its
derivative `Ȧ = 2c·rH·ṙH`, the fractional radius rate equals half the
fractional area rate: `ṙH/rH = ½·(Ȧ/A)`.  Requires `c ≠ 0`, `rH ≠ 0` (so `A`
and the denominators are nonzero).  Proven outright. -/
theorem hubble_half_area (c rH rHdot A Adot : ℝ)
    (hc : c ≠ 0) (hr : rH ≠ 0)
    (hA : A = c * rH ^ 2) (hAdot : Adot = 2 * c * rH * rHdot) :
    rHdot / rH = (1 / 2) * (Adot / A) := by
  subst hA hAdot
  field_simp

/-- **Hubble half-entropy factor.**  Adjoining Bekenstein–Hawking `S = k·A`
(`k ≠ 0`, so `Ṡ = k·Ȧ`), the previous identity becomes `H = ½·Ṡ/S`, i.e.
`ṙH/rH = ½·(Ṡ/S)`.  The entropy-proportionality `S ∝ A` is the documented
physical input (hypotheses `hS`, `hSdot`); the ½ factor is proven outright. -/
theorem hubble_half_entropy (c rH rHdot A Adot S Sdot k : ℝ)
    (hc : c ≠ 0) (hr : rH ≠ 0) (hk : k ≠ 0)
    (hA : A = c * rH ^ 2) (hAdot : Adot = 2 * c * rH * rHdot)
    (hS : S = k * A) (hSdot : Sdot = k * Adot) :
    rHdot / rH = (1 / 2) * (Sdot / S) := by
  subst hA hAdot hS hSdot
  field_simp

/-! ## 3. Round-S² Dirac η-invariant vanishes

The Dirac operator on the round 2-sphere of radius `r` has eigenvalues
`±(n+1)/r`, `n = 0,1,2,…`, with equal multiplicities `2(n+1)` on each sign —
a spectrum symmetric under `λ ↦ −λ`.  The η-invariant is the (regularized)
signed eigenvalue count `∑ sign λ`; on a symmetric spectrum it vanishes because
each `λ` cancels its partner `−λ`.

PROVENANCE SPLIT.  The concrete Dirac spectrum `±(n+1)/r` and its multiplicities
are the physical input — the round-S² Dirac operator is not formalized in
Mathlib.  What is PROVEN OUTRIGHT is the general cancellation lemma: the exact
symmetry condition (a bijection `σ` of the index set with `f(σ i) = −f i`, which
is precisely "symmetric spectrum with equal multiplicities") forces
`∑ sign(f i) = 0`.  The two-element `±λ` instance below shows the hypothesis is
satisfiable and non-vacuous. -/

/-- **η-invariant of a symmetric spectrum vanishes.**  Let `f : Fin n → ℝ` be a
finite list of eigenvalues (with multiplicity, indexed by `Fin n`) and let
`σ` be a permutation of the index set that negates every eigenvalue,
`f(σ i) = −f i`.  (Such a `σ` exists iff the spectrum is symmetric under
`λ ↦ −λ` with equal multiplicities.)  Then the signed sum `∑ sign(f i)` — the
η-invariant — is exactly `0`.  Proven outright; no physical input inside the
lemma, the symmetry hypothesis is the honest hypothesis. -/
theorem eta_symmetric_spectrum_zero {n : ℕ} (f : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, f (σ i) = -f i) :
    ∑ i, Real.sign (f i) = 0 := by
  have key : ∑ i, Real.sign (f i) = -∑ i, Real.sign (f i) := by
    calc ∑ i, Real.sign (f i)
        = ∑ i, Real.sign (f (σ i)) :=
          (Equiv.sum_comp σ (fun i => Real.sign (f i))).symm
      _ = ∑ i, Real.sign (-f i) := by simp_rw [hσ]
      _ = ∑ i, -Real.sign (f i) := by simp_rw [Real.sign_neg]
      _ = -∑ i, Real.sign (f i) := by rw [Finset.sum_neg_distrib]
  linarith [key]

/-- **Concrete non-vacuity witness (a single ±λ Dirac pair).**  For any level
eigenvalue `μ := (m+1)/r`, the pair `{μ, −μ}` contributes `sign μ + sign(−μ) = 0`
to the η-invariant.  This instantiates the S²-Dirac eigenvalues `±(m+1)/r` and
shows the symmetry cancellation is real, not vacuous. -/
theorem eta_s2_dirac_pair (m : ℕ) (r : ℝ) :
    Real.sign (((m : ℝ) + 1) / r) + Real.sign (-(((m : ℝ) + 1) / r)) = 0 := by
  rw [Real.sign_neg]
  ring

end QBP.Foundations.QBPHorizonFoundations
