import QBP.Substrate.Hosting
import QBP.Foundations.NormForm
import QBP.Foundations.CDDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Dynamics.OmegaLimit

/-!
# QBP.Substrate.RuleFlow — the FORM of the rule (#635)

**Substrate-layer discipline (beekeeper's lift, 2026-09-07,
#473 `issuecomment-5574256922`).**  The empty-`Substrate/` rule was lifted for
AC1-hosting work; every file here must say what it HOSTS and what it does NOT
DERIVE.  *What this file hosts:* the **form** of the rule — the vector field `F`
on `StateSphere` and the analytic structure (`Cᵏ`, gradient, Lipschitz, ODE
uniqueness) that the form forces.  *What this file does NOT derive:* the rule
itself (POSTULATE), the existence of the flow (local or global), the
omega-limit map, any measure, and any identification of rest points with
crystals beyond the one direction proved.  See FLAG-rule-flow-open below.

## THE RULE IS A POSTULATE.  NOTHING IS RULED HERE.

`QBP.Substrate.Hosting` deliberately names the rule and declines to define it:
*"**The rule.**  A POSTULATE (#635; currently first-order overdamped descent of
`V`).  **NOT defined here.**"*  This file supplies the missing definition **and
nothing else**: it writes down the postulate exactly as issue #635 / hosting
definition §0 states it — *first-order overdamped descent of `V = potential` in
the `N`-metric, on the imaginary unit sphere `StateSphere`* — and proves the
theorems that are consequences of that **form**.

It does **not** argue that this is the right rule, does not derive it from
anything, and does not rule on any of the open questions attached to it.  Every
theorem below is of the shape *"IF the rule is `γ' = F(γ)` with `F` as defined
here, THEN …"*.  The antecedent is a postulate.

## What IS proved here

1. **`gradV` is the gradient of `V`** (§2–§4).  `V` is the quartic
   `V(s) = ‖[cdLo s, cdHi s]‖²`; `gradV` is a *closed form* in the
   Cayley–Dickson pair coordinates, obtained from the octonion adjoint
   identities `⟪x·p, q⟫ = ⟪p, x̄·q⟫` / `⟪p·x, q⟫ = ⟪p, q·x̄⟫` (§2, themselves
   derived from the polarized composition law `octonion_normMap_zero`).
   `hasGradientAt_potential` / `hasFDerivAt_potential` are the Mathlib-grade
   statements; `contDiff_potential` gives `Cᵏ` for every `k`.
2. **The rule field `F` is tangent to the state sphere** (§5) and vanishes at
   every crystal (`ruleField_eq_zero_of_isVacuum`, via
   `gradV_eq_zero_of_isVacuum`).
3. **`StateSphere` is invariant** (§9): any integral curve of `F` that lies on
   the state sphere at one interior time lies on it throughout its interval.
4. **No deletion, discrete** (§7): the **un-normalised** explicit Euler step
   `eulerStep h s = s + h·F s` is injective on any set where `F` is
   `K`-Lipschitz and `hK < 1` (`eulerStep_injOn`).  **Scope warning:** this is
   NOT the step the #635/#473 probe scripts run.  They run the *renormalised*
   step `renormStep h s = normalise (s + h·F s)`, whose injectivity is proved
   here only on a **level set of `‖F‖`** (`renormStep_injOn_of_normForm_const`);
   the general case is open.  Do not cite `eulerStep_injOn` as covering the
   scripts.
5. **No deletion, continuous** (§8): two integral curves agreeing at one time
   agree throughout — hence the time-`t` map is injective where defined.
6. **`V` descends along the flow.**  Two distinct statements, do not conflate:
   *pointwise* (§6) `d/dt V(γ t) = −‖F(γ t)‖² ≤ 0`
   (`hasDerivAt_potential_along_flow`, `potential_nonincreasing_along_flow`) —
   this is a derivative sign at **one** time `t`, and is NOT by itself the
   Lyapunov/monotonicity statement; and *monotone* (§14)
   `AntitoneOn (V ∘ γ) (Icc a b)` (`potential_antitone_along_flow`), which is
   what every locus-avoidance argument actually needs.
7. **`V` in closed form** (§12): `V(s) = 4·(N(Im a)·N(Im b) − ⟪Im a, Im b⟫²)`
   for `a = cdLo s`, `b = cdHi s` (`potential_eq_cross`), with no imaginarity
   hypothesis — the unconditional form of
   `DeltaLandscape.sedenion_landscape_descends`.  Consequence
   (`potential_le_normForm_sq`): `V ≤ N²` globally.
8. **The frozen locus** (§16): `V` attains its maximum on `StateSphere` and that
   maximum is exactly `1` (`exists_isMaxOn_potential_stateSphere`), and every
   state-sphere point with `V = 1` is a **rest point**
   (`ruleField_eq_zero_of_potential_eq_one`).
9. **ω-limit avoidance** (§17): a forward integral curve on the sphere with
   `V(γ 0) < 1` has `V < 1` at every point of its ω-limit set
   (`omega_avoids_locus`).
10. **Non-vacuity of the landscape** (§10): `V` is not identically zero
   (`potential_witness`), so `gradV` is not identically zero
   (`exists_gradV_ne_zero`).  **Scope warning:** the witness there is
   `witness = e₁ + e₁₀`, which is one of the 42 rank-2 **zero divisors**; it lies
   on the argmax locus `{V = N²}` and, once normalised, is a **rest point**
   (`F = 0`, by item 8).  So `exists_gradV_ne_zero` does NOT witness that the
   *dynamics* is non-trivial.
11. **Non-vacuity of the dynamics** (§15): `∃ s ∈ StateSphere, F s ≠ 0`
   (`exists_ruleField_ne_zero`), witnessed by the in-flight point
   `(e₁ + e₂ + e₉)/√3` (CD pair `(e₁ + e₂, e₁)`, `V/N² = 4/9`).  This, not
   `exists_gradV_ne_zero`, is the statement that rules out the zero field.
12. **Crystals are not zero divisors** (§18): the norm defect of left
   multiplication is one associator pairing, `N(x·y) = N x·N y − 2⟪a,[d̄,b,c̄]⟫`
   (`normForm_mul_eq`), and it vanishes at a vacuum — so `N(s·y) = N s·N y`
   (`normForm_mul_of_isVacuum`) and `y ↦ s·y` is injective
   (`crystal_not_zeroDivisor`).

## FLAG-rule-flow-open — what is NOT proved

* **Global existence** of the flow is NOT proved and is explicitly out of scope.
  Nothing below asserts that an integral curve through a given point exists, or
  that it extends to all of `ℝ`.  Every uniqueness/invariance statement is
  conditional on curves that are *given* as hypotheses.
* **Local existence** is not proved either: `IsPicardLindelof` is not
  discharged here (it needs a ball/time-window budget that is not free).
* **The omega-limit map** `s ↦ lim_{t→∞} γ_s(t)` is NOT constructed, and no
  claim is made that the flow converges, that it converges to a vacuum, or that
  the limit map is measurable/measure-preserving/injective.
* **Rest points are not claimed to be vacua.**  `ruleField_eq_zero_iff` says
  exactly what `F s = 0` means — the tangential part of `∇V` vanishes — and
  `ruleField_eq_zero_of_isVacuum` gives one direction.  The converse (every
  critical point of `V` on the sphere is a minimum) is **FALSE in general** for
  a quartic on a sphere and is NOT asserted.
* **Renormalised-step injectivity** is proved only on level sets of `‖F‖`
  (`renormStep_injOn_of_normForm_const`); the general case is open.  The probe
  scripts run `renormStep`, not `eulerStep` — see item 4 above.
* **`ZD ⇔ V = N²` is NOT proved here.**  The `⇐` direction is not proof-owed;
  the `⇒` direction (`s ≠ 0`, `V s = (N s)²` ⟹ `s` is a zero divisor) is owed
  and OPEN — see `FLAG-P5-open` in the §18 preamble.  Everything in this file
  about the "zero-divisor locus" is therefore stated on `{V = 1}`, the argmax
  locus, which is what the proofs actually establish.
* No measure, no ensemble, no dynamics beyond the ODE form.  The initial
  ensemble remains the beekeeper ruling recorded in `Hosting`.

## Analytic structure on `CDAlg ℝ n`

`Hosting`/`Foundations` deliberately put **no** `InnerProductSpace` instance on
`CDAlg` (`HolographicSubalgebra` borrows Mathlib's machinery through
`toEuclid` instead).  Calculus needs one, so §1 installs a **`scoped`**
`NormedAddCommGroup` / `InnerProductSpace ℝ (CDAlg ℝ n)` whose inner product is
*exactly* the algebra-supplied polar form `bil` (`inner_def'` is `rfl`) and
whose norm is therefore `‖x‖² = N x` (`norm_sq_eq_normForm`).  This is the same
Euclidean form as `toEuclid`/`bil_eq_inner`, transported rather than re-chosen;
the D10 non-identification guardrail of `NormForm` applies verbatim — `N` is an
algebraic norm form, not a spacetime metric.

Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
`#print axioms` audit in §11.
-/

namespace QBP.Substrate.RuleFlow

open QBP.Foundations QBP.Foundations.CDAlg QBP.Foundations.CrystalHosting QBP.Substrate
open scoped RealInnerProductSpace

variable {n m : ℕ}

/-! ## 1. The Euclidean structure on `CDAlg ℝ n` (scoped) -/

/-- The inner product on `CDAlg ℝ n` is the algebra-supplied polar form `bil`.
    Scoped: `Foundations` deliberately carries no such instance. -/
scoped instance instInnerCD : Inner ℝ (CDAlg ℝ n) := ⟨fun x y => bil x y⟩

/-- `⟪x,y⟫ = bil x y` — definitionally. -/
theorem inner_def' (x y : CDAlg ℝ n) : ⟪x, y⟫ = bil x y := rfl

/-- The norm induced by `bil`; `‖x‖ = √(N x)`.  Scoped. -/
noncomputable scoped instance instNormedAddCommGroupCD : NormedAddCommGroup (CDAlg ℝ n) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (CDAlg ℝ n) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun x y => by
        simpa only [starRingEnd_apply, star_trivial, inner_def'] using NormForm.bil_symm y x
      re_inner_nonneg := fun x => by
        simpa only [RCLike.re_to_real, inner_def', bil_def] using
          Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (x.coord i))
      definite := fun x h => (alt_N_eq_zero_iff x).mp (by rw [N_eq_bil]; exact h)
      add_left := fun x y z => bil_add_left x y z
      smul_left := fun x y r => by
        simpa only [starRingEnd_apply, star_trivial, inner_def'] using bil_smul_left r x y }

/-- `CDAlg ℝ n` as a real inner-product space for the algebraic form `N`.  Scoped. -/
noncomputable scoped instance instInnerProductSpaceCD : InnerProductSpace ℝ (CDAlg ℝ n) :=
  InnerProductSpace.ofCore _

/-- `‖x‖² = N x`: the analytic norm is the algebraic norm form. -/
theorem norm_sq_eq_normForm (x : CDAlg ℝ n) : ‖x‖ ^ 2 = N x := by
  rw [← real_inner_self_eq_norm_sq, inner_def', ← N_eq_bil]


/-! ## 2. The octonion adjoint identities

`⟪x·p, q⟫ = ⟪p, x̄·q⟫` and `⟪p·x, q⟫ = ⟪p, q·x̄⟫` in 𝕆.  Both are consequences of
the polarized composition law `OctonionLaws.octonion_normMap_zero`
(`⟪ac,bd⟫ + ⟪bc,ad⟫ = 2⟪a,b⟫⟪c,d⟫`) specialised at `b = 1` resp. `d = 1`.  They
are what turns the derivative of `V` into a CLOSED FORM rather than an adjoint
operator applied blindly. -/

/-- `⟪x,1⟫ = x₀`. -/
theorem bil_one_right (x : CDAlg ℝ n) : bil x 1 = x.coord 0 := by
  simp only [bil_def, one_coord]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `x̄ = 2x₀·1 − x`. -/
theorem conj_eq_sub (x : CDAlg ℝ n) : conj x = (2 * x.coord 0) • (1 : CDAlg ℝ n) - x := by
  ext i
  rw [conj_coord, sub_coord, smul_coord, one_coord]
  by_cases h : i = 0
  · subst h; simp; ring
  · have h' : i.val ≠ 0 := fun hh => h (Fin.ext hh)
    simp [h, h']

/-- Octonion polarized composition: `⟪ac, bd⟫ + ⟪bc, ad⟫ = 2⟪a,b⟫⟪c,d⟫`. -/
theorem octonion_bil_polarized (a b c d : CDAlg ℝ 3) :
    bil (a * c) (b * d) + bil (b * c) (a * d) = 2 * bil a b * bil c d := by
  have h : (normMap a b c d).coord 0 = 0 := by rw [octonion_normMap_zero]; rfl
  rw [normMap_coord0] at h
  linarith [h]

/-- **Left adjoint identity in 𝕆.** `⟪x·p, q⟫ = ⟪p, x̄·q⟫`. -/
theorem bil_mul_left_adj (x p q : CDAlg ℝ 3) : bil (x * p) q = bil p (conj x * q) := by
  have h := octonion_bil_polarized x 1 p q
  rw [cd_one_mul, bil_one_right] at h
  rw [conj_eq_sub, mul_sub_left, mul_smul_left, cd_one_mul,
    show bil p ((2 * x.coord 0) • q - x * q)
      = (2 * x.coord 0) * bil p q - bil p (x * q) by
        rw [sub_eq_add_neg, bil_add_right, bil_smul_right]
        rw [show (-(x*q) : CDAlg ℝ 3) = (-1 : ℝ) • (x*q) by ext i; simp, bil_smul_right]
        ring]
  have hs : bil (1 * p) (x * q) = bil p (x * q) := by rw [cd_one_mul]
  rw [hs] at h
  linarith [h]

/-- **Right adjoint identity in 𝕆.** `⟪p·x, q⟫ = ⟪p, q·x̄⟫`. -/
theorem bil_mul_right_adj (x p q : CDAlg ℝ 3) : bil (p * x) q = bil p (q * conj x) := by
  have h := octonion_bil_polarized p q x 1
  rw [cd_mul_one, cd_mul_one, bil_one_right] at h
  rw [conj_eq_sub, mul_sub_right, mul_smul_right, cd_mul_one,
    show bil p ((2 * x.coord 0) • q - q * x)
      = (2 * x.coord 0) * bil p q - bil p (q * x) by
        rw [sub_eq_add_neg, bil_add_right, bil_smul_right]
        rw [show (-(q*x) : CDAlg ℝ 3) = (-1 : ℝ) • (q*x) by ext i; simp, bil_smul_right]
        ring]
  have hs : bil (q * x) p = bil p (q * x) := NormForm.bil_symm _ _
  rw [hs] at h
  linarith [h]


/-- `bil` is additive over subtraction on the left. -/
theorem bil_sub_left (x y z : CDAlg ℝ n) : bil (x - y) z = bil x z - bil y z := by
  simp only [bil_def, sub_coord]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `bil` is additive over subtraction on the right. -/
theorem bil_sub_right (x y z : CDAlg ℝ n) : bil x (y - z) = bil x y - bil x z := by
  simp only [bil_def, sub_coord]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ## 3. The commutator map `C` and the closed-form gradient `∇V` -/

/-- The CD commutator `C(s) = [cdLo s, cdHi s]`; `potential s = N (C s)`. -/
def comm (s : CDAlg ℝ 4) : CDAlg ℝ 3 := cdLo s * cdHi s - cdHi s * cdLo s

theorem potential_eq_N_comm (s : CDAlg ℝ 4) : Hosting.potential s = N (comm s) := rfl

/-- A crystal has vanishing commutator. -/
theorem comm_eq_zero_of_isVacuum {s : CDAlg ℝ 4} (hv : IsVacuum s) : comm s = 0 := by
  rw [comm, hv.2, sub_self]

/-- **The exact quadratic expansion of `C` along a ray.**  `secVar`/`quadVar` are
    `CrystalHosting`'s linear/quadratic terms; unlike `commutator_along_ray` this
    carries NO vacuum hypothesis (the constant term `C s` is kept). -/
theorem comm_along_ray (s v : CDAlg ℝ 4) (t : ℝ) :
    comm (s + t • v) = comm s + t • secVar s v + (t ^ 2) • quadVar v := by
  rw [comm, comm, secVar, quadVar, cdLo_add, cdHi_add, cdLo_smul, cdHi_smul]
  simp only [mul_add_left, mul_add_right, mul_smul_left, mul_smul_right]
  module

/-- The closed-form gradient of `V` at `s`, in CD pair coordinates. -/
noncomputable def gradV (s : CDAlg ℝ 4) : CDAlg ℝ 4 :=
  loOf ((2 : ℝ) • (comm s * conj (cdHi s) - conj (cdHi s) * comm s))
    + hiOf ((2 : ℝ) • (conj (cdLo s) * comm s - comm s * conj (cdLo s)))

/-- Low CD component of `∇V`. -/
theorem cdLo_gradV (s : CDAlg ℝ 4) :
    cdLo (gradV s) = (2 : ℝ) • (comm s * conj (cdHi s) - conj (cdHi s) * comm s) := by
  rw [gradV, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]

/-- High CD component of `∇V`. -/
theorem cdHi_gradV (s : CDAlg ℝ 4) :
    cdHi (gradV s) = (2 : ℝ) • (conj (cdLo s) * comm s - comm s * conj (cdLo s)) := by
  rw [gradV, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]

/-- **The defining property of `gradV`.** -/
theorem bil_gradV (s v : CDAlg ℝ 4) :
    bil (gradV s) v = 2 * bil (comm s) (secVar s v) := by
  have h1 : bil (comm s) (cdLo s * cdHi v) = bil (cdHi v) (conj (cdLo s) * comm s) := by
    rw [NormForm.bil_symm (comm s) _, bil_mul_left_adj]
  have h2 : bil (comm s) (cdHi v * cdLo s) = bil (cdHi v) (comm s * conj (cdLo s)) := by
    rw [NormForm.bil_symm (comm s) _, bil_mul_right_adj]
  have h3 : bil (comm s) (cdLo v * cdHi s) = bil (cdLo v) (comm s * conj (cdHi s)) := by
    rw [NormForm.bil_symm (comm s) _, bil_mul_right_adj]
  have h4 : bil (comm s) (cdHi s * cdLo v) = bil (cdLo v) (conj (cdHi s) * comm s) := by
    rw [NormForm.bil_symm (comm s) _, bil_mul_left_adj]
  rw [bil_split, cdLo_gradV, cdHi_gradV, secVar,
    bil_smul_left, bil_smul_left, bil_sub_left, bil_sub_left,
    bil_add_right, bil_sub_right, bil_sub_right,
    NormForm.bil_symm (comm s * conj (cdHi s)) (cdLo v),
    NormForm.bil_symm (conj (cdHi s) * comm s) (cdLo v),
    NormForm.bil_symm (conj (cdLo s) * comm s) (cdHi v),
    NormForm.bil_symm (comm s * conj (cdLo s)) (cdHi v)]
  linarith [h1, h2, h3, h4]

/-- The low embedding kills `0`. -/
theorem loOf_zero : loOf 0 = (0 : CDAlg ℝ 4) := by
  rw [loOf]; exact Finset.sum_eq_zero (fun p _ => by rw [zero_coord, zero_smul])

/-- The high embedding kills `0`. -/
theorem hiOf_zero : hiOf 0 = (0 : CDAlg ℝ 4) := by
  rw [hiOf]; exact Finset.sum_eq_zero (fun q _ => by rw [zero_coord, zero_smul])

/-- **At a crystal the gradient vanishes.**  This is the precise form of
    "`potential_taylor_at_vacuum` has no linear term": there the coefficient of `t`
    in `V(s + t·v)` is `2⟪C s, secVar s v⟫`, which vanishes identically in `v`
    because `C s = 0`.  Here the same fact is stated on the gradient itself. -/
theorem gradV_eq_zero_of_isVacuum {s : CDAlg ℝ 4} (hv : IsVacuum s) : gradV s = 0 := by
  rw [gradV, comm_eq_zero_of_isVacuum hv]
  simp only [alt_zero_mul, alt_mul_zero, sub_self, smul_zero, loOf_zero, hiOf_zero, add_zero]

/-! ## 4a. Smoothness infrastructure on the CD carriers -/

noncomputable scoped instance instFiniteDimensionalCD : FiniteDimensional ℝ (CDAlg ℝ n) :=
  Module.Finite.of_basis (QBP.Foundations.CDDimension.cdBasis n)

/-- The coordinate map as a continuous linear equivalence. -/
noncomputable def coordCLE (n : ℕ) : CDAlg ℝ n ≃L[ℝ] (Fin (2^n) → ℝ) :=
  (QBP.Foundations.CDDimension.coordEquiv n).toContinuousLinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}

/-- A `CDAlg`-valued map is `Cᵏ` iff each of its `2^n` coordinates is. -/
theorem contDiff_cd_iff {f : E → CDAlg ℝ n} :
    ContDiff ℝ k f ↔ ∀ i, ContDiff ℝ k (fun x => (f x).coord i) := by
  constructor
  · intro h i
    have h2 := ContDiff.fun_comp (ContinuousLinearMap.contDiff
      (coordCLE n : CDAlg ℝ n →L[ℝ] (Fin (2^n) → ℝ))) h
    exact contDiff_pi.mp h2 i
  · intro h
    have h2 := ContDiff.fun_comp (ContinuousLinearMap.contDiff
      ((coordCLE n).symm : (Fin (2^n) → ℝ) →L[ℝ] CDAlg ℝ n)) (contDiff_pi' h)
    exact h2

/-- Each coordinate functional is `Cᵏ`. -/
theorem contDiff_coord (i : Fin (2^n)) :
    ContDiff ℝ k (fun x : CDAlg ℝ n => x.coord i) :=
  contDiff_cd_iff.mp contDiff_id i

/-- Every ℝ-linear map between CD carriers is `Cᵏ` (finite dimension). -/
theorem contDiff_of_linear {m p : ℕ} (f : CDAlg ℝ m → CDAlg ℝ p)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (r : ℝ) x, f (r • x) = r • f x) :
    ContDiff ℝ k f :=
  ContinuousLinearMap.contDiff (LinearMap.toContinuousLinearMap
    ({ toFun := f, map_add' := hadd, map_smul' := hsmul } :
      CDAlg ℝ m →ₗ[ℝ] CDAlg ℝ p))

/-- A product of two `Cᵏ` `CDAlg`-valued maps is `Cᵏ` (multiplication is bilinear). -/
theorem contDiff_cdmul {m : ℕ} {f g : E → CDAlg ℝ m}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun x => f x * g x) := by
  rw [contDiff_cd_iff]
  intro i
  simp only [mul_coord]
  refine ContDiff.sum (fun p _ => ContDiff.sum (fun q _ => ?_))
  by_cases h : (p ^^^ q : Fin (2^m)) = i
  · simp only [h, if_pos]
    exact ContDiff.mul (ContDiff.mul contDiff_const (contDiff_cd_iff.mp hf p))
      (contDiff_cd_iff.mp hg q)
  · simp only [if_neg h]
    exact contDiff_const

/-- `cdLo` is `Cᵏ` (it is linear). -/
theorem contDiff_cdLo : ContDiff ℝ k (cdLo : CDAlg ℝ 4 → CDAlg ℝ 3) :=
  contDiff_of_linear _ cdLo_add cdLo_smul

/-- `cdHi` is `Cᵏ` (it is linear). -/
theorem contDiff_cdHi : ContDiff ℝ k (cdHi : CDAlg ℝ 4 → CDAlg ℝ 3) :=
  contDiff_of_linear _ cdHi_add cdHi_smul

/-- Conjugation is additive. -/
theorem conj_add (x y : CDAlg ℝ n) : conj (x + y) = conj x + conj y := by
  ext i
  simp only [conj_coord, add_coord]
  by_cases h : i.val = 0
  · simp [h]
  · simp only [h, if_false]; ring

/-- Conjugation is ℝ-homogeneous. -/
theorem conj_smul (r : ℝ) (x : CDAlg ℝ n) : conj (r • x) = r • conj x := by
  ext i
  simp only [conj_coord, smul_coord]
  by_cases h : i.val = 0
  · simp [h]
  · simp only [h, if_false]; ring

/-- Conjugation is `Cᵏ`. -/
theorem contDiff_conj : ContDiff ℝ k (conj : CDAlg ℝ n → CDAlg ℝ n) :=
  contDiff_of_linear _ conj_add conj_smul

/-- `loOf` is additive. -/
theorem loOf_add (a b : CDAlg ℝ 3) : loOf (a + b) = loOf a + loOf b := by
  ext i; rcases idx_cases i with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> simp

/-- `loOf` is ℝ-homogeneous. -/
theorem loOf_smul (r : ℝ) (a : CDAlg ℝ 3) : loOf (r • a) = r • loOf a := by
  ext i; rcases idx_cases i with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> simp

/-- `hiOf` is additive. -/
theorem hiOf_add (a b : CDAlg ℝ 3) : hiOf (a + b) = hiOf a + hiOf b := by
  ext i; rcases idx_cases i with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> simp

/-- `hiOf` is ℝ-homogeneous. -/
theorem hiOf_smul (r : ℝ) (a : CDAlg ℝ 3) : hiOf (r • a) = r • hiOf a := by
  ext i; rcases idx_cases i with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> simp

/-- `loOf` is `Cᵏ`. -/
theorem contDiff_loOf : ContDiff ℝ k (loOf : CDAlg ℝ 3 → CDAlg ℝ 4) :=
  contDiff_of_linear _ loOf_add loOf_smul

/-- `hiOf` is `Cᵏ`. -/
theorem contDiff_hiOf : ContDiff ℝ k (hiOf : CDAlg ℝ 3 → CDAlg ℝ 4) :=
  contDiff_of_linear _ hiOf_add hiOf_smul

/-- The commutator map is `Cᵏ` (it is quadratic). -/
theorem contDiff_comm : ContDiff ℝ k comm :=
  ContDiff.sub (contDiff_cdmul contDiff_cdLo contDiff_cdHi)
    (contDiff_cdmul contDiff_cdHi contDiff_cdLo)

/-- `N ∘ f` is `Cᵏ` when `f` is (a sum of squares of coordinates). -/
theorem contDiff_normForm {m : ℕ} {f : E → CDAlg ℝ m} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (fun x => N (f x)) := by
  simp only [N_def]
  exact ContDiff.sum (fun i _ => ContDiff.pow (contDiff_cd_iff.mp hf i) 2)

/-- **`V` is `C^∞` (indeed `Cᵏ` for every `k`)** — it is a quartic polynomial in
    the 16 sedenion coordinates. -/
theorem contDiff_potential : ContDiff ℝ k Hosting.potential :=
  contDiff_normForm contDiff_comm

/-- `∇V` is `Cᵏ` (a cubic polynomial map). -/
theorem contDiff_gradV : ContDiff ℝ k gradV := by
  have h1 : ContDiff ℝ k (fun s : CDAlg ℝ 4 =>
      comm s * conj (cdHi s) - conj (cdHi s) * comm s) :=
    ContDiff.sub (contDiff_cdmul contDiff_comm (ContDiff.fun_comp contDiff_conj contDiff_cdHi))
      (contDiff_cdmul (ContDiff.fun_comp contDiff_conj contDiff_cdHi) contDiff_comm)
  have h2 : ContDiff ℝ k (fun s : CDAlg ℝ 4 =>
      conj (cdLo s) * comm s - comm s * conj (cdLo s)) :=
    ContDiff.sub (contDiff_cdmul (ContDiff.fun_comp contDiff_conj contDiff_cdLo) contDiff_comm)
      (contDiff_cdmul contDiff_comm (ContDiff.fun_comp contDiff_conj contDiff_cdLo))
  exact ContDiff.add (ContDiff.fun_comp contDiff_loOf (ContDiff.const_smul (2 : ℝ) h1))
    (ContDiff.fun_comp contDiff_hiOf (ContDiff.const_smul (2 : ℝ) h2))

/-! ## 4b. `gradV` really IS the derivative of `V`

The route: `V` restricted to the ray `t ↦ s + t·v` is an EXACT quartic in `t`
(`potential_along_ray`), whose linear coefficient is `2⟪C s, secVar s v⟫ =
⟪gradV s, v⟫`.  Since `V` is differentiable (§4a), uniqueness of the derivative
pins `fderiv ℝ V s` to `⟪gradV s, ·⟫`. -/

/-- Three-term polarization of `N`. -/
theorem N_add3 (x y z : CDAlg ℝ m) :
    N (x + y + z) = N x + N y + N z + 2 * bil x y + 2 * bil x z + 2 * bil y z := by
  rw [alt_N_add, alt_N_add, bil_add_left]; ring

/-- **`V` along a ray is an exact quartic.**  The `t`-coefficient is the
    directional derivative; this is the general (no-vacuum-hypothesis) form of
    `CrystalHosting.potential_taylor_at_vacuum`. -/
theorem potential_along_ray (s v : CDAlg ℝ 4) (t : ℝ) :
    Hosting.potential (s + t • v)
      = Hosting.potential s
        + (2 * bil (comm s) (secVar s v)) * t
        + (N (secVar s v) + 2 * bil (comm s) (quadVar v)) * t ^ 2
        + (2 * bil (secVar s v) (quadVar v)) * t ^ 3
        + N (quadVar v) * t ^ 4 := by
  rw [potential_eq_N_comm, potential_eq_N_comm, comm_along_ray, N_add3,
    QBP.Foundations.NoAutonomousDynamics.N_smul, QBP.Foundations.NoAutonomousDynamics.N_smul,
    bil_smul_right, bil_smul_right, bil_smul_left, bil_smul_right]
  ring

/-- The directional derivative of `V` at `s` along `v`. -/
theorem hasDerivAt_potential_ray (s v : CDAlg ℝ 4) :
    HasDerivAt (fun t : ℝ => Hosting.potential (s + t • v))
      (2 * bil (comm s) (secVar s v)) 0 := by
  set A := Hosting.potential s
  set B := 2 * bil (comm s) (secVar s v)
  set C := N (secVar s v) + 2 * bil (comm s) (quadVar v)
  set D := 2 * bil (secVar s v) (quadVar v)
  set Eq := N (quadVar v)
  have hfun : (fun t : ℝ => Hosting.potential (s + t • v))
      = fun t : ℝ => A + B * t + C * t ^ 2 + D * t ^ 3 + Eq * t ^ 4 :=
    funext (potential_along_ray s v)
  rw [hfun]
  refine HasDerivAt.congr_deriv
    (((((hasDerivAt_const (0 : ℝ) A).add ((hasDerivAt_id (0 : ℝ)).const_mul B)).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul C)).add
      ((hasDerivAt_pow 3 (0 : ℝ)).const_mul D)).add
      ((hasDerivAt_pow 4 (0 : ℝ)).const_mul Eq)) ?_
  norm_num

/-- `V` is differentiable everywhere. -/
theorem differentiable_potential : Differentiable ℝ Hosting.potential :=
  ContDiff.differentiable (contDiff_potential (k := ⊤)) (by simp)

/-- `∇V` is differentiable everywhere. -/
theorem differentiable_gradV : Differentiable ℝ gradV :=
  ContDiff.differentiable (contDiff_gradV (k := ⊤)) (by simp)

/-- **`fderiv ℝ V s v = ⟪gradV s, v⟫` for every `v`.**  This is the theorem that
    makes `gradV` the gradient rather than an arbitrary cubic map. -/
theorem fderiv_potential_apply (s v : CDAlg ℝ 4) :
    fderiv ℝ Hosting.potential s v = bil (gradV s) v := by
  have hray : HasDerivAt (fun t : ℝ => s + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add s
  have hF : HasFDerivAt Hosting.potential (fderiv ℝ Hosting.potential s)
      ((fun t : ℝ => s + t • v) 0) := by
    rw [show ((fun t : ℝ => s + t • v) 0) = s by simp]
    exact (differentiable_potential s).hasFDerivAt
  have h1 := hF.comp_hasDerivAt 0 hray
  rw [bil_gradV]
  exact HasDerivAt.unique h1 (hasDerivAt_potential_ray s v)

/-- `fderiv ℝ V s = ⟪gradV s, ·⟫` as continuous linear maps. -/
theorem fderiv_potential (s : CDAlg ℝ 4) :
    fderiv ℝ Hosting.potential s = innerSL ℝ (gradV s) := by
  ext v; rw [fderiv_potential_apply]; rfl

/-- **`gradV` is the Fréchet derivative of `V`.** -/
theorem hasFDerivAt_potential (s : CDAlg ℝ 4) :
    HasFDerivAt Hosting.potential (innerSL ℝ (gradV s)) s := by
  rw [← fderiv_potential s]
  exact (differentiable_potential s).hasFDerivAt

/-- **`gradV` is the gradient of `V`** in the `N`-metric. -/
theorem hasGradientAt_potential (s : CDAlg ℝ 4) :
    HasGradientAt Hosting.potential (gradV s) s := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : (InnerProductSpace.toDual ℝ (CDAlg ℝ 4)) (gradV s) = innerSL ℝ (gradV s) := by
    ext v; rfl
  rw [h]
  exact hasFDerivAt_potential s

/-! ## 5. The rule field `F` — THE POSTULATE (#635)

`F s = −(∇V(s) − ⟪∇V(s),s⟫·s − (∇V(s))₀·1)`: minus the gradient, projected onto
the orthogonal complement of `span{s, 1}`, i.e. tangent to the unit sphere AND
to the imaginary hyperplane.  On `StateSphere` (`s₀ = 0`, `N s = 1`) the vectors
`s` and `1` are orthonormal, so this really is the orthogonal projection. -/

/-- `⟪1,x⟫ = x₀`. -/
theorem bil_one_left (x : CDAlg ℝ n) : bil 1 x = x.coord 0 := by
  rw [NormForm.bil_symm]; exact bil_one_right x

/-- `bil` is odd in its left argument. -/
theorem bil_neg_left (x y : CDAlg ℝ n) : bil (-x) y = - bil x y := by
  simp only [bil_def, neg_coord, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `⟪x,x⟫ = N x`. -/
theorem bil_self_eq_N (x : CDAlg ℝ n) : bil x x = N x := (N_eq_bil x).symm

/-- **THE RULE (POSTULATE, #635).**  `F s = −(∇V(s) − ⟪∇V(s),s⟫·s − (∇V(s))₀·1)`:
    first-order overdamped descent of `V` in the `N`-metric, projected tangent to
    the unit sphere and to the imaginary hyperplane.  The postulated dynamics is
    `γ' = F ∘ γ`.  Nothing in this file argues that this is the correct rule. -/
noncomputable def ruleField (s : CDAlg ℝ 4) : CDAlg ℝ 4 :=
  -(gradV s - (bil (gradV s) s) • s - ((gradV s).coord 0) • (1 : CDAlg ℝ 4))

/-- The orthogonal decomposition of `∇V` that defines `F`. -/
theorem gradV_decomp (s : CDAlg ℝ 4) :
    gradV s = -(ruleField s) + (bil (gradV s) s) • s + ((gradV s).coord 0) • (1 : CDAlg ℝ 4) := by
  rw [ruleField]; module

/-- **`F s ⟂ s` on the state sphere** — the flow is tangent to the sphere. -/
theorem ruleField_bil_self {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) :
    bil (ruleField s) s = 0 := by
  have h1 : bil s s = 1 := by rw [bil_self_eq_N, hs.2]
  have h2 : bil (1 : CDAlg ℝ 4) s = 0 := by rw [bil_one_left, hs.1]
  rw [ruleField, bil_neg_left, bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left, h1, h2]
  ring

/-- **`(F s)₀ = 0` on the state sphere** — the flow stays in the imaginary
    hyperplane. -/
theorem ruleField_coord_zero {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) :
    (ruleField s).coord 0 = 0 := by
  rw [ruleField, neg_coord, sub_coord, sub_coord, smul_coord, smul_coord, one_coord,
    if_pos rfl, hs.1]
  ring

/-- **Every crystal is a rest point of the rule.**  (The CONVERSE — that every
    rest point is a crystal — is NOT claimed and is false in general: a critical
    point of a quartic on a sphere need not be a minimum.  See
    FLAG-rule-flow-open.) -/
theorem ruleField_eq_zero_of_isVacuum {s : CDAlg ℝ 4} (hv : IsVacuum s) : ruleField s = 0 := by
  rw [ruleField, gradV_eq_zero_of_isVacuum hv]
  simp

/-- **Exactly what a rest point is:** `F s = 0` iff the tangential part of `∇V`
    vanishes, i.e. `∇V(s) ∈ span{s, 1}`.  This is the honest characterisation;
    it does NOT say `s` is a vacuum. -/
theorem ruleField_eq_zero_iff (s : CDAlg ℝ 4) :
    ruleField s = 0 ↔
      gradV s = (bil (gradV s) s) • s + ((gradV s).coord 0) • (1 : CDAlg ℝ 4) := by
  rw [ruleField, neg_eq_zero, sub_sub, sub_eq_zero]

/-- `F` is `Cᵏ`. -/
theorem contDiff_ruleField : ContDiff ℝ k ruleField := by
  have hb : ContDiff ℝ k (fun s : CDAlg ℝ 4 => bil (gradV s) s) := by
    simp only [bil_def]
    exact ContDiff.sum (fun i _ =>
      ContDiff.mul (contDiff_cd_iff.mp contDiff_gradV i) (contDiff_coord i))
  have h0 : ContDiff ℝ k (fun s : CDAlg ℝ 4 => (gradV s).coord 0) :=
    contDiff_cd_iff.mp contDiff_gradV 0
  exact ContDiff.neg (ContDiff.sub (ContDiff.sub contDiff_gradV (ContDiff.smul hb contDiff_id))
    (ContDiff.smul h0 contDiff_const))

/-- `F` is differentiable everywhere. -/
theorem differentiable_ruleField : Differentiable ℝ ruleField :=
  ContDiff.differentiable (contDiff_ruleField (k := ⊤)) (by simp)

/-! ## 6. Derivatives along an integral curve -/

/-- The `i`-th coordinate as a continuous linear functional. -/
noncomputable def coordCLM (n : ℕ) (i : Fin (2^n)) : CDAlg ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun x => x.coord i, map_add' := fun x y => rfl,
       map_smul' := fun r x => rfl } : CDAlg ℝ n →ₗ[ℝ] ℝ)

/-- Coordinates of a differentiable curve differentiate coordinate-wise. -/
theorem hasDerivAt_coord {γ : ℝ → CDAlg ℝ n} {w : CDAlg ℝ n} {t : ℝ}
    (h : HasDerivAt γ w t) (i : Fin (2^n)) :
    HasDerivAt (fun r => (γ r).coord i) (w.coord i) t :=
  (coordCLM n i).hasFDerivAt.comp_hasDerivAt t h

/-- **`coord 0` is stationary at state-sphere points.** -/
theorem hasDerivAt_coord_zero_along_flow {γ : ℝ → CDAlg ℝ 4} {t : ℝ}
    (hγ : HasDerivAt γ (ruleField (γ t)) t) (hs : γ t ∈ Hosting.StateSphere) :
    HasDerivAt (fun r => (γ r).coord 0) 0 t := by
  have h := hasDerivAt_coord hγ 0
  rwa [ruleField_coord_zero hs] at h

/-- **The norm form is stationary at state-sphere points.** -/
theorem hasDerivAt_normForm_along_flow {γ : ℝ → CDAlg ℝ 4} {t : ℝ}
    (hγ : HasDerivAt γ (ruleField (γ t)) t) (hs : γ t ∈ Hosting.StateSphere) :
    HasDerivAt (fun r => N (γ r)) 0 t := by
  have h := HasDerivAt.inner (𝕜 := ℝ) hγ hγ
  have hz : (inner ℝ (γ t) (ruleField (γ t)) : ℝ) + (inner ℝ (ruleField (γ t)) (γ t) : ℝ) = 0 := by
    show bil (γ t) (ruleField (γ t)) + bil (ruleField (γ t)) (γ t) = 0
    rw [NormForm.bil_symm (γ t) _, ruleField_bil_self hs]; ring
  rw [hz] at h
  have hfun : (fun r => (inner ℝ (γ r) (γ r) : ℝ)) = fun r => N (γ r) := by
    funext r; exact (N_eq_bil (γ r)).symm
  rwa [hfun] at h

/-- **`⟪∇V, F⟫ = −‖F‖²`** on the state sphere (`F` is minus the orthogonal
    projection of `∇V`). -/
theorem bil_gradV_ruleField {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) :
    bil (gradV s) (ruleField s) = - N (ruleField s) := by
  have h1 : bil s (ruleField s) = 0 := by
    rw [NormForm.bil_symm]; exact ruleField_bil_self hs
  have h2 : bil (1 : CDAlg ℝ 4) (ruleField s) = 0 := by
    rw [bil_one_left]; exact ruleField_coord_zero hs
  conv_lhs => rw [gradV_decomp s]
  rw [bil_add_left, bil_add_left, bil_neg_left, bil_smul_left, bil_smul_left, h1, h2,
    bil_self_eq_N]
  ring

/-- **The potential is non-increasing along the flow:** `d/dt V(γ t) = −‖F(γ t)‖² ≤ 0`. -/
theorem hasDerivAt_potential_along_flow {γ : ℝ → CDAlg ℝ 4} {t : ℝ}
    (hγ : HasDerivAt γ (ruleField (γ t)) t) (hs : γ t ∈ Hosting.StateSphere) :
    HasDerivAt (fun r => Hosting.potential (γ r)) (- N (ruleField (γ t))) t := by
  have h := (hasFDerivAt_potential (γ t)).comp_hasDerivAt t hγ
  have he : (innerSL ℝ (gradV (γ t))) (ruleField (γ t)) = - N (ruleField (γ t)) := by
    show bil (gradV (γ t)) (ruleField (γ t)) = _
    exact bil_gradV_ruleField hs
  rw [he] at h
  exact h

/-- **The rule is a descent:** `d/dt V(γ t) ≤ 0`. -/
theorem potential_nonincreasing_along_flow {γ : ℝ → CDAlg ℝ 4} {t : ℝ}
    (hγ : HasDerivAt γ (ruleField (γ t)) t) (hs : γ t ∈ Hosting.StateSphere) :
    deriv (fun r => Hosting.potential (γ r)) t ≤ 0 := by
  rw [(hasDerivAt_potential_along_flow hγ hs).deriv]
  exact neg_nonpos.mpr (alt_N_nonneg _)

/-! ## 7. `F` is Lipschitz on balls; the Euler step deletes nothing -/

/-- State-sphere points have analytic norm 1. -/
theorem norm_eq_one_of_mem_stateSphere {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) :
    ‖s‖ = 1 := by
  have h : ‖s‖ ^ 2 = 1 := by rw [norm_sq_eq_normForm, hs.2]
  nlinarith [norm_nonneg s, h]

/-- The state sphere sits in the closed unit ball. -/
theorem stateSphere_subset_closedBall :
    Hosting.StateSphere ⊆ Metric.closedBall (0 : CDAlg ℝ 4) 1 := by
  intro s hs
  rw [Metric.mem_closedBall, dist_zero_right, norm_eq_one_of_mem_stateSphere hs]

/-- **`F` is Lipschitz on every closed ball** (it is a polynomial map on a
    finite-dimensional space, hence `C^∞` with `fderiv` bounded on compacts). -/
theorem exists_lipschitzOnWith_ruleField (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K ruleField (Metric.closedBall (0 : CDAlg ℝ 4) R) := by
  have hcomp : IsCompact (Metric.closedBall (0 : CDAlg ℝ 4) R) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    (ContDiff.continuous_fderiv (contDiff_ruleField (k := ⊤)) (by simp)).continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => differentiable_ruleField x) (fun x hx => ?_) (convex_closedBall _ _)
  have hb : ‖fderiv ℝ ruleField x‖ ≤ max C 0 := le_trans (hC x hx) (le_max_left _ _)
  exact hb

/-- `F` is Lipschitz on the state sphere. -/
theorem exists_lipschitzOnWith_ruleField_stateSphere :
    ∃ K : NNReal, LipschitzOnWith K ruleField Hosting.StateSphere := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_ruleField 1
  exact ⟨K, hK.mono stateSphere_subset_closedBall⟩

/-- The explicit Euler step of the rule at step size `h`. -/
noncomputable def eulerStep (h : ℝ) (s : CDAlg ℝ 4) : CDAlg ℝ 4 := s + h • ruleField s

/-- **No-deletion (un-normalised).** -/
theorem eulerStep_injOn {K : NNReal} {h : ℝ} {S : Set (CDAlg ℝ 4)}
    (hK : LipschitzOnWith K ruleField S) (hh : 0 < h) (hhK : h * (K : ℝ) < 1) :
    Set.InjOn (eulerStep h) S := by
  intro s hs s' hs' heq
  by_contra hne
  have h0 : (s + h • ruleField s) - (s' + h • ruleField s') = 0 := by
    rw [show s + h • ruleField s = s' + h • ruleField s' from heq, sub_self]
  have h1 : s - s' = h • (ruleField s' - ruleField s) := by
    rw [smul_sub]
    have h0' : s - s' - (h • ruleField s' - h • ruleField s)
        = (s + h • ruleField s) - (s' + h • ruleField s') := by module
    rw [← sub_eq_zero, h0', h0]
  have h2 : ‖s - s'‖ = h * ‖ruleField s' - ruleField s‖ := by
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have h3 : ‖ruleField s' - ruleField s‖ ≤ (K : ℝ) * ‖s - s'‖ := by
    have hd := hK.dist_le_mul s' hs' s hs
    rw [dist_eq_norm, dist_eq_norm] at hd
    calc ‖ruleField s' - ruleField s‖ ≤ (K : ℝ) * ‖s' - s‖ := hd
      _ = (K : ℝ) * ‖s - s'‖ := by rw [norm_sub_rev]
  have h4 : 0 < ‖s - s'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith [h2, h3, h4, hhK, hh, norm_nonneg (ruleField s' - ruleField s)]

/-- `‖s + h·F s‖² = 1 + h²‖F s‖²` on the state sphere (`F s ⟂ s`). -/
theorem normForm_eulerStep {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) (h : ℝ) :
    N (eulerStep h s) = 1 + h ^ 2 * N (ruleField s) := by
  have hperp : bil s (ruleField s) = 0 := by
    rw [NormForm.bil_symm]; exact ruleField_bil_self hs
  rw [eulerStep, alt_N_add, bil_smul_right, hperp,
    QBP.Foundations.NoAutonomousDynamics.N_smul, hs.2]
  ring

/-- The renormalised (sphere-preserving) Euler step. -/
noncomputable def renormStep (h : ℝ) (s : CDAlg ℝ 4) : CDAlg ℝ 4 :=
  Hosting.normalise (eulerStep h s)

/-- **No-deletion for the renormalised step, on a level set of `‖F‖`.** -/
theorem renormStep_injOn_of_normForm_const {K : NNReal} {h c : ℝ} {S : Set (CDAlg ℝ 4)}
    (hS : S ⊆ Hosting.StateSphere) (hK : LipschitzOnWith K ruleField S)
    (hh : 0 < h) (hhK : h * (K : ℝ) < 1) (hc : ∀ s ∈ S, N (ruleField s) = c) :
    Set.InjOn (renormStep h) S := by
  have hpos : (0 : ℝ) < 1 + h ^ 2 * c ∨ S = ∅ := by
    rcases Set.eq_empty_or_nonempty S with he | ⟨s, hsS⟩
    · exact Or.inr he
    · refine Or.inl ?_
      have := hc s hsS
      have hN : 0 ≤ N (ruleField s) := alt_N_nonneg _
      nlinarith [sq_nonneg h]
  rcases hpos with hpos | he
  · intro s hs s' hs' heq
    have hns : N (eulerStep h s) = 1 + h ^ 2 * c := by
      rw [normForm_eulerStep (hS hs), hc s hs]
    have hns' : N (eulerStep h s') = 1 + h ^ 2 * c := by
      rw [normForm_eulerStep (hS hs'), hc s' hs']
    have hr : (Real.sqrt (1 + h ^ 2 * c))⁻¹ ≠ 0 :=
      inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hpos))
    have heq' : eulerStep h s = eulerStep h s' := by
      have h1 : (Real.sqrt (1 + h ^ 2 * c))⁻¹ • eulerStep h s
          = (Real.sqrt (1 + h ^ 2 * c))⁻¹ • eulerStep h s' := by
        have := heq
        rw [renormStep, renormStep, Hosting.normalise_def, Hosting.normalise_def,
          hns, hns'] at this
        exact this
      exact smul_right_injective _ hr h1
    exact eulerStep_injOn hK hh hhK hs hs' heq'
  · intro s hs; rw [he] at hs; exact absurd hs (Set.notMem_empty s)

/-! ## 8. Finite-time uniqueness of integral curves

Global existence is NOT proved (FLAG-rule-flow-open); these are conditional on
curves supplied as hypotheses. -/

/-- **Any two integral curves of the rule that agree at one interior time agree
    throughout** (on a closed interval, while both stay in a fixed ball).
    Existence of such curves is NOT asserted — see FLAG-rule-flow-open. -/
theorem flow_unique_of_mem_Icc {a b t₀ R : ℝ} {γ₁ γ₂ : ℝ → CDAlg ℝ 4}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hc₁ : ContinuousOn γ₁ (Set.Icc a b))
    (hd₁ : ∀ t ∈ Set.Ioo a b, HasDerivAt γ₁ (ruleField (γ₁ t)) t)
    (hb₁ : ∀ t ∈ Set.Ioo a b, γ₁ t ∈ Metric.closedBall (0 : CDAlg ℝ 4) R)
    (hc₂ : ContinuousOn γ₂ (Set.Icc a b))
    (hd₂ : ∀ t ∈ Set.Ioo a b, HasDerivAt γ₂ (ruleField (γ₂ t)) t)
    (hb₂ : ∀ t ∈ Set.Ioo a b, γ₂ t ∈ Metric.closedBall (0 : CDAlg ℝ 4) R)
    (heq : γ₁ t₀ = γ₂ t₀) :
    Set.EqOn γ₁ γ₂ (Set.Icc a b) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_ruleField R
  exact ODE_solution_unique_of_mem_Icc (K := K) (v := fun _ x => ruleField x)
    (s := fun _ => Metric.closedBall (0 : CDAlg ℝ 4) R)
    (fun t _ => hK) ht₀ hc₁ hd₁ hb₁ hc₂ hd₂ hb₂ heq

/-- Time-reversed form: agreement at the right endpoint propagates backwards. -/
theorem flow_unique_of_endpoint {a b R : ℝ} {γ₁ γ₂ : ℝ → CDAlg ℝ 4}
    (hc₁ : ContinuousOn γ₁ (Set.Icc a b))
    (hd₁ : ∀ t ∈ Set.Ioc a b, HasDerivAt γ₁ (ruleField (γ₁ t)) t)
    (hb₁ : ∀ t ∈ Set.Ioc a b, γ₁ t ∈ Metric.closedBall (0 : CDAlg ℝ 4) R)
    (hc₂ : ContinuousOn γ₂ (Set.Icc a b))
    (hd₂ : ∀ t ∈ Set.Ioc a b, HasDerivAt γ₂ (ruleField (γ₂ t)) t)
    (hb₂ : ∀ t ∈ Set.Ioc a b, γ₂ t ∈ Metric.closedBall (0 : CDAlg ℝ 4) R)
    (heq : γ₁ b = γ₂ b) :
    Set.EqOn γ₁ γ₂ (Set.Icc a b) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_ruleField R
  exact ODE_solution_unique_of_mem_Icc_left (K := K) (v := fun _ x => ruleField x)
    (s := fun _ => Metric.closedBall (0 : CDAlg ℝ 4) R)
    (fun t _ => hK) hc₁ (fun t ht => (hd₁ t ht).hasDerivWithinAt) hb₁
    hc₂ (fun t ht => (hd₂ t ht).hasDerivWithinAt) hb₂ heq

/-- **The time-`t` map of the rule is injective where it is defined.** -/
theorem flow_time_map_injective {a b R : ℝ} (hab : a ≤ b) {γ₁ γ₂ : ℝ → CDAlg ℝ 4}
    (hc₁ : ContinuousOn γ₁ (Set.Icc a b))
    (hd₁ : ∀ t ∈ Set.Ioc a b, HasDerivAt γ₁ (ruleField (γ₁ t)) t)
    (hb₁ : ∀ t ∈ Set.Ioc a b, γ₁ t ∈ Metric.closedBall (0 : CDAlg ℝ 4) R)
    (hc₂ : ContinuousOn γ₂ (Set.Icc a b))
    (hd₂ : ∀ t ∈ Set.Ioc a b, HasDerivAt γ₂ (ruleField (γ₂ t)) t)
    (hb₂ : ∀ t ∈ Set.Ioc a b, γ₂ t ∈ Metric.closedBall (0 : CDAlg ℝ 4) R)
    (heq : γ₁ b = γ₂ b) :
    γ₁ a = γ₂ a :=
  flow_unique_of_endpoint hc₁ hd₁ hb₁ hc₂ hd₂ hb₂ heq (Set.left_mem_Icc.mpr hab)

/-! ## 9. The state sphere is invariant -/

/-- The scalar part of `F` OFF the sphere: `(F s)₀ = ⟪∇V(s),s⟫·s₀`.  A linear
    scalar ODE in `s₀` — this is why `s₀ = 0` propagates. -/
theorem ruleField_coord_zero_general (s : CDAlg ℝ 4) :
    (ruleField s).coord 0 = bil (gradV s) s * s.coord 0 := by
  rw [ruleField, neg_coord, sub_coord, sub_coord, smul_coord, smul_coord, one_coord,
    if_pos rfl]
  ring

/-- The radial part of `F` OFF the sphere:
    `⟪F s,s⟫ = ⟪∇V(s),s⟫·(N s − 1) + (∇V(s))₀·s₀`. -/
theorem bil_ruleField_self_general (s : CDAlg ℝ 4) :
    bil (ruleField s) s = bil (gradV s) s * (N s - 1) + (gradV s).coord 0 * s.coord 0 := by
  rw [ruleField, bil_neg_left, bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left,
    bil_self_eq_N, bil_one_left]
  ring

/-- **A scalar linear ODE `u' = c(t)·u` with a zero value has `u ≡ 0`.** -/
theorem scalar_linear_ode_zero {a b t₀ : ℝ} {c u : ℝ → ℝ}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hc : ContinuousOn c (Set.Icc a b))
    (hu : ContinuousOn u (Set.Icc a b))
    (hu' : ∀ t ∈ Set.Ioo a b, HasDerivAt u (c t * u t) t)
    (h0 : u t₀ = 0) :
    ∀ t ∈ Set.Icc a b, u t = 0 := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc
  have hMnn : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hlip : ∀ t ∈ Set.Ioo a b,
      LipschitzOnWith ⟨max M 0, hMnn⟩ (fun x : ℝ => c t * x) Set.univ := by
    intro t ht
    have htI : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
    have habs : |c t| ≤ max M 0 := le_trans (hM t htI) (le_max_left _ _)
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul (fun x y => ?_))
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
  have hzero : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (c t * (0 : ℝ)) t := by
    intro t _
    simpa using hasDerivAt_const t (0 : ℝ)
  have h := ODE_solution_unique_of_mem_Icc (K := ⟨max M 0, hMnn⟩) (v := fun t x => c t * x)
    (s := fun _ => Set.univ) hlip ht₀ hu hu' (fun _ _ => Set.mem_univ _)
    continuousOn_const hzero (fun _ _ => Set.mem_univ _) h0
  intro t ht
  exact h ht

/-- **`StateSphere` is invariant under the rule.**  Any integral curve of `F` that
    is on the state sphere at one interior time stays on it. -/
theorem stateSphere_invariant {a b t₀ : ℝ} {γ : ℝ → CDAlg ℝ 4}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : γ t₀ ∈ Hosting.StateSphere) :
    ∀ t ∈ Set.Icc a b, γ t ∈ Hosting.StateSphere := by
  have hgc : Continuous (fun x : CDAlg ℝ 4 => bil (gradV x) x) := by
    simp only [bil_def]
    exact continuous_finsetSum _ (fun i _ =>
      Continuous.mul
        (ContDiff.continuous (contDiff_cd_iff.mp (contDiff_gradV (k := ⊤)) i))
        (ContDiff.continuous (contDiff_coord (k := ⊤) i)))
  have hcc : ContinuousOn (fun t => bil (gradV (γ t)) (γ t)) (Set.Icc a b) :=
    hgc.comp_continuousOn hcont
  -- Step A: the scalar coordinate stays zero.
  have hA : ∀ t ∈ Set.Icc a b, (γ t).coord 0 = 0 := by
    refine scalar_linear_ode_zero ht₀ hcc ?_ ?_ hmem.1
    · exact (ContDiff.continuous (contDiff_coord (k := ⊤) (0 : Fin (2^4)))).comp_continuousOn hcont
    · intro t ht
      have h := hasDerivAt_coord (hd t ht) (0 : Fin (2^4))
      rwa [ruleField_coord_zero_general (γ t)] at h
  -- Step B: with the scalar part zero, the norm form stays 1.
  have hB : ∀ t ∈ Set.Icc a b, N (γ t) - 1 = 0 := by
    refine scalar_linear_ode_zero (c := fun t => 2 * bil (gradV (γ t)) (γ t)) ht₀
      (continuousOn_const.mul hcc) ?_ ?_ (by rw [hmem.2, sub_self])
    · exact ((ContDiff.continuous (contDiff_normForm (f := id) (k := ⊤)
        contDiff_id)).comp_continuousOn hcont).sub continuousOn_const
    · intro t ht
      have hin := HasDerivAt.inner (𝕜 := ℝ) (hd t ht) (hd t ht)
      have hfun : (fun r => (inner ℝ (γ r) (γ r) : ℝ)) = fun r => N (γ r) := by
        funext r; exact (N_eq_bil (γ r)).symm
      rw [hfun] at hin
      have hval : (inner ℝ (γ t) (ruleField (γ t)) : ℝ)
          + (inner ℝ (ruleField (γ t)) (γ t) : ℝ)
          = 2 * bil (gradV (γ t)) (γ t) * (N (γ t) - 1) := by
        show bil (γ t) (ruleField (γ t)) + bil (ruleField (γ t)) (γ t) = _
        rw [NormForm.bil_symm (γ t) _, bil_ruleField_self_general,
          hA t (Set.Ioo_subset_Icc_self ht)]
        ring
      rw [hval] at hin
      exact hin.sub_const 1
  intro t ht
  exact ⟨hA t ht, by have := hB t ht; linarith⟩

/-! ## 10. Non-vacuity: the landscape is not flat -/

/-- Basis vectors are unit for `N`. -/
theorem N_e (i : Fin (2^n)) : N (e i : CDAlg ℝ n) = 1 := by
  rw [N_def, Finset.sum_eq_single i]
  · rw [e_coord, if_pos rfl]; norm_num
  · intro b _ hb; rw [e_coord, if_neg hb]; norm_num
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A concrete in-flight sedenion: `e₁ + e₂ℓ`, whose CD components do not commute. -/
noncomputable def witness : CDAlg ℝ 4 := loOf (e 1) + hiOf (e 2)

/-- The witness's commutator is `±2·e₃ ≠ 0`. -/
theorem comm_witness :
    comm witness = ((2 * (mulCoeff 3 1 2 : ℤ) : ℤ) : ℝ) • (e 3 : CDAlg ℝ 3) := by
  have h21 : mulCoeff 3 2 1 = - mulCoeff 3 1 2 := by decide
  have hx1 : (1 ^^^ 2 : Fin (2^3)) = 3 := by decide
  have hx2 : (2 ^^^ 1 : Fin (2^3)) = 3 := by decide
  have hlo : cdLo witness = e 1 := by
    rw [witness, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]
  have hhi : cdHi witness = e 2 := by
    rw [witness, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]
  rw [comm, hlo, hhi, e_mul_e, e_mul_e, hx1, hx2, h21, ← sub_smul]
  congr 1
  push_cast
  ring

/-- **`V` takes the value 4 at the witness** — the landscape is not identically
    zero. -/
theorem potential_witness : Hosting.potential witness = 4 := by
  have hsq : (mulCoeff 3 1 2 : ℤ) * (mulCoeff 3 1 2 : ℤ) = 1 := by decide
  rw [potential_eq_N_comm, comm_witness, QBP.Foundations.NoAutonomousDynamics.N_smul, N_e]
  have : ((2 * (mulCoeff 3 1 2 : ℤ) : ℤ) : ℝ) ^ 2 = 4 := by
    have : ((2 * (mulCoeff 3 1 2 : ℤ) : ℤ) : ℝ) ^ 2
        = 4 * (((mulCoeff 3 1 2 : ℤ) * (mulCoeff 3 1 2 : ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [this, hsq]; norm_num
  rw [this]; ring

/-- `V(0) = 0`. -/
theorem potential_zero : Hosting.potential (0 : CDAlg ℝ 4) = 0 := by
  have h : comm (0 : CDAlg ℝ 4) = 0 := by
    rw [comm]
    have h1 : cdLo (0 : CDAlg ℝ 4) = 0 := by ext p; rfl
    have h2 : cdHi (0 : CDAlg ℝ 4) = 0 := by ext q; rfl
    rw [h1, h2, alt_zero_mul, sub_self]
  rw [potential_eq_N_comm, h]
  rw [N_def]
  exact Finset.sum_eq_zero (fun i _ => by rw [zero_coord]; ring)

/-- **The landscape is not flat, hence the gradient is not identically zero.** -/
theorem exists_gradV_ne_zero : ∃ s : CDAlg ℝ 4, gradV s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hfd : ∀ x : CDAlg ℝ 4, fderiv ℝ Hosting.potential x = 0 := by
    intro x
    rw [fderiv_potential, hcon x]
    ext v
    simp
  have hconst := is_const_of_fderiv_eq_zero differentiable_potential hfd witness 0
  rw [potential_witness, potential_zero] at hconst
  norm_num at hconst

/-! ## 12. The closed form of `V` (P1) and the sharp bound `V ≤ N²` (P2)

`P1` is the keystone of the #635 confirmer's proof-owed list
(`docs/foundations/rule-flow-research-conversation-confirmer-verdict-2026-09-20.md`
§7): `V` depends only on the *imaginary parts* of the two Cayley–Dickson
components, through the Gram determinant of the pair.  `Foundations`'
`DeltaLandscape.sedenion_landscape_descends` is the same identity under the
standing hypothesis `s.coord 0 = 0`; the statement below drops that hypothesis
(the real part of `cdLo s` is central for the commutator too), which is what the
downstream global bound `V ≤ N²` needs. -/

/-- The imaginary part `Im x = x − x₀·1`. -/
def imPart (x : CDAlg ℝ n) : CDAlg ℝ n := x - (x.coord 0) • (1 : CDAlg ℝ n)

theorem imPart_def (x : CDAlg ℝ n) : imPart x = x - (x.coord 0) • (1 : CDAlg ℝ n) := rfl

/-- `Im x` is imaginary. -/
theorem imPart_coord_zero (x : CDAlg ℝ n) : (imPart x).coord 0 = 0 :=
  QBP.Foundations.DeltaLandscape.im_coord_zero x

/-- `N (Im x) = N x − x₀²`. -/
theorem N_imPart (x : CDAlg ℝ n) : N (imPart x) = N x - (x.coord 0) ^ 2 := by
  have h : imPart x = x + (-(x.coord 0)) • (1 : CDAlg ℝ n) := by
    rw [imPart_def, neg_smul]; abel
  rw [h, alt_N_add, bil_smul_right, bil_one_right,
    QBP.Foundations.NoAutonomousDynamics.N_smul, N_one']
  ring

/-- `N (Im x) ≤ N x`. -/
theorem N_imPart_le (x : CDAlg ℝ n) : N (imPart x) ≤ N x := by
  rw [N_imPart]; nlinarith [sq_nonneg (x.coord 0)]

/-- **Real multiples of `1` are central for the commutator — left version.**
    `[x − r·1, y] = [x, y]`.  (`DeltaLandscape.commutator_sub_central` is the
    right version.) -/
theorem commutator_sub_central_left {R : Type*} [CommRing R] {n : ℕ}
    (r : R) (x y : CDAlg R n) :
    (x - r • (1 : CDAlg R n)) * y - y * (x - r • (1 : CDAlg R n)) = x * y - y * x := by
  have h := QBP.Foundations.DeltaLandscape.commutator_sub_central r y x
  have h2 := congrArg (fun z : CDAlg R n => -z) h
  simpa only [neg_sub] using h2

/-- The CD commutator only sees the imaginary parts:
    `[cdLo s, cdHi s] = [Im (cdLo s), Im (cdHi s)]`. -/
theorem comm_eq_imPart (s : CDAlg ℝ 4) :
    comm s = imPart (cdLo s) * imPart (cdHi s) - imPart (cdHi s) * imPart (cdLo s) := by
  rw [comm, imPart_def, imPart_def,
    QBP.Foundations.DeltaLandscape.commutator_sub_central, commutator_sub_central_left]

/-- **P1 — the closed form of the landscape potential.**  For *every* sedenion
    `s` (no imaginarity hypothesis),

      `V(s) = 4·( N(Im a)·N(Im b) − ⟪Im a, Im b⟫² )`,  `a = cdLo s`, `b = cdHi s`,

    i.e. `4` times the Gram determinant of the imaginary parts of the two
    Cayley–Dickson components.  Equivalently `V(s) = ‖2·(Im a × Im b)‖²`.
    This is the confirmer's keystone (§7 P1); `V ≤ N²`, the equality locus and
    the frozen-locus theorem all follow from it. -/
theorem potential_eq_cross (s : CDAlg ℝ 4) :
    Hosting.potential s
      = 4 * (N (imPart (cdLo s)) * N (imPart (cdHi s))
             - (bil (imPart (cdLo s)) (imPart (cdHi s))) ^ 2) := by
  rw [potential_eq_N_comm, comm_eq_imPart]
  exact QBP.Foundations.DeltaLandscape.octonion_commutator_norm _ _
    (imPart_coord_zero _) (imPart_coord_zero _)

/-- **P2 — the sharp global bound `V ≤ N²`.**  Cauchy–Schwarz on the Gram
    determinant (drop `−⟪Im a, Im b⟫² ≤ 0`), then AM–GM `4uv ≤ (u+v)²`, then
    `N(Im a) + N(Im b) ≤ N a + N b = N s` (`N_split`).  Holds on all of
    `CDAlg ℝ 4`, not only on `StateSphere`. -/
theorem potential_le_normForm_sq (s : CDAlg ℝ 4) : Hosting.potential s ≤ (N s) ^ 2 := by
  have hu : N (imPart (cdLo s)) ≤ N (cdLo s) := N_imPart_le _
  have hv : N (imPart (cdHi s)) ≤ N (cdHi s) := N_imPart_le _
  have hu0 : 0 ≤ N (imPart (cdLo s)) := alt_N_nonneg _
  have hv0 : 0 ≤ N (imPart (cdHi s)) := alt_N_nonneg _
  have hsplit : N s = N (cdLo s) + N (cdHi s) :=
    QBP.Foundations.NoAutonomousDynamics.N_split s
  have hle : N (imPart (cdLo s)) + N (imPart (cdHi s)) ≤ N s := by rw [hsplit]; linarith
  have h0 : (0 : ℝ) ≤ N (imPart (cdLo s)) + N (imPart (cdHi s)) := by linarith
  have h1 : 4 * (N (imPart (cdLo s)) * N (imPart (cdHi s)))
      ≤ (N (imPart (cdLo s)) + N (imPart (cdHi s))) ^ 2 := by
    nlinarith [sq_nonneg (N (imPart (cdLo s)) - N (imPart (cdHi s)))]
  have h2 : (N (imPart (cdLo s)) + N (imPart (cdHi s))) ^ 2 ≤ (N s) ^ 2 := by
    nlinarith [hle, h0]
  have h3 : (0 : ℝ) ≤ (bil (imPart (cdLo s)) (imPart (cdHi s))) ^ 2 := sq_nonneg _
  rw [potential_eq_cross]
  linarith

/-! ## 13. Homogeneity of `V` -/

/-- `[·,·]` is homogeneous of degree 2: `C (r·s) = r²·C s`. -/
theorem comm_smul (r : ℝ) (s : CDAlg ℝ 4) : comm (r • s) = (r ^ 2) • comm s := by
  simp only [comm, cdLo_smul, cdHi_smul, mul_smul_left, mul_smul_right, smul_smul]
  module

/-- `V` is homogeneous of degree 4: `V(r·s) = r⁴·V(s)`. -/
theorem potential_smul (r : ℝ) (s : CDAlg ℝ 4) :
    Hosting.potential (r • s) = r ^ 4 * Hosting.potential s := by
  rw [potential_eq_N_comm, potential_eq_N_comm, comm_smul,
    QBP.Foundations.NoAutonomousDynamics.N_smul]
  ring

/-- `secVar` is linear in its first (base-point) argument. -/
theorem secVar_smul_left (r : ℝ) (s v : CDAlg ℝ 4) :
    secVar (r • s) v = r • secVar s v := by
  simp only [secVar, cdLo_smul, cdHi_smul, mul_smul_left, mul_smul_right]
  module

/-! ## 14. P3 — `V` is ANTITONE along the flow (not merely `deriv ≤ 0`)

`potential_nonincreasing_along_flow` (§6) is a **pointwise** statement: the
derivative of `V ∘ γ` at one time `t` is `≤ 0`.  Every locus-avoidance argument
needs the *monotone* form on an interval.  This is the confirmer's P3. -/

/-- **P3 — the potential is antitone along any integral curve on the state
    sphere.**  For `γ` continuous on `[a,b]`, an integral curve of `F` on
    `(a,b)`, staying on `StateSphere`: `t ↦ V(γ t)` is antitone on `[a,b]`. -/
theorem potential_antitone_along_flow {a b : ℝ} {γ : ℝ → CDAlg ℝ 4}
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : ∀ t ∈ Set.Icc a b, γ t ∈ Hosting.StateSphere) :
    AntitoneOn (fun t => Hosting.potential (γ t)) (Set.Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
  · exact ((contDiff_potential (k := 1)).continuous).comp_continuousOn hcont
  · rw [interior_Icc]
    intro t ht
    exact ((hasDerivAt_potential_along_flow (hd t ht)
      (hmem t (Set.Ioo_subset_Icc_self ht))).differentiableAt).differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_potential_along_flow (hd t ht)
      (hmem t (Set.Ioo_subset_Icc_self ht))).deriv]
    exact neg_nonpos.mpr (alt_N_nonneg _)

/-! ## 15. P4 — an IN-FLIGHT witness with `F ≠ 0`

The §10 witness `e₁ + e₁₀` is unusable for non-triviality of the *dynamics*:
it is one of the 42 rank-2 zero divisors, it sits on the argmax locus `{V = N²}`,
and once normalised it is a **rest point** (`F = 0`).  The confirmer measured
`‖F‖ = 0` there to `6.3e-16` and supplied a usable replacement,
`(e₁ + e₂ + e₉)/√3`, with `V/N² = 4/9` and `‖F‖ = 1.9876`.  In Cayley–Dickson
pair coordinates that is `(e₁ + e₂, e₁)`.  The proof does not compute `F`: it
pairs `F` against the tangent direction `e₁₀ = (0, e₂)` and uses
`⟪F s, v⟫ = −⟪∇V s, v⟫ = −2⟪C s, secVar s v⟫` for tangent imaginary `v`. -/

/-- `⟪x, 0⟫ = 0`. -/
theorem bil_zero_right (x : CDAlg ℝ n) : bil x 0 = 0 := by
  simp only [bil_def, zero_coord, mul_zero]
  exact Finset.sum_const_zero

/-- `⟪0, y⟫ = 0`. -/
theorem bil_zero_left (y : CDAlg ℝ n) : bil 0 y = 0 := by
  rw [NormForm.bil_symm]; exact bil_zero_right y

/-- **Tangential test for the rule field.**  If `v` is orthogonal to `s` and
    imaginary, then `⟪F s, v⟫ = −⟪∇V s, v⟫`: the two correction terms in the
    definition of `F` are orthogonal to `v`. -/
theorem bil_ruleField_tangent {s v : CDAlg ℝ 4} (hsv : bil s v = 0) (hv : v.coord 0 = 0) :
    bil (ruleField s) v = - bil (gradV s) v := by
  rw [ruleField, bil_neg_left, bil_sub_left, bil_sub_left, bil_smul_left, bil_smul_left,
    hsv, bil_one_left, hv]
  ring

/-- The in-flight witness `(e₁ + e₂, e₁)` = `e₁ + e₂ + e₉` (unnormalised). -/
noncomputable def flowWitness : CDAlg ℝ 4 := loOf (e 1 + e 2) + hiOf (e 1)

/-- The tangent direction `(0, e₂)` = `e₁₀` used to detect `F ≠ 0`. -/
noncomputable def flowWitnessDir : CDAlg ℝ 4 := hiOf (e 2)

theorem cdLo_flowWitness : cdLo flowWitness = e 1 + e 2 := by
  rw [flowWitness, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]

theorem cdHi_flowWitness : cdHi flowWitness = e 1 := by
  rw [flowWitness, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]

theorem cdLo_flowWitnessDir : cdLo flowWitnessDir = 0 := by
  rw [flowWitnessDir, cdLo_hiOf]

theorem cdHi_flowWitnessDir : cdHi flowWitnessDir = e 2 := by
  rw [flowWitnessDir, cdHi_hiOf]

/-- `C(flowWitness) = −2·μ·e₃` with `μ = mulCoeff 3 1 2 = ±1`. -/
theorem comm_flowWitness :
    comm flowWitness = ((-2 * (mulCoeff 3 1 2 : ℤ) : ℤ) : ℝ) • (e 3 : CDAlg ℝ 3) := by
  have h21 : mulCoeff 3 2 1 = - mulCoeff 3 1 2 := by decide
  have h11 : (1 ^^^ 1 : Fin (2 ^ 3)) = 0 := by decide
  have hx1 : (1 ^^^ 2 : Fin (2 ^ 3)) = 3 := by decide
  have hx2 : (2 ^^^ 1 : Fin (2 ^ 3)) = 3 := by decide
  rw [comm, cdLo_flowWitness, cdHi_flowWitness, mul_add_left, mul_add_right,
    e_mul_e, e_mul_e, e_mul_e, h11, hx1, hx2, h21]
  push_cast
  module

/-- `secVar(flowWitness, e₁₀) = 2·μ·e₃`. -/
theorem secVar_flowWitness :
    secVar flowWitness flowWitnessDir
      = ((2 * (mulCoeff 3 1 2 : ℤ) : ℤ) : ℝ) • (e 3 : CDAlg ℝ 3) := by
  have h21 : mulCoeff 3 2 1 = - mulCoeff 3 1 2 := by decide
  have h22 : (2 ^^^ 2 : Fin (2 ^ 3)) = 0 := by decide
  have hx1 : (1 ^^^ 2 : Fin (2 ^ 3)) = 3 := by decide
  have hx2 : (2 ^^^ 1 : Fin (2 ^ 3)) = 3 := by decide
  rw [secVar, cdLo_flowWitness, cdHi_flowWitness, cdLo_flowWitnessDir, cdHi_flowWitnessDir,
    alt_zero_mul, alt_mul_zero, sub_zero, add_zero, mul_add_left, mul_add_right,
    e_mul_e, e_mul_e, e_mul_e, h22, hx1, hx2, h21]
  push_cast
  module

/-- The pairing that certifies `F ≠ 0`: `⟪C w, secVar w v⟫ = −4 ≠ 0`. -/
theorem bil_comm_secVar_flowWitness :
    bil (comm flowWitness) (secVar flowWitness flowWitnessDir) = -4 := by
  have hsq : (mulCoeff 3 1 2 : ℤ) * (mulCoeff 3 1 2 : ℤ) = 1 := by decide
  have hcast : ((mulCoeff 3 1 2 : ℤ) : ℝ) * ((mulCoeff 3 1 2 : ℤ) : ℝ) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsq
  rw [comm_flowWitness, secVar_flowWitness, bil_smul_left, bil_smul_right, bil_e, if_pos rfl]
  push_cast
  linear_combination (-4 : ℝ) * hcast

theorem normForm_flowWitness : N flowWitness = 3 := by
  have h12 : bil (e 1 : CDAlg ℝ 3) (e 2) = 0 := by rw [bil_e, if_neg (by decide)]
  rw [QBP.Foundations.NoAutonomousDynamics.N_split, cdLo_flowWitness, cdHi_flowWitness,
    alt_N_add, h12, N_e, N_e]
  norm_num

theorem flowWitness_coord_zero : flowWitness.coord 0 = 0 := by
  have h : (cdLo flowWitness).coord 0 = flowWitness.coord 0 := by rw [cdLo_coord, loIdx_zero]
  rw [← h, cdLo_flowWitness, add_coord, e_coord, e_coord, if_neg (by decide),
    if_neg (by decide)]
  ring

theorem flowWitness_ne_zero : flowWitness ≠ 0 := by
  intro h
  have := normForm_flowWitness
  rw [h] at this
  rw [(alt_N_eq_zero_iff (0 : CDAlg ℝ 4)).mpr rfl] at this
  norm_num at this

theorem flowWitnessDir_coord_zero : flowWitnessDir.coord 0 = 0 := by
  have h : (cdLo flowWitnessDir).coord 0 = flowWitnessDir.coord 0 := by
    rw [cdLo_coord, loIdx_zero]
  rw [← h, cdLo_flowWitnessDir, zero_coord]

theorem bil_flowWitness_dir : bil flowWitness flowWitnessDir = 0 := by
  rw [bil_split, cdLo_flowWitness, cdHi_flowWitness, cdLo_flowWitnessDir, cdHi_flowWitnessDir,
    bil_zero_right, bil_e, if_neg (by decide)]
  ring

/-- **P4 — the dynamics is not trivial: some state-sphere point moves.**
    `∃ s ∈ StateSphere, F s ≠ 0`, witnessed by `(e₁ + e₂ + e₉)/√3`.  Note this is
    NOT deducible from `exists_gradV_ne_zero`: that theorem's witness `e₁ + e₁₀`
    is a zero divisor and, normalised, a rest point. -/
theorem exists_ruleField_ne_zero : ∃ s ∈ Hosting.StateSphere, ruleField s ≠ 0 := by
  refine ⟨Hosting.normalise flowWitness,
    Hosting.normalise_mem_stateSphere flowWitness_coord_zero flowWitness_ne_zero, ?_⟩
  set r : ℝ := (Real.sqrt (N flowWitness))⁻¹ with hr
  have hrpos : 0 < r := by
    rw [hr, normForm_flowWitness]
    positivity
  have hnorm : Hosting.normalise flowWitness = r • flowWitness := rfl
  have hsv : bil (r • flowWitness) flowWitnessDir = 0 := by
    rw [bil_smul_left, bil_flowWitness_dir]; ring
  have hgrad : bil (gradV (r • flowWitness)) flowWitnessDir = -8 * r ^ 3 := by
    rw [bil_gradV, comm_smul, secVar_smul_left, bil_smul_left, bil_smul_right,
      bil_comm_secVar_flowWitness]
    ring
  have hkey : bil (ruleField (r • flowWitness)) flowWitnessDir = 8 * r ^ 3 := by
    rw [bil_ruleField_tangent hsv flowWitnessDir_coord_zero, hgrad]
    ring
  intro hzero
  rw [← hnorm, hzero, bil_zero_left] at hkey
  have : (0 : ℝ) < 8 * r ^ 3 := by positivity
  linarith

/-! ## 16. P7/P6 — the argmax of `V` on the sphere is `1`, and it is FROZEN -/

theorem isClosed_stateSphere : IsClosed Hosting.StateSphere := by
  have h1 : Continuous fun s : CDAlg ℝ 4 => s.coord 0 := (coordCLM 4 0).continuous
  have h2 : Continuous fun s : CDAlg ℝ 4 => N s :=
    (contDiff_normForm (k := 1) (contDiff_id (𝕜 := ℝ) (E := CDAlg ℝ 4))).continuous
  exact (isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const)

theorem isCompact_stateSphere : IsCompact Hosting.StateSphere :=
  IsCompact.of_isClosed_subset (isCompact_closedBall (0 : CDAlg ℝ 4) 1)
    isClosed_stateSphere stateSphere_subset_closedBall

theorem normForm_witness : N witness = 2 := by
  have hlo : cdLo witness = e 1 := by rw [witness, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]
  have hhi : cdHi witness = e 2 := by rw [witness, cdHi_add, cdHi_loOf, cdHi_hiOf, zero_add]
  rw [QBP.Foundations.NoAutonomousDynamics.N_split, hlo, hhi, N_e, N_e]
  norm_num

theorem witness_coord_zero : witness.coord 0 = 0 := by
  have hlo : cdLo witness = e 1 := by rw [witness, cdLo_add, cdLo_loOf, cdLo_hiOf, add_zero]
  have h : (cdLo witness).coord 0 = witness.coord 0 := by rw [cdLo_coord, loIdx_zero]
  rw [← h, hlo, e_coord, if_neg (by decide)]

theorem witness_ne_zero : witness ≠ 0 := by
  intro h
  have h2 := normForm_witness
  rw [h, (alt_N_eq_zero_iff (0 : CDAlg ℝ 4)).mpr rfl] at h2
  norm_num at h2

/-- **The normalised zero divisor `(e₁ + e₁₀)/√2` attains `V = 1`.** -/
theorem potential_normalise_witness : Hosting.potential (Hosting.normalise witness) = 1 := by
  rw [Hosting.normalise_def, potential_smul, potential_witness, normForm_witness, inv_pow,
    show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem stateSphere_nonempty : Hosting.StateSphere.Nonempty :=
  ⟨Hosting.normalise witness,
    Hosting.normalise_mem_stateSphere witness_coord_zero witness_ne_zero⟩

/-- **P7 — `V` attains its maximum on `StateSphere`, and that maximum is `1`.**
    Compactness (`StateSphere` is closed and bounded in a finite-dimensional
    space) gives attainment; `V ≤ N² = 1` (P2) bounds it above; the normalised
    zero divisor `(e₁ + e₁₀)/√2` attains `1`, so the bound is sharp. -/
theorem exists_isMaxOn_potential_stateSphere :
    ∃ s ∈ Hosting.StateSphere,
      IsMaxOn Hosting.potential Hosting.StateSphere s ∧ Hosting.potential s = 1 := by
  obtain ⟨s, hs, hmax⟩ := isCompact_stateSphere.exists_isMaxOn stateSphere_nonempty
    ((contDiff_potential (k := 1)).continuous).continuousOn
  refine ⟨s, hs, hmax, le_antisymm ?_ ?_⟩
  · have h := potential_le_normForm_sq s
    rw [hs.2] at h
    simpa using h
  · have hz : Hosting.potential (Hosting.normalise witness) ≤ Hosting.potential s :=
      hmax (Hosting.normalise_mem_stateSphere witness_coord_zero witness_ne_zero)
    rwa [potential_normalise_witness] at hz

/-- **The tangential gradient vanishes at a point of `{V = 1} ∩ StateSphere`.**
    The trick avoids Lagrange multipliers: by P2 the function
    `h(t) = V(s + t·v) − N(s + t·v)²` is `≤ 0` *everywhere*, and `h(0) = 0` when
    `V(s) = N(s)² = 1`.  So `0` is a global max of `h`; and if `⟪s,v⟫ = 0` the
    `N²` term has vanishing derivative at `0`, so `h'(0) = ⟪∇V s, v⟫ = 0`. -/
theorem bil_gradV_eq_zero_of_potential_eq_one {s v : CDAlg ℝ 4}
    (hs : s ∈ Hosting.StateSphere) (h1 : Hosting.potential s = 1) (hv : bil s v = 0) :
    bil (gradV s) v = 0 := by
  have hN : ∀ t : ℝ, N (s + t • v) = 1 + t ^ 2 * N v := by
    intro t
    rw [alt_N_add, bil_smul_right, hv, QBP.Foundations.NoAutonomousDynamics.N_smul, hs.2]
    ring
  have hd1 : HasDerivAt (fun t : ℝ => Hosting.potential (s + t • v))
      (2 * bil (comm s) (secVar s v)) 0 := hasDerivAt_potential_ray s v
  have hd2 : HasDerivAt (fun t : ℝ => (N (s + t • v)) ^ 2) 0 0 := by
    have he : (fun t : ℝ => (N (s + t • v)) ^ 2) = fun t : ℝ => (1 + t ^ 2 * N v) ^ 2 := by
      funext t; rw [hN t]
    rw [he]
    have hin : HasDerivAt (fun t : ℝ => 1 + t ^ 2 * N v) 0 0 := by
      simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (N v)).const_add (1 : ℝ)
    simpa using hin.pow 2
  have hdf : HasDerivAt (fun t : ℝ => Hosting.potential (s + t • v) - (N (s + t • v)) ^ 2)
      (2 * bil (comm s) (secVar s v) - 0) 0 := hd1.sub hd2
  have hf0 : Hosting.potential (s + (0 : ℝ) • v) - (N (s + (0 : ℝ) • v)) ^ 2 = 0 := by
    rw [zero_smul, add_zero, h1, hs.2]; norm_num
  have hlm : IsLocalMax (fun t : ℝ => Hosting.potential (s + t • v) - (N (s + t • v)) ^ 2) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h := potential_le_normForm_sq (s + t • v)
    simp only [hf0]
    linarith
  have hzero := hlm.hasDerivAt_eq_zero hdf
  rw [bil_gradV]
  linarith

/-- **P6 — the frozen-locus theorem.**  Every state-sphere point at which `V`
    attains its maximum value `1` is a REST POINT of the rule: `F s = 0`.
    Since every zero divisor on the sphere has `V = 1`, the zero-divisor locus is
    frozen — it cannot be entered (`V` is antitone, P3) and cannot be left. -/
theorem ruleField_eq_zero_of_potential_eq_one {s : CDAlg ℝ 4}
    (hs : s ∈ Hosting.StateSphere) (h1 : Hosting.potential s = 1) : ruleField s = 0 := by
  have hv : bil s (ruleField s) = 0 := by
    rw [NormForm.bil_symm]; exact ruleField_bil_self hs
  have h := bil_gradV_eq_zero_of_potential_eq_one hs h1 hv
  rw [bil_gradV_ruleField hs] at h
  have hN : N (ruleField s) = 0 := by linarith
  exact (alt_N_eq_zero_iff _).mp hN

/-! ## 17. P8 — the ω-limit set of a sub-maximal forward orbit avoids `{V = 1}` -/

/-- **The tail bound.**  Along a forward integral curve on the state sphere,
    `V(γ t) ≤ V(γ 0)` for every `t ≥ 0` (P3 applied on `[0,t]`). -/
theorem potential_le_initial_along_flow {γ : ℝ → CDAlg ℝ 4}
    (hcont : ContinuousOn γ (Set.Ici 0))
    (hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt γ (ruleField (γ t)) t)
    (hmem : ∀ t ∈ Set.Ici (0 : ℝ), γ t ∈ Hosting.StateSphere) :
    ∀ t ∈ Set.Ici (0 : ℝ), Hosting.potential (γ t) ≤ Hosting.potential (γ 0) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht
  have hanti := potential_antitone_along_flow (a := 0) (b := t)
    (hcont.mono (Set.Icc_subset_Ici_self))
    (fun u hu => hd u (lt_of_le_of_lt (le_refl 0) hu.1))
    (fun u hu => hmem u (le_trans (le_refl 0) hu.1))
  exact hanti (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0

/-- **The closure form.**  Every limit point of the forward orbit inherits the
    tail bound, because `{x | V x ≤ c}` is closed. -/
theorem potential_le_initial_of_mem_closure {γ : ℝ → CDAlg ℝ 4}
    (hcont : ContinuousOn γ (Set.Ici 0))
    (hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt γ (ruleField (γ t)) t)
    (hmem : ∀ t ∈ Set.Ici (0 : ℝ), γ t ∈ Hosting.StateSphere)
    {p : CDAlg ℝ 4} (hp : p ∈ closure (γ '' Set.Ici 0)) :
    Hosting.potential p ≤ Hosting.potential (γ 0) := by
  have hsub : γ '' Set.Ici 0 ⊆ {x | Hosting.potential x ≤ Hosting.potential (γ 0)} := by
    rintro _ ⟨t, ht, rfl⟩
    exact potential_le_initial_along_flow hcont hd hmem t ht
  have hclosed : IsClosed {x : CDAlg ℝ 4 | Hosting.potential x ≤ Hosting.potential (γ 0)} :=
    isClosed_le ((contDiff_potential (k := 1)).continuous) continuous_const
  exact closure_minimal hsub hclosed hp

/-- **P8 — locus avoidance.**  If a forward integral curve on the state sphere
    starts strictly below the maximum (`V(γ 0) < 1`), then every point of its
    ω-limit set also has `V < 1` — in particular the ω-limit set misses the
    zero-divisor locus `{V = 1}` (frozen by P6).

    `omegaLimit Filter.atTop (fun t _ => γ t) Set.univ` is Mathlib's ω-limit of
    the single orbit: `⋂ u ∈ atTop, closure (γ '' u)`. -/
theorem omega_avoids_locus {γ : ℝ → CDAlg ℝ 4}
    (hcont : ContinuousOn γ (Set.Ici 0))
    (hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt γ (ruleField (γ t)) t)
    (hmem : ∀ t ∈ Set.Ici (0 : ℝ), γ t ∈ Hosting.StateSphere)
    (h0 : Hosting.potential (γ 0) < 1)
    {p : CDAlg ℝ 4}
    (hp : p ∈ omegaLimit Filter.atTop (fun (_t : ℝ) (_ : Unit) => γ _t) Set.univ) :
    Hosting.potential p < 1 := by
  rw [omegaLimit_def] at hp
  have hmem' := Set.mem_iInter₂.mp hp (Set.Ici (0 : ℝ)) (Filter.Ici_mem_atTop 0)
  have himg : Set.image2 (fun (_t : ℝ) (_ : Unit) => γ _t) (Set.Ici 0) Set.univ
      = γ '' Set.Ici 0 := by
    ext y
    simp only [Set.mem_image2, Set.mem_univ, true_and, Set.mem_image, exists_const]
  rw [himg] at hmem'
  exact lt_of_le_of_lt (potential_le_initial_of_mem_closure hcont hd hmem hmem') h0

/-- Every point of the ω-limit set of a sub-maximal forward orbit is a
    non-maximiser; combined with P6 (`V = 1 ⇒ F = 0`) this is the precise
    statement the #635 conversation's "frozen locus" argument needs. -/
theorem omega_ne_of_potential_eq_one {γ : ℝ → CDAlg ℝ 4}
    (hcont : ContinuousOn γ (Set.Ici 0))
    (hd : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt γ (ruleField (γ t)) t)
    (hmem : ∀ t ∈ Set.Ici (0 : ℝ), γ t ∈ Hosting.StateSphere)
    (h0 : Hosting.potential (γ 0) < 1)
    {p q : CDAlg ℝ 4}
    (hp : p ∈ omegaLimit Filter.atTop (fun (_t : ℝ) (_ : Unit) => γ _t) Set.univ)
    (hq : Hosting.potential q = 1) : p ≠ q := by
  intro h
  have := omega_avoids_locus hcont hd hmem h0 hp
  rw [h, hq] at this
  exact lt_irrefl 1 this

/-! ## 18. P9 — a crystal is not a zero divisor

The route is the **norm defect of left multiplication**.  Writing `x = (a,b)`,
`y = (c,d)` in Cayley–Dickson pairs and using the doubling formula
(`NoAutonomousDynamics.cdLo_mul`/`cdHi_mul`) together with 𝕆's norm composition:

    N(x·y) = N x · N y − 2·⟪a, [d̄, b, c̄]⟫       (`normForm_mul_eq`)

where `[·,·,·] = assoc` is the octonion associator.  At a **crystal** (`[a,b] = 0`)
the imaginary part of `b` is a real multiple of `a` (equality in Cauchy–Schwarz,
read off from `potential_eq_cross`), the real part of `b` is associator-inert, and
the associator is alternating — so the defect vanishes identically and `L_x` is a
similarity of the norm form, hence injective.

**FLAG-P5-open.**  The confirmer's P5 (`s ≠ 0 → V s = (N s)² → s` is a zero
divisor) is **NOT** proved here.  The route hinted in the verdict,
`N(s·x) ≥ (N s − √(V s))·N x`, degenerates at `V s = (N s)²` to `N(s·x) ≥ 0`,
which is vacuous; the `⇒` direction needs an *exhibited* kernel vector (or the
4/8/4 spectral identity of `L_sᵀL_s`, an XL-cost object).  What IS proved here is
the P9-relevant consequence of the same defect identity, in the opposite regime
(`V = 0`).  Nothing below may be read as establishing P5. -/

theorem assoc_def (x y z : CDAlg ℝ n) : assoc x y z = (x * y) * z - x * (y * z) := rfl

/-- `⟪x, −y⟫ = −⟪x, y⟫`. -/
theorem bil_neg_right (x y : CDAlg ℝ n) : bil x (-y) = - bil x y := by
  rw [NormForm.bil_symm, bil_neg_left, NormForm.bil_symm]

/-- Polarization of `N` over a difference. -/
theorem N_sub (x y : CDAlg ℝ n) : N (x - y) = N x - 2 * bil x y + N y := by
  have h : x - y = x + (-1 : ℝ) • y := by module
  rw [h, alt_N_add, bil_smul_right, QBP.Foundations.NoAutonomousDynamics.N_smul]
  ring

theorem imPart_eq_self {x : CDAlg ℝ n} (hx : x.coord 0 = 0) : imPart x = x := by
  rw [imPart_def, hx, zero_smul, sub_zero]

theorem conj_eq_neg_of_coord_zero {x : CDAlg ℝ n} (hx : x.coord 0 = 0) : conj x = -x := by
  rw [conj_eq_sub, hx, mul_zero, zero_smul, zero_sub]

theorem conj_conj_cd (x : CDAlg ℝ n) : conj (conj x) = x := by
  ext i
  by_cases h : i.val = 0 <;> simp [h]

/-- `1` is inert in the middle slot of the associator. -/
theorem assoc_mid_one (x z : CDAlg ℝ n) : assoc x (1 : CDAlg ℝ n) z = 0 := by
  rw [assoc_def, cd_mul_one, cd_one_mul, sub_self]

theorem assoc_neg_left (x y z : CDAlg ℝ n) : assoc (-x) y z = - assoc x y z := by
  have h : (-x : CDAlg ℝ n) = (-1 : ℝ) • x := by module
  rw [h, assoc_trilinear.smul_left]
  module

/-- **Adjoint transfer for the octonion associator.**
    `⟪[x,y,z], w⟫ = −⟪y, [x̄, w, z̄]⟫`.  Pure consequence of the two adjoint
    identities `⟪x·p, q⟫ = ⟪p, x̄·q⟫`, `⟪p·x, q⟫ = ⟪p, q·x̄⟫` (§2). -/
theorem bil_assoc_transfer (x y z w : CDAlg ℝ 3) :
    bil (assoc x y z) w = - bil y (assoc (conj x) w (conj z)) := by
  rw [assoc_def, assoc_def, bil_sub_left, bil_sub_right,
    bil_mul_right_adj z (x * y) w, bil_mul_left_adj x y (w * conj z),
    bil_mul_left_adj x (y * z) w, bil_mul_right_adj z y (conj x * w)]
  ring

/-- **The middle-slot contraction vanishes for an imaginary vector.**
    `⟪a, [u, a, v]⟫ = 0` whenever `a₀ = 0`.  Proof: swap the first two slots
    (polarized left alternativity), transfer the adjoint, use `ā = −a` and
    `[a,a,·] = 0`. -/
theorem bil_assoc_mid_self_of_imaginary {a : CDAlg ℝ 3} (ha : a.coord 0 = 0)
    (u v : CDAlg ℝ 3) : bil a (assoc u a v) = 0 := by
  have hswap : assoc u a v = - assoc a u v := by
    rw [eq_neg_iff_add_eq_zero]; exact octonion_left_alternative_polarized u a v
  rw [hswap, bil_neg_right, NormForm.bil_symm a (assoc a u v),
    bil_assoc_transfer a u v a, conj_eq_neg_of_coord_zero ha, assoc_neg_left,
    bil_neg_right, assoc_diag_left, bil_zero_right]
  ring

/-- **The norm defect of left multiplication on 𝕊.**  For `x = (a,b)`, `y = (c,d)`:

      `N(x·y) = N x · N y − 2·⟪a, [d̄, b, c̄]⟫`.

    The whole failure of the composition law on the sedenions sits in that one
    associator pairing. -/
theorem normForm_mul_eq (x y : CDAlg ℝ 4) :
    N (x * y) = N x * N y
      - 2 * bil (cdLo x) (assoc (conj (cdHi y)) (cdHi x) (conj (cdLo y))) := by
  have hcomp := QBP.Foundations.NormForm.octonion_norm_form_composition
  have h1 : N (cdLo (x * y))
      = N (cdLo x) * N (cdLo y) + N (cdHi y) * N (cdHi x)
        - 2 * bil (cdLo x * cdLo y) (conj (cdHi y) * cdHi x) := by
    rw [QBP.Foundations.NoAutonomousDynamics.cdLo_mul, N_sub, hcomp, hcomp,
      QBP.Foundations.NoAutonomousDynamics.N_conj]
    ring
  have h2 : N (cdHi (x * y))
      = N (cdHi y) * N (cdLo x) + N (cdHi x) * N (cdLo y)
        + 2 * bil (cdHi y * cdLo x) (cdHi x * conj (cdLo y)) := by
    rw [QBP.Foundations.NoAutonomousDynamics.cdHi_mul, alt_N_add, hcomp, hcomp,
      QBP.Foundations.NoAutonomousDynamics.N_conj]
    ring
  have hA : bil (cdHi y * cdLo x) (cdHi x * conj (cdLo y))
      = bil (cdLo x) (conj (cdHi y) * (cdHi x * conj (cdLo y))) :=
    bil_mul_left_adj (cdHi y) (cdLo x) (cdHi x * conj (cdLo y))
  have hB : bil (cdLo x * cdLo y) (conj (cdHi y) * cdHi x)
      = bil (cdLo x) ((conj (cdHi y) * cdHi x) * conj (cdLo y)) :=
    bil_mul_right_adj (cdLo y) (cdLo x) (conj (cdHi y) * cdHi x)
  have hassoc : bil (cdLo x) (assoc (conj (cdHi y)) (cdHi x) (conj (cdLo y)))
      = bil (cdLo x) ((conj (cdHi y) * cdHi x) * conj (cdLo y))
        - bil (cdLo x) (conj (cdHi y) * (cdHi x * conj (cdLo y))) := by
    rw [assoc_def, bil_sub_right]
  rw [QBP.Foundations.NoAutonomousDynamics.N_split (x * y), h1, h2, hA, hB, hassoc,
    QBP.Foundations.NoAutonomousDynamics.N_split x,
    QBP.Foundations.NoAutonomousDynamics.N_split y]
  ring

/-- **At a crystal the defect vanishes.**  `⟪a, [u, b, v]⟫ = 0` for every `u, v`,
    because `Im b` is a real multiple of `a` (equality in Cauchy–Schwarz, from
    `V(s) = 0` and `potential_eq_cross`) and the associator is alternating. -/
theorem bil_cdLo_assoc_eq_zero_of_isVacuum {s : CDAlg ℝ 4} (hv : IsVacuum s)
    (u v : CDAlg ℝ 3) : bil (cdLo s) (assoc u (cdHi s) v) = 0 := by
  have ha0 : (cdLo s).coord 0 = 0 := cdLo_coord_zero hv.1
  by_cases hA : cdLo s = 0
  · rw [hA, bil_zero_left]
  · have hNa : N (cdLo s) ≠ 0 := fun h => hA ((alt_N_eq_zero_iff _).mp h)
    have hp0 : Hosting.potential s = 0 := (Hosting.potential_eq_zero_iff_isVacuum hv.1).mpr hv
    have hcross := potential_eq_cross s
    rw [hp0, imPart_eq_self ha0] at hcross
    have hAP : N (cdLo s) * N (imPart (cdHi s))
        = (bil (cdLo s) (imPart (cdHi s))) ^ 2 := by linarith [hcross]
    set lam : ℝ := bil (cdLo s) (imPart (cdHi s)) / N (cdLo s) with hlam
    have hlamA : lam * N (cdLo s) = bil (cdLo s) (imPart (cdHi s)) := by
      rw [hlam]; field_simp
    have hlamQ : lam * bil (cdLo s) (imPart (cdHi s)) = N (imPart (cdHi s)) := by
      rw [hlam, div_mul_eq_mul_div, div_eq_iff hNa]
      linarith [hAP]
    have hexp : N (imPart (cdHi s) - lam • cdLo s)
        = N (imPart (cdHi s)) - 2 * (lam * bil (cdLo s) (imPart (cdHi s)))
          + lam ^ 2 * N (cdLo s) := by
      rw [N_sub, bil_smul_right, QBP.Foundations.NoAutonomousDynamics.N_smul,
        NormForm.bil_symm (imPart (cdHi s)) (cdLo s)]
    have hzero : N (imPart (cdHi s) - lam • cdLo s) = 0 := by
      rw [hexp, show lam ^ 2 * N (cdLo s) = lam * (lam * N (cdLo s)) by ring, hlamA, hlamQ]
      ring
    have hb : imPart (cdHi s) = lam • cdLo s := by
      have h := (alt_N_eq_zero_iff _).mp hzero
      rwa [sub_eq_zero] at h
    have hbb : cdHi s = lam • cdLo s + ((cdHi s).coord 0) • (1 : CDAlg ℝ 3) := by
      rw [← hb, imPart_def]; abel
    rw [hbb, assoc_trilinear.add_mid, assoc_trilinear.smul_mid, assoc_trilinear.smul_mid,
      assoc_mid_one, smul_zero, add_zero, bil_smul_right,
      bil_assoc_mid_self_of_imaginary ha0]
    ring

/-- **A crystal composes:** `N(s·y) = N s · N y` for every `y`, when `s` is a
    vacuum.  (The confirmer measured `σ_min(L_s) = 1.000000` and kernel dimension
    `0` on 200 random crystals; this is the theorem behind that measurement.) -/
theorem normForm_mul_of_isVacuum {s : CDAlg ℝ 4} (hv : IsVacuum s) (y : CDAlg ℝ 4) :
    N (s * y) = N s * N y := by
  rw [normForm_mul_eq, bil_cdLo_assoc_eq_zero_of_isVacuum hv]
  ring

/-- **P9 — a crystal is not a zero divisor.**  Left multiplication by a non-zero
    vacuum is injective on all of 𝕊.  No information is lost by multiplying by a
    crystal. -/
theorem crystal_not_zeroDivisor {s : CDAlg ℝ 4} (hv : IsVacuum s) (hs : s ≠ 0) :
    Function.Injective (fun y : CDAlg ℝ 4 => s * y) := by
  have hNs : N s ≠ 0 := fun h => hs ((alt_N_eq_zero_iff _).mp h)
  intro y₁ y₂ h
  simp only at h
  have hdist : s * (y₁ - y₂) = s * y₁ - s * y₂ := by
    have hy : y₁ - y₂ = y₁ + (-1 : ℝ) • y₂ := by module
    rw [hy, mul_add_right, mul_smul_right]
    module
  have h0 : s * (y₁ - y₂) = 0 := by rw [hdist, h, sub_self]
  have hN : N s * N (y₁ - y₂) = 0 := by
    rw [← normForm_mul_of_isVacuum hv, h0, (alt_N_eq_zero_iff (0 : CDAlg ℝ 4)).mpr rfl]
  have h1 := (mul_eq_zero.mp hN).resolve_left hNs
  exact sub_eq_zero.mp ((alt_N_eq_zero_iff _).mp h1)

/-- The zero-divisor form of P9: a non-zero crystal annihilates nothing but `0`. -/
theorem crystal_mul_ne_zero {s : CDAlg ℝ 4} (hv : IsVacuum s) (hs : s ≠ 0)
    {y : CDAlg ℝ 4} (hy : y ≠ 0) : s * y ≠ 0 := by
  intro h
  have h0 : s * y = s * 0 := by rw [h, alt_mul_zero]
  exact hy (crystal_not_zeroDivisor hv hs h0)

/-! ## 11. Completeness audit (`#print axioms`)

Every declaration introduced by this file.  The gate: only
`{propext, Classical.choice, Quot.sound}` may appear. -/

#print axioms instInnerCD
#print axioms inner_def'
#print axioms instNormedAddCommGroupCD
#print axioms instInnerProductSpaceCD
#print axioms norm_sq_eq_normForm
#print axioms bil_one_right
#print axioms conj_eq_sub
#print axioms octonion_bil_polarized
#print axioms bil_mul_left_adj
#print axioms bil_mul_right_adj
#print axioms bil_sub_left
#print axioms bil_sub_right
#print axioms comm
#print axioms potential_eq_N_comm
#print axioms comm_eq_zero_of_isVacuum
#print axioms comm_along_ray
#print axioms gradV
#print axioms cdLo_gradV
#print axioms cdHi_gradV
#print axioms bil_gradV
#print axioms loOf_zero
#print axioms hiOf_zero
#print axioms gradV_eq_zero_of_isVacuum
#print axioms instFiniteDimensionalCD
#print axioms coordCLE
#print axioms contDiff_cd_iff
#print axioms contDiff_coord
#print axioms contDiff_of_linear
#print axioms contDiff_cdmul
#print axioms contDiff_cdLo
#print axioms contDiff_cdHi
#print axioms conj_add
#print axioms conj_smul
#print axioms contDiff_conj
#print axioms loOf_add
#print axioms loOf_smul
#print axioms hiOf_add
#print axioms hiOf_smul
#print axioms contDiff_loOf
#print axioms contDiff_hiOf
#print axioms contDiff_comm
#print axioms contDiff_normForm
#print axioms contDiff_potential
#print axioms contDiff_gradV
#print axioms N_add3
#print axioms potential_along_ray
#print axioms hasDerivAt_potential_ray
#print axioms differentiable_potential
#print axioms differentiable_gradV
#print axioms fderiv_potential_apply
#print axioms fderiv_potential
#print axioms hasFDerivAt_potential
#print axioms hasGradientAt_potential
#print axioms bil_one_left
#print axioms bil_neg_left
#print axioms bil_self_eq_N
#print axioms ruleField
#print axioms gradV_decomp
#print axioms ruleField_bil_self
#print axioms ruleField_coord_zero
#print axioms ruleField_eq_zero_of_isVacuum
#print axioms ruleField_eq_zero_iff
#print axioms contDiff_ruleField
#print axioms differentiable_ruleField
#print axioms coordCLM
#print axioms hasDerivAt_coord
#print axioms hasDerivAt_coord_zero_along_flow
#print axioms hasDerivAt_normForm_along_flow
#print axioms bil_gradV_ruleField
#print axioms hasDerivAt_potential_along_flow
#print axioms potential_nonincreasing_along_flow
#print axioms norm_eq_one_of_mem_stateSphere
#print axioms stateSphere_subset_closedBall
#print axioms exists_lipschitzOnWith_ruleField
#print axioms exists_lipschitzOnWith_ruleField_stateSphere
#print axioms eulerStep
#print axioms eulerStep_injOn
#print axioms normForm_eulerStep
#print axioms renormStep
#print axioms renormStep_injOn_of_normForm_const
#print axioms flow_unique_of_mem_Icc
#print axioms flow_unique_of_endpoint
#print axioms flow_time_map_injective
#print axioms ruleField_coord_zero_general
#print axioms bil_ruleField_self_general
#print axioms scalar_linear_ode_zero
#print axioms stateSphere_invariant
#print axioms N_e
#print axioms witness
#print axioms comm_witness
#print axioms potential_witness
#print axioms potential_zero
#print axioms exists_gradV_ne_zero

#print axioms imPart
#print axioms imPart_def
#print axioms imPart_coord_zero
#print axioms N_imPart
#print axioms N_imPart_le
#print axioms commutator_sub_central_left
#print axioms comm_eq_imPart
#print axioms potential_eq_cross
#print axioms potential_le_normForm_sq
#print axioms comm_smul
#print axioms potential_smul
#print axioms secVar_smul_left
#print axioms potential_antitone_along_flow
#print axioms bil_zero_right
#print axioms bil_zero_left
#print axioms bil_ruleField_tangent
#print axioms flowWitness
#print axioms flowWitnessDir
#print axioms cdLo_flowWitness
#print axioms cdHi_flowWitness
#print axioms cdLo_flowWitnessDir
#print axioms cdHi_flowWitnessDir
#print axioms comm_flowWitness
#print axioms secVar_flowWitness
#print axioms bil_comm_secVar_flowWitness
#print axioms normForm_flowWitness
#print axioms flowWitness_coord_zero
#print axioms flowWitness_ne_zero
#print axioms flowWitnessDir_coord_zero
#print axioms bil_flowWitness_dir
#print axioms exists_ruleField_ne_zero
#print axioms isClosed_stateSphere
#print axioms isCompact_stateSphere
#print axioms normForm_witness
#print axioms witness_coord_zero
#print axioms witness_ne_zero
#print axioms potential_normalise_witness
#print axioms stateSphere_nonempty
#print axioms exists_isMaxOn_potential_stateSphere
#print axioms bil_gradV_eq_zero_of_potential_eq_one
#print axioms ruleField_eq_zero_of_potential_eq_one
#print axioms potential_le_initial_along_flow
#print axioms potential_le_initial_of_mem_closure
#print axioms omega_avoids_locus
#print axioms omega_ne_of_potential_eq_one

#print axioms assoc_def
#print axioms bil_neg_right
#print axioms N_sub
#print axioms imPart_eq_self
#print axioms conj_eq_neg_of_coord_zero
#print axioms conj_conj_cd
#print axioms assoc_mid_one
#print axioms assoc_neg_left
#print axioms bil_assoc_transfer
#print axioms bil_assoc_mid_self_of_imaginary
#print axioms normForm_mul_eq
#print axioms bil_cdLo_assoc_eq_zero_of_isVacuum
#print axioms normForm_mul_of_isVacuum
#print axioms crystal_not_zeroDivisor
#print axioms crystal_mul_ne_zero

end QBP.Substrate.RuleFlow
