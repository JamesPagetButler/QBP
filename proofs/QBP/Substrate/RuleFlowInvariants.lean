import QBP.Substrate.RuleFlow

/-!
# QBP.Substrate.RuleFlowInvariants — the rule's descent is INTEGRABLE in the Gram invariants (#473 target 6(i))

**Substrate-layer discipline** (beekeeper's lift, 2026-09-07,
#473 `issuecomment-5574256922`).  *What this file hosts:* the closed-form
**integrability** of the rule of `QBP.Substrate.RuleFlow` in the four
`G₂ × O(2)`-invariants of the Cayley–Dickson pair.
*What this file does NOT derive:* the rule (still a POSTULATE), the
**existence** of integral curves
(local or global — still open, #635), their **convergence** (also open), any
measure, and any ensemble average.  Every theorem here has the shape
*"IF `γ` is an integral curve of `F`, THEN …"*; the antecedent is never
discharged.

## The mathematics

Write `a = cdLo s`, `b = cdHi s` for the two Cayley–Dickson (octonion)
components of a sedenion `s`, and put

* `A = N (Im a)`     (`gramA`),
* `C = N (Im b)`     (`gramC`),
* `P = ⟪Im a, Im b⟫` (`gramP`),
* `b₀ = b.coord 0`   (`ellCoeff`, the `ℓ`-coefficient = coordinate 8 of `s`).

`RuleFlow.potential_eq_cross` says `V = 4·(A·C − P²)`, i.e. `V` is four times
the Gram determinant of `(Im a, Im b)`; so `V` is a function of `(A, C, P)`
alone.  The content of this file is that the *rule* closes on these four
numbers:

**(1) The closed-form ODE system** (`hasDerivAt_gram{A,C,P}_along_flow`,
`hasDerivAt_ellCoeff_along_flow`).  Along any integral curve `γ' = F(γ)`
— with **no** state-sphere hypothesis —

  `Ȧ = 4V·(2A − 1)`,  `Ċ = 4V·(2C − 1)`,  `Ṗ = 8V·P`,  `ḃ₀ = 4V·b₀`,

hence `d(b₀²)/dt = 8V·b₀²`.  (Consistency check, proved:
`Ȧ + Ċ + d(b₀²)/dt = 8V·(A + C + b₀² − 1) = 0` on the state sphere.)

**(2) The straight ray** (`IsRayCoord`, `ray_minor_eq_zero`, `gram_ray`,
`rayVec_collinear`).  Each of the four numbers

  `A − ½`,  `C − ½`,  `P`,  `b₀²`

obeys the *same* scalar linear ODE `ẏ = 8V(t)·y`.  Therefore every `2 × 2`
minor of the pair of vectors `(A − ½, C − ½, P, b₀²)(t)` and
`(A − ½, C − ½, P, b₀²)(t₀)` vanishes: the point moves on a **straight ray**
through `(½, ½, 0, 0)`, in *any* time parametrisation.  This is the exact
statement of the structure found numerically in attack 1 §3a
(`analysis/473-kill-attack/attack1_anneal_vs_quench.md`); "ray" here means
precisely *"all pairwise minors against the initial vector vanish"*, which is
collinearity, and is proved — not the existence of the ray parameter `λ`,
which is a consequence.

**(3) The endpoint** (`quench_relation`, `quench_root_pick`,
`ellSq_tendsto_closed_form`, `ellSq_limit_eq_closed_form`).  Collinearity plus
the sphere constraint `A + C + b₀² = 1` collapses to the *conserved quadratic*

  `V·B₀² = B²·(V₀ + 2B₀ − 1) − 2B₀²·B + B₀²`,  `B := b₀²`,  `B₀ := b₀(t₀)²`,

valid at every time.  **Conditionally on `V(γ t) → 0`** (which is NOT proved
— see FLAG below) and on `b₀² (γ t) → L`, the limit satisfies

  `L·(B₀ + √((1 − B₀)² − V₀)) = B₀`,  i.e.  `L = b₀²/(b₀² + √((1 − b₀²)² − V₀))`,

the closed form of attack 1.  The discriminant is non-negative on the state
sphere by `potential_le_one_sub_ellSq_sq` (`V = 4(AC − P²) ≤ (A + C)² = (1 − b₀²)²`).

**(4) `b₀²` only grows** (`ellSq_monotone_along_flow`, `quench_root_ge_initial`,
`ellSq_limit_ge_initial`).  Since `V ≥ 0`, `d(b₀²)/dt = 8V·b₀² ≥ 0`, so `b₀²` is
`MonotoneOn` along any integral curve; and the endpoint of (3) satisfies
`b₀²(t₀) ≤ L` purely algebraically (`D = √((1 − B₀)² − V₀) ≤ 1 − B₀`).

## FLAG-rule-flow-open (inherited, unchanged)

* **Existence** of integral curves is NOT proved here or in `RuleFlow`.
* **Convergence** `V(γ t) → 0` is NOT proved; it is a *hypothesis* of
  `ellSq_tendsto_closed_form`.  Likewise the existence of the limit `L`.
* Nothing here is a measure, an ensemble average, or a physical claim.  The
  numbers `0.1416 / 1/3` of attack 1 are *numerical* and stay numerical: this
  file proves the per-orbit map they integrate, not the integral.

Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
`#print axioms` audit in §8.
-/

namespace QBP.Substrate.RuleFlowInvariants

open QBP.Foundations QBP.Foundations.CDAlg QBP.Foundations.CrystalHosting QBP.Substrate
open QBP.Substrate.RuleFlow
open scoped RealInnerProductSpace

/-! ## 1. The four Gram invariants -/

/-- `Im a`, the imaginary part of the low Cayley–Dickson component. -/
def gramLo (s : CDAlg ℝ 4) : CDAlg ℝ 3 := imPart (cdLo s)

/-- `Im b`, the imaginary part of the high Cayley–Dickson component. -/
def gramHi (s : CDAlg ℝ 4) : CDAlg ℝ 3 := imPart (cdHi s)

/-- `A = N (Im a)`. -/
def gramA (s : CDAlg ℝ 4) : ℝ := N (gramLo s)

/-- `C = N (Im b)`. -/
def gramC (s : CDAlg ℝ 4) : ℝ := N (gramHi s)

/-- `P = ⟪Im a, Im b⟫`. -/
def gramP (s : CDAlg ℝ 4) : ℝ := bil (gramLo s) (gramHi s)

/-- `b₀`, the `ℓ`-coefficient: coordinate `0` of the high CD component, i.e.
    coordinate `8` of the sedenion. -/
def ellCoeff (s : CDAlg ℝ 4) : ℝ := (cdHi s).coord 0

theorem gramA_def (s : CDAlg ℝ 4) : gramA s = N (gramLo s) := rfl
theorem gramC_def (s : CDAlg ℝ 4) : gramC s = N (gramHi s) := rfl
theorem gramP_def (s : CDAlg ℝ 4) : gramP s = bil (gramLo s) (gramHi s) := rfl
theorem ellCoeff_def (s : CDAlg ℝ 4) : ellCoeff s = (cdHi s).coord 0 := rfl

theorem gramLo_coord_zero (s : CDAlg ℝ 4) : (gramLo s).coord 0 = 0 := imPart_coord_zero _
theorem gramHi_coord_zero (s : CDAlg ℝ 4) : (gramHi s).coord 0 = 0 := imPart_coord_zero _

/-- **`V = 4·(A·C − P²)`** — the potential in the Gram invariants
    (`RuleFlow.potential_eq_cross`, restated in the names used here). -/
theorem potential_eq_gram (s : CDAlg ℝ 4) :
    Hosting.potential s = 4 * (gramA s * gramC s - gramP s ^ 2) :=
  potential_eq_cross s

theorem gramA_nonneg (s : CDAlg ℝ 4) : 0 ≤ gramA s := alt_N_nonneg _
theorem gramC_nonneg (s : CDAlg ℝ 4) : 0 ≤ gramC s := alt_N_nonneg _

/-- **The sphere constraint in the invariants:** `A + C + b₀² = 1`. -/
theorem gram_sum_eq_one {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) :
    gramA s + gramC s + ellCoeff s ^ 2 = 1 := by
  have hsplit : N s = N (cdLo s) + N (cdHi s) :=
    QBP.Foundations.NoAutonomousDynamics.N_split s
  have hlo : N (gramLo s) = N (cdLo s) - ((cdLo s).coord 0) ^ 2 := N_imPart _
  have hhi : N (gramHi s) = N (cdHi s) - ((cdHi s).coord 0) ^ 2 := N_imPart _
  have h0 : (cdLo s).coord 0 = 0 := cdLo_coord_zero hs.1
  have hN : N s = 1 := hs.2
  rw [gramA_def, gramC_def, ellCoeff_def, hlo, hhi, h0]
  rw [hN] at hsplit
  linarith

/-- `0 ≤ b₀² ≤ 1` on the state sphere. -/
theorem ellSq_le_one {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) : ellCoeff s ^ 2 ≤ 1 := by
  have hsum := gram_sum_eq_one hs
  linarith [gramA_nonneg s, gramC_nonneg s]

/-- **The discriminant is non-negative on the state sphere:** `V ≤ (1 − b₀²)²`.
    Proof: `V = 4(AC − P²) ≤ 4AC ≤ (A + C)² = (1 − b₀²)²` — AM–GM plus the sphere
    constraint.  (This is the sharper, `b₀`-resolved form of
    `RuleFlow.potential_le_normForm_sq`.) -/
theorem potential_le_one_sub_ellSq_sq {s : CDAlg ℝ 4} (hs : s ∈ Hosting.StateSphere) :
    Hosting.potential s ≤ (1 - ellCoeff s ^ 2) ^ 2 := by
  have hsum := gram_sum_eq_one hs
  rw [potential_eq_gram]
  nlinarith [sq_nonneg (gramA s - gramC s), sq_nonneg (gramP s)]

/-! ## 2. Linearity of `Im` and the CD-split pairings -/

theorem imPart_add (x y : CDAlg ℝ n) : imPart (x + y) = imPart x + imPart y := by
  simp only [imPart_def, add_coord, add_smul]; abel

theorem imPart_smul (r : ℝ) (x : CDAlg ℝ n) : imPart (r • x) = r • imPart x := by
  simp only [imPart_def, smul_coord]; module

theorem imPart_sub (x y : CDAlg ℝ n) : imPart (x - y) = imPart x - imPart y := by
  simp only [imPart_def, sub_coord, sub_smul]; abel

/-- Pairing against a low-embedded octonion sees only the low component. -/
theorem bil_cdLo_left (x : CDAlg ℝ 4) (u : CDAlg ℝ 3) : bil (cdLo x) u = bil x (loOf u) := by
  rw [bil_split, cdLo_loOf, cdHi_loOf, bil_zero_right, add_zero]

/-- Pairing against a high-embedded octonion sees only the high component. -/
theorem bil_cdHi_left (x : CDAlg ℝ 4) (v : CDAlg ℝ 3) : bil (cdHi x) v = bil x (hiOf v) := by
  rw [bil_split, cdLo_hiOf, cdHi_hiOf, bil_zero_right, zero_add]

theorem secVar_loOf (s : CDAlg ℝ 4) (u : CDAlg ℝ 3) :
    secVar s (loOf u) = u * cdHi s - cdHi s * u := by
  simp only [secVar, cdLo_loOf, cdHi_loOf, alt_mul_zero, alt_zero_mul, sub_self, zero_add]

theorem secVar_hiOf (s : CDAlg ℝ 4) (v : CDAlg ℝ 3) :
    secVar s (hiOf v) = cdLo s * v - v * cdLo s := by
  simp only [secVar, cdLo_hiOf, cdHi_hiOf, alt_mul_zero, alt_zero_mul, sub_self, add_zero]

/-! ## 3. The four gradient pairings

`∇V` in CD coordinates is `(8(C·Im a − P·Im b), 8(A·Im b − P·Im a))`; the four
numbers below are exactly what the ODE system needs, and each is obtained from
`RuleFlow.bil_gradV` without ever unfolding the octonion closed form. -/

theorem bil_cdLo_gradV (s : CDAlg ℝ 4) (u : CDAlg ℝ 3) :
    bil (cdLo (gradV s)) u = 2 * bil (comm s) (u * cdHi s - cdHi s * u) := by
  rw [bil_cdLo_left, bil_gradV, secVar_loOf]

theorem bil_cdHi_gradV (s : CDAlg ℝ 4) (v : CDAlg ℝ 3) :
    bil (cdHi (gradV s)) v = 2 * bil (comm s) (cdLo s * v - v * cdLo s) := by
  rw [bil_cdHi_left, bil_gradV, secVar_hiOf]

/-- `[Im a, b] = [a, b] = C s`. -/
theorem gramLo_comm (s : CDAlg ℝ 4) : gramLo s * cdHi s - cdHi s * gramLo s = comm s := by
  show (cdLo s - ((cdLo s).coord 0) • (1 : CDAlg ℝ 3)) * cdHi s
      - cdHi s * (cdLo s - ((cdLo s).coord 0) • (1 : CDAlg ℝ 3)) = comm s
  rw [commutator_sub_central_left]
  rfl

/-- `[Im b, b] = 0`. -/
theorem gramHi_comm_self (s : CDAlg ℝ 4) : gramHi s * cdHi s - cdHi s * gramHi s = 0 := by
  show (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3)) * cdHi s
      - cdHi s * (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3)) = 0
  rw [commutator_sub_central_left, sub_self]

/-- `[a, Im b] = [a, b] = C s`. -/
theorem comm_gramHi (s : CDAlg ℝ 4) : cdLo s * gramHi s - gramHi s * cdLo s = comm s := by
  show cdLo s * (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3))
      - (cdHi s - ((cdHi s).coord 0) • (1 : CDAlg ℝ 3)) * cdLo s = comm s
  rw [QBP.Foundations.DeltaLandscape.commutator_sub_central]
  rfl

/-- `[a, Im a] = 0`. -/
theorem comm_gramLo_self (s : CDAlg ℝ 4) : cdLo s * gramLo s - gramLo s * cdLo s = 0 := by
  show cdLo s * (cdLo s - ((cdLo s).coord 0) • (1 : CDAlg ℝ 3))
      - (cdLo s - ((cdLo s).coord 0) • (1 : CDAlg ℝ 3)) * cdLo s = 0
  rw [QBP.Foundations.DeltaLandscape.commutator_sub_central, sub_self]

/-- `⟪∂_a V, Im a⟫ = 2V`. -/
theorem bil_cdLo_gradV_gramLo (s : CDAlg ℝ 4) :
    bil (cdLo (gradV s)) (gramLo s) = 2 * Hosting.potential s := by
  rw [bil_cdLo_gradV, gramLo_comm, ← N_eq_bil, potential_eq_N_comm]

/-- `⟪∂_a V, Im b⟫ = 0`. -/
theorem bil_cdLo_gradV_gramHi (s : CDAlg ℝ 4) : bil (cdLo (gradV s)) (gramHi s) = 0 := by
  rw [bil_cdLo_gradV, gramHi_comm_self, bil_zero_right, mul_zero]

/-- `⟪∂_b V, Im b⟫ = 2V`. -/
theorem bil_cdHi_gradV_gramHi (s : CDAlg ℝ 4) :
    bil (cdHi (gradV s)) (gramHi s) = 2 * Hosting.potential s := by
  rw [bil_cdHi_gradV, comm_gramHi, ← N_eq_bil, potential_eq_N_comm]

/-- `⟪∂_b V, Im a⟫ = 0`. -/
theorem bil_cdHi_gradV_gramLo (s : CDAlg ℝ 4) : bil (cdHi (gradV s)) (gramLo s) = 0 := by
  rw [bil_cdHi_gradV, comm_gramLo_self, bil_zero_right, mul_zero]

/-- `∂_a V` is a purely imaginary octonion: `V` does not see `Re a`. -/
theorem cdLo_gradV_coord_zero (s : CDAlg ℝ 4) : (cdLo (gradV s)).coord 0 = 0 := by
  have h := bil_cdLo_gradV s 1
  rw [bil_one_right, cd_one_mul, cd_mul_one, sub_self, bil_zero_right, mul_zero] at h
  exact h

/-- `∂_b V` is a purely imaginary octonion: `V` does not see `b₀`. -/
theorem cdHi_gradV_coord_zero (s : CDAlg ℝ 4) : (cdHi (gradV s)).coord 0 = 0 := by
  have h := bil_cdHi_gradV s 1
  rw [bil_one_right, cd_one_mul, cd_mul_one, sub_self, bil_zero_right, mul_zero] at h
  exact h

/-- `(∇V)₀ = 0`. -/
theorem gradV_coord_zero (s : CDAlg ℝ 4) : (gradV s).coord 0 = 0 := by
  have h := cdLo_gradV_coord_zero s
  rwa [cdLo_coord, loIdx_zero] at h

/-- **Euler's relation for the quartic `V`:** `⟪∇V(s), s⟫ = 4·V(s)`. -/
theorem bil_gradV_self (s : CDAlg ℝ 4) : bil (gradV s) s = 4 * Hosting.potential s := by
  have hsec : secVar s s = comm s + comm s := rfl
  rw [bil_gradV, hsec, bil_add_right, ← N_eq_bil, potential_eq_N_comm]; ring

/-! ## 4. The rule field in the invariants -/

theorem cdLo_ruleField (s : CDAlg ℝ 4) :
    cdLo (ruleField s) = (4 * Hosting.potential s) • cdLo s - cdLo (gradV s) := by
  rw [ruleField, cdLo_neg, cdLo_sub, cdLo_sub, cdLo_smul, cdLo_smul, cdLo_one,
    gradV_coord_zero, bil_gradV_self]
  module

theorem cdHi_ruleField (s : CDAlg ℝ 4) :
    cdHi (ruleField s) = (4 * Hosting.potential s) • cdHi s - cdHi (gradV s) := by
  rw [ruleField, cdHi_neg, cdHi_sub, cdHi_sub, cdHi_smul, cdHi_smul, cdHi_one,
    gradV_coord_zero, bil_gradV_self]
  module

theorem gramLo_ruleField (s : CDAlg ℝ 4) :
    gramLo (ruleField s) = (4 * Hosting.potential s) • gramLo s - cdLo (gradV s) := by
  show imPart (cdLo (ruleField s))
      = (4 * Hosting.potential s) • imPart (cdLo s) - cdLo (gradV s)
  rw [cdLo_ruleField, imPart_sub, imPart_smul, imPart_eq_self (cdLo_gradV_coord_zero s)]

theorem gramHi_ruleField (s : CDAlg ℝ 4) :
    gramHi (ruleField s) = (4 * Hosting.potential s) • gramHi s - cdHi (gradV s) := by
  show imPart (cdHi (ruleField s))
      = (4 * Hosting.potential s) • imPart (cdHi s) - cdHi (gradV s)
  rw [cdHi_ruleField, imPart_sub, imPart_smul, imPart_eq_self (cdHi_gradV_coord_zero s)]

/-- `ḃ₀ = 4V·b₀`, pointwise on the field. -/
theorem ellCoeff_ruleField (s : CDAlg ℝ 4) :
    ellCoeff (ruleField s) = 4 * Hosting.potential s * ellCoeff s := by
  show (cdHi (ruleField s)).coord 0 = 4 * Hosting.potential s * (cdHi s).coord 0
  rw [cdHi_ruleField, sub_coord, smul_coord, cdHi_gradV_coord_zero, sub_zero]

theorem bil_gramLo_gramLo_ruleField (s : CDAlg ℝ 4) :
    bil (gramLo s) (gramLo (ruleField s))
      = 4 * Hosting.potential s * gramA s - 2 * Hosting.potential s := by
  have h1 : bil (gramLo s) (cdLo (gradV s)) = 2 * Hosting.potential s := by
    rw [NormForm.bil_symm]; exact bil_cdLo_gradV_gramLo s
  rw [gramLo_ruleField, bil_sub_right, bil_smul_right, h1, ← N_eq_bil, ← gramA_def]

theorem bil_gramHi_gramHi_ruleField (s : CDAlg ℝ 4) :
    bil (gramHi s) (gramHi (ruleField s))
      = 4 * Hosting.potential s * gramC s - 2 * Hosting.potential s := by
  have h1 : bil (gramHi s) (cdHi (gradV s)) = 2 * Hosting.potential s := by
    rw [NormForm.bil_symm]; exact bil_cdHi_gradV_gramHi s
  rw [gramHi_ruleField, bil_sub_right, bil_smul_right, h1, ← N_eq_bil, ← gramC_def]

theorem bil_gramLo_gramHi_ruleField (s : CDAlg ℝ 4) :
    bil (gramLo s) (gramHi (ruleField s)) = 4 * Hosting.potential s * gramP s := by
  have h1 : bil (gramLo s) (cdHi (gradV s)) = 0 := by
    rw [NormForm.bil_symm]; exact bil_cdHi_gradV_gramLo s
  rw [gramHi_ruleField, bil_sub_right, bil_smul_right, h1, sub_zero, ← gramP_def]

theorem bil_gramLo_ruleField_gramHi (s : CDAlg ℝ 4) :
    bil (gramLo (ruleField s)) (gramHi s) = 4 * Hosting.potential s * gramP s := by
  rw [gramLo_ruleField, bil_sub_left, bil_smul_left, bil_cdLo_gradV_gramHi, sub_zero,
    ← gramP_def]

/-! ## 5. The closed-form ODE system along an integral curve

**Deliverable (1).**  No state-sphere hypothesis is needed: the system closes
on all of `CDAlg ℝ 4`. -/

noncomputable def gramLoCLM : CDAlg ℝ 4 →L[ℝ] CDAlg ℝ 3 :=
  LinearMap.toContinuousLinearMap
    ({ toFun := gramLo
       map_add' := fun x y => by
         show imPart (cdLo (x + y)) = imPart (cdLo x) + imPart (cdLo y)
         rw [cdLo_add, imPart_add]
       map_smul' := fun r x => by
         show imPart (cdLo (r • x)) = r • imPart (cdLo x)
         rw [cdLo_smul, imPart_smul] } : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 3)

@[simp] theorem gramLoCLM_apply (s : CDAlg ℝ 4) : gramLoCLM s = gramLo s := rfl

noncomputable def gramHiCLM : CDAlg ℝ 4 →L[ℝ] CDAlg ℝ 3 :=
  LinearMap.toContinuousLinearMap
    ({ toFun := gramHi
       map_add' := fun x y => by
         show imPart (cdHi (x + y)) = imPart (cdHi x) + imPart (cdHi y)
         rw [cdHi_add, imPart_add]
       map_smul' := fun r x => by
         show imPart (cdHi (r • x)) = r • imPart (cdHi x)
         rw [cdHi_smul, imPart_smul] } : CDAlg ℝ 4 →ₗ[ℝ] CDAlg ℝ 3)

@[simp] theorem gramHiCLM_apply (s : CDAlg ℝ 4) : gramHiCLM s = gramHi s := rfl

noncomputable def ellCoeffCLM : CDAlg ℝ 4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := ellCoeff
       map_add' := fun x y => by
         show (cdHi (x + y)).coord 0 = (cdHi x).coord 0 + (cdHi y).coord 0
         rw [cdHi_add, add_coord]
       map_smul' := fun r x => by
         show (cdHi (r • x)).coord 0 = r * (cdHi x).coord 0
         rw [cdHi_smul, smul_coord] } : CDAlg ℝ 4 →ₗ[ℝ] ℝ)

@[simp] theorem ellCoeffCLM_apply (s : CDAlg ℝ 4) : ellCoeffCLM s = ellCoeff s := rfl

variable {γ : ℝ → CDAlg ℝ 4} {t : ℝ}

theorem hasDerivAt_gramLo (hγ : HasDerivAt γ (ruleField (γ t)) t) :
    HasDerivAt (fun r => gramLo (γ r)) (gramLo (ruleField (γ t))) t := by
  simpa using gramLoCLM.hasFDerivAt.comp_hasDerivAt t hγ

theorem hasDerivAt_gramHi (hγ : HasDerivAt γ (ruleField (γ t)) t) :
    HasDerivAt (fun r => gramHi (γ r)) (gramHi (ruleField (γ t))) t := by
  simpa using gramHiCLM.hasFDerivAt.comp_hasDerivAt t hγ

/-- **`Ȧ = 4V·(2A − 1)`.** -/
theorem hasDerivAt_gramA_along_flow (hγ : HasDerivAt γ (ruleField (γ t)) t) :
    HasDerivAt (fun r => gramA (γ r))
      (4 * Hosting.potential (γ t) * (2 * gramA (γ t) - 1)) t := by
  have h : HasDerivAt (fun r => (inner ℝ (gramLo (γ r)) (gramLo (γ r)) : ℝ))
      ((inner ℝ (gramLo (γ t)) (gramLo (ruleField (γ t))) : ℝ)
        + (inner ℝ (gramLo (ruleField (γ t))) (gramLo (γ t)) : ℝ)) t :=
    HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_gramLo hγ) (hasDerivAt_gramLo hγ)
  have hfun : (fun r => (inner ℝ (gramLo (γ r)) (gramLo (γ r)) : ℝ)) = fun r => gramA (γ r) := by
    funext r; rw [inner_def', gramA_def, N_eq_bil]
  have hval : (inner ℝ (gramLo (γ t)) (gramLo (ruleField (γ t))) : ℝ)
      + (inner ℝ (gramLo (ruleField (γ t))) (gramLo (γ t)) : ℝ)
      = 4 * Hosting.potential (γ t) * (2 * gramA (γ t) - 1) := by
    rw [inner_def', inner_def', NormForm.bil_symm (gramLo (ruleField (γ t))),
      bil_gramLo_gramLo_ruleField]
    ring
  rw [hfun, hval] at h
  exact h

/-- **`Ċ = 4V·(2C − 1)`.** -/
theorem hasDerivAt_gramC_along_flow (hγ : HasDerivAt γ (ruleField (γ t)) t) :
    HasDerivAt (fun r => gramC (γ r))
      (4 * Hosting.potential (γ t) * (2 * gramC (γ t) - 1)) t := by
  have h : HasDerivAt (fun r => (inner ℝ (gramHi (γ r)) (gramHi (γ r)) : ℝ))
      ((inner ℝ (gramHi (γ t)) (gramHi (ruleField (γ t))) : ℝ)
        + (inner ℝ (gramHi (ruleField (γ t))) (gramHi (γ t)) : ℝ)) t :=
    HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_gramHi hγ) (hasDerivAt_gramHi hγ)
  have hfun : (fun r => (inner ℝ (gramHi (γ r)) (gramHi (γ r)) : ℝ)) = fun r => gramC (γ r) := by
    funext r; rw [inner_def', gramC_def, N_eq_bil]
  have hval : (inner ℝ (gramHi (γ t)) (gramHi (ruleField (γ t))) : ℝ)
      + (inner ℝ (gramHi (ruleField (γ t))) (gramHi (γ t)) : ℝ)
      = 4 * Hosting.potential (γ t) * (2 * gramC (γ t) - 1) := by
    rw [inner_def', inner_def', NormForm.bil_symm (gramHi (ruleField (γ t))),
      bil_gramHi_gramHi_ruleField]
    ring
  rw [hfun, hval] at h
  exact h

/-- **`Ṗ = 8V·P`.** -/
theorem hasDerivAt_gramP_along_flow (hγ : HasDerivAt γ (ruleField (γ t)) t) :
    HasDerivAt (fun r => gramP (γ r)) (8 * Hosting.potential (γ t) * gramP (γ t)) t := by
  have h : HasDerivAt (fun r => (inner ℝ (gramLo (γ r)) (gramHi (γ r)) : ℝ))
      ((inner ℝ (gramLo (γ t)) (gramHi (ruleField (γ t))) : ℝ)
        + (inner ℝ (gramLo (ruleField (γ t))) (gramHi (γ t)) : ℝ)) t :=
    HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_gramLo hγ) (hasDerivAt_gramHi hγ)
  have hfun : (fun r => (inner ℝ (gramLo (γ r)) (gramHi (γ r)) : ℝ)) = fun r => gramP (γ r) := by
    funext r; rw [inner_def', gramP_def]
  have hval : (inner ℝ (gramLo (γ t)) (gramHi (ruleField (γ t))) : ℝ)
      + (inner ℝ (gramLo (ruleField (γ t))) (gramHi (γ t)) : ℝ)
      = 8 * Hosting.potential (γ t) * gramP (γ t) := by
    rw [inner_def', inner_def', bil_gramLo_gramHi_ruleField, bil_gramLo_ruleField_gramHi]
    ring
  rw [hfun, hval] at h
  exact h

/-- **`ḃ₀ = 4V·b₀`.** -/
theorem hasDerivAt_ellCoeff_along_flow (hγ : HasDerivAt γ (ruleField (γ t)) t) :
    HasDerivAt (fun r => ellCoeff (γ r)) (4 * Hosting.potential (γ t) * ellCoeff (γ t)) t := by
  have h := ellCoeffCLM.hasFDerivAt.comp_hasDerivAt t hγ
  simp only [ellCoeffCLM_apply] at h
  rwa [ellCoeff_ruleField] at h

/-- **`d(b₀²)/dt = 8V·b₀²`.** -/
theorem hasDerivAt_ellSq_along_flow (hγ : HasDerivAt γ (ruleField (γ t)) t) :
    HasDerivAt (fun r => ellCoeff (γ r) ^ 2)
      (8 * Hosting.potential (γ t) * ellCoeff (γ t) ^ 2) t := by
  have h := (hasDerivAt_ellCoeff_along_flow hγ).pow 2
  convert h using 1
  push_cast
  ring

/-- **Consistency of the system with the sphere constraint:**
    `Ȧ + Ċ + d(b₀²)/dt = 8V·(A + C + b₀² − 1) = 0` on the state sphere. -/
theorem gram_sum_hasDerivAt_zero (hγ : HasDerivAt γ (ruleField (γ t)) t)
    (hs : γ t ∈ Hosting.StateSphere) :
    HasDerivAt (fun r => gramA (γ r) + gramC (γ r) + ellCoeff (γ r) ^ 2) 0 t := by
  have h := ((hasDerivAt_gramA_along_flow hγ).add (hasDerivAt_gramC_along_flow hγ)).add
    (hasDerivAt_ellSq_along_flow hγ)
  have hsum := gram_sum_eq_one hs
  have hzero : 4 * Hosting.potential (γ t) * (2 * gramA (γ t) - 1)
        + 4 * Hosting.potential (γ t) * (2 * gramC (γ t) - 1)
        + 8 * Hosting.potential (γ t) * ellCoeff (γ t) ^ 2 = 0 := by
    linear_combination (8 * Hosting.potential (γ t)) * hsum
  rw [hzero] at h
  exact h

/-- **`b₀²` never decreases along the flow.**  `d(b₀²)/dt = 8V·b₀² ≥ 0` because
    `V = N(C s) ≥ 0`, so `t ↦ b₀²(γ t)` is monotone on `[a,b]`.  No state-sphere
    hypothesis is needed.  This is the sign statement behind the "`|b₀|` only
    grows" remark of attack 1 §3a; note it is a statement about a *given* curve
    (existence of curves is still open). -/
theorem ellSq_monotone_along_flow {a b : ℝ} {γ : ℝ → CDAlg ℝ 4}
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (ruleField (γ t)) t) :
    MonotoneOn (fun t => ellCoeff (γ t) ^ 2) (Set.Icc a b) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
  · exact ((ellCoeffCLM.continuous).pow 2).comp_continuousOn hcont
  · rw [interior_Icc]
    intro t ht
    exact ((hasDerivAt_ellSq_along_flow (hd t ht)).differentiableAt).differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_ellSq_along_flow (hd t ht)).deriv]
    have hV : 0 ≤ Hosting.potential (γ t) := Hosting.potential_nonneg _
    nlinarith [sq_nonneg (ellCoeff (γ t))]

/-! ## 6. The straight ray

**Deliverable (2).**  A *ray coordinate* is a scalar observable obeying the
same scalar linear ODE `ẏ = 8V·y` along the flow.  Any two of them have
vanishing `2 × 2` minor against their initial values — that is exactly
collinearity, i.e. straight-ray motion, in any time parametrisation. -/

/-- A scalar observable `f` on the sedenions is a **ray coordinate** when it is
    continuous and obeys `d/dt f(γ t) = 8·V(γ t)·f(γ t)` along every integral
    curve of the rule. -/
def IsRayCoord (f : CDAlg ℝ 4 → ℝ) : Prop :=
  Continuous f ∧
    ∀ {γ : ℝ → CDAlg ℝ 4} {t : ℝ}, HasDerivAt γ (ruleField (γ t)) t →
      HasDerivAt (fun r => f (γ r)) (8 * Hosting.potential (γ t) * f (γ t)) t

theorem contDiff_gramLo {k : WithTop ℕ∞} : ContDiff ℝ k (gramLo : CDAlg ℝ 4 → CDAlg ℝ 3) :=
  gramLoCLM.contDiff

theorem contDiff_gramHi {k : WithTop ℕ∞} : ContDiff ℝ k (gramHi : CDAlg ℝ 4 → CDAlg ℝ 3) :=
  gramHiCLM.contDiff

theorem contDiff_gramA {k : WithTop ℕ∞} : ContDiff ℝ k (gramA : CDAlg ℝ 4 → ℝ) :=
  contDiff_normForm contDiff_gramLo

theorem contDiff_gramC {k : WithTop ℕ∞} : ContDiff ℝ k (gramC : CDAlg ℝ 4 → ℝ) :=
  contDiff_normForm contDiff_gramHi

theorem contDiff_gramP {k : WithTop ℕ∞} : ContDiff ℝ k (gramP : CDAlg ℝ 4 → ℝ) := by
  show ContDiff ℝ k (fun s : CDAlg ℝ 4 => bil (gramLo s) (gramHi s))
  simp only [bil_def]
  exact ContDiff.sum (fun i _ =>
    ContDiff.mul (contDiff_cd_iff.mp contDiff_gramLo i) (contDiff_cd_iff.mp contDiff_gramHi i))

theorem continuous_gramLo : Continuous (gramLo : CDAlg ℝ 4 → CDAlg ℝ 3) :=
  (contDiff_gramLo (k := ⊤)).continuous

theorem continuous_gramHi : Continuous (gramHi : CDAlg ℝ 4 → CDAlg ℝ 3) :=
  (contDiff_gramHi (k := ⊤)).continuous

theorem continuous_ellCoeff : Continuous (ellCoeff : CDAlg ℝ 4 → ℝ) := ellCoeffCLM.continuous

theorem continuous_gramA : Continuous (gramA : CDAlg ℝ 4 → ℝ) :=
  (contDiff_gramA (k := ⊤)).continuous

theorem continuous_gramC : Continuous (gramC : CDAlg ℝ 4 → ℝ) :=
  (contDiff_gramC (k := ⊤)).continuous

theorem continuous_gramP : Continuous (gramP : CDAlg ℝ 4 → ℝ) :=
  (contDiff_gramP (k := ⊤)).continuous

theorem isRayCoord_gramA_sub : IsRayCoord (fun s => gramA s - 1/2) :=
  ⟨continuous_gramA.sub continuous_const, fun hγ => by
    have h := (hasDerivAt_gramA_along_flow hγ).sub_const (1/2 : ℝ)
    convert h using 1
    ring⟩

theorem isRayCoord_gramC_sub : IsRayCoord (fun s => gramC s - 1/2) :=
  ⟨continuous_gramC.sub continuous_const, fun hγ => by
    have h := (hasDerivAt_gramC_along_flow hγ).sub_const (1/2 : ℝ)
    convert h using 1
    ring⟩

theorem isRayCoord_gramP : IsRayCoord gramP :=
  ⟨continuous_gramP, fun hγ => hasDerivAt_gramP_along_flow hγ⟩

theorem isRayCoord_ellSq : IsRayCoord (fun s => ellCoeff s ^ 2) :=
  ⟨continuous_ellCoeff.pow 2, fun hγ => hasDerivAt_ellSq_along_flow hγ⟩

/-- **The ray.**  For any two ray coordinates `f`, `g` and any integral curve of
    the rule on `[a,b]`, the `2 × 2` minor `f(γ t)·g(γ t₀) − g(γ t)·f(γ t₀)`
    vanishes identically: the vector of ray coordinates at time `t` is
    collinear with its value at `t₀`. -/
theorem ray_minor_eq_zero {a b t₀ : ℝ} {γ : ℝ → CDAlg ℝ 4} {f g : CDAlg ℝ 4 → ℝ}
    (hf : IsRayCoord f) (hg : IsRayCoord g)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (ruleField (γ t)) t) :
    ∀ t ∈ Set.Icc a b, f (γ t) * g (γ t₀) - g (γ t) * f (γ t₀) = 0 := by
  have hVc : ContinuousOn (fun t => 8 * Hosting.potential (γ t)) (Set.Icc a b) :=
    continuousOn_const.mul (((contDiff_potential (k := ⊤)).continuous).comp_continuousOn hcont)
  refine scalar_linear_ode_zero (c := fun t => 8 * Hosting.potential (γ t))
    (u := fun t => f (γ t) * g (γ t₀) - g (γ t) * f (γ t₀)) ht₀ hVc ?_ ?_ (by ring)
  · exact ((hf.1.comp_continuousOn hcont).mul continuousOn_const).sub
      ((hg.1.comp_continuousOn hcont).mul continuousOn_const)
  · intro t ht
    have h := ((hf.2 (hd t ht)).mul_const (g (γ t₀))).sub ((hg.2 (hd t ht)).mul_const (f (γ t₀)))
    convert h using 1
    ring

/-- **Deliverable (2), in the four Gram invariants.**  Along any integral curve
    of the rule the point `(A − ½, C − ½, P, b₀²)` stays collinear with its
    initial value: every minor against `b₀²` vanishes.  (The remaining minors
    follow by the same `ray_minor_eq_zero` with the corresponding pair.) -/
theorem gram_ray {a b t₀ : ℝ} {γ : ℝ → CDAlg ℝ 4}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (ruleField (γ t)) t) :
    ∀ t ∈ Set.Icc a b,
      (gramA (γ t) - 1/2) * ellCoeff (γ t₀) ^ 2
          - ellCoeff (γ t) ^ 2 * (gramA (γ t₀) - 1/2) = 0 ∧
      (gramC (γ t) - 1/2) * ellCoeff (γ t₀) ^ 2
          - ellCoeff (γ t) ^ 2 * (gramC (γ t₀) - 1/2) = 0 ∧
      gramP (γ t) * ellCoeff (γ t₀) ^ 2 - ellCoeff (γ t) ^ 2 * gramP (γ t₀) = 0 := by
  intro t ht
  exact ⟨ray_minor_eq_zero isRayCoord_gramA_sub isRayCoord_ellSq ht₀ hcont hd t ht,
    ray_minor_eq_zero isRayCoord_gramC_sub isRayCoord_ellSq ht₀ hcont hd t ht,
    ray_minor_eq_zero isRayCoord_gramP isRayCoord_ellSq ht₀ hcont hd t ht⟩

/-- The four ray coordinates as a vector in `ℝ⁴`. -/
noncomputable def rayVec (s : CDAlg ℝ 4) : Fin 4 → ℝ
  | 0 => gramA s - 1/2
  | 1 => gramC s - 1/2
  | 2 => gramP s
  | 3 => ellCoeff s ^ 2

theorem isRayCoord_rayVec : ∀ i : Fin 4, IsRayCoord (fun s => rayVec s i)
  | 0 => isRayCoord_gramA_sub
  | 1 => isRayCoord_gramC_sub
  | 2 => isRayCoord_gramP
  | 3 => isRayCoord_ellSq

/-- **Straight-ray motion, stated as collinearity in `ℝ⁴`:** every `2 × 2` minor
    of `rayVec (γ t)` against `rayVec (γ t₀)` vanishes. -/
theorem rayVec_collinear {a b t₀ : ℝ} {γ : ℝ → CDAlg ℝ 4}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (ruleField (γ t)) t) :
    ∀ (i j : Fin 4), ∀ t ∈ Set.Icc a b,
      rayVec (γ t) i * rayVec (γ t₀) j = rayVec (γ t) j * rayVec (γ t₀) i := by
  intro i j t ht
  have h := ray_minor_eq_zero (isRayCoord_rayVec i) (isRayCoord_rayVec j) ht₀ hcont hd t ht
  linarith

/-! ## 7. The conserved quadratic and the endpoint

**Deliverable (3).** -/

/-- **The quench relation.**  Collinearity plus the sphere constraint at `t₀`
    gives, at every time, the closed algebraic relation between `V` and `B = b₀²`

      `V·B₀² = B²·(V₀ + 2B₀ − 1) − 2B₀²·B + B₀²`.

    Notice it involves the *initial data only through* `(V₀, B₀)`. -/
theorem quench_relation {a b t₀ : ℝ} {γ : ℝ → CDAlg ℝ 4}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : γ t₀ ∈ Hosting.StateSphere) :
    ∀ t ∈ Set.Icc a b,
      Hosting.potential (γ t) * (ellCoeff (γ t₀) ^ 2) ^ 2
        = (ellCoeff (γ t) ^ 2) ^ 2
            * (Hosting.potential (γ t₀) + 2 * ellCoeff (γ t₀) ^ 2 - 1)
          - 2 * (ellCoeff (γ t₀) ^ 2) ^ 2 * ellCoeff (γ t) ^ 2
          + (ellCoeff (γ t₀) ^ 2) ^ 2 := by
  intro t ht
  obtain ⟨m1, m2, m3⟩ := gram_ray ht₀ hcont hd t ht
  have hc0 : gramA (γ t₀) + gramC (γ t₀) + ellCoeff (γ t₀) ^ 2 = 1 := gram_sum_eq_one hmem
  have hV := potential_eq_gram (γ t)
  have hV0 := potential_eq_gram (γ t₀)
  set A := gramA (γ t); set C := gramC (γ t); set P := gramP (γ t)
  set A0 := gramA (γ t₀); set C0 := gramC (γ t₀); set P0 := gramP (γ t₀)
  set B := ellCoeff (γ t) ^ 2; set B0 := ellCoeff (γ t₀) ^ 2
  have hAB : A * B0 = B * (A0 - 1/2) + B0/2 := by linear_combination m1
  have hCB : C * B0 = B * (C0 - 1/2) + B0/2 := by linear_combination m2
  have hPB : P * B0 = B * P0 := by linear_combination m3
  have key : Hosting.potential (γ t) * B0 ^ 2 = 4 * ((A * B0) * (C * B0) - (P * B0) ^ 2) := by
    rw [hV]; ring
  rw [hAB, hCB, hPB] at key
  rw [key, hV0]
  linear_combination (2 * B * B0 - 2 * B ^ 2) * hc0

/-- **Picking the root.**  If `L ∈ [0,1]` solves the quench quadratic with
    `B₀ ∈ [0,1]` and non-negative discriminant, then `L` is the *smaller* root,
    in the division-free form `L·(B₀ + D) = B₀` with `D = √((1 − B₀)² − V₀)`.
    (The other root is `> 1` whenever it is distinct, so `L ≤ 1` selects.) -/
theorem quench_root_pick_aux {B0 V0 L D : ℝ} (hB0 : 0 ≤ B0) (hDnn : 0 ≤ D)
    (hDsq : D ^ 2 = (1 - B0) ^ 2 - V0) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hq : L ^ 2 * (V0 + 2 * B0 - 1) - 2 * B0 ^ 2 * L + B0 ^ 2 = 0) :
    L * (B0 + D) = B0 := by
  have hfac : (L * (B0 + D) - B0) * (L * (B0 - D) - B0) = 0 := by
    linear_combination hq - L ^ 2 * hDsq
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · -- the "other root" case forces `L·D = 0`, hence the same conclusion
    have hLB : L * B0 ≤ B0 := by nlinarith
    have hLD_le : L * D ≤ 0 := by nlinarith [h, hLB]
    have hLD_ge : 0 ≤ L * D := mul_nonneg hL0 hDnn
    have hLD : L * D = 0 := le_antisymm hLD_le hLD_ge
    linear_combination h + 2 * hLD

theorem quench_root_pick {B0 V0 L : ℝ} (hB0 : 0 ≤ B0)
    (hdisc : 0 ≤ (1 - B0) ^ 2 - V0) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hq : L ^ 2 * (V0 + 2 * B0 - 1) - 2 * B0 ^ 2 * L + B0 ^ 2 = 0) :
    L * (B0 + Real.sqrt ((1 - B0) ^ 2 - V0)) = B0 :=
  quench_root_pick_aux hB0 (Real.sqrt_nonneg _) (Real.sq_sqrt hdisc) hL0 hL1 hq

/-- **The quench quadratic cannot move `B` down.**  If `L` lies in the
    admissible range and solves the quench quadratic with `0 ≤ V₀`, then
    `B₀ ≤ L`: with `D = √((1 − B₀)² − V₀) ≤ 1 − B₀` (here `0 ≤ V₀` is used),
    `B₀ = L·(B₀ + D) ≤ L·(B₀ + (1 − B₀)) = L`. -/
theorem quench_root_ge_initial {B0 V0 L : ℝ} (hB0 : 0 ≤ B0) (hB01 : B0 ≤ 1)
    (hV0 : 0 ≤ V0) (hdisc : 0 ≤ (1 - B0) ^ 2 - V0) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hq : L ^ 2 * (V0 + 2 * B0 - 1) - 2 * B0 ^ 2 * L + B0 ^ 2 = 0) :
    B0 ≤ L := by
  have hroot := quench_root_pick hB0 hdisc hL0 hL1 hq
  have hD : Real.sqrt ((1 - B0) ^ 2 - V0) ≤ 1 - B0 := by
    have h := Real.sqrt_le_sqrt (show (1 - B0) ^ 2 - V0 ≤ (1 - B0) ^ 2 by linarith)
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 - B0)] at h
  have h1 : 0 ≤ L * ((1 - B0) - Real.sqrt ((1 - B0) ^ 2 - V0)) :=
    mul_nonneg hL0 (by linarith)
  linarith [hroot, h1]

/-! ### The limit statement (convergence NOT claimed) -/

/-- `StateSphere` invariance for a curve defined on all of `ℝ`. -/
theorem stateSphere_invariant_univ {γ : ℝ → CDAlg ℝ 4} {t₀ : ℝ}
    (hd : ∀ t, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : γ t₀ ∈ Hosting.StateSphere) : ∀ t, γ t ∈ Hosting.StateSphere := by
  intro t
  have hlt : min t t₀ - 1 < t₀ := by
    have := min_le_right t t₀; linarith
  have hgt : t₀ < max t t₀ + 1 := by
    have := le_max_right t t₀; linarith
  have hta : min t t₀ - 1 ≤ t := by have := min_le_left t t₀; linarith
  have htb : t ≤ max t t₀ + 1 := by have := le_max_left t t₀; linarith
  exact stateSphere_invariant (a := min t t₀ - 1) (b := max t t₀ + 1) ⟨hlt, hgt⟩
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x) hmem t ⟨hta, htb⟩

/-- The quench relation for a curve defined on all of `ℝ`. -/
theorem quench_relation_univ {γ : ℝ → CDAlg ℝ 4} {t₀ : ℝ}
    (hd : ∀ t, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : γ t₀ ∈ Hosting.StateSphere) :
    ∀ t, Hosting.potential (γ t) * (ellCoeff (γ t₀) ^ 2) ^ 2
        = (ellCoeff (γ t) ^ 2) ^ 2
            * (Hosting.potential (γ t₀) + 2 * ellCoeff (γ t₀) ^ 2 - 1)
          - 2 * (ellCoeff (γ t₀) ^ 2) ^ 2 * ellCoeff (γ t) ^ 2
          + (ellCoeff (γ t₀) ^ 2) ^ 2 := by
  intro t
  have hlt : min t t₀ - 1 < t₀ := by have := min_le_right t t₀; linarith
  have hgt : t₀ < max t t₀ + 1 := by have := le_max_right t t₀; linarith
  have hta : min t t₀ - 1 ≤ t := by have := min_le_left t t₀; linarith
  have htb : t ≤ max t t₀ + 1 := by have := le_max_left t t₀; linarith
  exact quench_relation (a := min t t₀ - 1) (b := max t t₀ + 1) ⟨hlt, hgt⟩
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x) hmem t ⟨hta, htb⟩

/-- **Deliverable (3) — the endpoint, CONDITIONAL on convergence.**  If an
    integral curve of the rule through a state-sphere point has `V(γ t) → 0` and
    `b₀²(γ t) → L` as `t → ∞`, then

      `L·(b₀² + √((1 − b₀²)² − V₀)) = b₀²`   (initial data at `t₀`).

    **Convergence is a hypothesis, not a theorem:** neither `V(γ t) → 0` nor the
    existence of the limit `L` is proved anywhere (#635, FLAG-rule-flow-open). -/
theorem ellSq_tendsto_closed_form {γ : ℝ → CDAlg ℝ 4} {t₀ L : ℝ}
    (hd : ∀ t, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : γ t₀ ∈ Hosting.StateSphere)
    (hV : Filter.Tendsto (fun t => Hosting.potential (γ t)) Filter.atTop (nhds 0))
    (hB : Filter.Tendsto (fun t => ellCoeff (γ t) ^ 2) Filter.atTop (nhds L)) :
    L * (ellCoeff (γ t₀) ^ 2
          + Real.sqrt ((1 - ellCoeff (γ t₀) ^ 2) ^ 2 - Hosting.potential (γ t₀)))
      = ellCoeff (γ t₀) ^ 2 := by
  have hsph := stateSphere_invariant_univ hd hmem
  have hrel := quench_relation_univ hd hmem
  set B0 := ellCoeff (γ t₀) ^ 2 with hB0def
  set V0 := Hosting.potential (γ t₀) with hV0def
  -- the right-hand side of the quench relation is a polynomial in `B = b₀²`
  have hpoly : Continuous (fun B : ℝ => B ^ 2 * (V0 + 2 * B0 - 1) - 2 * B0 ^ 2 * B + B0 ^ 2) := by
    fun_prop
  have hrhs : Filter.Tendsto
      (fun t => (ellCoeff (γ t) ^ 2) ^ 2 * (V0 + 2 * B0 - 1)
        - 2 * B0 ^ 2 * ellCoeff (γ t) ^ 2 + B0 ^ 2)
      Filter.atTop (nhds (L ^ 2 * (V0 + 2 * B0 - 1) - 2 * B0 ^ 2 * L + B0 ^ 2)) :=
    (hpoly.tendsto L).comp hB
  have hlhs0 : Filter.Tendsto (fun t => Hosting.potential (γ t) * B0 ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using hV.mul_const (B0 ^ 2)
  have hlhs : Filter.Tendsto
      (fun t => (ellCoeff (γ t) ^ 2) ^ 2 * (V0 + 2 * B0 - 1)
        - 2 * B0 ^ 2 * ellCoeff (γ t) ^ 2 + B0 ^ 2) Filter.atTop (nhds 0) :=
    hlhs0.congr (fun t => hrel t)
  have hq : L ^ 2 * (V0 + 2 * B0 - 1) - 2 * B0 ^ 2 * L + B0 ^ 2 = 0 :=
    (tendsto_nhds_unique hrhs hlhs)
  refine quench_root_pick (B0 := B0) (V0 := V0) (L := L) (sq_nonneg _) ?_ ?_ ?_ hq
  · have := potential_le_one_sub_ellSq_sq hmem; linarith
  · exact ge_of_tendsto hB (Filter.Eventually.of_forall (fun t => sq_nonneg _))
  · exact le_of_tendsto hB (Filter.Eventually.of_forall (fun t => ellSq_le_one (hsph t)))

/-- **The quench endpoint is never below its start**, under the same
    (unproved) convergence hypotheses: `b₀²(t₀) ≤ L`.  Consistent with, and
    independent of, `ellSq_monotone_along_flow`. -/
theorem ellSq_limit_ge_initial {γ : ℝ → CDAlg ℝ 4} {t₀ L : ℝ}
    (hd : ∀ t, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : γ t₀ ∈ Hosting.StateSphere)
    (hV : Filter.Tendsto (fun t => Hosting.potential (γ t)) Filter.atTop (nhds 0))
    (hB : Filter.Tendsto (fun t => ellCoeff (γ t) ^ 2) Filter.atTop (nhds L)) :
    ellCoeff (γ t₀) ^ 2 ≤ L := by
  have hroot := ellSq_tendsto_closed_form hd hmem hV hB
  have hB01 : ellCoeff (γ t₀) ^ 2 ≤ 1 := ellSq_le_one hmem
  have hL0 : 0 ≤ L := ge_of_tendsto hB (Filter.Eventually.of_forall (fun t => sq_nonneg _))
  have hD : Real.sqrt ((1 - ellCoeff (γ t₀) ^ 2) ^ 2 - Hosting.potential (γ t₀))
      ≤ 1 - ellCoeff (γ t₀) ^ 2 := by
    have h := Real.sqrt_le_sqrt
      (show (1 - ellCoeff (γ t₀) ^ 2) ^ 2 - Hosting.potential (γ t₀)
          ≤ (1 - ellCoeff (γ t₀) ^ 2) ^ 2 by
        linarith [Hosting.potential_nonneg (γ t₀)])
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 1 - ellCoeff (γ t₀) ^ 2)] at h
  have h1 : 0 ≤ L * ((1 - ellCoeff (γ t₀) ^ 2)
      - Real.sqrt ((1 - ellCoeff (γ t₀) ^ 2) ^ 2 - Hosting.potential (γ t₀))) :=
    mul_nonneg hL0 (by linarith)
  linarith [hroot, h1]

/-- **The closed form of attack 1 §3a**, in division form:

      `b₀²(∞) = b₀² / (b₀² + √((1 − b₀²)² − V₀))`,

    valid whenever the denominator is non-zero (it vanishes only in the
    degenerate case `b₀(t₀) = 0` and `V₀ = 1`). -/
theorem ellSq_limit_eq_closed_form {γ : ℝ → CDAlg ℝ 4} {t₀ L : ℝ}
    (hd : ∀ t, HasDerivAt γ (ruleField (γ t)) t)
    (hmem : γ t₀ ∈ Hosting.StateSphere)
    (hV : Filter.Tendsto (fun t => Hosting.potential (γ t)) Filter.atTop (nhds 0))
    (hB : Filter.Tendsto (fun t => ellCoeff (γ t) ^ 2) Filter.atTop (nhds L))
    (hne : ellCoeff (γ t₀) ^ 2
        + Real.sqrt ((1 - ellCoeff (γ t₀) ^ 2) ^ 2 - Hosting.potential (γ t₀)) ≠ 0) :
    L = ellCoeff (γ t₀) ^ 2
        / (ellCoeff (γ t₀) ^ 2
           + Real.sqrt ((1 - ellCoeff (γ t₀) ^ 2) ^ 2 - Hosting.potential (γ t₀))) :=
  (eq_div_iff hne).mpr (ellSq_tendsto_closed_form hd hmem hV hB)

/-! ## 8. Completeness audit (`#print axioms`)

Every declaration introduced by this file.  The gate: only
`{propext, Classical.choice, Quot.sound}` may appear. -/

#print axioms gramLo
#print axioms gramHi
#print axioms gramA
#print axioms gramC
#print axioms gramP
#print axioms ellCoeff
#print axioms gramA_def
#print axioms gramC_def
#print axioms gramP_def
#print axioms ellCoeff_def
#print axioms gramLo_coord_zero
#print axioms gramHi_coord_zero
#print axioms potential_eq_gram
#print axioms gramA_nonneg
#print axioms gramC_nonneg
#print axioms gram_sum_eq_one
#print axioms ellSq_le_one
#print axioms potential_le_one_sub_ellSq_sq
#print axioms imPart_add
#print axioms imPart_smul
#print axioms imPart_sub
#print axioms bil_cdLo_left
#print axioms bil_cdHi_left
#print axioms secVar_loOf
#print axioms secVar_hiOf
#print axioms bil_cdLo_gradV
#print axioms bil_cdHi_gradV
#print axioms gramLo_comm
#print axioms gramHi_comm_self
#print axioms comm_gramHi
#print axioms comm_gramLo_self
#print axioms bil_cdLo_gradV_gramLo
#print axioms bil_cdLo_gradV_gramHi
#print axioms bil_cdHi_gradV_gramHi
#print axioms bil_cdHi_gradV_gramLo
#print axioms cdLo_gradV_coord_zero
#print axioms cdHi_gradV_coord_zero
#print axioms gradV_coord_zero
#print axioms bil_gradV_self
#print axioms cdLo_ruleField
#print axioms cdHi_ruleField
#print axioms gramLo_ruleField
#print axioms gramHi_ruleField
#print axioms ellCoeff_ruleField
#print axioms bil_gramLo_gramLo_ruleField
#print axioms bil_gramHi_gramHi_ruleField
#print axioms bil_gramLo_gramHi_ruleField
#print axioms bil_gramLo_ruleField_gramHi
#print axioms gramLoCLM
#print axioms gramLoCLM_apply
#print axioms gramHiCLM
#print axioms gramHiCLM_apply
#print axioms ellCoeffCLM
#print axioms ellCoeffCLM_apply
#print axioms hasDerivAt_gramLo
#print axioms hasDerivAt_gramHi
#print axioms hasDerivAt_gramA_along_flow
#print axioms hasDerivAt_gramC_along_flow
#print axioms hasDerivAt_gramP_along_flow
#print axioms hasDerivAt_ellCoeff_along_flow
#print axioms hasDerivAt_ellSq_along_flow
#print axioms gram_sum_hasDerivAt_zero
#print axioms ellSq_monotone_along_flow
#print axioms IsRayCoord
#print axioms contDiff_gramLo
#print axioms contDiff_gramHi
#print axioms contDiff_gramA
#print axioms contDiff_gramC
#print axioms contDiff_gramP
#print axioms continuous_gramLo
#print axioms continuous_gramHi
#print axioms continuous_ellCoeff
#print axioms continuous_gramA
#print axioms continuous_gramC
#print axioms continuous_gramP
#print axioms isRayCoord_gramA_sub
#print axioms isRayCoord_gramC_sub
#print axioms isRayCoord_gramP
#print axioms isRayCoord_ellSq
#print axioms ray_minor_eq_zero
#print axioms gram_ray
#print axioms rayVec
#print axioms isRayCoord_rayVec
#print axioms rayVec_collinear
#print axioms quench_relation
#print axioms quench_root_pick_aux
#print axioms quench_root_pick
#print axioms quench_root_ge_initial
#print axioms stateSphere_invariant_univ
#print axioms quench_relation_univ
#print axioms ellSq_tendsto_closed_form
#print axioms ellSq_limit_ge_initial
#print axioms ellSq_limit_eq_closed_form

end QBP.Substrate.RuleFlowInvariants
