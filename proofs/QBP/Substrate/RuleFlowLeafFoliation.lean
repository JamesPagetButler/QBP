import QBP.Substrate.RuleFlowBridge
import QBP.Substrate.RuleFlowInvariants

/-!
# QBP.Substrate.RuleFlowLeafFoliation — Fixed-Leaf Closure, the 2-Plane Identity, and CASH P4 Intertwining

**Target:** Ready-to-compile Substrate module extending `QBP.Substrate.RuleFlowBridge` (#690)
and `QBP.Substrate.RuleFlowInvariants` (#635) with the four theorems underwriting the
**QBP-CU Leaf-Foliated** (`𝕊 → H_s → 𝕊`) execution engine:

1. **Theorem 1 (`ruleField_mem_kernelAlgebra`)**: Closes the pointwise gap from `∇V(s) ∈ 𝕆_s`
(#690) to the full tangent rule field `RuleFlow.ruleField s ∈ 𝕆_s`, unconditionally for all
`s : CDAlg ℝ 4` (since `(∇V s)₀ = 0` by `RuleFlowInvariants.gradV_coord_zero`).
2. **Theorem 2 (`inKernelAlgebra_fixed_leaf` & `rk4Step_mem_fixed_leaf`)**: Generalizes the
basepoint from moving `s` to a **fixed initial seed `s₀`**. Because `H_{s₀}` is a closed
subalgebra (`inQuatSpanOct_mul`, `inQuatSpanOct_conj`), `x ∈ 𝕆_{s₀} ⇒ gradV x ∈ 𝕆_{s₀}`
and `ruleField x ∈ 𝕆_{s₀}` hold by pure subalgebra closure—requiring **zero ODE existence
or Grassmannian derivative machinery**. Discrete Euler and 4-stage RK4 trajectories stay in
`𝕆_{s₀}` at every step by induction.
3. **Theorem 3 (`cdLo_gradV_eq_plane_comb` & `cdHi_gradV_eq_plane_comb`)**: Proves structurally
(from `cdAlg_sq_eq`, `cdAlg_mul_add_swap_pure`, `octonion_alternative`, and `octonion_flexible`
— zero `decide`, zero `native_decide`) the exact **2-Plane Double-Commutator Identity**:
for `a = gramLo s` and `c = gramHi s`,
* `cdLo (gradV s) = (8 * N c) • a - (8 * bil a c) • c`
* `cdHi (gradV s) = (8 * N a) • c - (8 * bil a c) • a`
Hence `∇V(s)` has **zero component along `1` and zero component along `a * c`**—it stays
strictly inside the 2D plane `span_ℝ{a, c} ⊂ Im H_s`!
4. **Theorem 4 (`liftLeaf_gradV_eq`, `liftLeaf_ruleField_eq`, `liftLeaf_rk4Step_eq`)**:
Proves the **CASH P4 Lossless Intertwining Theorem** for the QBP-CU Leaf-Foliated engine:
for any orthonormal imaginary octonion 2-frame `(u₁, u₂)` (`N u₁ = 1`, `N u₂ = 1`,
`bil u₁ u₂ = 0`), lifting a 5D leaf state `q = (a₁, a₂, c₁, c₂, b₀)` to `𝕊 = CDAlg ℝ 4`
via `liftLeaf u₁ u₂ q` intertwines `gradV`, `ruleField`, and `rk4Step` identically.

Completeness target: zero `sorry`, zero `native_decide`, axioms ⊆ `{propext, Classical.choice, Quot.sound}`.
## Provenance

From the beekeeper's MDCU document ("The Case for the Multi-Dimensional Compute Unit",
§4 "Ready-to-Compile Lean 4 Module"), 2026-10-17, Gemini & QBP/Edda collaboration; written
against QBP head `2b9e5d2`.  Built by qbp-oppenheimer for inter#197 step 1 against master
`a4d4383`.  The text above this section is the document's own header, kept verbatim; every
theorem *statement* below is the document's, unchanged.  Changes are confined to proofs, to
the `noncomputable` marker on `rk4Stage` (its body is unchanged; it uses `Real.sqrt` and
`ruleField`), and to one added helper lemma (`comm_eq_gram_comm`).

**Substrate-layer discipline** (beekeeper's lift, 2026-09-07, #473
`issuecomment-5574256922`).  *What this file hosts:* algebraic closure facts about the rule
field `RuleFlow.ruleField` and the rule's gradient `RuleFlow.gradV` (pointwise membership in
`𝕆_s`, closure of a *fixed* `𝕆_{s₀}` under `gradV`, `ruleField` and one explicit RK4
stage), the octonion double-commutator identity, the 2-plane closed form of `∇V`, and the
gradient intertwining with a 5-coordinate leaf chart.  *What this file does NOT derive:* the
rule itself (a POSTULATE, #635); existence or uniqueness of integral curves
(`FLAG-rule-flow-open`); invariance of `𝕆_s` along a *continuous* trajectory (the RK4/closure
results are statements about explicit discrete updates, not about the flow); the reverse
inclusion `ker Δ(s) ⊆ 𝕆_s`; the leaf space `G₂/SO(4)`; the anneal or the endpoint.

## Status of the document's four claims (as built)

* **Theorem 1** (`ruleField_mem_kernelAlgebra`): **PROVED as stated**, for every
  `s : CDAlg ℝ 4`, no hypothesis.  Proof repair: the name
  `smul_self_add_smul_gradV_mem_kernelAlgebra` is ambiguous under the two `open`s (the
  Foundations version is about `gradVof`, the Substrate one about `RuleFlow.gradV`, and they
  are definitionally equal, so both elaborate); qualified as `RuleFlowBridge.…`.
* **Theorem 2** (`gradV_mem_fixed_leaf`, `ruleField_mem_fixed_leaf`,
  `rk4Stage_mem_fixed_leaf`): **PROVED as stated.**  `gradV_mem_fixed_leaf` and
  `ruleField_mem_fixed_leaf` (and their component lemmas) compiled unchanged.  Repairs:
  `rk4Stage` marked `noncomputable`; the `rk4Stage_mem_fixed_leaf` proof rewritten (the
  document's `dsimp [rk4Stage]` unfolded `N` into coordinate sums and left `_` placeholders
  unsynthesizable; a single closing `exact` on the zeta-reduced goal timed out in `isDefEq`)
  as `unfold rk4Stage; lift_lets; intro …` followed by stage-by-stage closure.  The header's
  names `inKernelAlgebra_fixed_leaf` and `rk4Step_mem_fixed_leaf`, and its "Discrete Euler …
  trajectories stay in `𝕆_{s₀}` at every step by induction", have **no Lean counterpart in
  the module text**: what is in Lean is closure under ONE RK4 stage (multi-step iteration
  and an Euler step are not stated).
* **Theorem 3** (`octonion_double_comm_pure`, `cdLo_gradV_eq_plane_comb`,
  `cdHi_gradV_eq_plane_comb`): **PROVED as stated.**  Repairs: `sq_eq_neg_N_one` needed a
  closing `neg_smul` (`-(N y • 1)` vs `-N y • 1`); `mul_right_self_pure`,
  `mul_left_self_pure` drop the inapplicable `cd_mul_neg`/`cd_neg_mul` rewrites (the
  negation sits on the scalar); `mul_swap_self_pure` uses `module` instead of `abel` for the
  scalar-negation step and closes with `module`; the `hcomm` steps of 3a/3b (whose
  `rw [← gramLo_comm, ← comm_gramHi]`/`exact cdComm_eq_comm_imHi _` failed or timed out)
  are replaced by the added helper `comm_eq_gram_comm` (`[a, b] = [Im a, Im b]`, via
  `gramLo_comm` and `InFlightAlgebra.comm_smul_one_add`).  `octonion_double_comm_pure` and
  the rest of 3a/3b compiled unchanged.
* **Theorem 4** (`liftLeaf_gradV_eq`): **PROVED as stated.**  Repairs: the `hlo`/`hhi`
  `simp` calls replaced by explicit `rw` chains through `cdLo_loOf`/`cdLo_hiOf`/
  `cdHi_loOf`/`cdHi_hiOf` and `imPart_one`; `N_smul` qualified as
  `NoAutonomousDynamics.N_smul` (unqualified name not in scope); `hbil` via `simp only`
  bilinearity then the frame rewrites; the final step compares Cayley–Dickson halves with
  `CrystalHosting.eq_of_halves` (the document's `rw [gradV, …]` unfolded `gradV` and then
  found no `cdLo (gradV _)` to rewrite).  The header's `liftLeaf_ruleField_eq` and
  `liftLeaf_rk4Step_eq` are **not in the module text** (no Lean statement); `potentialLeaf`
  and `ruleFieldLeaf` are defined but no theorem relates them to `Hosting.potential` /
  `ruleField`.  Only the **gradient** intertwining is proved.

No `sorry`, no `native_decide`, no new axioms; `#print axioms` audit in §5.
-/

namespace QBP.Substrate.RuleFlowLeafFoliation

open QBP.Foundations QBP.Foundations.CDAlg
open QBP.Foundations.InFlightAlgebra
open QBP.Substrate.RuleFlow
open QBP.Substrate.RuleFlowBridge
open QBP.Substrate.RuleFlowInvariants

/-! ## 1. Theorem 1 — Pointwise Rule Field Membership `F(s) ∈ 𝕆_s` -/

/-- The rule field `F(s)` equals `(4 * V(s)) • s - ∇V(s)` for every sedenion `s`
(no state-sphere hypothesis needed, since `(∇V s)₀ = 0` and `⟪∇V s, s⟫ = 4 V(s)`
hold on all of `CDAlg ℝ 4`). -/
theorem ruleField_eq_smul_sub_gradV (s : CDAlg ℝ 4) :
    ruleField s = (4 * Hosting.potential s) • s - gradV s := by
  rw [ruleField, bil_gradV_self, gradV_coord_zero, zero_smul, sub_zero]
  abel

/-- **Theorem 1 (`F(s) ∈ 𝕆_s`).** For every sedenion `s : CDAlg ℝ 4`, the tangent
rule field `RuleFlow.ruleField s` lies in the host kernel algebra
`𝕆_s = H_s ⊕ H_s·ℓ`. Closes the `ARGUMENT` tag on row 8 of
`688-in-flight-definition-2026-09-29.md` §1. -/
theorem ruleField_mem_kernelAlgebra (s : CDAlg ℝ 4) :
    InKernelAlgebra s (ruleField s) := by
  have h : ruleField s = (4 * Hosting.potential s) • s + (-1 : ℝ) • gradV s := by
    rw [ruleField_eq_smul_sub_gradV, neg_one_smul, sub_eq_add_neg]
  rw [h]
  exact RuleFlowBridge.smul_self_add_smul_gradV_mem_kernelAlgebra s (4 * Hosting.potential s) (-1)

/-! ## 2. Theorem 2 — Fixed-Leaf Subalgebra Closure (`∀ x ∈ 𝕆_{s₀}, F(x) ∈ 𝕆_{s₀}`) -/

/-- If `x ∈ 𝕆_{s₀}` (with fixed basepoint `s₀`), then the commutator
`cdComm x = cdLo x * cdHi x - cdHi x * cdLo x` lies in the fixed host
quaternion algebra `H_{s₀} = span_ℝ{1, cdLo s₀, imHi s₀, cdLo s₀ * imHi s₀}`. -/
theorem cdComm_mem_fixed_hostQuat {s₀ x : CDAlg ℝ 4}
    (hx : InKernelAlgebra s₀ x) :
    InQuatSpanOct (cdLo s₀) (imHi s₀) (cdComm x) := by
  rw [cdComm_def]
  exact inQuatSpanOct_sub
    (inQuatSpanOct_mul hx.1 hx.2)
    (inQuatSpanOct_mul hx.2 hx.1)

/-- If `x ∈ 𝕆_{s₀}`, then `cdLo (gradV x) ∈ H_{s₀}`. -/
theorem cdLo_gradV_mem_fixed_hostQuat {s₀ x : CDAlg ℝ 4}
    (hx : InKernelAlgebra s₀ x) :
    InQuatSpanOct (cdLo s₀) (imHi s₀) (cdLo (gradV x)) := by
  rw [← gradVlo_eq_cdLo_gradV, gradVlo_def]
  have hC := cdComm_mem_fixed_hostQuat hx
  have hb := inQuatSpanOct_conj hx.2
  exact inQuatSpanOct_smul (2 : ℝ)
    (inQuatSpanOct_sub (inQuatSpanOct_mul hC hb) (inQuatSpanOct_mul hb hC))

/-- If `x ∈ 𝕆_{s₀}`, then `cdHi (gradV x) ∈ H_{s₀}`. -/
theorem cdHi_gradV_mem_fixed_hostQuat {s₀ x : CDAlg ℝ 4}
    (hx : InKernelAlgebra s₀ x) :
    InQuatSpanOct (cdLo s₀) (imHi s₀) (cdHi (gradV x)) := by
  rw [← gradVhi_eq_cdHi_gradV, gradVhi_def]
  have hC := cdComm_mem_fixed_hostQuat hx
  have ha := inQuatSpanOct_conj hx.1
  exact inQuatSpanOct_smul (2 : ℝ)
    (inQuatSpanOct_sub (inQuatSpanOct_mul ha hC) (inQuatSpanOct_mul hC ha))

/-- **Theorem 2a (`gradV` preserves any fixed leaf `𝕆_{s₀}`).**
For any fixed seed `s₀` and any state `x ∈ 𝕆_{s₀}`, `gradV x ∈ 𝕆_{s₀}`. -/
theorem gradV_mem_fixed_leaf {s₀ x : CDAlg ℝ 4}
    (hx : InKernelAlgebra s₀ x) :
    InKernelAlgebra s₀ (gradV x) :=
  ⟨cdLo_gradV_mem_fixed_hostQuat hx, cdHi_gradV_mem_fixed_hostQuat hx⟩

/-- **Theorem 2b (`ruleField` preserves any fixed leaf `𝕆_{s₀}`).**
For any fixed seed `s₀` and any state `x ∈ 𝕆_{s₀}`, `ruleField x ∈ 𝕆_{s₀}`. -/
theorem ruleField_mem_fixed_leaf {s₀ x : CDAlg ℝ 4}
    (hx : InKernelAlgebra s₀ x) :
    InKernelAlgebra s₀ (ruleField x) := by
  have h : ruleField x = (4 * Hosting.potential x) • x + (-1 : ℝ) • gradV x := by
    rw [ruleField_eq_smul_sub_gradV, neg_one_smul, sub_eq_add_neg]
  rw [h]
  exact inKernelAlgebra_add
    (inKernelAlgebra_smul (4 * Hosting.potential x) hx)
    (inKernelAlgebra_smul (-1 : ℝ) (gradV_mem_fixed_leaf hx))

/-- **Theorem 2c (Discrete Euler & RK4 steps preserve the fixed initial leaf `𝕆_{s₀}`).** -/
noncomputable def rk4Stage (x : CDAlg ℝ 4) (h : ℝ) : CDAlg ℝ 4 :=
  let k1 := ruleField x
  let x2 := (N (x + (h / 2) • k1))⁻¹.sqrt • (x + (h / 2) • k1)
  let k2 := ruleField x2
  let x3 := (N (x + (h / 2) • k2))⁻¹.sqrt • (x + (h / 2) • k2)
  let k3 := ruleField x3
  let x4 := (N (x + h • k3))⁻¹.sqrt • (x + h • k3)
  let k4 := ruleField x4
  let raw := x + (h / 6) • (k1 + (2 : ℝ) • k2 + (2 : ℝ) • k3 + k4)
  (N raw)⁻¹.sqrt • raw

theorem rk4Stage_mem_fixed_leaf {s₀ x : CDAlg ℝ 4} (h : ℝ)
    (hx : InKernelAlgebra s₀ x) :
    InKernelAlgebra s₀ (rk4Stage x h) := by
  -- Proof repair: the document's `dsimp [rk4Stage]` unfolded `N` into coordinate
  -- sums, its `_` placeholders could not be synthesized, and closing the zeta-reduced
  -- goal with one `exact` sent `isDefEq` into unfolding `ruleField`/`gradV` (heartbeat
  -- timeout).  Instead lift the `let`s to the top of the goal (`lift_lets`), introduce
  -- them as local definitions, and close each stage by the closure combinators.
  unfold rk4Stage
  lift_lets
  intro k1 x2 k2 x3 k3 x4 k4 raw
  have hk1 : InKernelAlgebra s₀ k1 := ruleField_mem_fixed_leaf hx
  have hx2 : InKernelAlgebra s₀ x2 :=
    inKernelAlgebra_smul _ (inKernelAlgebra_add hx (inKernelAlgebra_smul _ hk1))
  have hk2 : InKernelAlgebra s₀ k2 := ruleField_mem_fixed_leaf hx2
  have hx3 : InKernelAlgebra s₀ x3 :=
    inKernelAlgebra_smul _ (inKernelAlgebra_add hx (inKernelAlgebra_smul _ hk2))
  have hk3 : InKernelAlgebra s₀ k3 := ruleField_mem_fixed_leaf hx3
  have hx4 : InKernelAlgebra s₀ x4 :=
    inKernelAlgebra_smul _ (inKernelAlgebra_add hx (inKernelAlgebra_smul _ hk3))
  have hk4 : InKernelAlgebra s₀ k4 := ruleField_mem_fixed_leaf hx4
  have hraw : InKernelAlgebra s₀ raw :=
    inKernelAlgebra_add hx (inKernelAlgebra_smul _
      (inKernelAlgebra_add (inKernelAlgebra_add (inKernelAlgebra_add hk1
        (inKernelAlgebra_smul _ hk2)) (inKernelAlgebra_smul _ hk3)) hk4))
  exact inKernelAlgebra_smul _ hraw

/-! ## 3. Theorem 3 — The 2-Plane Double-Commutator Identity in `𝕆 = CDAlg ℝ 3` -/

/-- For an imaginary octonion `y` (`y.coord 0 = 0`), `y * y = -(N y) • 1`. -/
theorem sq_eq_neg_N_one {y : CDAlg ℝ 3} (hy : y.coord 0 = 0) :
    y * y = - (N y) • (1 : CDAlg ℝ 3) := by
  rw [cdAlg_sq_eq, hy, mul_zero, zero_smul, zero_sub, neg_smul]

/-- Right-multiplying `x * y` by imaginary `y` collapses to `-(N y) • x` via
right-alternativity `(x * y) * y = x * (y * y)`. -/
theorem mul_right_self_pure (x : CDAlg ℝ 3) {y : CDAlg ℝ 3} (hy : y.coord 0 = 0) :
    (x * y) * y = - (N y) • x := by
  rw [(octonion_alternative x y).2, sq_eq_neg_N_one hy, mul_smul_right, cd_mul_one]

/-- Left-multiplying `y * x` by imaginary `y` collapses to `-(N y) • x` via
left-alternativity `y * (y * x) = (y * y) * x`. -/
theorem mul_left_self_pure (x : CDAlg ℝ 3) {y : CDAlg ℝ 3} (hy : y.coord 0 = 0) :
    y * (y * x) = - (N y) • x := by
  rw [← (octonion_alternative y x).1, sq_eq_neg_N_one hy, mul_smul_left, cd_one_mul]

/-- For imaginary octonions `x, y`, `(y * x) * y = (N y) • x - (2 * bil x y) • y`
via the pure swap identity `x * y + y * x = -(2 * bil x y) • 1`. -/
theorem mul_swap_self_pure {x y : CDAlg ℝ 3} (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) :
    (y * x) * y = (N y) • x - (2 * bil x y) • y := by
  have hswap : y * x = - (x * y) - (2 * bil x y) • (1 : CDAlg ℝ 3) := by
    have h := cdAlg_mul_add_swap_pure x y hx hy
    calc y * x = (x * y + y * x) - x * y := by abel
      _ = - (2 * bil x y) • (1 : CDAlg ℝ 3) - x * y := by rw [h]
      _ = - (x * y) - (2 * bil x y) • (1 : CDAlg ℝ 3) := by module
  rw [hswap, CrystalHosting.cd_sub_mul, CrystalHosting.cd_neg_mul,
    mul_right_self_pure x hy, mul_smul_left, cd_one_mul]
  module

/-- **Core Octonion Double-Commutator Identity.**
For any imaginary octonions `x, y : CDAlg ℝ 3` (`x.coord 0 = 0`, `y.coord 0 = 0`),
the double commutator `[[x, y], y] = (x*y - y*x)*y - y*(x*y - y*x)` lies strictly in
the 2-plane `span_ℝ{x, y}`:
`(x * y - y * x) * y - y * (x * y - y * x) = -(4 * N y) • x + (4 * bil x y) • y`. -/
theorem octonion_double_comm_pure {x y : CDAlg ℝ 3}
    (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) :
    (x * y - y * x) * y - y * (x * y - y * x)
      = - (4 * N y) • x + (4 * bil x y) • y := by
  rw [CrystalHosting.cd_sub_mul, CrystalHosting.cd_mul_sub,
    ← octonion_flexible y x,
    mul_right_self_pure x hy,
    mul_left_self_pure x hy,
    mul_swap_self_pure hx hy]
  module

/-- `C(s) = [a, b] = [Im a, Im b]`: the real parts of both CD components are central
and drop out of the commutator.  (Helper added in proof repair.) -/
theorem comm_eq_gram_comm (s : CDAlg ℝ 4) :
    comm s = gramLo s * gramHi s - gramHi s * gramLo s := by
  have hb : ((cdHi s).coord 0) • (1 : CDAlg ℝ 3) + gramHi s = cdHi s := by
    rw [gramHi, imPart_def]; abel
  rw [← gramLo_comm, ← comm_smul_one_add (gramLo s) (gramHi s) ((cdHi s).coord 0), hb]

/-- **Theorem 3a (`cdLo (gradV s)` 2-Plane Formula).**
For EVERY sedenion `s : CDAlg ℝ 4` (no imaginarity or norm hypothesis!), writing
`a = gramLo s = imPart (cdLo s)` and `c = gramHi s = imPart (cdHi s)`:
`cdLo (gradV s) = (8 * N c) • a - (8 * bil a c) • c`. -/
theorem cdLo_gradV_eq_plane_comb (s : CDAlg ℝ 4) :
    cdLo (gradV s) = (8 * N (gramHi s)) • gramLo s - (8 * bil (gramLo s) (gramHi s)) • gramHi s := by
  have ha : (gramLo s).coord 0 = 0 := gramLo_coord_zero s
  have hc : (gramHi s).coord 0 = 0 := gramHi_coord_zero s
  have hcomm : comm s = gramLo s * gramHi s - gramHi s * gramLo s := comm_eq_gram_comm s
  have hconj : conj (cdHi s) = ((cdHi s).coord 0) • (1 : CDAlg ℝ 3) - gramHi s := by
    rw [conj_eq_sub, gramHi, imPart_def]; module
  rw [cdLo_gradV, hcomm, hconj]
  -- Central scalar `(cdHi s).coord 0 • 1` drops out of commutator with `C`, leaving `-gramHi s`
  have hdrop : ∀ C : CDAlg ℝ 3,
      C * (((cdHi s).coord 0) • (1 : CDAlg ℝ 3) - gramHi s)
        - (((cdHi s).coord 0) • (1 : CDAlg ℝ 3) - gramHi s) * C
        = - (C * gramHi s - gramHi s * C) := by
    intro C
    rw [CrystalHosting.cd_mul_sub, CrystalHosting.cd_sub_mul,
      mul_smul_right, mul_smul_left, cd_mul_one, cd_one_mul]
    abel
  rw [hdrop, smul_neg, octonion_double_comm_pure ha hc]
  module

/-- **Theorem 3b (`cdHi (gradV s)` 2-Plane Formula).**
For EVERY sedenion `s : CDAlg ℝ 4`, writing `a = gramLo s` and `c = gramHi s`:
`cdHi (gradV s) = (8 * N a) • c - (8 * bil a c) • a`. -/
theorem cdHi_gradV_eq_plane_comb (s : CDAlg ℝ 4) :
    cdHi (gradV s) = (8 * N (gramLo s)) • gramHi s - (8 * bil (gramLo s) (gramHi s)) • gramLo s := by
  have ha : (gramLo s).coord 0 = 0 := gramLo_coord_zero s
  have hc : (gramHi s).coord 0 = 0 := gramHi_coord_zero s
  have hcomm : comm s = - (gramHi s * gramLo s - gramLo s * gramHi s) := by
    have h1 : comm s = gramLo s * gramHi s - gramHi s * gramLo s := comm_eq_gram_comm s
    rw [h1]; abel
  have hconj : conj (cdLo s) = ((cdLo s).coord 0) • (1 : CDAlg ℝ 3) - gramLo s := by
    rw [conj_eq_sub, gramLo, imPart_def]; module
  rw [cdHi_gradV, hcomm, hconj]
  have hdrop : ∀ C : CDAlg ℝ 3,
      (((cdLo s).coord 0) • (1 : CDAlg ℝ 3) - gramLo s) * (-C)
        - (-C) * (((cdLo s).coord 0) • (1 : CDAlg ℝ 3) - gramLo s)
        = - (C * gramLo s - gramLo s * C) := by
    intro C
    rw [CrystalHosting.cd_mul_neg, CrystalHosting.cd_neg_mul,
      CrystalHosting.cd_sub_mul, CrystalHosting.cd_mul_sub,
      mul_smul_left, mul_smul_right, cd_one_mul, cd_mul_one]
    abel
  rw [hdrop, smul_neg, octonion_double_comm_pure hc ha]
  have hsymm : bil (gramHi s) (gramLo s) = bil (gramLo s) (gramHi s) := NormForm.bil_symm _ _
  rw [hsymm]
  module

/-! ## 4. Theorem 4 — CASH P4 Lossless Intertwining (`S → 5D Leaf → S`) -/

/-- A 5-component leaf state `q = (a₁, a₂, c₁, c₂, b₀)` representing coordinates
along an orthonormal imaginary 2-frame `(u₁, u₂)` plus the `ℓ` component `b₀`. -/
structure LeafState where
  a1 : ℝ
  a2 : ℝ
  c1 : ℝ
  c2 : ℝ
  b0 : ℝ

/-- `QJOIN` (`liftLeaf`): Embeds a 5D `LeafState` into `𝕊 = CDAlg ℝ 4` given an
orthonormal imaginary 2-frame `(u₁, u₂)` in `𝕆 = CDAlg ℝ 3`. -/
def liftLeaf (u1 u2 : CDAlg ℝ 3) (q : LeafState) : CDAlg ℝ 4 :=
  loOf (q.a1 • u1 + q.a2 • u2) + hiOf (q.b0 • (1 : CDAlg ℝ 3) + q.c1 • u1 + q.c2 • u2)

/-- Leaf potential `V_leaf(q) = 4 * (a₁ c₂ - a₂ c₁)^2`. -/
def potentialLeaf (q : LeafState) : ℝ :=
  4 * (q.a1 * q.c2 - q.a2 * q.c1) ^ 2

/-- Leaf gradient in the 5D leaf coordinates (zero `OMUL`s!). -/
def gradVLeaf (q : LeafState) : LeafState :=
  let det := q.a1 * q.c2 - q.a2 * q.c1
  { a1 := 8 * det * q.c2
    a2 := -8 * det * q.c1
    c1 := -8 * det * q.a2
    c2 := 8 * det * q.a1
    b0 := 0 }

/-- Leaf tangent rule field `F_leaf(q) = 4 V_leaf(q) • q - gradVLeaf(q)`. -/
def ruleFieldLeaf (q : LeafState) : LeafState :=
  let v4 := 4 * potentialLeaf q
  let g := gradVLeaf q
  { a1 := v4 * q.a1 - g.a1
    a2 := v4 * q.a2 - g.a2
    c1 := v4 * q.c1 - g.c1
    c2 := v4 * q.c2 - g.c2
    b0 := v4 * q.b0 }

@[simp] theorem imPart_one {n : ℕ} : imPart (1 : CDAlg ℝ n) = 0 := by
  rw [imPart_def, one_coord, if_pos rfl, one_smul, sub_self]

/-- **Theorem 4a (Gradient Intertwining / CASH P4 Gate Reflection).**
For any orthonormal imaginary 2-frame `(u₁, u₂)` in `𝕆` (`u₁.coord 0 = 0`,
`u₂.coord 0 = 0`, `N u₁ = 1`, `N u₂ = 1`, `bil u₁ u₂ = 0`), the 16D sedenion
gradient of the lifted state equals the lift of the 5D leaf gradient:
`gradV (liftLeaf u₁ u₂ q) = liftLeaf u₁ u₂ (gradVLeaf q)`. -/
theorem liftLeaf_gradV_eq {u1 u2 : CDAlg ℝ 3}
    (hu1_im : u1.coord 0 = 0) (hu2_im : u2.coord 0 = 0)
    (hu1_N : N u1 = 1) (hu2_N : N u2 = 1) (hu12_orth : bil u1 u2 = 0)
    (q : LeafState) :
    gradV (liftLeaf u1 u2 q) = liftLeaf u1 u2 (gradVLeaf q) := by
  have hlo : gramLo (liftLeaf u1 u2 q) = q.a1 • u1 + q.a2 • u2 := by
    rw [gramLo, liftLeaf, cdLo_add, CrystalHosting.cdLo_loOf, CrystalHosting.cdLo_hiOf, add_zero,
      imPart_add, imPart_smul, imPart_smul, imPart_eq_self hu1_im, imPart_eq_self hu2_im]
  have hhi : gramHi (liftLeaf u1 u2 q) = q.c1 • u1 + q.c2 • u2 := by
    rw [gramHi, liftLeaf, cdHi_add, CrystalHosting.cdHi_loOf, CrystalHosting.cdHi_hiOf, zero_add,
      imPart_add, imPart_add, imPart_smul, imPart_smul, imPart_smul, imPart_one, smul_zero,
      zero_add, imPart_eq_self hu1_im, imPart_eq_self hu2_im]
  have hNa : N (gramLo (liftLeaf u1 u2 q)) = q.a1 ^ 2 + q.a2 ^ 2 := by
    rw [hlo, N_add, NoAutonomousDynamics.N_smul, NoAutonomousDynamics.N_smul, bil_smul_left, bil_smul_right, hu1_N, hu2_N, hu12_orth]
    ring
  have hNc : N (gramHi (liftLeaf u1 u2 q)) = q.c1 ^ 2 + q.c2 ^ 2 := by
    rw [hhi, N_add, NoAutonomousDynamics.N_smul, NoAutonomousDynamics.N_smul, bil_smul_left, bil_smul_right, hu1_N, hu2_N, hu12_orth]
    ring
  have hbil : bil (gramLo (liftLeaf u1 u2 q)) (gramHi (liftLeaf u1 u2 q))
      = q.a1 * q.c1 + q.a2 * q.c2 := by
    rw [hlo, hhi]
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right]
    rw [← N_eq_bil u1, ← N_eq_bil u2, NormForm.bil_symm u2 u1, hu1_N, hu2_N, hu12_orth]
    ring
  -- Proof repair: compare the two Cayley–Dickson halves (`eq_of_halves`) instead of
  -- unfolding `gradV`; each half is a coefficient identity on `span_ℝ{u₁, u₂}`.
  apply CrystalHosting.eq_of_halves
  · rw [cdLo_gradV_eq_plane_comb, hNc, hbil, hlo, hhi, liftLeaf, cdLo_add,
      CrystalHosting.cdLo_loOf, CrystalHosting.cdLo_hiOf, add_zero]
    simp only [gradVLeaf]
    module
  · rw [cdHi_gradV_eq_plane_comb, hNa, hbil, hlo, hhi, liftLeaf, cdHi_add,
      CrystalHosting.cdHi_loOf, CrystalHosting.cdHi_hiOf, zero_add]
    simp only [gradVLeaf, zero_smul, zero_add]
    module

/-! ## 5. Completeness audit — `#print axioms` -/

#print axioms ruleField_mem_kernelAlgebra
#print axioms gradV_mem_fixed_leaf
#print axioms ruleField_mem_fixed_leaf
#print axioms rk4Stage_mem_fixed_leaf
#print axioms octonion_double_comm_pure
#print axioms cdLo_gradV_eq_plane_comb
#print axioms cdHi_gradV_eq_plane_comb
#print axioms liftLeaf_gradV_eq

-- Audit of the supporting lemmas (added at build time so that every theorem in the
-- module is covered, not only the headline ones).
#print axioms ruleField_eq_smul_sub_gradV
#print axioms cdComm_mem_fixed_hostQuat
#print axioms cdLo_gradV_mem_fixed_hostQuat
#print axioms cdHi_gradV_mem_fixed_hostQuat
#print axioms sq_eq_neg_N_one
#print axioms mul_right_self_pure
#print axioms mul_left_self_pure
#print axioms mul_swap_self_pure
#print axioms comm_eq_gram_comm
#print axioms imPart_one

end QBP.Substrate.RuleFlowLeafFoliation
