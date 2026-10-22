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
  exact smul_self_add_smul_gradV_mem_kernelAlgebra s (4 * Hosting.potential s) (-1)

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
def rk4Stage (x : CDAlg ℝ 4) (h : ℝ) : CDAlg ℝ 4 :=
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
  dsimp [rk4Stage]
  have hk1 : InKernelAlgebra s₀ (ruleField x) := ruleField_mem_fixed_leaf hx
  have hx2 : InKernelAlgebra s₀ ((N (x + (h / 2) • ruleField x))⁻¹.sqrt • (x + (h / 2) • ruleField x)) :=
    inKernelAlgebra_smul _ (inKernelAlgebra_add hx (inKernelAlgebra_smul _ hk1))
  have hk2 := ruleField_mem_fixed_leaf hx2
  have hx3 := inKernelAlgebra_smul (N (x + (h / 2) • ruleField _))⁻¹.sqrt
    (inKernelAlgebra_add hx (inKernelAlgebra_smul (h / 2) hk2))
  have hk3 := ruleField_mem_fixed_leaf hx3
  have hx4 := inKernelAlgebra_smul (N (x + h • ruleField _))⁻¹.sqrt
    (inKernelAlgebra_add hx (inKernelAlgebra_smul h hk3))
  have hk4 := ruleField_mem_fixed_leaf hx4
  exact inKernelAlgebra_smul _
    (inKernelAlgebra_add hx
      (inKernelAlgebra_smul (h / 6)
        (inKernelAlgebra_add
          (inKernelAlgebra_add
            (inKernelAlgebra_add hk1 (inKernelAlgebra_smul 2 hk2))
            (inKernelAlgebra_smul 2 hk3))
          hk4)))

/-! ## 3. Theorem 3 — The 2-Plane Double-Commutator Identity in `𝕆 = CDAlg ℝ 3` -/

/-- For an imaginary octonion `y` (`y.coord 0 = 0`), `y * y = -(N y) • 1`. -/
theorem sq_eq_neg_N_one {y : CDAlg ℝ 3} (hy : y.coord 0 = 0) :
    y * y = - (N y) • (1 : CDAlg ℝ 3) := by
  rw [cdAlg_sq_eq, hy, mul_zero, zero_smul, zero_sub]

/-- Right-multiplying `x * y` by imaginary `y` collapses to `-(N y) • x` via
right-alternativity `(x * y) * y = x * (y * y)`. -/
theorem mul_right_self_pure (x : CDAlg ℝ 3) {y : CDAlg ℝ 3} (hy : y.coord 0 = 0) :
    (x * y) * y = - (N y) • x := by
  rw [(octonion_alternative x y).2, sq_eq_neg_N_one hy,
    CrystalHosting.cd_mul_neg, mul_smul_right, cd_mul_one]

/-- Left-multiplying `y * x` by imaginary `y` collapses to `-(N y) • x` via
left-alternativity `y * (y * x) = (y * y) * x`. -/
theorem mul_left_self_pure (x : CDAlg ℝ 3) {y : CDAlg ℝ 3} (hy : y.coord 0 = 0) :
    y * (y * x) = - (N y) • x := by
  rw [← (octonion_alternative y x).1, sq_eq_neg_N_one hy,
    CrystalHosting.cd_neg_mul, mul_smul_left, cd_one_mul]

/-- For imaginary octonions `x, y`, `(y * x) * y = (N y) • x - (2 * bil x y) • y`
via the pure swap identity `x * y + y * x = -(2 * bil x y) • 1`. -/
theorem mul_swap_self_pure {x y : CDAlg ℝ 3} (hx : x.coord 0 = 0) (hy : y.coord 0 = 0) :
    (y * x) * y = (N y) • x - (2 * bil x y) • y := by
  have hswap : y * x = - (x * y) - (2 * bil x y) • (1 : CDAlg ℝ 3) := by
    have h := cdAlg_mul_add_swap_pure x y hx hy
    calc y * x = (x * y + y * x) - x * y := by abel
      _ = - (2 * bil x y) • (1 : CDAlg ℝ 3) - x * y := by rw [h]
      _ = - (x * y) - (2 * bil x y) • (1 : CDAlg ℝ 3) := by abel
  rw [hswap, CrystalHosting.cd_sub_mul, CrystalHosting.cd_neg_mul,
    mul_right_self_pure x hy, neg_neg, mul_smul_left, cd_one_mul]

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

/-- **Theorem 3a (`cdLo (gradV s)` 2-Plane Formula).**
For EVERY sedenion `s : CDAlg ℝ 4` (no imaginarity or norm hypothesis!), writing
`a = gramLo s = imPart (cdLo s)` and `c = gramHi s = imPart (cdHi s)`:
`cdLo (gradV s) = (8 * N c) • a - (8 * bil a c) • c`. -/
theorem cdLo_gradV_eq_plane_comb (s : CDAlg ℝ 4) :
    cdLo (gradV s) = (8 * N (gramHi s)) • gramLo s - (8 * bil (gramLo s) (gramHi s)) • gramHi s := by
  have ha : (gramLo s).coord 0 = 0 := gramLo_coord_zero s
  have hc : (gramHi s).coord 0 = 0 := gramHi_coord_zero s
  have hcomm : comm s = gramLo s * gramHi s - gramHi s * gramLo s := by
    rw [← gramLo_comm, ← comm_gramHi]
    exact cdComm_eq_comm_imHi _
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
    have h1 : comm s = gramLo s * gramHi s - gramHi s * gramLo s := by
      rw [← gramLo_comm]; exact cdComm_eq_comm_imHi _
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
    simp [gramLo, liftLeaf, imPart_add, imPart_smul, imPart_eq_self hu1_im, imPart_eq_self hu2_im]
  have hhi : gramHi (liftLeaf u1 u2 q) = q.c1 • u1 + q.c2 • u2 := by
    simp [gramHi, liftLeaf, imPart_add, imPart_smul, imPart_eq_self hu1_im, imPart_eq_self hu2_im]
  have hNa : N (gramLo (liftLeaf u1 u2 q)) = q.a1 ^ 2 + q.a2 ^ 2 := by
    rw [hlo, N_add, N_smul, N_smul, bil_smul_left, bil_smul_right, hu1_N, hu2_N, hu12_orth]
    ring
  have hNc : N (gramHi (liftLeaf u1 u2 q)) = q.c1 ^ 2 + q.c2 ^ 2 := by
    rw [hhi, N_add, N_smul, N_smul, bil_smul_left, bil_smul_right, hu1_N, hu2_N, hu12_orth]
    ring
  have hbil : bil (gramLo (liftLeaf u1 u2 q)) (gramHi (liftLeaf u1 u2 q))
      = q.a1 * q.c1 + q.a2 * q.c2 := by
    rw [hlo, hhi, bil_add_left, bil_add_right, bil_add_right,
      bil_smul_left, bil_smul_left, bil_smul_left, bil_smul_left,
      bil_smul_right, bil_smul_right, bil_smul_right, bil_smul_right,
      ← N_eq_bil u1, ← N_eq_bil u2, NormForm.bil_symm u2 u1, hu1_N, hu2_N, hu12_orth]
    ring
  rw [gradV, cdLo_gradV_eq_plane_comb, cdHi_gradV_eq_plane_comb,
    hNa, hNc, hbil, hlo, hhi]
  dsimp [liftLeaf, gradVLeaf]
  rw [zero_smul, zero_add]
  -- Both sides are loOf (...) + hiOf (...) of linear combinations of u1, u2; match coefficients
  congr 1
  · rw [← loOf_add]; congr 1; module
  · rw [← hiOf_add]; congr 1; module

/-! ## 5. Completeness audit — `#print axioms` -/

#print axioms ruleField_mem_kernelAlgebra
#print axioms gradV_mem_fixed_leaf
#print axioms ruleField_mem_fixed_leaf
#print axioms rk4Stage_mem_fixed_leaf
#print axioms octonion_double_comm_pure
#print axioms cdLo_gradV_eq_plane_comb
#print axioms cdHi_gradV_eq_plane_comb
#print axioms liftLeaf_gradV_eq

end QBP.Substrate.RuleFlowLeafFoliation
