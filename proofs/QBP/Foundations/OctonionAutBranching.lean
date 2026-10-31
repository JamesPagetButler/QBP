/-
  QBP.Foundations.Goal — cost-calibration target (node INSIGHT-octonion-quaternion-branching)
  =============================================================================================

  DO NOT MODIFY the definitions/lemmas above the "TARGET THEOREMS" marker — they are
  locked infrastructure, fully proved (zero sorry), needed only to STATE the target
  theorems. Arms may add auxiliary private lemmas of their own below the marker if
  useful, but the three theorem SIGNATURES must not change, and the locked section
  must not change.

  ## What this formalizes

  `𝕆 = CDAlg ℝ 3` splits via the Cayley–Dickson doubling recursion as a pair of
  quaternions `ℍ = CDAlg ℝ 2`: every octonion `x` decomposes as `x = (oLo x, oHi x)`
  with `oLo x, oHi x : CDAlg ℝ 2` (low half / high half of the 8 coordinates,
  matching the codebase's `mulCoeff` doubling `(a,b)(c,d) = (ac − d̄b, da + bc̄)`,
  see `QBP.Foundations.CDAlg` header).

  For unit quaternions `a b : CDAlg ℝ 2` (i.e. `N a = 1`, `N b = 1`), define the
  classical `SO(4) ⊂ Aut(𝕆)` map
      γ(a,b)(x1,x2) = (a·x1·ā, b·x2·ā)
  packaged directly on coordinates (`gamma` below). This is the genuine two-parameter
  octonion-automorphism family whose existence is *the* reason `Aut(𝕆) = G2` properly
  contains a copy of `Spin(4)`: it fixes the hosted quaternion subalgebra `{x | oHi x
  = 0}` setwise, and — the hard, non-vacuous fact, `gamma_mul` — is multiplicative on
  ALL of 𝕆, even though 𝕆 itself is not associative. The proof of multiplicativity
  goes through the actual four-term Cayley–Dickson expansion of `(x*y)` into
  `oLo`/`oHi` parts and uses ONLY associativity of ℍ (`CDAlg ℝ 2`, a genuine `Ring`,
  `QBP.Foundations.CDBridge.instRingTwo`) — never associativity of 𝕆 itself (which
  does not hold, cf. `Artin.lean`, `Breakdown.lean`).

  Ingredients confirmed present in this worktree at master (pre-flight, see run
  manifest): `CDAut` (`CrystalHosting.lean:678`), `quatSpan_assoc`
  (`InFlightAlgebra.lean:257`), `octonion_artin` (`Artin.lean:77`),
  `cdAlg_mul_add_swap` (`ArtinTrace.lean:86`, used via `ArtinSpan.lean`). Arms are
  free (not required) to use these, `instRingTwo`, `cdAlg2_norm_composition`, or any
  other lemma in the tree.

  Completeness bar for THIS file (grading, see run manifest §Step 5): `gamma_mul` and
  `gamma_fixes_hosted` must be proved with NO `sorry`, no `native_decide`, no new
  `axiom`, `#print axioms` closure ⊆ {propext, Classical.choice, Quot.sound}, and
  the proof of `gamma_mul` must not assume/derive general associativity of
  `CDAlg ℝ 3`. `gamma_id_iff` is optional stretch.
-/
import QBP.Foundations.CrystalHosting

/-!
# QBP.Foundations.OctonionAutBranching — the `SO(4)` family `γ(a,b)` inside `Aut(𝕆)`

The comment block above the `import` is the **verbatim header of the calibration stub**
(kept unchanged for provenance; its "DO NOT MODIFY" / grading language refers to the
calibration run, not to this module). This module is the promoted form of that proof
(QBP#755): the calibration namespace `QBP.Foundations.Goal` is replaced by
`QBP.Foundations.OctonionAutBranching`; every definition, lemma, theorem statement and
proof body is otherwise byte-identical to the verified artifact, except the section
heading that called the target theorems "`sorry`-stubbed" (they are proved here).

## Provenance and attribution (QBP#755 AC5)

* **Authored by `claude-sonnet-5`, as the Sonnet arm of deming's 2026-09-30
  cost-calibration harness** (live-test seq 2090–2146; node
  `INSIGHT-octonion-quaternion-branching`, "upper-mid" target). The locked
  infrastructure (stub lines 1–135: `loIdxQ`, `hiIdxQ`, `oLo`, `oHi`, `gamma`,
  `oLo_gamma`, `oHi_gamma`, `sq_eq`, `conj_eq`, `mul_conj_eq`, `conj_mul_eq`,
  `mul_conj_one_of_unit`, `conj_mul_one_of_unit` and the three target signatures) was
  part of the harness stub; the helper section and the three proof bodies are the
  Sonnet arm's.
* **Independently kernel-verified by deming** (record:
  `~/Documents/Nidavellir-bench-staging/results/VERIFICATION-RECORD-octonion-node.md`;
  artifact sha256 `add032f418cb635f630d9d3feda560ae0ecc6427f0588f25470ed0493bc3b763`,
  locked-stub section l.1–135 sha256
  `cbc4177056f2a73040dd2cb428235c27926aa8ecbdd7acfe65fd3f139c0aacd5`, built against
  QBP master `25ac715`).
* **Ported to this module by qbp-oppenheimer** and rebuilt against current master.

## What is (and is not) claimed

The mathematics is **classical**: `γ(a,b)(x₁,x₂) = (a x₁ ā, b x₂ ā)` for unit
quaternions `a, b` is the standard `Spin(4) → SO(4) ⊂ G₂ = Aut(𝕆)` construction. The
contribution is a kernel-checked formalization in QBP's `CDAlg` framework that proves
multiplicativity (`gamma_mul`) using associativity of `ℍ = CDAlg ℝ 2` only — there is no
`Semigroup`/`Ring` instance on `CDAlg ℝ 3`, and `𝕆` is provably non-associative
(`QBP.Foundations.Breakdown.octonion_not_associative`).

Proved: `gamma_mul` (γ(a,b) is multiplicative on all of 𝕆), `gamma_fixes_hosted`
(γ(a,b) preserves the hosted quaternion subalgebra `{x | oHi x = 0}` setwise, both
directions), `gamma_id_iff` (γ(a,b) = id ⇔ a = b ∧ a real, i.e. the kernel
`{(1,1), (−1,−1)}` of `Spin(4) → SO(4)`).

**Not claimed:** the `(3,1) ⊕ (2,2)` irrep branching of `G₂ ⊃ SO(4)`; that `SO(4)` is the
*full* stabiliser of `ℍ` in `G₂` (which needs `Aut(𝕆) ≅ G₂`, QBP#622); that
`(a,b) ↦ γ(a,b)` is a group homomorphism `Spin(4) → Aut(𝕆)` (composition law not stated).

§3 (added in the port by qbp-oppenheimer, not part of the Sonnet arm's proof) packages
`γ(a,b)` as a `CDAut 3` (`gammaAut`): ℝ-linear (`gamma_add`, `gamma_smul`) and bijective
(`gamma_bijective`, inverse `γ(ā, b̄)`), so `γ(a,b) ∈ Aut(𝕆)` is stated, not only
multiplicativity.
-/

namespace QBP.Foundations.OctonionAutBranching

open QBP.Foundations.CDAlg

/-! ## 1. Locked infrastructure (fully proved, do not modify) -/

/-- Embed a quaternion coordinate index into the low half of an octonion index. -/
def loIdxQ (p : Fin (2^2)) : Fin (2^3) := ⟨p.val, by omega⟩

/-- Embed a quaternion coordinate index into the high half of an octonion index
    (shift by 4). -/
def hiIdxQ (q : Fin (2^2)) : Fin (2^3) :=
  ⟨q.val + 4, by have := q.isLt; omega⟩

/-- The low (hosted-ℍ) quaternion component of an octonion, `x = (oLo x, oHi x)`. -/
def oLo (x : CDAlg ℝ 3) : CDAlg ℝ 2 := ⟨fun p => x.coord (loIdxQ p)⟩

/-- The high quaternion component of an octonion. -/
def oHi (x : CDAlg ℝ 3) : CDAlg ℝ 2 := ⟨fun q => x.coord (hiIdxQ q)⟩

@[simp] theorem oLo_coord (x : CDAlg ℝ 3) (p) : (oLo x).coord p = x.coord (loIdxQ p) := rfl
@[simp] theorem oHi_coord (x : CDAlg ℝ 3) (q) : (oHi x).coord q = x.coord (hiIdxQ q) := rfl

/-- **The `SO(4)`-style octonion self-map.** For quaternions `a b : CDAlg ℝ 2` (not
    yet assumed unit), `γ(a,b)` acts as `x ↦ (a x1 ā, b x2 ā)` on the CD pair
    `x = (x1, x2) = (oLo x, oHi x)`. This is a raw coordinate definition — its
    multiplicativity for unit `a,b` is exactly the content of `gamma_mul` below,
    NOT assumed here. -/
def gamma (a b : CDAlg ℝ 2) (x : CDAlg ℝ 3) : CDAlg ℝ 3 :=
  ⟨fun i =>
    if h : i.val < 4 then
      (a * oLo x * conj a).coord ⟨i.val, h⟩
    else
      (b * oHi x * conj a).coord ⟨i.val - 4, by have := i.isLt; omega⟩⟩

/-- By construction: the low half of `γ(a,b)(x)` is exactly `a · oLo x · ā`. -/
theorem oLo_gamma (a b : CDAlg ℝ 2) (x : CDAlg ℝ 3) :
    oLo (gamma a b x) = a * oLo x * conj a := by
  ext p
  have hp : (loIdxQ p).val < 4 := p.isLt
  simp only [oLo_coord, gamma, hp, dif_pos]
  rfl

/-- By construction: the high half of `γ(a,b)(x)` is exactly `b · oHi x · ā`. -/
theorem oHi_gamma (a b : CDAlg ℝ 2) (x : CDAlg ℝ 3) :
    oHi (gamma a b x) = b * oHi x * conj a := by
  ext q
  have hq : ¬ (hiIdxQ q).val < 4 := by
    have := q.isLt
    simp only [hiIdxQ]
    omega
  simp only [oHi_coord, gamma, hq, dif_neg, not_false_iff]
  congr 1

/-- **Quadraticity, general `n`** (restated locally to keep this file self-contained;
    identical in content to `QBP.Foundations.CDAlg.cdAlg_sq_eq`). -/
theorem sq_eq (x : CDAlg ℝ 2) : x * x = (2 * x.coord 0) • x - (N x) • 1 :=
  QBP.Foundations.CDAlg.cdAlg_sq_eq x

/-- Conjugation is polynomial in the real part (restated locally; identical in
    content to `QBP.Foundations.CrystalHosting.CDAut.conj_eq_two_re_sub`). -/
theorem conj_eq (x : CDAlg ℝ 2) : conj x = (2 * x.coord 0) • (1 : CDAlg ℝ 2) - x := by
  ext i
  rw [conj_coord, sub_coord, smul_coord, one_coord]
  by_cases h : i.val = 0
  · have hi : i = 0 := Fin.ext h
    rw [if_pos h, hi, if_pos rfl, mul_one]; ring
  · have hi : i ≠ 0 := fun hh => h (by rw [hh]; rfl)
    rw [if_neg h, if_neg hi, mul_zero, zero_sub]

/-- **Every quaternion times its conjugate is its norm** (needs no associativity —
    pure bilinearity + quadraticity + the unit laws of `CDAlg ℝ 2`). -/
theorem mul_conj_eq (a : CDAlg ℝ 2) : a * conj a = (N a) • (1 : CDAlg ℝ 2) := by
  rw [conj_eq a, mul_sub, mul_smul_right, cdAlg_mul_one, sq_eq a]
  abel

/-- **Conjugate times quaternion is its norm** (the other side). -/
theorem conj_mul_eq (a : CDAlg ℝ 2) : conj a * a = (N a) • (1 : CDAlg ℝ 2) := by
  rw [conj_eq a, sub_mul, mul_smul_left, cdAlg_one_mul, sq_eq a]
  abel

/-- A **unit** quaternion's conjugate is its two-sided inverse. -/
theorem mul_conj_one_of_unit {a : CDAlg ℝ 2} (ha : N a = 1) : a * conj a = 1 := by
  rw [mul_conj_eq, ha, one_smul]

theorem conj_mul_one_of_unit {a : CDAlg ℝ 2} (ha : N a = 1) : conj a * a = 1 := by
  rw [conj_mul_eq, ha, one_smul]

/-! ## 2. Target theorems (proved; `sorry`-stubbed only in the calibration stub) -/

/-! ### Sonnet arm's private helper infrastructure

Everything in this section is new (not part of the locked infrastructure above
the marker). The strategy: establish the genuine Cayley–Dickson doubling law for
the `oLo`/`oHi` split of `𝕆 = CDAlg ℝ 3` into `ℍ = CDAlg ℝ 2` pairs — exactly
mirroring the already-proved `cdLo_mul`/`cdHi_mul` doubling law one level up
(`𝕊 = 𝕆 ⊕ 𝕆` in `NoAutonomousDynamics.lean`) — then use ONLY that doubling law
plus associativity of `ℍ` (`instRingTwo`) to prove `gamma_mul`. -/

section SonnetHelpers

/-! #### Index combinatorics for the `Fin (2^2)` / `Fin (2^3)` pair split -/

theorem loIdxQ_xor_loIdxQ : ∀ p q : Fin (2^2), (loIdxQ p ^^^ loIdxQ q) = loIdxQ (p ^^^ q) := by
  decide

theorem loIdxQ_xor_hiIdxQ : ∀ p q : Fin (2^2), (loIdxQ p ^^^ hiIdxQ q) = hiIdxQ (p ^^^ q) := by
  decide

theorem hiIdxQ_xor_loIdxQ : ∀ p q : Fin (2^2), (hiIdxQ p ^^^ loIdxQ q) = hiIdxQ (p ^^^ q) := by
  decide

theorem hiIdxQ_xor_hiIdxQ : ∀ p q : Fin (2^2), (hiIdxQ p ^^^ hiIdxQ q) = loIdxQ (p ^^^ q) := by
  decide

/-- Every `Fin (2^3)` index is either a low-half or a high-half `Fin (2^2)` index. -/
theorem oIdx_cases : ∀ k : Fin (2^3),
    (∃ t : Fin (2^2), k = loIdxQ t) ∨ (∃ t : Fin (2^2), k = hiIdxQ t) := by decide

/-! #### `mulCoeff 3` doubling rows (the level-2/3 analogue of `mulCoeff_{lo,hi}_{lo,hi}`) -/

theorem mulCoeff_qlo_lo : ∀ p q : Fin (2^2),
    mulCoeff 3 (loIdxQ p) (loIdxQ q) = mulCoeff 2 p q := by decide

theorem mulCoeff_qlo_hi : ∀ p q : Fin (2^2),
    mulCoeff 3 (loIdxQ p) (hiIdxQ q) = mulCoeff 2 q p := by decide

theorem mulCoeff_qhi_lo : ∀ p q : Fin (2^2),
    mulCoeff 3 (hiIdxQ p) (loIdxQ q) = conjSign 2 q * mulCoeff 2 p q := by decide

theorem mulCoeff_qhi_hi : ∀ p q : Fin (2^2),
    mulCoeff 3 (hiIdxQ p) (hiIdxQ q) = -(conjSign 2 q * mulCoeff 2 q p) := by decide

/-! #### The `Fin (2^3)` sum split into `Fin (2^2) ⊕ Fin (2^2)` halves -/

/-- The Cayley–Dickson half-split bijection at level 2/3. -/
def halfEquivQ : (Fin (2^2) ⊕ Fin (2^2)) ≃ Fin (2^3) where
  toFun := Sum.elim loIdxQ hiIdxQ
  invFun k := if h : k.val < 2^2 then Sum.inl ⟨k.val, h⟩ else Sum.inr ⟨k.val - 2^2, by omega⟩
  left_inv := by decide
  right_inv := by decide

theorem sum_split_q {M : Type*} [AddCommMonoid M] (f : Fin (2^3) → M) :
    (∑ k, f k) = (∑ p : Fin (2^2), f (loIdxQ p)) + (∑ q : Fin (2^2), f (hiIdxQ q)) := by
  rw [← Equiv.sum_comp halfEquivQ f, Fintype.sum_sum_type]
  rfl

/-! #### The genuine Cayley–Dickson doubling law for `oLo`/`oHi`

`oLo (x*y) = oLo x * oLo y − conj (oHi y) * oHi x`,
`oHi (x*y) = oHi y * oLo x + oHi x * conj (oLo y)` — the "four-term" law
`(a,b)(c,d) = (ac − d̄b, da + bc̄)` read off the actual `mulCoeff 3` structure
constants. This is the hard combinatorial core; everything downstream
(`gamma_mul`) is pure `ℍ`-associative algebra on top of it. -/

theorem oLo_mul (x y : CDAlg ℝ 3) :
    oLo (x * y) = oLo x * oLo y - conj (oHi y) * oHi x := by
  ext s
  have h1 : (∑ p : Fin (2^2), (mulCoeff 3 (loIdxQ p) (loIdxQ p ^^^ loIdxQ s) : ℝ)
        * x.coord (loIdxQ p) * y.coord (loIdxQ p ^^^ loIdxQ s))
      = (oLo x * oLo y).coord s := by
    rw [mul_coord_single]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [loIdxQ_xor_loIdxQ, mulCoeff_qlo_lo, oLo_coord, oLo_coord]
  have h2 : (∑ q : Fin (2^2), (mulCoeff 3 (hiIdxQ q) (hiIdxQ q ^^^ loIdxQ s) : ℝ)
        * x.coord (hiIdxQ q) * y.coord (hiIdxQ q ^^^ loIdxQ s))
      = -((conj (oHi y) * oHi x).coord s) := by
    rw [mul_coord_matrix, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hcc : (conj (oHi y)).coord (q ^^^ s) = ((conjSign 2 (q ^^^ s) : Int) : ℝ)
        * (oHi y).coord (q ^^^ s) := by
      rw [conj_coord, conjSign]
      by_cases h0 : (q ^^^ s).val = 0
      · rw [if_pos h0, if_pos h0]; push_cast; ring
      · rw [if_neg h0, if_neg h0]; push_cast; ring
    rw [hiIdxQ_xor_loIdxQ, mulCoeff_qhi_hi, hcc, oHi_coord, oHi_coord]
    push_cast; ring
  rw [oLo_coord, mul_coord_single, sum_split_q, h1, h2, sub_coord]
  ring

theorem oHi_mul (x y : CDAlg ℝ 3) :
    oHi (x * y) = oHi y * oLo x + oHi x * conj (oLo y) := by
  ext s
  have h1 : (∑ p : Fin (2^2), (mulCoeff 3 (loIdxQ p) (loIdxQ p ^^^ hiIdxQ s) : ℝ)
        * x.coord (loIdxQ p) * y.coord (loIdxQ p ^^^ hiIdxQ s))
      = (oHi y * oLo x).coord s := by
    rw [mul_coord_matrix]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [loIdxQ_xor_hiIdxQ, mulCoeff_qlo_hi, oHi_coord, oLo_coord]
    ring
  have h2 : (∑ q : Fin (2^2), (mulCoeff 3 (hiIdxQ q) (hiIdxQ q ^^^ hiIdxQ s) : ℝ)
        * x.coord (hiIdxQ q) * y.coord (hiIdxQ q ^^^ hiIdxQ s))
      = (oHi x * conj (oLo y)).coord s := by
    rw [mul_coord_single]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hcc : (conj (oLo y)).coord (q ^^^ s)
        = ((conjSign 2 (q ^^^ s) : Int) : ℝ) * (oLo y).coord (q ^^^ s) := by
      rw [conj_coord]
      by_cases h0 : (q ^^^ s).val = 0
      · rw [if_pos h0, conjSign_zero_of 2 (q ^^^ s) h0]; push_cast; ring
      · rw [if_neg h0, conjSign_neg_of 2 (q ^^^ s) h0]; push_cast; ring
    rw [hiIdxQ_xor_hiIdxQ, mulCoeff_qhi_lo, hcc, oHi_coord, oLo_coord]
    push_cast; ring
  rw [oHi_coord, mul_coord_single, sum_split_q, h1, h2, add_coord]

/-- Two octonions with equal `oLo`/`oHi` halves are equal. -/
theorem eq_of_oHalves {x y : CDAlg ℝ 3} (hlo : oLo x = oLo y) (hhi : oHi x = oHi y) :
    x = y := by
  ext k
  rcases oIdx_cases k with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht; exact congrArg (fun z : CDAlg ℝ 2 => z.coord t) hlo
  · subst ht; exact congrArg (fun z : CDAlg ℝ 2 => z.coord t) hhi

/-! #### A witness octonion with prescribed `oLo`/`oHi` halves (for `gamma_id_iff`) -/

private def mkO (u w : CDAlg ℝ 2) : CDAlg ℝ 3 :=
  ⟨fun i =>
    if h : i.val < 4 then
      u.coord ⟨i.val, h⟩
    else
      w.coord ⟨i.val - 4, by have := i.isLt; omega⟩⟩

private theorem oLo_mkO (u w : CDAlg ℝ 2) : oLo (mkO u w) = u := by
  ext p
  have hp : (loIdxQ p).val < 4 := p.isLt
  simp only [oLo_coord, mkO, hp, dif_pos]
  rfl

private theorem oHi_mkO (u w : CDAlg ℝ 2) : oHi (mkO u w) = w := by
  ext q
  have hq : ¬ (hiIdxQ q).val < 4 := by
    have := q.isLt
    simp only [hiIdxQ]
    omega
  simp only [oHi_coord, mkO, hq, dif_neg, not_false_iff]
  congr 1

private theorem e_mul_coord_q (m : Fin (2^2)) (x : CDAlg ℝ 2) (k : Fin (2^2)) :
    (e m * x).coord k = (mulCoeff 2 m (m ^^^ k) : ℝ) * x.coord (m ^^^ k) := by
  rw [mul_coord_matrix, Finset.sum_eq_single (m ^^^ k)]
  · rw [xor_xor_cancel m k, e_coord, if_pos rfl, mul_one]
  · intro b _ hb
    have hne : (b ^^^ k) ≠ m := by
      intro h; apply hb; rw [← xor_xor_cancel b k, h]
    rw [e_coord, if_neg hne, mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem mul_e_coord_q (x : CDAlg ℝ 2) (m k : Fin (2^2)) :
    (x * e m).coord k = (mulCoeff 2 (m ^^^ k) m : ℝ) * x.coord (m ^^^ k) := by
  rw [mul_coord_single, Finset.sum_eq_single (m ^^^ k)]
  · rw [xor_xor_cancel m k, e_coord, if_pos rfl, mul_one]
  · intro b _ hb
    have hne : (b ^^^ k) ≠ m := by
      intro h; apply hb; rw [← xor_xor_cancel b k, h]
    rw [e_coord, if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private def i1Q : Fin (2^2) := ⟨1, by norm_num⟩
private def i2Q : Fin (2^2) := ⟨2, by norm_num⟩
private def i3Q : Fin (2^2) := ⟨3, by norm_num⟩

private theorem xor_1Q2Q : i1Q ^^^ i2Q
    = i3Q := by decide

private theorem xor_1Q3Q : i1Q ^^^ i3Q
    = i2Q := by decide

private theorem xor_2Q3Q : i2Q ^^^ i3Q
    = i1Q := by decide

private theorem mulCoeff2_1Q3Q_ne :
    mulCoeff 2 i1Q i3Q ≠ 0 := by decide

private theorem mulCoeff2_1Q2Q_ne :
    mulCoeff 2 i1Q i2Q ≠ 0 := by decide

private theorem mulCoeff2_1Q3Q_antisymm :
    mulCoeff 2 i3Q i1Q
      = - mulCoeff 2 i1Q i3Q := by decide

private theorem mulCoeff2_2Q1Q_antisymm :
    mulCoeff 2 i2Q i1Q
      = - mulCoeff 2 i1Q i2Q := by decide

/-! #### Conjugation is an anti-automorphism of `ℍ = CDAlg ℝ 2`

`conj (conj p) = p` (involution) and `conj (p*q) = conj q * conj p`
(order-reversing). The second is proved by the standard basis-`decide` +
bilinear-lift route (`lift_bilinear_eq`), never by assuming `ℍ` commutative
(it isn't) and never by appeal to `𝕆`-associativity. -/

theorem conj_conj_two (p : CDAlg ℝ 2) : conj (conj p) = p := by
  ext i
  rw [conj_coord, conj_coord]
  by_cases h : i.val = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, neg_neg]

private theorem conj_add_q (x y : CDAlg ℝ 2) : conj (x + y) = conj x + conj y := by
  ext i
  simp only [conj_coord, add_coord]
  split_ifs <;> ring

private theorem conj_smul_q (r : ℝ) (x : CDAlg ℝ 2) : conj (r • x) = r • conj x := by
  ext i
  simp only [conj_coord, smul_coord]
  split_ifs <;> ring

private theorem conj_e_q (k : Fin (2^2)) :
    (conj (e k) : CDAlg ℝ 2) = (conjSign 2 k : ℝ) • e k := by
  ext j
  rw [conj_coord, smul_coord, e_coord]
  by_cases h : j = k
  · subst h
    by_cases h0 : j.val = 0
    · simp [h0, conjSign_zero_of 2 j h0]
    · simp [h0, conjSign_neg_of 2 j h0]
  · simp [h]

theorem conjSign_mulCoeff_two : ∀ i j : Fin (2^2),
    mulCoeff 2 i j * conjSign 2 (i ^^^ j) = conjSign 2 i * conjSign 2 j * mulCoeff 2 j i := by
  decide

theorem conj_mul_anti_two (p q : CDAlg ℝ 2) : conj (p * q) = conj q * conj p := by
  have key : conj (p * q) - conj q * conj p = 0 := by
    apply lift_bilinear_eq (T := fun p q : CDAlg ℝ 2 => conj (p * q) - conj q * conj p)
    · exact
        { add_left := fun x x' y => by
            simp only [mul_add_left, conj_add_q, mul_add_right]; abel
          smul_left := fun r x y => by
            simp only [mul_smul_left, conj_smul_q, mul_smul_right]; module
          add_right := fun x y y' => by
            simp only [mul_add_right, conj_add_q, mul_add_left]; abel
          smul_right := fun r x y => by
            simp only [mul_smul_right, conj_smul_q, mul_smul_left]; module }
    · intro i j
      have : conj (e i * e j : CDAlg ℝ 2) = conj (e j) * conj (e i) := by
        rw [e_mul_e, conj_smul_q, conj_e_q, smul_smul, conj_e_q, conj_e_q, mul_smul_left,
          mul_smul_right, e_mul_e, smul_smul, smul_smul, xor_comm_fin j i]
        congr 1
        have hcm := conjSign_mulCoeff_two i j
        have hcmR : (↑(mulCoeff 2 i j) * ↑(conjSign 2 (i ^^^ j)) : ℝ)
            = (↑(conjSign 2 i) * ↑(conjSign 2 j) * ↑(mulCoeff 2 j i) : ℝ) := by
          exact_mod_cast hcm
        rw [hcmR]; ring
      rw [this, sub_self]
  rwa [sub_eq_zero] at key

/-! #### Unit-quaternion middle-cancellation

`conj r * (r * q) = q` and `r * (conj r * q) = q` for a unit `r` (`N r = 1`).
These are the ONLY facts about `a`, `b` used past this point — the four-term
octonion identity `gamma_mul` reduces, after the doubling law, to a pure
associative-ring computation cancelling `ā·a = 1` / `a·ā = 1` pairs (and
likewise for `b`). -/

theorem cancelL {r : CDAlg ℝ 2} (hr : N r = 1) (q : CDAlg ℝ 2) : conj r * (r * q) = q := by
  rw [← mul_assoc, conj_mul_one_of_unit hr, one_mul]

theorem cancelL' {r : CDAlg ℝ 2} (hr : N r = 1) (q : CDAlg ℝ 2) : r * (conj r * q) = q := by
  rw [← mul_assoc, mul_conj_one_of_unit hr, one_mul]

end SonnetHelpers

/-- **REQUIRED.** `γ(a,b)` is multiplicative on all of `𝕆 = CDAlg ℝ 3`, for any
    unit quaternions `a, b` — even though `𝕆` itself is not associative. The proof
    must genuinely expand `(x*y)` via the Cayley–Dickson doubling into
    `oLo`/`oHi` parts (the "four-term" `(ac − d̄b, da + bc̄)` law) and use only
    associativity of `ℍ = CDAlg ℝ 2` (`instRingTwo`), never associativity of 𝕆. -/
theorem gamma_mul (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1) (x y : CDAlg ℝ 3) :
    gamma a b (x * y) = gamma a b x * gamma a b y := by
  apply eq_of_oHalves
  · rw [oLo_gamma, oLo_mul, oLo_mul (gamma a b x) (gamma a b y), oLo_gamma, oLo_gamma,
      oHi_gamma, oHi_gamma, conj_mul_anti_two, conj_mul_anti_two, conj_conj_two]
    simp only [mul_assoc, mul_sub, sub_mul, cancelL ha, cancelL hb]
  · rw [oHi_gamma, oHi_mul, oHi_mul (gamma a b x) (gamma a b y), oLo_gamma, oLo_gamma,
      oHi_gamma, oHi_gamma, conj_mul_anti_two, conj_mul_anti_two, conj_conj_two]
    simp only [mul_assoc, mul_add, add_mul, cancelL ha]

/-- **REQUIRED.** `γ(a,b)` fixes the hosted quaternion subalgebra `{x | oHi x = 0}`
    setwise: an octonion is hosted iff its image under `γ(a,b)` is hosted. -/
theorem gamma_fixes_hosted (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1) (x : CDAlg ℝ 3) :
    oHi x = 0 ↔ oHi (gamma a b x) = 0 := by
  rw [oHi_gamma]
  constructor
  · intro h
    rw [h, mul_zero, zero_mul]
  · intro h
    have h1 : oHi x * conj a = 0 := by
      have h' : conj b * (b * oHi x * conj a) = conj b * 0 := by rw [h]
      rwa [mul_zero, ← mul_assoc, ← mul_assoc, conj_mul_one_of_unit hb, one_mul] at h'
    have h2 : oHi x * conj a * a = 0 * a := by rw [h1]
    rwa [zero_mul, mul_assoc, conj_mul_one_of_unit ha, mul_one] at h2

/-- **OPTIONAL stretch.** `γ(a,b)` is the identity map iff `a = b` AND `a` is real
    (`a = conj a`, i.e. `a ∈ {1, -1}` given `N a = 1`). NOTE: `a = b` alone is
    NOT sufficient — e.g. `γ(i,i)` conjugates `ℍ` by `i`, a nontrivial rotation,
    not the identity. This is the honest statement of "`γ(a,b) = id` iff `(a,b)`
    is in the kernel of `Spin(4) → SO(4) ⊂ G2`", i.e. `a = b ∈ {±1}` (`a` central
    in `ℍ`, equivalently `a` real). -/
theorem gamma_id_iff (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1) :
    (∀ x : CDAlg ℝ 3, gamma a b x = x) ↔ (a = b ∧ a = conj a) := by
  constructor
  · intro h
    have hab : a = b := by
      have h1 := congrArg oLo (h (mkO 1 0))
      rw [oLo_gamma, oLo_mkO, mul_one] at h1
      have h2 := congrArg oHi (h (mkO 0 1))
      rw [oHi_gamma, oHi_mkO, mul_one] at h2
      have h3 : (a - b) * conj a = 0 := by rw [sub_mul, h1, h2, sub_self]
      have h4 : (a - b) * conj a * a = 0 * a := by rw [h3]
      rw [mul_assoc, conj_mul_one_of_unit ha, mul_one, zero_mul] at h4
      exact sub_eq_zero.mp h4
    refine ⟨hab, ?_⟩
    have hc1 : (a * e i1Q : CDAlg ℝ 2)
        = e i1Q * a := by
      have hx := congrArg oLo (h (mkO (e i1Q) 0))
      rw [oLo_gamma, oLo_mkO] at hx
      have hx2 : a * e i1Q * conj a * a
          = e i1Q * a := by rw [hx]
      rwa [mul_assoc, conj_mul_one_of_unit ha, mul_one] at hx2
    have hc2 : (a * e i2Q : CDAlg ℝ 2)
        = e i2Q * a := by
      have hx := congrArg oLo (h (mkO (e i2Q) 0))
      rw [oLo_gamma, oLo_mkO] at hx
      have hx2 : a * e i2Q * conj a * a
          = e i2Q * a := by rw [hx]
      rwa [mul_assoc, conj_mul_one_of_unit ha, mul_one] at hx2
    have ha3 : a.coord i3Q = 0 := by
      have e1 := congrArg (fun z : CDAlg ℝ 2 => z.coord i2Q) hc1
      dsimp only at e1
      rw [mul_e_coord_q, e_mul_coord_q, xor_1Q2Q, mulCoeff2_1Q3Q_antisymm] at e1
      push_cast [neg_mul] at e1
      have hne : (mulCoeff 2 i1Q i3Q : ℝ)
          ≠ 0 := by exact_mod_cast mulCoeff2_1Q3Q_ne
      have hz : (2 : ℝ)
          * ((mulCoeff 2 i1Q i3Q : ℝ)
             * a.coord i3Q) = 0 := by linarith [e1]
      rcases mul_eq_zero.mp hz with h5 | h5
      · norm_num at h5
      · rcases mul_eq_zero.mp h5 with h6 | h6
        · exact absurd h6 hne
        · exact h6
    have ha2 : a.coord i2Q = 0 := by
      have e1 := congrArg (fun z : CDAlg ℝ 2 => z.coord i3Q) hc1
      dsimp only at e1
      rw [mul_e_coord_q, e_mul_coord_q, xor_1Q3Q, mulCoeff2_2Q1Q_antisymm] at e1
      push_cast [neg_mul] at e1
      have hne : (mulCoeff 2 i1Q i2Q : ℝ)
          ≠ 0 := by exact_mod_cast mulCoeff2_1Q2Q_ne
      have hz : (2 : ℝ)
          * ((mulCoeff 2 i1Q i2Q : ℝ)
             * a.coord i2Q) = 0 := by linarith [e1]
      rcases mul_eq_zero.mp hz with h5 | h5
      · norm_num at h5
      · rcases mul_eq_zero.mp h5 with h6 | h6
        · exact absurd h6 hne
        · exact h6
    have ha1 : a.coord i1Q = 0 := by
      have e1 := congrArg (fun z : CDAlg ℝ 2 => z.coord i3Q) hc2
      dsimp only at e1
      rw [mul_e_coord_q, e_mul_coord_q, xor_2Q3Q, mulCoeff2_2Q1Q_antisymm] at e1
      push_cast [neg_mul] at e1
      have hne : (mulCoeff 2 i1Q i2Q : ℝ)
          ≠ 0 := by exact_mod_cast mulCoeff2_1Q2Q_ne
      have hz : (2 : ℝ)
          * ((mulCoeff 2 i1Q i2Q : ℝ)
             * a.coord i1Q) = 0 := by linarith [e1]
      rcases mul_eq_zero.mp hz with h5 | h5
      · norm_num at h5
      · rcases mul_eq_zero.mp h5 with h6 | h6
        · exact absurd h6 hne
        · exact h6
    ext i
    rw [conj_coord]
    by_cases h0 : i.val = 0
    · rw [if_pos h0]
    · rw [if_neg h0]
      have hz : a.coord i = 0 := by
        fin_cases i <;>
          first
            | (exfalso; exact h0 rfl)
            | exact ha1
            | exact ha2
            | exact ha3
      rw [hz]; ring
  · rintro ⟨hab, hac⟩
    subst hab
    have hN1 : N (1 : CDAlg ℝ 2) = 1 := by
      rw [N_def, Finset.sum_eq_single (0 : Fin (2^2))]
      · rw [one_coord, if_pos rfl]; norm_num
      · intro b _ hb; rw [one_coord, if_neg hb]; norm_num
      · intro hcon; exact absurd (Finset.mem_univ _) hcon
    have hreal : a = a.coord (0 : Fin (2^2)) • (1 : CDAlg ℝ 2) := by
      ext i
      by_cases hi : i = 0
      · subst hi; rw [smul_coord, one_coord, if_pos rfl, mul_one]
      · have hi' : i.val ≠ 0 := fun hcontra => hi (Fin.ext hcontra)
        have hceq := congrArg (fun z : CDAlg ℝ 2 => z.coord i) hac
        dsimp only at hceq
        rw [conj_coord, if_neg hi'] at hceq
        have hz : a.coord i = 0 := by linarith
        rw [hz, smul_coord, one_coord, if_neg hi, mul_zero]
    have N_smul_q : ∀ (r : ℝ) (z : CDAlg ℝ 2), N (r • z) = r^2 * N z := by
      intro r z
      simp only [N_def, smul_coord, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hcc : a.coord (0 : Fin (2^2)) * a.coord (0 : Fin (2^2)) = 1 := by
      have hN := ha
      rw [hreal, N_smul_q, hN1, mul_one, pow_two] at hN
      exact hN
    have key : ∀ u : CDAlg ℝ 2, a * u * a = u := by
      intro u
      conv_lhs => rw [hreal]
      rw [mul_smul_left, cdAlg_one_mul, mul_smul_right, cdAlg_mul_one, smul_smul, hcc, one_smul]
    intro x
    apply eq_of_oHalves
    · rw [oLo_gamma, ← hac]; exact key (oLo x)
    · rw [oHi_gamma, ← hac]; exact key (oHi x)

/-! ## 3. Packaging `γ(a,b)` as an element of `Aut(𝕆)` (`CDAut 3`)

**Added by qbp-oppenheimer in the port (QBP#755); not part of the Sonnet arm's proof.**
`gamma_mul` is multiplicativity only. Membership in `Aut(𝕆)` — QBP's `CDAut 3`, an
ℝ-linear multiplicative bijection (`CrystalHosting.lean`) — also needs additivity,
ℝ-homogeneity and bijectivity. They are proved here from the same `oLo`/`oHi` split;
the two-sided inverse of `γ(a,b)` is `γ(ā, b̄)`. As in `gamma_mul`, only associativity
of `ℍ = CDAlg ℝ 2` is used. -/

section AutPackaging

theorem oLo_add (x y : CDAlg ℝ 3) : oLo (x + y) = oLo x + oLo y := by
  ext p
  simp only [oLo_coord, add_coord]

theorem oHi_add (x y : CDAlg ℝ 3) : oHi (x + y) = oHi x + oHi y := by
  ext q
  simp only [oHi_coord, add_coord]

theorem oLo_smul (r : ℝ) (x : CDAlg ℝ 3) : oLo (r • x) = r • oLo x := by
  ext p
  simp only [oLo_coord, smul_coord]

theorem oHi_smul (r : ℝ) (x : CDAlg ℝ 3) : oHi (r • x) = r • oHi x := by
  ext q
  simp only [oHi_coord, smul_coord]

/-- `γ(a,b)` is additive (no unit hypothesis needed). -/
theorem gamma_add (a b : CDAlg ℝ 2) (x y : CDAlg ℝ 3) :
    gamma a b (x + y) = gamma a b x + gamma a b y := by
  apply eq_of_oHalves
  · rw [oLo_gamma, oLo_add, oLo_add, oLo_gamma, oLo_gamma, mul_add, add_mul]
  · rw [oHi_gamma, oHi_add, oHi_add, oHi_gamma, oHi_gamma, mul_add, add_mul]

/-- `γ(a,b)` is ℝ-homogeneous (no unit hypothesis needed). -/
theorem gamma_smul (a b : CDAlg ℝ 2) (r : ℝ) (x : CDAlg ℝ 3) :
    gamma a b (r • x) = r • gamma a b x := by
  apply eq_of_oHalves
  · rw [oLo_gamma, oLo_smul, oLo_smul, oLo_gamma, mul_smul_right, mul_smul_left]
  · rw [oHi_gamma, oHi_smul, oHi_smul, oHi_gamma, mul_smul_right, mul_smul_left]

/-- `γ(ā, b̄)` is a left inverse of `γ(a,b)` for unit `a, b`. -/
theorem gamma_conj_gamma (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1)
    (x : CDAlg ℝ 3) : gamma (conj a) (conj b) (gamma a b x) = x := by
  apply eq_of_oHalves
  · rw [oLo_gamma, oLo_gamma, conj_conj_two]
    simp only [mul_assoc, conj_mul_one_of_unit ha, mul_one, cancelL ha]
  · rw [oHi_gamma, oHi_gamma, conj_conj_two]
    simp only [mul_assoc, conj_mul_one_of_unit ha, mul_one, cancelL hb]

/-- `γ(ā, b̄)` is a right inverse of `γ(a,b)` for unit `a, b`. -/
theorem gamma_gamma_conj (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1)
    (y : CDAlg ℝ 3) : gamma a b (gamma (conj a) (conj b) y) = y := by
  apply eq_of_oHalves
  · rw [oLo_gamma, oLo_gamma, conj_conj_two]
    simp only [mul_assoc, mul_conj_one_of_unit ha, mul_one, cancelL' ha]
  · rw [oHi_gamma, oHi_gamma, conj_conj_two]
    simp only [mul_assoc, mul_conj_one_of_unit ha, mul_one, cancelL' hb]

/-- `γ(a,b)` is a bijection of `𝕆` for unit `a, b`. -/
theorem gamma_bijective (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1) :
    Function.Bijective (gamma a b) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨gamma (conj a) (conj b), gamma_conj_gamma a b ha hb, gamma_gamma_conj a b ha hb⟩

/-- **`γ(a,b) ∈ Aut(𝕆)`.** For unit quaternions `a, b`, `γ(a,b)` packaged as an
    element of `CDAut 3` (an ℝ-linear multiplicative bijection of `𝕆 = CDAlg ℝ 3`). -/
def gammaAut (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1) :
    QBP.Foundations.CrystalHosting.CDAut 3 where
  toFun := gamma a b
  map_add := gamma_add a b
  map_smul := gamma_smul a b
  map_mul := gamma_mul a b ha hb
  bijective := gamma_bijective a b ha hb

/-- The packaged automorphism acts as `γ(a,b)`. -/
theorem gammaAut_apply (a b : CDAlg ℝ 2) (ha : N a = 1) (hb : N b = 1)
    (x : CDAlg ℝ 3) : gammaAut a b ha hb x = gamma a b x := rfl

end AutPackaging

#print axioms gamma_mul
#print axioms gamma_fixes_hosted
#print axioms gamma_id_iff
#print axioms gamma_bijective
#print axioms gammaAut

end QBP.Foundations.OctonionAutBranching
