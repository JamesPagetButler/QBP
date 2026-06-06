/-
  QBP.Foundations.CDBridge
  ========================

  The bridge theorem: **Cayley–Dickson level 2 IS the quaternions**, as a Lean
  theorem rather than a comment.  Concretely:

    * `cdAlg_two_assoc`        — `CDAlg R 2` is associative for ALL `x y z`
                                 (any `CommRing R`), via the trilinear lift
                                 (`lift_trilinear_eq`) + the basis `decide` fact
                                 `assocCoeffZ 2 i j k = 0`.  This is the honest
                                 promotion of a 4³ = 64-case integer check to an
                                 algebra-wide law — not asserted.
    * `instance Ring (CDAlg R 2)` — now that associativity is a theorem, the carrier
                                 earns a `Ring` (left/right distributivity already in
                                 CDAlg; `one_mul`/`mul_one` proven here).  We add
                                 ONLY what is proven (no `CommRing`, no `Field`).
    * `cdAlg2EquivQuaternion`  — `CDAlg ℝ 2 ≃ₐ[ℝ] Quaternion ℝ`, the basis map
                                 `e₀↦1, e₁↦i, e₂↦j, e₃↦k`.

  ## Sign-convention finding (reported for the record)

  The task brief flagged that `mulCoeff 2` and Mathlib's `Quaternion` multiplication
  might differ by an orientation, forcing a permuted/negated basis map.  They do NOT.
  Computing `mulCoeff 2` on the four basis units (i = e₁, j = e₂, k = e₃) gives

      i·i = j·j = k·k = −1,   i·j = k,  j·i = −k,
      j·k = i,  k·j = −i,     k·i = j,  i·k = −j,

  i.e. the standard right-handed Hamilton convention.  Mathlib's `Quaternion R =
  ℍ[R,-1,0,-1]` has `imI² = c₁ = −1`, `imJ² = c₃ = −1`, `imI·imJ = imK`,
  `imJ·imK = imI` (from `mk_mul_mk` with `c₁=-1, c₂=0, c₃=-1`) — the SAME Hamilton
  convention.  Hence the honest correspondence is the *identity on basis labels*:
  `e₀↦1, e₁↦i, e₂↦j, e₃↦k`, with no permutation and no sign flip.  The 16 basis-pair
  multiplicativity checks below confirm this constructively.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.
-/
import QBP.Foundations.CDLifting
import Mathlib.Algebra.Quaternion

namespace QBP.Foundations.CDAlg

open Quaternion

/-! ## 1. Associativity of `CDAlg R 2` (the structural payoff) -/

/-- **Integer basis fact (kernel `decide`).**  Every level-2 basis associator
    coefficient vanishes: `assocCoeffZ 2 i j k = 0` on all `4³ = 64` basis triples.
    This is the finite seed that the trilinear lift promotes to full associativity. -/
theorem cdAlg_two_assocCoeffZ_zero :
    ∀ i j k : Fin (2^2), assocCoeffZ 2 i j k = 0 := by decide

/-- The associator vanishes on every basis triple of `CDAlg R 2` (over any
    `CommRing R`): `assoc (e i) (e j) (e k) = 0`. -/
theorem cdAlg_two_assoc_basis {R : Type*} [CommRing R] (i j k : Fin (2^2)) :
    (assoc (e i) (e j) (e k) : CDAlg R 2) = 0 := by
  rw [assoc_e]
  have h : (assocCoeffZ 2 i j k : R) = 0 := by
    rw [cdAlg_two_assocCoeffZ_zero i j k]; norm_num
  rw [h, zero_smul]

/-- **STRUCTURAL PAYOFF: `CDAlg R 2` is associative.**  For all `x y z`,
    `(x · y) · z = x · (y · z)`.  Proven via the trilinear lift of the basis fact
    `cdAlg_two_assocCoeffZ_zero` — the basis-vs-algebra-wide honesty gap closed by
    the keystone `lift_trilinear_eq`, not asserted.  Holds over any `CommRing R`. -/
theorem cdAlg_two_assoc {R : Type*} [CommRing R] (x y z : CDAlg R 2) :
    (x * y) * z = x * (y * z) := by
  have h : assoc x y z = 0 :=
    lift_trilinear_eq assoc_trilinear (fun i j k => cdAlg_two_assoc_basis i j k) x y z
  rwa [assoc, sub_eq_zero] at h

/-! ## 2. The unit laws and the `Ring` instance for `CDAlg R 2`

`CDAlg` already provides left/right distributivity (`mul_add_left`/`mul_add_right`)
and the additive group.  With associativity (§1) and the unit laws below, the
carrier earns a genuine `Ring`.  We add ONLY the `Ring` (associativity is proven;
commutativity is NOT — it fails at ℍ, handled in PR-D), never `CommRing`/`Field`. -/

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Multiplication on `CDAlg R n` is `R`-bilinear (packaged from the four
    `mul_add_*` / `mul_smul_*` lemmas in `CDAlg`).  Lets us distribute `*` over
    `Finset.sum` on either side via `IsBilinear.sum_{left,right}`. -/
theorem mul_isBilinear : IsBilinear (fun x y : CDAlg R n => x * y) where
  add_left x x' y := mul_add_left x x' y
  smul_left r x y := mul_smul_left r x y
  add_right x y y' := mul_add_right x y y'
  smul_right r x y := mul_smul_right r x y

/-- `e 0` is a left unit on basis elements: `e 0 * e j = e j`. -/
theorem one_mul_e (j : Fin (2^n)) : (e 0 * e j : CDAlg R n) = e j := by
  rw [e_mul_e, mulCoeff_zero_left, xor_zero_left]; norm_num

/-- `e 0` is a right unit on basis elements: `e i * e 0 = e i`. -/
theorem e_mul_one (i : Fin (2^n)) : (e i * e 0 : CDAlg R n) = e i := by
  rw [e_mul_e, mulCoeff_zero_right, xor_zero_right]; norm_num

/-- **Left-unit law** for `CDAlg R n`: `1 · x = x`.  By basis expansion of `x`,
    distributing `e 0 = 1` over the sum (bilinearity) and `one_mul_e`. -/
theorem cdAlg_one_mul (x : CDAlg R n) : (1 : CDAlg R n) * x = x := by
  conv_lhs => rw [one_def, basis_expansion x]
  rw [mul_isBilinear.sum_right]
  conv_rhs => rw [basis_expansion x]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_smul_right, one_mul_e]

/-- **Right-unit law** for `CDAlg R n`: `x · 1 = x`.  Dual of `cdAlg_one_mul`. -/
theorem cdAlg_mul_one (x : CDAlg R n) : x * (1 : CDAlg R n) = x := by
  conv_lhs => rw [one_def, basis_expansion x]
  rw [mul_isBilinear.sum_left]
  conv_rhs => rw [basis_expansion x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_smul_left, e_mul_one]

/-- **`Ring` instance for `CDAlg R 2`.**  Earned honestly: associativity is the
    theorem `cdAlg_two_assoc`, the unit laws are `cdAlg_one_mul`/`cdAlg_mul_one`,
    distributivity is `mul_add_right`/`mul_add_left` from `CDAlg`, and the additive
    group is the existing `AddCommGroup`.  Nothing stronger than `Ring` is added —
    commutativity FAILS at this level (ℍ) and is the PR-D ✗ cell. -/
instance instRingTwo : Ring (CDAlg R 2) where
  left_distrib  := mul_add_right
  right_distrib := mul_add_left
  zero_mul x := by
    have := mul_smul_left (0 : R) (1 : CDAlg R 2) x; rwa [zero_smul, zero_smul] at this
  mul_zero x := by
    have := mul_smul_right (0 : R) x (1 : CDAlg R 2); rwa [zero_smul, zero_smul] at this
  mul_assoc := cdAlg_two_assoc
  one_mul := cdAlg_one_mul
  mul_one := cdAlg_mul_one

/-- The `R`-algebra structure map `r ↦ r • 1`, bundled as a `RingHom` (used by the
    `Algebra` instance below). -/
def algebraMapTwo : R →+* CDAlg R 2 where
  toFun r := r • (1 : CDAlg R 2)
  map_one' := one_smul R 1
  map_mul' r s := by
    show (r * s) • (1 : CDAlg R 2) = (r • 1) * (s • 1)
    rw [mul_smul_left, cdAlg_one_mul, smul_smul]
  map_zero' := zero_smul R 1
  map_add' r s := add_smul r s 1

/-- **`Algebra R (CDAlg R 2)`.**  The structure map `r ↦ r • 1` (`algebraMapTwo`);
    `smul_def` and `commutes` follow from `mul_smul_left`/`mul_smul_right` and the
    unit laws.  This upgrades `Module`+`Ring` to an `R`-algebra — the home of the
    bridge equiv. -/
instance instAlgebraTwo : Algebra R (CDAlg R 2) where
  algebraMap := algebraMapTwo
  commutes' r x := by
    show (r • (1 : CDAlg R 2)) * x = x * (r • 1)
    rw [mul_smul_left, mul_smul_right, cdAlg_one_mul, cdAlg_mul_one]
  smul_def' r x := by
    show r • x = (r • (1 : CDAlg R 2)) * x
    rw [mul_smul_left, cdAlg_one_mul]

/-! ## 3. The algebra isomorphism `CDAlg ℝ 2 ≃ₐ[ℝ] Quaternion ℝ`

The honest basis correspondence (see the sign-convention finding in the header) is
the identity on basis labels: `e₀↦1, e₁↦i, e₂↦j, e₃↦k`, i.e. coordinate-for-field.
Forward reads the four coordinates into `⟨re, imI, imJ, imK⟩`; inverse builds the
coordinate vector.  Linearity is coordinatewise; multiplicativity is reduced to the
16 basis-pair checks via double basis expansion. -/

open scoped Quaternion

/-- The four basis indices of `Fin (2^2) = Fin 4`, as explicit `Fin 4` values. -/
private def i0 : Fin (2^2) := ⟨0, by norm_num⟩
private def i1 : Fin (2^2) := ⟨1, by norm_num⟩
private def i2 : Fin (2^2) := ⟨2, by norm_num⟩
private def i3 : Fin (2^2) := ⟨3, by norm_num⟩

/-- Forward coordinate read: `CDAlg ℝ 2 → Quaternion ℝ`. -/
private def toQuat (x : CDAlg ℝ 2) : ℍ[ℝ] :=
  ⟨x.coord i0, x.coord i1, x.coord i2, x.coord i3⟩

/-- Inverse: build the coordinate vector from a quaternion's four fields. -/
private def ofQuat (q : ℍ[ℝ]) : CDAlg ℝ 2 :=
  ⟨![q.re, q.imI, q.imJ, q.imK]⟩

private theorem toQuat_ofQuat (q : ℍ[ℝ]) : toQuat (ofQuat q) = q := by
  cases q; rfl

private theorem ofQuat_toQuat (x : CDAlg ℝ 2) : ofQuat (toQuat x) = x := by
  ext k
  fin_cases k <;> rfl

private theorem toQuat_add (x y : CDAlg ℝ 2) : toQuat (x + y) = toQuat x + toQuat y := by
  apply QuaternionAlgebra.ext <;> simp [toQuat]

private theorem toQuat_smul (r : ℝ) (x : CDAlg ℝ 2) :
    toQuat (r • x) = r • toQuat x := by
  apply QuaternionAlgebra.ext <;> simp [toQuat]

/-- `toQuat` sends `1` to `1`. -/
private theorem toQuat_one : toQuat (1 : CDAlg ℝ 2) = 1 := by
  apply QuaternionAlgebra.ext <;> simp [toQuat, one_def, e, i0, i1, i2, i3]

/-- `toQuat` sends the four basis vectors to `1, i, j, k`. -/
private theorem toQuat_e0 : toQuat (e i0) = 1 := by apply QuaternionAlgebra.ext <;> simp [toQuat, e, i0, i1, i2, i3]
private theorem toQuat_e1 : toQuat (e i1) = ⟨0,1,0,0⟩ := by apply QuaternionAlgebra.ext <;> simp [toQuat, e, i0, i1, i2, i3]
private theorem toQuat_e2 : toQuat (e i2) = ⟨0,0,1,0⟩ := by apply QuaternionAlgebra.ext <;> simp [toQuat, e, i0, i1, i2, i3]
private theorem toQuat_e3 : toQuat (e i3) = ⟨0,0,0,1⟩ := by apply QuaternionAlgebra.ext <;> simp [toQuat, e, i0, i1, i2, i3]

/-- **Multiplicativity on basis pairs.**  `toQuat (e i * e j) = toQuat (e i) * toQuat (e j)`
    for all 16 basis pairs.  Each side is computed concretely: LHS via `e_mul_e`
    + `mulCoeff 2`, RHS via the quaternion product `mk_mul_mk` at `c₁=-1,c₂=0,c₃=-1`.
    Agreement of all 16 is the constructive proof that the basis correspondence is
    the orientation-preserving identity (no permutation/sign flip). -/
private theorem toQuat_mul_basis (i j : Fin (2^2)) :
    toQuat (e i * e j) = toQuat (e i) * toQuat (e j) := by
  fin_cases i <;> fin_cases j <;>
    (rw [e_mul_e]
     apply QuaternionAlgebra.ext <;>
       simp [toQuat, e, mulCoeff, conjSign, i0, i1, i2, i3,
             QuaternionAlgebra.mk_mul_mk, Fin.xor_val_of_two_pow])

/-- Scalar-mixing law on `ℍ[ℝ]`: `(a•p)·(b•q) = (a·b)•(p·q)`.  Proved coordinatewise
    via `QuaternionAlgebra.ext`, sidestepping the `IsScalarTower`/`SMulCommClass`
    diamond between the quaternion `SMul` instance and the algebra `Module`. -/
private theorem quat_smul_mul_smul (a b : ℝ) (p q : ℍ[ℝ]) :
    (a • p) * (b • q) = (a * b) • (p * q) := by
  apply QuaternionAlgebra.ext <;>
    simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, smul_eq_mul] <;> ring

/-- `toQuat` distributes over a `Finset.sum` (it is additive + maps 0 to 0). -/
private theorem toQuat_sum {ι : Type*} (s : Finset ι) (f : ι → CDAlg ℝ 2) :
    toQuat (∑ i ∈ s, f i) = ∑ i ∈ s, toQuat (f i) := by
  classical
  induction s using Finset.induction with
  | empty => apply QuaternionAlgebra.ext <;> simp [toQuat]
  | insert a s ha ih => rw [Finset.sum_insert ha, toQuat_add, ih, Finset.sum_insert ha]

/-- **Multiplicativity of `toQuat` (full).**  Lifted from the 16 basis pairs
    (`toQuat_mul_basis`) by double basis expansion + bilinearity of both products.
    `toQuat (x * y) = toQuat x * toQuat y`. -/
private theorem toQuat_mul (x y : CDAlg ℝ 2) :
    toQuat (x * y) = toQuat x * toQuat y := by
  -- Expand both arguments in the basis; push `toQuat` (linear) and both products
  -- (bilinear) through the two sums; reduce each (i,j) term to `toQuat_mul_basis`.
  conv_lhs => rw [basis_expansion x, basis_expansion y]
  conv_rhs => rw [basis_expansion x, basis_expansion y]
  rw [mul_isBilinear.sum_left, toQuat_sum, toQuat_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_isBilinear.sum_right, toQuat_sum, toQuat_smul, toQuat_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- term i,j : toQuat ((x.coord i • e i) * (y.coord j • e j))
  --          = (x.coord i • toQuat (e i)) * (y.coord j • toQuat (e j))
  rw [mul_smul_left, mul_smul_right, toQuat_smul, toQuat_smul, toQuat_smul,
      toQuat_mul_basis, quat_smul_mul_smul, smul_smul]

/-- **THE BRIDGE.**  `CDAlg ℝ 2 ≃ₐ[ℝ] Quaternion ℝ`: Cayley–Dickson level 2 *is* the
    Hamilton quaternions, as an `ℝ`-algebra isomorphism, with the orientation-
    preserving identity basis map `e₀↦1, e₁↦i, e₂↦j, e₃↦k`.  Forward = `toQuat`,
    inverse = `ofQuat`; multiplicativity = `toQuat_mul`, additivity = `toQuat_add`,
    `commutes` from `toQuat (r•1) = r` (algebraMap).  This is the matrix's
    "ℍ = CD(ℂ)" / "ℍ = CDAlg 2" cell discharged as a theorem, not a comment. -/
def cdAlg2EquivQuaternion : CDAlg ℝ 2 ≃ₐ[ℝ] ℍ[ℝ] where
  toFun := toQuat
  invFun := ofQuat
  left_inv := ofQuat_toQuat
  right_inv := toQuat_ofQuat
  map_add' := toQuat_add
  map_mul' := toQuat_mul
  commutes' r := by
    show toQuat (algebraMap ℝ (CDAlg ℝ 2) r) = algebraMap ℝ ℍ[ℝ] r
    rw [Algebra.algebraMap_eq_smul_one, toQuat_smul, toQuat_one,
        Algebra.algebraMap_eq_smul_one]

/-- Sanity face of the bridge: the four basis vectors map to `1, i, j, k`
    (restating `toQuat_e{0,1,2,3}` through the bundled equiv). -/
theorem cdAlg2EquivQuaternion_basis :
    cdAlg2EquivQuaternion (e i0) = 1 ∧
    cdAlg2EquivQuaternion (e i1) = ⟨0,1,0,0⟩ ∧
    cdAlg2EquivQuaternion (e i2) = ⟨0,0,1,0⟩ ∧
    cdAlg2EquivQuaternion (e i3) = ⟨0,0,0,1⟩ :=
  ⟨toQuat_e0, toQuat_e1, toQuat_e2, toQuat_e3⟩

/-! ## 4. Completeness audit — `#print axioms` -/

#print axioms cdAlg_two_assoc
#print axioms cdAlg_one_mul
#print axioms cdAlg_mul_one
#print axioms toQuat_mul_basis
#print axioms toQuat_mul
#print axioms cdAlg2EquivQuaternion
#print axioms cdAlg2EquivQuaternion_basis

end QBP.Foundations.CDAlg
