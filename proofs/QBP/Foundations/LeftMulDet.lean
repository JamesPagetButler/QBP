/-
  QBP.Foundations.LeftMulDet — det(Lₓ) = N(x)⁴ on 𝕆 (the ZD determinantal hypersurface)
  =====================================================================================

  First rung of the #594 QBP-VML CD-tower geometric-objects ladder.  For the
  octonions 𝕆 = `CDAlg ℝ 3` (dim 8), let `Lₓ` be the 8×8 real matrix of LEFT
  multiplication by `x` (`Lₓ y = x·y`).  We prove the determinantal identity

      det(Lₓ) = N(x)⁴          (exponent 4 = dim/2 = 8/2)

  where `N(x) = ∑ᵢ xᵢ²` is the (Euclidean, non-metric — see the `NormForm`
  non-identification guardrail) norm form.

  Route (NO 8×8 symbolic expansion):
    1. Polarize the PROVEN composition law `N(x·y) = N(x)·N(y)`
       (`octonion_norm_composition`, #591) into the conformality identity
       `⟨x·a, x·b⟩ = N(x)·⟨a,b⟩` (`octonion_bil_comp`).
    2. Hence the Gram identity `Lₓᵀ·Lₓ = N(x)·1` (`octonionLeftMul_transpose_mul`).
    3. Taking det: `det(Lₓ)² = N(x)⁸` (`octonionLeftMul_det_sq`).
    4. Sign: lift to the polynomial ring `MvPolynomial (Fin 8) ℝ` (an integral
       domain).  There `P² = Q⁸` with `P` the determinant polynomial and
       `Q = ∑ Xᵢ²`, so `(P − Q⁴)(P + Q⁴) = 0`, hence `P = ±Q⁴`; evaluating at
       the algebra unit (where `L₁ = 1`, `det = 1 = N(1)⁴`) rules out the minus
       branch.  Transfer between the polynomial and evaluated worlds is by
       `MvPolynomial.funext` (ℝ infinite domain) and `RingHom.map_det` — the
       determinant is never expanded.

  Mandate B (#570, generate-not-organize): the vanishing locus `det(Lₓ) = 0`
  is the zero-divisor / stability geometry of the algebra — this theorem proves
  it is EMPTY at 𝕆 (`octonionLeftMul_det_eq_zero_iff`: `det Lₓ = 0 ↔ x = 0`),
  the smooth baseline against which the sedenion zero-divisor cone (the 42
  assessors, `Breakdown.lean`) is contrasted in the substrate-ripple stability
  program (#595/#592) that aims to generate measured particle-stability numbers.

  Mandate C (callable API): `octonionLeftMul` is a real, COMPUTABLE `def`,
  generic over any `CommRing R` (`CDAlg R 3 → Matrix (Fin 8) (Fin 8) R`), with
  the spec-as-contract theorems `octonionLeftMul_mulVec` (it IS left
  multiplication) and `octonionLeftMul_det_comm` (det = N⁴ over EVERY
  commutative ring, via descent of the identity to `MvPolynomial (Fin 8) ℤ`,
  §5).  At `R = ℝ` this recovers the analytic statement
  (`octonionLeftMul_det`); at `R = ℚ`/`ℤ` it is executable — `#eval` demo §7.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom — every result depends only on
  `{propext, Classical.choice, Quot.sound}`.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import QBP.Foundations.ArtinTrace
import QBP.Foundations.NormForm

namespace QBP.Foundations.LeftMulDet

open QBP.Foundations.CDAlg MvPolynomial Matrix

/-! ## 1. Polarized norm composition: left multiplication is conformal

From the proven composition law `N (x*y) = N x * N y` (#591), applied at
`y = a + b` and expanded through the polarization `N (u+v) = N u + N v + 2⟨u,v⟩`
(`N_add`), left multiplication by `x` scales the polar form by `N x`. -/

/-- **Conformality of left multiplication:** `⟨x·a, x·b⟩ = N(x)·⟨a,b⟩` on 𝕆. -/
theorem octonion_bil_comp (x a b : CDAlg ℝ 3) :
    bil (x * a) (x * b) = N x * bil a b := by
  have h := octonion_norm_composition x (a + b)
  rw [mul_add_right, N_add, N_add, octonion_norm_composition x a,
      octonion_norm_composition x b] at h
  linear_combination h / 2

/-! ## 2. The left-multiplication matrix (callable API surface)

The definition is generic over any commutative ring `R` — the structure
constants `mulCoeff 3` are integers, so `Lₓ` makes sense (and is COMPUTABLE:
no `noncomputable`, `#eval`-able over ℚ/ℤ — §6) at every coefficient ring.
`R = ℝ` recovers the analytic tower; `R = ℚ` is the executable tier Edda /
qbp-compute-unit can actually run. -/

variable {R : Type*} [CommRing R]

/-- The 8×8 matrix of LEFT multiplication by `x` on the level-3 CD algebra
    (𝕆 at `R = ℝ`): `(octonionLeftMul x) i j` is the coefficient of `eᵢ` in
    `x * e_j`, so that `(octonionLeftMul x).mulVec y.coord = (x * y).coord`
    (`octonionLeftMul_mulVec`).  Computable for computable `R` (ℚ, ℤ, …). -/
def octonionLeftMul (x : CDAlg R 3) : Matrix (Fin 8) (Fin 8) R :=
  Matrix.of fun i j => (x * e j).coord i

@[simp] theorem octonionLeftMul_apply (x : CDAlg R 3) (i j : Fin 8) :
    octonionLeftMul x i j = (x * e j).coord i := rfl

/-- Coordinate expansion of `(x * e j).coord i` as a linear form in the
    coordinates of `x` (the structure-constant column). -/
theorem mul_e_coord (x : CDAlg R 3) (j i : Fin (2^3)) :
    (x * e j).coord i
      = ∑ p : Fin (2^3),
          (if (p ^^^ j : Fin (2^3)) = i then (mulCoeff 3 p j : R) else 0) * x.coord p := by
  rw [mul_coord]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_eq_single j]
  · simp only [e_coord]
    split <;> simp
  · intro b _ hb
    simp only [e_coord, if_neg hb, mul_zero]
    split <;> rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Spec-as-contract:** `octonionLeftMul x` really implements left
    multiplication by `x` at the coordinate level (any commutative ring). -/
theorem octonionLeftMul_mulVec (x y : CDAlg R 3) :
    (octonionLeftMul x).mulVec y.coord = (x * y).coord := by
  funext i
  show ∑ j : Fin (2^3), (x * e j).coord i * y.coord j = (x * y).coord i
  rw [mul_coord]
  calc ∑ j : Fin (2^3), (x * e j).coord i * y.coord j
      = ∑ j : Fin (2^3), ∑ p : Fin (2^3),
          ((if (p ^^^ j : Fin (2^3)) = i then (mulCoeff 3 p j : R) else 0) * x.coord p)
            * y.coord j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [mul_e_coord, Finset.sum_mul]
    _ = ∑ p : Fin (2^3), ∑ j : Fin (2^3),
          ((if (p ^^^ j : Fin (2^3)) = i then (mulCoeff 3 p j : R) else 0) * x.coord p)
            * y.coord j := Finset.sum_comm
    _ = ∑ p : Fin (2^3), ∑ j : Fin (2^3),
          (if (p ^^^ j : Fin (2^3)) = i then (mulCoeff 3 p j : R) * x.coord p * y.coord j
           else 0) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun j _ => ?_))
        split <;> ring

/-! ## 3. The Gram identity `Lₓᵀ · Lₓ = N(x) · 1` and `det(Lₓ)² = N(x)⁸` -/

/-- **Gram identity:** the columns of `Lₓ` are orthogonal with common square
    norm `N x`:  `Lₓᵀ * Lₓ = N x • 1`. -/
theorem octonionLeftMul_transpose_mul (x : CDAlg ℝ 3) :
    (octonionLeftMul x)ᵀ * octonionLeftMul x
      = N x • (1 : Matrix (Fin 8) (Fin 8) ℝ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, octonionLeftMul_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have hb : (∑ k : Fin 8, (x * e i).coord k * (x * e j).coord k)
      = bil (x * e i) (x * e j) := rfl
  have hbe : (bil (e (n := 3) i) (e (n := 3) j) : ℝ) = if i = j then 1 else 0 :=
    bil_e (n := 3) i j
  rw [hb, octonion_bil_comp, hbe]

/-- `det(Lₓ)² = N(x)⁸` — the unsigned form of the determinantal identity. -/
theorem octonionLeftMul_det_sq (x : CDAlg ℝ 3) :
    (octonionLeftMul x).det ^ 2 = N x ^ 8 := by
  have h := congrArg Matrix.det (octonionLeftMul_transpose_mul x)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, mul_one] at h
  rw [sq]; exact h

/-- At the algebra unit, `L₁` is the identity matrix (any commutative ring). -/
theorem octonionLeftMul_one : octonionLeftMul (1 : CDAlg R 3) = 1 := by
  ext i j
  rw [octonionLeftMul_apply, cdAlg_one_mul, Matrix.one_apply]
  exact e_coord (n := 3) j i

/-- `N(1) = 1` on any CD level (any commutative ring). -/
theorem N_one {n : ℕ} : N (1 : CDAlg R n) = 1 := by
  rw [N_def]
  rw [show (∑ i, ((1 : CDAlg R n).coord i)^2)
        = ∑ i, (if i = (0 : Fin (2^n)) then (1:R) else 0) from
      Finset.sum_congr rfl (fun i _ => by rw [one_coord]; split <;> norm_num)]
  rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (2^n)) (fun _ => (1:R))]
  simp only [Finset.mem_univ, if_true]

/-! ## 4. The sign, via the polynomial ring

`det(Lₓ)` and `N(x)⁴` are polynomial in the 8 coordinates of `x`.  We realize
both in `MvPolynomial (Fin 8) ℝ` — an integral domain — where `P² = Q⁸` forces
`P = ±Q⁴`, and evaluation at the unit (where both sides are `1`) forces `+`. -/

/-- The generic left-multiplication matrix: entries are the linear forms
    `∑ₚ (structure constant) · Xₚ` in the polynomial ring. -/
noncomputable def octLeftMulPoly : Matrix (Fin 8) (Fin 8) (MvPolynomial (Fin 8) ℝ) :=
  Matrix.of fun i j => ∑ k : Fin 8,
    C (if (k ^^^ j : Fin (2^3)) = i then (mulCoeff 3 k j : ℝ) else 0) * X k

/-- The generic norm form `Q = ∑ Xᵢ²`. -/
noncomputable def octNormPoly : MvPolynomial (Fin 8) ℝ := ∑ k : Fin 8, X k ^ 2

/-- Evaluating the generic matrix at coordinates `c` gives `L_{⟨c⟩}`. -/
theorem octLeftMulPoly_map_eval (c : Fin 8 → ℝ) :
    octLeftMulPoly.map (eval c) = octonionLeftMul ⟨c⟩ := by
  ext i j
  rw [Matrix.map_apply]
  have hR : octonionLeftMul (⟨c⟩ : CDAlg ℝ 3) i j
      = ∑ p : Fin (2^3),
          (if (p ^^^ j : Fin (2^3)) = i then (mulCoeff 3 p j : ℝ) else 0) * c p := by
    rw [octonionLeftMul_apply]; exact mul_e_coord ⟨c⟩ j i
  rw [hR]
  show eval c (∑ k : Fin 8,
      C (if (k ^^^ j : Fin (2^3)) = i then (mulCoeff 3 k j : ℝ) else 0) * X k) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, eval_C, eval_X]

/-- Evaluating the generic norm form at coordinates `c` gives `N ⟨c⟩`. -/
theorem octNormPoly_eval (c : Fin 8 → ℝ) :
    eval c octNormPoly = N (⟨c⟩ : CDAlg ℝ 3) := by
  rw [octNormPoly, map_sum, N_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_pow, eval_X]

/-- The polynomial identity `P² = Q⁸`, transferred from the evaluated identity
    `det(Lₓ)² = N(x)⁸` via `MvPolynomial.funext` (ℝ is an infinite domain). -/
theorem octDetPoly_sq : octLeftMulPoly.det ^ 2 = octNormPoly ^ 8 := by
  apply MvPolynomial.funext
  intro c
  rw [map_pow, map_pow, RingHom.map_det, RingHom.mapMatrix_apply,
    octLeftMulPoly_map_eval, octNormPoly_eval, octonionLeftMul_det_sq]

/-- The coordinate vector of the algebra unit. -/
def unitCoord : Fin 8 → ℝ := fun k => if k = 0 then 1 else 0

theorem unitCoord_mk : (⟨unitCoord⟩ : CDAlg ℝ 3) = 1 := by
  ext i
  rw [one_coord]
  rfl

/-- **The determinant polynomial is `+Q⁴`** — the sign is fixed by evaluation at
    the algebra unit, where `det L₁ = det 1 = 1 = N(1)⁴` (not `−1`). -/
theorem octDetPoly_eq : octLeftMulPoly.det = octNormPoly ^ 4 := by
  have hsq : (octLeftMulPoly.det - octNormPoly ^ 4)
      * (octLeftMulPoly.det + octNormPoly ^ 4) = 0 := by
    linear_combination octDetPoly_sq
  rcases mul_eq_zero.mp hsq with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have h1 : octLeftMulPoly.det = - octNormPoly ^ 4 := by linear_combination h
    have h2 := congrArg (eval unitCoord) h1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, octLeftMulPoly_map_eval,
      unitCoord_mk, octonionLeftMul_one, Matrix.det_one] at h2
    rw [map_neg, map_pow, octNormPoly_eval, unitCoord_mk, N_one] at h2
    norm_num at h2

/-! ## 5. Descent to ℤ, and the identity over EVERY commutative ring

The structure constants are integers, so `det(Lₓ) = N(x)⁴` is really a
ℤ-coefficient polynomial identity.  We restate the generic matrix over
`MvPolynomial (Fin 8) ℤ`, pull the proven ℝ-identity back along the injective
coefficient map `ℤ ↪ ℝ`, and then push the ℤ-identity out along the unique
ring map `ℤ → R` into ANY commutative ring — in particular the computable
rings ℚ and ℤ (the executable tier). -/

/-- The generic left-multiplication matrix over ℤ-polynomials. -/
noncomputable def octLeftMulPolyZ : Matrix (Fin 8) (Fin 8) (MvPolynomial (Fin 8) ℤ) :=
  Matrix.of fun i j => ∑ k : Fin 8,
    C (if (k ^^^ j : Fin (2^3)) = i then mulCoeff 3 k j else 0) * X k

/-- The generic norm form over ℤ-polynomials. -/
noncomputable def octNormPolyZ : MvPolynomial (Fin 8) ℤ := ∑ k : Fin 8, X k ^ 2

/-- Coefficient extension ℤ → ℝ carries `octLeftMulPolyZ` to `octLeftMulPoly`. -/
theorem octLeftMulPolyZ_map :
    octLeftMulPolyZ.map (MvPolynomial.map (Int.castRingHom ℝ)) = octLeftMulPoly := by
  ext i j : 1   -- depth 1: stop at matrix entries (don't descend into MvPolynomial.ext)
  have hZ : octLeftMulPolyZ i j
      = ∑ k : Fin 8, C (if (k ^^^ j : Fin (2^3)) = i then mulCoeff 3 k j else 0) * X k := rfl
  have hR : octLeftMulPoly i j
      = ∑ k : Fin 8,
          C (if (k ^^^ j : Fin (2^3)) = i then (mulCoeff 3 k j : ℝ) else 0) * X k := rfl
  rw [Matrix.map_apply, hZ, hR, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  congr 2
  split <;> simp

/-- Coefficient extension ℤ → ℝ carries `octNormPolyZ` to `octNormPoly`. -/
theorem octNormPolyZ_map :
    MvPolynomial.map (Int.castRingHom ℝ) octNormPolyZ = octNormPoly := by
  rw [octNormPolyZ, octNormPoly, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_pow, MvPolynomial.map_X]

/-- **The determinantal identity as a ℤ-polynomial identity** — pulled back from
    the proven ℝ identity along the injective coefficient map `ℤ ↪ ℝ`. -/
theorem octDetPolyZ_eq : octLeftMulPolyZ.det = octNormPolyZ ^ 4 := by
  apply MvPolynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  rw [map_pow, octNormPolyZ_map, ← octDetPoly_eq, RingHom.map_det,
    RingHom.mapMatrix_apply, octLeftMulPolyZ_map]

/-- Evaluating the ℤ-generic matrix at the coordinates of `x : CDAlg R 3`
    (along `ℤ → R`) gives `octonionLeftMul x`. -/
theorem octLeftMulPolyZ_eval₂ (x : CDAlg R 3) :
    octLeftMulPolyZ.map (eval₂Hom (Int.castRingHom R) x.coord)
      = octonionLeftMul x := by
  ext i j
  rw [Matrix.map_apply]
  have hR : octonionLeftMul x i j
      = ∑ p : Fin (2^3),
          (if (p ^^^ j : Fin (2^3)) = i then (mulCoeff 3 p j : R) else 0) * x.coord p := by
    rw [octonionLeftMul_apply]; exact mul_e_coord x j i
  rw [hR, octLeftMulPolyZ, Matrix.of_apply, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, eval₂Hom_C, eval₂Hom_X']
  congr 1
  split <;> simp

/-- Evaluating the ℤ-generic norm form at the coordinates of `x : CDAlg R 3`
    gives `N x`. -/
theorem octNormPolyZ_eval₂ (x : CDAlg R 3) :
    eval₂Hom (Int.castRingHom R) x.coord octNormPolyZ = N x := by
  rw [octNormPolyZ, map_sum, N_def]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_pow, eval₂Hom_X']

/-- **The determinantal identity over every commutative ring:**
    `det(Lₓ) = N(x)⁴` for every `x : CDAlg R 3`, `R` any `CommRing` —
    obtained by evaluating the ℤ-polynomial identity along `ℤ → R`. -/
theorem octonionLeftMul_det_comm (x : CDAlg R 3) :
    (octonionLeftMul x).det = N x ^ 4 := by
  have h := congrArg (eval₂Hom (Int.castRingHom R) x.coord) octDetPolyZ_eq
  rw [RingHom.map_det, RingHom.mapMatrix_apply, octLeftMulPolyZ_eval₂,
    map_pow, octNormPolyZ_eval₂] at h
  exact h

/-! ## 6. The main theorems and the empty ZD hypersurface -/

/-- **Main theorem — the determinantal identity on 𝕆:**
    `det(Lₓ) = N(x)⁴` for every `x : CDAlg ℝ 3`, with `N x = ∑ᵢ xᵢ²` and
    exponent `4 = dim 𝕆 / 2`.  (The `R = ℝ` instance of
    `octonionLeftMul_det_comm`.) -/
theorem octonionLeftMul_det (x : CDAlg ℝ 3) :
    (octonionLeftMul x).det = N x ^ 4 :=
  octonionLeftMul_det_comm x

/-- The identity at the computable tier: `det(Lₓ) = N(x)⁴` over ℚ, where
    `octonionLeftMul` is executable (`#eval` demo in §7). -/
theorem octonionLeftMul_det_rat (x : CDAlg ℚ 3) :
    (octonionLeftMul x).det = N x ^ 4 :=
  octonionLeftMul_det_comm x

/-- **The ZD determinantal hypersurface of 𝕆 is empty:** `det(Lₓ) = 0 ↔ x = 0`.
    Left multiplication by any nonzero octonion is invertible — 𝕆 has no zero
    divisors.  (Contrast: at 𝕊 the analogous locus is the nonempty zero-divisor
    cone of the 42 assessors, `Breakdown.lean`.) -/
theorem octonionLeftMul_det_eq_zero_iff (x : CDAlg ℝ 3) :
    (octonionLeftMul x).det = 0 ↔ x = 0 := by
  rw [octonionLeftMul_det, pow_eq_zero_iff (by norm_num : (4:ℕ) ≠ 0)]
  exact QBP.Foundations.NormForm.N_eq_zero_iff x

/-! ## 7. Executable demo (Mandate C: the API genuinely runs)

`octonionLeftMul` is computable over computable rings.  The `#eval`s below are
NOT proofs (federation standard: `#eval` runs compiled code and is never
evidence a proposition holds) — correctness is carried by the theorems
`octonionLeftMul_det_rat` / `octonionLeftMul_det_comm` above.  These lines are
the CALLABILITY witness: Edda / qbp-compute-unit can execute this API to
concrete numbers.

`demoX = 1·e₀ + 2·e₁ + … + 8·e₇ : CDAlg ℚ 3`, so `N demoX = ∑ k² = 204` and
the theorem predicts `det = 204⁴ = 1731891456`. -/

/-- A concrete rational octonion: coordinates (1, 2, …, 8). -/
def demoX : CDAlg ℚ 3 := ⟨fun i => (i.val : ℚ) + 1⟩

/-- The rows of `octonionLeftMul demoX`, materialized once (Array-backed), so
    the 8!-term determinant evaluation below doesn't recompute every entry sum
    on each of its ~322 560 entry accesses. -/
def demoRows : Array (Array ℚ) :=
  Array.ofFn fun i => Array.ofFn fun j => octonionLeftMul demoX i j

/-- The materialized matrix (runtime-checked below to coincide with the API
    object `octonionLeftMul demoX`). -/
def demoMat : Matrix (Fin 8) (Fin 8) ℚ :=
  Matrix.of fun i j => (demoRows[i.val]!)[j.val]!

#eval demoRows                        -- the concrete 8×8 structure matrix
#eval decide (∀ i j, demoMat i j = octonionLeftMul demoX i j)  -- true
#eval demoMat.det                     -- 1731891456
#eval N demoX ^ 4                     -- 1731891456  (= 204⁴, matching the theorem)
#eval decide (demoMat.det = N demoX ^ 4)                       -- true

/-! ## Completeness audit — `#print axioms` -/

#print axioms octonion_bil_comp
#print axioms octonionLeftMul_mulVec
#print axioms octonionLeftMul_transpose_mul
#print axioms octonionLeftMul_det_sq
#print axioms octDetPoly_eq
#print axioms octDetPolyZ_eq
#print axioms octonionLeftMul_det_comm
#print axioms octonionLeftMul_det
#print axioms octonionLeftMul_det_rat
#print axioms octonionLeftMul_det_eq_zero_iff

end QBP.Foundations.LeftMulDet
