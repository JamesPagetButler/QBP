/-
TOOLCHECK T14 — linear algebra QBP uses: `LinearMap` (`→ₗ[R]`, `LinearMap.ker`,
`LinearMap.mk`), `Module.finrank` of coordinate spaces, `Matrix` with
`Matrix.det_fin_two`, `EuclideanSpace` + inner product, and `Polynomial.eval`.

Used by (QBP, 2026-11-20 grep): `LinearMap` 6 files — `QBP/Foundations/SeamSpectrum.lean`,
`SeamKernel.lean`, `TransitionState.lean`, `HolographicSubalgebra.lean`; `Matrix` 4 files —
`LeftMulDet.lean` (`Matrix.det`), `HolographicSubalgebra.lean`, `SeamKernel.lean`;
`Module.finrank`: `CDDimension.lean`, `HolographicSubalgebra.lean` (imports
`Mathlib.LinearAlgebra.Dimension.Constructions`, `.Finrank`, `.StrongRankCondition`);
`EuclideanSpace`/inner: `HolographicSubalgebra.lean`, `QBP/Substrate/RuleFlow.lean`
(`Mathlib.Analysis.InnerProductSpace.PiL2`); `Polynomial`: `LeftMulDet.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

namespace QBPToolcheck.T14

/-- The coordinate space `Fin 8 → ℝ` has dimension 8 (octonion coordinate count). -/
theorem finrank_fin8 : Module.finrank ℝ (Fin 8 → ℝ) = 8 := by
  simp

/-- A linear map built by hand (`LinearMap.mk`), and its kernel membership. -/
def proj0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := v 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem proj0_ker : (![0, 5] : Fin 2 → ℝ) ∈ LinearMap.ker proj0 := by
  simp [proj0]

/-- The 2×2 determinant formula. -/
theorem det2 (a b c d : ℝ) : Matrix.det !![a, b; c, d] = a * d - b * c := by
  rw [Matrix.det_fin_two_of]

/-- Inner product on `EuclideanSpace ℝ (Fin 2)` of a vector with itself is its norm². -/
theorem inner_self (v : EuclideanSpace ℝ (Fin 2)) : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp

/-- Polynomial evaluation. -/
theorem poly_eval : (Polynomial.X ^ 2 + 1 : Polynomial ℤ).eval 3 = 10 := by
  simp

end QBPToolcheck.T14

#print axioms QBPToolcheck.T14.finrank_fin8
#print axioms QBPToolcheck.T14.proj0_ker
#print axioms QBPToolcheck.T14.det2
#print axioms QBPToolcheck.T14.inner_self
#print axioms QBPToolcheck.T14.poly_eval
