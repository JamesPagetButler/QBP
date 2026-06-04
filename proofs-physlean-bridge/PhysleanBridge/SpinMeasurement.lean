import QuantumInfo.Measurements.POVM
import QuantumInfo.States.Mixed.MState
import QuantumInfo.States.Pure.Braket

/-!
# Independent reproduction of the QBP angle-dependent Born rule from PhysLean

QBP issue #490.  This file derives the spin-1/2 angle-dependent measurement law
(`prob_up = cos²(θ/2)`, the row-"01b" oracle prediction) **from PhysLean's own
QuantumInfo measurement formalism** — the POVM/Born-rule machinery in
`QuantumInfo.Measurements.POVM` — rather than by asserting the QBP formula.

The physics, stated independently of QBP:

* A spin-1/2 system prepared at polar angle `θ` from the measurement (`z`) axis,
  in the `x`–`z` plane, is the pure state with computational-basis amplitudes
  `(cos (θ/2), sin (θ/2))`.  (`spinKet`.)
* The standard projective measurement in the `z` (up/down) basis is the POVM
  `{ |0⟩⟨0|, |1⟩⟨1| }` — the two diagonal rank-1 projectors.  (`zBasisPOVM`.)
* PhysLean's `POVM.measure Λ ρ` is the Born rule: outcome `x` has probability
  `⟪Λ.mats x, ρ.M⟫ = Re Tr(Mₓ ρ)`.  We feed it the pure state `MState.pure`
  and read off the two outcome probabilities.

The theorems below show the `cos²(θ/2)` / `sin²(θ/2)` / `cos θ` law *emerges*
from `POVM.measure` applied to `MState.pure spinKet`.  No QBP formula is copied;
the `cos²` arises from the matrix trace `Re Tr(diag(1,0) · |ψ⟩⟨ψ|)`.

The `#print axioms` audit (end of file) shows these rest only on the three
standard Mathlib axioms — they are genuine proofs, not stubs.
-/

set_option maxHeartbeats 400000

namespace PhysleanBridge

open scoped ComplexConjugate ComplexOrder
open Braket Complex Matrix RealInnerProductSpace

noncomputable section

/-- The prepared spin-1/2 state at polar angle `θ` (in the `x`–`z` plane), as a
PhysLean `Ket (Fin 2)` with computational-basis amplitudes `(cos (θ/2), sin (θ/2))`.

Normalization is `cos²(θ/2) + sin²(θ/2) = 1` — proven, not assumed. -/
def spinKet (θ : ℝ) : Ket (Fin 2) where
  vec := ![ (Real.cos (θ / 2) : ℂ), (Real.sin (θ / 2) : ℂ) ]
  normalized' := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

/-- The `z`-basis (up/down) projective measurement as a PhysLean `POVM`:
the two diagonal projectors `P₀ = diag(1,0)` (outcome "up") and `P₁ = diag(0,1)`
(outcome "down").  Both are PSD and they sum to the identity — the POVM axioms,
proven here (not stubbed). -/
def zBasisPOVM : POVM (Fin 2) (Fin 2) where
  mats := fun x => HermitianMat.diagonal ℂ (fun i => if i = x then 1 else 0)
  nonneg := by
    intro x
    rw [HermitianMat.zero_le_iff, HermitianMat.diagonal_mat]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split <;> simp
  normalized := by
    apply HermitianMat.ext
    rw [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
    ext i j
    simp only [HermitianMat.diagonal_mat, Matrix.sum_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp

/-- Born-rule outcome probability ("up") for the prepared spin state at angle `θ`,
**as computed by PhysLean's `POVM.measure`**, equals `cos²(θ/2)`.

This is the load-bearing independence claim: the LHS is PhysLean's Born rule
`⟪P₀, |ψ⟩⟨ψ|⟫ = Re Tr(diag(1,0)·|ψ⟩⟨ψ|)` evaluated on the pure state; the RHS
`cos²(θ/2)` is what falls out of the 2×2 trace.  Nothing here mentions a QBP
formula — the `cos²` is derived. -/
theorem probUp_eq (θ : ℝ) :
    ((zBasisPOVM.measure (MState.pure (spinKet θ))) 0 : ℝ) = Real.cos (θ / 2) ^ 2 := by
  show (⟪zBasisPOVM.mats 0, (MState.pure (spinKet θ)).M⟫ : ℝ) = _
  rw [HermitianMat.inner_eq_re_trace]
  simp only [zBasisPOVM, HermitianMat.diagonal_mat]
  rw [Matrix.trace, Fin.sum_univ_two]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  norm_num
  show ((MState.pure (spinKet θ)).m 0 0).re = _
  rw [MState.pure_apply]
  show ((spinKet θ) 0 * conj ((spinKet θ) 0)).re = _
  rw [Complex.mul_conj]
  show (Complex.normSq ((spinKet θ) 0) : ℂ).re = _
  rw [Complex.ofReal_re]
  simp only [spinKet, Ket.coe_fun_eq, Matrix.cons_val_zero, Complex.normSq_ofReal]
  rw [sq]

/-- Born-rule "down" probability equals `sin²(θ/2)`, derived from PhysLean's `measure`. -/
theorem probDown_eq (θ : ℝ) :
    ((zBasisPOVM.measure (MState.pure (spinKet θ))) 1 : ℝ) = Real.sin (θ / 2) ^ 2 := by
  show (⟪zBasisPOVM.mats 1, (MState.pure (spinKet θ)).M⟫ : ℝ) = _
  rw [HermitianMat.inner_eq_re_trace]
  simp only [zBasisPOVM, HermitianMat.diagonal_mat]
  rw [Matrix.trace, Fin.sum_univ_two]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  norm_num
  show ((MState.pure (spinKet θ)).m 1 1).re = _
  rw [MState.pure_apply]
  show ((spinKet θ) 1 * conj ((spinKet θ) 1)).re = _
  rw [Complex.mul_conj]
  show (Complex.normSq ((spinKet θ) 1) : ℂ).re = _
  rw [Complex.ofReal_re]
  simp only [spinKet, Ket.coe_fun_eq, Matrix.cons_val_one,
    Matrix.cons_val_zero, Complex.normSq_ofReal]
  rw [sq]

/-- The two outcome probabilities sum to 1 — sanity check that this is a genuine
probability distribution (`cos²(θ/2) + sin²(θ/2) = 1`). -/
theorem probUp_add_probDown (θ : ℝ) :
    ((zBasisPOVM.measure (MState.pure (spinKet θ))) 0 : ℝ)
      + ((zBasisPOVM.measure (MState.pure (spinKet θ))) 1 : ℝ) = 1 := by
  rw [probUp_eq, probDown_eq, add_comm]
  exact Real.sin_sq_add_cos_sq (θ / 2)

/-- The expectation value `prob_up − prob_down` equals `cos θ`, the QBP "expectation"
column.  Derived from the two PhysLean Born-rule probabilities via the double-angle
identity `cos²(θ/2) − sin²(θ/2) = cos θ`. -/
theorem expectation_eq (θ : ℝ) :
    ((zBasisPOVM.measure (MState.pure (spinKet θ))) 0 : ℝ)
      - ((zBasisPOVM.measure (MState.pure (spinKet θ))) 1 : ℝ) = Real.cos θ := by
  rw [probUp_eq, probDown_eq]
  have h : θ = 2 * (θ / 2) := by ring
  rw [h, Real.cos_two_mul']
  ring

end

end PhysleanBridge

-- Completeness gate: these must depend only on {propext, Classical.choice, Quot.sound}.
#print axioms PhysleanBridge.spinKet
#print axioms PhysleanBridge.zBasisPOVM
#print axioms PhysleanBridge.probUp_eq
#print axioms PhysleanBridge.probDown_eq
#print axioms PhysleanBridge.probUp_add_probDown
#print axioms PhysleanBridge.expectation_eq
