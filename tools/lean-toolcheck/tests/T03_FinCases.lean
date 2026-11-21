/-
TOOLCHECK T03 — `fin_cases` case-splitting over `Fin n` (and over a hypothesis
`i ∈ Finset`), followed by per-case `simp`/`decide`/`rfl`.

Feature: `fin_cases i` replaces a `Fin n` variable by each literal `0..n-1`, so a goal
over a finite index set becomes n concrete goals (the federation standard §5 pattern for
"check every element of a finite index set").

Used by (QBP, 2026-11-20 grep): `QBP/Foundations/SeamKernel.lean`, `CDBridge.lean`,
`SeamSpectrum.lean`, `HolographicSubalgebra.lean`, `OctonionAutBranching.lean`,
`CDAlg.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

namespace QBPToolcheck.T03

/-- A `Fin 3`-indexed integer vector. -/
def v : Fin 3 → ℤ := ![2, -1, 5]

/-- `fin_cases` over every index, each case closed by `simp`/`decide`. -/
theorem v_ne_zero : ∀ i : Fin 3, v i ≠ 0 := by
  intro i
  fin_cases i <;> simp [v]

/-- `fin_cases` on a `Finset` membership hypothesis. -/
theorem mem_small (i : Fin 5) (h : i ∈ ({1, 3} : Finset (Fin 5))) : i.val % 2 = 1 := by
  fin_cases h <;> decide

/-- Pointwise function equality on `Fin 3` via `funext` + `fin_cases`. -/
theorem v_eq : v = fun i => if i = 0 then 2 else if i = 1 then -1 else 5 := by
  funext i
  fin_cases i <;> decide

end QBPToolcheck.T03

#print axioms QBPToolcheck.T03.v_ne_zero
#print axioms QBPToolcheck.T03.mem_small
#print axioms QBPToolcheck.T03.v_eq
