/-
TOOLCHECK T00 — the Mathlib IMPORT SURFACE: every Mathlib module any QBP .lean file imports
(comment-stripped grep over proofs/, excluding .lake and this suite; 65 modules on the
current pins).

Feature: module paths. Mathlib moves and splits files between releases (with
`deprecated_module` shims since Lean v4.31.0, or outright removal); a renamed module
breaks `import` before any proof is elaborated. This file fails first on such a bump,
and `run.sh` refuses to run if this list has drifted from QBP's live imports
(`toolcheck.py check-imports`). Regenerate with
`python3 lean-toolcheck/toolcheck.py imports --proofs .` (from proofs/).

Used by: every QBP file that imports Mathlib (see `FEATURES.md` row T00).

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Condensed.TopCatAdjunction
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Dynamics.OmegaLimit
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.Nucleus
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Bases
import Mathlib.Topology.Category.Locale
import Mathlib.Topology.Closure
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Topology.Sets.Opens

namespace QBPToolcheck.T00

/-- A trivial closed fact, so the file has a declaration to audit after the imports load. -/
theorem imports_loaded : (2 : ℕ) + 2 = 4 := rfl

end QBPToolcheck.T00

#print axioms QBPToolcheck.T00.imports_loaded
