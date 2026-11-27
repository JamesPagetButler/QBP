/-
TOOLCHECK T02 — user `Decidable` instances (`unfold …; infer_instance`), `deriving
DecidableEq`, and kernel-checked counting over `Finset.univ.filter` / `Finset.card`.

Feature: a named `Prop` predicate is made decidable by unfolding it to a `∀`/`∃` over a
`Fintype` and letting instance search find the `Decidable` instance; a count is then a
closed `Finset.card` that `decide` reduces in the kernel (structured enumeration,
federation standard §5 — not `native_decide` on a hand-rolled `Bool`).

Used by (QBP, 2026-11-20 grep): `QBP/Foundations/Octonion32Count.lean` (instances on
`List (Fin 32)` predicates), `SedenionOctonionCount.lean`, `Breakdown.lean`,
`FanoSubalgebras.lean` (`Finset.filter`); `deriving DecidableEq`:
`QBP/Foundations/QBPHorizonFoundations.lean`; `Finset.card`: `NoAutonomousDynamics.lean`,
`LocaleDynamics.lean`, `CDDimension.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Fin

namespace QBPToolcheck.T02

/-- A small enumerated type with derived decidable equality (QBPHorizonFoundations shape). -/
inductive Op where
  | add | mul | conj | norm
  deriving DecidableEq, Repr

instance : Fintype Op where
  elems := {.add, .mul, .conj, .norm}
  complete x := by cases x <;> decide

/-- A named predicate on a list of indices (QBP's `isAlternative H` shape). -/
def closedUnderSucc (H : List (Fin 8)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, (a + b) ∈ H

instance (H : List (Fin 8)) : Decidable (closedUnderSucc H) := by
  unfold closedUnderSucc; infer_instance

/-- The subgroup `{0,2,4,6}` of `ℤ/8` is closed; checked in the kernel. -/
theorem evens_closed : closedUnderSucc [0, 2, 4, 6] := by decide

/-- `{0,1}` is not closed (`1+1 = 2 ∉`): a decided negative, not a comment. -/
theorem zero_one_not_closed : ¬ closedUnderSucc [0, 1] := by decide

/-- A count over `Finset.univ.filter` on `Fin 16`, closed by kernel `decide`. -/
theorem card_odd_fin16 : (Finset.univ.filter (fun i : Fin 16 => i.val % 2 = 1)).card = 8 := by
  decide

/-- `Fintype.card` of the derived enumeration. -/
theorem card_op : Fintype.card Op = 4 := by decide

end QBPToolcheck.T02

#print axioms QBPToolcheck.T02.evens_closed
#print axioms QBPToolcheck.T02.zero_one_not_closed
#print axioms QBPToolcheck.T02.card_odd_fin16
#print axioms QBPToolcheck.T02.card_op
