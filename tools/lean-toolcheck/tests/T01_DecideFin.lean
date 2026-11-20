/-
TOOLCHECK T01 — kernel `decide` / `decide +kernel` on finite types (`Fin n`, `Bool`,
`List (Fin n)`), plus the `maxRecDepth` / `maxHeartbeats` options that QBP's heavy
enumerations raise.

Feature: the kernel reduces a `Decidable` instance for a closed finite proposition
(∀ over `Fin n`, a basis-index multiplication table, a list-of-triples membership).
`decide +kernel` skips the elaborator's whnf and reduces once in the kernel.

Used by (QBP, 2026-11-20 grep, comment-stripped): `QBP/Foundations/SeamSpectrum.lean`,
`SeamKernel.lean`, `NoAutonomousDynamics.lean`, `Octonion32Count.lean`
(`decide +kernel`), `FanoGenesis.lean` (`decide +kernel`), `CDDimension.lean`,
`Breakdown.lean`; `maxRecDepth`/`maxHeartbeats`: `Octonion32Count.lean`,
`FanoSubalgebras.lean`, `Breakdown.lean`, `Sprint12-Inherited/Sedenion.lean`.

TOOLCHECK-EXPECT: pass
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

namespace QBPToolcheck.T01

/-- The seven Fano lines (index triples on `Fin 7`), in QBP's `canonicalFanoLines` shape. -/
def fanoLines : List (Fin 7 × Fin 7 × Fin 7) :=
  [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2)]

/-- Every pair of distinct points lies on exactly one line (kernel enumeration, 42 pairs). -/
theorem fano_pair_on_unique_line :
    ∀ a b : Fin 7, a ≠ b →
      (fanoLines.filter (fun l => (l.1 = a ∨ l.2.1 = a ∨ l.2.2 = a) ∧
        (l.1 = b ∨ l.2.1 = b ∨ l.2.2 = b))).length = 1 := by
  decide

/-- The line count, by `decide`. -/
theorem fanoLines_length : fanoLines.length = 7 := by decide

/-- A signed basis multiplication table on `Fin 4` (the quaternion units 1,i,j,k),
encoded as (sign, index) with an `Int` sign — the `: ℤ` annotation matters (Nat truncates). -/
def qtab (a b : Fin 4) : ℤ × Fin 4 :=
  match a.val, b.val with
  | 0, _ => (1, b)
  | _, 0 => (1, a)
  | 1, 1 => (-1, 0) | 1, 2 => (1, 3) | 1, 3 => (-1, 2)
  | 2, 1 => (-1, 3) | 2, 2 => (-1, 0) | 2, 3 => (1, 1)
  | 3, 1 => (1, 2) | 3, 2 => (-1, 1) | 3, 3 => (-1, 0)
  | _, _ => (0, 0)

/-- Anticommutation of distinct imaginary units, all 6 ordered pairs, kernel-checked. -/
theorem qtab_anticomm :
    ∀ a b : Fin 4, a ≠ 0 → b ≠ 0 → a ≠ b →
      (qtab a b).2 = (qtab b a).2 ∧ (qtab a b).1 = -(qtab b a).1 := by
  decide

set_option maxRecDepth 4000 in
/-- The same check via `decide +kernel` (QBP's heavy-sweep form), under a raised `maxRecDepth`. -/
theorem qtab_sq_neg_one : ∀ a : Fin 4, a ≠ 0 → qtab a a = (-1, 0) := by
  decide +kernel

set_option maxHeartbeats 400000 in
/-- A `Bool`-valued finite check closed by `decide` (not `native_decide`). -/
theorem bool_table : (List.range 20).all (fun n => n * n % 4 == 0 || n * n % 4 == 1) = true := by
  decide

end QBPToolcheck.T01

#print axioms QBPToolcheck.T01.fano_pair_on_unique_line
#print axioms QBPToolcheck.T01.fanoLines_length
#print axioms QBPToolcheck.T01.qtab_anticomm
#print axioms QBPToolcheck.T01.qtab_sq_neg_one
#print axioms QBPToolcheck.T01.bool_table
