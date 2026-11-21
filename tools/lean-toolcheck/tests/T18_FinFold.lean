/-
TOOLCHECK T18 — kernel reduction through core `Fin` folds: `Fin.foldr` by kernel
`decide`, `Fin.foldl` by `decide +kernel`, and `Fin.foldl` structurally via
`Fin.foldl_succ`.

Feature: QBP's kernel `decide` sweeps over `Fin`-indexed tables reduce through core
list/fold definitions; changes to how those definitions reduce (lean4#14267 in v4.33.0:
`Fin.foldl` reduces in the kernel; lean4#14554 in v4.35.0: type-theoretic vs runtime
`Fin.foldl` split) move what `decide` can close and how much memory it needs. QBP never
calls `Fin.foldl` by name; this pins the reduction path (Red Team triage note on PR #824).
The companion version probe (elaborator `decide` stuck on `Fin.foldl` at v4.30.0) is
`known-limits/KL02_FinFoldlDecide/`.

Used by (indirectly): the kernel `decide` sweeps in `QBP/Foundations/Octonion32Count.lean`,
`SedenionOctonionCount.lean`, `FanoGenesis.lean`, `SeamSpectrum.lean` (Fin-indexed tables).

TOOLCHECK-EXPECT: pass
-/

namespace QBPToolcheck.T18

/-- `Fin.foldr` reduces under elaborator + kernel `decide`. -/
theorem foldr_sum : Fin.foldr 8 (fun i a => a + i.val) 0 = 28 := by decide

/-- `Fin.foldl` via `decide +kernel` (skips the elaborator's stuck whnf). -/
theorem foldl_sum_kernel : Fin.foldl 8 (fun a i => a + i.val) 0 = 28 := by decide +kernel

/-- `Fin.foldl` structurally, unfolding by the `Fin.foldl_succ` equation. -/
theorem foldl_sum_simp : Fin.foldl 3 (fun a i => a + i.val) 0 = 3 := by
  simp [Fin.foldl_succ]

end QBPToolcheck.T18

#print axioms QBPToolcheck.T18.foldr_sum
#print axioms QBPToolcheck.T18.foldl_sum_kernel
#print axioms QBPToolcheck.T18.foldl_sum_simp
