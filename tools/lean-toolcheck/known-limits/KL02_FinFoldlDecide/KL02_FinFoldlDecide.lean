/-
TOOLCHECK KL02 — KNOWN LIMIT (report-only, version probe): elaborator `decide` gets
STUCK on `Fin.foldl` on the current pins.

On v4.30.0, `Fin.foldl`'s inner loop is well-founded (irreducible by default), so
`decide` reports "did not reduce to `isTrue` or `isFalse`". `decide +kernel` and the
structural `simp [Fin.foldl_succ]` both work (tests/T18_FinFold.lean). Upstream:
lean4#14267 (v4.33.0) makes `Fin.foldl` reduce in the kernel, and lean4#14554 (v4.35.0)
splits its type-theoretic and runtime implementations. So on the #723 target this probe
is EXPECTED to report "CHANGED" — which then confirms those items landed as described.
It never fails the suite.

TOOLCHECK-EXPECT: known-limit lean-error (?s)^19:\d+: error: Tactic `decide` failed.*did not reduce to `isTrue` or `isFalse`
-/

namespace QBPToolcheck.KL02

/-- Stuck on v4.30.0 (elaborator `decide`). -/
theorem foldl_by_decide : Fin.foldl 8 (fun a i => a + i.val) 0 = 28 := by decide

end QBPToolcheck.KL02
