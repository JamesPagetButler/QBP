/-
TOOLCHECK MF02 — MUST-FAIL control: `native_decide` (the trusted-compiler escape).

Lean ACCEPTS this file (exit 0): the proposition is true and the compiled evaluator
says so. The suite must detect it two ways:
  (1) the foundations checker (`scripts/check_lean_foundations.py`) HARD-BANs it;
  (2) the axiom audit shows a non-standard axiom — federation standard §1/§3.
      The check is name-agnostic on purpose. Measured on v4.30.0 (BASELINE.md):
      the axiom is already a per-call one, `QBPToolcheck.MF02.by_native._native.
      native_decide.ax_1_1` — NOT `Lean.ofReduceBool` — and v4.35.0 (lean4#14953)
      removes `Lean.ofReduceBool` altogether. A check keyed on that name is blind.
If either detection is missing, the suite FAILS.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.MF02.by_native
TOOLCHECK-EXPECT: checker-reject HARD-BAN violated — native_decide: 1 occurrence
-/

namespace QBPToolcheck.MF02

/-- A true finite fact, closed the forbidden way. -/
theorem by_native : (List.range 10).sum = 45 := by
  native_decide

end QBPToolcheck.MF02

#print axioms QBPToolcheck.MF02.by_native
