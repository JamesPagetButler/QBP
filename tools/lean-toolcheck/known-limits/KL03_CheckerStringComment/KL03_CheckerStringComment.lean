/-
TOOLCHECK KL03 — KNOWN LIMIT of the FOUNDATIONS CHECKER (report-only) + a hard audit
expectation: a string literal containing a comment opener blinds the checker's comment
stripper (found while fixing Gemini (6) on PR #824).

`scripts/check_lean_foundations.py` strips comments with a non-greedy regex that does not
know about string literals. The string in `opener` below contains the two-character block
comment opener, so the checker deletes everything from there to the closer in the trailing
comment — including the `native_decide` proof in between — and ACCEPTS the file. Lean
itself reads the string as a string, compiles the `native_decide`, and the axiom audit
reports a non-standard native axiom: that detection is a HARD expectation (a miss fails
the suite). The checker gap is recorded as report-only; fixing the checker is outside
#823 W5 (this PR changes no gate script).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.KL03.hidden_native
TOOLCHECK-EXPECT: known-limit checker-accepts
-/

namespace QBPToolcheck.KL03

/-- A string whose text happens to contain a comment opener. -/
def opener : String := "/-"

-- Proved the forbidden way; the checker cannot see it (no doc comment here: its closer would end the blind span early).
theorem hidden_native : (List.range 10).sum = 45 := by
  native_decide

/- a trailing comment whose closer ends the checker's blind span -/

end QBPToolcheck.KL03

#print axioms QBPToolcheck.KL03.hidden_native
