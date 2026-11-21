/-
TOOLCHECK KL01 — KNOWN LIMIT (report-only, never fails the suite): vacuous statements
that the toolchain gates CANNOT see (Red Team F3 on PR #824).

Both theorems below assert nothing useful, yet:
  - the foundations checker ACCEPTS the file (its vacuity rule is a regex on the
    literal `: True :=`; neither statement is spelled that way), and
  - `#print axioms` is CLEAN for both (`does not depend on any axioms`).
`alternativity` is the #472 shape (an "alternativity theorem" that proves `True`)
hidden behind a beta-redex. The vacuity check is SYNTACTIC ONLY; the defence for these
is statement-level human review. Hardening the checker is out of #823 W5's scope.

The grader reports each line as "confirmed" (limit still there) or "CHANGED" (a tool
now catches it — re-read at the next bump).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: known-limit checker-accepts
TOOLCHECK-EXPECT: known-limit audit-clean QBPToolcheck.KL01.refl_implies_true
TOOLCHECK-EXPECT: known-limit audit-clean QBPToolcheck.KL01.alternativity
-/

namespace QBPToolcheck.KL01

/-- Vacuous: the conclusion is `True`, behind an implication. -/
theorem refl_implies_true (x : Nat) : x = x → True := fun _ => trivial

/-- Vacuous: `(fun _ => True) 3` beta-reduces to `True` (the #472 shape, disguised). -/
theorem alternativity : (fun (_ : Nat) => True) 3 := trivial

end QBPToolcheck.KL01

#print axioms QBPToolcheck.KL01.refl_implies_true
#print axioms QBPToolcheck.KL01.alternativity
