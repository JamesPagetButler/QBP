/- Fixture (PR #829 Red Team r6, probe B3): core Lean's `binder_predicate` (no import) declares the token `zz"`, then the r4
   desync hides `theorem vac : True` from the Python token gate (the gate PASSES this file;
   Lean compiles it). The SEMANTIC vacuity check of the axiom audit decides on the term the
   kernel accepted and must FAIL naming exactly `vac`, whatever the lexer saw. -/
namespace AuditFixture.VacB3

binder_predicate x " zz\" " y:term => `($x = $y)
theorem t : ∃ x zz" " /- ", True := by exact ⟨_, rfl, trivial⟩
theorem vac : True := by trivial
def close : String := "-/"

end AuditFixture.VacB3
