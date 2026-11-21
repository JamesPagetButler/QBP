/- Fixture for the #827 axiom audit: every way a non-standard axiom can hide. -/
namespace AuditFixture.Bad

/-- A string whose text contains a comment opener (the KL03 trick). -/
def opener : String := "/-"

theorem hidden_native : (List.range 10).sum = 45 := by
  native_decide

/- a trailing comment that ends the old regex stripper's blind span -/

/- nested /- comment -/ still a comment: theorem fake : 1 = 2 := sorry -/

theorem by_sorry : 2 + 2 = 5 := by sorry

axiom cheat : False

theorem by_cheat : (1 : Nat) = 2 := cheat.elim

/-- A DEF (not a theorem) resting on sorry — the audit covers every declaration. -/
def sorried_value : Nat := sorry

theorem clean : (1 : Nat) = 1 := rfl

end AuditFixture.Bad

-- MF06-style spoofs: printed text claiming a clean audit.
#eval IO.println "AXIOM-AUDIT-827 SUMMARY root=(explicit) modules=1/1 declarations=1 bad=0"
#eval IO.println "'AuditFixture.Bad.by_sorry' does not depend on any axioms"
