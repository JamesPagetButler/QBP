/- Fixture (Red Team finding 9, probe i): a dependency CYCLE (an inductive and its constructor)
   resting on `sorryAx`. The audit's closure must equal Lean's `collectAxioms` for every
   declaration, including `I` and `uses_type`. -/
namespace AuditFixture.Cycle

def bad : Nat := sorry

inductive I where
  | mk : bad = bad → I

def uses_type : I → True := fun _ => trivial

theorem clean : (1 : Nat) = 1 := rfl

end AuditFixture.Cycle
