/- Fixture (Red Team finding 9, probe i): dependency CYCLES (an inductive and its constructor)
   resting on `sorryAx`. The audit's closure must equal Lean's `collectAxioms` for every
   declaration, including each inductive and `uses_type`. A non-SCC closure gets an inductive
   wrong only when the search reaches the constructor before the inductive, which depends on the
   enumeration order; six independent cycles make that order matter for at least one of them
   (mutation run: the non-SCC mutant M16b is killed). -/
namespace AuditFixture.Cycle

def bad : Nat := sorry

inductive I where
  | mk : bad = bad → I

def uses_type : I → True := fun _ => trivial

inductive I2 where
  | mk : bad = bad → I2

inductive I3 where
  | mk : bad = bad → I3

inductive I4 where
  | mk : bad = bad → I4

inductive I5 where
  | mk : bad = bad → I5

inductive I6 where
  | mk : bad = bad → I6

def uses_all : I2 → I3 → I4 → I5 → I6 → True := fun _ _ _ _ _ => trivial

theorem clean : (1 : Nat) = 1 := rfl

end AuditFixture.Cycle
