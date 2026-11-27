/- Fixture (PR #829 Red Team r7, probe D2): the B3 `binder_predicate` desync hiding a `def vac :
   True` (not a theorem) from the token gate. The vacuity check must flag exactly `vac`. -/
namespace AuditFixture.VacB3Def

binder_predicate x " zz\" " y:term => `($x = $y)
theorem t : ∃ x zz" " /- ", (1 : Nat) = 1 := by exact ⟨_, rfl, rfl⟩
def vac : True := trivial
def close : String := "-/"

end AuditFixture.VacB3Def
