/- Fixture (PR #829 Red Team r6): must-PASS controls for the vacuity check: real statements,
   some proved by `trivial`, none reducing to `True`. -/
namespace AuditFixture.VacControl

theorem ok1 : (2 : Nat) + 2 = 4 := by trivial
theorem ok2 : ∀ n : Nat, n = n := fun _ => rfl
theorem ok3 : True → (1 : Nat) = 1 := fun _ => rfl
theorem ok4 : ∃ n : Nat, n = 0 := ⟨0, rfl⟩
theorem ok5 : True ∧ (1 : Nat) = 1 := ⟨trivial, rfl⟩

end AuditFixture.VacControl
