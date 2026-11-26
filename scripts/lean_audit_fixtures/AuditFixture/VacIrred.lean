/- Fixture (PR #829 Red Team r7 finding 2, probe E2): an `@[irreducible]` def unfolding to True.
   The check reduces at `.all` transparency, so `vi` must be flagged. -/
namespace AuditFixture.VacIrred

@[irreducible] def T : Prop := True

theorem vi : T := by unfold T; trivial

end AuditFixture.VacIrred
