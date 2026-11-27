/- Fixture (PR #829 Red Team r7 finding 3, probe F1): recursive definitions whose value is True
   (structural recursion; well-founded recursion). Unfolded with `smartUnfolding := false`. -/
namespace AuditFixture.VacRec

def T : Nat → Prop
  | 0 => True
  | n + 1 => T n

theorem r0 : T 0 := trivial
theorem r3 : T 3 := by simp [T]

def W (n : Nat) : Prop := if n = 0 then True else W (n - 1)
termination_by n
decreasing_by omega

theorem w2 : W 2 := by unfold W; simp; unfold W; simp; unfold W; simp

end AuditFixture.VacRec
