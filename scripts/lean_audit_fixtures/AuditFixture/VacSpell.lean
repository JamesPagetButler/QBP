/- Fixture (PR #829 Red Team r6, V1): vacuous statements in plain spellings the old `: True :=`
   regex misses, no lexer trick at all. Each must be flagged by the semantic vacuity check. -/
namespace AuditFixture.VacSpell

def T : Prop := True

theorem v1 : (True) := trivial
theorem v2 : id True := trivial
theorem v3 : True ∧ True := ⟨trivial, trivial⟩
theorem v4 : ∀ n : Nat, True := fun _ => trivial
theorem v5 : T := trivial
theorem v6 (p : Prop) : p → True := fun _ => trivial
theorem v7 : True ↔ True := Iff.rfl

end AuditFixture.VacSpell
