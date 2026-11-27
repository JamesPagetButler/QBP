/- Fixture (Red Team M13): the allowlisted declaration rests on its native axiom PLUS `sorryAx`.
   An entry permits EXACTLY its axioms, never a superset, so this must FAIL. -/
namespace AuditFixture.AllowPlus

theorem allowed_native : (List.range 10).sum = 45 ∧ (1 : Nat) = 2 :=
  ⟨by native_decide, sorry⟩

end AuditFixture.AllowPlus
