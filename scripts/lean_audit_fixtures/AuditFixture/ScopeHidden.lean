/- Fixture (Red Team finding 4, probe h1): imported by ScopeRoot on the SAME line as ScopeA, where
   a line-anchored import regex does not see it. Lean imports it, so the audit must see its
   `sorry`. -/
namespace AuditFixture.ScopeHidden

theorem by_sorry : 2 + 2 = 5 := by sorry

end AuditFixture.ScopeHidden
