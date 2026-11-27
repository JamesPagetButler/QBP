import AuditFixture.ScopeA import AuditFixture.ScopeHidden
/- Fixture (Red Team finding 4, probe h1): two imports on ONE line (valid Lean). -/
namespace AuditFixture.ScopeRoot

theorem root_fine : (2 : Nat) = 2 := rfl

end AuditFixture.ScopeRoot
