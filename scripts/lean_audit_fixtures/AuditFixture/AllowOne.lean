/- Fixture for the #827 allowlist: ONE native_decide declaration (allowlisted in the test). -/
namespace AuditFixture.AllowOne

theorem allowed_native : (List.range 10).sum = 45 := by
  native_decide

end AuditFixture.AllowOne
