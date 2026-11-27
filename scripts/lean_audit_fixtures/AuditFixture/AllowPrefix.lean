/- Fixture (Red Team M2): a declaration whose name EXTENDS the allowlisted one. Only the exactly
   named declaration (and its axiom) may pass; `allowed_native.extra` must FAIL. -/
namespace AuditFixture.AllowPrefix

theorem allowed_native : (List.range 10).sum = 45 := by
  native_decide

theorem allowed_native.extra : (List.range 10).sum = 45 := allowed_native

end AuditFixture.AllowPrefix
