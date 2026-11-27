/- Fixture for the #827 allowlist: the allowlisted declaration PLUS a second native_decide
   in the same file — the second must fail (entries are per declaration, never per file). -/
namespace AuditFixture.AllowTwo

theorem allowed_native : (List.range 10).sum = 45 := by
  native_decide

theorem second_native : (List.range 5).sum = 10 := by
  native_decide

end AuditFixture.AllowTwo
