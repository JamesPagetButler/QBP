/- Fixture (PR #829 Red Team r3, mutant N4): an allowlisted native_decide declaration whose
   statement the test then changes by ONE numeric literal (`≤ 50` → `≤ 51`), keeping the old
   pins. The fingerprint serialises literals, so the changed declaration must FAIL the pins. -/
namespace AuditFixture.AllowLit

theorem allowed_native : (List.range 10).sum ≤ 50 := by
  native_decide

end AuditFixture.AllowLit
