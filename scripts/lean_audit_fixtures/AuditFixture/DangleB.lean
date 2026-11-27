import AuditFixture.DangleA
/- Fixture (PR #829 Red Team r3, dangling references): uses `DangleA.helper`. Once DangleA.olean
   is replaced by a compile without `helper`, the reference DANGLES; the audit must FAIL on it,
   never count it as axiom-free. -/
namespace AuditFixture.DangleB

theorem uses : AuditFixture.DangleA.helper = AuditFixture.DangleA.helper := rfl

end AuditFixture.DangleB
