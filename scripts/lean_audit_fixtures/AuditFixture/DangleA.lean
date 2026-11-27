/- Fixture (PR #829 Red Team r3, dangling references): the module that the test REPLACES, after
   DangleB is built, by a compile of a different source that lacks `helper` (an inconsistent
   .olean set, as in the S1 olean-substitution probe). `helper` rests on `sorryAx`. -/
namespace AuditFixture.DangleA

def helper : Nat := sorry

end AuditFixture.DangleA
