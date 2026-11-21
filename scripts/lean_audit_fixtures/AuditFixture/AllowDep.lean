/- Fixture for the #827 allowlist's TRANSITIVITY (Cartan, seq 5688): the excepted declaration
   plus a theorem that USES it. The dependent inherits the native axiom in its closure, has no
   allowlist entry of its own, and must FAIL. -/
namespace AuditFixture.AllowDep

theorem allowed_native : (List.range 10).sum = 45 := by
  native_decide

theorem uses_allowed : 45 = (List.range 10).sum := allowed_native.symm

end AuditFixture.AllowDep
