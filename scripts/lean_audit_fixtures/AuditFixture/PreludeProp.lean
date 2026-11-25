prelude
/- Fixture (PR #829 Red Team r2 finding 3, probe T3): a `prelude` module (no `Init`) that
   declares its OWN `axiom propext : False` and proves `False` from it. Matched by name alone,
   `propext` is one of the standard three and `bad` would PASS. The auditor reports what the
   name denotes (kind, module, fingerprint); it is not the toolchain's `Init.Core.propext`, so
   the audit must FAIL. -/
namespace AuditFixture.PreludeProp

inductive False : Prop

end AuditFixture.PreludeProp

axiom propext : AuditFixture.PreludeProp.False

theorem AuditFixture.PreludeProp.bad : AuditFixture.PreludeProp.False := propext
