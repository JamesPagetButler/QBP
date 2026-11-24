/- Fixture (Red Team finding 3, probe e4): a FORGED match for the allowlist entries of
   `AuditFixture.AllowOne.allowed_native`. A user axiom with the native axiom's exact name states
   `1 = 2`, and a theorem with the allowlisted exact name is proved from it. The names alone
   would match; the module and fingerprint pins do not, so the audit must FAIL. -/
axiom AuditFixture.AllowOne.allowed_native._native.native_decide.ax_1_1 : (1 : Nat) = 2

theorem AuditFixture.AllowOne.allowed_native : (1 : Nat) = 2 :=
  AuditFixture.AllowOne.allowed_native._native.native_decide.ax_1_1
