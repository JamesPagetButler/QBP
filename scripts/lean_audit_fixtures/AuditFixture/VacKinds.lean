/- Fixture (PR #829 Red Team r7 finding 1, probe E1): vacuous statements carried by a `def`,
   `abbrev`, `opaque` and `noncomputable def` (Lean keeps these as `defnInfo` / `opaqueInfo`, not
   theorems). Every Prop-typed constant is checked; all four must be flagged. -/
namespace AuditFixture.VacKinds

def vd : (True) := trivial
abbrev va : (True) := trivial
opaque vo : (True)
noncomputable def vn : (True) := trivial

-- a non-Prop def is not a candidate
def notProp : Nat := 1

end AuditFixture.VacKinds
