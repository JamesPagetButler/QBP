/- Fixture (PR #829 Gemini r2 finding 5): an `opaque` constant whose VALUE rests on `sorryAx`
   (its type is clean). The closure must walk opaque values; the audit must name exactly
   `AuditFixture.OpaqueSorry.op` and `uses_op`, as Lean's own `collectAxioms` does. -/
namespace AuditFixture.OpaqueSorry

opaque op : Nat := sorry

def uses_op : Nat := op + 1

theorem clean : (1 : Nat) = 1 := rfl

end AuditFixture.OpaqueSorry
