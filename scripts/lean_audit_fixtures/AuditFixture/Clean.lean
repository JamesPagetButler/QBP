/- Fixture for the #827 axiom audit: a clean module (standard axioms only). -/
namespace AuditFixture.Clean

theorem add_zero' (n : Nat) : n + 0 = n := rfl

theorem em' (p : Prop) : p ∨ ¬p := Classical.em p

def double (n : Nat) : Nat := 2 * n

instance : Inhabited (Fin 3) := ⟨0⟩

inductive Color where
  | red | green
  deriving DecidableEq

end AuditFixture.Clean
