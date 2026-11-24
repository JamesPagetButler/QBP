/- Fixture for the #827 axiom audit, PR #829 Gemini r1 finding 1 (IDENTIFIER OVERRIDE). The
   module rests on `sorryAx` (`by_sorry`) and exports instances that change what ordinary
   operators mean in any file importing it:

   (a) `BEq Lean.Name` calling every two names equal (the first driver located its modules with
       `· == t`);
   (b) `HAdd Nat Nat Nat` dropping its second argument (the first driver counted with
       `bad + 1`);
   (c) a definition in the namespace the first driver opened (`Lean.Elab.Command`) named like
       the driver's own helper, so an unqualified `qbpAuditAxiomsOf` would be ambiguous;
   (d) Red Team finding 1 (probe e1, verbatim): `macro_rules` rewriting every `run_cmd` into a
       `run_meta` that logs a clean SUMMARY — against the first driver this PASSED.

   The audit must FAIL naming exactly `AuditFixture.InjectId.by_sorry`. -/
import Lean

namespace AuditFixture.InjectId

theorem by_sorry : 2 + 2 = 5 := by sorry

end AuditFixture.InjectId

instance (priority := high) qbpEvilBEqName : BEq Lean.Name := ⟨fun _ _ => true⟩
instance (priority := high) qbpEvilHAddNat : HAdd Nat Nat Nat := ⟨fun a _ => a⟩

def Lean.Elab.Command.qbpAuditAxiomsOf (_env : Lean.Environment) (_roots : Array Lean.Name) :
    Std.HashMap Lean.Name Lean.NameSet := {}

macro_rules
  | `(command| run_cmd $_) =>
    `(command| run_meta Lean.logInfo "AXIOM-AUDIT-827 SUMMARY root=(explicit) modules=1/1 declarations=3 bad=0")
