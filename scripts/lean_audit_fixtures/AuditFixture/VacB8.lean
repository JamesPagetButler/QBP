/- Fixture (PR #829 Red Team r6, probe B8): `#eval` in `CommandElabM` elaborating a parsed `notation` command declares the token `zz"`, then the r4
   desync hides `theorem vac : True` from the Python token gate (the gate PASSES this file;
   Lean compiles it). The SEMANTIC vacuity check of the axiom audit decides on the term the
   kernel accepted and must FAIL naming exactly `vac`, whatever the lexer saw. -/
import Lean

namespace AuditFixture.VacB8

open Lean Elab Command in
#eval show CommandElabM Unit from do
  match Parser.runParserCategory (← getEnv) `command "notation \"zz\\\"\" x => x" with
  | .ok stx => elabCommand stx
  | .error e => throwError e

def a : String := zz" " /- "
theorem vac : True := by trivial
def close : String := "-/"

end AuditFixture.VacB8
