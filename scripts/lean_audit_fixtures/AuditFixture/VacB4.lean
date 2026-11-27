/- Fixture (PR #829 Red Team r6, probe B4): `run_cmd` elaborating a `notation` command parsed from a string declares the token `zz"`, then the r4
   desync hides `theorem vac : True` from the Python token gate (the gate PASSES this file;
   Lean compiles it). The SEMANTIC vacuity check of the axiom audit decides on the term the
   kernel accepted and must FAIL naming exactly `vac`, whatever the lexer saw. -/
import Lean

namespace AuditFixture.VacB4

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  match Parser.runParserCategory env `command "notation \"zz\\\"\" x => x" with
  | .ok stx => elabCommand stx
  | .error e => throwError e

def a : String := zz" " /- "
theorem vac : True := by trivial
def close : String := "-/"

end AuditFixture.VacB4
