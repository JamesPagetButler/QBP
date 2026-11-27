/- Fixture (PR #829 Red Team r6, probe B6): `@[term_parser]` on a hand-written `ParserDescr` plus `@[term_elab]` declares the token `zz"`, then the r4
   desync hides `theorem vac : True` from the Python token gate (the gate PASSES this file;
   Lean compiles it). The SEMANTIC vacuity check of the axiom audit decides on the term the
   kernel accepted and must FAIL naming exactly `vac`, whatever the lexer saw. -/
import Lean

namespace AuditFixture.VacB6

@[term_parser] def zzP : Lean.ParserDescr :=
  Lean.ParserDescr.node `AuditFixture.VacB6.zz 1024
    (Lean.ParserDescr.binary `andthen (Lean.ParserDescr.symbol "zz\"") (Lean.ParserDescr.cat `term 0))
@[term_elab AuditFixture.VacB6.zz] def zzE : Lean.Elab.Term.TermElab :=
  fun stx ty => Lean.Elab.Term.elabTerm (stx.getArg 1) ty

def a : String := zz" " /- "
theorem vac : True := by trivial
def close : String := "-/"

end AuditFixture.VacB6
