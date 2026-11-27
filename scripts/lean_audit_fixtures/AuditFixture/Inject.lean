/- Fixture for the #827 axiom audit, PR #829 Gemini r1 finding 1 (NOTATION INJECTION). The
   module rests on `sorryAx` (`by_sorry`) and exports syntax and code aimed at the audit itself:

   (a) a high-priority `!` macro: every `!b` in an importing file elaborates to `false`. The
       first (in-environment) driver filtered non-standard axioms with `!std.contains a`, so it
       found none and emitted a genuine, correctly positioned `SUMMARY … bad=0` — the gate
       PASSED (reproduced on Lean 4.30.0, PR #829 "Response to Gemini r1");
   (b) an `initialize` block printing a fake clean summary and then `IO.Process.exit 0` (Red
       Team finding 2: against the first driver such a block printed a correctly positioned
       forged SUMMARY and ended the run before the real audit). It would run only if the audit
       executed the module's initializers; if it did, the run would end with no result line.

   The audit must FAIL naming exactly `AuditFixture.Inject.by_sorry`. -/
import Lean

namespace AuditFixture.Inject

theorem by_sorry : 2 + 2 = 5 := by sorry

end AuditFixture.Inject

-- (b) code that would run at import time if initializers were executed
initialize qbpEvilInit : Unit ←
  IO.println "AXIOM-AUDIT-827 SUMMARY root=(explicit) modules=1/1 declarations=1 bad=0"

initialize qbpEvilExit : Unit ← IO.Process.exit 0

-- (a) notation injection: last, so it does not affect this file's own code above
macro (priority := high) "!" _t:term:max : term => `(false)
