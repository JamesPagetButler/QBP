/-
TOOLCHECK MF05 — MUST-FAIL control: a user-declared `axiom` (here `cheat : False`),
the most direct untrusted-author escape (Red Team F2 on PR #824).

Lean ACCEPTS this file (exit 0, no warning). The foundations checker ACCEPTS it too:
it bans `native_decide` / `: True := by trivial` and ratchets `sorry`, but has no rule
for `axiom` — that is recorded below as a report-only known limit. The ONLY detector is
the axiom audit: `#print axioms` lists `QBPToolcheck.MF05.cheat`, a name outside
{propext, Classical.choice, Quot.sound}. If the audit misses it, the suite FAILS.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF05.one_eq_two QBPToolcheck.MF05.cheat
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.MF05.one_eq_two
TOOLCHECK-EXPECT: audit-nonstd QBPToolcheck.MF05.one_eq_two
TOOLCHECK-EXPECT: known-limit checker-accepts
-/

namespace QBPToolcheck.MF05

/-- The cheat. -/
axiom cheat : False

/-- A false statement "proved" from the cheat. -/
theorem one_eq_two : 1 = 2 := cheat.elim

end QBPToolcheck.MF05

#print axioms QBPToolcheck.MF05.one_eq_two
