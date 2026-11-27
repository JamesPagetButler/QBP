/-
TOOLCHECK MF12 — MUST-FAIL control: an ESCAPED QUOTE in a string before a same-line
`#print axioms` site (Red Team mutant M07 on PR #824).

A lexer that ignored backslash escapes would end the string at `\"`, open a NEW string at the
closing quote, and blank the rest of the line — hiding `dirty`'s site, so `dirty` would never
be audited (fail-open). The grader's lexer must honour `\"` and see `QBPToolcheck.MF12.cheat`.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF12.dirty QBPToolcheck.MF12.cheat
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.MF12.dirty
-/

namespace QBPToolcheck.MF12

/-- The cheat. -/
axiom cheat : False

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF12

def QBPToolcheck.MF12.s : String := "a\"b" #print axioms QBPToolcheck.MF12.dirty
