/-
TOOLCHECK MF09 — MUST-FAIL control: a same-line `#print axioms` after NON-ASCII text
(Gemini r3 (e) on PR #824).

If the grader computed a site's column in a different unit from Lean's `pos.column`
(characters vs UTF-8 bytes), the multi-byte prefix `αβγ` would shift the expected column,
Lean's real report for `dirty` would be discarded as "unpositioned", and a pass-labelled
file would silently pass. Probe (v4.30.0): Lean's column is the CODEPOINT offset (in the probe
`def αβγ : Nat := 1 #print axioms dirty`: column 19, byte offset 22). The grader computes the
column in that unit from the original
source line (`LEAN_COLUMN_UNIT`), and `selftest_grader.py` re-checks the unit on this
file's real Lean output. The astral `𝔽` (U+1D53D, one codepoint, TWO UTF-16 units, four
bytes) makes the three units differ, so the pin also catches a switch to UTF-16 (Red Team
finding 5 on PR #824). `dirty` rests on a user axiom; the audit is the only detector.

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: axiom QBPToolcheck.MF09.dirty QBPToolcheck.MF09.cheat
TOOLCHECK-EXPECT: axiom-nonstd QBPToolcheck.MF09.dirty
-/

namespace QBPToolcheck.MF09

/-- The cheat. -/
axiom cheat : False

theorem clean : (1 : Nat) = 1 := rfl

theorem dirty : (1 : Nat) = 2 := cheat.elim

end QBPToolcheck.MF09

#print axioms QBPToolcheck.MF09.clean
def QBPToolcheck.MF09.αβγ : Nat := 1 /- 𝔽 -/ #print axioms QBPToolcheck.MF09.dirty
