/-
TOOLCHECK MF04 — MUST-FAIL control: a deliberately FALSE closed proposition fed to
kernel `decide`.

`(2 : Fin 5) + 3 = 1` is false (`2 + 3 = 5 ≡ 0 mod 5`). Lean must REJECT the file
(non-zero exit) with `decide`'s "proposition is false" diagnostic. If Lean accepts it,
the kernel/`decide` path is unsound on the current pins and the suite FAILS loudly.
A second false claim checks the Nat-truncation trap (standard §7): over `Int`,
`1 - 2 = -1`, so claiming `= 0` must be rejected (it would be *true* over `Nat`).
The expected messages are anchored to one Lean error each, at its source line (`^19:` / `^22:`).

TOOLCHECK-EXPECT: lean-error ^19:\d+: error: Tactic `decide` proved that the proposition\s+2 \+ 3 = 1\s+is false
TOOLCHECK-EXPECT: lean-error ^22:\d+: error: Tactic `decide` proved that the proposition\s+1 - 2 = 0\s+is false
-/

namespace QBPToolcheck.MF04

/-- False: must be rejected by `decide`. -/
theorem fin5_bad : (2 : Fin 5) + 3 = 1 := by decide

/-- False over `Int` (true over `Nat` by truncation): must be rejected by `decide`. -/
theorem int_trunc_bad : (1 : Int) - 2 = 0 := by decide

end QBPToolcheck.MF04
