/-
TOOLCHECK T20 — features QBP uses that are OUTSIDE the pass-file subset: `local notation`
(QBP: `notation` 5 files) and `attribute [local simp]` (QBP: `simp` sets). Moved here from
T16 and T09 (Red Team r2 on PR #824): syntax extension and the `attribute` command can
register code that runs during elaboration, so the grader refuses them in a pass file
(`subset-refused` below confirms the refusal on real QBP-style input).

This is a COMPILE check only: it shows the current Lean still accepts these features. It is
not axiom-graded, and its `#print axioms` output is not trusted. QBP's own files that use
these features are audited by the out-of-process audit (QBP#827 / PR #829).

TOOLCHECK-EXPECT: lean-ok
TOOLCHECK-EXPECT: subset-refused
-/
import Mathlib.Tactic.Ring

namespace QBPToolcheck.T20

structure Pair where
  fst : Int
  snd : Int

def Pair.swap (p : Pair) : Pair := ⟨p.snd, p.fst⟩

local notation "⇄" p => Pair.swap p

theorem swap_swap (p : Pair) : (⇄ (⇄ p)) = p := by
  cases p
  rfl

section LocalSimp
/-- A non-simp lemma promoted locally. -/
theorem double (a : Int) : a + a = 2 * a := by ring
attribute [local simp] double

theorem local_simp_use (a : Int) : a + a + 0 = 2 * a := by simp
end LocalSimp

end QBPToolcheck.T20
