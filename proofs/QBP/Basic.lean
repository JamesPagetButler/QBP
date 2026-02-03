import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion

namespace QBP

/-- Use mathlib's quaternion type over reals -/
abbrev Q := Quaternion ℝ

/-- Axiom 1: State is a unit quaternion (|ψ|² = 1) -/
def isUnitQuaternion (q : Q) : Prop := q.normSq = 1

/-- Axiom 2: Observable is a pure quaternion (real part = 0) -/
def isPureQuaternion (q : Q) : Prop := q.re = 0

/-- Example theorem: pure quaternion has zero real part -/
theorem pure_has_zero_re (q : Q) (h : isPureQuaternion q) : q.re = 0 := h

/-- The three standard spin observables -/
def SPIN_X : Q := ⟨0, 1, 0, 0⟩
def SPIN_Y : Q := ⟨0, 0, 1, 0⟩
def SPIN_Z : Q := ⟨0, 0, 0, 1⟩

/-- SPIN_X is a pure quaternion -/
theorem spin_x_is_pure : isPureQuaternion SPIN_X := rfl

end QBP
