/-
  Float Oracle: Computable versions of QBP probability calculations.

  This module mirrors the verified definitions in QBP.Basic but uses Float
  for actual computation. The structure intentionally parallels the proofs
  so correctness is evident by inspection.

  Used by Phase 4d (Verified Differential Testing) to generate test predictions
  that are compared against Python's qphysics.py.
-/

namespace QBP.Oracle

/-- Computable quaternion using Float -/
structure QFloat where
  re  : Float
  imI : Float
  imJ : Float
  imK : Float
  deriving Repr

/-- Create a pure quaternion (mirrors QBP.vecPart) -/
def QFloat.pure (i j k : Float) : QFloat :=
  { re := 0.0, imI := i, imJ := j, imK := k }

/-- Dot product of vector parts (mirrors QBP.vecDot) -/
def floatVecDot (a b : QFloat) : Float :=
  a.imI * b.imI + a.imJ * b.imJ + a.imK * b.imK

/-- Expectation value: vecDot(ψ, O) (mirrors QBP.expectationValue) -/
def floatExpectationValue (psi obs : QFloat) : Float :=
  floatVecDot psi obs

/-- P(+) = (1 + ⟨O⟩) / 2 (mirrors QBP.probUp) -/
def floatProbUp (psi obs : QFloat) : Float :=
  (1.0 + floatExpectationValue psi obs) / 2.0

/-- P(-) = (1 - ⟨O⟩) / 2 (mirrors QBP.probDown) -/
def floatProbDown (psi obs : QFloat) : Float :=
  (1.0 - floatExpectationValue psi obs) / 2.0

/-- Spin-Z observable: k direction (mirrors QBP.SPIN_Z) -/
def floatSpinZ : QFloat := QFloat.pure 0.0 0.0 1.0

/-- Spin-X observable: i direction (mirrors QBP.SPIN_X) -/
def floatSpinX : QFloat := QFloat.pure 1.0 0.0 0.0

/-- Angle-dependent state: ψ(θ) = sin(θ)·i + cos(θ)·k
    (mirrors QBP.Experiments.AngleDependent.psiAngle) -/
def floatPsiAngle (theta : Float) : QFloat :=
  QFloat.pure (Float.sin theta) 0.0 (Float.cos theta)

/-- Norm squared of a quaternion -/
def QFloat.normSq (q : QFloat) : Float :=
  q.re * q.re + q.imI * q.imI + q.imJ * q.imJ + q.imK * q.imK

end QBP.Oracle
