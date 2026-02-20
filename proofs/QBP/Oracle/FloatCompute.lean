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

/-- General state on Bloch sphere: ψ(θ,φ) = sinθ cosφ·i + sinθ sinφ·j + cosθ·k
    Generalizes floatPsiAngle to arbitrary 3D directions (#211) -/
def floatPsiGeneral (theta phi : Float) : QFloat :=
  QFloat.pure (Float.sin theta * Float.cos phi)
              (Float.sin theta * Float.sin phi)
              (Float.cos theta)

/-- Symplectic form: construct quaternion from complex components ψ₀ = (re₀, im₀), ψ₁ = (re₁, im₁)
    (mirrors QBP.Experiments.DoubleSlit.sympForm) -/
def floatSympForm (re₀ im₀ re₁ im₁ : Float) : QFloat :=
  { re := re₀, imI := im₀, imJ := re₁, imK := im₁ }

/-- Norm squared of a quaternion viewed as symplectic form: |ψ₀|² + |ψ₁|²
    (mirrors QBP.Experiments.DoubleSlit.normSq_sympForm) -/
def floatNormSqSymp (q : QFloat) : Float :=
  q.re * q.re + q.imI * q.imI + q.imJ * q.imJ + q.imK * q.imK

/-- Visibility: V = (Imax - Imin) / (Imax + Imin)
    (mirrors QBP.Experiments.DoubleSlit.visibility) -/
def floatVisibility (imax imin : Float) : Float :=
  (imax - imin) / (imax + imin)

/-- Fraunhofer intensity: I₀ · cos²(π·d·x/(λ·L))
    (mirrors QBP.Optics.Fraunhofer.fraunhoferIntensity) -/
def floatFraunhoferIntensity (i0 d lam l x : Float) : Float :=
  let arg := Float.acos (-1.0) * d * x / (lam * l)
  i0 * (Float.cos arg) * (Float.cos arg)

/-- Fringe spacing: Δx = λ·L/d
    (mirrors QBP.Optics.Fraunhofer.fringeSpacing) -/
def floatFringeSpacing (lam l d : Float) : Float :=
  lam * l / d

/-- Quaternionic fraction: η = |ψ₁|² / (|ψ₀|² + |ψ₁|²)
    (mirrors QBP.Experiments.DoubleSlit.quatFraction) -/
def floatQuatFraction (normSq0 normSq1 : Float) : Float :=
  normSq1 / (normSq0 + normSq1)

/-- Coupling decomposition: (U₀ + U₁j)(ψ₀ + ψ₁j) result
    (mirrors QBP.Experiments.DoubleSlit.coupling_decomposition) -/
def floatCouplingDecomposition (u0 u1 a0 b0 a1 b1 : Float) : QFloat :=
  { re  := u0 * a0 - u1 * a1
  , imI := u0 * b0 + u1 * b1
  , imJ := u0 * a1 + u1 * a0
  , imK := u0 * b1 - u1 * b0 }

/-- Decay constant: κ = U₁ · d
    (mirrors QBP.Experiments.DoubleSlit.decayConstant) -/
def floatDecayConstant (u1 d : Float) : Float := u1 * d

/-- Decay length: L_decay = 1/κ
    (mirrors QBP.Experiments.DoubleSlit.decayLength) -/
def floatDecayLength (κ : Float) : Float := 1.0 / κ

end QBP.Oracle
