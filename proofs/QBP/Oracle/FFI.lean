/-
  FFI exports: Make Float oracle functions callable from C/Go.

  These @[export] functions provide a C-compatible interface to the
  proven-correct Float oracle. Used by Phase 4e (Verified Simulation Engine)
  for Go/cgo integration.

  Fallback approach: If Lean→C shared library export proves problematic,
  the Go simulation can call `lake exe oracle` via subprocess and parse JSON.
  Both approaches use the same verified oracle code.

  C function signatures:
    double qbp_prob_up(double theta);
    double qbp_expectation(double theta);
    double qbp_prob_down(double theta);
-/
import QBP.Oracle.FloatCompute

open QBP.Oracle

/-- Probability of spin-up for state at angle θ from z-axis, measured on z -/
@[export qbp_prob_up]
def qbpProbUp (theta : Float) : Float :=
  floatProbUp (floatPsiAngle theta) floatSpinZ

/-- Expectation value for state at angle θ from z-axis, measured on z -/
@[export qbp_expectation]
def qbpExpectation (theta : Float) : Float :=
  floatExpectationValue (floatPsiAngle theta) floatSpinZ

/-- Probability of spin-down for state at angle θ from z-axis, measured on z -/
@[export qbp_prob_down]
def qbpProbDown (theta : Float) : Float :=
  floatProbDown (floatPsiAngle theta) floatSpinZ
