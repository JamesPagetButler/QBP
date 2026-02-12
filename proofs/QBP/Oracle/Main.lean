/-
  Oracle Main: Executable entry point for generating test predictions as JSON.

  Generates predictions for Experiments 01 (Stern-Gerlach) and 01b (Angle-Dependent)
  using the Float oracle. Output is committed as tests/oracle_predictions.json
  so CI can run differential tests without needing Lean installed.

  Usage: cd proofs && lake build oracle && lake exe oracle
-/
import QBP.Oracle.FloatCompute

open QBP.Oracle

/-- Format a Float as a JSON number string with sufficient precision -/
def floatToJson (f : Float) : String :=
  let s := toString f
  if s.contains '.' then s
  else s ++ ".0"

/-- Generate a single test case as a JSON object string -/
def testCaseJson (experiment : String) (label : String) (theta : Float)
    (probUp probDown expectation : Float) : String :=
  s!"  \{\"experiment\": \"{experiment}\", \"label\": \"{label}\", " ++
  s!"\"theta_rad\": {floatToJson theta}, " ++
  s!"\"prob_up\": {floatToJson probUp}, " ++
  s!"\"prob_down\": {floatToJson probDown}, " ++
  s!"\"expectation\": {floatToJson expectation}}"

/-- Generate all test cases -/
def generateTestCases : List String := Id.run do
  let mut cases : List String := []
  let pi := Float.acos (-1.0)

  -- Experiment 01: Stern-Gerlach (θ = π/2, spin-x measured on z)
  let theta01 := pi / 2.0
  let psi01 := floatPsiAngle theta01
  cases := cases ++ [testCaseJson "01" "stern_gerlach_spin_x_on_z" theta01
    (floatProbUp psi01 floatSpinZ)
    (floatProbDown psi01 floatSpinZ)
    (floatExpectationValue psi01 floatSpinZ)]

  -- Experiment 01b: Angle-Dependent (9 angles from 0° to 180°)
  let angles := #[0.0, 22.5, 45.0, 67.5, 90.0, 112.5, 135.0, 157.5, 180.0]
  for deg in angles do
    let theta := deg * pi / 180.0
    let psi := floatPsiAngle theta
    let label := s!"angle_dep_{floatToJson deg}deg"
    cases := cases ++ [testCaseJson "01b" label theta
      (floatProbUp psi floatSpinZ)
      (floatProbDown psi floatSpinZ)
      (floatExpectationValue psi floatSpinZ)]

  -- Edge cases: exact 0, π, and 2π
  let edgeCases := #[("edge_theta_0", 0.0),
                      ("edge_theta_pi", pi),
                      ("edge_theta_2pi", 2.0 * pi)]
  for (label, theta) in edgeCases do
    let psi := floatPsiAngle theta
    cases := cases ++ [testCaseJson "edge" label theta
      (floatProbUp psi floatSpinZ)
      (floatProbDown psi floatSpinZ)
      (floatExpectationValue psi floatSpinZ)]

  return cases

/-- Join a list of strings with commas, outputting each on its own line -/
def joinWithCommas : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ ",\n" ++ joinWithCommas xs

def main : IO Unit := do
  let cases := generateTestCases
  IO.println "["
  IO.println (joinWithCommas cases)
  IO.println "]"
