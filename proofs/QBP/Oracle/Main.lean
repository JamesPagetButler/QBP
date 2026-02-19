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

/-- Generate a single test case as a JSON object string (xz-plane, 1 angle) -/
def testCaseJson (experiment : String) (label : String) (theta : Float)
    (probUp probDown expectation : Float) : String :=
  s!"  \{\"experiment\": \"{experiment}\", \"label\": \"{label}\", " ++
  s!"\"theta_rad\": {floatToJson theta}, " ++
  s!"\"prob_up\": {floatToJson probUp}, " ++
  s!"\"prob_down\": {floatToJson probDown}, " ++
  s!"\"expectation\": {floatToJson expectation}}"

/-- Generate a 3D test case as a JSON object string (arbitrary directions) -/
def testCase3DJson (experiment : String) (label : String)
    (theta_s phi_s theta_o phi_o : Float)
    (probUp probDown expectation : Float) : String :=
  s!"  \{\"experiment\": \"{experiment}\", \"label\": \"{label}\", " ++
  s!"\"theta_s\": {floatToJson theta_s}, \"phi_s\": {floatToJson phi_s}, " ++
  s!"\"theta_o\": {floatToJson theta_o}, \"phi_o\": {floatToJson phi_o}, " ++
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

  -- General 3D test cases (#211): arbitrary state and observable directions
  let cases3D := #[
    -- y-state measured on z (j component, previously untested)
    ("3d_y_on_z", pi / 2.0, pi / 2.0, 0.0, 0.0),
    -- y-state measured on x
    ("3d_y_on_x", pi / 2.0, pi / 2.0, pi / 2.0, 0.0),
    -- general oblique angles
    ("3d_oblique_1", pi / 6.0, pi / 4.0, pi / 3.0, pi / 2.0),
    ("3d_oblique_2", pi / 4.0, pi, 3.0 * pi / 4.0, 0.0),
    ("3d_oblique_3", 2.0 * pi / 3.0, pi / 4.0, pi / 6.0, 5.0 * pi / 4.0),
    -- same direction → P(+) = 1
    ("3d_same_dir", pi / 4.0, pi / 3.0, pi / 4.0, pi / 3.0),
    -- opposite directions → P(+) = 0
    ("3d_opposite", pi / 3.0, pi / 4.0, 2.0 * pi / 3.0, pi + pi / 4.0)
  ]
  for (label, ts, ps, to_, po) in cases3D do
    let psi := floatPsiGeneral ts ps
    let obs := floatPsiGeneral to_ po
    cases := cases ++ [testCase3DJson "3d" label ts ps to_ po
      (floatProbUp psi obs)
      (floatProbDown psi obs)
      (floatExpectationValue psi obs)]

  -- Experiment 03: Double-Slit test vectors
  let pi := Float.acos (-1.0)

  -- Coupling decomposition test: (2 + 3j)(1 + 0.5i + 0.7j + 0.3k)
  let coupResult := floatCouplingDecomposition 2.0 3.0 1.0 0.5 0.7 0.3
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"coupling_decomp\", " ++
    s!"\"re\": {floatToJson coupResult.re}, \"imI\": {floatToJson coupResult.imI}, " ++
    s!"\"imJ\": {floatToJson coupResult.imJ}, \"imK\": {floatToJson coupResult.imK}}"]

  -- Norm squared of symplectic form: ψ = (0.6, 0.8, 0.3, 0.4)
  let sympPsi := floatSympForm 0.6 0.8 0.3 0.4
  let nsq := floatNormSqSymp sympPsi
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"normSq_sympForm\", " ++
    s!"\"normSq\": {floatToJson nsq}}"]

  -- Visibility: perfect interference (Imin = 0), no interference (Imax = Imin)
  let visA := floatVisibility 1.0 0.0
  let visB := floatVisibility 1.0 1.0
  let visPartial := floatVisibility 1.0 0.3
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"visibility_perfect\", " ++
    s!"\"visibility\": {floatToJson visA}}"]
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"visibility_none\", " ++
    s!"\"visibility\": {floatToJson visB}}"]
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"visibility_partial\", " ++
    s!"\"visibility\": {floatToJson visPartial}}"]

  -- Fraunhofer intensity at maximum and minimum
  -- d=1e-6, λ=500e-9, L=1.0, I₀=1.0
  let iAtMax := floatFraunhoferIntensity 1.0 1.0e-6 500.0e-9 1.0 0.0  -- x=0 is a maximum
  let spacing := floatFringeSpacing 500.0e-9 1.0 1.0e-6
  let iAtMin := floatFraunhoferIntensity 1.0 1.0e-6 500.0e-9 1.0 (spacing / 2.0)
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"fraunhofer_at_max\", " ++
    s!"\"intensity\": {floatToJson iAtMax}}"]
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"fraunhofer_at_min\", " ++
    s!"\"intensity\": {floatToJson iAtMin}}"]
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"fringe_spacing\", " ++
    s!"\"spacing\": {floatToJson spacing}}"]

  -- Quaternionic fraction
  let eta0 := floatQuatFraction 1.0 0.0    -- pure complex: η = 0
  let etaHalf := floatQuatFraction 0.5 0.5  -- equal split: η = 0.5
  let eta1 := floatQuatFraction 0.0 1.0    -- pure quaternionic: η = 1
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"eta_zero\", " ++
    s!"\"eta\": {floatToJson eta0}}"]
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"eta_half\", " ++
    s!"\"eta\": {floatToJson etaHalf}}"]
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"eta_one\", " ++
    s!"\"eta\": {floatToJson eta1}}"]

  -- Decay constant scaling
  let kappa1 := floatDecayConstant 1.0 1.0e-6
  let kappa2 := floatDecayConstant 2.0 1.0e-6
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"decay_constant_1\", " ++
    s!"\"kappa\": {floatToJson kappa1}}"]
  cases := cases ++ [s!"  \{\"experiment\": \"03\", \"label\": \"decay_constant_2\", " ++
    s!"\"kappa\": {floatToJson kappa2}}"]

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
