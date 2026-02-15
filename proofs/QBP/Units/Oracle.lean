/-
  Float Oracle for SI Conversions

  Computable Float versions of the verified definitions in Constants.lean
  and ScaleFactors.lean. Mirrors the proof structure so correctness is
  evident by inspection.

  Used to generate test vectors that Python's si_conversion.py must match
  within IEEE 754 tolerance (< 1e-15 relative error).

  Architecture follows the established QBP.Oracle pattern:
    Real (proven) → Float (computable) → JSON (test vectors) → Python (verified)
-/

namespace QBP.Units.Oracle

/-! ## Physical Constants (Float) -/

/-- h = 6.62607015 × 10⁻³⁴ J⋅s (mirrors h_SI) -/
def h_SI : Float := 6.62607015e-34

/-- e = 1.602176634 × 10⁻¹⁹ C (mirrors e_SI) -/
def e_SI : Float := 1.602176634e-19

/-- c = 299792458 m/s (mirrors c_SI) -/
def c_SI : Float := 299792458.0

/-- ℏ = h/(2π) (mirrors hbar_SI) -/
def hbar_SI : Float := h_SI / (2.0 * 3.14159265358979323846)

/-- eV in joules (mirrors eV_in_J) -/
def eV_in_J : Float := e_SI

/-! ## BPM Code Parameters (Float) -/

/-- ℏ_code = 1 (mirrors hbar_code) -/
def hbar_code : Float := 1.0

/-- m_code = 0.5 (mirrors m_code) -/
def m_code : Float := 0.5

/-- k₀_code = 20 (mirrors k0_code) -/
def k0_code : Float := 20.0

/-- v_z_code = 40 (mirrors v_z_code, proven = 40) -/
def v_z_code : Float := hbar_code * k0_code / m_code

/-! ## Scale Factor Computation (Float) -/

/-- Scale factors for a given particle. Mirrors ScaleFactors definitions. -/
structure FloatScaleFactors where
  mass_si : Float
  lambda_si : Float
  L0 : Float
  E0 : Float
  T0 : Float
  v_z_si : Float
  k_si : Float
  deriving Repr

/-- Compute scale factors from mass and wavelength (mirrors compute_scales). -/
def computeScales (m_si lambda_si : Float) : FloatScaleFactors :=
  let k := 2.0 * 3.14159265358979323846 / lambda_si
  let l0 := k0_code * lambda_si / (2.0 * 3.14159265358979323846)
  let e0 := hbar_SI ^ 2 * m_code / (m_si * l0 ^ 2 * hbar_code ^ 2)
  let t0 := hbar_SI / e0
  let vz := hbar_SI * k / m_si
  { mass_si := m_si
    lambda_si := lambda_si
    L0 := l0
    E0 := e0
    T0 := t0
    v_z_si := vz
    k_si := k }

/-! ## Conversion Functions (Float)

Mirror the Python/Real versions exactly.
-/

def convertPosition (x_code : Float) (sc : FloatScaleFactors) : Float :=
  x_code * sc.L0

def convertLengthToCode (x_si : Float) (sc : FloatScaleFactors) : Float :=
  x_si / sc.L0

def convertEnergy (E_code : Float) (sc : FloatScaleFactors) : Float :=
  E_code * sc.E0

def convertEnergyToCode (E_si : Float) (sc : FloatScaleFactors) : Float :=
  E_si / sc.E0

def convertPotential (U_code : Float) (sc : FloatScaleFactors) : Float :=
  U_code * v_z_code * sc.E0 / eV_in_J

/-! ## Test Vector Generation

Standard test particles for cross-language verification.
-/

/-- Electron: m = 9.1093837015 × 10⁻³¹ kg, λ = 5 × 10⁻¹¹ m -/
def electronMass : Float := 9.1093837015e-31
def electronLambda : Float := 5.0e-11

/-- Neutron: m = 1.67492749804 × 10⁻²⁷ kg, λ = 1.8 × 10⁻¹⁰ m -/
def neutronMass : Float := 1.67492749804e-27
def neutronLambda : Float := 1.8e-10

/-- Normalize a positive Float to [1, 10) and return (mantissa, exponent). -/
private partial def normalize (f : Float) (exp : Int) : Float × Int :=
  if f >= 10.0 then normalize (f / 10.0) (exp + 1)
  else if f < 1.0 then normalize (f * 10.0) (exp - 1)
  else (f, exp)

/-- Extract n decimal digits from a Float in [0, 10). -/
private def extractDigits (f : Float) (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n + 1 =>
    let d := f.toUInt64.toNat
    let d := if d > 9 then 9 else d  -- clamp
    d :: extractDigits ((f - d.toFloat) * 10.0) n

/-- Format a Float in scientific notation with 15 significant digits.
    Pure Lean implementation — no C FFI needed.
    Returns e.g. "6.626070150000000e-34" -/
def floatToScientific (f : Float) : String :=
  if f == 0.0 then "0.0"
  else
    let abs_f := if f < 0.0 then -f else f
    let sign := if f < 0.0 then "-" else ""
    let (mantissa, exp) := normalize abs_f 0
    let digits := extractDigits mantissa 16
    let first := digits.head!
    let rest := digits.tail!
    let restStr := String.join (rest.map (fun d => toString d))
    s!"{sign}{first}.{restStr}e{if exp >= 0 then "+" else ""}{exp}"

/-! ## Structured JSON Builder

Eliminates manual comma placement — the `jsonObj` and `jsonArr` helpers
handle separators automatically, preventing the class of bugs where a
missing or extra comma produces invalid JSON.
-/

/-- Build a JSON object from key-value pairs. Handles comma separation. -/
def jsonObj (pairs : List (String × String)) : String :=
  "{" ++ String.intercalate ", " (pairs.map fun (k, v) => "\"" ++ k ++ "\": " ++ v) ++ "}"

/-- Build a JSON array from elements. Handles comma separation. -/
def jsonArr (items : List String) : String :=
  "[" ++ String.intercalate ", " items ++ "]"

/-- JSON-encode a string value. -/
def jsonStr (s : String) : String := "\"" ++ s ++ "\""

/-- Generate a JSON object for one test particle's scale factors. -/
def scaleFactorsToJson (name : String) (sc : FloatScaleFactors) : String :=
  jsonObj [
    ("particle", jsonStr name),
    ("mass_si", floatToScientific sc.mass_si),
    ("lambda_si", floatToScientific sc.lambda_si),
    ("L0", floatToScientific sc.L0),
    ("E0", floatToScientific sc.E0),
    ("T0", floatToScientific sc.T0),
    ("v_z_si", floatToScientific sc.v_z_si),
    ("k_si", floatToScientific sc.k_si)
  ]

/-- Generate round-trip test vectors for a particle. -/
def roundTripToJson (name : String) (sc : FloatScaleFactors) : String :=
  let x_code := 3.7
  let x_si := convertPosition x_code sc
  let x_back := convertLengthToCode x_si sc
  let E_code := 5.5
  let E_si := convertEnergy E_code sc
  let E_back := convertEnergyToCode E_si sc
  let U_code := 10.0
  let U_eV := convertPotential U_code sc
  jsonObj [
    ("particle", jsonStr name),
    ("position_code", floatToScientific x_code),
    ("position_si", floatToScientific x_si),
    ("position_roundtrip", floatToScientific x_back),
    ("energy_code", floatToScientific E_code),
    ("energy_si", floatToScientific E_si),
    ("energy_roundtrip", floatToScientific E_back),
    ("potential_code", floatToScientific U_code),
    ("potential_eV", floatToScientific U_eV)
  ]

end QBP.Units.Oracle
