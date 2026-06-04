import PhysleanBridge.SpinMeasurement

/-!
# `physlean_oracle` executable (AC-T2)

Emits, in QBP's `oracle_predictions.json` schema, the spin-1/2 angle-dependent
measurement predictions for the five Exp-01b angles `{0, 22.5, 45, 67.5, 90}°`.

## What is verified vs. what is computed (read this — it is the honesty boundary)

PhysLean's `POVM.measure` / `MState` / `HermitianMat` stack is `noncomputable`
(it lives over `ℝ`/`ℂ` with `RCLike.re`, matrix traces, CFC square roots, …).
There is **no** way to *run* it as compiled code, and even if there were, doing so
would be the `#eval`/`native_decide` trusted-compiler hole the federation Lean
standard forbids.  So this executable does **not** evaluate PhysLean's measurement
numerically.

Instead, the independence lives in the **proofs** in `SpinMeasurement.lean`:

* `probUp_eq      : (zBasisPOVM.measure (MState.pure (spinKet θ))) 0 = cos²(θ/2)`
* `probDown_eq    : (zBasisPOVM.measure (MState.pure (spinKet θ))) 1 = sin²(θ/2)`
* `expectation_eq : (…0) − (…1) = cos θ`

each kernel-checked to depend only on `{propext, Classical.choice, Quot.sound}`.
Those theorems establish — from PhysLean's Born-rule machinery, not from any QBP
formula — that the closed-form law is `cos²(θ/2)` / `sin²(θ/2)` / `cos θ`.

This executable then evaluates **that proven closed form** at the five angles using
`Float`.  The `Float` arithmetic is an *unverified numeric transcription* of the
proven law — it is the trust boundary, stated openly.  It is sound to use here
because the *form* of the law is what PhysLean independently certifies; the diff
against QBP's oracle is then a check that two independent derivations of the same
proven law agree numerically.  We are NOT presenting `Float`/`#eval` output as a
proof of any proposition (that would violate the standard) — the propositions are
proved in `SpinMeasurement.lean`; here we only tabulate.
-/

namespace PhysleanBridge.Oracle

/-- The five Exp-01b angles, in radians, paired with their QBP labels.
Values match `tests/oracle_predictions.json` rows. -/
def angles : List (String × Float) :=
  [ ("angle_dep_0.000000deg",  0.0)
  , ("angle_dep_22.500000deg", 0.392699)
  , ("angle_dep_45.000000deg", 0.785398)
  , ("angle_dep_67.500000deg", 1.178097)
  , ("angle_dep_90.000000deg", 1.570796) ]

/-- prob_up evaluated from the PROVEN closed form `cos²(θ/2)` (`probUp_eq`). -/
def probUp (θ : Float) : Float := (Float.cos (θ / 2)) ^ 2

/-- prob_down evaluated from the PROVEN closed form `sin²(θ/2)` (`probDown_eq`). -/
def probDown (θ : Float) : Float := (Float.sin (θ / 2)) ^ 2

/-- expectation evaluated from the PROVEN closed form `cos θ` (`expectation_eq`). -/
def expectation (θ : Float) : Float := Float.cos θ

/-- Format a Float to 6 decimal places (matching the oracle's `%f` formatting). -/
def fmt6 (x : Float) : String :=
  let neg := x < 0
  let a := if neg then -x else x
  let scaled := (a * 1000000.0 + 0.5).floor
  let n := scaled.toUInt64.toNat
  let intPart := n / 1000000
  let fracPart := n % 1000000
  let fracStr := toString fracPart
  let pad := String.mk (List.replicate (6 - fracStr.length) '0')
  (if neg && n != 0 then "-" else "") ++ toString intPart ++ "." ++ pad ++ fracStr

/-- One JSON object row in QBP's schema. -/
def rowJson (label : String) (θ : Float) : String :=
  "  {\"experiment\": \"01b\", \"label\": \"" ++ label ++
  "\", \"theta_rad\": " ++ fmt6 θ ++
  ", \"prob_up\": " ++ fmt6 (probUp θ) ++
  ", \"prob_down\": " ++ fmt6 (probDown θ) ++
  ", \"expectation\": " ++ fmt6 (expectation θ) ++ "}"

def emit : String :=
  let rows := angles.map (fun (lbl, θ) => rowJson lbl θ)
  "[\n" ++ String.intercalate ",\n" rows ++ "\n]"

end PhysleanBridge.Oracle

def main : IO Unit :=
  IO.println PhysleanBridge.Oracle.emit
