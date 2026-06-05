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

/-- Round a `Float` to the 6-decimal value it is emitted as (half-up at the 6th
    place). The result is the exact 6-dp decimal as a `Float`, so subsequent
    decimal arithmetic on emitted values is exact. Identical rounding to QBP's
    `round6` in `proofs/QBP/Oracle/Main.lean` and to the magnitude rounding in
    `fmt6` below — this is the single rule both backends share (#492). -/
def round6 (x : Float) : Float :=
  let neg := x < 0.0
  let a := if neg then -x else x
  let scaled := (a * 1000000.0 + 0.5).floor
  let r := scaled / 1000000.0
  if neg then -r else r

/-- `expectation` is a DERIVED field: both backends emit
    `round6(prob_up) − round6(prob_down)` by convention (#492); the physics
    comparison lives in the independently-derived probabilities. This replaces
    the previous independent `Float.cos θ` path, which rounded differently from
    the emitted probabilities at 1-ULP boundary angles (e.g. 45°). The PROVEN
    cos-θ law (`expectation_eq` in `SpinMeasurement.lean`) is unaffected — this
    is the Float EMISSION path only. -/
def expectation (θ : Float) : Float :=
  round6 (probUp θ) - round6 (probDown θ)

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

/-- One JSON object row in QBP's schema.

    `expectation` is emitted from `round6(prob_up) − round6(prob_down)` — the
    SAME 6-dp-rounded probability values emitted for `prob_up` / `prob_down`,
    making it a single-source-of-truth derivation (#492) rather than an
    independent cos-θ float path. -/
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
