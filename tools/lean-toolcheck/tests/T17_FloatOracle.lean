/-
TOOLCHECK T17 — the computable `Float` / `IO` surface of QBP's differential-testing
oracle: `structure … deriving Repr` over `Float`, `Float` arithmetic and `toString`,
`String` building, and a `def main : IO Unit` that type-checks.

Feature: the oracle executables (`lake exe oracle`, `lake exe gen_test_vectors`) mirror
verified ℝ definitions in `Float` and print JSON. This is NOT proof (standard §1: `#eval`
and compiled code are not evidence) — it is a *compile* check that the `Float`/`String`/
`IO` API the oracle uses still elaborates, so a core-library rename (e.g. in
`Float`/`String`) is caught before the oracle build breaks. Nothing here is `#eval`'d.
The one theorem below is about the `String` structure, not about `Float` values.

Used by (QBP, 2026-11-20 grep): `QBP/Oracle/FloatCompute.lean` (`QFloat` with
`deriving Repr`), `QBP/Oracle/Main.lean` (`def main : IO Unit`, `IO.println`),
`QBP/Units/Oracle.lean` (`deriving Repr, Inhabited`), `QBP/Units/GenTestVectors.lean`.

TOOLCHECK-EXPECT: pass
-/

namespace QBPToolcheck.T17

/-- Float quaternion, as in `QBP.Oracle.QFloat`. -/
structure QFloat where
  re : Float
  imI : Float
  imJ : Float
  imK : Float
  deriving Repr, Inhabited

/-- Vector-part dot product. -/
def vecDot (a b : QFloat) : Float := a.imI * b.imI + a.imJ * b.imJ + a.imK * b.imK

/-- `P(+) = (1 + ⟨O⟩)/2`. -/
def probUp (psi obs : QFloat) : Float := (1.0 + vecDot psi obs) / 2.0

/-- A JSON-ish line. -/
def line (x : Float) : String := "\x7B\"p\": " ++ toString x ++ "\x7D"  -- \x7B/\x7D = braces (suite rule: no literal brace in a string)

/-- Join with commas (the oracle's `joinWithCommas`). -/
def joinWithCommas : List String → String
  | [] => ""
  | [s] => s
  | s :: rest => s ++ ",\n" ++ joinWithCommas rest

/-- The oracle entry-point shape. Type-checked, never run by the suite. -/
def main : IO Unit := do
  let z : QFloat := { re := 0.0, imI := 0.0, imJ := 0.0, imK := 1.0 }
  IO.println "["
  IO.println (joinWithCommas [line (probUp z z)])
  IO.println "]"

/-- A structural fact about the pure-`String` helper (kernel-checked by `rfl`). -/
theorem join_singleton (s : String) : joinWithCommas [s] = s := rfl

end QBPToolcheck.T17

#print axioms QBPToolcheck.T17.join_singleton
