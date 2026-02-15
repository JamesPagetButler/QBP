/-
  Test Vector Generator for SI Conversion Cross-Language Verification

  Computes scale factors and conversion results for standard test particles
  and outputs JSON that Python's test suite loads and verifies against.

  Usage: lake exec gen_test_vectors > tests/fixtures/si_test_vectors.json
-/
import QBP.Units.Oracle

open QBP.Units.Oracle

def main : IO Unit := do
  let electronScales := computeScales electronMass electronLambda
  let neutronScales := computeScales neutronMass neutronLambda

  -- Build JSON using structured helpers (no manual comma placement)
  let json := jsonObj [
    ("generator", jsonStr "QBP Lean 4 Oracle"),
    ("v_z_code", floatToScientific v_z_code),
    ("hbar_SI", floatToScientific hbar_SI),
    ("eV_in_J", floatToScientific eV_in_J),
    ("scale_factors", jsonArr [
      scaleFactorsToJson "electron" electronScales,
      scaleFactorsToJson "neutron" neutronScales
    ]),
    ("round_trips", jsonArr [
      roundTripToJson "electron" electronScales,
      roundTripToJson "neutron" neutronScales
    ])
  ]
  IO.println json
