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

  -- Output JSON
  IO.println "{"
  IO.println "  \"generator\": \"QBP Lean 4 Oracle\","
  IO.println s!"  \"v_z_code\": {floatToScientific v_z_code},"
  IO.println s!"  \"hbar_SI\": {floatToScientific hbar_SI},"
  IO.println s!"  \"eV_in_J\": {floatToScientific eV_in_J},"

  -- Scale factors
  IO.println "  \"scale_factors\": ["
  IO.println s!"    {scaleFactorsToJson "electron" electronScales},"
  IO.println s!"    {scaleFactorsToJson "neutron" neutronScales}"
  IO.println "  ],"

  -- Round-trip tests
  IO.println "  \"round_trips\": ["
  IO.println s!"    {roundTripToJson "electron" electronScales},"
  IO.println s!"    {roundTripToJson "neutron" neutronScales}"
  IO.println "  ]"

  IO.println "}"
