import Lake
open Lake DSL

-- Mathlib pin (foundations rebuild Phase 0, housekeeping item §2 in discovery
-- response action items): pinned to the SHA already resolved in
-- proofs/lake-manifest.json so `lake update` is reproducible across machines.
-- This SHA corresponds to Mathlib at a state compatible with toolchain
-- `leanprover/lean4:v4.30.0-rc2` (see proofs/lean-toolchain). To bump:
-- 1. update this @ "<sha>" to a known-good Mathlib commit on the same
--    Lean major version, 2. run `lake update`, 3. verify zero-sorry rebuild.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "215c5f44e65f6e8431452880ebf0d433a3c00747"

package «QBPProofs» where
  -- Package configuration

@[default_target]
lean_lib «QBP» where
  roots := #[`QBP]

-- Sprint 12 inherited Lean corpus (folded from archive/lean-project/ per #81 PR8).
-- These files were authored on toolchain v4.18.0; this Lake project is v4.30.0-rc2.
-- Toolchain migration is the work — see paper/Sprint12-Inherited-Reconciliation.md.
-- Original package: «qbp»; renamed to «QBPSprint12» to avoid collision with «QBP» above.
lean_lib «QBPSprint12» where
  srcDir := "Sprint12-Inherited"
  roots := #[`Bi2Se3, `Crystallisation, `Elements, `Graphene, `Kitaev, `Quaternion, `Sedenion]

-- Phase 4d: Float oracle executable for differential testing
lean_exe «oracle» where
  root := `QBP.Oracle.Main

-- SI conversion test vector generator
lean_exe «gen_test_vectors» where
  root := `QBP.Units.GenTestVectors
