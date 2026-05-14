import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

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
