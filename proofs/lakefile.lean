import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «QBPProofs» where
  -- Package configuration

@[default_target]
lean_lib «QBP» where
  roots := #[`QBP]

-- Phase 4d: Float oracle executable for differential testing
lean_exe «oracle» where
  root := `QBP.Oracle.Main
