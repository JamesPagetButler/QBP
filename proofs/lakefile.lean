import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «QBPProofs» where
  -- Package configuration

@[default_target]
lean_lib «QBP» where
  roots := #[`QBP]
