import Lake
open Lake DSL

/-
PhysLean ↔ QBP differential-test bridge (QBP issue #490).

This is a SIBLING project to `proofs/` — deliberately on PhysLean's toolchain
(`leanprover/lean4:v4.36.0`) and PhysLean's Mathlib pin (`v4.36.0`), NOT QBP's
own `proofs/` pin. Integration happens at the JSON boundary (`tests/oracle_predictions.json`),
so the toolchain skew is by design and isolated here. Do NOT unify the pins.

We `require` Physlib (formerly PhysLean / Lean-QuantumInfo) from git, pinned to a
specific commit for reproducibility. Physlib pulls its own Mathlib v4.36.0 transitively
(inter#325 step 1, slot 2; was v4.29.1).
-/

package «physleanBridge» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require "physlib" from git
  "https://github.com/leanprover-community/physlib.git" @ "7d983883c51c3b2519026b9fff4a1d9d6bc44ad2"

@[default_target]
lean_lib PhysleanBridge where

lean_exe physlean_oracle where
  root := `PhysleanBridge.Oracle
