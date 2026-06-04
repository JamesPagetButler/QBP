import Lake
open Lake DSL

/-
PhysLean ↔ QBP differential-test bridge (QBP issue #490).

This is a SIBLING project to `proofs/` — deliberately on PhysLean's toolchain
(`leanprover/lean4:v4.29.1`) and PhysLean's Mathlib pin (`v4.29.1`), NOT QBP's
(`v4.30.0`). Integration happens at the JSON boundary (`tests/oracle_predictions.json`),
so the toolchain skew is by design and isolated here. Do NOT unify the pins.

We `require` Physlib (formerly PhysLean / Lean-QuantumInfo) from git, pinned to a
specific commit for reproducibility. Physlib pulls its own Mathlib v4.29.1 transitively.
-/

package «physleanBridge» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require "physlib" from git
  "https://github.com/leanprover-community/physlib.git" @ "23a05a37bf1ac7bae69568ca0723ceff90c4a334"

@[default_target]
lean_lib PhysleanBridge where

lean_exe physlean_oracle where
  root := `PhysleanBridge.Oracle
