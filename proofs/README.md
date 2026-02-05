# QBP Formal Proofs

This directory contains Lean 4 formal proofs for Quaternion-Based Physics experiments.

## Quick Start

```bash
# Install Lean 4 (if not already installed)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source ~/.elan/env

# Build the project
cd proofs
lake update
lake exe cache get
lake build
```

For detailed instructions, see [docs/lean4_setup.md](../docs/lean4_setup.md).

## Project Structure

```
proofs/
├── QBP.lean              # Root module
├── QBP/
│   ├── Basic.lean        # Core axiom definitions (Axioms 1 & 2)
│   └── Experiments/      # Experiment-specific proofs
│       ├── SternGerlach.lean   # Issue #55
│       ├── DoubleSlit.lean     # Issue #56
│       └── ...
├── lakefile.lean         # Build configuration with mathlib4
└── lean-toolchain        # Lean version specification
```

## Core Definitions (QBP/Basic.lean)

| Definition | QBP Axiom | Description |
|------------|-----------|-------------|
| `Q` | - | Quaternion type over reals (`Quaternion ℝ`) |
| `isUnitQuaternion` | Axiom 1 | State is a unit quaternion (normSq = 1) |
| `isPureQuaternion` | Axiom 2 | Observable is a pure quaternion (re = 0) |
| `SPIN_X/Y/Z` | Axiom 2 | Standard spin observables |

## Phase 4 Formal Verification

Each experiment's Phase 4 issue involves creating formal proofs:

| Issue | Experiment | Proof File |
|-------|------------|------------|
| #55 | Stern-Gerlach | `QBP/Experiments/SternGerlach.lean` |
| #56 | Double-Slit | `QBP/Experiments/DoubleSlit.lean` |
| #57 | Lamb Shift | `QBP/Experiments/LambShift.lean` |
| #58 | g-2 | `QBP/Experiments/AnomalousMagnetic.lean` |
| #59 | Bell's Theorem | `QBP/Experiments/Bell.lean` |
| #60 | Particle Statistics | `QBP/Experiments/Statistics.lean` |
| #61 | Positronium | `QBP/Experiments/Positronium.lean` |
| #62 | Hydrogen Spectrum | `QBP/Experiments/Hydrogen.lean` |
| #63 | Gravity Tests | `QBP/Experiments/Gravity.lean` |

See [docs/gemini_phase4_guide.md](../docs/gemini_phase4_guide.md) for the formal verification workflow.

## Library Development

When Phase 4 proofs require Lean 4 capabilities that don't exist in Mathlib or the broader ecosystem, we develop them as independent Lake packages in `/libs/`. These libraries are general-purpose — they must not depend on QBP-specific definitions from this directory.

During development, proofs in `/proofs` reference libraries via local `require` path dependencies. Before publication (Phase 5 Track B), libraries are finalized to meet the Library Quality Standards documented in [CONTRIBUTING.md](../CONTRIBUTING.md#library-quality-standards).

## Verification

All proofs must:
- Compile without errors (`lake build` succeeds)
- Contain no `sorry` (incomplete proofs)
- Match ground truth claims from Phase 1 research

## Phase 4c Visualization Bridge

Phase 4a proof structure is exported to JSON (alongside Phase 2 results) for consumption by the Phase 4c interactive visualization. A Python export script (`export_data.py`) extracts proof metadata — theorem names, statement summaries, and dependency structure — and combines it with Phase 2 simulation data into a single JSON file per experiment. The C/WASM visualization in `src/viz/interactive/` reads this JSON to render proof annotations overlaid on the physics simulation. See [CONTRIBUTING.md](../CONTRIBUTING.md#phase-4c-interactive-proof-visualization) for the full Phase 4c specification.
