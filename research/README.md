# Research Directory

This directory contains the **ground truth documentation** for all synthetic experiments in the QBP project. Each file defines the theoretical expectations, experimental parameters, and acceptance criteria that our simulations must satisfy.

## Purpose

As per [Rule 5 in CONTRIBUTING.md](../CONTRIBUTING.md):

> **Link Tests to Reality:** Every automated test must be a "synthetic experiment" that simulates a real, physically verifiable experiment. This connection must be explicitly documented.

These research files serve as the bridge between real physics and our quaternion-based simulations. They define:

- The physical experiment being modeled
- Expected theoretical predictions (from standard QM or QFT)
- Acceptance criteria for our implementation
- References to experimental literature

## File Naming Convention

Files follow the pattern: `{NN}_{experiment_name}_expected_results.md`

- `{NN}`: Two-digit experiment number matching the `/experiments` directory
- `{experiment_name}`: Snake_case description of the experiment
- `_expected_results.md`: Standard suffix indicating ground truth documentation

## Experiments

| # | Experiment | Research File | Status |
|---|------------|---------------|--------|
| 01 | Stern-Gerlach | [01_stern_gerlach_expected_results.md](01_stern_gerlach_expected_results.md) | Implemented |
| 02 | Double-Slit | [02_double_slit_expected_results.md](02_double_slit_expected_results.md) | Planned |
| 03 | Lamb Shift | [03_lamb_shift_expected_results.md](03_lamb_shift_expected_results.md) | Planned |
| 04 | Anomalous g-2 | [04_g-2_expected_results.md](04_g-2_expected_results.md) | Planned |
| 05 | Bell's Theorem | [05_bell_theorem_expected_results.md](05_bell_theorem_expected_results.md) | Planned |
| 06 | Particle Statistics | [06_particle_statistics_derivation.md](06_particle_statistics_derivation.md) | Planned |
| 07 | Positronium Ground State | [07_positronium_ground_state_expected_results.md](07_positronium_ground_state_expected_results.md) | Planned |
| 08 | Hydrogen Spectrum | [08_hydrogen_spectrum_expected_results.md](08_hydrogen_spectrum_expected_results.md) | Planned |
| 09 | Gravity Tests | [09_gravity_tests_expected_results.md](09_gravity_tests_expected_results.md) | Planned |

## Usage

When implementing a new experiment:

1. Read the corresponding research file to understand the physics
2. Note the expected theoretical values and acceptance criteria
3. Implement the simulation in `/experiments/{NN}_{name}/`
4. Create tests in `/tests/physics/` that validate against the research file
5. Document any deviations or refinements needed
