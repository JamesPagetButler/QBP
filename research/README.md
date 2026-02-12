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
- Sub-experiments use letter suffix (e.g., `01b` for Angle-Dependent, an extension of 01)
- `{experiment_name}`: Snake_case description of the experiment
- `_expected_results.md`: Standard suffix indicating ground truth documentation

## Experiments

**Note:** Experiment numbers align with sprint numbers (Sprint N = Experiment N). Experiment 01b is a sub-experiment extending 01.

| # | Experiment | Sprint | Research File | Status |
|---|------------|--------|---------------|--------|
| 01 | Stern-Gerlach | 1 | [01_stern_gerlach_expected_results.md](01_stern_gerlach_expected_results.md) | Complete |
| 01b | Angle-Dependent Measurement | 2 | [01b_angle_dependent_expected_results.md](01b_angle_dependent_expected_results.md) | Complete |
| 03 | Double-Slit | 3 | [03_double_slit_expected_results.md](03_double_slit_expected_results.md) | Planned |
| 04 | Lamb Shift | 4 | [04_lamb_shift_expected_results.md](04_lamb_shift_expected_results.md) | Planned |
| 05 | Anomalous g-2 | 5 | [05_g-2_expected_results.md](05_g-2_expected_results.md) | Planned |
| 06 | Bell's Theorem | 6 | [06_bell_theorem_expected_results.md](06_bell_theorem_expected_results.md) | Planned |
| 07 | Particle Statistics | 7 | [07_particle_statistics_derivation.md](07_particle_statistics_derivation.md) | Planned |
| 08 | Positronium Ground State | 8 | [08_positronium_ground_state_expected_results.md](08_positronium_ground_state_expected_results.md) | Planned |
| 09 | Hydrogen Spectrum | 9 | [09_hydrogen_spectrum_expected_results.md](09_hydrogen_spectrum_expected_results.md) | Planned |
| 10 | Gravity Tests | 10 | [10_gravity_tests_expected_results.md](10_gravity_tests_expected_results.md) | Planned |

> **File Renaming Pending:** Research files 02-09 need renaming to match new experiment numbers. Tracked in #256.

## Usage

When implementing a new experiment:

1. Read the corresponding research file to understand the physics
2. Note the expected theoretical values and acceptance criteria
3. Implement the simulation in `/experiments/{NN}_{name}/`
4. Create tests in `/tests/physics/` that validate against the research file
5. Document any deviations or refinements needed
