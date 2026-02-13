# Verification & Validation (V&V) Workflow

This document defines the V&V methodology used by the QBP project to ensure that simulations accurately represent the intended physics experiments.

## Definitions

- **Verification** — "Is it built correctly?" Does the simulation implementation match the mathematical model?
- **Validation** — "Does it reflect reality?" Do simulation results match expected real-world outcomes?

## The V&V Pipeline

```
Lean 4 Proofs (Phase 4a)
    │
    ├── Float Oracle (Phase 4d) ──► Differential Testing vs Python
    │
    └── FFI Exports (Phase 4e) ──► Interactive 3D Simulation
                                        │
                                        ├── Setup Verification (V)
                                        ├── Behavior Verification (V)
                                        ├── Results Validation (V)
                                        └── Iterate if needed
```

## V&V Steps

### Step 1: Setup Verification (V)

Human inspects the simulation to verify the experimental setup:

- Is the apparatus configured correctly?
- Are fields/gradients oriented properly?
- Is the particle source positioned correctly?
- Do boundary conditions match the experiment?

### Step 2: Behavior Verification (V)

Run the simulation and verify intermediate behavior:

- Do particles respond correctly to forces?
- Is state evolution visually sensible?
- Are there unexpected artifacts?

### Step 3: Results Validation (V)

Compare simulation output to expected real-world results:

- Does the measurement distribution match QM predictions?
- Does it match the Lean oracle predictions?
- Does it match historical experimental data?
- **Do results match the Empirical Anchor values** from the ground truth document (§3)? Compare simulation output directly to the measured values, uncertainties, and constraints recorded in the Empirical Anchor — not just to QM formulas.

### Step 4: Iterate

If V&V fails at any step:

1. Identify the error (setup, parameters, or theory)
2. Correct and re-verify
3. Document the finding

## Per-Experiment V&V Checklists

These checklists are **templates** to be filled in during human review sessions.
The reviewer runs the simulation, inspects each item, and records Pass/Fail with
the date and reviewer initials. Copy the relevant table into a review record
(e.g., `workspace/human_review/vv_01_YYYY-MM-DD.md`) and fill it in.

### Experiment 01: Stern-Gerlach

| Step | Check | Pass/Fail | Reviewer | Date |
|------|-------|-----------|----------|------|
| Setup V | Magnet poles oriented vertically (N up, S down) | | | |
| Setup V | Particle source on beam axis | | | |
| Setup V | Detector screen positioned after magnet | | | |
| Behavior V | Particles deflect up or down (never sideways) | | | |
| Behavior V | No particles remain undeflected | | | |
| Results V | P(+) = 0.50 +/- 0.05 for theta=90 deg | | | |
| Results V | Matches oracle: P(+) = cos^2(theta/2) | | | |
| Results V | Simulation results consistent with Empirical Anchor values | | | |

### Experiment 01b: Angle-Dependent Measurement

| Step | Check | Pass/Fail | Reviewer | Date |
|------|-------|-----------|----------|------|
| Setup V | Angle slider controls state preparation angle | | | |
| Setup V | Measurement axis is fixed (z-axis) | | | |
| Behavior V | theta=0: all particles deflect up | | | |
| Behavior V | theta=180: all particles deflect down | | | |
| Behavior V | theta=90: roughly equal up/down | | | |
| Results V | P(+) matches cos^2(theta/2) at 9 test angles | | | |
| Results V | N > 1000 for statistical confidence | | | |
| Results V | Oracle and simulation agree within 5% | | | |
| Results V | Simulation results consistent with Empirical Anchor values | | | |

## Integration with Phase 4

Phase 4d (Differential Testing) provides automated verification.
Phase 4e (Simulation Engine) provides interactive verification.

Both use the same Lean-proven oracle as the source of truth.

## References

- [Simulation V&V Methodology (PMC)](https://pmc.ncbi.nlm.nih.gov/articles/PMC7219780/)
- [JHU APL: Modeling and Simulation V&V](https://secwww.jhuapl.edu/techdigest/content/techdigest/pdf/V25-N02/25-02-Pace.pdf)
