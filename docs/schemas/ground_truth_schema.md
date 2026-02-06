# Ground Truth Document Schema

This schema defines the structure and requirements for Phase 1 Ground Truth documents (`research/NN_..._expected_results.md`).

## Purpose

Ground truth documents establish the theoretical predictions for an experiment **before** implementation. They serve as:
1. The specification for Phase 2 implementation
2. The acceptance criteria for Phase 3 validation
3. The basis for Phase 4 formal proofs

## Required Sections

### 1. Overview
- Brief description of the experiment
- Key result (the main prediction)
- Cross-references to theory documents

### 2. Physical Situation
- Real-world setup being modeled
- What question we're answering
- Standard QM answer (if known)

### 3. QBP Axioms
- List the axioms used in the derivation
- Note any corrections or refinements from previous experiments

### 4. Core Derivation
- Step-by-step mathematical derivation
- Key insights and geometric interpretations
- Code example for verification

### 5. Prediction Classification (REQUIRED)

**This section is mandatory for all ground truth documents.**

Every prediction must be classified as either:

| Type | Definition | Implication |
|------|------------|-------------|
| **Validation** | Matches standard QM exactly | Confirms QBP is consistent with known physics |
| **Novel** | Differs from standard QM | Provides testable distinction between QBP and QM |

**Template:**

```markdown
## Prediction Classification

| Prediction | Type | Standard QM | Notes |
|------------|------|-------------|-------|
| P(+) = cos²(θ/2) | Validation | cos²(θ/2) | Identical to QM |

### Classification Summary

**Validation:** This experiment confirms QBP reproduces standard quantum mechanics
for [specific scenario]. It does not distinguish QBP from QM.

**Novel predictions (if any):** [None for this experiment / Description of QBP-specific predictions]

### Implications

[What this classification means for QBP's status as a theory]
```

**Why this matters:** If all QBP predictions match QM exactly, QBP is a reformulation, not a falsifiable alternative theory. Tracking this explicitly helps identify where novel predictions might emerge. See issue #167 for ongoing research into potential QBP divergences.

### 6. Edge Cases
- Limiting cases (e.g., θ = 0°, 90°, 180°)
- Physical interpretation of each case

### 7. Quantitative Predictions
- Table of test values with expected results
- Statistical acceptance criteria (e.g., 3σ)
- Detailed acceptance table with μ, σ, and ranges

### 8. Potential Difficulties
- Known issues or corrections
- Implementation considerations
- Numerical precision concerns

### 9. Connection to Future Experiments
- How this experiment relates to later work
- What foundations it establishes

### 10. Summary
- Key insights
- What Phase 2 will test

### 11. Phase 2 Acceptance Criteria
- Specific criteria for implementation phase
- What must pass for Phase 2 to complete

### 12. References
- Academic citations
- Internal document references

## File Naming

Ground truth documents follow the pattern:
```
research/NN_experiment_name_expected_results.md
```

Where `NN` is the two-digit experiment number (01, 02, etc.).

## Examples

- `research/01_expected_results.md` (Stern-Gerlach)
- `research/02_angle_dependent_expected_results.md` (Angle-Dependent Measurement)
