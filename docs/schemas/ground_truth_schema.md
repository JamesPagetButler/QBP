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

### 2. Environmental Conditions (REQUIRED)
- **Ambient baseline:** The standard facility conditions defined in `docs/design/facility_location.md`.
  - **Atmosphere:** Old Growth Forest (21.5% $O_2$, 55% Humidity, trace phytoncides).
  - **Temperature:** 295.15 K (22°C / 71.6°F).
  - **Pressure:** 1.0 atm (101.325 kPa).
  - **Gravity:** 1.0 g (9.81 m/s²).
- **Lab-specific alterations:** Any deviations from these values required for the experiment.
- **Airlock/Safety Protocols:** Specific procedures for entering the lab environment (e.g., mandatory protective gear, airlock cycles).
- **Rationale:** Why these conditions are necessary for the quaternionic effects being tested.

### 3. Physical Situation
- Real-world setup being modeled
- What question we're answering
- Standard QM answer (if known)

### 3. Empirical Anchor (REQUIRED)

**This section is mandatory for all ground truth documents.**

Every experiment must be anchored to peer-reviewed, replicated real-world measurements *before* attempting to derive predictions from QBP. This closes the gap between theory and reality:

```
Reality → Empirical Anchor → Standard QM → QBP prediction → Simulation
```

#### 3.1 Key Measured Values

A table of the primary experimental measurements relevant to this experiment:

| Quantity | Measured Value | Uncertainty | Source | Year | DOI / Identifier |
|----------|---------------|-------------|--------|------|------------------|
| *e.g., P(+) for orthogonal axes* | *0.50* | *Statistical (binary)* | *Gerlach & Stern* | *1922* | *ZS.9.349* |

**Requirements:**
- At least one primary source with a measured value (or explicit Theoretical-derived classification — see Data Type below)
- Uncertainties must be stated (even if qualitative, e.g., "binary outcome")
- Citations must have DOIs, stable identifiers, or standard academic references

#### 3.2 Experimental Confidence

| Factor | Assessment |
|--------|------------|
| Replication status | *e.g., Replicated thousands of times across all major labs* |
| Measurement precision | *e.g., Binary outcome — no precision issue* |
| Relevance to QBP test | *e.g., Direct — QBP must reproduce the discrete splitting* |

#### 3.3 What "Matching Reality" Means

1–3 paragraphs defining what it means for QBP predictions to "match" the empirical data for this specific experiment. This must handle the heterogeneity across experiment types:

- **Quantitative-precise** experiments (e.g., g-2): matching means agreement to N significant figures
- **Qualitative-binary** experiments (e.g., Stern-Gerlach): matching means reproducing the discrete outcome structure
- **Formula-confirmed** experiments (e.g., cos²(θ/2)): matching means deriving the same functional form
- **Constraint-based** experiments (e.g., null results): matching means falling within the experimental bound

#### 3.4 Null Results and Constraints (Conditional)

If experimental upper bounds on deviations from standard QM exist for this phenomenon, list them here:

| Constraint | Bound | Source | Year | DOI / Identifier |
|-----------|-------|--------|------|------------------|
| *e.g., Quaternionic phase* | *< 1:30,000* | *Kaiser et al.* | *1984* | *...* |

**This subsection is required if relevant null results exist.** If none are known, state: "No known null results specific to this phenomenon."

#### Data Type Classification (REQUIRED)

Every experiment must declare its **data type**, which determines how "matching reality" is evaluated:

| Data Type | Definition | Example Experiments |
|-----------|------------|---------------------|
| **Quantitative-precise** | High-precision numerical measurements (>6 sig figs) | Anomalous magnetic moment (g-2) |
| **Quantitative-moderate** | Moderate-precision numerical measurements (2–6 sig figs) | Spectral line frequencies |
| **Qualitative-binary** | Discrete outcome structure (yes/no, up/down) | Stern-Gerlach splitting |
| **Formula-confirmed** | Functional form confirmed by many experiments | Malus's law, cos²(θ/2) |
| **Theoretical-derived** | Result follows from theoretical framework, no direct measurement | Particle statistics (spin-statistics theorem) |
| **Constraint-based** | Upper bound from null-result experiments | Quaternionic phase limits |

**Template:**

```markdown
## Empirical Anchor

**Data type:** [Classification from table above]

### Key Measured Values

| Quantity | Measured Value | Uncertainty | Source | Year | DOI / Identifier |
|----------|---------------|-------------|--------|------|------------------|
| ... | ... | ... | ... | ... | ... |

### Experimental Confidence

| Factor | Assessment |
|--------|------------|
| Replication status | ... |
| Measurement precision | ... |
| Relevance to QBP test | ... |

### What "Matching Reality" Means

[1-3 paragraphs]

### Null Results and Constraints

[Table or "No known null results specific to this phenomenon."]
```

### 4. QBP Axioms
- List the axioms used in the derivation
- Note any corrections or refinements from previous experiments

### 5. Core Derivation
- Step-by-step mathematical derivation
- Key insights and geometric interpretations
- Code example for verification

### 6. Prediction Classification (REQUIRED)

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

### 7. Edge Cases
- Limiting cases (e.g., θ = 0°, 90°, 180°)
- Physical interpretation of each case

### 8. Quantitative Predictions
- Table of test values with expected results
- Statistical acceptance criteria (e.g., 3σ)
- Detailed acceptance table with μ, σ, and ranges

### 9. Potential Difficulties
- Known issues or corrections
- Implementation considerations
- Numerical precision concerns

### 10. Connection to Future Experiments
- How this experiment relates to later work
- What foundations it establishes

### 11. Summary
- Key insights
- What Phase 2 will test

### 12. Phase 2 Acceptance Criteria
- Specific criteria for implementation phase
- What must pass for Phase 2 to complete

### 13. References
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
- `research/01b_angle_dependent_expected_results.md` (Angle-Dependent Measurement)
