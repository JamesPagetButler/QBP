# Prompt for Claude: Phase 1 Ground Truth - Experiment 02

## Context

You are working on the QBP (Quaternion-Based Physics) project. The project aims to reformulate quantum mechanics using quaternion algebra, testing whether the mathematical properties of quaternions naturally encode quantum behavior.

**Experiment 01 (Stern-Gerlach) is complete.** It validated the special case where a spin-x state is measured along the z-axis (θ = 90°), yielding P(+) = P(-) = 0.5.

**Your task:** Complete Phase 1 (Ground Truth) for Experiment 02: Angle-Dependent Measurement.

---

## The QBP Axioms (for reference)

1. **Axiom 1 (State):** The state of a spin-1/2 particle is represented by a pure unit quaternion ψ.
2. **Axiom 2 (Observable):** A measurement direction is represented by a pure unit quaternion O.
3. **Expectation Value:** ⟨O⟩ = 2 × vecDot(ψ, O), where vecDot is the dot product of the vector (imaginary) parts.
4. **Born Rule:** P(+) = (1 + ⟨O⟩) / 2, P(-) = (1 - ⟨O⟩) / 2

---

## What Experiment 02 Tests

Experiment 01 tested θ = 90° (orthogonal). Experiment 02 must validate the **general angular dependence**:

- Prepare a state ψ along some axis
- Measure along an axis at angle θ to the preparation axis
- Validate that the QBP framework predicts the correct probability P(+) as a function of θ

Standard quantum mechanics predicts: P(+) = cos²(θ/2)

---

## Your Deliverable

Create a comprehensive ground truth document that:

1. **Derives** the QBP prediction for P(+) as a function of angle θ from the axioms
2. **Shows** why this matches (or differs from) standard QM
3. **Specifies** which angles to test and why
4. **Defines** quantitative acceptance criteria for each test case
5. **Identifies** potential difficulties or edge cases

---

## Output

Write your ground truth document. Be thorough. Show your reasoning. If you discover something interesting or concerning about the QBP framework during this derivation, say so.

Output location: `workspace/claude/02_angle_test_ground_truth.md`

---

## Important Notes

- Derive from QBP axioms, not from standard QM. The goal is to test whether quaternions *independently* predict the right answer.
- Think about what could go wrong. Where might the QBP framework fail?
- Consider the experimental perspective: what would a physicist actually measure?
- This is theory work. Go deep. Don't just fill in a template.
