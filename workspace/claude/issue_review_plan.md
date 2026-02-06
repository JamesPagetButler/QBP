# Issue Review and Update Plan

This plan ensures all open issues conform to our rigorous 5-Phase workflow and that Phase 3 visualizations are built correctly.

---

## Summary of Open Issues (54 total)

| Category | Count | Issues |
|----------|-------|--------|
| **Experiment Phase 1 (Ground Truth)** | 8 | #22, #23, #30, #31, #32, #33, #34, #35 |
| **Experiment Phase 2 (Implementation)** | 8 | #36, #38, #40, #42, #44, #46, #48, #50 |
| **Experiment Phase 3 (Visualization)** | 8 | #37, #39, #41, #43, #45, #47, #49, #51 |
| **Experiment Phase 4 (Formal Proof)** | 9 | #56, #57, #58, #59, #60, #61, #62, #63, #108 |
| **Experiment Phase 5 (Publication)** | 9 | #64, #65, #66, #67, #68, #69, #70, #71, #72 |
| **Theory Refinement** | 10 | #80-88 |
| **Research** | 2 | #6, #20 |

---

## Workflow Compliance Checklist

Per CONTRIBUTING.md and the new methodology docs, each phase issue must:

### Phase 1 (Ground Truth) Issues Must Have:
- [ ] Link to output: `research/NN_experiment_expected_results.md`
- [ ] Formal derivation requirement
- [ ] Quantitative predictions with acceptance criteria (e.g., 3σ)
- [ ] References to literature

### Phase 2 (Implementation) Issues Must Have:
- [ ] Link to simulation script: `experiments/NN_name/simulate.py`
- [ ] Link to tests: `tests/physics/test_name.py`
- [ ] Requirement for machine-readable CSV output to `/results`
- [ ] Blocked by Phase 1 completion

### Phase 3 (Visualization) Issues Must Have:
- [ ] **vpython interactive demo requirement** (not just static charts!)
- [ ] Manim scene requirement (if applicable)
- [ ] Analysis script in `analysis/NN_experiment/`
- [ ] Analysis report generation requirement
- [ ] Human interpretation decision gate
- [ ] Blocked by Phase 2 completion

### Phase 4 (Formal Proof) Issues Must Have:
- [ ] Lean 4 proof file location: `/proofs`
- [ ] Theorems must match Phase 3 validated results
- [ ] Blocked by Phase 3 completion

### Phase 5 (Publication) Issues Must Have:
- [ ] Paper section in `paper/quaternion_physics.md`
- [ ] Must follow `docs/schemas/physics_paper_schema.md`
- [ ] Blocked by Phase 4 completion

---

## Execution Plan

### Step 1: Review Issue #108 (Exp 01 Phase 4)
**Action**: Verify it's properly structured for the new workflow
**Expected**: Issue should reference the merged Phase 3 work (PR #105)

### Step 2: Close Premature Phase 4/5 Issues
**Rationale**: Per workflow, Phase 4 issues should only exist after Phase 3 is complete
**Issues to potentially close**:
- Phase 4 issues (#56-63) for experiments that haven't completed Phase 3
- Phase 5 issues (#64-72) for experiments that haven't completed Phase 4

### Step 3: Update All Phase 3 Issues with Correct Visualization Requirements
**Critical Fix**: Ensure all Phase 3 issues specify:
1. vpython interactive demo (like `src/viz/stern_gerlach_demo.py`)
2. NOT just static bar charts
3. Human interpretation decision gate

**Issues to update**: #37, #39, #41, #43, #45, #47, #49, #51

### Step 4: Create Template Comment for Phase 3 Issues
**Standard acceptance criteria for Phase 3**:
```markdown
## Phase 3 Acceptance Criteria (Updated per Workflow)

### Core Requirement: Insight-Enabling Visualization

The purpose of Phase 3 is to create visualizations that provide **fundamental insight** into the experiment and its results. The quality standard is 3Blue1Brown / Richard Behiel level clarity - visualizations that make complex physics **visually intuitive**.

**The visualization must enable the reviewer to:**
- [ ] Gain fundamental understanding of what's happening in the experiment
- [ ] Intuitively grasp the physics being demonstrated
- [ ] See *why* results match (or don't match) ground truth, not just *that* they match
- [ ] Understand the quantum phenomena visually, not just numerically

### Recommended Tools (not constraints):
- **vpython**: Interactive 3D browser-based demos (e.g., `src/viz/{experiment}_demo.py`)
- **Manim**: High-quality explanatory animations
- **matplotlib**: Static plots for supplementary analysis
- **Custom solutions**: Any tool that achieves the insight goal

### Required Outputs:
- [ ] **Insight-enabling visualization** that demonstrates the physics
- [ ] **Analysis Script**: `analysis/NN_experiment/analyze_results.py`
  - Loads CSV from `/results`
  - Compares against ground truth
  - Calculates σ deviation
- [ ] **Analysis Report**: `analysis/NN_experiment/analysis_report_*.md`
  - Quantitative comparison table
  - PASS/FAIL determination

### Decision Gate:
Human reviews the visualization and confirms:
1. "I understand what this experiment demonstrates"
2. "I can see why the results match/don't match the ground truth"
3. "The physics is visually evident, not just numerically validated"
```

### Step 5: Update Issue Bodies
For each Phase 3 issue, add the standard acceptance criteria comment.

### Step 6: Review Dependency Chain
Ensure issues are properly blocked:
- Phase 2 blocked by Phase 1
- Phase 3 blocked by Phase 2
- Phase 4 blocked by Phase 3
- Phase 5 blocked by Phase 4

---

## Execution Order (for "proceed" workflow)

1. **Add workflow compliance comment to Issue #108** (Exp 01 Phase 4)
2. **Update Issue #37** (Exp 2 Double-Slit Phase 3) with correct viz requirements
3. **Update Issue #39** (Exp 3 Lamb Shift Phase 3) with correct viz requirements
4. **Update Issue #41** (Exp 4 g-2 Phase 3) with correct viz requirements
5. **Update Issue #43** (Exp 5 Bell's Theorem Phase 3) with correct viz requirements
6. **Update Issue #45** (Exp 6 Particle Stats Phase 3) with correct viz requirements
7. **Update Issue #47** (Exp 7 Positronium Phase 3) with correct viz requirements
8. **Update Issue #49** (Exp 8 Hydrogen Phase 3) with correct viz requirements
9. **Update Issue #51** (Exp 9 Gravity Phase 3) with correct viz requirements
10. **Close premature Phase 4 issues** (those without completed Phase 3)
11. **Close premature Phase 5 issues** (those without completed Phase 4)
12. **Summary report** of all changes made

---

## Ready for Execution

When you say "proceed", I will execute steps 1-12 in order, updating each issue with proper workflow compliance and ensuring Phase 3 visualization requirements are correct.
