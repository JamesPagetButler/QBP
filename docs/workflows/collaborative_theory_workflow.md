# Collaborative Theory Development Workflow

## Overview

This document describes the iterative, multi-agent workflow for Phase 1 (Ground Truth) and Phase 4 (Formal Proof) theory work. The process leverages the complementary strengths of multiple AI agents to produce rigorous, insightful theoretical documents.

---

## The Problem This Solves

Initial experiments showed that:
- **Gemini** produces structured, correct work but may follow templates mechanically
- **Claude** produces deeper analysis but benefits from alternative perspectives
- **Neither alone** captures all valuable insights

The collaborative workflow extracts the best from both through structured iteration.

---

## Workflow Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                    PHASE 1: PARALLEL EXPLORATION                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   ┌─────────────┐                           ┌─────────────┐         │
│   │   CLAUDE    │                           │   GEMINI    │         │
│   │             │                           │             │         │
│   │  Independent│                           │  Independent│         │
│   │  Theory Work│                           │  Theory Work│         │
│   │             │                           │             │         │
│   └──────┬──────┘                           └──────┬──────┘         │
│          │                                         │                │
│          │         workspace/claude/               │                │
│          │         workspace/gemini/               │                │
│          ▼                                         ▼                │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    PHASE 2: BELL'S EVALUATION                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   ┌─────────────────────────────────────────────────────────────┐   │
│   │                        BELL                                  │   │
│   │                                                              │   │
│   │  • Side-by-side analysis of both documents                  │   │
│   │  • Identifies strengths of each approach                    │   │
│   │  • Flags errors, gaps, or inconsistencies                   │   │
│   │  • Extracts key insights from both                          │   │
│   │  • Applies the Four Tests:                                  │   │
│   │      - The "Why" Question                                   │   │
│   │      - The Counterfactual Test                              │   │
│   │      - The Surprise Test                                    │   │
│   │      - The Explanation Test                                 │   │
│   │  • Produces evaluation report with recommendations          │   │
│   │                                                              │   │
│   └─────────────────────────────────────────────────────────────┘   │
│                              │                                       │
│                              ▼                                       │
│                   workspace/evaluation/                              │
│                   bell_evaluation_report.md                          │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    PHASE 3: HUMAN REVIEW                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   Human reviews Bell's evaluation and both source documents.        │
│   Provides guidance on:                                              │
│     • Which insights to prioritize                                   │
│     • Any concerns or questions                                      │
│     • Approval to proceed to synthesis                               │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    PHASE 4: CLAUDE SYNTHESIS                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   ┌─────────────────────────────────────────────────────────────┐   │
│   │                       CLAUDE                                 │   │
│   │                                                              │   │
│   │  Inputs:                                                     │   │
│   │    • Claude's original work                                  │   │
│   │    • Gemini's original work                                  │   │
│   │    • Bell's evaluation report                                │   │
│   │    • Human guidance                                          │   │
│   │                                                              │   │
│   │  Task:                                                       │   │
│   │    • Integrate rigorous elements from both documents         │   │
│   │    • Incorporate Bell's recommended improvements             │   │
│   │    • Address any gaps or errors identified                   │   │
│   │    • Ensure deep explanatory content (the "why")             │   │
│   │    • Produce final ground truth document                     │   │
│   │                                                              │   │
│   │  Output:                                                     │   │
│   │    • research/NN_experiment_expected_results.md              │   │
│   │                                                              │   │
│   └─────────────────────────────────────────────────────────────┘   │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    PHASE 5: STANDARD REVIEW PROCESS                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   1. Claude creates PR with synthesized document                     │
│   2. Red Team Review (Sabine, Grothendieck, Knuth)                  │
│   3. Gemini Review                                                   │
│   4. Human approval                                                  │
│   5. Merge                                                           │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Detailed Role Definitions

### Gemini's Role: Structured Exploration

**Strengths to leverage:**
- Methodical, template-compliant output
- Good at identifying discrepancies with known physics
- Clear, organized structure

**Task:** Produce an independent ground truth document following the standard template. Focus on:
- Correct mathematical derivation
- Clear test specifications
- Identification of discrepancies with established theory

**Output:** `workspace/gemini/{experiment}_ground_truth.md`

---

### Claude's Role: Deep Exploration + Synthesis

**Strengths to leverage:**
- Investigative approach (notices problems mid-derivation)
- Explains *why* things work, not just *that* they work
- Connects to deeper mathematical structures
- Integrates multiple perspectives

**Task (Exploration):** Produce an independent ground truth document. Focus on:
- Showing the reasoning process, including dead ends
- Explaining the geometric/physical intuition
- Identifying potential issues and their implications
- Connecting to the broader theoretical framework

**Output (Exploration):** `workspace/claude/{experiment}_ground_truth.md`

**Task (Synthesis):** After Bell's evaluation, integrate the best elements:
- Gemini's structural clarity and test specifications
- Claude's explanatory depth and insight
- Bell's recommended improvements
- Resolution of any conflicts or gaps

**Output (Synthesis):** `research/{experiment}_expected_results.md`

---

### Bell's Role: Critical Evaluation

**Strengths to leverage:**
- Detects pattern-matching vs. genuine understanding
- Focuses on foundational rigor
- Fair and precise criticism

**Task:** Evaluate both documents and produce a report that:
1. Compares the approaches side-by-side
2. Identifies the strengths of each
3. Flags errors, gaps, or inconsistencies
4. Applies the Four Tests for understanding
5. Recommends what to incorporate in the synthesis

**The Four Tests:**
1. **The "Why" Question:** Does it explain *why* the math works?
2. **The Counterfactual Test:** Does it consider alternatives?
3. **The Surprise Test:** Are there unexpected insights?
4. **The Explanation Test:** Could an undergraduate learn from this?

**Output:** `workspace/evaluation/bell_evaluation_{experiment}.md`

---

### Human's Role: Guidance and Approval

**Tasks:**
1. Review Bell's evaluation
2. Provide guidance on priorities or concerns
3. Approve transition from evaluation to synthesis
4. Final approval of PR

**Key decision points:**
- After Bell's evaluation: "Proceed to synthesis" or "Need more exploration"
- After synthesis: "Create PR" or "Revise synthesis"
- After review process: "Merge" or "Request changes"

---

## File Structure

```
workspace/
├── claude/
│   ├── {experiment}_ground_truth.md      # Claude's exploration
│   └── prompt_{phase}_{experiment}.md    # Prompt used
├── gemini/
│   ├── {experiment}_ground_truth.md      # Gemini's exploration
│   └── prompt_{phase}_{experiment}.md    # Prompt used
└── evaluation/
    ├── bell_evaluator_persona.md         # Bell persona definition
    ├── bell_review_plan.md               # How Bell evaluates
    ├── evaluation_template.md            # Scoring template
    └── bell_evaluation_{experiment}.md   # Bell's report

research/
└── {experiment}_expected_results.md      # Final synthesized document
```

---

## When to Use This Workflow

**Use collaborative workflow for:**
- Phase 1 (Ground Truth) - All experiments
- Phase 4 (Formal Proof) - All experiments
- Any theory work that benefits from multiple perspectives

**Use single-agent workflow for:**
- Phase 2 (Implementation) - Gemini primary
- Phase 3 (Visualization) - Claude primary
- Phase 5 (Publication) - Claude primary

---

## Example: Experiment 01b (Angle-Dependent Measurement)

*Note: This experiment was originally labeled "Experiment 02" during early development. It was reclassified as Experiment 01b in issue #179 since it extends Stern-Gerlach to arbitrary angles.*

### Step 1: Parallel Exploration ✓
- Claude produced: `workspace/claude/02_angle_test_ground_truth.md` (historical filename)
- Gemini produced: `workspace/gemini/02_angle_test_ground_truth.md` (historical filename)

### Step 2: Bell's Evaluation ✓
- Bell produced: `workspace/evaluation/bell_preliminary_analysis.md`

### Step 3: Human Review ✓
- Human confirmed Claude's work showed deeper engagement
- Human approved proceeding to synthesis

### Step 4: Claude Synthesis (NEXT)
- Claude will integrate both documents
- Output: `research/01b_angle_dependent_expected_results.md`

### Step 5: Standard Review Process
- PR created
- Red Team review
- Gemini review
- Merge

---

## Benefits of This Workflow

1. **Leverages complementary strengths** - Gemini's structure + Claude's depth
2. **Quality control** - Bell catches issues before PR stage
3. **Human oversight** - Guidance at key decision points
4. **Iterative improvement** - Each round produces better theory work
5. **Transparency** - All exploration work preserved in workspace/
6. **Learning opportunity** - Bell's evaluations are educational

---

---

## Multi-AI Integration

This workflow requires reliable communication between Claude and Gemini.

**Integration Methods:**
1. **MCP Server** — Use directly when Gemini tools are available in Claude's tool list
2. **CLI Fallback** — When MCP unavailable:
   ```bash
   ~/.claude/scripts/gemini review "content" "context"
   ~/.claude/scripts/gemini critique "problem" "approach"
   ```

**Important:** Claude must never simulate Gemini's responses. If integration fails, pause and fix before proceeding.

See [CONTRIBUTING.md § Multi-AI Integration](../../CONTRIBUTING.md#multi-ai-integration-claude--gemini) for full details.

---

## Revision History

| Date | Change | Author |
|------|--------|--------|
| 2026-02-06 | Added Multi-AI Integration section | Claude |
| 2026-02-04 | Initial workflow design | Claude + Human |
