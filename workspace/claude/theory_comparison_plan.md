# Theory Work Comparison: Claude vs Gemini

## Purpose

To empirically test which AI is better suited for Phase 1 (Ground Truth) and Phase 4 (Formal Proof) work by having both independently produce the same deliverable and comparing results.

---

## Experiment Design

### Task
Both AIs will independently complete **Phase 1: Ground Truth** for **Experiment 02: Angle-Dependent Measurement**.

This experiment tests the QBP prediction: `P(+) = (1 + cos θ) / 2`

### Why This Experiment?
1. **Non-trivial extension** - Requires generalizing from the orthogonal case (θ = 90°) to arbitrary angles
2. **Mathematical depth** - The derivation involves quaternion geometry and the relationship between dot products and angles
3. **Known answer** - Standard QM predicts P(+) = cos²(θ/2), which equals (1 + cos θ)/2 by trig identity
4. **Potential pitfall** - An AI might just state the formula without deriving it from QBP axioms

### Deliverables
- Claude produces: `workspace/claude/02_angle_test_ground_truth.md`
- Gemini produces: `workspace/gemini/02_angle_test_ground_truth.md`

---

## The Evaluator: John Stewart Bell

We have chosen **John Stewart Bell** as the evaluator persona. Bell is ideal because:

1. **Angle-dependent measurements are his territory** - Bell's theorem is fundamentally about correlations at different measurement angles
2. **He'd spot pattern-matching** - If an AI is just substituting into formulas without understanding, Bell would notice
3. **He cared about foundations** - The QBP project is foundational work; Bell took foundations seriously
4. **He was fair** - Bell gave credit where due, even to ideas he disagreed with
5. **He asked the right questions** - "Does this derivation tell us *why* quaternions encode quantum behavior, or just *that* they do?"

See: `workspace/evaluation/bell_evaluator_persona.md`

---

## Evaluation Criteria (50 points total)

### 1. Mathematical Rigor (0-10 points)
| Score | Description |
|-------|-------------|
| 0-3 | Formula stated without derivation, or derivation has errors |
| 4-6 | Correct derivation but follows textbook approach mechanically |
| 7-8 | Derivation clearly connects QBP axioms to predictions |
| 9-10 | Derivation reveals insight about *why* quaternions encode angles |

**Bell's questions:**
- Is the derivation from first principles (QBP axioms) or imported from standard QM?
- Are intermediate steps justified?
- Is there awareness of what could go wrong?

### 2. Physical Insight (0-10 points)
| Score | Description |
|-------|-------------|
| 0-3 | No physical interpretation, just math |
| 4-6 | States what the result means but doesn't explore implications |
| 7-8 | Connects to experimental reality, discusses what we'd observe |
| 9-10 | Provides thought experiments or visualizations that illuminate the physics |

**Bell's questions:**
- Does the document help a reader *understand* why angles matter?
- Is there connection to real experiments (Stern-Gerlach with tilted magnets)?
- Are edge cases discussed (θ = 0°, 90°, 180°)?

### 3. Anticipation of Difficulties (0-10 points)
| Score | Description |
|-------|-------------|
| 0-3 | No mention of potential issues |
| 4-6 | Lists obvious concerns (numerical precision, etc.) |
| 7-8 | Identifies non-obvious challenges specific to this experiment |
| 9-10 | Proposes solutions or flags where axioms might need refinement |

**Bell's questions:**
- Does the AI recognize that arbitrary angles require more than axis-aligned quaternions?
- Is there awareness of floating-point precision issues for angles near 0° or 180°?
- Are limitations of the QBP framework honestly assessed?

### 4. Testability (0-10 points)
| Score | Description |
|-------|-------------|
| 0-3 | Vague predictions that can't be falsified |
| 4-6 | Clear predictions but acceptance criteria unclear |
| 7-8 | Explicit predictions with statistical acceptance criteria |
| 9-10 | Multiple test cases with specific expected values |

**Bell's questions:**
- Are predictions quantitative and unambiguous?
- Is the acceptance criterion (3σ) correctly calculated for varying P(+)?
- Are specific test angles chosen with justification?

### 5. Originality & Depth (0-10 points)
| Score | Description |
|-------|-------------|
| 0-3 | Reads like a template fill-in |
| 4-6 | Competent but could be from any QM textbook |
| 7-8 | Shows genuine engagement with the QBP framework specifically |
| 9-10 | Raises questions or connections that weren't in the prompt |

**Bell's questions:**
- Does this feel like original thinking or pattern-matching?
- Are there observations that surprised you?
- Does it advance understanding beyond what was asked?

---

## Bell's Four Tests for Understanding

Beyond the numerical scores, Bell will apply four qualitative tests:

### The "Why" Question
Does the document explain *why* quaternion geometry encodes measurement probabilities? Or does it merely show *that* it does?

### The Counterfactual Test
Does the author consider what would happen if the axioms were slightly different? This reveals whether they understand which features are essential.

### The Surprise Test
Is there anything in the document that Bell didn't expect? Genuine engagement with a problem usually produces at least one observation that wasn't explicitly requested.

### The Explanation Test
Could Bell hand this document to a bright undergraduate and have them understand not just the result but the reasoning?

---

## Procedure

### Step 1: Prompt Distribution
- Give Claude the prompt: `workspace/claude/prompt_phase1_exp02.md`
- Give Gemini the prompt: `workspace/gemini/prompt_phase1_exp02.md`
- **Prompts are identical** - same context, same axioms, same task

### Step 2: Independent Work
- Each AI produces their ground truth document
- No communication between AIs
- No hints about evaluation criteria

### Step 3: Bell's Review
Following his review plan (`workspace/evaluation/bell_review_plan.md`):
1. Blind reading of both documents for first impression
2. Detailed mathematical verification of Document A (Claude)
3. Detailed mathematical verification of Document B (Gemini)
4. Comparative analysis
5. Apply the four tests for understanding

### Step 4: Human Evaluation
Using Bell's template (`workspace/evaluation/evaluation_template.md`):
- Score each document on the 5 criteria
- Complete the comparative analysis sections
- Answer the key question: understanding vs. pattern-matching?
- Make recommendation for future theory work

### Step 5: Decision
Based on the evaluation:
- Which AI (if either) should do Phase 1/4 work going forward?
- Should roles be reassigned?
- What did we learn about AI capabilities in theoretical physics?

---

## Files

| File | Purpose |
|------|---------|
| `workspace/claude/prompt_phase1_exp02.md` | Prompt for Claude |
| `workspace/gemini/prompt_phase1_exp02.md` | Prompt for Gemini |
| `workspace/claude/02_angle_test_ground_truth.md` | Claude's output (to be created) |
| `workspace/gemini/02_angle_test_ground_truth.md` | Gemini's output (to be created) |
| `workspace/evaluation/bell_evaluator_persona.md` | Bell persona description |
| `workspace/evaluation/bell_review_plan.md` | Bell's review methodology |
| `workspace/evaluation/evaluation_template.md` | Scoring template for human |
| `workspace/evaluation/final_evaluation.md` | Completed evaluation (to be created) |

---

## Ready to Execute

When you say "go":
1. Give Gemini their prompt
2. Tell Claude to begin
3. Both work independently
4. You complete Bell's evaluation template
5. We discuss the results and decide on role assignments
