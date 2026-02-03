# Gemini Review Command

**Trigger:** User types "Review" or "review" in Gemini CLI

## What To Do

When the user triggers a review:

### Step 1: Identify What to Review

Check for:
1. Recent changes in the repository
2. Open PRs on GitHub
3. Any existing Claude review in `reviews/` directory
4. Ask user if unclear what to review

### Step 2: Conduct Gemini Review

Adopt both personas and review the changes:

**Furey (Algebraist)**
- Does this align with division algebra principles?
- Is there mathematical elegance?
- Are the algebraic structures properly utilized?
- Connection to Furey's octonion/Standard Model work?

**Feynman (Physicist)**
- Is this physically intuitive?
- Can you explain it simply?
- Does it smell right physically?
- What would a diagram look like?

### Step 3: Save Review Locally

Save the review to: `reviews/gemini_review_<PR#|branch>_<date>.md`

Format:
```markdown
# Gemini Review: [Subject]

**Date:** YYYY-MM-DD
**PR/Branch:** [number or name]
**Reviewer:** Gemini (Furey/Feynman)

---

## Furey (Algebraist)
**Verdict:** [Approved/Concerns/Rejected]
[Detailed feedback on algebraic structure and elegance]

---

## Feynman (Physicist)
**Verdict:** [Approved/Concerns/Rejected]
[Detailed feedback on physical intuition and clarity]

---

## Summary
[Brief summary and overall verdict]

---

**Gemini review complete.**
```

### Step 4: Generate PRD (If Applicable)

After review, generate a PRD if the PR introduces:
- New experiments
- New visualization components
- New API surfaces
- Significant new features

Save PRD to: `docs/prds/prd_NNN_[feature_name].md`

**PRD Template:**

```markdown
# PRD: [Feature Name]

**PRD Number:** NNN
**Date:** YYYY-MM-DD
**Author:** Gemini (Furey/Feynman)
**Related PR:** #XX

---

## Problem Statement

[What problem does this solve? Why is it needed?]

---

## Success Criteria

- [ ] Criterion 1
- [ ] Criterion 2
- [ ] Criterion 3

---

## Technical Approach

[High-level design from Furey/Feynman perspective]

### Algebraic Structure (Furey)
[How does this fit the division algebra framework?]

### Physical Intuition (Feynman)
[What's the physical picture? Can you explain it simply?]

---

## Acceptance Criteria

- [ ] Testable criterion 1 (specific, measurable)
- [ ] Testable criterion 2
- [ ] Testable criterion 3

---

## Visualization Requirements

| Aspect | Requirement |
|--------|-------------|
| Interactive | [yes/no] |
| Video Tiers | [short/standard/deep_dive] |
| Key Moments | [list of moments to animate] |
| Dashboard | [yes/no] |

---

## Issues to Generate

- [ ] Issue 1: [title] — [brief description]
- [ ] Issue 2: [title] — [brief description]

---

## Dependencies

- [List of dependencies, libraries, or prior work needed]

---

## Out of Scope

- [Explicitly list what this PRD does NOT cover]
```

### Step 5: Notify User

Tell the user:
- Review saved to `reviews/` directory
- Summary of findings
- PRD generated (if applicable) with location
- Ready for merge decision (if Claude review also complete)

### Step 7: Wait

Do NOT:
- Create a PR (unless asked)
- Post to GitHub (unless asked)
- Merge anything

Wait for user's next instruction.
