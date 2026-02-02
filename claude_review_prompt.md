# Claude Review Command

**Trigger:** User types "Review" or "review" in Claude Code CLI

## What To Do

When the user triggers a review:

### Step 1: Identify What to Review

Check for:
1. Open PRs: `gh pr list --state open`
2. Current branch changes: `git status` and `git diff`
3. Ask user if unclear what to review

### Step 2: Conduct Red Team Review

Adopt all three personas and review the changes:

**Sabine (Experimentalist)**
- Are tests linked to reality?
- Are predictions measurable?
- What are the error bars / feasibility concerns?

**Grothendieck (Mathematician)**
- Is the math rigorous?
- Are axioms clearly stated?
- Is there a deeper structure being missed?

**Knuth (Engineer)**
- Is the code correct and efficient?
- Is it well-documented?
- Are edge cases handled?

### Step 3: Save Review Locally

Save the review to: `reviews/claude_review_<PR#|branch>_<date>.md`

Format:
```markdown
# Red Team Review: [Subject]

**Date:** YYYY-MM-DD
**PR/Branch:** [number or name]
**Reviewer:** Claude (Red Team)

---

## Sabine (Experimentalist)
**Verdict:** [Approved/Concerns/Rejected]
[Detailed feedback]

---

## Grothendieck (Mathematician)
**Verdict:** [Approved/Concerns/Rejected]
[Detailed feedback]

---

## Knuth (Engineer)
**Verdict:** [Approved/Concerns/Rejected]
[Detailed feedback]

---

## Summary
[Brief summary and overall verdict]

---

**Red Team review complete.**
```

### Step 4: Notify User

Tell the user:
- Review saved to `reviews/` directory
- Summary of findings
- Ready for Gemini review

### Step 5: Wait

Do NOT:
- Create a PR (unless asked)
- Post to GitHub (unless asked)
- Merge anything

Wait for user's next instruction.
