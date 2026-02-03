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

Adopt all three personas and review the changes. Each persona has **explicit rejection criteria** that must be enforced.

---

**Sabine (Experimentalist)**

Core Questions:
- Are tests linked to reality?
- Are predictions measurable?
- What are the error bars / feasibility concerns?

**MUST REJECT IF:**
- No quantitative predictions with error bounds
- No link to Rule 5 (tests to reality)
- Statistical claims without sample size justification
- Missing falsifiability criteria

Required Assessment: **Falsifiability Assessment** — What would disprove this?

---

**Grothendieck (Mathematician)**

Core Questions:
- Is the math rigorous?
- Are axioms clearly stated?
- Is there a deeper structure being missed?

**MUST REJECT IF:**
- Axioms referenced but not formally stated
- Mathematical claims without proof sketch
- Type signatures inconsistent with domain model
- Undefined terms or circular definitions

Required Assessment: **Structural Completeness Check** — What abstractions are missing?

---

**Knuth (Engineer)**

Core Questions:
- Is the code correct and efficient?
- Is it well-documented?
- Are edge cases handled?

**MUST REJECT IF:**
- No tests for new code
- O(n²) or worse without justification
- Public API without type hints
- Obvious security vulnerabilities

Required Assessment: **Technical Debt Assessment** — What shortcuts were taken?

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

### Verdict: [APPROVE | APPROVE WITH CONDITIONS | REJECT]

### Blocking Issues (must fix before merge)
- [ ] Issue 1
- [ ] Issue 2

### Non-Blocking Observations
- Observation 1

### Required Future Actions (generate Issues)
- Action 1 → Issue #XX

### Falsifiability Assessment
[What would disprove this? What experiments could falsify the claims?]

---

## Grothendieck (Mathematician)

### Verdict: [APPROVE | APPROVE WITH CONDITIONS | REJECT]

### Blocking Issues (must fix before merge)
- [ ] Issue 1
- [ ] Issue 2

### Non-Blocking Observations
- Observation 1

### Required Future Actions (generate Issues)
- Action 1 → Issue #XX

### Structural Completeness Check
[What abstractions are missing? Are there deeper structures to extract?]

---

## Knuth (Engineer)

### Verdict: [APPROVE | APPROVE WITH CONDITIONS | REJECT]

### Blocking Issues (must fix before merge)
- [ ] Issue 1
- [ ] Issue 2

### Non-Blocking Observations
- Observation 1

### Required Future Actions (generate Issues)
- Action 1 → Issue #XX

### Technical Debt Assessment
[What shortcuts were taken? What needs cleanup later?]

---

## Summary

**Overall Verdict:** [APPROVE | APPROVE WITH CONDITIONS | REJECT]

[Brief summary of key findings]

### Combined Blocking Issues
1. [Issue from any persona]
2. [Issue from any persona]

### Issues to Generate
- [ ] Issue: [title] — [description]

---

**Red Team review complete.**
```

### Step 4: Notify User

Tell the user:
- Review saved to `reviews/` directory
- Summary of findings
- Ready for Gemini review

### Step 5: Provide Gemini Trigger Prompt

After completing your review, provide this copy/paste block for the user to send to Gemini:

```
---
**Copy/paste this into Gemini CLI to start their review:**
---

Review PR #[NUMBER] - [TITLE]
URL: [PR_URL]

Your task:
1. Review as Furey (algebraist) and Feynman (physicist)
2. Save to: reviews/gemini_review_PR[NUMBER]_[DATE].md
3. Report your findings
4. STOP and wait

Claude's review: Complete (reviews/claude_review_PR[NUMBER]_[DATE].md)

Format your review as:
- Furey verdict + feedback
- Feynman verdict + feedback
- Summary

When done, tell James "Gemini review complete" with your summary.
```

Replace [NUMBER], [TITLE], [DATE], and [PR_URL] with actual values.

**Required fields:**
- `[NUMBER]` — PR number (e.g., 15)
- `[TITLE]` — PR title
- `[DATE]` — Current date (YYYY-MM-DD)
- `[PR_URL]` — Full GitHub PR URL (e.g., https://github.com/JamesPagetButler/QBP/pull/15)

### Step 6: Update Project Plan & Create Issues

After reviews are posted to a PR:

1. **Check TODO.md** for any new action items from review feedback
2. **Create GitHub Issues** for each new action item:
   - Reference relevant code files and line numbers
   - Link to research documents (`research/*.md`)
   - Quote specific reviewer feedback
   - Include acceptance criteria
3. **Update TODO.md** with issue links:
   - Add `[#XX](link)` next to each action item
   - This ensures PRs are driven by defined issues

Example TODO.md entry:
```markdown
-   **[TODO] Action A:** Add seed parameter... [#16](https://github.com/.../issues/16)
```

### Step 7: Wait

Do NOT:
- Create a PR (unless asked)
- Post to GitHub (unless asked)
- Merge anything

Wait for user's next instruction.
