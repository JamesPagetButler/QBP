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

### Step 4: Notify User

Tell the user:
- Review saved to `reviews/` directory
- Summary of findings
- Ready for merge decision (if Claude review also complete)

### Step 5: Wait

Do NOT:
- Create a PR (unless asked)
- Post to GitHub (unless asked)
- Merge anything

Wait for user's next instruction.
