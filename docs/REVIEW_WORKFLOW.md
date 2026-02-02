# Review Workflow

## Quick Start

To trigger a review, simply type **"Review"** in each CLI:

| CLI | Command | What Happens |
|-----|---------|--------------|
| Claude Code | `Review` | Red Team review (Sabine, Grothendieck, Knuth) |
| Gemini | `Review` | Theory review (Furey, Feynman) |

## Complete Workflow

```
┌─────────────────────────────────────────────────────────────┐
│  1. WORK COMPLETE                                           │
│     Developer finishes changes on feature branch            │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  2. TRIGGER REVIEWS                                         │
│     In Claude CLI:  type "Review"                           │
│     In Gemini CLI:  type "Review"                           │
│     (Can be done in parallel)                               │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  3. REVIEWS SAVED LOCALLY                                   │
│     reviews/claude_review_<branch>_<date>.md                │
│     reviews/gemini_review_<branch>_<date>.md                │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  4. HUMAN REVIEWS SUMMARIES                                 │
│     Read both review files                                  │
│     Ask clarifying questions in either CLI                  │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  5. CREATE PR (if not exists)                               │
│     Tell Claude: "Create PR"                                │
│     Claude creates PR and posts both reviews as comments    │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  6. VERIFY CI                                               │
│     All checks must pass                                    │
└─────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────┐
│  7. EXPLICIT MERGE COMMAND                                  │
│     Tell Claude: "merge" or "merge PR #X"                   │
│     This is the ONLY way to merge                           │
└─────────────────────────────────────────────────────────────┘
```

## Review File Locations

```
QBP/
├── reviews/
│   ├── claude_review_feature-xyz_2026-02-01.md
│   └── gemini_review_feature-xyz_2026-02-01.md
├── claude_review_prompt.md   ← Instructions for Claude
└── gemini_review_prompt.md   ← Instructions for Gemini
```

## Asking Questions

During review, you can ask either AI clarifying questions:

**In Claude CLI:**
```
"Explain Grothendieck's concern about the axioms"
"What did Sabine mean by error bars?"
```

**In Gemini CLI:**
```
"What would Feynman's diagram look like?"
"Explain Furey's algebraic concern"
```

## After Reviews Are Complete

Tell Claude to create the PR and post reviews:

```
"Create PR with reviews"
```

Claude will:
1. Create the PR (if not exists)
2. Post Red Team review as comment
3. Post Gemini review as comment (scribed)
4. Report back and WAIT for merge instruction

## Hard Gate Reminder

**No merge happens without explicit human command.**

Even after all reviews are posted and CI passes, you must explicitly say "merge" for the merge to execute.
