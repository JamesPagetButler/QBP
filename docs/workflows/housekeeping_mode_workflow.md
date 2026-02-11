# Housekeeping Mode Workflow

*A workflow for autonomous batch cleanup when James is unavailable.*

---

## Overview

Housekeeping Mode enables Claude to work through low-risk cleanup tasks autonomously without requiring interactive approval for each action. This is useful when James is stepping away (sleep, meetings, etc.) and wants progress on accumulated housekeeping items.

**Key insight:** Pre-approve permission categories and a work plan at session start, then work autonomously within those boundaries.

---

## When to Use Housekeeping Mode

Housekeeping Mode is appropriate when:
- James is stepping away for an extended period
- There's a backlog of low-risk housekeeping issues
- All tasks have clear acceptance criteria
- Work is reversible (git-tracked)

Housekeeping Mode is NOT appropriate when:
- Tasks require design decisions
- Sprint phase work is pending
- Issues lack clear acceptance criteria
- Destructive operations are needed

---

## Triggering Housekeeping Mode

When the user mentions they're going to bed/sleep/stepping away, Claude should ask:

> "Would you like me to switch into Housekeeping Mode while you're away?"

---

## Pre-Approval Checklist

Before entering Housekeeping Mode, Claude must present:

### 1. Work Plan

List all issues to be addressed:

```markdown
## Housekeeping Mode Request

**Issues to address:**
- #148 — Security audit cleanup
- #142 — Automate proof graph generation
- #150 — Documentation updates

**Proposed order:** #150 → #148 → #142 (increasing complexity)
**Estimated scope:** 5 files, ~100 lines
```

### 2. Required Permissions

| Category | Examples | Risk Level |
|----------|----------|------------|
| File edits | Edit, Write | Low |
| Git operations | add, commit, push, branch | Low |
| GitHub CLI | gh pr create, gh issue close | Low |
| Build/test | make, pytest, lake build | Medium |

### 3. Risk Assessment

- **Reversible?** All git operations can be reverted
- **Destructive?** No force-push, no delete without backup
- **Scope-limited?** Only touches files related to listed issues

### 4. Get Blanket Approval

User approves:
- The work plan (issues to address)
- The permission categories needed
- The risk assessment

Once approved, Claude works autonomously without per-command prompts.

---

## Autonomous Execution

### Work Locally First
- Make all edits
- Run local tests if applicable
- Commit with clear messages

### Batch Into PRs
- Group related fixes
- Create PR with summary
- Run tiered reviews (Red Team, Gemini if appropriate tier)

### Fix Review Issues In-PR
- Don't defer during housekeeping mode
- Iterate until reviews pass

### Leave Ready for Merge
- PR approved by reviews
- Summary comment posted
- User merges when they return

---

## Scope Limits

### In Scope

- Documentation fixes
- Code cleanup
- Minor bug fixes with clear AC
- Process improvements
- Closing resolved issues
- Updating dependencies (non-breaking)

### Out of Scope

- New features
- Architectural changes
- Design decisions
- Sprint phase work
- Anything requiring user input
- Force operations

---

## Safety Rails

1. **No force operations** — no `--force`, `--hard`, `-f` flags
2. **No deletions without issues** — only delete what's explicitly requested
3. **No external API calls** — except GitHub and Gemini for reviews
4. **Checkpoint commits** — commit frequently so work isn't lost
5. **Stop on confusion** — if unclear, leave a note and move to next item
6. **Review cycle limit** — max 3 cycles per issue, then defer

---

## Example Session

### Entry

```
James: I'm heading to bed. There are a few housekeeping issues piling up.

Claude: Would you like me to enter Housekeeping Mode?

Here's my plan:
- Issues: #148 (security cleanup), #150 (doc fixes), #169 (submodule)
- Estimated scope: 8 files, ~150 lines
- Required permissions: file edits, git operations, gh CLI
- Risk: Low (all reversible, no destructive operations)

Approve this plan to let me work autonomously?

James: Approved. See you in the morning.

Claude: Housekeeping Mode engaged. Starting with #150 (docs).
I'll leave PRs ready for your review when you return.
```

### Progress Update (Async)

Claude posts updates as PR comments, not expecting immediate response.

### Exit

When James returns:

```
James: Morning. Status?

Claude: ## Housekeeping Mode Complete

**Completed:**
- #150: Doc fixes (PR #180, ready for merge)
- #148: Security cleanup (PR #181, ready for merge)

**Deferred:**
- #169: Submodule issue — needs architecture decision

**Summary:** 2 PRs ready for your review. 1 issue deferred with notes.
```

---

## Comparison: Housekeeping Mode vs Sprint Mode

| Aspect | Housekeeping Mode | Sprint Mode |
|--------|-------------------|-------------|
| Scope | Batch of issues | Full sprint |
| Duration | Hours | Days |
| Work type | Cleanup, fixes | Physics experiments |
| Branch strategy | Per-issue or batched | Per-phase |
| Review tier | Tier 1-2 | Tier 1-3 |
| Human involvement | Start/end | Checkpoints |

---

## References

- [Sprint Mode Workflow](sprint_mode_workflow.md) — Full experiment sprints
- [Tiered Review System](../CONTRIBUTING.md#tiered-review-system) — Review requirements
- [Herschel Check](../CONTRIBUTING.md#session-start-protocol-the-herschel-check) — Process verification
