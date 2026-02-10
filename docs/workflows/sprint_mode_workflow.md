# Sprint Mode Workflow

*A workflow for AI team (Claude + Gemini) to execute full experimental sprints with high autonomy.*

---

## Overview

Sprint Mode enables the AI team to manage an entire experimental sprint (Phases 1-5 + Theory Refinement) with pre-approved permissions, reducing constant human intervention while maintaining safety rails and clear checkpoints.

**Key insight:** Pre-approve permission categories at session start (like Housekeeping Mode), then work autonomously within those boundaries.

---

## When to Use Sprint Mode

Sprint Mode is appropriate when:
- Starting a new experimental sprint
- James will be away for an extended session
- The experiment scope is well-defined
- Prior sprints have established patterns to follow

Sprint Mode is NOT appropriate when:
- Requirements are unclear or exploratory
- Significant architecture decisions are needed
- The experiment involves untested physics domains

---

## Phase 1: Setup (Human Approval Required)

### Triggering Sprint Mode

James explicitly requests Sprint Mode:

> "Engage Sprint Mode for Experiment 3: Lamb Shift"

### Pre-Approval Checklist

Claude presents the approval request:

```markdown
## Sprint Mode Request: Experiment 3 (Lamb Shift)

**Scope:** Phases 1-5 + Theory Refinement
**Branch pattern:** sprint-3/phase-N-name
**Estimated duration:** 3-5 sessions

**Permission categories requested:**

| Category | Examples | Risk |
|----------|----------|------|
| File edits | Edit, Write | Low |
| Git operations | add, commit, push, branch | Low |
| GitHub CLI | gh pr create, gh pr comment, gh issue close | Low |
| Build/test | lake build, pytest | Medium |
| Gemini API | Review requests via fallback scripts | Low |

**Safety rails:**
- No force operations (--force, --hard, -f)
- No direct commits to master
- Review cycle limit: 5 per phase
- Escalate on confusion or blocking issues

**Exit conditions:**
- All phases complete and merged
- Blocking issue requiring human decision
- Review cycle limit exceeded
- James requests exit

Approve to begin Sprint Mode?
```

James approves by confirming:
> "Approved. Begin Sprint Mode."

---

## Phase 2: Autonomous Execution

### Branch-Per-Phase Structure

Each phase gets its own branch, enabling incremental progress and focused PRs:

```
Sprint 3 Execution Flow
───────────────────────────────────────────────────────
Phase 1: Ground Truth
  Branch: sprint-3/phase-1-ground-truth
  └── Work → commit → review → PR → merge

Phase 2: Implementation
  Branch: sprint-3/phase-2-implementation
  └── Work → commit → review → PR → merge

Phase 3: Visualization
  Branch: sprint-3/phase-3-visualization
  └── Work → commit → review → PR → merge

Phase 4: Formal Verification
  Branch: sprint-3/phase-4-verification
  └── Work → commit → review → PR → merge

Phase 5: Publication
  Branch: sprint-3/phase-5-publication
  └── Work → commit → review → PR → merge

Theory Refinement
  Branch: sprint-3/theory-refinement
  └── Work → commit → review → PR → merge
───────────────────────────────────────────────────────
```

### Per-Phase Workflow

For each phase:

1. **Create branch** from master
2. **Do work** for that phase
3. **Commit** with clear, descriptive messages
4. **Run internal reviews**:
   - Red Team (Claude): Sabine, Grothendieck, Knuth
   - Theory Team (Gemini): Furey, Feynman
   - Review tier based on content (Tier 1/2/3)
5. **Fix issues** (up to 5 review cycles)
6. **Create PR** with summary and test plan
7. **Merge or escalate**:
   - If all reviews pass → merge
   - If blocking issues → escalate to James
8. **Proceed** to next phase

### Review Tiers in Sprint Mode

| Phase | Default Tier | Reviews Required |
|-------|--------------|------------------|
| Phase 1: Ground Truth | Tier 3 | Red Team + Gemini |
| Phase 2: Implementation | Tier 2 | Red Team + Gemini |
| Phase 3: Visualization | Tier 2 | Red Team |
| Phase 4a: Proof | Tier 3 | Red Team + Gemini |
| Phase 4b: Review | Tier 2 | Red Team |
| Phase 4c: Viz | Tier 2 | Red Team |
| Phase 5: Publication | Tier 2 | Red Team + Gemini |
| Theory Refinement | Tier 3 | Red Team + Gemini |

---

## Phase 3: Human Checkpoints

James can engage at any point through these mechanisms:

### Async Review
Check completed PRs asynchronously. Each PR has full review history for context.

### Batch Review
Review multiple phase PRs at once when returning from a break.

### Intervention
Jump in at any point if:
- Escalation occurs
- Quality concerns arise
- Direction needs adjustment

### Status Check
Ask for sprint status at any time:
> "Sprint status?"

Claude responds with current phase, completed phases, and any blockers.

---

## Phase 4: Sprint Completion

After all phases merge:

1. **Post sprint summary** to tracking issue
2. **Close phase issues** that are satisfied
3. **Update SPRINT_STATUS.md** with completion status
4. **Run retrospective** (answer the 4 questions)
5. **Notify James** of completion

### Sprint Summary Template

```markdown
## Sprint N Complete

**Experiment:** N — [Name]
**Duration:** [X sessions over Y days]

### Phases Completed
- [x] Phase 1: Ground Truth (PR #XX)
- [x] Phase 2: Implementation (PR #XX)
- [x] Phase 3: Visualization (PR #XX)
- [x] Phase 4: Formal Verification (PR #XX)
- [x] Phase 5: Publication (PR #XX)
- [x] Theory Refinement (PR #XX)

### Key Findings
- [Summary of physics results]
- [Any corrections or refinements]

### Issues Created
- #XX — [Housekeeping item]
- #XX — [Future work item]

### Retrospective
1. Did we follow the critical path? [Yes/No + brief]
2. Where did we deviate? [List]
3. What was the cost? [Impact]
4. Commitment for next sprint? [Action]
```

---

## Safety Rails

### Prohibited Actions
- `git push --force`, `git reset --hard`
- Direct commits to master
- Closing issues without AC verification
- Skipping required reviews

### Escalation Triggers
- Review cycle limit (5) exceeded
- Blocking issue with no clear resolution
- AC cannot be met without scope expansion
- Confusion about requirements
- Test failures that can't be resolved

### Recovery Procedures
If Sprint Mode must be interrupted:
1. Commit current work-in-progress
2. Document state in SPRINT_STATUS.md
3. Note return point clearly
4. Exit Sprint Mode cleanly

---

## Comparison: Sprint Mode vs Other Modes

| Aspect | Normal Mode | Housekeeping Mode | Sprint Mode |
|--------|-------------|-------------------|-------------|
| Scope | Single task | Batch of issues | Full sprint |
| Duration | Minutes-hours | Hours | Days |
| Permissions | Per-command | Pre-approved batch | Pre-approved categories |
| Human involvement | Constant | At start/end | Checkpoints |
| Branch strategy | Per-issue | Flexible | Per-phase |
| Review level | Per-PR | Tier-based | Tier-based |

---

## Example: Sprint Mode for Experiment 3

### Session Start
```
James: Engage Sprint Mode for Experiment 3: Lamb Shift

Claude: [Presents pre-approval checklist]

James: Approved. Begin Sprint Mode.

Claude: Sprint Mode engaged. Starting Phase 1: Ground Truth.
Creating branch: sprint-3/phase-1-ground-truth
```

### Mid-Sprint Status Check
```
James: Sprint status?

Claude: ## Sprint 3 Status

**Current:** Phase 3: Visualization (in progress)

**Completed:**
- Phase 1: Ground Truth (PR #201, merged)
- Phase 2: Implementation (PR #205, merged)

**Next:** Phase 4: Formal Verification

**Blockers:** None

**Estimated completion:** 2 more sessions
```

### Sprint Completion
```
Claude: ## Sprint 3 Complete

All 6 phases merged successfully. Retrospective documented
in SPRINT_STATUS.md. Created 2 housekeeping issues (#220, #221).

Ready to begin Sprint 4 when you are, James.
```

---

## References

- [Housekeeping Mode Workflow](housekeeping_mode_workflow.md) — Pre-approval model
- [Tiered Review System](../CONTRIBUTING.md#tiered-review-system) — Review requirements
- [The 5-Phase Lifecycle](../CONTRIBUTING.md#the-5-phase-experimental-lifecycle) — Phase definitions
- [Herschel Check](../CONTRIBUTING.md#session-start-protocol-the-herschel-check) — Process verification
