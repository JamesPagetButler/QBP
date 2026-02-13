# Full Project Mode Workflow

*An advanced workflow for autonomous end-to-end execution of the entire experimental roadmap.*

---

## Overview

Full Project Mode represents the highest level of AI team autonomy, enabling execution of multiple complete experimental sprints (Experiments 1-N) with all phases and Theory Refinement stages, culminating in a single comprehensive Pull Request for final human review.

**Key distinction from Sprint Mode:** While Sprint Mode handles one experiment at a time, Full Project Mode chains multiple sprints together with autonomous internal merges, presenting a complete body of work at the end.

---

## When to Use Full Project Mode

Full Project Mode is appropriate when:
- The experimental roadmap is well-defined
- James wants to see substantial progress with minimal intervention
- The AI team has demonstrated reliability in prior sprints
- Physics foundations are stable (no major theoretical pivots expected)

Full Project Mode is NOT appropriate when:
- Requirements are still being explored
- Major architecture decisions are pending
- The project is in early stages without established patterns
- Frequent human input is expected

---

## Workflow Phases

### Phase 1: Invocation (Human Approval Required)

James explicitly triggers Full Project Mode:

> "Engage Full Project Mode for Experiments 1-9"

Claude presents the comprehensive approval request:

```markdown
## Full Project Mode Request: Experiments 1-9

**Scope:** Complete roadmap execution
- Experiment 01: Stern-Gerlach (+ 01b Angle-Dependent)
- Experiment 02: Double-Slit
- Experiment 03: Lamb Shift
- Experiment 04: Anomalous g-2
- Experiment 05: Bell's Theorem
- Experiment 06: Particle Statistics
- Experiment 07: Positronium Ground State
- Experiment 08: Hydrogen Spectrum
- Experiment 09: Gravity Tests

**Branch structure:**
- Integration branch: `feature/full-project-run-1`
- Sprint branches: `sprint/exp-NN-full-run`
- Draft PR: Created immediately as master logbook

**Estimated duration:** [X weeks]

**Permission categories requested:**

| Category | Examples | Risk |
|----------|----------|------|
| File edits | Edit, Write | Low |
| Git operations | add, commit, push, branch | Low |
| GitHub CLI | gh pr create, gh pr comment | Low |
| Build/test | lake build, pytest | Medium |
| Gemini API | Review requests | Low |
| **Internal merge** | Merge sprint → integration | Medium |

**Safety rails:**
- No force operations
- No direct commits to master
- Review cycle limit: 5 per phase
- Failed sprints documented but not merged
- Escalate on major blockers

**Deliverables:**
1. Single comprehensive PR (marked Ready for Review)
2. Process Report: `docs/reports/full_project_run_YYYY-MM-DD.md`

Approve to begin Full Project Mode?
```

James approves:
> "Approved. Begin Full Project Mode."

---

### Phase 2: Setup

1. **Create integration branch:**
   ```bash
   git checkout -b feature/full-project-run-1 master
   ```

2. **Create Draft PR:**
   ```bash
   gh pr create --draft --title "Full Project Run 1: Experiments 1-9" --body "..."
   ```

3. **Initialize logbook:**
   Post initial status comment on Draft PR with experiment list and timeline.

---

### Phase 3: Per-Experiment Execution

For each experiment in sequence:

```
┌─────────────────────────────────────────────────────────────────┐
│  Experiment N Sprint                                            │
│                                                                 │
│  1. Create sprint branch from integration:                      │
│     git checkout -b sprint/exp-0N-full-run feature/full-...     │
│                                                                 │
│  2. Execute all 5 phases + Theory Refinement:                   │
│     ├── Phase 1: Ground Truth → internal review                 │
│     ├── Phase 2: Implementation → internal review               │
│     ├── Phase 3: Visualization → internal review                │
│     ├── Phase 4: Formal Verification → internal review          │
│     ├── Phase 5: Publication → internal review                  │
│     └── Theory Refinement → internal review                     │
│                                                                 │
│  3. On success: Merge sprint → integration branch               │
│     On failure: Document and continue to next experiment        │
│                                                                 │
│  4. Update logbook on Draft PR                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Internal Review Cycles

Each phase within a sprint follows the standard review process:
- Red Team review (Sabine, Grothendieck, Knuth)
- Gemini review (Furey, Feynman) for Tier 2/3 content
- Maximum 5 review cycles per phase
- Fix issues and re-review until APPROVE or limit reached

---

### Phase 4: Internal Merge (AI-Authorized)

When a sprint passes all reviews:

1. **Merge sprint branch into integration:**
   ```bash
   git checkout feature/full-project-run-1
   git merge sprint/exp-0N-full-run --no-ff -m "Merge Experiment N sprint"
   git push
   ```

2. **Update Draft PR logbook:**
   ```markdown
   ## Experiment N: [Name] ✅ COMPLETE

   **Phases completed:** 5/5 + Theory Refinement
   **Key findings:** [Brief summary]
   **Issues created:** #XX, #XX
   ```

3. **Continue to next experiment**

---

### Phase 5: Failure Handling

If a phase fails after 5 review cycles:

1. **Do NOT merge** the sprint branch
2. **Document failure** in Draft PR logbook:
   ```markdown
   ## Experiment N: [Name] ❌ INCOMPLETE

   **Failed at:** Phase X
   **Reason:** [Detailed explanation]
   **Abandoned branch:** sprint/exp-0N-full-run
   **Recovery notes:** [What would be needed to complete]
   ```

3. **Create issue** for manual follow-up:
   ```bash
   gh issue create --title "Manual follow-up: Experiment N Phase X failure"
   ```

4. **Continue to next experiment** from the last successful state

---

### Phase 6: Completion

When all experiments have been attempted:

1. **Mark PR as Ready for Review:**
   ```bash
   gh pr ready
   ```

2. **Generate Process Report:**
   Create `docs/reports/full_project_run_YYYY-MM-DD.md`:

   ```markdown
   # Full Project Run Report: YYYY-MM-DD

   ## Summary
   - Experiments attempted: N
   - Experiments completed: X
   - Experiments incomplete: Y

   ## Results by Experiment

   ### Experiment 01: Stern-Gerlach ✅
   - Status: COMPLETE
   - Key findings: [...]
   - Notable challenges: [...]

   ### Experiment 02: Double-Slit ❌
   - Status: INCOMPLETE (failed at Phase 3)
   - Reason: [...]
   - Recommendations: [...]

   [...continue for all experiments...]

   ## Scientific Findings Summary
   - [Key physics results]
   - [Theoretical insights]
   - [Open questions discovered]

   ## Process Observations
   - What worked well
   - What could be improved
   - Recommendations for future runs

   ## Follow-up Items
   - #XX — [Issue description]
   - #XX — [Issue description]
   ```

3. **Post final status** to Draft PR:
   ```markdown
   ## Full Project Run Complete

   **Summary:**
   - Completed: X/N experiments
   - Incomplete: Y/N experiments
   - Duration: Z days

   **Deliverables:**
   - ✅ Comprehensive PR ready for review
   - ✅ Process Report: docs/reports/full_project_run_YYYY-MM-DD.md

   @JamesPagetButler — Ready for your review.
   ```

4. **Notify James** of completion

---

## Key Design Decisions

### Why One Integration Branch + Draft PR?

| Alternative | Problems |
|-------------|----------|
| Multiple PRs per experiment | Fragmented review, no unified view |
| Direct commits to master | No safety net, no review |
| One giant branch with everything | One integration branch provides unified view with clean merge history |

### Why Allow AI-Authorized Internal Merges?

The integration branch is NOT master. Allowing sprint→integration merges:
- Maintains clean commit history (one merge per experiment)
- Enables best-effort continuation after failures
- Reduces human intervention for successful work
- Final merge to master still requires James's approval

### Loop Prevention

Hard limit of 5 review cycles per phase prevents infinite loops. If limit reached:
- Phase is marked as failed
- Sprint is not merged
- Process continues with next experiment
- Issue created for manual follow-up

---

## Permission Hygiene

### Canonical Project Mode Permissions

Project Mode uses all Sprint Mode permissions plus internal merge capability. Before entering Project Mode, set up `.claude/settings.local.json`:

```json
{
  "permissions": {
    "allow": [
      "Bash(git *)",
      "Bash(/home/prime/.local/bin/gh *)",
      "Bash(python3 *)",
      "Bash(lake *)",
      "Bash(timeout *)",
      "Bash(ls *)",
      "Bash(GEMINI_API_KEY=* *)",
      "Bash(cd *)",
      "Read",
      "Edit",
      "Write",
      "Glob",
      "Grep",
      "WebSearch",
      "WebFetch",
      "mcp__gemini__*"
    ]
  }
}
```

**Note:** The `Bash(git *)` pattern covers `git merge` for internal merges (sprint → integration branch). Merging to master is prohibited by the safety rails below, not by permissions — it's enforced by process.

See [Sprint Mode: Permission Hygiene](sprint_mode_workflow.md#permission-hygiene) for detailed pattern explanations and env-prefix strategy.

---

## Safety Rails

### Prohibited Actions
- `git push --force`, `git reset --hard`
- Merging directly to master
- Skipping internal reviews
- Continuing after catastrophic failure (e.g., CI completely broken)

### Escalation Triggers
- Critical infrastructure failure
- Review cycle limit exceeded on multiple phases
- Confusion about physics foundations
- Dependencies between experiments that weren't anticipated

### Human Intervention Points
James can intervene at any point by:
- Commenting on Draft PR
- Requesting a pause
- Providing direction on failures
- Adjusting scope mid-run

---

## Comparison with Other Modes

| Aspect | Housekeeping | Sprint Mode | Full Project Mode |
|--------|--------------|-------------|-------------------|
| Scope | Batch of issues | Single experiment | Multiple experiments |
| Duration | Hours | Days | Weeks |
| Branches | Per-issue | Per-phase | Integration + per-sprint |
| Internal merges | No | No | Yes (sprint → integration) |
| Final PR | Multiple small | Multiple (per-phase) | Single comprehensive |
| Failure handling | Skip item | Escalate | Document & continue |

---

## Example Timeline

```
Week 1
├── Day 1: Setup, Experiment 01 Ground Truth
├── Day 2-3: Experiment 01 Implementation + Visualization
├── Day 4-5: Experiment 01 Verification + Publication
├── Day 6: Experiment 01 Theory Refinement → Internal merge ✅
└── Day 7: Begin Experiment 02

Week 2
├── Day 1-3: Experiment 02 complete → Internal merge ✅
├── Day 4-5: Experiment 03 Phases 1-2
└── Day 6-7: Experiment 03 Phase 3 fails (cycle limit)
    → Document failure, continue to Experiment 04

Week 3
├── Continue with remaining experiments...
└── ...

Week N
├── Final experiments complete
├── Generate Process Report
├── Mark PR as Ready for Review
└── Notify James
```

---

## References

- [Sprint Mode Workflow](sprint_mode_workflow.md) — Single-experiment autonomy
- [Housekeeping Mode](../CONTRIBUTING.md#housekeeping-mode) — Batch cleanup
- [The 5-Phase Lifecycle](../CONTRIBUTING.md#the-5-phase-experimental-lifecycle) — Phase definitions
- [Experiment Roadmap](../../research/README.md) — Full experiment list
