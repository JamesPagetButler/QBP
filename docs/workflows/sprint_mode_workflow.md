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

## Pre-Sprint Research Gate

Before beginning Phase 1, Claude **must** run the Research Gate checkpoint:

```bash
python scripts/research_gate.py --scope sprint-N experiment-NN
```

| Verdict | Action |
|---------|--------|
| **PASS** (exit 0) | Proceed to Phase 1 |
| **BLOCK** (exit 1) | Enter Pre-Sprint Research to resolve scoped findings, then re-run gate |
| **ERROR** (exit 2) | Escalate to James — KG may need attention |

**In Sprint Mode:** Claude runs the gate autonomously as the first action after receiving sprint approval. If the gate returns BLOCK, Claude enters a research loop:

1. Run gate → BLOCK
2. Identify scoped weak claims and research gaps from gate output
3. Conduct focused research to resolve them (literature review, KG updates)
4. Re-run gate
5. Repeat until PASS or escalate if stuck after 2 cycles

**Precedent:** Sprint 3 Pre-Sprint Research (#255) resolved 5 blocking questions before Phase 1 could begin. The gate formalises this pattern.

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

### Phase 1 Exit Criteria

Phase 1 (Ground Truth) is not complete until:

1. **Empirical Anchor section** is present and complete per the [ground truth schema](../schemas/ground_truth_schema.md#3-empirical-anchor-required)
2. **At least one primary source** with a measured value is cited — or the experiment has an explicit **Theoretical-derived** data type classification
3. **Data type classification** is declared (Quantitative-precise, Quantitative-moderate, Qualitative-binary, Formula-confirmed, Theoretical-derived, or Constraint-based)
4. **Null results** are cited if relevant experimental constraints exist
5. **Check first (#170 / #736):** before starting any experiment phase, confirm the expected-results doc's `## Prediction Classification` section is present and current (Validation / Novel / OPEN per row, each row citing the doc line it relies on); CI gates its presence via `scripts/check_prediction_classification.py`

These criteria are enforced by the [Empirical Grounding Verification](../../CONTRIBUTING.md#empirical-grounding-verification) checklist during review.

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

### Oppenheimer AI Gate (Sprint Mode autonomy hardening)

Per #383, Sprint Mode uses an AI-gate pattern to enable autonomous PR review for rework cycles where the territory is familiar. The gate is the **Oppenheimer Strategic Lead persona** ([`docs/personas/project_lead.md`](../personas/project_lead.md)) operating alongside Red Team + Gemini reviewers.

**Authority scope of Oppenheimer in Sprint Mode:**

| Action | Oppenheimer authority | Escalation trigger |
|---|---|---|
| Accept Red Team + Gemini PASS verdicts | ✅ may approve merge | n/a — routine |
| Adjudicate CONTESTED findings (Pattern 2 / CONFLICT block) | ✅ may resolve per anchor-rule (`docs/workflows/review_anchoring.md`) | If unconvergent after 3 debate rounds → Pattern 4 (James) |
| Accept BORDERLINE findings (caveated) | ✅ may approve if anchor-rule-compliant + non-blocking | Substantive theory change → defer to James |
| Modify acceptance criteria | ❌ must escalate | Always escalate |
| Change sprint scope or experiment selection | ❌ must escalate | Always escalate |
| Approve new axiom or theory revision | ❌ must escalate | Always escalate |

**Per-PR review flow under Oppenheimer AI Gate:**

1. PR opened by Dev Team (any sprint-phase artifact)
2. CI runs; Red Team review per [Activation Matrix](review_tiers.md#activation-matrix-pattern--tier) Pattern × Tier
3. Gemini review per Activation Matrix (Pattern 3 with session_id for multi-round)
4. **Oppenheimer review** (this gate): synthesises Red Team + Gemini findings, applies anchor-rule discipline, classifies CONTESTED items
5. If all reviewers concur PASS → Oppenheimer may merge (skip James explicit-merge step)
6. If any reviewer FAILS or CONTESTS → fix-iterate-cycle until PASS, OR escalate per the table above
7. If escalation triggered → Pattern 4 (James-in-the-loop) per Activation Matrix

**Entry criteria for Sprint Mode with Oppenheimer Gate:**

- [ ] Sprint scope ratified by Beekeeper (e.g., #408 closure 2026-05-15)
- [ ] Anchoring rule in effect (`docs/workflows/review_anchoring.md`)
- [ ] Activation Matrix in effect (`review_tiers.md`)
- [ ] Oppenheimer persona instantiated (prompt loaded)
- [ ] James acknowledges entry: *"Sprint Mode with Oppenheimer Gate engaged."*

**Exit criteria:**

- Sprint complete (all phases CLOSED) → return to Focus Mode default
- James halts at any point with a single command: *"Halt Sprint Mode."*
- Escalation event resolved → Sprint Mode resumes (James re-confirms)

**Decision logging:**

Every Oppenheimer-approved merge under the AI Gate logs:
- PR number + summary
- Reviewer verdicts (Red Team + Gemini)
- Anchor-rule compliance check
- Any CONTESTED items + their resolution
- Logged via Gemini MCP `record_decision` tool OR as a sticky PR comment with header `oppenheimer-gate-log`

**Git revert safety:** see [§Git Revert Safety](#git-revert-safety) below (the #383 deferred AC, delivered by #734 with the dummy-branch test on record).

**Precedent operational use (2026-05-13 through 2026-05-15):**

The Oppenheimer Strategic Lead persona was de-facto operational during the #81 PR2-PR8 theory-refinement train (PRs #412, #428, #430, #435, #424, #418, #423, #414 + #415/#419 + #413). The R6 Resolution on PR #407 (Sprint 4 scope re-frame) is the canonical precedent for Oppenheimer's strategic-review authority. The 2026-05-15 ratification of #408 Pre-Sprint-4 Strategic Scoping is the canonical precedent for sprint-boundary coherence-brief work. Sprint Mode formalises and documents this de-facto pattern.

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
4. **KG Consolidation** — before Theory Refinement begins:
   ```bash
   git diff master...HEAD --name-only | xargs python scripts/qbp_knowledge_sqlite.py suggest-updates
   python scripts/qbp_knowledge_sqlite.py report
   ```
5. **Run Theory Refinement** using KG report as input
6. **Run retrospective** (answer the 4 questions)
7. **Run Research Gate** for next sprint:
   ```bash
   python scripts/research_gate.py --scope sprint-N+1 experiment-NN
   ```
8. **Notify James** of completion

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

## Permission Hygiene

### The Problem

Claude Code stores tool permissions in `.claude/settings.local.json`. When "Always allow" is clicked on a specific command, the **exact literal** gets saved. Over time this causes:
- Giant literal commands with heredocs and special characters
- API keys embedded in saved patterns
- Parse errors when `:` characters in literals are misinterpreted
- Settings file skipped entirely on parse error — losing ALL permissions

### Canonical Sprint Mode Permissions

Before entering Sprint Mode, set up `.claude/settings.local.json` with these wildcard patterns. This replaces one-off literal accumulation with broad category coverage:

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

**Pattern explanations:**

| Pattern | Covers |
|---------|--------|
| `Bash(git *)` | All git operations (add, commit, push, branch, etc.) |
| `Bash(/home/prime/.local/bin/gh *)` | GitHub CLI — full path avoids the outdated system `gh` |
| `Bash(python3 *)` | pytest, research_gate.py, validate_knowledge.py, etc. |
| `Bash(lake *)` | Lean build system |
| `Bash(timeout *)` | Timeout-wrapped commands (e.g., `timeout 5 python3 ...`) |
| `Bash(ls *)` | Directory listings |
| `Bash(GEMINI_API_KEY=* *)` | Env-prefixed commands (see below) |
| `Bash(cd *)` | Directory changes |
| `mcp__gemini__*` | All Gemini MCP tools |

### Env-Prefix Strategy

Claude Code matches the **first token** of a command. So `Bash(gh *)` matches `gh issue view` but NOT `GEMINI_API_KEY=xxx gh issue view` because the first token is `GEMINI_API_KEY=xxx`.

**Solution:** Add explicit patterns for env-prefix wrappers:
- `Bash(GEMINI_API_KEY=* *)` — covers any command run with the API key env var
- `Bash(timeout *)` — covers timeout-wrapped commands

### Setup Procedure

1. **At session start**, Claude checks for the canonical patterns (part of Herschel Check)
2. **If missing**, Claude proposes the canonical template to James
3. **Periodically**, remove accumulated literal patterns that are already covered by wildcards
4. **Never** save patterns containing API keys, heredocs, or multi-line content

### Cleanup

To clean accumulated literals:
```bash
# Back up current settings
cp ~/.claude/settings.local.json ~/.claude/settings.local.json.bak

# Replace with canonical template (review first!)
cat ~/.claude/settings.local.json
```

Remove any entry that:
- Contains `GEMINI_API_KEY=` followed by an actual key value
- Contains heredoc content (`<<'EOF'`)
- Is a long literal already covered by a wildcard (e.g., `gh issue comment 289 --body "..."` is covered by `Bash(/home/prime/.local/bin/gh *)`)

---

## Safety Rails

### Prohibited Actions
- `git push --force` (confirm-first everywhere); `git reset` of any mode on a shared branch — see [Git Revert Safety](#git-revert-safety)
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

## Git Revert Safety

Delivered by #734 (the #383 deferred AC). Four blocks: what we tag, how we undo, what the
Oppenheimer gate checks before a merge, and how each action is logged. The dummy-branch test
that validates the revert path is on record at
[`analysis/734-revert-safety-test-log.md`](../../analysis/734-revert-safety-test-log.md).

### Tagging strategy

Tags are the recovery anchors: a revert decision is made relative to the nearest tag, never
relative to "whatever HEAD was yesterday".

| Event | Tag name | Who creates + pushes | When |
|---|---|---|---|
| Sprint opens (scope ratified, Oppenheimer Gate engaged) | `sprint-N-open` | beekeeper or herschel (sprint-driver) | on the merge-base commit the sprint branches from |
| Sprint closes (close runbook run in full) | `sprint-N-close` | beekeeper or herschel | on the master commit after the last sprint PR merges |
| Theory-bearing PR (Tier 3 / `proofs/` / `docs/foundations/`) about to merge | `pre-merge-<PR>` | the merging seat, immediately before `gh pr merge` | on the master commit the PR will land on |
| Anchor-ledger version bump (CTH ledger) | `ledger-vX.Y.Z` | the seat that merges the bump (cth-implementor lane) | on the merge commit that carries the new version |
| Pre-registration frozen (spike runbook) | `prereg-<slug>-frozen-vN` | the spike director, after the sha256 is posted on the issue | on the commit that contains the FROZEN document |

Rules:

- **Annotated tags only** (`git tag -a`), message = the issue/PR number and one line of context.
  Lightweight tags carry no author or date and cannot be signed.
- **Signed where the signer is available** (`git tag -s`): the beekeeper's YubiKey GPG key signs
  sprint and ledger tags; seats without a key use `-a` and say so in the tag message.
- **Push a tag by name** — `git push origin sprint-N-open` — never `git push --tags` (it sweeps up
  local scratch tags) and never `git push -f origin <tag>`: moving a tag is a force-push and is
  confirm-first like every other force-push (below).
- A tag is immutable once pushed. A wrong tag is corrected by a **new** tag (`…-v2`) plus a note
  on the issue, not by deletion.
- Tags never substitute for the ledger or the pre-registration sha256; they locate the commit the
  recorded sha256 belongs to.
- **Authority note.** A tag push by a seat is a new write category not covered by the standing
  federation authorizations. Until the beekeeper ratifies this section, every tag in the table is
  created and pushed by the beekeeper (seats may *propose* the tag name + commit on the issue).

### Revert-vs-reset decision tree

`git revert` is the default. `git reset` of any kind — `--soft`, `--mixed`, `--hard` — is
**forbidden on shared branches**: master, and any pushed PR branch another seat has fetched. All
three modes rewrite published history on the next push and silently drop the collaborator's view
of it (the test log shows exactly what a collaborator loses).

```
A bad change has landed. Where?
│
├─ Local-only branch nobody else has fetched
│    → reset / amend / rebase are fine (your history, your risk).
│
└─ Shared branch (master, or a pushed PR branch another seat has fetched)
     → git reset is FORBIDDEN (any mode). Choose:
     │
     ├─ Is the bad commit already built upon (later commits depend on its content)?
     │    └─ yes → NEW FORWARD COMMIT that fixes the state. A revert would conflict
     │             with or silently undo the dependent work.
     │
     ├─ Would a revert re-open a closed ledger version or a FROZEN pre-registration?
     │    └─ yes → NEW FORWARD COMMIT that bumps the version (ledger-vX.Y.Z+1,
     │             prereg …-frozen-vN+1). Closed versions are never un-closed.
     │
     └─ otherwise → git revert <sha> --no-edit, one revert per bad commit, NEWEST
                    first (reverse chronological: C, then B, then A — reverting the
                    oldest while its dependants stand guarantees conflicts); keep the
                    auto message, add the rationale in the log entry. A revert of a
                    TRUE merge commit uses -m 1 (parent 1 = the target branch); this
                    repo squash-merges, so a landed PR is one ordinary commit and
                    needs no -m. Either way the revert is a PR like any other.
```

- Expect a conflict when neighbouring commits touch adjacent lines (the #734 test reverted the
  middle of three one-line appends and conflicted): resolve by hand, `git add`, `git revert
  --continue`; `--no-edit` only helps when the revert applies cleanly. Git also refuses `git switch`
  mid-revert and `git branch -D` of the checked-out branch — finish or `--abort` first.
- A revert on master goes through a PR with the same review tier as the change it undoes;
  "it is only a revert" does not lower the tier.
- **Force-push is confirm-first everywhere**, on every repo, regardless of ownership or interim
  write-grant — workspace `CLAUDE.md` §Federation-mode standing authorizations ("Force-push stays
  confirm-first … regardless of repo ownership or interim grant"). A classifier block on a
  force-push is the rule working, not an obstacle to route around.
- Never `git stash` in a shared worktree stack and never `git reset --hard` outside a throwaway
  clone; the `worktree-isolation` hard gate exists because a shared tree lost data (2026-05-14).

### Oppenheimer-gate checklist

The gate "synthesises Red Team + Gemini findings" (flow step 4 above). Synthesis is not a
verdict; before the merge the gate ticks all four groups, citing the artifact for each tick.

- **Correctness**
  - [ ] every statement in the PR matches its proof or evidence (theorem text = the claim; a
        number in prose = the number in the measurement file)
  - [ ] every derived formula or sign is checked against two known limits and the check is
        asserted in the PR (the w_eff sign in PR #774 was missed by both reviewers and caught only by
        a two-limit check)
  - [ ] the anchoring rule holds: no unanchored BLOCKING claim in any review (`review_tiers.md`)
- **Scope**
  - [ ] the diff is a subset of the tracked issue's ACs; anything else is split out or named as
        an explicit, reviewed addition
  - [ ] no theory smuggled into a housekeeping PR (tier 3 / `proofs/` / `docs/foundations/`
        content in a `housekeeping`-labelled PR is a BLOCK and a re-tier)
- **Tests**
  - [ ] CI green at the **head** sha, read from `gh pr checks` at the moment of the verdict
  - [ ] every test-plan box ticked, or ⊘-nil'd with a reason (`- [ ] ~~option~~ ⊘ reason`)
  - [ ] a refactor shows which existing tests cover each changed path
- **AC verification**
  - [ ] each AC of the tracked issue ticked on the issue with the evidence link that satisfies it
  - [ ] `Closes #N` present only when every AC of #N is met; `Tracks #N` when legs remain
  - [ ] `mergeStateStatus == CLEAN` (branch current, not BEHIND) in the readiness line

A gate verdict is APPROVE / APPROVE-WITH-CONCERN / DEFER. A DEFER names the box that is not
ticked. The gate never ticks a box on the author's word (evidence-first discipline).

### Logging format

**Per-action entry.** Every Oppenheimer-approved merge and every revert or forward-fix on a
shared branch logs the fields in *Decision logging* above (PR + summary, reviewer verdicts,
anchor-rule check, CONTESTED items) **plus**:

- `rationale` — why this action and not nothing
- `alternatives considered` — the branches of the decision tree that were rejected, one clause each
- `risk` — what could still be wrong after this action, and who watches for it

**Phase-boundary summary.** At sprint open, at sprint close and at each merge to master, one
entry with: `what changed` (PRs/commits, tag), `what was reverted` (sha → revert sha, or "none"),
`open risks` (carried forward, each with an owner). It is posted where the per-action log lives
(Gemini MCP `record_decision`, or a sticky PR / tracking-issue comment headed
`oppenheimer-gate-log`).

Filled example (merge boundary):

```
oppenheimer-gate-log · merge · PR #NNN · 2026-11-01T03:10Z
summary: revert of 1a2b3c4 (ledger row 17 re-tagged PROOF without a proof artifact)
verdicts: Red Team APPROVE (3/3) · Gemini APPROVE · §I4 ack cth-implementor
anchor-rule: PASS — the revert cites the missing artifact, not an opinion
contested: none
rationale: row 17 claimed PROOF with no Lean file; the ledger must not carry an
  unbacked PROOF across the sprint-5-open tag
alternatives considered: forward commit re-tagging to ARGUMENT (rejected — the
  original commit had no other content, revert is exact); reset (forbidden, shared)
risk: a downstream edge may already cite row 17 as PROOF — cth-implementor re-runs
  the inverse-audit tool; owner: cth-implementor, due before sprint-5-open
--- phase boundary ---
what changed: PR #NNN merged at d4e5f6a; tag pre-merge-NNN on c3d2e1f
what was reverted: 1a2b3c4 → d4e5f6a
open risks: inverse-audit re-run pending (cth-implementor)
```

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
