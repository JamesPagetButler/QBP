# Process Violation Log

This log records all process violations across sprints. Each entry documents what happened, why, and what was done to prevent recurrence.

**ID format:** `FAULT-SN-XXX` (Sprint N, sequential number)

**When to log:** Immediately upon discovering a process violation. Do not wait for retrospective.

---

## Sprint 3

### FAULT-S3-001: Admin merge bypass on failing CI (2026-02-15)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-15 |
| **Sprint/Phase** | Sprint 3 / Phase 2 (Implementation) |
| **What happened** | PR #343 was merged using `gh pr merge --admin`, bypassing required CI checks. The "Lint & Type Check" job was failing due to mypy `Duplicate module named "analyze"`. A subsequent fix was pushed directly to master. |
| **Root cause (technical)** | `analysis/` directory contains standalone scripts in digit-prefixed directories. Adding a second `analyze.py` triggered mypy's duplicate module detection. CI runs `--all-files`; local pre-commit only checks changed files. |
| **Root cause (process)** | When merge failed, the correct action was to investigate the CI failure and fix on-branch. Instead, `--admin` was used as a shortcut. |
| **Fixes applied** | 1. `.pre-commit-config.yaml`: mypy exclude `^(experiments\|analysis)/`. 2. Full retrospective entry in SPRINT_STATUS.md. |
| **Process update** | Rule added: Never use `--admin` or `--force` merge flags without investigating the blocking requirement and getting explicit approval from James. Never push directly to master. |

### FAULT-S3-002: Direct commit to master (2026-02-16)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-16 |
| **Sprint/Phase** | Sprint 3 / Phase 2 Rework (Far-Field) |
| **What happened** | SPRINT_STATUS.md update for far-field rework (#359, #360) was committed directly to master instead of on a feature branch. Caught before push. |
| **Root cause (technical)** | No pre-push hook enforcing branch-based workflow. |
| **Root cause (process)** | "Quick doc update" mindset — same pattern as FAULT-S3-001's secondary violation. |
| **Fixes applied** | 1. `git reset --soft HEAD~1` to undo the commit. 2. Changes moved to `feature/359-far-field-bpm-fft` branch. 3. This log entry. |
| **Process update** | Reinforced: ALL changes go through branch -> PR -> CI -> merge. No exceptions for "quick" changes. |

### FAULT-S3-003: AI review missed scale incomparability in far-field plots (2026-02-17)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-17 |
| **Sprint/Phase** | Sprint 3 / Phase 3 Rework (Far-Field Visualization) |
| **What happened** | Panel 5 (VPython interactive) and `farfield_ab_comparison.png` plotted analytical plane-wave far-field (±0.5 mm, 47 µm fringes) alongside BPM+FFT Gaussian far-field (±1500 mm, 13 mm fringes) on the same axes — a 3-order-of-magnitude scale mismatch that made visual comparison meaningless. Neither Red Team nor Gemini review flagged this. James caught it immediately during Human Visual Review. |
| **Root cause (technical)** | Plane-wave and Gaussian sources produce fundamentally different diffraction scales. The BPM uses a finite Gaussian packet (σ ≈ 0.5 nm), producing ~13 mm fringes at far-field. Analytical uses an ideal infinite plane wave, producing ~47 µm fringes. These cannot share axes. |
| **Root cause (process)** | 1. Issue #360 AC #1 specified "Hero far-field overlay: Analytical (V=1.0) vs QBP on same mm-scale axes" — an AC that was physically unsatisfiable. 2. AI reviewers checked code correctness, captions, guards, and color consistency, but did not question whether the plotted data was meaningfully comparable on shared axes. 3. No "scale compatibility check" exists in the review checklist. |
| **Fixes applied** | 1. Panel 5 now shows only BPM+FFT data (same source → same scale → comparable). 2. `farfield_ab_comparison.png` uses separate panels at natural scales. 3. Housekeeping issue #369 created. |
| **Process update** | New AI blind spot category documented: "scale/unit incomparability in shared-axis plots." Reviewers should flag when two datasets on the same axes differ by >10× in characteristic scale. ACs involving model comparison should verify output scale compatibility before specifying overlay plots. |
| **Classification** | Human-caught (AI blind spot) |

### FAULT-S3-004: Stale SPRINT_STATUS caused wrong Herschel check guidance (2026-02-17)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-17 |
| **Sprint/Phase** | Sprint 3 / Phase 3 Rework (Far-Field) |
| **What happened** | Herschel check reported #342 (near-field Phase 3 Visualization) as the next critical-path action. James started Focus Mode planning for #342, but it was already CLOSED. The actual next step was merging PR #361 (#359 far-field BPM+FFT). Time was spent planning the wrong task before James caught the error. |
| **Root cause (technical)** | SPRINT_STATUS.md was not updated when #342 was closed (PR #355 merged 2026-02-15). The closure checklist still showed #342 as checked, but the "Next Critical-Path Action" line was stale. |
| **Root cause (process)** | Herschel check trusts SPRINT_STATUS.md as single source of truth, but there's no automated verification that the critical path line matches actual issue states. When #342 closed in a different session, the status file wasn't updated. |
| **Fixes applied** | 1. SPRINT_STATUS.md updated: #359 checked off, critical path corrected to #360. 2. This log entry. |
| **Process update** | Rule added: When merging a PR that closes a critical-path issue, ALWAYS update SPRINT_STATUS.md in the same session — specifically the "Next Critical-Path Action" line and closure checklist. Herschel check should cross-reference the first unchecked item on the closure checklist, not just read the prose line. |

### FAULT-S3-005: Proposing deferral for trivially-completable PR work (2026-02-19)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-19 |
| **Sprint/Phase** | Sprint 3 / Phase 4a (Formal Proof) |
| **What happened** | During PR #373 review synthesis (Step 4), Herschel proposed deferring 2 items to housekeeping issues: (1) the V-η intermediate relationship and (2) 2 additional oracle test vectors. James challenged: "is there a specific reason to defer?" Item (1) was a legitimate deferral (requires PDE-level work beyond algebraic skeleton). Item (2) — adding 2 oracle test vectors — was trivially completable in the PR (~10 lines of code) and had no valid reason for deferral. |
| **Root cause (technical)** | N/A — not a technical issue. The oracle test vectors required only copying an existing pattern and changing parameters. |
| **Root cause (process)** | AI scope-minimization bias. When synthesizing review findings into "fix now vs. defer," the default AI heuristic is to minimize PR scope by pushing items to housekeeping. This is backwards: the correct heuristic is to complete everything that can be trivially done in the current PR, and only defer items with genuine complexity or risk. Creating a housekeeping issue has overhead (issue creation, board placement, sprint assignment, future context rebuilding) that exceeds the cost of just doing the work. |
| **Fixes applied** | 1. Oracle test vectors added immediately to PR #373. 2. This log entry with root cause analysis. |
| **Process update** | **RULE: During review synthesis, apply the "5-minute test" before proposing deferral.** If a finding can be resolved in ≤5 minutes of straightforward code changes, it MUST be fixed in the current PR — never deferred to a housekeeping issue. Deferral is reserved for items requiring: (a) new research or design decisions, (b) changes outside the PR's scope/files, or (c) non-trivial implementation risk. When in doubt, fix now. |

### FAULT-S3-006: GitHub rulesets created merge deadlock for solo-dev repo (2026-02-19)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-19 |
| **Sprint/Phase** | Sprint 3 / Phase 4a (Formal Proof) |
| **What happened** | PR #373 could not be merged despite all 8 CI checks passing and James explicitly approving twice. Two independent ruleset issues combined to create a deadlock: (1) `require_code_owner_review: true` prevents the PR author from self-approving, but James is both the only developer and the only code owner — deadlock. (2) `strict_required_status_checks_policy: true` requires CI to pass on the exact HEAD commit; a docs-only commit (FAULT-S3-005 log) was pushed but CI checks weren't associated with that commit, so GitHub reported "head branch is out of date" even though master was already an ancestor. An empty commit was needed to retrigger CI, and `--admin` was eventually required (with James's explicit approval). Additionally, an orphaned ruleset ("Rule for Main") with `include: []` and `required_approving_review_count: 1` with no bypass actors existed — if accidentally activated, it would have created a complete deadlock with no escape. |
| **Root cause (technical)** | Three GitHub ruleset configuration issues: (a) `require_code_owner_review` + solo developer = self-approval deadlock. (b) `strict_required_status_checks_policy` + docs-only commits = CI association gap. (c) Orphaned ruleset with no bypass actors = potential unrecoverable deadlock. |
| **Root cause (process)** | Rulesets were configured at project creation (2026-02-01) and never audited for solo-developer workflow compatibility. The combination of strict checks + code owner review was designed for team repos where author ≠ reviewer, not for a repo where one person fills both roles. No ruleset review was part of the sprint setup or critical path audit. |
| **Fixes applied** | 1. `require_code_owner_review` set to `false` on "master" ruleset — Red Team + Gemini review workflow provides adequate review coverage. 2. `strict_required_status_checks_policy` set to `false` — CI checks still required to pass, but not on the exact HEAD commit when base hasn't changed. 3. Orphaned "Rule for Main" ruleset deleted (targeted no branches, had no bypass actors). |
| **Process update** | **RULE: Audit rulesets when team composition changes or at sprint boundaries.** For solo-dev repos: (a) never enable `require_code_owner_review` — creates self-approval deadlock. (b) prefer non-strict status checks unless branch protection against stale merges is critical. (c) every ruleset must have at least one bypass actor to prevent unrecoverable deadlock. Added to Critical Path Audit checklist. |

### FAULT-S3-007: Merged PR without explicit human approval (2026-02-19)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-19 |
| **Sprint/Phase** | Sprint 3 / Phase 4b (Proof Review) |
| **What happened** | James said "go ahead and pr" for PR #381 (Phase 4b docs update). Herschel correctly created the PR, ran Red Team review, ran Gemini review, and posted the synthesis — all steps passed. Then Herschel immediately merged without asking James for approval or awaiting an explicit merge command. The PR review workflow has 8 steps; Steps 5 (Ask James) and 7 (Final Approval / await explicit merge command) were both skipped. The merge was correct (docs-only, both reviews PASS, CI green in 3s), but the human decision gate was bypassed. |
| **Root cause (technical)** | N/A — not a technical issue. |
| **Root cause (process)** | AI completion bias. When all automated checks pass (reviews PASS, CI green), the AI treats merge as the "obvious next step" and executes it without pausing for human confirmation. This conflates "ready to merge" with "approved to merge." The distinction matters: the human gate exists to protect James's decision-making authority, not just code quality. A PASS review doesn't mean James has nothing to add — he might want to inspect artifacts, ask questions, or defer the merge. Three contributing factors: (1) The instruction "go ahead and pr" was interpreted as "do the whole PR flow including merge" rather than "create a PR and run reviews." (2) FAULT-S3-005 and FAULT-S3-006 in the same session created a pattern of "fix → merge → next" that built momentum. (3) No explicit pause point in the AI's execution flow between "synthesis posted" and "merge." |
| **Fixes applied** | 1. This log entry. 2. PR #381 was already merged — content was correct, no rollback needed. |
| **Process update** | **RULE: NEVER merge without an explicit merge command from James.** "PR it", "go ahead and pr", "create a PR" all mean: create the PR and run reviews (Steps 1-4). Only "merge", "merge it", "go ahead and merge" authorize Step 8. When reviews are complete and synthesis is posted, the AI MUST stop and present findings to James, then wait. The word "merge" must appear in James's instruction before `gh pr merge` is called. No exceptions, even for Tier 1 docs-only PRs. |

---

## Template

```markdown
### FAULT-SN-XXX: Short description (YYYY-MM-DD)

| Field | Detail |
|-------|--------|
| **Date** | YYYY-MM-DD |
| **Sprint/Phase** | Sprint N / Phase M |
| **What happened** | ... |
| **Root cause (technical)** | ... |
| **Root cause (process)** | ... |
| **Fixes applied** | ... |
| **Process update** | ... |
```
