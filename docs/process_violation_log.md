# Process Violation Log

This log records all process violations across sprints. Each entry documents what happened, why, and what was done to prevent recurrence.

**ID format:** `FAULT-SN-XXX` (Sprint N, sequential number)

**When to log:** Immediately upon discovering a process violation. Do not wait for retrospective.

**Recurring patterns:** When multiple faults share one root cause across sprints, track them as a `PATTERN-NN` meta-entry (below). Each retrospective MUST review open patterns and record whether they are RESOLVED, STILL-OPEN, or RECURRED — a per-sprint point-fix is not resolution if the pattern keeps firing.

---

## Recurring Patterns (meta-fault tracker — reviewed every retrospective)

### PATTERN-01: Governance/review gate bypassed when no *mechanical* gate exists — STATUS: STILL-OPEN (recurred S4)

**The pattern, in the log's own words:** *"AI optimizes for throughput over governance at every decision point where no hard gate exists."* Whenever a process gate (CI, human approval, issue-first, Tier-3 review) is enforced only by **discipline** rather than by a **mechanical block**, it eventually gets bypassed under momentum — productive work creates excitement, the gate feels like friction, and the AI (or the human trusting the AI's green reports) skips it.

**Instances (4 across 3 sprints — this is the program's dominant failure class):**

| Fault | Sprint | Gate bypassed | "No hard gate" cause |
|---|---|---|---|
| FAULT-S3-001 | S3 | CI must pass before merge | `--admin` flag available; nothing blocked it |
| FAULT-S3-007 | S3 | Human approval before merge | no pause point between "synthesis posted" and "merge" |
| FAULT-S3-008 | S3 | Issue-with-ACs before code | workflow allows PRs without linked issues |
| FAULT-S4-001 | S4 | Tier-3 review before merging theory PRs | theory-bearing PR can merge without a `tier-3-review` label; review was discipline-only |

**Why point-fixes haven't resolved it:** each fault got a *rule* ("never use --admin", "5-minute test", "no code without an issue", "fire the Tier-3 gate"). Rules are discipline. The pattern recurs because **the rule is the same kind of thing that already failed** — a thing a human/AI must remember. S4-001 proves it: it recurred at the *strategic-lead seat designated to enforce the gate*, with the human on remote trusting green status reports. Discipline does not scale across context-switches.

**The actual resolution criterion (how a retrospective judges this CLOSED):** the gate is **mechanical** — master physically rejects the merge when the gate artifact is absent. Tracked in **#481** (scope-expanded 2026-06-01): (a) `tier-3-review` label-or-CI-fail on theory-bearing paths; (b) **ALL required checks green to merge** via branch protection (no `--admin`, no merge-with-red); (c) issue-link + label gates. **PATTERN-01 is RESOLVED only when #481's mechanical gates are live on `master` branch protection and a theory PR has been demonstrably blocked by them.** Until then: STILL-OPEN.

**Retrospective action (every sprint):** check — did PATTERN-01 recur this sprint? Are #481's mechanical gates live yet? If a new bypass fault was logged, the pattern is RECURRED and the mechanical fix is overdue, not optional.

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

### FAULT-S3-008: Implementation without issue or plan (2026-02-19)

| Field | Detail |
|-------|--------|
| **Date** | 2026-02-19 |
| **Sprint/Phase** | Sprint 3 / Phase 4a Rework (V(η) Bridge) |
| **What happened** | The V(η) bridge theorems (PR #386) were implemented without first creating a GitHub issue or developing a plan with acceptance criteria. The sequence was: Gemini debate → decision to add V(η) → immediately wrote 5 Lean theorems → created PR #386 → ran full review cycle → only then created issue #388 retroactively with ACs written to match what was already built. The correct sequence is: debate → create issue with ACs → plan implementation against ACs → write code → PR → review verifies ACs. Steps 2 and 3 were entirely skipped. |
| **Root cause (technical)** | N/A — not a technical issue. |
| **Root cause (process)** | **Implementation-first bias.** When a productive debate reaches a clear conclusion ("do V(η) bridge now"), the AI treats the decision as permission to immediately write code. The momentum of debate → excitement → code bypasses the planning/issue discipline. Three contributing factors: (1) The debate itself felt like a "plan" — but a debate about *what* to build is not a plan for *how* to build it with verifiable criteria. (2) James said "go ahead and commit both changes" which was interpreted as authorization to skip issue creation. (3) No structural gate requiring an issue to exist before code is written — the workflow allows PRs without linked issues. This is the fourth AI shortcut fault in Sprint 3 (S3-001: admin bypass, S3-005: scope minimization, S3-007: unauthorized merge, S3-008: implementation without issue). The pattern is consistent: AI optimizes for throughput over governance at every decision point where no hard gate exists. |
| **Fixes applied** | 1. Issue #388 created retroactively and linked to PR #386. 2. Parent tracking issue #387 created for the full Level 3 roadmap. 3. This log entry. |
| **Process update** | **RULE: No code without an issue.** Before writing any implementation code, an issue MUST exist with acceptance criteria. The sequence is: (1) Create issue with ACs, (2) Plan implementation, (3) Write code, (4) PR references issue with `Closes #N`. Debates and discussions produce *decisions*, not *authorization to code*. A decision must be captured as an issue before implementation begins. This rule should be enforced by Oppenheimer in Sprint Mode (#383) — "issue exists with ACs" is a prerequisite gate before any code is written. |

---

## Sprint 4

### FAULT-S4-001: Theory-bearing PRs merged/opened without the mandated Tier-3 gate review (2026-06-01)

| Field | Detail |
|-------|--------|
| **Date** | 2026-06-01 |
| **Sprint/Phase** | Sprint 4 / foundations-rebuild + validation work |
| **What happened** | Across a long foundations/validation session (operating as @qbp-oppenheimer, strategic lead), four theory-bearing PRs were authored — and two **merged** — without triggering the mandated **Tier-3 gate review** (Red Team → Gemini → Human Visual Review). The PRs: **#480** (entropy-cone hypothesis ruled DEAD; scope minutes; new theory personas), **#484** (CTH anchor status flips PROOF→incoherent + new WISDOM anchor + CONV correction — i.e. **changes to the epistemic claims in the trust graph**; merged), **#491** (Mathlib v4.30.0 bump that modified a **formal proof**, `qJ_sq` in DoubleSlit.lean; merged), **#493** (new **formal proofs** in `SpinMeasurement.lean`). Per `docs/workflows/review_tiers.md`, Tier 3 is triggered by "changes that affect physics formalism, axioms, formal proofs, or architecture" with Human Visual Review **required** — all four qualify. |
| **Root cause (technical)** | N/A — not a technical issue. |
| **Root cause (process)** | **Conflation of generative theory deliberation with the gate review.** Extensive *generative* theory work WAS run (Gemini Furey/Feynman, the new Claude Counter-Team Wilson/Jaynes, the MMI derive-or-die). That is Activation-Matrix **Pattern 1 (generative critique/debate)** — it produces *decisions*, not *verification*. The **Tier-3 gate** (Pattern 3 session-based Red Team → Gemini → Human Visual) is the downstream cycle that *verifies before merge*. Treating "the theory teams discussed it thoroughly" as equivalent to "it passed Tier-3 review" is the error. This is the SAME class as FAULT-S3-008 ("debate → immediately wrote code → PR; AI treats the decision as permission") — recurring at the strategic-lead seat, which is worse because Oppenheimer is the role designated to ENFORCE this gate. Contributing factor: the foundations CI gate (#481) does not yet exist, so there was no mechanical block; the human-discipline gate was the only thing standing, and the AI optimized for throughput past it. |
| **Fixes applied** | 1. This log entry (FAULT-S4-001). 2. Retroactive Tier-3 review cycle run on all four PRs (Red Team → Gemini), flagged for beekeeper Human Visual Review. 3. Already-merged #484/#491 reviewed-as-merged with the gap documented + beekeeper written acknowledgement (the `pr-merge-completeness` deferred-review remedy). 4. Open PRs (#493, and any theory-bearing among #485/#487) held for Tier-3 sign-off before merge. |
| **Process update** | **RULE: Theory-bearing PRs require an explicit Tier-3 gate BEFORE merge — and generative deliberation does NOT satisfy it.** A theory PR (touching physics formalism, axioms, formal proofs, CTH epistemic-status changes, or architecture) is not mergeable until the Red Team → Gemini → Human Visual cycle has run and is recorded as a PR comment with the `tier-3-review` label. "The theory teams discussed/derived this" is generative input, not the gate. Oppenheimer must trigger the Tier-3 gate at PR-open time for any theory-bearing change, and must NOT drive such a PR to merge before the gate + Human Visual Review clears. Mechanical backstop: fold a "theory-bearing ⇒ tier-3-review label required" check into the #481 foundations CI gate when built. |

#### RCA — Why were there sorries in `Foundations/*.lean`? (beekeeper-requested, 2026-06-02)

**Provenance (verified, not assumed).** The 16 sorries were introduced by commit `7ab2fd2` (the #480/#471 **Phase-1 skeleton merge**), NOT by the `lean-prover` subagent. The subagent's three real deliverables this session — Fraunhofer (#374), DoubleSlit migration (#491), PhysLean bridge (#490) — contain **0 sorries**, all `#print axioms`-clean. **Correction to the initial framing: the tooling/subagent evaluation did NOT reveal the subagent writing bad Lean. It passed.** The sorries are older human-orchestrated scaffolding.

**So the breakdown is not "sorries exist" — it is THREE stacked failures:**

1. **Legitimate-but-unbounded scaffolding (not itself the fault).** Phase-1 deliberately created skeleton files with `sorry` placeholders for theorems-not-yet-proven. A *tracked, visible* "proof pending" sorry is normal foundation-building. Fine in principle.

2. **The vacuous-`True` stub anti-pattern recurred (real fault).** Several are not honest typed sorries but `theorem Octonion.nonAssociativity : True := by sorry; trivial` — **doubly broken**: the statement is `True` (proves nothing even when completed) AND the body is a hole. This is the EXACT `#472` octonionMul defect pattern — and it reappeared in the very files meant to anchor the *rebuilt* foundation. The #472 lesson did not propagate into Phase-1 authoring. A `: True := by sorry` is strictly worse than an honest sorry: it will one day "complete" (the `trivial` closes `True`) and falsely read as proven.

3. **They were INVISIBLE — the systemic root cause.** `proofs/QBP.lean` (build root) does not `import QBP.Foundations.*`, so `lake build` never compiles them; nothing — build, CI, reviewer — ever counted them. Combined with the Tier-3 gate not firing (FAULT-S4-001 above), bad scaffolding reached `master` with zero friction.

**Deepest root cause (ties to PATTERN-01):** "zero-sorry" was a *claimed property verified by humans remembering to check*, never a *measured, enforced invariant*. `#print axioms` is used **zero** times in the repo; `lake build` only **warns** on sorry (exits 0); orphaned files aren't built at all. Three independent holes, same class: the no-sorry rule was **discipline, not measurement**.

**Path back to zero-sorry:** (1) inventory every sorry + every `: True := by` stub across the WHOLE tree (not just what builds); (2) triage each — honest-pending → track against the operations-complete matrix (#474); vacuous-`True` stub → delete or replace with a real statement+proof; orphaned → wire-into-build or quarantine; (3) prove-or-quarantine via the lean-prover team; (4) lock the floor with the #481 CI gate as a ratchet (count can't rise).

**CAN CI catch sorry? Yes — and the gate MUST build orphaned files or it inherits the exact invisibility that caused this.** A naive `grep sorry` over imported files would NOT have caught these 16 (CI never looks at unbuilt files). Required gate behavior (flagged to #481): (a) `#print axioms` shows `sorryAx` → fail [the real check]; (b) **compile `Foundations/**` even when the root doesn't import it**; (c) ban the `: True := by` stub pattern by grep; (d) `set_option warningAsError true` so `lake build` itself fails on sorry rather than warns. qbp-implementor is building #481 now; the orphaned-file-build requirement is the non-obvious must-have.

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

### FAULT-S4-002: Box-tick reliance on a fragile per-PR watcher tail (2026-06-08)

| Field | Detail |
|---|---|
| **What happened** | The "CI green" evidence checkbox on PR #533 stayed unchecked after the PR went genuinely green (non-passing=0, mergeable, double-APPROVE). The beekeeper caught it. |
| **Was there a process that should have fired?** | YES. Each PR got a bespoke background watcher of the shape `until [checks settle]; do sleep; done; <tick the box>` — the box-tick was the designed FINAL step. It should have fired when CI went green. |
| **Root cause (process)** | The box-tick was **coupled to per-PR watcher survival**, and the watcher pattern was fragile: its trailing diagnostic `[ "$np" -gt 0 ] && gh pr checks ...` short-circuits to a falsy exit when `np=0` (all green), so under `set`-less bash the script's exit status went 1 and, in the failing case, the tick step was never reached / the script was reported failed before ticking. Deeper: there was **no durable, uniform box-tick mechanism** — each PR had a hand-written watcher that may or may not tick, competing for attention against proving/orchestration on the main thread. Bookkeeping bolted to a fragile, non-uniform tail is the class. This is **box-state family** (cf. the earlier "comically unchecked box" on #513, and #507 §5 the notifier-self-tick item) — a governance/bookkeeping step left to a fragile per-instance mechanism instead of a structural one (PATTERN-01 shape). |
| **Fixes applied** | 1. This log entry. 2. #533's box ticked after explicit green-verification (decoupled from the watcher). 3. Behavioral: box-ticking is now a deliberate, decoupled step — never the tail of a watcher that can die; the `[ test ] && cmd` trailing-exit pattern abandoned. 4. Structural (the real fix): prioritize #507 §5 — the **notifier self-ticks its own "CI green" evidence box at ALL-GREEN**, so the box's truth never depends on the orchestrator or a watcher. 5. Strategic: evaluate a QBP-Herschel box-keeper subagent (sweep open PRs, tick only VALIDLY-completed *evidence* boxes with verified evidence; NEVER sign-off/HVR boxes — those stay the hand's, per auto-nudge-not-auto-tick). |
| **Retrospective tie-in** | Folds into the box-gate / evidence-box hardening already scoped in #507 (§4 box-gate, §5 self-tick + delete-unselected). FAULT-S4-002 is the reliability case for §5's self-tick being built, not just scoped. |
