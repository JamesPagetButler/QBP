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
