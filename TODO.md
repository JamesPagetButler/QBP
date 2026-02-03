# QBP Project Plan & TODO

This document serves as the official project plan, tracking our high-level roadmap and the granular tasks required to achieve our goals.

**Workflow:** All work should be driven by GitHub Issues. PRs must reference the issue they address.

---

## Project Roadmap (The Eight-Fold Path)

This is our strategic guide. We will tackle these items sequentially.

| # | Experiment | Status | Issue |
|---|------------|--------|-------|
| 1 | The Stern-Gerlach Experiment | **Visualization** | [#29](https://github.com/JamesPagetButler/QBP/issues/29) |
| 2 | The Double-Slit Experiment | Next | [#22](https://github.com/JamesPagetButler/QBP/issues/22) |
| 3 | The Lamb Shift | Upcoming | [#30](https://github.com/JamesPagetButler/QBP/issues/30) |
| 4 | Bell's Theorem Experiments | Upcoming | [#23](https://github.com/JamesPagetButler/QBP/issues/23) |
| 5 | Derivation of Particle Statistics | Upcoming | [#32](https://github.com/JamesPagetButler/QBP/issues/32) |
| 6 | Modeling Positronium's Ground State | Upcoming | [#33](https://github.com/JamesPagetButler/QBP/issues/33) |
| 7 | The Hydrogen Atom Spectrum | Upcoming | [#34](https://github.com/JamesPagetButler/QBP/issues/34) |
| 8 | The Anomalous Magnetic Moment (g-2) | Aspirational | [#31](https://github.com/JamesPagetButler/QBP/issues/31) |
| 9 | Gravitational Lensing & Rotation Curves | Aspirational | [#35](https://github.com/JamesPagetButler/QBP/issues/35) |

---

## Current Sprint: Stern-Gerlach Visualization

The core Stern-Gerlach simulation is complete. Current focus: publication-ready visualizations.

### Active Tasks

| Task | Issue | Status |
|------|-------|--------|
| Stern-Gerlach Manim animations | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | TODO |
| Double-Slit theory & implementation | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | TODO |

### Recently Completed (PR #27, #28)

| Task | Issue | Status |
|------|-------|--------|
| Add `seed` parameter to `measure()` | [#16](https://github.com/JamesPagetButler/QBP/issues/16) | ✅ Done |
| Add type hints to `qphysics.py` | [#17](https://github.com/JamesPagetButler/QBP/issues/17) | ✅ Done |
| Vectorize simulation loop | [#18](https://github.com/JamesPagetButler/QBP/issues/18) | ✅ Done |
| Create angle-dependent test | [#19](https://github.com/JamesPagetButler/QBP/issues/19) | ✅ Done |

---

## Research & Theory Backlog

| Action | Task | Issue | Status |
|--------|------|-------|--------|
| E | Investigate quaternion scalar component (S³ vs S²) | [#20](https://github.com/JamesPagetButler/QBP/issues/20) | TODO |
| — | Document Lean 4 setup process | [#21](https://github.com/JamesPagetButler/QBP/issues/21) | TODO |

---

## Completed Tasks

| Task | PR/Issue | Date |
|------|----------|------|
| Initial Project Setup & Constitution | — | 2026-02-01 |
| Initial Red Team Review | PR #13 | 2026-02-01 |
| `qphysics.py` v0.1 (Axioms 1-3 + Measurement) | PR #13 | 2026-02-01 |
| Stern-Gerlach simulation v1 | PR #13 | 2026-02-01 |
| Ground Truth Research (all 9 experiments) | PR #15 | 2026-02-02 |
| CI/CD Pipeline | PR #8 | 2026-02-01 |

---

## Issue-Driven Workflow

```
1. Work identified → Create GitHub Issue
2. Issue assigned → Create feature branch
3. Work completed → Create PR referencing issue
4. Reviews posted → Update TODO.md, create new issues from feedback
5. PR merged → Issue auto-closed, TODO.md updated
```

All PRs should include `Closes #XX` or `Fixes #XX` in the description to auto-close issues on merge.
