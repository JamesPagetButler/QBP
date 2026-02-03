# QBP Project Plan & TODO

This document serves as the official project plan, tracking our high-level roadmap and the granular tasks required to achieve our goals.

**Workflow:** All work should be driven by GitHub Issues. PRs must reference the issue they address.

---

## Project Roadmap (The Nine Experiments)

This is our strategic guide. Each experiment has an associated issue for tracking.

| # | Experiment | Status | Issue | Priority |
|---|------------|--------|-------|----------|
| 1 | Stern-Gerlach | **Visualization** | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | High |
| 2 | Double-Slit | Next | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | High |
| 3 | Lamb Shift | Upcoming | [#30](https://github.com/JamesPagetButler/QBP/issues/30) | Medium |
| 4 | Bell's Theorem | Upcoming | [#23](https://github.com/JamesPagetButler/QBP/issues/23) | Medium |
| 5 | Particle Statistics | Upcoming | [#32](https://github.com/JamesPagetButler/QBP/issues/32) | Medium |
| 6 | Positronium Ground State | Upcoming | [#33](https://github.com/JamesPagetButler/QBP/issues/33) | Medium |
| 7 | Hydrogen Spectrum | Upcoming | [#34](https://github.com/JamesPagetButler/QBP/issues/34) | Medium |
| 8 | Anomalous g-2 | Aspirational | [#31](https://github.com/JamesPagetButler/QBP/issues/31) | Low |
| 9 | Gravity Tests | Aspirational | [#35](https://github.com/JamesPagetButler/QBP/issues/35) | Low |

---

## Current Sprint

### Active Work

| Task | Issue | Type | Status |
|------|-------|------|--------|
| Stern-Gerlach Manim animations | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | `type: experiment` | 🔄 Ready |
| Double-Slit theory & implementation | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | `type: experiment` | 📋 TODO |
| Quaternion scalar investigation | [#20](https://github.com/JamesPagetButler/QBP/issues/20) | `type: research` | 📋 TODO |

### Backlog

| Task | Issue | Type | Priority |
|------|-------|------|----------|
| Lean 4 setup documentation | [#21](https://github.com/JamesPagetButler/QBP/issues/21) | `type: docs` | Low |
| Initial premise review | [#6](https://github.com/JamesPagetButler/QBP/issues/6) | `type: research` | Triage |

---

## Research & Theory

| Topic | Issue | Status |
|-------|-------|--------|
| Quaternion scalar component (S³ vs S²) | [#20](https://github.com/JamesPagetButler/QBP/issues/20) | 📋 TODO |
| Lean 4 formal verification setup | [#21](https://github.com/JamesPagetButler/QBP/issues/21) | 📋 TODO |

---

## Infrastructure & Documentation

| Task | Issue | Status |
|------|-------|--------|
| Issue schema & templates | — | ✅ Done (2026-02-02) |
| CI/CD pipeline | [#7](https://github.com/JamesPagetButler/QBP/issues/7) | ✅ Done |
| Design system | [#3](https://github.com/JamesPagetButler/QBP/issues/3) | ✅ Done |
| Visualization framework | [#1](https://github.com/JamesPagetButler/QBP/issues/1) | ✅ Done |
| Research README | [#24](https://github.com/JamesPagetButler/QBP/issues/24) | ✅ Done |
| Black formatting automation | [#25](https://github.com/JamesPagetButler/QBP/issues/25) | ✅ Done |

---

## Completed Work

### Stern-Gerlach Refinements (PR #27, #28)

| Task | Issue | PR |
|------|-------|-----|
| Add `seed` parameter to `measure()` | [#16](https://github.com/JamesPagetButler/QBP/issues/16) | #27 |
| Add type hints to `qphysics.py` | [#17](https://github.com/JamesPagetButler/QBP/issues/17) | #27 |
| Vectorize simulation loop | [#18](https://github.com/JamesPagetButler/QBP/issues/18) | #27 |
| Create angle-dependent test | [#19](https://github.com/JamesPagetButler/QBP/issues/19) | #28 |

### Initial Setup (2026-02-01)

| Task | Issue | PR |
|------|-------|-----|
| Initial project constitution | — | — |
| `qphysics.py` v0.1 (Axioms 1-3 + Measurement) | — | #13 |
| Stern-Gerlach simulation v1 | — | #13 |
| Ground truth research (all 9 experiments) | — | #15 |

---

## Issue-Driven Workflow

```
1. Work identified → Create GitHub Issue (use templates)
2. Issue labeled → type:, priority:, status: labels applied
3. Issue assigned → Create feature branch
4. Work completed → Create PR with "Closes #XX"
5. Reviews posted → Red Team + Gemini approve
6. PR merged → Issue auto-closed, TODO.md updated
```

### Issue Templates

All new issues must use templates from `.github/ISSUE_TEMPLATE/`:
- `experiment.yml` — Physics experiments
- `feature.yml` — New features
- `bug.yml` — Bug reports
- `research.yml` — Theoretical investigations

See `docs/schemas/issue_schema.md` for full schema and best practices.

---

## Quick Reference: All Open Issues

| # | Title | Type | Priority |
|---|-------|------|----------|
| [#6](https://github.com/JamesPagetButler/QBP/issues/6) | Initial Project Premise & Setup Review | research | triage |
| [#20](https://github.com/JamesPagetButler/QBP/issues/20) | Quaternion scalar component investigation | research | medium |
| [#21](https://github.com/JamesPagetButler/QBP/issues/21) | Lean 4 setup documentation | docs | low |
| [#22](https://github.com/JamesPagetButler/QBP/issues/22) | Experiment 2: Double-Slit | experiment | high |
| [#23](https://github.com/JamesPagetButler/QBP/issues/23) | Experiment 5: Bell's Theorem | experiment | medium |
| [#29](https://github.com/JamesPagetButler/QBP/issues/29) | Experiment 1: Stern-Gerlach Visualization | experiment | high |
| [#30](https://github.com/JamesPagetButler/QBP/issues/30) | Experiment 3: Lamb Shift | experiment | medium |
| [#31](https://github.com/JamesPagetButler/QBP/issues/31) | Experiment 4: Anomalous g-2 | experiment | low |
| [#32](https://github.com/JamesPagetButler/QBP/issues/32) | Experiment 6: Particle Statistics | experiment | medium |
| [#33](https://github.com/JamesPagetButler/QBP/issues/33) | Experiment 7: Positronium Ground State | experiment | medium |
| [#34](https://github.com/JamesPagetButler/QBP/issues/34) | Experiment 8: Hydrogen Spectrum | experiment | medium |
| [#35](https://github.com/JamesPagetButler/QBP/issues/35) | Experiment 9: Gravity Tests | experiment | low |
