# QBP Project Plan & TODO

This document serves as the official project plan, tracking our high-level roadmap and the granular tasks required to achieve our goals.

**Workflow:** All work should be driven by GitHub Issues. PRs must reference the issue they address.

---

## Experiment Phases

Each experiment follows a 3-phase workflow:

| Phase | Focus | Deliverables |
|-------|-------|--------------|
| **Phase 1: Refine** | Theory, planning, tool building | Research docs, design decisions, required tooling |
| **Phase 2: Execute** | Run simulation/calculation | Working code, tests, validated results |
| **Phase 3: Visualize** | Publication-ready outputs | Manim videos, interactive demos, documentation |

---

## Project Roadmap (The Nine Experiments)

### Experiment 1: Stern-Gerlach

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | ✅ Completed (#16-19) | Done |
| Phase 2: Execute | ✅ Completed (PR #13, #27, #28) | Done |
| Phase 3: Visualize | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | 🔄 Ready |

### Experiment 2: Double-Slit

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | 📋 TODO |
| Phase 2: Execute | [#36](https://github.com/JamesPagetButler/QBP/issues/36) | ⏳ Blocked by #22 |
| Phase 3: Visualize | [#37](https://github.com/JamesPagetButler/QBP/issues/37) | ⏳ Blocked by #36 |

### Experiment 3: Lamb Shift

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#30](https://github.com/JamesPagetButler/QBP/issues/30) | 📋 TODO |
| Phase 2: Execute | [#38](https://github.com/JamesPagetButler/QBP/issues/38) | ⏳ Blocked by #30 |
| Phase 3: Visualize | [#39](https://github.com/JamesPagetButler/QBP/issues/39) | ⏳ Blocked by #38 |

### Experiment 4: Anomalous g-2

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#31](https://github.com/JamesPagetButler/QBP/issues/31) | 📋 TODO |
| Phase 2: Execute | [#40](https://github.com/JamesPagetButler/QBP/issues/40) | ⏳ Blocked by #31 |
| Phase 3: Visualize | [#41](https://github.com/JamesPagetButler/QBP/issues/41) | ⏳ Blocked by #40 |

### Experiment 5: Bell's Theorem

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#23](https://github.com/JamesPagetButler/QBP/issues/23) | 📋 TODO |
| Phase 2: Execute | [#42](https://github.com/JamesPagetButler/QBP/issues/42) | ⏳ Blocked by #23 |
| Phase 3: Visualize | [#43](https://github.com/JamesPagetButler/QBP/issues/43) | ⏳ Blocked by #42 |

### Experiment 6: Particle Statistics

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#32](https://github.com/JamesPagetButler/QBP/issues/32) | 📋 TODO |
| Phase 2: Execute | [#44](https://github.com/JamesPagetButler/QBP/issues/44) | ⏳ Blocked by #32 |
| Phase 3: Visualize | [#45](https://github.com/JamesPagetButler/QBP/issues/45) | ⏳ Blocked by #44 |

### Experiment 7: Positronium

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#33](https://github.com/JamesPagetButler/QBP/issues/33) | 📋 TODO |
| Phase 2: Execute | [#46](https://github.com/JamesPagetButler/QBP/issues/46) | ⏳ Blocked by #33 |
| Phase 3: Visualize | [#47](https://github.com/JamesPagetButler/QBP/issues/47) | ⏳ Blocked by #46 |

### Experiment 8: Hydrogen Spectrum

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#34](https://github.com/JamesPagetButler/QBP/issues/34) | 📋 TODO |
| Phase 2: Execute | [#48](https://github.com/JamesPagetButler/QBP/issues/48) | ⏳ Blocked by #34 |
| Phase 3: Visualize | [#49](https://github.com/JamesPagetButler/QBP/issues/49) | ⏳ Blocked by #48 |

### Experiment 9: Gravity Tests (Aspirational)

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Refine | [#35](https://github.com/JamesPagetButler/QBP/issues/35) | 📋 TODO |
| Phase 2: Execute | [#50](https://github.com/JamesPagetButler/QBP/issues/50) | ⏳ Blocked by #35 |
| Phase 3: Visualize | [#51](https://github.com/JamesPagetButler/QBP/issues/51) | ⏳ Blocked by #50 |

---

## Current Sprint

### Active Work

| Task | Issue | Phase |
|------|-------|-------|
| Stern-Gerlach visualization | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | Phase 3 |
| Double-Slit theory & planning | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | Phase 1 |

### Research Backlog

| Topic | Issue | Status |
|-------|-------|--------|
| Quaternion scalar component (S³ vs S²) | [#20](https://github.com/JamesPagetButler/QBP/issues/20) | 📋 TODO |
| Lean 4 setup documentation | [#21](https://github.com/JamesPagetButler/QBP/issues/21) | 📋 TODO |
| Initial premise review | [#6](https://github.com/JamesPagetButler/QBP/issues/6) | 📋 Triage |

---

## Infrastructure & Documentation (Completed)

| Task | Issue | Status |
|------|-------|--------|
| Issue schema & templates | — | ✅ Done |
| CI/CD pipeline | [#7](https://github.com/JamesPagetButler/QBP/issues/7) | ✅ Done |
| Design system | [#3](https://github.com/JamesPagetButler/QBP/issues/3) | ✅ Done |
| Visualization framework | [#1](https://github.com/JamesPagetButler/QBP/issues/1) | ✅ Done |
| Manim infrastructure | — | ✅ Done |
| Publication pipeline schema | — | ✅ Done |

---

## Issue Summary

### All Experiment Issues (27 total)

| Exp | Phase 1: Refine | Phase 2: Execute | Phase 3: Visualize |
|-----|-----------------|------------------|-------------------|
| 1 | ✅ Done | ✅ Done | [#29](https://github.com/JamesPagetButler/QBP/issues/29) |
| 2 | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | [#36](https://github.com/JamesPagetButler/QBP/issues/36) | [#37](https://github.com/JamesPagetButler/QBP/issues/37) |
| 3 | [#30](https://github.com/JamesPagetButler/QBP/issues/30) | [#38](https://github.com/JamesPagetButler/QBP/issues/38) | [#39](https://github.com/JamesPagetButler/QBP/issues/39) |
| 4 | [#31](https://github.com/JamesPagetButler/QBP/issues/31) | [#40](https://github.com/JamesPagetButler/QBP/issues/40) | [#41](https://github.com/JamesPagetButler/QBP/issues/41) |
| 5 | [#23](https://github.com/JamesPagetButler/QBP/issues/23) | [#42](https://github.com/JamesPagetButler/QBP/issues/42) | [#43](https://github.com/JamesPagetButler/QBP/issues/43) |
| 6 | [#32](https://github.com/JamesPagetButler/QBP/issues/32) | [#44](https://github.com/JamesPagetButler/QBP/issues/44) | [#45](https://github.com/JamesPagetButler/QBP/issues/45) |
| 7 | [#33](https://github.com/JamesPagetButler/QBP/issues/33) | [#46](https://github.com/JamesPagetButler/QBP/issues/46) | [#47](https://github.com/JamesPagetButler/QBP/issues/47) |
| 8 | [#34](https://github.com/JamesPagetButler/QBP/issues/34) | [#48](https://github.com/JamesPagetButler/QBP/issues/48) | [#49](https://github.com/JamesPagetButler/QBP/issues/49) |
| 9 | [#35](https://github.com/JamesPagetButler/QBP/issues/35) | [#50](https://github.com/JamesPagetButler/QBP/issues/50) | [#51](https://github.com/JamesPagetButler/QBP/issues/51) |

### Research & Other Issues

| # | Title | Type |
|---|-------|------|
| [#6](https://github.com/JamesPagetButler/QBP/issues/6) | Initial Project Premise Review | research |
| [#20](https://github.com/JamesPagetButler/QBP/issues/20) | Quaternion scalar component | research |
| [#21](https://github.com/JamesPagetButler/QBP/issues/21) | Lean 4 setup | docs |

---

## Workflow

```
Phase 1: Refine & Plan
    ↓ (blocked until complete)
Phase 2: Execute
    ↓ (blocked until complete)
Phase 3: Visualize & Publish
```

All PRs should include `Closes #XX` in the description to auto-close issues on merge.

See `docs/schemas/issue_schema.md` for issue templates and best practices.
