# QBP Project Plan & TODO

This document serves as the official project plan, tracking our high-level roadmap and the granular tasks required to achieve our goals.

**Workflow:** All work should be driven by GitHub Issues. PRs must reference the issue they address.

---

## 5-Phase Experimental Lifecycle

Each experiment follows a rigorous 5-phase workflow with decision gates and failure loops:

```
Phase 1: Ground Truth → Phase 2: Implementation → Phase 3: Visualization
                               ↑                         │
                               └─────[FAIL]──────────────┘
                               ↑
Phase 4: Proof ─────[FAIL]─────┘
    │
[PASS]↓
Phase 5: Publication
```

| Phase | Focus | Deliverables | Gate Criteria |
|-------|-------|--------------|---------------|
| **Phase 1: Ground Truth** | Establish target values from literature | Ground truth doc, success criteria, tool requirements | Red Team approved |
| **Phase 2: Implementation** | Build simulation/calculation | Working code, tests, validated results | Results within 3σ of ground truth |
| **Phase 3: Visualization** | Create comprehensible outputs | Manim videos, interactive demos, analysis | Red Team approved |
| **Phase 4: Formal Proof** | Mathematical verification in Lean 4 | Proof files, formal theorems | Compiles without `sorry` |
| **Phase 5: Publication** | Final documentation & release | Theory docs, videos, website | Ready for public |

### Decision Gates

- **Phase 1 → 2:** Ground truth document exists with quantitative targets
- **Phase 2 → 3:** Simulation results match ground truth within 3σ tolerance
- **Phase 3 → 4:** Visualizations approved, ready for formal verification
- **Phase 4 → 5:** Lean 4 proofs compile, core theorems verified

### Failure Loops

- **Phase 2 FAIL:** Debug implementation, return to Phase 2
- **Phase 3 FAIL:** Fix visualization issues, may require Phase 2 changes
- **Phase 4 FAIL:** Proof failure may indicate implementation or theory issues → return to Phase 2

---

## Project Roadmap (The Nine Experiments)

### Experiment 1: Stern-Gerlach

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#52](https://github.com/JamesPagetButler/QBP/issues/52) | ✅ Done |
| Phase 2: Implementation | [#53](https://github.com/JamesPagetButler/QBP/issues/53) | ✅ Done |
| Phase 3: Visualization | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | 🔄 Ready |
| Phase 4: Formal Proof | [#55](https://github.com/JamesPagetButler/QBP/issues/55) | ⏳ Blocked by #29 |
| Phase 5: Publication | [#64](https://github.com/JamesPagetButler/QBP/issues/64) | ⏳ Blocked by #55 |

### Experiment 2: Double-Slit

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | 📋 TODO |
| Phase 2: Implementation | [#36](https://github.com/JamesPagetButler/QBP/issues/36) | ⏳ Blocked by #22 |
| Phase 3: Visualization | [#37](https://github.com/JamesPagetButler/QBP/issues/37) | ⏳ Blocked by #36 |
| Phase 4: Formal Proof | [#56](https://github.com/JamesPagetButler/QBP/issues/56) | ⏳ Blocked by #37 |
| Phase 5: Publication | [#65](https://github.com/JamesPagetButler/QBP/issues/65) | ⏳ Blocked by #56 |

### Experiment 3: Lamb Shift

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#30](https://github.com/JamesPagetButler/QBP/issues/30) | 📋 TODO |
| Phase 2: Implementation | [#38](https://github.com/JamesPagetButler/QBP/issues/38) | ⏳ Blocked by #30 |
| Phase 3: Visualization | [#39](https://github.com/JamesPagetButler/QBP/issues/39) | ⏳ Blocked by #38 |
| Phase 4: Formal Proof | [#57](https://github.com/JamesPagetButler/QBP/issues/57) | ⏳ Blocked by #39 |
| Phase 5: Publication | [#66](https://github.com/JamesPagetButler/QBP/issues/66) | ⏳ Blocked by #57 |

### Experiment 4: Anomalous g-2

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#31](https://github.com/JamesPagetButler/QBP/issues/31) | 📋 TODO |
| Phase 2: Implementation | [#40](https://github.com/JamesPagetButler/QBP/issues/40) | ⏳ Blocked by #31 |
| Phase 3: Visualization | [#41](https://github.com/JamesPagetButler/QBP/issues/41) | ⏳ Blocked by #40 |
| Phase 4: Formal Proof | [#58](https://github.com/JamesPagetButler/QBP/issues/58) | ⏳ Blocked by #41 |
| Phase 5: Publication | [#67](https://github.com/JamesPagetButler/QBP/issues/67) | ⏳ Blocked by #58 |

### Experiment 5: Bell's Theorem

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#23](https://github.com/JamesPagetButler/QBP/issues/23) | 📋 TODO |
| Phase 2: Implementation | [#42](https://github.com/JamesPagetButler/QBP/issues/42) | ⏳ Blocked by #23 |
| Phase 3: Visualization | [#43](https://github.com/JamesPagetButler/QBP/issues/43) | ⏳ Blocked by #42 |
| Phase 4: Formal Proof | [#59](https://github.com/JamesPagetButler/QBP/issues/59) | ⏳ Blocked by #43 |
| Phase 5: Publication | [#68](https://github.com/JamesPagetButler/QBP/issues/68) | ⏳ Blocked by #59 |

### Experiment 6: Particle Statistics

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#32](https://github.com/JamesPagetButler/QBP/issues/32) | 📋 TODO |
| Phase 2: Implementation | [#44](https://github.com/JamesPagetButler/QBP/issues/44) | ⏳ Blocked by #32 |
| Phase 3: Visualization | [#45](https://github.com/JamesPagetButler/QBP/issues/45) | ⏳ Blocked by #44 |
| Phase 4: Formal Proof | [#60](https://github.com/JamesPagetButler/QBP/issues/60) | ⏳ Blocked by #45 |
| Phase 5: Publication | [#69](https://github.com/JamesPagetButler/QBP/issues/69) | ⏳ Blocked by #60 |

### Experiment 7: Positronium

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#33](https://github.com/JamesPagetButler/QBP/issues/33) | 📋 TODO |
| Phase 2: Implementation | [#46](https://github.com/JamesPagetButler/QBP/issues/46) | ⏳ Blocked by #33 |
| Phase 3: Visualization | [#47](https://github.com/JamesPagetButler/QBP/issues/47) | ⏳ Blocked by #46 |
| Phase 4: Formal Proof | [#61](https://github.com/JamesPagetButler/QBP/issues/61) | ⏳ Blocked by #47 |
| Phase 5: Publication | [#70](https://github.com/JamesPagetButler/QBP/issues/70) | ⏳ Blocked by #61 |

### Experiment 8: Hydrogen Spectrum

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#34](https://github.com/JamesPagetButler/QBP/issues/34) | 📋 TODO |
| Phase 2: Implementation | [#48](https://github.com/JamesPagetButler/QBP/issues/48) | ⏳ Blocked by #34 |
| Phase 3: Visualization | [#49](https://github.com/JamesPagetButler/QBP/issues/49) | ⏳ Blocked by #48 |
| Phase 4: Formal Proof | [#62](https://github.com/JamesPagetButler/QBP/issues/62) | ⏳ Blocked by #49 |
| Phase 5: Publication | [#71](https://github.com/JamesPagetButler/QBP/issues/71) | ⏳ Blocked by #62 |

### Experiment 9: Gravity Tests (Aspirational)

| Phase | Issue | Status |
|-------|-------|--------|
| Phase 1: Ground Truth | [#35](https://github.com/JamesPagetButler/QBP/issues/35) | 📋 TODO |
| Phase 2: Implementation | [#50](https://github.com/JamesPagetButler/QBP/issues/50) | ⏳ Blocked by #35 |
| Phase 3: Visualization | [#51](https://github.com/JamesPagetButler/QBP/issues/51) | ⏳ Blocked by #50 |
| Phase 4: Formal Proof | [#63](https://github.com/JamesPagetButler/QBP/issues/63) | ⏳ Blocked by #51 |
| Phase 5: Publication | [#72](https://github.com/JamesPagetButler/QBP/issues/72) | ⏳ Blocked by #63 |

---

## Current Sprint

### Active Work

| Task | Issue | Phase |
|------|-------|-------|
| Stern-Gerlach visualization | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | Phase 3 |
| Double-Slit ground truth | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | Phase 1 |

### Research Backlog

| Topic | Issue | Status |
|-------|-------|--------|
| Quaternion scalar component (S³ vs S²) | [#20](https://github.com/JamesPagetButler/QBP/issues/20) | 📋 TODO |
| Lean 4 setup documentation | [#21](https://github.com/JamesPagetButler/QBP/issues/21) | 📋 TODO |
| Initial premise review | [#6](https://github.com/JamesPagetButler/QBP/issues/6) | 📋 Triage |
| 5-Phase workflow proposal | [#54](https://github.com/JamesPagetButler/QBP/issues/54) | ✅ Implemented |

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
| 5-Phase workflow | [#54](https://github.com/JamesPagetButler/QBP/issues/54) | ✅ Done |

---

## Issue Summary

### All Experiment Issues (45 total)

| Exp | Phase 1: Ground Truth | Phase 2: Implementation | Phase 3: Visualization | Phase 4: Proof | Phase 5: Publication |
|-----|----------------------|------------------------|----------------------|----------------|---------------------|
| 1 | ✅ [#52](https://github.com/JamesPagetButler/QBP/issues/52) | ✅ [#53](https://github.com/JamesPagetButler/QBP/issues/53) | [#29](https://github.com/JamesPagetButler/QBP/issues/29) | [#55](https://github.com/JamesPagetButler/QBP/issues/55) | [#64](https://github.com/JamesPagetButler/QBP/issues/64) |
| 2 | [#22](https://github.com/JamesPagetButler/QBP/issues/22) | [#36](https://github.com/JamesPagetButler/QBP/issues/36) | [#37](https://github.com/JamesPagetButler/QBP/issues/37) | [#56](https://github.com/JamesPagetButler/QBP/issues/56) | [#65](https://github.com/JamesPagetButler/QBP/issues/65) |
| 3 | [#30](https://github.com/JamesPagetButler/QBP/issues/30) | [#38](https://github.com/JamesPagetButler/QBP/issues/38) | [#39](https://github.com/JamesPagetButler/QBP/issues/39) | [#57](https://github.com/JamesPagetButler/QBP/issues/57) | [#66](https://github.com/JamesPagetButler/QBP/issues/66) |
| 4 | [#31](https://github.com/JamesPagetButler/QBP/issues/31) | [#40](https://github.com/JamesPagetButler/QBP/issues/40) | [#41](https://github.com/JamesPagetButler/QBP/issues/41) | [#58](https://github.com/JamesPagetButler/QBP/issues/58) | [#67](https://github.com/JamesPagetButler/QBP/issues/67) |
| 5 | [#23](https://github.com/JamesPagetButler/QBP/issues/23) | [#42](https://github.com/JamesPagetButler/QBP/issues/42) | [#43](https://github.com/JamesPagetButler/QBP/issues/43) | [#59](https://github.com/JamesPagetButler/QBP/issues/59) | [#68](https://github.com/JamesPagetButler/QBP/issues/68) |
| 6 | [#32](https://github.com/JamesPagetButler/QBP/issues/32) | [#44](https://github.com/JamesPagetButler/QBP/issues/44) | [#45](https://github.com/JamesPagetButler/QBP/issues/45) | [#60](https://github.com/JamesPagetButler/QBP/issues/60) | [#69](https://github.com/JamesPagetButler/QBP/issues/69) |
| 7 | [#33](https://github.com/JamesPagetButler/QBP/issues/33) | [#46](https://github.com/JamesPagetButler/QBP/issues/46) | [#47](https://github.com/JamesPagetButler/QBP/issues/47) | [#61](https://github.com/JamesPagetButler/QBP/issues/61) | [#70](https://github.com/JamesPagetButler/QBP/issues/70) |
| 8 | [#34](https://github.com/JamesPagetButler/QBP/issues/34) | [#48](https://github.com/JamesPagetButler/QBP/issues/48) | [#49](https://github.com/JamesPagetButler/QBP/issues/49) | [#62](https://github.com/JamesPagetButler/QBP/issues/62) | [#71](https://github.com/JamesPagetButler/QBP/issues/71) |
| 9 | [#35](https://github.com/JamesPagetButler/QBP/issues/35) | [#50](https://github.com/JamesPagetButler/QBP/issues/50) | [#51](https://github.com/JamesPagetButler/QBP/issues/51) | [#63](https://github.com/JamesPagetButler/QBP/issues/63) | [#72](https://github.com/JamesPagetButler/QBP/issues/72) |

### Research & Other Issues

| # | Title | Type |
|---|-------|------|
| [#6](https://github.com/JamesPagetButler/QBP/issues/6) | Initial Project Premise Review | research |
| [#20](https://github.com/JamesPagetButler/QBP/issues/20) | Quaternion scalar component | research |
| [#21](https://github.com/JamesPagetButler/QBP/issues/21) | Lean 4 setup | docs |
| [#54](https://github.com/JamesPagetButler/QBP/issues/54) | 5-Phase Workflow Proposal | research |

---

## Phase Labels

Issues are tagged with phase labels for filtering:

| Label | Description |
|-------|-------------|
| `phase: ground-truth` | Phase 1: Ground truth and planning |
| `phase: implementation` | Phase 2: Implementation and execution |
| `phase: visualization` | Phase 3: Visualization and analysis |
| `phase: proof` | Phase 4: Formal proof in Lean 4 |
| `phase: publication` | Phase 5: Publication and documentation |

---

## Workflow

```
Phase 1: Ground Truth
    ↓ [Gate: Ground truth doc with quantitative targets]
Phase 2: Implementation
    ↓ [Gate: Results within 3σ of ground truth]
    ↑ [FAIL: Debug loop back to Phase 2]
Phase 3: Visualization
    ↓ [Gate: Red Team approved visualizations]
    ↑ [FAIL: May loop back to Phase 2]
Phase 4: Formal Proof
    ↓ [Gate: Lean 4 compiles, no sorry]
    ↑ [FAIL: May indicate theory/implementation issues → Phase 2]
Phase 5: Publication
    ↓ [Gate: Final Red Team review]
    ✓ Public Release
```

All PRs should include `Closes #XX` in the description to auto-close issues on merge.

See `CONTRIBUTING.md` for detailed workflow documentation.
See `docs/schemas/issue_schema.md` for issue templates and best practices.
