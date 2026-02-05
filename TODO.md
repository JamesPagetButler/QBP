# QBP Project Plan

This document serves as the official project plan, tracking our high-level roadmap and the status of each experiment through our 5-phase lifecycle.

**Workflow:** All work should be driven by GitHub Issues. PRs must reference the issue they address.

---

## 5-Phase Experimental Lifecycle

Each experiment follows a rigorous 5-phase workflow with decision gates and failure loops:

```
Phase 1: Ground Truth → Phase 2: Implementation → Phase 3: Visualization
↑ │
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
| **Phase 4: Formal Verification** | Prove (4a), review (4b), visualize (4c) | `.lean` proofs, review report, WASM viz | 4a+4b gate publication; 4c parallel deliverable |
| **Phase 5: Publication** | Final documentation & release | Theory docs, videos, website | Ready for public |

### Decision Gates

- **Phase 1 → 2:** Ground truth document exists with quantitative targets
- **Phase 2 → 3:** Simulation results match ground truth within 3σ tolerance
- **Phase 3 → 4:** Visualizations approved, ready for formal verification
- **Phase 4 → 5:** Lean 4 proofs compile (4a) AND proof review approved (4b). Phase 4c (interactive visualization) runs in parallel with Phase 5 — not a gate.

### Failure Loops

- **Phase 2 FAIL:** Debug implementation, return to Phase 2
- **Phase 3 FAIL:** Fix visualization issues, may require Phase 2 changes
- **Phase 4 FAIL:** Proof failure may indicate implementation or theory issues → return to Phase 2

---

## Project Roadmap (The Nine Experiments)

Our work is organized into sprints, with each sprint corresponding to one experiment on our roadmap. A sprint is complete only when all 5 phases for that experiment are complete and merged.

### Experiment 1: Stern-Gerlach
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#52](https://github.com/JamesPagetButler/QBP/issues/52))
-   ✅ **[Done]** Phase 2: Implementation & Execution ([#53](https://github.com/JamesPagetButler/QBP/issues/53))
-   ✅ **[Done]** Phase 3: Visualization & Analysis ([#29](https://github.com/JamesPagetButler/QBP/issues/29))
-   📋 **[TODO]** Phase 4: Formal Verification ([#55](https://github.com/JamesPagetButler/QBP/issues/55))
-   📋 **[TODO]** Phase 5: Publication ([#64](https://github.com/JamesPagetButler/QBP/issues/64))

### Experiment 2: Double-Slit
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#22](https://github.com/JamesPagetButler/QBP/issues/22))
-   📋 **[TODO]** Phase 2: Implementation & Execution ([#36](https://github.com/JamesPagetButler/QBP/issues/36))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#37](https://github.com/JamesPagetButler/QBP/issues/37))
-   📋 **[TODO]** Phase 4: Formal Verification ([#56](https://github.com/JamesPagetButler/QBP/issues/56))
-   📋 **[TODO]** Phase 5: Publication ([#65](https://github.com/JamesPagetButler/QBP/issues/65))

### Experiment 3: Lamb Shift
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#30](https://github.com/JamesPagetButler/QBP/issues/30))
-   📋 **[TODO]** Phase 2: Implementation & Execution ([#38](https://github.com/JamesPagetButler/QBP/issues/38))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#39](https://github.com/JamesPagetButler/QBP/issues/39))
-   📋 **[TODO]** Phase 4: Formal Verification ([#57](https://github.com/JamesPagetButler/QBP/issues/57))
-   📋 **[TODO]** Phase 5: Publication ([#66](https://github.com/JamesPagetButler/QBP/issues/66))

### Experiment 4: Anomalous g-2
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#31](https://github.com/JamesPagetButler/QBP/issues/31))
-   📋 **[TODO]** Phase 2: Implementation & Execution ([#40](https://github.com/JamesPagetButler/QBP/issues/40))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#41](https://github.com/JamesPagetButler/QBP/issues/41))
-   📋 **[TODO]** Phase 4: Formal Verification ([#58](https://github.com/JamesPagetButler/QBP/issues/58))
-   📋 **[TODO]** Phase 5: Publication ([#67](https://github.com/JamesPagetButler/QBP/issues/67))

### Experiment 5: Bell's Theorem
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#23](https://github.com/JamesPagetButler/QBP/issues/23))
-   📋 **[TODO]** Phase 2: Implementation & Execution ([#42](https://github.com/JamesPagetButler/QBP/issues/42))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#43](https://github.com/JamesPagetButler/QBP/issues/43))
-   📋 **[TODO]** Phase 4: Formal Verification ([#59](https://github.com/JamesPagetButler/QBP/issues/59))
-   📋 **[TODO]** Phase 5: Publication ([#68](https://github.com/JamesPagetButler/QBP/issues/68))

### Experiment 6: Particle Statistics
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#32](https://github.com/JamesPagetButler/QBP/issues/32))
-   📋 **[TODO]** Phase 2: Implementation & Execution (Theoretical Derivation) ([#44](https://github.com/JamesPagetButler/QBP/issues/44))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#45](https://github.com/JamesPagetButler/QBP/issues/45))
-   📋 **[TODO]** Phase 4: Formal Verification ([#60](https://github.com/JamesPagetButler/QBP/issues/60))
-   📋 **[TODO]** Phase 5: Publication ([#69](https://github.com/JamesPagetButler/QBP/issues/69))

### Experiment 7: Positronium
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#33](https://github.com/JamesPagetButler/QBP/issues/33))
-   📋 **[TODO]** Phase 2: Implementation & Execution ([#46](https://github.com/JamesPagetButler/QBP/issues/46))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#47](https://github.com/JamesPagetButler/QBP/issues/47))
-   📋 **[TODO]** Phase 4: Formal Verification ([#61](https://github.com/JamesPagetButler/QBP/issues/61))
-   📋 **[TODO]** Phase 5: Publication ([#70](https://github.com/JamesPagetButler/QBP/issues/70))

### Experiment 8: Hydrogen Spectrum
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#34](https://github.com/JamesPagetButler/QBP/issues/34))
-   📋 **[TODO]** Phase 2: Implementation & Execution ([#48](https://github.com/JamesPagetButler/QBP/issues/48))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#49](https://github.com/JamesPagetButler/QBP/issues/49))
-   📋 **[TODO]** Phase 4: Formal Verification ([#62](https://github.com/JamesPagetButler/QBP/issues/62))
-   📋 **[TODO]** Phase 5: Publication ([#71](https://github.com/JamesPagetButler/QBP/issues/71))

### Experiment 9: Gravity Tests (Aspirational)
-   ✅ **[Done]** Phase 1: Ground Truth & Planning ([#35](https://github.com/JamesPagetButler/QBP/issues/35))
-   📋 **[TODO]** Phase 2: Implementation & Execution ([#50](https://github.com/JamesPagetButler/QBP/issues/50))
-   📋 **[TODO]** Phase 3: Visualization & Analysis ([#51](https://github.com/JamesPagetButler/QBP/issues/51))
-   📋 **[TODO]** Phase 4: Formal Verification ([#63](https://github.com/JamesPagetButler/QBP/issues/63))
-   📋 **[TODO]** Phase 5: Publication ([#72](https://github.com/JamesPagetButler/QBP/issues/72))

---

## Issue Summary

### Research & Other Issues

| # | Title | Type | Status |
|---|-------|------|--------|
| [#6](https://github.com/JamesPagetButler/QBP/issues/6) | Initial Project Premise Review | research | 📋 Triage |
| [#20](https://github.com/JamesPagetButler/QBP/issues/20) | Quaternion scalar component (S³ vs S²) | research | 📋 TODO |
| [#21](https://github.com/JamesPagetButler/QBP/issues/21) | Lean 4 setup documentation | docs | ✅ Done |
| [#54](https://github.com/JamesPagetButler/QBP/issues/54) | 5-Phase Workflow Proposal | research | ✅ Implemented |

---

## Completed Infrastructure & Documentation

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

*Note: The detailed project workflow, including the 5-phase lifecycle definitions, is documented in `CONTRIBUTING.md`.*
