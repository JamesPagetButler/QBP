# QBP Operational Modes: Focus, Sprint & Project

*This document defines the three operational modes for QBP development and how they enable an antifragile, iterative research process with progressive autonomy.*

---

## Rollout Strategy

Modes are enabled progressively as process validation occurs:

| Phase | Mode | Autonomy | Status |
|-------|------|----------|--------|
| 1 | **Focus Mode** | Human controls each step | **CURRENT** |
| 2 | **Sprint Mode** | Claude runs full sprint, human reviews | Planned |
| 3 | **Project Mode** | Claude proposes portfolio changes, human approves | Planned |

**Principle:** Validate process works under human control before increasing autonomy.

---

## The Three Modes

### Focus Mode (Current)
**Focus:** Human-directed work with AI assistance.

```
┌─────────────────────────────────────────────────────────┐
│  FOCUS MODE                                             │
│                                                         │
│  Human: "Do Phase 2 for Experiment 01b"                 │
│            ↓                                            │
│  Claude: Executes Phase 2, requests review              │
│            ↓                                            │
│  Human: Reviews, approves/requests changes              │
│            ↓                                            │
│  Human: "Now do Phase 3"                                │
│            ↓                                            │
│         ... and so on ...                               │
└─────────────────────────────────────────────────────────┘
```

**Characteristics:**
- Human explicitly requests each phase/task
- Claude executes and reports back
- Human reviews before proceeding
- PR review workflow enforced
- Maximum control, validates process correctness

**Purpose:** Establish that the process works correctly before automating.

---

### Sprint Mode (Planned)
**Focus:** Claude autonomously completes one experiment through all phases.

```
┌─────────────────────────────────────────────────────────┐
│  SPRINT MODE                                            │
│                                                         │
│  Human: "Run Sprint N for Experiment X"                 │
│            ↓                                            │
│  Claude: Executes all phases autonomously               │
│    Phase 1 → 2 → 3 → 4a → 4b → 4c → 4d → 4e → 5        │
│            ↓                                            │
│  Claude: Theory Refinement analysis                     │
│            ↓                                            │
│  Claude: "Sprint complete. Summary: [...]               │
│           Recommendation: Continue / Project Mode"      │
│            ↓                                            │
│  Human: Reviews sprint output, approves/rejects         │
│            ↓                                            │
│  Human: "Continue to next sprint" or "Enter Project"    │
└─────────────────────────────────────────────────────────┘
```

**Characteristics:**
- Claude runs full sprint without step-by-step approval
- Human reviews at sprint boundaries (not phase boundaries)
- PR workflow still applies (Claude creates, human merges)
- Herschel self-enforces critical path
- Time-boxed execution (target: 1-2 weeks)

**Entry criteria:**
- Focus Mode has validated the process for this experiment type
- Experiment is defined and scoped
- Human explicitly enables Sprint Mode

**Exit criteria:**
- All phases complete (1-5 + 4a-e)
- Theory Refinement documented
- Human reviews and approves sprint output
- Decision gate: human decides next action

---

### Project Mode (Planned)
**Focus:** Claude analyzes portfolio and proposes changes; human approves.

```
┌─────────────────────────────────────────────────────────┐
│  PROJECT MODE                                           │
│                                                         │
│  Human: "Enter Project Mode" or triggered by sprint     │
│            ↓                                            │
│  ┌─────────────────────────────────────────────────┐    │
│  │ Claude: Portfolio Analysis                      │    │
│  │  • Which experiments are complete?              │    │
│  │  • Which need rework due to theory changes?     │    │
│  │  • What gaps exist?                             │    │
│  │  • What's redundant?                            │    │
│  └─────────────────────────────────────────────────┘    │
│                          ↓                              │
│  ┌─────────────────────────────────────────────────┐    │
│  │ Claude: Proposes Changes                        │    │
│  │  • ADD experiments (with rationale)             │    │
│  │  • REMOVE experiments (with rationale)          │    │
│  │  • REORDER priority (with rationale)            │    │
│  │  • REWORK scope (list affected experiments)     │    │
│  │  • Axiom updates (if needed)                    │    │
│  └─────────────────────────────────────────────────┘    │
│                          ↓                              │
│  ┌─────────────────────────────────────────────────┐    │
│  │ Human: Reviews & Decides                        │    │
│  │  • Approve / Modify / Reject each proposal      │    │
│  │  • Add additional changes                       │    │
│  │  • Set priorities                               │    │
│  └─────────────────────────────────────────────────┘    │
│                          ↓                              │
│  ┌─────────────────────────────────────────────────┐    │
│  │ Claude: Executes Approved Changes               │    │
│  │  • Create/close issues                          │    │
│  │  • Update knowledge graph                       │    │
│  │  • Update SPRINT_STATUS.md                      │    │
│  │  • Prepare next sprint                          │    │
│  └─────────────────────────────────────────────────┘    │
│                          ↓                              │
│                  Return to Sprint Mode                  │
└─────────────────────────────────────────────────────────┘
```

**Characteristics:**
- Claude analyzes and proposes; human decides
- Whole-portfolio perspective
- Can modify experiment set (with approval)
- Can update foundational axioms (with approval)
- Enables faster iterations than Focus Mode
- Human retains strategic control

**Entry triggers:**
- Human explicitly enters Project Mode
- Sprint Mode recommends Project Mode (human approves)
- Scheduled milestone (e.g., after every 3 sprints)

**Exit criteria:**
- Human approves portfolio decisions
- Changes executed and documented
- Next sprint selected
- Human approves return to Sprint Mode

---

## The Iterative Cycle

```
                    ┌──────────────┐
                    │ Project Mode │
                    │  (evaluate)  │
                    └──────┬───────┘
                           │
              ┌────────────┼────────────┐
              ↓            ↓            ↓
         ┌────────┐   ┌────────┐   ┌────────┐
         │Sprint 1│   │Sprint 2│   │Sprint N│
         └────┬───┘   └────┬───┘   └────┬───┘
              │            │            │
              ↓            ↓            ↓
         Theory Ref   Theory Ref   Theory Ref
              │            │            │
              └────────────┴────────────┘
                           │
                    Decision Gate:
                    Continue or Project Mode?
                           │
              ┌────────────┴────────────┐
              ↓                         ↓
         Continue to              Enter Project Mode
         next Sprint              (rework/add/remove)
```

**Key principle:** Theory Refinement is the checkpoint where we decide whether to continue linearly or step back to Project Mode.

---

## Antifragile Properties

The process is **antifragile** because disruptions make it stronger:

| Disruption | Fragile Response | Antifragile Response |
|------------|------------------|---------------------|
| Axiom found to be wrong | Project fails | Enter Project Mode, fix axiom, rework affected experiments, theory is now stronger |
| Experiment reveals gap | Ignore it, continue plan | Add new experiment to address gap |
| Two experiments redundant | Waste time on both | Remove one, reallocate effort |
| External physics discovery | Threatens project | Add experiment to compare, opportunity to validate/extend |
| V&V reveals setup error | Trust broken | Fix error, strengthen V&V process, more confidence going forward |

**The goal:** Each iteration through the cycle produces a more robust, more complete, more trustworthy theory.

---

## Mode Transitions

### Sprint → Project Mode

**Triggers:**
1. Theory Refinement reveals axiom change needed
2. V&V fails in a way that affects multiple experiments
3. James decides portfolio review is needed
4. Scheduled milestone reached

**Process:**
1. Complete current sprint phase (don't stop mid-phase)
2. Document trigger reason in SPRINT_STATUS.md
3. Enter Project Mode with clear scope
4. Complete Project Mode tasks before returning

### Project → Sprint Mode

**Requirements:**
1. Portfolio decisions documented
2. Next experiment selected
3. Rework scope defined (if any)
4. Dependencies clear
5. SPRINT_STATUS.md updated

**Process:**
1. Create/update issues for selected sprint
2. Run Herschel Check
3. Begin Phase 1 of selected experiment

---

## SPRINT_STATUS.md Updates

The status file must always reflect current mode:

```markdown
## Current Position

- **Operational Mode:** Sprint Mode | Project Mode
- **Active Sprint:** Sprint N (Experiment X) | N/A (Project Mode)
- **Mode Entry Date:** YYYY-MM-DD
- **Mode Entry Reason:** [why we're in this mode]
```

---

## Decision Framework

### When to stay in Sprint Mode
- Current experiment is progressing normally
- Theory Refinement reveals only local adjustments
- No cross-experiment dependencies discovered

### When to enter Project Mode
- Axiom change affects 2+ experiments
- New experiment needed that blocks current work
- Redundancy discovered between experiments
- Strategic reassessment requested
- 3+ sprints completed without portfolio review

---

## Herschel's Role in Each Mode

### Sprint Mode
- Enforce critical path discipline
- Minimize diversions
- Track phase completion
- Flag when Theory Refinement suggests Project Mode

### Project Mode
- Ensure all decisions are documented
- Track rework scope
- Verify portfolio changes are reflected in issues
- Confirm exit criteria before returning to Sprint Mode

---

## Summary

| Aspect | Focus Mode | Sprint Mode | Project Mode |
|--------|------------|-------------|--------------|
| **Status** | **CURRENT** | Planned | Planned |
| **Focus** | One phase at a time | One full sprint | Whole portfolio |
| **Human role** | Directs each step | Reviews at boundaries | Approves proposals |
| **Claude role** | Executes on request | Runs autonomously | Analyzes & proposes |
| **Duration** | Variable | 1-2 weeks | As needed |
| **Axiom changes** | Human decides | Flag for Project | Propose to human |
| **Experiment changes** | Human decides | Not allowed | Propose to human |

---

## Progressive Autonomy

```
Focus Mode                Sprint Mode               Project Mode
(validate process)   →    (validate autonomy)   →   (enable scale)
     │                         │                         │
Human controls each      Human reviews at          Human approves
phase; Claude executes   sprint boundaries;        portfolio changes;
                         Claude runs full sprint   Claude proposes & executes
```

**Progression criteria:**

| Transition | Requirement |
|------------|-------------|
| Focus → Sprint | Process validated for experiment type; human enables Sprint Mode |
| Sprint → Project | Sprint Mode validated across multiple experiments; human enables Project Mode |

**Fallback:** If issues arise in higher-autonomy modes, drop back to Focus Mode to diagnose and fix.

---

**The antifragile principle:** We don't fear discovering that changes are needed — we have a process to handle them that makes the theory stronger each time. Progressive autonomy ensures we validate each level before scaling up.
