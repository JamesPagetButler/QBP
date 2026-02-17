# Parallel Sub-Agent Workflow

*Execution model for Sprint 3+ leveraging Claude Opus 4.6's sub-agent tooling for concurrent task execution.*

---

## Overview

Instead of serial role-play through Dev Team personas, we use **parallel sub-agents** for concurrent execution with a **shared contract** for consistency. This enables:

- Faster wall-clock time for multi-file changes
- Independent failure isolation (one agent's error doesn't block others)
- Natural separation of concerns (physics code vs. viz vs. tests)

---

## Five-Phase Execution

### Phase 1: Explore (Parallel)

Multiple Explore agents scan the codebase simultaneously. Each agent targets a specific concern:

| Agent | Focus | Output |
|-------|-------|--------|
| Physics Explorer | Existing simulation code, constants, conventions | File list + API inventory |
| Test Explorer | Test patterns, fixtures, assertion styles | Test contract |
| Viz Explorer | Plotting conventions, color schemes, layout patterns | Visual contract |

**Gemini Integration:** Theory Team (Furey, Feynman) validates physics interpretations in parallel with Explore agents.

### Phase 2: Contract (Serial)

Define the shared interface before any implementation begins. This is the critical coordination step.

**Contract includes:**
- Column names and units for CSVs
- Color palette and plot style (matplotlib rcParams)
- Tolerance values for numerical assertions
- Shared constants (imported from `si_conversion.py`)
- File naming conventions

**Format:** A brief Markdown document or code comment block that all Build agents reference.

**Why serial:** The contract must be finalized before Build begins. Parallel contract-writing leads to contradictions.

### Phase 3: Build (Parallel)

Independent GP agents write separate files concurrently. Each agent receives the contract from Phase 2.

| Agent | Responsibility | Output Files |
|-------|---------------|--------------|
| Simulation Agent | Physics code, numerical engine | `experiments/NN_*/simulate.py` |
| Test Agent | Unit and physics tests | `tests/physics/test_*.py` |
| Analysis Agent | Data loading, metrics, plotting | `analysis/NN_*/analyze.py` |

**Rules:**
- Agents must not modify files outside their responsibility
- All agents import shared constants from the contract
- No agent reads another agent's output until Phase 4

### Phase 4: Run (Serial)

Execute scripts and validate outputs:

1. Run simulation: `python experiments/NN_*/simulate.py`
2. Run tests: `pytest tests/physics/test_*.py -v`
3. Run analysis: `python analysis/NN_*/analyze.py`
4. Validate outputs match contract expectations

**If failures:** Fix in the responsible agent's scope, re-run.

### Phase 5: Review (Serial)

Apply persona design principles as quality checks:

| Persona | Review Focus |
|---------|-------------|
| Sabine | Statistical rigor, methodology, error bars |
| Grothendieck | Mathematical correctness, proof structure |
| Knuth | Algorithm efficiency, code quality |
| Tufte | Visualization clarity, data-ink ratio |
| Bret Victor | Interactivity, explorable explanations |

**Gemini Integration:** Theory Team reviews generated analysis before PR creation.

---

## When to Use

| Scenario | Use Parallel? | Rationale |
|----------|--------------|-----------|
| New experiment phase (3+ files) | Yes | Natural file separation enables parallelism |
| Single-file bug fix | No | Overhead exceeds benefit |
| Phase 2 rework (schema change) | Yes | Simulation + tests + analysis change independently |
| Documentation-only | No | Serial is simpler |
| Formal proof work | Maybe | Lean files may have dependencies |

---

## Measuring Effectiveness

After each use, log the following as an issue comment on #317:

1. **Phase used for:** (e.g., Sprint 3 Phase 3 Visualization)
2. **Wall-clock time:** Start to PR creation
3. **Agent count:** How many parallel agents ran
4. **Contract violations:** Did any agent break the shared contract?
5. **Rework needed:** How many Phase 4 failures required fixing?
6. **Comparison estimate:** Rough estimate of serial time for the same task

---

## Open Questions (To Resolve During Sprint 3)

1. Does the Contract Phase actually prevent inconsistencies, or is it overhead?
2. What's the real wall-clock speedup vs serial?
3. Where does Gemini fit best — Phase 1 only, or also Phase 3 (Build)?
4. Should we formalize which persona principles map to which phase?
5. Is the 5-phase model the right granularity, or should we collapse Explore+Contract?

---

## References

- [Issue #317](https://github.com/JamesPagetButler/QBP/issues/317) — Tracking issue
- [Sprint Mode Workflow](sprint_mode_workflow.md) — Sprint execution process
- [TEAMS.md](../../TEAMS.md) — Persona definitions
