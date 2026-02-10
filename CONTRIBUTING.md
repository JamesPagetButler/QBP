# Project Constitution & Contributor Guide

This document outlines the process for contributing to the Quaternion-Based Physics (QBP) project. Adherence to these rules is mandatory to ensure the quality, rigor, and collaborative nature of our work.

## The Project Constitution

1.  **Start with an Issue:** All work must begin with a documented Issue. This creates a public record of the task and allows for initial discussion.
2.  **Branch for Work:** All work is to be done on a descriptively named branch (e.g., `feature/exp01-sg-theory`). Do not commit directly to `master`.
3.  **Submit a Pull Request:** All changes must be proposed via a Pull Request (PR), which must reference the originating Issue in its description.
4.  **Require Tiered Review & Sign-Off:** All Pull Requests are subject to a tiered review process based on scope. Tier 1 (docs/typos) requires single AI review. Tier 2 (code/tests) requires dual AI review (Red Team + Blue Team). Tier 3 (theory/proofs) requires full panel review. See [Tiered Review System](#tiered-review-system) for details. Final sign-off from James is always required.
5.  **Link Tests to Reality:** Every automated test must be a "synthetic experiment" that simulates a real, physically verifiable experiment. This connection must be explicitly documented.

---

## The Research Lifecycle

Our project operates on a `Sprint -> Refine -> Sprint` cycle, which is the engine for our scientific discovery.

1.  **Sprint (Experiment N):** We execute all 5 phases for a single experiment from our roadmap (Ground Truth, Implementation, Visualization, Formal Proof, Publication). A sprint is not complete until all 5 phases are successfully implemented and merged.

2.  **Theory Refinement Stage:** After a sprint is complete, we enter a dedicated phase to:
    *   **Analyze:** Discuss the results and what they imply for our theory.
    *   **Check Guide Posts:** Evaluate if any "Guide Posts" (e.g., emergent conservation laws) have appeared.
    *   **Extend Theory:** Develop the new theoretical underpinnings required to tackle the *next* experiment on our roadmap.
    *   **Document:** All findings from this stage are documented in `paper/DESIGN_RATIONALE.md` and the main `paper/quaternion_physics.md`.

    The Expert Panel (7 personas) reviews all Theory Refinement work. See [Expert Panel](docs/personas/expert_panel.md).

3.  **Loop:** We then begin the next sprint for Experiment N+1.

This ensures our theory evolves based on our experimental results.

### Sprint Retrospective Gate

Before beginning Sprint N+1, a brief retrospective must be documented in `SPRINT_STATUS.md` answering:

1.  Did we follow the critical path this sprint?
2.  If not, where did we deviate?
3.  What was the *cost* of that deviation?
4.  What is our simple, agreed-upon commitment for the next sprint?

This is not a compliance gate — it is a learning gate. The goal is to connect the pain of deviation to the action that was skipped, building institutional memory that makes the process feel valuable rather than bureaucratic.

---

## Session-Start Protocol (The Herschel Check)

At the start of every work session, all collaborators (human and AI) must:

1.  **Read `SPRINT_STATUS.md`** — understand current lifecycle position.
2.  **Verify alignment** — confirm planned work matches the critical path.
3.  **Log diversions** — if starting housekeeping or a side quest, add it to the Active Diversions table with a return point.
4.  **Close diversions** — when returning, mark the diversion complete and resume from the recorded return point.

This is the "Herschel Check." It exists because all three collaborators have demonstrated a tendency to drift from the critical path. It adds ~30 seconds of overhead per session to prevent hours of unmanaged drift.

### The Herschel Persona

**Caroline Herschel (1750-1848)** — Pioneering German astronomer. While her brother William pursued sweeping theoretical discoveries, Caroline was the meticulous, systematic engine behind their work. She catalogued nebulae and star clusters, bringing order to chaos. She polished the mirrors, took the measurements, and did the math. Her contribution was foundational: the process-driven, disciplined bedrock upon which grander discoveries were built.

**Voice:** Meticulous, calm, persistent. Not adversarial — supportive but firm. The person who makes sure the telescope is calibrated before you start observing.

**Relationship to other personas:** Herschel is **orthogonal** to the content-focused personas. Sabine, Grothendieck, Knuth, Furey, and Feynman are concerned with the *content* of work (the what and how). Herschel is concerned exclusively with *process* (the when and why). She doesn't argue with Grothendieck's theory — she asks, "Does the plan say we should be exploring this tangent right now?" She doesn't critique Knuth's code — she asks, "Now that your PR is merged, have you closed the corresponding issue?"

**Key questions:**
-   "Have we completed what we started before beginning something new?"
-   "What does the status file say is our next action?"
-   "Are we logging this diversion, or have we decided to change the plan?"

**Invocation:**
-   AI agents invoke Herschel at session start (the "Herschel Check").
-   Any collaborator can invoke mid-session: *"Herschel check — are we on the critical path?"*
-   Shared between Claude and Gemini — either can wear the hat.

---

## Close Your Loops

When a PR merges that satisfies an issue's acceptance criteria, the issue must be closed in the same work session. Do not move on to new work leaving issues open that should be closed. Open issues with merged PRs create false signals about project status and erode trust in the tracking system.

**Responsibility:** The collaborator who merges the PR (or requests the merge) must verify that the issue's acceptance criteria are met, then close the issue immediately. If acceptance criteria are only partially met, document the remaining gaps on the issue rather than leaving it silently open.

---

## Experiment Numbering

Each experiment has a unique two-digit number (01, 02, 03...). Sub-experiments that extend a base experiment use a letter suffix (01b, 01c, etc.).

### Current Experiment Registry

| Number | Experiment | Sprint | Status |
|--------|------------|--------|--------|
| 01 | Stern-Gerlach | Sprint 1 | Complete |
| 01b | Angle-Dependent Measurement | Sprint 2 | In Progress |
| 02 | Double-Slit | — | Planned |
| 03 | Lamb Shift | — | Planned |
| 04 | Anomalous g-2 | — | Planned |
| 05 | Bell's Theorem | — | Planned |
| 06 | Particle Statistics | — | Planned |
| 07 | Positronium Ground State | — | Planned |
| 08 | Hydrogen Spectrum | — | Planned |
| 09 | Gravity Tests | — | Planned |

See `research/README.md` for the authoritative experiment list and Sprint mapping.

### Adding a New Experiment

When adding a new experiment:

1. **Check for collisions:** Run `python scripts/validate_experiment_numbers.py` to verify the number is unique.
2. **Reserve the number:** Add an entry to `research/README.md` before creating files.
3. **Use consistent naming:** All files and directories must use the same number:
   - `research/NN_name_expected_results.md`
   - `experiments/NN_name/`
   - `results/NN_name/`
4. **Sub-experiments:** If extending an existing experiment, use a letter suffix (e.g., 01b for angle-dependent measurement, which extends Stern-Gerlach).

CI will fail if duplicate experiment numbers are detected.

---

## Branch Lifecycle

All work must be done on branches. Never commit directly to `master`.

### Branch Rules

1. **All issues must be worked on a branch** — No exceptions.
2. **Related issues can share a branch** — Group logically connected work (e.g., multiple fixes for same feature).
3. **Mandatory new branch for major lifecycle stages:**
   - New sprint phase (Phase 1, 2, 3, 4, 5)
   - New sprint (Sprint 1, Sprint 2, etc.)
   - Theory Refinement stage

### Branch Naming Convention

| Work Type | Branch Pattern | Example |
|-----------|----------------|---------|
| Sprint phase | `sprint-N/phase-M-name` | `sprint-2/phase-2-implementation` |
| Theory Refinement | `sprint-N/theory-refinement` | `sprint-1/theory-refinement` |
| Housekeeping | `housekeeping/description` | `housekeeping/security-audit` |
| Feature (grouped issues) | `feature/description` | `feature/proof-viz-improvements` |
| Docs | `docs/description` | `docs/update-contributing` |
| Bugfix | `fix/description` | `fix/expectation-value-bounds` |

### Branch Lifetime

- **Target:** Merge branches within 1-3 work sessions
- **Rebase frequently:** Keep branches up-to-date with master to minimize merge conflicts
- **Smaller PRs:** Prefer multiple small, focused PRs over one large PR

---

## The 5-Phase Experimental Lifecycle

Every experiment on our roadmap follows a structured 5-phase lifecycle. This ensures rigorous validation before publication.

### Phase Overview

| Phase | Goal | Output | Success Criteria |
|-------|------|--------|------------------|
| **Phase 1: Ground Truth** | Research and document expected results | `research/NN_..._expected_results.md` | Complete specification with quantitative predictions |
| **Phase 2: Implementation** | Build code and run synthetic experiment | `qphysics.py` updates, `/results` data | Results within 3σ of ground truth |
| **Phase 3: Visualization** | Visualize results, verify success | `vpython` animations, Manim videos | Visual confirmation of Phase 2 success |
| **Phase 4: Formal Verification** | Prove, review, and visualize | `.lean` proofs, review report, interactive WASM viz | 4a+4b+4c gate for Phase 5 (James may waive 4c) |
| **Phase 5: Publication** | Document and communicate success | `paper/quaternion_physics.md` section; library releases when applicable | Complete, reviewed documentation |

### Phase Transitions & Decision Gates

```
┌─────────────────────────────────────────────────────────────────────┐
│                                                                      │
│  Phase 1: Ground Truth                                               │
│  └── Output: research/NN_..._expected_results.md                     │
│              ↓                                                       │
│  Phase 2: Implementation                                             │
│  └── Output: experiments/NN_.../simulate.py, tests, results          │
│              ↓                                                       │
│  Phase 3: Visualization & Analysis ◄──────────────────────┐          │
│  └── Decision Gate:                                       │          │
│      "Do visualization & analysis confirm results          │          │
│       match ground truth within defined tolerance?"       │          │
│              │                                            │          │
│         [NO] └──► Create issue, loop back ────────────────┘          │
│              │                                                       │
│        [YES] ↓                                                       │
│  Phase 4: Formal Verification ◄───────────────────────────┐          │
│  │                                                        │          │
│  ├── 4a: Formal Proof (Gemini)                            │          │
│  │   └── Output: .lean proof files in /proofs             │          │
│  ├── 4b: Proof Review (Claude)                            │          │
│  │   └── Output: review report, compilation check         │          │
│  ├── 4c: Interactive Proof Visualization (Claude/team)    │          │
│  │   └── Output: C/WASM interactive viz in browser        │          │
│  │                                                        │          │
│  └── Decision Gate (4a + 4b + 4c):                        │          │
│      "Do all Lean proofs verify AND does the              │          │
│       proof review confirm correctness AND is the         │          │
│       interactive visualization complete?"                │          │
│              │                                            │          │
│         [NO] └──► Create issue, loop back to Phase 2 ─────┘          │
│              │    (James may waive 4c to proceed)                    │
│              │                                                       │
│        [YES / 4c WAIVED] ↓                                           │
│  Phase 5: Publication                                                │
│  ├── Track A (Required): paper/quaternion_physics.md section         │
│  └── Track B (If applicable): /libs/ package → Reservoir publish     │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### Phase Details

#### Phase 1: Ground Truth & Planning

**Goal:** Research and document the real-world results we need to match.

**Schema:** See [Ground Truth Schema](docs/schemas/ground_truth_schema.md) for required sections and format.

**Tasks:**
- Review existing literature and experimental data
- Define quantitative predictions with error bounds
- Specify acceptance criteria (e.g., "within 3σ of expected value")
- Classify predictions as "Validation" (matches QM) or "Novel" (differs from QM)
- Identify required tools or framework extensions

**Output:** `research/NN_experiment_expected_results.md`

**Exit Criteria:** Ground truth document reviewed and approved, with prediction classification complete.

---

#### Phase 2: Implementation & Execution

**Goal:** Build the code and run the synthetic experiment.

**Tasks:**
- Extend `qphysics.py` if needed
- Create simulation script in `experiments/NN_name/simulate.py`
- Create tests in `tests/physics/test_name.py`
- Run simulation and capture results

**Output:**
- Updated `qphysics.py` (if needed)
- Simulation script and tests
- Raw data in `/results` directory

**Exit Criteria:** All physics tests pass; results statistically match ground truth.

---

#### Phase 3: Visualization & Analysis (The Debug Loop)

**Goal:** Visualize the results from Phase 2 to gain intuitive understanding and iteratively verify success. This phase is crucial for debugging and refining our model if initial results do not match ground truth.

**Tasks:**
- Create `vpython` animations showing experiment
- Create plots comparing results to predictions
- Build interactive dashboard components

**Workflow:**
1.  **Human Interpretation:** The principal human collaborator (James) reviews the visualization and states their interpretation of the experimental outcome.
2.  **Gemini Verification:** Gemini programmatically analyzes the raw numerical data from the `/results` file and provides an independent statistical summary to confirm or clarify the human interpretation.

**Decision Gate:**
> "Do both the human interpretation and Gemini's data analysis confirm that the results from Phase 2 accurately depict a successful experiment that matches the ground truth within our defined tolerance (e.g., 3σ)?"

-   **If NO:** Document the failure, create a new issue for debugging and refinement, and **loop back to Phase 2 (Implementation & Execution)**.
-   **If YES:** Proceed to Phase 4.

**Output:** Verified visualizations in `src/viz/` that faithfully represent Phase 2 data and confirm understanding.

---

#### Phase 4: Formal Verification (Sub-Phases 4a/4b/4c)

Phase 4 is divided into three sub-phases. The phase count remains 5 and each experiment still has 5 issues — sub-phases are tracked as task sections within the single Phase 4 issue.

**Sub-phase dependencies:** 4a (Formal Proof) must complete before 4b (Proof Review) can begin. 4b must complete before 4c (Interactive Proof Visualization) can begin. Phase 4c runs in parallel with Phase 5 preparation — it is a deliverable, not a gate for publication.

##### Phase 4a: Formal Proof

**Owner:** Gemini

**Goal:** Mathematically prove that the successful implementation (Phase 2) is logically sound according to our axioms.

**Tasks:**
- Define formal statements of theorems in Lean 4 based on the quaternionic model.
- Write proofs connecting implementation's logic to our axioms.
- Verify all proofs compile without errors in Lean 4.

**Output:** Completed `.lean` proof files in `/proofs` directory.

**Library Development (When Needed)**

During Phase 4a, proofs may require Lean 4 capabilities that do not exist in Mathlib or the broader ecosystem, or where existing capabilities are insufficient (buggy, incomplete, or incompatible API). When this happens, we build the missing capability as an independent library.

*We do not speculatively create libraries — we build only when proofs demand capabilities that don't exist or are inadequate.*

**When existing libraries are insufficient:**
- **Buggy:** File an upstream issue first. If no fix is forthcoming, fork and patch.
- **Incomplete:** Contribute upstream if feasible. Otherwise, build a wrapper or extension.
- **Incompatible API:** Build a wrapper that provides the interface we need.

**Process:**
1. **Document the gap** — create a GitHub Issue describing the missing capability and why existing libraries are insufficient.
2. **Create a separate Lake package** in `/libs/<name>/` — the library must be a standalone project with its own `lakefile.lean`, `lean-toolchain`, and `README.md`.
3. **Wire into proofs** via local `require` — the QBPProofs package references the library using a local path dependency during development. **Important:** During local development, the library's `lean-toolchain` must match the `proofs/` toolchain exactly. Version divergence is only acceptable after the library is published to Reservoir and referenced via a versioned dependency.
4. **Follow Library Quality Standards** — see the [Library Quality Standards](#library-quality-standards) section below. Full compliance is required before Phase 5 Track B publication, not during active Phase 4a development.

**Key principle:** Libraries must remain general-purpose. They must not import from `proofs/QBP/` or depend on any QBP-specific definitions. If other Lean users could benefit from the capability, it belongs in `/libs/`.

##### Phase 4b: Proof Review

**Owner:** Claude

**Goal:** Review Gemini's formal proofs for rigor, verify clean compilation, and check correspondence to Phase 1/2 results.

**Tasks:**
- Review all `.lean` proof files for mathematical rigor and structural correctness.
- Verify clean compilation (`lake build` succeeds with no `sorry`).
- Check that proven theorems correspond to the ground truth claims from Phase 1 and the implementation logic from Phase 2.
- Document review findings in a review report posted to the Phase 4 issue.

**Output:** Proof review report confirming correctness or identifying issues.

> **Axiom-first principle:** The deepest risk to formal verification is not
> a software bug but a conceptual feedback loop: a developer runs the Phase 2
> simulation, observes a numerical result, and then formulates axioms specifically
> to make a Lean proof of that result succeed. This "simulation-steered proving"
> can enshrine artifacts of the numerical model as formal truths.
>
> Phase 4b reviewers must challenge every axiom on **first principles alone**,
> asking: "Would this axiom be chosen if we had never run the simulation?"
> Discrepancies between the formal (exact) result and the simulation (approximate)
> result are where genuine insights live — they should be documented, not hidden.

##### Phase 4c: Interactive Proof Visualization

**Owner:** Claude / team

**Goal:** Build an interactive browser-based visualization of the formal proof structure, allowing users to step through the proof dependency tree and see how axioms connect to experiment-specific theorems. The formal proof visualization is independent of the Python simulation — it derives entirely from Phase 4a proof metadata.

**Tech Stack:** C with [raylib](https://www.raylib.com/) compiled to WASM via [Emscripten](https://emscripten.org/). If raylib proves unsuitable, alternatives (SDL2 + Emscripten, raw WebGL) may be evaluated in a Phase 4c issue — the constitution does not pre-commit to fallbacks.

**Tasks:**
- Port relevant quaternion math to C (`qphysics.c/h`).
- Create proof annotation overlay (`proof_annotations.c/h`) driven by Phase 4a proof metadata.
- Build scene for the specific experiment implementing `init/update/draw/cleanup` interface.
- Compile to WASM with Emscripten; produce deployable `dist/` output.
- Ensure interactive controls (rotate, zoom, toggle proof annotations, step through proof structure).
- Follow the QBP design palette for visual consistency.

**Data Flow (Formal Proof — Independent of Simulation):**
```
Phase 4a proofs (.lean) ──► export_data.py ──► data/proof_graph_NN.json
         │                                            │
         │  (proof metadata extraction                ▼
         │   is semi-automated: script          C reads JSON (Emscripten --preload-file)
         │   parses .lean for theorem                  │
         │   names/deps, human curates                  ▼
         │   physical meanings as needed)       Interactive WASM app in browser
         │                                     (proof dependency tree + annotations)
         └──► export_data.py lives at src/viz/interactive/export_data.py
```

> **Independence invariant:** `export_data.py` reads ONLY from `proofs/` (Lean files).
> It must NEVER import or reference Phase 2 simulation code (`src/qphysics.py`),
> results CSVs, or any other simulation artifacts. Phase 2 results may be shown
> for comparison in a separate, optional data file — but the proof graph is
> self-contained. This boundary is enforced by the test suite in
> `tests/test_proof_viz_independence.py`.

**Scene Interface Pattern:** Each experiment implements a scene with `init/update/draw/cleanup` functions. New experiments add a `.c` file in `scenes/` and register it in `main.c`.

**Directory Layout:**
```
src/viz/interactive/
├── README.md                # Build instructions and usage
├── CMakeLists.txt           # CMake build configuration
├── Makefile                 # Convenience wrapper
├── shell.html               # Emscripten HTML template
├── export_data.py           # Extracts proof metadata from .lean files → JSON (no simulation deps)
├── src/
│   ├── qphysics.c           # C port of quaternion math
│   ├── qphysics.h
│   ├── proof_annotations.c  # Proof overlay rendering
│   ├── proof_annotations.h
│   ├── scene.h              # Scene interface (init/update/draw/cleanup)
│   ├── main.c               # Entry point, scene dispatch
│   └── scenes/
│       └── experiment_01_stern_gerlach.c
├── data/                    # Committed — generated by export_data.py, checked in for reproducibility
│   └── proof_graph_01.json  # Proof dependency graph (axioms, theorems, deps, physical meanings)
├── build/                   # .gitignore'd — native/WASM build artifacts
└── dist/                    # .gitignore'd — deployable WASM output
```

**Output:** Interactive WASM visualization in `src/viz/interactive/dist/`.

##### Phase 4 Decision Gate

> "Do all Lean proofs verify (4a) AND does the proof review confirm correctness (4b)?"

-   **If NO (4a/4b failure):** Document the flaw (e.g., a mathematical inconsistency), create a new issue, and **loop back to Phase 2 (Implementation & Execution)** to address the underlying problem.
-   **If YES:** Proceed to Phase 5. Phase 4c (visualization) runs in parallel with Phase 5 — it is a deliverable, not a blocker.

**Phase 4c failures** (visualization bugs, build issues, rendering problems) are engineering problems. They loop back to 4c, not to Phase 2. A 4c issue does not block publication.

---

#### Phase 5: Publication

**Goal:** Document and communicate our confirmed and verified success.

Phase 5 has two tracks. Track A is always required. Track B applies only when Phase 4 produced one or more libraries in `/libs/`.

##### Track A: Paper (Required)

**Tasks:**
- Write a new, detailed section for `paper/quaternion_physics.md` for this experiment.
- Include visualizations from Phase 3.
- Reference formal proofs from Phase 4.
- Update `DESIGN_RATIONALE.md` with key decisions and insights gained.

**Output:** Finalized, reviewed section in the main paper, ready for broader dissemination.

**Exit Criteria:** Section reviewed by Red Team and Gemini; merged to master.

##### Track B: Community Contribution (When Applicable)

*Skip this track if no libraries were developed during Phase 4.*

**Tasks:**
- Finalize library to meet all [Library Quality Standards](#library-quality-standards).
- Follow Lean 4 community publishing guidelines (Reservoir submission requirements, naming conventions, documentation standards).
- If Reservoir requires a standalone repository, extract the library from `/libs/` into its own repo. This is acceptable and expected for community publication.
- Tag a semantic version (`vMAJOR.MINOR.PATCH`) on the library.
- Submit the library to [Reservoir](https://reservoir.lean-lang.org/) for indexing.
- Generate API documentation with `doc-gen4`.
- Announce on [Lean Zulip](https://leanprover.zulipchat.com/) with a brief description and link.

**Output:** Published, documented Lean 4 library available to the community.

**Exit Criteria:** Library indexed on Reservoir; documentation live; announcement posted.

---

### Library Quality Standards

The following standards apply to any library in `/libs/` before it can be published via Phase 5 Track B. During active Phase 4 development, these are goals to work toward — not blockers.

| Requirement | Details |
|-------------|---------|
| Separate Lake package | Own `lakefile.lean`, `lean-toolchain`, `README.md` |
| No QBP dependencies | General-purpose; no imports from `proofs/QBP/` |
| License | MIT license (`LICENSE` file in package root), matching the QBP project |
| CI builds | GitHub Actions workflow running `lake build` |
| No `sorry` | All proofs complete |
| API documentation | Doc-strings on public definitions; `doc-gen4` compatible |
| Semantic versioning | Git tags `vMAJOR.MINOR.PATCH` |
| Reservoir metadata | `lakefile.lean` includes `name`, `version`, `keywords`, `homepage` |
| README | Purpose, installation, usage examples, license reference |

---

### Issue Structure for 5-Phase Lifecycle

Each experiment requires 5 issues, one per phase:

| Issue Title Pattern | Labels |
|---------------------|--------|
| `Experiment N: Name - Phase 1: Ground Truth` | `type: experiment`, `phase: ground-truth` |
| `Experiment N: Name - Phase 2: Implementation` | `type: experiment`, `phase: implementation` |
| `Experiment N: Name - Phase 3: Visualization` | `type: experiment`, `phase: visualization` |
| `Experiment N: Name - Phase 4: Formal Verification (4a/4b/4c)` | `type: experiment`, `phase: proof` |
| `Experiment N: Name - Phase 5: Publication` | `type: experiment`, `phase: publication` |

Phase 2 is blocked by Phase 1. Phase 3 is blocked by Phase 2. And so on.

**Note:** Phase 4 sub-phases (4a/4b/4c) are tracked as task sections within the single Phase 4 issue, not as 3 separate issues. The issue count per experiment remains 5.

---

## Review Process Details

Our review process is designed to be rigorous and auditable, with review depth matched to PR scope.

### Tiered Review System

Not all PRs need the same level of scrutiny. Use the appropriate tier based on PR scope:

| Tier | PR Type | Review Process | Labels |
|------|---------|----------------|--------|
| **Tier 1** | Docs, typos, formatting, comments | Single AI review (Red OR Blue) | `tier-1-review` |
| **Tier 2** | Code, tests, config, housekeeping | Dual AI review (Red AND Blue, can be parallel) | `tier-2-review` |
| **Tier 3** | Theory, proofs, architecture, new phases | Full panel review (sequential, deep analysis) | `tier-3-review` |

**Tier Selection Guidelines:**
- **Tier 1:** Changes that don't affect behavior — README updates, comment fixes, formatting
- **Tier 2:** Changes that affect behavior but not core theory — bug fixes, new tests, tooling
- **Tier 3:** Changes that affect physics formalism, axioms, or formal proofs — theory refinement, new experiments

**Parallel Reviews (Tier 2):** For Tier 2 PRs, Red Team and Blue Team reviews can run in parallel to reduce latency. Both reviews are still required before merge.

**Default:** If unsure, default to Tier 2. James can upgrade or downgrade tier as needed.

### Reviewing Agents

| Agent | Persona(s) | Tool/CLI | Role |
|-------|-----------|----------|------|
| **Claude** | Sabine (Experimentalist) | Claude Code CLI | Red Team - tests, feasibility, measurements |
| **Claude** | Grothendieck (Mathematician) | Claude Code CLI | Red Team - rigor, axioms, structure |
| **Claude** | Knuth (Engineer) | Claude Code CLI | Red Team - code quality, efficiency, docs |
| **Gemini** | Furey (Algebraist) | Gemini CLI | Theory - division algebras, elegance |
| **Gemini** | Feynman (Physicist) | Gemini CLI | Theory - physical intuition, clarity |
| **Claude / Gemini** | Herschel (Process Navigator) | Either CLI | Process - lifecycle compliance, sprint transitions |
| **Claude** | Der Depperte (Communicator) | Claude Code CLI | Writing - clarity, accessibility, wonder (Phase 5) |
| **Claude** | Expert Panel (7 personas) | Claude Code CLI | Theory Refinement - deep theoretical validation (see [docs/personas/](docs/personas/)) |

### Pre-Merge Requirements

Before any PR can be merged, the PR **must** contain:

| Requirement | Posted By | Format |
|-------------|-----------|--------|
| Red Team Review (3 personas) | Claude | PR Comment |
| Red Team Summary | Claude | PR Comment |
| Gemini Review (2 personas) | Claude (as scribe) | PR Comment |
| Gemini Summary | Claude (as scribe) | PR Comment |
| All CI checks passing | GitHub Actions | Status checks |
| Human explicit merge command | James | CLI instruction |

### Review Flow

```
1. PR Created
      ↓
2. Claude posts Red Team review (Sabine, Grothendieck, Knuth)
      ↓
3. Gemini provides review (Furey, Feynman) in Gemini CLI
      ↓
4. Claude scribes Gemini's review to PR
      ↓
5. CI checks pass
      ↓
6. James reviews summaries, asks questions if needed
      ↓
7. James issues explicit "merge" command
      ↓
8. Merge executed
```

### Review Process Steps

1.  **Red Team Review:** Claude conducts three-persona peer review (`Sabine`, `Grothendieck`, `Knuth`) and posts findings as a PR comment with summary. Must include **Acceptance Criteria Verification** (see below).
2.  **Gemini Review:** Gemini conducts two-persona review (`Furey`, `Feynman`) in structured Markdown format within Gemini CLI. Must include **Acceptance Criteria Verification** (see below).
3.  **Documentation of Gemini's Review:** Claude acts as scribe, copying Gemini's Markdown review and posting it as a separate PR comment.
4.  **Issue Synthesis:** Claude synthesizes both reviews into a numbered list of issues, flagging any unmet acceptance criteria as **BLOCKING**.
5.  **Final Approval:** James reviews all summaries, asks clarifying questions if needed, then issues explicit merge command.

### Acceptance Criteria Verification Protocol

Every review must include a formal **Acceptance Criteria Verification** section that checks the PR against the linked issue's requirements. This ensures PRs don't just receive qualitative approval but actually satisfy what was specified.

**Prerequisites:** Requires GitHub CLI (`gh`) with repository access configured.

**Protocol:**
1. **Identify linked issues** from PR title, body, and commit messages (`Closes #X`, `Fixes #X`, etc.). If no issues are linked, AC verification is N/A (not a failure).
2. **Fetch issue content** using `gh issue view <number>`
3. **Extract requirements** — all `- [ ] **AC:**` lines and `Definition of Done` checkboxes
4. **Verify each criterion:**
   - Quote the criterion verbatim
   - Assess: PASS / FAIL / PARTIAL
   - Cite evidence (file:line or explanation)
5. **Verdict:** PASS (all criteria met) or BLOCKING (any unmet)

**Status Definitions:**
- **PASS** — Criterion fully satisfied with cited evidence
- **FAIL** — Criterion not satisfied; requires action before merge
- **PARTIAL** — Criterion partially satisfied; treated as BLOCKING unless James explicitly approves proceeding

**Template-Agnostic Design:** This protocol parses the actual issue text, not a hardcoded schema. If issue templates evolve, the verification protocol still works — the rigor comes from the process, not the template structure.

**Rule:** Unmet acceptance criteria (FAIL or PARTIAL) = BLOCKING. Cannot be deferred to housekeeping without James's explicit approval.

**Example:** For a PR linking to issue #64 (Phase 5: Publication), the AC verification section would look like:

```markdown
# Acceptance Criteria Verification

**Linked Issue(s):** #64

## Issue #64: Experiment 1 - Phase 5: Publication

| # | Criterion | Status | Evidence |
|---|-----------|--------|----------|
| 1 | "Paper section follows physics paper schema" | PASS | `paper/quaternion_physics.md:103-181` follows schema structure |
| 2 | "Phase 4 formal proofs referenced" | PASS | Line 166 references `SternGerlach.lean` |
| 3 | "Phase 3 visualizations included" | PARTIAL | References `stern_gerlach_demo.py` but no figure numbers |
| 4 | "DESIGN_RATIONALE.md updated" | FAIL | No Experiment 1 insights added |

**Verdict:** BLOCKING — Criteria 3-4 require action
```

## Issue-Driven Workflow

All work in this project is driven by GitHub Issues. This ensures traceability and prevents scope creep.

### The Issue Lifecycle

```
1. Work identified        → Create GitHub Issue with acceptance criteria
2. Issue discussed        → Refine scope, assign to sprint
3. Work started           → Create feature branch referencing issue
4. Work completed         → Create PR with "Closes #XX" in description
5. Reviews complete       → Extract new action items, create follow-up issues
6. PR merged              → Issue auto-closes, TODO.md updated
```

### Sub-Phase Issues

When a phase has sub-phases (e.g., Phase 4 has 4a, 4b, 4c), create a **separate GitHub issue for each sub-phase**. The parent phase issue becomes a tracking issue that links to all sub-phase issues.

**Rules:**
- A PR's `Closes #XX` must reference only the sub-phase issues it fully satisfies — never the parent tracking issue.
- The parent tracking issue closes only when all sub-phase issues are closed.
- This prevents premature auto-closure when a PR addresses one sub-phase but not others.

**Example:**
```
#55 (Phase 4 — tracking issue)
  ├── #131 (4a: Formal Proof)      ← closed by proof PR
  ├── #132 (4b: Proof Review)      ← closed by review PR
  └── #133 (4c: Interactive Viz)   ← closed by viz PR
  └── #55 closes manually when #131 + #132 + #133 are all closed
```

### Issue Requirements

Every issue must include:
- **Summary:** Clear description of the task
- **Background:** Why this work is needed (link to review feedback, roadmap)
- **Acceptance Criteria:** Checklist of requirements for completion
- **References:** Links to relevant code, research docs, and prior PRs

### Issue Labels

Issues are categorized using labels to separate main research work from infrastructure concerns.

#### Core Research Labels

| Label | Description |
|-------|-------------|
| `type: experiment` | Experiment phase work (Phases 1-5) |
| `type: research` | Theory Refinement and scientific investigation |
| `phase: ground-truth` | Phase 1 work |
| `phase: implementation` | Phase 2 work |
| `phase: visualization` | Phase 3 work |
| `phase: proof` | Phase 4 work |
| `phase: publication` | Phase 5 work |

#### Infrastructure Labels

| Label | Description |
|-------|-------------|
| `housekeeping` | Maintenance tasks outside main research workflow |

**Use `housekeeping` for:**
- Documentation infrastructure (CONTRIBUTING.md, README updates)
- CI/CD fixes and improvements
- TODO.md maintenance and accuracy
- Process/workflow documentation
- Tooling setup (Lean 4, pre-commit, etc.)
- Review process improvements

**Do NOT use `housekeeping` for:**
- Experiment phases (1-5) — use `type: experiment`
- Theory Refinement issues — use `type: research`
- Ground truth research — use `phase: ground-truth`
- Scientific investigations — use `type: research`
- Core physics implementation — use appropriate phase label

**Why This Matters:**
Separating housekeeping from research ensures infrastructure concerns don't block or distract from the main experimental workflow. Housekeeping issues can be addressed opportunistically without disrupting sprint progress.

### Issue Closure Checklist

**CRITICAL:** Issues must NOT be closed until ALL of the following are verified:

- [ ] **All acceptance criteria verified** — Each criterion must be actively tested/confirmed, not just marked complete based on historical work
- [ ] **Red Team review completed** — Claude's review (Sabine, Grothendieck, Knuth) posted to the issue
- [ ] **Gemini review completed** — Gemini's review (Furey, Feynman) posted to the issue
- [ ] **Human approval obtained** — Explicit sign-off from James

**Why This Matters:**
Closing issues prematurely (e.g., because "the work was done in PR #X") bypasses the review process and can allow defects to slip through. The review requirement exists precisely to catch issues that automated tests might miss.

**Process Violation Recovery:**
If an issue is found to have been closed without proper reviews:
1. Reopen the issue immediately
2. Add a comment documenting the process violation
3. Conduct the missing reviews
4. Only close after all checklist items are verified

### Post-Review Issue Creation

After reviews are posted to a PR, Claude must:
1. Extract action items from reviewer feedback
2. Create GitHub Issues for each new task
3. Update `TODO.md` with issue links
4. Reference the originating PR in new issues

This ensures no feedback is lost and all follow-up work is tracked.

### Project Plan (TODO.md)

The `TODO.md` file serves as the central project plan:
- **Roadmap:** High-level experiment sequence with issue links
- **Current Sprint:** Active tasks with issue links and status
- **Backlog:** Future tasks with issue links
- **Completed:** Historical record with PR references

## Updating the Design Rationale

To ensure the project's intellectual history is preserved, the `paper/DESIGN_RATIONALE.md` file must be continuously updated.

1.  **Rationale in PRs:** For any Pull Request that introduces a new feature, a significant change in logic, or a new architectural decision, the author **must** include a "Design Rationale" section in the PR's description, explaining the "why" behind the changes.
2.  **Post-Merge Scribe Duty:** After such a PR is merged, it is the responsibility of the scribe AI (Claude) to create a subsequent PR that appends the "Design Rationale" from the merged PR's description into the main `paper/DESIGN_RATIONALE.md` document.

This process creates a living document that evolves alongside the project itself.

## Hard Gate: Human Merge Authorization

**CRITICAL RULE:** No merge to `master` may occur without explicit human authorization.

### Pre-Merge Checklist

Before any merge can occur, the following must be completed:

1. **Claude (Red Team) Review Confirmation**
   - Claude must explicitly confirm: "Red Team review complete"
   - Must provide a summary of findings from all three personas (Sabine, Grothendieck, Knuth)
   - Summary must be posted as a PR comment

2. **Gemini (Furey/Feynman) Review Confirmation**
   - Gemini must explicitly confirm: "Gemini review complete"
   - Must provide a summary of findings from both personas
   - Claude scribes this to the PR as a comment

3. **Review Summary Available**
   - A consolidated summary of both AI reviews must be available
   - Key concerns, approvals, and action items clearly listed
   - Human can read this before deciding

4. **Q&A Window**
   - Before merge, human may pose questions to either AI agent via CLI
   - Agents must be available to clarify their review findings
   - Example: "Claude, explain Grothendieck's concern about X"
   - Example: "Gemini, what did Feynman mean by Y?"

5. **Explicit Human Merge Command**
   - Only after reviewing summaries and asking any questions
   - Human issues explicit merge instruction

### For AI Agents (Claude, Gemini)

**Gemini's Role (Implementation):**
1. Complete all local work for an assigned issue.
2. Create a branch, commit, and push the changes.
3. **Create the Pull Request** using `gh pr create`.
4. Notify the team that the PR is ready for Red Team review.
5. **STOP** and wait for the review cycle to begin.

**Claude's Role (Review & Scribe):**
1. When a PR is ready, perform the Red Team review.
2. Later, when Gemini's review is ready, scribe it to the PR.
3. Create new issues based on review feedback.
4. **STOP** and wait for the explicit merge instruction.

AI agents must **never** merge a PR based on:
- Prior approval in the conversation
- Assumed permission
- CI passing
- The change being "trivial"

Each merge requires a fresh, explicit instruction such as:
- "merge"
- "merge it"
- "merge PR #X"
- "go ahead and merge"

### Multi-Agent Git Coordination

When Claude and Gemini work on the repository simultaneously, branch confusion can occur. Both agents **must** follow the protocols in:

**[docs/multi_agent_git_coordination.md](docs/multi_agent_git_coordination.md)**

Key requirements:
- **Always verify branch** with `git branch --show-current` before any commit
- **Announce branch ownership** at the start of each work session
- **One branch per agent** at any given time
- **Include branch name in commit messages** as secondary verification

Failure to follow these protocols can result in commits landing on wrong branches and appearing in unrelated PRs.

### Rationale

This gate ensures the human collaborator always has time to:
- Review the PR on GitHub
- Read AI review summaries
- Ask clarifying questions
- Verify CI status
- Make an informed decision

This is a **hard gate** — no exceptions.

## AI Prompt Conventions

To maintain clarity and organization in how we instruct our AI collaborators, we adhere to the following conventions.

### Prompt Generation Workflow

A detailed prompt file for Claude is generated by Gemini **only under two conditions**:
1.  After Gemini has completed all local work required to resolve a specific GitHub Issue.
2.  When explicitly requested by the principal human collaborator (James).

This ensures that Pull Requests are always tied to discrete, completed units of work and are not created prematurely.

### Storage and Naming

*   **Location:** All detailed prompt files are stored in a top-level `/prompts` directory.
*   **Git Status:** This directory is in `.gitignore` and is not committed to the repository.
*   **General Convention:** `prompt_claude_{YYYY-MM-DD}_{short-task-description}.md`
*   **Consolidated Sync Prompts:** For large, end-of-session prompts that bundle multiple changes, a timestamp is used for clarity: `prompt_claude_{YYYY-MM-DD}_{HH-MM-SS}_consolidated-sync.md`


## How to Enforce Our Rules: Branch Protection

The `master` branch is protected by rules configured on the Git hosting platform (e.g., GitHub). This is a one-time, manual setup for the repository administrator.

### Step-by-Step Guide for GitHub

1.  Navigate to the main page of the repository on GitHub.
2.  Click the **Settings** tab.
3.  In the left sidebar, click on **Branches**.
4.  Click the **Add branch protection rule** button.
5.  In the "Branch name pattern" field, type **`master`**.
6.  Enable **Require a pull request before merging**.
7.  Enable **Require approvals** and set the number of required approvals to **3**.
8.  Click **Create** to save the rule.

## Project Toolkit

This project uses a variety of tools for different purposes. Adherence to this toolkit ensures our work remains consistent and reproducible.

### Primary Toolkit
*   **Version Control:** Git
*   **Documentation:** Markdown
*   **Exploration & Simulation:** Python with Jupyter Notebooks.
*   **Python Libraries:**
    *   `numpy`, `matplotlib`, `sympy`, `scipy` for general scientific computing.
    *   `numpy-quaternion` for core quaternion mathematics.
    *   `vpython` for 3D visualization.
*   **Formal Proof:** Lean 4.
*   **Interactive Visualization:** C with [raylib](https://www.raylib.com/) compiled to WASM via [Emscripten](https://emscripten.org/). (Phase 4c output)
*   **Lean Library Publishing:** [Reservoir](https://reservoir.lean-lang.org/) for package registry; `doc-gen4` for API documentation.
*   **Code Quality:** `pre-commit` framework using `black` for formatting and `mypy` for type checking.

### Advanced Toolkit (To be used as the need arises)
*   **High-Performance Simulation:**
    *   **Go:** For highly concurrent simulation tasks (e.g., many-particle systems).
    *   **Numba:** For just-in-time compilation to accelerate specific Python functions.
    *   **C++/Rust:** For rewriting performance-critical library components if necessary.
*   **Large Data Storage:** HDF5.
*   **Automation (CI/CD):** GitHub Actions (a basic setup should be implemented).
*   **Knowledge Management:** Zotero or Mendeley.
*   **Publishing:** Quarto and/or LaTeX for professional typesetting of the final paper.
*   **Design System:** The front-end assets and framework implemented by Claude.
*   **Formal Proof Setup:** The setup and configuration for Lean 4 must be documented.

### Multi-AI Integration (Claude + Gemini)

This project uses a multi-AI architecture: Claude handles development and Red Team reviews; Gemini provides Theory Team reviews (Furey/Feynman personas).

**Integration Methods (in order of preference):**

1. **MCP Server** — When available, Gemini tools appear in Claude's tool list. Use these directly.

2. **Direct CLI Script** — When MCP is unavailable, use the fallback scripts:
   ```bash
   # Test connection
   ~/.claude/scripts/gemini test

   # Quick question
   ~/.claude/scripts/gemini ask "your prompt"

   # Furey/Feynman review (stdin or argument)
   ~/.claude/scripts/gemini review "content to review" "optional context"

   # Critical analysis
   ~/.claude/scripts/gemini critique "problem" "proposed approach"

   # Full PR review with structured output
   ~/.claude/scripts/gemini-pr-review.py <pr_number>
   ~/.claude/scripts/gemini-pr-review.py 178 --output reviews/gemini_review_PR178_2026-02-06.md
   ```

**Usage in Modes:**
- All collaboration modes (Brainstorm, Housekeeping, Focus, Sprint) should use MCP when available, falling back to CLI scripts when not
- Reviews MUST call real Gemini — Claude must never write Gemini's review itself
- If both methods fail, pause the workflow and notify the human

**Script Location:** `~/.claude/scripts/` — Scripts auto-read API key from `~/.claude/settings.json`.

## Troubleshooting CI Failures

### Pre-commit Hook Failures

If CI fails due to formatting or type errors, follow these steps:

1. **Run pre-commit locally:**
   ```bash
   pre-commit run --all-files
   ```

2. **Auto-fix formatting issues:**
   Pre-commit will automatically fix `black` formatting issues. After running, stage the changes:
   ```bash
   git add -u
   git commit -m "style: apply black formatting"
   ```

3. **Fix mypy type errors:**
   Type errors require manual fixes. Review the output and update type hints accordingly.

4. **Re-run pre-commit:**
   Ensure all checks pass before pushing:
   ```bash
   pre-commit run --all-files
   ```

### Common Issues

| Error | Cause | Solution |
|-------|-------|----------|
| `black would reformat` | Code not formatted | Run `black .` or `pre-commit run black --all-files` |
| `mypy: error` | Type annotation issues | Add/fix type hints per mypy output |
| `pre-commit not found` | Hooks not installed | Run `pre-commit install` |
| `ModuleNotFoundError` | Dependencies missing | Run `pip install -r requirements.txt` |

### Keeping Pre-commit Updated

Periodically update pre-commit hooks to their latest versions:
```bash
pre-commit autoupdate
```

### Link Checker Failures

The `Link Checker` workflow runs on all pushes and pull requests to the `master` branch and verifies that all links in markdown files (`.md`) are valid.

| Error | Cause | Solution |
|-------|-------|----------|
| `ERROR: 404 Not Found ...` | A link points to a file or URL that does not exist. | Correct the link path. For links to files that will be created in the same PR, you may need to temporarily ignore the link. |
| `ERROR: Invalid relative link ...` | A relative link is malformed or points to a location outside the repository. | Fix the relative path to be correct within the project structure. |

To ignore specific links that are expected to fail temporarily (e.g., links to documents that will be created in the same PR), you can create a `mlc_config.json` file in the root of the repository. See the `github-action-markdown-link-check` documentation for configuration options.

## Directory Structure

This project follows a defined directory structure to keep our work organized.

*   `/paper`: Contains the formal, human-readable research paper (`quaternion_physics.md`) and the intellectual history of the project (`DESIGN_RATIONALE.md`).
*   `/research`: Contains markdown files detailing the ground truth, experimental methods, and expected results for each test on our roadmap. (Phase 1 output)
*   `/src`: Contains the `qphysics.py` library, the computational heart of our formalism. (Phase 2 output)
*   `/src/viz`: Contains visualization code including `vpython` demos and Manim scenes. (Phase 3 output)
*   `/src/viz/interactive`: C/WASM interactive proof visualizations. (Phase 4c output)
*   `/experiments`: Contains the Python scripts for our "synthetic experiments," which use the `qphysics.py` library to test our hypotheses. (Phase 2 output)
*   `/tests/physics`: Contains physics validation tests for each experiment. (Phase 2 output)
*   `/analysis`: Contains analysis scripts and reports for each experiment (e.g., `analysis/01_stern_gerlach/`). (Phase 3 output)
*   `/proofs`: Contains Lean 4 formal proof files. (Phase 4a output)
*   `/libs`: Independent Lean 4 library packages developed during Phase 4a. Each subdirectory is a standalone Lake package with its own `lakefile.lean` and `lean-toolchain`. See [Library Quality Standards](#library-quality-standards).
*   `/results`: Contains the timestamped output logs from our synthetic experiments. This directory is in `.gitignore` and is not committed to the repository.
*   `/reviews`: Contains locally saved review files from both Claude and Gemini before they are posted to a PR. This directory is in `.gitignore`.
*   `/prompts`: Contains detailed prompt files for instructing AI agents. This directory is in `.gitignore`.
*   `/docs`: Contains general project documentation, schemas, and agent definitions.
    *   `multi_agent_git_coordination.md`: Mandatory git workflow protocols for Claude and Gemini.

## Security

See [SECURITY.md](SECURITY.md) for:
- How to report vulnerabilities
- Secrets management best practices
- Pre-commit hook for detecting secrets (gitleaks)
- Security audit log

**Key rule:** Never commit API keys, tokens, passwords, or credentials to git. Use environment variables or `.env` files (which are in `.gitignore`).

---

## Collaboration Modes

### Brainstorm Mode

A collaborative ideation session where Claude and Gemini engage in creative dialogue, pushing ideas back and forth while keeping the human in the loop.

**Invocation:** Say "brainstorm mode" or "let's brainstorm about X"

**Multi-AI Integration:** Uses MCP or fallback scripts. See [Multi-AI Integration](#multi-ai-integration-claude--gemini).

**Characteristics:**

| Aspect | Description |
|--------|-------------|
| **Tone** | Creative, exploratory, "yes-and" mentality |
| **Structure** | Conversational volleys between Claude ↔ Gemini |
| **Question dynamics** | Push questions to each other, build on responses |
| **Human role** | Can interject anytime; always offered free-form input |

**Session Flow:**

1. Claude poses opening question/framing
2. Gemini responds with ideas + counter-questions
3. Claude builds on Gemini's ideas + new angles
4. Repeat 2-3 volleys
5. Synthesize into concrete proposals
6. Present to human with numbered options + free-form input

**Output Format:**

After a brainstorm session, present results like this:

```
## Brainstorm Results

We explored X and Y. Here's what emerged:

1. **Option A** — [description]
2. **Option B** — [description]
3. **Option C** — [description]

Which direction resonates? Or tell us something different:

> [Your thoughts here]
```

**Rules:**

1. **Always include free-form option** — User is never boxed into AI-generated choices only
2. **Keep volleys short** — 2-4 exchanges, then synthesize
3. **Cite who said what** — "Gemini suggested X, Claude pushed back with Y"
4. **End with action** — Brainstorms must conclude with concrete next steps

---

### Housekeeping Mode

An autonomous batch cleanup mode where Claude works through low-risk housekeeping tasks while the human is away, with pre-approved scope and permissions.

**Invocation:** When the user mentions they're going to bed, sleeping, or stepping away, Claude should ask:

**Multi-AI Integration:** For Gemini reviews during housekeeping, use MCP or fallback scripts. See [Multi-AI Integration](#multi-ai-integration-claude--gemini).

> "Would you like me to switch into Housekeeping Mode while you're away?"

**Purpose:** Allow productive work to continue during human downtime on tasks that don't require interactive decision-making.

#### Pre-Approval Checklist

Before entering Housekeeping Mode, Claude must present and get explicit approval for:

**1. Work Plan**
| Item | Description |
|------|-------------|
| Issues to address | List all issues with numbers and titles |
| Proposed order | Sequence with rationale (dependencies, priority) |
| Estimated scope | Number of files, approximate lines changed |

**2. Required Permissions**

| Category | Examples | Risk Level |
|----------|----------|------------|
| File edits | Edit, Write | Low |
| Git operations | add, commit, push, branch | Low |
| GitHub CLI | gh pr create, gh issue close | Low |
| Build/test | make, pytest, lake build | Medium |
| Install | pip install, npm install | Medium |

**3. Risk Assessment**
- **Reversible?** Confirm all git operations can be reverted
- **Destructive?** Confirm no force-push, no delete without backup
- **Scope-limited?** Confirm changes only touch files related to listed issues

#### Scope Limits

**IN SCOPE:**
- Documentation fixes and improvements
- Code cleanup and formatting
- Minor bug fixes with clear acceptance criteria
- Process improvements
- Closing resolved issues
- Creating housekeeping issues from review feedback

**OUT OF SCOPE:**
- New features
- Architectural changes
- Design decisions requiring human input
- Sprint phase work (Phases 1-5)
- Theory refinement
- Changes to test assertions or expected values
- Anything ambiguous or requiring clarification

#### Process (After Approval)

```
1. Work Locally First
   └── Make all edits, run local tests, commit with clear messages

2. Batch Into PRs
   └── Group related fixes, create PR with summary

3. Run Tiered Reviews
   └── Red Team review (always)
   └── Gemini review (if Tier 2+)

4. Fix Review Issues In-PR
   └── Don't defer — iterate until reviews pass

5. Leave Ready for Merge
   └── PR approved by reviews
   └── Summary comment posted
   └── User merges when they return
```

#### Safety Rails

| Rule | Description |
|------|-------------|
| **No force operations** | Never use `--force`, `--hard`, `-f` flags |
| **No deletions without issues** | Only delete what's explicitly requested in an issue |
| **No external API calls** | Except GitHub and Gemini for reviews |
| **Checkpoint commits** | Commit frequently so work isn't lost |
| **Stop on confusion** | If unclear, leave a note and move to next item |

#### Example Approval Dialog

```
Claude: I see you're heading to bed. Would you like me to enter Housekeeping Mode?

Here's my plan:

**Issues to address:**
1. #169 — Evaluate workspace/gemini submodule
2. #170 — Update ground truth template
3. #168 — Document SU(2) connection

**Estimated scope:** 3 files, ~50 lines

**Required permissions:**
- File edits (Edit, Write)
- Git operations (add, commit, push, branch)
- GitHub CLI (gh pr create, gh issue close)

**Risk assessment:**
- All reversible via git
- No destructive operations
- Scope limited to listed issues

Approve this plan to let me work autonomously?
```

**User Response Options:**
- "Yes, go ahead" — Enters Housekeeping Mode with stated plan
- "Yes, but skip #170" — Enters with modified scope
- "No, just wait" — Does not enter Housekeeping Mode
- Custom modifications to the plan

#### Exit Conditions

Housekeeping Mode ends when:
1. All planned issues are addressed (or blocked)
2. User returns and resumes interactive mode
3. Claude encounters a blocking ambiguity that requires human input
4. An unexpected error occurs that cannot be safely resolved

**On Exit:** Claude posts a summary of work completed, PRs created, and any issues encountered.

#### Example Exit Summary

```
## Housekeeping Mode Complete

**Session:** 2026-02-06 23:00 - 2026-02-07 02:30

### Work Completed
| Issue | Status | PR |
|-------|--------|-----|
| #169 — Evaluate submodule | ✅ Done | #172 (ready for merge) |
| #170 — Update template | ✅ Done | #172 (ready for merge) |
| #168 — SU(2) docs | ⏸️ Blocked | Needs theory input |

### PRs Created
- **#172** — Housekeeping batch: #169, #170
  - Red Team: APPROVE
  - Ready for your merge

### Issues Encountered
- #168 requires clarification on SU(2) representation choice
  - Left comment on issue, moved to next item

### Next Steps
When you return:
1. Review and merge #172
2. Clarify #168 so I can continue

Welcome back!
```

---

### Focus Mode

An autonomous single-issue development mode for targeted work on one specific issue with pre-approved permissions.

**Invocation:** "Focus on issue #X" or "Let's do #X in Focus Mode"

**Multi-AI Integration:** For Gemini reviews, use MCP or fallback scripts. See [Multi-AI Integration](#multi-ai-integration-claude--gemini).

**Purpose:** Enable concentrated, autonomous work on a single issue when you need dedicated attention outside of sprint phases or batch housekeeping.

> **Note:** Focus Mode complements [Housekeeping Mode](#housekeeping-mode) (batch cleanup) and Sprint Mode (multi-phase experimental sprints, see #156). Choose Focus Mode when you need dedicated attention on a single issue outside the sprint lifecycle.

**When to Use:**
- Urgent fixes that can't wait for sprint flow
- Complex issues requiring dedicated attention
- Work outside the current sprint scope
- One-off tasks that don't fit housekeeping or sprint categories

#### Pre-Approval Checklist

Before entering Focus Mode, Claude must present and get explicit approval for:

**1. Issue Summary**
| Item | Description |
|------|-------------|
| Issue | Number, title, and link |
| Acceptance criteria | List all ACs from the issue |
| Branch name | Following branch naming convention |
| Estimated scope | Files affected, approximate complexity |

**2. Required Permissions**

| Category | Examples | Risk Level |
|----------|----------|------------|
| File edits | Edit, Write | Low |
| Git operations | add, commit, push, branch | Low |
| GitHub CLI | gh pr create, gh pr comment | Low |
| Build/test | make, pytest, lake build | Medium |
| External APIs | Gemini review requests | Low |

**3. Review Tier**
- Identify the appropriate tier (1/2/3) based on issue type (see [Tiered Review System](#tiered-review-system))
- Confirm review requirements before starting

**4. Bell Review (Physics Work)**

For physics-related implementations, an optional **Bell Review** evaluates whether the code reflects genuine understanding of the physics, not just correct output.

| Setting | Bell Review |
|---------|-------------|
| **Critical path issues** (sprint phases, theory refinement) | **Default ON** — opt-out with "skip Bell" |
| **Other issues** (housekeeping, infrastructure) | Default OFF — opt-in with "include Bell" |

**Bell evaluates:**

| Criterion | What Bell Checks |
|-----------|------------------|
| Mathematical Rigor | Does the code correctly implement the physics derivation? |
| Physical Insight | Are edge cases handled with understanding, not just code coverage? |
| Anticipation of Difficulties | Does implementation address numerical precision, boundary conditions? |
| Testability | Are tests meaningful physics validations, not just unit tests? |

**Bell's Four Tests (adapted for code):**

1. **The "Why" Question** — Does the code reflect *why* the physics works, not just *that* it works?
2. **The Counterfactual Test** — Would the code catch it if the axioms were wrong?
3. **The Surprise Test** — Did implementation reveal anything unexpected?
4. **The Explanation Test** — Could a physicist read this code and understand the physics?

Bell Review runs after standard tier reviews, before PR creation. See `workspace/evaluation/bell_evaluator_persona.md` for the full persona specification.

#### Workflow

```
1. Create Branch
   └── Branch from master: focus/issue-NNN-description

2. Work Autonomously
   └── Implement solution
   └── Commit with clear messages
   └── Run local tests

3. Run Reviews
   └── Apply appropriate tier reviews
   └── Fix issues (up to 3 cycles)

4. Create PR
   └── Link to issue with "Closes #NNN"
   └── Post review summaries as comments

5. Present for Merge
   └── Summary of work done
   └── Review status
   └── Await human merge approval
```

#### Scope Boundaries

**IN SCOPE:**
- Everything needed to satisfy the issue's acceptance criteria
- Related test updates
- Documentation updates for changed behavior

**OUT OF SCOPE:**
- Unrelated improvements noticed along the way (create separate issues)
- Refactoring beyond what's needed for the fix
- Changes to other issues (even if "quick")

#### Safety Rails

| Rule | Description |
|------|-------------|
| **Single issue only** | Don't scope-creep into other issues |
| **AC-driven** | Only do what acceptance criteria require |
| **Escalate ambiguity** | If ACs are unclear, ask before assuming |
| **Checkpoint commits** | Commit frequently so work isn't lost |
| **No force operations** | Never use `--force`, `--hard`, `-f` flags |

#### Merge Gate

**Before executing a merge command, Claude must verify all required reviews are complete.**

If the user requests merge but reviews are incomplete:

```
User: merge #178

Claude: PR #178 hasn't completed the full review cycle:
- Red Team: APPROVE ✅
- Gemini: BLOCKED (MCP disconnected)
- Bell Review: PENDING

Options:
1. "merge anyway" — Skip remaining reviews and merge now
2. "wait" — Complete reviews first
3. "skip [review]" — Skip specific review(s)

Which would you prefer?
```

**Rationale:** Even explicit user commands should be validated against process gates. The cost of asking is low; the cost of skipping reviews unintentionally is higher.

**Exception:** If the user has already acknowledged skipped reviews in the same conversation turn (e.g., "skip Gemini and merge"), proceed without re-asking.

#### Example Approval Dialog

```
User: Focus on issue #161

Claude: I'll enter Focus Mode for #161.

**Issue:** #161 — Experiment 01b: Angle-Dependent Measurement - Phase 2: Implementation
**Acceptance Criteria:**
- [ ] All new and existing tests pass in CI
- [ ] Simulation generates timestamped CSV output
- [ ] Results match P(+) = cos²(θ/2) within 3σ
- [ ] Edge cases pass: θ=0° → P(+)=1, θ=90° → P(+)=0.5, θ=180° → P(+)=0

**Branch:** sprint-2/phase-2-implementation
**Estimated scope:** 4 files (~250 lines)
**Review tier:** Tier 2 (code change)
**Bell Review:** Yes (critical path issue — say "skip Bell" to opt out)

**Required permissions:**
- File edits, Git operations, GitHub CLI, pytest

Approve to begin Focus Mode?
```

**User Response Options:**
- "Yes, begin Focus Mode" — Enters with stated scope
- "Yes, but change X" — Enters with modified scope
- "No, let's discuss first" — Does not enter Focus Mode
- Custom modifications to the plan

#### Exit Conditions

Focus Mode ends when:
1. PR is created and ready for merge
2. Issue is blocked and requires human decision
3. User requests to exit
4. Acceptance criteria cannot be met without scope expansion (escalate)

**On Exit:** Claude posts a summary with PR link, review status, and any blockers.

#### Example Exit Summary

```
## Focus Mode Complete

**Issue:** #161 — Experiment 01b: Phase 2 Implementation
**Duration:** ~2 hours

### Work Completed
- Extended qphysics.py with rotate_observable()
- Created simulate.py for angle-dependent measurements
- Added physics validation tests for 6 angles
- Generated CSV results in results/01b_angle_dependent/

### PR Created
- **#177** — Implement angle-dependent measurement simulation
  - Red Team: APPROVE
  - Gemini: APPROVE
  - Bell Review: PASS (see below)
  - All tests passing
  - Ready for your merge

### Bell Review Summary
| Criterion | Assessment |
|-----------|------------|
| Mathematical Rigor | ✅ Quaternion rotation correctly implements half-angle formula |
| Physical Insight | ✅ Edge cases (0°, 180°) handled with σ=0 special logic |
| Testability | ✅ Tests validate physics predictions, not just code paths |
| The "Why" Question | ✅ Code comments explain geometric interpretation |

### Acceptance Criteria Status
| AC | Status |
|----|--------|
| All tests pass | ✅ Done |
| CSV output generated | ✅ Done |
| Results within 3σ | ✅ Done |
| Edge cases pass | ✅ Done |

Focus Mode complete. Awaiting merge approval.
```
