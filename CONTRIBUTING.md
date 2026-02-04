# Project Constitution & Contributor Guide

This document outlines the process for contributing to the Quaternion-Based Physics (QBP) project. Adherence to these rules is mandatory to ensure the quality, rigor, and collaborative nature of our work.

## The Project Constitution

1.  **Start with an Issue:** All work must begin with a documented Issue. This creates a public record of the task and allows for initial discussion.
2.  **Branch for Work:** All work is to be done on a descriptively named branch (e.g., `feature/exp01-sg-theory`). Do not commit directly to `master`.
3.  **Submit a Pull Request:** All changes must be proposed via a Pull Request (PR), which must reference the originating Issue in its description.
4.  **Require Multi-Stage Review & Sign-Off:** All Pull Requests are subject to a formal, multi-stage review process. First, our 'Red Team' AI (Claude) provides a peer review. Second, Gemini (as Furey & Feynman) provides its review. Only after both AI reviews are complete and their feedback is addressed can the final sign-off from the principal human collaborator (James) be given.
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

3.  **Loop:** We then begin the next sprint for Experiment N+1.

This ensures our theory evolves based on our experimental results.

---

## The 5-Phase Experimental Lifecycle

Every experiment on our roadmap follows a structured 5-phase lifecycle. This ensures rigorous validation before publication.

### Phase Overview

| Phase | Goal | Output | Success Criteria |
|-------|------|--------|------------------|
| **Phase 1: Ground Truth** | Research and document expected results | `research/NN_..._expected_results.md` | Complete specification with quantitative predictions |
| **Phase 2: Implementation** | Build code and run synthetic experiment | `qphysics.py` updates, `/results` data | Results within 3σ of ground truth |
| **Phase 3: Visualization** | Visualize results, verify success | `vpython` animations, Manim videos | Visual confirmation of Phase 2 success |
| **Phase 4: Formal Proof** | Mathematically prove implementation | `.lean` proof files in `/proofs` | All theorems verified by Lean |
| **Phase 5: Publication** | Document and communicate success | `paper/quaternion_physics.md` section | Complete, reviewed documentation |

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
│  └── Decision Gate:                                       │          │
│      "Do all Lean proofs successfully verify?"            │          │
│              │                                            │          │
│         [NO] └──► Create issue, loop back to Phase 2 ─────┘          │
│              │                                                       │
│        [YES] ↓                                                       │
│  Phase 5: Publication                                                │
│  └── Output: paper/quaternion_physics.md section                     │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### Phase Details

#### Phase 1: Ground Truth & Planning

**Goal:** Research and document the real-world results we need to match.

**Tasks:**
- Review existing literature and experimental data
- Define quantitative predictions with error bounds
- Specify acceptance criteria (e.g., "within 3σ of expected value")
- Identify required tools or framework extensions

**Output:** `research/NN_experiment_expected_results.md`

**Exit Criteria:** Ground truth document reviewed and approved.

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

#### Phase 4: Formal Verification

**Goal:** Mathematically prove that the successful implementation (Phase 2) is logically sound according to our axioms.

**Tasks:**
- Define formal statements of theorems in Lean 4 based on the quaternionic model.
- Write proofs connecting implementation's logic to our axioms.
- Verify all proofs compile without errors in Lean 4.

**Decision Gate:**
> "Do all Lean proofs successfully verify the theoretical claims of the implementation?"

-   **If NO:** Document the flaw (e.g., a mathematical inconsistency), create a new issue for theoretical re-evaluation or implementation fix, and **loop back to Phase 2 (Implementation & Execution)** to address the underlying problem.
-   **If YES:** Proceed to Phase 5.

**Output:** Completed `.lean` proof files in `/proofs` directory.

---

#### Phase 5: Publication

**Goal:** Document and communicate our confirmed and verified success.

**Tasks:**
- Write a new, detailed section for `paper/quaternion_physics.md` for this experiment.
- Include visualizations from Phase 3.
- Reference formal proofs from Phase 4.
- Update `DESIGN_RATIONALE.md` with key decisions and insights gained.

**Output:** Finalized, reviewed section in the main paper, ready for broader dissemination.

**Exit Criteria:** Section reviewed by Red Team and Gemini; merged to master.

---

### Issue Structure for 5-Phase Lifecycle

Each experiment requires 5 issues, one per phase:

| Issue Title Pattern | Labels |
|---------------------|--------|
| `Experiment N: Name - Phase 1: Ground Truth` | `type: experiment`, `phase: ground-truth` |
| `Experiment N: Name - Phase 2: Implementation` | `type: experiment`, `phase: implementation` |
| `Experiment N: Name - Phase 3: Visualization` | `type: experiment`, `phase: visualization` |
| `Experiment N: Name - Phase 4: Formal Proof` | `type: experiment`, `phase: proof` |
| `Experiment N: Name - Phase 5: Publication` | `type: experiment`, `phase: publication` |

Phase 2 is blocked by Phase 1. Phase 3 is blocked by Phase 2. And so on.

---

## Review Process Details

Our review process is designed to be rigorous and auditable.

### Reviewing Agents

| Agent | Persona(s) | Tool/CLI | Role |
|-------|-----------|----------|------|
| **Claude** | Sabine (Experimentalist) | Claude Code CLI | Red Team - tests, feasibility, measurements |
| **Claude** | Grothendieck (Mathematician) | Claude Code CLI | Red Team - rigor, axioms, structure |
| **Claude** | Knuth (Engineer) | Claude Code CLI | Red Team - code quality, efficiency, docs |
| **Gemini** | Furey (Algebraist) | Gemini CLI | Theory - division algebras, elegance |
| **Gemini** | Feynman (Physicist) | Gemini CLI | Theory - physical intuition, clarity |

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

1.  **Red Team Review:** Claude conducts three-persona peer review (`Sabine`, `Grothendieck`, `Knuth`) and posts findings as a PR comment with summary.
2.  **Gemini Review:** Gemini conducts two-persona review (`Furey`, `Feynman`) in structured Markdown format within Gemini CLI.
3.  **Documentation of Gemini's Review:** Claude acts as scribe, copying Gemini's Markdown review and posting it as a separate PR comment.
4.  **Final Approval:** James reviews all summaries, asks clarifying questions if needed, then issues explicit merge command.

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
*   `/experiments`: Contains the Python scripts for our "synthetic experiments," which use the `qphysics.py` library to test our hypotheses. (Phase 2 output)
*   `/tests/physics`: Contains physics validation tests for each experiment. (Phase 2 output)
*   `/proofs`: Contains Lean 4 formal proof files. (Phase 4 output)
*   `/results`: Contains the timestamped output logs from our synthetic experiments. This directory is in `.gitignore` and is not committed to the repository.
*   `/reviews`: Contains locally saved review files from both Claude and Gemini before they are posted to a PR. This directory is in `.gitignore`.
*   `/prompts`: Contains detailed prompt files for instructing AI agents. This directory is in `.gitignore`.
*   `/docs`: Contains general project documentation, schemas, and agent definitions.
    *   `multi_agent_git_coordination.md`: Mandatory git workflow protocols for Claude and Gemini.
