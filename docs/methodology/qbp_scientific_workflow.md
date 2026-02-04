# QBP Scientific Workflow: Project-Specific Best Practices

This document provides a practical guide for applying the project's defined "5-Phase Experimental Lifecycle" (as outlined in `CONTRIBUTING.md`) and integrating it with general scientific method best practices. It clarifies agent responsibilities, documentation standards, and decision gates to ensure rigorous, reproducible, and insightful experimental work.

---

## 1. Core Principles

Our project's scientific workflow is built upon the following principles:

*   **Transparency & Traceability**: Every step from hypothesis to conclusion must be documented and auditable.
*   **Rigor & Reproducibility**: Experiments must be designed and executed such that their results are reliable and can be independently verified.
*   **Systematic Validation**: Continuous comparison of simulation outputs against clearly defined theoretical ground truths.
*   **Iterative Refinement**: Acknowledge that scientific progress is iterative; feedback from analysis and formal verification drives refinement.
*   **Agent-Human Collaboration**: Leverage AI agents for execution, analysis, and scribing, while maintaining human oversight for critical decision-making and scientific interpretation.

---

## 2. Detailed Application of the 5-Phase Experimental Lifecycle

This section elaborates on each phase, providing concrete steps and requirements.

### Phase 1: Ground Truth & Planning

**Goal:** Formally define the expected experimental outcome based on established theory or prior knowledge. This is our "hypothesis" in a quantitative form.

**Tasks:**

1.  **Issue Creation**: Start with a GitHub Issue (e.g., `Experiment NN: [Name] - Phase 1: Ground Truth`) with the `type: experiment` and `phase: ground-truth` labels.
2.  **Literature Review**: Research and cite relevant literature, theoretical derivations, or empirical data.
3.  **Formal Derivation**: Provide a step-by-step derivation of the expected quantitative predictions. This must be clear enough for independent verification.
4.  **Acceptance Criteria**: Explicitly state the expected quantitative predictions, including units, error bounds, and the tolerance for simulation results (e.g., "results must be within 3 standard deviations of the mean expected value").
5.  **Output**: Create `research/NN_experiment_expected_results.md`.

    *   **Content Requirements for `research/NN_experiment_expected_results.md`**:
        *   **Experiment Title & Number**: e.g., `Experiment 02: Angle-Dependent Measurement`
        *   **Abstract/Summary**: Briefly describe the phenomenon and the expected outcome.
        *   **Theoretical Background**: Contextualize the experiment within QBP and broader physics.
        *   **Ground Truth Derivation**: Provide the full mathematical derivation (e.g., `P(+) = (1 + cos(theta))/2`), clearly stating all assumptions and steps. Use LaTeX for equations.
        *   **Quantitative Predictions**: List specific predicted values, functions, or distributions against which simulation results will be compared.
        *   **Acceptance Criteria**: Reiterate the tolerance for success (e.g., 3σ, 5% deviation).
        *   **References**: Cite all sources.
6.  **Review**: The `research/NN_experiment_expected_results.md` document must undergo review by Claude (as Grothendieck and Sabine) and Gemini (as Furey and Feynman) for theoretical soundness, clarity, and quantitative accuracy.

**Exit Criteria**: Ground truth document `research/NN_experiment_expected_results.md` is complete, reviewed, and approved via a PR.

### Phase 2: Implementation & Execution

**Goal:** Build the simulation code that tests the hypothesis defined in Phase 1 and generate raw experimental data.

**Tasks:**

1.  **Issue Creation**: `Experiment NN: [Name] - Phase 2: Implementation`.
2.  **Code Development**: Extend `src/qphysics.py` if necessary. Create simulation script `experiments/NN_name/simulate.py`. Ensure code is clean, modular, and adheres to project style guides (checked via `pre-commit`).
3.  **Testing**: Create corresponding tests in `tests/physics/test_name.py`.
4.  **Execution**: Run the simulation. The simulation script *must* output raw, machine-readable data to a timestamped file within `results/NN_experiment_name/`. Examples: CSV, JSON. The output should include all relevant measurements and parameters.
5.  **Agent Role (Gemini)**: Gemini is primarily responsible for this phase, ensuring the simulation runs correctly and outputs data in the expected format.

**Output**:
*   Updated `src/qphysics.py` (if needed)
*   `experiments/NN_name/simulate.py`
*   `tests/physics/test_name.py`
*   Raw data files in `results/NN_experiment_name/` (e.g., `results/02_angle_test/angle_test_data_YYYY-MM-DD_HH-MM-SS.csv`).

**Exit Criteria**: All physics tests pass; simulation runs successfully; raw data is generated and stored in the `/results` directory.

### Phase 3: Visualization & Analysis (The Debug Loop)

**Goal:** Programmatically and visually compare simulation results against the Phase 1 ground truth, interpret deviations, and draw initial conclusions. This is where we confirm if our simulation matches our theory.

**Tasks:**

1.  **Issue Creation**: `Experiment NN: [Name] - Phase 3: Visualization & Analysis`.
2.  **Data Ingestion**: Programmatically load the raw data from `results/NN_experiment_name/`.
3.  **Ground Truth Loading**: Programmatically parse the quantitative predictions from `research/NN_experiment_expected_results.md`. (This might require developing parsing utilities).
4.  **Comparative Analysis (Gemini's Role)**:
    *   **Automated Comparison**: Gemini will write and execute analysis scripts (e.g., Python, Jupyter Notebooks in `analysis/NN_experiment_name/`) that perform statistical comparisons between the simulation results and the ground truth.
    *   **Deviation Metrics**: Calculate relevant deviation metrics (e.g., statistical significance, average percentage error, maximum deviation in sigma).
    *   **Visualization Generation**: Generate plots, charts, and animations (e.g., using `matplotlib`, `vpython`, `Manim`) that visually represent the comparison.
5.  **Analysis Report**: Gemini will generate a detailed markdown analysis report (e.g., `analysis/NN_experiment_name/analysis_report_YYYY-MM-DD_HH-MM-SS.md`) that includes:
    *   Summary of findings.
    *   Comparison tables/graphs (simulation vs. ground truth).
    *   Discussion of deviations and their potential causes.
    *   Conclusion: Does the simulation match the ground truth within tolerance?
6.  **Human Interpretation**: The human collaborator reviews Gemini's analysis report and visualizations for intuitive understanding and agreement.
7.  **Decision Gate**: Based on Gemini's programmatic analysis and human interpretation, confirm if the results match ground truth within defined tolerance.
    *   **If NO**: Document the discrepancies, create a new issue for debugging (revisiting Phase 1 or 2), and **loop back**.
    *   **If YES**: Proceed to Phase 4.

**Output**:
*   Analysis scripts/notebooks in a new `analysis/NN_experiment_name/` directory.
*   Generated visualizations (plots, animations) in `src/viz/`.
*   Detailed markdown analysis report in `analysis/NN_experiment_name/`.

**Exit Criteria**: Comprehensive analysis report confirms simulation results match ground truth within tolerance, reviewed and approved via a PR.

### Phase 4: Formal Verification

**Goal:** Mathematically prove that the successful implementation (Phase 2) is logically sound according to our axioms, complementing the empirical validation from Phase 3.

**Tasks:**

1.  **Issue Creation**: `Experiment NN: [Name] - Phase 4: Formal Proof`.
2.  **Lean Proof Development**: Define formal statements of theorems in Lean 4 based on the quaternionic model. Write proofs connecting the implementation's logic to our axioms.
3.  **Verification**: Ensure all proofs compile without errors in Lean 4.
4.  **Agent Role (Gemini/Claude)**: Gemini can assist in drafting formal statements, while Claude (as Grothendieck) provides rigorous review.

**Output**: Completed `.lean` proof files in `/proofs` directory.

**Exit Criteria**: All Lean proofs successfully verify the theoretical claims, reviewed and approved via a PR.

### Phase 5: Publication

**Goal:** Document and communicate our confirmed and verified experimental success to a broader audience.

**Tasks:**

1.  **Issue Creation**: `Experiment NN: [Name] - Phase 5: Publication`.
2.  **Paper Section**: Write a new, detailed section for `paper/quaternion_physics.md` for this experiment.
3.  **Integration**: Integrate key findings from the Phase 3 analysis report, and reference formal proofs from Phase 4. Include relevant visualizations from `src/viz/`.
4.  **Design Rationale Update**: Update `paper/DESIGN_RATIONALE.md` with key decisions and insights gained during the experiment's lifecycle.
5.  **Agent Role (Claude)**: Claude (as scribe) ensures all documentation is coherent, well-formatted, and accurate.

**Output**: Finalized, reviewed section in `paper/quaternion_physics.md` and updated `paper/DESIGN_RATIONALE.md`.

**Exit Criteria**: Section reviewed by Red Team and Gemini; merged to master.

---

## 3. Integrating New Workspace Directories

The `workspace/` directories serve to enhance isolation for concurrent agent activities.

*   **`workspace/gemini/`**: Gemini will clone the QBP repository here for all its active tasks related to Phase 2, Phase 3 analysis, and Phase 4 proof drafting. This ensures its working copy is separate from Claude's or the human's main repository.
*   **`workspace/claude/`**: Claude will clone the QBP repository here for all its review (Red Team) and scribing activities.
*   **`workspace/human_review/`**: The human collaborator will maintain a clean clone of the `master` (or `main`) branch here, primarily for reviewing PRs and the overall project state without local agent interference. This should be regularly synchronized with `origin/master`.

---

## 4. Agent-Specific Responsibilities within the Workflow

### Gemini (Furey & Feynman Personas)

*   **Primary Executor**: Phases 2 (Implementation) and 3 (Automated Analysis/Visualization).
*   **Proof Drafter**: Assists in Phase 4 by proposing formal statements or proof strategies.
*   **Scientific Investigator**: Uses Feynman persona to provide physical intuition and Furey persona for algebraic elegance during Phase 1 research and Phase 3 analysis.
*   **Analysis Report Generation**: Generates comprehensive markdown analysis reports (Phase 3).
*   **PR Creation**: Creates PRs for completed work in Phase 1, 2, 3, and 4.
*   **Git Workflow Adherence**: Strictly follows the Gemini Git Workflow outlined in `docs/multi_agent_git_coordination.md`.

### Claude (Sabine, Grothendieck, Knuth Personas)

*   **Primary Reviewer (Red Team)**: Reviews PRs for all phases, focusing on experimental feasibility (Sabine), mathematical rigor (Grothendieck), and code quality/documentation (Knuth).
*   **Scribe**: Posts Gemini's reviews and summaries to PRs.
*   **Documentation Maintainer**: Assists in Phase 5 documentation and updates `DESIGN_RATIONALE.md`.
*   **Issue Management**: Creates follow-up issues based on review feedback.
*   **Git Workflow Adherence**: Strictly follows the Claude Git Workflow outlined in `docs/multi_agent_git_coordination.md`.

---

## 5. Addressing the Current Methodology Gaps (Issue #101)

### 5.1 Standardizing Ground Truth Documentation (Phase 1)

*   **Action**: For every new experiment, `research/NN_experiment_expected_results.md` MUST be created before any code is written. This document will contain the full mathematical derivation and quantitative predictions.
*   **Retroactive Action (for Experiment 02)**: Create `research/02_angle_test_expected_results.md` documenting the derivation of `P(+) = (1 + cos(theta))/2` and the specific predictions for the angles tested. This will be a new Phase 1 task.

### 5.2 Establishing Structured Analysis (Phase 3)

*   **Action**: A new `analysis/` top-level directory will be created to house automated analysis scripts and generated analysis reports. Each experiment will have its own subdirectory (e.g., `analysis/02_angle_test/`).
*   **Action**: Gemini will be tasked with creating analysis scripts that:
    *   Load raw data from `/results`.
    *   Load ground truth from `/research`.
    *   Perform statistical comparisons.
    *   Generate visualizations.
    *   Generate a markdown analysis report.
*   **Retroactive Action (for Experiments 01 & 02)**: Create dedicated Phase 3 tasks to generate comprehensive analysis reports and visualizations for `Experiment 01 (Stern-Gerlach)` and `Experiment 02 (Angle-Dependent Measurement)`, comparing their respective `/results` data to the `research/` ground truths.

---

## Conclusion

By implementing this refined workflow, we aim to elevate the scientific rigor, reproducibility, and collaborative efficiency of the QBP project. Adherence to these practices will transform our raw data into validated scientific insights, making our work more impactful and understandable.
