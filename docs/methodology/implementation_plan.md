# Implementation Plan for Enhanced Scientific Workflow in QBP

This document outlines a phased approach to integrate the "QBP Scientific Workflow: Project-Specific Best Practices" into our project, addressing the methodology gaps identified in Issue #101. The plan considers our multi-agent protocol, human and AI limitations, and existing project processes.

---

## 1. Guiding Principles for Implementation

*   **Iterative Rollout**: Start with existing experiments (01 and 02) to establish the new workflow, then apply to new experiments.
*   **Agent-Assisted, Human-Driven**: Leverage AI agents for automation and analysis, but critical scientific decisions and interpretations remain with the human collaborator.
*   **Minimize Overhead**: Integrate new steps as seamlessly as possible into existing issue and PR workflows.
*   **Transparency**: All changes to methodology and process will be documented and communicated.

---

## 2. Updates to Project Processes

### 2.1 Project Planning & Issue Creation

*   **Update Issue Templates**: Modify GitHub Issue templates (`.github/ISSUE_TEMPLATE/experiment.yml`) to include new fields for:
    *   **Hypothesis/Problem Statement**: Clear, testable statement.
    *   **Ground Truth Document Reference**: Link to `research/NN_..._expected_results.md`.
    *   **Acceptance Criteria**: Explicit metrics for success, including deviation tolerance (e.g., "results within 3σ of expected").
*   **New Issue Label**: Introduce a `status: needs-analysis` label for experiments that have run but require Phase 3 analysis.
*   **Phased Issue Creation**: Reinforce the creation of 5 distinct issues per experiment (Phase 1-5), ensuring Phase 1 (Ground Truth) is always completed and approved before Phase 2.

### 2.2 Experiment Lifecycle (Reinforcing `CONTRIBUTING.md` & New Steps)

*   **Phase 1 (Ground Truth)**:
    *   **Human/Gemini**: Human collaborator initiates research, Gemini assists with literature search and initial derivation.
    *   **Gemini's Task**: Generate `research/NN_experiment_expected_results.md` content, ensuring all requirements (derivation, quantitative predictions, acceptance criteria) are met.
    *   **Claude's Task**: Review `research/NN_experiment_expected_results.md` (Grothendieck for rigor, Sabine for physical consistency).
*   **Phase 2 (Implementation)**:
    *   **Gemini's Task**: Develop simulation code, ensure raw output is machine-readable (CSV/JSON preferred) and saved to `results/NN_experiment_name/`.
*   **Phase 3 (Visualization & Analysis)**:
    *   **New Directory**: Create top-level `/analysis` directory, with subdirectories for each experiment (e.g., `analysis/02_angle_test/`).
    *   **Gemini's Task**:
        *   Develop analysis script/notebook in `analysis/NN_experiment_name/` to:
            *   Load raw data from `/results`.
            *   Parse ground truth from `research/NN_experiment_expected_results.md`.
            *   Perform statistical comparison, calculate deviation metrics.
            *   Generate visualizations (`src/viz/`).
        *   Generate comprehensive markdown analysis report (`analysis/NN_experiment_name/analysis_report_YYYY-MM-DD_HH-MM-SS.md`).
    *   **Human's Role**: Review Gemini's report and visualizations for scientific interpretation and decision-making at the "Decision Gate."
    *   **Claude's Task**: Review Phase 3 output (analysis scripts, visualizations, reports) for clarity, correctness, and adherence to scientific communication standards (Knuth).
*   **Phase 4 (Formal Verification)**:
    *   **Gemini's Task**: Draft Lean 4 formal statements and proofs.
    *   **Claude's Task**: Rigorously review Lean 4 proofs for logical soundness (Grothendieck).
*   **Phase 5 (Publication)**:
    *   **Claude's Task**: Scribe Gemini's output and assist with updating `paper/quaternion_physics.md` and `paper/DESIGN_RATIONALE.md`.

### 2.3 Multi-Agent Protocol Integration

*   **Dedicated Workspaces**: Agents will strictly use their assigned `workspace/gemini` and `workspace/claude` directories for their respective tasks to prevent local conflicts.
*   **Clear Handoffs**: Emphasize explicit handoff messages, especially after Phase 1 and Phase 3 approvals, to ensure the next agent knows when to begin.
*   **Review Roles**: Reinforce existing review roles as outlined in `CONTRIBUTING.md`. Gemini for scientific analysis (Furey/Feynman), Claude for Red Team review (Sabine/Grothendieck/Knuth).

---

## 3. Retroactive Application to Existing Experiments

### 3.1 Experiment 01: Stern-Gerlach

*   **Status**: Ground truth (`research/01_stern_gerlach_expected_results.md`) exists. Raw results (`results/01_stern_gerlach/`) exist.
*   **Action**: Create a new GitHub Issue: `Experiment 01: Stern-Gerlach - Phase 3: Visualization & Analysis (Retrofit)`.
    *   **Gemini's Task**: Develop analysis script in `analysis/01_stern_gerlach/` and generate a markdown analysis report comparing existing results to the existing ground truth.
    *   **Claude's Task**: Review the analysis report and visualizations.

### 3.2 Experiment 01b: Angle-Dependent Measurement

*   **Status**: Ground truth (`research/01b_angle_dependent_expected_results.md`) exists. Raw results (`results/01b_angle_dependent/`) exist.
*   **Note**: Originally planned as "Experiment 02", this was reclassified as Experiment 01b since it extends the Stern-Gerlach experiment to arbitrary angles (see #179). The original `02_angle_test/` prototype remains for historical reference.
*   **Action 1**: Create a new GitHub Issue: `Experiment 01b: Angle-Dependent Measurement - Phase 1: Ground Truth (Retrofit)`.
    *   **Gemini's Task**: Create `research/01b_angle_dependent_expected_results.md` by formally deriving `P(+) = (1 + cos(theta))/2` and listing quantitative predictions.
    *   **Claude's Task**: Review the new ground truth document.
*   **Action 2**: Once Phase 1 (Retrofit) is approved, create a new GitHub Issue: `Experiment 01b: Angle-Dependent Measurement - Phase 3: Visualization & Analysis (Retrofit)`.
    *   **Gemini's Task**: Develop analysis script in `analysis/01b_angle_dependent/` and generate a markdown analysis report comparing existing results to the newly documented ground truth.
    *   **Claude's Task**: Review the analysis report and visualizations.

---

## 4. Addressing Limitations

*   **Human Limitations**: Overcome by clear documentation, agent assistance, and structured decision gates. The `human_review` workspace provides a clean environment for human oversight.
*   **AI Limitations (e.g., Creative Derivations, Intuition)**:
    *   **Gemini**: Can assist in drafting derivations (Phase 1) and complex analysis scripts (Phase 3) but requires human oversight for scientific judgment.
    *   **Claude**: Excels in structured review and feedback but human input is critical for interpreting nuanced scientific insights.
*   **CLI Limitations**:
    *   **Verbose Output**: Agents will prioritize concise summaries and file generation over raw CLI output for complex tasks.
    *   **Interactive vs. Automated**: Design workflows to be non-interactive where possible; human intervention will be required for interactive decision gates.

---

## 5. Next Steps & Timeline (High-Level)

1.  **Immediate**: Create the new `/analysis` top-level directory (DONE).
2.  **Week 1**: Implement Retroactive Application for Experiment 01b Phase 1 (Ground Truth).
3.  **Week 2**: Implement Retroactive Application for Experiment 01 and Experiment 01b Phase 3 (Analysis).
4.  **Ongoing**: Apply new workflow to all future experiments, starting from Phase 1.
