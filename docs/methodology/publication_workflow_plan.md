# Plan for Schema-Driven Publication Workflow

This document outlines the plan to integrate the new `physics_paper_schema.md` into our project's lifecycle. The objective is to standardize and elevate the quality of our main scientific paper, `paper/quaternion_physics.md`, by ensuring it is written according to established best practices.

---

## 1. Objective

To transform our Phase 5 (Publication) from a simple documentation task into a rigorous, schema-driven scientific writing process that is seamlessly integrated with the outputs of Phases 1-4.

---

## 2. Integration with the 5-Phase Experimental Lifecycle

The new schema directly leverages the artifacts produced in each phase of our experimental lifecycle.

| Phase | Input Artifact(s) | Output for Paper (Section) |
|-------|-------------------|----------------------------|
| **Phase 1: Ground Truth** | `research/NN_..._expected_results.md` | `3. Methodology`, `4. Results` (Ground Truth Summary) |
| **Phase 2: Implementation** | `experiments/NN_.../simulate.py` | `3. Methodology` |
| **Phase 3: Analysis** | `analysis/NN_.../analysis_report.md` | `4. Results` (Data & Tables), `5. Discussion` (Interpretation) |
| **Phase 4: Formal Proof** | `proofs/QBP/Experiments/NN_....lean` | `Appendices` |
| **Phase 5: Publication** | All of the above | A new, schema-compliant section in `paper/quaternion_physics.md` |

### Reframing Phase 5: "Schema-Driven Synthesis"

Phase 5 is no longer just "writing up" the results. It is a **synthesis** task where the outputs of the preceding four phases are woven into a coherent narrative that conforms *exactly* to the `physics_paper_schema.md`.

**The new workflow for a Phase 5 task is as follows:**

1.  **Gather Artifacts**: Collect the approved `research`, `analysis`, and `proof` documents for the completed experiment.
2.  **Draft 'Results' Section**: Transcribe the quantitative comparison tables and visualizations from the `analysis_report.md` into the "Results" section of the paper, following the schema.
3.  **Draft 'Discussion' Section**: Synthesize the "Interpretation" and "Conclusion" from the `analysis_report.md` into the "Discussion" section of the paper.
4.  **Update 'Methodology' Section**: Ensure the methods used in the experiment are accurately described in the "Methodology" section.
5.  **Review and Refine**: The entire new section is reviewed for narrative flow, clarity, and adherence to the schema and style guide.

---

## 3. Agent Roles in the Publication Workflow

This workflow leverages the distinct strengths of each agent.

### **Gemini (The Analyst & Drafter)**

*   **Role**: Gemini's strength is in programmatic execution and data analysis. As the primary agent for Phases 2 & 3, it generates the core, data-driven content for the paper.
*   **Phase 5 Task**:
    1.  Upon initiation of a Phase 5 task, Gemini's first step is to **draft the raw "Results" and "Discussion" subsections** for the specific experiment.
    2.  This draft will be a direct, structured transcription from its own `analysis_report.md` into the format required by the main paper's schema.
    3.  This provides the initial, data-grounded text that Claude will then refine.

### **Claude (The Scribe & Narrator)**

*   **Role**: Claude's strength is in language, structure, and maintaining a consistent narrative voice.
*   **Phase 5 Task**:
    1.  Take Gemini's raw draft of the "Results" and "Discussion" sections.
    2.  **Weave it into the main `paper/quaternion_physics.md` document.** This involves:
        *   Ensuring the tone is consistent with the rest of the paper.
        *   Checking for clarity, conciseness, and adherence to the style guide.
        *   Managing the bibliography and ensuring all new claims are properly cited.
        *   Formatting all tables, figures, and equations according to the schema.
    3.  Claude is the final integrator, responsible for the overall coherence and professional quality of the document.

### **Human (The Strategist & Interpreter)**

*   **Role**: The human collaborator provides the high-level scientific narrative, strategic direction, and final sign-off.
*   **Phase 5 Task**:
    1.  Review the integrated sections from Claude.
    2.  Provide the key insights and interpretations for the "Discussion" section, ensuring the "so what?" is clear.
    3.  Write or approve the final "Conclusion" and "Future Work" sections, which require strategic vision for the project.
    4.  Give the final approval before the PR is merged.

---

## 4. Actionable Plan to Refactor `paper/quaternion_physics.md`

To bring our existing work into conformance with the new schema, the following one-time project will be executed.

1.  **Create a New GitHub Issue**:
    *   **Title**: `refactor: Align paper/quaternion_physics.md with new schema`
    *   **Body**: "This issue tracks the one-time effort to restructure the main research paper according to the `docs/schemas/physics_paper_schema.md`. This will involve reorganizing existing content and integrating the detailed analysis from the recent Experiment 01 sprint retrofit."
    *   **Labels**: `housekeeping`, `documentation`

2.  **Execution Steps for the Issue**:

    *   **Sub-task 1: Restructure Skeleton**:
        *   **Agent**: Claude
        *   **Action**: Create a new branch. Edit `paper/quaternion_physics.md` to create the top-level headings defined in the schema (Abstract, Introduction, Theoretical Framework, etc.). Move existing content into the most appropriate new sections.

    *   **Sub-task 2: Integrate Experiment 01 Results**:
        *   **Agent**: Gemini
        *   **Action**: Following the new workflow, draft the "Results" and "Discussion" subsections for Experiment 01, using the `analysis/01_stern_gerlach/analysis_report_*.md` as the source. Provide this as a text block.

    *   **Sub-task 3: Synthesize and Refine**:
        *   **Agent**: Claude
        *   **Action**: Take the draft from Gemini and integrate it into the restructured paper. Ensure the narrative is clean and all figures/tables are captioned and referenced correctly.

    *   **Sub-task 4: Final Review**:
        *   **Agent**: Human
        *   **Action**: Review the fully refactored paper for scientific accuracy, clarity, and narrative coherence. Request final edits as needed.

    *   **Sub-task 5: Create PR**:
        *   **Agent**: Gemini/Claude
        *   **Action**: Once all edits are complete, create a Pull Request for the final, refactored paper.

---

## 5. Conclusion

This plan provides a clear path to elevate our scientific publication process. By making Phase 5 a structured synthesis task and clarifying agent roles, we can ensure our main paper is a rigorous, readable, and professional representation of our research, directly and traceably linked to the experimental work that underpins it.
