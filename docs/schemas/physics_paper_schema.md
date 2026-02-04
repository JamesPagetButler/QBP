# Schema for QBP Research Papers

This document provides a formal schema and style guide for the main research paper, `paper/quaternion_physics.md`. It is based on best practices from established physics journals (e.g., those following the AIP Style Manual) and is tailored to the specific needs of the QBP project. Adherence to this schema ensures our work is presented with scientific rigor, clarity, and consistency.

---

## 1. Paper Structure: The Hourglass Model

Our paper will follow the "hourglass" structure, starting broad, narrowing to specifics, and broadening again at the end.

```
┌───────────────────┐  ◄──  Broad Scope
│     Abstract      │
│   Introduction    │
├───────────────────┤
│ Theoretical       │  ◄──  Narrow Scope (Specifics of QBP)
│ Framework         │
│    Methodology    │
│      Results      │
│     Discussion    │
├───────────────────┤
│     Conclusion    │  ◄──  Broad Scope
│    Future Work    │
└───────────────────┘
```

---

## 2. Section-by-Section Schema

### **Title Block**
*   **Title**: Clear, concise, and descriptive of the paper's core contribution.
*   **Authors**: List of contributors (human and AI), with affiliations.
*   **Date**: Date of the last significant revision.

### **Abstract**
*   **Length**: One paragraph, under 250 words.
*   **Content**: A dense summary of the entire paper. Must state:
    1.  The fundamental problem being addressed (e.g., "re-evaluating quantum mechanics using a quaternionic framework").
    2.  The methodology used (e.g., "a series of synthetic experiments validated against formal proofs").
    3.  The key results (e.g., "successfully replicated N foundational experiments...").
    4.  The principal conclusion and its significance.
*   **Timing**: This section should be written *last*, after all other sections are complete.

### **1. Introduction**
*   **Purpose**: To provide context and motivation for the reader.
*   **Content**:
    1.  **General Context**: Start broadly, introducing the area of physics the paper contributes to (e.g., quantum mechanics, foundational physics).
    2.  **Problem Statement**: Clearly articulate the specific problem or gap this research addresses (e.g., "the non-intuitive nature of complex Hilbert spaces...").
    3.  **Historical Background**: Briefly discuss previous relevant work and how this project relates to it.
    4.  **Proposed Solution**: Introduce the QBP framework as the proposed solution/investigation.
    5.  **Roadmap**: Briefly outline the structure of the rest of the paper.

### **2. Theoretical Framework**
*   **Purpose**: To present the core axioms and mathematical machinery of the QBP framework.
*   **Content**:
    1.  **Quaternionic Algebra**: A brief primer on quaternion mathematics as it applies to the framework.
    2.  **The QBP Axioms**: A formal, numbered list and description of the core axioms (State, Observables, Evolution, Measurement).
    3.  **Key Derivations**: Show derivations of key concepts that stem from the axioms (e.g., the formula for expectation value, probability calculations).
*   **Style**: This section must be mathematically precise. All non-standard symbols must be defined.

### **3. Methodology**
*   **Purpose**: To describe *how* the research was conducted, ensuring reproducibility.
*   **Content**:
    1.  **The 5-Phase Experimental Lifecycle**: Describe our project's specific methodology, from Ground Truth to Publication. This section justifies the rigor of our approach.
    2.  **Synthetic Experiment Setup**: Detail the computational environment (Python version, key libraries like NumPy/SciPy, `numpy-quaternion`).
    3.  **Formal Verification Setup**: Detail the formal methods environment (Lean 4 version).
    4.  **Data Analysis Protocol**: Explain the process of comparing raw results from `/results` to the ground truth from `/research`, including the statistical methods used (e.g., binomial deviation, sigma calculation).

### **4. Results**
*   **Purpose**: To present the findings of each experiment, objectively and without interpretation.
*   **Structure**: This section should be divided into subsections, one for each experiment (e.g., "4.1 Experiment 01: Stern-Gerlach", "4.2 Experiment 02: Angle-Dependent Measurement").
*   **Content for each subsection**:
    1.  **Objective**: State the specific hypothesis tested in the experiment.
    2.  **Ground Truth Summary**: Briefly summarize the expected outcome as defined in the corresponding `research/` document.
    3.  **Data Presentation**: Present the key findings from the simulation. This *must* include:
        *   A quantitative comparison table summarizing the expected vs. measured results, including deviation metrics (e.g., σ-value). This table should be sourced from the `analysis_report_*.md`.
        *   Visualizations (plots, charts) with clear captions. All figures must be referenced in the text.
    4.  **Outcome**: A clear statement of whether the experiment PASSED or FAILED the acceptance criteria.

### **5. Discussion**
*   **Purpose**: To interpret the results and explain their significance.
*   **Structure**: Should mirror the structure of the "Results" section, with a subsection for each experiment.
*   **Content for each subsection**:
    1.  **Interpretation**: What do the results from this experiment mean? For example, for Stern-Gerlach, "The successful validation (0.4140σ deviation) provides strong evidence that the QBP framework's axiomatic treatment of measurement correctly reproduces spin quantization..."
    2.  **Connection to Theory**: Explicitly link the experimental outcome back to the Theoretical Framework (Section 2).
    3.  **Limitations & Discrepancies**: Honestly discuss any limitations of the simulation or any results that were close to the acceptance boundary.
    4.  **Emergent Phenomena**: Discuss any unexpected or emergent behaviors observed (relevant for the "Theory Refinement Stage" of our lifecycle).

### **6. Conclusion**
*   **Purpose**: To summarize the paper's contribution and provide a final, high-level takeaway.
*   **Content**:
    1.  **Restate Thesis**: Briefly restate the paper's main thesis or objective.
    2.  **Synthesize Findings**: Summarize the key findings from the "Results" and "Discussion" sections. Do not introduce new information.
    3.  **Overall Significance**: State the broader impact of the work. What has been learned? How does this advance our understanding?
*   **Style**: As with the introduction, this section should be written for a slightly broader audience.

### **7. Future Work**
*   **Purpose**: To outline the next steps for the project.
*   **Content**:
    1.  **Immediate Next Steps**: Reference the next experiment(s) on the project roadmap.
    2.  **Long-Term Vision**: Discuss open questions, potential extensions of the theory, and long-term research goals.

### **Acknowledgments**
*   **Purpose**: To credit individuals and organizations who contributed support, ideas, or resources.

### **References**
*   **Purpose**: To provide a complete bibliography of all cited work.
*   **Style**: Adhere to the AIP style for citations and formatting. A bibliography management tool (e.g., Zotero) should be used to maintain this section.

### **Appendices**
*   **Purpose**: To provide supplementary material that is too detailed or lengthy for the main body.
*   **Potential Content**:
    *   Detailed mathematical derivations.
    *   Source code for key algorithms (if not available elsewhere).
    *   Full, unabridged formal proofs from Lean 4.

---

## 3. Style Guide

*   **Clarity & Conciseness**: Be direct. Avoid jargon where simpler terms suffice. Each sentence should have a clear purpose.
*   **Voice**: Use the active voice where possible ("We simulated..." instead of "A simulation was run..."). It is more direct and engaging.
*   **Tense**: Use past tense for describing your methods and results ("We ran the simulation...", "The results showed..."). Use present tense for general truths and conclusions ("The QBP framework provides...", "Our results indicate...").
*   **Figures & Tables**: All figures and tables must have a numbered caption that clearly explains what is being shown. They must be referenced in the text (e.g., "as shown in Fig. 3...").
*   **Equations**: All significant equations should be on their own line and numbered. Use LaTeX for formatting.
*   **Citations**: Use the AIP citation style (numerical, e.g., `[1]`).
