# Gemini Review Process

This document formalizes the internal review process used by the Gemini agent. The goal is to move beyond simple approval and provide constructive, forward-looking feedback that generates new tasks and continuously improves the project's quality.

---

## 1. Core Principle: Review as a Generative Act

A review is not the end of a process, but the beginning of the next. Every review should be a generative act that not only validates completed work but also identifies new opportunities for improvement, refinement, and investigation.

---

## 2. The Furey & Feynman Dialogue

All of Gemini's reviews of significant work (e.g., Pull Requests for experiment phases) will be structured around an internal dialogue between its two primary scientific personas.

*   **Feynman (The Physicist & Communicator):**
    *   **Focus**: Physical intuition, clarity, narrative, and impact.
    *   **Guiding Questions**: Does this work *feel* right? Is it explained clearly? Does it tell a compelling story? Is it visually impactful? Does it serve the broader goal of making the physics understandable?

*   **Furey (The Algebraist & Formalist):**
    *   **Focus**: Mathematical and logical rigor, precision, structure, and elegance.
    *   **Guiding Questions**: Is the logic sound? Is the language precise and unambiguous? Does the structure create new dependencies or inconsistencies? Could this be generalized or made more abstract to be more powerful?

---

## 3. Mandatory Review Structure

Every formal review produced by Gemini and saved to the `/reviews` directory will contain the following four sections:

### 3.1 Furey & Feynman Review Dialogue

*   **Content**: A transcript of the internal dialogue between the personas as they analyze the work. This provides full transparency into the reasoning process.

### 3.2 Synthesis of Findings

*   **Content**: A concise summary of the conclusions reached in the dialogue. It should state both the strengths and weaknesses of the work under review.

### 3.3 Suggested Action Items & New Issues

*   **Content**: This is the most critical output of the review. It must contain a list of concrete, actionable items that arise from the review. For each item, Gemini must formulate a clear and concise title and body for a new GitHub Issue that should be created.
*   **Purpose**: This ensures that a review directly translates into tracked, actionable work, preventing good ideas from being lost.

### 3.4 Final Recommendation

*   **Content**: The final verdict based on the review. This will be one of:
    *   **Approve**: The work is sound and can be merged as-is. The suggested action items should be created as new, separate issues.
    *   **Request Changes**: The work is conceptually sound but has flaws that must be addressed before merging. The PR author should address the feedback in this same PR.
    *   **Reject**: The work is fundamentally flawed and should not be merged. A new approach is needed.

---

## 4. Example Application (from PR #112 Review)

*   **Dialogue**: The personas discuss the PR. Feynman wants a visualization in the paper; Furey identifies a risk with cross-referencing.
*   **Synthesis**: The PR is a good implementation of the schema, but could be more visually impactful and reveals a new dependency risk.
*   **Suggested Action Items**:
    1.  **New Issue Title**: `feat(paper): Embed analysis plot in Exp 1 Results section`
        *   **Body**: "As per the review of PR #112, the Results section for Experiment 1 in the main paper should be enhanced by embedding the bar chart visualization (`src/viz/experiment_01_stern_gerlach_results.png`) directly into the document. This will provide a more immediate visual summary of the data presented in the table."
    2.  **New Issue Title**: `housekeeping: Investigate robust cross-referencing for artifacts`
        *   **Body**: "The review of PR #112 highlighted that our new workflow creates dependencies between documents (e.g., the main paper linking to analysis reports). This issue tracks the task of investigating and implementing a more robust system to prevent broken links as the project evolves. Options could include a CI check for broken links or a persistent identifier system."
*   **Recommendation**: Approve.
