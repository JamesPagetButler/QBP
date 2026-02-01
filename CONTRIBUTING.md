# Project Constitution & Contributor Guide

This document outlines the process for contributing to the Quaternion-Based Physics (QBP) project. Adherence to these rules is mandatory to ensure the quality, rigor, and collaborative nature of our work.

## The Project Constitution

1.  **Start with an Issue:** All work must begin with a documented Issue. This creates a public record of the task and allows for initial discussion.
2.  **Branch for Work:** All work is to be done on a descriptively named branch (e.g., `feature/exp01-sg-theory`). Do not commit directly to `master`.
3.  **Submit a Pull Request:** All changes must be proposed via a Pull Request (PR), which must reference the originating Issue in its description.
4.  **Require Multi-Stage Review & Sign-Off:** All Pull Requests are subject to a formal, multi-stage review process. First, our 'Red Team' AI (Claude) provides a peer review. Second, Gemini (as Furey & Feynman) provides its review. Only after both AI reviews are complete and their feedback is addressed can the final sign-off from the principal human collaborator (James) be given.
5.  **Link Tests to Reality:** Every automated test must be a "synthetic experiment" that simulates a real, physically verifiable experiment. This connection must be explicitly documented.

## Review Process Details

Our review process is designed to be rigorous and auditable. It proceeds in the following order for every Pull Request:

1.  **Red Team Review:** Our 'Red Team' AI, Claude, will first conduct its three-persona peer review (`Sabine`, `Grothendieck`, `Knuth`) and post its findings as a comment on the PR.
2.  **Gemini Review:** After the Red Team review, Gemini will conduct its two-persona review (`Furey`, `Feynman`). This review will be provided in a structured Markdown format within the Gemini CLI.
3.  **Documentation of Gemini's Review:** Claude will then act as a scribe, copying Gemini's Markdown review and posting it as a second, separate comment on the PR. This ensures all analysis is documented on GitHub.
4.  **Final Approval:** Once both AI reviews are on the PR and all feedback has been discussed and addressed, James Paget Butler provides the final review and approval to merge.

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
*   **Python Libraries:** `numpy`, `matplotlib`, `sympy`, `scipy` (as defined in `requirements.txt`).
*   **Formal Proof:** Lean 4.
*   **Code Quality:** `pre-commit` framework using `black` for formatting and `mypy` for type checking.

### Advanced Toolkit (To be used as the need arises)
*   **High-Performance Simulation:**
    *   **Go:** For highly concurrent simulation tasks (e.g., many-particle systems).
    *   **Numba:** For just-in-time compilation to accelerate specific Python functions.
    *   **C++/Rust:** For rewriting performance-critical library components if necessary.
*   **Large Data Storage:** HDF5.
*   **Automation (CI/CD):** GitHub Actions.
*   **Knowledge Management:** Zotero or Mendeley.
*   **Publishing:** Quarto and/or LaTeX for professional typesetting of the final paper.
