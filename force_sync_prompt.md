### Prompt for Claude: Force-Sync Local Files to Remote Branch

**Goal:**
The primary goal is to get the complete, correct content of three key setup files (`README.md`, `LICENSE`, `CONTRIBUTING.md`) into a new branch on the GitHub repository. Previous attempts at this workflow have failed, so follow these instructions with extreme precision.

**Your Immediate Task:**
Your task is to execute a sequence of commands that will create a new branch, add the correct file contents to it, and push it to the remote repository.

---

### Step 1: File Content

Here is the **exact and complete** content for each of the three files.

#### **Content for `README.md`:**
```markdown
# QBP: A Quaternion-Based Physics Project

[![Project Status: Active – Initial Setup Phase](https://img.shields.io/badge/status-active-success.svg)](https://github.com/JamesPagetButler/QBP)

This repository is the home of a collaborative research project to develop a coherent physical formalism derived from the mathematical properties of quaternion algebra. Our guiding hypothesis is that the fundamental laws of nature can be expressed as a direct consequence of this algebraic structure.

This project is a collaboration between James Paget Butler and the AI agents Gemini (acting as Furey and Feynman) and Claude (acting as our Red Team).

## Getting Started

Follow these instructions to set up a local development environment.

### Prerequisites

- Python 3.10+
- Git
- [Go](https://go.dev/doc/install) (for advanced simulation work)
- [pre-commit](https://pre-commit.com/#installation)

### Installation

1.  **Clone the repository:**
    ```bash
    git clone https://github.com/JamesPagetButler/QBP.git
    cd QBP
    ```

2.  **Install Python dependencies:**
    ```bash
    pip install -r requirements.txt
    ```

3.  **Set up Git hooks:**
    This will install the pre-commit hooks defined in `.pre-commit-config.yaml`, which automatically format and check our code.
    ```bash
    pre-commit install
    ```

## Usage

The core work of this project is divided into theoretical development and computational experiments.

-   **Theoretical Work:** The central paper and ongoing theoretical discussions are in the `/paper` directory.
-   **Computational Experiments:** Each of the eight experiments on our roadmap has a dedicated directory within `/experiments`. To run a simulation, navigate to the relevant directory and execute the Python script (e.g., `python experiments/01_stern_gerlach/simulate.py`).

## Contributing

This project has a strict, collaborative workflow. All contributors **must** read and adhere to the rules outlined in our [**CONTRIBUTING.md**](CONTRIBUTING.md) file before starting work.

## License

This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.
```

#### **Content for `LICENSE`:**
```markdown
MIT License

Copyright (c) 2026 James Paget Butler

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

#### **Content for `CONTRIBUTING.md`:**
```markdown
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
```

---

### Step 2: Git Commands

Execute these steps in order. This is the most critical part of the task.

1.  Ensure you are in the root directory of the `QBP` Git repository.
2.  Run `git checkout master` and `git pull` to ensure you have the latest version of the main branch.
3.  Create a new branch with the command: `git checkout -b chore/force-sync-all-files`
4.  **Overwrite** the local files `README.md`, `LICENSE`, and `CONTRIBUTING.md` with the full content provided above in Step 1.
5.  Add these files to the staging area with the command: `git add README.md LICENSE CONTRIBUTING.md`
6.  Commit the changes with the command: `git commit -m "chore: force sync of all setup files"`
7.  Push the new branch to the remote repository with the command: `git push origin chore/force-sync-all-files`

---

### Step 3: Confirmation

Once you have successfully pushed the branch `chore/force-sync-all-files` to the GitHub repository, please confirm that the task is complete. Do not proceed to create a Pull Request. A human collaborator will handle the PR creation from your pushed branch.
