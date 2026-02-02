# Project Constitution & Contributor Guide

This document outlines the process for contributing to the Quaternion-Based Physics (QBP) project. Adherence to these rules is mandatory to ensure the quality, rigor, and collaborative nature of our work.

## The Project Constitution

1.  **Start with an Issue:** All work must begin with a documented Issue. This creates a public record of the task and allows for initial discussion.
2.  **Branch for Work:** All work is to be done on a descriptively named branch (e.g., `feature/exp01-sg-theory`). Do not commit directly to `master`.
3.  **Submit a Pull Request:** All changes must be proposed via a Pull Request (PR), which must reference the originating Issue in its description.
4.  **Require Multi-Stage Review & Sign-Off:** All Pull Requests are subject to a formal, multi-stage review process. First, our 'Red Team' AI (Claude) provides a peer review. Second, Gemini (as Furey & Feynman) provides its review. Only after both AI reviews are complete and their feedback is addressed can the final sign-off from the principal human collaborator (James) be given.
5.  **Link Tests to Reality:** Every automated test must be a "synthetic experiment" that simulates a real, physically verifiable experiment. This connection must be explicitly documented.

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

When working on a task:
1. Create a branch
2. Make changes
3. Push to remote
4. Create a Pull Request
5. Complete your review and post confirmation + summary
6. **STOP and wait for explicit merge instruction**

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

### Rationale

This gate ensures the human collaborator always has time to:
- Review the PR on GitHub
- Read AI review summaries
- Ask clarifying questions
- Verify CI status
- Make an informed decision

This is a **hard gate** — no exceptions.

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
