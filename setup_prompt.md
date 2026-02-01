### Prompt for Red Team AI Assistant

**Project Context:**
We are setting up a collaborative research project to develop a quaternion-based formulation of physics. The project is in its initial setup phase. A directory structure has already been created (`/paper`, `/src`, `/experiments`, `/proofs`), and a `git init` command has been run.

**Our Collaboration Rules (The "Project Constitution"):**
We have agreed on the following five rules for our development workflow:
1.  **Start with an Issue:** All work must begin with a documented Issue.
2.  **Branch for Work:** All work is to be done on a descriptively named branch.
3.  **Submit a Pull Request:** Changes are proposed via a Pull Request that references the originating Issue.
4.  **Require Universal Sign-Off:** The PR must be reviewed and approved by all three collaborators before being merged into the `main` branch.
5.  **Link Tests to Reality:** Every automated test must simulate a real, physically verifiable experiment, with the connection explicitly documented.

**Your Immediate Task:**
Your task is to create the configuration files that will help us document and enforce these rules. Please perform the following two actions:

**1. Create the `CONTRIBUTING.md` File:**
Create a markdown file named `CONTRIBUTING.md` in the project's root directory. This file should serve as a guide for all collaborators. It must contain two main sections:

*   A "Project Constitution" Section: This section should clearly list the five collaboration rules mentioned above.
*   A "Branch Protection Setup" Section: This section must provide a clear, step-by-step guide for a repository administrator on how to set up branch protection rules on GitHub to enforce our constitution. The guide should instruct them to:
    *   Navigate to Settings > Branches and add a rule for the `main` branch.
    *   Enable "Require a pull request before merging."
    *   Enable "Require approvals" and set the required number of approvals to **3**.

**2. Set up `pre-commit` Hooks:**
Create a YAML file named `.pre-commit-config.yaml` in the project's root directory. This file will be used by the `pre-commit` framework to run checks before any code is committed. Configure it with the following two hooks:

*   **black:** The standard Python code formatter.
*   **mypy:** The standard Python static type checker.

Please provide the complete contents of both the `CONTRIBUTING.md` and `.pre-commit-config.yaml` files.
