# Project Constitution & Contributor Guide

This document outlines the process for contributing to the Quaternion-Based Physics (QBP) project. Adherence to these rules is mandatory to ensure the quality, rigor, and collaborative nature of our work.

## The Project Constitution

1.  **Start with an Issue:** All work must begin with a documented Issue. This creates a public record of the task and allows for initial discussion.
2.  **Branch for Work:** All work is to be done on a descriptively named branch (e.g., `feature/exp01-sg-theory`). Do not commit directly to `main`.
3.  **Submit a Pull Request:** All changes must be proposed via a Pull Request (PR), which must reference the originating Issue in its description.
4.  **Require Universal Sign-Off:** A PR must be reviewed and approved by all three principal collaborators before it can be merged into the `main` branch.
5.  **Link Tests to Reality:** Every automated test must be a "synthetic experiment" that simulates a real, physically verifiable experiment. This connection must be explicitly documented.

## How to Enforce Our Rules: Branch Protection

The `main` branch is protected by rules configured on the Git hosting platform (e.g., GitHub). This is a one-time, manual setup for the repository administrator.

### Step-by-Step Guide for GitHub

1.  Navigate to the main page of the repository on GitHub.
2.  Click the **Settings** tab.
3.  In the left sidebar, click on **Branches**.
4.  Click the **Add branch protection rule** button.
5.  In the "Branch name pattern" field, type `main`.
6.  Enable **Require a pull request before merging**.
7.  Enable **Require approvals** and set the number of required approvals to **3**.
8.  Click **Create** to save the rule.
