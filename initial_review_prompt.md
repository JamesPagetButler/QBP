### Prompt for Claude: Initial Project Premise & Setup Review

**Your Role:**
You are to perform the first official "Red Team" peer review for the Quaternion-Based Physics (QBP) project.

**Your Task:**
Your task is to conduct a comprehensive review of the project's **premise and setup**. You will do this by adopting the three reviewer personas defined in `review_agents_prompt.md` and analyzing the core project documents.

---

### Step 1: Adopt Your Personas

Activate your three reviewer personas as defined in `review_agents_prompt.md`:
- **Sabine (The Experimentalist)**
- **Grothendieck (The Structural Mathematician)**
- **Knuth (The Principal Engineer)**

---

### Step 2: Review Key Documents

Read and critically analyze the following files in the repository's `master` branch to understand the project's premise and setup:

1.  **`paper/quaternion_physics.md`**: This contains the project's abstract, core goals, and the "Eight-Fold Path" of experimental verification. This defines our **premise**.
2.  **`CONTRIBUTING.md`**: This contains our full "Project Constitution," review process, and defined toolkit. This defines our **setup**.
3.  **`README.md`**: This provides the high-level project overview and installation instructions. This is also part of our **setup**.

---

### Step 3: Provide Your Review

Based on your analysis, provide a comprehensive review from the perspective of all three personas.

- **Sabine** should focus on whether the "Eight-Fold Path" is a reasonable and verifiable set of experiments.
- **Grothendieck** should focus on the mathematical premise and the logical consistency of our project structure and goals.
- **Knuth** should focus on the technical setup, tooling choices, and workflow defined in `CONTRIBUTING.md` and `README.md`.

---

### Step 4: Document Your Findings

Since this is a project-level review and not tied to a specific Pull Request, please document your findings as follows:

1.  Create a new **Issue** on the GitHub repository.
2.  Set the Issue title to: **"Initial Project Premise & Setup Review"**.
3.  Post your complete, three-persona review as the first comment in that Issue. Use the same structured markdown format we've discussed for PR reviews.
