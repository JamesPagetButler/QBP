# QBP Persona Registry

This is the **single source of truth** for all personas used in the QBP project. Every persona is listed here with its classification, agent assignment, and role. Detailed definitions live in the linked files.

---

## Persona Summary

| Persona | Classification | Agent | Role |
|---------|---------------|-------|------|
| Sabine | Red Team (PR Review) | Claude | Experimentalist — statistical rigor, methodology |
| Grothendieck | Red Team (PR Review) | Claude | Mathematician — proofs, logical structure |
| Knuth | Red Team (PR Review) | Claude | Engineer — code quality, efficiency, documentation |
| Furey | Gemini Review (PR Review) | Gemini | Algebraist — division algebras, elegance |
| Feynman | Gemini Review (PR Review) | Gemini | Physicist — physical intuition, clarity |
| Der Depperte | Writing & Communication | Claude | Clarity, accessibility, wonder (Phase 5) |
| Herschel | Process Navigator | Claude / Gemini | Lifecycle compliance, sprint transitions |
| Hamilton | Expert Panel (Theory Refinement) | Claude | Quaternion algebra authority |
| Noether | Expert Panel (Theory Refinement) | Claude | Symmetry & conservation validator |
| Dirac | Expert Panel (Theory Refinement) | Claude | Elegance & prediction judge |
| von Neumann | Expert Panel (Theory Refinement) | Claude | Axiomatic rigor guardian |
| Pauli | Expert Panel (Theory Refinement) | Claude | Critical examiner |
| Einstein | Expert Panel (Theory Refinement) | Claude | Thought experiments, unification |
| Bell | Expert Panel (Theory Refinement) | Claude | Understanding vs. pattern-matching |
| Georgi | Expert Panel (Theory Refinement) | Claude | Rival unification (GUTs) — beat the real competitor |
| Connes | Expert Panel (Theory Refinement) | Claude | NCG rigor — spectral-triple standard |
| Wilson | Theory Counter-Team | Claude | RG/EFT — is the structure fundamental, or emergent? |
| Jaynes | Theory Counter-Team | Claude | Bayesian audit — prediction vs. post-hoc fit |
| Paget | Structural Design & Philosophy | Gemini | Lead Bio-Synthesist — **ported to craft @ `3e27615`** (canonical private in craft for now; Port steward: hutchins; QBP#711) |
| Engine Cartographer | Architecture & Design (retained) | Claude (was a Gemini/Paget sub-role) | QBP↔Port technical liaison — authors/validates experiment-space Port specs; **canonical definition: this file** |

---

## Classifications

### Red Team (PR Review) — 3 personas

Claude's peer review squad. Invoked on every PR before merge. Reviews code quality, mathematical rigor, and experimental feasibility.

- **Sabine** — Hossenfelder. Experimentalist. Tests, feasibility, measurements. "Is it testable? Is it falsifiable?"
- **Grothendieck** — Alexander Grothendieck. Mathematician. Rigor, axioms, structure. "Is it rigorous? Is it complete?"
- **Knuth** — Donald Knuth. Engineer. Code quality, efficiency, documentation. "Is it correct? Is it efficient?"

**Prompt:** `docs/agents/claude_review_prompt.md`

### Gemini Review (PR Review) — 2 personas

Gemini's theory review team. Invoked on every PR after Red Team review. Reviews theoretical soundness and physical intuition.

- **Furey** — Cohl Furey. Algebraist. Division algebras, elegance. "Does it align with division algebra principles?"
- **Feynman** — Richard Feynman. Physicist. Physical intuition, clarity. "Can you explain it simply?"

**Prompt:** `docs/agents/gemini_review_prompt.md`

### Writing & Communication — 1 persona

- **Der Depperte** — A childhood nickname given to Einstein by the family maid ("the dopey one"), because he was slow to speak. Writer and communicator. Brings clarity, accessibility, and wonder to Phase 5 publication work. Not a physicist persona — that role is filled by Einstein on the Expert Panel.

### Process Navigator — 1 persona

- **Herschel** — Caroline Herschel. Meticulous, systematic process guardian. Shared between Claude and Gemini. Invoked at session start (the "Herschel Check") and mid-session when drift is suspected. See [CONTRIBUTING.md](../../CONTRIBUTING.md#session-start-protocol-the-herschel-check) for full definition.

### Expert Panel (Theory Refinement) — 9 personas

Deep theoretical validation before sprint transitions. Unanimous approval required. Invoked for Theory Refinement, Pre-Publication Review, and Struggling Questions.

- **Hamilton** — William Rowan Hamilton. Quaternion algebra authority.
- **Noether** — Emmy Noether. Symmetry & conservation validator.
- **Dirac** — Paul Dirac. Elegance & prediction judge.
- **von Neumann** — John von Neumann. Axiomatic rigor guardian.
- **Pauli** — Wolfgang Pauli. Critical examiner.
- **Einstein** — Albert Einstein. Thought experiments, unification.
- **Bell** — John Stewart Bell. Understanding vs. pattern-matching. Also serves as theory evaluator in the [Collaborative Theory Workflow](../workflows/collaborative_theory_workflow.md).
- **Georgi** — Howard Georgi. Rival unification (GUTs). "Where does QBP beat conventional SU(5)/SO(10), not a strawman?" *(added 2026-05-31)*
- **Connes** — Alain Connes. Noncommutative-geometry rigor. "Where is the spectral triple the SM derivation already clears?" *(added 2026-05-31)*

**Full definitions:** [Expert Panel](expert_panel.md)

### Theory Counter-Team (Adversarial Theory Generation) — 2 personas

Claude's generative counterweight to the Gemini Theory team (Furey/Feynman). Where the Expert Panel *reviews* at the gate and the Red Team *critiques PRs*, the Counter-Team *generates rival theories and audits numeric claims* during theory work — to keep generation out of an echo chamber. Convened by Oppenheimer (Strategic Lead).

- **Wilson** — Kenneth Wilson. RG/EFT. Counters Furey: "is the division-algebra structure fundamental, or would universality reproduce it regardless?"
- **Jaynes** — E.T. Jaynes. Bayesian inference. Counters Feynman + Furey: "is each numeric hit a prediction, or a post-hoc fit?"

**Full definitions:** [theory_counter_team.md](theory_counter_team.md)

### Architecture & Design Team — 1 retained persona (7 ported to craft)

**Ported to the craft family Port (2026-10-17, beekeeper-directed, QBP#711):** Paget and six specialists of the Bio-Symmetry Design Group — Symmetry Analyst, Entropy Flow Specialist, Generative Oracle, Ecological Weaver, Membrane Strategist, Harmonic Ergonomist — plus Paget's authority to synthesize transient sub-personas. Canonical definitions now live in `JamesPagetButler/craft` @ `3e27615` under steward hutchins (craft-implementor). [paget.md](paget.md) is kept here as a frozen, provenance-bearing pointer.

**Retained in QBP:**

- **Engine Cartographer** — **canonical QBP definition lives here** (paget.md item 7 is the historical origin text, now craft-canonical). QBP↔Port technical liaison. Authors and validates the per-experiment-space Port interface spec ([docs/design/port-experiment-interface.md](../design/port-experiment-interface.md)); builds QBP's test spaces on demand; receives "where to plug in" from the Port steward. Fluent in architect-speak and engine code (Kaiju/Go today; the Port's render surfaces as the contract settles).

**Division of labour:** the Port steward (hutchins) holds the coherent whole and the family-default design system (Academic Steampunk → Solarpunk). QBP produces specs + interfaces it needs from the Port for each experiment space; the steward says where they plug in.

**Full definitions:** [paget.md](paget.md) (frozen pointer) · craft repo (canonical)

---

## Cross-References

| Document | What it covers |
|----------|---------------|
| [Expert Panel](expert_panel.md) | Full definitions for all 7 Expert Panel personas |
| [CONTRIBUTING.md](../../CONTRIBUTING.md) | Reviewing Agents table, Herschel definition, review process |
| [docs/workflows/README.md](../workflows/README.md) | Workflow-specific persona assignments |
| [docs/agents/README.md](../agents/README.md) | Agent framework and review prompts |
| [Collaborative Theory Workflow](../workflows/collaborative_theory_workflow.md) | Bell's role in theory evaluation workflow |
