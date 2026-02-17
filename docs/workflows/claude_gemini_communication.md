# Claude–Gemini Communication Protocol

*Structured protocols for multi-AI collaboration, ensuring human-readable outputs and rigorous disagreement resolution.*

---

## Overview

Claude and Gemini collaborate across PR reviews, theory discussions, and design debates. This document defines mandatory protocols to ensure every exchange is:

1. **Human-readable** — James can follow the reasoning without reading raw tool logs
2. **Core-premise-focused** — Grounded in whether QBP produces observable deviations from standard QM
3. **Verifiable** — Algebraic claims include show-your-work evidence
4. **Persistent** — Key decisions recorded for cross-session continuity

---

## 1. Human-Readable Summary Protocol

Every Claude–Gemini exchange must produce a summary posted where James can read it.

| Exchange Type | Where to Post | Format |
|---------------|---------------|--------|
| PR reviews | PR comments | Persona-attributed Markdown |
| Theory discussions | Issue comments or `workspace/theory_discussions/` | Structured Markdown with conclusion |
| Design debates | Issue comments + `record_decision` | Markdown summary + recorded decision |
| Brainstorm sessions | Issue comments or conversation | Numbered options with synthesis |

**Minimum summary structure:**

```markdown
## [Exchange Type]: [Topic]

**Participants:** [personas involved]
**Core Premise Relevance:** [1-2 sentences — see §2]

### Key Points
- [Point 1]
- [Point 2]

### Conclusion / Decision
[What was decided or concluded]

### Open Items
- [Anything unresolved]
```

---

## 2. Core Premise Focus Filter

Each exchange must include a section answering: **"How does this advance or challenge the core QBP premise?"**

The core premise: *Quaternionic quantum mechanics produces predictions that can be experimentally distinguished from standard complex QM.*

| Exchange Type | Core Premise Question |
|---------------|----------------------|
| PR reviews | "Does this simulation correctly test quaternionic predictions?" |
| Theory work | "Does this analysis support or refute observable quaternionic effects?" |
| Design decisions | "Does this choice enable rigorous premise testing?" |
| Research | "Does this finding strengthen or weaken the case for quaternionic deviations?" |

If an exchange is purely infrastructural (CI fix, formatting, etc.), the Core Premise Relevance section should state: "Infrastructure — no direct premise impact."

---

## 3. Structured Disagreement Resolution

When Claude and Gemini disagree on physics or mathematics:

### Protocol

```
1. IDENTIFY — State the disagreement precisely
   "Claude claims X. Gemini claims Y. They cannot both be true."

2. SHOW WORK — Both sides must provide explicit derivation
   - Algebraic steps, not just conclusions
   - Cite axioms or sources used

3. VERIFY — Run an independent check
   Options (in order of preference):
   a. Symbolic computation (SymPy, Lean)
   b. Numerical test (Python, specific values)
   c. 2×2 matrix representation (for SU(2) claims)
   d. Literature reference (with exact equation/page)

4. RESOLVE — Post resolution with evidence
   "Resolution: [X/Y/neither] is correct because [evidence]."

5. RECORD — If the resolution changes understanding, record it:
   - Update knowledge graph if a claim changes status
   - Use Gemini's record_decision tool for architectural decisions
   - Post to the relevant issue/PR
```

### Example (from PR #287)

```
DISAGREEMENT: Gemini claimed the coupling equation ε·sin(kd·sin(θ))
contained an algebraic error. Claude disagreed.

SHOW WORK: Both posted their derivations.

VERIFY: Independent numerical evaluation at θ=π/4 confirmed
Claude's derivation matched the simulation output.

RESOLVE: Gemini's concern was based on a different normalisation
convention. No error in the implementation.

RECORD: Posted as PR comment with full working.
```

---

## 4. Session Persistence

### What to Record

| Tool | When | What |
|------|------|------|
| `record_decision` | After design debates, architecture choices | Decision + rationale + alternatives |
| `debate_turn` | During extended theory discussions | Multi-turn debate with history |
| Knowledge graph | After theory conclusions | New claims, updated evidence chains |
| Issue comments | After any substantive exchange | Human-readable summary |

### Cross-Session Context

At the start of sessions involving Gemini, check for relevant prior context:

```bash
# List recent decisions
# (via MCP: list_decisions tool)

# Check for active debate sessions
# (via MCP: list_sessions tool)
```

---

## 5. Communication Templates

### Theory Review Template

```markdown
## Theory Review: [Topic]

**Question:** [What's being investigated]

### Gemini Analysis (Furey/Feynman)
[Gemini's analysis]

### Claude Critique (Red Team)
[Claude's response]

### Resolution
[Agreed conclusion, or structured disagreement if unresolved]

### Core Premise Relevance
[How this affects the QBP premise]

### Action Items
- [ ] [Follow-up 1]
- [ ] [Follow-up 2]
```

### PR Physics Review Template

```markdown
## Physics Review: PR #NNN

### Code Reading
[What the code does, physically]

### Physics Assessment
[Is the physics correct? Show-your-work for any claims]

### AC Verification
[Standard AC verification table]

### Core Premise Relevance
[Does this correctly test quaternionic predictions?]

### Verdict
[APPROVE / REQUEST CHANGES / COMMENT]
```

### Premise Check Template

```markdown
## Premise Check: [Sprint/Phase Context]

### Current Evidence
**For observable quaternionic effects:**
- [Evidence 1]

**Against observable quaternionic effects:**
- [Evidence 1]

### Gaps
- [What we don't know yet]

### Next Experiment Priorities
1. [Most important next test]
2. [Second priority]
```

---

## 6. Prescriptive Collaboration Patterns

### Pattern 1: Pre-Implementation Critique

**When:** Before implementing any non-trivial design decision.
**Tool:** `critique_my_approach` via Gemini MCP (`thinking=true`)

| Step | Actor | Action |
|------|-------|--------|
| 1 | Claude | Drafts approach (plan, architecture, algorithm) |
| 2 | Gemini | Critiques — finds flaws, edge cases, alternatives |
| 3 | Claude | Integrates feedback, proceeds to implementation |

**Skip when:** Single-line fixes, obvious bugs, tasks where James gave specific instructions.

**Precedent:** PR #340 — Gemini's critique changed single-file to split nearfield/farfield results.

### Pattern 2: Structured Debate for Contested Physics

**When:** A review finding is ambiguous, or two valid interpretations exist.
**Tool:** `debate_turn` with session history

| Step | Actor | Action |
|------|-------|--------|
| 1 | Claude | Identifies contested finding, opens debate session |
| 2 | Gemini | Responds (Furey or Feynman persona) |
| 3 | Both | Multiple rounds until convergence |
| 4 | Escalate | If no convergence after 3 rounds → present to James as tie-breaker |

### Pattern 3: Session-Based Iterative Reviews

**When:** Multi-round PRs where Gemini has previously reviewed.
**Tool:** `review_document` with `session_id` for continuity

| Round | What Happens |
|-------|-------------|
| 1 | Gemini reviews PR diff. Claude records returned `session_id`. |
| 2+ | Gemini re-reviews with same `session_id` — can reference Round 1 findings. |

**Advantage:** Without session continuity, Gemini reviews each round from scratch, losing context about what it previously flagged.

### Pattern 4: Human Tie-Breaking (James-in-the-Loop)

**When:** Claude and Gemini genuinely disagree on a significant finding after 3 debate rounds.

| Escalation Trigger | Action |
|-------------------|--------|
| Disagreement after 3 debate rounds | Present both positions to James |
| Finding would change sprint direction | Present impact analysis to James |
| Acceptance criterion is contested | Present evidence for both sides to James |

**Design principle:** Not a bottleneck — routine reviews proceed without James. Tie-breaking triggers only on genuine disagreement or large-impact findings.

**Output:** Decision recorded via `record_decision` or issue comment.

### Pattern 5: Interactive Question Sessions

**When:** Claude needs James's input on a decision.
**Tool:** `AskUserQuestion` with multi-select options

James can:
- **Refine the question** — ask Claude to rephrase
- **Request more context** — ask for more information before answering
- **Reject the framing** — "wrong question, the real question is..."

Questions are a conversation, not a one-shot form.

---

## References

- [TEAMS.md](../../TEAMS.md) — Persona definitions
- [CONTRIBUTING.md](../../CONTRIBUTING.md) — Review process
- [Review Tiers](review_tiers.md) — Tier system and BLOCKING criteria
- PR #287 — Motivating example for disagreement resolution
- [Issue #346](https://github.com/JamesPagetButler/QBP/issues/346) — Living issue for workflow refinement
