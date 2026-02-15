# Review Tiers Reference

*Comprehensive guide to the QBP tiered review system. Single source of truth for tier selection, checklists, tool configuration, and BLOCKING criteria.*

**Living document:** This will be refined after Sprint 3 completes with a full sprint's worth of interactions. See #346 for ongoing improvements.

---

## Tier Selection Decision Tree

```
Is this a design decision before implementation begins?
  YES → Tier 0 (Pre-Implementation Critique)

Does this change physics formalism, axioms, or formal proofs?
  YES → Tier 3 (Deep Review)

Does this change code behavior, tests, or results?
  YES → Tier 2 (Standard Review)

Is it docs, formatting, comments, or process only?
  YES → Tier 1 (Light Review)

Default → Tier 2
James can upgrade or downgrade any PR's tier.
```

---

## Tier 0: Pre-Implementation Critique

**When:** Before implementing any non-trivial design decision.

**Purpose:** Catch flaws, edge cases, and missed alternatives *before* code is written. Cheaper to fix a plan than refactor an implementation.

| Aspect | Detail |
|--------|--------|
| **Trigger** | Claude is about to implement something non-trivial |
| **Reviewer** | Gemini via `critique_my_approach` |
| **Tool config** | `thinking=true` |
| **Blocking?** | No — advisory only |
| **Output** | Critique informs implementation; not posted as formal review |

**Precedent:** PR #340 — Gemini's critique changed single-file to split nearfield/farfield results, improved grid assertion from `np.allclose` to `np.array_equal`.

**When to skip:** Single-line fixes, obvious bugs, tasks where James gave specific instructions.

---

## Tier 1: Light Review

**When:** Changes that don't affect behavior — docs, typos, formatting, comments, process updates.

| Aspect | Detail |
|--------|--------|
| **Trigger** | PR opened with docs-only changes |
| **Reviewer** | Single AI review (Red Team OR Gemini, not both) |
| **Tool config** | `thinking=false` for Gemini |
| **Blocking?** | Only if factually wrong |
| **Label** | `tier-1-review` |
| **Human Visual Review** | Not required (no visual artifacts to inspect) |

### Tier 1 Checklist

- [ ] Content is factually accurate
- [ ] No broken links or rendering issues
- [ ] Consistent with existing documentation
- [ ] AC verification (if issue linked)

---

## Tier 2: Standard Review

**When:** Changes that affect behavior but not core theory — bug fixes, new tests, tooling, housekeeping code.

| Aspect | Detail |
|--------|--------|
| **Trigger** | PR with code, test, or config changes |
| **Reviewers** | Red Team (Sabine, Grothendieck, Knuth) + Gemini (Furey, Feynman) |
| **Sequence** | Red Team first, then Gemini (Gemini sees Red Team context) |
| **Tool config** | Gemini: `thinking=true`, `session_id` for multi-round PRs |
| **Blocking?** | Yes — FAIL items block merge |
| **Label** | `tier-2-review` |
| **Human Visual Review** | **Required** — see below |

### Tier 2 Checklist

- [ ] Logic is correct (no bugs introduced)
- [ ] Tests cover the change
- [ ] No security vulnerabilities (OWASP top 10)
- [ ] Code style consistent with codebase
- [ ] AC verification (if issue linked)
- [ ] **Human Visual Review completed** (James inspects outputs)

### Human Visual Review (Tier 2+)

After AI reviews complete, AI prepares visual artifacts for James:

| Artifact | When to include |
|----------|----------------|
| Regenerated plots with PR's changes | Any PR touching physics or results |
| Side-by-side numerical comparison tables | Any PR changing computation outputs |
| Before/after screenshots | Any PR changing visualization |
| Traffic-light AC status table | All Tier 2+ PRs |

James inspects these visually. His pattern recognition catches anomalies that sequential text-based AI review misses (proven: unit issue, results format issue). Findings from Human Visual Review are BLOCKING.

---

## Tier 3: Deep Review

**When:** Changes that affect physics formalism, axioms, formal proofs, or architecture. New experiment phases.

| Aspect | Detail |
|--------|--------|
| **Trigger** | PR with theory, proofs, or architectural changes |
| **Reviewers** | Red Team → Gemini (strictly sequential) |
| **Sequence** | Red Team first; Gemini reviews with Red Team findings as context |
| **Tool config** | Gemini: `thinking=true`, `session_id` always |
| **Blocking?** | Yes — strict. All findings require resolution. |
| **Label** | `tier-3-review` |
| **Human Visual Review** | **Required** — James inspects all visual outputs |

### Tier 3 Checklist

- [ ] Physics is correct (equations, derivations, predictions)
- [ ] Axiom consistency maintained
- [ ] Formal proofs compile without `sorry`
- [ ] Proofs correspond to ground truth claims
- [ ] No simulation-steered proving (axiom-first principle)
- [ ] Tests match ground truth within tolerance
- [ ] AC verification (if issue linked)
- [ ] **Human Visual Review completed**
- [ ] **Dimensional/unit consistency verified**

---

## Session-Based Reviews (Multi-Round PRs)

For PRs that go through multiple review rounds, Gemini reviews use `session_id` to maintain context across rounds.

**How it works:**
1. Round 1: Gemini reviews via `review_document`. Claude records the returned `session_id`.
2. Claude fixes findings, pushes new commits.
3. Round 2: Gemini re-reviews with the same `session_id`. Gemini can now say "you fixed X but introduced Y" or "my previous concern about Z is now resolved."
4. Continues until PASS.

**Why:** Without session continuity, Gemini reviews each round from scratch, losing context about what it previously flagged. This leads to repeated findings and missed regressions.

**Technical:** The Gemini MCP server persists sessions in `~/.claude/mcp-servers/gemini/state/`. No external infrastructure needed.

---

## BLOCKING Criteria (Formalized)

### BLOCKING (merge cannot proceed)

- Acceptance criteria FAIL or PARTIAL
- Physics error (wrong equation, incorrect prediction, dimensional inconsistency)
- Axiom violation (proof relies on unvalidated assumption)
- Formal proof gap (`sorry` in proof, theorem doesn't match claim)
- Security vulnerability
- Human Visual Review finding (James spots an anomaly)
- Test failure

### NON-BLOCKING (note but don't block)

- Style suggestions (naming, formatting preferences)
- Alternative approaches ("could also do X")
- Documentation wording improvements
- Performance optimization ideas
- Code cleanup suggestions

### CONTESTED (use Debate Lite)

When Claude and Gemini disagree on whether a finding is BLOCKING:

```markdown
## CONFLICT: [finding ID]
**Claude position:** [X]
**Gemini position:** [Y]
**Impact:** BLOCKING / NON-BLOCKING
**Recommendation:** [which position to adopt, or "escalate to James"]
```

**Rules:**
- Used only for genuine disagreements on BLOCKING items
- Not a multi-round debate — a structured presentation for James
- James resolves CONFLICTs; decision recorded via `record_decision` or issue comment
- If both agree it's non-blocking, no CONFLICT block needed

---

## Review Summary Format

All review summaries should be optimized for James's workflow (dyslexic, high pattern recognition, visual-spatial strength):

### Lead with visual/table format

| Format | Use for |
|--------|---------|
| Traffic-light table (PASS/FAIL/PARTIAL) | AC verification |
| Side-by-side comparison | Before/after numerical changes |
| Bullet points | Key findings (3-5 max) |
| CONFLICT block | Disagreements requiring James's input |

### Then provide detail

Prose explanation follows the visual summary, not the other way around. James scans the table first, reads prose only for items that need context.

---

## References

- [CONTRIBUTING.md — Review Process Details](../../CONTRIBUTING.md#review-process-details)
- [Tiered Review System](../../CONTRIBUTING.md#tiered-review-system)
- [Acceptance Criteria Verification Protocol](../../CONTRIBUTING.md#acceptance-criteria-verification-protocol)
- [Issue #346](https://github.com/JamesPagetButler/QBP/issues/346) — Living issue for workflow refinement
