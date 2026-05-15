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

## Activation Matrix (Pattern × Tier)

Cross-walks the 5 prescriptive [collaboration patterns](claude_gemini_communication.md#6-prescriptive-collaboration-patterns) against the 4 review tiers. Tells you "for tier X, which patterns activate, and when."

| Pattern | Tier 0 | Tier 1 | Tier 2 | Tier 3 | Trigger | Human in loop? |
|---|---|---|---|---|---|---|
| **1. Pre-Implementation Critique** | ✅ **default** | optional | recommended for non-trivial impl | recommended for non-trivial impl | Non-trivial design decision before code | No (routine) |
| **2. Structured Debate** | n/a | n/a | on contested BLOCKING finding | on contested BLOCKING finding | Reviewers disagree on whether a finding is BLOCKING | Tie-break only (after 3 unconvergent rounds) |
| **3. Session-Based Reviews** | n/a | optional | ✅ **required** if multi-round | ✅ **required** if multi-round | PR Round 2+ where Gemini previously reviewed | No (routine) |
| **4. Human Tie-Breaking** | rare | rare | escalation | escalation | (a) Pattern 2 doesn't converge, (b) finding affects sprint direction, (c) AC contested | **YES** (by definition) |
| **5. Interactive Questions** | as needed | as needed | as needed | as needed | Claude needs James's input on a decision | **YES** (by definition) |

### Tool configuration per Pattern × Tier intersection

| Pattern | Gemini tool | Thinking mode | Session ID | Notes |
|---|---|---|---|---|
| 1. Pre-Implementation Critique | `critique_my_approach` | `thinking=true` | new session | Advisory only — no PR comment unless flaw blocks impl |
| 2. Structured Debate | `debate_turn` | `thinking=true` | continue session across rounds | Max 3 rounds before Pattern 4 escalation |
| 3. Session-Based Reviews (Tier 2) | `review_document` | `thinking=true` | continue session across rounds | Persist session_id in PR comment for next round |
| 3. Session-Based Reviews (Tier 3) | `review_document` | `thinking=true`, `thinking_budget=16000` | continue session across rounds | Higher budget for theory-paper sections |
| 4. Human Tie-Breaking | `record_decision` (post-resolution) | n/a | n/a | Decision recorded for cross-session continuity |
| 5. Interactive Questions | `AskUserQuestion` (Claude-native) | n/a | n/a | James may reject framing → reformulate |

### Quick reference: "What do I need for this PR?"

| Situation | Tier | Patterns to invoke |
|---|---|---|
| Docs-only change | 1 | Pattern 1 optional + Pattern 5 if scope ambiguous |
| Bug fix or new test | 2 | Pattern 1 (if non-trivial), Pattern 3 (Round 2+) |
| Refactor with behavior change | 2 | Patterns 1 + 3, possibly Pattern 2 on contested findings |
| New experiment phase | 3 | Patterns 1 + 3, almost always Pattern 5 at scope decisions |
| Theory-paper section | 3 | Patterns 1 + 3, Pattern 2 on algebraic/physical disagreements |
| Plan or architecture decision | 0 → 2/3 | Pattern 1 (before impl), then per impl tier |
| Disputed BLOCKING finding | (carries from impl tier) | Pattern 2 → Pattern 4 if unconvergent |
| Routine sprint phase work | 2 | Patterns 1 + 3; Patterns 4 + 5 if scope or direction is contested |

### Escalation thresholds (Pattern 4 trigger detail)

Pattern 4 (Human Tie-Breaking) is the escape hatch from Pattern 2's debate loop, and it has strict triggers to avoid becoming a routine bottleneck:

| Trigger | Threshold | Example |
|---|---|---|
| Pattern 2 unconvergent | **3 debate rounds** with no agreement on BLOCKING status | "Furey says CCvS coefficient is X; Feynman says X' — neither persona budges after 3 rounds" |
| Finding affects sprint direction | Any finding that would change the next phase's scope or acceptance criteria | "Reviewer flags that Sprint 4 cannot start without solving Y" |
| AC contested | Reviewers disagree on whether an AC is satisfied | "Red Team says AC #3 PASS via evidence Z; Gemini says PARTIAL because Z doesn't address sub-condition Z'" |
| Anchor unavailable | Pattern 1-3 cannot resolve because the required anchor (per [`review_anchoring.md`](review_anchoring.md)) doesn't exist | "Both reviewers agree we need a Lean theorem for claim Y, but no theorem exists yet" |

**Anti-bottleneck principle:** if a finding doesn't match a trigger above, the reviewers must resolve via Pattern 2 (debate) or accept the finding as NON-BLOCKING. Pattern 4 is not a substitute for thinking.

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

**Weight:** Advisory means Tier 0 does not block PR creation. However, Tier 2/3 reviewers should reference any Tier 0 findings — if a critique flagged a flaw that wasn't addressed, that becomes a Tier 2/3 BLOCKING finding.

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
- [ ] **Scale compatibility check** — datasets on shared axes must not differ by >10× in characteristic scale (see [Known AI Blind Spots](#known-ai-blind-spots))
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
- [ ] **Scale compatibility check** — datasets on shared axes must not differ by >10× in characteristic scale
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
- Any unforeseen critical error not listed above — when in doubt, it's BLOCKING

### Anchoring discipline (standing rule, effective 2026-05-13)

Every BLOCKING-class claim in a Tier 2+ review must terminate at a verifiable artifact: a Lean theorem at file:line, a simulation output with numerical value + source, a published experimental citation, a pre-registered ground-truth document, or a formally derived dimensional/algebraic identity. Reviews containing unanchored blocking claims are **returned to the reviewer** and not read on merits until re-anchored. Full rule + examples + return mechanic: see [`docs/workflows/review_anchoring.md`](review_anchoring.md). Precedent incident: PR #407 Round 1 (three reviewers each missed three one-line check failures).

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

## Known AI Blind Spots

Documented cases where AI reviewers (Red Team and/or Gemini) missed an issue that a human caught. Reviewers should actively check for these patterns.

| Category | Description | Caught by | Reference |
|----------|-------------|-----------|-----------|
| **Scale/unit incomparability** | Two datasets plotted on shared axes with >10× difference in characteristic scale (e.g. 47 µm vs 13 mm fringes). AI verified code correctness and captions but did not question whether the visual comparison was physically meaningful. | James (Human Visual Review) | FAULT-S3-003, PR #368 |

### Scale Compatibility Check

When reviewing plots that overlay or compare multiple datasets:

1. **Identify the characteristic scale** of each dataset (fringe spacing, peak width, envelope scale)
2. **Compare scales** — if they differ by more than 10×, the overlay is likely misleading
3. **Check ACs** — if an AC specifies "plot X vs Y on same axes", verify the outputs are scale-compatible before accepting the AC as satisfiable
4. **Flag incompatible overlays** as BLOCKING — the fix is usually separate panels at natural scales, with a quantitative metric (e.g. visibility curve) for comparison

---

## References

- [CONTRIBUTING.md — Review Process Details](../../CONTRIBUTING.md#review-process-details)
- [Tiered Review System](../../CONTRIBUTING.md#tiered-review-system)
- [Acceptance Criteria Verification Protocol](../../CONTRIBUTING.md#acceptance-criteria-verification-protocol)
- [Issue #346](https://github.com/JamesPagetButler/QBP/issues/346) — Living issue for workflow refinement
- [Process Violation Log](../process_violation_log.md) — All documented faults
