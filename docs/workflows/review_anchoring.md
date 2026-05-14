# Review Anchoring Discipline

**Status:** Standing rule. Effective 2026-05-13. Blocking for all Tier 2+ reviews.
**Authority:** QBP:Oppenheimer (Strategic Lead) per session 2026-05-13.
**Precedent incident:** PR #407 Round 1 — three reviewers (Red Team, Gemini, qbp-implementor) each independently posted reviews citing a Lean theorem name that did not exist, asserting a sudden-approximation regime when the numerics were adiabatic by 4 orders of magnitude, and propagating a dimensional formula off by factor α ≈ 137. All three defects were one-line checks. The team's verbal hedging was the failure mode.

---

## The rule

**Every blocking-class claim in a review must terminate at a verifiable artifact.** Five artifact types are acceptable; nothing else is.

| # | Artifact | What "verifiable" means |
|---|----------|-------------------------|
| 1 | **Lean theorem at file:line** | The reviewer ran `grep` (or equivalent) and quoted the file path + line number. The theorem name appears verbatim in the file at that line. |
| 2 | **Simulation output with exact numerical value + source** | The reviewer cites the actual number (e.g., `V_ff = 0.6554`) and the file it came from (e.g., `analysis/03_double_slit/RESULTS.md §9.1`). |
| 3 | **Published experimental constraint with citation** | Author + year + DOI or arXiv ID, with the cited quantity matched to the digit of precision claimed. |
| 4 | **Pre-registered ground-truth document** | Repo-relative path (e.g., `research/03_double_slit_expected_results.md §4.3.2`). The document must exist in the repo. |
| 5 | **Formally derived dimensional/algebraic identity** | The chain shown explicitly. Substitutions written out. No symbolic shortcuts. |

**If a blocking-class claim cannot be anchored to one of (1)–(5), it is not a finding — it is a hypothesis.** Hypotheses can be raised as questions or non-blocking observations, but they cannot block merge.

---

## What gets returned

A Tier 2+ review comment is **returned to the reviewer** (not read on merits) if any of the following hold for a claim marked BLOCKING:

- Cites a Lean theorem by name without a file:line and without evidence the reviewer grepped for it
- Asserts a regime (sudden, adiabatic, perturbative, etc.) without the numerical check that would distinguish it
- Quotes a dimensional formula without showing the unit substitution
- References a sibling-repo document without verifying it exists on disk
- Hedges with verbal markers (*"likely tractable"*, *"probably consistent with"*, *"sounds reasonable"*, *"should be the case"*) on a blocking item

**"Returned" mechanic.** The synthesizer (qbp-implementor or whoever runs synthesis for the PR) posts a comment of the form:

```markdown
## Review returned for re-anchoring — [reviewer name]

Per `docs/workflows/review_anchoring.md`, the following blocking-class findings require anchors before they are read on merits:

- **[Finding ID]:** [verbatim quote]. Required anchor: [Lean file:line / numerical citation / dimensional chain / etc.]

Please re-post with anchors. The review will be incorporated into the synthesis once anchored.
```

The reviewer re-posts; their re-anchored review is incorporated as if it were the first review.

---

## What stays NON-blocking even without anchors

Anchoring is required for **blocking** claims. Three categories remain valid as advisory:

- **Style / readability suggestions** — no anchor needed
- **Convention divergence from existing precedent** — cite the precedent, that's the anchor
- **Open questions** — explicitly framed as questions ("Is this what you intended?") rather than asserted defects

---

## Examples — acceptable vs. unacceptable

### Lean theorem reference

❌ **Unacceptable** (PR #407 R1 pre-resolution):
> "The formal proof `complex_subspace_reduces_to_QM` in `DoubleSlit.lean §7` certifies this algebraically."

The theorem name does not exist in the file. One `grep` would have caught it.

✅ **Acceptable** (PR #407 R1 post-resolution):
> "Three theorems compose the proof: `coupling_decouples_U1_zero` (`DoubleSlit.lean:398`), `sympForm_zero_psi1` (line 406), `scenarioA_visibility` (line 455). Verified via grep."

### Regime claim

❌ **Unacceptable** (PR #407 R2 pre-resolution):
> "The result is consistent with sudden-approximation behavior."

No numerical check distinguishing sudden from adiabatic.

✅ **Acceptable** (PR #407 R2 post-resolution):
> "τ_transit = (32 nm)/(0.404 c) = 2.65 × 10⁻¹⁶ s; ℏ/E_k = 1.39 × 10⁻²⁰ s; ratio = 1.91 × 10⁴. τ_transit ≫ ℏ/E_k → adiabatic regime (sudden requires τ ≪ ℏ/E)."

### Dimensional formula

❌ **Unacceptable** (PR #407 A1 pre-resolution):
> "τ_transit ≈ a₀/v_e ≈ ℏ/(α m_e c²)"

The substitution chain is not shown; the actual result is ℏ/(α² m_e c²), off by α ≈ 137.

✅ **Acceptable**:
> "a₀ = ℏ/(α m_e c) [Gaussian]; v_e = α c → a₀/v_e = ℏ/(α² m_e c²) = 2.42 × 10⁻¹⁷ s (atomic time unit)."

### Sibling-repo reference

❌ **Unacceptable** (PR #403 A2 pre-escalation):
> "Per BMA Theory Addendum 15 (Reciprocal Focus) ..."

The addendum does not exist on disk; `ls ~/Documents/BMA/theory/` would have shown only Addendum 18.

✅ **Acceptable**:
> "Per BMA Theory Addendum 15 [ASPIRATIONAL — not yet authored on disk; depends on BMA-side delivery]"

---

## Why this is blocking

Three independent reviewers missed three one-line check failures on PR #407 Round 1. That's not bad luck — that's a structural failure of the review discipline. Verbal hedging accumulates risk: each individually-plausible hedge stacks into a synthesis that looks rigorous but is built on unverified premises. The PIVOT-S3-001 incident (Sprint 3 Phase 2 unit-mismatch, requiring a full Phase 2 redo) was the same failure mode at the experimental layer. The team got lucky that PR #407's defects were caught in time; relying on luck does not scale.

**The anchoring rule converts hedging into a falsifiable check at review time, not at merge time.** A reviewer who would have hedged is forced either to (a) anchor and discover their hedge was wrong, or (b) downgrade the claim to a non-blocking question. Both are improvements.

---

## Severity ladder

Per `docs/strategic/oppenheimer_review_001.md`:

- **Level 1 (Advisory):** A reviewer occasionally posts an unanchored claim; flagged in synthesis with a suggestion to anchor next time.
- **Level 2 (Action):** A review has multiple unanchored blocking claims; returned for re-anchoring; the re-anchored version is then read.
- **Level 3 (Stop-work):** A reviewer repeatedly posts unanchored blocking claims across multiple PRs; review-discipline retrospective triggered.

---

## Relationship to other workflow docs

- **`docs/workflows/review_tiers.md`** — defines the tier structure (1/2/3) and reviewer composition; anchoring is a discipline that operates *within* every tier.
- **`memory/pr_review_workflow.md`** — defines the PR-cycle workflow (Red Team → Gemini → human visual review → merge); anchoring is a precondition for a review being incorporated into the cycle.
- **`docs/process_violation_log.md`** — anchoring violations that result in returned reviews are logged here (FAULT category TBD on first incident).

---

*Standing rule effective 2026-05-13. Authored by QBP:Oppenheimer; precedent incident is PR #407 Round 1.*
