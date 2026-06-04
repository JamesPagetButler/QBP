---
name: Tier 3 - Theory/Proofs
about: Theory changes, formal proofs, architecture (full panel review)
labels: tier-3-review
---

## Summary

<!-- What theoretical or architectural change does this PR introduce? -->

## Theory-element headline: three-way evidence comparison

<!-- REQUIRED for any PR introducing or modifying a theory element that makes a
     quantitative claim. This is the program's critical-path question in table
     form: is QBP more predictive of the evidence than the incumbent?
     Delete this section ONLY for pure-infrastructure / pure-math PRs with no
     physical claim (state why in Summary).

     UNITS RULE (enforced): ALL quantities in every pillar are stated in QBP
     canonical format. Conversions happen ONCE at ingestion via QBP/Units
     (Constants / ScaleFactors / gen_test_vectors) and the conversion is LINKED.
     Dimensionless or natively-canonical quantities (probabilities, ratios,
     visibilities): write "no conversion required — dimensionless" on the
     provenance line rather than leaving it blank. Hand-converted or
     mixed-unit rows are a review-blocking defect — unit mismatch is a
     historically human-caught error class; exclude it structurally. -->

**Claim under test:** <!-- one sentence -->
**Dataset choice (look-elsewhere guard):** <!-- cite the pre-registered ground-truth doc. REQUIRED for any verdict-grade claim — no free-text justification substitutes. Exploratory work without pre-registration must state "exploratory — no verdict claimed" and the Verdict line stays empty -->

| Pillar | Value (QBP canonical units) | Free params | Data status | Evidence (link, not assertion) |
|---|---|---|---|---|
| **Experimental evidence** (ground truth) | value ± σ | n/a | n/a | dataset + supporting papers |
| **1. QBP prediction** | value | count tuned on THIS dataset | in-sample fit / out-of-sample prediction | Lean theorem / oracle run **with exact input fixture/config linked** (same premise standard as theorems — undocumented config is a smuggled premise) |
| **2. PhysLean baseline** (QM/SM incumbent) | value | count | in-sample / out-of-sample | bridge derivation; if PhysLean cannot produce this number (its SM layer is structure-only), use a PUBLISHED SM prediction with citation and say so — never leave blank, never let QBP grade its own homework |

**Verdict:** QBP closer / equal / farther than baseline w.r.t. experiment, by <Δ in σ or relative error> — **valid only with parameter counts disclosed; an in-sample fit may never be scored against an out-of-sample prediction without saying so** (a theory with more knobs can always sit closer; Δ without the Occam columns is not evidence)
**Unit conversion provenance:** <!-- link to the QBP/Units conversion used. Dimensionless means genuinely unit-free (probabilities, ratios); natural/Planck-unit nondimensionalization (c=ħ=1) does NOT qualify — those quantities still convert via QBP/Units -->

## Mechanical verification evidence (links, not assertions)

<!-- Body claims are not evidence. Every box needs a pointer a reviewer can click.
     A claim without a link is treated by reviewers as UNVERIFIED. -->

- [ ] Clean-checkout build: <!-- CI run link — a green run from YOUR working dir does not count -->
- [ ] Gate scripts (foundations ratchet / layer imports / anchor impact): <!-- CI link -->
- [ ] Differential oracle (PhysLean↔QBP): PASS / FAIL+table / N-A: <!-- run output or link -->
- [ ] `#print axioms` audit (Lean-bearing PRs): <!-- output location in file or CI log -->

## Type of Change

- [ ] New axiom or postulate
- [ ] Formal proof (Lean 4)
- [ ] Theory refinement
- [ ] New experiment phase
- [ ] Architectural decision

## Linked Issue(s)

<!-- Use "Closes #X" or "Fixes #X" -->

## Theoretical Context

<!-- How does this fit into the QBP framework? What does it build on? -->

## Changes Made

<!-- Detailed list of changes with file references -->

-

## Verification

<!-- How was correctness verified? -->

- [ ] Lean proofs compile and verify
- [ ] Consistency with existing axioms checked
- [ ] Physical interpretation validated
- [ ] Connection to experimental predictions documented

## Impact Analysis

<!-- What does this change affect? -->

- **Affects axioms:** Yes / No
- **Affects existing proofs:** Yes / No
- **Affects experimental predictions:** Yes / No
- **Breaking changes:** Yes / No

## CTH anchor impact (per `docs/workflows/review_anchoring.md`)

<!--
Tier 3 PRs almost always touch CTH anchors. Be specific.
Tracked baseline: archive/cth-inventory/confluent-trust-inventory-v5_3.json
Routing rubric: docs/workflows/pr7_conflict_routing_rubric.md (v0.2)
-->

- **New anchors minted:** <!-- list AXIOM-/DERIV-/PRED-/CONJ-/CONV-/OBS-... IDs with one-line description -->
- **Anchors revised:** <!-- list anchor IDs with old → new state -->
- **Anchors retired / killed:** <!-- list KILLED-* IDs with falsification basis -->
- **Anchor-rule terminations** (per the 5 anchor types):
  - [ ] Lean file:line
  - [ ] simulation output + provenance
  - [ ] published experimental constraint
  - [ ] pre-registered ground-truth doc
  - [ ] derived dimensional / algebraic identity
- **Routing axis** (per `docs/workflows/pr7_conflict_routing_rubric.md` v0.2):
  - [ ] theory-axis → co-sign by @qbp-oppenheimer needed (default for Tier 3)
  - [ ] schema-axis → co-sign by @cth-implementor needed
  - [ ] two-axis → both co-signs needed (schema first, then theory)
  - [ ] N/A — purely structural/notation change with no anchor impact

## Test Plan

- [ ] Formal proofs pass
- [ ] Physics tests pass
- [ ] Documentation updated

## Checklist

- [ ] Theory aligns with QBP axioms
- [ ] Notation is consistent with existing documentation
- [ ] DESIGN_RATIONALE.md updated (if applicable)
- [ ] quaternion_physics.md updated (if applicable)
- [ ] CTH anchor impact declared above
- [ ] Every substantive claim terminates at one of the 5 anchor types

---
*Tier 3: Full panel review required (Red Team + Blue Team, sequential)*
