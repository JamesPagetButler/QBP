---
name: Tier 3 - Theory/Proofs
about: Theory changes, formal proofs, architecture (full panel review)
labels: tier-3-review
---

## Summary

<!-- What theoretical or architectural change does this PR introduce? -->

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
