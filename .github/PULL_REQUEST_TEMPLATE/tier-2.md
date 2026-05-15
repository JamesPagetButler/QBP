---
name: Tier 2 - Code/Tests
about: Code changes, tests, config, housekeeping (dual AI review)
labels: tier-2-review
---

## Summary

<!-- What does this PR do? Why is it needed? -->

## Type of Change

- [ ] Bug fix
- [ ] New feature
- [ ] Test addition/update
- [ ] Configuration change
- [ ] Housekeeping/refactor

## Linked Issue(s)

<!-- Use "Closes #X" or "Fixes #X" -->

## Changes Made

<!-- List key changes -->

-

## Test Plan

<!-- How was this tested? -->

- [ ] Existing tests pass
- [ ] New tests added (if applicable)
- [ ] Manual testing performed

## CTH anchor impact (per `docs/workflows/review_anchoring.md`)

<!--
If this PR touches paper/**, proofs/**, analysis/**, or archive/**,
declare the CTH inventory impact below. If none of those paths are
touched, write "N/A — no anchor-bearing paths modified" and skip
the routing-axis section.

Anchor types (per docs/workflows/review_anchoring.md PR #413):
AXIOM-* / DERIV-* / MEAS-* / OBS-* / PRED-* / FLAG-* / INST-*
/ CONJ-* / CONV-* / KILLED-* / WISDOM-* / FORK-* / CHAIN-*
/ INSIGHT-*

Tracked baseline: archive/cth-inventory/confluent-trust-inventory-v5_3.json
Routing rubric: docs/workflows/pr7_conflict_routing_rubric.md (v0.2)
-->

- **New anchors minted:** <!-- e.g., DERIV-spectral-triple-as-invariant; OBS-jwst-grb-counterpart -->
- **Anchors revised:** <!-- e.g., WISDOM-003 (statement narrowed per §9.7); PRED-foo (status: open → falsified) -->
- **Anchors retired:** <!-- e.g., KILLED-f4-info-theoretic-justification -->
- **Routing axis** (per `docs/workflows/pr7_conflict_routing_rubric.md` v0.2):
  - [ ] theory-axis → co-sign by @qbp-oppenheimer needed
  - [ ] schema-axis → co-sign by @cth-implementor needed
  - [ ] two-axis → both co-signs needed (schema first, then theory)
  - [ ] not-conflict / auto-fold (no co-sign)
  - [ ] N/A — no anchor impact

## Checklist

- [ ] Code follows project style
- [ ] Self-review completed
- [ ] No secrets or credentials included
- [ ] CTH anchor impact declared above (or marked N/A)

---
*Tier 2: Dual AI review required (Red Team + Blue Team)*
