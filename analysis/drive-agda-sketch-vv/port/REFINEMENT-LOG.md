# CD-join square — refinement loop log (CHT provenance trail)

Loop invariant: CDJoin.agda type-checks with N holes, postulate-free. Ratchet: commit only on progress.

| Iter | Hypothesis | Attempt | Agda result | N | Committed? |
|------|-----------|---------|-------------|---|-----------|
| 0 | (baseline) | minimal CDStr, all 1-cells filled | type-checks, 1 hole (twisted square) | 1 | yes (d712720) |
| 1 | square needs cancellation (Hopf template uses secEq/retEq of (a·_)) | +6 CDStr fields: ⊗-isEquivˡ, conj-conj, conj-⊗, neg-neg, neg-⊗ˡ | type-checks, still 1 hole (no regression) | 1 | yes |
