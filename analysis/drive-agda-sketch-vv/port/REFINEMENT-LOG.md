# CD-join square — refinement loop log (CHT provenance trail)

Loop invariant: CDJoin.agda type-checks with N holes, postulate-free. Ratchet: commit only on progress.

| Iter | Hypothesis | Attempt | Agda result | N | Committed? |
|------|-----------|---------|-------------|---|-----------|
| 0 | (baseline) | minimal CDStr, all 1-cells filled | type-checks, 1 hole (twisted square) | 1 | yes (d712720) |
| 1 | square needs cancellation (Hopf template uses secEq/retEq of (a·_)) | +6 CDStr fields: ⊗-isEquivˡ, conj-conj, conj-⊗, neg-neg, neg-⊗ˡ | type-checks, still 1 hole (no regression) | 1 | yes |
| 2 | STATE: confirm exact square goal | isolate as PathP-of-PathP | Agda accepts the type (goal confirmed) | 1 | n/a |
| 3 | filler via hcomp, constant tube + diagonal base | hcomp, 4 faces, base push(a·c')(b·c c')(i∧~k) | FAIL: base circular — tube faces must be l-DEPENDENT morphs via secEq/retEq | 1 | no |

## Loop status (this session)
- **Phase A: DONE** (iter 1) — CDStr extended with the invertibility/compatibility structure the filler needs. Ratcheted + committed.
- **Phase C: IDENTIFIED** (iter 3) — the square closes via a nested hcomp whose tube faces morph the boundary using the equivalence laws secEq/retEq of (a⊗_), per the Hopf.agda §93-122 template. This is a genuine interactive nested-cubical construction (multi-session).
- **TERMINATE**: escalated per loop design (identified-but-not-yet-built nested construction). Structure, goal, template, and required laws are all now in place around the one hole.
