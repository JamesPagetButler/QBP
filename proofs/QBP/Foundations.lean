import QBP.Foundations.LieAlgebraIso
import QBP.Foundations.Operations
import QBP.Foundations.SedenionOctonionCount
import QBP.Foundations.Octonion32Count

/-!
# QBP.Foundations — aggregator root for the foundation layer

Single build/gate target for the tower (numbers + operations). Layer rules:
`docs/foundations/layer-architecture.md`. Foundations imports Mathlib ONLY —
never `QBP.Physics`, never `QBP.Substrate`. No energy/crystallisation semantics
in types or theorem statements (doc-comments only).

Build: `lake build QBP.Foundations`

## Quarantine table (NOT imported; pending beekeeper HVR decision 480-B)

The #471 skeleton files shipped orphaned via #480 (16 sorries, 8 vacuous-True
between them). They stay out of the aggregator until the wire-or-quarantine
ruling, but remain visible to the ratchet gate (`scripts/check_lean_foundations.py`
globs `Foundations/**` directly), so their counts cannot regress silently.

| Quarantined module | Tracking |
|---|---|
| `QBP.Foundations.Breakdown`     | 480-B |
| `QBP.Foundations.Sedenion`      | 480-B |
| `QBP.Foundations.CayleyDickson` | 480-B |
| `QBP.Foundations.Octonion`      | 480-B |
-/
