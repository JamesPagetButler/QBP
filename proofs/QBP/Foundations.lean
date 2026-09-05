import QBP.Foundations.Alternator
import QBP.Foundations.Artin
import QBP.Foundations.ArtinCore
import QBP.Foundations.ArtinSpan
import QBP.Foundations.ArtinTrace
import QBP.Foundations.CDAlg
import QBP.Foundations.CDBridge
import QBP.Foundations.CDDimension
import QBP.Foundations.CPPhase
import QBP.Foundations.CDLifting
import QBP.Foundations.CrossProduct
import QBP.Foundations.DeltaLandscape
import QBP.Foundations.Exp
import QBP.Foundations.Breakdown
import QBP.Foundations.FanoGenesis
import QBP.Foundations.Hurwitz
import QBP.Foundations.SpatialFirstLink
import QBP.Foundations.NoAutonomousDynamics
import QBP.Foundations.SpectralMoments
import QBP.Foundations.UnitQuaternion
import QBP.Foundations.OctonionLaws
import QBP.Foundations.FanoOrientationF3
import QBP.Foundations.FanoSubalgebras
import QBP.Foundations.TowerLaws
import QBP.Foundations.LeftMulDet
import QBP.Foundations.LieAlgebraIso
import QBP.Foundations.NormForm
import QBP.Foundations.Operations
import QBP.Foundations.SedenionOctonionCount
import QBP.Foundations.Octonion32Count
import QBP.Foundations.QBPHorizonFoundations
import QBP.Foundations.G2Transitivity

/-!
# QBP.Foundations — aggregator root for the foundation layer

Single build/gate target for the tower (numbers + operations). Layer rules:
`docs/foundations/layer-architecture.md`. Foundations imports Mathlib ONLY —
never `QBP.Physics`, never `QBP.Substrate`. No energy/crystallisation semantics
in types or theorem statements (doc-comments only).

Build: `lake build QBP.Foundations`

## Deletion record (480-B resolved: beekeeper ruling 2026-06-04, option c)

The #471 skeleton files (shipped orphaned via #480's squash; sorries +
vacuous-True stubs; pre-dating the re-derive-native scope ratification) were
DELETED in this PR rather than wired or quarantined. Their intended-theorem
inventory is preserved as the rebuild plan of record in issue #503, with
per-claim dispositions (done / superseded / rebuild-under-conventions).
The ratchet baseline (`.lean-gate-baseline.json`) is zeroed in the same
change: the Foundations gate now enforces ZERO sorry / ZERO vacuous-True,
permanently.

Deleted: Breakdown, Sedenion, CayleyDickson, Octonion (see #503).
-/
