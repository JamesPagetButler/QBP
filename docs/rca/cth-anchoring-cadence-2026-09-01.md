# RCA — CTH anchoring cadence breakdown (FAULT-S4-005, 2026-09-01)

**Beekeeper-flagged serious process breach.** Co-authored + co-signed: @qbp-implementor (analysis, #602 owner), @qbp-oppenheimer (foundations/theory-state), @cth-implementor (confluent-trust#96 schema-authority), with @qbp-cu-implementor supplying the solved-precedent shape (#59/#65/#66). Blameless / system-focused; each cause has an owner.

## Summary
Proven **foundation + substrate** results stopped flowing into the canonical CTH ledger (`archive/cth-inventory/…v0.3.json`) after **#574 (Aug 20)**. Two weeks of theory-state work (foundation #583/#585/#588/#591/#603, substrate #575/#606/#608) merged with **no ledger anchor**. Source-of-truth is materially behind the proven state. This is a **declaration-gate-masquerading-as-enforcement** failure — an evolution of PATTERN-01.

## Full causal chain (all git-verified)
1. **Metric conflation** — the `inverse-anchor-audit` ratchet (#584) counts *every* `grep theorem` (640 orphans, dominated by auxiliary plumbing: `OctonionLaws`×55, `Exp`×65, `TowerLaws`×49), not the *declared* deliverable set. Anchoring 640 is impossible → the escape hatch became mandatory.
2. **Silent escape hatch** — a baseline-bump requires no justification. Bumped in *every* foundation PR since the gate existed (`2fe2f65`→`5343521`→`fddf758`→`b6d33fd`). Enforcement went nominal-green, invisibly. (@qbp-oppenheimer, self-owned: bumped twice this session as routine; didn't flag that enforcement had gone nominal.)
3. **Backstop had no PULL-trigger / fire-owner** — confluent-trust#96 was **push-only**: the flow *begins* at "qbp-oppenheimer emits theorem list." Nothing pulls; no scheduled sweep, no milestone hook, no gate on accumulated debt. When emits lapsed to the lower-energy baseline-bump, the batch went **silently dormant.** *Nobody owned the fire — the root gap.*
4. **The protocol itself never landed (proven ≠ wired)** — the #96 spec (`doc/design/proven-theorem-anchoring.md`, which would have named the trigger/owner) lives on an **un-pushed local-only branch** (`doc/96-proven-theorem-anchoring` @ `4f9d87f`). **Confirmed absent from `confluent-trust` `main`** (verified via `gh` against the canonical repo). The governing spec existed near the work but never gated it.

## Root cause
**Every control could be satisfied without the anchor landing.** The ratchet (declaration gate via a raisable baseline), `cth-anchor-impact` (declaration gate via a "deferred" routing note), and the push-only unowned backstop combined so that "green" never meant "anchored." The deeper flaw: **a ratchet whose baseline can be silently raised is a logbook, not a gate.**

## Relation to PATTERN-01 — this is a RECURRENCE, not a novelty
PATTERN-01 ("gate bypassed when no *mechanical* gate exists") is logged **STILL-OPEN** (its mechanical fix #481 not fully live). This breach is a **direct recurrence**, and specifically the **same class as FAULT-S4-003** ("a gate satisfiable without the underlying work") — here one layer up: the `inverse-anchor-audit` ratchet WAS built (#584) but is satisfiable without anchoring, via a silent baseline-bump. **Sub-pattern to add to the meta-tracker: a ratchet whose baseline can be silently raised is a declaration-gate, not an enforcement-gate.** Resolution criterion inherits PATTERN-01's: *closed only when the gate is mechanical (master physically rejects the merge when the anchor is absent) and a foundation PR has been demonstrably blocked by it.*

## The real owed-anchor debt (@qbp-oppenheimer's rigorous pass — ~16 results, NOT 640)
Filter refinement dropped two issues to zero: **#583** (`native_decide→decide` — hardens existing theorems, no new theory-state) and **#588** (indexing *doc* cross-ref — no theorem). Confirms the filter: **top-level (non-`private`) AND named in an issue-AC / #474 matrix row.**
| Issue | Anchor-worthy result | Top-level theorem(s) on master |
|---|---|---|
| #575 | quaternion H-space on S³ | `S3FromCD.S³-HSpace` |
| #585 | CD dimension = 2ⁿ | `CDDimension.finrank_cdAlg` |
| #585 | Sp(1) unit-quaternion SU(2) | `UnitQuaternion.norm_mul_of_unit` / `mem_Sp1_iff_norm` |
| #585 | **CP phase `cos²(δ_CP)=1/8`** | `CPPhase.cos_sq_delta_CP` / `tan_delta_CP` |
| #585 | spectral-action moments | `SpectralMoments.f4_scaling` / `f2_scaling` |
| #585 | Fano octonion genesis | `FanoGenesis.imaginary_units_square_neg_one` |
| #591 | composition-tower classification | `Hurwitz.octonion_norm_multiplicative` + `sedenion_not_composition` + `tower_dims_in_1248` |
| #603 | 𝕆 ZD-hypersurface empty | `LeftMulDet.octonionLeftMul_det` + `..._eq_zero_iff` |
| #606 | baryon charge = complete invariant | `SkyrmionCharge.baryonNumber` + `baryonNumber-complete` + `π₃S³≅ℤ` |
| #608 | SU(2)→additive baryon topology | `SubstrateCharge.baryonNumber-quaternionProduct-correct` |

### ⚠️ Severity escalation — the gap hit the critical path
`cos²(δ_CP)=1/8` (#585 `CPPhase`) is the **Sprint-4 inherited falsification criterion** (SPRINT_STATUS.md; `paper/quaternion_physics.md` §XIII.D) — the make-or-break constraint whose violation "kills the model before Sprint 4 results phase." The anchoring breakdown left this **critical-path scientific anchor un-recorded in the source-of-truth ledger.** This is not housekeeping — **prioritize `CPPhase` in the first C5 batch.**

## Corrective actions
| # | Action | Owner |
|---|---|---|
| C1 | **Anchor-worthiness filter** — audit candidate set derives from a **declared manifest** (issue-AC / #474-row registry or a `@cth-anchor` marker), not `grep theorem`. 640 → ~dozen. | @qbp-oppenheimer (criterion) + @qbp-implementor (gate) |
| C2 | **Kill the silent bump** — only *auxiliary* theorems may enter the baseline; a bump that would grandfather an **anchor-worthy** orphan is a **hard fail**. | @qbp-implementor + @qbp-oppenheimer |
| C3 | **PULL trigger-gate + owner** — canonical ledger carries the last-anchored HEAD sha (seq=723/724); a foundation/substrate merge past it introducing an anchor-worthy theorem trips a **fail-closed drift-gate that blocks further foundation merges until a batch signs.** **CI fires** (the missing piece) · **@cth-implementor signs** (§6) · **@qbp-architecture co-signs** (§5). Reuse qbp-cu **#66 Step-1** infra-vs-drift run-pattern so this *required cross-repo gate* is required-safe by construction (hard-fail on real drift, soft-pass on infra). | @cth-implementor (trigger) |
| C4 | **Land the protocol** — push the #96 AC3 spec (`4f9d87f`) to canonical `confluent-trust` (currently local-only). | @cth-implementor |
| C5 | **Current-debt sweep** — land the ~dozen owed anchors (table above) through the first real batch. | @qbp-oppenheimer (list) + @cth-implementor (batch) |

## FAULT log entry (docs/process_violation_log.md)
**FAULT-S4-005: CTH anchoring cadence silently stalled — ratchet defeated by routine baseline-bump; backstop unowned + un-landed (2026-09-01)**
- What happened: proven foundation+substrate results (#575–#608) merged un-anchored ~2 weeks; the ratchet stayed green via baseline-bumps not anchors; the confluent-trust#96 backstop was push-only/unowned and its protocol was never pushed to canonical.
- Root cause (process): declaration-gate masquerading as enforcement + silent escape hatch + unowned/un-landed backstop. Extends PATTERN-01 → add row to the meta-tracker.
- Fixes: C1–C5.

*Status: DRAFT — three-seat co-signed on substance (oppenheimer, cth, qbp-implementor); qbp-architecture to co-sign C3 §5. Awaiting beekeeper sign-off + sequencing. All fixes (land #96, build gate+manifest, land anchors) are beekeeper-gated PR moves.*
