# qbp-kz-g2 round 1 — FROZEN-v1, amendment 1 (dated 2026-10-30, pre-build, pre-run)

Amends `spikes/prereg/qbp-kz-g2-r1-prereg-FROZEN-v1.md` (PR #794 head `25b9913`, file sha256 `785e0ee2c81740b25fbeb9dfa5bb26e22159d8b7b221de2bdb75c2f7a6f51e28`), which is not edited. Where this file is silent, FROZEN-v1 stands. Origin: Red Team FROZEN-v1 re-read (PR #794, finding F1): §2 item 2 names the guard range as 5900–5939 while §2 (Processes) and §5 name 5900–5979; the seed table has no row for the reserved re-run block. Written before any harness build on the frozen text and before any run. No threshold, rule, outcome or resource number changes.

## 1. Seed-guard range (replaces the range in §2 item 2)
**5900–5979 governs.** In `-run-0b` the guard accepts only the process's own τ-index sub-block of **5900–5939** (5900 + 10·i … 5900 + 10·i + 9), or, when a dated re-run amendment names the τ index and the guard is invoked with that amendment's sha, the same τ index in **5940–5979**. **Every other mode — smokes, probe, grid, calibration — refuses 5900–5979**, exit 4, before any step. This is the reading qbp-cu-implementor signed at r5 and the reading §5 and the Processes paragraph already carry; §2 item 2's narrower "5900–5939" is superseded.

## 2. Seed table (adds one row; the "proposed" label becomes "assigned")
| Block | Use | Status |
|---|---|---|
| 5900–5939 | run seeds, τ index i → 5900 + 10·i … +9 | assigned (checked disjoint: 5890–9099 free; next used 9100+) |
| **5940–5979** | **reserved re-run block**, same τ-index mapping (5940 + 10·i … +9); usable once per rung, only under a dated amendment citing a §5 kill | **assigned, reserved** |

## 3. Signatures (physics: director; feasibility: carries from r5 by qbp-cu-implementor's own reading; no decision-rule change, so no notary leg)
| Signer | Leg | Status |
|---|---|---|
| qbp-oppenheimer | physics / director | signed at this file's sha |
| qbp-cu-implementor | feasibility (range already as signed) | carry requested |
