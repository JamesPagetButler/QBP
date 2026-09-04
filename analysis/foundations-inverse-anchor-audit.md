# Foundations Inverse Anchor Audit (#464)

**Generated:** (unstamped) · **Tool:** `scripts/anchor_inverse_audit.py` (re-runnable; replaces the hand-authored `scripts/inventory_verification_report.md`)
**Inputs:** `proofs/` Lean corpus · `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json`

## 1. Summary

| Metric | Count |
|---|---|
| theorems total | 871 |
| anchors total | 274 |
| anchors with theorems list | 55 |
| anchors with proof file | 67 |
| lean side orphans | 49 |
| anchor side phantoms | 0 |
| stale path citations | 0 |

> **Note — `lean_side_orphans` is a LOWER BOUND.** A theorem counts as *anchored* if any anchor cites its **file** (or its name), so a theorem in a file some anchor references is counted anchored even if no anchor addresses *that* theorem. True per-theorem orphans are ≥ this count; the exact figure lands in Phase B (per-theorem classification, #464). The CI gate closes the resulting ratchet loophole with a **per-file theorem-count ratchet**: new theorems added to an already-file-anchored file are caught (they can't hide behind the coarse global count), forcing a deliberate baseline bump that confirms the new theorems are anchored.

## 2. Lean-side orphans by directory

| Directory | Orphan theorems |
|---|---|
| `proofs/QBP/Foundations` | 49 |

## 3. Anchor-side phantoms (cite a non-existent `.lean`)

_none_

## 4. Stale-path drift (cite archive/legacy trees)

_none_

## 5. Full orphan list

See `analysis/foundations-inverse-anchor-audit.json` for the machine-readable per-theorem list (49 orphans). Classification (back-fill vs unanchored-by-design) is Phase B (#464).
