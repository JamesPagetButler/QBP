# Foundations Inverse Anchor Audit (#464)

**Generated:** 2026-08-21 · **Tool:** `scripts/anchor_inverse_audit.py` (re-runnable; replaces the hand-authored `scripts/inventory_verification_report.md`)
**Inputs:** `proofs/` Lean corpus · `archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json`

## 1. Summary

| Metric | Count |
|---|---|
| theorems total | 682 |
| anchors total | 226 |
| anchors with theorems list | 4 |
| anchors with proof file | 20 |
| lean side orphans | 615 |
| anchor side phantoms | 16 |
| stale path citations | 8 |

> **Note — `lean_side_orphans` is a LOWER BOUND.** A theorem counts as *anchored* if any anchor cites its **file** (or its name), so a theorem in a file some anchor references is counted anchored even if no anchor addresses *that* theorem. True per-theorem orphans are ≥ this count; the exact figure lands in Phase B (per-theorem classification, #464). The CI gate closes the resulting ratchet loophole with a **per-file theorem-count ratchet**: new theorems added to an already-file-anchored file are caught (they can't hide behind the coarse global count), forcing a deliberate baseline bump that confirms the new theorems are anchored.

## 2. Lean-side orphans by directory

| Directory | Orphan theorems |
|---|---|
| `proofs/QBP/Foundations` | 467 |
| `proofs/QBP/Experiments` | 62 |
| `proofs/QBP/Units` | 23 |
| `proofs/Sprint12-Inherited/Kitaev.lean` | 13 |
| `proofs/Sprint12-Inherited/Graphene.lean` | 11 |
| `proofs/Sprint12-Inherited/Quaternion.lean` | 11 |
| `proofs/QBP/Optics` | 10 |
| `proofs/QBP/Basic.lean` | 6 |
| `proofs/Sprint12-Inherited/Bi2Se3.lean` | 6 |
| `proofs/Sprint12-Inherited/Crystallisation.lean` | 6 |

## 3. Anchor-side phantoms (cite a non-existent `.lean`)

- `DERIV-hubble-half-entropy-factor` → `proofs/QBP/Foundations/QBPHorizonFoundations.lean`
- `DERIV-vaidya-accreting-horizon-spacelike` → `proofs/QBP/Foundations/QBPHorizonFoundations.lean`
- `FIT-zeta-modulated-profile` → `lean4/QBP/SpectralAction/ProfileFit.lean`
- `INSIGHT-s2-dirac-eta-vanishes` → `proofs/QBP/Foundations/QBPHorizonFoundations.lean`
- `PRED-a0-redshift-linear` → `QBP/Cosmo/RedshiftEvolution.lean`
- `PRED-btfr-mass-correction` → `QBP/Cosmo/RedshiftEvolution.lean`
- `PROOF-3gen` → `lean4/QBP/GaugeBosons.lean`
- `PROOF-alpha-particle-quaternion` → `QBP/Cosmo/Nucleosynthesis.lean`
- `PROOF-cl6` → `lean4/QBP/GaugeBosons.lean`
- `PROOF-eigenratios` → `lean4/QBP/GaugeBosons.lean`
- `PROOF-fano-choice-information` → `QBP/Cosmo/FanoChoiceInformation.lean`
- `PROOF-iron-56-double-octet` → `QBP/Cosmo/Nucleosynthesis.lean`
- `PROOF-iron-to-ns-bridge` → `QBP/Cosmo/DenseMatter.lean`
- `PROOF-oxygen-16-sedenion` → `QBP/Cosmo/Nucleosynthesis.lean`
- `PROOF-seed-mass-from-ln7` → `QBP/Cosmo/SeedMass.lean`
- `PROOF-silicon-28-fano-ladder` → `QBP/Cosmo/Nucleosynthesis.lean`

## 4. Stale-path drift (cite archive/legacy trees)

- `FIT-zeta-modulated-profile` → `lean4/QBP/SpectralAction/ProfileFit.lean`
- `PROOF-3gen` → `lean4/QBP/GaugeBosons.lean`
- `PROOF-42zd` → `lean4/QBP/Sedenion.lean`
- `PROOF-cl6` → `lean4/QBP/GaugeBosons.lean`
- `PROOF-eigenratios` → `lean4/QBP/GaugeBosons.lean`
- `PROOF-fano` → `lean4/QBP/Sedenion.lean`
- `PROOF-hessian` → `lean4/QBP/Sedenion.lean`
- `PROOF-shells` → `lean4/QBP/Elements.lean`

## 5. Full orphan list

See `analysis/foundations-inverse-anchor-audit.json` for the machine-readable per-theorem list (615 orphans). Classification (back-fill vs unanchored-by-design) is Phase B (#464).
