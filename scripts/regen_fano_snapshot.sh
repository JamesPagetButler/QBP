#!/usr/bin/env bash
# Regenerate the fanoTableF4 cross-repo snapshot + axiom attestation from the
# KERNEL-PROVEN QBP.Foundations.FanoOrientationF3.fanoTableF4 (#59 / qbp-cu #65).
# Drift-guarded in CI (.github/workflows/fano-snapshot-drift.yml): CI runs this
# then `git diff --exit-code`, so a hand-edited snapshot fails loudly.
set -euo pipefail
cd "$(dirname "$0")/../proofs"
OUT="$(lake env lean FanoSnapshotGen.lean)"
SNAP="QBP/Foundations/fanoTableF4.snapshot"
AX="QBP/Foundations/fanoTableF4.axioms.txt"
{
  cat <<'HDR'
# fanoTableF4 snapshot — cross-repo drift-gate producer artifact (#59, qbp-cu #65)
# Exported from kernel-proven QBP.Foundations.FanoOrientationF3.fanoTableF4:
#   fanoTableF4 i j = (sign, index)  <=>  e_i * e_j = sign * e_index  (octonion product)
# Provenance (see fanoTableF4.axioms.txt): fanoTableF4_eq_cayleyDickson [propext].
# Format: `i j sign index`, 64 rows row-major; sign in {-1,1}; index in [0,7].
# DO NOT hand-edit — regenerate via scripts/regen_fano_snapshot.sh; CI diffs it.
HDR
  printf '%s\n' "$OUT" | sed -n '/^===SNAPSHOT===$/,/^===AXIOMS===$/p' | grep -E '^[0-7] [0-7] -?1 [0-7]$'
} > "$SNAP"
{
  cat <<'HDR'
# fanoTableF4 axiom-closure attestation (#59, qbp-cu #65)
# Kernel `#print axioms` for the provenance theorems tying the exported snapshot
# to the octonion Cayley-Dickson product. Closure subset of
# {propext, Classical.choice, Quot.sound}: no sorry, no native_decide, no ofReduce*.
HDR
  printf '%s\n' "$OUT" | sed -n '/^===AXIOMS===$/,$p' | grep 'depends on axioms'
} > "$AX"
echo "regenerated: $SNAP ($(grep -cE '^[0-7]' "$SNAP") rows), $AX"
