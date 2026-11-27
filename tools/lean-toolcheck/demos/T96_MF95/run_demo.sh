#!/usr/bin/env bash
# Red Team r9 regression demonstration (PR #824): T96 (a pass-labelled file with a false theorem
# that lists `records-tampered`) + MF95 (a later must-fail that rewrites T96's log).
#
#   run_demo.sh SRC_SUITE_DIR SCRATCH_DIR
#
# Builds SCRATCH_DIR/tools/lean-toolcheck as a copy of SRC_SUITE_DIR (a tools/lean-toolcheck tree,
# e.g. `git archive df2b03e` for the BEFORE run, or this tree for the AFTER run) holding only T00,
# T01, T96, MF95 and KL01, links SCRATCH_DIR/proofs and SCRATCH_DIR/scripts to this repository's,
# and runs that copy's own run.sh (which takes its own boxrun lease). Nothing in the real tree is
# written. Expected: BEFORE (df2b03e) T96 PASS and the run GREEN; AFTER T96 FAIL and the run
# INVALID (exit 1). Delete SCRATCH_DIR afterwards.
set -euo pipefail
SRC="$(cd "$1" && pwd)"
OUT="$2"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../../.." && pwd)"
[[ ! -e "$OUT" ]] || { echo "run_demo: $OUT exists; pass a fresh directory" >&2; exit 2; }
S="$OUT/tools/lean-toolcheck"
mkdir -p "$S"
(cd "$SRC" && tar --exclude=./results --exclude='./__pycache__' -cf - .) | tar -xf - -C "$S"
mkdir -p "$S/results"
ln -s "$REPO/proofs" "$OUT/proofs"
ln -s "$REPO/scripts" "$OUT/scripts"
find "$S/tests" -name '*.lean' ! -name 'T00_*' ! -name 'T01_*' -delete
find "$S/must-fail" -mindepth 1 -maxdepth 1 -type d -exec rm -rf {} +
find "$S/known-limits" -mindepth 1 -maxdepth 1 -type d ! -name 'KL01_*' -exec rm -rf {} +
cp "$HERE/T96_PassDecoy.lean" "$S/tests/T96_PassDecoy.lean"
mkdir -p "$S/must-fail/MF95_TamperPassDecoy"
sed "/let script/s#@RAWGLOB@#$S/results/runs/*/raw#" "$HERE/MF95_TamperPassDecoy.lean.in" \
  > "$S/must-fail/MF95_TamperPassDecoy/MF95_TamperPassDecoy.lean"
set +e
TOOLCHECK_RUN_ID="demo-t96" "$S/run.sh"
rc=$?
set -e
echo "run_demo: run.sh exit $rc"
exit "$rc"
