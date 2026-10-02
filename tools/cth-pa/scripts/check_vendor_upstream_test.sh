#!/usr/bin/env bash
# Mutation test for check_vendor_upstream.sh (QBP#692, the architect's ruling:
# "a mutant that edits anything else must fail the check"). Two controls:
#
#   positive — the committed vendored tree passes the check-of-record;
#   mutant   — a single byte appended to a vendored engine file makes it fail.
#
# The mutant runs the check from a throwaway COPY of the tree, so a tracked file
# is never touched. Requires an upstream confluent-trust checkout and the pin,
# same arguments as the check itself.
#
# usage: check_vendor_upstream_test.sh <confluent-trust-checkout> <pin>
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: $0 <confluent-trust-checkout> <pin>" >&2
  exit 64
fi
UP="$1"
PIN="$2"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)" # tools/cth-pa
CHECK="scripts/check_vendor_upstream.sh"

# --- positive control: the real tree must pass ------------------------------
if ! "$HERE/$CHECK" "$UP" "$PIN" >/dev/null; then
  echo "FAIL (positive control): the committed vendored tree did not pass the check" >&2
  exit 1
fi

# --- mutant: a tampered engine byte must be caught --------------------------
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cp -a "$HERE/." "$tmp/"
# Append one byte-sequence to a vendored engine file. Any edit changes its
# sha256 (DRIFT) and its bytes (DIFF after the import-rewrite reversal), so the
# check must reject it. A comment survives the rewrite reversal, proving the
# byte-cmp — not just the import rule — is what bites.
printf '\n// mutation-test tamper: this line is not in upstream\n' >> "$tmp/vendor-src/pa/pa.go"
if "$tmp/$CHECK" "$UP" "$PIN" >/dev/null 2>&1; then
  echo "FAIL (mutant): a tampered vendor-src/pa/pa.go was NOT caught by the check" >&2
  exit 1
fi

echo "OK: positive control passes; tampered engine file is caught"
