#!/usr/bin/env bash
# check_vendor_upstream.sh — the check of record for tools/cth-pa (QBP#692).
#
# Diffs every vendored file listed in VENDOR.meta.json against the bytes of the
# same path in an upstream confluent-trust checkout at the pinned sha, after
# reversing the ONLY permitted substitution (the Go import-path rewrite). Any
# byte difference, any sha256 drift from the meta, or a pin that does not match
# the meta's source_sha exits non-zero.
#
# usage: check_vendor_upstream.sh <confluent-trust-checkout> <pin>
#   <confluent-trust-checkout>  path to a git checkout of
#                               github.com/JamesPagetButler/confluent-trust
#                               (any branch; read via `git show <pin>:<path>`,
#                               the working tree is never consulted)
#   <pin>                       the commit the vendored files must match; must
#                               resolve to VENDOR.meta.json's source_sha
set -euo pipefail

if [ $# -ne 2 ]; then
  echo "usage: $0 <confluent-trust-checkout> <pin>" >&2
  exit 64
fi
UP="$1"
PIN="$2"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
META="$HERE/VENDOR.meta.json"

for bin in git python3 sha256sum cmp sed; do
  command -v "$bin" >/dev/null || { echo "missing tool: $bin" >&2; exit 69; }
done
[ -f "$META" ] || { echo "missing $META" >&2; exit 66; }

FULL_PIN="$(git -C "$UP" rev-parse --verify "${PIN}^{commit}")" || { echo "pin $PIN does not resolve in $UP" >&2; exit 65; }
META_SHA="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["source_sha"])' "$META")"
if [ "$FULL_PIN" != "$META_SHA" ]; then
  echo "pin mismatch: argument resolves to $FULL_PIN but VENDOR.meta.json records $META_SHA" >&2
  exit 1
fi

# The import rewrite, read from the meta so the script and the meta cannot drift.
# Lines: "<upstream import>\t<vendored import>".
REWRITES="$(python3 -c '
import json,sys
m=json.load(open(sys.argv[1]))
for r in m["import_rewrites"]:
    print(r["from"]+"\t"+r["to"])
' "$META")"

# Per-file table: "<upstream_path>\t<vendored_path>\t<upstream_sha256>\t<vendored_sha256>".
FILES="$(python3 -c '
import json,sys
m=json.load(open(sys.argv[1]))
for f in m["files"]:
    print("\t".join([f["upstream_path"],f["vendored_path"],f["upstream_sha256"],f["vendored_sha256"]]))
' "$META")"

fail=0
n=0
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

while IFS=$'\t' read -r up_path vd_path up_sha vd_sha; do
  [ -n "$up_path" ] || continue
  n=$((n+1))
  vd_file="$HERE/$vd_path"
  if [ ! -f "$vd_file" ]; then
    echo "MISSING  $vd_path (vendored file absent)"; fail=1; continue
  fi
  # 1. upstream bytes at the pin.
  if ! git -C "$UP" show "$FULL_PIN:$up_path" > "$tmp/up" 2>/dev/null; then
    echo "MISSING  $up_path (not in upstream at $FULL_PIN)"; fail=1; continue
  fi
  got_up="$(sha256sum "$tmp/up" | cut -d' ' -f1)"
  if [ "$got_up" != "$up_sha" ]; then
    echo "DRIFT    $up_path upstream sha256 $got_up != meta $up_sha"; fail=1
  fi
  # 2. vendored bytes as committed.
  got_vd="$(sha256sum "$vd_file" | cut -d' ' -f1)"
  if [ "$got_vd" != "$vd_sha" ]; then
    echo "DRIFT    $vd_path vendored sha256 $got_vd != meta $vd_sha"; fail=1
  fi
  # 3. reverse the import rewrite (Go files only; testdata is compared raw).
  cp "$vd_file" "$tmp/vd"
  case "$vd_path" in
    *.go)
      while IFS=$'\t' read -r from to; do
        [ -n "$from" ] || continue
        # exact quoted import strings only — never a bare module-path sed, so a
        # URL or comment that happens to mention the upstream module is untouched.
        sed -i "s#\"$to\"#\"$from\"#g" "$tmp/vd"
      done <<< "$REWRITES"
      ;;
  esac
  if cmp -s "$tmp/up" "$tmp/vd"; then
    echo "OK       $up_path -> $vd_path"
  else
    echo "DIFF     $up_path -> $vd_path"
    diff -u "$tmp/up" "$tmp/vd" | head -40 || true
    fail=1
  fi
done <<< "$FILES"

echo "checked $n files against $UP @ $FULL_PIN"
if [ "$fail" -ne 0 ]; then
  echo "RESULT: FAIL — vendored tree is not byte-identical to upstream (modulo the recorded import rewrite)" >&2
  exit 1
fi
echo "RESULT: OK"
