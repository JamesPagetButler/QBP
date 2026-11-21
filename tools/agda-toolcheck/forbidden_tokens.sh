#!/usr/bin/env bash
# tools/agda-toolcheck/forbidden_tokens.sh — the lexical control for Agda files
# under QBP's --safe discipline (QBP#823 W1), as a thin wrapper around the ONE
# scanner, `scripts/agda_forbidden_tokens.py` (PR #826).
#
# Why a scan at all: Agda 2.8.0's --safe accepts a `let`-bound axiom
# (agda/agda#8341, fixed in 2.9.0). Until the pin is past the fix, this scan
# is the only thing between such a file and a green `agda --safe`.
#
# ONE SCANNER, FAIL-CLOSED (Gemini r2 on PR #825, (3)): there is no fallback
# grep here. If scripts/agda_forbidden_tokens.py is absent the control FAILS
# with "requires PR #826's scanner" — a known-incomplete substitute is worse
# than an honest failure. Consequently PR #825 merges after PR #826. The
# shared script scans RAW TEXT (no comment stripping; the PR #826 review
# bypassed a comment-aware scanner with a "{-" string literal and an a--b
# identifier), walks directories recursively (nothing excluded), scans
# .agda / .lagda / .lagda.* / .agda-lib, flags symlinks and .agda-lib
# `include:` escapes, and runs its own must-hit self-test first.
#
# This wrapper adds exactly one check the shared script does not make:
#   --require-safe   every .agda / .lagda* file under the given paths must
#                    have an `{-# OPTIONS … #-}` line that contains `--safe`.
#
# Usage:  forbidden_tokens.sh [--require-safe] <file-or-dir>...
# Output: one line per hit, `<path>:<line>:<kind>:<text>`; summary on stderr
#         ending in `[<scanner>]`.
# Exit:   0 no hits · 1 hits · 2 usage / scanner absent / scanner self-test failure.
set -euo pipefail

REQUIRE_SAFE=0
if [ "${1:-}" = "--require-safe" ]; then REQUIRE_SAFE=1; shift; fi
[ $# -ge 1 ] || { echo "usage: $0 [--require-safe] <file-or-dir>..." >&2; exit 2; }

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SHARED="${TOOLCHECK_SHARED_SCANNER:-$HERE/../../scripts/agda_forbidden_tokens.py}"

if [ ! -f "$SHARED" ]; then
  echo "forbidden_tokens: requires PR #826's scanner (scripts/agda_forbidden_tokens.py) — not found at $SHARED" >&2
  exit 2
fi

hits=0
for p in "$@"; do
  [ -e "$p" ] || { echo "$p:0:missing:no such path"; hits=$((hits+1)); }
done

set +e
out="$(python3 -I "$SHARED" "$@" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 2 ]; then echo "$out" >&2; exit 2; fi
while IFS= read -r line; do
  case "$line" in
    FORBIDDEN\ *)
      rest="${line#FORBIDDEN }"
      if [[ "$rest" =~ ^(.*):([0-9]+):\ (.*)$ ]]; then
        echo "${BASH_REMATCH[1]}:${BASH_REMATCH[2]}:token:${BASH_REMATCH[3]}"
      else
        echo "${rest%%:*}:0:finding:${rest#*: }"
      fi
      hits=$((hits+1)) ;;
  esac
done <<< "$out"

if [ "$REQUIRE_SAFE" = 1 ]; then
  for p in "$@"; do
    [ -e "$p" ] || continue
    while IFS= read -r f; do
      [ -n "$f" ] || continue
      if ! grep -E '\{-#[[:space:]]*OPTIONS' "$f" | grep -qE '(^|[[:space:]])--safe([[:space:]]|#)'; then
        echo "$f:0:missing-safe:no OPTIONS pragma with --safe"; hits=$((hits+1))
      fi
    done < <(if [ -d "$p" ]; then find "$p" -type f \( -name '*.agda' -o -name '*.lagda' -o -name '*.lagda.*' \) | sort; else printf '%s\n' "$p"; fi)
  done
fi

echo "forbidden_tokens: $hits hit(s) over $# path(s) [scripts/agda_forbidden_tokens.py]" >&2
[ "$hits" -eq 0 ]
