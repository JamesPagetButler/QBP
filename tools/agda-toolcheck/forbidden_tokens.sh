#!/usr/bin/env bash
# tools/agda-toolcheck/forbidden_tokens.sh — lexical control for Agda files
# under QBP's --safe discipline (QBP#823 W1, Red Team F3; raw-text per the
# PR #826 review).
#
# Why a scan at all: Agda 2.8.0's --safe accepts a `let`-bound axiom
# (agda/agda#8341, fixed in 2.9.0). Until the pin is past the fix, this scan
# is the only thing between such a file and a green `agda --safe`.
#
# RAW TEXT, no comment stripping. A comment-aware scanner was bypassed twice
# in review (PR #826 Red Team): a string literal `"{-"` opening a fake block
# comment (B1), and an identifier `a--b` read as a line comment (B2) — each
# hid a forbidden declaration later in the file with 0 hits. Raw scanning has
# no lexer to get wrong; the convention that pays for it is: never write a
# forbidden token in a gated Agda file, even in a comment.
#
# ONE SCANNER: when the shared `scripts/agda_forbidden_tokens.py` (PR #826)
# is present in the repo it is used, so the suite and CI agree by
# construction; otherwise this file's grep applies the SAME token list.
#
# Token list (= scripts/agda_forbidden_tokens.py):
#   words  postulate primTrustMe primEraseEquality REWRITE TERMINATING
#          NON_TERMINATING NO_POSITIVITY_CHECK NO_UNIVERSE_CHECK NON_COVERING
#          INJECTIVE                           (whole words, not inside an identifier)
#   flags  --type-in-type --rewriting --allow-unsolved-metas
#          --allow-incomplete-matches --no-positivity-check
#          --no-termination-check --omega-in-omega
#   holes  {!
# plus, with --require-safe (this script only): every file must have an
# `{-# OPTIONS … #-}` line that contains `--safe`.
#
# Usage:  forbidden_tokens.sh [--require-safe] <file.agda>...
# Output: one line per hit, `<file>:<line>:<kind>:<text>`; summary on stderr.
# Exit:   0 no hits · 1 hits · 2 usage / shared-script self-test failure.
set -euo pipefail

REQUIRE_SAFE=0
if [ "${1:-}" = "--require-safe" ]; then REQUIRE_SAFE=1; shift; fi
[ $# -ge 1 ] || { echo "usage: $0 [--require-safe] <file.agda>..." >&2; exit 2; }

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SHARED="$HERE/../../scripts/agda_forbidden_tokens.py"

WORDS='postulate|primTrustMe|primEraseEquality|REWRITE|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|NON_COVERING|INJECTIVE'
FLAGS='type-in-type|rewriting|allow-unsolved-metas|allow-incomplete-matches|no-positivity-check|no-termination-check|omega-in-omega'

hits=0
for f in "$@"; do
  [ -f "$f" ] || { echo "$f:0:missing:no such file"; hits=$((hits+1)); }
done

if [ -f "$SHARED" ]; then
  # delegate the token scan to the shared scanner (its own must-hit self-test runs first)
  set +e
  out="$(python3 -I "$SHARED" "$@" 2>&1)"; rc=$?
  set -e
  if [ "$rc" -eq 2 ]; then echo "$out" >&2; exit 2; fi
  while IFS= read -r line; do
    case "$line" in
      FORBIDDEN\ *) rest="${line#FORBIDDEN }"; file="${rest%%:*}"; rest="${rest#*:}"; ln="${rest%%:*}"; tok="${rest#*: }"
                    echo "$file:$ln:token:$tok"; hits=$((hits+1)) ;;
    esac
  done <<< "$out"
  SCANNER="scripts/agda_forbidden_tokens.py"
else
  for f in "$@"; do
    [ -f "$f" ] || continue
    while IFS= read -r line; do
      echo "$f:${line%%:*}:token:${line#*:}"; hits=$((hits+1))
    done < <(grep -nE "(^|[^[:alnum:]_'])($WORDS)([^[:alnum:]_']|$)|--($FLAGS)([^[:alnum:]_-]|$)|\{!" "$f" || true)
  done
  SCANNER="builtin grep (shared scripts/agda_forbidden_tokens.py not present)"
fi

if [ "$REQUIRE_SAFE" = 1 ]; then
  for f in "$@"; do
    [ -f "$f" ] || continue
    if ! grep -E '\{-#[[:space:]]*OPTIONS' "$f" | grep -qE '(^|[[:space:]])--safe([[:space:]]|#)'; then
      echo "$f:0:missing-safe:no OPTIONS pragma with --safe"; hits=$((hits+1))
    fi
  done
fi

echo "forbidden_tokens: $hits hit(s) in $# file(s) [$SCANNER]" >&2
[ "$hits" -eq 0 ]
