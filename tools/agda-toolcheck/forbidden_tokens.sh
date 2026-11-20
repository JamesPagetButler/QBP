#!/usr/bin/env bash
# tools/agda-toolcheck/forbidden_tokens.sh — lexical control for Agda files
# under QBP's --safe discipline (QBP#823 W1, Red Team F3; raw-text per the
# PR #826 review; file walk per Gemini (3) on PR #825).
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
# is present in the repo it does the whole scan (its own self-test runs
# first), so the suite and CI agree by construction. The fallback below is
# kept as thin as possible and mirrors that script at 45a050e:
#   * arguments may be files or directories; directories are walked
#     recursively (no directory is excluded — `_build` is a legal module
#     path component);
#   * every source form Agda loads is scanned: .agda, .lagda, .lagda.* and
#     .agda-lib;
#   * any symlink under a scanned root is a finding (Agda's module lookup
#     follows directory symlinks; a traversal that does not could be hidden from);
#   * token list identical to the shared script:
#       words  postulate primTrustMe primEraseEquality REWRITE TERMINATING
#              NON_TERMINATING NO_POSITIVITY_CHECK NO_UNIVERSE_CHECK
#              NON_COVERING INJECTIVE        (whole words, not inside an identifier)
#       flags  --type-in-type --rewriting --allow-unsolved-metas
#              --allow-incomplete-matches --no-positivity-check
#              --no-termination-check --omega-in-omega
#       holes  {!
# plus, with --require-safe (this script, both modes): every .agda / .lagda*
# file must have an `{-# OPTIONS … #-}` line that contains `--safe`.
# (The shared script additionally checks .agda-lib `include:` escapes.)
#
# Usage:  forbidden_tokens.sh [--require-safe] <file-or-dir>...
# Output: one line per hit, `<path>:<line>:<kind>:<text>`; summary on stderr
#         ending in `[<scanner>]`.
# Exit:   0 no hits · 1 hits · 2 usage / shared-script self-test failure.
set -euo pipefail

REQUIRE_SAFE=0
if [ "${1:-}" = "--require-safe" ]; then REQUIRE_SAFE=1; shift; fi
[ $# -ge 1 ] || { echo "usage: $0 [--require-safe] <file-or-dir>..." >&2; exit 2; }

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SHARED="$HERE/../../scripts/agda_forbidden_tokens.py"

WORDS='postulate|primTrustMe|primEraseEquality|REWRITE|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|NON_COVERING|INJECTIVE'
FLAGS='type-in-type|rewriting|allow-unsolved-metas|allow-incomplete-matches|no-positivity-check|no-termination-check|omega-in-omega'

hits=0
for p in "$@"; do
  [ -e "$p" ] || { echo "$p:0:missing:no such path"; hits=$((hits+1)); }
done

# the files Agda would load under the given paths (sorted, deterministic)
collect() {
  local p
  for p in "$@"; do
    [ -e "$p" ] || continue
    if [ -d "$p" ]; then
      find "$p" -type f \( -name '*.agda' -o -name '*.lagda' -o -name '*.lagda.*' -o -name '*.agda-lib' \) | sort
    else
      printf '%s\n' "$p"
    fi
  done
}

if [ -f "$SHARED" ]; then
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
  SCANNER="scripts/agda_forbidden_tokens.py"
else
  # symlinks under the scanned roots are findings
  for p in "$@"; do
    [ -e "$p" ] || continue
    if [ -L "$p" ]; then echo "$p:0:symlink:symlinks are not allowed under the gated trees"; hits=$((hits+1)); fi
    if [ -d "$p" ] && [ ! -L "$p" ]; then
      while IFS= read -r l; do
        [ -n "$l" ] || continue
        echo "$l:0:symlink:symlinks are not allowed under the gated trees"; hits=$((hits+1))
      done < <(find "$p" -type l | sort)
    fi
  done
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    while IFS= read -r line; do
      echo "$f:${line%%:*}:token:${line#*:}"; hits=$((hits+1))
    done < <(grep -nE "(^|[^[:alnum:]_'])($WORDS)([^[:alnum:]_']|$)|--($FLAGS)([^[:alnum:]_-]|$)|\{!" "$f" || true)
  done < <(collect "$@")
  SCANNER="builtin grep (shared scripts/agda_forbidden_tokens.py not present)"
fi

if [ "$REQUIRE_SAFE" = 1 ]; then
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    case "$f" in *.agda-lib) continue ;; esac
    if ! grep -E '\{-#[[:space:]]*OPTIONS' "$f" | grep -qE '(^|[[:space:]])--safe([[:space:]]|#)'; then
      echo "$f:0:missing-safe:no OPTIONS pragma with --safe"; hits=$((hits+1))
    fi
  done < <(collect "$@")
fi

echo "forbidden_tokens: $hits hit(s) over $# path(s) [$SCANNER]" >&2
[ "$hits" -eq 0 ]
