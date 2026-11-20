#!/usr/bin/env bash
# proofs/agda-toolcheck/run.sh — the Agda toolchain baseline suite (QBP#823 W1).
#
# What it does
#   1. Reads the toolchain: `agda --version`, the agda/cubical pin from
#      .github/workflows/agda-cubical.yml, the library name from
#      proofs/agda-cubical/qbp-cubical.agda-lib, and the HEAD of the locally
#      registered cubical checkout (~/.agda/libraries). A local/CI pin mismatch
#      is a finding and fails the run (ALLOW_PIN_MISMATCH=1 to override).
#   2. Runs four layers, every file as `agda --safe <file>` (exactly as CI does):
#        tool/      builtins-only feature tests            → must PASS
#        lib/       pinned agda/cubical symbol tests        → must PASS
#        mustfail/  negative controls                       → must FAIL with the
#                   `-- EXPECT: <substring>` recorded in each file's header;
#                   a `MUSTFAIL-KNOWN-HOLE` file is reported as KNOWN-HOLE when
#                   accepted and FIXED when rejected (neither fails the suite)
#        project    proofs/agda/*.agda and proofs/agda-cubical/*.agda, the CI-gated
#                   QBP proofs, in the CI order                → must PASS
#      plus one lexical control over the project layer: no forbidden token
#      (postulate, primTrustMe, REWRITE, TERMINATING, NON_TERMINATING,
#      NO_POSITIVITY_CHECK, NO_UNIVERSE_CHECK, type-in-type, `{!`) outside a
#      line comment. This covers the --safe hole of agda/agda#8341 on 2.8.0.
#   3. Records per file: status, exit code, wall seconds, max RSS (KiB) via
#      /usr/bin/time, into results/results-<agda-version>-<cubical-sha7>.json
#      and a Markdown table results/results-<agda-version>-<cubical-sha7>.md.
#   4. Exits non-zero on ANY unexpected result.
#
# Box safety
#   The whole run is wrapped in ONE boxrun scope (box lease + thermal guard +
#   RSS cap + deadline); it re-execs itself under boxrun unless already inside
#   (AGDA_TOOLCHECK_INNER=1) or --no-boxrun is given. Knobs:
#     TOOLCHECK_MEM_MB   RSS cap for the run, MiB   (default 8000)
#     TOOLCHECK_TIMEOUT  deadline, seconds          (default 3600)
#     TOOLCHECK_TAG      suffix for the results files (e.g. "cold"), optional
#   Timings are what they are: a file's wall time includes re-checking any
#   QBP module it imports whose interface (_build/) is missing, and the
#   pinned library's interfaces are expected to be prebuilt (~/cubical/_build).
#   Exit 87 = RSS cap hit, 124 = deadline/thermal pause ran out, 75 = box busy
#   (--wait is passed, so the run queues instead).
#
# Usage
#   proofs/agda-toolcheck/run.sh [--layer tool|lib|mustfail|project|all] [--no-boxrun]
#
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
LAYER=all
USE_BOXRUN=1
while [ $# -gt 0 ]; do
  case "$1" in
    --layer) LAYER="$2"; shift 2 ;;
    --no-boxrun) USE_BOXRUN=0; shift ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "run.sh: unknown argument $1" >&2; exit 2 ;;
  esac
done

TOOLCHECK_MEM_MB="${TOOLCHECK_MEM_MB:-8000}"
TOOLCHECK_TIMEOUT="${TOOLCHECK_TIMEOUT:-3600}"

# ---- re-exec under boxrun (one scope for the whole suite) -------------------
if [ "$USE_BOXRUN" = 1 ] && [ "${AGDA_TOOLCHECK_INNER:-0}" != 1 ]; then
  if ! command -v boxrun >/dev/null 2>&1; then
    echo "run.sh: boxrun not on PATH; refusing to run bare (use --no-boxrun only in CI)" >&2
    exit 2
  fi
  exec boxrun --gpu --mem-mb "$TOOLCHECK_MEM_MB" --timeout "$TOOLCHECK_TIMEOUT" --wait \
       --label agda-toolcheck-suite -- \
       env AGDA_TOOLCHECK_INNER=1 "$0" --layer "$LAYER" --no-boxrun
fi

for tool in agda jq /usr/bin/time; do
  command -v "$tool" >/dev/null 2>&1 || { echo "run.sh: missing $tool" >&2; exit 2; }
done

# ---- toolchain facts --------------------------------------------------------
AGDA_VERSION="$(agda --version | head -1 | awk '{print $3}')"
WORKFLOW="$REPO/.github/workflows/agda-cubical.yml"
CI_PIN="$(grep -oE 'checkout [0-9a-f]{40}' "$WORKFLOW" | awk '{print $2}' | head -1)"
CI_AGDA="$(grep -oE 'releases/download/v[0-9.]+' "$WORKFLOW" | head -1 | sed 's#.*/v##')"
LIB_NAME="$(awk '/^depend:/{print $2}' "$REPO/proofs/agda-cubical/qbp-cubical.agda-lib")"
LIB_FLAGS="$(sed -n 's/^flags: *//p' "$REPO/proofs/agda-cubical/qbp-cubical.agda-lib")"

LOCAL_LIB_FILE=""
if [ -f "$HOME/.agda/libraries" ]; then
  LOCAL_LIB_FILE="$(grep -m1 'cubical.agda-lib' "$HOME/.agda/libraries" || true)"
fi
LOCAL_PIN="unknown"
if [ -n "$LOCAL_LIB_FILE" ] && [ -d "$(dirname "$LOCAL_LIB_FILE")/.git" ]; then
  LIB_DIR="$(dirname "$LOCAL_LIB_FILE")"
  if command -v git >/dev/null 2>&1; then
    LOCAL_PIN="$(git -C "$LIB_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
  fi
  if [ "$LOCAL_PIN" = unknown ]; then
    head_ref="$(cat "$LIB_DIR/.git/HEAD")"
    case "$head_ref" in
      ref:*) ref="${head_ref#ref: }"; [ -f "$LIB_DIR/.git/$ref" ] && LOCAL_PIN="$(cat "$LIB_DIR/.git/$ref")" ;;
      *) LOCAL_PIN="$head_ref" ;;
    esac
  fi
fi
PIN_MATCH=false
[ "$LOCAL_PIN" = "$CI_PIN" ] && PIN_MATCH=true
AGDA_MATCH=false
[ "$AGDA_VERSION" = "$CI_AGDA" ] && AGDA_MATCH=true

# box conditions
TCTL="null"
for h in /sys/class/hwmon/hwmon*; do
  if [ -r "$h/name" ] && [ "$(cat "$h/name")" = k10temp ] && [ -r "$h/temp1_input" ]; then
    TCTL="$(awk '{printf "%.1f", $1/1000}' "$h/temp1_input")"; break
  fi
done
START_ISO="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
SHA7="${CI_PIN:0:7}"
OUT_DIR="$HERE/results"
mkdir -p "$OUT_DIR/logs"   # full per-file agda output (results/logs/ is git-ignored)
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
ROWS="$TMP/rows.ndjson"; : > "$ROWS"
UNEXPECTED=0

echo "agda-toolcheck: Agda $AGDA_VERSION (CI pins $CI_AGDA, match=$AGDA_MATCH)"
echo "agda-toolcheck: cubical CI pin $CI_PIN ($LIB_NAME; flags: $LIB_FLAGS)"
echo "agda-toolcheck: cubical local HEAD $LOCAL_PIN (match=$PIN_MATCH)"
echo "agda-toolcheck: Tctl at start ${TCTL} C; layer=$LAYER; start $START_ISO"
if [ "$PIN_MATCH" != true ] && [ "${ALLOW_PIN_MISMATCH:-0}" != 1 ]; then
  echo "agda-toolcheck: PIN MISMATCH between local cubical checkout and CI — fix ~/cubical or set ALLOW_PIN_MISMATCH=1" >&2
  UNEXPECTED=$((UNEXPECTED+1))
fi

# ---- one check -------------------------------------------------------------
# check <layer> <dir> <file> <expectation: pass|fail|hole>
check() {
  local layer="$1" dir="$2" file="$3" expect="$4"
  local out="$TMP/out" tfile="$TMP/time" rc wall rss status detail="" expect_msg=""
  if [ "$expect" != pass ]; then
    expect_msg="$(sed -n 's/^-- EXPECT: *//p' "$dir/$file" | head -1)"
  fi
  set +e
  ( cd "$dir" && /usr/bin/time -f '%e %M' -o "$tfile" agda --safe "$file" ) > "$out" 2>&1
  rc=$?
  set -e
  cp "$out" "$OUT_DIR/logs/$layer-${file%.agda}.log"
  # GNU time prepends "Command exited with non-zero status N" on failure: take the last line
  read -r wall rss < <(tail -1 "$tfile") || { wall=0; rss=0; }
  case "$wall" in ''|*[!0-9.]*) wall=0 ;; esac
  case "$rss" in ''|*[!0-9]*) rss=0 ;; esac
  case "$expect" in
    pass)
      if [ "$rc" -eq 0 ]; then status=PASS; else status=FAIL; detail="$(grep -v '^Checking\|^ Checking\|^Finished' "$out" | head -3 | tr '\n' ' ' | cut -c1-200)"; fi ;;
    fail)
      if [ "$rc" -ne 0 ] && grep -qF -- "$expect_msg" "$out"; then status=REJECTED
      elif [ "$rc" -ne 0 ]; then status=WRONG-ERROR; detail="$(tail -5 "$out" | tr '\n' ' ' | cut -c1-200)"
      else status=ACCEPTED; detail="must-fail was accepted"; fi ;;
    hole)
      if [ "$rc" -eq 0 ]; then status=KNOWN-HOLE; detail="accepted on this pin (agda/agda#8341)"
      elif grep -qF -- "$expect_msg" "$out"; then status=FIXED; detail="rejected: the pin has moved past the fix"
      else status=WRONG-ERROR; detail="$(tail -5 "$out" | tr '\n' ' ' | cut -c1-200)"; fi ;;
  esac
  case "$status" in FAIL|ACCEPTED|WRONG-ERROR) UNEXPECTED=$((UNEXPECTED+1)) ;; esac
  printf '%-9s %-8s %-28s rc=%-3s %7ss %9s KiB  %s\n' "$layer" "$status" "$file" "$rc" "$wall" "$rss" "$detail"
  jq -nc --arg layer "$layer" --arg file "$file" --arg expect "$expect" --arg status "$status" \
         --argjson rc "$rc" --argjson wall "$wall" --argjson rss "$rss" --arg detail "$detail" \
         --arg expect_msg "$expect_msg" \
         '{layer:$layer,file:$file,expect:$expect,status:$status,exit_code:$rc,wall_s:$wall,max_rss_kib:$rss,expect_msg:$expect_msg,detail:$detail}' >> "$ROWS"
}

run_layer_dir() {   # run_layer_dir <layer> <dir> <expectation>
  local layer="$1" dir="$2" expect="$3" f
  for f in "$dir"/*.agda; do
    [ -e "$f" ] || continue
    check "$layer" "$dir" "$(basename "$f")" "$expect"
  done
}

want() { [ "$LAYER" = all ] || [ "$LAYER" = "$1" ]; }

if want tool;     then run_layer_dir tool     "$HERE/tool" pass; fi
if want lib;      then run_layer_dir lib      "$HERE/lib"  pass; fi
if want mustfail; then
  for f in "$HERE"/mustfail/*.agda; do
    if grep -q '^-- MUSTFAIL-KNOWN-HOLE' "$f"; then exp=hole; else exp=fail; fi
    check mustfail "$HERE/mustfail" "$(basename "$f")" "$exp"
  done
fi
if want project; then
  # exactly as CI: cd into the directory, `agda --safe` each file in glob order
  run_layer_dir substrate "$REPO/proofs/agda"         pass
  run_layer_dir cubical   "$REPO/proofs/agda-cubical" pass
  # lexical control: no forbidden token outside line comments in any gated file
  hits="$(sed 's/--.*$//' "$REPO"/proofs/agda/*.agda "$REPO"/proofs/agda-cubical/*.agda \
          | grep -nE '(^|[^A-Za-z0-9_.'"'"'-])(postulate|primTrustMe|REWRITE|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|type-in-type)([^A-Za-z0-9_'"'"'-]|$)|\{!' || true)"
  if [ -z "$hits" ]; then lstatus=PASS; ldetail="0 hits in $(ls "$REPO"/proofs/agda/*.agda "$REPO"/proofs/agda-cubical/*.agda | wc -l) files"
  else lstatus=FAIL; ldetail="$(echo "$hits" | head -3 | tr '\n' ' ' | cut -c1-200)"; UNEXPECTED=$((UNEXPECTED+1)); fi
  printf '%-9s %-8s %-28s %s\n' control "$lstatus" no-forbidden-token "$ldetail"
  jq -nc --arg status "$lstatus" --arg detail "$ldetail" \
     '{layer:"control",file:"no-forbidden-token",expect:"pass",status:$status,exit_code:0,wall_s:0,max_rss_kib:0,expect_msg:"",detail:$detail}' >> "$ROWS"
fi

END_ISO="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
# TOOLCHECK_TAG=cold (etc.) keeps a variant run from overwriting the baseline file
TAG="${TOOLCHECK_TAG:+-$TOOLCHECK_TAG}"
JSON="$OUT_DIR/results-$AGDA_VERSION-$SHA7$TAG.json"
MD="$OUT_DIR/results-$AGDA_VERSION-$SHA7$TAG.md"
jq -n --arg agda "$AGDA_VERSION" --arg ci_agda "$CI_AGDA" --argjson agda_match "$AGDA_MATCH" \
      --arg ci_pin "$CI_PIN" --arg local_pin "$LOCAL_PIN" --argjson pin_match "$PIN_MATCH" \
      --arg lib "$LIB_NAME" --arg flags "$LIB_FLAGS" --arg start "$START_ISO" --arg finish "$END_ISO" \
      --argjson tctl "$TCTL" --arg layer "$LAYER" --argjson unexpected "$UNEXPECTED" \
      --argjson mem "$TOOLCHECK_MEM_MB" --argjson timeout "$TOOLCHECK_TIMEOUT" \
      --slurpfile rows "$ROWS" \
      '{suite:"qbp-agda-toolcheck", version:1,
        toolchain:{agda:$agda, ci_agda:$ci_agda, agda_match:$agda_match,
                   cubical_ci_pin:$ci_pin, cubical_local_head:$local_pin, pin_match:$pin_match,
                   cubical_lib_name:$lib, lib_flags:$flags},
        run:{"start":$start, "finished":$finish, "layer":$layer, "tctl_start_c":$tctl,
             "boxrun":{"mem_mb":$mem, "timeout_s":$timeout}},
        unexpected:$unexpected, results:$rows}' > "$JSON"
{
  echo "# agda-toolcheck results — Agda $AGDA_VERSION, agda/cubical $SHA7"
  echo
  echo "Run $START_ISO → $END_ISO · Tctl at start ${TCTL} C · layer $LAYER · unexpected $UNEXPECTED"
  echo
  echo "| layer | file | status | rc | wall s | max RSS MiB | detail |"
  echo "|---|---|---|---|---|---|---|"
  jq -r '"| \(.layer) | `\(.file)` | \(.status) | \(.exit_code) | \(.wall_s) | \((.max_rss_kib/1024*10|round)/10) | \(.detail) |"' "$ROWS"
} > "$MD"
echo
echo "agda-toolcheck: wrote $JSON"
echo "agda-toolcheck: wrote $MD"
if [ "$UNEXPECTED" -ne 0 ]; then
  echo "agda-toolcheck: $UNEXPECTED UNEXPECTED result(s)" >&2
  exit 1
fi
echo "agda-toolcheck: all expected (green)"
