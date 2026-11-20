#!/usr/bin/env bash
# tools/agda-toolcheck/run.sh — the Agda toolchain baseline suite (QBP#823 W1).
#
# What it does
#   0. Self-tests its own grader (synthetic outputs → expected statuses) and
#      refuses to run if a case fails. `--self-test` runs only this.
#   1. Reads the toolchain: `agda --version`, the agda/cubical pin from
#      .github/workflows/agda-cubical.yml, the library name from
#      proofs/agda-cubical/qbp-cubical.agda-lib, and the HEAD of the locally
#      registered cubical checkout (~/.agda/libraries). A local/CI pin mismatch
#      is a finding and fails the run (ALLOW_PIN_MISMATCH=1 to override).
#   2. Runs four layers, every file as `agda --safe <file>` (exactly as CI does):
#        tool/      builtins-only feature tests            → must PASS
#        lib/       pinned agda/cubical symbol tests        → must PASS
#        mustfail/  negative controls                       → must be REJECTED with
#                   the non-empty `-- EXPECT: <substring>` of each header, matched
#                   against the error output (not the "Checking …" echo lines).
#                   A `MUSTFAIL-KNOWN-HOLE` file also carries `FIXED-IN: <ver>`:
#                   on Agda < FIXED-IN acceptance is KNOWN-HOLE (not a failure),
#                   on Agda >= FIXED-IN acceptance is ACCEPTED = suite failure.
#        project    proofs/agda/*.agda and proofs/agda-cubical/*.agda, the CI-gated
#                   QBP proofs, in the CI order                → must PASS
#      plus controls: no-nested-source (any .agda/.lagda* below the top level of
#      a gated directory, _build/ included, is an unchecked source → FAIL; CI
#      type-checks the trees flat), forbidden_tokens.sh --require-safe over the
#      two gated directories (covers the --safe hole of agda/agda#8341 on 2.8.0;
#      REQUIRES PR #826's scripts/agda_forbidden_tokens.py, else FAIL), its own
#      controls — every fixture in control/ must yield exactly its `PLANTED: n`
#      hits — and the MANIFEST check: every file listed in MANIFEST was found and
#      ran (suite layers: the found set must equal the listed set).
#      A signal exit (rc >= 128) is CRASH in every layer; a crash never counts
#      as REJECTED.
#   3. Records per file: status, exit code, wall seconds, max RSS (KiB) via
#      /usr/bin/time, into results/runs/<run-id>/ (git-ignored). With
#      --update-baseline, and ONLY if the whole run graded green, the record is
#      then copied to results/results-<agda>-<cubical-sha7>.{json,md} (the
#      committed baseline). A failed run never touches the baseline.
#   4. Exits non-zero on ANY unexpected result (FAIL, ACCEPTED, WRONG-ERROR,
#      CRASH, manifest mismatch, fixture mismatch, pin mismatch).
#
# Box safety
#   The whole run is wrapped in ONE boxrun scope (box lease + thermal guard +
#   RSS cap + deadline); it re-execs itself under boxrun unless already inside
#   (AGDA_TOOLCHECK_INNER=1) or --no-boxrun is given. Knobs:
#     TOOLCHECK_MEM_MB   RSS cap for the run, MiB   (default 8000)
#     TOOLCHECK_TIMEOUT  deadline, seconds          (default 3600)
#     TOOLCHECK_TAG      suffix for the results files (e.g. "cold"), optional
#   Exit 87 = RSS cap hit, 124 = deadline/thermal pause ran out, 75 = box busy
#   (--wait is passed, so the run queues instead).
#   Timings are what they are: a file's wall time includes re-checking any
#   QBP module it imports whose interface (_build/) is missing, and the
#   pinned library's interfaces are expected to be prebuilt (~/cubical/_build).
#
# Test seams — DENY BY DEFAULT: every TOOLCHECK_* environment variable other
# than the three knobs above is a seam. All active seams are recorded in the
# JSON (run.test_seams); with any seam set, --update-baseline is REFUSED
# (exit 3 after an otherwise green run) and the committed baseline is never
# written. Known seams (an unknown TOOLCHECK_FOO=1 is caught the same way):
#     TOOLCHECK_FAKE_AGDA_VERSION=<ver>  pretend the pin is another Agda (F2 grading)
#     TOOLCHECK_INJECT_FAIL=1            add a synthetic FAIL row (shows a failed run
#                                        cannot write the baseline)
#     TOOLCHECK_MANIFEST=<path>          use another MANIFEST (shows a missing file fails)
#     TOOLCHECK_SHARED_SCANNER=<path>    point forbidden_tokens.sh at another scanner
#                                        (a stub printing 0 hits must never baseline)
#
# Usage
#   tools/agda-toolcheck/run.sh [--layer tool|lib|mustfail|project|all] [--no-boxrun]
#                              [--update-baseline] [--self-test]
#
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
LAYER=all
USE_BOXRUN=1
UPDATE_BASELINE=0
SELF_TEST_ONLY=0
while [ $# -gt 0 ]; do
  case "$1" in
    --layer) LAYER="$2"; shift 2 ;;
    --no-boxrun) USE_BOXRUN=0; shift ;;
    --update-baseline) UPDATE_BASELINE=1; shift ;;
    --self-test) SELF_TEST_ONLY=1; USE_BOXRUN=0; shift ;;
    -h|--help) sed -n '2,60p' "$0"; exit 0 ;;
    *) echo "run.sh: unknown argument $1" >&2; exit 2 ;;
  esac
done
case "$LAYER" in tool|lib|mustfail|project|all) ;; *) echo "run.sh: bad --layer $LAYER" >&2; exit 2 ;; esac

TOOLCHECK_MEM_MB="${TOOLCHECK_MEM_MB:-8000}"
TOOLCHECK_TIMEOUT="${TOOLCHECK_TIMEOUT:-3600}"

# ---- grading (pure: no agda, no globals except AGDA_VERSION) ---------------
# version comparison (GNU sort -V): ver_ge A B  ⇔  A >= B
ver_ge() { [ "$(printf '%s\n%s\n' "$1" "$2" | sort -V | tail -1)" = "$1" ]; }

# error lines of an agda log: drop the progress echoes and boxrun chatter
error_lines() { grep -vE '^(Checking|Finished| Checking|boxrun:)' "$1" || true; }

# grade <expect: pass|fail|hole> <rc> <outfile> <expect_msg> <fixed_in> <agda_version>
# prints "STATUS|detail"
grade() {
  local expect="$1" rc="$2" out="$3" msg="$4" fixed_in="$5" ver="$6"
  local tail5; tail5="$(error_lines "$out" | head -5 | tr '\n' ' ' | cut -c1-200)"
  if [ "$rc" -ge 128 ]; then echo "CRASH|agda died by signal (rc=$rc): a crash is never a rejection"; return; fi
  case "$expect" in
    pass)
      if [ "$rc" -eq 0 ]; then echo "PASS|"; else echo "FAIL|$tail5"; fi ;;
    fail|hole)
      if [ -z "$msg" ]; then echo "WRONG-ERROR|must-fail file has no non-empty EXPECT: line"; return; fi
      local matched=0
      if [ "$rc" -ne 0 ] && error_lines "$out" | grep -qF -- "$msg"; then matched=1; fi
      if [ "$expect" = fail ]; then
        if [ "$matched" = 1 ]; then echo "REJECTED|"
        elif [ "$rc" -ne 0 ]; then echo "WRONG-ERROR|rejected but not with '$msg': $tail5"
        else echo "ACCEPTED|must-fail was accepted"; fi
        return
      fi
      # hole: keyed to the pin by FIXED-IN (Red Team F2)
      if [ -z "$fixed_in" ]; then echo "WRONG-ERROR|KNOWN-HOLE file without a FIXED-IN: line"; return; fi
      if ver_ge "$ver" "$fixed_in"; then
        if [ "$matched" = 1 ]; then echo "FIXED|rejected on Agda $ver >= $fixed_in"
        elif [ "$rc" -ne 0 ]; then echo "WRONG-ERROR|rejected but not with '$msg': $tail5"
        else echo "ACCEPTED|REGRESSION: accepted on Agda $ver, fixed in $fixed_in"; fi
      else
        if [ "$rc" -eq 0 ]; then echo "KNOWN-HOLE|accepted on Agda $ver < $fixed_in (agda/agda#8341)"
        elif [ "$matched" = 1 ]; then echo "FIXED-EARLY|rejected on Agda $ver < $fixed_in: update FIXED-IN"
        else echo "WRONG-ERROR|rejected but not with '$msg': $tail5"; fi
      fi ;;
  esac
}
is_unexpected() { case "$1" in FAIL|ACCEPTED|WRONG-ERROR|CRASH) return 0 ;; *) return 1 ;; esac; }

# ---- grader self-test (runs first, always) ---------------------------------
self_test() {
  local t; t="$(mktemp -d)"; local fails=0 n=0
  printf 'Checking X (x.agda).\nerror: [Foo]\nboom here\n' > "$t/err"
  printf 'Checking postulate-in-name (p.agda).\nerror: [Bar]\nsomething else\n' > "$t/echo-only"
  printf 'Checking X (x.agda).\nFinished X.\n' > "$t/ok"
  : > "$t/empty"
  expect_case() {  # expect_case <name> <want-status> <expect> <rc> <out> <msg> <fixed_in> <ver>
    local name="$1" want="$2"; shift 2
    local got; got="$(grade "$@")"; got="${got%%|*}"; n=$((n+1))
    if [ "$got" = "$want" ]; then printf '  self-test ok    %-34s → %s\n' "$name" "$got"
    else printf '  self-test FAIL  %-34s → %s (wanted %s)\n' "$name" "$got" "$want"; fails=$((fails+1)); fi
  }
  expect_case pass-rc0                PASS        pass 0   "$t/ok"        ""     ""    2.8.0
  expect_case pass-rc1                FAIL        pass 1   "$t/err"       ""     ""    2.8.0
  expect_case pass-signal-137         CRASH       pass 137 "$t/empty"     ""     ""    2.8.0
  expect_case fail-rejected-with-msg  REJECTED    fail 42  "$t/err"       boom   ""    2.8.0
  expect_case fail-empty-expect       WRONG-ERROR fail 42  "$t/err"       ""     ""    2.8.0
  expect_case fail-msg-only-in-echo   WRONG-ERROR fail 42  "$t/echo-only" postulate "" 2.8.0
  expect_case fail-wrong-message      WRONG-ERROR fail 42  "$t/err"       other  ""    2.8.0
  expect_case fail-accepted           ACCEPTED    fail 0   "$t/ok"        boom   ""    2.8.0
  expect_case fail-signal-not-reject  CRASH       fail 139 "$t/err"       boom   ""    2.8.0
  expect_case hole-below-fix-accepted KNOWN-HOLE  hole 0   "$t/ok"        boom   2.9.0 2.8.0
  expect_case hole-below-fix-patch    KNOWN-HOLE  hole 0   "$t/ok"        boom   2.9.0 2.8.0.2
  expect_case hole-at-fix-accepted    ACCEPTED    hole 0   "$t/ok"        boom   2.9.0 2.9.0
  expect_case hole-after-fix-accepted ACCEPTED    hole 0   "$t/ok"        boom   2.9.0 2.10.0
  expect_case hole-at-fix-rejected    FIXED       hole 42  "$t/err"       boom   2.9.0 2.9.0
  expect_case hole-below-fix-rejected FIXED-EARLY hole 42  "$t/err"       boom   2.9.0 2.8.0
  expect_case hole-no-fixed-in        WRONG-ERROR hole 0   "$t/ok"        boom   ""    2.8.0
  expect_case hole-empty-expect       WRONG-ERROR hole 0   "$t/ok"        ""     2.9.0 2.8.0
  expect_case hole-signal             CRASH       hole 137 "$t/err"       boom   2.9.0 2.8.0
  if ver_ge 2.10.0 2.9.0 && ! ver_ge 2.8.0.2 2.9.0 && ver_ge 2.9.0 2.9.0; then printf '  self-test ok    %-34s\n' ver_ge; n=$((n+1))
  else printf '  self-test FAIL  %-34s\n' ver_ge; fails=$((fails+1)); n=$((n+1)); fi
  rm -rf "$t"
  echo "agda-toolcheck: grader self-test: $((n-fails))/$n ok"
  [ "$fails" -eq 0 ]
}
if ! self_test; then echo "run.sh: grader self-test FAILED — refusing to run" >&2; exit 2; fi
[ "$SELF_TEST_ONLY" = 1 ] && exit 0

# ---- re-exec under boxrun (one scope for the whole suite) -------------------
if [ "$USE_BOXRUN" = 1 ] && [ "${AGDA_TOOLCHECK_INNER:-0}" != 1 ]; then
  if ! command -v boxrun >/dev/null 2>&1; then
    echo "run.sh: boxrun not on PATH; refusing to run bare (use --no-boxrun only in CI)" >&2
    exit 2
  fi
  UB=(); [ "$UPDATE_BASELINE" = 1 ] && UB=(--update-baseline)
  exec boxrun --gpu --mem-mb "$TOOLCHECK_MEM_MB" --timeout "$TOOLCHECK_TIMEOUT" --wait \
       --label agda-toolcheck-suite -- \
       env AGDA_TOOLCHECK_INNER=1 "$0" --layer "$LAYER" --no-boxrun "${UB[@]}"
fi

for tool in agda jq /usr/bin/time; do
  command -v "$tool" >/dev/null 2>&1 || { echo "run.sh: missing $tool" >&2; exit 2; }
done

# ---- toolchain facts --------------------------------------------------------
AGDA_VERSION="$(agda --version | head -1 | awk '{print $3}')"
# Test seams, DENY BY DEFAULT (Gemini r3 (8)): EVERY environment variable named
# TOOLCHECK_* is a seam unless it is one of the three resource/filename knobs
# that cannot affect grading (MEM_MB, TIMEOUT, TAG). Seams are all recorded in
# the JSON (run.test_seams) and any seam refuses --update-baseline — so an
# override added later (in this script, in forbidden_tokens.sh, anywhere) can
# never be forgotten and never produce a baseline.
SEAMS=""
for v in $(compgen -e | grep '^TOOLCHECK_' | sort || true); do
  case "$v" in TOOLCHECK_MEM_MB|TOOLCHECK_TIMEOUT|TOOLCHECK_TAG) ;; *) SEAMS="$SEAMS $v" ;; esac
done
AGDA_FAKED=false
if [ -n "${TOOLCHECK_FAKE_AGDA_VERSION:-}" ]; then AGDA_VERSION="$TOOLCHECK_FAKE_AGDA_VERSION"; AGDA_FAKED=true; fi
INJECT_FAIL=false
[ "${TOOLCHECK_INJECT_FAIL:-0}" = 1 ] && INJECT_FAIL=true
MANIFEST="${TOOLCHECK_MANIFEST:-$HERE/MANIFEST}"
UPDATE_REQUESTED="$UPDATE_BASELINE"
if [ -n "$SEAMS" ]; then
  echo "agda-toolcheck: WARNING — test seam(s) active:$SEAMS (not a baseline; --update-baseline refused)" >&2
  UPDATE_BASELINE=0
fi
[ -f "$MANIFEST" ] || { echo "run.sh: MANIFEST not found at $MANIFEST" >&2; exit 2; }

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
RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)"
RUN_DIR="$HERE/results/runs/$RUN_ID"          # every run records here (git-ignored)
BASE_DIR="$HERE/results"                       # the committed baseline, written only on green
mkdir -p "$RUN_DIR/logs"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
ROWS="$TMP/rows.ndjson"; : > "$ROWS"
UNEXPECTED=0

echo "agda-toolcheck: Agda $AGDA_VERSION (CI pins $CI_AGDA, match=$AGDA_MATCH)"
echo "agda-toolcheck: cubical CI pin $CI_PIN ($LIB_NAME; flags: $LIB_FLAGS)"
echo "agda-toolcheck: cubical local HEAD $LOCAL_PIN (match=$PIN_MATCH)"
echo "agda-toolcheck: Tctl at start ${TCTL} C; layer=$LAYER; start $START_ISO; run dir $RUN_DIR$([ "$UPDATE_BASELINE" = 1 ] && echo '; will update the committed baseline IF green')"

if [ "$PIN_MATCH" != true ] && [ "${ALLOW_PIN_MISMATCH:-0}" != 1 ]; then
  echo "agda-toolcheck: PIN MISMATCH between local cubical checkout and CI — fix ~/cubical or set ALLOW_PIN_MISMATCH=1" >&2
  UNEXPECTED=$((UNEXPECTED+1))
fi

# row <layer> <file> <expect> <status> <rc> <wall> <rss> <detail>
row() {
  is_unexpected "$4" && UNEXPECTED=$((UNEXPECTED+1))
  printf '%-9s %-11s %-28s rc=%-3s %7ss %9s KiB  %s\n' "$1" "$4" "$2" "$5" "$6" "$7" "$8"
  jq -nc --arg layer "$1" --arg file "$2" --arg expect "$3" --arg status "$4" \
         --argjson rc "$5" --argjson wall "$6" --argjson rss "$7" --arg detail "$8" \
         '{layer:$layer,file:$file,expect:$expect,status:$status,exit_code:$rc,wall_s:$wall,max_rss_kib:$rss,detail:$detail}' >> "$ROWS"
}

# ---- one check -------------------------------------------------------------
# check <layer> <dir> <file> <expectation: pass|fail|hole>
check() {
  local layer="$1" dir="$2" file="$3" expect="$4"
  local out="$TMP/out" tfile="$TMP/time" rc wall rss graded expect_msg="" fixed_in=""
  if [ "$expect" != pass ]; then
    expect_msg="$(sed -n 's/^-- *EXPECT: *//p' "$dir/$file" | head -1)"
    fixed_in="$(sed -n 's/^-- *FIXED-IN: *//p' "$dir/$file" | head -1)"
  fi
  set +e
  ( cd "$dir" && /usr/bin/time -f '%e %M' -o "$tfile" agda --safe "$file" ) > "$out" 2>&1
  rc=$?
  set -e
  cp "$out" "$RUN_DIR/logs/$layer-${file%.agda}.log"
  # GNU time prepends "Command exited with non-zero status N" on failure: take the last line
  read -r wall rss < <(tail -1 "$tfile") || { wall=0; rss=0; }
  case "$wall" in ''|*[!0-9.]*) wall=0 ;; esac
  case "$rss" in ''|*[!0-9]*) rss=0 ;; esac
  graded="$(grade "$expect" "$rc" "$out" "$expect_msg" "$fixed_in" "$AGDA_VERSION")"
  row "$layer" "$file" "$expect" "${graded%%|*}" "$rc" "$wall" "$rss" "${graded#*|}"
}

# ---- manifest: what must be found (Gemini (6)) -------------------------------
# manifest_check <layer> <dir> <mode: exact|superset>  — also echoes the files to run
manifest_check() {
  local layer="$1" dir="$2" mode="$3" listed found missing extra f detail status
  listed="$(awk -F'\t' -v l="$layer" '$1==l {print $2}' "$MANIFEST" | sort)"
  found="$(cd "$dir" 2>/dev/null && ls -1 *.agda 2>/dev/null | sort || true)"
  missing="$(comm -23 <(printf '%s\n' "$listed") <(printf '%s\n' "$found") | grep . || true)"
  extra="$(comm -13 <(printf '%s\n' "$listed") <(printf '%s\n' "$found") | grep . || true)"
  local nl nf; nl="$(printf '%s\n' "$listed" | grep -c . || true)"; nf="$(printf '%s\n' "$found" | grep -c . || true)"
  status=PASS; detail="$nf found, $nl listed"
  if [ "$nl" -eq 0 ]; then status=FAIL; detail="MANIFEST lists no files for layer $layer"
  elif [ -n "$missing" ]; then status=FAIL; detail="listed but not found in $dir: $(echo "$missing" | tr '\n' ' ')"
  elif [ "$mode" = exact ] && [ -n "$extra" ]; then status=FAIL; detail="found but not listed in MANIFEST: $(echo "$extra" | tr '\n' ' ')"
  elif [ -n "$extra" ]; then detail="$detail (new, unlisted, will be checked: $(echo "$extra" | tr '\n' ' '))"; fi
  row control "manifest-$layer" manifest "$status" 0 0 0 "$detail"
  [ "$status" = PASS ] || return 0
  printf '%s\n' "$found" > "$TMP/files-$layer"
}

run_layer_dir() {   # run_layer_dir <layer> <dir> <expectation> <manifest-mode>
  local layer="$1" dir="$2" expect="$3" mode="$4" f
  : > "$TMP/files-$layer"
  manifest_check "$layer" "$dir" "$mode"
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    if [ "$expect" = mustfail ]; then
      if grep -q '^-- MUSTFAIL-KNOWN-HOLE' "$dir/$f"; then check "$layer" "$dir" "$f" hole; else check "$layer" "$dir" "$f" fail; fi
    else
      check "$layer" "$dir" "$f" "$expect"
    fi
  done < "$TMP/files-$layer"
}

want() { [ "$LAYER" = all ] || [ "$LAYER" = "$1" ]; }

if want tool;     then run_layer_dir tool     "$HERE/tool"     pass     exact; fi
if want lib;      then run_layer_dir lib      "$HERE/lib"      pass     exact; fi
if want mustfail; then run_layer_dir mustfail "$HERE/mustfail" mustfail exact; fi
if want project; then
  # exactly as CI: cd into the directory, `agda --safe` each file in glob order
  run_layer_dir substrate "$REPO/proofs/agda"         pass superset
  run_layer_dir cubical   "$REPO/proofs/agda-cubical" pass superset
  # (7) the gated trees are flat by convention and CI type-checks `*.agda` flat:
  # any source in a subdirectory (_build/ included) is an unchecked nested source
  nested="$(find "$REPO/proofs/agda" "$REPO/proofs/agda-cubical" -mindepth 2 -type f \
            \( -name '*.agda' -o -name '*.lagda' -o -name '*.lagda.*' \) 2>/dev/null | sort || true)"
  if [ -z "$nested" ]; then nstatus=PASS; ndetail="no .agda/.lagda* source below the top level of proofs/agda or proofs/agda-cubical"
  else nstatus=FAIL; ndetail="unchecked nested source: $(echo "$nested" | sed "s#^$REPO/##" | head -3 | tr '\n' ' ' | cut -c1-200)"; fi
  row control no-nested-source pass "$nstatus" 0 0 0 "$ndetail"
  # lexical control over the two gated DIRECTORIES, as PR #826's CI step does:
  # every file carries --safe, no forbidden token anywhere. ONE scanner,
  # fail-closed: without scripts/agda_forbidden_tokens.py the control FAILS.
  set +e
  hits="$("$HERE/forbidden_tokens.sh" --require-safe "$REPO/proofs/agda" "$REPO/proofs/agda-cubical" 2>"$TMP/ft.err")"; hrc=$?
  set -e
  if [ "$hrc" -eq 0 ] && [ -z "$hits" ]; then lstatus=PASS; ldetail="0 hits over proofs/agda + proofs/agda-cubical (--require-safe; scripts/agda_forbidden_tokens.py)"
  elif [ "$hrc" -eq 2 ]; then lstatus=FAIL; ldetail="$(tr '\n' ' ' < "$TMP/ft.err" | cut -c1-220)"
  else lstatus=FAIL; ldetail="$(echo "$hits" | head -3 | tr '\n' ' ' | cut -c1-200)"; fi
  row control forbidden-tokens pass "$lstatus" 0 0 0 "$ldetail"
  # the control's own controls: every fixture in control/ must yield exactly its PLANTED hits
  : > "$TMP/files-control"
  manifest_check control "$HERE/control" exact
  while IFS= read -r fname; do
    [ -n "$fname" ] || continue
    fixture="$HERE/control/$fname"
    planted="$(sed -n 's/^-- *PLANTED: *\([0-9]*\).*/\1/p' "$fixture" | head -1)"
    set +e
    fhits="$("$HERE/forbidden_tokens.sh" "$fixture" 2>/dev/null)"
    set -e
    nf="$(printf '%s\n' "$fhits" | grep -c . || true)"
    if [ -n "$planted" ] && [ "$nf" -eq "$planted" ]; then fstatus=PASS; fdetail="fixture yields $nf/$planted planted hits"
    else fstatus=FAIL; fdetail="fixture yields $nf hits, expected ${planted:-?} — the scan is blind or over-eager"; fi
    row control "fixture-${fname%.agda}" hits "$fstatus" 0 0 0 "$fdetail"
  done < "$TMP/files-control"
fi
if [ "$INJECT_FAIL" = true ]; then
  row control injected-failure pass FAIL 0 0 0 "TOOLCHECK_INJECT_FAIL=1: synthetic failure to show the baseline is not written"
fi

# ---- record (always to the run dir; the baseline only on green) -------------
END_ISO="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
TAG="${TOOLCHECK_TAG:+-$TOOLCHECK_TAG}"
NAME="results-$AGDA_VERSION-$SHA7$TAG"
jq -n --arg agda "$AGDA_VERSION" --arg ci_agda "$CI_AGDA" --argjson agda_match "$AGDA_MATCH" --argjson agda_faked "$AGDA_FAKED" \
      --arg ci_pin "$CI_PIN" --arg local_pin "$LOCAL_PIN" --argjson pin_match "$PIN_MATCH" \
      --arg lib "$LIB_NAME" --arg flags "$LIB_FLAGS" --arg start "$START_ISO" --arg finish "$END_ISO" \
      --argjson tctl "$TCTL" --arg layer "$LAYER" --argjson unexpected "$UNEXPECTED" --arg seams "${SEAMS# }" \
      --argjson mem "$TOOLCHECK_MEM_MB" --argjson timeout "$TOOLCHECK_TIMEOUT" --arg run_id "$RUN_ID" \
      --slurpfile rows "$ROWS" \
      '{suite:"qbp-agda-toolcheck", version:2,
        toolchain:{agda:$agda, agda_faked:$agda_faked, ci_agda:$ci_agda, agda_match:$agda_match,
                   cubical_ci_pin:$ci_pin, cubical_local_head:$local_pin, pin_match:$pin_match,
                   cubical_lib_name:$lib, lib_flags:$flags},
        run:{"id":$run_id, "start":$start, "finished":$finish, "layer":$layer, "tctl_start_c":$tctl,
             "test_seams":$seams, "boxrun":{"mem_mb":$mem, "timeout_s":$timeout}},
        unexpected:$unexpected, results:$rows}' > "$RUN_DIR/$NAME.json"
{
  echo "# agda-toolcheck results — Agda $AGDA_VERSION, agda/cubical $SHA7"
  echo
  echo "Run $RUN_ID: $START_ISO → $END_ISO · Tctl at start ${TCTL} C · layer $LAYER · unexpected $UNEXPECTED${SEAMS:+ · TEST SEAMS:$SEAMS}"
  echo
  echo "| layer | file | status | rc | wall s | max RSS MiB | detail |"
  echo "|---|---|---|---|---|---|---|"
  jq -r '"| \(.layer) | `\(.file)` | \(.status) | \(.exit_code) | \(.wall_s) | \((.max_rss_kib/1024*10|round)/10) | \(.detail) |"' "$ROWS"
} > "$RUN_DIR/$NAME.md"
echo
echo "agda-toolcheck: wrote $RUN_DIR/$NAME.{json,md}"
if [ "$UNEXPECTED" -ne 0 ]; then
  echo "agda-toolcheck: $UNEXPECTED UNEXPECTED result(s)" >&2
  [ "$UPDATE_BASELINE" = 1 ] && echo "agda-toolcheck: committed baseline NOT updated (run was not green)" >&2
  exit 1
fi
if [ "$UPDATE_REQUESTED" = 1 ] && [ -n "$SEAMS" ]; then
  echo "agda-toolcheck: all expected (green), but --update-baseline REFUSED: test seam(s) active:$SEAMS" >&2
  exit 3
fi
if [ "$UPDATE_BASELINE" = 1 ] && [ -z "$SEAMS" ]; then
  cp "$RUN_DIR/$NAME.json" "$BASE_DIR/$NAME.json"
  cp "$RUN_DIR/$NAME.md"   "$BASE_DIR/$NAME.md"
  echo "agda-toolcheck: committed baseline updated → $BASE_DIR/$NAME.{json,md}"
fi
echo "agda-toolcheck: all expected (green)"
