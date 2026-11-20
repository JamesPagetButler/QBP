#!/usr/bin/env bash
# QBP Lean toolcheck suite runner (issue #823 W5; policy docs/lean-version-cadence.md).
#
# Runs every tool test (tests/*.lean) and every must-fail control (must-fail/*/*.lean)
# under `boxrun` (box lease, thermal guard, RSS cap), one Lean process at a time, then
# grades each run against the TOOLCHECK-EXPECT lines in its header (toolcheck.py).
#
#   tools/lean-toolcheck/run.sh            # all files (from any cwd; Lean runs from proofs/)
#   tools/lean-toolcheck/run.sh T04 MF02   # a subset (file-name prefixes)
#
# Modes:
#   default  ONE boxrun lease for the whole suite (one queue slot, one cool-start gate);
#            each file is still a separate `lake env lean` process, timed and RSS-measured
#            with /usr/bin/time; boxrun's RSS watch caps the process group at
#            TOOLCHECK_MEM_MB and its deadline is TOOLCHECK_TIMEOUT × number of files.
#   TOOLCHECK_PER_FILE=1  one boxrun lease PER FILE (per-file boxrun records: pauses, max Tctl).
#
# Reads the pins from proofs/lean-toolchain and proofs/lakefile.lean — no version is
# hard-coded here. Writes results/results-<toolchain>-<mathlib-sha7>.{json,md}.
# Exit 0 = every file behaved as expected (tools pass, must-fails caught with the expected
# message); 1 = an unexpected result; 2 = preflight refused (pins/manifest/import surface);
# 75/86/87/124 = boxrun refused or aborted the batch (busy / thermal / memory / timeout).
#
# Resource bound (pre-run-resource-estimate gate): each file is one `lake env lean`
# importing a slice of the pinned Mathlib .oleans; measured 0.8–3.8 GB RSS, 1–5 s each,
# ~70 s for the whole suite on a warm page cache (BASELINE.md).
# Cap: TOOLCHECK_MEM_MB (default 8000) enforced by boxrun's RSS watch (exit 87).
# Disk: < 1 MB of logs per run. Needs the pinned Mathlib .oleans present
# (`lake exe cache get`, or a borrowed .lake/packages); it never builds Mathlib and never
# runs `lake update`.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"          # suite lives in <repo>/tools/lean-toolcheck
PROOFS="$REPO/proofs"                       # Lean env, pins and Mathlib .oleans come from proofs/
CHECKER="$REPO/scripts/check_lean_foundations.py"
MEM_MB="${TOOLCHECK_MEM_MB:-8000}"
TIMEOUT="${TOOLCHECK_TIMEOUT:-900}"
BOXRUN="${BOXRUN:-boxrun}"
BOXRUN_LOG="${BOXRUN_LOG:-$HOME/.box-telemetry/boxrun.log}"
RUN_ID="${TOOLCHECK_RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}"
INNER="${TOOLCHECK_INNER:-0}"

cd "$PROOFS"

# ---- pins (read, never hard-coded) -------------------------------------------------
eval "$(python3 -I "$HERE/toolcheck.py" pins --proofs "$PROOFS")"
OUT_BASE="results-${VERSION}-${MATHLIB_SHA7}"
RAW="$HERE/results/raw-${OUT_BASE}"

# ---- file list ------------------------------------------------------------------
mapfile -t FILES < <(ls "$HERE"/tests/*.lean; ls "$HERE"/must-fail/*/*.lean)
if (($# > 0)); then
  sel=()
  for f in "${FILES[@]}"; do
    for p in "$@"; do [[ "$(basename "$f")" == "$p"* ]] && sel+=("$f"); done
  done
  FILES=("${sel[@]}")
fi

tctl() { # current k10temp Tctl in °C, or empty
  local h
  for h in /sys/class/hwmon/hwmon*; do
    if [[ "$(cat "$h/name" 2>/dev/null || true)" == k10temp ]]; then
      awk '{printf "%.1f", $1/1000}' "$h/temp1_input" 2>/dev/null || true
      return 0
    fi
  done
  return 0
}

# ---- no box (CI runners only): BOXRUN=none runs the files directly, no lease ----------
if [[ "$BOXRUN" == none && "$INNER" != 1 ]]; then
  if [[ -z "${CI:-}" ]]; then
    echo "toolcheck: BOXRUN=none is for CI runners only (CI is unset) — on the federation box use boxrun" >&2
    exit 2
  fi
  rm -rf "$RAW"; mkdir -p "$RAW"
  INNER=1
  export TOOLCHECK_BATCH_LABEL="ci-no-boxrun"
fi

# ---- batch mode: re-exec this script once inside a single boxrun lease -------------
if [[ "$INNER" != 1 && "${TOOLCHECK_PER_FILE:-0}" != 1 ]]; then
  rm -rf "$RAW"; mkdir -p "$RAW"
  total_to=$((TIMEOUT * ${#FILES[@]}))
  echo "toolcheck: batch mode — one boxrun lease for ${#FILES[@]} file(s); cap ${MEM_MB} MB RSS, ${total_to} s"
  set +e
  "$BOXRUN" --gpu --mem-mb "$MEM_MB" --timeout "$total_to" --wait \
    --label "lean-toolcheck-suite-${RUN_ID}" -- \
    env TOOLCHECK_INNER=1 TOOLCHECK_RUN_ID="$RUN_ID" TOOLCHECK_BATCH_LABEL="lean-toolcheck-suite-${RUN_ID}" \
    bash "$HERE/run.sh" "$@"
  rc=$?
  set -e
  rec="$(grep -F "\"lean-toolcheck-suite-${RUN_ID}\"" "$BOXRUN_LOG" 2>/dev/null | grep -v 'queue-' | tail -1 || true)"
  [[ -n "$rec" ]] && echo "toolcheck: boxrun record: $rec"
  if [[ ! -s "$RAW/meta.json" ]]; then
    echo "toolcheck: boxrun did not run the suite (exit $rc) — box busy/hot/degraded or aborted; see above"
    ((rc == 0)) && rc=3
  fi
  exit "$rc"
fi

if [[ "$INNER" != 1 ]]; then rm -rf "$RAW"; fi
mkdir -p "$RAW"

preflight=()
if [[ -n "$MANIFEST_MATHLIB_REV" && "$MANIFEST_MATHLIB_REV" != "$MATHLIB_SHA" ]]; then
  preflight+=("lake-manifest.json mathlib rev $MANIFEST_MATHLIB_REV != lakefile pin $MATHLIB_SHA (lockstep rule, inter §12)")
fi
if [[ "$TOOLCHAIN" == *-rc* || "$TOOLCHAIN" == *nightly* ]]; then
  preflight+=("lean-toolchain names a non-stable release: $TOOLCHAIN (cadence policy P1)")
fi
LEAN_REPORTED="$(lake env lean --version 2>&1 | head -1 || true)"
want_ver="${VERSION#v}"
if [[ "$LEAN_REPORTED" != *"version ${want_ver},"* && "$LEAN_REPORTED" != *"version ${want_ver} "* ]]; then
  preflight+=("lake env lean reports '$LEAN_REPORTED', pin is $TOOLCHAIN")
fi
if ! python3 -I "$HERE/toolcheck.py" check-imports --proofs "$PROOFS" \
     --file "$HERE/tests/T00_ImportSurface.lean" > "$RAW/import-surface.log" 2>&1; then
  preflight+=("T00 import surface is stale — see $(basename "$RAW")/import-surface.log")
fi
cat "$RAW/import-surface.log"

# Zero baseline for the checker: any sorry / vacuous True in a suite file is a violation.
ZERO_BASELINE="$RAW/zero-baseline.json"
printf '{\n  "sorry": 0,\n  "vacuous-`: True :=` theorem": 0\n}\n' > "$ZERO_BASELINE"

echo "toolcheck: $TOOLCHAIN · Mathlib $MATHLIB_SHA7 · ${#FILES[@]} file(s) · run $RUN_ID · Tctl now $(tctl) °C"

for f in "${FILES[@]}"; do
  stem="$(basename "$f" .lean)"
  rel="../${f#"$REPO"/}"   # repo-relative from proofs/ (cwd = the Lake project), e.g. ../tools/lean-toolcheck/tests/T01_…lean
  t0="$(tctl)"
  set +e
  if [[ "$INNER" == 1 ]]; then
    /usr/bin/time -f 'TOOLCHECK-TIME wall=%e maxrss_kb=%M' -o "$RAW/$stem.time" \
      lake env lean "$rel" > "$RAW/$stem.log" 2>&1
    rc=$?
    label="${TOOLCHECK_BATCH_LABEL:-}"
  else
    label="lean-toolcheck-${stem}-${RUN_ID}"
    "$BOXRUN" --gpu --mem-mb "$MEM_MB" --timeout "$TIMEOUT" --wait --label "$label" -- \
      /usr/bin/time -f 'TOOLCHECK-TIME wall=%e maxrss_kb=%M' -o "$RAW/$stem.time" \
      lake env lean "$rel" > "$RAW/$stem.log" 2>&1
    rc=$?
  fi
  set -e
  t1="$(tctl)"
  wall="$(sed -n 's/.*wall=\([0-9.]*\).*/\1/p' "$RAW/$stem.time" 2>/dev/null | tail -1 || true)"
  kb="$(sed -n 's/.*maxrss_kb=\([0-9]*\).*/\1/p' "$RAW/$stem.time" 2>/dev/null | tail -1 || true)"
  mb=""; [[ -n "$kb" ]] && mb=$((kb / 1024))
  pauses=""; maxt=""
  if [[ "$INNER" != 1 ]]; then # per-file boxrun record: pauses, max Tctl
    rec="$(grep -F "\"$label\"" "$BOXRUN_LOG" 2>/dev/null | grep -v 'queue-' | tail -1 || true)"
    pauses="$(awk -F, '{print $(NF-3)}' <<<"$rec" | tr -d '"' || true)"
    maxt="$(awk -F, '{print $(NF-2)}' <<<"$rec" | tr -d '"' || true)"
  fi
  # foundations checker on this file alone (isolated dir: the checker scans a directory)
  cdir="$RAW/checker-$stem"; mkdir -p "$cdir"; cp "$f" "$cdir/"
  set +e
  python3 -I "$CHECKER" --dir "$cdir" --baseline "$ZERO_BASELINE" > "$RAW/$stem.checker.log" 2>&1
  crc=$?
  set -e
  python3 -I - "$RAW/$stem.meta.json" "$rc" "$wall" "$mb" "$crc" "$t0" "$t1" "$maxt" "$pauses" <<'PY'
import json, sys
p, rc, wall, mb, crc, t0, t1, maxt, pauses = sys.argv[1:]
num = lambda s, f=float: f(s) if s not in ("", None) else None
json.dump({"lean_exit": int(rc), "wall_s": num(wall), "maxrss_mb": num(mb, int),
           "checker_exit": int(crc), "tctl_start_c": num(t0), "tctl_end_c": num(t1),
           "max_tctl_c": num(maxt), "pauses": num(pauses, int)}, open(p, "w"))
PY
  printf '  %-28s lean_exit=%-3s wall=%-6s rss=%-5sMB checker_exit=%s Tctl=%s→%s\n' \
    "$stem" "$rc" "${wall:-?}" "${mb:-?}" "$crc" "${t0:-?}" "${t1:-?}"
done

# ---- grade ------------------------------------------------------------------------
python3 -I - "$RAW/meta.json" "$TOOLCHAIN" "$VERSION" "$MATHLIB_SHA" "$MATHLIB_SHA7" \
  "$MANIFEST_MATHLIB_REV" "$LEAN_REPORTED" "$RUN_ID" "$MEM_MB" "$TIMEOUT" "$INNER" \
  "${preflight[@]+"${preflight[@]}"}" <<'PY'
import json, sys, datetime, os
p, tc, ver, sha, sha7, man, rep, rid, mem, to, inner, *pre = sys.argv[1:]
cpu = ""
try:
    for l in open("/proc/cpuinfo"):
        if l.startswith("model name"):
            cpu = l.split(":", 1)[1].strip(); break
except OSError:
    pass
memtotal = memavail = None
try:
    for l in open("/proc/meminfo"):
        k, v = l.split(":", 1)
        if k == "MemTotal": memtotal = int(v.split()[0]) // 1024
        if k == "MemAvailable": memavail = int(v.split()[0]) // 1024
except OSError:
    pass
mode = "batch: one boxrun lease for the suite" if inner == "1" else "per-file boxrun lease"
json.dump({"toolchain": tc, "version": ver, "mathlib_sha": sha, "mathlib_sha7": sha7,
           "manifest_mathlib_rev": man, "lean_version_reported": rep, "run_id": rid,
           "date_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
           "runner": {"wrapper": "boxrun --gpu --wait (RSS watch, thermal guard)", "mode": mode,
                      "mem_cap_mb": int(mem), "timeout_s_per_file": int(to), "threads": 1},
           "box": {"cpu": cpu, "mem_total_mb": memtotal,
                   "mem_available_mb_at_end": memavail, "nproc": os.cpu_count()},
           "preflight_failures": pre}, open(p, "w"), indent=1)
PY

set +e
subset=(); (($# > 0)) && subset=(--only-present)
python3 -I "$HERE/toolcheck.py" evaluate --raw "$RAW" --suite "$HERE" --meta "$RAW/meta.json" \
  --out-json "$HERE/results/${OUT_BASE}.json" --out-md "$HERE/results/${OUT_BASE}.md" "${subset[@]+"${subset[@]}"}"
grc=$?
set -e
if ((${#preflight[@]} > 0)); then
  printf 'toolcheck: PREFLIGHT FAILURE: %s\n' "${preflight[@]}"
  exit 2
fi
echo "toolcheck: results → tools/lean-toolcheck/results/${OUT_BASE}.{json,md} (raw logs: $(basename "$RAW")/, gitignored)"
exit "$grc"
