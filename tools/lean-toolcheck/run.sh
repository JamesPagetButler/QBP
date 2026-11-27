#!/usr/bin/env bash
# QBP Lean toolcheck suite runner (issue #823 W5; policy docs/lean-version-cadence.md).
#
# Runs every tool test (tests/*.lean), every must-fail control (must-fail/*/*.lean) and
# every report-only known-limit probe (known-limits/*/*.lean) under `boxrun` (box lease, thermal guard, RSS cap), one Lean process at a time, then
# grades each run against the TOOLCHECK-EXPECT lines in its header (toolcheck.py).
#
#   tools/lean-toolcheck/run.sh            # all files (from any cwd; Lean runs from proofs/)
#   tools/lean-toolcheck/run.sh T04 MF02   # a subset (file-name prefixes)
#   tools/lean-toolcheck/run.sh --update-baseline   # full run; if GREEN, ALSO overwrite the
#                                                   # COMMITTED results/results-<tc>-<sha7>.*
#                                                   # (alias --record). Never on a subset.
#
# Modes:
#   default  ONE boxrun lease for the whole suite (one queue slot, one cool-start gate);
#            each file is still a separate `lake env lean` process, timed and RSS-measured
#            with /usr/bin/time; boxrun's RSS watch caps the process group at
#            TOOLCHECK_MEM_MB and its deadline is TOOLCHECK_TIMEOUT × number of files.
#   TOOLCHECK_PER_FILE=1  one boxrun lease PER FILE (per-file boxrun records: pauses, max Tctl).
#
# Reads the pins from proofs/lean-toolchain and proofs/lakefile.lean — no version is
# hard-coded here. A normal run writes ONLY to results/runs/<run-id>/ (gitignored); the
# committed baseline results/results-<toolchain>-<mathlib-sha7>.{json,md} is rewritten only
# with --update-baseline (Red Team F4 on PR #824: a reviewer's run must not dirty the record).
# Exit 0 = every file behaved as expected (tools pass, must-fails caught with the expected
# message); 1 = an unexpected result; 2 = preflight refused (pins/manifest/import surface);
# 75/86/87/124 = boxrun refused or aborted the batch (busy / thermal / memory / timeout).
#
# Resource bound (pre-run-resource-estimate gate): each file is THREE sequential Lean processes,
# each importing a slice of the pinned Mathlib .oleans: `lake env lean --json` (messages), a
# fresh `lake env lean -o` compile, and the PR #829 auditor (`lean --run`, which loads the
# .olean's environment). Measured 0.8–3.8 GB RSS and 1–5 s for the first (BASELINE.md); the
# compile is the same elaboration again, so the upper bound is about 3x the old ~70–110 s per
# suite at the same peak RSS. Disk: one small .olean per file under results/runs/<id>/audit/.
# Cap: TOOLCHECK_MEM_MB (default 8000) enforced by boxrun's RSS watch (exit 87).
# Disk: < 1 MB of logs per run. Needs the pinned Mathlib .oleans present
# (`lake exe cache get`, or a borrowed .lake/packages); it never builds Mathlib and never
# runs `lake update`.
set -euo pipefail
# Red Team r6: the whole script is one function, so bash has PARSED all of it before the first Lean
# process runs. A suite file that rewrites run.sh mid-run cannot change what this run does next.
main() {
# The input-manifest program (Red Team r6 concern 1), held IN MEMORY for the same reason: the
# post-run check must not be code a suite file could have rewritten on disk.
MANIFEST_PY="$(cat <<'PYEOF'
import hashlib, json, os, sys


def suite_files(root):
    out = {}
    for d, dirs, fs in os.walk(root):
        rel = os.path.relpath(d, root)
        if rel == ".":
            dirs[:] = [x for x in dirs if x != "results"]
        dirs[:] = [x for x in dirs if x != "__pycache__"]
        for f in fs:
            if f.endswith(".md"):  # docs never affect grading (and BASELINE is edited after runs)
                continue
            p = os.path.join(d, f)
            r = os.path.relpath(p, root).replace(os.sep, "/")
            with open(p, "rb") as fh:
                out[r] = hashlib.sha256(fh.read()).hexdigest()
    return dict(sorted(out.items()))


def all_files(root):
    out = {}
    for d, dirs, fs in os.walk(root):
        for f in fs:
            p = os.path.join(d, f)
            try:
                with open(p, "rb") as fh:
                    out[os.path.relpath(p, root)] = hashlib.sha256(fh.read()).hexdigest()
            except OSError:
                out[os.path.relpath(p, root)] = None
    return dict(sorted(out.items()))


def tree_digest(root):
    root = os.path.realpath(root)
    h, n = hashlib.sha256(), 0
    for d, dirs, fs in os.walk(root):
        dirs.sort()
        for f in sorted(fs):
            p = os.path.join(d, f)
            st = os.lstat(p)
            h.update(
                f"{os.path.relpath(p, root)}\0{st.st_size}\0{st.st_mtime_ns}\0{st.st_ctime_ns}\0{st.st_ino}\n".encode()
            )
            if os.path.islink(p):  # Red Team r7 finding 2: follow the link and stat its TARGET too
                try:
                    t = os.stat(p)
                    h.update(f"-> {os.path.realpath(p)}\0{t.st_size}\0{t.st_mtime_ns}\0{t.st_ctime_ns}\0{t.st_ino}\n".encode())
                except OSError:
                    h.update(f"-> {os.path.realpath(p)}\0dangling\n".encode())
            n += 1
    return {"root": root, "files": n, "digest": h.hexdigest()}


def snapshot(suite, repo_files, trees):
    rf = {}
    for p in repo_files:
        try:
            with open(p, "rb") as fh:
                rf[p] = hashlib.sha256(fh.read()).hexdigest()
        except OSError:
            rf[p] = None
    return {
        "suite_dir": os.path.realpath(suite),
        "suite": suite_files(suite),
        "repo_files": rf,
        "trees": [tree_digest(t) for t in trees if t],
    }


mode = sys.argv[1]
if mode == "all":  # all DIR OUT: content hashes of EVERY file under DIR (no exclusions)
    json.dump(all_files(sys.argv[2]), open(sys.argv[3], "w"))
elif mode == "suite-check":  # suite-check BEFORE BEFORE_SHA DIR: DIR's suite == the manifest's
    raw = open(sys.argv[2], "rb").read()
    if hashlib.sha256(raw).hexdigest() != sys.argv[3]:
        print("the pre-run manifest itself was rewritten"); sys.exit(1)
    want, now = json.loads(raw)["suite"], suite_files(sys.argv[4])
    bad = sorted(k for k in set(want) | set(now) if want.get(k) != now.get(k))
    for k in bad:
        print(f"private grader copy differs from the manifest: {k}")
    sys.exit(1 if bad else 0)
elif mode == "suite":  # suite DIR OUT: content hashes of a (throwaway) suite tree
    json.dump(suite_files(sys.argv[2]), open(sys.argv[3], "w"))
elif mode == "diff":  # diff BEFORE AFTER: changed/added/removed paths, one JSON list
    a, b = json.load(open(sys.argv[2])), json.load(open(sys.argv[3]))
    print(json.dumps(sorted(k for k in set(a) | set(b) if a.get(k) != b.get(k))))
else:  # snapshot|verify OUT SUITE TREES(:-sep) REPO_FILE...  [verify: + BEFORE BEFORE_SHA]
    if mode == "verify":
        before_p, before_sha = sys.argv[2], sys.argv[3]
        out, suite, trees, files = sys.argv[4], sys.argv[5], sys.argv[6], sys.argv[7:]
    else:
        out, suite, trees, files = sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5:]
    now = snapshot(suite, files, [t for t in trees.split(":") if t])
    if mode == "snapshot":
        json.dump(now, open(out, "w"), indent=0)
        sys.exit(0)
    probs = []
    raw = open(before_p, "rb").read()
    if hashlib.sha256(raw).hexdigest() != before_sha:
        probs.append("the pre-run manifest itself was rewritten during the run")
    before = json.loads(raw)
    for k in sorted(set(before["suite"]) | set(now["suite"])):
        if before["suite"].get(k) != now["suite"].get(k):
            probs.append(f"suite input changed during the run: {k}")
    for k in sorted(set(before["repo_files"]) | set(now["repo_files"])):
        if before["repo_files"].get(k) != now["repo_files"].get(k):
            probs.append(f"repo input changed during the run: {k}")
    if [(t["root"], t["files"], t["digest"]) for t in before["trees"]] != [
        (t["root"], t["files"], t["digest"]) for t in now["trees"]
    ]:
        for tb, tn in zip(before["trees"], now["trees"]):
            if tb != tn:
                probs.append(
                    f"package/toolchain tree changed during the run: {tb['root']} "
                    f"({tb['files']} -> {tn['files']} files)"
                )
        if len(before["trees"]) != len(now["trees"]):
            probs.append("the set of package/toolchain trees changed")
    json.dump({"ok": not probs, "problems": probs}, open(out, "w"), indent=1)
    sys.exit(1 if probs else 0)
PYEOF
)"

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"          # suite lives in <repo>/tools/lean-toolcheck
PROOFS="$REPO/proofs"                       # Lean env, pins and Mathlib .oleans come from proofs/
CHECKER="$REPO/scripts/check_lean_foundations.py"
# Structural axiom audit (Red Team r3 / director ruling on PR #824): the PR #829 / issue #827
# out-of-process auditor, run on an .olean compiled in a fresh process. Until PR #829 is on
# master, point TOOLCHECK_AUDITOR at its LeanAxiomAudit.lean (check_lean_axiom_audit.py must sit
# beside it); without an auditor the run is a PREFLIGHT FAILURE, never a stdout-only GREEN.
AUDITOR="${TOOLCHECK_AUDITOR:-$REPO/scripts/LeanAxiomAudit.lean}"
MEM_MB="${TOOLCHECK_MEM_MB:-8000}"
TIMEOUT="${TOOLCHECK_TIMEOUT:-900}"
BOXRUN="${BOXRUN:-boxrun}"
BOXRUN_LOG="${BOXRUN_LOG:-$HOME/.box-telemetry/boxrun.log}"
RUN_ID="${TOOLCHECK_RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}"
INNER="${TOOLCHECK_INNER:-0}"
UPDATE_BASELINE="${TOOLCHECK_UPDATE_BASELINE:-0}"

args=()
for a in "$@"; do
  case "$a" in
    --update-baseline | --record) UPDATE_BASELINE=1 ;;
    -*) echo "toolcheck: unknown flag $a" >&2; exit 2 ;;
    *) args+=("$a") ;;
  esac
done
set -- "${args[@]+"${args[@]}"}"
if [[ "$UPDATE_BASELINE" == 1 && $# -gt 0 ]]; then
  echo "toolcheck: --update-baseline needs a FULL run (no file prefixes)" >&2
  exit 2
fi

cd "$PROOFS"

# ---- pins (read, never hard-coded) -------------------------------------------------
eval "$(python3 -I "$HERE/toolcheck.py" pins --proofs "$PROOFS")"
OUT_BASE="results-${VERSION}-${MATHLIB_SHA7}"
RUN_DIR="$HERE/results/runs/${RUN_ID}" # gitignored; one directory per run
RAW="$RUN_DIR/raw"

# ---- file list ------------------------------------------------------------------
# Null-safe globs (no `ls` parsing; any filename character is fine). An empty layer, an empty
# suite, or a prefix that matches nothing is a refusal (exit 2), never a vacuous GREEN.
shopt -s nullglob
L_TESTS=("$HERE"/tests/*.lean)
L_MF=("$HERE"/must-fail/*/*.lean)
L_KL=("$HERE"/known-limits/*/*.lean)
shopt -u nullglob
for layer in L_TESTS L_MF L_KL; do
  declare -n arr="$layer"
  if ((${#arr[@]} == 0)); then
    echo "toolcheck: REFUSED — layer ${layer#L_} has zero .lean files (an empty layer is RED)" >&2
    exit 2
  fi
  unset -n arr
done
FILES=("${L_TESTS[@]}" "${L_MF[@]}" "${L_KL[@]}")
if (($# > 0)); then
  sel=()
  for p in "$@"; do
    hit=0
    for f in "${FILES[@]}"; do
      if [[ "$(basename "$f")" == "$p"* ]]; then sel+=("$f"); hit=1; fi
    done
    if ((hit == 0)); then
      echo "toolcheck: REFUSED — prefix '$p' matches no suite file" >&2
      exit 2
    fi
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
    TOOLCHECK_UPDATE_BASELINE="$UPDATE_BASELINE" \
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
# F1 (Red Team on PR #824): on a fresh checkout lake-manifest.json is absent (gitignored) and
# the first `lake env` prints "info: QBPProofs: no previous manifest, creating one from
# scratch" BEFORE Lean's version line — never take line 1; match the `Lean (version` line.
LEAN_VERSION_OUT="$(lake env lean --version 2>&1 || true)"
LEAN_REPORTED="$(grep -m1 -E '^Lean \(version ' <<<"$LEAN_VERSION_OUT" || true)"
if [[ -z "$LEAN_REPORTED" ]]; then
  LEAN_REPORTED="(no 'Lean (version' line in: $(tr '\n' ' ' <<<"$LEAN_VERSION_OUT" | cut -c1-200))"
fi
# lake may just have (re)created the manifest — re-read so the lockstep check sees it.
eval "$(python3 -I "$HERE/toolcheck.py" pins --proofs "$PROOFS")"
if [[ -n "$MANIFEST_MATHLIB_REV" && "$MANIFEST_MATHLIB_REV" != "$MATHLIB_SHA" ]]; then
  preflight+=("lake-manifest.json mathlib rev $MANIFEST_MATHLIB_REV != lakefile pin $MATHLIB_SHA (after lake env)")
fi
want_ver="${VERSION#v}"
if [[ "$LEAN_REPORTED" != *"version ${want_ver},"* && "$LEAN_REPORTED" != *"version ${want_ver} "* ]]; then
  preflight+=("lake env lean reports '$LEAN_REPORTED', pin is $TOOLCHAIN")
fi
if ! python3 -I "$HERE/toolcheck.py" check-imports --proofs "$PROOFS" \
     --file "$HERE/tests/T00_ImportSurface.lean" > "$RAW/import-surface.log" 2>&1; then
  preflight+=("T00 import surface is stale — see $(basename "$RAW")/import-surface.log")
fi
cat "$RAW/import-surface.log"
if [[ ! -f "$AUDITOR" || ! -f "$(dirname "$AUDITOR")/check_lean_axiom_audit.py" ]]; then
  preflight+=("structural auditor not found ($AUDITOR + check_lean_axiom_audit.py beside it): PR #829 is not on this branch — set TOOLCHECK_AUDITOR or rebase onto master after #829 lands")
  AUDITOR=""
fi
# Red Team r5 finding 2: the auditor and its checker must be the PINNED files (auditor_pin.json).
if [[ -n "$AUDITOR" ]]; then
  if ! pin_out="$(python3 -I - "$HERE/auditor_pin.json" "$AUDITOR" <<'PY'
import hashlib, json, os, sys
pin = json.load(open(sys.argv[1])); a = sys.argv[2]
c = os.path.join(os.path.dirname(a), "check_lean_axiom_audit.py")
h = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
bad = [n for n, f in (("LeanAxiomAudit.lean", a), ("check_lean_axiom_audit.py", c)) if h(f) != pin[n]]
if bad:
    print(f"{', '.join(bad)} sha256 differs from auditor_pin.json (PR #829 {pin['commit'][:7]})")
    sys.exit(1)
PY
)"; then
    preflight+=("structural auditor not the pinned one: $pin_out")
  fi
fi
# The project search path the auditor resolves Mathlib from (the toolchain library goes FIRST,
# inside the auditor); the per-file audit build dir is appended per file.
LAKE_LP="$(lake env printenv LEAN_PATH 2>/dev/null || true)"
# The Lean-parser layer sees ONLY the pinned packages (Mathlib and its deps), never the project's
# own build dir: no QBP module, and so no QBP initializer, can be imported by a suite file there.
PKG_LP="$(tr ':' '\n' <<<"$LAKE_LP" | grep -F '/.lake/packages/' | paste -sd: - || true)"

# Zero baseline for the checker: any sorry / vacuous True in a suite file is a violation.
ZERO_BASELINE="$RAW/zero-baseline.json"
printf '{\n  "sorry": 0,\n  "vacuous-`: True :=` theorem": 0\n}\n' > "$ZERO_BASELINE"

echo "toolcheck: $TOOLCHAIN · Mathlib $MATHLIB_SHA7 · ${#FILES[@]} file(s) · run $RUN_ID · Tctl now $(tctl) °C"

# ---- process isolation (Red Team r7, MF91) ------------------------------------------
# Every Lean process runs as PID 1 of its OWN PID namespace (`unshare --user --map-root-user
# --fork --pid --mount-proc --kill-child`). When it exits, the kernel kills every process left in that
# namespace, `setsid` and double-forked daemons included. So nothing a file starts can outlive
# the file's Lean process and race the verification or the grader. If the box cannot create the
# namespace (unprivileged user namespaces off), that is a PREFLIGHT FAILURE, never a silent skip.
# TOOLCHECK_TEST_NO_PIDNS=1 (selftest demonstrations only) turns the namespace off; such a run is
# always INVALID, and shows what the survivor check below catches.
# `--mount-proc` gives the namespace its own /proc: Lean finds its own binary through
# /proc/<pid>/exe, and inside the namespace its pid is 1 (the host's init without it).
ISO=(unshare --user --map-root-user --fork --pid --mount-proc --kill-child --)
ISO_OFF=0
if [[ "${TOOLCHECK_TEST_NO_PIDNS:-0}" == 1 ]]; then
  ISO=(); ISO_OFF=1
  echo "toolcheck: WARNING — TOOLCHECK_TEST_NO_PIDNS=1: PID namespaces OFF (demonstration); this run is INVALID by construction"
elif ! "${ISO[@]}" true 2>/dev/null; then
  preflight+=("cannot create a PID namespace (unshare --user --pid): unprivileged user namespaces are disabled on this host")
fi

# ---- cross-run persistence (Red Team r6 concern 1) -----------------------------------
# (b) every Lean process that runs a file's code (the --json run, the fresh compile) runs in a
# THROWAWAY COPY of the suite outside the repo, with its cwd there. Relative writes land in the
# copy; the copy is hashed before and after each file, so a write is attributed to that file.
# Absolute-path writes cannot be stopped without a sandbox (S1, QBP#836), so:
# (a) a manifest of every input (suite files by content; repo inputs; the pinned package trees
# and the toolchain by stat: size, mtime, ctime, inode) is taken BEFORE the first Lean process
# and verified after the last one. A mismatch makes the run INVALID (exit 1, no baseline update).
WORK_TMP="$(mktemp -d "${TMPDIR:-/tmp}/lean-toolcheck-${RUN_ID}-XXXXXX")"
trap 'rm -rf "$WORK_TMP"' EXIT
TSUITE="$WORK_TMP/suite"
SURVIVORS=()
mkdir -p "$WORK_TMP/late" "$WORK_TMP/audit"
fresh_copy() {
  rm -rf "$TSUITE"; mkdir -p "$TSUITE"
  (cd "$HERE" && tar --exclude=./results --exclude='./__pycache__' -cf - .) | tar -xf - -C "$TSUITE"
}
fresh_copy
# The GRADER runs from a PRIVATE copy taken now, before any Lean process, and checked against the
# manifest right before it runs (Red Team r7 ask 2): never from the working tree.
GDIR="$WORK_TMP/grader"
mkdir -p "$GDIR"
(cd "$HERE" && tar --exclude=./results --exclude='./__pycache__' -cf - .) | tar -xf - -C "$GDIR"
TC_DIR="$(lake env lean --print-prefix 2>/dev/null || true)"
MAN_TREES="${PKG_LP}:${TC_DIR}"
MAN_FILES=("$PROOFS/lean-toolchain" "$PROOFS/lakefile.lean" "$CHECKER")
[[ -n "$AUDITOR" ]] && MAN_FILES+=("$AUDITOR" "$(dirname "$AUDITOR")/check_lean_axiom_audit.py")
python3 -I -c "$MANIFEST_PY" snapshot "$RAW/inputs.json" "$HERE" "$MAN_TREES" "${MAN_FILES[@]}"
INPUTS_SHA="$(sha256sum "$RAW/inputs.json" | cut -d' ' -f1)"

# Run a Lean process inside the batch lease (INNER) or its own boxrun lease (per-file mode).
bx() {
  local tag="$1"; shift
  if [[ "$INNER" == 1 ]]; then "$@"
  else "$BOXRUN" --gpu --mem-mb "$MEM_MB" --timeout "$TIMEOUT" --wait --label "lean-toolcheck-${tag}-${RUN_ID}" -- "$@"
  fi
}

for f in "${FILES[@]}"; do
  stem="$(basename "$f" .lean)"
  rel="../${f#"$REPO"/}"   # repo-relative from proofs/ (cwd = the Lake project), e.g. ../tools/lean-toolcheck/tests/T01_…lean
  t0="$(tctl)"
  # ---- Lean-parser subset check FIRST (Red Team r5 / director decision): LeanSubsetParse.lean
  # parses the file with Lean's own parser and elaborates nothing but builtin scope commands, so
  # the file's code never runs here. It runs before every other Lean process on this file, with
  # its own nonce drawn just before it.
  pnonce="$(python3 -I -c 'import secrets; print(secrets.token_hex(16))')"
  set +e
  bx "parse-$stem" "${ISO[@]+"${ISO[@]}"}" env -u LEAN_PATH QBP_SUBSET_LEAN_PATH="$PKG_LP" \
    lean --run "$HERE/LeanSubsetParse.lean" "$pnonce" "$f" \
    > "$RAW/$stem.parse.out" 2> "$RAW/$stem.parse.stderr"
  prc=$?
  tf="$TSUITE/${f#"$HERE"/}"   # this file's copy in the throwaway suite
  python3 -I -c "$MANIFEST_PY" suite "$TSUITE" "$WORK_TMP/copy.before.json"
  if [[ "$INNER" == 1 ]]; then
    (cd "$(dirname "$tf")" && "${ISO[@]+"${ISO[@]}"}" /usr/bin/time -f 'TOOLCHECK-TIME wall=%e maxrss_kb=%M' -o "$RAW/$stem.time" \
      lake -d "$PROOFS" env lean --json "$tf") > "$RAW/$stem.log" 2> "$RAW/$stem.stderr"
    rc=$?
    label="${TOOLCHECK_BATCH_LABEL:-}"
  else
    label="lean-toolcheck-${stem}-${RUN_ID}"
    (cd "$(dirname "$tf")" && "$BOXRUN" --gpu --mem-mb "$MEM_MB" --timeout "$TIMEOUT" --wait --label "$label" -- \
      "${ISO[@]+"${ISO[@]}"}" /usr/bin/time -f 'TOOLCHECK-TIME wall=%e maxrss_kb=%M' -o "$RAW/$stem.time" \
      lake -d "$PROOFS" env lean --json "$tf") > "$RAW/$stem.log" 2> "$RAW/$stem.stderr"
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
  # ---- structural axiom audit: compile in a FRESH process to an .olean, then run the PR #829
  # auditor on it (`lean --run`, LEAN_PATH unset, toolchain library first, `importModules
  # (loadExts := false)`, no initializers). The nonce is drawn AFTER the compile, so nothing the
  # file runs while compiling can know it. Neither process's stdout is ever parsed for a verdict
  # except the auditor's one result line. Fail-closed: no .olean (e.g. the file exited early)
  # means no audit, which fails a pass file.
  aud="$WORK_TMP/audit/$stem"   # in the throwaway area too (its cwd and its -o path)
  rm -rf "$aud"; mkdir -p "$aud/src/ToolcheckAudit" "$aud/build/ToolcheckAudit"
  cp "$f" "$aud/src/ToolcheckAudit/$stem.lean"
  olean="$aud/build/ToolcheckAudit/$stem.olean"
  set +e
  (cd "$aud" && bx "audit-c-$stem" "${ISO[@]+"${ISO[@]}"}" lake -d "$PROOFS" env lean -R "$aud/src" -o "$olean" \
    "$aud/src/ToolcheckAudit/$stem.lean") > "$RAW/$stem.compile.log" 2>&1
  comp_rc=$?
  olean_ok=0; [[ -s "$olean" ]] && olean_ok=1
  nonce="$(python3 -I -c 'import secrets; print(secrets.token_hex(16))')"
  arc=""
  if [[ -n "$AUDITOR" && "$olean_ok" == 1 ]]; then
    bx "audit-r-$stem" "${ISO[@]+"${ISO[@]}"}" env -u LEAN_PATH QBP_AUDIT_LEAN_PATH="${LAKE_LP}:$aud/build" \
      lean --run "$AUDITOR" "$nonce" "$stem" "i:ToolcheckAudit.$stem" "t:ToolcheckAudit.$stem" \
      "p:$aud/build" > "$RAW/$stem.audit.out" 2> "$RAW/$stem.audit.stderr"
    arc=$?
  fi
  set -e
  python3 -I -c "$MANIFEST_PY" suite "$TSUITE" "$WORK_TMP/copy.after.json"
  writes="$(python3 -I -c "$MANIFEST_PY" diff "$WORK_TMP/copy.before.json" "$WORK_TMP/copy.after.json")"
  # SURVIVOR CHECK (Red Team r7 ask 1, second layer): after the file's last Lean process, the
  # throwaway suite copy and the audit area (the cwd of every code-running process) are hashed,
  # and hashed again 1.2 s later. Any change means something the file started is still running.
  for k in a b; do
    [[ "$k" == b ]] && sleep 1.2
    python3 -I -c "$MANIFEST_PY" all "$TSUITE" "$WORK_TMP/late/s.$k.json"
    python3 -I -c "$MANIFEST_PY" all "$WORK_TMP/audit" "$WORK_TMP/late/u.$k.json"
  done
  late="$(python3 -I - "$WORK_TMP/late" <<'PY'
import json, sys
w = sys.argv[1]
out = []
for tag, name in (("s", "suite-copy"), ("u", "audit")):
    x, y = json.load(open(f"{w}/{tag}.a.json")), json.load(open(f"{w}/{tag}.b.json"))
    out += [f"{name}/{k}" for k in sorted(set(x) | set(y)) if x.get(k) != y.get(k)]
print(json.dumps(out))
PY
)"
  if [[ "$late" != "[]" ]]; then
    SURVIVORS+=("$stem: $late")
    echo "toolcheck: SURVIVOR: something $stem started kept writing after its Lean processes ended: $late"
  fi
  [[ "$writes" != "[]" || "$late" != "[]" ]] && fresh_copy   # the next file gets a clean copy
  python3 -I - "$RAW/$stem.meta.json" "$rc" "$wall" "$mb" "$crc" "$t0" "$t1" "$maxt" "$pauses" \
    "$comp_rc" "$olean_ok" "$arc" "$nonce" "$prc" "$pnonce" "$writes" "$late" <<'PY'
import json, sys
p, rc, wall, mb, crc, t0, t1, maxt, pauses, comp, ok, arc, nonce, prc, pnonce, writes, late = sys.argv[1:]
num = lambda s, f=float: f(s) if s not in ("", None) else None
json.dump({"lean_exit": int(rc), "wall_s": num(wall), "maxrss_mb": num(mb, int),
           "checker_exit": int(crc), "tctl_start_c": num(t0), "tctl_end_c": num(t1),
           "max_tctl_c": num(maxt), "pauses": num(pauses, int),
           "audit": {"compile_exit": int(comp), "olean": ok == "1",
                     "auditor_exit": num(arc, int), "nonce": nonce},
           "subset_parse": {"exit": int(prc), "nonce": pnonce},
           "suite_copy_writes": json.loads(writes), "late_writes": json.loads(late)},
          open(p, "w"))
PY
  printf '  %-28s lean_exit=%-3s wall=%-6s rss=%-5sMB checker_exit=%s olean=%s audit_exit=%s Tctl=%s→%s\n' \
    "$stem" "$rc" "${wall:-?}" "${mb:-?}" "$crc" "$olean_ok" "${arc:-none}" "${t0:-?}" "${t1:-?}"
done

# ---- post-run input verification (in memory; Red Team r6 concern 1(a)) -----------------
set +e
python3 -I -c "$MANIFEST_PY" verify "$RAW/inputs.json" "$INPUTS_SHA" "$RAW/inputs.verify.json" \
  "$HERE" "$MAN_TREES" "${MAN_FILES[@]}"
vrc=$?
set -e
INPUTS_OK=1
if ((vrc != 0)); then
  INPUTS_OK=0
  echo "toolcheck: INPUT MANIFEST MISMATCH after the run:"
  python3 -I -c 'import json,sys; [print("  -", p) for p in json.load(open(sys.argv[1]))["problems"]]' \
    "$RAW/inputs.verify.json" || true
fi

# ---- grade ------------------------------------------------------------------------
python3 -I - "$RAW/meta.json" "$TOOLCHAIN" "$VERSION" "$MATHLIB_SHA" "$MATHLIB_SHA7" \
  "$MANIFEST_MATHLIB_REV" "$LEAN_REPORTED" "$RUN_ID" "$MEM_MB" "$TIMEOUT" "$INNER" "$AUDITOR" \
  "${preflight[@]+"${preflight[@]}"}" <<'PY'
import json, sys, datetime, os, hashlib
p, tc, ver, sha, sha7, man, rep, rid, mem, to, inner, auditor, *pre = sys.argv[1:]
aud = {"path": auditor or None}
if auditor:
    chk = os.path.join(os.path.dirname(auditor), "check_lean_axiom_audit.py")
    aud.update(sha256=hashlib.sha256(open(auditor, "rb").read()).hexdigest(), checker=chk,
               checker_sha256=hashlib.sha256(open(chk, "rb").read()).hexdigest())
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
           "auditor": aud, "preflight_failures": pre}, open(p, "w"), indent=1)
PY

set +e
subset=(); (($# > 0)) && subset=(--only-present)
# The private grader copy must still match the manifest (Red Team r7 ask 2).
if ! gchk="$(python3 -I -c "$MANIFEST_PY" suite-check "$RAW/inputs.json" "$INPUTS_SHA" "$GDIR")"; then
  INPUTS_OK=0
  echo "toolcheck: PRIVATE GRADER COPY MISMATCH: $gchk"
fi
python3 -I "$GDIR/toolcheck.py" evaluate --raw "$RAW" --suite "$GDIR" --meta "$RAW/meta.json" \
  --out-json "$RUN_DIR/${OUT_BASE}.json" --out-md "$RUN_DIR/${OUT_BASE}.md" "${subset[@]+"${subset[@]}"}"
grc=$?
OUT_SHA="$(cat "$RUN_DIR/${OUT_BASE}.json" "$RUN_DIR/${OUT_BASE}.md" | sha256sum | cut -d' ' -f1)"
# Re-verify every input AFTER grading (Red Team r7 ask 3): nothing may have changed since the start.
python3 -I -c "$MANIFEST_PY" verify "$RAW/inputs.json" "$INPUTS_SHA" "$RAW/inputs.verify2.json" \
  "$HERE" "$MAN_TREES" "${MAN_FILES[@]}"
vrc2=$?
set -e
if ((vrc2 != 0)); then
  INPUTS_OK=0
  echo "toolcheck: INPUT MANIFEST MISMATCH after grading (see raw/inputs.verify2.json)"
fi
if ((ISO_OFF == 1)); then INPUTS_OK=0; fi
if ((${#SURVIVORS[@]} > 0)); then
  INPUTS_OK=0
  printf 'toolcheck: SURVIVING PROCESS(ES): %s\n' "${SURVIVORS[@]}"
fi
if ((${#preflight[@]} > 0)); then
  printf 'toolcheck: PREFLIGHT FAILURE: %s\n' "${preflight[@]}"
  exit 2
fi
echo "toolcheck: results → tools/lean-toolcheck/results/runs/${RUN_ID}/${OUT_BASE}.{json,md} (gitignored)"
if [[ "$UPDATE_BASELINE" == 1 ]]; then
  if ((grc == 0)) && [[ "$INPUTS_OK" == 1 ]] \
     && [[ "$(cat "$RUN_DIR/${OUT_BASE}.json" "$RUN_DIR/${OUT_BASE}.md" | sha256sum | cut -d' ' -f1)" == "$OUT_SHA" ]]; then
    cp "$RUN_DIR/${OUT_BASE}.json" "$RUN_DIR/${OUT_BASE}.md" "$HERE/results/"
    [[ "$(cat "$HERE/results/${OUT_BASE}.json" "$HERE/results/${OUT_BASE}.md" | sha256sum | cut -d' ' -f1)" == "$OUT_SHA" ]] \
      || { echo "toolcheck: baseline copy does not match the grader's output"; grc=1; }
    echo "toolcheck: --update-baseline: committed baseline results/${OUT_BASE}.{json,md} overwritten from run ${RUN_ID}"
  else
    echo "toolcheck: --update-baseline REFUSED: the run is not GREEN and VALID (or its output changed) — committed baseline left untouched"
  fi
fi
if [[ "${INPUTS_OK:-1}" != 1 ]]; then
  echo "toolcheck: RUN INVALID — an input changed, the grader copy differed, a process survived its file, or PID namespaces were off (see above and raw/inputs.verify*.json)"
  grc=1
fi
exit "$grc"
}
main "$@"; exit $?  # one line: bash never reads past it, even if this file was rewritten
