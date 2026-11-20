#!/usr/bin/env python3
"""QBP Lean toolcheck — evaluator + helpers for run.sh (issue #823 W5).

Subcommands
  pins      --proofs DIR                  print toolchain, mathlib sha, sha7, manifest rev (shell-friendly)
  imports   --proofs DIR                  print the Mathlib modules QBP imports (comment-stripped, sorted)
  check-imports --proofs DIR --file F     exit 1 if F's import list != the live QBP Mathlib import set
  evaluate  --raw DIR --suite DIR --out-json F --out-md F [--meta F]
                                          grade every run against its TOOLCHECK-EXPECT lines

Expectation lines live in each .lean file's header comment:
  TOOLCHECK-EXPECT: pass                       Lean exit 0, no error / sorry, every `#print axioms`
                                               result within {propext, Classical.choice, Quot.sound},
                                               one axiom report per `#print axioms` line, and the
                                               foundations checker accepts the file
  TOOLCHECK-EXPECT: lean-ok                    Lean exit 0
  TOOLCHECK-EXPECT: lean-error <regex>         Lean exit != 0 and the output matches <regex>
  TOOLCHECK-EXPECT: lean-output <regex>        the output matches <regex>
  TOOLCHECK-EXPECT: axiom <thm> <axiom>        `#print axioms <thm>` lists <axiom>
  TOOLCHECK-EXPECT: axiom-nonstd <thm>         `#print axioms <thm>` lists at least one axiom outside
                                               {propext, Classical.choice, Quot.sound} (name-agnostic:
                                               the native-evaluation axiom's name changes in Lean v4.35.0)
  TOOLCHECK-EXPECT: checker-reject <regex>     check_lean_foundations.py (zero baseline) exits 1
                                               and its output matches <regex>

A must-fail whose expected detection does not happen is a suite FAILURE.
This script only reads Lean's text output; it never treats `#eval` output as proof.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# [ \t] not \s: a `\s*` here would run across the newline and swallow the NEXT expectation
# line into this one's argument (caught on the first suite run: MF02's axiom check vanished).
EXPECT_RE = re.compile(r"^TOOLCHECK-EXPECT:[ \t]*(\S+)[ \t]*(.*?)[ \t]*$", re.MULTILINE)
AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]", re.DOTALL)
NOAXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")
PRINT_AXIOMS_RE = re.compile(r"^#print axioms\s+(\S+)", re.MULTILINE)
# Lean 4.30 prints "declaration uses `sorry`" (backticks); older toolchains used 'sorry' (quotes).
SORRY_WARN_RE = re.compile(r"declaration uses [`']sorry[`']")
ERROR_RE = re.compile(r"^\S+:\d+:\d+: error", re.MULTILINE)


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)
    return re.sub(r"--.*", "", src)


# ---------------------------------------------------------------- pins


def read_pins(proofs: Path) -> dict:
    toolchain = (proofs / "lean-toolchain").read_text().strip()
    lake = (proofs / "lakefile.lean").read_text()
    m = re.search(
        r'require\s+mathlib\s+from\s+git\s+"[^"]+"\s*@\s*"([0-9a-f]{40})"', lake
    )
    if not m:
        raise SystemExit("toolcheck: cannot find the Mathlib sha in lakefile.lean")
    sha = m.group(1)
    manifest_rev = ""
    mf = proofs / "lake-manifest.json"
    if mf.exists():
        for pkg in json.loads(mf.read_text()).get("packages", []):
            if pkg.get("name") == "mathlib":
                manifest_rev = pkg.get("rev", "")
    version = toolchain.split(":", 1)[-1]
    return {
        "toolchain": toolchain,
        "version": version,
        "mathlib_sha": sha,
        "mathlib_sha7": sha[:7],
        "manifest_mathlib_rev": manifest_rev,
    }


def cmd_pins(a: argparse.Namespace) -> int:
    p = read_pins(Path(a.proofs))
    for k, v in p.items():
        print(f"{k.upper()}={v}")
    return 0


# ---------------------------------------------------------------- imports


def qbp_mathlib_imports(proofs: Path) -> list[str]:
    mods: set[str] = set()
    for f in proofs.rglob("*.lean"):
        parts = f.relative_to(proofs).parts
        if parts[0] in (".lake", "lean-toolcheck"):
            continue
        code = strip_comments(f.read_text(encoding="utf-8", errors="replace"))
        mods.update(re.findall(r"^[ \t]*import\s+(Mathlib[\w.]*)", code, re.MULTILINE))
    return sorted(mods)


def cmd_imports(a: argparse.Namespace) -> int:
    for m in qbp_mathlib_imports(Path(a.proofs)):
        print(m)
    return 0


def cmd_check_imports(a: argparse.Namespace) -> int:
    live = set(qbp_mathlib_imports(Path(a.proofs)))
    code = strip_comments(Path(a.file).read_text())
    have = set(re.findall(r"^[ \t]*import\s+(Mathlib[\w.]*)", code, re.MULTILINE))
    missing, extra = sorted(live - have), sorted(have - live)
    if missing or extra:
        print(f"toolcheck: import surface STALE — {a.file}")
        for m in missing:
            print(f"  missing (QBP imports it, the surface file does not): {m}")
        for m in extra:
            print(f"  extra (no QBP file imports it any more): {m}")
        print("  regenerate: python3 lean-toolcheck/toolcheck.py imports --proofs .")
        return 1
    print(f"toolcheck: import surface current ({len(live)} Mathlib modules)")
    return 0


# ---------------------------------------------------------------- evaluate


def parse_axioms(out: str) -> dict[str, list[str]]:
    res: dict[str, list[str]] = {}
    for thm, lst in AXIOMS_RE.findall(out):
        res[thm] = sorted(
            x.strip() for x in lst.replace("\n", " ").split(",") if x.strip()
        )
    for thm in NOAXIOMS_RE.findall(out):
        res[thm] = []
    return res


def grade(src_path: Path, raw: Path, suite: Path) -> dict:
    rel = src_path.relative_to(suite).as_posix()
    stem = src_path.stem
    src = src_path.read_text(encoding="utf-8")
    expects = EXPECT_RE.findall(src)
    meta_p = raw / f"{stem}.meta.json"
    if not meta_p.exists():
        return {
            "file": rel,
            "kind": "must-fail" if rel.startswith("must-fail/") else "tool",
            "expect": [f"{k} {a}".strip() for k, a in expects],
            "lean_exit": None,
            "wall_s": None,
            "maxrss_mb": None,
            "axioms": {},
            "detections": [],
            "failures": [
                "not run (no raw result) — the suite was interrupted or skipped it"
            ],
            "result": "FAIL",
        }
    log = (raw / f"{stem}.log").read_text(encoding="utf-8", errors="replace")
    meta = json.loads(meta_p.read_text())
    chk_out_p = raw / f"{stem}.checker.log"
    chk_out = chk_out_p.read_text() if chk_out_p.exists() else ""
    chk_exit = meta.get("checker_exit")
    axioms = parse_axioms(log)
    lean_exit = meta.get("lean_exit")
    failures: list[str] = []
    detections: list[str] = []

    if lean_exit in (75, 86, 87, 124):
        failures.append(
            f"boxrun aborted the run (exit {lean_exit}: 75 busy / 86 thermal / 87 mem / 124 timeout)"
        )

    kinds = [k for k, _ in expects]
    if not expects:
        failures.append("no TOOLCHECK-EXPECT line in the file header")

    for kind, arg in expects:
        if kind == "pass":
            if lean_exit != 0:
                failures.append(f"Lean exit {lean_exit} (expected 0)")
            if ERROR_RE.search(log):
                failures.append("Lean reported an error")
            if SORRY_WARN_RE.search(log):
                failures.append("Lean reported a sorry")
            wanted = PRINT_AXIOMS_RE.findall(strip_comments(src))
            for thm in wanted:
                if thm not in axioms:
                    failures.append(f"no axiom report for {thm}")
            for thm, ax in axioms.items():
                extra = set(ax) - STANDARD_AXIOMS
                if extra:
                    failures.append(f"{thm}: non-standard axioms {sorted(extra)}")
            if not wanted:
                failures.append("a pass file must end with at least one #print axioms")
            if chk_exit != 0:
                failures.append(
                    f"foundations checker rejected a pass file (exit {chk_exit})"
                )
        elif kind == "lean-ok":
            if lean_exit != 0:
                failures.append(
                    f"Lean exit {lean_exit} (expected 0 — Lean should accept)"
                )
        elif kind == "lean-error":
            if lean_exit == 0:
                failures.append(
                    f"Lean ACCEPTED a must-fail file (expected error /{arg}/)"
                )
            elif not re.search(arg, log):
                failures.append(f"Lean failed but without the expected message /{arg}/")
            else:
                detections.append(f"Lean rejected: /{arg}/")
        elif kind == "lean-output":
            if re.search(arg, log):
                detections.append(f"Lean output: /{arg}/")
            else:
                failures.append(f"expected Lean output /{arg}/ not found")
        elif kind == "axiom":
            thm, ax = arg.split()
            if thm not in axioms:
                failures.append(f"no axiom report for {thm}")
            elif ax not in axioms[thm]:
                failures.append(f"axiom audit MISSED {ax} on {thm} (got {axioms[thm]})")
            else:
                detections.append(f"axiom audit: {thm} ⊇ {ax}")
        elif kind == "axiom-nonstd":
            thm = arg.strip()
            if thm not in axioms:
                failures.append(f"no axiom report for {thm}")
            else:
                nonstd = sorted(set(axioms[thm]) - STANDARD_AXIOMS)
                if nonstd:
                    detections.append(f"axiom audit: {thm} has non-standard {nonstd}")
                else:
                    failures.append(
                        f"axiom audit MISSED: {thm} shows only standard axioms {axioms[thm]}"
                    )
        elif kind == "checker-reject":
            if chk_exit != 1:
                failures.append(f"foundations checker did not reject (exit {chk_exit})")
            elif not re.search(arg, chk_out):
                failures.append(
                    f"checker rejected but without the expected message /{arg}/"
                )
            else:
                detections.append(f"checker: /{arg}/")
        else:
            failures.append(f"unknown expectation kind {kind!r}")

    # Non-pass files: any non-standard axiom must be EXPECTED (an unexpected one is a failure).
    if "pass" not in kinds:
        expected_ax = {tuple(a.split()) for k, a in expects if k == "axiom"}
        any_ok = {a.strip() for k, a in expects if k == "axiom-nonstd"}
        for thm, ax in axioms.items():
            if thm in any_ok:
                continue
            for x in set(ax) - STANDARD_AXIOMS:
                if (thm, x) not in expected_ax:
                    failures.append(f"{thm}: unexpected non-standard axiom {x}")

    return {
        "file": rel,
        "kind": "must-fail" if rel.startswith("must-fail/") else "tool",
        "expect": [f"{k} {a}".strip() for k, a in expects],
        "lean_exit": lean_exit,
        "wall_s": meta.get("wall_s"),
        "maxrss_mb": meta.get("maxrss_mb"),
        "tctl_start_c": meta.get("tctl_start_c"),
        "tctl_end_c": meta.get("tctl_end_c"),
        "max_tctl_c": meta.get("max_tctl_c"),
        "guard_pauses": meta.get("pauses"),
        "checker_exit": chk_exit,
        "axioms": axioms,
        "detections": detections,
        "failures": failures,
        "result": "PASS" if not failures else "FAIL",
    }


def axiom_summary(axioms: dict[str, list[str]]) -> str:
    sets = {tuple(v) for v in axioms.values()}
    extra = sorted({x for v in axioms.values() for x in v} - STANDARD_AXIOMS)
    if not axioms:
        return "—"
    if not extra:
        return f"{len(axioms)} thm ⊆ std3"
    return f"{len(axioms)} thm; non-std: {', '.join(extra)}" + ("" if len(sets) else "")


def cmd_evaluate(a: argparse.Namespace) -> int:
    raw, suite = Path(a.raw), Path(a.suite)
    meta = json.loads(Path(a.meta).read_text()) if a.meta else {}
    files = sorted((suite / "tests").glob("*.lean")) + sorted(
        (suite / "must-fail").glob("*/*.lean")
    )
    if a.only_present:
        files = [f for f in files if (raw / f"{f.stem}.meta.json").exists()]
    rows = [grade(f, raw, suite) for f in files]
    ok = all(r["result"] == "PASS" for r in rows) and not meta.get("preflight_failures")
    doc = {
        "suite": "qbp-lean-toolcheck",
        "schema": 1,
        **meta,
        "files": rows,
        "summary": {
            "files": len(rows),
            "pass": sum(r["result"] == "PASS" for r in rows),
            "fail": sum(r["result"] == "FAIL" for r in rows),
            "tool_files": sum(r["kind"] == "tool" for r in rows),
            "must_fail_files": sum(r["kind"] == "must-fail" for r in rows),
            "theorems_audited": sum(len(r["axioms"]) for r in rows),
            "overall": "GREEN" if ok else "RED",
        },
    }
    Path(a.out_json).write_text(json.dumps(doc, indent=2, ensure_ascii=False) + "\n")

    lines = [
        f"# Lean toolcheck results — {meta.get('toolchain', '?')} / Mathlib {meta.get('mathlib_sha7', '?')}",
        "",
        f"Run {meta.get('run_id', '?')} · {meta.get('date_utc', '?')} · overall **{doc['summary']['overall']}** "
        f"({doc['summary']['pass']}/{doc['summary']['files']} as expected)",
        "",
        "| File | Kind | Result | Lean exit | Wall (s) | Max RSS (MB) | Tctl start→end (°C) | Axiom audit | Detections / failures |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for r in rows:
        det = "; ".join(r["failures"] or r["detections"]) or "—"
        lines.append(
            f"| `{r['file']}` | {r['kind']} | {'✅' if r['result'] == 'PASS' else '❌'} {r['result']} | "
            f"{r['lean_exit']} | {r['wall_s']} | {r['maxrss_mb']} | {r.get('tctl_start_c')}→{r.get('tctl_end_c')} | "
            f"{axiom_summary(r['axioms'])} | {det} |"
        )
    for pf in meta.get("preflight_failures", []):
        lines.append(f"\n**Preflight failure:** {pf}")
    Path(a.out_md).write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("pins")
    p.add_argument("--proofs", required=True)
    p.set_defaults(fn=cmd_pins)
    p = sub.add_parser("imports")
    p.add_argument("--proofs", required=True)
    p.set_defaults(fn=cmd_imports)
    p = sub.add_parser("check-imports")
    p.add_argument("--proofs", required=True)
    p.add_argument("--file", required=True)
    p.set_defaults(fn=cmd_check_imports)
    p = sub.add_parser("evaluate")
    p.add_argument("--raw", required=True)
    p.add_argument("--suite", required=True)
    p.add_argument("--out-json", required=True)
    p.add_argument("--out-md", required=True)
    p.add_argument("--meta")
    p.add_argument(
        "--only-present",
        action="store_true",
        help="grade only files that were run (subset runs)",
    )
    p.set_defaults(fn=cmd_evaluate)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
