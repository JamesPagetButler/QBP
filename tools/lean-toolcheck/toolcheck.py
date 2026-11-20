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
  TOOLCHECK-EXPECT: lean-error <regex>         Lean exit != 0 and ONE error message, rendered
                                               `LINE:COL: error: TEXT`, matches <regex> (re.search
                                               on that single message — anchor with ^LINE:)
  TOOLCHECK-EXPECT: lean-output <regex>        ONE warning/information message, rendered
                                               `LINE:COL: warning: TEXT`, matches <regex>
  TOOLCHECK-EXPECT: axiom <thm> <axiom>        `#print axioms <thm>` lists <axiom>
  TOOLCHECK-EXPECT: axiom-nonstd <thm>         `#print axioms <thm>` lists at least one axiom outside
                                               {propext, Classical.choice, Quot.sound} (name-agnostic:
                                               the native-evaluation axiom's name changes in Lean v4.35.0)
  TOOLCHECK-EXPECT: checker-reject <regex>     check_lean_foundations.py (zero baseline) exits 1
                                               and ONE of its `::error::` lines matches <regex>

  TOOLCHECK-EXPECT: known-limit checker-accepts            REPORT-ONLY: the checker exits 0 on the file
  TOOLCHECK-EXPECT: known-limit audit-clean <thm>          REPORT-ONLY: `#print axioms <thm>` is ⊆ std3
  TOOLCHECK-EXPECT: known-limit lean-error <regex>         REPORT-ONLY: Lean exits != 0 matching <regex>
      A known-limit row documents a gap the suite KNOWS it cannot catch (e.g. the vacuity
      check is syntactic). It is reported as "confirmed" or "changed" and never fails the
      suite; a "changed" row means the tool improved (or regressed) — read it at the bump.

A must-fail whose expected detection does not happen is a suite FAILURE. A Lean crash
(exit >= 128, e.g. 139 = SIGSEGV) is a FAILURE for every file and is never retried.
Lean is run with `--json`: only Lean's own message stream (one JSON object per line) is
trusted. An axiom report counts only if it is an `information` message positioned exactly at
a `#print axioms <thm>` command for that <thm>, and reports merge worst-case (union), so
printed text (`#eval IO.println "'x' does not depend on any axioms"`) can neither add a clean
report nor clear a real one (MF06). Expected theorem names come from a nesting-aware comment
stripper (T19). This script never treats `#eval` output as proof.
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
# Lean 4.30 prints "declaration uses `sorry`" (backticks); older toolchains used 'sorry' (quotes).
SORRY_WARN_RE = re.compile(r"declaration uses [`']sorry[`']")


def strip_comments(src: str) -> str:
    """Blank out Lean comments, preserving every newline and column (Gemini (6) on PR #824).

    A small lexer, not a regex: `/- … -/` block comments NEST in Lean (depth-counted here —
    a non-greedy `/-.*?-/` ends at the first inner `-/` and exposes the rest as "code"),
    `--` runs to end of line, and string literals are skipped so a `"/-"` or `"--"` inside a
    string neither opens a comment nor hides code. Comment characters become spaces, so
    line/column positions in the result equal those in the source (the axiom audit relies
    on that to tie each report to its `#print axioms` command).
    """
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        two = src[i : i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_str:
            if c == "\\" and i + 1 < n:
                out.append(src[i : i + 2])
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append(c)
            i += 1
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif c == "'" and i + 2 < n and src[i + 2] == "'" and src[i + 1] != "\\":
            out.append(src[i : i + 3])  # char literal such as '"' — not a string opener
            i += 3
        else:
            if c == '"':
                in_str = True
            out.append(c)
            i += 1
    return "".join(out)


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
        print(
            "  regenerate: python3 tools/lean-toolcheck/toolcheck.py imports --proofs proofs  (from the repo root)"
        )
        return 1
    print(f"toolcheck: import surface current ({len(live)} Mathlib modules)")
    return 0


# ---------------------------------------------------------------- evaluate


def lean_messages(log: str) -> tuple[list[dict], int]:
    """Lean's own message stream from `lean --json` output: one JSON object per line.

    Returns (messages, n_untrusted) — each message is {sev, line, col, text}; any other
    stdout line (e.g. from `#eval IO.println`) is UNTRUSTED and only counted.
    """
    msgs: list[dict] = []
    untrusted = 0
    for raw in log.splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            m = json.loads(raw) if raw.startswith("{") else None
        except json.JSONDecodeError:
            m = None
        if not isinstance(m, dict) or "severity" not in m or "data" not in m:
            untrusted += 1
            continue
        pos = m.get("pos") or {}
        msgs.append(
            {
                "sev": m["severity"],
                "line": pos.get("line"),
                "col": pos.get("column"),
                "text": str(m["data"]),
            }
        )
    return msgs, untrusted


def render(m: dict) -> str:
    """One message as `L:C: severity: text` — the unit every expectation regex is matched against."""
    return f"{m['line']}:{m['col']}: {m['sev']}: {m['text']}"


def print_axioms_sites(code: str) -> dict[tuple[int, int], str]:
    """(line, column) of every `#print axioms <thm>` command in comment-stripped source."""
    sites: dict[tuple[int, int], str] = {}
    for ln, line in enumerate(code.splitlines(), start=1):
        m = re.match(r"^([ \t]*)#print axioms\s+(\S+)", line)
        if m:
            sites[(ln, len(m.group(1)))] = m.group(2)
    return sites


def parse_axioms(
    msgs: list[dict], sites: dict[tuple[int, int], str]
) -> tuple[dict[str, list[str]], int]:
    """Axiom audit, spoof-resistant (Gemini (2) on PR #824).

    (a) A report counts only if it is an `information` message from Lean's message stream
        positioned EXACTLY at a `#print axioms <thm>` command for that same <thm>; text
        printed by `#eval IO.println`, `run_cmd logInfo …` or anything else is ignored.
    (b) Merge is worst-case: reports for one theorem are UNIONED, so a later "does not
        depend on any axioms" can never clear a non-standard axiom already reported.
    Returns (axioms per theorem, number of axiom-like messages rejected as unpositioned).
    """
    res: dict[str, set[str]] = {}
    rejected = 0
    for m in msgs:
        text = m["text"]
        dep = AXIOMS_RE.search(text)
        nodep = NOAXIOMS_RE.search(text)
        if not (dep or nodep):
            continue
        thm = (dep or nodep).group(1)  # type: ignore[union-attr]
        if m["sev"] != "information" or sites.get((m["line"], m["col"])) != thm:
            rejected += 1
            continue
        acc = res.setdefault(thm, set())
        if dep:
            acc.update(
                x.strip()
                for x in dep.group(2).replace("\n", " ").split(",")
                if x.strip()
            )
    return {k: sorted(v) for k, v in res.items()}, rejected


def file_kind(rel: str) -> str:
    if rel.startswith("must-fail/"):
        return "must-fail"
    if rel.startswith("known-limits/"):
        return "known-limit"
    return "tool"


def grade(src_path: Path, raw: Path, suite: Path) -> dict:
    rel = src_path.relative_to(suite).as_posix()
    stem = src_path.stem
    src = src_path.read_text(encoding="utf-8")
    expects = EXPECT_RE.findall(src)
    meta_p = raw / f"{stem}.meta.json"
    if not meta_p.exists():
        return {
            "file": rel,
            "kind": file_kind(rel),
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
    code = strip_comments(src)
    msgs, n_untrusted = lean_messages(log)
    sites = print_axioms_sites(code)
    axioms, n_rejected = parse_axioms(msgs, sites)
    errors = [render(m) for m in msgs if m["sev"] == "error"]
    warn_info = [render(m) for m in msgs if m["sev"] in ("warning", "information")]
    # checker-reject regexes are matched per `::error::` line, never against the whole output
    chk_errors = [ln for ln in chk_out.splitlines() if ln.startswith("::error")]
    lean_exit = meta.get("lean_exit")
    failures: list[str] = []
    detections: list[str] = []
    if n_rejected:
        detections.append(
            f"axiom audit ignored {n_rejected} axiom-like message(s) not positioned at a "
            f"`#print axioms` command (spoof guard)"
        )

    def any_match(rx: str, lines: list[str]) -> bool:
        return any(re.search(rx, ln) for ln in lines)

    known: list[str] = []
    kind_is_kl = file_kind(rel) == "known-limit"
    if lean_exit in (75, 86, 87, 124):
        failures.append(
            f"boxrun aborted the run (exit {lean_exit}: 75 busy / 86 thermal / 87 mem / 124 timeout)"
        )
    elif isinstance(lean_exit, int) and lean_exit >= 128:
        failures.append(
            f"Lean CRASHED (exit {lean_exit} = signal {lean_exit - 128}; "
            f"wall {meta.get('wall_s')} s, RSS {meta.get('maxrss_mb')} MB) — not retried"
        )

    kinds = [k for k, _ in expects]
    if not expects:
        failures.append("no TOOLCHECK-EXPECT line in the file header")

    for kind, arg in expects:
        if kind == "pass":
            if lean_exit != 0:
                failures.append(f"Lean exit {lean_exit} (expected 0)")
            if errors:
                failures.append("Lean reported an error")
            if any(SORRY_WARN_RE.search(w) for w in warn_info):
                failures.append("Lean reported a sorry")
            wanted = list(sites.values())
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
            elif not any_match(arg, errors):
                failures.append(f"Lean failed but without the expected message /{arg}/")
            else:
                detections.append(f"Lean rejected: /{arg}/")
        elif kind == "lean-output":
            if any_match(arg, warn_info):
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
            elif not any_match(arg, chk_errors):
                failures.append(
                    f"checker rejected but without the expected message /{arg}/"
                )
            else:
                detections.append(f"checker: /{arg}/")
        elif kind == "known-limit":
            check, _, rest = arg.partition(" ")
            if check == "checker-accepts":
                hold = chk_exit == 0
                what = f"foundations checker accepts the file (exit {chk_exit})"
            elif check == "audit-clean":
                thm = rest.strip()
                ax = axioms.get(thm)
                hold = ax is not None and not (set(ax) - STANDARD_AXIOMS)
                what = f"`#print axioms {thm}` is clean ({ax})"
            elif check == "lean-error":
                hold = lean_exit not in (0, None) and any_match(rest, errors)
                what = f"Lean still rejects with /{rest}/"
            else:
                failures.append(f"unknown known-limit check {check!r}")
                continue
            known.append(
                (
                    "KNOWN-LIMIT confirmed: "
                    if hold
                    else "KNOWN-LIMIT CHANGED (re-read): "
                )
                + what
            )
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
        "kind": file_kind(rel),
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
        "known_limits": known,
        "result": "FAIL" if failures else ("KNOWN-LIMIT" if kind_is_kl else "PASS"),
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
    files = (
        sorted((suite / "tests").glob("*.lean"))
        + sorted((suite / "must-fail").glob("*/*.lean"))
        + sorted((suite / "known-limits").glob("*/*.lean"))
    )
    if a.only_present:
        files = [f for f in files if (raw / f"{f.stem}.meta.json").exists()]
    rows = [grade(f, raw, suite) for f in files]
    # An empty suite (or an emptied layer) must be RED, never a vacuous GREEN (Gemini on PR #824).
    empty: list[str] = []
    if not rows:
        empty.append("no suite files graded — an empty suite is RED")
    elif not a.only_present:
        for layer in ("tool", "must-fail", "known-limit"):
            if not any(r["kind"] == layer for r in rows):
                empty.append(f"the {layer} layer has zero files — RED")
    meta.setdefault("preflight_failures", [])
    meta["preflight_failures"] = list(meta["preflight_failures"]) + empty
    ok = all(r["result"] in ("PASS", "KNOWN-LIMIT") for r in rows) and not meta.get(
        "preflight_failures"
    )
    doc = {
        "suite": "qbp-lean-toolcheck",
        "schema": 1,
        **meta,
        "files": rows,
        "summary": {
            "files": len(rows),
            "pass": sum(r["result"] in ("PASS", "KNOWN-LIMIT") for r in rows),
            "fail": sum(r["result"] == "FAIL" for r in rows),
            "tool_files": sum(r["kind"] == "tool" for r in rows),
            "must_fail_files": sum(r["kind"] == "must-fail" for r in rows),
            "known_limit_files": sum(r["kind"] == "known-limit" for r in rows),
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
        det = (
            "; ".join(r["failures"] or (r["detections"] + r.get("known_limits", [])))
            or "—"
        )
        lines.append(
            f"| `{r['file']}` | {r['kind']} | { {'PASS': '✅', 'KNOWN-LIMIT': '🟡'}.get(r['result'], '❌') } {r['result']} | "
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
