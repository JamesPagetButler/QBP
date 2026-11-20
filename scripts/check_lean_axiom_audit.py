#!/usr/bin/env python3
"""Lean CI axiom audit, checker side — QBP issue #827 AC2/AC3.

Grades the outputs of the driver files written by `gen_lean_axiom_audit.py` and run with
`lake env lean --json <driver>`. The drivers make LEAN enumerate every constant of every
in-scope module (the default targets' import closure) and compute its axiom closure; this
script only checks what Lean reported. A non-standard axiom — `sorryAx`, a native-evaluation
axiom (`…_native.native_decide.ax_…`, `Lean.ofReduceBool`), any user `axiom` — FAILS.

Trust rules (as in PR #824's toolcheck grader, Gemini (2)):
  * only Lean's own `--json` message stream is read; any other output line (e.g. printed by an
    imported module's `initialize`) is untrusted and ignored;
  * a message counts only if its `fileName` is the driver itself and it is positioned at the
    driver's `run_cmd` line (recorded by the generator) — imported modules cannot place
    messages there;
  * the driver must emit exactly one `SUMMARY` information message with
    `modules=K/K` (every in-scope module of that root was found in the environment) and
    `declarations>0`; `bad` must equal the number of `NONSTD` error messages; ANY other error
    message in the driver (failed import, missing module, elaboration error) FAILS;
  * an empty audit (no drivers, no declarations) FAILS.

usage: check_lean_axiom_audit.py --manifest DIR/manifest.json [--json OUT]
       (expects DIR/AxiomAudit_<k>.jsonl next to each driver, as written by the CI step)
Exit 0 = pass, 1 = fail.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path

MARK = "AXIOM-AUDIT-827"
SUMMARY = re.compile(
    rf"^{MARK} SUMMARY root=(?P<root>\S+) modules=(?P<found>\d+)/(?P<total>\d+) "
    r"declarations=(?P<decls>\d+) bad=(?P<bad>\d+)\s*$"
)
NONSTD = re.compile(
    rf"^{MARK} NONSTD (?P<decl>\S+) module=(?P<mod>\S+) axioms=(?P<ax>.*)$", re.DOTALL
)


def read_jsonl(p: Path) -> tuple[list[dict], int]:
    msgs, untrusted = [], 0
    for raw in p.read_text(encoding="utf-8", errors="replace").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            m = json.loads(raw) if raw.startswith("{") else None
        except json.JSONDecodeError:
            m = None
        if isinstance(m, dict) and "severity" in m and "data" in m:
            msgs.append(m)
        else:
            untrusted += 1
    return msgs, untrusted


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--json")
    a = ap.parse_args()
    man = json.loads(Path(a.manifest).read_text())
    drivers = man.get("drivers", [])
    errors: list[str] = []
    nonstd: list[dict] = []
    total_decls = 0
    audited_modules: set[str] = set()
    if not drivers:
        errors.append("no audit drivers — an empty audit is a failure")
    for d in drivers:
        drv = Path(d["file"])
        out = drv.with_suffix(".jsonl")
        tag = d["root"] or "(explicit)"
        if not out.exists():
            errors.append(f"[{tag}] no Lean output {out.name} — driver not run")
            continue
        msgs, untrusted = read_jsonl(out)
        mine = [
            m
            for m in msgs
            if os.path.realpath(str(m.get("fileName", "")))
            == os.path.realpath(str(drv))
        ]
        at_cmd = [
            m for m in mine if (m.get("pos") or {}).get("line") == d["run_cmd_line"]
        ]
        summaries = [
            SUMMARY.match(m["data"].strip())
            for m in at_cmd
            if m["severity"] == "information" and SUMMARY.match(m["data"].strip())
        ]
        bad_here = []
        for m in at_cmd:
            if m["severity"] == "error":
                hit = NONSTD.match(m["data"].strip())
                if hit:
                    bad_here.append(
                        {
                            "decl": hit["decl"],
                            "module": hit["mod"],
                            "axioms": hit["ax"].strip(),
                            "root": tag,
                        }
                    )
        others = [
            m
            for m in mine
            if m["severity"] == "error"
            and not (m in at_cmd and NONSTD.match(m["data"].strip()))
        ]
        for m in others:
            errors.append(
                f"[{tag}] Lean error in the driver: {m['data'].strip()[:300]}"
            )
        if len(summaries) != 1:
            errors.append(
                f"[{tag}] expected exactly 1 positioned SUMMARY, found {len(summaries)}"
            )
            continue
        s = summaries[0]
        found, total, decls, bad = (
            int(s["found"]),
            int(s["total"]),
            int(s["decls"]),
            int(s["bad"]),
        )
        if found != total or total != len(d["modules"]):
            errors.append(
                f"[{tag}] only {found}/{total} in-scope modules present (manifest lists {len(d['modules'])})"
            )
        if decls == 0:
            errors.append(
                f"[{tag}] zero declarations audited — an empty audit is a failure"
            )
        if bad != len(bad_here):
            errors.append(
                f"[{tag}] SUMMARY says bad={bad} but {len(bad_here)} NONSTD message(s) were found"
            )
        total_decls += decls
        audited_modules.update(d["modules"])
        nonstd.extend(bad_here)
        print(
            f"axiom audit [{tag}]: {found}/{total} modules, {decls} declarations, {bad} non-standard; "
            f"{untrusted} untrusted non-JSON line(s) ignored"
        )
    uniq = {(b["decl"], b["axioms"]) for b in nonstd}
    for decl, ax in sorted(uniq):
        mod = next(b["module"] for b in nonstd if b["decl"] == decl)
        print(f"::error::NON-STANDARD AXIOM: {decl} (module {mod}) depends on {ax}")
    for e in errors:
        print(f"::error::{e}")
    not_built = man.get("not_built", [])
    print(
        f"coverage (AC3): EVERY constant (theorem, def, instance, axiom, inductive, auxiliary) of the "
        f"{len(audited_modules)} module(s) in the default targets' import closure — enumerated by Lean from the "
        f"elaborated environment, independent of how the source is written ({total_decls} declaration audits, "
        f"overlapping closures counted per root). NOT covered: modules no default target builds: "
        f"{', '.join(not_built) or 'none'}."
    )
    if a.json:
        Path(a.json).write_text(
            json.dumps(
                {
                    "non_standard": sorted(map(list, uniq)),
                    "errors": errors,
                    "modules": sorted(audited_modules),
                    "declaration_audits": total_decls,
                    "not_built": not_built,
                },
                indent=1,
            )
            + "\n"
        )
    failed = bool(uniq or errors)
    print("axiom audit " + ("FAILED." if failed else "PASSED."))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
