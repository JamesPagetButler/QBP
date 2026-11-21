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

ALLOWLIST (scripts/lean_axiom_allowlist.json): exact, issue-linked exceptions — fully qualified
declaration + the exact extra axiom names + an issue number. A declaration is allowed only if its
non-standard axioms EQUAL the entry's; any other non-standard axiom fails; an entry whose
declaration no longer reports exactly those axioms is STALE and fails, so the entry must be
deleted when its issue lands. No wildcards, prefixes or per-file entries. Today there is ONE
exception: the documented native_decide theorem of issue #582.

usage: check_lean_axiom_audit.py --manifest DIR/manifest.json [--json OUT] [--allowlist FILE]
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


DEFAULT_ALLOWLIST = Path(__file__).resolve().parent / "lean_axiom_allowlist.json"


def parse_axiom_list(text: str) -> set[str]:
    """`[a, b]` (Lean's rendering of the NONSTD list) -> {"a", "b"}."""
    return {
        x.strip()
        for x in text.strip().strip("[]").replace("\n", " ").split(",")
        if x.strip()
    }


def load_allowlist(path: Path, errors: list[str]) -> dict[str, dict]:
    """Exact, issue-linked exceptions. Each entry: declaration (fully qualified), axioms (exact
    names), issue (int), reason. No wildcards, prefixes or per-file entries — those are rejected.
    """
    if not path.exists():
        errors.append(f"allowlist {path} not found")
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    out: dict[str, dict] = {}
    for e in data.get("entries", []):
        decl, axs, issue = e.get("declaration"), e.get("axioms"), e.get("issue")
        bad = (
            not isinstance(decl, str)
            or not decl
            or not isinstance(axs, list)
            or not axs
            or not isinstance(issue, int)
            or not e.get("reason")
            or any(ch in s for s in [decl, *axs] for ch in "*?[]")
            or decl.endswith(".")
            or decl.endswith(".lean")
        )
        if bad:
            errors.append(
                f"malformed allowlist entry (exact names, a list of axioms, an int issue and a reason required): {e}"
            )
            continue
        if decl in out:
            errors.append(f"duplicate allowlist entry for {decl}")
        out[decl] = {"axioms": list(axs), "issue": issue}
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--json")
    ap.add_argument(
        "--allowlist",
        default=str(DEFAULT_ALLOWLIST),
        help="issue-linked exact exceptions (default scripts/lean_axiom_allowlist.json; '' = none)",
    )
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
    found_ax: dict[str, set[str]] = {}
    for b in nonstd:
        found_ax.setdefault(b["decl"], set()).update(parse_axiom_list(b["axioms"]))
    allow = load_allowlist(Path(a.allowlist), errors) if a.allowlist else {}
    uniq: set[tuple[str, str]] = set()
    allowed_hits: list[str] = []
    for decl, axs in sorted(found_ax.items()):
        mod = next(b["module"] for b in nonstd if b["decl"] == decl)
        entry = allow.get(decl)
        if entry is not None and axs == set(entry["axioms"]):
            allowed_hits.append(decl)
            print(
                f"::warning::ALLOWLISTED (issue #{entry['issue']}): {decl} (module {mod}) depends on "
                f"{sorted(axs)} — the only kind of exception this gate accepts; delete the entry when "
                f"#{entry['issue']} lands"
            )
            continue
        uniq.add((decl, str(sorted(axs))))
        why = ""
        if entry is not None:
            why = f" (allowlist entry for issue #{entry['issue']} permits exactly {sorted(entry['axioms'])})"
        print(
            f"::error::NON-STANDARD AXIOM: {decl} (module {mod}) depends on {sorted(axs)}{why}"
        )
    # A STALE entry fails too: the declaration is gone, or no longer needs exactly those axioms,
    # so the exception must be deleted (e.g. when #582 lands) rather than linger unused.
    for decl, entry in sorted(allow.items()):
        if decl not in allowed_hits and decl not in found_ax:
            errors.append(
                f"STALE allowlist entry: {decl} (issue #{entry['issue']}) — the audit no longer reports it "
                f"with {sorted(entry['axioms'])}; delete the entry from {a.allowlist}"
            )
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
                    "allowlisted": allowed_hits,
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
