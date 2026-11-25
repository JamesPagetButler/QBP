#!/usr/bin/env python3
"""Lean CI axiom audit, checker side — QBP issue #827 AC2/AC3.

Grades the outputs of the trusted auditor program `scripts/LeanAxiomAudit.lean`, run once per
default-target root with the arguments `gen_lean_axiom_audit.py` wrote. The auditor makes LEAN
enumerate every constant of every in-scope module and compute its exact axiom closure; this
script only checks what Lean reported. RULE 1: ANY axiom outside {propext, Classical.choice,
Quot.sound} FAILS — `sorryAx`, a native-evaluation axiom of whatever name the toolchain emits
(per-call `…_native.native_decide.ax_…` since Lean 4.29; `Lean.ofReduceBool` before), any user
`axiom`. The gate never keys on a specific native-axiom name; the standard-three filter itself
runs inside the auditor.

Trust model (PR #829: Gemini r1 finding 1, Red Team findings 1, 2, 4). The auditor is elaborated
against the toolchain only and loads the audited modules at run time as data
(`importModules (loadExts := false)`, initializers never enabled): no macro, notation, instance
or `initialize` block of an audited module can change what it computes or prints. On top:
  * each run's stdout is redirected into a fresh file and must hold EXACTLY ONE result line
    (`{"mark": "AXIOM-AUDIT-827", …}`); other lines are shown, never graded;
  * the result must carry the run's NONCE (fresh per generation, after `lake build`) and root;
  * SCOPE is Lean's: every module the root really loads whose .olean is a project build output.
    Every module of the Python import closure must be in it (`missing == []`), every loaded
    module's .olean must resolve (`unresolved == []`), and at least one declaration must be
    audited. Modules of `proofs/` that NO run loaded are listed as not covered;
  * a run with no output (crash, failed import), a malformed result, or no runs at all FAILS;
  * CI runs THIS script, the auditor and the allowlist from a copy taken BEFORE `lake build`, so
    code run during the build (`#eval`) cannot rewrite them (Red Team 2, e3).
Known limit: the .olean files are trusted as `lake build` wrote them; there is no kernel re-check
(lean4checker's job).

ALLOWLIST (scripts/lean_axiom_allowlist.json): exact, issue-linked exceptions. An entry names ONE
declaration and PINS its identity (Red Team 3): its module and a SHA-256 fingerprint (computed in
Lean: the constant's canonical statement/body plus every project constant it reaches), and for
EACH excepted axiom: name, module and fingerprint. A declaration is allowed only if its name,
module and fingerprint match AND its non-standard axioms are EXACTLY the entry's, each with the
pinned module and fingerprint. A forged same-named declaration or axiom (other statement, other
module) fails. The pins are identity checks for the allowlist only — no axiom name ever decides
pass or fail. An entry whose declaration is not reported, or no longer matches, is STALE and
fails (delete or re-pin it after review; never widen). No wildcards, prefixes or per-file
entries. TRANSITIVE: matching is by exact name against each declaration's FULL closure, so any
declaration that depends on an excepted one inherits its axiom and fails.

usage: check_lean_axiom_audit.py --manifest DIR/manifest.json [--json OUT] [--allowlist FILE]
       (expects DIR/AxiomAudit_<k>.out, the auditor's stdout for each run, as written by CI)
Exit 0 = pass, 1 = fail.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

MARK = "AXIOM-AUDIT-827"
DEFAULT_ALLOWLIST = Path(__file__).resolve().parent / "lean_axiom_allowlist.json"
_BAD_CHARS = "*?[]"
REJECTED: list[dict] = []  # malformed allowlist entries (reported in --json as a count)


def read_output(p: Path) -> tuple[list[dict], int]:
    """(result objects carrying the audit mark, count of other non-empty lines)."""
    results, other = [], 0
    for raw in p.read_text(encoding="utf-8", errors="replace").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            m = json.loads(raw) if raw.startswith("{") else None
        except json.JSONDecodeError:
            m = None
        if isinstance(m, dict) and m.get("mark") == MARK:
            results.append(m)
        else:
            other += 1
    return results, other


def sha(text: str | None) -> str | None:
    return None if text is None else hashlib.sha256(text.encode("utf-8")).hexdigest()


def _exact_name(s: object) -> bool:
    return (
        isinstance(s, str)
        and bool(s)
        and not any(ch in s for ch in _BAD_CHARS)
        and not s.endswith(".")
        and not s.endswith(".lean")
    )


def _hex64(s: object) -> bool:
    return (
        isinstance(s, str) and len(s) == 64 and all(c in "0123456789abcdef" for c in s)
    )


def load_allowlist(path: Path, errors: list[str]) -> dict[str, dict]:
    """Exact, issue-linked, identity-pinned exceptions (see the module docstring)."""
    if not path.exists():
        errors.append(f"allowlist {path} not found")
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    out: dict[str, dict] = {}
    for e in data.get("entries", []):
        axs = e.get("axioms") if isinstance(e, dict) else None
        ok = (
            isinstance(e, dict)
            and _exact_name(e.get("declaration"))
            and _exact_name(e.get("module"))
            and _hex64(e.get("fingerprint"))
            and isinstance(e.get("issue"), int)
            and bool(e.get("reason"))
            and isinstance(axs, list)
            and bool(axs)
            and all(
                isinstance(x, dict)
                and _exact_name(x.get("name"))
                and _exact_name(x.get("module"))
                and _hex64(x.get("fingerprint"))
                for x in axs
            )
            and len({x["name"] for x in axs}) == len(axs)
        )
        if not ok:
            REJECTED.append(e)
            errors.append(
                "malformed allowlist entry (exact declaration + module + fingerprint, a list of "
                f"axioms each with exact name + module + fingerprint, an int issue and a reason): {e}"
            )
            continue
        decl = e["declaration"]
        if decl in out:
            errors.append(f"duplicate allowlist entry for {decl}")
        out[decl] = {
            "module": e["module"],
            "fingerprint": e["fingerprint"],
            "axioms": {x["name"]: (x["module"], x["fingerprint"]) for x in axs},
            "issue": e["issue"],
        }
    return out


def entry_mismatch(b: dict, entry: dict) -> str:
    """'' if the reported declaration `b` is exactly the allowlisted one; else the reason."""
    if b["module"] != entry["module"]:
        return f"module {b['module']} ≠ pinned {entry['module']}"
    if sha(b.get("fp")) != entry["fingerprint"]:
        return f"fingerprint {sha(b.get('fp'))} ≠ pinned {entry['fingerprint']}"
    got = {x["name"]: x for x in b["axioms"]}
    if set(got) != set(entry["axioms"]):
        return f"axioms {sorted(got)} ≠ exactly {sorted(entry['axioms'])}"
    for name, (mod, fp) in entry["axioms"].items():
        if got[name]["module"] != mod:
            return f"axiom {name}: module {got[name]['module']} ≠ pinned {mod}"
        if sha(got[name].get("fp")) != fp:
            return f"axiom {name}: fingerprint {sha(got[name].get('fp'))} ≠ pinned {fp}"
    return ""


def grade_run(d: dict, errors: list[str]) -> tuple[list[dict], int, list[str]] | None:
    """Validate one auditor run; (non-standard entries, declarations, scope) or None."""
    out = Path(d["output"])
    tag = d["label"]
    if not out.exists():
        errors.append(f"[{tag}] no auditor output {out.name} — the run did not happen")
        return None
    results, other = read_output(out)
    if other:
        print(f"[{tag}] {other} non-result output line(s) ignored")
    if len(results) != 1:
        errors.append(
            f"[{tag}] expected exactly 1 auditor result line, found {len(results)}"
        )
        return None
    r = results[0]
    if r.get("nonce") != d["nonce"]:
        errors.append(
            f"[{tag}] auditor result carries the wrong nonce — not this run's output"
        )
        return None
    if r.get("root") != tag:
        errors.append(f"[{tag}] auditor result is for another root ({r.get('root')})")
        return None
    scope, missing, unresolved = r.get("scope"), r.get("missing"), r.get("unresolved")
    decls, bad_raw = r.get("declarations"), r.get("nonstd")
    if not (
        isinstance(scope, list)
        and isinstance(missing, list)
        and isinstance(unresolved, list)
        and isinstance(decls, int)
        and isinstance(bad_raw, list)
    ):
        errors.append(f"[{tag}] malformed auditor result")
        return None
    if missing or not set(d["modules"]) <= set(scope):
        errors.append(
            f"[{tag}] in-scope module(s) absent from Lean's loaded scope: "
            f"{sorted(set(missing) | (set(d['modules']) - set(scope)))}"
        )
    if unresolved:
        errors.append(
            f"[{tag}] loaded module(s) whose .olean did not resolve: {unresolved}"
        )
    if decls <= 0:
        errors.append(
            f"[{tag}] zero declarations audited — an empty audit is a failure"
        )
    extra = sorted(set(scope) - set(d["modules"]))
    if extra:
        print(
            f"[{tag}] Lean's scope includes {len(extra)} module(s) the Python import parser "
            f"did not list (audited anyway): {', '.join(extra)}"
        )
    bad_here = []
    for b in bad_raw:
        ok = (
            isinstance(b, dict)
            and isinstance(b.get("decl"), str)
            and isinstance(b.get("module"), str)
            and isinstance(b.get("axioms"), list)
            and bool(b["axioms"])
            and all(
                isinstance(x, dict)
                and isinstance(x.get("name"), str)
                and isinstance(x.get("module"), str)
                for x in b["axioms"]
            )
        )
        if not ok:
            errors.append(f"[{tag}] malformed non-standard entry: {b}")
            continue
        bad_here.append(dict(b, root=tag))
    print(
        f"axiom audit [{tag}]: Lean scope {len(scope)} module(s), {decls} declarations, "
        f"{len(bad_here)} non-standard"
    )
    return bad_here, decls, [str(s) for s in scope]


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
    audited: set[str] = set()
    if not drivers:
        errors.append("no audit runs — an empty audit is a failure")
    for d in drivers:
        g = grade_run(d, errors)
        if g is None:
            continue
        bad_here, decls, scope = g
        total_decls += decls
        audited.update(scope)
        nonstd.extend(bad_here)
    allow = load_allowlist(Path(a.allowlist), errors) if a.allowlist else {}
    # One verdict per declaration (overlapping roots report the same declaration); every report
    # of a declaration must match its entry for it to be allowed.
    by_decl: dict[str, list[dict]] = {}
    for b in nonstd:
        by_decl.setdefault(b["decl"], []).append(b)
    uniq: set[tuple[str, str]] = set()
    allowed_hits: list[str] = []
    stale_reason: dict[str, str] = {}
    # TRANSITIVE by construction (Cartan, seq 5688): each declaration's axiom set is its FULL
    # closure, computed by Lean, and the allowlist is matched by EXACT declaration name only, so
    # a dependent of an excepted declaration has no entry of its own and FAILS. No axiom name
    # decides pass or fail (architect, seq 5690); the names below only word the failure hint.
    excepted_axioms = {x for e in allow.values() for x in e["axioms"]}
    for decl, reports in sorted(by_decl.items()):
        axs = sorted({x["name"] for b in reports for x in b["axioms"]})
        mod = reports[0]["module"]
        entry = allow.get(decl)
        if entry is not None:
            why = next(
                (m for m in (entry_mismatch(b, entry) for b in reports) if m), ""
            )
            if not why:
                allowed_hits.append(decl)
                print(
                    f"::warning::ALLOWLISTED (issue #{entry['issue']}): {decl} (module {mod}) "
                    f"depends on {axs} — identity pinned (module + fingerprint); delete the entry "
                    f"when #{entry['issue']} lands"
                )
                continue
            stale_reason[decl] = why
            hint = (
                f" (allowlist entry for issue #{entry['issue']} does not match: {why})"
            )
        elif set(axs) & excepted_axioms:
            hint = (
                f" — inherits {sorted(set(axs) & excepted_axioms)} from an allowlisted "
                f"declaration; dependents of an exception are NOT excused (transitive gate)"
            )
        else:
            hint = ""
        uniq.add((decl, str(axs)))
        print(
            f"::error::NON-STANDARD AXIOM: {decl} (module {mod}) depends on {axs}{hint}"
        )
    # STALE: an entry whose declaration is not reported, or no longer matches its pins, fails —
    # the exception must be deleted (e.g. when #582 lands) or re-pinned after review, never kept.
    for decl, entry in sorted(allow.items()):
        if decl not in allowed_hits:
            why = stale_reason.get(decl, "the audit does not report this declaration")
            errors.append(
                f"STALE allowlist entry: {decl} (issue #{entry['issue']}) — {why}; delete or "
                f"re-pin it in {a.allowlist}"
            )
            for b in by_decl.get(decl, []):
                print(
                    f"observed pins for {decl}: module={b['module']} fingerprint={sha(b.get('fp'))} "
                    "axioms="
                    + json.dumps(
                        [
                            {
                                "name": x["name"],
                                "module": x["module"],
                                "fingerprint": sha(x.get("fp")),
                            }
                            for x in b["axioms"]
                        ]
                    )
                )
    for e in errors:
        print(f"::error::{e}")
    every = man.get("all_modules", [])
    not_covered = sorted(set(every) - audited)
    print(
        f"coverage (AC3): EVERY constant (theorem, def, instance, axiom, inductive, auxiliary) of the "
        f"{len(audited)} project module(s) Lean actually loaded for the default targets — enumerated "
        f"by Lean, independent of how the source is written ({total_decls} declaration audits, "
        f"overlapping roots counted per root). NOT covered (no default target loads them): "
        f"{', '.join(not_covered) or 'none'}."
    )
    if a.json:
        Path(a.json).write_text(
            json.dumps(
                {
                    "non_standard": sorted(map(list, uniq)),
                    "allowlisted": allowed_hits,
                    "errors": errors,
                    "rejected_entries": len(REJECTED),
                    "modules": sorted(audited),
                    "declaration_audits": total_decls,
                    "not_covered": not_covered,
                    "reports": nonstd,
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
