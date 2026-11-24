#!/usr/bin/env python3
"""Lean CI axiom audit, checker side — QBP issue #827 AC2/AC3.

Grades the outputs of the fixed auditor program `scripts/LeanAxiomAudit.lean`, run once per
default-target root with the arguments `gen_lean_axiom_audit.py` wrote. The auditor makes LEAN
enumerate every constant of every in-scope module (the default targets' import closure) and
compute its axiom closure; this script only checks what Lean reported. RULE 1: ANY axiom
outside {propext, Classical.choice, Quot.sound} FAILS — `sorryAx`, a native-evaluation axiom of
whatever name the toolchain emits (per-call `…_native.native_decide.ax_…` since Lean 4.29;
`Lean.ofReduceBool` before), any user `axiom`. The gate never keys on a specific native-axiom
name; the standard-three filter itself runs inside the auditor.

Trust model (PR #829, Gemini r1 finding 1). The auditor is elaborated against the toolchain
only and loads the audited modules at run time as data (`importModules (loadExts := false)`):
no macro, notation, instance or initializer of an audited module can change what it computes
or prints. On top of that:
  * each run's stdout is redirected into a fresh file and must hold EXACTLY ONE result line
    (`{"mark": "AXIOM-AUDIT-827", …}`); other lines are shown, never graded;
  * the result must carry the run's NONCE (fresh per generation, after `lake build`), the
    run's root, and EXACTLY the manifest's target module list;
  * every target module must be present in the loaded environment (`missing == []`), at least
    one declaration must be audited, and an empty audit (no runs) FAILS;
  * a run with no output (crash, failed import) FAILS.
Known limit (not this gate's job): the .olean files are trusted as written by `lake build`; the
auditor does not re-typecheck them in the kernel (that is lean4checker's job).

ALLOWLIST (scripts/lean_axiom_allowlist.json): exact, issue-linked exceptions — fully qualified
declaration + the exact extra axiom names + an issue number. A declaration is allowed only if its
non-standard axioms EQUAL the entry's; any other non-standard axiom fails; an entry whose
declaration no longer reports exactly those axioms is STALE and fails, so the entry must be
deleted when its issue lands. No wildcards, prefixes or per-file entries. TRANSITIVE: matching
is by exact declaration name against each declaration's FULL axiom closure, so any declaration
that depends on an excepted one inherits its axiom and fails (it has no entry of its own).
Today there is ONE exception: the documented native_decide theorem of issue #582.

usage: check_lean_axiom_audit.py --manifest DIR/manifest.json [--json OUT] [--allowlist FILE]
       (expects DIR/AxiomAudit_<k>.out, the auditor's stdout for each run, as written by CI)
Exit 0 = pass, 1 = fail.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

MARK = "AXIOM-AUDIT-827"


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


DEFAULT_ALLOWLIST = Path(__file__).resolve().parent / "lean_axiom_allowlist.json"


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
        out = Path(d["output"])
        tag = d["label"]
        if not out.exists():
            errors.append(
                f"[{tag}] no auditor output {out.name} — the run did not happen"
            )
            continue
        results, other = read_output(out)
        if other:
            # The auditor prints nothing but its one JSON line; anything else (e.g. a warning
            # from elaborating LeanAxiomAudit.lean) is shown, never graded.
            print(f"[{tag}] {other} non-result output line(s) ignored")
        if len(results) != 1:
            errors.append(
                f"[{tag}] expected exactly 1 auditor result line, found {len(results)}"
            )
            continue
        r = results[0]
        if r.get("nonce") != d["nonce"]:
            errors.append(
                f"[{tag}] auditor result carries the wrong nonce — not this run's output"
            )
            continue
        if r.get("root") != tag or r.get("targets") != d["modules"]:
            errors.append(
                f"[{tag}] auditor result is for a different scope "
                f"(root={r.get('root')}, {len(r.get('targets') or [])} targets)"
            )
            continue
        missing = r.get("missing")
        decls = r.get("declarations")
        bad_raw = r.get("nonstd")
        if (
            not isinstance(missing, list)
            or not isinstance(decls, int)
            or not isinstance(bad_raw, list)
        ):
            errors.append(f"[{tag}] malformed auditor result")
            continue
        if missing:
            errors.append(
                f"[{tag}] in-scope module(s) absent from the loaded environment: {missing}"
            )
        if decls == 0:
            errors.append(
                f"[{tag}] zero declarations audited — an empty audit is a failure"
            )
        bad_here = []
        for b in bad_raw:
            if not (
                isinstance(b, dict)
                and isinstance(b.get("decl"), str)
                and isinstance(b.get("axioms"), list)
                and b["axioms"]
            ):
                errors.append(f"[{tag}] malformed non-standard entry: {b}")
                continue
            bad_here.append(
                {
                    "decl": b["decl"],
                    "module": str(b.get("module", "")),
                    "axioms": [str(x) for x in b["axioms"]],
                    "root": tag,
                }
            )
        total_decls += decls
        audited_modules.update(d["modules"])
        nonstd.extend(bad_here)
        print(
            f"axiom audit [{tag}]: {len(d['modules']) - len(missing)}/{len(d['modules'])} modules, "
            f"{decls} declarations, {len(bad_here)} non-standard"
        )
    found_ax: dict[str, set[str]] = {}
    for b in nonstd:
        found_ax.setdefault(b["decl"], set()).update(b["axioms"])
    allow = load_allowlist(Path(a.allowlist), errors) if a.allowlist else {}
    uniq: set[tuple[str, str]] = set()
    allowed_hits: list[str] = []
    # TRANSITIVE by construction (Cartan, seq 5688): every declaration's axiom set is its FULL
    # closure, computed by Lean, and the allowlist is matched by EXACT declaration name only.
    # A theorem that USES an excepted declaration inherits that declaration's non-standard
    # axiom in its own closure, has no entry of its own, and therefore FAILS — the exception
    # covers exactly the named declaration, never anything that depends on it.
    # The gate keys on NO specific axiom name (architect, seq 5690: from Lean 4.29 each native
    # computation gets its own named axiom, and 4.35.0 removes `Lean.trustCompiler` /
    # `Lean.ofReduceBool`): RULE 1 is "any axiom outside {propext, Classical.choice,
    # Quot.sound} fails", decided in the Lean driver. `excepted_axioms` below is used ONLY to
    # add an explanatory hint to a dependent's failure message, never to decide pass/fail.
    excepted_axioms = {x for e in allow.values() for x in e["axioms"]}
    for decl, axs in sorted(found_ax.items()):
        mod = next(b["module"] for b in nonstd if b["decl"] == decl)
        entry = allow.get(decl)  # exact name; no prefix / dependency / file matching
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
        elif axs & excepted_axioms:
            why = (
                f" — inherits {sorted(axs & excepted_axioms)} from an allowlisted declaration; "
                f"dependents of an exception are NOT excused (transitive gate)"
            )
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
