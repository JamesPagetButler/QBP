#!/usr/bin/env python3
"""Root GATE + chain-to-root audit for the CTH ledger — issue #654 D1/D2.

The beekeeper's standard (2026-09-11): "We work from axioms, the fewer the better,
preferably zero — anchoring all of QBP to experimentally proven facts. We only change
an axiom because we have proven that it must." This script mechanises it as a GATE,
not a ratchet (PATTERN-02, docs/process_violation_log.md): absolute, whole-population,
no count, no baseline file. The only escape is an ITEMISED, issue-linked, SHRINK-ONLY
register (docs/cth/root-audit-register.json, modelled on proof-anchor-remediation.json):
adding an entry is a visible, reviewed commit with a tracking issue, never a CI-driven
baseline raise; a listed entry that is later fixed but not removed HARD-FAILS. Register
GROWTH is a REVIEW gate (a same-commit entry passes the machine) — the machine enforces
shrink-only staleness, resolution and issue-linking; the human reviewer owns growth.

D1 — ROOT GATE. Every root (a record in the root lists `meta_axiom`, `meta_principles`,
`axioms`, `interpretations`, whose id starts with AXIOM-, POST-, META- or INTERP-) must
sort into exactly one Conversation-MO bucket, from the ledger alone:

  bucket 1  PROVED   `forced_by` names a PROOF-* anchor that resolves in-ledger with
                     proof_state verified.
  bucket 2  FORCED   `forced_by` names a MEAS-* anchor that resolves in-ledger with status
                     coherent/converged (an untested, marginal, contested or dead anchor
                     forces nothing), or
                     `decision_state: ruled` with a `ruling` that cites a
                     JamesPagetButler/* GitHub issue/PR URL (the beekeeper's own-hand
                     line — a scope/process ruling, never a physical truth). This
                     check is STRUCTURAL (a cite is present); whether the cited ruling
                     actually forces THIS root is the Red Team confirmer's semantic
                     half (#654 D4) — the URL check is not the whole guard.
  bucket 3  OPEN     `kill_condition` is a NON-EMPTY ARRAY of non-placeholder entries — one
                     Impasse Record per open question on the root (array-only canonical,
                     confluent-trust #102) — AND `decision_state: open` (or `status: open`).
                     An open root is an Impasse Record, not a request.
  bucket 4  RETIRED  lives in `retired_axioms` / `retired_principles` — reported only.

A root sorting into NO bucket is UNSORTED → HARD FAIL unless listed in the register's
`open_roots`. A root-prefixed id living in ANY other id-bearing list (`anchors`,
`derived_principles`, `chains`, `inputs`, …) is a smuggled
root → HARD FAIL unless registered — a structural rule, no hand-maintained exception
list (a legacy `META-*-field` documentation anchor is renamed out of the prefix space,
tracked by its register entry, never carved out).

D2 — CHAIN-TO-ROOT. Chains are followed transitively: a DERIV-* principle via
`derived_from`, an anchor via `prediction_chain`. A path TERMINATES at a root id, a
PROOF-*/MEAS-* anchor, or an anchor with `provenance: "E"` (an experimental fact — the
beekeeper's zero-axiom target) — PROVIDED its status is not killed/incoherent/refuted/
falsified. A dead anchor grounds nothing AND ends the path: the walker never recurses
through it, so a chain whose only ground is a dead anchor is DANGLING. A seen-set on the current path catches cycles (A→B→A
fails, never loops).
  * RESOLUTION is gated for EVERY chain: an id that is not in the ledger HARD-FAILS
    unless the missing id is listed in the register's `chain_debt`.
  * TERMINATION is gated for `derived_principles`, DERIV-* / PRED-* anchors, and any anchor
    whose declared `provenance_kind` is derivation or internal-compute:
    an empty or dangling chain HARD-FAILS unless the chain's owner is listed in
    `chain_debt`.
  * Other anchor kinds (INSIGHT, REF, DEFN, FLAG, …) with non-terminating chains are
    REPORTED (enumerated, counted by kind), not gated — because those kinds carry NO
    DERIVATION OBLIGATION in the ledger (they are inputs, records or observations, not
    derived claims), NEVER because they are many. The moment a kind is report-only to
    tolerate its debt, that is PATTERN-02. A terminal owner (PROOF/MEAS/experimental)
    is self-grounding: its own chain is checked for resolution only.
Ledger-only: reads the JSON, never proofs/**, never cross-repo — the intra-QBP C3
discipline (a)+(b), none of clause (c). Complementary to check_anchor_manifest.py
(theorem witnesses exist in source), not overlapping.

Exit 0 = every root sorted or registered, every gated chain resolves and terminates or
is registered, no stale register entry. Exit 1 otherwise. `--report-md PATH` writes the
honest root list, every chain problem and the warnings (the D6 retro report).
"""

import argparse
import json
import re
import sys
from collections import Counter, OrderedDict

DEFAULT_LEDGER = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DEFAULT_REGISTER = "docs/cth/root-audit-register.json"

ROOT_PREFIXES = ("AXIOM-", "POST-", "META-", "INTERP-")
TERMINAL_ANCHOR_PREFIXES = ("PROOF-", "MEAS-")
GATED_CHAIN_PREFIXES = ("DERIV-", "PRED-")
GATED_PROVENANCE_KINDS = (
    "derivation",
    "internal-compute",
)  # ledger-declared derived claims
DEAD_STATUSES = (
    "killed",
    "incoherent",
    "refuted",
    "falsified",
)  # dead: grounds/forces nothing; ends a path
FORCING_STATUSES = (
    "coherent",
    "converged",
)  # a MEAS-* forcing must be measured and hold; PROOF-* verified
# array<string> era (cth-implementor, live-test 1325; qbp-implementor 1330): a kill entry must be
# real prose, not empty/stub. This is the HEURISTIC half of §10 precision — "does each open
# question name a precise missing piece". The STRUCTURAL half (each entry must also name a
# resolving discharge) lands with array<object> at the confluent-trust #102 delta; until then a
# text heuristic is the honest bound. The >= 8 floor is a crude stub-guard, not a quality check.
_KILL_PLACEHOLDER = re.compile(
    r"^(todo|tbd|tba|fixme|xxx+|placeholder|none|n/?a|\?+|-+|\.+)(\b|$)", re.I
)  # matches a stub token at the START of an entry — so "TODO: write later" is a stub too
ROOT_LISTS = ("meta_axiom", "meta_principles", "axioms", "interpretations")
RETIRED_LISTS = ("retired_axioms", "retired_principles")
GITHUB_CITE = re.compile(
    r"https://github\.com/JamesPagetButler/[^\s)/]+/(issues|pull)/\d+"
)

BUCKET = {
    1: "bucket-1 PROVED",
    2: "bucket-2 FORCED",
    3: "bucket-3 OPEN",
    4: "bucket-4 RETIRED",
}


def _as_list(v):
    if v is None:
        return []
    return v if isinstance(v, list) else [v]


def is_root_id(rid):
    return isinstance(rid, str) and rid.startswith(ROOT_PREFIXES)


def collect(ledger):
    """Whole-population collection. Returns roots, retired, principles, anchors,
    population problems (hard) and warnings (reported)."""
    roots, problems, warnings = OrderedDict(), [], []
    for key in ROOT_LISTS:
        for rec in _as_list(ledger.get(key)):
            rid = rec.get("id")
            if not is_root_id(rid):
                problems.append(f"ROOT POPULATION {key}[{rid}]: id has no root prefix")
                continue
            if rid in roots:
                problems.append(f"ROOT POPULATION {key}[{rid}]: duplicate root id")
            roots[rid] = (key, rec)
    retired = OrderedDict()
    for key in RETIRED_LISTS:
        for rec in _as_list(ledger.get(key)):
            retired[rec.get("id")] = (key, rec)
    principles = OrderedDict((p["id"], p) for p in ledger.get("derived_principles", []))
    anchors = OrderedDict((a["id"], a) for a in ledger.get("anchors", []))
    # Smuggled roots: a root-prefixed id in ANY id-bearing top-level list that is not a
    # root list (anchors, derived_principles, chains, inputs, …) — structural, no carve-out.
    # Smuggled roots: a root-prefixed id-bearing record ANYWHERE outside the root lists —
    # top-level lists and nested containers alike (walked recursively). Structural, no carve-out.
    smuggled = OrderedDict()

    def walk(node, where):
        if isinstance(node, dict):
            if is_root_id(node.get("id")):
                # walk() is only ever entered from a non-root list or from INSIDE a root
                # record, so any root-prefixed id seen here is smuggled
                smuggled.setdefault(node["id"], (where, node))
            for k, v in node.items():
                if isinstance(v, (dict, list)):
                    walk(v, f"{where}.{k}" if where else k)
        elif isinstance(node, list):
            for i, v in enumerate(node):
                walk(v, f"{where}[{i}]")

    for key, val in ledger.items():
        if key in ROOT_LISTS or key in RETIRED_LISTS:
            # the top-level records ARE roots; anything root-prefixed nested INSIDE one of them
            # is smuggled (Gemini round 2 on PR #658)
            for rec in _as_list(val):
                if isinstance(rec, dict):
                    for k, v in rec.items():
                        if isinstance(v, (dict, list)):
                            walk(v, f"{key}[{rec.get('id')}].{k}")
            continue
        walk(val, key)
    return roots, retired, principles, anchors, problems, warnings, smuggled


def _non_placeholder(e):
    if not isinstance(e, str):
        return False  # array-only<string>: objects/nulls are not a kill yet
    t = e.strip()
    return len(t) >= 8 and not _KILL_PLACEHOLDER.search(t)


def kill_present(kc):
    """cth-implementor's D3 invariant: an open root carries a NON-EMPTY ARRAY of kill entries,
    one per open question, EVERY entry non-placeholder. A bare string is not the canonical
    shape (array-only, confluent-trust #102) and does not count."""
    return isinstance(kc, list) and len(kc) > 0 and all(_non_placeholder(e) for e in kc)


def sort_root(rec, anchors):
    """Return (bucket_number or None, reason)."""
    forced = [x for x in _as_list(rec.get("forced_by")) if isinstance(x, str)]
    missing = [x for x in forced if x not in anchors]
    if missing:
        return None, f"forced_by names ids that do not resolve in-ledger: {missing}"
    dead = [x for x in forced if anchors[x].get("status") in DEAD_STATUSES]
    if dead:
        return None, (
            f"forced_by names dead anchors (status killed/incoherent/refuted) — a dead anchor "
            f"forces nothing: {dead}"
        )
    weak = [
        x
        for x in forced
        if (x.startswith("PROOF-") and anchors[x].get("proof_state") != "verified")
        or (x.startswith("MEAS-") and anchors[x].get("status") not in FORCING_STATUSES)
    ]
    if weak:
        return None, (
            f"forced_by names anchors that cannot force — an unverified PROOF-* or a MEAS-* "
            f"whose status is not coherent/converged (untested, marginal, contested…): {weak}"
        )
    if any(x.startswith("PROOF-") for x in forced):
        return 1, "forced_by verified PROOF-* resolves"
    if any(x.startswith("MEAS-") for x in forced):
        return 2, "forced_by coherent/converged MEAS-* resolves"
    if forced:
        return None, f"forced_by names non-PROOF/MEAS ids (not a forcing): {forced}"
    ds = rec.get("decision_state")
    if ds == "settled":
        ruling = rec.get("ruling")
        if isinstance(ruling, str) and GITHUB_CITE.search(ruling):
            return (
                2,
                "decision_state ruled with a GitHub-cited ruling (structural check only)",
            )
        return None, (
            "decision_state ruled but `ruling` is not a string citing a JamesPagetButler/* "
            "GitHub issue/PR URL"
        )
    has_kill = kill_present(rec.get("kill_condition"))
    is_open = ds == "open" or rec.get("status") == "open"
    if has_kill and is_open:
        return 3, "kill_condition present and open"
    if has_kill:
        return (
            None,
            "kill_condition present but neither decision_state nor status is open",
        )
    if is_open:
        return None, (
            "open but kill_condition is missing, not a non-empty array, or has a placeholder/"
            "stub entry (an open root without a real falsifier)"
        )
    return None, "no forcing (forced_by), no ruling cite, no kill_condition"


def load_register(path):
    """Returns (open_roots by id, chain_debt by id, problems)."""
    try:
        with open(path, encoding="utf-8") as f:
            reg = json.load(f)
    except FileNotFoundError:
        return {}, {}, []
    problems = []
    out = []
    for section in ("open_roots", "chain_debt"):
        byid = {}
        for e in reg.get(section, []):
            if not (e.get("id") and e.get("issue")):
                problems.append(f"REGISTER {section} entry without id+issue: {e}")
                continue
            if e["id"] in byid:
                problems.append(f"REGISTER {section}: duplicate entry {e['id']}")
            byid[e["id"]] = e
        out.append(byid)
    return out[0], out[1], problems


def is_terminal(node, roots, anchors):
    if node in roots:
        return True
    a = anchors.get(node)
    if a is None:
        return False
    if a.get("status") in DEAD_STATUSES:
        return False  # a killed / incoherent / refuted anchor grounds nothing
    return node.startswith(TERMINAL_ANCHOR_PREFIXES) or a.get("provenance") == "E"


def walk_chain(owner, start_ids, roots, principles, anchors):
    """DFS from the owner's chain. Returns (unresolved_ids, dangling_paths, cycles)."""
    unresolved, dangling, cycles = [], [], []

    def visit(node, path):
        if node in path:
            cycles.append(" -> ".join(path[path.index(node) :] + [node]))
            return
        if is_terminal(node, roots, anchors):
            return
        if node in principles:
            nxt = _as_list(principles[node].get("derived_from"))
            if not nxt:
                dangling.append(" -> ".join(path + [node]) + " (empty derived_from)")
            for n in nxt:
                visit(n, path + [node])
            return
        if node in anchors:
            if anchors[node].get("status") in DEAD_STATUSES:
                # a dead anchor is the END of a path, never a node to recurse through: the
                # chain must ground elsewhere (PR #658 round-2 NF-1)
                dangling.append(
                    " -> ".join(path + [node])
                    + f" (dead anchor, status {anchors[node].get('status')}: grounds nothing)"
                )
                return
            nxt = [
                x for x in _as_list(anchors[node].get("prediction_chain")) if x != node
            ]
            if not nxt:
                dangling.append(
                    " -> ".join(path + [node]) + " (empty prediction_chain)"
                )
            for n in nxt:
                visit(n, path + [node])
            return
        unresolved.append((node, " -> ".join(path + [node])))

    starts = [x for x in start_ids if x != owner]
    if not starts and not is_terminal(owner, roots, anchors):
        dangling.append(f"{owner} (empty chain)")
    for s in starts:
        visit(s, [owner])
    return unresolved, dangling, cycles


def audit(ledger, open_roots_reg, chain_debt_reg, register_problems):
    roots, retired, principles, anchors, pop_problems, warnings, smuggled = collect(
        ledger
    )
    failures = list(pop_problems) + list(register_problems)
    for sid, (where, _) in smuggled.items():
        reg = open_roots_reg.get(sid)
        if reg is None:
            failures.append(
                f"SMUGGLED ROOT {sid}: a root-prefixed id living in {where}[] — roots live in "
                f"{ROOT_LISTS} where the root gate sees them; rename it out of the root prefix "
                f"space or move it, and register it meanwhile"
            )
        else:
            warnings.append(
                f"registered smuggled root {sid} in {where}[] (issue {reg.get('issue')})"
            )

    sorted_roots = OrderedDict()
    for rid, (where, rec) in roots.items():
        b, why = sort_root(rec, anchors)
        reg = open_roots_reg.get(rid)
        if b is None and reg is None:
            failures.append(
                f"UNSORTED ROOT {rid} ({where}): {why} — sorts into no bucket (needs "
                f"{BUCKET[1]}/{BUCKET[2]} forcing, or {BUCKET[3]} kill_condition + open) "
                f"and is not in the register's open_roots"
            )
        elif b is not None and reg is not None:
            failures.append(
                f"STALE REGISTER open_roots {rid}: now sorts into {BUCKET[b]} ({why}) — "
                f"remove the entry (shrink-only; issue {reg.get('issue')})"
            )
        sorted_roots[rid] = (where, b, why, reg)
    for rid in open_roots_reg:
        if rid not in roots and rid not in smuggled:
            failures.append(
                f"STALE REGISTER open_roots {rid}: no such root in the ledger — remove it"
            )

    # Chains. Owners: every principle and every non-terminal anchor.
    unresolved_by_id = OrderedDict()  # missing id -> [owners]
    dangling_by_owner = OrderedDict()  # owner -> [paths]
    cycles_by_owner = OrderedDict()

    def gated_owner(o):
        # termination obligation = the ledger says it is a derived claim: by id prefix OR by
        # its declared provenance_kind (never by volume — PATTERN-02)
        if o in anchors and anchors[o].get("status") in DEAD_STATUSES:
            return False  # a killed / incoherent / refuted claim has no live derivation obligation
        return (
            o in principles
            or o.startswith(GATED_CHAIN_PREFIXES)
            or (
                o in anchors
                and anchors[o].get("provenance_kind") in GATED_PROVENANCE_KINDS
            )
        )

    owners = [(pid, _as_list(p.get("derived_from"))) for pid, p in principles.items()]
    owners += [(aid, _as_list(a.get("prediction_chain"))) for aid, a in anchors.items()]
    dead_owners = [
        o
        for o, _ in owners
        if o in anchors and anchors[o].get("status") in DEAD_STATUSES
    ]
    dead_terminators_hit = (
        Counter()
    )  # dead anchor id -> number of live chains that reach it
    for owner, chain in owners:
        if owner in dead_owners:
            continue
        for node in _as_list(chain):
            a = anchors.get(node)
            if a is not None and a.get("status") in DEAD_STATUSES:
                dead_terminators_hit[node] += 1
    for owner, chain in owners:
        unresolved, dangling, cycles = walk_chain(
            owner, chain, roots, principles, anchors
        )
        for mid, path in unresolved:
            unresolved_by_id.setdefault(mid, []).append(path)
        if dangling:
            dangling_by_owner[owner] = dangling
        if cycles:
            cycles_by_owner[owner] = cycles

    used_debt = set()
    for mid, paths in unresolved_by_id.items():
        if mid in chain_debt_reg:
            used_debt.add(mid)
        else:
            failures.append(
                f"CHAIN UNRESOLVED {mid}: cited but not in the ledger — via "
                f"{paths[0]}" + (f" (+{len(paths)-1} more)" if len(paths) > 1 else "")
            )
    for owner, cycs in cycles_by_owner.items():
        for c in cycs:
            failures.append(f"CHAIN CYCLE {owner}: {c}")
    ungated_dangling = Counter()
    for owner, paths in dangling_by_owner.items():
        if gated_owner(owner):
            if owner in chain_debt_reg:
                used_debt.add(owner)
            else:
                failures.append(
                    f"CHAIN DANGLING {owner}: does not terminate in "
                    f"{{root | PROOF | MEAS | provenance E}} — {paths[0]}"
                )
        else:
            ungated_dangling[owner.split("-")[0]] += 1
    for did, e in chain_debt_reg.items():
        if did not in used_debt:
            failures.append(
                f"STALE REGISTER chain_debt {did}: no longer unresolved/dangling — remove the "
                f"entry (shrink-only; issue {e.get('issue')})"
            )

    return {
        "roots": sorted_roots,
        "retired": retired,
        "unresolved": unresolved_by_id,
        "dangling": dangling_by_owner,
        "cycles": cycles_by_owner,
        "ungated_dangling": ungated_dangling,
        "gated_owner": gated_owner,
        "warnings": warnings,
        "dead_owners": dead_owners,
        "dead_terminators_hit": dead_terminators_hit,
        "dead_forcings": [
            f for f in failures if f.startswith("UNSORTED ROOT") and "dead anchors" in f
        ],
        "failures": failures,
        "n_principles": len(principles),
        "n_anchors": len(anchors),
        "n_owners": len(owners),
    }


def write_report(res, path, ledger_path, register_path):
    L = ["# Root audit report (issue #654 D6)", ""]
    L.append(f"Ledger: `{ledger_path}` — register: `{register_path}`")
    L += [
        "",
        "## Scope of the root population",
        "",
        f"Roots are the id-bearing records of the root lists {list(ROOT_LISTS)} (plus any "
        "root-prefixed id found elsewhere, reported as smuggled). A ledger may carry roots the "
        "programme names but has not yet encoded as records — e.g. the #654 D6 expectation of "
        "six roots (AXIOM-1, POST-hosting, the rule, META-2, the crystal definition, the "
        "state-space identification) against the three records below: POST-hosting and META-2 "
        "are not encoded until the #652 encode lands; the rule (#635), the crystal definition and "
        "the state-space identification live inside other records under non-root prefixes and "
        "are outside this gate's reach until encoded as roots. The gate audits what is written, "
        "and says so.",
    ]
    L += ["", "## Roots (whole population of the root lists)", ""]
    L.append("| Root | lives in | bucket | reason | register issue |")
    L.append("|---|---|---|---|---|")
    for rid, (where, b, why, reg) in res["roots"].items():
        bl = BUCKET[b] if b else "UNSORTED"
        L.append(
            f"| {rid} | {where} | {bl} | {why} | {reg.get('issue') if reg else ''} |"
        )
    if res["retired"]:
        L += ["", "## Retired (bucket-4, reported not gated)", ""]
        for rid, (where, rec) in res["retired"].items():
            L.append(f"- {rid} ({where})")
    cnt = Counter(b for (_, b, _, _) in res["roots"].values())
    L += ["", "## Counts", "", "| bucket | roots |", "|---|---|"]
    for b in (1, 2, 3):
        L.append(f"| {BUCKET[b]} | {cnt.get(b, 0)} |")
    L.append(f"| UNSORTED (registered or failing) | {cnt.get(None, 0)} |")
    L.append(f"| {BUCKET[4]} | {len(res['retired'])} |")
    L += [
        "",
        f"## Chains: {res['n_principles']} principles + {res['n_anchors']} anchors; "
        f"{res['n_owners']} chain owners walked",
        "",
        f"### Unresolved ids ({len(res['unresolved'])}) — gated for every owner",
        "",
    ]
    for mid, paths in res["unresolved"].items():
        L.append(f"- `{mid}` cited via: " + "; ".join(paths))
    gated = {o: p for o, p in res["dangling"].items() if res["gated_owner"](o)}
    L += [
        "",
        f"### Dangling gated chains — principles / DERIV-* / PRED-* ({len(gated)})",
        "",
    ]
    for owner, paths in gated.items():
        L.append(f"- `{owner}`: " + "; ".join(paths))
    L += ["", f"### Cycles ({len(res['cycles'])})", ""]
    for owner, cycs in res["cycles"].items():
        L.append(f"- `{owner}`: " + "; ".join(cycs))
    other = {o: p for o, p in res["dangling"].items() if not res["gated_owner"](o)}
    L += [
        "",
        f"### Reported, not gated — other kinds with non-terminating chains ({len(other)})",
        "",
        "| kind | owners |",
        "|---|---|",
    ]
    for k, n in sorted(res["ungated_dangling"].items()):
        L.append(f"| {k} | {n} |")
    L += [""]
    for owner, paths in other.items():
        L.append(f"- `{owner}`: " + "; ".join(paths))
    L += [
        "",
        f"## Dead anchors (status killed / incoherent / refuted) — visibility (qbp-implementor, live-test 1336)",
        "",
        "A dead anchor carries no derivation obligation of its own AND satisfies nobody else's: it is",
        "not a terminator and not a forcing. Marking an anchor dead is a reviewed status change; this",
        "section makes a wave of such changes visible on the report, not only in a diff.",
        "",
        f"- dead owners (ungated for termination): {len(res['dead_owners'])} — "
        + (", ".join(f"`{o}`" for o in res["dead_owners"]) or "none"),
        f"- dead anchors reached directly by live chains (each such chain must ground elsewhere): "
        f"{len(res['dead_terminators_hit'])} — "
        + (
            ", ".join(
                f"`{k}` (×{v})" for k, v in res["dead_terminators_hit"].most_common()
            )
            or "none"
        ),
        f"- roots rejected for a dead `forced_by`: {len(res['dead_forcings'])}",
    ]
    L += ["", f"## Warnings ({len(res['warnings'])})", ""]
    for w in res["warnings"]:
        L.append(f"- {w}")
    verdict = "PASS" if not res["failures"] else f"FAIL ({len(res['failures'])})"
    L += ["", f"## Gate: {verdict}", ""]
    for f in res["failures"]:
        L.append(f"- {f}")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(L) + "\n")


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--ledger", default=DEFAULT_LEDGER)
    ap.add_argument("--register", default=DEFAULT_REGISTER)
    ap.add_argument("--report-md", default=None, help="write the D6 retro report")
    args = ap.parse_args()

    with open(args.ledger, encoding="utf-8") as f:
        ledger = json.load(f)
    open_roots_reg, chain_debt_reg, reg_problems = load_register(args.register)
    res = audit(ledger, open_roots_reg, chain_debt_reg, reg_problems)
    if args.report_md:
        write_report(res, args.report_md, args.ledger, args.register)

    cnt = Counter(b for (_, b, _, _) in res["roots"].values())
    gated = sum(1 for o in res["dangling"] if res["gated_owner"](o))
    print(
        f"roots {len(res['roots'])}: {BUCKET[1]}={cnt.get(1, 0)} {BUCKET[2]}={cnt.get(2, 0)} "
        f"{BUCKET[3]}={cnt.get(3, 0)} unsorted={cnt.get(None, 0)} "
        f"(registered open_roots={len(open_roots_reg)}); retired={len(res['retired'])}; "
        f"chains: unresolved ids={len(res['unresolved'])}, dangling gated={gated}, "
        f"cycles={len(res['cycles'])}, reported-only dangling="
        f"{sum(res['ungated_dangling'].values())} (registered chain_debt={len(chain_debt_reg)}); "
        f"warnings={len(res['warnings'])}"
    )
    if res["failures"]:
        print(f"FAIL ({len(res['failures'])}):")
        for f in res["failures"]:
            print("  " + f)
        return 1
    print(
        "PASS: every root sorted or registered (shrink-only); every gated chain resolves "
        "and terminates in {root | PROOF | MEAS | provenance E} or is registered; no cycles."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
