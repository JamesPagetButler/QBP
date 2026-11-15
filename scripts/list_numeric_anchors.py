#!/usr/bin/env python3
"""List every numeric CTH anchor and propose its FORCED / SELECTED / UNDECIDED tag (QBP #479).

Read-only over the ledger. This script PROPOSES tags for the steward's review (#479 AC4);
it never writes the ledger (ledger edits are the confined-writer lane, `scripts/cth_ledger_edit.py`).

Inclusion rule (#479 AC1 scope, applied mechanically — Grothendieck completeness)
  An `anchors[]` record is NUMERIC iff at least one top-level field OTHER THAN the
  bookkeeping fields {tier, sorry_count, pa_local, pa_effective} holds a number
  (int/float, never bool), or a list/dict with AT LEAST ONE numeric leaf (so a mixed
  `experimental_backing` dict carrying a fit result counts — Red Team G1 on PR #769).
  String-typed numbers do not count (the schema types measured/predicted_value as number).

OWN tag rules (first match wins; every rule reads the record's OWN fields, never a physics judgement,
and never another record — AC4 ruling Q4, PR #769: the stored `alignment.tag` is the record's own basis)
  R-FIT   `independent: false` or id prefix `FIT-`           -> SELECTED (record declares the fit)
  R-OVR   id in OVERRIDES (verbatim quote of a record field) -> tag per table (quote is VERIFIED
          against the record at run time; drift = hard error, so the table cannot rot silently)
  R-FREE  the record's OWN `prediction_chain` directly names a free-parameter node (an
          `inputs[]` id or an `INST-` anchor)                -> SELECTED (the record itself cites
                                                                the fitted input; dof = inputs named)
  R-EXT   prediction_chain == [], provenance_kind in {experiment, theory-external}, and NO
          predicted-side field                               -> FORCED (external datum; no QBP
                                                                number in the record at all).
          A record with a predicted-side number and an empty chain falls through: an empty
          chain is absence of a RECORDED dof, not evidence of none (Red Team S1). Where the
          predicted number is the external theory's own, the record says so and R-OVR cites it.
  R-MEAS  has measured_value and NO predicted-side field     -> FORCED (external measurement only;
                                                                nothing QBP-side to be forced/selected)
  R-THM   provenance_kind == proof, lean_theorem, sorry_count 0, verification.result verified
                                                             -> UNDECIDED (the algebraic identity is
                                                                forced by the theorem; whether the
                                                                physical identification was derived
                                                                or chosen is not on record)
  default                                                    -> UNDECIDED (ruling needed: a Lean
                                                                derivation of the number from the
                                                                chain => FORCED; a named selection
                                                                step => SELECTED)

EFFECTIVE tag (derived, never stored — the ledger's `pa_local` / `pa_effective` split, AC4 Q4)
  alignment_effective = weakest link = MIN over the record's own tag and its `prediction_chain`
  DERIVATION closure, with SELECTED < UNDECIDED < FORCED. Closure nodes contribute:
    a numeric anchor         -> its OWN tag
    an `inputs[]` id / INST- -> SELECTED (a free parameter is a degree of freedom exercised;
                                reached INDIRECTLY — the v0.2 "R-INST inherited" case — it
                                lives here; named directly it is already the own tag, R-FREE)
    a DANGLING id (resolves in NO ledger collection) -> UNDECIDED-until-resolved, id named
    any other resolved node (non-numeric anchor, axiom, derived principle, interpretation ...)
                             -> neutral (carries no alignment; the closure continues through
                                anchors, as `EffectivePA` folds only over graded anchors)
  So any SELECTED ancestor => effectively SELECTED; a FORCED row over an UNDECIDED or dangling
  ancestor => effectively UNDECIDED. Only `prediction_chain` is an edge; relevance / mention
  prose never counts (docs/cth/qbp-local-extensions.md, `pa_effective`).

Every row also carries `basis` — WHAT fixes or frees the number on the record's own fields
(algebra-identity / external-theorem / external-datum / measurement-only / fitted-input /
calibrated-input / candidate-scan / unruled). The issue's FORCED means "uniquely determined by
the algebra"; no row today has basis algebra-* with tag FORCED — the basis column is what makes
that visible (Red Team S4); `basis_kind` is a REQUIRED companion of `tag` in the schema (AC4 Q9).
AC3: every row whose EFFECTIVE tag is SELECTED carries the fixed note G2_TRIVIAL_NOTE (an inherited
fitted input zeroes the row's independent evidential weight just as a direct one does). Whether
the "G₂-trivial" mechanism is the operative one (orientation choice) or the dof is a fitted input
is shown in `free_params` (closure-wide, for the AC2 count) and `free_params_own` (stored side).

Usage
  python3 scripts/list_numeric_anchors.py                 # markdown table + summary
  python3 scripts/list_numeric_anchors.py --format json   # machine-readable rows
  python3 scripts/list_numeric_anchors.py --summary       # counts only (own AND effective)
  python3 scripts/list_numeric_anchors.py --effective     # id | own | effective | set by | dangling
  python3 scripts/list_numeric_anchors.py --dangling      # dangling prediction_chain ids, ledger-wide,
                                                          #   with the numeric-scope reach of each
  python3 scripts/list_numeric_anchors.py --ledger PATH   # another ledger file
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import sys
from collections import Counter, defaultdict
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(HERE)
LEDGER_DIR = os.path.join(REPO_ROOT, "archive", "cth-inventory")
LEDGER_GLOB = "confluent-trust-inventory-*.v0.3.json"


def discover_ledger(ledger_dir: str = LEDGER_DIR) -> str:
    """The live v0.3 ledger: the lexically latest `confluent-trust-inventory-*.v0.3.json`.

    Only the `.v0.3.json` family is the schema-v0.3 ledger (the bare `-v5_3.json` /
    `-v5.13.json` files beside it are legacy raw inventories), so the glob is pinned to
    that suffix rather than to one filename (Gemini SHOULD-FIX on PR #769). Falls back to
    the historical filename if the directory is missing so error messages stay useful.
    """
    hits = sorted(glob.glob(os.path.join(ledger_dir, LEDGER_GLOB)))
    if hits:
        return hits[-1]
    return os.path.join(ledger_dir, "confluent-trust-inventory-v5_3.v0.3.json")


DEFAULT_LEDGER = discover_ledger()

BOOKKEEPING_FIELDS = frozenset({"tier", "sorry_count", "pa_local", "pa_effective"})
PREDICTED_SIDE_FIELDS = (
    "predicted_value",
    "predicted_value_lo",
    "predicted_value_hi",
    "predicted_values",
    "prediction_at_z_14",
    "F_max_value",
)
TAGS = ("FORCED", "SELECTED", "UNDECIDED")
# Weakest-link order for the effective tag: a number is no more FORCED than its
# least-forced derivation ancestor (AC4 Q4).
TAG_RANK = {"SELECTED": 0, "UNDECIDED": 1, "FORCED": 2}
RANK_TAG = {v: k for k, v in TAG_RANK.items()}
G2_TRIVIAL_NOTE = "G₂-trivial: zero independent evidential weight."
ORIENTATION_RE = re.compile(r"furey|baez|orientation|fano", re.IGNORECASE)

# Record-cited overrides. Each entry: (tag, field, verbatim quote, free-parameter name or
# None, basis). The quote MUST be a substring of the named field of the live record;
# `verify_overrides` raises otherwise. Adding a row here = citing the record, not deciding
# physics. Records that DISCLAIM a prediction ("IDENTIFICATION not prediction", "does not
# PREDICT") are deliberately NOT overridden: the identification is the open claim, so they
# stay UNDECIDED uniformly (Red Team S3).
OVERRIDES: Dict[str, Tuple[str, str, str, Optional[str], str]] = {
    "OBS-cbt-koide": (
        "SELECTED",
        "description",
        "Post-hoc observation from scanning all 20 quark triplets",
        "quark-triplet choice (scan of 20)",
        "candidate-scan",
    ),
    "OBS-alpha-invsqrt3": (
        "SELECTED",
        "notes",
        "Scanned multiple algebraic ratios; 1/√3 was closest",
        "algebraic-ratio choice (closest of scanned)",
        "candidate-scan",
    ),
    "OBS-cmb-314": (
        "SELECTED",
        "description",
        "No other parameter-free algebraic quantity from the crystallisation geometry is closer",
        "algebraic-ratio choice (closest of candidates)",
        "candidate-scan",
    ),
    "PRED-lambda-as-cross-term": (
        "SELECTED",
        "notes",
        "The transition redshift z_t = 0.7 is an INPUT (calibrated to the observed "
        "deceleration-acceleration transition), not a prediction",
        "z_t = 0.7 (calibrated input)",
        "calibrated-input",
    ),
    "PRED-a0-saturating-matter-era": (
        "SELECTED",
        "description",
        "Empirical fit to BTFR data",
        "F_max (BTFR best-fit)",
        "fitted-input",
    ),
    "PRED-a0-saturation-factor-fano": (
        "SELECTED",
        "description",
        "The empirical best-fit a₀(z) saturation factor matches dim(Im 𝕆) = 7",
        "F_max (BTFR best-fit)",
        "fitted-input",
    ),
    "PRED-inv-alpha-GUT-16pi": (
        "SELECTED",
        "description",
        "The closest algebraic expression is 16π = 50.27 (2.9% off)",
        "algebraic-expression choice (closest of candidates)",
        "candidate-scan",
    ),
    "PROOF-stelle-no-linear": (
        "FORCED",
        "measured_source",
        "Stelle 1977, 1978 (analytic proof)",
        None,
        "external-theorem",
    ),
    # Empty-chain external records whose predicted-side number is the EXTERNAL theory's own
    # (re-admitted to FORCED after Red Team S1 took them out of R-EXT):
    "REF-efimov-kraemer-2006": (
        "FORCED",
        "notes",
        "The 0.96(3) is the zero-range universal prediction",
        None,
        "external-theorem",
    ),
    "REF-efimov-gross-2009": (
        "FORCED",
        "description",
        "consistent with the zero-range prediction 0.96(3)",
        None,
        "external-theorem",
    ),
    "REF-efimov-pollack-2009": (
        "FORCED",
        "notes",
        "Universal prediction from zero-range three-body theory (Efimov 1970; Braaten & Hammer, "
        "Phys. Rep. 428, 259 (2006))",
        None,
        "external-theorem",
    ),
    "REF-efimov-huang-2014": (
        "FORCED",
        "description",
        "No QBP prediction is recorded here.",
        None,
        "external-theorem",
    ),
    "REF-efimov-ulmanis-2016": (
        "FORCED",
        "description",
        "against the mass-ratio-universal e^{π/s₀} ≈ 4.9 for this system",
        None,
        "external-theorem",
    ),
    "REF-jido-eta-prime-chiral-2012": (
        "FORCED",
        "description",
        "At nuclear saturation density ρ₀, ~30% chiral condensate reduction produces ~100 MeV "
        "η′ mass reduction",
        None,
        "external-theorem",
    ),
    "EXT-omega-dm": (
        "FORCED",
        "notes",
        "It is not derived from QBP axioms — it is imported from ΛCDM",
        None,
        "external-datum",
    ),
}


# ── numeric detection ────────────────────────────────────────────────────────


def is_numeric_value(value: Any) -> bool:
    """A number (not bool), or a list/dict with at least one numeric leaf."""
    if isinstance(value, bool):
        return False
    if isinstance(value, (int, float)):
        return True
    if isinstance(value, list):
        return any(is_numeric_value(v) for v in value)
    if isinstance(value, dict):
        return any(is_numeric_value(v) for v in value.values())
    return False


def numeric_fields(anchor: Dict[str, Any]) -> Dict[str, Any]:
    """The anchor's numeric top-level fields, bookkeeping fields excluded."""
    return {
        k: v
        for k, v in anchor.items()
        if k not in BOOKKEEPING_FIELDS and is_numeric_value(v)
    }


def list_numeric_anchors(ledger: Dict[str, Any]) -> List[Dict[str, Any]]:
    return [a for a in ledger.get("anchors", []) if numeric_fields(a)]


# ── chain closure and free parameters ────────────────────────────────────────


def free_input_nodes(ledger: Dict[str, Any]) -> Dict[str, str]:
    """id -> parameter name for the ledger's free INPUTS: `inputs[]` ids and INST- anchors.

    These are the terminals that make a record's OWN tag SELECTED when its own chain names
    one (R-FREE); an `inputs[]` record's `status: measurable|irreducible` IS the
    free-parameter statement (AC4 Q8), so no `alignment` is needed on the input itself.
    """
    nodes: Dict[str, str] = {}
    for inp in ledger.get("inputs", []):
        nodes[inp["id"]] = inp["id"]
    for a in ledger.get("anchors", []):
        if a["id"].startswith("INST-"):
            nodes[a["id"]] = a["id"]
    return nodes


def free_parameter_nodes(ledger: Dict[str, Any]) -> Dict[str, str]:
    """id -> parameter name for every node that introduces a free parameter (closure side):
    the free inputs plus every R-OVR SELECTED anchor (its quoted parameter)."""
    nodes = free_input_nodes(ledger)
    for aid, (tag, _field, _quote, param, _basis) in OVERRIDES.items():
        if tag == "SELECTED" and param:
            nodes[aid] = param
    return nodes


def chain_closure(anchors_by_id: Dict[str, Dict[str, Any]], anchor_id: str) -> Set[str]:
    """All ids reachable from anchor_id along prediction_chain (cycle-safe, excludes self)."""
    seen: Set[str] = set()
    stack = list(anchors_by_id.get(anchor_id, {}).get("prediction_chain", []))
    while stack:
        cur = stack.pop()
        if cur in seen or cur == anchor_id:
            continue
        seen.add(cur)
        stack.extend(anchors_by_id.get(cur, {}).get("prediction_chain", []))
    return seen


def resolvable_ids(ledger: Dict[str, Any]) -> Dict[str, str]:
    """id -> top-level collection name, for EVERY id-bearing record in the ledger.

    `prediction_chain` entries point at anchors, `inputs[]`, `axioms`, `derived_principles`,
    `interpretations`, ... — an id is DANGLING only if it resolves in none of them. (The v0.2
    doc §7 count of 13 used this test; a count of 27 is what "not in `anchors[]`" gives, the
    extra 14 being resolved non-anchor nodes such as AXIOM-1 and DERIV-crystallisation-asymptotic.)
    """
    out: Dict[str, str] = {}
    for key, val in ledger.items():
        if not isinstance(val, list):
            continue
        for rec in val:
            if isinstance(rec, dict) and isinstance(rec.get("id"), str):
                out.setdefault(rec["id"], key)
    return out


def dangling_report(ledger: Dict[str, Any]) -> Dict[str, Any]:
    """Ledger-wide reconciliation of `prediction_chain` ids that are not anchors.

    Returns {"dangling": [...], "resolved_elsewhere": [...]}, each row
    {id, refs, referrers, collection (None when dangling), numeric_rows, in_numeric_scope}:
    refs/referrers count every anchor whose chain names the id directly; numeric_rows are the
    numeric anchors whose transitive closure reaches it (the #479 scope).
    """
    by_id = {a["id"]: a for a in ledger.get("anchors", [])}
    resolv = resolvable_ids(ledger)
    refs: Counter = Counter()
    referrers: Dict[str, List[str]] = defaultdict(list)
    for a in ledger.get("anchors", []):
        for c in a.get("prediction_chain", []):
            if c not in by_id:
                refs[c] += 1
                referrers[c].append(a["id"])
    reach: Dict[str, List[str]] = defaultdict(list)
    for a in list_numeric_anchors(ledger):
        for c in chain_closure(by_id, a["id"]):
            if c not in by_id:
                reach[c].append(a["id"])
    dangling: List[Dict[str, Any]] = []
    elsewhere: List[Dict[str, Any]] = []
    for cid in sorted(refs, key=lambda k: (-refs[k], k)):
        row = {
            "id": cid,
            "refs": refs[cid],
            "referrers": sorted(referrers[cid]),
            "collection": resolv.get(cid),
            "numeric_rows": sorted(reach.get(cid, [])),
            "in_numeric_scope": bool(reach.get(cid)),
        }
        (elsewhere if cid in resolv else dangling).append(row)
    return {"dangling": dangling, "resolved_elsewhere": elsewhere}


# ── overrides ────────────────────────────────────────────────────────────────


def verify_overrides(ledger: Dict[str, Any]) -> Tuple[List[str], List[str]]:
    """Return (drift_errors, missing_ids).

    drift_errors: an override's anchor exists but the quoted text is no longer in the
    named field (or the tag is not in the enum) — a hard error, the table has rotted.
    missing_ids: override ids absent from this ledger's anchors[] — not an error for a
    synthetic/partial ledger; on the real ledger the test asserts this list is empty.
    """
    by_id = {a["id"]: a for a in ledger.get("anchors", [])}
    errors: List[str] = []
    missing: List[str] = []
    for aid, (tag, field, quote, _param, _basis) in OVERRIDES.items():
        if tag not in TAGS:
            errors.append(f"{aid}: override tag {tag!r} not in {TAGS}")
        rec = by_id.get(aid)
        if rec is None:
            missing.append(aid)
            continue
        text = rec.get(field)
        if not isinstance(text, str) or quote not in text:
            errors.append(f"{aid}: quote not found in field {field!r}: {quote!r}")
    return errors, missing


# ── classification ───────────────────────────────────────────────────────────


def _fmt_num(v: Any) -> str:
    if isinstance(v, dict):
        return "{" + ", ".join(f"{k}: {_fmt_num(x)}" for k, x in v.items()) + "}"
    if isinstance(v, list):
        return "[" + ", ".join(_fmt_num(x) for x in v) + "]"
    return repr(v) if isinstance(v, float) else str(v)


def classify(
    anchor: Dict[str, Any],
    ledger: Dict[str, Any],
    by_id: Optional[Dict[str, Dict[str, Any]]] = None,
    free_nodes: Optional[Dict[str, str]] = None,
) -> Dict[str, Any]:
    """Propose the OWN tag for one numeric anchor. Pure function of (anchor, OVERRIDES, inputs).

    Reads the record's own fields only — never another anchor's (AC4 Q4: the stored
    `alignment.tag` is the record's own basis; inheritance along `prediction_chain` is the
    derived `tag_effective`, added by `annotate_effective`). The one chain read is R-FREE: a
    free input the record's own chain names DIRECTLY is the record citing its own fitted
    input. `free_nodes` (the free inputs) may be precomputed by the caller (Red Team K1);
    `by_id` is accepted for call-site compatibility and unused here.
    """
    if free_nodes is None:
        free_nodes = free_input_nodes(ledger)
    aid = anchor["id"]
    chain = list(anchor.get("prediction_chain", []))
    pk = anchor.get("provenance_kind")
    nf = numeric_fields(anchor)
    has_pred = any(f in nf for f in PREDICTED_SIDE_FIELDS)
    ver = anchor.get("verification") or {}
    text = " ".join(str(anchor.get(k) or "") for k in ("name", "description", "notes"))

    tag: str
    rule: str
    reason: str
    basis: str
    own_params: List[str] = []
    if anchor.get("independent") is False or aid.startswith("FIT-"):
        tag, rule, basis = "SELECTED", "R-FIT", "fitted-input"
        which = (
            "`independent: false`"
            if anchor.get("independent") is False
            else "`FIT-` prefix"
        )
        reason = f"record declares the fit ({which})"
        # the fitted parameter itself is named by the chain (closure side), not invented here
    elif aid in OVERRIDES:
        tag, field, quote, param, basis = OVERRIDES[aid]
        rule = "R-OVR"
        reason = f"record `{field}`: “{quote}”"
        if param:
            own_params = [param]
    elif any(c in free_nodes for c in chain):
        tag, rule, basis = "SELECTED", "R-FREE", "fitted-input"
        own_params = sorted({free_nodes[c] for c in chain if c in free_nodes})
        reason = (
            "record's own `prediction_chain` names a free input ("
            + ", ".join(own_params)
            + ")"
        )
    elif not chain and pk in ("experiment", "theory-external") and not has_pred:
        tag, rule, basis = "FORCED", "R-EXT", "external-datum"
        reason = (
            f"`prediction_chain: []`, `provenance_kind: {pk}`, no predicted-side field — "
            "external datum; no QBP number in the record"
        )
    elif "measured_value" in nf and not has_pred:
        tag, rule, basis = "FORCED", "R-MEAS", "measurement-only"
        reason = (
            "record carries `measured_value` and no predicted-side field — external "
            "measurement only; nothing QBP-side to be forced or selected"
        )
    elif (
        pk == "proof"
        and anchor.get("lean_theorem")
        and anchor.get("sorry_count") == 0
        and ver.get("result") == "verified"
    ):
        tag, rule, basis = "UNDECIDED", "R-THM", "algebra-identity (mapping unruled)"
        reason = (
            f"`lean_theorem: {anchor['lean_theorem']}` (sorry 0, verified) forces the "
            "algebraic identity; whether its physical identification was derived or chosen "
            "is not on record — ruling: derived ⇒ FORCED, chosen among candidates ⇒ SELECTED"
        )
    else:
        tag, rule, basis = "UNDECIDED", "default", "unruled"
        reason = (
            f"`provenance_kind: {pk}`; no fit, scan or calibration on the record's own "
            "fields, no kernel theorem for the number — ruling: Lean derivation from the "
            "chain ⇒ FORCED, a named selection step ⇒ SELECTED"
        )

    if tag == "FORCED":
        own_params = (
            []
        )  # a FORCED number has no free parameter by definition (Red Team K2)

    row = {
        "id": aid,
        "prefix": aid.split("-", 1)[0],
        "numeric_fields": nf,
        "unit": anchor.get("predicted_unit"),
        "external_reference": anchor.get("measured_source"),
        "provenance_kind": pk,
        "status": anchor.get("status"),
        "prediction_chain": chain,
        "lean_theorem": anchor.get("lean_theorem"),
        "tag": tag,
        "rule": rule,
        "basis": basis,
        "reason": reason,
        "free_params_own": own_params,
        # closure-side fields — filled by annotate_effective; defaults = "no chain effect"
        "tag_effective": tag,
        "effective_via": [],
        "dangling": [],
        "free_params": list(own_params),
        "dof": len(own_params),
        "orientation_keyword": bool(ORIENTATION_RE.search(text)),
        "ac3_note": G2_TRIVIAL_NOTE if tag == "SELECTED" else None,
    }
    return row


def annotate_effective(
    rows: Sequence[Dict[str, Any]], ledger: Dict[str, Any]
) -> List[Dict[str, Any]]:
    """Derive `tag_effective` for every row: MIN over own tag + the derivation closure.

    Closure contributions (module docstring, EFFECTIVE tag): numeric anchor -> its own tag;
    free-parameter node (`inputs[]`, INST- anchor) -> SELECTED; dangling id -> UNDECIDED;
    any other resolved node -> neutral. `effective_via` names the ancestors at the minimum
    when the chain lowered the tag; `dangling` names every unresolved id in the closure
    whether or not it moved the tag. `free_params` / `dof` are closure-wide (AC2 count).
    """
    by_id = {a["id"]: a for a in ledger.get("anchors", [])}
    resolv = resolvable_ids(ledger)
    free_nodes = free_parameter_nodes(ledger)
    own = {r["id"]: r for r in rows}
    out: List[Dict[str, Any]] = []
    for r in rows:
        closure = chain_closure(by_id, r["id"])
        contrib: List[Tuple[str, str]] = []
        params: Set[str] = set(r["free_params_own"])
        dangling: List[str] = []
        for c in sorted(closure):
            if c in own:
                contrib.append((own[c]["tag"], c))
                params |= set(own[c]["free_params_own"])
            elif c in free_nodes:
                contrib.append(("SELECTED", c))
                params.add(free_nodes[c])
            elif c not in resolv:
                contrib.append(("UNDECIDED", c))
                dangling.append(c)
            # else: resolved non-numeric node — neutral
        own_rank = TAG_RANK[r["tag"]]
        best = min([own_rank] + [TAG_RANK[t] for t, _ in contrib])
        eff = RANK_TAG[best]
        via = [c for t, c in contrib if TAG_RANK[t] == best] if best < own_rank else []
        if eff == "FORCED":
            params = set()  # K2 at the effective level: FORCED-effective ⇒ dof 0
        new = dict(r)
        new["tag_effective"] = eff
        new["effective_via"] = via
        new["dangling"] = dangling
        new["free_params"] = sorted(params)
        new["dof"] = len(new["free_params"])
        new["ac3_note"] = G2_TRIVIAL_NOTE if eff == "SELECTED" else None
        out.append(new)
    return out


def classify_all(ledger: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Own tag + effective tag for every numeric anchor; raise if any override quote drifted."""
    errors, _missing = verify_overrides(ledger)
    if errors:
        raise ValueError("OVERRIDES drifted from the ledger:\n  " + "\n  ".join(errors))
    by_id = {a["id"]: a for a in ledger.get("anchors", [])}
    free_nodes = free_input_nodes(ledger)
    rows = [
        classify(a, ledger, by_id, free_nodes) for a in list_numeric_anchors(ledger)
    ]
    return annotate_effective(rows, ledger)


def summarize(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    counts = {t: sum(1 for r in rows if r["tag"] == t) for t in TAGS}
    eff_counts = {t: sum(1 for r in rows if r["tag_effective"] == t) for t in TAGS}
    by_rule: Dict[str, int] = {}
    by_basis: Dict[str, int] = {}
    moves: Dict[str, int] = {}
    for r in rows:
        by_rule[r["rule"]] = by_rule.get(r["rule"], 0) + 1
        key = f"{r['tag']}/{r['basis']}"
        by_basis[key] = by_basis.get(key, 0) + 1
        if r["tag"] != r["tag_effective"]:
            mk = f"{r['tag']}→{r['tag_effective']}"
            moves[mk] = moves.get(mk, 0) + 1
    params: Dict[str, List[str]] = {}
    for r in rows:
        if r["tag_effective"] == "SELECTED":
            for p in r["free_params"]:
                params.setdefault(p, []).append(r["id"])
    dangling_rows = [r for r in rows if r["dangling"]]
    dangling_ids: Dict[str, int] = {}
    for r in dangling_rows:
        for d in r["dangling"]:
            dangling_ids[d] = dangling_ids.get(d, 0) + 1
    return {
        "numeric_anchors": len(rows),
        "tags": counts,
        "tags_effective": eff_counts,
        "moves": dict(sorted(moves.items())),
        "rules": dict(sorted(by_rule.items())),
        "tag_basis": dict(sorted(by_basis.items())),
        "free_choice_count": eff_counts["SELECTED"],
        "free_choice_count_own": counts["SELECTED"],
        "distinct_free_parameters": {k: sorted(v) for k, v in sorted(params.items())},
        "rows_with_dangling_ancestor": len(dangling_rows),
        "dangling_ids_in_scope": dict(sorted(dangling_ids.items())),
        "orientation_keyword_rows": sum(1 for r in rows if r["orientation_keyword"]),
    }


# ── rendering ────────────────────────────────────────────────────────────────


def _esc(s: Any) -> str:
    return str(s).replace("|", "\\|").replace("\n", " ")


def render_markdown(rows: Sequence[Dict[str, Any]], ledger: Dict[str, Any]) -> str:
    out: List[str] = []
    out.append(
        f"Ledger `{ledger.get('programme')}` version `{ledger.get('version')}` "
        f"(schema `{ledger.get('schema_version')}`), {len(rows)} numeric anchors."
    )
    out.append("")
    out.append(
        "| # | Anchor | Number(s) | Unit | External reference (`measured_source`) | "
        "kind / status | Own tag | Basis | Rule | Effective tag | Effective via | Dangling | "
        "Free params (dof) | Orient. kw | Reason |"
    )
    out.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for i, r in enumerate(rows, 1):
        nums = "; ".join(f"{k}={_fmt_num(v)}" for k, v in r["numeric_fields"].items())
        fp = (
            (", ".join(r["free_params"]) + f" ({r['dof']})")
            if r["free_params"]
            else "— (0)"
        )
        reason = r["reason"] + (f" {r['ac3_note']}" if r["ac3_note"] else "")
        eff = r["tag_effective"]
        eff_s = f"**{eff}**" if eff != r["tag"] else eff
        via = ", ".join(r["effective_via"]) if r["effective_via"] else "— (own)"
        dang = ", ".join(r["dangling"]) if r["dangling"] else "—"
        out.append(
            f"| {i} | `{r['id']}` | {_esc(nums)} | {_esc(r['unit'] or '—')} | "
            f"{_esc(r['external_reference'] or '— (none on record)')} | "
            f"{_esc(r['provenance_kind'])} / {_esc(r['status'])} | **{r['tag']}** | "
            f"{_esc(r['basis'])} | {r['rule']} | {eff_s} | {_esc(via)} | {_esc(dang)} | "
            f"{_esc(fp)} | {'Y' if r['orientation_keyword'] else 'N'} | {_esc(reason)} |"
        )
    return "\n".join(out)


def render_effective(rows: Sequence[Dict[str, Any]]) -> str:
    """Compact own -> effective view, one line per numeric anchor."""
    out = ["| # | Anchor | Own | Effective | Set by (closure) | Dangling in closure |"]
    out.append("|---|---|---|---|---|---|")
    for i, r in enumerate(rows, 1):
        via = ", ".join(r["effective_via"]) if r["effective_via"] else "— (own)"
        dang = ", ".join(r["dangling"]) if r["dangling"] else "—"
        mark = "**" if r["tag"] != r["tag_effective"] else ""
        out.append(
            f"| {i} | `{r['id']}` | {r['tag']} | {mark}{r['tag_effective']}{mark} | "
            f"{_esc(via)} | {_esc(dang)} |"
        )
    return "\n".join(out)


def render_dangling(report: Dict[str, Any]) -> str:
    dang = report["dangling"]
    elsewhere = report["resolved_elsewhere"]
    n_scope = sum(1 for d in dang if d["in_numeric_scope"])
    out = [
        f"Dangling `prediction_chain` ids (resolve in NO ledger collection): "
        f"{len(dang)} ledger-wide, {n_scope} reachable from the numeric anchors' closures.",
        f"Chain ids outside `anchors[]` that DO resolve elsewhere: {len(elsewhere)} "
        f"(total not-in-anchors = {len(dang) + len(elsewhere)}).",
        "",
        "| Chain id (not an anchor) | Resolves in | Direct refs | Referrers | "
        "Numeric rows whose closure reaches it |",
        "|---|---|---:|---|---|",
    ]
    for d in dang + elsewhere:
        where = f"`{d['collection']}`" if d["collection"] else "**UNDEFINED**"
        nrows = d["numeric_rows"]
        reach = f"{len(nrows)}: " + _esc(", ".join(nrows)) if nrows else "0"
        out.append(
            f"| `{d['id']}` | {where} | {d['refs']} | {_esc(', '.join(d['referrers']))} | "
            f"{reach} |"
        )
    return "\n".join(out)


def render_summary(summary: Dict[str, Any]) -> str:
    lines = [
        f"numeric anchors: {summary['numeric_anchors']}",
        "own tags: " + ", ".join(f"{t} {summary['tags'][t]}" for t in TAGS),
        "effective tags: "
        + ", ".join(f"{t} {summary['tags_effective'][t]}" for t in TAGS),
        "own→effective moves: "
        + (", ".join(f"{k} {v}" for k, v in summary["moves"].items()) or "none"),
        "rules (own): " + ", ".join(f"{k} {v}" for k, v in summary["rules"].items()),
        "own tag/basis: "
        + ", ".join(f"{k} {v}" for k, v in summary["tag_basis"].items()),
        f"free-choice count (SELECTED tags): effective {summary['free_choice_count']}, "
        f"own {summary['free_choice_count_own']}",
        f"distinct free parameters: {len(summary['distinct_free_parameters'])}",
    ]
    for p, ids in summary["distinct_free_parameters"].items():
        lines.append(f"  - {p}: {len(ids)} anchor(s) — {', '.join(ids)}")
    lines.append(
        f"rows with a dangling ancestor: {summary['rows_with_dangling_ancestor']} "
        f"over {len(summary['dangling_ids_in_scope'])} dangling id(s)"
    )
    lines.append(
        f"rows with an orientation keyword: {summary['orientation_keyword_rows']}"
    )
    return "\n".join(lines)


# ── CLI ──────────────────────────────────────────────────────────────────────


def load_ledger(path: str) -> Dict[str, Any]:
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def main(argv: Optional[Iterable[str]] = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ledger", default=DEFAULT_LEDGER, help="ledger JSON (read-only)")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--format", choices=("md", "json"), default="md")
    mode.add_argument("--summary", action="store_true", help="print counts only")
    mode.add_argument(
        "--effective",
        action="store_true",
        help="compact own -> effective tag table (set-by ancestor, dangling ids)",
    )
    mode.add_argument(
        "--dangling",
        action="store_true",
        help="reconcile prediction_chain ids outside anchors[]: dangling vs resolved elsewhere",
    )
    args = ap.parse_args(list(argv) if argv is not None else None)

    try:
        ledger = load_ledger(args.ledger)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"ERROR: cannot read ledger {args.ledger}: {exc}", file=sys.stderr)
        return 2
    if args.dangling:
        print(render_dangling(dangling_report(ledger)))
        return 0
    errors, missing = verify_overrides(ledger)
    if errors:
        print(
            "ERROR: OVERRIDES drifted from the ledger:\n  " + "\n  ".join(errors),
            file=sys.stderr,
        )
        return 1
    rows = classify_all(ledger)
    for aid in missing:
        print(
            f"WARNING: override anchor {aid} not in this ledger's anchors[]",
            file=sys.stderr,
        )
    summary = summarize(rows)
    if args.summary:
        print(render_summary(summary))
    elif args.effective:
        print(render_effective(rows))
    elif args.format == "json":
        print(
            json.dumps(
                {
                    "summary": summary,
                    "dangling": dangling_report(ledger),
                    "rows": rows,
                },
                indent=1,
                ensure_ascii=False,
            )
        )
    else:
        print(render_markdown(rows, ledger))
        print()
        print("```")
        print(render_summary(summary))
        print("```")
    return 0


if __name__ == "__main__":
    sys.exit(main())
