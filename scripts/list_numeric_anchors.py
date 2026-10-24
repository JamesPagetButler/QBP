#!/usr/bin/env python3
"""List every numeric CTH anchor and propose its FORCED / SELECTED / UNDECIDED tag (QBP #479).

Read-only over the ledger. This script PROPOSES tags for the steward's review (#479 AC4);
it never writes the ledger (ledger edits are the confined-writer lane, `scripts/cth_ledger_edit.py`).

Inclusion rule (#479 AC1 scope, applied mechanically — Grothendieck completeness)
  An `anchors[]` record is NUMERIC iff at least one top-level field OTHER THAN the
  bookkeeping fields {tier, sorry_count, pa_local, pa_effective} holds a number
  (int/float, never bool), or a non-empty list/dict whose values are all numbers.
  String-typed numbers do not count (the schema types measured/predicted_value as number).

Tag rules (first match wins; every rule cites a record field, never a physics judgement)
  R-FIT   `independent: false` or id prefix `FIT-`           -> SELECTED (record declares the fit)
  R-OVR   id in OVERRIDES (verbatim quote of a record field) -> tag per table (quote is VERIFIED
          against the record at run time; drift = hard error, so the table cannot rot silently)
  R-INST  prediction_chain closure reaches a free-parameter node (an `inputs[]` id, an `INST-`
          anchor, or an R-OVR SELECTED anchor)                -> SELECTED (dof = distinct parameters)
  R-EXT   prediction_chain == [] and provenance_kind in {experiment, theory-external}
                                                             -> FORCED (external datum; no QBP
                                                                degree of freedom is exercised)
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

AC3: every SELECTED row carries the fixed note G2_TRIVIAL_NOTE. Whether the "G₂-trivial" mechanism
is the operative one (orientation choice) or the dof is a fitted input is shown in `free_params`.

Usage
  python3 scripts/list_numeric_anchors.py                 # markdown table + summary
  python3 scripts/list_numeric_anchors.py --format json   # machine-readable rows
  python3 scripts/list_numeric_anchors.py --summary       # counts only
  python3 scripts/list_numeric_anchors.py --ledger PATH   # another ledger file
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(HERE)
DEFAULT_LEDGER = os.path.join(
    REPO_ROOT, "archive", "cth-inventory", "confluent-trust-inventory-v5_3.v0.3.json"
)

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
G2_TRIVIAL_NOTE = "G₂-trivial: zero independent evidential weight."
ORIENTATION_RE = re.compile(r"furey|baez|orientation|fano", re.IGNORECASE)

# Record-cited overrides. Each entry: (tag, field, verbatim quote, free-parameter name or None).
# The quote MUST be a substring of the named field of the live record; `verify_overrides`
# raises otherwise. Adding a row here = citing the record, not deciding physics.
OVERRIDES: Dict[str, Tuple[str, str, str, Optional[str]]] = {
    "OBS-cbt-koide": (
        "SELECTED",
        "description",
        "Post-hoc observation from scanning all 20 quark triplets",
        "quark-triplet choice (scan of 20)",
    ),
    "OBS-alpha-invsqrt3": (
        "SELECTED",
        "notes",
        "Scanned multiple algebraic ratios; 1/√3 was closest",
        "algebraic-ratio choice (closest of scanned)",
    ),
    "OBS-cmb-314": (
        "SELECTED",
        "description",
        "No other parameter-free algebraic quantity from the crystallisation geometry is closer",
        "algebraic-ratio choice (closest of candidates)",
    ),
    "PRED-lambda-as-cross-term": (
        "SELECTED",
        "notes",
        "The transition redshift z_t = 0.7 is an INPUT (calibrated to the observed "
        "deceleration-acceleration transition), not a prediction",
        "z_t = 0.7 (calibrated input)",
    ),
    "PRED-a0-saturating-matter-era": (
        "SELECTED",
        "description",
        "Empirical fit to BTFR data",
        "F_max (BTFR best-fit)",
    ),
    "PRED-a0-saturation-factor-fano": (
        "SELECTED",
        "description",
        "The empirical best-fit a₀(z) saturation factor matches dim(Im 𝕆) = 7",
        "F_max (BTFR best-fit)",
    ),
    "PRED-inv-alpha-GUT-16pi": (
        "SELECTED",
        "description",
        "The closest algebraic expression is 16π = 50.27 (2.9% off)",
        "algebraic-expression choice (closest of candidates)",
    ),
    "PROOF-stelle-no-linear": (
        "FORCED",
        "measured_source",
        "Stelle 1977, 1978 (analytic proof)",
        None,
    ),
    "PROOF-beta-function-3-times-7": (
        "FORCED",
        "notes",
        "IDENTIFICATION not prediction — this is a known QCD result",
        None,
    ),
}


# ── numeric detection ────────────────────────────────────────────────────────


def is_numeric_value(value: Any) -> bool:
    """A number (not bool), or a non-empty list/dict whose leaves are all numbers."""
    if isinstance(value, bool):
        return False
    if isinstance(value, (int, float)):
        return True
    if isinstance(value, list):
        return bool(value) and all(is_numeric_value(v) for v in value)
    if isinstance(value, dict):
        return bool(value) and all(is_numeric_value(v) for v in value.values())
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


def free_parameter_nodes(ledger: Dict[str, Any]) -> Dict[str, str]:
    """id -> parameter name for every node that introduces a free parameter."""
    nodes: Dict[str, str] = {}
    for inp in ledger.get("inputs", []):
        nodes[inp["id"]] = inp["id"]
    for a in ledger.get("anchors", []):
        if a["id"].startswith("INST-"):
            nodes[a["id"]] = a["id"]
    for aid, (tag, _field, _quote, param) in OVERRIDES.items():
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
    for aid, (tag, field, quote, _param) in OVERRIDES.items():
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


def classify(anchor: Dict[str, Any], ledger: Dict[str, Any]) -> Dict[str, Any]:
    """Propose a tag for one numeric anchor. Pure function of (anchor, ledger, OVERRIDES)."""
    by_id = {a["id"]: a for a in ledger.get("anchors", [])}
    free_nodes = free_parameter_nodes(ledger)
    aid = anchor["id"]
    chain = list(anchor.get("prediction_chain", []))
    closure = chain_closure(by_id, aid)
    direct = sorted(c for c in chain if c in free_nodes)
    inherited = sorted(c for c in closure if c in free_nodes and c not in direct)
    params = sorted({free_nodes[c] for c in direct + inherited})
    pk = anchor.get("provenance_kind")
    nf = numeric_fields(anchor)
    has_pred = any(f in nf for f in PREDICTED_SIDE_FIELDS)
    ver = anchor.get("verification") or {}
    text = " ".join(str(anchor.get(k) or "") for k in ("name", "description", "notes"))

    tag: str
    rule: str
    reason: str
    if anchor.get("independent") is False or aid.startswith("FIT-"):
        tag, rule = "SELECTED", "R-FIT"
        which = (
            "`independent: false`"
            if anchor.get("independent") is False
            else "`FIT-` prefix"
        )
        reason = f"record declares the fit ({which})"
    elif aid in OVERRIDES:
        tag, field, quote, param = OVERRIDES[aid]
        rule = "R-OVR"
        reason = f"record `{field}`: “{quote}”"
        if param:
            params = sorted(set(params) | {param})
    elif direct or inherited:
        tag, rule = "SELECTED", "R-INST"
        via = []
        if direct:
            via.append("direct: " + ", ".join(direct))
        if inherited:
            via.append("inherited via chain: " + ", ".join(inherited))
        reason = "`prediction_chain` reaches a free parameter (" + "; ".join(via) + ")"
    elif not chain and pk in ("experiment", "theory-external"):
        tag, rule = "FORCED", "R-EXT"
        reason = (
            f"`prediction_chain: []`, `provenance_kind: {pk}` — external datum, "
            "no QBP degree of freedom exercised in this record"
        )
    elif "measured_value" in nf and not has_pred:
        tag, rule = "FORCED", "R-MEAS"
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
        tag, rule = "UNDECIDED", "R-THM"
        reason = (
            f"`lean_theorem: {anchor['lean_theorem']}` (sorry 0, verified) forces the "
            "algebraic identity; whether its physical identification was derived or chosen "
            "is not on record — ruling: derived ⇒ FORCED, chosen among candidates ⇒ SELECTED"
        )
    else:
        tag, rule = "UNDECIDED", "default"
        reason = (
            f"`provenance_kind: {pk}`; no free parameter in `prediction_chain`, no kernel "
            "theorem for the number — ruling: Lean derivation from the chain ⇒ FORCED, "
            "a named selection step ⇒ SELECTED"
        )

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
        "reason": reason,
        "free_params": params,
        "dof": len(params),
        "orientation_keyword": bool(ORIENTATION_RE.search(text)),
        "ac3_note": G2_TRIVIAL_NOTE if tag == "SELECTED" else None,
    }
    return row


def classify_all(ledger: Dict[str, Any]) -> List[Dict[str, Any]]:
    """Classify every numeric anchor; raise if any override quote has drifted."""
    errors, _missing = verify_overrides(ledger)
    if errors:
        raise ValueError("OVERRIDES drifted from the ledger:\n  " + "\n  ".join(errors))
    return [classify(a, ledger) for a in list_numeric_anchors(ledger)]


def summarize(rows: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    counts = {t: sum(1 for r in rows if r["tag"] == t) for t in TAGS}
    by_rule: Dict[str, int] = {}
    for r in rows:
        by_rule[r["rule"]] = by_rule.get(r["rule"], 0) + 1
    params: Dict[str, List[str]] = {}
    for r in rows:
        if r["tag"] == "SELECTED":
            for p in r["free_params"]:
                params.setdefault(p, []).append(r["id"])
    return {
        "numeric_anchors": len(rows),
        "tags": counts,
        "rules": dict(sorted(by_rule.items())),
        "free_choice_count": counts["SELECTED"],
        "distinct_free_parameters": {k: sorted(v) for k, v in sorted(params.items())},
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
        "kind / status | Tag | Rule | Free params (dof) | Orient. kw | Reason |"
    )
    out.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for i, r in enumerate(rows, 1):
        nums = "; ".join(f"{k}={_fmt_num(v)}" for k, v in r["numeric_fields"].items())
        fp = (
            (", ".join(r["free_params"]) + f" ({r['dof']})")
            if r["free_params"]
            else "— (0)"
        )
        reason = r["reason"] + (f" {r['ac3_note']}" if r["ac3_note"] else "")
        out.append(
            f"| {i} | `{r['id']}` | {_esc(nums)} | {_esc(r['unit'] or '—')} | "
            f"{_esc(r['external_reference'] or '— (none on record)')} | "
            f"{_esc(r['provenance_kind'])} / {_esc(r['status'])} | **{r['tag']}** | "
            f"{r['rule']} | {_esc(fp)} | {'Y' if r['orientation_keyword'] else 'N'} | "
            f"{_esc(reason)} |"
        )
    return "\n".join(out)


def render_summary(summary: Dict[str, Any]) -> str:
    lines = [
        f"numeric anchors: {summary['numeric_anchors']}",
        "tags: " + ", ".join(f"{t} {summary['tags'][t]}" for t in TAGS),
        "rules: " + ", ".join(f"{k} {v}" for k, v in summary["rules"].items()),
        f"free-choice count (SELECTED tags): {summary['free_choice_count']}",
        f"distinct free parameters: {len(summary['distinct_free_parameters'])}",
    ]
    for p, ids in summary["distinct_free_parameters"].items():
        lines.append(f"  - {p}: {len(ids)} anchor(s) — {', '.join(ids)}")
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
    ap.add_argument("--format", choices=("md", "json"), default="md")
    ap.add_argument("--summary", action="store_true", help="print counts only")
    args = ap.parse_args(list(argv) if argv is not None else None)

    ledger = load_ledger(args.ledger)
    try:
        rows = classify_all(ledger)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    _errs, missing = verify_overrides(ledger)
    for aid in missing:
        print(
            f"WARNING: override anchor {aid} not in this ledger's anchors[]",
            file=sys.stderr,
        )
    summary = summarize(rows)
    if args.summary:
        print(render_summary(summary))
    elif args.format == "json":
        print(
            json.dumps({"summary": summary, "rows": rows}, indent=1, ensure_ascii=False)
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
