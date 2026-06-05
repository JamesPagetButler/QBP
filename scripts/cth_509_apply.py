#!/usr/bin/env python3
"""
QBP #509 apply — unified vNext on the canonical CTH ledger.

Deterministic applier. Inputs are the adjudication record only:
  - analysis/509-apply-rulings.json       (structured encoding of all rulings)
  - analysis/batch-B-decisions-draft.json (74 provenance_kind decisions, Convention D)
  - archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json     (canonical, 150)
  - archive/cth-inventory/confluent-trust-inventory-v5.13.json         (Batch-A stream)
  - archive/cth-inventory/baselines/confluent-trust-inventory-v5_24.json (Batch-C stream)
  - archive/cth-inventory/confluent-trust-inventory-v5_3.json          (three-way base)

Output:
  - canonical file updated IN PLACE (the one-live-file rule; vNext is a state)
  - analysis/509-apply-provenance-trail.md  (full per-anchor trail, adjudicator-attributed)

Validation: every anchor (old + new) against docs/cth/inventory.schema.current.json,
plus the tier-domain gate [1,3] and the stale-pointer resolution rule.

Authors: qbp-implementor (Integration role), 2026-06-04
"""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
RULINGS = REPO / "analysis/509-apply-rulings.json"
BATCH_B = REPO / "analysis/batch-B-decisions-draft.json"
CANON = REPO / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
V513 = REPO / "archive/cth-inventory/confluent-trust-inventory-v5.13.json"
V524 = REPO / "archive/cth-inventory/baselines/confluent-trust-inventory-v5_24.json"
BASE = REPO / "archive/cth-inventory/confluent-trust-inventory-v5_3.json"
SCHEMA = REPO / "docs/cth/inventory.schema.current.json"
TRAIL = REPO / "analysis/509-apply-provenance-trail.md"

MIGRATION_FIELDS = {
    "provenance_kind",
    "independent",
    "proof_language",
    "proof_state",
    "theory_citation",
    "schema_version",
}

trail: list[str] = []


def log(anchor: str, action: str, who: str, detail: str = "") -> None:
    trail.append(f"| `{anchor}` | {action} | {who} | {detail} |")


def load(p: Path) -> dict:
    return json.loads(p.read_text())


def index(inv: dict) -> dict[str, dict]:
    return {a["id"]: a for a in inv["anchors"]}


def find_lean_theorem(name: str, lean_index: dict[str, str]) -> str | None:
    """Resolve a theorem name to its live file path."""
    return lean_index.get(name)


def build_lean_index() -> dict[str, str]:
    """theorem/lemma/def name -> repo-relative path, from the live proofs tree."""
    out: dict[str, str] = {}
    pat = re.compile(r"^\s*(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_'.]+)", re.M)
    for f in sorted((REPO / "proofs").rglob("*.lean")):
        try:
            for m in pat.finditer(f.read_text()):
                out.setdefault(m.group(1).split(".")[-1], str(f.relative_to(REPO)))
        except OSError:
            continue
    return out


def mechanical_provenance_kind(a: dict, rules: dict) -> str:
    psys = str(a.get("proof_system", ""))
    for ov in rules["overrides"]:
        if psys in ov["if_proof_system_in"]:
            return ov["then"]
    return rules["by_provenance"].get(str(a.get("provenance", "T")), "theory")


def translate_v02_to_v03(a: dict, pk_rules: dict) -> dict:
    """Shape an incoming v0.2-lineage anchor for the v0.3 canonical file."""
    out = dict(a)
    out.setdefault("provenance_kind", mechanical_provenance_kind(a, pk_rules))
    # v0.3 required fields — fill conservative defaults where the stream omitted them
    out.setdefault("description", out.get("notes", out.get("name", "")))
    out.setdefault("prediction_chain", out.get("chain_id", "unchained"))
    # Strip ALL null-valued fields: schema types reject null; a stream null means
    # "explicitly unknown", which v0.3 represents by omission.
    for f in [k for k, v in out.items() if v is None]:
        del out[f]
    # Web-stream provenance inventions (e.g. 'PWL') are not in the canonical enum.
    # Map to 'T' (theoretical) and preserve the original for the trail.
    if out.get("provenance") not in {"T", "E", "H", "D", "I", "P"}:
        out["provenance_original"] = out.get("provenance")
        out["provenance"] = "T"
        log(
            out["id"],
            f"provenance normalised `{out['provenance_original']}`→`T`",
            "apply-lane translation (mechanical)",
            "web-stream value outside canonical enum; original preserved",
        )
    return out


def stale_pointer_pass(a: dict, lean_index: dict[str, str]) -> None:
    """cth seq=95 R2/R3: verify proof_file by lean_theorem name or flag."""
    thm = a.get("lean_theorem")
    if not thm and not a.get("proof_file"):
        return
    if thm:
        live = find_lean_theorem(thm, lean_index)
        if live:
            if a.get("proof_file") != live:
                old = a.get("proof_file", "(absent)")
                a["proof_file"] = live
                log(
                    a["id"],
                    "proof_file repointed",
                    "cth R2 (mechanical)",
                    f"`{old}` → `{live}` via theorem-name `{thm}`",
                )
            return
    # No theorem name resolved — stale
    a["lean_migration_status"] = "stale-pointer"
    a["review_flag"] = True
    log(
        a["id"],
        "stale-pointer flagged",
        "cth R2/R3 (mechanical)",
        f"theorem `{thm or '(none)'}` / file `{a.get('proof_file', '(absent)')}` not in live tree",
    )


def main() -> None:
    rulings = load(RULINGS)
    canon = load(CANON)
    idx = index(canon)
    v513 = index(load(V513))
    v524 = index(load(V524))
    base = index(load(BASE))
    pk_rules = rulings["provenance_kind_mechanical_map"]
    lean_index = build_lean_index()
    rider = rulings["_meta"]["empty_substrate_rider"]
    lo, hi = rulings["_meta"]["tier_domain"]

    trail.append("| Anchor | Action | Authority | Detail |")
    trail.append("|---|---|---|---|")

    # ---- Batch B: provenance backfill on canonical anchors --------------------
    bdec = load(BATCH_B)
    b_entries = bdec.get("anchors", bdec if isinstance(bdec, list) else [])
    for d in b_entries:
        aid = d["id"]
        a = idx.get(aid)
        if a is None:
            log(aid, "SKIPPED (not in canonical)", "Batch B", "")
            continue
        a["provenance_kind"] = d["provenance_kind"]
        if d.get("theory_citation"):
            a["theory_citation"] = d["theory_citation"]
        log(
            aid,
            f"provenance_kind = {d['provenance_kind']}",
            "Oppenheimer Batch B (Convention D)",
            d.get("theory_citation", ""),
        )

    # ---- Batch A: v5.13 fold-in ----------------------------------------------
    for aid, r in rulings["batch_A"]["anchors"].items():
        src = v513.get(aid)
        if src is None:
            raise SystemExit(f"Batch A anchor missing from v5.13 stream: {aid}")
        if aid in idx:
            raise SystemExit(f"Batch A collision with canonical (unexpected): {aid}")
        a = translate_v02_to_v03(src, pk_rules)
        for k, v in r.get("set", {}).items():
            a[k] = v
        if r.get("ruling_note"):
            a["intake_note"] = r["ruling_note"]
        a["intake_batch"] = "509-A"
        a["intake_source"] = "v5.13 (federation-tenancy stream)"
        stale_pointer_pass(a, lean_index)
        if not (lo <= int(a.get("tier", 1)) <= hi):
            log(aid, f"tier CLAMP {a['tier']}→{hi}", "Beekeeper/Oppenheimer CLAMP", "")
            a["tier"] = hi
        canon["anchors"].append(a)
        idx[aid] = a
        log(aid, r["ruling"], "Oppenheimer Batch A", r.get("ruling_note", "")[:120])

    # Batch A canonical side-effects
    for aid, se in rulings["batch_A"]["canonical_side_effects"].items():
        a = idx.get(aid)
        if a is None:
            raise SystemExit(f"Side-effect target missing: {aid}")
        for k, v in se["set"].items():
            a[k] = v
        log(
            aid, "canonical side-effect", "Oppenheimer Batch A", se["ruling_note"][:140]
        )

    # ---- Batch C §2: v5_24-only intake ----------------------------------------
    c2 = rulings["batch_C_s2"]
    ref_t = rulings["ref_transform"]

    def intake_v524(aid: str, extra: dict, action: str, who: str, note: str) -> None:
        src = v524.get(aid)
        if src is None:
            raise SystemExit(f"Batch C anchor missing from v5_24 stream: {aid}")
        a = translate_v02_to_v03(src, pk_rules)
        a.update(extra)
        a["intake_batch"] = "509-C"
        a["intake_source"] = "v5_24 (QBP-web continued lineage)"
        # REF transform
        if aid.startswith(ref_t["applies_to_prefix"]):
            a["provenance_kind"] = ref_t["set"]["provenance_kind"]
            a["coherence_semantics"] = "citation-integrity (not endorsement)"
        stale_pointer_pass(a, lean_index)
        if not (lo <= int(a.get("tier", 1)) <= hi):
            log(aid, f"tier CLAMP {a['tier']}→{hi}", "Beekeeper/Oppenheimer CLAMP", "")
            a["tier"] = hi
        new_id = a["id"]
        if new_id in idx:
            raise SystemExit(f"Batch C collision with canonical: {new_id}")
        canon["anchors"].append(a)
        idx[new_id] = a
        log(new_id, action, who, note[:140])

    for aid in c2["substrate_nascent"]:
        intake_v524(
            aid,
            {"maturity": "nascent", "layer_tag": "substrate", "intake_rider": rider},
            "include-as-NASCENT + substrate tag",
            "Oppenheimer Batch C §2",
            rider,
        )
    for aid in c2["nascent_insight"]:
        intake_v524(
            aid,
            {"maturity": "nascent"},
            "include-as-NASCENT (insight)",
            "Oppenheimer Batch C §2",
            "chains to NASCENT parents",
        )
    for aid, rl in c2["relabel"].items():
        intake_v524(
            aid,
            {
                "id": rl["new_id"],
                "id_history": [aid],
                "lean_migration_status": "stale-pointer",
                "review_flag": True,
                "intake_note": rl["reason"],
            },
            f"RELABEL → {rl['new_id']}",
            "Oppenheimer Batch C §2 (truth-in-labelling, standing policy)",
            rl["reason"],
        )
    for aid in c2["standard_include"]:
        intake_v524(aid, {}, "include", "Oppenheimer Batch C §2", "")

    # ---- Batch C §3: theirs-side updates on in-both anchors --------------------
    c3 = rulings["batch_C_s3"]
    exceptions = c3["exceptions"]
    adopted, protected_hits = 0, 0
    for aid in sorted(set(base) & set(idx) & set(v524)):
        b, o, t = base[aid], idx[aid], v524[aid]
        exc = exceptions.get(aid, {})
        rule = exc.get("rule", c3["default"])
        protected = set(exc.get("protected_fields", []))
        for f in set(b) | set(t):
            if f in MIGRATION_FIELDS:
                continue
            bv, tv = b.get(f, "<M>"), t.get(f, "<M>")
            if tv == bv:
                continue  # theirs didn't change it
            ov = o.get(f, "<M>")
            if ov != bv:
                continue  # ours changed too (0 true conflicts verified; safety)
            if f in protected:
                protected_hits += 1
                log(
                    aid,
                    f"REJECTED adoption of `{f}`",
                    "Oppenheimer/cth Batch C §3",
                    exc["reason"][:120],
                )
                continue
            if rule == "null-fills-only" and tv is not None:
                protected_hits += 1
                log(
                    aid,
                    f"REJECTED non-null adoption of `{f}`",
                    "Oppenheimer Batch C §3",
                    "null-fills-only rule",
                )
                continue
            if f == "tier":
                tval = int(tv) if tv not in (None, "<M>") else 1
                if not (lo <= tval <= hi):
                    log(
                        aid,
                        f"tier CLAMP {tval}→{hi}",
                        "Beekeeper/Oppenheimer CLAMP",
                        "napkin issue filed",
                    )
                    tv = hi
            if tv == "<M>":
                o.pop(f, None)
            elif tv is None:
                # schema rejects null numerics; a null-fill means "explicitly unknown" — omit
                o.pop(f, None)
            else:
                o[f] = tv
            adopted += 1

    # ---- Conditional rider: Q27-TOV -------------------------------------------
    q27 = idx.get("Q27-TOV-limit-from-Fano")
    if q27 is not None:
        desc = str(q27.get("description", "")) + " " + str(q27.get("notes", ""))
        asserts_global = bool(
            re.search(r"(M_?max|maximum\s+(?:NS|neutron[- ]star)?\s*mass)", desc, re.I)
            and re.search(r"7\s*/\s*3|sqrt\(7/3\)|√\(?7/3\)?|2\.2", desc)
            and not re.search(r"bump[- ]peak|regime", desc, re.I)
        )
        if asserts_global:
            q27["physical_mapping_status"] = "falsified-as-global"
            q27["regime_of_validity"] = (
                "bump-peak rho_c only — see PRED-tov-mass-at-bump-peak"
            )
            log(
                "Q27-TOV-limit-from-Fano",
                "conditional rider APPLIED",
                "Oppenheimer criterion, mechanical",
                "description asserts global sqrt(7/3) M_max",
            )
        else:
            log(
                "Q27-TOV-limit-from-Fano",
                "conditional rider NOT triggered",
                "Oppenheimer criterion, mechanical",
                "Fano-derivation statement only",
            )

    # ---- Validate ---------------------------------------------------------------
    from jsonschema import Draft202012Validator

    schema = load(SCHEMA)
    v = Draft202012Validator(schema)
    errors = sorted(v.iter_errors(canon), key=lambda e: list(e.absolute_path))
    if errors:
        for e in errors[:20]:
            print(f"  ✗ /{'/'.join(str(p) for p in e.absolute_path)}: {e.message}")
        raise SystemExit(f"SCHEMA VALIDATION FAILED: {len(errors)} violations")

    tiers_ok = all(lo <= int(a.get("tier", 1)) <= hi for a in canon["anchors"])
    if not tiers_ok:
        raise SystemExit("TIER GATE FAILED post-apply")

    # ---- Write -------------------------------------------------------------------
    canon["last_updated"] = "2026-06-04"
    canon["update_provenance"] = (
        "QBP #509 unified vNext apply — batches A (24) + B (74) + C (28+55); "
        "see analysis/509-apply-provenance-trail.md"
    )
    CANON.write_text(json.dumps(canon, indent=2, ensure_ascii=False) + "\n")

    header = [
        "# QBP #509 Apply — Provenance Trail",
        "",
        "**Applied:** 2026-06-04 by qbp-implementor (Integration role) via `scripts/cth_509_apply.py`  ",
        "**Adjudication record:** `analysis/509-apply-rulings.json` (encodes #509 comments "
        "4627495414 / 4627533376 / 4627480904 / 4627520669 / 4627540950) + worksheets in `analysis/`  ",
        f"**Convention D (standing):** {rulings['_meta']['convention_D']}  ",
        f"**Result:** canonical ledger now {len(canon['anchors'])} anchors; schema-valid; tier domain [1,3] holds.",
        "",
    ]
    TRAIL.write_text("\n".join(header + trail) + "\n")

    print(f"APPLY COMPLETE: canonical now {len(canon['anchors'])} anchors")
    print(
        f"  §3 adoptions: {adopted} field-updates; protected rejections: {protected_hits}"
    )
    print(f"  trail: {TRAIL.relative_to(REPO)} ({len(trail)} rows)")


if __name__ == "__main__":
    main()
