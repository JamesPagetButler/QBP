#!/usr/bin/env python3
"""
CTH Inventory Reconciliation Diff — v5.13 ↔ v5_3 (Cycle 1)

Per #81 PR7 (Integration role) + the PR7 conflict-routing rubric committed
at docs/workflows/pr7_conflict_routing_rubric.md (PR #416).

Loads the two divergent inventory streams:
- archive/confluent-trust-inventory-v5.13.json (150 anchors, federation-tenancy)
- archive/confluent-trust-inventory-v5_3.json  (141 anchors, Session-13 closeout)

Produces a delta report classifying each difference by routing axis
(theory / schema / two-axis / not-conflict / unclassifiable) per the rubric.

Output: paper/CTH-Inventory-Reconciliation-Delta-v0.1.md

Authors: qbp-implementor (Claude Opus 4.7), Integration role
Date:    2026-05-14
"""

from __future__ import annotations
import json
import sys
from pathlib import Path
from typing import Any

QBP_ROOT = Path("/home/prime/Documents/QBP")
V513_PATH = QBP_ROOT / "archive/confluent-trust-inventory-v5.13.json"
V5_3_PATH = QBP_ROOT / "archive/confluent-trust-inventory-v5_3.json"
OUT_PATH = QBP_ROOT / "paper/CTH-Inventory-Reconciliation-Delta-v0.1.md"

# Field classification per the rubric (docs/workflows/pr7_conflict_routing_rubric.md)
THEORY_AXIS_FIELDS = {
    "status",
    "description",  # substantive
    "notes",  # scientific update
    "predicted_value",
    "predicted_unit",
    "measured_value",
    "measured_error",
    "discrepancy_pct",
    "prediction_chain",  # content (vs reference format)
    "interference_hypothesis",
    "interference_type",
    "converges_with",
    # last_tested_at — joint-axis: alone is schema; with status flip is theory
}
SCHEMA_AXIS_FIELDS = {
    "id",  # rename only
    "tier",
    "provenance",
    "proof_system",
    "proof_file",
    "sorry_count",
    "chain_id",  # placeholder vs real
    "last_tested_at",  # alone is schema
}
NOT_CONFLICT_FIELDS = {
    # If only these differ, not a real conflict
    "added_at",  # timestamp
    "updated_at",  # timestamp
}


def load_inventories():
    """Load both streams; return (v513, v5_3) as dicts."""
    v513 = json.loads(V513_PATH.read_text())
    v5_3 = json.loads(V5_3_PATH.read_text())
    return v513, v5_3


def index_anchors(inv: dict) -> dict[str, dict]:
    return {a["id"]: a for a in inv["anchors"]}


def diff_fields(a_513: dict, a_5_3: dict) -> dict[str, tuple]:
    """Return {field: (v513_value, v5_3_value)} for fields that differ."""
    diffs = {}
    keys = set(a_513.keys()) | set(a_5_3.keys())
    for k in keys:
        v513_val = a_513.get(k, "<MISSING>")
        v5_3_val = a_5_3.get(k, "<MISSING>")
        if v513_val != v5_3_val:
            diffs[k] = (v513_val, v5_3_val)
    return diffs


def classify_diff(diffs: dict[str, tuple]) -> str:
    """Classify per the routing rubric."""
    fields = set(diffs.keys())
    theory_hits = fields & THEORY_AXIS_FIELDS
    schema_hits = fields & SCHEMA_AXIS_FIELDS
    unknown = fields - THEORY_AXIS_FIELDS - SCHEMA_AXIS_FIELDS - NOT_CONFLICT_FIELDS
    # Special handling: last_tested_at — alone is schema; with status flip is theory
    if fields - NOT_CONFLICT_FIELDS == set():
        return "NOT_CONFLICT"
    if theory_hits and schema_hits:
        return (
            f"TWO_AXIS (theory: {sorted(theory_hits)} | schema: {sorted(schema_hits)})"
        )
    if theory_hits:
        return f"THEORY_AXIS ({sorted(theory_hits)})"
    if schema_hits:
        return f"SCHEMA_AXIS ({sorted(schema_hits)})"
    if unknown:
        return f"UNCLASSIFIABLE ({sorted(unknown)})"
    return "NOT_CONFLICT"


def truncate(s: Any, n: int = 80) -> str:
    if not isinstance(s, str):
        s = repr(s)
    if len(s) > n:
        return s[:n] + "…"
    return s


def main():
    v513, v5_3 = load_inventories()
    idx_513 = index_anchors(v513)
    idx_5_3 = index_anchors(v5_3)

    only_513 = sorted(set(idx_513) - set(idx_5_3))
    only_5_3 = sorted(set(idx_5_3) - set(idx_513))
    both = sorted(set(idx_513) & set(idx_5_3))

    # Classify the in-both anchors
    classifications: dict[str, list] = {
        "NOT_CONFLICT": [],
        "THEORY_AXIS": [],
        "SCHEMA_AXIS": [],
        "TWO_AXIS": [],
        "UNCLASSIFIABLE": [],
    }
    in_both_diffs = {}
    for aid in both:
        diffs = diff_fields(idx_513[aid], idx_5_3[aid])
        if not diffs:
            classifications["NOT_CONFLICT"].append(aid)
            continue
        cls = classify_diff(diffs)
        in_both_diffs[aid] = (diffs, cls)
        cls_key = cls.split(" ")[0]
        classifications[cls_key].append(aid)

    # Top-level shape diff
    top_513 = set(v513.keys()) - set(v5_3.keys())
    top_5_3 = set(v5_3.keys()) - set(v513.keys())

    # Schema field universe in each stream
    fields_513 = set()
    fields_5_3 = set()
    for a in v513["anchors"]:
        fields_513.update(a.keys())
    for a in v5_3["anchors"]:
        fields_5_3.update(a.keys())
    fields_only_513 = fields_513 - fields_5_3
    fields_only_5_3 = fields_5_3 - fields_513

    # Write delta report
    lines: list[str] = []
    lines.append("# CTH Inventory Reconciliation Delta — v5.13 ↔ v5_3")
    lines.append("")
    lines.append(
        f"**Generated:** by `scripts/cth_inventory_diff.py` (qbp-implementor, 2026-05-14)"
    )
    lines.append(
        "**Routing rubric:** `docs/workflows/pr7_conflict_routing_rubric.md` (PR #416)"
    )
    lines.append(
        "**Authority:** Beekeeper D4 (2026-05-13) — theory-axis → qbp-oppenheimer; schema-axis → cth-implementor"
    )
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Headline counts")
    lines.append("")
    lines.append("| | v5.13 (federation-tenancy) | v5_3 (Session-13) |")
    lines.append("|---|---|---|")
    lines.append(f"| Total anchors | {len(idx_513)} | {len(idx_5_3)} |")
    lines.append(
        f"| Anchor IDs only in this stream | {len(only_513)} | {len(only_5_3)} |"
    )
    lines.append(f"| Anchor IDs in both | {len(both)} | {len(both)} |")
    lines.append("")
    lines.append("## In-both anchor classification (per rubric)")
    lines.append("")
    lines.append("| Class | Count | Route |")
    lines.append("|---|---|---|")
    for k in [
        "NOT_CONFLICT",
        "SCHEMA_AXIS",
        "THEORY_AXIS",
        "TWO_AXIS",
        "UNCLASSIFIABLE",
    ]:
        route = {
            "NOT_CONFLICT": "(skip — handle in-stream)",
            "SCHEMA_AXIS": "→ cth-implementor",
            "THEORY_AXIS": "→ qbp-oppenheimer",
            "TWO_AXIS": "→ both, schema first",
            "UNCLASSIFIABLE": "→ escalate to bridge",
        }[k]
        lines.append(f"| {k} | {len(classifications[k])} | {route} |")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Top-level schema differences")
    lines.append("")
    if top_513:
        lines.append(f"- Top-level keys only in v5.13: `{sorted(top_513)}`")
    if top_5_3:
        lines.append(f"- Top-level keys only in v5_3: `{sorted(top_5_3)}`")
    if not top_513 and not top_5_3:
        lines.append("- Top-level shape identical.")
    lines.append("")
    lines.append("## Anchor-field schema differences")
    lines.append("")
    if fields_only_513:
        lines.append(f"- Anchor fields only in v5.13: `{sorted(fields_only_513)}`")
    if fields_only_5_3:
        lines.append(f"- Anchor fields only in v5_3: `{sorted(fields_only_5_3)}`")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append(f"## Anchors only in v5.13 ({len(only_513)})")
    lines.append("")
    lines.append(
        "Likely federation-tenancy / qbp-architecture-stream additions. Each needs a decision: import into unified vNext, or drop as federation-only."
    )
    lines.append("")
    lines.append("| Anchor ID | Name (truncated) | Tier | Provenance |")
    lines.append("|---|---|---|---|")
    for aid in only_513:
        a = idx_513[aid]
        lines.append(
            f"| `{aid}` | {truncate(a.get('name', '<no name>'), 60)} | {a.get('tier', '?')} | {a.get('provenance', '?')} |"
        )
    lines.append("")
    lines.append(f"## Anchors only in v5_3 ({len(only_5_3)})")
    lines.append("")
    lines.append(
        "Likely Session-13 / QBP-web-stream additions (including the canonical Session-13 closeout: KILLED-f4-info-theoretic-justification, CONV-cd-tower-in-zeta-moments, CONV-spectral-entropy-zeta)."
    )
    lines.append("")
    lines.append("| Anchor ID | Name (truncated) | Tier | Provenance |")
    lines.append("|---|---|---|---|")
    for aid in only_5_3:
        a = idx_5_3[aid]
        lines.append(
            f"| `{aid}` | {truncate(a.get('name', '<no name>'), 60)} | {a.get('tier', '?')} | {a.get('provenance', '?')} |"
        )
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## In-both anchors with differences (detail)")
    lines.append("")
    lines.append(
        f"{len(in_both_diffs)} of {len(both)} in-both anchors have at least one differing field."
    )
    lines.append("")
    for cls in [
        "TWO_AXIS",
        "THEORY_AXIS",
        "SCHEMA_AXIS",
        "UNCLASSIFIABLE",
        "NOT_CONFLICT",
    ]:
        bucket = [aid for aid in classifications.get(cls, []) if aid in in_both_diffs]
        if not bucket:
            continue
        lines.append(f"### {cls} ({len(bucket)})")
        lines.append("")
        lines.append("| Anchor ID | Differing fields | Sample v5.13 | Sample v5_3 |")
        lines.append("|---|---|---|---|")
        for aid in bucket[:30]:  # Cap each section to 30 for readability
            diffs, _classification = in_both_diffs[aid]
            field_list = ", ".join(f"`{k}`" for k in sorted(diffs.keys()))
            # Pick the first non-trivial field for the sample columns
            first_field = sorted(diffs.keys())[0]
            v513_v, v5_3_v = diffs[first_field]
            lines.append(
                f"| `{aid}` | {field_list} | {truncate(v513_v, 40)} | {truncate(v5_3_v, 40)} |"
            )
        if len(bucket) > 30:
            lines.append(f"")
            lines.append(
                f"(... {len(bucket) - 30} additional `{cls}` entries truncated; see full classification table in the script output.)"
            )
        lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## Cycle 1 conclusion")
    lines.append("")
    lines.append(
        "Structural delta surfaced; classification table seeded. Cycle 2 will produce per-anchor merge proposals for THEORY_AXIS + TWO_AXIS entries, routed to @qbp-oppenheimer adjudication. SCHEMA_AXIS entries route to @cth-implementor for schema-level merge decisions. NOT_CONFLICT entries auto-fold into vNext."
    )
    lines.append("")
    lines.append("## Provenance")
    lines.append("")
    lines.append(f"- Script: `scripts/cth_inventory_diff.py`")
    lines.append(
        f"- Input: `archive/confluent-trust-inventory-v5.13.json` ({V513_PATH.stat().st_size} bytes)"
    )
    lines.append(
        f"- Input: `archive/confluent-trust-inventory-v5_3.json` ({V5_3_PATH.stat().st_size} bytes)"
    )
    lines.append(
        f"- Routing rubric: `docs/workflows/pr7_conflict_routing_rubric.md` (PR #416)"
    )
    lines.append("")

    OUT_PATH.write_text("\n".join(lines))
    print(f"Delta report written to: {OUT_PATH}")
    print(
        f"  {len(only_513)} v5.13-only / {len(only_5_3)} v5_3-only / {len(both)} in-both"
    )
    print(
        f"  Classifications: {' / '.join(f'{k}={len(v)}' for k, v in classifications.items())}"
    )


if __name__ == "__main__":
    main()
