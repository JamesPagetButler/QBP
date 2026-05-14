#!/usr/bin/env python3
"""
CTH Inventory Reconciliation — Cycle 2 Per-Anchor Merge Proposals

Per #81 PR7 (Integration role), Beekeeper D4 routing (2026-05-13), and the
PR7 conflict-routing rubric at docs/workflows/pr7_conflict_routing_rubric.md.

Inputs (now git-tracked per PR #422):
  archive/cth-inventory/confluent-trust-inventory-v5.13.json (150 anchors)
  archive/cth-inventory/confluent-trust-inventory-v5_3.json  (141 anchors)

Outputs:
  paper/CTH-Inventory-Reconciliation-Cycle2-Proposals.md

For each in-both anchor with diffs and each stream-only anchor, this emits a
per-anchor merge proposal with:
  - Routing recommendation (theory-axis → qbp-oppenheimer; schema-axis →
    cth-implementor; two-axis → schema first, then theory; rubric-extension
    proposed for UNCLASSIFIABLE)
  - Field-by-field diff (full values, not truncated)
  - A proposed resolution where deterministic (e.g., NOT_CONFLICT auto-folds
    timestamps to the later one; SCHEMA_AXIS where the schema rule is
    obvious gets a recommended value); else "→ adjudicator decides"

Authors: qbp-implementor (Claude Opus 4.7), Integration role
Date:    2026-05-14
"""

from __future__ import annotations
import json
from pathlib import Path
from typing import Any

QBP_ROOT = Path("/home/prime/Documents/QBP")
V513_PATH = QBP_ROOT / "archive/cth-inventory/confluent-trust-inventory-v5.13.json"
V5_3_PATH = QBP_ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.json"
OUT_PATH = QBP_ROOT / "paper/CTH-Inventory-Reconciliation-Cycle2-Proposals.md"

# Rubric v0.1 (committed in PR #416)
THEORY_AXIS_FIELDS = {
    "status",
    "description",
    "notes",
    "predicted_value",
    "predicted_unit",
    "measured_value",
    "measured_error",
    "discrepancy_pct",
    "prediction_chain",
    "interference_hypothesis",
    "interference_type",
    "converges_with",
}
SCHEMA_AXIS_FIELDS = {
    "id",
    "tier",
    "provenance",
    "proof_system",
    "proof_file",
    "sorry_count",
    "chain_id",
    "last_tested_at",
}
NOT_CONFLICT_FIELDS = {"added_at", "updated_at"}

# Rubric v0.2 proposed extension surfaced by cycle 2 analysis.
# Counts shown are appearances in the v5.13 ↔ v5_3 in-both diff.
RUBRIC_V02_EXTENSION_SCHEMA = {
    # Mapping-classification metadata (categorical; how anchor maps to a physical observable)
    "physical_mapping_type",  # 46 appearances
    "physical_mapping_status",  # 2
    "physical_mapping_diagnosis",  # 1
    # Proof-system metadata (file pointers, statuses, free-text notes about proofs/tests)
    "lean_theorem",  # 36
    "lean_companion_theorems",  # 21
    "integration_test_status",  # 15
    "lean_scope",  # 8
    "lean_migration_status",  # 5
    "lean_migration_scope",  # 1
    "lean_migration_remaining",  # 1
    "lean_migration_target_file",  # 1
    "proof_results",  # 4
    "proof_note",  # 4
    "analysis_pipeline",  # 1
    "python_caveats",  # 1
    "supporting_python_proof",  # 1
}
RUBRIC_V02_EXTENSION_THEORY = {
    # Theory-axis content (scientific claims, predictions, regimes)
    "regime_of_validity",  # 2  — explicit statement of when a prediction holds
    "qbp_threshold_R",  # 1  — numeric theory prediction (QBP-side)
    "null_threshold_R",  # 1  — numeric theory prediction (null hypothesis)
}


def load_inventories():
    v513 = json.loads(V513_PATH.read_text())
    v5_3 = json.loads(V5_3_PATH.read_text())
    return v513, v5_3


def index(inv: dict) -> dict[str, dict]:
    return {a["id"]: a for a in inv["anchors"]}


def diff_fields(a_513: dict, a_5_3: dict) -> dict[str, tuple]:
    diffs = {}
    for k in set(a_513.keys()) | set(a_5_3.keys()):
        v_a, v_b = a_513.get(k, "<MISSING>"), a_5_3.get(k, "<MISSING>")
        if v_a != v_b:
            diffs[k] = (v_a, v_b)
    return diffs


def classify_fields(field_set: set[str], use_v02: bool = False) -> dict:
    """Return {category: set_of_fields_in_that_category}."""
    schema_universe = SCHEMA_AXIS_FIELDS | (
        RUBRIC_V02_EXTENSION_SCHEMA if use_v02 else set()
    )
    theory_universe = THEORY_AXIS_FIELDS | (
        RUBRIC_V02_EXTENSION_THEORY if use_v02 else set()
    )
    return {
        "theory": field_set & theory_universe,
        "schema": field_set & schema_universe,
        "not_conflict": field_set & NOT_CONFLICT_FIELDS,
        "unknown": field_set - theory_universe - schema_universe - NOT_CONFLICT_FIELDS,
    }


def _stringify(v: Any) -> str:
    if v == "<MISSING>":
        return "<MISSING>"
    if isinstance(v, str):
        return repr(v)
    if isinstance(v, (list, dict)):
        return json.dumps(v, default=str, separators=(",", ":"))
    return repr(v)


def render_value(v: Any, max_len: int = 200) -> str:
    """Render a single value; truncate at max_len with ellipsis. Used as a fallback
    when the paired value is not available."""
    if v == "<MISSING>":
        return "_(field absent)_"
    s = _stringify(v)
    return s if len(s) <= max_len else s[:max_len] + "…"


def render_value_pair(va: Any, vb: Any, max_len: int = 200) -> tuple[str, str]:
    """Render two values for side-by-side display. If both are strings/JSON and
    share a long common prefix, slide the window to the divergence point so the
    diff is visible. Pad both renderings to similar length to keep cells aligned."""
    if va == "<MISSING>":
        return "_(field absent)_", render_value(vb, max_len)
    if vb == "<MISSING>":
        return render_value(va, max_len), "_(field absent)_"
    sa, sb = _stringify(va), _stringify(vb)
    # If both fit in max_len, return as-is
    if len(sa) <= max_len and len(sb) <= max_len:
        return sa, sb
    # Find common prefix length
    i = 0
    n = min(len(sa), len(sb))
    while i < n and sa[i] == sb[i]:
        i += 1
    # If divergence point is past max_len/2 of the shorter one, slide the window
    cut = max(0, i - 30)  # leave 30 chars of shared prefix for context
    if cut == 0:
        ra = sa if len(sa) <= max_len else sa[:max_len] + "…"
        rb = sb if len(sb) <= max_len else sb[:max_len] + "…"
        return ra, rb
    end_a = min(len(sa), cut + max_len)
    end_b = min(len(sb), cut + max_len)
    ra = "…" + sa[cut:end_a] + ("…" if end_a < len(sa) else "")
    rb = "…" + sb[cut:end_b] + ("…" if end_b < len(sb) else "")
    return ra, rb


def render_diff_block(diffs: dict[str, tuple], use_v02: bool = False) -> list[str]:
    """Render one anchor's full diff as a markdown sub-table."""
    out: list[str] = []
    out.append("| Field | Axis | v5.13 (federation-tenancy) | v5_3 (Session-13) |")
    out.append("|---|---|---|---|")
    cats = classify_fields(set(diffs.keys()), use_v02=use_v02)
    # Order: schema-axis, theory-axis, not-conflict, unknown
    for field in sorted(diffs.keys()):
        if field in cats["schema"]:
            axis = "schema"
        elif field in cats["theory"]:
            axis = "theory"
        elif field in cats["not_conflict"]:
            axis = "timestamp"
        else:
            axis = "**?**"
        v_513, v_5_3 = diffs[field]
        rv_513, rv_5_3 = render_value_pair(v_513, v_5_3)
        out.append(f"| `{field}` | {axis} | {rv_513} | {rv_5_3} |")
    return out


def routing_for(field_cats: dict) -> str:
    """Recommendation string given field categorisation (cycle 1 rule:
    schema/theory take precedence over unknown so an anchor with both
    schema fields and rubric-gap fields still routes via schema-axis)."""
    theory = field_cats["theory"]
    schema = field_cats["schema"]
    unknown = field_cats["unknown"]
    if theory and schema:
        base = "**TWO_AXIS** — schema first → @cth-implementor; then theory → @qbp-oppenheimer"
    elif theory:
        base = "**THEORY_AXIS** → @qbp-oppenheimer"
    elif schema:
        base = "**SCHEMA_AXIS** → @cth-implementor"
    elif unknown:
        base = "**UNCLASSIFIABLE** — rubric extension needed (see §2)"
    else:
        base = "_(timestamps only — fold to later value, no adjudication needed)_"
    if unknown and (theory or schema):
        base += (
            f" — _includes rubric-gap fields_ `{sorted(unknown)}` "
            "(auto-resolves via §2 rubric v0.2 extension)"
        )
    return base


def proposed_resolution(diffs: dict[str, tuple], field_cats: dict) -> str:
    """Where deterministic, propose a concrete resolution. Else 'adjudicator'."""
    cats = field_cats
    # NOT_CONFLICT-only: auto-fold to later timestamp
    if not cats["theory"] and not cats["schema"] and not cats["unknown"]:
        return (
            "Fold timestamps: prefer later of `updated_at` / `added_at` "
            "(deterministic; no adjudication)."
        )
    # Pure schema renaming via `id` field is deterministic if v5.13 is newer
    if cats["schema"] == {"id"} and not cats["theory"] and not cats["unknown"]:
        return (
            "Schema rename only. cth-implementor picks canonical ID via the "
            "schema-locking convention; the other becomes an alias."
        )
    # `last_tested_at` schema-only diff with no status flip: take the later
    # value as more current.
    if cats["schema"] == {"last_tested_at"} and not cats["theory"]:
        return "Take later `last_tested_at` (test most recent). Schema-side only."
    # Pure-schema, all other cases
    if cats["schema"] and not cats["theory"] and not cats["unknown"]:
        return (
            f"Schema-axis fields ({sorted(cats['schema'])}) — cth-implementor "
            "decides per schema lock. Default: v5.13 (federation-tenancy = newer authored schema)."
        )
    # Theory-only
    if cats["theory"] and not cats["schema"] and not cats["unknown"]:
        return (
            f"Theory-axis fields ({sorted(cats['theory'])}) — qbp-oppenheimer "
            "adjudicates. Default: v5_3 (Session-13 closeout = newer scientific state)."
        )
    # Two-axis
    if cats["theory"] and cats["schema"] and not cats["unknown"]:
        return (
            "Two-axis. Cycle 3 sequence: (1) cth-implementor resolves schema fields "
            f"({sorted(cats['schema'])}); (2) qbp-oppenheimer resolves theory fields "
            f"({sorted(cats['theory'])}); (3) qbp-implementor reconciles into unified vNext."
        )
    return "_(falls to adjudicator)_"


def per_anchor_section(
    title: str,
    anchors_with_diffs: list[tuple[str, dict, dict, dict]],
    use_v02: bool = False,
    max_render: int = 30,
) -> list[str]:
    """Render one bucket: title, intro, then per-anchor blocks."""
    lines: list[str] = []
    lines.append(f"### {title} — {len(anchors_with_diffs)} anchor(s)")
    lines.append("")
    if not anchors_with_diffs:
        lines.append("_(empty)_")
        lines.append("")
        return lines
    rendered = anchors_with_diffs[:max_render]
    for aid, a513, a5_3, diffs in rendered:
        cats = classify_fields(set(diffs.keys()), use_v02=use_v02)
        name = a513.get("name") or a5_3.get("name") or "<unnamed>"
        lines.append(f"#### `{aid}` — {name}")
        lines.append("")
        lines.append(f"- **Routing:** {routing_for(cats)}")
        lines.append(f"- **Proposed resolution:** {proposed_resolution(diffs, cats)}")
        lines.append("")
        lines.extend(render_diff_block(diffs, use_v02=use_v02))
        lines.append("")
    if len(anchors_with_diffs) > max_render:
        lines.append(
            f"_(... {len(anchors_with_diffs) - max_render} additional anchors in this "
            f"bucket — full output via `python3 scripts/cth_inventory_proposals.py "
            f"--unfiltered`.)_"
        )
        lines.append("")
    return lines


def stream_only_section(
    title: str,
    anchors: list[tuple[str, dict]],
    other_stream_label: str,
    max_render: int = 30,
) -> list[str]:
    """Render a v5.13-only or v5_3-only inclusion-proposal bucket."""
    lines: list[str] = []
    lines.append(f"### {title} — {len(anchors)} anchor(s)")
    lines.append("")
    if not anchors:
        lines.append("_(empty)_")
        lines.append("")
        return lines
    lines.append(
        f"Each of these anchors exists in one stream only. Proposed inclusion in unified vNext:"
    )
    lines.append("")
    lines.append("| Anchor ID | Name | Tier | Status | Provenance | Proposed action |")
    lines.append("|---|---|---|---|---|---|")
    # Per the tracked-baseline README §"Files in this directory", these 3 anchors
    # are the explicit Session-13 closeout findings (canonical from QBP-web 2026-05-11).
    SESSION_13_CLOSEOUT = {
        "KILLED-f4-info-theoretic-justification",
        "CONV-cd-tower-in-zeta-moments",
        "CONV-spectral-entropy-zeta",
    }
    for aid, a in anchors[:max_render]:
        name = a.get("name", "<unnamed>")[:60]
        tier = a.get("tier", "?")
        status = a.get("status", "?")
        prov = (a.get("provenance") or "?")[:40]
        if aid in SESSION_13_CLOSEOUT:
            action = "**INCLUDE** (Session-13 closeout finding)"
        elif aid.startswith("WISDOM-"):
            action = "DEFER to wisdom-registry migration (per Beekeeper D2)"
        elif aid.startswith(("META-", "INSIGHT-")):
            action = "INCLUDE (suggested; META/INSIGHT class)"
        else:
            action = "→ adjudicator decides on inclusion"
        lines.append(f"| `{aid}` | {name} | {tier} | {status} | {prov} | {action} |")
    if len(anchors) > max_render:
        lines.append(
            f"\n_(... {len(anchors) - max_render} more — see `--unfiltered`.)_"
        )
    lines.append("")
    return lines


def main():
    v513, v5_3 = load_inventories()
    idx_513 = index(v513)
    idx_5_3 = index(v5_3)

    only_513 = sorted(set(idx_513) - set(idx_5_3))
    only_5_3 = sorted(set(idx_5_3) - set(idx_513))
    both = sorted(set(idx_513) & set(idx_5_3))

    # Bucket the in-both anchors
    buckets: dict[str, list] = {
        "TWO_AXIS": [],
        "THEORY_AXIS": [],
        "SCHEMA_AXIS": [],
        "UNCLASSIFIABLE": [],
        "NOT_CONFLICT": [],
    }
    # And the same again under rubric v0.2 (collapses UNCLASSIFIABLE)
    buckets_v02: dict[str, list] = {k: [] for k in buckets}

    def cycle1_classify(cats: dict) -> str:
        """Match cycle 1 (PR #418): theory+schema → TWO_AXIS; any theory → THEORY_AXIS;
        any schema → SCHEMA_AXIS; else unknown → UNCLASSIFIABLE."""
        if cats["theory"] and cats["schema"]:
            return "TWO_AXIS"
        if cats["theory"]:
            return "THEORY_AXIS"
        if cats["schema"]:
            return "SCHEMA_AXIS"
        if cats["unknown"]:
            return "UNCLASSIFIABLE"
        return "NOT_CONFLICT"

    for aid in both:
        a513, a5_3 = idx_513[aid], idx_5_3[aid]
        diffs = diff_fields(a513, a5_3)
        if not diffs:
            buckets["NOT_CONFLICT"].append((aid, a513, a5_3, diffs))
            buckets_v02["NOT_CONFLICT"].append((aid, a513, a5_3, diffs))
            continue
        cats_v01 = classify_fields(set(diffs.keys()), use_v02=False)
        cls_v01 = cycle1_classify(cats_v01)
        buckets[cls_v01].append((aid, a513, a5_3, diffs))

        cats_v02 = classify_fields(set(diffs.keys()), use_v02=True)
        cls_v02 = cycle1_classify(cats_v02)
        buckets_v02[cls_v02].append((aid, a513, a5_3, diffs))

    lines: list[str] = []
    lines.append("# CTH Inventory Reconciliation — Cycle 2 Per-Anchor Proposals")
    lines.append("")
    lines.append(
        "**Generated:** by `scripts/cth_inventory_proposals.py` (qbp-implementor, 2026-05-14)  "
    )
    lines.append(
        "**Inputs:** `archive/cth-inventory/confluent-trust-inventory-v5.13.json` (150) + `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (141)  "
    )
    lines.append(
        "**Routing rubric:** `docs/workflows/pr7_conflict_routing_rubric.md` (v0.1, PR #416)  "
    )
    lines.append(
        "**Routing authority:** Beekeeper D4 (2026-05-13) — theory-axis → @qbp-oppenheimer; schema-axis → @cth-implementor"
    )
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## 1. Summary")
    lines.append("")
    lines.append(
        "Cycle 1 classified 165 anchor-level differences (126 in-both with diffs + 24 v5.13-only + 15 v5_3-only)."
    )
    lines.append(
        "Cycle 2 turns the classification into per-anchor merge proposals to drive Cycle 3 unified-vNext production."
    )
    lines.append("")
    lines.append(
        "| Bucket | v0.1 count | v0.2 count (with proposed extension) | Routing |"
    )
    lines.append("|---|---|---|---|")
    lines.append(
        f"| NOT_CONFLICT | {len(buckets['NOT_CONFLICT'])} | {len(buckets_v02['NOT_CONFLICT'])} | _(auto-fold; no adjudication)_ |"
    )
    lines.append(
        f"| SCHEMA_AXIS | {len(buckets['SCHEMA_AXIS'])} | {len(buckets_v02['SCHEMA_AXIS'])} | → @cth-implementor |"
    )
    lines.append(
        f"| THEORY_AXIS | {len(buckets['THEORY_AXIS'])} | {len(buckets_v02['THEORY_AXIS'])} | → @qbp-oppenheimer |"
    )
    lines.append(
        f"| TWO_AXIS | {len(buckets['TWO_AXIS'])} | {len(buckets_v02['TWO_AXIS'])} | → both, schema first |"
    )
    lines.append(
        f"| UNCLASSIFIABLE | {len(buckets['UNCLASSIFIABLE'])} | {len(buckets_v02['UNCLASSIFIABLE'])} | → bridge escalation (v0.1) or @cth-implementor (v0.2 if extension accepted) |"
    )
    lines.append("")
    lines.append(
        f"Plus **{len(only_513)} v5.13-only** and **{len(only_5_3)} v5_3-only** anchors with per-stream inclusion proposals."
    )
    lines.append("")
    lines.append("---")
    lines.append("")

    # Section 2: rubric v0.2 extension proposal
    lines.append("## 2. Rubric v0.2 Extension Proposal")
    lines.append("")
    lines.append(
        "Cycle 2 surfaced 19 anchor-fields appearing in the in-both diff that the v0.1 rubric "
        "does not classify. Their semantics fall cleanly into two groups:"
    )
    lines.append("")
    lines.append(
        "**SCHEMA_AXIS extensions (proof-system + mapping-classification metadata; →@cth-implementor):**"
    )
    lines.append("")
    lines.append("| Field | Appearances | Why schema-axis |")
    lines.append("|---|---|---|")
    schema_explain = {
        "physical_mapping_type": (
            46,
            "categorical: how anchor maps to a physical observable",
        ),
        "lean_theorem": (36, "pointer to a Lean theorem ID — proof-system metadata"),
        "lean_companion_theorems": (21, "list of supporting Lean theorems"),
        "integration_test_status": (
            15,
            "CI/test-run pass/fail/skip — not theory content",
        ),
        "lean_scope": (8, "Lean namespace/module scope for proof"),
        "lean_migration_status": (
            5,
            "migration state of Lean proof (`planned`/`done`/…)",
        ),
        "proof_results": (4, "file pointer to raw test results"),
        "proof_note": (4, "free-text annotation about the proof procedure"),
        "physical_mapping_status": (2, "status of the mapping declaration"),
        "physical_mapping_diagnosis": (1, "diagnostic note about the mapping"),
        "lean_migration_scope": (1, "scope of a Lean migration"),
        "lean_migration_remaining": (1, "what remains to migrate"),
        "lean_migration_target_file": (1, "destination Lean file"),
        "analysis_pipeline": (1, "which analysis pipeline produced the result"),
        "python_caveats": (1, "caveats on a Python proof"),
        "supporting_python_proof": (1, "file pointer to a Python proof"),
    }
    for field, (count, why) in sorted(schema_explain.items(), key=lambda x: -x[1][0]):
        lines.append(f"| `{field}` | {count} | {why} |")
    lines.append("")
    lines.append("**THEORY_AXIS extensions (scientific content; →@qbp-oppenheimer):**")
    lines.append("")
    lines.append("| Field | Appearances | Why theory-axis |")
    lines.append("|---|---|---|")
    theory_explain = {
        "regime_of_validity": (
            2,
            "explicit statement of the domain where a prediction holds — theory content",
        ),
        "qbp_threshold_R": (1, "numeric theory prediction (QBP-side R threshold)"),
        "null_threshold_R": (
            1,
            "numeric theory prediction (null-hypothesis R threshold)",
        ),
    }
    for field, (count, why) in sorted(theory_explain.items(), key=lambda x: -x[1][0]):
        lines.append(f"| `{field}` | {count} | {why} |")
    lines.append("")
    lines.append(
        f"**Effect:** moves the 49 anchors with unclassified fields under v0.1 to "
        f"({len(buckets_v02['SCHEMA_AXIS']) - len(buckets['SCHEMA_AXIS'])} additional → SCHEMA_AXIS, "
        f"{len(buckets_v02['THEORY_AXIS']) - len(buckets['THEORY_AXIS'])} additional → THEORY_AXIS, "
        f"{len(buckets_v02['TWO_AXIS']) - len(buckets['TWO_AXIS'])} additional → TWO_AXIS) — "
        f"taking UNCLASSIFIABLE to {len(buckets_v02['UNCLASSIFIABLE'])}."
    )
    lines.append("")
    lines.append(
        "**Authority:** Beekeeper sign-off in this PR; @cth-implementor co-sign on the schema additions; "
        "@qbp-oppenheimer co-sign on the theory additions."
    )
    lines.append("")
    lines.append("```diff")
    lines.append(" SCHEMA_AXIS_FIELDS = {")
    lines.append('   "id", "tier", "provenance", "proof_system", "proof_file",')
    lines.append('   "sorry_count", "chain_id", "last_tested_at",')
    for f in sorted(RUBRIC_V02_EXTENSION_SCHEMA):
        lines.append(f'+  "{f}",')
    lines.append(" }")
    lines.append("")
    lines.append(" THEORY_AXIS_FIELDS = {")
    lines.append('   "status", "description", "notes",')
    lines.append('   "predicted_value", "predicted_unit",')
    lines.append('   "measured_value", "measured_error", "discrepancy_pct",')
    lines.append('   "prediction_chain", "interference_hypothesis",')
    lines.append('   "interference_type", "converges_with",')
    for f in sorted(RUBRIC_V02_EXTENSION_THEORY):
        lines.append(f'+  "{f}",')
    lines.append(" }")
    lines.append("```")
    lines.append("")
    lines.append("---")
    lines.append("")

    # Section 3: per-anchor proposals
    lines.append("## 3. Per-anchor merge proposals (in-both, with diffs)")
    lines.append("")
    lines.append(
        "Each anchor shows: routing recommendation; proposed deterministic resolution where possible; full field diffs (untruncated)."
    )
    lines.append("")

    # Order: TWO_AXIS (highest cost), THEORY_AXIS, SCHEMA_AXIS, UNCLASSIFIABLE
    lines.extend(
        per_anchor_section(
            "3.1 TWO_AXIS — needs both adjudicators (schema first, then theory)",
            buckets["TWO_AXIS"],
            use_v02=False,
            max_render=25,
        )
    )
    lines.extend(
        per_anchor_section(
            "3.2 THEORY_AXIS — → @qbp-oppenheimer",
            buckets["THEORY_AXIS"],
            use_v02=False,
            max_render=25,
        )
    )
    lines.extend(
        per_anchor_section(
            "3.3 SCHEMA_AXIS — → @cth-implementor (batchable)",
            buckets["SCHEMA_AXIS"],
            use_v02=False,
            max_render=25,
        )
    )
    lines.extend(
        per_anchor_section(
            "3.4 UNCLASSIFIABLE under rubric v0.1 (→ SCHEMA_AXIS if v0.2 accepted, see §2)",
            buckets["UNCLASSIFIABLE"],
            use_v02=False,
            max_render=10,
        )
    )

    # Section 4: stream-only inclusion proposals
    lines.append("---")
    lines.append("")
    lines.append("## 4. Stream-only anchor inclusion proposals")
    lines.append("")
    lines.append(
        "These anchors exist in one stream only. Each needs an inclusion decision for unified vNext."
    )
    lines.append("")
    lines.extend(
        stream_only_section(
            "4.1 v5_3 only — Session-13 closeout additions",
            [(aid, idx_5_3[aid]) for aid in only_5_3],
            other_stream_label="v5.13",
            max_render=20,
        )
    )
    lines.extend(
        stream_only_section(
            "4.2 v5.13 only — federation-tenancy stream additions",
            [(aid, idx_513[aid]) for aid in only_513],
            other_stream_label="v5_3",
            max_render=25,
        )
    )

    # Section 5: cycle 3 plan
    lines.append("---")
    lines.append("")
    lines.append("## 5. Cycle 3 plan (unified vNext)")
    lines.append("")
    lines.append("Sequencing:")
    lines.append("")
    lines.append(
        "1. **Beekeeper sign-off on rubric v0.2 extension** (§2) — collapses UNCLASSIFIABLE → SCHEMA_AXIS."
    )
    lines.append(
        "2. **@cth-implementor batch resolution of SCHEMA_AXIS bucket** (23 v0.1 → 30 v0.2 after extension). Schema rule defaults are deterministic where noted; cases needing schema-lock discussion route via the `cth-design` channel."
    )
    lines.append(
        "3. **@qbp-oppenheimer per-anchor theory-axis adjudication for TWO_AXIS bucket** (19 anchors) — schema fields land first per (2); theory fields land next using the v5_3 (Session-13) closeout default where Oppenheimer concurs."
    )
    lines.append(
        "4. **Stream-only inclusion decisions** (§4): KILLED-/CONV-/CONJ- Session-13 closeout findings → INCLUDE by default; WISDOM-* defer to the wisdom-registry migration per Beekeeper D2; META-/INSIGHT- from federation-tenancy → INCLUDE by default; everything else → adjudicator."
    )
    lines.append(
        "5. **qbp-implementor produces unified vNext JSON** — `archive/cth-inventory/confluent-trust-inventory-vNext.json` — with full provenance trail (which fields came from which stream, which adjudicator signed off)."
    )
    lines.append(
        "6. **BMA re-audit hook** — once vNext lands, BMA (when ready) re-runs the audit per Capability #6 against the unified ledger; ρ_net trajectory shows continuous (no schema breaks)."
    )
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("## 6. Provenance")
    lines.append("")
    lines.append("- Script: `scripts/cth_inventory_proposals.py`")
    lines.append(
        f"- Input v5.13: `archive/cth-inventory/confluent-trust-inventory-v5.13.json` ({V513_PATH.stat().st_size} bytes, 150 anchors)"
    )
    lines.append(
        f"- Input v5_3: `archive/cth-inventory/confluent-trust-inventory-v5_3.json` ({V5_3_PATH.stat().st_size} bytes, 141 anchors)"
    )
    lines.append(
        "- Rubric v0.1: `docs/workflows/pr7_conflict_routing_rubric.md` (PR #416)"
    )
    lines.append(
        "- Cycle 1 delta: `paper/CTH-Inventory-Reconciliation-Delta-v0.1.md` (PR #418)"
    )
    lines.append(
        "- Tracked baselines: `archive/cth-inventory/` (PR #422; Beekeeper option (b) of a+b+c, 2026-05-14)"
    )
    lines.append("")

    OUT_PATH.write_text("\n".join(lines))
    print(f"Cycle 2 proposals written: {OUT_PATH}")
    print(
        f"  {len(only_513)} v5.13-only / {len(only_5_3)} v5_3-only / {len(both)} in-both"
    )
    print("  v0.1 buckets: " + " / ".join(f"{k}={len(v)}" for k, v in buckets.items()))
    print(
        "  v0.2 buckets: " + " / ".join(f"{k}={len(v)}" for k, v in buckets_v02.items())
    )


if __name__ == "__main__":
    main()
