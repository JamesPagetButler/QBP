#!/usr/bin/env python3
"""
CTH v5_24 Intake — Batch-C Per-Anchor Proposals (three-way diff)

Per QBP #509 Batch C (`pr407-conflict-resolution` seq=93-95) and Oppenheimer's
Batch-C flag (seq=94): condensed-mathematics anchors are judged against the
ratified layer architecture (docs/foundations/layer-architecture.md — SUBSTRATE
layer, napkin-level); v5_24 `PROOF-*` labels face the anchor-rule termination
test (web-stream "PROOF" IDs don't inherit kernel credibility).

Three-way comparison (the v5.13 cycle-2 two-way design would misreport
migration noise as theory divergence here, because canonical is v0.3 and
v5_24 is v0.2):

    base   = archive/cth-inventory/confluent-trust-inventory-v5_3.json   (common ancestor, v0.2-lineage)
    ours   = archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json (canonical, post-migration)
    theirs = archive/cth-inventory/baselines/confluent-trust-inventory-v5_24.json (QBP-web fork)

For each in-all-three anchor, a field is reported ONLY if theirs != base
(QBP-web actually changed it since the fork). Whether ours also changed it
(true three-way conflict) vs. ours kept base (clean theirs-side update) is
classified per row. Fields that differ only ours-vs-theirs but match
base-vs-theirs are migration translation — suppressed.

Output: paper/CTH-V5_24-Intake-Batch-C-Proposals.md

Authors: qbp-implementor (Integration role)
Date:    2026-06-04
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
BASE_PATH = REPO_ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.json"
OURS_PATH = REPO_ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
THEIRS_PATH = (
    REPO_ROOT / "archive/cth-inventory/baselines/confluent-trust-inventory-v5_24.json"
)
OUT_PATH = REPO_ROOT / "paper/CTH-V5_24-Intake-Batch-C-Proposals.md"

# Rubric v0.2 axes (PR #423 §2, cth-implementor co-signed #509 ruling §1)
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
    "regime_of_validity",
    "qbp_threshold_R",
    "null_threshold_R",
}
# v0.2→v0.3 migration produces these mechanically; ours-vs-theirs diffs on them
# are translation noise unless theirs-vs-base also differs.
MIGRATION_FIELDS = {
    "provenance_kind",
    "independent",
    "proof_language",
    "proof_state",
    "theory_citation",
    "schema_version",
}

# Oppenheimer seq=94 Batch-C lenses
CONDENSED_MATH_IDS_HINT = ("condensed", "clausen", "fargues", "scholze", "prismatic")


def load(p: Path) -> dict[str, dict]:
    inv = json.loads(p.read_text())
    return {a["id"]: a for a in inv["anchors"]}


def render(v: Any, n: int = 240) -> str:
    if v == "<MISSING>":
        return "_(absent)_"
    s = repr(v) if isinstance(v, str) else json.dumps(v, default=str)
    return s if len(s) <= n else s[:n] + "…"


def intake_lens(aid: str, a: dict) -> str:
    """Per-anchor intake lens per Oppenheimer's seq=94 Batch-C flag."""
    blob = (aid + " " + str(a.get("name", "")) + " " + str(a.get("notes", ""))).lower()
    if aid.startswith("REF-") or any(h in blob for h in CONDENSED_MATH_IDS_HINT):
        return (
            "**SUBSTRATE-layer candidate** — judge against layer-architecture §SUBSTRATE "
            "(napkin-level; no Lean until first real theorem; imports-Foundations-never-the-reverse). "
            "Likely include-as-NASCENT with substrate-layer tag"
        )
    if aid.startswith("PROOF-"):
        return (
            "**Anchor-rule termination test REQUIRED** — web-stream PROOF label does not "
            "inherit kernel credibility; prediction_chain must terminate at one of the 5 "
            "anchor types (docs/workflows/review_anchoring.md) or the ID gets relabelled"
        )
    if aid.startswith("WISDOM-"):
        return "DEFER to wisdom-registry migration (Beekeeper D2)"
    return "Standard ruling: include / include-as-killed / drop-superseded"


def main() -> None:
    base = load(BASE_PATH)
    ours = load(OURS_PATH)
    theirs = load(THEIRS_PATH)

    theirs_only = sorted(set(theirs) - set(base) - set(ours))
    ours_only = sorted(set(ours) - set(theirs))
    in_three = sorted(set(base) & set(ours) & set(theirs))

    # Three-way field analysis on in-all-three anchors
    clean_updates: dict[str, dict] = {}  # theirs changed, ours kept base
    true_conflicts: dict[str, dict] = {}  # both sides changed since base
    for aid in in_three:
        b, o, t = base[aid], ours[aid], theirs[aid]
        fields = set(b) | set(o) | set(t)
        cu, tc = {}, {}
        for f in fields:
            if f in MIGRATION_FIELDS:
                continue
            bv = b.get(f, "<MISSING>")
            ov = o.get(f, "<MISSING>")
            tv = t.get(f, "<MISSING>")
            if tv == bv:
                continue  # theirs didn't change it — nothing to intake
            if ov == bv:
                cu[f] = (bv, tv)  # clean theirs-side update
            elif ov == tv:
                continue  # both converged to same value — no action
            else:
                tc[f] = (bv, ov, tv)  # true three-way conflict
        if cu:
            clean_updates[aid] = cu
        if tc:
            true_conflicts[aid] = tc

    L: list[str] = []
    L.append("# CTH v5_24 Intake — Batch-C Per-Anchor Proposals")
    L.append("")
    L.append(
        "**Generated:** `scripts/cth_v524_intake_diff.py` (qbp-implementor, 2026-06-04)  "
    )
    L.append(
        "**Method:** three-way diff — base = v5_3 (common ancestor), ours = canonical "
        "v5_3.v0.3, theirs = v5_24 (QBP-web fork, received 2026-05-31). A field is "
        "reported only when theirs ≠ base; migration-translation fields suppressed.  "
    )
    L.append(
        "**Adjudicator:** @qbp-oppenheimer (scientific) per #509 Batch C; "
        "schema-side per @cth-implementor #509 ruling R1–R3 (incl. mechanical "
        "`lean_theorem`-name `proof_file` resolution; stale pointers get "
        '`lean_migration_status: "stale-pointer"` + `review_flag`).  '
    )
    L.append(
        "**Intake lenses (Oppenheimer seq=94):** condensed-math/REF-* → SUBSTRATE-layer "
        "candidates (include-as-NASCENT likely); v5_24 PROOF-* → anchor-rule termination "
        "test; truth-in-labelling extends to anchor IDs."
    )
    L.append("")
    L.append("---")
    L.append("")
    L.append("## 1. Summary")
    L.append("")
    L.append("| Bucket | Count | Action |")
    L.append("|---|---|---|")
    L.append(
        f"| v5_24-only anchors (§2) | {len(theirs_only)} | per-anchor intake ruling |"
    )
    L.append(
        f"| In-all-three, clean theirs-side updates (§3) | {len(clean_updates)} | "
        "adopt-or-reject per anchor (ours kept ancestor value) |"
    )
    L.append(
        f"| In-all-three, TRUE three-way conflicts (§4) | {len(true_conflicts)} | "
        "both sides changed since fork — full adjudication |"
    )
    L.append(
        f"| Canonical-only anchors (informational, §5) | {len(ours_only)} | none — "
        "already canonical; v5_24 forked before they landed |"
    )
    L.append("")
    L.append(
        "All ruled-in content passes through v0.2→v0.3 schema translation "
        "(`cth migrate`) and validates against schema semver 0.3.1 "
        "(confluent-trust PR #97) before landing in the canonical ledger."
    )
    L.append("")
    L.append("---")
    L.append("")

    # §2 v5_24-only
    L.append(f"## 2. v5_24-only anchors ({len(theirs_only)}) — intake rulings needed")
    L.append("")
    for aid in theirs_only:
        a = theirs[aid]
        L.append(f"### `{aid}`")
        L.append("")
        L.append(f"- **Name:** {a.get('name', '<unnamed>')}")
        L.append(
            f"- **Tier:** {a.get('tier', '?')} | **Status:** {a.get('status', '?')} "
            f"| **Provenance:** {a.get('provenance', '?')}"
        )
        L.append(f"- **Intake lens:** {intake_lens(aid, a)}")
        if a.get("description"):
            L.append(f"- **Description:** {render(a['description'], 500)}")
        if a.get("notes"):
            L.append(f"- **Notes:** {render(a['notes'], 700)}")
        for f in (
            "predicted_value",
            "predicted_unit",
            "measured_value",
            "measured_error",
            "discrepancy_pct",
            "prediction_chain",
            "proof_file",
            "lean_theorem",
            "converges_with",
        ):
            if a.get(f) is not None and f in a:
                L.append(f"- **{f}:** {render(a[f])}")
        L.append(
            "- **Ruling:** ☐ include ☐ include-as-NASCENT ☐ include-as-killed ☐ drop-superseded ☐ relabel"
        )
        L.append("")

    L.append("---")
    L.append("")

    # §3 clean updates
    L.append(
        f"## 3. Clean theirs-side updates ({len(clean_updates)} anchors) — "
        "QBP-web changed, canonical kept ancestor value"
    )
    L.append("")
    L.append(
        "Default proposal: **adopt** unless superseded by canonical-side rulings "
        "the fork predates (entropy-cone DEAD #484, a₀ evolution, 2026-06-03/04 "
        "crystallisation-debate kills). Theory-axis fields → @qbp-oppenheimer; "
        "pure schema/metadata rows → R1 adopt."
    )
    L.append("")
    for aid, cu in clean_updates.items():
        theory_hit = set(cu) & THEORY_AXIS_FIELDS
        marker = " ⚠️ theory-axis" if theory_hit else " (schema/meta only)"
        L.append(f"### `{aid}`{marker}")
        L.append("")
        L.append("| Field | base (v5_3) | theirs (v5_24) |")
        L.append("|---|---|---|")
        for f in sorted(cu):
            bv, tv = cu[f]
            ax = "**theory**" if f in THEORY_AXIS_FIELDS else "schema"
            L.append(f"| `{f}` ({ax}) | {render(bv)} | {render(tv)} |")
        L.append("")

    L.append("---")
    L.append("")

    # §4 true conflicts
    L.append(
        f"## 4. TRUE three-way conflicts ({len(true_conflicts)} anchors) — "
        "both streams changed since the fork"
    )
    L.append("")
    for aid, tc in true_conflicts.items():
        L.append(f"### `{aid}`")
        L.append("")
        L.append("| Field | base (v5_3) | ours (canonical) | theirs (v5_24) |")
        L.append("|---|---|---|---|")
        for f in sorted(tc):
            bv, ov, tv = tc[f]
            L.append(
                f"| `{f}` | {render(bv, 160)} | {render(ov, 160)} | {render(tv, 160)} |"
            )
        L.append("")

    L.append("---")
    L.append("")
    L.append(f"## 5. Canonical-only anchors ({len(ours_only)}) — informational")
    L.append("")
    L.append("No action: these postdate the fork and are already canonical.")
    L.append("")
    L.append("| Anchor ID | Source |")
    L.append("|---|---|")
    for aid in ours_only:
        L.append(
            f"| `{aid}` | canonical-side append (foundations / kill dispositions) |"
        )
    L.append("")
    L.append("---")
    L.append("")
    L.append("## 6. Provenance")
    L.append("")
    L.append(f"- base: `{BASE_PATH.relative_to(REPO_ROOT)}` ({len(base)} anchors)")
    L.append(f"- ours: `{OURS_PATH.relative_to(REPO_ROOT)}` ({len(ours)} anchors)")
    L.append(
        f"- theirs: `{THEIRS_PATH.relative_to(REPO_ROOT)}` ({len(theirs)} anchors)"
    )
    L.append(
        "- rubric: `docs/workflows/pr7_conflict_routing_rubric.md` v0.2 + #509 R1–R3"
    )
    L.append(
        "- intake lenses: `pr407-conflict-resolution` seq=94 (Oppenheimer Batch-C flag)"
    )
    L.append("")

    OUT_PATH.write_text("\n".join(L))
    print(f"Batch-C proposals written: {OUT_PATH}")
    print(
        f"  v5_24-only={len(theirs_only)} clean-updates={len(clean_updates)} "
        f"true-conflicts={len(true_conflicts)} canonical-only={len(ours_only)}"
    )


if __name__ == "__main__":
    main()
