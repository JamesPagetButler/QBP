#!/usr/bin/env python3
"""Issue #697 / inter#197 step 1 / PR #729 — mint the leaf-foliation Substrate PROOF anchor.

`proofs/QBP/Substrate/RuleFlowLeafFoliation.lean` (Substrate layer, #729) proves the eight
headline theorems underwriting the QBP-CU leaf-foliated engine. This encoder mints the single
CTH anchor that cites the module, so the inverse-anchor audit (red-by-design while the 18 new
theorems are un-anchored) goes green once `--update-baseline` runs in the same commit.

Anchor spec from qbp-oppenheimer's theory-axis comment on #729 (co-signer); prefix per
`docs/conventions/anchor-prefix-policy.md` R2 (loose reading). `derived_from` resolved to the
#690 anchor `PROOF-rule-gradient-lies-in-host-kernel-algebra` (RuleFlowBridge.lean): the file
imports RuleFlowBridge and Theorem 1 closes the gap from #690's `∇V(s) ∈ 𝕆_s` to the full rule
field — i.e. oppenheimer's "or its successor". Flagged for his theory-axis co-sign.

Mint-only (no existing anchor revised). Idempotent-guarded, confined write, version bump,
changelog, manifest entry. Then `scripts/anchor_inverse_audit.py --update-baseline` (separate,
same commit) records the new anchor↔theorem mapping.

Usage: python3 scripts/encode_697_leaf_foliation_anchor.py [--dry-run]
"""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
MANIFEST = ROOT / "docs/cth/anchor-worthy-manifest.json"
TOOLCHAIN = (ROOT / "proofs/lean-toolchain").read_text().strip()

DATE = "2026-10-22T00:00:00Z"
VERSION = "6.19.0"
BATCH = "#697-leaf-foliation"

NEW_ID = "PROOF-rule-field-in-kernel-algebra-leaf-foliation"
DERIVED_FROM = (
    "PROOF-rule-gradient-lies-in-host-kernel-algebra"  # the #690 anchor (∇V(s) ∈ 𝕆_s)
)

NS = "QBP.Substrate.RuleFlowLeafFoliation."
PROOF_FILE = "proofs/QBP/Substrate/RuleFlowLeafFoliation.lean"

# The eight headline theorems (oppenheimer's spec; helpers stay out, same rule as #727).
HEADLINE = "ruleField_mem_kernelAlgebra"  # Theorem 1
COMPANION_BARE = [
    "gradV_mem_fixed_leaf",  # Theorem 2
    "ruleField_mem_fixed_leaf",
    "rk4Stage_mem_fixed_leaf",
    "octonion_double_comm_pure",  # Theorem 3
    "cdLo_gradV_eq_plane_comb",
    "cdHi_gradV_eq_plane_comb",
    "liftLeaf_gradV_eq",  # Theorem 4
]
ALL_BARE = [HEADLINE] + COMPANION_BARE
WITNESSES = [NS + t for t in ALL_BARE]

# Current uniform foundations pin (matches every 6.18.0 proof anchor; #729 built against it).
LIBS = {
    "mathlib": {
        "ref": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "sha": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
    },
    "batteries": {
        "ref": "main",
        "sha": "32dc18cde3684679f3c003de608743b57498c56f",
    },
}

NEW_NAME = (
    "For every sedenion s the rule field RuleFlow.ruleField(s) lies in the host kernel algebra "
    "𝕆_s (Theorem 1, unconditional, closing the pointwise gap from ∇V(s) ∈ 𝕆_s at #690 via "
    "(∇V s)₀ = 0); for a fixed seed s₀, gradV, ruleField and ONE RK4 stage preserve the fixed "
    "leaf 𝕆_{s₀} by subalgebra closure (Theorem 2); cdLo/cdHi(∇V s) = the 2-plane double-"
    "commutator closed forms in span{gramLo s, gramHi s} (Theorem 3); and the 5D leaf lift "
    "liftLeaf intertwines gradV for an orthonormal imaginary 2-frame (Theorem 4). "
    "ONE-STAGE closure, NOT trajectory invariance — the #688 leaf-invariance row stays open; "
    "liftLeaf_ruleField_eq / liftLeaf_rk4Step_eq, a multi-step iterate and an Euler step are "
    "NOT proved. Pointwise / single-step in s; nothing about the continuous flow."
)

NEW_DESC = (
    f"{PROOF_FILE} (Substrate layer, namespace QBP.Substrate.RuleFlowLeafFoliation; imports "
    "QBP.Substrate.RuleFlowBridge (#690) and QBP.Substrate.RuleFlowInvariants (#635)). The eight "
    "headline theorems, each kernel-checked with #print axioms ⊆ {propext, Classical.choice, "
    "Quot.sound}, 0 sorry, 0 native_decide: "
    "`ruleField_mem_kernelAlgebra` (Theorem 1) — ∀ s : CDAlg ℝ 4, InFlightAlgebra.InKernelAlgebra "
    "s (RuleFlow.ruleField s), no hypothesis; closes the gap from #690's ∇V(s) ∈ 𝕆_s to the full "
    "tangent rule field using (∇V s)₀ = 0 (RuleFlowInvariants.gradV_coord_zero). "
    "`gradV_mem_fixed_leaf`, `ruleField_mem_fixed_leaf`, `rk4Stage_mem_fixed_leaf` (Theorem 2) — "
    "for a FIXED seed s₀, x ∈ 𝕆_{s₀} ⇒ gradV x, ruleField x and one explicit RK4 stage stay in "
    "𝕆_{s₀}, by closed-subalgebra closure (inQuatSpanOct_mul / _conj), no ODE/Grassmannian "
    "machinery. `octonion_double_comm_pure`, `cdLo_gradV_eq_plane_comb`, `cdHi_gradV_eq_plane_comb` "
    "(Theorem 3) — the 2-plane double-commutator identity, structural (cdAlg_sq_eq, "
    "cdAlg_mul_add_swap_pure, octonion_alternative, octonion_flexible; zero decide/native_decide): "
    "for a = gramLo s, c = gramHi s, cdLo(∇V s) = (8·N c)•a − (8·bil a c)•c and cdHi(∇V s) = "
    "(8·N a)•c − (8·bil a c)•a, so ∇V(s) stays in span_ℝ{a, c}. `liftLeaf_gradV_eq` (Theorem 4) — "
    "the CASH P4 intertwining: for an orthonormal imaginary octonion 2-frame (u₁, u₂) "
    "(N u₁ = N u₂ = 1, bil u₁ u₂ = 0) the 5D leaf lift liftLeaf u₁ u₂ q intertwines gradV. "
    "SCOPE (record-level, oppenheimer theory-axis): ONE-stage closure, NOT trajectory invariance "
    "— the #688 leaf-invariance row stays ARGUMENT; the header names inKernelAlgebra_fixed_leaf / "
    "rk4Step_mem_fixed_leaf / liftLeaf_ruleField_eq / liftLeaf_rk4Step_eq and an 'Euler step by "
    "induction' have NO Lean statement in the module (only one RK4 stage and liftLeaf for gradV). "
    "derived_from: PROOF-rule-gradient-lies-in-host-kernel-algebra (#690, the ∇V(s) ∈ 𝕆_s result "
    "Theorem 1 builds on; Substrate → Substrate). NOT claimed: the rule itself (POSTULATE #635); "
    "existence/uniqueness of integral curves (FLAG-rule-flow-open); invariance of 𝕆_s along a "
    "CONTINUOUS trajectory (the closure results are about explicit discrete updates, not the flow); "
    "the reverse inclusion ker Δ(s) ⊆ 𝕆_s; the leaf space G₂/SO(4); the anneal or the endpoint. "
    "PA (pa_local/pa_effective) computed by the encoder, never typed: 0/0, ungraded — no Notary "
    "proof-assistant evidence recorded for this anchor yet (QBP#710 'ungraded' state), as for the "
    "rest of the verified-but-ungraded corpus."
)

VERIFIER = (
    "PR #729 (inter#197 step 1), head bd652ec against master a4d4383. run-bounded 8G 1200 "
    "/usr/bin/time -v lake env lean QBP/Substrate/RuleFlowLeafFoliation.lean — exit 0, wall 6.06 s, "
    "peak RSS 3.49 GiB; lake build --no-build QBP.Substrate = all 3132 targets up-to-date (oleans "
    "match worktree sources by trace hash). #print axioms on all 18 theorems (file l.410–430) and "
    "the 5 defs ⊆ {propext, Classical.choice, Quot.sound}; grep native_decide/sorry = 0 (3 comment "
    "hits only); check_lean_foundations.py exit 0, check_layer_imports.py clean (Substrate→Substrate "
    "import, registered in QBP/Substrate.lean). PR #729 Red Team APPROVE (Grothendieck + Knuth; "
    "Sabine REQUEST-CHANGES was doc-only, resolved) and qbp-architecture §I4 APPROVE-WITH-CONCERN; "
    "CI lake build green. Anchor minted by qbp-implementor; theory axis co-signed by qbp-oppenheimer."
)


def new_anchor():
    return {
        "id": NEW_ID,
        "name": NEW_NAME,
        "tier": 1,
        "layer_tag": "T",
        "status": "coherent",
        "provenance_kind": "proof",
        "description": NEW_DESC,
        "proof_file": PROOF_FILE,
        "proof_language": "lean4",
        "proof_state": "verified",
        "lean_theorem": NS + HEADLINE,
        "lean_companion_theorems": [NS + t for t in COMPANION_BARE],
        "sorry_count": 0,
        "provenance": "T",
        "prediction_chain": [DERIVED_FROM],
        "foundation_batch": BATCH,
        "last_tested_at": DATE,
        "verification": {
            "toolchain": TOOLCHAIN,
            "libraries": LIBS,
            "verified_at": DATE,
            "verifier": VERIFIER,
            "result": "verified",
            "axiom_closure": ["propext", "Classical.choice", "Quot.sound"],
            "witnesses": WITNESSES,
        },
        "theorems": [{"name": t, "status": "verified"} for t in ALL_BARE],
        "pa_local": 0,
        "pa_effective": 0,
    }


CHANGELOG = {
    "version": VERSION,
    "date": DATE,
    "note": (
        f"#697 / inter#197 step 1 / PR #729: {NEW_ID} minted (Substrate) — the CTH anchor for "
        f"{PROOF_FILE}, citing its eight headline theorems "
        "(ruleField_mem_kernelAlgebra; gradV/ruleField/rk4Stage_mem_fixed_leaf; "
        "octonion_double_comm_pure, cdLo/cdHi_gradV_eq_plane_comb; liftLeaf_gradV_eq), all "
        "kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound}, 0 sorry, 0 native_decide. "
        "derived_from PROOF-rule-gradient-lies-in-host-kernel-algebra (#690: Theorem 1 closes the gap "
        "from ∇V(s) ∈ 𝕆_s to the full rule field). Scope: one-stage closure, NOT trajectory "
        "invariance — the #688 leaf-invariance row stays ARGUMENT; liftLeaf_ruleField_eq / "
        "liftLeaf_rk4Step_eq / multi-step / Euler NOT proved. PA 0/0 (ungraded — no Notary evidence "
        "yet, QBP#710). Manifest entry added; inverse-anchor baseline bumped in the same commit so "
        "the 18 theorems are no longer orphans. Mint-only — no existing anchor, root, principle, "
        "decision or kill touched. (Version 6.19.0: encoded on 6.18.0.)"
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    # Witness resolution guard: every cited theorem must exist in the module on this head.
    if not (ROOT / PROOF_FILE).exists():
        raise SystemExit(f"module missing on this head: {PROOF_FILE}")
    src = (ROOT / PROOF_FILE).read_text(encoding="utf-8")
    for t in ALL_BARE:
        if f"theorem {t}" not in src:
            raise SystemExit(f"witness does not resolve in {PROOF_FILE}: {t}")

    rec = new_anchor()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        if NEW_ID in have:
            raise SystemExit(f"already applied: {NEW_ID} present")
        if DERIVED_FROM not in have:
            raise SystemExit(f"derived_from target missing from ledger: {DERIVED_FROM}")
        ed.append("anchors", rec)
        L["version"] = VERSION
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")

    m = json.loads(MANIFEST.read_text())
    ids = {e["anchor_id"] for e in m["entries"]}
    if NEW_ID not in ids:
        m["entries"].append(
            {
                "anchor_id": NEW_ID,
                "declared_by": BATCH,
                "proof_system": "lean4",
                "witnesses": WITNESSES,
            }
        )
        if not args.dry_run:
            MANIFEST.write_text(json.dumps(m, ensure_ascii=False, indent=2) + "\n")

    print(
        f"{'DRY ' if args.dry_run else ''}minted {NEW_ID}: headline={HEADLINE}, "
        f"{len(WITNESSES)} witnesses, chain={rec['prediction_chain']}; ledger {VERSION}; "
        f"manifest entries {len(m['entries'])}"
    )


if __name__ == "__main__":
    main()
