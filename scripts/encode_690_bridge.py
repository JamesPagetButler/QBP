#!/usr/bin/env python3
"""Issue #690 / PR #691 — mint the Substrate bridge anchor; point anchor 4 at it (option (b)).

`proofs/QBP/Substrate/RuleFlowBridge.lean` (Substrate layer) states and proves the identification
that PR #689 could only cite textually:

    QBP.Foundations.InFlightAlgebra.gradVof s = QBP.Substrate.RuleFlow.gradV s

with its two CD halves and the two memberships it transports (`RuleFlow.gradV s ∈ 𝕆_s`,
`α • s + β • RuleFlow.gradV s ∈ 𝕆_s`).  Five theorems, kernel-checked, `#print axioms` ⊆
{propext, Classical.choice, Quot.sound}, 0 sorry, no native_decide.

Under the federation's import-direction edge rule (Foundations → Substrate is never a derivation
edge; live-test seq 2120–2125, qbp-architecture + cth concur — option (b)) the Foundations anchor
`PROOF-gradient-lies-in-host-kernel-algebra` (proof_file Foundations/InFlightAlgebra.lean) may
neither carry a chain edge to the Substrate anchor `PROOF-rule-gradient-and-tangent-field` nor
claim the Substrate fact in its name.  So this encoder does exactly two things:

  1. MINTS `PROOF-rule-gradient-lies-in-host-kernel-algebra` (Substrate): proof_file
     Substrate/RuleFlowBridge.lean, headline `gradV_mem_kernelAlgebra`, the other four bridge
     theorems + the Foundations `gradVof_mem_kernelAlgebra` as companions, chain
     [PROOF-gradient-lies-in-host-kernel-algebra (S→F), PROOF-rule-gradient-and-tangent-field (S→S)].
  2. REVISES anchor 4 `PROOF-gradient-lies-in-host-kernel-algebra` in `name` and `description`
     ONLY: every "NOT stated in Lean (#683)" / "bridge lemma owed, #683" / "withheld until the
     #683 bridge lemma lands" clause becomes a pointer to the Substrate anchor.  `prediction_chain`
     stays [PROOF-alternator-vanishes-iff-commute]; `lean_theorem`, `proof_file`,
     `lean_companion_theorems` and `verification` are byte-identical to master (25ac715).

Plus `version` 6.12.0 → 6.13.0, `last_updated`, one `changelog` entry, and one manifest entry
(`docs/cth/anchor-worthy-manifest.json`) for the new anchor.  Idempotent-guarded: refuses to run
if the new anchor already exists or anchor 4 no longer carries the master-text clauses.

Usage: python3 scripts/encode_690_bridge.py [--dry-run]
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
LAKE = ROOT / "proofs/lake-manifest.json"
TOOLCHAIN = (ROOT / "proofs/lean-toolchain").read_text().strip()

DATE = "2026-09-30T00:00:00Z"
VERSION = "6.13.0"
BATCH = "#690-gradV-bridge"

ANCHOR4 = "PROOF-gradient-lies-in-host-kernel-algebra"
NEW_ID = "PROOF-rule-gradient-lies-in-host-kernel-algebra"
CHAIN_FOUNDATIONS_TARGET = ANCHOR4  # S → F
CHAIN_SUBSTRATE_TARGET = "PROOF-rule-gradient-and-tangent-field"  # S → S

IF = "QBP.Foundations.InFlightAlgebra."
BR = "QBP.Substrate.RuleFlowBridge."
F_IF = "proofs/QBP/Foundations/InFlightAlgebra.lean"
F_BR = "proofs/QBP/Substrate/RuleFlowBridge.lean"

MAIN = BR + "gradV_mem_kernelAlgebra"
BRIDGE_COMPANIONS = [
    BR + "gradVlo_eq_cdLo_gradV",
    BR + "gradVhi_eq_cdHi_gradV",
    BR + "gradVof_eq_gradV",
    BR + "smul_self_add_smul_gradV_mem_kernelAlgebra",
]
SUBSTRATE_WITNESSES = [
    MAIN
] + BRIDGE_COMPANIONS  # the five theorems of RuleFlowBridge.lean
COMPANIONS = BRIDGE_COMPANIONS + [IF + "gradVof_mem_kernelAlgebra"]

# ---------------------------------------------------------------------------------------
# Anchor 4: pointer-only edits.  Each (old, new) pair must match EXACTLY ONCE in the master
# text; anything else means the record is not the 25ac715 record and the encode refuses.
# ---------------------------------------------------------------------------------------
POINTER = (
    "the identity gradVof = RuleFlow.gradV and RuleFlow.gradV(s) ∈ 𝕆_s are PROVED in Substrate at "
    f"{NEW_ID} ({F_BR}); this Foundations anchor claims only the gradVof form"
)

NAME_EDITS = [
    (
        "The identity gradVof = RuleFlow.gradV is NOT stated in Lean (#683)",
        POINTER[0].upper() + POINTER[1:],
    ),
]

DESC_EDITS = [
    (
        "(matched to RuleFlow's gradient by citation only — see the NOT-claimed clause)",
        "(identified with RuleFlow's gradient in Substrate — see the NOT-claimed pointer)",
    ),
    (
        "the identity `gradVof s = gradV s` is NOT stated in Lean (bridge lemma owed, #683).",
        POINTER + " (#690).",
    ),
    (
        "prediction_chain: PROOF-alternator-vanishes-iff-commute only — the chain to "
        "PROOF-rule-gradient-and-tangent-field is deliberately withheld until the #683 bridge lemma "
        "lands in Substrate (InFlightAlgebra.lean imports only Foundations; §I4 R2).",
        "prediction_chain: PROOF-alternator-vanishes-iff-commute only — the edge to "
        f"PROOF-rule-gradient-and-tangent-field (a Substrate anchor) is carried by {NEW_ID}, not "
        "here: Foundations → Substrate is never a derivation edge (import-direction edge rule; "
        "InFlightAlgebra.lean imports only Foundations; §I4 R2).",
    ),
    (
        "NOT claimed: that `gradVof` = `RuleFlow.gradV` in Lean (matched by citation only);",
        "NOT claimed here: that `gradVof` = `RuleFlow.gradV` and RuleFlow.gradV(s) ∈ 𝕆_s — PROVED "
        f"in Substrate at {NEW_ID} ({F_BR}), pointed to, not claimed by this Foundations anchor;",
    ),
]

# ---------------------------------------------------------------------------------------
# The new Substrate anchor
# ---------------------------------------------------------------------------------------
NOT_ANCHORED = (
    " Definition D of #688 (the foliation of InFlight by the leaves S⁶(𝕆_s) ∩ InFlight, leaf invariance "
    "under deterministic G₂-equivariant rules, the leaf space {ℍ ⊂ 𝕆} = G₂/SO(4)) is ARGUMENT / NUMERICAL "
    "and is NOT anchored; this anchor supports only the PROVED clause named above."
)

NEW_NAME = (
    "For EVERY sedenion s the rule's gradient RuleFlow.gradV(s) equals the Foundations closed form "
    "gradVof(s) (componentwise: gradVlo s = cdLo (gradV s), gradVhi s = cdHi (gradV s)) and therefore "
    "lies in the host kernel algebra 𝕆_s = H_s ⊕ H_s·ℓ, H_s = span{1, a, Im b, a·Im b}; likewise "
    "α·s + β·gradV(s) ∈ 𝕆_s. Pointwise in s; nothing about the flow."
)

NEW_DESC = (
    f"{F_BR} (Substrate layer, namespace QBP.Substrate.RuleFlowBridge; imports QBP.Substrate.RuleFlow "
    "and QBP.Foundations.InFlightAlgebra — the allowed direction, since Foundations may not import "
    "Substrate and the identity therefore has to live here). Five theorems, each for every "
    "s : CDAlg ℝ 4 with no hypothesis on s: `gradVlo_eq_cdLo_gradV` — "
    "QBP.Foundations.InFlightAlgebra.gradVlo s = cdLo (RuleFlow.gradV s); `gradVhi_eq_cdHi_gradV` — "
    "QBP.Foundations.InFlightAlgebra.gradVhi s = cdHi (RuleFlow.gradV s) (the two CD halves the "
    "InFlightAlgebra header, l.546–548, had asserted textually only); `gradVof_eq_gradV` — "
    "QBP.Foundations.InFlightAlgebra.gradVof s = RuleFlow.gradV s (the packaged sedenion-level "
    "identity: the Foundations closed form IS the rule's gradient); `gradV_mem_kernelAlgebra` (the main "
    "theorem) — InFlightAlgebra.InKernelAlgebra s (RuleFlow.gradV s), i.e. both CD components of the "
    "RULE's gradient lie in H_s = span{1, a, Im b, a·Im b} ⊂ 𝕆 (InKernelAlgebra s x := InQuatSpanOct "
    "(cdLo s) (imHi s) (cdLo x) ∧ InQuatSpanOct (cdLo s) (imHi s) (cdHi x)), so RuleFlow.gradV s ∈ "
    "𝕆_s = H_s ⊕ H_s·ℓ; `smul_self_add_smul_gradV_mem_kernelAlgebra` — for all α β : ℝ, "
    "InFlightAlgebra.InKernelAlgebra s (α • s + β • RuleFlow.gradV s). Proof shape: the two component "
    "identities are `rw` chains through RuleFlow.cdLo_gradV / cdHi_gradV, InFlightAlgebra.gradVlo_def / "
    "gradVhi_def / cdComm_def and RuleFlow.comm (both sides are 2 • (C·b̄ − b̄·C), resp. 2 • (ā·C − C·ā), "
    "C = [a, b]); `gradVof_eq_gradV` unfolds gradVof and rewrites with them; the two memberships are "
    "`rw [← gradVof_eq_gradV]` followed by the Foundations theorems "
    "QBP.Foundations.InFlightAlgebra.gradVof_mem_kernelAlgebra (companion here; the algebraic core, "
    "anchored at PROOF-gradient-lies-in-host-kernel-algebra) and "
    "QBP.Foundations.InFlightAlgebra.smul_self_add_smul_gradV_mem_kernelAlgebra. `#print axioms` on all "
    "five ⊆ {propext, Classical.choice, Quot.sound}; 0 sorry, 0 native_decide, 0 vacuous `True`. "
    "prediction_chain: PROOF-gradient-lies-in-host-kernel-algebra (the Foundations membership this "
    "module transports — a Substrate → Foundations edge, the allowed direction) and "
    "PROOF-rule-gradient-and-tangent-field (RuleFlow.gradV, the closed form cdLo_gradV / cdHi_gradV — "
    "Substrate → Substrate); this Substrate anchor, not the Foundations one, carries the edge to "
    "RuleFlow (import-direction edge rule, live-test seq 2120–2125). NOT claimed: the rule FIELD "
    "F(s) = −(∇V(s) − ⟪∇V(s), s⟫·s − (∇V(s))₀·1) (`RuleFlow.ruleField`) ∈ 𝕆_s — no theorem states "
    "InKernelAlgebra s (ruleField s); it would follow from the proved closure of 𝕆_s under + and • with "
    "s ∈ 𝕆_s and a true but UNSTATED 1 ∈ 𝕆_s, so the F-level containment remains ARGUMENT, one unstated "
    "lemma away; flow existence / uniqueness and leaf invariance — that 𝕆_s is constant along a "
    "trajectory (ARGUMENT, conditional on existence of integral curves — FLAG-rule-flow-open, #635; every "
    "theorem here is pointwise in s and says nothing about a trajectory); 𝕆_s = ker Δ(s) (rank 8 "
    "NUMERICAL, reverse inclusion OPEN); the leaf space G₂/SO(4) (ARGUMENT); anything about the anneal "
    "(#635) or the endpoint / ω-limit." + NOT_ANCHORED
)

VERIFIER = (
    "run-bounded 6G 1800 taskset -c 3-5 lake build QBP.Substrate.RuleFlowBridge — exit 0, 3129 jobs; "
    "5/5 `#print axioms` audits standard-only (gradVlo_eq_cdLo_gradV, gradVhi_eq_cdHi_gradV, "
    "gradVof_eq_gradV, gradV_mem_kernelAlgebra, smul_self_add_smul_gradV_mem_kernelAlgebra, all ⊆ "
    "{propext, Classical.choice, Quot.sound}); statements re-read fully qualified (`#check` with full "
    "names) to confirm the right-hand sides are QBP.Substrate.RuleFlow.gradV and not a local copy; 0 "
    "sorry, 0 native_decide, 0 vacuous `True`; gates 0 — check_lean_foundations.py exit 0, "
    "check_layer_imports.py exit 0 (Substrate file importing Foundations — the allowed direction — "
    "registered in the QBP/Substrate.lean aggregator) (lean-prover, 2026-09-30, isolated worktree "
    "probe-690-bridge; PR #691 Red Team APPROVE at b616357, issuecomment-5918526831, N1–N5, no M; "
    "restructured to option (b) per the import-direction edge rule, live-test seq 2120–2125, "
    "qbp-architecture + cth concur)"
)


def _libs():
    m = json.loads(LAKE.read_text())
    return {
        p["name"]: {"ref": p.get("inputRev") or p["rev"], "sha": p["rev"]}
        for p in m["packages"]
        if p["name"] in ("mathlib", "batteries")
    }


def new_anchor():
    # Same field set and order as anchor 4 (encode_688_inflight_anchors.anchor()).
    # layer_tag "T" as on every Substrate-file PROOF anchor of the ledger (#635/#639/#649/#679/#681):
    # the ledger's "substrate" layer_tag value marks the 509-C condensed-math intake batch, not the
    # Lean layer, which is recorded by proof_file and the namespace of lean_theorem.
    return {
        "id": NEW_ID,
        "name": NEW_NAME,
        "tier": 1,
        "layer_tag": "T",
        "status": "coherent",
        "provenance_kind": "proof",
        "description": NEW_DESC,
        "proof_file": F_BR,
        "proof_language": "lean4",
        "proof_state": "verified",
        "lean_theorem": MAIN,
        "lean_companion_theorems": COMPANIONS,
        "sorry_count": 0,
        "provenance": "T",
        "prediction_chain": [CHAIN_FOUNDATIONS_TARGET, CHAIN_SUBSTRATE_TARGET],
        "foundation_batch": BATCH,
        "last_tested_at": DATE,
        "verification": {
            "toolchain": TOOLCHAIN,
            "libraries": _libs(),
            "verified_at": DATE,
            "verifier": VERIFIER,
            "result": "verified",
            "axiom_closure": ["propext", "Classical.choice", "Quot.sound"],
            "witnesses": SUBSTRATE_WITNESSES,
        },
    }


CHANGELOG = {
    "version": VERSION,
    "date": DATE,
    "note": (
        f"#690 / PR #691: {NEW_ID} minted (Substrate); anchor 4 NOT-claimed pointer updated; no other "
        "anchor changed. Detail — lean-prover / qbp-oppenheimer, option (b) of the import-direction edge "
        "rule (Foundations → Substrate is never a derivation edge; live-test seq 2120–2125, "
        "qbp-architecture + cth concur). MINTED: the bridge anchor for "
        f"{F_BR} (5 theorems, kernel-checked, axioms ⊆ {{propext, Classical.choice, Quot.sound}}, 0 "
        "sorry, no native_decide): `gradVof_eq_gradV` (QBP.Foundations.InFlightAlgebra.gradVof s = "
        "QBP.Substrate.RuleFlow.gradV s), its two CD halves `gradVlo_eq_cdLo_gradV` / "
        "`gradVhi_eq_cdHi_gradV`, and the transported memberships `gradV_mem_kernelAlgebra` "
        "(InKernelAlgebra s (RuleFlow.gradV s), the headline) and "
        "`smul_self_add_smul_gradV_mem_kernelAlgebra`; chain [PROOF-gradient-lies-in-host-kernel-algebra "
        "(Substrate → Foundations), PROOF-rule-gradient-and-tangent-field (Substrate → Substrate)]; "
        "manifest entry added. REVISED: PROOF-gradient-lies-in-host-kernel-algebra (anchor 4 of PR #689) "
        "in `name` and `description` only — its 'NOT stated in Lean (#683)' / 'bridge lemma owed' / "
        "'withheld until the #683 bridge lemma lands' clauses become a pointer to the Substrate anchor; "
        "its prediction_chain stays [PROOF-alternator-vanishes-iff-commute] (the Foundations anchor "
        "does NOT regain the RuleFlow edge), and lean_theorem, proof_file, lean_companion_theorems and "
        "verification are byte-identical to 6.12.0. STILL NOT claimed by either anchor: the rule FIELD "
        "F(s) ∈ 𝕆_s (needs an unstated 1 ∈ 𝕆_s; ARGUMENT), flow existence / uniqueness and leaf "
        "invariance (FLAG-rule-flow-open, #635), 𝕆_s = ker Δ(s) (reverse inclusion OPEN), the leaf space "
        "G₂/SO(4), the anneal, the endpoint. Anchors 1–3 of PR #689 untouched; no root, principle, "
        "decision or kill touched; FLAG-rule-flow-open and CONJ-condensed-math-for-transition-state not "
        "touched. (Version 6.13.0: encoded on master 6.12.0/343 → 344.)"
    ),
}


def _apply_edits(text, edits, label):
    for old, new in edits:
        n = text.count(old)
        if n != 1:
            raise SystemExit(
                f"{label}: expected exactly one occurrence of the master clause, found {n}: {old[:80]!r}"
            )
        text = text.replace(old, new)
    return text


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if not (ROOT / F_BR).exists():
        raise SystemExit(f"bridge module missing on this head: {F_BR}")
    src = (ROOT / F_BR).read_text(encoding="utf-8")
    for t in SUBSTRATE_WITNESSES:
        if f"theorem {t.rsplit('.', 1)[1]}" not in src:
            raise SystemExit(f"witness does not resolve in {F_BR}: {t}")
    if "theorem gradVof_mem_kernelAlgebra" not in (ROOT / F_IF).read_text(
        encoding="utf-8"
    ):
        raise SystemExit(
            f"companion does not resolve in {F_IF}: gradVof_mem_kernelAlgebra"
        )

    rec = new_anchor()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        if NEW_ID in have:
            raise SystemExit(f"already applied: {NEW_ID} present")
        for cid in (CHAIN_FOUNDATIONS_TARGET, CHAIN_SUBSTRATE_TARGET):
            if cid not in have:
                raise SystemExit(f"prediction_chain target missing from ledger: {cid}")
        a4 = ed.record("anchors", ANCHOR4)
        if a4["prediction_chain"] != ["PROOF-alternator-vanishes-iff-commute"]:
            raise SystemExit(
                "anchor 4 is not the master record: unexpected prediction_chain"
            )
        a4["name"] = _apply_edits(a4["name"], NAME_EDITS, "anchor 4 name")
        a4["description"] = _apply_edits(
            a4["description"], DESC_EDITS, "anchor 4 description"
        )
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
                "witnesses": SUBSTRATE_WITNESSES,
            }
        )
    if not args.dry_run:
        MANIFEST.write_text(json.dumps(m, ensure_ascii=False, indent=2) + "\n")

    print(
        f"  minted  {NEW_ID}  main={MAIN.removeprefix(BR)}  witnesses={len(SUBSTRATE_WITNESSES)}  "
        f"chain={rec['prediction_chain']}"
    )
    print(
        f"  revised {ANCHOR4}: name ({len(NAME_EDITS)} clause), description ({len(DESC_EDITS)} clauses); "
        "chain unchanged"
    )
    print(
        f"{'DRY ' if args.dry_run else ''}applied: 1 minted + 1 revised; ledger {VERSION}; "
        f"manifest entries {len(m['entries'])}"
    )


if __name__ == "__main__":
    main()
