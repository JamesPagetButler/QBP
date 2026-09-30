#!/usr/bin/env python3
"""Re-scope anchor 4 of PR #689 now that the bridge lemma is PROVED (issue #690).

`proofs/QBP/Substrate/RuleFlowBridge.lean` (new, Substrate layer) states and proves the
identification that PR #689 could only cite textually:

    QBP.Foundations.InFlightAlgebra.gradVof s = QBP.Substrate.RuleFlow.gradV s

together with its two CD halves and the two memberships it transports
(`RuleFlow.gradV s ∈ 𝕆_s`, `α • s + β • RuleFlow.gradV s ∈ 𝕆_s`).  Five theorems, kernel-checked,
`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}, 0 sorry, no native_decide.

This encoder touches ONE record, `PROOF-gradient-lies-in-host-kernel-algebra`:
  (a) `name` — the identity, and hence `RuleFlow.gradV(s) ∈ 𝕆_s`, move from NOT-claimed to CLAIMED;
  (b) `description` — the bridge module, its five theorem names and both `proof_file`s are named;
      the NOT-claimed list keeps flow/leaf invariance (conditional on existence, FLAG-rule-flow-open),
      the rule FIELD F(s) (still unstated in Lean), 𝕆_s = ker Δ(s), the leaf space G₂/SO(4), the anneal
      and the endpoint;
  (c) `lean_companion_theorems` — the five bridge theorems added (headline `lean_theorem` unchanged:
      the anchor's main statement is still the Foundations `gradVof_mem_kernelAlgebra`, and
      `proof_file` therefore stays the Foundations file, with the bridge module named in the
      description — the C3 manifest gate resolves manifest witnesses against `proof_file`);
  (d) `prediction_chain` — `PROOF-rule-gradient-and-tangent-field` re-added.  That edge was
      deliberately withheld on PR #689 (§I4 R2) because no Lean statement linked the anchor to
      RuleFlow's gradient; the bridge module is exactly that link (a Substrate → Substrate/Foundations
      derivation, target layer ≤ source layer, so countable under the 2026-09-30 edge rules);
  (e) `verification` — re-stamped with the bounded bridge build and the five new witnesses.

Nothing else in the ledger changes except `version` (6.12.0 → 6.13.0), `last_updated` and the
appended `changelog` entry.  The manifest is NOT touched: the anchor's `proof_file` is still the
Foundations file, and C3 requires every manifest witness to appear in that file, so adding the
Substrate-layer bridge names to the manifest entry would break the gate rather than strengthen it.

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
TOOLCHAIN = (ROOT / "proofs/lean-toolchain").read_text().strip()

ANCHOR_ID = "PROOF-gradient-lies-in-host-kernel-algebra"
DATE = "2026-09-30T00:00:00Z"
VERSION = "6.13.0"
NEW_EDGE = "PROOF-rule-gradient-and-tangent-field"

IF = "QBP.Foundations.InFlightAlgebra."
BR = "QBP.Substrate.RuleFlowBridge."
F_IF = "proofs/QBP/Foundations/InFlightAlgebra.lean"
F_BR = "proofs/QBP/Substrate/RuleFlowBridge.lean"

BRIDGE_THEOREMS = [
    BR + "gradVof_eq_gradV",
    BR + "gradVlo_eq_cdLo_gradV",
    BR + "gradVhi_eq_cdHi_gradV",
    BR + "gradV_mem_kernelAlgebra",
    BR + "smul_self_add_smul_gradV_mem_kernelAlgebra",
]

NAME = (
    "For EVERY sedenion s = a + b·ℓ (no imaginarity or unit-norm hypothesis) the RULE's gradient "
    "∇V(s) = RuleFlow.gradV(s) lies in the host kernel algebra 𝕆_s = H_s ⊕ H_s·ℓ, where "
    "H_s = span{1, a, Im b, a·Im b} ⊂ 𝕆 is closed under product and conjugation and associative; "
    "s ∈ 𝕆_s; hence α·s + β·∇V(s) ∈ 𝕆_s for all α, β. The identity gradVof(s) = RuleFlow.gradV(s) "
    "is PROVED in Lean (Substrate/RuleFlowBridge.lean, #690), so the Foundations membership is a "
    "membership of the rule's own gradient; flow / leaf invariance of 𝕆_s stays OPEN "
    "(FLAG-rule-flow-open)"
)

NOT_ANCHORED = (
    " Definition D of #688 (the foliation of InFlight by the leaves S⁶(𝕆_s) ∩ InFlight, leaf invariance "
    "under deterministic G₂-equivariant rules, the leaf space {ℍ ⊂ 𝕆} = G₂/SO(4)) is ARGUMENT / NUMERICAL "
    "and is NOT anchored; this anchor supports only the PROVED clause named above."
)

DESCRIPTION = (
    f"{F_IF}: `gradVof_mem_kernelAlgebra` (the main theorem) — for every s : CDAlg ℝ 4, "
    "InKernelAlgebra s (gradVof s), where InKernelAlgebra s x := InQuatSpanOct (cdLo s) (imHi s) "
    "(cdLo x) ∧ InQuatSpanOct (cdLo s) (imHi s) (cdHi x) (both CD components of x in H_s), "
    "InQuatSpanOct a c x := x ∈ Submodule.span ℝ (gen4 a c) = span{1, a, c, a·c} ⊂ 𝕆 = CDAlg ℝ 3, "
    "imHi s := cdHi s − (cdHi s).coord 0 • 1 = Im b, and gradVof s := loOf (gradVlo s) + hiOf "
    "(gradVhi s) is the Foundations closed form of the CD components of ∇V — identified with the "
    "rule's gradient by theorem, see the bridge paragraph below. "
    "`gradVof_components_mem_kernelAlgebra` (renamed from `gradV_mem_kernelAlgebra` by §I4 C2, which "
    "is kept as a deprecated alias and is NOT a witness of this anchor) — the component form: "
    "InQuatSpanOct (cdLo s) (imHi s) (gradVlo s) ∧ InQuatSpanOct (cdLo s) (imHi s) (gradVhi s). "
    "`self_mem_kernelAlgebra` — InKernelAlgebra s s. `smul_self_add_smul_gradV_mem_kernelAlgebra` — "
    "for every s and α β : ℝ, InKernelAlgebra s (α • s + β • gradVof s) (via `inKernelAlgebra_add`, "
    "`inKernelAlgebra_smul`: 𝕆_s is closed under + and •). The host algebra: `inQuatSpanOct_mul` — H "
    "closed under the product (on `span4_mul_closed`); `inQuatSpanOct_conj` — H closed under "
    "conjugation (x̄ = 2 Re x · 1 − x); `inQuatSpanOct_assoc` — (x * y) * z = x * (y * z) on H (on "
    "`assoc_vanishes_on_span4`): H_s is a conjugation-closed associative subalgebra of 𝕆, a quaternion "
    "algebra when 4-dimensional (degenerate at a vacuum, where a ∥ Im b). `cdComm_eq_comm_imHi` — "
    "cdComm s = cdLo s * imHi s − imHi s * cdLo s, i.e. [a, b] = [a, Im b] ∈ H_s. "
    f"THE BRIDGE (#690, {F_BR}, Substrate layer — Foundations may not import Substrate, so the "
    "identity has to live there): `gradVof_eq_gradV` — for every s : CDAlg ℝ 4, "
    "QBP.Foundations.InFlightAlgebra.gradVof s = QBP.Substrate.RuleFlow.gradV s, i.e. the Foundations "
    "closed form IS the rule's gradient; `gradVlo_eq_cdLo_gradV` — gradVlo s = cdLo (RuleFlow.gradV s) "
    "and `gradVhi_eq_cdHi_gradV` — gradVhi s = cdHi (RuleFlow.gradV s), the two CD halves that the "
    "InFlightAlgebra header (l.546–548) had asserted textually only. Transported through the bridge: "
    "`gradV_mem_kernelAlgebra` — InKernelAlgebra s (RuleFlow.gradV s), the RULE's gradient lies in "
    "𝕆_s for every sedenion s; and (the Substrate-layer) "
    "`smul_self_add_smul_gradV_mem_kernelAlgebra` — InKernelAlgebra s (α • s + β • RuleFlow.gradV s) "
    "for all α β : ℝ. So the clause PR #689 recorded as NOT claimed ('gradVof = RuleFlow.gradV is not "
    "stated in Lean', #683 → #690) is now CLAIMED, and with it ∇V(s) ∈ 𝕆_s for the rule's own "
    "gradient. prediction_chain: PROOF-alternator-vanishes-iff-commute and "
    "PROOF-rule-gradient-and-tangent-field — the second edge, withheld on PR #689 (§I4 R2) precisely "
    "because no Lean statement linked this anchor to RuleFlow's gradient, is now live: the bridge "
    "module reaches RuleFlow.gradV directly and is a Substrate → Substrate/Foundations derivation "
    "(target layer ≤ source layer). NOT claimed: the rule FIELD F(s) = −(∇V(s) − ⟪∇V(s), s⟫·s − "
    "(∇V(s)).coord 0 · 1) (`RuleFlow.ruleField`) — no theorem states InKernelAlgebra s (ruleField s); "
    "it would follow from the proved closure of 𝕆_s under + and • with s ∈ 𝕆_s and a true but "
    "UNSTATED 1 ∈ 𝕆_s, so the F-level containment remains ARGUMENT, one unstated lemma away; flow / "
    "leaf invariance — that 𝕆_s is constant along a trajectory (ARGUMENT, conditional on existence of "
    "integral curves — FLAG-rule-flow-open, #635; the containment proved here is pointwise in s and "
    "says nothing about a trajectory); 𝕆_s = ker Δ(s) (rank 8 NUMERICAL, reverse inclusion OPEN); the "
    "leaf space G₂/SO(4) (ARGUMENT); 4-dimensionality of H_s (Lean says 'at most 4-dimensional'); "
    "anything about the anneal (#635) or the endpoint / ω-limit." + NOT_ANCHORED
)

VERIFIER = (
    "Bridge (#690, lean-prover, 2026-09-30, isolated worktree probe-690-bridge): run-bounded 6G 1800 "
    "taskset -c 3-5 lake build QBP.Substrate.RuleFlowBridge — exit 0, 3129 jobs; `#print axioms` on "
    "all five bridge theorems (gradVof_eq_gradV, gradVlo_eq_cdLo_gradV, gradVhi_eq_cdHi_gradV, "
    "gradV_mem_kernelAlgebra, smul_self_add_smul_gradV_mem_kernelAlgebra) ⊆ {propext, "
    "Classical.choice, Quot.sound}; statements re-read fully qualified (`#check` with pp of full "
    "names) to confirm the right-hand sides are QBP.Substrate.RuleFlow.gradV and not a local copy; 0 "
    "sorry, 0 native_decide, 0 vacuous `True`; check_lean_foundations.py exit 0, "
    "check_layer_imports.py exit 0 (the new module is a Substrate file importing Foundations — the "
    "allowed direction — and is registered in the QBP/Substrate.lean aggregator). Foundations half, "
    "carried from PR #689: run-bounded lake build QBP.Foundations.InFlightAlgebra (3022 jobs, exit 0) "
    "+ #print axioms on the 42 audited declarations of InFlightAlgebra.lean, all ⊆ {propext, "
    "Classical.choice, Quot.sound}; PR #689 Red Team APPROVE-WITH-CONCERN M1–M4 applied, Gemini "
    "APPROVE, §I4 qbp-architecture APPROVE-WITH-CONCERN at b85df23 (C1–C4) and a38a0af (R1/R2 — this "
    "encode retires R2's withheld chain edge by supplying the Lean link it was withheld for)"
)

CHANGELOG = {
    "version": VERSION,
    "date": DATE,
    "note": (
        "lean-prover / qbp-oppenheimer (issue #690): the bridge lemma is PROVED, so anchor "
        "PROOF-gradient-lies-in-host-kernel-algebra is re-scoped from the Foundations copy to the "
        "RULE's gradient. New Substrate module proofs/QBP/Substrate/RuleFlowBridge.lean (5 theorems, "
        "kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound}, 0 sorry, no native_decide): "
        "`gradVof_eq_gradV` (QBP.Foundations.InFlightAlgebra.gradVof s = QBP.Substrate.RuleFlow.gradV "
        "s), its two CD halves `gradVlo_eq_cdLo_gradV` / `gradVhi_eq_cdHi_gradV` (the identities the "
        "InFlightAlgebra header had asserted textually only), and the transported memberships "
        "`gradV_mem_kernelAlgebra` (InKernelAlgebra s (RuleFlow.gradV s)) and "
        "`smul_self_add_smul_gradV_mem_kernelAlgebra` (InKernelAlgebra s (α • s + β • "
        "RuleFlow.gradV s)). Consequently: (a) the anchor's `name` and `description` move the identity "
        "— and with it ∇V(s) ∈ 𝕆_s for the rule's own gradient — from the NOT-claimed list into the "
        "claimed list, citing both proof files; (b) the five bridge theorems join "
        "`lean_companion_theorems` and `verification.witnesses` (headline `lean_theorem` and "
        "`proof_file` unchanged — the anchor's main statement is still the Foundations "
        "`gradVof_mem_kernelAlgebra`); (c) `prediction_chain` regains "
        "PROOF-rule-gradient-and-tangent-field, the edge withheld on PR #689 (§I4 R2) for want of "
        "exactly this Lean link — a Substrate → Substrate/Foundations derivation, target layer ≤ "
        "source layer; (d) `verification` re-stamped with the bounded bridge build (exit 0, 3129 "
        "jobs) and both gates at exit 0. STILL NOT claimed, unchanged: the rule FIELD F(s) = "
        "−(∇V − ⟪∇V, s⟫s − (∇V)₀·1) (no theorem mentions `ruleField`; it needs an unstated 1 ∈ 𝕆_s), "
        "flow / leaf invariance of 𝕆_s (conditional on existence of integral curves — "
        "FLAG-rule-flow-open, #635; the new containment is pointwise in s), 𝕆_s = ker Δ(s) (reverse "
        "inclusion OPEN, rank 8 NUMERICAL), the leaf space G₂/SO(4), the anneal, the endpoint. One "
        "record touched; anchors 1–3 of PR #689 untouched; no root, principle, decision or kill "
        "touched; FLAG-rule-flow-open and CONJ-condensed-math-for-transition-state not touched. "
        "(Version 6.13.0: encoded on master 6.12.0/343.)"
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if not (ROOT / F_BR).exists():
        raise SystemExit(f"bridge module missing on this head: {F_BR}")
    src = (ROOT / F_BR).read_text(encoding="utf-8")
    for t in BRIDGE_THEOREMS:
        short = t.rsplit(".", 1)[1]
        if f"theorem {short}" not in src:
            raise SystemExit(f"witness does not resolve in {F_BR}: {short}")

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        if NEW_EDGE not in have:
            raise SystemExit(f"prediction_chain target missing from ledger: {NEW_EDGE}")
        a = ed.record("anchors", ANCHOR_ID)
        if NEW_EDGE in a["prediction_chain"]:
            raise SystemExit("already applied: chain edge present")
        a["name"] = NAME
        a["description"] = DESCRIPTION
        a["lean_companion_theorems"] = a["lean_companion_theorems"] + BRIDGE_THEOREMS
        a["prediction_chain"] = sorted(set(a["prediction_chain"]) | {NEW_EDGE})
        a["last_tested_at"] = DATE
        v = a["verification"]
        v["toolchain"] = TOOLCHAIN
        v["verified_at"] = DATE
        v["verifier"] = VERIFIER
        v["witnesses"] = v["witnesses"] + BRIDGE_THEOREMS
        L["version"] = VERSION
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")

    print(
        f"  {ANCHOR_ID}: +{len(BRIDGE_THEOREMS)} companions/witnesses, chain += {NEW_EDGE}"
    )
    print(
        f"{'DRY ' if args.dry_run else ''}applied: 1 anchor re-scoped; ledger {VERSION}"
    )


if __name__ == "__main__":
    main()
