#!/usr/bin/env python3
"""PROOF anchors for the in-flight algebra (PR #689, #688 definition D) — encode-AFTER-review.

Four anchors for `proofs/QBP/Foundations/InFlightAlgebra.lean`: the alternator Δ(s) = L_s² + N(s)·id =
−[s, s, ·] is blind to the ℓ-direction ([s + tℓ, s + tℓ, ·] = [s, s, ·]) while L_s² alone is not; at
EVERY imaginary s the in-flight span ℍ_s = span{1, s, ℓ, s·ℓ} is closed under the product and associative,
4-dimensional for unit imaginary s iff s ≠ ±ℓ (both directions of the independence iff proved), and
associative even at s = e₁ + e₁₀ where 𝕊's alternator
is nonzero; ℍ_s ⊆ ker Δ(s) (the hosting identity s·(s·x) = −N(s)·x holds on ℍ_s); and for EVERY sedenion
s = a + b·ℓ the Foundations closed-form gradient components gradVof(s) lie in 𝕆_s = H_s ⊕ H_s·ℓ, H_s =
span{1, a, Im b, a·Im b} ⊂ 𝕆 a conjugation-closed associative subalgebra, with s ∈ 𝕆_s and
α·s + β·gradVof(s) ∈ 𝕆_s (the identity gradVof = RuleFlow.gradV is NOT stated in Lean, #683). These are
the PROVED clauses of D (§1 of docs/foundations/688-in-flight-definition-2026-09-29.md); D itself — the
foliation of InFlight by the 6-dim leaves S⁶(𝕆_s) ∩ InFlight, leaf invariance, the leaf space G₂/SO(4) —
is ARGUMENT / NUMERICAL and is NOT anchored. Every anchor cites theorems on the branch, 0-sorry,
`#print axioms` ⊆ {propext, Classical.choice, Quot.sound} on the 42 audited declarations, reviewed
(PR #689 Red Team APPROVE-WITH-CONCERN M1–M4 applied, Gemini APPROVE, §I4 qbp-architecture
APPROVE-WITH-CONCERN at b85df23 with C1–C4 applied; §I4 re-read at a38a0af APPROVE-WITH-CONCERN with
R1/R2 applied — anchor 4 named for gradVof only, its RuleFlow chain edge withheld; Red Team re-check at
a38a0af APPROVE-WITH-CONCERN with M1 applied — anchor 2's "independent iff p ≠ 0" now has BOTH directions in
Lean, `inFlight_dependent_of_pOf_eq_zero` and `inFlight_independent_iff`). No root, principle, decision or
kill is touched; FLAG-rule-flow-open and CONJ-condensed-math-for-transition-state are not touched. The
§8 NOT-claimed clauses go into every anchor; anchor 4 states explicitly that `gradVof = RuleFlow.gradV`
is NOT in Lean (bridge lemma owed, #683). Manifest entries added alongside; then
`anchor_inverse_audit.py --update-baseline` records the anchored growth.
Usage: python3 scripts/encode_688_inflight_anchors.py [--dry-run]
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
BATCH = "#689-in-flight-algebra"
IF = "QBP.Foundations.InFlightAlgebra."
F_IF = "proofs/QBP/Foundations/InFlightAlgebra.lean"
VERIFIER = (
    "run-bounded lake build QBP.Foundations.InFlightAlgebra (3022 jobs, exit 0) + #print axioms on the 42 "
    "audited declarations of the file (71 theorems — 70 plus the deprecated alias gradV_mem_kernelAlgebra "
    "kept by §I4 C2 — and 10 defs), all ⊆ {propext, Classical.choice, Quot.sound}; foundations gate + "
    "layer-imports gate exit 0 (lean-prover, 2026-09-30, re-run at the Red Team re-check M1 head — the "
    "converse `inFlight_dependent_of_pOf_eq_zero` and the packaged `inFlight_independent_iff` added, so "
    "anchor 2's independence 'iff' is proved in both directions; PR #689 Red Team APPROVE-WITH-CONCERN "
    "M1–M4 applied, Gemini APPROVE, §I4 qbp-architecture APPROVE-WITH-CONCERN at b85df23 — independently "
    "verified there: build exit 0, 39/39 audits clean before C1–C4; Red Team re-check at a38a0af "
    "APPROVE-WITH-CONCERN, 40/40 clean, its M1 fixed here)"
)
# Anchors 1–3 (the ℍ_s algebra) chain to the in-flight hosting-failure anchor whose NOT-claimed clause they
# fill and to the δ-landscape alternator anchor (T_s = 0 ⟺ CD components commute) that Δ = −T_s refines.
CHAIN_ALG = [
    "PROOF-hosting-identity-fails-in-flight",
    "PROOF-alternator-vanishes-iff-commute",
]
# Anchor 4 (gradVof(s) ∈ 𝕆_s) chains to the same alternator anchor ONLY. The edge to
# PROOF-rule-gradient-and-tangent-field (proof file Substrate/RuleFlow.lean) is deliberately withheld: the Lean
# file imports only Foundations, and the only link to RuleFlow's gradient is the OPEN #683 bridge lemma
# (§I4 R2 at a38a0af — a chain edge is support, and that edge would launder the gap into provenance).
CHAIN_GRAD = [
    "PROOF-alternator-vanishes-iff-commute",
]
CHAIN_ALL = sorted(set(CHAIN_ALG) | set(CHAIN_GRAD))
NOT_ANCHORED = (
    " Definition D of #688 (the foliation of InFlight by the leaves S⁶(𝕆_s) ∩ InFlight, leaf invariance "
    "under deterministic G₂-equivariant rules, the leaf space {ℍ ⊂ 𝕆} = G₂/SO(4)) is ARGUMENT / NUMERICAL "
    "and is NOT anchored; this anchor supports only the PROVED clause named above."
)


def _libs():
    m = json.loads(LAKE.read_text())
    return {
        p["name"]: {"ref": p.get("inputRev") or p["rev"], "sha": p["rev"]}
        for p in m["packages"]
        if p["name"] in ("mathlib", "batteries")
    }


def anchor(aid, name, desc, main, companions, chain):
    wits = [main] + companions
    return {
        "id": aid,
        "name": name,
        "tier": 1,
        "layer_tag": "T",
        "status": "coherent",
        "provenance_kind": "proof",
        "description": desc,
        "proof_file": F_IF,
        "proof_language": "lean4",
        "proof_state": "verified",
        "lean_theorem": main,
        "lean_companion_theorems": companions,
        "sorry_count": 0,
        "provenance": "T",
        "prediction_chain": chain,
        "foundation_batch": BATCH,
        "last_tested_at": DATE,
        "verification": {
            "toolchain": TOOLCHAIN,
            "libraries": _libs(),
            "verified_at": DATE,
            "verifier": VERIFIER,
            "result": "verified",
            "axiom_closure": ["propext", "Classical.choice", "Quot.sound"],
            "witnesses": wits,
        },
    }


ANCHORS = [
    anchor(
        "PROOF-in-flight-alternator-blind-to-ell",
        "The left alternator [s, s, ·] is blind to the ℓ-direction: [s + tℓ, s + tℓ, ·] = [s, s, ·] for EVERY s ∈ 𝕊 and t ∈ ℝ; hence Δ(s) := L_s² + N(s)·id = −[s, s, ·] satisfies Δ(s + tℓ) = Δ(s) for imaginary s, while L_s² alone shifts by (N(s) − N(s + tℓ))·id",
        "Foundations/InFlightAlgebra.lean: `assoc_self_add_smul_ell` (the main theorem) — for every s, x : "
        "CDAlg ℝ 4 and t : ℝ, assoc (s + t • ell) (s + t • ell) x = assoc s s x, with NO imaginarity or norm "
        "hypothesis on s: the left alternator at s depends on s only through its ℓ-orthogonal part. "
        "`delta_eq_neg_assoc` — for imaginary s (s.coord 0 = 0), Delta s x = −assoc s s x, where "
        "Delta s x := s * (s * x) + (N s) • x (`Delta`); so Δ(s) is exactly minus the left alternator, "
        "Δ(s) = −T_s of PROOF-alternator-vanishes-iff-commute. `delta_blind_to_ell` — for imaginary s and "
        "every t, Delta (s + t • ell) x = Delta s x: Δ is ℓ-blind as an operator on 𝕊 (D's clause 'Δ blind "
        "to b₀'). `left_mul_sq_ell_shift` — the honest caveat, in L_s² form: for imaginary s, "
        "(s + tℓ)·((s + tℓ)·x) + N(s + tℓ)·x = s·(s·x) + N(s)·x, i.e. L_{s+tℓ}² = L_s² + (N(s) − N(s + tℓ))·id; "
        "L_s² on its own is NOT ℓ-blind, only the combination Δ is. NOT claimed: that L_s² alone is ℓ-blind "
        "(the shift is the theorem); anything about Δ's spectrum (T2b: Δ³ = VΔ, ‖Δ‖_op = √V, spectrum "
        "{0⁸, ±√V⁴} — NUMERICAL to 3·10⁻¹⁶ only, OPEN in Lean)." + NOT_ANCHORED,
        IF + "assoc_self_add_smul_ell",
        [
            IF + "delta_blind_to_ell",
            IF + "left_mul_sq_ell_shift",
            IF + "delta_eq_neg_assoc",
        ],
        CHAIN_ALG,
    ),
    anchor(
        "PROOF-in-flight-quaternion-closes-and-associates",
        "At EVERY imaginary s ∈ 𝕊 the in-flight span ℍ_s = span{1, s, ℓ, s·ℓ} is closed under the product and associative; {1, s, ℓ, s·ℓ} is linearly independent iff p = s − b₀ℓ ≠ 0 (BOTH directions proved: independence where p ≠ 0, an explicit dependence witness where p = 0), and for UNIT imaginary s, p = 0 iff s = ±ℓ — so ℍ_s is 4-dimensional for unit imaginary s iff s ≠ ±ℓ; associativity holds at s = e₁ + e₁₀ where 𝕊's alternator at s is nonzero",
        "Foundations/InFlightAlgebra.lean: `inFlight_closed_associative` (the main theorem) — for every s with "
        "s.coord 0 = 0: (∀ x y, InFlightSpan s x → InFlightSpan s y → InFlightSpan s (x * y)) ∧ (∀ x y z, "
        "InFlightSpan s x → InFlightSpan s y → InFlightSpan s z → (x * y) * z = x * (y * z)), where "
        "InFlightSpan s x := ∃ α β γ δ : ℝ, x = α • 1 + β • s + γ • ell + δ • (s * ell) (`InFlightSpan`). "
        "Components: `inFlightSpan_mul_closed` and `inFlightSpan_assoc` (same hypotheses, the two conjuncts), "
        "proved through the change of basis ℍ_s = span{1, ℓ, p, ℓ·p} with p = pOf s := s − b₀·ℓ, "
        "b₀ = s.coord (hiIdx 0) (`inFlightSpan_iff_quatSpan`); `quatSpan_mul_expand` — for imaginary p ⊥ ℓ "
        "(p.coord 0 = 0, p.coord (hiIdx 0) = 0) the explicit quaternion multiplication table of "
        "(a₁·1 + b₁ℓ + c₁p + d₁ℓp)(a₂·1 + b₂ℓ + c₂p + d₂ℓp) with N(p) as the structure constant; "
        "`quatSpan_assoc` — three elements of span{1, ℓ, p, ℓp} re-associate. Independence, BOTH "
        "directions: `inFlight_independent` (⇐) — for imaginary s with pOf s ≠ 0, α • 1 + β • s + γ • ell + "
        "δ • (s * ell) = 0 → α = β = γ = δ = 0; `inFlight_dependent_of_pOf_eq_zero` (⇒) — for EVERY s with "
        "pOf s = 0 (no imaginarity hypothesis needed) there EXIST α β γ δ : ℝ, not all zero, with "
        "α • 1 + β • s + γ • ell + δ • (s * ell) = 0, by the explicit witness (α, β, γ, δ) = (b₀, 0, 0, 1): "
        "pOf s = 0 gives s = b₀·ℓ, hence s·ℓ = b₀·(ℓ·ℓ) = −b₀·1, and δ = 1 ≠ 0 covers both b₀ ≠ 0 and the "
        "degenerate b₀ = 0 (s = 0) case; `inFlight_independent_iff` — the packaged equivalence, for imaginary "
        "s: (∀ α β γ δ : ℝ, α • 1 + β • s + γ • ell + δ • (s * ell) = 0 → α = β = γ = δ = 0) ↔ pOf s ≠ 0. So "
        "the 'independent iff p ≠ 0' of this anchor's name is a Lean theorem, not a one-way reading. `pOf_eq_zero_iff` — for N s = 1, pOf s = 0 ↔ (s = ell ∨ "
        "s = −ell): so for UNIT imaginary s, ℍ_s is 4-dimensional iff s ≠ ±ℓ (at ±ℓ the span degenerates to "
        "span{1, ℓ} ≅ ℂ). `ell_mul_eq` — for imaginary s, ell * s = (−2·b₀) • 1 − s * ell: s and ℓ anticommute "
        "iff b₀ = 0. `inFlight_associative_even_where_alternator_nonzero` — (∃ x, assoc sedWitX sedWitX x ≠ 0) "
        "∧ ℍ_{sedWitX} is associative, sedWitX = e₁ + e₁₀: associativity of ℍ_s is NOT alternativity restated "
        "(𝕊 is not alternative at s, yet the span through s associates). NOT claimed: 4-dimensionality at "
        "s = ±ℓ (there ℍ_s = span{1, ℓ}); that ℍ_s is the full kernel ker Δ(s) (the reverse inclusion is OPEN; "
        "rank 8 is NUMERICAL only); anything about the flow, orbits or the endpoint; any reversal of "
        "PROOF-hosting-identity-fails-in-flight — this anchor FILLS that anchor's NOT-claimed clause: the "
        "hosting identity fails for SOME x at every in-flight s, and holds on ℍ_s "
        "(PROOF-in-flight-span-in-alternator-kernel)." + NOT_ANCHORED,
        IF + "inFlight_closed_associative",
        [
            IF + "inFlightSpan_mul_closed",
            IF + "inFlightSpan_assoc",
            IF + "quatSpan_assoc",
            IF + "quatSpan_mul_expand",
            IF + "inFlight_independent",
            IF + "inFlight_dependent_of_pOf_eq_zero",
            IF + "inFlight_independent_iff",
            IF + "pOf_eq_zero_iff",
            IF + "ell_mul_eq",
            IF + "inFlight_associative_even_where_alternator_nonzero",
        ],
        CHAIN_ALG,
    ),
    anchor(
        "PROOF-in-flight-span-in-alternator-kernel",
        "At EVERY imaginary s ∈ 𝕊 the in-flight span ℍ_s = span{1, s, ℓ, s·ℓ} lies in ker Δ(s): Δ(s)x = 0 and the hosting identity s·(s·x) = −N(s)·x hold for every x ∈ ℍ_s; the four kernel witnesses 1, s, ℓ, s·ℓ",
        "Foundations/InFlightAlgebra.lean: `delta_vanishes_on_inFlightSpan` (the main theorem) — for s with "
        "s.coord 0 = 0 and x with InFlightSpan s x (x = α • 1 + β • s + γ • ell + δ • (s * ell)), "
        "Delta s x = 0, Delta s x := s * (s * x) + (N s) • x; via Δ(s) = −[s, s, ·] and the associativity of "
        "ℍ_s (PROOF-in-flight-quaternion-closes-and-associates), so ℍ_s ⊆ ker Δ(s) = ker [s, s, ·]. "
        "`left_mul_sq_on_inFlightSpan` — the same in L_s² form: under the same hypotheses, "
        "s * (s * x) = (−(N s)) • x — the hosting identity of PROOF-crystal-hosts-quaternion holds on ℍ_s at "
        "every imaginary s (hosting sharpened), consistent with PROOF-hosting-identity-fails-in-flight, which "
        "says it fails for SOME x ∈ 𝕊 at every in-flight s. The four kernel witnesses, each for s.coord 0 = 0: "
        "`one_mem_ker_delta` — Delta s 1 = 0; `s_mem_ker_delta` — Delta s s = 0 (third-power associativity "
        "[s, s, s] = 0); `ell_mem_ker_delta` — Delta s ell = 0 (the doubling unit is always a kernel "
        "direction); `s_mul_ell_mem_ker_delta` — Delta s (s * ell) = 0. NOT claimed: the reverse inclusion "
        "ker Δ(s) ⊆ ℍ_s or ker Δ(s) ⊆ 𝕆_s (OPEN — K-a's target); that ker Δ(s) has rank 8 (NUMERICAL: 200 "
        "random states + the ridge witness (e₁ + e₁₀)/√2, `analysis/688-in-flight/delta_spectrum_check.py`)."
        + NOT_ANCHORED,
        IF + "delta_vanishes_on_inFlightSpan",
        [
            IF + "left_mul_sq_on_inFlightSpan",
            IF + "one_mem_ker_delta",
            IF + "s_mem_ker_delta",
            IF + "ell_mem_ker_delta",
            IF + "s_mul_ell_mem_ker_delta",
        ],
        CHAIN_ALG,
    ),
    anchor(
        "PROOF-gradient-lies-in-host-kernel-algebra",
        "For EVERY sedenion s = a + b·ℓ (no imaginarity or unit-norm hypothesis) gradVof(s) — the Foundations closed-form gradient components — lies in the host kernel algebra 𝕆_s = H_s ⊕ H_s·ℓ, where H_s = span{1, a, Im b, a·Im b} ⊂ 𝕆 is closed under product and conjugation and associative; s ∈ 𝕆_s; hence α·s + β·gradVof(s) ∈ 𝕆_s for all α, β. The identity gradVof = RuleFlow.gradV is NOT stated in Lean (#683)",
        "Foundations/InFlightAlgebra.lean: `gradVof_mem_kernelAlgebra` (the main theorem) — for every "
        "s : CDAlg ℝ 4, InKernelAlgebra s (gradVof s), where InKernelAlgebra s x := "
        "InQuatSpanOct (cdLo s) (imHi s) (cdLo x) ∧ InQuatSpanOct (cdLo s) (imHi s) (cdHi x) (both CD "
        "components of x in H_s), InQuatSpanOct a c x := x ∈ Submodule.span ℝ (gen4 a c) = span{1, a, c, a·c} "
        "⊂ 𝕆 = CDAlg ℝ 3, imHi s := cdHi s − (cdHi s).coord 0 • 1 = Im b, and gradVof s := loOf (gradVlo s) + "
        "hiOf (gradVhi s) is the Foundations copy of the closed-form CD components (matched to RuleFlow's gradient by "
        "citation only — see the NOT-claimed clause). "
        "`gradVof_components_mem_kernelAlgebra` (renamed from `gradV_mem_kernelAlgebra` by §I4 C2, which is "
        "kept as a deprecated alias and is NOT a witness of this anchor) — the component form: "
        "InQuatSpanOct (cdLo s) (imHi s) (gradVlo s) ∧ InQuatSpanOct (cdLo s) (imHi s) (gradVhi s). `self_mem_kernelAlgebra` — InKernelAlgebra s s. "
        "`smul_self_add_smul_gradV_mem_kernelAlgebra` — for every s and α β : ℝ, "
        "InKernelAlgebra s (α • s + β • gradVof s) (via `inKernelAlgebra_add`, `inKernelAlgebra_smul`: 𝕆_s is "
        "closed under + and •). The host algebra: `inQuatSpanOct_mul` — H closed under the product (on "
        "`span4_mul_closed`); `inQuatSpanOct_conj` — H closed under conjugation (x̄ = 2 Re x · 1 − x); "
        "`inQuatSpanOct_assoc` — (x * y) * z = x * (y * z) on H (on `assoc_vanishes_on_span4`): H_s is a "
        "conjugation-closed associative subalgebra of 𝕆, a quaternion algebra when 4-dimensional (degenerate "
        "at a vacuum, where a ∥ Im b). `cdComm_eq_comm_imHi` — cdComm s = cdLo s * imHi s − imHi s * cdLo s, "
        "i.e. [a, b] = [a, Im b] ∈ H_s. `gradVof` is a Foundations-level copy of the closed form that "
        "`RuleFlow.cdLo_gradV`/`cdHi_gradV` prove; the identity `gradVof s = gradV s` is NOT stated in Lean "
        "(bridge lemma owed, #683). prediction_chain: PROOF-alternator-vanishes-iff-commute only — the chain "
        "to PROOF-rule-gradient-and-tangent-field is deliberately withheld until the #683 bridge lemma lands in "
        "Substrate (InFlightAlgebra.lean imports only Foundations; §I4 R2). NOT claimed: that `gradVof` = `RuleFlow.gradV` in Lean (matched by "
        "citation only); flow / leaf invariance (ARGUMENT, conditional on existence — FLAG-rule-flow-open); "
        "anything about the rule field F(s) — no theorem in this file mentions it, and no membership of it is "
        "claimed here (§I4 C3); 𝕆_s = ker Δ(s) (rank 8 NUMERICAL, reverse inclusion OPEN); the leaf space "
        "G₂/SO(4) (ARGUMENT); 4-dimensionality of H_s (Lean says 'at most 4-dimensional'); anything about the "
        "anneal (#635) or the endpoint / ω-limit." + NOT_ANCHORED,
        IF + "gradVof_mem_kernelAlgebra",
        [
            IF + "gradVof_components_mem_kernelAlgebra",
            IF + "self_mem_kernelAlgebra",
            IF + "smul_self_add_smul_gradV_mem_kernelAlgebra",
            IF + "inQuatSpanOct_mul",
            IF + "inQuatSpanOct_conj",
            IF + "inQuatSpanOct_assoc",
            IF + "cdComm_eq_comm_imHi",
        ],
        CHAIN_GRAD,
    ),
]

CHANGELOG = {
    "version": "6.12.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: PROOF anchors for the in-flight algebra (PR #689; #688 definition D) — "
        "encode-after-review (Red Team APPROVE-WITH-CONCERN M1–M4 applied, Gemini APPROVE, §I4 "
        "qbp-architecture APPROVE-WITH-CONCERN at b85df23 with C1–C4 applied, §I4 re-read at a38a0af "
        "APPROVE-WITH-CONCERN with R1/R2 applied, Red Team re-check at a38a0af with M1 applied — the gradient theorem renamed "
        "gradV_mem_kernelAlgebra → gradVof_components_mem_kernelAlgebra, old name a deprecated alias): "
        "PROOF-in-flight-alternator-blind-to-ell ([s + tℓ, s + tℓ, ·] = [s, s, ·] for every s, t; "
        "Δ(s + tℓ) = Δ(s) for imaginary s; L_s² alone shifts by (N(s) − N(s + tℓ))·id), "
        "PROOF-in-flight-quaternion-closes-and-associates (ℍ_s = span{1, s, ℓ, sℓ} closed under the product and "
        "associative at every imaginary s, 4-dimensional for unit imaginary s iff s ≠ ±ℓ — both directions of "
        "the independence iff proved, `inFlight_independent` and `inFlight_dependent_of_pOf_eq_zero`, packaged "
        "as `inFlight_independent_iff` (Red Team re-check M1) — associative even at "
        "e₁ + e₁₀ where the alternator is nonzero), PROOF-in-flight-span-in-alternator-kernel (ℍ_s ⊆ ker Δ(s); "
        "the hosting identity s(sx) = −N(s)x holds on ℍ_s; the four kernel witnesses), "
        "PROOF-gradient-lies-in-host-kernel-algebra (for every sedenion s = a + bℓ, gradVof(s) — the Foundations "
        "closed-form gradient components — lies in 𝕆_s = H_s ⊕ H_s ℓ with H_s = span{1, a, Im b, a·Im b} a "
        "conjugation-closed associative subalgebra of 𝕆; s ∈ 𝕆_s; α·s + β·gradVof(s) ∈ 𝕆_s; "
        "gradVof = RuleFlow.gradV NOT stated in Lean, bridge lemma owed on #683). "
        "These support D's PROVED clauses — Δ = −T_s and ℓ-blind; ℍ_s closed, associative, 4-dim off ±ℓ, "
        "⊆ ker Δ(s); H_s a quaternion algebra in 𝕆; gradVof(s), s, α·s + β·gradVof(s) ∈ 𝕆_s. D itself — the foliation of "
        "InFlight = {V > 0} by the 6-dim leaves S⁶(𝕆_s) ∩ InFlight, leaf invariance under deterministic "
        "G₂-equivariant rules, the leaf space {ℍ ⊂ 𝕆} = G₂/SO(4) — is ARGUMENT / NUMERICAL and is NOT anchored. "
        "Four anchors, all 0-sorry, axiom closure {propext, Classical.choice, Quot.sound} on the 42 audited "
        "declarations of InFlightAlgebra.lean (71 theorems incl. one deprecated alias + 10 defs); anchors 1–3 chained to "
        "PROOF-hosting-identity-fails-in-flight (whose NOT-claimed clause anchor 2 fills) and "
        "PROOF-alternator-vanishes-iff-commute; anchor 4 to PROOF-alternator-vanishes-iff-commute ONLY — the edge to "
        "PROOF-rule-gradient-and-tangent-field (Substrate/RuleFlow.lean) is withheld until the #683 bridge lemma "
        "lands (§I4 R2: InFlightAlgebra.lean imports only Foundations). Every anchor carries the §8 NOT-claimed clauses of "
        "docs/foundations/688-in-flight-definition-2026-09-29.md: L_s² alone is not ℓ-blind; nothing about Δ's "
        "spectrum (T2b); no 4-dimensionality at ±ℓ; ℍ_s / 𝕆_s is not claimed to be the full kernel (reverse "
        "inclusion OPEN, rank 8 NUMERICAL); no reversal of PROOF-hosting-identity-fails-in-flight; no flow, "
        "leaf invariance, leaf space, anneal or endpoint claim. No root, principle, decision or kill touched; "
        "FLAG-rule-flow-open and CONJ-condensed-math-for-transition-state not touched. (Version 6.12.0: encoded "
        "on master 6.11.0/339.)"
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        for cid in CHAIN_ALL:
            if cid not in have:
                raise SystemExit(f"prediction_chain target missing from ledger: {cid}")
        for a in ANCHORS:
            if a["id"] in have:
                raise SystemExit(f"already applied: {a['id']}")
            ed.append("anchors", a)
        L["version"] = CHANGELOG["version"]
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")
    m = json.loads(MANIFEST.read_text())
    ids = {e["anchor_id"] for e in m["entries"]}
    for a in ANCHORS:
        if a["id"] not in ids:
            m["entries"].append(
                {
                    "anchor_id": a["id"],
                    "declared_by": BATCH,
                    "proof_system": "lean4",
                    "witnesses": a["verification"]["witnesses"],
                }
            )
    if not args.dry_run:
        MANIFEST.write_text(json.dumps(m, ensure_ascii=False, indent=2) + "\n")
    for a in ANCHORS:
        print(
            f"  {a['id']}  main={a['lean_theorem'].removeprefix(IF)}  "
            f"witnesses={len(a['verification']['witnesses'])}  chain={a['prediction_chain']}"
        )
    print(
        f"{'DRY ' if args.dry_run else ''}applied: {len(ANCHORS)} anchors; manifest entries {len(m['entries'])}"
    )


if __name__ == "__main__":
    main()
