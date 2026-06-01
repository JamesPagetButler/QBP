# CTH Disposition Draft — Entropy-Cone Inversion Hypothesis (DEAD)

**For:** @cth-implementor review (canonical inventory edits)
**From:** @qbp-oppenheimer
**Status:** DRAFT — content for review; canonical-target path to be confirmed before an inventory PR opens
**Basis:** beekeeper-ratified DEAD ruling (gemini decision log `qbp.md`, "Entropy-cone INVERSION hypothesis: DEAD"); derivation in `analysis/HQM-MMI-derive-or-die-report.md`; disposition agreed on `cth-qbp-live-testing` seq 15–17.

> **Canonical-target flag:** three copies of `confluent-trust-inventory-v5_3.v0.3.json` exist — QBP `archive/cth-inventory/` (tracked here), `qbp-systema/pkg/bookkeeper/testdata/`, and the `confluent-trust` repo (not checked out, the true canonical). @cth-implementor: confirm which path the inventory PR targets (and whether the others mirror). Edits below are path-independent.

---

## Edit 1 — `PROOF-division-algebra-entropy-cone-mapping`

```diff
- "status": "coherent",
+ "status": "incoherent",
+ "killed_by": "analysis/HQM-MMI-derive-or-die-report.md",
+ "killed_note": "Falsified (beekeeper-ratified). The 'ℂ→ℍ shrinks the entropy cone' mechanism is dead: multipartite ℍ-QM has no canonical tensor product; every definable repair builds on the complex projection (q=z+jz') ⟹ the achievable cone is identical to ℂ-QM's, so ℂ-QM's MMI violation (GHZ₄→I₃=+1>0) transports verbatim. Moretti-Oppio independently forces ℍ→ℂ under Poincaré+m²≥0. The genuinely-quaternionic regime gives super-Tsirelson (PR-box) correlations — a LARGER cone, opposite of the claim. Kept as a witnessed negative result.",
```
- **Keep the ID** (`PROOF-` prefix) — `provenance_kind` is already `theory` (machine layer honest); re-id is a breaking cross-tenant change (`cth://` refs + downstream chain). Defer re-id to a separate atomic op if desired.
- **tier-1 + incoherent** is semantically odd (tier 1 = proofs) — flag for tier review; status flip is the load-bearing fix.

## Edit 2 — `INSIGHT-entropy-cone-division-algebra-inversion`

```diff
- "status": "untested",
+ "status": "incoherent",
+ "killed_by": "analysis/HQM-MMI-derive-or-die-report.md",
+ "killed_note": "Tested (derive-or-die) and failed — no longer 'untested.' Same falsification as PROOF-division-algebra-entropy-cone-mapping.",
```

## Edit 3 — `CONV-cd-tower-in-zeta-moments` (statement rewrite, status stays `coherent`)

The arithmetic is true; only the structural over-claim is stripped. **Proposed corrected statement text:**

> The CCvS closed form γ(−a) carries the factor 2^(2a)−1. Since dim(Im A_n) = 2ⁿ−1 for **every** Cayley-Dickson level n, this factor equals dim(Im A_{2a}) — a **continuous family**, not a parity selection. Sampling integer a yields even levels (a=1→3=Im ℍ, a=2→15=Im 𝕊, …); sampling **half-integer a** recovers the odd levels (a=½→1=Im ℂ, a=3/2→7=Im 𝕆, a=5/2→31=Im pathions), and γ is finite/smooth there. **The earlier "even levels privileged / odd levels absent" claim is withdrawn** — it was an artifact of integer-a sampling, not a structural feature (verified: half-integer-a evaluation, `analysis/HQM-MMI-derive-or-die-report.md` companion check).

## Edit 4 — `INSIGHT-branch-A-hypergraph-boundary` (downstream, do NOT auto-flip)

- `prediction_chain` = `[PROOF-division-algebra-entropy-cone-mapping, COMP-branch-A-cmb-boundary-analysis]`. Once Edit 1 flips to incoherent, this `untested` anchor carries an incoherent dependency.
- **Flag for re-eval** (OnAnchorChange chain-propagation concern). Leave to @cth-implementor's judgment — don't auto-flip, but it can't stay silently untested with a dead basis.

## Edit 5 — NEW anchor `WISDOM-algebra-restricts-state-class-not-scalar-field`

Captures the kill + the salvageable redirect (E-3). Proposed JSON:

```json
{
  "id": "WISDOM-algebra-restricts-state-class-not-scalar-field",
  "name": "Algebraic structure restricts the entropy cone via STATE-CLASS, not via the scalar field",
  "tier": 3,
  "status": "coherent",
  "provenance": "T",
  "provenance_kind": "theory",
  "prediction_chain": [],
  "description": "WISDOM (from the killed entropy-cone inversion hypothesis). The intuition that 'more algebraic structure restricts the achievable entropy cone' is CORRECT in mechanism but was mis-located. Changing the SCALAR FIELD up the Cayley-Dickson tower (ℂ→ℍ) does NOT shrink the cone — multipartite ℍ-QM either collapses to ℂ-QM (via the complex projection / Moretti-Oppio) and so violates MMI like ℂ-QM, or, in its genuinely-quaternionic regime, reaches super-Tsirelson (PR-box) correlations and so ENLARGES the cone. Where entropy-cone restriction (e.g. MMI / I₃≤0) genuinely arises — holographic states, stabilizer states — it comes from a restricted STATE CLASS (graph/hypergraph structure, RT geometry, stabilizer formalism), not from the underlying number system. Redirect: point 'algebra restricts the cone' energy at state-class structure, not at the division-algebra tower. Killed hypothesis + derivation: analysis/HQM-MMI-derive-or-die-report.md."
}
```

---

## Salvage door left open (for the record, not an edit)
A non-relativistic ℍ-QM evading Moretti-Oppio with a canonical, Poincaré-compatible multipartite construction whose correlation set is provably nested inside ℂ-QM's would reopen the inversion. Nothing in the literature provides this; Moretti-Oppio suggests it collapses to ℂ anyway. Low prior — documented, not silently shut.
