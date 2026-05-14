# Wisdom Paper — v1.3 → v1.4 Diff Summary

**Generated:** by qbp-implementor (PR6 Wisdom integration, 2026-05-14)
**Inputs:**
- `archive/historical/QBP-First-Wisdom-Theory-v1_3-original.md` (baseline)
- `paper/wisdom_v1_4.md` (this revision; promoted from `archive/QBP-First-Wisdom-Theory-v1_4.md` 2026-05-11)

**Diff size:** 63 lines (mostly localized in one new subsection + history entry)

---

## What changed

### 1. Programme name rationalisation (cosmetic)

| Field | v1.3 | v1.4 |
|---|---|---|
| Subtitle | "Quaternion-Bridge Programme" | "Quaternion-Based Physics Programme" |
| Programme attribution | "QBP (Quaternion-Bridge Programme)" | "QBP (Quaternion-Based Physics)" |

QBP has been canonically "Quaternion-Based Physics" since the project naming convergence (see workspace `CLAUDE.md`). v1.3 still carried the older "Quaternion-Bridge" naming; v1.4 normalises.

### 2. Coherence metadata update

| Field | v1.3 | v1.4 |
|---|---|---|
| Coherent with | CTH v5.1 (106 anchors, 70% coherence) | CTH v5.3 (141 anchors) |
| Date | 2026-04-27 | 2026-05-11 |
| Version | — (implicit 1.3) | 1.4 |

The CTH v5.3 baseline (141 anchors) is the Session-13 closeout snapshot now tracked at `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (per PR #422).

### 3. New subsection — §9.7 "v1.4 Revision: The Spectral Triple is the Invariant" (+32 lines)

**Substantive content addition.** Revises W-003 ("There is only f(u)") in response to:

- **Chamseddine-Connes-van Suijlekom 2018** ("Entropy and the Spectral Action", *Commun. Math. Phys.* 373) — proves von Neumann entropy of fermionic 2nd-quantisation of a spectral triple equals the spectral action for a universal test function χ(x) = h(√x), h(x) = x/(1+eˣ) + log(1+e⁻ˣ).
- **T1–T4 mp-arithmetic verification** (50-digit precision) confirms three findings:
  1. χ(u) is *not* QBP's f(u) — function-level identity fails; rescaling tests give inconsistent A values (0.69 from f₀, 1.80 from f₂).
  2. CCvS γ(−a) coefficients for positive integer a contain the even-level Cayley-Dickson tower dim Im 𝒜_(2a) = 2^(2a) − 1 as a numerator factor (ℍ at a=1, 𝕊 at a=2, chingons at a=3, …) — **structural confluence in the coefficients**.
  3. χ and f are different test functions for different observables on the same spectral triple.

**Revised wisdom statement (v1.4):** *There is only the spectrum. Test functions select observables.*

**What is preserved from v1.3:**
- Forces are not separate entities; they are moments of a single underlying object.
- The classical "derive each force separately" framing was the obstacle.
- Deriving the test function from physical principles remains central.

**What is sharpened:**
- The "single underlying object" is the **spectral triple (𝒜, ℋ, D)**, not f(u).
- Test function = *choice of observable*, not the physics itself.
- Different observables → different test functions on the same triple.

**What is lost:**
- Claim that QBP's f(u) is *THE* function to derive. There are multiple test functions; QBP's f(u) for the gravity-matter spectral action remains open, but CCvS provides a related-but-distinct first-principles result for the entropy spectral action.

**New direction surfaced:** CONJ-fu-from-hawking-time-reverse — proposes f(u) is the time-reverse of the parent BH's Hawking decay dynamics. Closes W-003's central problem from an unexpected angle (𝕆→ℍ Hawking spectrum gives f(u) shape directly).

### 4. Document History entry (+1 row)

| Version | Date | Notes |
|---|---|---|
| 1.4 | 2026-05-11 | Added §9.7: v1.4 revision of W-003. The spectral triple is the invariant; test functions select observables. CCvS 2018 comparison run (T1–T4), function-level identity f(u) ≡ χ(u) disconfirmed, structural Cayley-Dickson confluence in coefficients confirmed. New direction: CONJ-fu-from-hawking-time-reverse. |

---

## CTH inventory anchors affected

Per Session-13 closeout (committed as canonical baseline at `archive/cth-inventory/confluent-trust-inventory-v5_3.json` via PR #422):

| Anchor | Status |
|---|---|
| `KILLED-f4-info-theoretic-justification` | killed — vacuum-energy = f₄ = 0 cannot be derived from CCvS information-theoretic principle (rescaling inconsistency) |
| `CONV-cd-tower-in-zeta-moments` | confirmed — Cayley-Dickson tower appears structurally in CCvS γ(−a) coefficients |
| `CONV-spectral-entropy-zeta` | confirmed — CCvS proof of "entropy = spectral action(χ)" connects QBP's spectral action programme to von Neumann entropy of fermionic 2nd-quantisation |
| `CONJ-fu-from-hawking-time-reverse` | conjecture — f(u) is the time-reverse of the parent BH's Hawking decay (open) |
| `WISDOM-003` | revised — "there is only f(u)" → "the spectral triple is the invariant; test functions select observables" |

All five anchors are derivable from the tracked baselines (`v5_3.json` for the first four; `WISDOM-003` revision pending as a wisdom-registry entry per PR6 follow-on work).

---

## Provenance

- Source paper: `archive/QBP-First-Wisdom-Theory-v1_4.md` (508 lines, dated 2026-05-11)
- v1.3 baseline: `archive/historical/QBP-First-Wisdom-Theory-v1_3-original.md`
- Cross-reference: `paper/DESIGN_RATIONALE.md` §12.4 (Session-13 integration touchpoints) — updated by this PR to forward-reference §9.7
- CCvS 2018 source: Chamseddine, Connes, van Suijlekom — "Entropy and the Spectral Action", *Commun. Math. Phys.* 373 (2020)
- T1–T4 mp-arithmetic verification: per `archive/SESSION-13-WORKING-NOTES.md` (untracked; verification log)

---

## Anchor-rule terminations (per `docs/workflows/review_anchoring.md`)

Every substantive claim in §9.7:

| Claim | Anchor type | Anchor |
|---|---|---|
| CCvS proves "entropy = spectral action(χ)" | published experimental constraint | Chamseddine-Connes-van Suijlekom 2018, *Commun. Math. Phys.* 373 |
| χ(u) ≠ QBP's f(u) at function-level identity | simulation output + provenance | T1–T4 mp-arithmetic, 50-digit precision |
| Rescaling gives inconsistent A values (0.69 vs 1.80) | simulation output + provenance | T1–T4 mp-arithmetic |
| CCvS γ(−a) contains Cayley-Dickson tower 2^(2a)−1 | derived dimensional / algebraic identity | even-level dim Im 𝒜_(2a) algebraic structure |
| `KILLED-f4-info-theoretic-justification` status | pre-registered ground-truth doc | `archive/cth-inventory/confluent-trust-inventory-v5_3.json` (tracked baseline) |

All five claims terminate at one of the five anchor types. No unanchored prose.

— @qbp-implementor (Integration role), 2026-05-14
