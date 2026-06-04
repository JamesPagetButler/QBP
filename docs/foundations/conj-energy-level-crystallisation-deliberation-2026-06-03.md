# CONJ-crystallisation-energy-level-equilibrium — Theory-Team Deliberation Brief

**Date:** 2026-06-03
**Status:** NASCENT / UNTESTED — provenance T (theory-generative, beekeeper-proposed)
**Convened by:** Oppenheimer (QBP strategic lead)
**Reviewers:** Gemini Theory Team (Furey, Feynman) + Claude Counter-Team (Wilson, Jaynes)
**Gate note:** This is generative deliberation, NOT a Tier-3 gate review. Any artifact
that hardens out of this (ontology doc, Lean target, CTH anchor) gets its own Tier-3
cycle per FAULT-S4-001 remediation.

---

## 1. The conjecture (beekeeper's formulation, verbatim intent preserved)

> "The substrate crystallizes to level n; the tower is defined down to that level;
> you can do physics up until the 'energy level' gets too high, which breaks the
> crystallization; you go up a level; those physics apply; it cools back down;
> it recrystallizes you back down at level n."

**Restated:** Crystallisation is not a one-shot cosmological event but a **general,
reversible, level-indexed, energy-parameterised dynamic** on the Cayley-Dickson tower:

```
   high energy
       ▲   MELT: energy exceeds level-n binding → structure law breaks
       │   → climb to level n+1 (more algebra, fewer laws)
   ────┼──── level n: tower crystallised down to here; physics valid HERE
       │   FREEZE: energy cools → re-crystallise → drop back to level n
       ▼
   low energy
```

- Each Cayley-Dickson rung (ℝ→ℂ→ℍ→𝕆→𝕊) is an **energy regime**, not just a
  mathematical level.
- "Physics at level n" is valid below level-n's decrystallisation energy.
- The structure-loss ladder (order→ℂ, commutativity→ℍ, associativity→𝕆,
  alternativity/division→𝕊) and the energy axis are **the same arrow**.

## 2. Existing QBP material this generalises (grounding evidence)

1. **QBP-HYPOTHESIS-Holographic-Boundary §2.4.2:** "At the extreme gravitational
   compression of black hole collapse... the associative structure breaks down...
   transition to the octonionic (𝕆) regime... The octonions are not a higher level
   of physics. They are the liminal algebra — the threshold between universes."
   → This IS the melt/up-leg, documented for one transition (ℍ→𝕆 at BH collapse).
2. **§2.4.3:** white-hole-side expansion → cooling → ℍ′ crystallises.
   → This IS the freeze/down-leg, documented once (Big Bang).
3. **DERIV-crystallisation-asymptotic (CTH anchor):** "Time IS crystallisation;
   constants converge asymptotically, never freeze."
   → Supports *ongoing/propagated* crystallisation: the system continuously
   re-freezing at level n, not a completed event.
4. **SeedMass.lean:** M_seed = √(ln7·ℏc/4πG) — the one quantitative threshold QBP
   currently has (genesis/ℍ↔𝕆 scale).

The conjecture promotes the documented one-shot ℍ→𝕆→ℍ′ cycle to the **generic
behaviour at every rung**.

## 3. The four questions for deliberation

### Q1 — Binding energy ladder (quantitative content)
What is the binding energy of level n, as a number? Does M_seed = √(ln7·ℏc/4πG)
generalise to a per-rung threshold ladder E(n)? If the model is physical, every
rung needs a threshold, and the thresholds should connect to known scales
(electroweak ~246 GeV, QCD deconfinement, GUT, Planck). If no number is derivable
even in principle, the conjecture is a picture, not physics. What would the
derivation strategy be?

### Q2 — Arrow direction (the entropy-cone lesson)
Standard high-energy physics RESTORES symmetry (electroweak unification, QCD
deconfinement): up in energy = more symmetric. The conjecture says up in energy =
up the tower = LOSE structure (associativity, etc.). Are these compatible?
Candidate reconciliation: structure-loss = automorphism-group GROWTH
(Aut(ℍ)=SO(3), Aut(𝕆)=G₂, dim 3→14), so "fewer laws" = "more symmetry."
**Check this rigorously** — does the automorphism ladder actually grow monotonically
up the tower, including the 𝕆→𝕊 step? (Aut(𝕊) is known to be G₂ × S₃-related —
does the pattern hold or break there?) This is exactly the failure mode that killed
the entropy-cone hypothesis (assumed the arrow direction, reality pointed the
other way). Do NOT assume; derive or refute.

### Q3 — Reversibility and re-selection
Big-Bang crystallisation SELECTED one of 7 Fano quaternionic subalgebras
(symmetry-breaking choice; G₂ acts transitively, 480 orientations). If a region
melts to 𝕆 and refreezes, does it necessarily land in the SAME subalgebra
(same physics constants), or can it re-select (domain-wall / different-constants
regions)? Either answer has consequences:
- Always-same → need a memory mechanism (what stores the selection through the melt?)
- Can-differ → predicts constant-discontinuity domains; connects to Smolin
  cosmological natural selection (already cited in the hypothesis doc); possibly
  observable.

### Q4 — The seam (process-architectural, NEW)
QBP just defined a foundation↔physics separation: foundation = numbers + operations
(ground truth: Lean kernel); physics = predictions (ground truth: experiment).
This conjecture is a PHYSICS claim (energy thresholds, testable) that REINTERPRETS
the FOUNDATION (tower rungs = energy regimes). Concretely for the Lean file split:
- Does the tower stay purely foundational (algebra, no energy semantics), with the
  energy-indexing living entirely in physics files that IMPORT the tower?
- Or does the conjecture imply foundation-side structures (e.g., a "crystallisation
  state" parameter on the tower) that would blur the split?
- Recommended seam design so foundation proving (Oppenheimer + lean-prover) and
  physics work can proceed without blocking each other on this conjecture.

## 4. Constraints on the deliberation

- The conjecture is NASCENT. The deliverable is NOT accept/reject; it is:
  (a) per-question assessment (TRACTABLE / NEEDS-WORK / FATAL-IF-TRUE),
  (b) sharpest known objection,
  (c) cheapest discriminating test or derivation,
  (d) recommendation on registration status (register-as-conjecture / hold / drop).
- Honest negative results are preferred over elegant accommodation. The foundations
  rebuild exists because "elegant + useful" was mistaken for "proven."
- Counter-Team (Wilson, Jaynes): your job is to attack. Wilson: renormalisation/
  effective-field-theory lens — is "level-n physics below threshold E(n)" just EFT
  restated, and if so what does the conjecture add? Jaynes: information-theoretic
  lens — what would distinguish this from a re-description with zero new predictive
  content?
- Theory Team (Furey, Feynman): Furey — algebraic structure, division-algebra
  particle content, automorphism ladder rigor. Feynman — physical mechanism,
  what experiment could ever see this, simplest formulation.

---

## 5. DELIBERATION OUTCOME (2026-06-03, sequential: Counter-Team → Theory Team)

### 5.1 Verdict matrix

| Q | Counter-Team (Wilson/Jaynes) | Theory Team (Furey/Feynman) | Converged? |
|---|---|---|---|
| Q1 energy ladder | NEEDS-WORK (numerology-prone; M_seed tautological) | NEEDS-WORK (derivation strategy exists: S² selection entropy) | ✅ NEEDS-WORK |
| Q2 arrow direction | **FATAL-IF-TRUE** (Aut(𝕊) stall) | FATAL for automorphism analogy; TRACTABLE if pivot to zero-divisor entropy | ⚠️ analogy dead, pivot proposed |
| Q3 memory/re-selection | NEEDS-WORK→VACUOUS (both branches lose) | TRACTABLE via localized melts + epitaxial boundary recrystallisation | ⚠️ reformulation proposed |
| Q4 Lean seam | TRACTABLE: foundation purely algebraic | TRACTABLE: concur, "physics instantiates the algebra; it does not redefine it" | ✅ **UNANIMOUS** |
| Registration | REGISTER-AS-CONJECTURE, hard NASCENT, zero foundation footprint | REGISTER-AS-CONJECTURE, same conditions + explicit Aut(𝕊)-stall admission | ✅ UNANIMOUS |

### 5.2 Key findings

**FINDING 1 — The automorphism reconciliation is DEAD (Counter-Team kill, Theory
Team concession).** Aut(𝕊) ≅ Aut(𝕆) × S₃ ≅ G₂ × S₃ (Eakin–Sathaye 1990; Wilson
verified vs literature; Gemini marked UNVERIFIED — needs independent citation check
if conjecture proceeds). Continuous-symmetry dimension ladder: 0, 0, 3, 14, **14**.
It stalls at exactly the 𝕆→𝕊 rung — maximum structure loss, zero new continuous
symmetry. "Fewer laws = more symmetry" is false at the decisive rung. Additionally
(Wilson): Aut(coefficient algebra) is categorically different from the dynamical/gauge
symmetry physics restores at high energy — verbal analogy, not structural; no order
parameter, no critical temperature.

**FINDING 2 — Proposed pivot: zero-divisor entropy as the energy-conjugate
(Furey).** Replace automorphism dimension with the measure/dimensionality of the
zero-divisor structure (𝕊's norm-1 zero divisors form a 14-dim manifold ≅ G₂ —
consistent with Moreno 1998 already in the corpus). Up-leg = transition into
zero-divisor-dominant regime.
**Oppenheimer caveat (unresolved):** this quantity is 0 at ℝ, ℂ, ℍ, 𝕆 (all
division algebras — no zero divisors anywhere below 𝕊) and only becomes nonzero at
𝕊. A ladder that is flat-zero through four rungs is not an arrow either — the pivot
fixes the stall at the top and breaks monotonicity at the bottom. The correct
invariant, if one exists, must distinguish ℝ from ℂ from ℍ from 𝕆 AND keep growing
into 𝕊. Neither team produced one. **This is the open core of Q2.**

**FINDING 3 — Memory-through-the-melt reformulation: epitaxial holographic
recrystallisation (Feynman).** Jaynes's dilemma (always-same branch: no carrier can
survive a regime defined as absence of causal ordering; can-differ branch:
α-variation surveys show no spatial domain walls at 10⁻⁵–10⁻⁶) is answered by
constraining the conjecture: **melts are always local and bounded**, embedded in an
unmelted bulk; on cooling, the region crystallises *epitaxially from the boundary
inward*, forced into the bulk's Fano selection. The memory lives in the unmelted
boundary, not in the melt — consistent with (and reinforcing) the existing
holographic-boundary hypothesis. Kills the α-domain-wall falsification because no
walls are predicted. Cost: the conjecture loses its only would-have-been-observable
signature; new observability channel needed (Jaynes's zero-new-content audit still
bites unless Q1 produces a number).

**FINDING 4 — Q1 derivation target (both teams).** Derive E(ℍ→ℂ) by the same
entropy-cost-to-energy bridge as M_seed with NO new free parameter: the cost of
selecting one imaginary axis from the S² of quaternionic imaginaries (continuous
selection entropy), set S_BH(M) equal to it, see where the mass lands. If it lands
near a known scale unprompted → first non-tautological number. If not → "it is a
picture, not physics" (Wilson). This is the cheapest discriminating computation and
the conjecture's make-or-break.

**FINDING 5 — Q4 SETTLED, UNANIMOUS, both lenses independent.** Foundation Lean
files (Foundations/, tower, operations matrix) stay **purely algebraic — zero
energy/crystallisation semantics in types or theorems** (physics gestures allowed in
doc-comments only). All energy-indexing lives physics-side in files that IMPORT the
tower (e.g. a `CrystallisationRegime` structure referencing tower truncations).
Wilson: don't bolt a possibly-fatal physics claim onto the kernel-truth layer.
Jaynes: mixing a likelihood-bearing claim into the certainty-bearing layer is an
evidential category error — it would let conjecture inherit kernel credibility by
file-adjacency. Feynman/Furey: "Physics instantiates the algebra; it does not
redefine it. Keep the math pure."

### 5.3 Registration decision

**REGISTER-AS-CONJECTURE** (unanimous, 4 personas + 2 independent argument lines),
conditions:
- Hard **NASCENT / CONTESTED** tag; explicit admission of the Aut(𝕊) stall in the
  registration text.
- **Zero foundation footprint**: no CTH anchor minting, no Lean target, no
  Foundations/ changes until the open core (Finding 2 caveat) and Q1 number exist.
- The fork it generates is productive: two crisp, cheap, near-term-decidable
  questions — (a) the E(ℍ→ℂ) S²-entropy computation; (b) the monotone invariant
  that distinguishes all five rungs.

### 5.4 Standing obligations out of this deliberation

| # | Obligation | Owner | Status |
|---|---|---|---|
| O1 | E(ℍ→ℂ) derivation via S² selection entropy, zero free parameters | theory teams (commission when beekeeper green-lights) | OPEN |
| O2 | Find the monotone five-rung invariant (or prove none exists ⇒ arrow dies) | theory teams | OPEN |
| O3 | Independent citation check: Aut(𝕊) ≅ G₂ × S₃ (Eakin–Sathaye 1990) | QBP-Herschel / lit task | OPEN |
| O4 | Working-ontology doc v0.1 records the conjecture as NASCENT with this deliberation linked | Oppenheimer | OPEN |
| O5 | Foundation↔physics Lean seam: adopt Finding 5 as the split rule | Oppenheimer + qbp-implementor | **READY TO ADOPT** |
