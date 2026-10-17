/-
  QBP.Cosmo.FanoChoiceInformation — Fano-line selection costs exactly ln 7 nats
  ============================================================================

  Backing file for the CTH anchor `PROOF-fano-choice-information`
  (`fano_choice_information`).

  Claim (from the CTH inventory):
    Information-cost identity `log(numFanoLines) = log 7`.  Bridges the
    combinatorial Fano result (`FanoGenesis.fano_lines_count`: exactly 7 lines)
    to the entropic threshold used for the seed mass (`S_BH = ln 7`, see
    `SeedMass.lean`).  The crystallisation threshold and the Shannon information
    of a uniform 7-way choice are the SAME number — by construction.

  ── WHAT IS PROVEN (honesty boundary) ───────────────────────────────────────
  The left-hand side `log (numFanoLines)` is NOT a bare `log 7`: `numFanoLines`
  is defined as `FanoGenesis.fanoLines.length`, and the identity is discharged by
  rewriting with the genuine combinatorial theorem `fano_lines_count`
  (`fanoLines.length = 7`, proved in `FanoGenesis.lean` from the explicit list of
  lines).  So the theorem genuinely connects the proven 7-line count to the
  entropy base `log 7`; it is not the vacuous `log 7 = log 7`.

  This is a pure-mathematics identity (a `Real.log` fact about a proven cardinal),
  so it is honestly a `proof`, not merely a `derivation`.

  Completeness: zero `sorry`, zero `native_decide`, zero vacuous `True`.
  `#print axioms` audit at the bottom.

  ── INTERPRETATION (#539 ruling, 2026-06-12; annotated per #550) ────────────
  `S = ln 7` is GAUGE-FIXING information, NOT a physical genesis entropy.
  Strategy B (#548, `basisAuto_transitive_on_triples`) proved that the 7
  Fano-line quaternion subalgebras form a single Aut(𝕆) orbit, so "which of
  the 7 lines" is an unobservable gauge choice (one labeling among the 7
  orientations/labelings related by the basis automorphisms).  The number
  `log 7` is therefore the bookkeeping cost of fixing that gauge — the
  Shannon information of naming one orbit representative — and the theorems
  below remain true and useful as the combinatorial bridge to `SeedMass.lean`.
  What they do NOT establish is that `ln 7` is a physical selection entropy.
  Per the #539 ruling, a physical genesis entropy must be reformulated in terms
  of the symmetry-breaking structure itself (the quotient `G₂ / Stab`, i.e. the
  stabiliser-pinning programme), not the count of gauge-equivalent labels.
  Nothing is deleted here (forensic trail): the identity stands as proven; its
  reading as "physical selection information" is withdrawn.
  Cross-refs: issue #539 (ln-7 theory ruling), issue #548 (Strategy-B gauge
  result), issue #550 (this annotation).
-/
import QBP.Foundations.FanoGenesis
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace QBP.Cosmo.FanoChoiceInformation

open QBP.Foundations

/-- **The number of Fano lines**, taken from the combinatorial construction in
    `FanoGenesis.lean` — NOT a hard-coded `7`. -/
def numFanoLines : ℕ := FanoGenesis.fanoLines.length

/-- The Fano-line count is exactly 7 (re-exported from `fano_lines_count`, which
    proves it from the explicit 7-element list of lines). -/
theorem numFanoLines_eq_seven : numFanoLines = 7 := FanoGenesis.fano_lines_count

/-- **Information-cost identity: `log (numFanoLines) = log 7`.**
    Plain reading: the Shannon information of a uniform choice among the Fano
    lines equals `log 7`, because the *proven* number of Fano lines is 7.  The
    left side is `Real.log` of the combinatorial count `fanoLines.length`, tied
    to `7` through `fano_lines_count` — this is the genuine bridge from the
    combinatorics to the `ln 7` threshold.

    **Interpretation (#539 ruling / #550):** this `log 7` is *gauge-fixing*
    information — the 7 lines are one Aut(𝕆) orbit (#548), so the choice is
    unobservable gauge — and NOT a physical genesis entropy; see the file
    header. -/
theorem fano_choice_information :
    Real.log (numFanoLines : ℝ) = Real.log 7 := by
  rw [numFanoLines_eq_seven]
  norm_num

/-- **Natural-log form (nats):** the same identity spelled as the seed-mass
    threshold `ln 7`.  This is definitionally `fano_choice_information` (Mathlib's
    `Real.log` is the natural logarithm), recorded to make the bridge to
    `SeedMass.S_BH_at_M_seed_log_seven` explicit: the crystallisation threshold
    `S_BH = ln 7` equals the information cost of selecting one of the 7 Fano
    lines.

    **Interpretation (#539 ruling / #550):** that "information cost" is the
    gauge-fixing bookkeeping cost of naming one of 7 gauge-equivalent labels
    (#548), not a physical entropy; the physical genesis entropy is to be
    reformulated via the symmetry-breaking structure `G₂ / Stab` (#539). -/
theorem fano_choice_information_nats :
    Real.log (numFanoLines : ℝ) = Real.log 7 := fano_choice_information

/-! ## Completeness audit — `#print axioms` -/

#print axioms numFanoLines_eq_seven
#print axioms fano_choice_information
#print axioms fano_choice_information_nats

end QBP.Cosmo.FanoChoiceInformation
