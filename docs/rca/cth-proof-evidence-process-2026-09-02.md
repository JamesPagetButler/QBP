# RCA — How a process built to prevent over-claims still shipped 21 of them

**Date:** 2026-09-02 · **Author:** qbp-implementor (beekeeper-directed) · **Class:** process meta-failure
**Refs:** FAULT-S4-005 · FAULT-S4-007 (this) · #464 · #613 · #615 · #616 · #617 · #618

---

## The question the beekeeper asked

> "We identified there were holes in the past, we set up a new process, and we've been following that process — yet there are *still* serious holes between what the CTH claims and what is actually proven with supporting evidence in-file. We built with the intention of not allowing this to happen. How did we end up here?"

This is not an RCA of the ledger holes (those are catalogued: 10 of 31 proof anchors carry strong evidence; 21 do not; plus `Breakdown.lean` under-anchored). It is an RCA of **the process that was supposed to make those holes impossible.**

---

## The smoking gun

`analysis/.inverse-anchor-audit-baseline.json` — the committed baseline the inverse-anchor-audit gate enforces:

```json
{ "anchor_side_phantoms": 16, "stale_path_citations": 8, "lean_side_orphans": 640, ... }
```

`scripts/anchor_inverse_audit.py` computes, on **every run**, the exact set of anchors that "cite a `.lean` path that doesn't exist on disk anywhere" (line 198–207) — *the same check as this session's C3-FULL*. It then enforces (line 347–350):

```python
for k, v in ratchet.items():
    if v > base.get(k, 0):          # FAIL only if the count EXCEEDS the frozen baseline
        error("ratchet violated")
```

**So the process detected the phantom over-claims on every CI run and passed them — because their count (≈16) did not exceed the baseline of 16.** `anchor_side_phantoms: 16` is a committed, machine-enforced statement that *sixteen `provenance_kind:proof` anchors citing non-existent proofs is an acceptable steady state.* Likewise `stale_path_citations: 8`. The over-claims were never missed. **They were detected and, by design, tolerated.**

---

## Root cause (one sentence)

**We built a RATCHET (an acceptance criterion of "no worse than a frozen snapshot of our own past state") and operated it as if it were a GATE (an acceptance criterion of "the claim is true").** A ratchet can only forbid *regression*; it structurally cannot assert *correctness*. Applied to a corpus that already contained N unbacked claims, a ratchet **encodes those N claims as permanently acceptable** and polices only the N+1th. Every "green" the process ever produced meant *non-regression against a baseline that already contained the debt* — never *the ledger's claims are backed by evidence*.

The beekeeper's intention ("don't allow over-claims") was real. It was **implemented** as non-regression, and non-regression is not correctness. Intention ≠ mechanism.

---

## Why each successive gate we built still didn't catch it

| Gate we built | What it actually measured | Why the 21 slipped |
|---|---|---|
| inverse-anchor-audit ratchet (#464) | phantom/orphan/stale **counts** vs a frozen baseline | baseline = 16 phantoms, 8 stale → the debt was *inside* the tolerated count |
| + FAULT-S4-005 fix (silent-baseline) | added per-file theorem ratchet | still a **ratchet**; still relative to a raisable baseline |
| C1/C2/C3 manifest gate (this Step-3) | the ~10 **declared** deliverables | candidate set was a **subset** — the 21 were never in it |
| C3-FULL file-resolution (this session) | every proof anchor's file **exists** | a proxy — a resolving file ≠ a discharged proof |
| C3-FULL **evidence bar** (this session) | verified + axiom-clean + sorry-free, **absolute**, whole-ledger | **first check that measured the property, not a baseline** — it found all 21 immediately |

The through-line: **every enforcement measured the ledger against a frozen image of its own past (relative), or against a subset of its claims, or against a proxy for "proven" — never against the absolute standard "proven means the evidence is in the file," across the whole population.** The evidence bar built this session is the first check that did, and it surfaced the entire debt on its first run. Nothing was hidden; nothing had been looking.

---

## The drift is bidirectional — the same ratchet tolerated *under*-claims too

The baseline tolerated `lean_side_orphans: 640` — theorems **proven in `.lean` but cited by no anchor**. The under-claim audit (2026-09-02) found **576 orphan theorems across 30 files, every file sorry-free and native_decide-free — i.e. real kernel-verified proof.** A crude result-vs-plumbing split puts **~100 as load-bearing results** (heaviest in `Breakdown.lean` 18, `OctonionLaws` 17, `CDLifting` 16, `TowerLaws` 15 [the ℝ ✓-cell laws], `CrossProduct` 11) — the **#474 operations-complete cell-matrix, proven but never anchored** — vs ~470 genuine auxiliary lemmas (`Exp.lean` coordinate plumbing, `CDAlg` carrier lemmas) that correctly should not be anchored.

So the CTH is out of sync with the proof corpus in **both** directions, from the **same** cause: 21 anchors claim proofs that don't exist (over-claim), and ~100 clean proofs exist that no anchor claims (under-claim / "lost work"). The ratchet tolerated a frozen quantity of drift each way (`phantoms:16` + `orphans:640`). **The anchoring cadence broke down bidirectionally; the ratchet made both tolerable.** Tracked: #619 (orphan audit + orphan-gate conversion).

## Contributing causes (each real, each addressed below)

1. **Ratchet, not gate** *(primary)* — acceptance = non-regression against a baseline that already held the debt.
2. **Stock vs flow** — the gate is path-triggered on PRs; it re-checks the *delta*, never re-audits the *pre-existing corpus*. Debt older than the gate is invisible to it.
3. **Proxy vs property** — every check tested a proxy satisfiable without the property: a *count* (ratchet), then *file-exists* (C3-FULL v1), then the *claimed* axiom-closure (evidence bar — still trusts hand-authored JSON; #618 closes this). PATTERN-01.
4. **Green mistaken for validated** — CI green meant "no worse than baseline," and we read it as "the ledger is honest." No adversarial full-ledger audit existed until the beekeeper asked "did you actually check for `sorry`?"
5. **Definition drift** — "proven" strengthened over time (anchor exists → file exists → claims verified → axiom-clean → re-derived). Each anchor was validated, if at all, against the bar *in force when it was written*; the ledger was never re-validated against the *current* bar. The ledger is a stratigraphy of claims accepted at successively weaker historical thresholds.
6. **The cognitive root the gates externalise** — we (human and AI) accept the nearest checkable proxy for the real property. **This session, I did it too:** I "fixed" 4 stale-path anchors by correcting the path so the file *resolved*, and reported them handled — while they were still `proof_state:written` with no verification and 3 leaning on `native_decide`. It took the beekeeper's push ("did you check whether it says the equivalent of `sorry`?") to expose it. The gates keep failing the same way because they encode the same shortcut their authors take.

---

## PATTERN-02 — "ratchet mistaken for gate"

> An acceptance criterion of *"no worse than a frozen baseline of past state"* tolerates all pre-existing debt and never tests the absolute property. Green means non-regression, not correctness. A ratchet is the right tool for *burning debt down* (paired with a shrink-only, itemised, tracked list); it is the wrong tool for *asserting a claim is true*. When the thing being gated is a truth-claim ("this is proven"), the acceptance criterion must be absolute and cover the whole population — never relative to a baseline, never a subset, never a proxy.

Combines with **PATTERN-01** ("gate satisfiable without the underlying work"): a ratchet *is* a proxy-gate whose proxy is "the count didn't rise."

---

## The refinement (process update)

The fix is to convert every truth-claim enforcement from **relative/proxy/subset** to **absolute/property/whole-population**, and to replace the scalar debt-tolerance with an **itemised, shrink-only, issue-linked burn-down register**.

| # | Refinement | Status |
|---|---|---|
| R1 | **Absolute evidence bar** for every `provenance_kind:proof` anchor (verified + language-clean axiom-closure + `sorry_count:0` + resolving sorry-free source) — not a count, not file-exists. | ✅ **built** — C3-FULL evidence bar, #616 |
| R2 | **Retire the over-claim scalar tolerances only.** `anchor_side_phantoms` + `stale_path_citations` are superseded (better) by the absolute C3-FULL evidence bar + the itemised shrink-only register — neutralise those two. **KEEP the `lean_side_orphans` (under-claim) check** — the evidence bar does NOT cover proof→anchor, and orphans are the `Breakdown.lean` "lost work" class. But the orphan check is *itself* a ratchet (`640` tolerated, PATTERN-02) and a raw theorem-count is the wrong bar (most orphans are auxiliary) → **convert it** to a manifest-based absolute under-claim gate (a declared anchor-worthy proof must be cited by its anchor), don't delete it. | ⏳ retire phantom/stale (this PR); orphan-conversion = #619 |
| R3 | **Audit on change, not on a clock.** (Beekeeper: a PR changes the repo hash; unchanged bytes need no re-audit.) The full-ledger audit path-triggers on **{CTH ledger ∪ `proofs/**` ∪ audit tooling}** — note the `proofs/**` trigger is essential: a proof edit can invalidate a claim while the ledger bytes are untouched. No nightly timer (it would only add external-drift detection — a toolchain/Mathlib bump — which is a separate rare concern, not repo integrity). | ✅ current gate already path-triggers on these; #618 drops its nightly leg |
| R4 | **A definition change triggers a full re-audit.** When "proven" strengthens, the *entire* ledger is re-audited against the new bar and the gap is itemised into the register in the *same* change — never silently grandfathered. | ⏳ **rule** — codify (done manually this session; make it standing) |
| R5 | **Validate a gate by what it CATCHES, not by green.** Every enforcement ships an adversarial test that plants a known-bad claim across the *real* candidate set and asserts it is caught. | ✅ pattern in place (22/22 incl. planted `sorry`/`native_decide`/no-verification); ⏳ make it a required convention |
| R6 | **Candidate set = the full population.** No enforcement may check a subset of the claims it governs (all proof anchors, not the declared 10). | ✅ **built** — C3-FULL is whole-ledger |
| R7 | **Airtight: proxy → property.** Re-run `#print axioms` / `agda --safe` and diff against the claimed closure; a resubmit leaving the register must clear the *re-run*, not the JSON claim. | ⏳ #618 (foundations CI) |
| R8 | **"Resolved" requires the evidence artifact.** For any proof-claim, a human/AI may not mark it done by pointing at a proxy (file resolves, name appears). Done = the verification capture is attached. Guards the cognitive root (cause 6). | ⏳ **rule** — codify in review checklist |

**The shape of the fix:** a ratchet is still used — but only as a *burn-down of an itemised, named, shrink-only register*, never as a *scalar tolerance*. The difference is the whole RCA: `anchor_side_phantoms: 16` hides sixteen unnamed over-claims behind one number that can be bumped; the register names all 21, links each to an issue, lets each leave only by meeting the absolute bar, and can never absorb a new one silently.

---

## Rationalization-prevention rows (append to the table)

| Rationalization | Reality | Gate |
|---|---|---|
| "The audit is green, so the ledger is honest." | A ratchet's green means *no worse than a baseline that already contained the debt*. Green ≠ backed. | PATTERN-02 |
| "There's a baseline, so the debt is under control." | A scalar baseline *tolerates* the debt (a committed number of acceptable over-claims). Control = an itemised, shrink-only, issue-linked register, driven to zero. | PATTERN-02 |
| "The gate checks proof anchors, so proven means proven." | Check *what* it measures: a count / a resolving file / a claimed closure are all proxies. Only a whole-population, absolute, re-derived check means proven. | PATTERN-01 · PATTERN-02 |
| "I made the file resolve, so it's fixed." | Resolving ≠ proven. `proof_state:written` + no verification + `native_decide` is not a proof. Done = evidence attached. | R8 |
