# `qbp-kz-g2` round 1 (ex `mdcu-kz-r2`): pre-registration — DRAFT r3

Status: **DRAFT r1 (2026-10-29). Nothing built, nothing run.** Stage-0b-only hysteresis probe, H-first vs H-slow, for the G₂/SO(4) plane-field sigma model. Spike / napkin grade (Go harness on the qbp-compute-unit spike branch, pre-registered). Tracking issue: **QBP#793** (typed `research`). Director: @qbp-oppenheimer. Runner: @antigravity (accepted, mdcu-spike seq 254: "available to build and run it once those exist"). Feasibility: @qbp-cu-implementor. Box-safety: @deming. E-verify: @notary-implementor. Merges (this pre-reg, the record, the write-back): the beekeeper's (QBP lane; mdcu-spike seq 284).

**Approval.** The beekeeper approved `mdcu-kz-r2` onto the inter#224 approved list first-hand in qbp-architecture's session, 2026-10-29 (inter#224 issuecomment-6509361203), and passed the kz line to qbp-oppenheimer as director with its own QBP spike queue (mdcu-spike seq 284). This is that spike, renamed `qbp-kz-g2`, round 1. The predecessor's round-1 records stay in qbp-compute-unit (#92, #93).

**Standing go.** Under the approved-list rule the run go is the director's, not the beekeeper's, once all three hold: (1) a named runner has accepted (done, seq 254; re-confirmed on the frozen text per §8); (2) FROZEN-v1 committed and pushed with its sha256 posted on QBP#793 and every §8 gate ticked; (3) deming has cleared box-safety on the frozen plan. The go message cites all three.

**Binding condition (notary seq 276, arch seq 279).** The H-first prior does not soften the decision rule, which must be able to return H-slow or inconclusive (notary, mdcu-spike seq 276/279).

**Freeze procedure.** When the §8 gates are in, the director commits this body verbatim as `spikes/prereg/qbp-kz-g2-r1-prereg-FROZEN-v1.md`; the only permitted edits are the status block and §8. The sha256 is posted on QBP#793. From the freeze onward no rule, seed range, number or threshold in the file is edited; any change is a new, dated amendment file that cites the frozen one, written before the data it affects.

**Predecessor texts (cited by section throughout, read-only, not edited):**
- `mdcu-kz-prereg-FROZEN-v1.md` (qbp-compute-unit, commit `7ac4ed0`, sha256 `176bdce2bd4544f0f0bac8523ecc04f5a6eb582d603bb2714713fa72fa676a5f`) — "FROZEN-v1" below.
- `mdcu-kz-prereg-FROZEN-v1-amend-1.md` (sha256 `e226da2352ae431ad40d49c582417f1fee0ea715a9ff9163a5d6e7440d26db59`) — "amend-1" below.
- `doc/spikes/mdcu-kz-round1-results.md` (qbp-compute-unit main; #92 `0113bf5`, #93) — "the round-1 record" below. Harness at `c739a62` (`spike/mdcu-xqbp-v2`).

## 1. Question

mdcu-kz round 1 falsified, for this model with this ramp only, the premise "the G₂/SO(4) plane-field sigma model (chordal energy, Model-A dynamics, ramp over [1.5 T_c, 0.5 T_c]) has a continuous ordering transition": Stage 0b at τ_Q = 1600 gave a hysteresis gap of 0.5176 of S_max against the 5 % tolerance (the round-1 record). Two explanations are on file (oppenheimer, mdcu-spike seq 252). This round separates them.

- **H-first:** the transition is genuinely first-order — a two-state coexistence region; the hysteresis gap **saturates to a nonzero value as τ_Q → ∞**.
- **H-slow:** the transition is continuous but τ_Q = 1600 is too fast for Model-A dynamics at L = 16 near T_c — critical slowing down, not thermodynamics; the gap **falls as a power of 1/τ_Q** and drops below the 5 % tolerance at some reachable τ_Q.

**Pre-data prior: H-first favoured.** The order parameter is the projector Π onto the 3-plane, a traceless symmetric tensor, which carries a Landau cubic invariant tr(Π_tl³) — the nematic Q-tensor / RPⁿ⁻¹ class, whose ordering transitions are first-order by that mechanism. Round 1's P5 ("continuous-looking transition", ~60 %) was a recorded miss on exactly this point (the round-1 record, P5 row; oppenheimer seq 257 §3). **The H-first prior does not soften the decision rule, which must be able to return H-slow or inconclusive (notary, mdcu-spike seq 276/279).** §3 is written so that each of its three outcomes is reachable from data alone.

Not asked here: anything about the topology of G₂/SO(4) (π₂ = ℤ₂ point defects), any KZ exponent, any defect count, the S³ null, the −φ² landscape, M1–M3, any CD speed claim.

## 2. Design (Stage 0b only)

**What runs.** The Stage 0b hysteresis protocol of FROZEN-v1 §5, main arm only, at four ramp lengths. No detector, no ladder, no saturation gate, no S³ null, **no Stage 0a re-run**.

**T_c is reused, not re-derived.** T_c = **1.0666**, the midpoint of the steepest-drop pair (T = 0.9973, 1.1359) of round 1's Stage 0a seed-mean S(T) on seeds 5600–5602 (the round-1 record, Evidence table). This round takes that number as a fixed input. Any re-derivation of T_c is out of scope; if a later round wants a T_c on more seeds or a finer grid, that is a new pre-registration. Consequences: T_hi = 1.5 T_c = 1.5999, T_lo = 0.5 T_c = 0.5333 (units of J), common-grid spacing T_c/40 = 0.026665.

**Ramp set.** τ_Q ∈ {1600, 3200, 6400, 12800} (three doublings, 0.90 decades). τ_Q = 1600 is the round-1 value and is the reproduction rung (P4).

**Lattice.** L = 16, periodic, as in round 1 (the probe chose L = 16; FROZEN-v1 §6). No L revision.

**Seeds.** 10 seeds per τ_Q, **one fresh seed per (τ_Q, seed)**, proposed block **5900–5939**: seed = 5900 + 10·i + j for τ_Q index i ∈ {0: 1600, 1: 3200, 2: 6400, 3: 12800} and replicate j ∈ {0, …, 9}. So 5900–5909 run τ_Q = 1600, 5910–5919 run 3200, 5920–5929 run 6400, 5930–5939 run 12800. The block is disjoint from every used range listed below (the nearest used value is 5889); it must stay out of the harness's tests and smokes (those use 12000+/13000+). **The runner lists every used range beside this block in the harness PR, and qbp-cu-implementor and the architect check the list** (§8). Used and reserved ranges, from amend-1 §4/§5 and FROZEN-v1 §7, off limits:

| Range | Use | Source |
|---|---|---|
| 3000–3199 | R3 | FROZEN-v1 §7 |
| 4000–4399, 9960–9969 | R4 | FROZEN-v1 §7 |
| 9100–9979 (scattered; 9970–9979 tests) | tests and probes | FROZEN-v1 §7 |
| 5000–5199 | mdcu-kz main arm (ladder; never run) | FROZEN-v1 §7 |
| 5200–5399 | mdcu-kz S³ null (never run) | FROZEN-v1 §7 |
| 5400–5599 | reserved, split-G₂ round 2 | FROZEN-v1 §7, amend-1 §4 |
| 5600–5629 | mdcu-kz Stage 0 (0a main 5600–5602 used; 0b main 5610–5619 used) | FROZEN-v1 §5, the round-1 record |
| 5630–5649 | saturation fields (used) | amend-1 §4 |
| 5650–5849 | S³ null run tilt seeds | amend-1 §5 |
| 5850–5869 | σ* calibration tilt seeds (used) | amend-1 §5 |
| 5870–5889 | calibration field seeds (reserved, unused) | amend-1 §5 |
| 9930–9949 | probe (η descent test, timing; used) | FROZEN-v1 §6 |
| 12000+, 12300+, 13000+, 13300+ | smokes, unit tests, exploration (free seeds) | amend-1 §4, §5 |
| **5900–5939** | **this round (proposed)** | this file |

**Dynamics — identical to the frozen predecessor, cited not restated.** FROZEN-v1 §2 (model: associative plane P(x) = span(u, v, uv) per site; energy Σ_bonds 3 − tr(Π_P Π_Q); Model A = overdamped Stiefel-projected Langevin on (u, v)); FROZEN-v1 §2a (units J = 1; meaning of T; **step rule**: synchronous gradient step on the Stiefel pair with step η plus Gaussian noise of variance 2ηT per component, then Gram–Schmidt; start state i.i.d. Haar-G₂ planes seeded by the run seed; **η**: round 1's probe fixed η = 0.1 by the frozen T = 0 descent rule on seeds 9930–9934 — **η = 0.1 is reused; the descent test is not re-run**). Stage 0b mechanics as FROZEN-v1 §5 and as implemented in the round-1 harness (`KZStage0bRun`, read from the qbp-compute-unit spike branch; the run binary was `c739a62`):

- per seed: **200 steps at T_hi** (the §2a hold; `KZHoldSteps`), then **cool** over exactly τ_Q steps with T(k) = T_hi − (T_hi − T_lo)·k/τ_Q, then **heat** over exactly τ_Q steps from the cooled end state at the same rate, T(k) = T_lo + (T_hi − T_lo)·k/τ_Q;
- S = ‖(1/N) Σ_x Π_{P(x)} − (3/7) I‖_F normalised by √(12/7), so **S_max = 1** (FROZEN-v1 §2);
- S recorded at step 0 of each branch and after every 10 steps, labelled by the nominal T(k) (τ_Q/10 + 1 records per branch: 161, 321, 641, 1281);
- the seed-mean cool and heat curves are interpolated linearly onto the **common 41-point grid, linear in T over [T_lo, T_hi]**;
- **noise-stream convention:** `KZNoiseRNG(seed, stream)` with the Stage 0b stream constant (100001) — the seed fixes both the Haar start state and the noise stream, as in round 1. Unchanged.

**The frozen Stage 0b clauses, kept as the measurement definitions (not as a pass/fail gate here):** the **5 % gap clause** — |mean S_cool − mean S_heat| ≤ 0.05·S_max at every grid T — and the **10 % jump clause** — no single recorded-step jump of the seed-mean S exceeds 0.10·S_max (FROZEN-v1 §5; `KZStage0bAnalyze`, tolerance slack 1e-12). In this round they feed §3; "premise fails" is not a reading of this round.

**Harness additions required for this round (on the qbp-compute-unit spike branch; reviewed and pushed by qbp-cu-implementor; tests first):**

1. A **Stage-0b-only run mode** that takes T_c (= 1.0666) and the τ_Q list as inputs and never calls Stage 0a, the detector, the saturation check or the ladder; the seed guard refuses every range in the table above except 5900–5939 in this mode, and refuses 5900–5939 in every other mode.
2. **Store the full 41-point cool and heat seed-mean arrays per τ_Q in the raw record** (round 1 kept only `max_gap` and the two jumps — arch's measurement-gap note, seq 253). Also store the common grid itself and, per seed, the per-branch recorded S series (τ_Q/10 + 1 values), so the seed spread can be read later without a re-run.
3. **Put the maximum-gap grid point in the reason/summary string.** Round 1's reason string reported the *last* failing grid point (point 27, 0.0856), not the maximum (0.5176), because the string was overwritten per failing point (the round-1 record, "Reading of the reason string"). The record must carry `max_gap`, its grid index and its T.
4. **Record the max single-step jump per direction** with its grid position. The round-1 code already emits `cool_jump` and `heat_jump` (`KZMaxJump` of each seed-mean branch); this round keeps them and adds the step index and T label of each.
5. Per-τ_Q meta: wall seconds, `load_start`/`load_end`, exit code, pause-file state, binary sha256, code sha.

Everything else in the harness is called, not edited; the bit-identity check on the R2/R3/R4 code paths (FROZEN-v1 §8 item 9) is kept.

## 3. Decision rule (pre-data; frozen verbatim at the freeze)

Let **gap(τ)** = max over the 41 grid points of |mean S_cool − mean S_heat| / S_max at that τ_Q (S_max = 1; this is `max_gap` on the common grid, as in round 1).

- **(a)** gap(12800) ≥ 0.6 · gap(1600) → **H-first**.
  *Claim scope of (a) (director, 2026-10-29):* under a pure power law gap ∝ τ_Q^−α over this 8× span, (a) fires iff α ≤ log(1/0.6)/log 8 ≈ 0.246, so "H-first" here means operationally **"the gap decays no faster than τ_Q^−0.25 over 1600–12800"**; a genuinely first-order gap saturates (α → 0). (b) with gap(1600) ≈ 0.52 needs α ≥ 1.12. The thresholds are unchanged; this sentence fixes what the verdict words claim.
- **(b)** gap(12800) < 0.05 → **H-slow**, and the KZ premise is restored at the **smallest τ_Q in the set with gap(τ_Q) < 0.05** (report that τ_Q; a future ladder would start there).
- **(c)** otherwise → **inconclusive (rate)**.

**Precedence (ruled by the director, 2026-10-29).** The clauses are evaluated in the order **(b), then (a), then (c)**. (a) and (b) can both hold only if gap(1600) < 0.05/0.6 = 0.0833, i.e. only if round 1's 0.5176 is not reproduced (a P4 miss); in that case **(b) governs**: a gap below the frozen 5 % tolerance restores the premise regardless of its ratio to a small gap(1600), and the P4 miss is reported beside it. This makes the rule total and keeps H-slow reachable from data alone.

**Secondary, non-gating:**
- OLS fit of log gap(τ_Q) against log τ_Q over the 4 points; report the slope with its standard error (2 degrees of freedom). A gap of exactly 0 at any rung is reported and excluded from the fit (the fit is then on the remaining points, and labelled so). Under H-first the slope tends to 0; under H-slow it is negative. The slope is descriptive and decides nothing.
- The **jump clause**: a single recorded-step jump of the seed-mean S > 0.10·S_max in either direction at any τ_Q is reported as **"jump observed at τ_Q = …"** (supports H-first) but **does not override (a)–(c)**.
- gap(τ_Q) with the seed spread (per-seed max gap, min/max) at every rung, and the 41-point curves plotted cool vs heat per τ_Q (Human Visual Review material).

**What each outcome does and does not claim** (these are the four outcome rows of the QBP#793 AC2 planning-consequence table, posted on the issue before any data; the AC2 table adds two secondary rows, "jump observed" and "P4 fails", from §3's secondaries and §4, with no rule consequence):

| Outcome | Claims | Does not claim | Write-back (§7) |
|---|---|---|---|
| H-first | For this sigma model (chordal energy, Model A, this window, L = 16), the hysteresis does not close with ramp length over 1600–12800: consistent with a first-order transition. | Nothing about the topology of G₂/SO(4); no KZ exponent; no statement about other energies, dynamics or L; not a proof of first order (a 0.9-decade span cannot exclude slow convergence). | QBP#776 E6 note: the round-1 falsification of "continuous" stands and is sharpened ("not continuous on this rate scale; hysteresis persists to τ_Q = 12800"). KZ ladder on this model stays closed. |
| H-slow | The gap falls below the frozen 5 % tolerance at the reported τ_Q: the round-1 Stage 0b failure was a rate effect, and the KZ premise ("a continuous transition the ramp can cross quasi-statically") is restored for ramps at or above that τ_Q. | Nothing about topology or exponents; no reading of the round-1 E-move being wrong (it was about τ_Q = 1600 and stands as recorded). | QBP#776 E6 note; new research-queue item for a ladder starting at the reported τ_Q (its own pre-reg; beekeeper re-approval, off the approved list).; the Landau-cubic prior is recorded as a second pre-data miss (the QBP#776 E6 note's a-priori expectation is annotated, not "retracted": no H-first row exists there) |
| inconclusive (rate) | The gap falls with τ_Q but neither saturates (per (a)) nor closes (per (b)) within the set. | Either hypothesis. | QBP#776 note recording the four gap values and the slope; any extension to larger τ_Q is a new pre-reg (cost doubles per rung). |
| harness kill (any §5 abort) | Nothing. "harness kill, no reading." | Anything. | None; the abort is recorded on QBP#793. |

## 4. Predictions on file (director's, pre-data)

| # | Prediction | Probability |
|---|---|---|
| P1 | H-first (rule (a) fires) | ≈ 70 % |
| P2 | H-slow (rule (b) fires) | ≈ 15 % |
| P3 | inconclusive (rate) (rule (c)) | ≈ 15 % |
| P4 | gap(1600) reproduces round 1's 0.5176 within ±0.05 on the fresh seeds (i.e. in [0.4676, 0.5676]) | ≈ 85 % |
| P5 | the jump clause fires (> 10 % of S_max) at some τ_Q ≥ 6400, given H-first | ≈ 50 % |

P1–P3 are exhaustive and sum to 100 %. Freeze-check question asked and answered (inter#249 wisdom): does the order parameter admit a cubic invariant? Yes (tr(Π_tl³)) — that is why P1 is the prior, and why the rule in §3 is written so that P2 and P3 remain reachable.

## 5. Kills, aborts and resources

**Aborts (any one → the round reads "harness kill, no reading"; nothing is re-run without a dated amendment):**
- wall > **2 h** → exit 2;
- pause file present at start or at a poll → exit 3 (path as in the round-1 harness: `$HOME/.federation-watcher/box-pause/mdcu`, deming's; the runner confirms or states the path in the harness PR);
- seed guard: any seed outside 5900–5939 in run mode, or any mode other than run mode touching 5900–5939 → exit 4, before any step;
- NaN / non-finite order parameter → exit 6 (round-1 harness convention);
- parity or bit-identity regression check failure on the untouched code paths → exit 4.

**Resource estimate (upper bounds, written before the run):**
- Steps: 10 seeds × 2 branches × (1600 + 3200 + 6400 + 12800) = **480,000 ramp steps** (qbp-cu-implementor seq 263), plus 40 × 200 = 8,000 hold steps = **488,000** steps total. At t_s16 ≈ 6.5 ms (round-1 probe medians via seq 263): 480k → ≈ 52 min; 488k → ≈ 53 min. Round 1's Stage 0 + saturation ran in 1,384 s wall at the same L and η (the round-1 record), consistent with that rate. Headroom to the 2 h cap: > 2×.
- RAM: one 16³ lattice of 14 floats ≈ 0.5 MB plus records; **< 50 MB** (qbp-cu seq 174/184 envelope, FROZEN-v1 §9 item 3).
- Disk: 40 seeds × 2 branches × ≤ 1281 records × ~20 bytes ≈ 2 MB of per-seed series plus the 41-point arrays and meta; **< 5 MB** raw jsonl.
- Kill condition: the run is bounded by construction (fixed step count) **and** by the 2 h wall cap; no open-ended loop exists.
- Load discipline as round 1: **one lattice at a time**, `GOMAXPROCS=1`, core-pinned (`taskset`), `nice -n 19`, quiet-load wait before start, `load_start`/`load_end` recorded in meta (round 1's pre-step `go test` raised `load_start` to 2.01; the runner runs the tests *before* the quiet-load wait this time, and discloses the loads either way).

Feasibility sign (qbp-cu-implementor) binds to the frozen numbers above; it re-opens only if L > 32, GOMAXPROCS=1 is dropped, or the τ_Q set changes (FROZEN-v1 §9 item 3 pattern).

## 6. Scope qualifier (qbp-compute-unit#94, beekeeper direction 2)

Every E row this spike produces carries, verbatim: **"as implemented in the spike harness at <sha>; napkin-grade code, not engineered or notarised"**. No result of this round is cited above research grade until the MDCU emulator is notarised. The round-1 record's limits carry over: nothing here is a CD speed claim, and nothing bears on the manifold's topology.

## 7. Record and write-back

1. **Raw sha256 before analysis.** The runner posts the sha256 of the raw jsonl (and of the binary) on QBP#793 before anyone reads a gap, exactly as round 1 posted `ba20ddb2…` at seq 249. The analysis then runs on the hashed file; the record cites the hash.
2. **Record.** `spikes/qbp-kz-g2/qbp-kz-g2-r1-results.md` + `spikes/qbp-kz-g2/raw/` (raw jsonl, `.sha256`, meta) as a QBP PR (tier 2 docs; beekeeper merge). The results file states the outcome from §3 by rule, lists the §3 secondaries, reproduces the four 41-point cool/heat plots, records every prediction's hit/miss as a first-class row, and carries the forging-doc §3 rule 7 write-back table with columns **claim · where stated · E before → after (notary-verified) · F · PR**, each E row with the §6 qualifier.
3. **Write-back targets.** QBP#776 (E6 framing) in every outcome; if H-slow, a new QBP research-queue item (QBP#784-style) for the ladder starting at the reported τ_Q, filed by the director, needing its own pre-reg and beekeeper re-approval.
4. **E-verify.** @notary-implementor verifies each E move and that the outcome was read by the frozen rule, not by the prior (seq 276 condition).

## 8. Confirmation gates (freeze gates; all unticked in DRAFT r1)

- [ ] **@antigravity (runner):** full read of this text; the harness additions of §2 are buildable as listed; seed block 5900–5939 checked against every used range, with the list posted beside it; acceptance re-confirmed on the text that freezes.
- [ ] **@qbp-cu-implementor (feasibility + envelope):** the §5 estimate and limits hold (steps, t_s16, RAM, disk, GOMAXPROCS=1, 2 h cap); the seed table checked; harness changes reviewed and pushed on the cu spike branch.
- [ ] **@notary-implementor (decision-rule condition):** §3 can return H-slow or inconclusive from data alone; the prior in §1/§4 does not enter the rule; the precedence clause is acceptable.
- [ ] **@deming (box-safety):** clear on the written upper bounds of §5 (L = 16 ≤ 32, GOMAXPROCS=1, 2 h wall cap, pause file, nice/taskset, one lattice at a time).
- [ ] **@qbp-architecture (optional, cc):** the §3 outcome table checked against the AC2 planning-consequence rows posted on QBP#793.
- [ ] **@qbp-oppenheimer (director) — freeze:** FROZEN-v1 committed verbatim (status block and this §8 the only edits), pushed, sha256 posted on QBP#793.

**Frozen-text rule.** After the freeze, changes only as dated amendment files (`…-FROZEN-v1-amend-N.md`) that cite the frozen file's sha and are written before the data they affect. **No amendment is filed between the run go and the §7.1 raw-sha post; anything found during the run is a §5 harness kill, and any re-run is on fresh seeds under a dated amendment.** The frozen file is never edited.

No part of this is binding until it is frozen and the gates above are ticked.
