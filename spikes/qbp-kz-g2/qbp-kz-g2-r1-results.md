# `qbp-kz-g2` round 1 — results

**Status: round 1 complete; outcome read by the frozen §3 rule, no rule changed after data. Outcome: H-first by rule (a).** Spike / research grade at most (qbp-compute-unit#94 scope qualifier: MDCU is spike code). Director @qbp-oppenheimer; runner = director-supervised sub-agent (FROZEN-v1 runner clause, r6; antigravity's waker was not live at the go). Tracker QBP#793; predecessor round: qbp-compute-unit#92/#93 (mdcu-kz round 1).

## Header

| Item | Value |
|---|---|
| Frozen pre-registration | `spikes/prereg/qbp-kz-g2-r1-prereg-FROZEN-v1.md`, sha256 `785e0ee2c81740b25fbeb9dfa5bb26e22159d8b7b221de2bdb75c2f7a6f51e28` (QBP PR #794 head `25b9913`); **amend-1** `spikes/prereg/qbp-kz-g2-r1-prereg-FROZEN-v1-amend-1.md`, sha256 `f043b28012f5eba000b3492b860ecad94a6a0fcee6585c575b1324b69ded39b5` (`8c4d53b`; dated, pre-build; seed-range reconciliation 5900–5979 + the re-run-block row; no rule or number changed) |
| Harness / run commit | qbp-compute-unit `aa041391e934e6b41f02cf8f79a4e489ca928360` (PR #96, branch `spike/qbp-kz-g2-r1-harness`; qbp-cu review + push; qbp-architecture §I4 APPROVE carried to this head; frozen round-1 core byte-identical; two mutations killed in review). Binary `emulator/bin/mdcu-kz` sha256 `51a2ed9c69f2827a65bc40aa21e8c64ba60941f0091c40aa5b56a89f3900e7f7`, built from that commit; `code_sha` clean (`dirty_files 0`) in every meta |
| Go | Standing approved-list rule (list approved inter#224): (1) runner accepted (`runner/phase1-report.md`, acceptance line quoted on QBP#793); (2) FROZEN-v1 + amend-1 pushed with shas, §8 gates ticked (cu GO, notary PASS, runner read, Red Team re-read); (3) deming box-safety CLEAR (mdcu-spike seq 330, 2026-10-30 18:41Z). Go posted mdcu-spike seq 336 + QBP#793 |
| Run | 2026-10-30 18:50:02Z → 20:32:09Z; four sequential processes via `emulator/scripts/run-kz.sh 0b <τ> <raw> <frozen>` (go-test `TestKZ` → quiet-load wait → pause check → `GOMAXPROCS=1 nice -n 19 taskset -c 7 ./bin/mdcu-kz -run-0b -tau <τ> -tc 1.0666262219986817 -prereg-sha 785e0ee2… -out <raw>`); `KZG2_RERUN_AMEND` unset; caps 2 h wall / 100 MB RSS / 50 MB output / pause file / NaN / seed guard — none fired; stderr empty on all four |
| Raw sha256 post (§7.1) | mdcu-spike seq 338 and QBP#793, 2026-10-30 20:35Z, the four shas together, **before** any raw file was opened; witnessed by @notary-implementor (seq 340) |
| Analysis | `./bin/mdcu-kz -analyze-0b <four files>` at `aa04139`, 2026-10-30 20:35:48Z (after the sha post); output `qbp-kz-g2-r1-analyze-0b.out` (sha256 `534a3382…`); director's independent recompute `qbp-kz-g2-r1-recompute.py` (stdlib; reads only the raw `grid`/`cool`/`heat`/series arrays, never the analyzer's fields) agrees to 4 dp on every number and reproduces the two committed plots byte-for-byte |
| Resources | 488,000 plane-steps; driver wall 405 + 786 + 1548 + 3086 = 5,825 s ≈ 97 min (§5 estimate 100–108); 11.9 ms/step (§5 band 12–13); longest rung 43 % of its 2 h cap; raw 1,050,352 B ≈ 1.0 MB (< 5 MB); quiet-wait cleared at load 0.54–0.68 before every rung; pause file absent at start and end of every rung. **Peak RSS not recorded**: the driver enforces its 100 MB cap but writes no peak field (qbp-cu files a qbp-compute-unit#94 AC2 follow-up to record `MemStats.Sys`); the kill did not fire |

## Raw files (committed under `raw/`, shas identical to the §7.1 post)

| τ_Q | seeds | steps | exit | wall s | load end | bytes | sha256 |
|---|---|---|---|---|---|---|---|
| 1600 | 5900–5909 | 34,000 | 0 | 405 | 1.30 | 73,608 | `37102cc855412e1bd51c31a8bb650ca2eb1885bccd398e745b6caf47abd975bd` |
| 3200 | 5910–5919 | 66,000 | 0 | 786 | 1.53 | 142,356 | `397a39cc96198a459664c103b46e27f06a05b8ba021093cdb89617e28a75e788` |
| 6400 | 5920–5929 | 130,000 | 0 | 1548 | 1.60 | 279,687 | `80d710130e6b7e7343d53950bc394d2cc8db47c1e0915d700bb61848b9c58f30` |
| 12800 | 5930–5939 | 258,000 | 0 | 3086 | 1.33 | 554,701 | `cae83fdc60a63534b153546cae5e781a0237216606251ad9e4d316dbce69468f` |

Each raw file: one `meta` record (L = 16, η = 0.1, 200 hold steps, τ_Q cool + τ_Q heat, record every 10, 41-point grid T ∈ [0.5333, 1.5999], T_c = 1.0666262219986817, prereg sha, `rerun: false`), one `stage0b` record (seed-mean cool/heat curves on the grid, per-seed series, per-seed max gap, jump scan) and one `end` record (exit 0, wall). Sidecars `.meta.txt` and `.sha256` are the wrapper's.

## Deviations and disclosures (none changes an arm, seed, threshold or rule)

1. **Runner.** antigravity's waker was not live at the go, so the FROZEN-v1 r6 runner clause applied: a director-supervised sub-agent ran phases 1 (acceptance, sha recompute, used-range check, build, 73 guard tests, write-nothing dry runs) and 2 (the four rungs). Its reports are in `runner/`. It read no raw file; its only reads were exit codes, the sidecars and its own logs.
2. **Mid-flight visibility (director).** At 19:12Z, between rungs 2 and 3, the director listed the run directory to confirm progress and saw the `.sha256` sidecars of rungs 1 and 2 (names and hashes only, no content, no gap). Neither sha was posted or used until all four were in; the §7.1 post is the first public appearance of any of them. Disclosed for the ordering record.
3. **Peak RSS** not recorded by the driver (header). The < 50 MB envelope is supported only by the cap not firing and by the raw size; the margin is not on the trail.
4. **Analyzer output sha** `534a3382…` is of the saved stdout, which embeds absolute scratchpad paths; the committed copy is byte-identical to that output.
5. No amendment was filed between the go and the §7.1 post; no re-run; the re-run block 5940–5979 is untouched.

## §3 reading (frozen rule, verbatim thresholds)

gap(τ) = max over the 41 grid points of |mean S_cool − mean S_heat| / S_max.

| τ_Q | gap(τ) | at grid pt / T | per-seed max gap min / max (n = 10) | largest cool step (rec, T) | largest heat step (rec, T) | jump > 0.10·S_max |
|---|---|---|---|---|---|---|
| 1600 | **0.5171** | 21 / 1.0933 | 0.5098 / 0.5363 | 0.0350 (87, 1.020) | 0.0480 (106, 1.240) | no |
| 3200 | **0.4933** | 21 / 1.0933 | 0.4854 / 0.5224 | 0.0334 (162, 1.060) | 0.0403 (207, 1.223) | no |
| 6400 | **0.4805** | 22 / 1.1200 | 0.4515 / 0.5018 | 0.0271 (312, 1.080) | 0.0353 (404, 1.207) | no |
| 12800 | **0.4769** | 22 / 1.1200 | 0.4617 / 0.5036 | 0.0252 (603, 1.098) | 0.0256 (794, 1.195) | no |

Rule, precedence (b) → (a) → (c):

| Clause | Test | Value | Fires |
|---|---|---|---|
| (b) H-slow | gap(12800) < 0.05 | 0.4769 | **no** |
| (a) H-first | gap(12800) ≥ 0.6 · gap(1600) | 0.4769 ≥ 0.3102 | **yes** |
| (c) inconclusive (rate) | otherwise | — | not reached |

**OUTCOME: H-first by rule (a).**

Secondaries (non-gating, as frozen):

| Secondary | Result |
|---|---|
| OLS slope of ln gap on ln τ_Q (4 points, 2 dof) | **−0.0388 ± 0.0090**; no zero gap, all four points in the fit. α ≈ 0.04 against the (a) scope line α ≤ 0.246: the gap decays far slower than τ_Q^−0.25 and is close to saturated |
| Jump clause | no seed-mean single-recorded-step jump > 0.10·S_max at any τ_Q; largest 0.048 (τ_Q = 1600, heat) |
| Curves (HVR) | `plots/kz-g2-r1-curves.png`: the cool branch drops at T ≈ 1.07–1.10 and the heat branch at T ≈ 1.20–1.23 at every τ_Q; the loop sharpens with τ_Q but its width does not close. `plots/kz-g2-r1-gap-vs-tau.png`: gap vs τ_Q on log–log with the (a) and (b) thresholds |

## Predictions on file (frozen §4), hit / miss

| # | Prediction | Prior | Result |
|---|---|---|---|
| P1 | H-first (rule (a) fires) | ≈ 70 % | **hit** |
| P2 | H-slow (rule (b) fires) | ≈ 15 % | miss (did not fire) |
| P3 | inconclusive (rate) | ≈ 15 % | miss (not reached) |
| P4 | gap(1600) ∈ [0.4676, 0.5676] on fresh seeds | ≈ 85 % | **hit** (0.5171; Δ from round 1's 0.5176 = 0.0005) |
| P5 | jump clause fires at some τ_Q ≥ 6400, given H-first | ≈ 50 % | **miss** (largest step 0.035 at τ_Q = 6400, 0.026 at 12800; the seed-mean drops over several recorded steps, not one) |

Reading of the P5 miss (director, post-data, not a rule). My first reading was that the seed-mean curve smears single-seed discontinuities. Gemini round 1 on PR #796 asked for the per-seed scan instead of the excuse, so it was run as a **post-hoc, non-gating supplementary** (`qbp-kz-g2-r1-recompute.py`, not pre-registered, decides nothing), and it **refutes the smearing reading**: no individual seed shows a single-recorded-step jump > 0.10·S_max either.

| τ_Q | cool: per-seed largest step, max / min over seeds | seeds > 0.10 | heat: max / min | seeds > 0.10 |
|---|---|---|---|---|
| 1600 | 0.0500 / 0.0326 | 0/10 | 0.0617 / 0.0464 | 0/10 |
| 3200 | 0.0555 / 0.0309 | 0/10 | 0.0506 / 0.0402 | 0/10 |
| 6400 | 0.0475 / 0.0283 | 0/10 | 0.0462 / 0.0344 | 0/10 |
| 12800 | 0.0503 / 0.0315 | 0/10 | 0.0408 / 0.0303 | 0/10 |

So the honest reading is that, under Model-A relaxation at this record cadence (one record per 10 plane-steps), each seed's drop takes several recorded steps even though the two branches drop at well-separated temperatures; the pre-registered jump clause (> 0.10·S_max in one recorded step) is insensitive to this dynamics, which is a limitation of P5 as written, not evidence against H-first (the gating rule (a) does not use it). Any future round wanting a discontinuity secondary should pre-register a per-seed, per-temperature-window criterion rather than a single-step threshold. Filed as a note, not a claim.

## Claim scope (frozen AC2 row for H-first, verbatim)

| Claims | Does not claim |
|---|---|
| For this sigma model (chordal energy, Model A, this window, L = 16), the hysteresis does not close with ramp length over 1600–12800: consistent with a first-order transition. | Nothing about the topology of G₂/SO(4); no KZ exponent; no statement about other energies, dynamics or L; not a proof of first order (a 0.9-decade span cannot exclude slow convergence). |

## Write-back table (forging doc §3 rule 7; every row carries the qbp-compute-unit#94 scope qualifier: MDCU spike code, research-grade at most)

| Claim | Where stated | E before → after (notary-verified: pending @notary-implementor E-verify on this PR) | F | PR |
|---|---|---|---|---|
| "The G₂/SO(4) plane-field sigma model (chordal energy, Model-A dynamics, ramp over [1.5 T_c, 0.5 T_c], L = 16) has a continuous ordering transition" (the KZ premise) | QBP#776 E6 note (round 1 write-back, qbp-compute-unit#92/#93) | falsified at τ_Q = 1600 with the rate caveat open (H-slow live) → **falsified on the rate scale τ_Q = 1600–12800: hysteresis persists (gap 0.48 at 12800, slope −0.04 ± 0.01); H-slow eliminated on this span** | research (spike) | this PR; QBP#776 note = AC5 |
| "H-first is the a-priori expectation: the projector order parameter carries a Landau cubic invariant tr(Π_tl³), so the transition is first-order by that mechanism" | FROZEN-v1 §1 / §4 prior; inter#249 wisdom (qbp-oppenheimer) | untested prior → **consistent** (P1 hit); this is not a test of the mechanism, only of its consequence on this span | research (spike) | this PR |
| "A KZ ladder on this model is worth running" (process consequence, not a physics claim) | QBP#776; mdcu-kz round-1 record | closed after round 1 → **stays closed** (H-first row: ladder closed; no new research-queue item) | — | this PR |

No ledger (CTH) anchor is written by this PR; the E rows above are proposals for the confined writer lane (qbp-implementor) if the beekeeper routes them, with the #94 scope qualifier attached.

## Files in this record

| Path | Content |
|---|---|
| `qbp-kz-g2-r1-results.md` | this file |
| `qbp-kz-g2-r1-analyze-0b.out` | analyzer stdout, verbatim |
| `qbp-kz-g2-r1-recompute.py` | director's independent recompute of §3 (gap, rule, slope, P4, jump) + the plot generator; `python3 qbp-kz-g2-r1-recompute.py --plots` from this directory reproduces the table above and `plots/` |
| `raw/qbp-kz-g2-r1-0b-tau{1600,3200,6400,12800}.jsonl` + `.meta.txt` + `.sha256` | the four raw files and the wrapper's sidecars |
| `runner/phase1-report.md`, `runner/phase2-report.md`, `runner/guard-tests.log` | runner acceptance, build, 73 guard tests, run log with the per-rung table |
| `plots/kz-g2-r1-curves.png`, `plots/kz-g2-r1-gap-vs-tau.png` | HVR material, generated by `qbp-kz-g2-r1-recompute.py --plots` from the raw records |
