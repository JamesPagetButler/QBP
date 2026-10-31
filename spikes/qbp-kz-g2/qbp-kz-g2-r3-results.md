# `qbp-kz-g2` round 3 — results (equilibrium first-order test)

**Status: round 3 complete; outcome read by the frozen §3 rule, no rule changed after data. Outcome: H-FO by rule (a).** Spike / research grade at most (qbp-compute-unit#94 scope qualifier: MDCU is spike code). Director @qbp-oppenheimer; runner = director-supervised sub-agent (FROZEN-v1 runner clause; antigravity's waker not live). Tracker QBP#797; this is an **oppenheimer-spike**: it discharges the ledger anchor `HYP-g2so4-planefield-continuous-transition` (QBP PR #799, `status: contested`), named before the run. Predecessors: round 1 of this line (`qbp-kz-g2-r1-results.md`, PR #796) and mdcu-kz round 1 (qbp-compute-unit#92/#93).

## Header

| Item | Value |
|---|---|
| Frozen pre-registration | `spikes/prereg/qbp-kz-g2-r3-prereg-FROZEN-v1.md`, sha256 `132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623` (QBP PR #800 head `ae37319`, cut from DRAFT r7 `88910757…`); no amendment filed |
| Harness / run commit | qbp-compute-unit `45639ed11ff516c70be7263136c1cb0a794295b2` (PR #97, branch `spike/qbp-kz-g2-r3-harness` off the round-1 harness `aa04139`; cu review + push; architect §I4 APPROVE-WITH-CONCERN at `45639ed` — no verdict-bearing mismatch; two later tests-only commits `99145b0`, `2cf2375` leave every non-test file byte-identical). 13 frozen round-1 function bodies byte-identical. Binary `emulator/bin/mdcu-kz` sha256 `89e7fd539a507ec7d94c00fd12c54bd741de5c14c60135244e3f2afb9a98b899`, built once in phase 1 and never rebuilt; `code_sha` clean (`dirty_files 0`) in every meta |
| Go | Standing approved-list rule (list approved by the beekeeper in session 2026-10-30, inter#224; "Beekeeper boxes" on QBP#797): (1) runner acceptance line (`runner-r3/phase1-report.md`); (2) FROZEN-v1 + sha + §8 gates (RT r1; Gemini r1 R-C → r2 APPROVE → r3 APPROVE; notary PASS r5 → carries to the frozen sha, seq 376; cu GO → carries, seq 377, binding sign on the smoke rates, seq 394; runner read); (3) deming box-safety CLEAR at the frozen sha (mdcu-spike seq 375) + box-lease conformance (seq 382). Go posted mdcu-spike seq 397 + QBP#797 |
| Run | 2026-10-31 02:10:19Z (process 1) → 12:17:24Z (process 27 wrapper exit); 27 sequential processes via `emulator/scripts/run-kz.sh eq <L> <t> <raw> <frozen>` (go-test `TestKZ` → quiet-load wait → pause check → **box lease** `flock -n` → `GOMAXPROCS=1 nice -n 19 taskset -c 7 ./bin/mdcu-kz -run-eq -L <L> -t <t> -prereg-sha 132f6a42… -max-out-mb 10`); `KZG2_RERUN_AMEND` unset; caps 2 h wall / 100 MB Sys / 10 MB output / pause file / NaN / seed guard — none fired; no no-runs, no kills |
| Raw sha256 post (§7.1) | QBP#797 (issuecomment-6543299715, 12:22:05Z) and mdcu-spike seq 411 (12:21Z): all 27 shas + the binary sha together, **before** any raw file was opened; director's own `sha256sum` = wrapper sidecar = driver end line for all 27 |
| Analysis | `./bin/mdcu-kz -analyze-eq -plot-out … <27 files>` at `45639ed`, 12:22:29Z (after the sha post); output `qbp-kz-g2-r3-analyze-eq.out` (sha256 `966433c3…`), plot data `qbp-kz-g2-r3-analyze-eq-plot.json`; independent recompute `qbp-kz-g2-r3-recompute.py` (stdlib; reads only the raw series; see §Recompute) |
| Resources | 27 × 165,000 = 4,455,000 plane-steps; driver wall 30,369 s = 8.44 h (§5 projection 8.23 h, smoke projection 8.49 h); total elapsed 10 h 7 min, the rest quiet-load waiting; ms/step L8 1.542–1.552 · L12 5.108–5.186 · L16 12.169–12.228 (ratios ≤ 1.04 to §5); longest process 2,018 s = 28 % of its cap; **peak Sys ≤ 14.8 MB recorded in every `end` record** (closes round 1's disclosure 3); raw 15,538,006 B ≈ 0.58 MB each |

## Raw files (committed under `raw/`, shas identical to the §7.1 post)

| k | L | t | T | seeds (j = 0, 1 hot Haar; j = 2 cold aligned) | exit | wall s | peak Sys MB | bytes | sha256 |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 8 | 0 | 1.08 | 6000–6002 | 0 | 255 | 14.7 | 568006 | `caf86820…3856` |
| 2 | 8 | 1 | 1.10 | 6004–6006 | 0 | 255 | 14.7 | 567796 | `24817f20…38da` |
| 3 | 8 | 2 | 1.12 | 6008–6010 | 0 | 255 | 14.7 | 567000 | `a5bdc0dc…9e9a` |
| 4 | 8 | 4 | 1.14 | 6016–6018 | 0 | 257 | 14.7 | 566648 | `1f9a7ae0…8f7d` |
| 5 | 8 | 6 | 1.16 | 6024–6026 | 0 | 255 | 14.7 | 576301 | `d8a1385d…1217` |
| 6 | 8 | 8 | 1.18 | 6032–6034 | 0 | 256 | 14.7 | 580691 | `81e7ff99…72fc` |
| 7 | 8 | 9 | 1.20 | 6036–6038 | 0 | 255 | 14.7 | 580712 | `f3af8bff…c93b` |
| 8 | 12 | 0 | 1.08 | 6040–6042 | 0 | 856 | 14.7 | 568011 | `d5c9e156…95bb` |
| 9 | 12 | 1 | 1.10 | 6044–6046 | 0 | 843 | 14.5 | 567945 | `33d6288f…3915` |
| 10 | 12 | 2 | 1.12 | 6048–6050 | 0 | 844 | 14.7 | 566531 | `3070d1bd…9d11` |
| 11 | 12 | 3 | 1.13 | 6052–6054 | 0 | 848 | 14.5 | 566251 | `8cb96ca3…4adb8` |
| 12 | 12 | 4 | 1.14 | 6056–6058 | 0 | 852 | 14.7 | 570761 | `fe392763…1e0c` |
| 13 | 12 | 5 | 1.15 | 6060–6062 | 0 | 845 | 14.7 | 579900 | `173066dd…02ff` |
| 14 | 12 | 6 | 1.16 | 6064–6066 | 0 | 846 | 14.7 | 581306 | `f58a5209…b90b` |
| 15 | 12 | 7 | 1.17 | 6068–6070 | 0 | 843 | 14.7 | 581661 | `1ffcf2cb…1220` |
| 16 | 12 | 8 | 1.18 | 6072–6074 | 0 | 844 | 14.5 | 586043 | `de40485b…076d` |
| 17 | 12 | 9 | 1.20 | 6076–6078 | 0 | 844 | 14.7 | 586285 | `aceefd18…dfa7` |
| 18 | 16 | 0 | 1.08 | 6080–6082 | 0 | 2010 | 14.7 | 568083 | `1cf48096…afc8` |
| 19 | 16 | 1 | 1.10 | 6084–6086 | 0 | 2015 | 14.7 | 568020 | `6222b4c4…72db` |
| 20 | 16 | 2 | 1.12 | 6088–6090 | 0 | 2008 | 14.7 | 566311 | `8f214897…bad5` |
| 21 | 16 | 3 | 1.13 | 6092–6094 | 0 | 2009 | 14.7 | 566343 | `05e80b2d…54fa` |
| 22 | 16 | 4 | 1.14 | 6096–6098 | 0 | 2013 | 14.7 | 580392 | `6301d5bc…bdfb` |
| 23 | 16 | 5 | 1.15 | 6100–6102 | 0 | 2010 | 14.7 | 582462 | `2d1771ce…d22f` |
| 24 | 16 | 6 | 1.16 | 6104–6106 | 0 | 2014 | 14.7 | 583090 | `b1d9d626…3414` |
| 25 | 16 | 7 | 1.17 | 6108–6110 | 0 | 2010 | 14.8 | 583208 | `1cebe705…cc3e` |
| 26 | 16 | 8 | 1.18 | 6112–6114 | 0 | 2018 | 14.7 | 588609 | `10f2c86f…077b` |
| 27 | 16 | 9 | 1.20 | 6116–6118 | 0 | 2009 | 14.7 | 589640 | `40ed422d…ee79` |

Full shas are in the `.sha256` sidecars and on QBP#797. Each raw file: one `meta` record (L, T, t_index, eta 0.1, seeds, burn-in 5,000, sampling 50,000, record every 10, noise stream 100002, prereg sha, binary sha, code sha, caps, pause state, lease), one `eq` record (per seed: seed, start, 5,000-record `s_series` and `e_series`, `tau_int_rec`, `n_eff`, `undersampled`; no pooled statistic), one `end` record (exit 0, wall, ms/step, peak Sys).

## Deviations and disclosures (none changes a seed, step count, threshold or rule)

1. **Runner.** antigravity's waker was not live at the go; the FROZEN-v1 runner clause applied (director-supervised sub-agent). Its reports are in `runner-r3/`.
2. **Process control (flagged by the harness).** The runner launched points 1 and 2 with the wrapper **detached** (`setsid nohup … &`, polling a done marker) "so no harness timeout could reach the driver"; the harness flagged this as an auto-mode bypass. The director reviewed the effects (every control — pause file, caps, lease — lives inside the wrapper/driver and travelled with the process; the launch gates and the sidecar-only reads held), ruled that points 1–2 stand as recorded, and ordered tracked foreground tasks from point 3 onward (mdcu-spike seq 401; deming, architect, cu and notary concurred, seq 402–407). A hard line for runner briefs ("never detach") is now in the spike-director runbook addendum (inter PR #250).
3. **Lease seat label.** The wrapper's holder line was written with `KZ_LEASE_SEAT=qbp-oppenheimer` (wrapper default `qbp-cu-implementor`); the lease behaved to contract on all 27 processes (first live enforcement).
4. **Lock file creation.** The phase-1 `flock -n` probe created the previously nonexistent empty `~/.federation-watcher/state/box-lease.lock` (no holder written); the wrapper would have created the same file.
5. **Test-process seed consumption (pre-run).** During a mutation check of the harness before `45639ed`, a guard test without a `Check` let an accepted L = 16 configuration step inside the test binary and consume the noise stream of re-run seeds 6220–6222 in-process; nothing was written. Not a use of the re-run block (notary and cu concur: each run re-seeds deterministically from the integer); the test design was fixed in `45639ed`. The re-run block 6120–6239 is untouched by this round.
6. **Analyzer invocation.** The first `-analyze-eq` call placed `-plot-out` after the file list; the analyzer counted 29 arguments and refused by its complete-set check without reading any file. The second call (flag first) is the one reported.
7. **Smoke outputs** (seeds 13000/13001, L = 8/12/16, phase 1) were never analysed; their shas are in `runner-r3/phase1-report.md`.

## §3 reading (frozen rule, verbatim thresholds)

Per L: 60 equal-width bins over the pooled e of all T and seeds at that L; per (L, T) the pooled histogram of the 3 seeds' 15,000 samples, 3-bin smoothed; a two-peak candidate (two strict local maxima ≥ 1 bin apart) is **resolved** iff n_lower − n_valley > 3·√(n_lower + n_valley); ΔF_L(T) = ln(h_lower / h_valley) (h_valley = 0 → 0.5), unresolved → 0.

| L | T | ΔF_L(T) | resolved | peaks (bins) | h_lower / h_valley | V_L(T) | D_e | D_S | start-dep. | under-sampled run |
|---|---|---|---|---|---|---|---|---|---|---|
| 8 | 1.08–1.14 | 0 | no | — | — | 0.6658–0.6660 | ≤ 0.8 | ≤ 1.0 | no | no |
| 8 | **1.16** | **7.426** | yes | 20, 52 (valley 34) | 839.7 / 0.5 | 0.6442 | 20.2 | 20.2 | **yes** | **yes** (seed 6025, τ ≈ 339) |
| 8 | 1.18–1.20 | 0 | no | — | — | 0.6665 | ≤ 0.8 | ≤ 1.3 | no | no |
| 12 | 1.08–1.13 | 0 | no | — | — | 0.6664–0.6665 | ≤ 1.4 | ≤ 1.4 | no | no |
| 12 | **1.14** | **7.826** | yes | 15, 51 (valley 32) | 834.7 / 0.3 | 0.6351 | 4.6 | 4.6 | **yes** | **yes** (seeds 6056, 6057: τ ≈ 437, 207) |
| 12 | **1.15** | **7.731** | yes | 17, 53 (valley 25) | 1139.3 / 0.5 | 0.6455 | 898 | 1205 | **yes** | no |
| 12 | **1.16** | **7.666** | yes | 20, 54 (valley 28) | 1067.7 / 0.5 | 0.6479 | 684 | 826 | **yes** | no |
| 12 | **1.17** | **7.408** | yes | 24, 54 (valley 35) | 824.3 / 0.5 | 0.6514 | 317 | 361 | **yes** | no |
| 12 | 1.18–1.20 | 0 | no | — | — | 0.6666 | ≤ 1.7 | ≤ 2.3 | no | no |
| 16 | 1.08–1.13 | 0 | no | — | — | 0.6666 | ≤ 1.3 | ≤ 2.3 | no | no |
| 16 | **1.14** | **7.942** | yes | 13, 52 (valley 20) | 1406.7 / 0.5 | 0.6440 | 1100 | 1256 | **yes** | no |
| 16 | **1.15** | **7.937** | yes | 16, 54 (valley 21) | 1400.0 / 0.5 | 0.6458 | 1217 | 1359 | **yes** | no |
| 16 | **1.16** | **7.885** | yes | 19, 55 (valley 26) | 1328.0 / 0.5 | 0.6481 | 937 | 1150 | **yes** | no |
| 16 | **1.17** | **7.684** | yes | 23, 56 (valley 31) | 1086.7 / 0.5 | 0.6518 | 367 | 442 | **yes** | no |
| 16 | 1.18–1.20 | 0 | no | — | — | 0.6666 | ≤ 0.9 | ≤ 1.8 | no | no |

(Every row of the full 27-point table, the per-seed table and the τ_int table is in `qbp-kz-g2-r3-analyze-eq.out`.)

**Primary statistic:**

| L | ΔF*(L) | T*(L) | σ*(L) (jackknife) | V_min(L) | note |
|---|---|---|---|---|---|
| 8 | 7.4262 | 1.16 | 1.19 | 0.6442 | one resolved point |
| 12 | 7.8256 | 1.14 | 1.67 | 0.6351 | window 1.14–1.17 |
| 16 | 7.9421 | 1.14 | 5.29 | 0.6440 | window 1.14–1.17 |

**Rule, precedence (a) → (b) → (c)** (ΔF₀ = ln 2 = 0.6931; ε(L₁, L₂) = max(0.2, 2·√(σ*² + σ*²)) → ε(16, 12) = 11.11, ε(12, 8) = 4.11):

| Clause | Test | Value | Fires |
|---|---|---|---|
| (a) H-FO | ΔF*(16) ≥ ln 2 | 7.94 ≥ 0.69 | yes |
| | ΔF*(16) ≥ ΔF*(12) − ε(16, 12) | 7.94 ≥ −3.28 | yes |
| | ΔF*(12) ≥ ΔF*(8) − ε(12, 8) | 7.83 ≥ 3.32 | yes |
| (a)-gate | under-sampled run at (16, T*(16) = 1.14)? | no | (a) may fire |
| (b) H-CONT | ΔF_16(T) = 0 and ΔF_12(T) = 0 at every T | false (8 resolved points) | no |

**OUTCOME: H-FO by rule (a).**

**Director's reading of the numbers (post-data; the verdict above is the rule's, this paragraph is not a rule):** every resolved barrier sits at the half-count floor, so each ΔF is a **lower bound** — no transition between the two phases was observed at any resolved point in 50,000 sampling steps — and the L-trend clauses pass with inflated ε (the leave-one-seed-out jackknife removes the cold seed and the subsample reads unimodal; flagged pre-data in the §3 B11 note; it loosens only (a)'s trend clauses). The evidence for "first-order" is therefore not a measured barrier height but the **two-state structure itself**: at L = 12 and 16, for T ∈ [1.14, 1.17], the two hot seeds hold the disordered phase (⟨e⟩ ≈ 1.44–1.48, ⟨S⟩ ≈ 0.04–0.06) and the cold seed holds the ordered phase (⟨e⟩ ≈ 1.05–1.15, ⟨S⟩ ≈ 0.43–0.51) for the whole run, each with a within-phase τ_int of 1–7 records (relaxed, not drifting), while at T ≤ 1.13 all three seeds agree on the ordered phase and at T ≥ 1.18 on the disordered one. At L = 8 the window shrinks to the single point T = 1.16 and the seeds switch phase within the run (seed 6025 caught mid-transition, τ ≈ 339 records); at (12, 1.14) both hot seeds are mid-transition. A coexistence window whose metastability persists from L = 12 to L = 16 and dissolves at L = 8 is the finite-size signature of a first-order transition, with the coexistence temperature inside [1.14, 1.17]. Under a continuous transition both starts converge to one distribution; they did not, anywhere in the window, at either larger lattice.

**The guards, as frozen and as intended (recorded at the architect's request, mdcu-spike seq 416, so the argument is on file for the E-verify):**

1. *The (a)-side phase-locking guard did not engage, and why.* FROZEN-v1 §3's (a)-side under-sampling gate exists so that "a phase-locked seed must not be read as a deep valley"; it is implemented as n_eff < 20 at any run at (16, T*(16)). Here the locking was **total**: each seed sat well relaxed inside its own phase (τ_int ≈ 1–4 records at (16, 1.14)), so n_eff stayed in the thousands and the gate, working exactly as frozen, did not fire. The pre-data concern behind that gate — a seed stuck in one phase mimicking a barrier — is the situation this data most directly tests.
2. *Why H-FO stands despite that.* (i) The two persistent states have well-separated ⟨e⟩ plateaus (Δe ≈ 0.39 at L = 16, D_e ≈ 300–1300): that separation is latent heat, not a correlation-time artefact. (ii) Seeds switch phase at L = 8 (the window shrinks to one T and seed 6025 is caught mid-transition) but stay locked at L = 12 and L = 16 over four consecutive T: the barrier grows with L, which is the finite-size behaviour of a first-order transition and the opposite of what a crossover does. (iii) Critical slowing down near a continuous T_c produces long correlation times and broad, drifting distributions, not two narrow, stable, separated energy levels that persist for 50,000 steps at two lattice sizes. (iv) The hot/cold start probe (r5) was added precisely to expose a hidden second phase; it did, in the same direction at every point of the window.
3. *ΔF\* values are lower bounds.* Every resolved valley has zero smoothed counts and was set to 0.5 before the logarithm, so ΔF*(L) = ln(h_lower / 0.5) measures the peak height, not a barrier; the L-trend clauses of (a) therefore compare floors, and their passing is consistent with H-FO but carries less weight than an observed crossing would. The weight of the verdict rests on points 1–2.

**Secondaries (non-gating):**

| Secondary | Result |
|---|---|
| Binder cumulant | V_min(L) = 0.6442 / 0.6351 / 0.6440 (shift-dependent, see FROZEN-v1 §1 r3 note); two-point 1/L³ extrapolation V* = 0.6505 vs 2/3 = 0.6667 |
| Coexistence T (equal-weight) | **not readable** at L = 16: the peak weights are set by the 2 : 1 hot/cold start split at every resolved point, so no equal-weight crossing exists; the window itself brackets it: [1.14, 1.17] |
| Latent-heat proxy Δe at (16, 1.14) | 0.390 (peak separation); trend at each L's own T*: 0.370 → 0.386 → 0.390 |
| Phase-locking count at (16, 1.14) | 3 of 3 seeds (every seed stayed on one side of the valley for the whole run) |
| Per-seed max single-record step | e: ≤ 0.13 (L = 8), ≤ 0.07 (L = 12), ≤ 0.05 (L = 16); S: ≤ 0.09 / 0.05 / 0.03 — no single-record jump anywhere (consistent with round 1's P5 lesson) |
| S histograms | resolved-bimodal at 9 of 27 points (the same window), descriptive only |
| τ_int / n_eff | per run in the analyzer output; 3 under-sampled runs: (8, 1.16) seed 6025; (12, 1.14) seeds 6056, 6057 — all three are phase transitions in progress |

## Predictions on file (frozen §4), hit / miss

| # | Prediction | Prior | Result |
|---|---|---|---|
| P1 | H-FO (rule (a) fires) | ≈ 75 % | **hit** |
| P2 | H-CONT (rule (b) fires) | ≈ 10 % | miss |
| P3 | inconclusive (rule (c)) | ≈ 15 % | miss (not reached) |
| P4 | equal-weight coexistence T at L = 16 readable and in [1.12, 1.18] | ≈ 70 % | **miss** — not readable (the weights are start-set); the window [1.14, 1.17] lies inside the predicted interval but the prediction's own clause required a readable crossing |
| P5 | ΔF*(16) ≥ 2 given H-FO | ≈ 50 % | **hit** (7.94, a floor-saturated lower bound) |

Lessons recorded for a future round (notes, not claims): with one cold and two hot seeds and no inter-phase transitions, the histogram weights carry no thermodynamic information, so an equal-weight coexistence estimate needs either a reweighting method or a sampler that crosses the barrier (multicanonical / parallel tempering) — a different design, off this approved list; and a barrier that saturates the count floor should be reported as "≥" from the start.

## Claim scope (frozen AC2 row for H-FO, verbatim)

| Claims | Does not claim |
|---|---|
| For this sigma model (chordal energy, Model-A sampler at η = 0.1, periodic L ≤ 16), the equilibrium energy distribution is two-state near T ≈ T*(16) with a free-energy barrier that does not shrink from L = 8 to 16: **first-order ordering transition**, consistent with the Landau cubic mechanism and with the ramp rounds. | Nothing about the topology of G₂/SO(4); no latent heat value beyond the proxy; no statement about other energies, dynamics, η or L > 16; not a proof (three sizes cannot exclude a crossover at larger L). |

## Write-back table (forging doc §3 rule 7; every row carries the qbp-compute-unit#94 scope qualifier: "as implemented in the spike harness at `45639ed`; napkin-grade code, not engineered or notarised")

| Claim | Where stated | E before → after (notary-verified: pending @notary-implementor E-verify on this PR) | F | PR |
|---|---|---|---|---|
| "The G₂/SO(4) plane-field sigma model (chordal energy, Model-A relaxation, L = 16 reference lattice) has a continuous ordering transition at its T_c, so a slow temperature ramp crosses it quasi-statically (the Kibble–Zurek premise)" — anchor `HYP-g2so4-planefield-continuous-transition` | ledger (PR #799), `status: contested` | row (ii) of the anchor's notes, equilibrium continuity: **unconfronted → falsified** (two-state coexistence window [1.14, 1.17] at L = 12, 16 with no inter-phase transition; dissolves at L = 8); `decision_state` → **falsified**, discharged by this record; row (i) (ramp crossing, falsified at `aa04139`) unchanged | research (spike) | this PR; ledger write = writer lane (qbp-implementor), after notary |
| "H-first is the a-priori expectation: the projector order parameter carries a Landau cubic invariant tr(Π_tl³), so the transition is first-order by that mechanism" | FROZEN-v1 §1 / §4 prior; inter#249 wisdom | consistent (round 1) → **consistent** (round 3: equilibrium two-state structure); still not a test of the mechanism itself | research (spike) | this PR |
| "A KZ ladder on this model is worth running" (process consequence) | QBP#776; round-1 record | closed → **stays closed**; no research-queue item | — | this PR |

No ledger (CTH) anchor is written by this PR; the E rows above are proposals for the confined writer lane with the #94 qualifier attached.

## Recompute (director's independent check)

`qbp-kz-g2-r3-recompute.py` (stdlib + matplotlib; reads only the raw `eq` records' series and start kinds, never the analyzer's fields) re-derives the 27-point table, the primary statistic, the rule and the secondaries, and draws the plots under `plots/`. Its agreement with `qbp-kz-g2-r3-analyze-eq.out` is stated in `qbp-kz-g2-r3-recompute-report.md`: **all 27 point rows and 81 run rows agree to the printed precision** (max |Δ| ΔF 4.8e-5, V_L 5e-7, D 5e-3, τ_int 5e-4; every peak/valley bin index, Sokal window, resolved / start-dependent / under-sampled flag, the primary table, ε, V*, the phase-locking count, the coexistence verdict and the OUTCOME line identical). Run: `python3 qbp-kz-g2-r3-recompute.py --raw raw --out <dir> --plots` from this directory (≈ 10 s; exit 0 = agreement). Leave-one-seed-out ΔF at T*(16) = {7.94, 7.94, 0.00}: the leave-cold-out subsample reads unimodal, which is where σ*(16) = 5.29 and the inflated ε come from.

## Plots (Human Visual Review material, `plots/`)

| File | What it shows |
|---|---|
| `kz-g2-r3-eseries-hot-cold.png` | per-seed ⟨e⟩ vs T at L = 8, 12, 16, hot seeds vs the cold seed; the shaded start-dependent window |
| `kz-g2-r3-S-vs-T.png` | the same for ⟨S⟩ |
| `kz-g2-r3-hist-panels.png` | pooled smoothed e-histograms at T = 1.14 and 1.16 for the three L, hot/cold contributions stacked, valley marked, ΔF annotated |
| `kz-g2-r3-traces-L16-T114.png` | the three seeds' e-series at (16, 1.14) (phase-locked) beside (8, 1.16) (tunnelling) |
| `kz-g2-r3-VL.png` | V_L(T) for the three L with 2/3 marked |

## Files in this record

| Path | Content |
|---|---|
| `qbp-kz-g2-r3-results.md` | this file |
| `qbp-kz-g2-r3-analyze-eq.out`, `qbp-kz-g2-r3-analyze-eq-plot.json` | frozen analyzer stdout (verbatim) and its plot data |
| `qbp-kz-g2-r3-recompute.py`, `qbp-kz-g2-r3-recompute-report.md` | independent recompute + its comparison report |
| `raw/qbp-kz-g2-r3-eq-L<L>-t<tt>.jsonl` + `.meta.txt` + `.sha256` (27 each) | the raw files and the wrapper's sidecars |
| `runner-r3/phase1-report.md`, `phase2-report.md`, `progress.log`, `harness-handoff.md` | runner acceptance/build/smoke, the 27-process run table, the progress log, the builder's hand-off |
| `plots/` | the five PNGs above |
