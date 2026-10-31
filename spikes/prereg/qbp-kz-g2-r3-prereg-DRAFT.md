# `qbp-kz-g2` round 3: pre-registration — DRAFT r2

Status: **DRAFT r2 (2026-10-31). Nothing frozen, nothing built, nothing run.** r1 was drafted by a director-supervised sub-agent from the QBP#797 sketch; r2 = r1 + the director's decisions on the drafter's [proposal] items: **(1) the reduced option is chosen** (§5: 7 T × 3 L × 3 seeds); **(2) δ = 0.02, 60 bins, 3-bin smoothing and the under-sampling sub-clause are accepted; (3) a tolerance ε = 0.01 is added to the §3 monotonicity clause** so that noise in V_min at the small lattices cannot by itself push a two-state reading into (c); **(4) the optional burn-in trace is dropped** (nothing in §3 reads it). Numbers still marked **[proposal]** are open for the reviewers; no number here binds anyone before the freeze. Equilibrium (no-ramp) finite-size test of the order of the ordering transition of the G₂/SO(4) plane-field sigma model: first-order vs continuous. Spike / napkin grade (Go harness on the qbp-compute-unit spike branch, pre-registered). Tracking issue: **QBP#797** (typed `research`). Director: @qbp-oppenheimer. Runner: a named runner accepts before the go (antigravity if its waker is live, otherwise a **sub-agent runner supervised by the director**, as in round 1 — round-1 record, deviation 1). Feasibility: @qbp-cu-implementor. Box-safety: @deming. E-verify: @notary-implementor. Merges (this pre-reg, the record, the write-back): the beekeeper's (QBP lane).

**Spike type.** This is an **oppenheimer-spike**: it discharges a ledger hypothesis. The anchor it discharges is **`HYP-g2so4-planefield-continuous-transition`** (the KZ-premise hypothesis as a ledger anchor; mint requested from the writer lane 2026-10-31, live-test seq 4057; hypothesis / open, with `kill_condition` = this file's §3 rule). The anchor id is named here, pre-data, so that QBP#797 AC2's planning-consequence table can cite it.

**Approval.** The beekeeper approved this spike in session, 2026-10-30 ("approved"), after the round-1 record (PR #796) and the post-hoc loop-width table; recorded on inter#224 (issuecomment-6535987333) and on QBP#797. It is on the inter#224 approved list.

**Standing go.** Under the approved-list rule (CLAUDE.md "Spike run go on approved lists", 2026-10-25) the run go is the director's, not the beekeeper's, once all three hold: (1) a named runner has accepted the frozen text; (2) FROZEN-v1 committed and pushed with its sha256 posted on QBP#797 and every §8 gate ticked; (3) deming has cleared box-safety on the frozen plan. The go message cites all three. Deming's live-test schedule (seq 4051) applies: **the run happens only when no warp builder is live on the box** (§5).

**Scope qualifier.** qbp-compute-unit#94 (§6): MDCU is spike code; every result is research-grade at most.

**Binding condition (notary; same shape as round 1's seq 276/279).** The H-FO prior does not soften the decision rule, which must be able to return H-CONT or inconclusive from data alone (§1, §3).

**Freeze procedure.** When the §8 gates are in, the director commits the body verbatim as `spikes/prereg/qbp-kz-g2-r3-prereg-FROZEN-v1.md`; the only permitted edits at the freeze are the status block and §8. The sha256 is posted on QBP#797. From the freeze onward no rule, seed range, number or threshold in the file is edited; any change is a new, dated amendment file that cites the frozen one, written before the data it affects.

**Predecessor texts (cited, read-only, not edited):**
- `spikes/prereg/qbp-kz-g2-r1-prereg-FROZEN-v1.md` (QBP, sha256 `785e0ee2c81740b25fbeb9dfa5bb26e22159d8b7b221de2bdb75c2f7a6f51e28`) + amend-1 (`f043b28012f5eba000b3492b860ecad94a6a0fcee6585c575b1324b69ded39b5`) — "R1-FROZEN" below.
- `spikes/qbp-kz-g2/qbp-kz-g2-r1-results.md` (QBP PR #796) — "the round-1 record" below. Harness at qbp-compute-unit `aa04139` (`spike/qbp-kz-g2-r1-harness`), binary sha256 `51a2ed9c…3900e7f7`.
- `mdcu-kz-prereg-FROZEN-v1.md` (qbp-compute-unit `7ac4ed0`, sha256 `176bdce2…a676a5f`) — "FROZEN-v1" below, for the model, units, step rule and η.
- Rounds "1–2" in the tracker's wording = the mdcu-kz round-1 Stage 0b probe at τ_Q = 1600 (qbp-compute-unit#92/#93) and qbp-kz-g2 round 1 (QBP#793, PR #796); this file calls them "the two ramp rounds".

## 1. Question

The two ramp rounds (QBP#793, PR #796) read **H-first by the frozen ramp rule (a)**: the hysteresis gap does not close over τ_Q = 1600–12800 (0.5171 → 0.4769, OLS slope −0.039 ± 0.009). A **post-hoc, not pre-registered** look at the same raw files (QBP#797 table) shows the two branches' drop temperatures converging from both sides — cooling drop 0.977 → 1.094, heating drop 1.198 → 1.172 — with the loop width falling 0.221 → 0.149 → 0.104 → 0.078 in T over τ_Q 1600 → 12800, ≈ τ_Q^−0.5, the branches converging toward T ≈ 1.15. That trend is consistent with **both** a first-order transition under a finite-rate sweep (nucleation closer to coexistence when given more time) **and** a continuous one (a finite-rate lag that closes as τ_Q → ∞); no further ramp bracket decides it. The decisive test is the **equilibrium** one, no ramp, at fixed T, as a function of L.

- **H-FO (first-order):** at some T in the window the equilibrium energy-density distribution is **double-peaked**, with a valley between the peaks that **deepens with L**; the energy Binder cumulant **V_L = 1 − ⟨e⁴⟩ / (3 ⟨e²⟩²)** has a minimum over T that **stays below 2/3 as L grows** (the two-state limit).
- **H-CONT (continuous):** the energy-density distribution is **single-peaked at every T**, narrowing with L; **V_L → 2/3** at every T as L grows (the Gaussian limit).

**Pre-data prior: H-FO favoured, ≈ 75 %.** Two grounds, both already on file: (i) the order parameter is the projector Π onto the 3-plane, a traceless symmetric tensor carrying a Landau cubic invariant tr(Π_tl³), the nematic Q-tensor class whose ordering transitions are first-order by that mechanism (R1-FROZEN §1; inter#249 wisdom); (ii) the two ramp rounds (P1 hit at ≈ 70 %). **The prior does not enter the rule.** §3 is written so that H-CONT and inconclusive are each reachable from data alone, and the notary's binding condition is that this be checkable on the frozen text.

**What "equilibrium" means here (scope, not a claim) [drafter's note for the director].** The sampler is the same Model-A step rule as the ramp rounds (FROZEN-v1 §2a: synchronous Stiefel gradient step with η = 0.1 plus Gaussian noise of variance 2ηT, Gram–Schmidt), run at **fixed T** long enough to forget the random start. Its stationary distribution is the stationary distribution of that discrete dynamics at η = 0.1, which approximates the Boltzmann distribution of the chordal energy with an O(η) discretisation error; this round does **not** re-tune η and does **not** claim the exact Boltzmann ensemble. Every outcome row in §3 is a statement about "this model, this energy, this sampler (Model A, η = 0.1)", matching the claim scope of the ramp rounds.

Not asked here: the topology of G₂/SO(4), any KZ exponent, any defect count, the S³ null, the −φ² landscape, M1–M3, any CD speed claim, any value of T_c beyond the window, any critical exponent under H-CONT.

## 2. Design (equilibrium sampling at fixed T) — all numbers [proposal]

**What runs.** Equilibrium Model-A sampling at fixed T on a T grid, at three lattice sizes, several independent seeds per (L, T). No ramp, no hold-then-cool, no hysteresis metric, no detector, no ladder, no null arm, no Stage 0a re-run. T_c is **not** re-derived (round 1's value is used only to place one grid point).

**T grid [proposal].** Nine points **T ∈ {1.08, 1.10, 1.12, 1.14, 1.16, 1.18, 1.20, 1.22, 1.24}** (step 0.02, units of J), bracketing the converging drop temperatures at τ_Q = 12800 (1.094 cooling, 1.172 heating) and the apparent coexistence ≈ 1.15, plus a **tenth point at round 1's T_c = 1.0666262219986817** (the R1-FROZEN §2 literal; it sits just below the grid and is included so the equilibrium curve covers the ramp rounds' T_c). **Ten T points in all**, indexed t ∈ 0..9 in ascending T: t = 0 is T_c, t = 1..9 are 1.08 … 1.24. The T values are typed into the harness as a frozen table, not computed.

**Lattices.** **L ∈ {8, 12, 16}**, periodic, indexed l ∈ {0: 8, 1: 12, 2: 16}. L = 16 is the ramp rounds' size; 8 and 12 give the finite-size direction. (No L = 24: at L³ scaling it would cost 3.4× an L = 16 process; see §5.)

**Per run (one seed at one (L, T)) [proposal].** Start state i.i.d. Haar-G₂ planes seeded by the run seed (FROZEN-v1 §2a, as implemented in `NewKZPlaneFieldHaar`); **burn-in 5,000 plane-steps** at T, discarded; then **50,000 sampling steps** at T; **S and the energy density e are recorded after every 10th step** of the sampling phase → **5,000 (S, e) samples per seed**. The burn-in is not recorded (director's r2 decision: nothing in §3 reads it; the equilibration check is the per-run τ_int and the blocked errors below). **Energy density** e = E / (3 L³), the chordal bond energy Σ_bonds (3 − ‖F_a F_bᵀ‖_F²) per bond (J = 1; e ∈ [0, 3]; zero at perfect alignment), as computed by `KZPlaneField.Energy()` divided by the bond count. The Binder cumulant is scale-invariant in e but not shift-invariant, so the energy zero is fixed here: the chordal energy's own zero, no subtraction.

**Seeds per (L, T).** **4 independent seeds**, each its own Haar start and its own noise stream. Each (L, T) point pools its 4 seeds' samples for the histogram and V_L (§3) and also reports them per seed.

**Processes.** **One driver process per (L, T)**, running its 4 seeds **sequentially**, so each process is independently capped (2 h wall, pause file, RSS, output — §5). 3 × 10 = **30 processes** for the full design; they run **one at a time**. Each process writes `spikes/qbp-kz-g2/raw/qbp-kz-g2-r3-eq-L<L>-t<t>.jsonl` (t = the T index, two digits) with a meta sidecar, and its sha256 is posted with the others before any analysis (§7). A kill in one process voids that (L, T) point; the point is re-run on the reserved re-run block under a dated amendment (below), and no rule is evaluated on a partial set (§3 harness-kill row).

**Autocorrelation [proposal].** For each run the integrated autocorrelation time τ_int of e (in sampling steps) is estimated from the recorded series by the standard windowed sum (Sokal window, c = 6) and reported with n_eff = 50,000 / (2 τ_int); the analyzer also reports the blocked standard error of ⟨e⟩ at block sizes 10, 50, 250 records. **Under-sampling flag:** a run with n_eff < 20 (τ_int > 1,250 steps) is flagged `undersampled`; §3 says what the flag does.

**Seeds — block [proposal] 6000–6119, re-run block 6120–6239.** 10 T × 3 L × 4 seeds = 120 seeds. **Deterministic mapping:** seed = **6000 + 40·l + 4·t + j**, l ∈ {0: L = 8, 1: L = 12, 2: L = 16}, t ∈ 0..9 the T index above, j ∈ 0..3 the replicate. So L = 8 runs 6000–6039, L = 12 runs 6040–6079, L = 16 runs 6080–6119; within an L block, T index t runs 4 consecutive seeds. Re-run block: the same formula + 120 (6120–6239), selectable only under a dated amendment that names the (L, T) point (as `-rerun-amend-sha` did in round 1). **The seeds are derived from (l, t) in the driver, never typed.** Any reduced option (§5) uses the same formula and simply leaves the unselected (t, j) seeds unused.

*Evidence the block is free (harness `aa04139`, read 2026-10-30):* `KZClassifySeed` (`emulator/mdcu/kzseeds.go`) has no case between 5979 (the round-1 re-run block's top) and 9100 (the "used" range), so every seed in 6000–6239 is `KZSeedFree` today; `kzlattice_test.go:252` asserts 5980 is free. A grep of every `.go` and `scripts/*` file in `emulator/` for literals in 5980–9099 finds no seed in 6000–6239: `6000` is `maxSteps` in `pillar2.go`, `6097` is a canonical metric in a test log string, `6400` is a τ_Q. The nearest literal seeds outside the kz registry are the R3Q2 benchmark seeds 8000–8090 / 8400–8490 (`r3q2_w2diag_test.go`) and a q1grid smoke seed 9000; smokes and unit tests of the kz harness use 12000+/13000+. The round-1 table of used ranges is carried forward with this row added:

| Range | Use | Source |
|---|---|---|
| 3000–3199 | R3 | FROZEN-v1 §7 |
| 4000–4399, 9960–9969 | R4 | FROZEN-v1 §7 |
| 9100–9979 (scattered; 9970–9979 tests) | tests and probes | FROZEN-v1 §7 |
| 5000–5199 | mdcu-kz main arm (ladder; never run) | FROZEN-v1 §7 |
| 5200–5399 | mdcu-kz S³ null (never run) | FROZEN-v1 §7 |
| 5400–5599 | reserved, split-G₂ round 2 | FROZEN-v1 §7, amend-1 §4 |
| 5600–5629 | mdcu-kz Stage 0 (used) | FROZEN-v1 §5, round-1 record |
| 5630–5649 | saturation fields (used) | amend-1 §4 |
| 5650–5849 | S³ null run tilt seeds | amend-1 §5 |
| 5850–5889 | σ* calibration tilt seeds (used) | amend-1 §5 |
| 5900–5939 | qbp-kz-g2 round 1 run block (used) | R1-FROZEN §2 |
| 5940–5979 | qbp-kz-g2 round 1 re-run block (reserved, unused) | R1-FROZEN §2, amend-1 |
| 8000–8090, 8400–8490, 9000 | R3Q2 / q1grid benchmark and smoke seeds (outside the kz registry) | `r3q2_w2diag_test.go`, `q1grid_test.go` |
| 9930–9949 | probe (used) | FROZEN-v1 §6 |
| 12000+, 12300+, 13000+, 13300+ | smokes, unit tests (free seeds) | amend-1 §4, §5 |
| **6000–6119** | **this round, run block [proposal]** | this file |
| **6120–6239** | **this round, reserved re-run block [proposal]** | this file |

**Dynamics — identical to the frozen predecessor, cited not restated.** FROZEN-v1 §2 (model, energy, Model A), §2a (units; step rule; Haar start; **η = 0.1 reused, the descent test is not re-run**). Noise stream: `KZNoiseRNG(seed, stream)` with a **new stream constant for this mode** (e.g. `kzStreamEq = 100002`, beside Stage 0a's 100000 and Stage 0b's 100001), so no equilibrium run shares a noise stream with any ramp run of the same seed.

**Harness: what exists at `aa04139` (read 2026-10-30) and what this round must add.** On the qbp-compute-unit spike branch; reviewed and pushed by qbp-cu-implementor; tests first; **the frozen round-1 code (`KZStage0bRun`, `KZStage0bRunWithSeries`, `KZExecuteStage0bOnly`, `-run-0b`, `-analyze-0b`, the R2/R3/R4 paths) is called or left alone, never edited**, which the harness PR's diff shows.

| # | Needed | Exists today | Must add |
|---|---|---|---|
| 1 | Energy density per recorded step | `KZPlaneField.Energy()` (`kzlattice.go:152`, total over 3N bonds) exists; **no harness mode records it** — `KZArm` exposes `Step`/`Order`/`Detect` only, `kzSeriesArm` records S reads only, the `stage0b` record carries S per seed per record and no energy | an energy read on the main arm (`KZMainArm.F.Energy()/(3N)`) at the record cadence, in the per-seed `e_series`; a test that e of an aligned field is 0 and of a Haar field is positive |
| 2 | Fixed-T equilibrium mode | **No equilibrium/hold mode with recording exists.** Stage 0a (`KZStage0aRun`) has an equilibrate-then-measure loop (Equil then Meas steps) but chains states across a cooling scan and keeps only the mean S per T; Stage 0b has the **200-step hold at T_hi** (`KZHoldSteps`), fixed length, nothing recorded during it | **`KZEqRun`** (new): Haar start → burn-in → sampling at fixed T, recording (S, e) every `rec_every` steps, per seed; **`KZExecuteEqOnly`** (new orchestrator, pattern of `KZExecuteStage0bOnly`: guards → meta → per-step `Check` via `kzTick` → `eq` record → `end`/`abort`) |
| 3 | Driver mode | `-run-0b`/`-smoke-0b` (`cmd/mdcu-kz/kzg2.go`) with per-step wall/pause/RSS/output checks and the meta fields (`prereg_sha`, `binary_sha256`, `code_sha`, `loadavg_start/end`, `pause_present_at_start`, caps, `exit_code`) | **`-run-eq -L <8|12|16> -t <0..9> -prereg-sha <64 hex>`** (seeds derived from (l, t); `-first-seed` refused), **`-smoke-eq`** on free seeds (13000+), `-dry-run` printing the plan; the same check closure; **peak RSS (`MemStats.Sys` high-water) written in the `end` record** (closes the round-1 disclosure 3 / qbp-compute-unit#94 AC2 follow-up) |
| 4 | Seed class + guard | `KZSeedClass` registry with `KZSeedKzG2R1`/`…Rerun` and `KZCheckKzG2R1Seeds`; `KZCheckSmokeSeeds` refuses every non-free seed | **`KZSeedKzG2R3`** (6000–6119) and **`KZSeedKzG2R3Rerun`** (6120–6239); `KZKzG2R3Seeds(l, t, rerun)` and `KZCheckKzG2R3Seeds`; guard tests (every other mode, smokes included, refuses 6000–6239 → exit 4 before any step; `-run-eq` refuses everything else) |
| 5 | Record schema | `stage0b` record: grid, cool/heat seed means, `cool_t`/`heat_t`, `cool_series`/`heat_series`, max gap + idx + T, jumps + idx + T, reason | **`eq` record:** `L`, `T`, `t_index`, `seeds`, `burn_in`, `sampling`, `rec_every`, per seed `s_series`, `e_series` (and the burn-in trace if kept), per seed `mean_e`, `mean_s`, `tau_int_e`, `n_eff`, `undersampled`; pooled `mean_e`, `var_e`, `binder_v`; `noise_stream`; the `meta` fields of row 3 |
| 6 | Analyzer | `-analyze-0b` (four files, refuses partial sets, OLS slope, jump report) | **`-analyze-eq`** over all 30 (or the reduced set's) raw files: refuses a partial set; per L: common bins, histograms per T, V_L(T), V_min(L) and its T; the bimodality test; rule (a)/(b)/(c) with precedence; the secondaries of §3; a text report + the plot data |
| 7 | Wrapper | `scripts/run-kz.sh 0b <tau> <raw> <frozen>` (go test → quiet-load wait → pause pre-check → `GOMAXPROCS=1 nice -n 19 taskset -c 7`, sidecar with load, binary sha, pause state) | verb **`eq <L> <t> <raw-out> <frozen.md>`**, same discipline; the run loop over the 30 (L, t) pairs is the runner's, one process at a time, never a parallel launch |
| 8 | Noise stream | `kzStreamStage0a = 100000`, `kzStreamStage0b = 100001` | `kzStreamEq = 100002` [proposal], recorded in `meta` |

## 3. Decision rule (pre-data; to be frozen verbatim) — thresholds [proposal]

**Statistics.** For each L, pool the samples of all T and all seeds at that L and set **60 equal-width bins over that pooled min–max of e** (common bins across T at a given L, so the histograms at different T are comparable) [proposal]. For each (L, T): the histogram h_{L,T}(e) of the 4 seeds' 5,000 samples each (20,000 samples), and the energy Binder cumulant **V_L(T) = 1 − ⟨e⁴⟩ / (3 ⟨e²⟩²)** over the same 20,000 samples (plain moments of e, the energy zero as in §2). **Primary statistic:** **V_min(L) = min over the ten T of V_L(T)**, with T*(L) the T at which it occurs.

**Bimodality test [proposal].** The histogram at (L = 16, T*(16)) is **bimodal** iff, after a 3-bin moving-average smoothing, it has **two local maxima** (each a bin strictly above both neighbours; the two tallest if more) **separated by a valley whose minimum density is < 0.5 of the lower of the two peaks**. A histogram failing this is **unimodal** for the rule. The same test is reported, non-gating, at every (L, T).

**Rule, with δ = 0.02 [proposal]:**

- **(a) H-FO** iff **V_min(16) < 2/3 − δ** **and** **V_min(16) ≤ V_min(12) + ε and V_min(12) ≤ V_min(8) + ε** with **ε = 0.01** (the minimum deepens, or at least does not rise beyond noise, with L; director's r2 decision) **and** the histogram at (16, T*(16)) is **bimodal** by the test above.
- **(b) H-CONT** iff **V_min(16) ≥ 2/3 − δ** **and** the histogram at **every** T is **unimodal at L = 16**.
- **(c) inconclusive** otherwise (e.g. V_min(16) < 2/3 − δ but not deepening with L; or deepening but unimodal; or V_min(16) ≥ 2/3 − δ but some L = 16 histogram bimodal).

**Precedence: (a), then (b), then (c).** (a) and (b) are mutually exclusive by their first clauses, so the order matters only for the record. The rule is total: every data set lands in exactly one row.

**Under-sampling sub-clause [proposal].** If any of the 4 runs at (16, T*(16)) is flagged `undersampled` (§2: n_eff < 20), rule (a) **cannot fire**; the round reads **(c) inconclusive (sampling)** with the flagged τ_int values reported, and a longer-sampling round is a new pre-registration. Flags at other (L, T) are reported and do not gate. (This keeps a phase-locked seed — a seed that never leaves one phase in 50,000 steps — from being read as evidence of a deep valley.)

**Harness kill (per-process structure).** A kill in any process voids that (L, T) point, and **no part of the rule is evaluated until all 30 (or the reduced set's) points have completed**: the killed point is re-run on its reserved re-run seeds (§2, block 6120–6239, same (l, t)) under a dated amendment that cites the kill's exit code and meta; if the re-run cannot happen within the round, the round reads **"inconclusive (span)"** with no (a)/(b)/(c) reading. No raw file is opened by anyone until all shas are posted (§7).

**Secondary, non-gating:**
- **Coexistence temperature estimate:** at L = 16, the T (interpolated between grid points on the two peaks' weights) at which the two histogram peaks have **equal weight** (equal-weight criterion), reported only if the bimodality test passes at ≥ 2 grid points; otherwise "no coexistence T readable".
- **Latent-heat proxy:** the separation Δe of the two peak positions at (16, T*(16)) if bimodal, and its trend over L at each L's own T*(L).
- **Per-seed max-step scan** (the lesson of round 1's P5): for each run, the largest single-record change of S and of e; and the **phase-locking count** — the number of seeds at (16, T*(16)) whose e-series stays on one side of the valley for the whole 50,000 steps.
- **S histograms** at every (L, T), the same bimodality test applied, descriptive only.
- V_L(T) curves for the three L on one plot; the histogram panels at the three L at T*(16); the per-seed equilibration traces (Human Visual Review material).
- τ_int and n_eff per run, in a table.

**What each outcome does and does not claim** (the outcome rows of the QBP#797 AC2 planning-consequence table, to be posted on the issue before any data, naming the anchor id `HYP-g2so4-planefield-continuous-transition`):

| Outcome | Claims | Does not claim | Write-back (§7) |
|---|---|---|---|
| **H-FO** | For this sigma model (chordal energy, Model-A sampler at η = 0.1, periodic L ≤ 16), the equilibrium energy distribution is two-state near T ≈ T*(16) and the Binder minimum does not approach 2/3 from L = 8 to 16: **first-order ordering transition**, consistent with the Landau cubic mechanism and with the ramp rounds. | Nothing about the topology of G₂/SO(4); no latent heat value beyond the proxy; no statement about other energies, dynamics, η or L > 16; not a proof (three sizes cannot exclude a crossover at larger L). | Anchor `HYP-g2so4-planefield-continuous-transition`: `decision_state` → **falsified** (the KZ premise "continuous transition" falls), discharged by this record, with the §6 qualifier; QBP#776 E6 note sharpened ("not continuous: first-order by the equilibrium finite-size test at L ≤ 16"); the KZ ladder on this model stays closed. |
| **H-CONT** | The equilibrium energy distribution is single-peaked at every T in the window at L = 16 and the Binder minimum is within δ of 2/3: **no first-order signature at L ≤ 16**; the ramp rounds' hysteresis is a **finite-rate (dynamical) effect** of Model A at these τ_Q, not thermodynamics. | Nothing about exponents or universality class; no value of T_c beyond "in or near the window"; nothing about L > 16. The ramp rounds' E rows stand as recorded (they were about hysteresis on their rate scale). | Anchor stays **open** (not falsified by this test); the ramp rounds' "falsified on the rate scale" row is **reclassified as a dynamics statement** in the QBP#776 E6 note; the **KZ premise is restored**; a **new ladder item** (a ramp long enough that the hysteresis closes) needs its **own pre-registration and beekeeper approval** — off this approved list; the Landau-cubic prior is recorded as a pre-data miss. |
| **inconclusive** (rule (c), incl. "(sampling)") | Neither signature is clean at L ≤ 16 with this sampling. | Either hypothesis. | QBP#776 note recording V_min(L), T*(L), the bimodality readings and τ_int; anchor stays open; any extension (larger L, longer sampling, finer T) is a new pre-reg. |
| **harness kill** (any §5 abort) | Nothing: the killed point is re-run on its reserved seeds under a dated amendment before any rule is evaluated; if it cannot be, the round reads "inconclusive (span)". | Anything; no partial-set reading. | None; the abort and the amendment are recorded on QBP#797. |

## 4. Predictions on file (director's, pre-data) — [proposal]

| # | Prediction | Probability |
|---|---|---|
| P1 | H-FO (rule (a) fires) | ≈ 75 % |
| P2 | H-CONT (rule (b) fires) | ≈ 10 % |
| P3 | inconclusive (rule (c), any sub-reading) | ≈ 15 % |
| P4 | the equal-weight coexistence T at L = 16 lies in **[1.12, 1.18]** (readable, and in that interval) | ≈ 70 % |
| P5 | **V_min(16) < 0.60**, given H-FO | ≈ 50 % |

P1–P3 are exhaustive and sum to 100 %. Freeze-check question (as in round 1): does the order parameter admit a cubic invariant? Yes (tr(Π_tl³)) — that is why P1 is the prior, and why §3 is written so that P2 and P3 remain reachable; the notary's §8 pre-check is that this holds on the frozen text.

## 5. Kills, aborts and resources — [proposal]

**Aborts (any one → that process's (L, T) reads "harness kill, no reading" and the §3 harness-kill row governs; nothing is re-run without a dated amendment). Each process carries its own set:**
- wall > **2 h** per process → exit 2;
- pause file present at start or at any step (the driver checks at start and at every step via `kzTick`) → exit 3; the wrapper's pre-check on the same file → exit 4 (path `$HOME/.federation-watcher/box-pause/mdcu`, deming's, as in `run-kz.sh`);
- seed guard: any seed outside the derived 4-seed sub-block of (l, t) in `-run-eq` (or outside its re-run sub-block under a dated amendment), or any other mode (smokes included) touching 6000–6239 → exit 4, before any step;
- wrapper `go test ./mdcu -run TestKZ` failure before the run → exit 10; quiet-load wait timeout → exit 11;
- NaN / non-finite S or e → exit 6; runtime `Sys` > **100 MB** or output > **10 MB** per process → exit 5.

**Resource estimate (upper bounds, written before the run).** **Rate assumption:** round 1 measured **11.9 ms per plane-step at L = 16** (η = 0.1, one `OrderS` read per 10 steps; the round-1 record, Resources row). This round assumes **cost ∝ L³** (the step is a full sweep of the 3N bonds plus a per-site Gram–Schmidt; nothing in it scales otherwise), so **L = 12 ≈ 0.422×** and **L = 8 ≈ 0.125×** the L = 16 rate — an assumption, not a measurement; the runner's `-smoke-eq` at L = 8 and 12 (free seeds, ~1,000 steps) checks it before the go and the meta records the realised rate. The added `Energy()` read (one bond sweep per 10 steps) is < 10 % of the step cost; a **10 % margin** is added to the totals for it.

**Full design: 10 T × 3 L × 4 seeds; per process 4 × (5,000 + 50,000) = 220,000 plane-steps, 20,000 (S, e) records.**

| L | ms / step (assumed) | wall per process | % of 2 h cap | processes | wall per L |
|---|---|---|---|---|---|
| 8 | 1.49 | 327 s ≈ 5.5 min | 5 % | 10 | 3,272 s ≈ 0.91 h |
| 12 | 5.02 | 1,104 s ≈ 18.4 min | 15 % | 10 | 11,045 s ≈ 3.07 h |
| 16 | 11.9 (measured) | 2,618 s ≈ 43.6 min | 36 % | 10 | 26,180 s ≈ 7.27 h |
| **total** | | | | **30** | **40,497 s ≈ 11.25 h; with the 10 % energy-read margin ≈ 12.4 h** |

Every process fits its 2 h cap with ≥ 2.7× headroom (the longest, L = 16, at 36 % of the cap, 48 min with the margin). **The total is stated honestly: ≈ 11–12.5 h of serial box time**, i.e. more than one quiet night; at one process at a time with the quiet-load wait before each, it is a two- to three-session run under deming's warp-builder schedule (live-test seq 4051: **no process starts while a warp builder is live**). Steps total: 30 × 220,000 = **6.6 M plane-steps** (13.5× round 1's 488,000).

**Reduced option [proposal, for the director]: 7 T × 3 L × 3 seeds** — T ∈ {1.08, 1.10, 1.12, 1.14, 1.16, 1.18, 1.20} (t = 1..7; drops T_c, 1.22 and 1.24; still brackets 1.094, 1.15 and 1.172), j ∈ 0..2; same seed formula, the unselected seeds stay unused. Per process 3 × 55,000 = 165,000 steps.

| L | wall per process | % of 2 h cap | processes | wall per L |
|---|---|---|---|---|
| 8 | 245 s ≈ 4.1 min | 3 % | 7 | 1,718 s ≈ 0.48 h |
| 12 | 828 s ≈ 13.8 min | 12 % | 7 | 5,798 s ≈ 1.61 h |
| 16 | 1,964 s ≈ 32.7 min | 27 % | 7 | 13,744 s ≈ 3.82 h |
| **total** | | | **21** | **21,261 s ≈ 5.91 h; with the margin ≈ 6.5 h** |

The reduced option halves the wall at the cost of 3 instead of 4 seeds per point (the pooled histogram has 15,000 instead of 20,000 samples; the phase-locking secondary is weaker) and of the T_c point. **Director's r2 decision: the reduced option is the design of this round** (21 processes, ≈ 6.5 h of serial box time with the margin; T_c = 1.0666 is dropped because both ramp branches now sit above it, and 1.22/1.24 because the heating branch has already dropped by 1.20). The full-design table stays above as the sizing reference; §3 reads "all 21 points" wherever it says 30; the seed formula and the T index t = 1..7 are unchanged.

- **RAM:** one lattice of L³ × 14 floats (L = 16: ≈ 0.46 MB) plus the per-seed series held until the record is written (4 × 2 × 5,500 floats ≈ 0.35 MB); **< 100 MB** with the Go runtime, the cap at 100 MB (`MemStats.Sys`, checked every 256 steps as in round 1); **peak `Sys` is written in the `end` record this time.**
- **Disk:** per process 4 seeds × 2 series × ≤ 5,500 records × ~20 bytes ≈ 0.9 MB plus meta; **< 10 MB per process** (cap at 10 MB); ≈ 30 MB raw across the 30 files (≈ 20 MB reduced).
- **Kill condition:** each process is bounded by construction (fixed step count) **and** by its own 2 h wall cap; no open-ended loop exists.
- **Load discipline as round 1:** **one lattice at a time**, `GOMAXPROCS=1`, core-pinned (`taskset -c 7`), `nice -n 19`, `wait-quiet.sh` (1-min load ≤ 1.0 on three consecutive 20 s samples) before each process, `load_start`/`load_end` in each sidecar and meta; unit tests run **before** the quiet-load wait; **run only when no warp builder is live** (deming's schedule, live-test seq 4051); the pause file stops any process cleanly at the next step.

Feasibility sign (qbp-cu-implementor) binds to the frozen numbers above; after the freeze it re-opens only if L > 16, GOMAXPROCS = 1 is dropped, the step counts change, or the smoke-measured rate at L = 8/12 exceeds the L³ assumption by more than 1.5× (then the totals are re-stated in a dated amendment before the go).

## 6. Scope qualifier (qbp-compute-unit#94, beekeeper direction 2)

Every E row this spike produces carries, verbatim: **"as implemented in the spike harness at <sha>; napkin-grade code, not engineered or notarised"**. No result of this round is cited above research grade until the MDCU emulator is notarised. The ramp rounds' limits carry over: nothing here is a CD speed claim, and nothing bears on the manifold's topology. Added for this round: every claim is about the stationary distribution of the Model-A sampler at η = 0.1 (§1 note), on periodic lattices L ≤ 16, in the T window of §2.

## 7. Record and write-back (four-way, as round 1)

1. **Raw sha256 before analysis.** The runner posts the sha256 of **every raw jsonl file** (30, or 21 reduced) and of the binary on QBP#797, **all together**, before anyone reads a histogram or a cumulant, exactly as round 1 posted its four shas together (mdcu-spike seq 338). The analysis then runs on the hashed files; the record cites every hash. No raw file is opened by anyone — the director included — before that post.
2. **Record.** One results file `spikes/qbp-kz-g2/qbp-kz-g2-r3-results.md` + `spikes/qbp-kz-g2/raw/` (the raw jsonl `qbp-kz-g2-r3-eq-L<L>-t<tt>.jsonl`, their `.sha256`, their meta sidecars) + `plots/` + the runner reports, as a QBP PR (tier 2 docs; beekeeper merge). The results file states the outcome from §3 by rule, lists the §3 secondaries, reproduces the V_L(T) plot and the histogram panels, records every prediction's hit/miss as a first-class row, carries an independent recompute (stdlib Python reading only the raw series, as round 1's `qbp-kz-g2-r1-recompute.py`), and carries the forging-doc §3 rule 7 write-back table with columns **claim · where stated · E before → after (notary-verified) · F · PR**, each E row with the §6 qualifier.
3. **Write-back targets.** The anchor **`HYP-g2so4-planefield-continuous-transition`** (writer lane, qbp-implementor: `decision_state` per the §3 outcome row, `discharged_by` = this record's PR, the §6 qualifier attached) and **QBP#776** (E6 framing) in every outcome; if H-CONT, a new QBP research-queue item for the long-ramp ladder, filed by the director, needing its own pre-reg and beekeeper re-approval.
4. **E-verify.** @notary-implementor verifies each E move, the anchor write, and that the outcome was read by the frozen rule, not by the prior (the binding condition).

## 8. Confirmation gates (freeze gates; all unticked in DRAFT r1)

- [ ] **runner read** — a named runner (antigravity if live, otherwise the director-supervised sub-agent) has read this text, accepted, and run `-smoke-eq` at L = 8/12/16 on free seeds to check the §5 rate assumption.
- [ ] **@qbp-cu-implementor (feasibility + envelope):** the §5 estimate and limits hold (steps, the L³ assumption against the smoke rates, RAM, disk, GOMAXPROCS = 1, per-process 2 h cap, the honest total); the seed block 6000–6239 checked free against the registry and every smoke/test; the §2 harness additions reviewed and pushed on the cu spike branch with the frozen round-1 code untouched.
- [ ] **@notary-implementor (decision-rule condition):** §3 can return H-CONT or inconclusive from data alone; the prior in §1/§4 does not enter the rule; the precedence and under-sampling sub-clauses are acceptable; the anchor id and its kill condition match the rule.
- [ ] **@deming (box-safety):** clear on the written upper bounds of §5 (L ≤ 16, GOMAXPROCS = 1, 2 h wall cap per process, 100 MB / 10 MB caps, pause file, nice/taskset, one lattice at a time, no run while a warp builder is live).
- [ ] **@qbp-architecture (optional, cc):** the §3 outcome table checked against the AC2 planning-consequence rows posted on QBP#797.
- [ ] **Red Team + Gemini** on the draft (QBP#797 AC1).
- [ ] **@qbp-oppenheimer (director) — choose full or reduced option (§5); freeze:** FROZEN-v1 committed verbatim (status block and this §8 the only edits), pushed, sha256 posted on QBP#797.

**Frozen-text rule.** After the freeze, changes only as dated amendment files (`…-FROZEN-v1-amend-N.md`) that cite the frozen file's sha and are written before the data they affect. **No amendment is filed between the run go and the §7.1 raw-sha post; anything found during the run is a §5 harness kill, and any re-run is on the reserved seeds under a dated amendment.** The frozen file is never edited.

No part of this is binding until it is frozen and the gates above are ticked.
