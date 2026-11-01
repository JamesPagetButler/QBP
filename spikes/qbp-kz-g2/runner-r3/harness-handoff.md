# qbp-kz-g2 round 3 — harness build hand-off (for the reviewer)

Builder: director-supervised sub-agent (Claude Fable 5.1), 2026-10-31. Director: qbp-oppenheimer.
Spec: `spikes/prereg/qbp-kz-g2-r3-prereg-FROZEN-v1.md` at QBP `ae37319`, sha256 recomputed
`132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623` — **matches**.
Runner-read report folded: `/tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-r3-runner-read.md`.

**Not done, by instruction:** no push; no §2 production seed (6000–6239) run; no frozen round-1 function edited; no Lean.
`pgrep -af 'lean|lake|mdcu'` was empty before every build/test; everything ran single-process.

## 1. Branch

| | |
|---|---|
| repo / worktree | `/home/prime/Documents/QBP-CU-mdcu/.worktrees/kz-r3-build` (qbp-compute-unit spike clone) |
| branch | `spike/qbp-kz-g2-r3-harness` |
| base | `aa041391e934e6b41f02cf8f79a4e489ca928360` (= round-1 harness `aa04139`, `spike/qbp-kz-g2-r1-harness`) |
| HEAD | `45639ed11ff516c70be7263136c1cb0a794295b2` |
| pushed | **no** |
| `git status --porcelain` after build | empty (`emulator/bin/` is gitignored) |
| built binary sha256 | `89e7fd539a507ec7d94c00fd12c54bd741de5c14c60135244e3f2afb9a98b899` (`go build -o bin/mdcu-kz ./cmd/mdcu-kz` at HEAD; the runner rebuilds and posts its own) |

### Commits (oldest first)

| sha | message |
|---|---|
| `ffc9bd2` | spike(qbp-kz-g2-r3): tests first — seed table, T table, KZEqRun, Sokal, orchestrator, analyzer (FROZEN-v1 §2/§3) — *red by design* |
| `fb9d615` | spike(qbp-kz-g2-r3): seed classes 6000-6239, KZEqRun/KZExecuteEqOnly, Sokal tau_int, -analyze-eq library (§2 rows 1,2,4,5,6,8; §3) |
| `7dfc72d` | spike(qbp-kz-g2-r3): driver -run-eq/-smoke-eq/-analyze-eq, wrapper eq verb + box lease, guard tests (§2 rows 3,6,7; §5; §7.1) |
| `45639ed` | spike(qbp-kz-g2-r3): safety-net Check in the orchestrator guard tests (lesson of the seed-guard mutation check) |

Each message ends with the two trailers (Co-Authored-By: Claude Fable 5.1; Claude-Session).

## 2. Files

| file | status | one line |
|---|---|---|
| `emulator/mdcu/kzseeds.go` | **changed** (+101/−1) | registry: `KZSeedKzG2R3` (6000–6119), `KZSeedKzG2R3Rerun` (6120–6239) + their `String()` names + two `KZClassifySeed` cases — this is what makes every other mode (smokes included) refuse the block; appended `KZKzG2R3TTable` (frozen literal), `KZKzG2R3LSet`, `KZKzG2R3LIndex`, `KZKzG2R3Runs` (L = 8 excludes t ∈ {3,5,7}), `KZKzG2R3Starts` (haar, haar, aligned), `KZKzG2R3Seeds(l, t, rerun)`, `KZCheckKzG2R3Seeds`. No existing function in this file changed body. |
| `emulator/mdcu/kzeq.go` | **new** | `kzStreamEq = 100002`; `KZEqParams`/`DefaultKZEqParams` (5000/50000/10); `KZEqEnergyDensity` = `Energy()/(3L³)`; `kzEqStartField` (Haar / `NewKZPlaneFieldAligned(L, seed)`); `KZEqRun` (burn-in, then sampling with records after steps 10, 20, …; no step-0 record; Check every step via `kzTick`; NaN → 6); `KZSokalTauInt` (W = smallest W ≥ 6·τ(W)); `KZEqNEff`; `KZExecuteEqOnly` (guards → meta → eq → end with steps / ms_per_step / peak_sys_mb; abort carries steps). |
| `emulator/mdcu/kzeqanalyze.go` | **new** | complete-set loader (`KZEqLoad`) and `KZEqDecide` (all refusals of §3 r6), 60 fixed bins per L, 3-bin truncated smoothing, `KZEqBarrierOf` (strict maxima, ≥ 1 bin apart, 3σ floor on smoothed counts, h_valley 0 → 0.5, largest resolved barrier), jackknife σ, ε, blocked SE (never straddling), D_e/D_S, rule (a)→(b)→(c) with both gates and the sub-labels, secondaries, `KZEqFormatReport` (tables first), `KZEqPlotJSON`. |
| `emulator/mdcu/kzeq_test.go` | **new** | 11 tests: T table literal, seed table (27/81/6000–6118/no repeats), guards, start kinds, e(aligned)=0 / e(Haar)>0, record count 5000 & no step-0, Check in burn-in, Sokal (white noise, AR(1) φ=0.9, constant), orchestrator flow/guards/aborts. |
| `emulator/mdcu/kzeqanalyze_test.go` | **new** | 17 tests: binning/smoothing, barrier + floor, single-peak ripple → unimodal, pair choice, jackknife + ε, blocked SE, start dependence, Binder, max step, synthetic 27-point sets → H-CONT / H-FO / plain (c) / (c) sampling via the (a)-gate / **mutation: (b) with an undersampled L = 12 run** / metastability + precedence + locked-start two-state, coexistence T, 14 refusal cases, loader round-trip. |
| `emulator/cmd/mdcu-kz/kzeq.go` | **new** | `runEqMode` (`-run-eq`, `-smoke-eq`, plan, check closure, blind end line) and `analyzeEqFiles` (`-analyze-eq`, 27 files, optional `-plot-out`). |
| `emulator/cmd/mdcu-kz/main.go` | **changed** (+32/−4) | registers `-run-eq`, `-smoke-eq`, `-t`, `-analyze-eq`, `-plot-out`; adds the two modes to the mode list and to every mode-mixing refusal; dispatches to `runEqMode`; doc comment. The round-1 pipeline code is not touched. |
| `emulator/scripts/run-kz.sh` | **changed** | verb `eq <L> <t> <raw-out> <frozen.md>` (passes `-max-out-mb 10`, no `-tc`, `KZG2_RERUN_AMEND` → `-rerun-amend-sha`); the quiet-load wait + **box lease** loop (`flock -n` on `~/.federation-watcher/state/box-lease.lock`, holder line, BUSY → back to the loop) for `0b` **and** `eq`; sidecar for eq carries L, t, caps, lease, wall, exit, raw sha and the blind `# driver_end:` line. |
| `emulator/scripts/test-kz-guards.sh` | **changed** | 58 new `expect` cases for the r3 mode (seed block refused by every mode, `-run-eq` guards, dry-run plans, pause safety net, analyzer cross-refusals and partial sets, smoke-eq); the 0b-paused file is now kept until the eq block (cross-refusal) and removed there. |

Frozen round-1 code: `KZStage0bRun`, `KZStage0bRunWithSeries`, `KZExecuteStage0bOnly`, `-run-0b`, `-analyze-0b`, the R2/R3/R4 paths — **not edited** (table §4; `kzprotocol.go`, `kzrun.go`, `kzlattice.go`, `kzg2.go`, `kzg2analyze.go` have no diff at all).

## 3. Tests

```
GOMAXPROCS=1 go test -C /home/prime/Documents/QBP-CU-mdcu/.worktrees/kz-r3-build/emulator ./mdcu -run TestKZ -count=1
ok   github.com/JamesPagetButler/qbp-compute-unit/emulator/mdcu   7.705s
```

| suite | count | result |
|---|---|---|
| `go test ./mdcu -run TestKZ` (what the wrapper runs) | **120 PASS**, 0 FAIL (92 pre-existing + 28 new) | 7.7 s total (base: 6.8 s) |
| new r3 tests (`-run 'TestKZKzG2R3\|TestKZEq\|TestKZSokal'`) | 28 PASS | slowest 0.24 s (`TestKZEqDecideStartDependenceAndSubLabels`), next 0.19 s; all others ≤ 0.09 s |
| `bash scripts/test-kz-guards.sh` (from `emulator/`, built binary) | **131 ok**, 0 FAIL, exit 0 (58 new cases) | log: `/tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-r3-guards.log` |
| `go vet ./...` | clean | |
| `go build -o bin/mdcu-kz ./cmd/mdcu-kz` | clean | |

No test runs a production-length simulation: the orchestrator/eq-run tests use L = 4 with 4–7 burn-in and 20–50 sampling steps; the analyzer tests use synthetic iid / AR(1) series of 5,000 records (the frozen record count, so the 250-block SE has its 20 blocks) at 27 points.

### Mutation checks (applied by hand to the source, tests run, source reverted; HEAD has no mutant)

| # | mutant | killed by | note |
|---|---|---|---|
| 1 | `KZCheckKzG2R3Seeds` accepts the other block (re-run seeds without the flag / run seeds under it) | `TestKZKzG2R3SeedGuards` (0.00 s) and `TestKZEqOnlyFlowAndGuards` (0.01 s: "err abort 3: safety net: a guard accepted, want abort code 4") | **KILLED.** First run of this mutant (before `45639ed`): `TestKZKzG2R3SeedGuards` failed at once, but the orchestrator case had no `Check` and the accepted L = 16 config **stepped inside the test binary** until I killed it (go-test 10-min timeout hit; nothing written, Emit went to a slice; seeds 6220–6222's noise stream was consumed in-process only). Fixed in `45639ed`: every guard case now carries a Check that aborts at the start check (code 3) — an accepted guard fails before the first plane-step. Re-run of the mutant: killed in 0.01 s. **Disclosed here; the director decides whether this counts as touching the re-run block** (my reading: no raw file, no record, test binary only — but it was a real sweep of frozen-seed dynamics and the test design that allowed it is the defect). |
| 2 | the rule's `case d.B && d.UnderB` disabled ((b) fires despite an undersampled L = 12 run) | `TestKZEqMutationBGateUndersampledL12` (0.09 s) and `TestKZEqDecideStartDependenceAndSubLabels` (precedence case) | **KILLED** (7.6 s suite). |

Also exercised with the real binary (free seeds, scratchpad only, not in the repo): `-smoke-eq -L 4 -first-seed 13100` → 2 seeds × (500 + 2,000) = 5,000 steps, wall 1.0 s, 0.198 ms/step at L = 4, peak Sys 14.7 MB, exit 0; raw file has meta → eq → end only, no pooled statistic; `-analyze-eq` fed 27 copies of it → "refusing: … is a smoke-eq file; smoke output is never analyzed", exit 1. (Seeds 13100, 13101 touched — free range.)

## 4. Byte-identity of the frozen functions (body text, base `aa04139` vs HEAD)

| function | file | base sha256 (body, first 16) | HEAD | verdict |
|---|---|---|---|---|
| `KZRunRung` | kzprotocol.go | 19e3f44e51ddea47 | 19e3f44e51ddea47 | IDENTICAL |
| `KZInterp` | kzprotocol.go | 1c025b79e983030c | 1c025b79e983030c | IDENTICAL |
| `KZMaxJump` | kzprotocol.go | 68532afbb28d8cef | 68532afbb28d8cef | IDENTICAL |
| `KZStage0aRun` | kzprotocol.go | 4ae1215e7617af21 | 4ae1215e7617af21 | IDENTICAL |
| `KZStage0bRun` | kzprotocol.go | e1217d20ea5986d6 | e1217d20ea5986d6 | IDENTICAL |
| `KZStage0bAnalyze` | kzprotocol.go | 711f67d59798e71a | 711f67d59798e71a | IDENTICAL |
| `KZStage0bRunWithSeries` | kzprotocol.go | 85c1a453f20ab6b0 | 85c1a453f20ab6b0 | IDENTICAL |
| `KZExecute` | kzrun.go | 9417538b1f2e4046 | 9417538b1f2e4046 | IDENTICAL |
| `KZExecuteStage0bOnly` | kzrun.go | c9f1002d7b26ced4 | c9f1002d7b26ced4 | IDENTICAL |
| `(*KZPlaneField) Energy` | kzlattice.go | 7f2acaea8c0ba104 | 7f2acaea8c0ba104 | IDENTICAL |
| `(*KZS3Field) Energy` | kzlattice.go | 32b55aa15a77ef57 | 32b55aa15a77ef57 | IDENTICAL |
| `(*KZPlaneField) Step` | kzlattice.go | 89aa876342655f9d | 89aa876342655f9d | IDENTICAL |
| `(*KZS3Field) Step` | kzlattice.go | 70e396ff00655e49 | 70e396ff00655e49 | IDENTICAL |

(The three files themselves have **no diff** vs base: `git diff --stat aa04139..HEAD` lists only the 9 files of §2.)

## 5. Dry-runs

`-run-eq -L 16 -t 5 -prereg-sha 132f6a42… -max-out-mb 10 -dry-run` → exit 0, writes nothing:
```
mdcu-kz  mode=EQ  qbp-kz-g2 r3 equilibrium  prereg sha 132f6a42…
  L=16 (l=2)  t=5  T=1.15  eta=0.1  burn-in 5000  sampling 50000  record every 10 (5000 records/seed)  noise stream 100002
  seeds 6100,6101,6102 (3, run block 6000-6119)  starts haar,haar,aligned  steps 165000  out=qbp-kz-g2-r3-eq-L16-t05.jsonl  wall cap 2h0m0s  pause file /home/prime/.federation-watcher/box-pause/mdcu  caps Sys 100 MB out 10 MB
dry-run: nothing executed
```
`-run-eq -L 8 -t 3 -prereg-sha 132f6a42… -max-out-mb 10 -dry-run` → **exit 4**, refused before the plan (writes nothing):
```
refusing: L = 8 does not run t = 3 (FROZEN-v1 §2: L = 8 runs the seven coarse points t ∈ {0,1,2,4,6,8,9} only)
```
Also in the guard log: (8, 9) → seeds 6036,6037,6038; (12, 0) → 6040,6041,6042; (16, 5) under `-rerun-amend-sha` → 6220,6221,6222; `-run-eq -L 8 -t 0` against a pause file → exit 3 with meta + abort(`steps: 0`) only.

## 6. Harness choices and deviations — nothing silent; each is listed

Nothing in the frozen text was impossible to implement; the items below are where the text left a choice, where I matched an existing convention, or where a literal reading needed a degenerate-case guard.

| # | spec says | built | why |
|---|---|---|---|
| D1 | brief: `KZKzG2R3Seeds(l, t int, rerun bool) []int` | returns **`[]uint64`** | every seed in the registry (`KZClassifySeed`, `KZCheckSmokeSeeds`, `KZKzG2R1Seeds`, the driver) is `uint64`; an `[]int` would need conversions at every guard. Semantics unchanged. It returns **nil** for a point outside the design (bad l/t, or L = 8 at t ∈ {3,5,7}); the guard turns nil into the exit-4 refusal. |
| D2 | "a test that e of an aligned field is 0" | asserts **\|e\| ≤ 1e-12** | the frozen `Energy()` returns −8.5e-14 for an aligned L = 4 field (3 − ‖F Fᵀ‖² rounding). No clamp is applied to data; the test tolerance is the only accommodation. (Aligned-start runs can therefore record e ≈ −1e-14 at their first records only if T were 0; at T ≥ 1.08 the first record is far from 0.) |
| D3 | n_eff = 5000/(2·tau_int_rec) | **inside n_eff only**, τ_rec < ½ (or NaN) is floored at ½ (white noise); the recorded `tau_int_rec` is left as computed | τ(W) = ½ + Σρ can fall below ½ for an anticorrelated series; the literal formula then gives n_eff > N (and ∞/NaN at τ ≤ 0, which JSON cannot encode). The flag's direction is unaffected. Also: a series with zero variance has τ = ½, W = 0 by convention; if no W satisfies W ≥ 6·τ(W) before n − 1, τ at W = n − 1 is returned (very long correlation → flagged). |
| D4 | D_e = \|Δ\|/√(SE²+SE²) | Δ = 0 → D = 0; SE = 0 with Δ ≠ 0 → D = 1e6 (cap); else min(D, 1e6) | keeps D finite and JSON-encodable; the cap is far above 3. |
| D5 | "(c) inconclusive (sampling)" "in either case" | the label "sampling" is set **only when a gate actually blocked an (a) or (b) that would otherwise have fired**: (A ∧ underA) or (B ∧ underB); "metastability" iff ¬(a fires) ∧ ∃ start-dependent (L ∈ {12,16}) point with no resolved pair; plain (c) otherwise; sampling > metastability | this is the §3 text read with the r6 sub-label ruling; an undersampled run in a plain-(c) data set (neither A nor B) is reported in the τ table but does not relabel the outcome. **Please confirm this reading**; it is one line in `KZEqDecide` if the director wants "any undersampled L ∈ {12,16} run anywhere → (sampling)". |
| D6 | "(16, T*(16))" when ΔF*(16) = 0 | T*(L) = the lowest grid T by the tiebreak; the secondaries there are reported **only if ΔF*(16) > 0** (`Secondary16Reported`); the (a)-side gate is still evaluated at the tiebreak T (harmless: (a) cannot fire) | as the r6 ruling. |
| D7 | equal-weight coexistence T "interpolated between grid points on the two peaks' weights … only if the bimodality test passes at ≥ 2 grid points" | weights = raw counts split at the smoothed valley bin (low side includes the valley bin); readable iff ≥ 2 resolved-bimodal points at L = 16 **and** (w_low − w_high)/(w_low + w_high) changes sign between two consecutive bimodal points (linear interpolation in T); an exact zero reads as that T | the crossing condition is implicit in "equal weight"; without a crossing the report says "no coexistence T readable (n bimodal points)". |
| D8 | analyzer accepts the complete set | a point's seeds may be **either** its run sub-block or its re-run sub-block (both from the frozen formula) | a re-run under a dated amendment is a legitimate complete set; the file list in the report shows each file's seeds so the reviewer sees which block was used. |
| D9 | `-smoke-eq -L <L> [-first-seed ≥ 13000]` | one invocation per L (the runner calls it three times, for L = 8, 12, 16, with distinct `-out` names — the default name `mdcu-kz-smoke-eq.jsonl` is shared); T defaults to the table's t = 5 (1.15), `-t` may pick another grid T; seeds {first, first + 1} as (haar, aligned); 500 + 2,000 steps; `-prereg-sha` optional (shape-checked if given) | the spec fixes everything but the T and the per-L invocation shape. |
| D10 | wrapper lease: "release implicit on the driver's exit, the lease fd closed in every subshell" | the **driver inherits the lease fd** (so the lock lives exactly as long as the driver, even if the wrapper is killed); the wrapper's own subshells (the two sidecar blocks) close it (`close_lease_fd`); after the driver exits the wrapper removes the holder line and closes its fd; the holder line is also removed by an EXIT trap; BUSY → `sleep 60` → back to `wait-quiet.sh`; the whole wait is bounded by `MAX_WAIT_S` (default 14,400 s) → exit 11 (a no-run); `mkdir -p` creates `~/.federation-watcher/state/` if absent; seat name `KZ_LEASE_SEAT` (default `qbp-cu-implementor`) | my reading of the two clauses together; if deming's contract wants the driver **not** to hold the fd, it is one `{LEASE_FD}>&-` on the driver line. Not exercised against a live lock here (no second holder available); `bash -n` clean; the 0b verb gained the same call. |
| D11 | sidecar "carries wall, steps, peak Sys, exit code and the raw sha only" | the eq driver's stdout is written to `<raw>.stdout.txt` and shown **after** the run; the sidecar's `# driver_end:` line is the driver's blind end line (wall, steps, ms/step, peak Sys, exit) | the wrapper cannot know steps / peak Sys otherwise; the cost is no live terminal output during a process (the driver prints nothing during the run anyway). |
| D12 | — | the plan prints a non-blocking **note** if `-prereg-sha` ≠ the FROZEN-v1 sha compiled into the binary (`kzG2R3FrozenSHA`); the sha is recorded as given (round-1 behaviour) | guards against hashing the DRAFT by mistake without making the binary refuse a legitimately amended workflow. |
| D13 | §2 "the analyzer also reports the blocked SE of ⟨e⟩ at block sizes 10, 50, 250" | per run, in the τ table; **not** in the raw file | as row 5 (blindness). |
| D14 | — | `KZEqDecide` requires from each file: mode eq, same prereg_sha, Complete (meta + eq + end with exit_code 0, no abort), burn_in/sampling/rec_every = 5000/50000/10, eta = 0.1, T = table[t], seeds = the sub-block, starts = haar,haar,aligned, exactly 5,000 records per series, 27 distinct valid points | "complete set" made mechanical; a shortened or re-parametrised run cannot be analyzed. |
| D15 | — | the orchestrator in **run** mode also refuses eta ≠ 0.1, non-frozen step counts, non-frozen start kinds and T ≠ table[t] (exit 4), independently of the driver | belt and braces, as `KZExecuteStage0bOnly` re-checks its seeds. |
| D16 | "the pair of strict local maxima ≥ 1 bin apart with the largest resolved barrier" | as written; when **no** pair resolves, the pair closest to resolving (largest (n_lower − n_valley)/√(n_lower + n_valley)) is reported with ΔF = 0 for the record; edge bins are never maxima (one neighbour) | descriptive only. |
| D17 | per-seed τ recorded by the driver | the analyzer **recomputes** τ_int/n_eff/undersampled from the series and uses the recomputed values, with a WARNING line on any mismatch with the recorded ones | as the round-1 analyzer did for the gap. |
| D18 | "phase-locking count … whose e-series stays on one side of the valley" | the valley is the smoothed-valley bin's centre e; a seed counts if all its e are < it or all ≥ it | — |
| D19 | S histograms "the same bimodality test" | 60 bins over the pooled S min–max at that L, same smoothing/floor/pair rule; reported as a count and a per-point column | descriptive. |
| D20 | `-max-out-mb` | driver default stays 50 (round 1); the wrapper passes 10; a bare `-run-eq` dry-run prints 50 | as ruled. |

## 7. What the runner needs to know

- Build: `go build -C <W>/emulator -o bin/mdcu-kz ./cmd/mdcu-kz`; post the binary sha at the go.
- Smoke before the go (§5): `scripts/run-kz.sh` has no smoke verb (as round 1); run from `emulator/`: `GOMAXPROCS=1 nice -n 19 taskset -c 7 ./bin/mdcu-kz -smoke-eq -L 8 -out smoke-eq-L8.jsonl`, then `-L 12`, `-L 16` (default seeds 13000, 13001 each time — same free seeds at each L; pass `-first-seed` to vary). Read `ms_per_step` from each `end` record against 1.49 / 5.02 / 11.9 ms.
- A point: `scripts/run-kz.sh eq <L> <t> <raw-out.jsonl> <frozen.md>`; the 27-pair loop is a plain `for` over L = 8 → 12 → 16, t ascending, skipping (8, {3,5,7}) (the driver refuses them anyway with exit 4 = no-run).
- No-run vs kill: the abort record carries `steps`; `steps: 0` = before the first plane-step.
- After all 27: post the 27 shas + binary sha together, then `./bin/mdcu-kz -analyze-eq <27 files> -plot-out plot.json`.

## 8. Scratch artefacts (not in the repo)

`/tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-r3-guards.log` (guard run), `/tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/smoke-eq-L4.jsonl` (the L = 4 smoke on seeds 13100–13101), this file.
