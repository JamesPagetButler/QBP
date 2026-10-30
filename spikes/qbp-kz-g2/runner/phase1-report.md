# qbp-kz-g2 round 1 — runner PHASE 1 report (acceptance, build, guard tests)

Runner: director-supervised sub-agent (director: qbp-oppenheimer). Date: 2026-10-30 14:43–14:46 local.
Scope: PHASE 1 ONLY. No `-run-0b`, no `run-kz.sh` invocation, no `go test` execution. Nothing heavier than `go build` + `test-kz-guards.sh` (+ four `-dry-run`s, which write nothing).

Scratchpad run dir (RUN): /tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-g2-run
Worktree (W): /home/prime/Documents/QBP-CU-mdcu/.worktrees/kz-g2-build

## 1. Worktree
| Check | Result |
|---|---|
| `git -C W rev-parse HEAD` | **aa041391e934e6b41f02cf8f79a4e489ca928360** (== expected) |
| branch | spike/qbp-kz-g2-r1-harness |
| `git -C W status --porcelain` (before) | empty (0 lines) |

## 2. Frozen plan — recomputed sha256 (raw files from QBP commit 8c4d53b, written to scratchpad only)
| File | Written to | sha256 | Match |
|---|---|---|---|
| spikes/prereg/qbp-kz-g2-r1-prereg-FROZEN-v1.md | RUN/FROZEN-v1.md (27,403 B) | 785e0ee2c81740b25fbeb9dfa5bb26e22159d8b7b221de2bdb75c2f7a6f51e28 | **YES** |
| spikes/prereg/qbp-kz-g2-r1-prereg-FROZEN-v1-amend-1.md | RUN/FROZEN-v1-amend-1.md (2,051 B) | f043b28012f5eba000b3492b860ecad94a6a0fcee6585c575b1324b69ded39b5 | **YES** |

Cross-check: FROZEN-v1 at PR #794 head 25b9913 also hashes to 785e0ee2…f51e28 (byte-identical at both commits). No repo tree was written to.

## 3. Frozen protocol summary (verbatim numbers)
**FROZEN-v1 §2 (Design, Stage 0b only)**
- Four separate driver processes, one per τ_Q ∈ {1600, 3200, 6400, 12800}; sequential; main arm only; no detector / ladder / saturation gate / S³ null / Stage 0a.
- T_c = 1.0666262219986817 (reused, typed into `-tc` at full precision); T_hi = 1.5·T_c = 1.5999, T_lo = 0.5·T_c = 0.5333; common grid spacing T_c/40 = 0.026666 → 41-point grid linear in T over [T_lo, T_hi].
- L = 16, periodic. η = 0.1 reused (descent test not re-run). Per seed: 200 hold steps at T_hi (KZHoldSteps), cool over exactly τ_Q steps, heat over exactly τ_Q steps; S recorded at step 0 and every 10 steps (161 / 321 / 641 / 1281 records per branch). Noise stream constant 100001.
- Seeds: 10 per τ_Q, seed = 5900 + 10·i + j, i = τ index (0:1600, 1:3200, 2:6400, 3:12800), j ∈ 0..9 → 5900–5909 / 5910–5919 / 5920–5929 / 5930–5939. Seed count derived from τ index, never typed. Reserved re-run block 5940–5979 (5940 + 10·i …), only under a dated amendment.
- Raw output per process: `qbp-kz-g2-r1-0b-tau<τ>.jsonl` + meta sidecar; four shas posted together before any raw file is opened (§7).
- Measurement definitions kept (not gates here): 5 % gap clause (|mean S_cool − mean S_heat| ≤ 0.05·S_max on every grid T), 10 % jump clause; S_max = 1.

**FROZEN-v1 §5 (Kills, aborts, resources)**
- Per-process aborts: wall > 2 h → exit 2; pause file `$HOME/.federation-watcher/box-pause/mdcu` at start or any step → driver exit 3 (wrapper pre-check exit 4); seed guard violation → exit 4 before any step; wrapper `go test` failure → exit 10; NaN / non-finite S → exit 6.
- Steps: 480,000 ramp + 8,000 hold = **488,000** steps, 48,080 OrderS reads. Rate ≈ 12–13 ms/plane-step → ≈ 100–108 min total: 1600 ≈ 34,000 steps ≈ 7 min; 3200 ≈ 66,000 ≈ 14 min; 6400 ≈ 130,000 ≈ 28 min; 12800 ≈ 258,000 ≈ 55 min (≈ 46 % of its own 2 h cap).
- RAM < 50 MB (lattice ≈ 0.5 MB). Disk < 5 MB raw jsonl across the four files.
- Load discipline: one lattice at a time, GOMAXPROCS=1, taskset core-pinned, nice -n 19, quiet-load wait before each process, load_start/load_end in meta; unit tests run BEFORE the quiet wait.
- Kill condition: fixed step count by construction AND 2 h wall cap per process.

**amend-1 §1 (seed-guard range)**
- **5900–5979 governs.** In `-run-0b` the guard accepts only the process's own τ-index sub-block of 5900–5939 (5900 + 10·i … 5900 + 10·i + 9), or — only when a dated re-run amendment names the τ index and the guard is invoked with that amendment's sha — the same τ index in 5940–5979. Every other mode (smokes, probe, grid, calibration) refuses 5900–5979, exit 4, before any step. §2 item 2's narrower "5900–5939" is superseded.
- amend-1 §2 table: 5900–5939 "assigned (checked disjoint: 5890–9099 free; next used 9100+)"; 5940–5979 "assigned, reserved" (usable once per rung, only under a dated amendment citing a §5 kill).

**§8 gates as printed in the frozen text:** runner read [x]; qbp-cu-implementor feasibility [x]; notary [x]; deming box-safety [ ]; architecture cc [ ] (optional); director freeze [ ]. Deming's clear is standing-auth condition (3) and is NOT phase 1's to fill (brief line 6 still blank).

## 4. Used-range check (W/emulator/mdcu/kzseeds.go — the only seed registry; no other registry is referenced)
`KZClassifySeed` ranges: main 5000–5199 · null 5200–5399 · reserved 5400–5599 · stage0 5600–5629 · saturation 5630–5649 · tilt 5650–5849 · tilt-calibration 5850–5889 · **kz-g2-r1 5900–5939** · **kz-g2-r1-rerun 5940–5979** · probe 9930–9949 · used 3000–3199, 4000–4399, 9100–9929, 9950–9979 · everything else free.
- Seeds 5900–5979 are classified ONLY as `KZSeedKzG2R1` / `KZSeedKzG2R1Rerun` — registered to **no previous run** (5890–5899 free; next used range above is 9100+). Consistent with amend-1 §2.
- τ-index mapping: `KZKzG2R1TauSet = {1600, 3200, 6400, 12800}`; `KZKzG2R1Seeds(i, rerun)` = base + 10·i + j, base 5900 (run) / 5940 (rerun), 10 seeds — exactly amend-1 §1. `KZCheckKzG2R1Seeds` requires the exact ordered sub-block AND the matching class. The driver (`cmd/mdcu-kz/kzg2.go`) derives seeds from `-tau` and refuses a typed `-first-seed` and `-L` (guard tests confirm).
- grep of `59[0-9]{2}` / `KzG2` over non-test Go files: hits only in kzseeds.go, kzg2.go, main.go, kzrun.go (guards and comments) — no other registration.

## 5. Box state
- `pgrep -af 'lean|lake|mdcu'` (excluding the grep itself): **no matches**.
- `uptime`: 14:43:42 up 14 days, 33 min, 18 users, load average: 0.72, 0.63, 0.54 (after build + guards: 0.67 0.64 0.55).
- Top CPU: chrome 2.7 %, claude sessions ≤ 2 %, Xorg 1.9 % — nothing heavy.
- RAM: 31,991 MB total, 17,528 MB available. Disk: / 229 G, 33 G avail (86 % used) — ample for < 5 MB raw.
- Pause file `~/.federation-watcher/box-pause/mdcu`: **absent** (directory holds only README).

## 6. Build + guard tests
- Build: `(cd W/emulator && go build -o bin/mdcu-kz ./cmd/mdcu-kz)` — rc 0, 0.29 s, go1.24.2 linux/amd64. NOTE: built from `emulator/` (not `W/bin` as the task text sketched) because run-kz.sh and test-kz-guards.sh resolve `./bin/mdcu-kz` relative to `emulator/`, and `emulator/bin/` is the gitignored path.
- Binary: W/emulator/bin/mdcu-kz, 4,442,819 B, sha256 **51a2ed9c69f2827a65bc40aa21e8c64ba60941f0091c40aa5b56a89f3900e7f7**.
- Guard tests: `(cd W/emulator && bash scripts/test-kz-guards.sh)` → rc 0, **73 ok, 0 FAIL** (log: RUN/guard-tests.log).
- `git -C W status --porcelain` AFTER build + tests: **empty (0 lines)**; `git check-ignore -v emulator/bin/mdcu-kz` → `.gitignore:12 emulator/bin/`.
- Dry-runs with the REAL prereg sha (write nothing; tmp dir verified empty afterwards), all rc 0, each printing tc=1.0666262219986817, T_hi=1.599939, T_lo=0.533313, L=16, eta=0.1, hold=200, record every 10, grid 41, wall cap 2h0m0s, pause file /home/prime/.federation-watcher/box-pause/mdcu:
  - τ 1600 (index 0): seeds 5900..5909, steps 34,000, out qbp-kz-g2-r1-0b-tau1600.jsonl
  - τ 3200 (index 1): seeds 5910..5919, steps 66,000
  - τ 6400 (index 2): seeds 5920..5929, steps 130,000
  - τ 12800 (index 3): seeds 5930..5939, steps 258,000
- `go test ./mdcu -run TestKZ -list` (listing only, NOT executed): 40 tests matched (incl. TestKZFrozenSeedsAreInTheirClasses, TestKZG2DecideHFirst, TestKZG2DecideHSlow). run-kz.sh executes these itself before each quiet-load wait (exit 10 on failure).

## 7. Exact phase-2 commands (NOT run in phase 1)
run-kz.sh must be invoked from `emulator/` (BIN=./bin/mdcu-kz is relative; the wrapper calls `go test ./mdcu` and `wait-quiet.sh` via `dirname $0`). Usage line: `scripts/run-kz.sh 0b <tau> <raw-out.jsonl> <frozen.md>`. The 4th argument is the FROZEN-v1 copy; the wrapper sha256s it and passes `-prereg-sha`. **The amend file is NOT an argument, and `KZG2_RERUN_AMEND` must be UNSET for the primary block** — setting it switches the driver to the re-run sub-block 5940–5979 via `-rerun-amend-sha`. Sequential, one at a time, in this order, each only after the director's go:

```
RUN=/tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-g2-run
W=/home/prime/Documents/QBP-CU-mdcu/.worktrees/kz-g2-build
(cd $W/emulator && bash scripts/run-kz.sh 0b 1600  $RUN/qbp-kz-g2-r1-0b-tau1600.jsonl  $RUN/FROZEN-v1.md)
(cd $W/emulator && bash scripts/run-kz.sh 0b 3200  $RUN/qbp-kz-g2-r1-0b-tau3200.jsonl  $RUN/FROZEN-v1.md)
(cd $W/emulator && bash scripts/run-kz.sh 0b 6400  $RUN/qbp-kz-g2-r1-0b-tau6400.jsonl  $RUN/FROZEN-v1.md)
(cd $W/emulator && bash scripts/run-kz.sh 0b 12800 $RUN/qbp-kz-g2-r1-0b-tau12800.jsonl $RUN/FROZEN-v1.md)
```
Each wrapper call: pre-checks binary (exit 9) and pause file (exit 4) → `go test ./mdcu -run TestKZ` (exit 10 on fail) → quiet-load wait (exit 11 on timeout) → pause re-check (exit 4) → writes `<raw-out>.meta.txt` (started, load_start, cpu, go, binary_sha256, code_sha + dirty_files, tau_Q, tc=1.0666262219986817, frozen_file, prereg_sha256, rerun_amend_sha256=none, pause_file, pinned) → `GOMAXPROCS=1 nice -n 19 taskset -c 7 ./bin/mdcu-kz -run-0b -tau <τ> -tc 1.0666262219986817 -prereg-sha 785e0ee2…f51e28 -out <raw-out>` → appends exit, wall_s, load_end, pause-file state, finished, raw_sha256 (also written to `<raw-out>.sha256`); the wrapper exits with the driver's code.
Driver caps (from `-h`): `-max-wall 2h0m0s`, `-max-rss-mb 100` (abort if Go runtime Sys exceeds this; frozen ≤ 100 MB), `-max-out-mb 50`, pause file default `/home/prime/.federation-watcher/box-pause/mdcu` — matches the brief (2 h / 100 MB RAM / 50 MB disk).
Raw-output path note: FROZEN-v1 §2 names the repo path `spikes/qbp-kz-g2/raw/qbp-kz-g2-r1-0b-tau<τ>.jsonl`; per the task the raw files go to RUN and are moved into the repo by the director after the four shas are posted.

**wait-quiet.sh:** polls `/proc/loadavg` 1-min average every 20 s; exits 0 ("QUIET") once the load is ≤ LOAD_CEIL (run-kz.sh sets **1.0**) on **3 consecutive 20 s samples**; exits 3 ("TIMEOUT") after MAX_WAIT_S (default **14,400 s = 4 h**), which run-kz.sh maps to exit 11 (no run). Zero tokens while waiting. Current 1-min load 0.67 would clear it on the first three samples.

## 8. Acceptance line
Runner (director-supervised sub-agent) accepts FROZEN-v1 sha 785e0ee2c81740b25fbeb9dfa5bb26e22159d8b7b221de2bdb75c2f7a6f51e28 and amend-1 sha f043b28012f5eba000b3492b860ecad94a6a0fcee6585c575b1324b69ded39b5 at run commit aa04139; used-range check: seeds 5900–5979 unregistered (KZSeedKzG2R1 / KZSeedKzG2R1Rerun only; no prior run); guard tests 73 ok; tree clean.

Standing-auth condition (3) — deming box-safety clear — is still OPEN in the brief (seq/comment blank). Phase 2 waits for the director's go.
