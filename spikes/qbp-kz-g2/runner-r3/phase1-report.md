# qbp-kz-g2 round 3 — Runner phase-1 report (acceptance, build, guards, pre-go smoke)

Runner: director-supervised sub-agent (director: qbp-oppenheimer). Date: 2026-10-30 (21:51–22:00 EDT).
Phase 1 only. **No production process was started** (no `run-kz.sh eq`, no `-run-eq`; the only non-dry-run invocations were the three `-smoke-eq` runs on free seeds 13000/13001).

## Acceptance line

Runner (director-supervised sub-agent) accepts FROZEN-v1 sha 132f6a42… at run commit 45639ed; used-range check: seeds 6000–6239 registered to KZSeedKzG2R3/Rerun only, no prior run; guard tests 131 ok, go tests 120 ok; tree clean; smoke rates L8/L12/L16 = 1.528/5.143/12.310 ms/step (ratios 1.026/1.025/1.035 vs §5), projected total 8.49 h, longest process 33.9 min (28.2% of cap).

## 0. Frozen plan read

- `git -C /home/prime/Documents/QBP show ae37319:spikes/prereg/qbp-kz-g2-r3-prereg-FROZEN-v1.md` → `$R/FROZEN-v1.md` (222 lines).
- sha256 recomputed: `132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623` — **matches**.
- Read §2 (design, seed formula 6000+40l+4t+j, run order L=8→12→16 t ascending, one process at a time), §5 (smoke ruling ≤1.5× → proceed; no-run vs kill; lease; caps: 2 h wall, Sys 100 MB, out 10 MB via wrapper), §7.1 (blindness: only wall/steps/peak Sys/exit/sha read; series never read).
- Builder hand-off §7 read (build cmd, smoke cmd with default seeds 13000/13001, `run-kz.sh eq <L> <t> <raw> <frozen>`, no-run `steps: 0`, post 27 shas + binary sha together).

## 1. Worktree

- W = `/home/prime/Documents/QBP-CU-mdcu/.worktrees/kz-r3-build`
- `git -C W rev-parse HEAD` = `45639ed11ff516c70be7263136c1cb0a794295b2` — **matches** the run commit.
- `git -C W status --porcelain` → empty (checked before build, after tests, after smoke: empty every time).

## 2. Used-range check

- `emulator/mdcu/kzseeds.go` `KZClassifySeed`: `case seed >= 6000 && seed <= 6119 → KZSeedKzG2R3`, `case seed >= 6120 && seed <= 6239 → KZSeedKzG2R3Rerun`; the adjacent cases are 5940–5979 (R1 rerun) below and 9930–9949 (probe) above; nothing else covers 6000–6239.
- Literal grep for 6000–6239 across `emulator/**/*.go` and `emulator/scripts`: outside kzseeds.go the only non-test hits are `pillar2.go:47 maxSteps = 6000` (a step count, not a seed), the r3 driver's own strings in `cmd/mdcu-kz/kzeq.go` / `main.go`, and `0.6097` in a test log string. Test hits are all `kzeq_test.go` (the r3 guard tests themselves). **No prior run claims any seed in 6000–6239.**
- `-run-eq -dry-run` (prereg sha passed), exit 0 each:
  - L=8 t=0: T=1.08, seeds 6000,6001,6002, starts haar,haar,aligned, steps 165000, out `qbp-kz-g2-r3-eq-L8-t00.jsonl`, noise stream 100002, wall cap 2h, caps Sys 100 MB / out 50 MB (driver default; the wrapper passes `-max-out-mb 10`).
  - L=12 t=9: T=1.2, seeds 6076,6077,6078, starts haar,haar,aligned, steps 165000.
  - L=16 t=5: T=1.15, seeds 6100,6101,6102, starts haar,haar,aligned, steps 165000.
  - All three agree with 6000+40l+4t+j. Saved as `$R/dry-run-L*-t*.txt`.

## 3. Box

- `pgrep -af 'lean|lake|mdcu-kz'`: the only match was my own bash invocation (self-match on the pattern); **no lean/lake/mdcu-kz process running**.
- `uptime` at 21:51: load 3.05/1.84/1.45 (18 users). Before smoke, `wait-quiet.sh` (MAX_WAIT_S=600) returned QUIET load1=0.77 at 21:58:47.
- Pause file `~/.federation-watcher/box-pause/mdcu`: **absent** (dir holds only README). Re-checked immediately before the smokes: absent.
- Lease `~/.federation-watcher/state/box-lease.lock`: `flock -n … -c echo` **acquired and released immediately** (free). Disclosure: the file did not exist before my test; `flock` created it as an empty 0-byte file (21:51). No holder file was written. This is the same path the wrapper's `eq` verb will flock; harmless, but noted.

## 4. Build and tests

- `(cd W/emulator && go build -o bin/mdcu-kz ./cmd/mdcu-kz)` → ok. `emulator/bin/` is gitignored (`.gitignore:12`).
- **Binary sha256: `89e7fd539a507ec7d94c00fd12c54bd741de5c14c60135244e3f2afb9a98b899`** (also recorded as `binary_sha256` in each smoke meta record; `code_sha` = 45639ed).
- `GOMAXPROCS=1 go test ./mdcu -run TestKZ -count=1` → `ok … 7.805s`; **120 top-level `--- PASS: TestKZ…`, 0 FAIL** (log `$R/go-test-kz.log`).
- `bash scripts/test-kz-guards.sh` → exit 0, **131 `ok:` lines**, no failures (the single "FAIL" substring in the log is the test name "a probe whose descent test failed is refused (exit 8)"). Log `$R/guards.log`.
- Tree clean after both.

## 5. Smoke (`-smoke-eq`, pinned, one at a time)

Command per L, from `W/emulator` in a subshell: `GOMAXPROCS=1 nice -n 19 taskset -c 7 ./bin/mdcu-kz -smoke-eq -L $L -prereg-sha 132f6a42… -out $R/smoke-eq-L$L.jsonl` (default `-first-seed 13000` → seeds 13000 hot + 13001 cold; both free; `pause_present_at_start=false`, `gomaxprocs=1` in meta). Only the `end` and `meta` records were read (jq); the `eq` series record was not opened.

| L | §5 assumed ms/step | realised ms/step | ratio | steps | wall_s | peak_sys_mb | exit | ≤1.5? |
|---|---|---|---|---|---|---|---|---|
| 8  | 1.49 | 1.528 | 1.026 | 5000 | 7.64 | 14.7 | 0 | yes |
| 12 | 5.02 | 5.143 | 1.025 | 5000 | 25.71 | 14.5 | 0 | yes |
| 16 | 11.9 | 12.310 | 1.035 | 5000 | 61.55 | 14.8 | 0 | yes |

**Every ratio ≤ 1.5 → proceed per §5 smoke ruling; no amendment needed.** Load at smoke start: 0.77 / 0.97 / 1.44 (the last elevated by my own preceding smoke).

Smoke raw sha256 (smoke output is never fed to `-analyze-eq`):
- L8  `536ea30a68aa84ae78d183a15f1e36ee16253b928f9295dc98afc0b069ef669d`
- L12 `98658e102e452335b6935a6668071647b143bf163890e6160b004fa28b06074c`
- L16 `6b5f5b89232266998a973626be923ebe9e4cc958a189b0387ab0727056dff2ff`

### Projection from realised rates (165,000 steps/process; 7/10/10 processes)

| L | per process | processes | wall per L |
|---|---|---|---|
| 8  | 252.1 s ≈ 4.2 min (3.5% of cap) | 7 | 1,765 s |
| 12 | 848.6 s ≈ 14.1 min (11.8% of cap) | 10 | 8,486 s |
| 16 | 2,031.2 s ≈ 33.9 min (**28.2% of 2 h cap**) | 10 | 20,312 s |
| **total** | | **27** | **30,562 s ≈ 8.49 h** (+10% §5 energy-read margin ≈ 9.34 h) |

Compare §5 frozen table: 8.23 h (9.1 h with margin); realised is ~3% above. Peak Sys ≈ 15 MB vs the 100 MB cap.

## Notes for the director's go

- Binary sha to post at the go: `89e7fd539a507ec7d94c00fd12c54bd741de5c14c60135244e3f2afb9a98b899`.
- Flags confirmed from `-h`: `-run-eq -L <L> -t <t> -prereg-sha <64hex>`, `-smoke-eq`, `-dry-run`, `-first-seed` (smoke only), `-max-out-mb`, `-out`, `-analyze-eq`. Wrapper verb: `scripts/run-kz.sh eq <L> <t> <raw-out.jsonl> <frozen.md>`.
- Awaiting phase-2 message before any `run-kz.sh eq` launch.
