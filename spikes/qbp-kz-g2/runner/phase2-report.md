Phase-2 start (UTC): 2026-10-30T18:50:02+00:00 — end (UTC): 2026-10-30T20:32:09+00:00 (last wrapper exit); report written 20:32:38Z.

# qbp-kz-g2 round 1 — runner PHASE 2 report (four Stage-0b rungs, run only — NO analysis)

Runner: director-supervised sub-agent (director: qbp-oppenheimer). Go: director, mdcu-spike seq 336 + QBP#793 comment; deming BOX-SAFETY CLEAR mdcu-spike seq 330 (2026-10-30 18:41Z). Run commit aa041391e934e6b41f02cf8f79a4e489ca928360; binary sha256 51a2ed9c69f2827a65bc40aa21e8c64ba60941f0091c40aa5b56a89f3900e7f7; prereg sha 785e0ee2c81740b25fbeb9dfa5bb26e22159d8b7b221de2bdb75c2f7a6f51e28 (recorded in every meta); rerun_amend_sha256 = none in every meta (KZG2_RERUN_AMEND unset throughout).

Commands executed (exactly as in phase1-report §7, sequential, each from the worktree's emulator/ in a subshell, each only after the previous one's exit + between-rung checks):
```
RUN=/tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-g2-run
W=/home/prime/Documents/QBP-CU-mdcu/.worktrees/kz-g2-build
(cd $W/emulator && bash scripts/run-kz.sh 0b 1600  $RUN/qbp-kz-g2-r1-0b-tau1600.jsonl  $RUN/FROZEN-v1.md)
(cd $W/emulator && bash scripts/run-kz.sh 0b 3200  $RUN/qbp-kz-g2-r1-0b-tau3200.jsonl  $RUN/FROZEN-v1.md)
(cd $W/emulator && bash scripts/run-kz.sh 0b 6400  $RUN/qbp-kz-g2-r1-0b-tau6400.jsonl  $RUN/FROZEN-v1.md)
(cd $W/emulator && bash scripts/run-kz.sh 0b 12800 $RUN/qbp-kz-g2-r1-0b-tau12800.jsonl $RUN/FROZEN-v1.md)
```

## Result table (all values from the wrapper's `.meta.txt` / `.sha256` sidecars and my own `sha256sum`; raw .jsonl never opened)

| τ_Q | idx | seeds | steps | exit | wall_s | started (local −04:00) | load_start | load_end | raw sha256 (full) | sidecar == meta == mine | raw bytes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1600 | 0 | 5900..5909 | 34,000 | **0** | **405** | 14:50:55 | 0.64 0.59 0.55 | 1.30 1.15 0.86 | 37102cc855412e1bd51c31a8bb650ca2eb1885bccd398e745b6caf47abd975bd | **MATCH** | 73,608 |
| 3200 | 1 | 5910..5919 | 66,000 | **0** | **786** | 14:58:51 | 0.68 1.00 0.83 | 1.53 1.44 1.19 | 397a39cc96198a459664c103b46e27f06a05b8ba021093cdb89617e28a75e788 | **MATCH** | 142,356 |
| 6400 | 2 | 5920..5929 | 130,000 | **0** | **1548** | 15:13:26 | 0.62 1.14 1.10 | 1.60 1.52 1.45 | 80d710130e6b7e7343d53950bc394d2cc8db47c1e0915d700bb61848b9c58f30 | **MATCH** | 279,687 |
| 12800 | 3 | 5930..5939 | 258,000 | **0** | **3086** | 15:40:43 | 0.54 1.19 1.34 | 1.33 1.23 1.28 | cae83fdc60a63534b153546cae5e781a0237216606251ad9e4d316dbce69468f | **MATCH** | 554,701 |

Totals: 488,000 steps; wall 5,825 s ≈ 97.1 min of driver time (frozen §5 estimate 100–108 min; longest rung 3086 s = 43 % of its 2 h cap); raw total 1,050,352 B ≈ 1.0 MB (< 5 MB envelope). Implied rate ≈ 11.9 ms/step (34,000→405 s; 258,000→3086 s), inside the §5 12–13 ms figure.

Per-rung meta, identical across all four: `binary_sha256 51a2ed9c…`, `code_sha aa041391… dirty_files: 0`, `tc 1.0666262219986817`, `prereg_sha256 785e0ee2…f51e28`, `rerun_amend_sha256: none`, `pause_file … (absent at start)`, `pause_file_present_at_end: no`, `pinned: GOMAXPROCS=1 nice -n 19 taskset -c 7`, `unit tests: go test ./mdcu -run TestKZ passed`. Quiet-load wait cleared before every rung (QUIET load1 = 0.64 / 0.68 / 0.62 / 0.54); no TIMEOUT. stderr empty for all four rungs.

**Peak RSS:** the wrapper/driver meta records NO RSS field (the driver enforces `-max-rss-mb 100` internally; no kill fired). Not measured externally — not available.

## Kills / aborts
None. No exit 2/3/4/6/9/10/11 on any rung; pause file absent at start and end of every rung; nothing re-run; no amendment used.

## Discipline notes
- Raw .jsonl files were never read, grepped, tailed or parsed; `-analyze-0b` was NOT run. My only reads: wrapper exit codes, `.meta.txt`, `.sha256`, my own stdout/stderr logs, file sizes.
- The driver itself prints a one-line per-rung result summary to stdout (not a raw-file read by me); it is in `rung-tau<τ>.stdout.log`. I filtered it out of my inspection for rungs 2–4 and have not acted on, compared or summarised it; the director reads those lines, not the runner.
- Between every pair of rungs: `git -C W status --porcelain` empty; `pgrep -af 'lean|lake|mdcu'` no other process; pause file absent.

## Final box state (20:32:38Z)
HEAD aa041391… · porcelain 0 · no lean/lake/mdcu process · pause file absent · uptime 14 days 2:22, load 0.80 1.11 1.24 · RAM 17,879 MB available · disk / 33 G avail.

## Files (all under RUN)
qbp-kz-g2-r1-0b-tau{1600,3200,6400,12800}.jsonl + .meta.txt + .sha256 · rung-tau*.stdout.log / .stderr.log · FROZEN-v1.md · FROZEN-v1-amend-1.md · phase1-report.md · phase2-start-utc.txt · guard-tests.log.

## Runner STOP
Four shas above are to be posted together by the director (FROZEN-v1 §7) before any raw file is opened. Analysis (`-analyze-0b`) is a separate director-issued step. Runner stops here.
