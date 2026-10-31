# qbp-kz-g2 round 3 — Runner phase-2 report (27 production processes)

Runner: director-supervised sub-agent (director: qbp-oppenheimer). FROZEN-v1 sha256 `132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623`; run commit `45639ed11ff516c70be7263136c1cb0a794295b2`; **binary sha256 `89e7fd539a507ec7d94c00fd12c54bd741de5c14c60135244e3f2afb9a98b899`** (built in phase 1, never rebuilt; identical in all 27 meta sidecars).

- **Start (UTC):** 2026-10-31T02:10:08+00:00 (go received; process 1 launched 02:10:19Z)
- **End (UTC):** 2026-10-31T12:17:36+00:00 (process 27 wrapper exit 12:17:24Z)
- **Elapsed:** 607 min = 10 h 7 min (the 11 h report threshold was not crossed). Sum of per-process wall (wrapper, incl. go-test + quiet wait inside each process's sidecar window): see table; the balance is quiet-load waiting between processes.
- **Outcome:** 27 of 27 processes complete, every exit 0, every one 165,000 steps; **no no-runs, no kills, no re-runs**; `KZG2_RERUN_AMEND` unset throughout (`rerun_amend_sha256: none` in all 27 sidecars).
- **Blindness (§7.1):** no raw `.jsonl` was read, grepped, tailed, parsed or summarised; `-analyze-eq` was never run. Reads were limited to wrapper exit codes, `.meta.txt` sidecar lines, the driver end lines of `.stdout.txt`, file sizes and sha256s. T, seeds and start kinds in the table are derived from the frozen formula/table (seed = 6000 + 40l + 4t + j; starts haar,haar,aligned), cross-checked against the phase-1 `-dry-run` plan lines for (8,0), (12,9), (16,5).

## 27-row table (three-way = `sha256sum` of raw file vs wrapper `.sha256` sidecar vs driver end line in `.stdout.txt`)

| k | L | t | T | seeds | starts | steps | exit | wall s | peak Sys MB | ms/step | bytes | raw sha256 | 3-way |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 8 | 0 | 1.08 | 6000,6001,6002 | haar,haar,aligned | 165000 | 0 | 255 | 14.7 | 1.542 | 568006 | caf86820d84ef9f0edd8ef6ca1a2acc287fe6ad89286cc8aad8ace663363f856 | MATCH |
| 2 | 8 | 1 | 1.10 | 6004,6005,6006 | haar,haar,aligned | 165000 | 0 | 255 | 14.7 | 1.544 | 567796 | 24817f203d481905d141a0d893300d8c895e218f8c34eea017bca661cb7638da | MATCH |
| 3 | 8 | 2 | 1.12 | 6008,6009,6010 | haar,haar,aligned | 165000 | 0 | 255 | 14.7 | 1.545 | 567000 | a5bdc0dca012ef5757728ec4ce1413719f951ee71db7f55f46bfcc214ddf9e9a | MATCH |
| 4 | 8 | 4 | 1.14 | 6016,6017,6018 | haar,haar,aligned | 165000 | 0 | 257 | 14.7 | 1.552 | 566648 | 1f9a7ae08c883903deac643d8445ca52ab6f7a3e823c1e2d7d0a791881608f7d | MATCH |
| 5 | 8 | 6 | 1.16 | 6024,6025,6026 | haar,haar,aligned | 165000 | 0 | 255 | 14.7 | 1.545 | 576301 | d8a1385d3cb335530d7575e959b24f8ff19a0c015e39da67501c6d80a6b81217 | MATCH |
| 6 | 8 | 8 | 1.18 | 6032,6033,6034 | haar,haar,aligned | 165000 | 0 | 256 | 14.7 | 1.552 | 580691 | 81e7ff99cab193bb901ac65935be452717fd29f8f32135fcc6d7869eb4c372fc | MATCH |
| 7 | 8 | 9 | 1.20 | 6036,6037,6038 | haar,haar,aligned | 165000 | 0 | 255 | 14.7 | 1.544 | 580712 | f3af8bff79c780d30a05ea250d9978a1d97482859a8daf6a6706e86f8521c93b | MATCH |
| 8 | 12 | 0 | 1.08 | 6040,6041,6042 | haar,haar,aligned | 165000 | 0 | 856 | 14.7 | 5.186 | 568011 | d5c9e15661a6da2173a001aab3c28fbddb817409a965600c9bb4b38e83a595bb | MATCH |
| 9 | 12 | 1 | 1.10 | 6044,6045,6046 | haar,haar,aligned | 165000 | 0 | 843 | 14.5 | 5.113 | 567945 | 33d6288ffba03d5d4124833dff793231621587ef7c064f859756ae7ffd6d3915 | MATCH |
| 10 | 12 | 2 | 1.12 | 6048,6049,6050 | haar,haar,aligned | 165000 | 0 | 844 | 14.7 | 5.117 | 566531 | 3070d1bdd878224aa1cc384a913cbc4c64d74422544534b38b77d050b5aa9d11 | MATCH |
| 11 | 12 | 3 | 1.13 | 6052,6053,6054 | haar,haar,aligned | 165000 | 0 | 848 | 14.5 | 5.138 | 566251 | 8cb96ca340cfda3b9462e13e054ead824f03133ef01fe08e9a1fe621c1a4adb8 | MATCH |
| 12 | 12 | 4 | 1.14 | 6056,6057,6058 | haar,haar,aligned | 165000 | 0 | 852 | 14.7 | 5.166 | 570761 | fe392763b811bcbdec18bcc08c28813a6c09f8a8014696fa73c3cc8eca061e0c | MATCH |
| 13 | 12 | 5 | 1.15 | 6060,6061,6062 | haar,haar,aligned | 165000 | 0 | 845 | 14.7 | 5.120 | 579900 | 173066dd2d84a06653a48243e2e65992ae1b0ea5b0d98175ca2854ff5f9a02ff | MATCH |
| 14 | 12 | 6 | 1.16 | 6064,6065,6066 | haar,haar,aligned | 165000 | 0 | 846 | 14.7 | 5.124 | 581306 | f58a5209895b852eee39de9c88598d28de21d8b562c12fd17b9f133187feb90b | MATCH |
| 15 | 12 | 7 | 1.17 | 6068,6069,6070 | haar,haar,aligned | 165000 | 0 | 843 | 14.7 | 5.108 | 581661 | 1ffcf2cbba0f46ceed7ea6c582aaa74890012f89f2fb0c0e628caf1b7bf41220 | MATCH |
| 16 | 12 | 8 | 1.18 | 6072,6073,6074 | haar,haar,aligned | 165000 | 0 | 844 | 14.5 | 5.117 | 586043 | de40485bb5175db5ab1cfa7940a67c89eab97a685bd97c3f0b01edaa791e076d | MATCH |
| 17 | 12 | 9 | 1.20 | 6076,6077,6078 | haar,haar,aligned | 165000 | 0 | 844 | 14.7 | 5.115 | 586285 | aceefd18ee115ca02b6a43f23b2e802dba4040cc083d5e293c94ba5e9471dfa7 | MATCH |
| 18 | 16 | 0 | 1.08 | 6080,6081,6082 | haar,haar,aligned | 165000 | 0 | 2010 | 14.7 | 12.176 | 568083 | 1cf48096d8c7b1e922265f4cd057c25790af301f9287af26befdd65444a7afc8 | MATCH |
| 19 | 16 | 1 | 1.10 | 6084,6085,6086 | haar,haar,aligned | 165000 | 0 | 2015 | 14.7 | 12.211 | 568020 | 6222b4c4b1b1d98a2cd16ab8550dfb3e7a5cab0b640422e5f024c071fe5d72db | MATCH |
| 20 | 16 | 2 | 1.12 | 6088,6089,6090 | haar,haar,aligned | 165000 | 0 | 2008 | 14.7 | 12.169 | 566311 | 8f21489747ff56dabca3a779286f0c11795ada37108472964f4796926b52bad5 | MATCH |
| 21 | 16 | 3 | 1.13 | 6092,6093,6094 | haar,haar,aligned | 165000 | 0 | 2009 | 14.7 | 12.173 | 566343 | 05e80b2df000e874eafe19a43c7d1ddc002e0ee156b748e402b592aadf0c54fa | MATCH |
| 22 | 16 | 4 | 1.14 | 6096,6097,6098 | haar,haar,aligned | 165000 | 0 | 2013 | 14.7 | 12.201 | 580392 | 6301d5bc5d0eafc49db45644e6b94e1eafaa9206eeaa531e3ead47e99d30bdfb | MATCH |
| 23 | 16 | 5 | 1.15 | 6100,6101,6102 | haar,haar,aligned | 165000 | 0 | 2010 | 14.7 | 12.184 | 582462 | 2d1771ce64081642a176205270bb618ae388a4ffc452bc43044698c2edacd22f | MATCH |
| 24 | 16 | 6 | 1.16 | 6104,6105,6106 | haar,haar,aligned | 165000 | 0 | 2014 | 14.7 | 12.205 | 583090 | b1d9d62662ddeb56e8b9f8aede57c36e462d0900a841b0c1ac5e198017253414 | MATCH |
| 25 | 16 | 7 | 1.17 | 6108,6109,6110 | haar,haar,aligned | 165000 | 0 | 2010 | 14.8 | 12.182 | 583208 | 1cebe705ec751c63ae04e419583a9f336292fe757f35ee2a927f699659b2cc3e | MATCH |
| 26 | 16 | 8 | 1.18 | 6112,6113,6114 | haar,haar,aligned | 165000 | 0 | 2018 | 14.7 | 12.228 | 588609 | 10f2c86f305a91fcb3b9bb9def8717cf7419694fe3400b4ebd96ca90393f077b | MATCH |
| 27 | 16 | 9 | 1.20 | 6116,6117,6118 | haar,haar,aligned | 165000 | 0 | 2009 | 14.7 | 12.178 | 589640 | 40ed422dacc2055425bb810817572df9f536830c9d15454ce6ea34d4814aee79 | MATCH |

rows: 27  exit-0: 27  pending: 0  sum of per-process wall: 30369 s = 8.44 h

## Totals

| L | processes | ms/step range (end records) | per-process wall | peak Sys |
|---|---|---|---|---|
| 8 | 7 | 1.542–1.552 (§5 assumed 1.49; ratio ≤ 1.04) | 255–257 s | 14.7 MB |
| 12 | 10 | 5.108–5.186 (§5 assumed 5.02; ratio ≤ 1.04) | 843–856 s | 14.5–14.7 MB |
| 16 | 10 | 12.169–12.228 (§5 assumed 11.9; ratio ≤ 1.03) | 2008–2018 s (28 % of the 2 h cap) | 14.7–14.8 MB |

- Steps total: 27 × 165,000 = 4,455,000 plane-steps. Sum of per-process wall: 30,369 s = 8.44 h (§5 projection 8.23 h; phase-1 smoke projection 8.49 h). Raw output: 27 files, 15,538,006 bytes total (≈ 0.58 MB each; cap 10 MB per process). Peak Sys ≤ 14.8 MB everywhere (cap 100 MB).
- Three-way sha: **27 MATCH, 0 MISMATCH.**

## No-runs / kills

None. Every wrapper exited 0 after its driver's `done` line with steps 165000. Pre-run go-test passed inside each of the 27 wrappers; every process took the box lease (holder `qbp-oppenheimer`, purpose `qbp-kz-g2-r3:eq:L<L>:t<t>`) and released it; `pause_file_present_at_end: no` in all 27 sidecars.

## Process-control notes (disclosed)

- Points 1–2 were launched by `launch.sh`; point 2 ran its wrapper detached (`setsid nohup`), which the director flagged and ruled must not recur; point 2 finished under its own caps and stands as recorded. Points 3–27 were launched by `launch-fg.sh`: wrapper in the foreground of a tracked `run_in_background` task, gates (progress count, clean tree, no other lean/lake/mdcu-kz process, pause file absent, no existing output) checked before each launch; `post.sh` classified each exit from the sidecar only.
- The lease holder seat was set to `qbp-oppenheimer` (the directing seat) via `KZ_LEASE_SEAT`; the wrapper default is `qbp-cu-implementor`.
- Phase 1's `flock -n` probe created the previously nonexistent empty `~/.federation-watcher/state/box-lease.lock`; the wrapper would have created the same file.

## Box state at the end (2026-10-31 08:18 EDT / 12:18 UTC)

- `uptime`: load 0.71 / 1.07 / 1.17; no lean/lake/mdcu-kz process; pause file `~/.federation-watcher/box-pause/mdcu` absent; lease holder file absent, `flock -n` on the lock succeeds (lease free).
- Worktree `/home/prime/Documents/QBP-CU-mdcu/.worktrees/kz-r3-build`: HEAD 45639ed, `status --porcelain` empty. Binary sha unchanged: `89e7fd539a507ec7d94c00fd12c54bd741de5c14c60135244e3f2afb9a98b899`.

## Artefacts (all under the scratchpad run dir, nothing inside any repo tree)

`$R = /tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-r3-run/`: `raw/qbp-kz-g2-r3-eq-L<L>-t<tt>.jsonl` (27) + `.sha256` + `.meta.txt` + `.stdout.txt` (27 each); `progress.log` (27 lines); `launch-L*-t*.log` (27); `table.md`; `phase1-report.md`; `FROZEN-v1.md` (sha-verified copy used as the wrapper's frozen argument); `launch.sh`, `launch-fg.sh`, `post.sh`, `report.sh`.

Next (director's, not the runner's): post the 27 raw shas + binary sha together on QBP#797 before any analysis (§7.1); then `-analyze-eq` on the 27 hashed files; raw files copied verbatim into `spikes/qbp-kz-g2/raw/` for the record PR.
