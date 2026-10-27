# docs/process/edda — Edda lock files for QBP process gates

Edda source for QBP process gates written as executable specs, starting with the housekeeping-before-Sprint-4 gate (QBP#714). Edda is the federation's spec language (`JamesPagetButler/edda`); the lowering of forging terms (thread, strike, lock) to Edda forms is tracked on inter#197.

**Check:** from a snapshot of edda `origin/Main` (`git archive origin/Main | tar -x -C <dir>`), run `go run ./cmd/edda-stage-1 check <path>/qbp_housekeeping_sprint4_gate.edda`. Expected: `ok: ... 1 contract(s), 1 skill(s) checked (stage-1)`, exit 0.

| File | Status |
|---|---|
| `qbp_housekeeping_sprint4_gate.edda` | **Compiles** (stage-1, edda Main @9d571a5 and @4ab6354): `skill` thread path + `contract strike_exit`. Negative probe (exercise before settle) -> `EDDA-AUTH-018`. |
| `ac-legs-2026-10-24.tsv` | **Leg set** the lock keys on: every AC of the 28 in-scope issues, ids `#<issue>-AC<k>`, numbered 2026-10-24 by qbp-oppenheimer from the live bodies. 145 legs: 102 open, 41 ticked, 2 nil (snapshot). |
| `714-thread-and-lock-draft.md` | Glossary (§a), the compilable subset (§B1), the **pseudo** lock block `lock/legs/where/unlock/scope` (§B2, not in the parser), and 8 questions for edda-implementor (§c). |

Goal (beekeeper, 2026-10-24): by the next housekeeping session the lock compiles in full and an actual unlock is performed by completing the in-scope housekeeping work. Tracks [QBP#714](https://github.com/JamesPagetButler/QBP/issues/714); language asks on [inter#197](https://github.com/JamesPagetButler/inter/issues/197).
