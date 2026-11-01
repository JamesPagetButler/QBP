# qbp-kz-g2 round 3 — director's independent recompute (FROZEN-v1 §3)

- Frozen rule: QBP PR #800 @ `ae37319`, `spikes/prereg/qbp-kz-g2-r3-prereg-FROZEN-v1.md`, sha256 `132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623` (matches `prereg_sha` in all 27 `meta` records).
- Inputs: the 27 raw files `raw/qbp-kz-g2-r3-eq-L{8,12,16}-t{00..09}.jsonl` (shas as posted on QBP#797). Only the `eq` record's per-seed `e_series` / `s_series` / `seed` / `start` and the header `L` / `T` / `t_index` are read. The harness-derived `tau_int_rec`, `n_eff`, `undersampled`, `sokal_w` fields are NOT read; the analyzer's `analyze-eq.out` is parsed only for the comparison table at the end.
- Script: `qbp-kz-g2-r3-recompute.py` (stdlib + matplotlib; Python 3.10, matplotlib 3.5.1). Invocation used:

```
cd /tmp/claude-1000/-home-prime-Documents-QBP/cc9bae42-b88b-4399-8c1c-777c775ce9bd/scratchpad/kz-r3-run/recompute
python3 qbp-kz-g2-r3-recompute.py --raw ../raw --out . --plots
```
  (exit 0 = agreement to printed precision; exit 2 = a disagreement is listed. `--analyzer <path>` overrides the default `<out>/../analysis/analyze-eq.out`. Runtime about 10 s.)

## Reading of the frozen text where it leaves a choice (declared, not tuned)

| Item | Choice made in this recompute |
|---|---|
| Strict local maximum | a bin strictly above BOTH neighbours; the two edge bins (one neighbour) are not candidates |
| 3σ floor | evaluated on the smoothed counts with the raw h_valley (0 stays 0 in the test); 0.5 is substituted only before the log, as the text says |
| Candidate pair | every pair of strict maxima with ≥ 1 bin between; the pair with the largest RESOLVED barrier wins |
| Jackknife SE | √((n−1)/n · Σ(θ_i − θ̄)²), n = 3 leave-one-seed-out subsamples on the fixed 60-bin grid |
| Blocked SE | block means b_i of 250 records; SE = √(Σ(b_i − b̄)² / (N_b (N_b − 1))); hot pair N_b = 40 (20 per seed, never straddling), cold N_b = 20 |
| τ_int | ρ(k) = c(k)/c(0), c(k) = (1/(N−k)) Σ (x_i − x̄)(x_{i+k} − x̄); τ(W) = ½ + Σ_{k=1}^{W} ρ(k); W = smallest W ≥ 1 with W ≥ 6 τ(W) |
| Peak separation Δe | (j − i) × bin width (bin centres) |
| Phase locking | seed counted iff max(e) < valley-bin centre or min(e) > valley-bin centre over all 5,000 records |
| Coexistence weights | raw counts, bins below the valley bin → w_low, above → w_high, the valley bin half to each; sign change searched between CONSECUTIVE resolved grid points only |
| Max-step index | k = 0-based index of the earlier record of the pair (the text names no convention; this is the analyzer's) |
| D_e / D_S at L = 8 | computed and reported; only L ∈ {12, 16} gate, as the text says |

# qbp-kz-g2 round 3 — independent recompute of the FROZEN-v1 §3 reading

Frozen rule sha256 `132f6a4251ab3ff9ecb8f9b56c607ba1a1dd7e7ed4256fd4fb6f952c0fe1a623` (QBP PR #800 @ ae37319). Computed from the raw per-seed series only; no harness-derived or analyzer field used.
bins: 60 per L over the pooled e; smoothing 3-bin (truncated edges); floor 3 sigma; dF0 = ln 2 = 0.6931; eps floor 0.20; block 250; D > 3

## Per-(L, T) table

| L | t | T | dF_L(T) | sigma_dF | resolved | peaks (bins) | h_lower | h_valley | depth/sigma | V_L(T) | D_e | D_S | start-dep | undersampled | S bimodal |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 8 | 0 | 1.08 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.665978 | 0.06 | 0.27 | false | false | false |
| 8 | 1 | 1.10 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.665938 | 0.64 | 0.97 | false | false | false |
| 8 | 2 | 1.12 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.665896 | 0.75 | 0.17 | false | false | false |
| 8 | 4 | 1.14 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.665781 | 0.39 | 0.62 | false | false | false |
| 8 | 6 | 1.16 | 7.4262 | 1.1915 | true | 20,52 (valley 34) | 839.7 | 0.5 | 28.98 | 0.644226 | 20.22 | 20.17 | true | true | true |
| 8 | 8 | 1.18 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666500 | 0.31 | 0.45 | false | false | false |
| 8 | 9 | 1.20 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666524 | 0.76 | 1.33 | false | false | false |
| 12 | 0 | 1.08 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666460 | 0.15 | 0.85 | false | false | false |
| 12 | 1 | 1.10 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666450 | 0.48 | 0.15 | false | false | false |
| 12 | 2 | 1.12 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666435 | 0.51 | 1.07 | false | false | false |
| 12 | 3 | 1.13 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666423 | 1.40 | 1.35 | false | false | false |
| 12 | 4 | 1.14 | 7.8256 | 1.6729 | true | 15,51 (valley 32) | 834.7 | 0.3 | 28.87 | 0.635118 | 4.56 | 4.58 | true | true | true |
| 12 | 5 | 1.15 | 7.7313 | 5.1542 | true | 17,53 (valley 25) | 1139.3 | 0.5 | 33.75 | 0.645466 | 897.86 | 1204.52 | true | false | true |
| 12 | 6 | 1.16 | 7.6664 | 5.1109 | true | 20,54 (valley 28) | 1067.7 | 0.5 | 32.68 | 0.647873 | 683.65 | 825.61 | true | false | true |
| 12 | 7 | 1.17 | 7.4077 | 4.9385 | true | 24,54 (valley 35) | 824.3 | 0.5 | 28.71 | 0.651432 | 317.39 | 361.35 | true | false | true |
| 12 | 8 | 1.18 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666618 | 1.72 | 1.16 | false | false | false |
| 12 | 9 | 1.20 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666626 | 0.67 | 2.27 | false | false | false |
| 16 | 0 | 1.08 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666581 | 0.57 | 0.47 | false | false | false |
| 16 | 1 | 1.10 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666575 | 0.83 | 0.19 | false | false | false |
| 16 | 2 | 1.12 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666569 | 1.26 | 2.28 | false | false | false |
| 16 | 3 | 1.13 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666562 | 0.19 | 0.25 | false | false | false |
| 16 | 4 | 1.14 | 7.9421 | 5.2948 | true | 13,52 (valley 20) | 1406.7 | 0.5 | 37.51 | 0.643988 | 1100.25 | 1255.80 | true | false | true |
| 16 | 5 | 1.15 | 7.9374 | 5.2916 | true | 16,54 (valley 21) | 1400.0 | 0.5 | 37.42 | 0.645799 | 1217.31 | 1359.06 | true | false | true |
| 16 | 6 | 1.16 | 7.8846 | 5.2564 | true | 19,55 (valley 26) | 1328.0 | 0.5 | 36.44 | 0.648146 | 936.56 | 1149.74 | true | false | true |
| 16 | 7 | 1.17 | 7.6840 | 5.1227 | true | 23,56 (valley 31) | 1086.7 | 0.5 | 32.96 | 0.651849 | 366.62 | 442.20 | true | false | true |
| 16 | 8 | 1.18 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666647 | 0.85 | 1.29 | false | false | false |
| 16 | 9 | 1.20 | 0.0000 | 0.0000 | false | - | 0.0 | 0.0 | 0.00 | 0.666649 | 0.81 | 1.77 | false | false | false |

## Per-seed table (tau_int in RECORD units from the e record series; n_eff = 5000/(2 tau); undersampled iff n_eff < 20)

| L | t | T | seed | start | <e> | SE250(e) | <S> | SE250(S) | tau_int_rec | W | n_eff | undersampled | max step e (rec k, 0-based) | max step S (rec k) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 8 | 0 | 1.08 | 6000 | haar | 0.940837 | 3.71e-04 | 0.597910 | 2.34e-04 | 0.785 | 5 | 3186.6 | false | 0.0974 (52) | 0.0578 (4299) |
| 8 | 0 | 1.08 | 6001 | haar | 0.940408 | 3.13e-04 | 0.598039 | 2.34e-04 | 0.730 | 5 | 3426.8 | false | 0.1045 (2549) | 0.0605 (778) |
| 8 | 0 | 1.08 | 6002 | aligned | 0.940646 | 3.09e-04 | 0.598047 | 2.16e-04 | 0.744 | 5 | 3358.7 | false | 0.1346 (478) | 0.0723 (478) |
| 8 | 1 | 1.10 | 6004 | haar | 0.972242 | 3.07e-04 | 0.579422 | 2.44e-04 | 0.857 | 6 | 2918.6 | false | 0.1079 (3318) | 0.0626 (893) |
| 8 | 1 | 1.10 | 6005 | haar | 0.971633 | 4.12e-04 | 0.580083 | 2.98e-04 | 0.800 | 5 | 3126.8 | false | 0.1094 (625) | 0.0676 (3363) |
| 8 | 1 | 1.10 | 6006 | aligned | 0.972261 | 4.34e-04 | 0.579354 | 3.62e-04 | 0.858 | 6 | 2912.7 | false | 0.1122 (1891) | 0.0626 (1891) |
| 8 | 2 | 1.12 | 6008 | haar | 1.007164 | 4.76e-04 | 0.558175 | 4.41e-04 | 0.946 | 6 | 2644.0 | false | 0.1069 (4111) | 0.0619 (3129) |
| 8 | 2 | 1.12 | 6009 | haar | 1.007043 | 4.96e-04 | 0.558664 | 3.95e-04 | 0.986 | 6 | 2536.1 | false | 0.1036 (2263) | 0.0576 (2631) |
| 8 | 2 | 1.12 | 6010 | aligned | 1.007468 | 3.52e-04 | 0.558354 | 2.62e-04 | 0.949 | 6 | 2635.4 | false | 0.1223 (1732) | 0.0619 (1732) |
| 8 | 4 | 1.14 | 6016 | haar | 1.047299 | 6.25e-04 | 0.532757 | 4.91e-04 | 1.386 | 9 | 1803.3 | false | 0.0984 (3149) | 0.0713 (3942) |
| 8 | 4 | 1.14 | 6017 | haar | 1.048235 | 5.21e-04 | 0.532278 | 4.63e-04 | 1.451 | 9 | 1723.3 | false | 0.1226 (3662) | 0.0754 (3662) |
| 8 | 4 | 1.14 | 6018 | aligned | 1.047474 | 6.38e-04 | 0.532883 | 4.81e-04 | 1.265 | 8 | 1976.8 | false | 0.1085 (4312) | 0.0822 (2435) |
| 8 | 6 | 1.16 | 6024 | haar | 1.465294 | 7.91e-04 | 0.105666 | 1.04e-03 | 2.534 | 16 | 986.6 | false | 0.0894 (950) | 0.0743 (823) |
| 8 | 6 | 1.16 | 6025 | haar | 1.397147 | 3.12e-02 | 0.178605 | 3.36e-02 | 338.943 | 2034 | 7.4 | true | 0.1274 (4088) | 0.0872 (4088) |
| 8 | 6 | 1.16 | 6026 | aligned | 1.100167 | 7.98e-04 | 0.497151 | 6.90e-04 | 1.885 | 12 | 1326.3 | false | 0.1200 (4341) | 0.0873 (2987) |
| 8 | 8 | 1.18 | 6032 | haar | 1.483425 | 3.96e-04 | 0.093379 | 4.20e-04 | 1.299 | 8 | 1923.8 | false | 0.0726 (2376) | 0.0622 (1279) |
| 8 | 8 | 1.18 | 6033 | haar | 1.484010 | 4.94e-04 | 0.092692 | 5.70e-04 | 1.284 | 8 | 1946.7 | false | 0.0727 (1803) | 0.0619 (3543) |
| 8 | 8 | 1.18 | 6034 | aligned | 1.483857 | 3.15e-04 | 0.093268 | 3.72e-04 | 1.108 | 7 | 2256.8 | false | 0.0852 (2675) | 0.0557 (1676) |
| 8 | 9 | 1.20 | 6036 | haar | 1.497131 | 2.76e-04 | 0.086659 | 4.23e-04 | 0.931 | 6 | 2684.2 | false | 0.0735 (3227) | 0.0624 (3296) |
| 8 | 9 | 1.20 | 6037 | haar | 1.496882 | 2.95e-04 | 0.086973 | 3.83e-04 | 0.902 | 6 | 2770.1 | false | 0.0723 (1663) | 0.0554 (4947) |
| 8 | 9 | 1.20 | 6038 | aligned | 1.497283 | 3.03e-04 | 0.086283 | 2.85e-04 | 0.946 | 6 | 2642.7 | false | 0.0808 (1118) | 0.0634 (2056) |
| 12 | 0 | 1.08 | 6040 | haar | 0.943015 | 2.34e-04 | 0.583808 | 2.53e-04 | 0.843 | 6 | 2966.1 | false | 0.0518 (1508) | 0.0337 (2335) |
| 12 | 0 | 1.08 | 6041 | haar | 0.942873 | 2.13e-04 | 0.584006 | 2.45e-04 | 0.757 | 5 | 3301.5 | false | 0.0572 (2923) | 0.0308 (1265) |
| 12 | 0 | 1.08 | 6042 | aligned | 0.942988 | 2.52e-04 | 0.584124 | 1.86e-04 | 0.829 | 5 | 3016.1 | false | 0.0609 (4189) | 0.0304 (1048) |
| 12 | 1 | 1.10 | 6044 | haar | 0.975143 | 1.99e-04 | 0.564402 | 1.76e-04 | 0.889 | 6 | 2811.9 | false | 0.0610 (242) | 0.0382 (230) |
| 12 | 1 | 1.10 | 6045 | haar | 0.975086 | 2.31e-04 | 0.564154 | 2.57e-04 | 0.865 | 6 | 2889.8 | false | 0.0592 (2307) | 0.0392 (2228) |
| 12 | 1 | 1.10 | 6046 | aligned | 0.974960 | 2.84e-04 | 0.564318 | 2.08e-04 | 0.873 | 6 | 2862.1 | false | 0.0669 (1682) | 0.0377 (132) |
| 12 | 2 | 1.12 | 6048 | haar | 1.010884 | 2.04e-04 | 0.541834 | 2.29e-04 | 0.964 | 6 | 2592.5 | false | 0.0569 (3893) | 0.0365 (942) |
| 12 | 2 | 1.12 | 6049 | haar | 1.011201 | 2.92e-04 | 0.541776 | 2.82e-04 | 1.011 | 7 | 2472.2 | false | 0.0607 (1611) | 0.0361 (982) |
| 12 | 2 | 1.12 | 6050 | aligned | 1.011225 | 3.13e-04 | 0.541414 | 3.19e-04 | 1.115 | 7 | 2241.6 | false | 0.0597 (4521) | 0.0401 (822) |
| 12 | 3 | 1.13 | 6052 | haar | 1.030931 | 3.12e-04 | 0.529044 | 2.77e-04 | 1.127 | 7 | 2217.5 | false | 0.0598 (2141) | 0.0359 (2932) |
| 12 | 3 | 1.13 | 6053 | haar | 1.030714 | 3.45e-04 | 0.528736 | 3.93e-04 | 1.300 | 8 | 1923.8 | false | 0.0599 (4892) | 0.0374 (1721) |
| 12 | 3 | 1.13 | 6054 | aligned | 1.031440 | 3.74e-04 | 0.528354 | 3.18e-04 | 1.261 | 8 | 1983.3 | false | 0.0652 (1315) | 0.0345 (1505) |
| 12 | 4 | 1.14 | 6056 | haar | 1.286116 | 4.37e-02 | 0.247888 | 4.98e-02 | 437.430 | 2630 | 5.7 | true | 0.0574 (3750) | 0.0390 (4979) |
| 12 | 4 | 1.14 | 6057 | haar | 1.086878 | 2.37e-02 | 0.475155 | 2.69e-02 | 207.384 | 1245 | 12.1 | true | 0.0631 (1638) | 0.0381 (4851) |
| 12 | 4 | 1.14 | 6058 | aligned | 1.053129 | 3.28e-04 | 0.514152 | 3.63e-04 | 1.444 | 9 | 1731.7 | false | 0.0622 (2511) | 0.0387 (4145) |
| 12 | 5 | 1.15 | 6060 | haar | 1.457566 | 3.08e-04 | 0.060580 | 3.50e-04 | 2.612 | 16 | 957.0 | false | 0.0499 (290) | 0.0354 (781) |
| 12 | 5 | 1.15 | 6061 | haar | 1.457799 | 2.77e-04 | 0.060421 | 2.37e-04 | 2.062 | 13 | 1212.2 | false | 0.0453 (4155) | 0.0344 (528) |
| 12 | 5 | 1.15 | 6062 | aligned | 1.078003 | 3.70e-04 | 0.497135 | 2.96e-04 | 1.585 | 10 | 1577.5 | false | 0.0684 (2123) | 0.0406 (394) |
| 12 | 6 | 1.16 | 6064 | haar | 1.468444 | 2.86e-04 | 0.055833 | 2.50e-04 | 1.568 | 10 | 1593.9 | false | 0.0458 (4189) | 0.0350 (4504) |
| 12 | 6 | 1.16 | 6065 | haar | 1.468176 | 2.60e-04 | 0.056243 | 2.35e-04 | 1.635 | 10 | 1528.6 | false | 0.0416 (2372) | 0.0309 (2358) |
| 12 | 6 | 1.16 | 6066 | aligned | 1.108218 | 4.90e-04 | 0.474634 | 4.77e-04 | 2.158 | 13 | 1158.5 | false | 0.0584 (3619) | 0.0403 (827) |
| 12 | 7 | 1.17 | 6068 | haar | 1.476958 | 1.97e-04 | 0.053203 | 1.74e-04 | 1.282 | 8 | 1950.8 | false | 0.0400 (3210) | 0.0316 (2110) |
| 12 | 7 | 1.17 | 6069 | haar | 1.476778 | 2.17e-04 | 0.052962 | 1.88e-04 | 1.281 | 8 | 1951.5 | false | 0.0382 (4110) | 0.0301 (2644) |
| 12 | 7 | 1.17 | 6070 | aligned | 1.151030 | 1.02e-03 | 0.440207 | 1.06e-03 | 6.361 | 39 | 393.0 | false | 0.0670 (2884) | 0.0458 (2884) |
| 12 | 8 | 1.18 | 6072 | haar | 1.484206 | 1.94e-04 | 0.050760 | 1.61e-04 | 1.147 | 7 | 2180.1 | false | 0.0353 (2459) | 0.0317 (298) |
| 12 | 8 | 1.18 | 6073 | haar | 1.484273 | 2.04e-04 | 0.050624 | 1.53e-04 | 1.000 | 6 | 2500.6 | false | 0.0373 (2298) | 0.0334 (3801) |
| 12 | 8 | 1.18 | 6074 | aligned | 1.484577 | 1.39e-04 | 0.050480 | 1.47e-04 | 1.229 | 8 | 2034.8 | false | 0.0420 (1066) | 0.0292 (4321) |
| 12 | 9 | 1.20 | 6076 | haar | 1.497275 | 1.30e-04 | 0.046898 | 1.45e-04 | 0.805 | 5 | 3103.8 | false | 0.0370 (3231) | 0.0271 (4120) |
| 12 | 9 | 1.20 | 6077 | haar | 1.497420 | 1.41e-04 | 0.046958 | 1.22e-04 | 0.890 | 6 | 2810.3 | false | 0.0439 (3547) | 0.0298 (61) |
| 12 | 9 | 1.20 | 6078 | aligned | 1.497232 | 1.41e-04 | 0.047279 | 1.23e-04 | 0.882 | 6 | 2834.1 | false | 0.0414 (4744) | 0.0307 (2628) |
| 16 | 0 | 1.08 | 6080 | haar | 0.943762 | 1.40e-04 | 0.577058 | 1.66e-04 | 0.895 | 6 | 2792.6 | false | 0.0348 (807) | 0.0202 (4105) |
| 16 | 0 | 1.08 | 6081 | haar | 0.943699 | 1.22e-04 | 0.577261 | 1.42e-04 | 0.758 | 5 | 3300.1 | false | 0.0375 (3006) | 0.0198 (176) |
| 16 | 0 | 1.08 | 6082 | aligned | 0.943815 | 1.17e-04 | 0.577255 | 1.72e-04 | 0.805 | 5 | 3104.1 | false | 0.0362 (600) | 0.0193 (327) |
| 16 | 1 | 1.10 | 6084 | haar | 0.975936 | 1.84e-04 | 0.557256 | 2.43e-04 | 0.940 | 6 | 2658.7 | false | 0.0413 (354) | 0.0285 (354) |
| 16 | 1 | 1.10 | 6085 | haar | 0.975742 | 1.63e-04 | 0.557426 | 1.88e-04 | 0.871 | 6 | 2869.1 | false | 0.0458 (1527) | 0.0227 (994) |
| 16 | 1 | 1.10 | 6086 | aligned | 0.975681 | 1.47e-04 | 0.557298 | 1.61e-04 | 1.076 | 7 | 2324.4 | false | 0.0414 (4109) | 0.0213 (2781) |
| 16 | 2 | 1.12 | 6088 | haar | 1.011809 | 2.29e-04 | 0.534297 | 2.17e-04 | 1.038 | 7 | 2407.5 | false | 0.0411 (1850) | 0.0238 (102) |
| 16 | 2 | 1.12 | 6089 | haar | 1.011888 | 1.71e-04 | 0.534266 | 2.23e-04 | 0.984 | 6 | 2540.1 | false | 0.0371 (583) | 0.0243 (622) |
| 16 | 2 | 1.12 | 6090 | aligned | 1.012115 | 1.57e-04 | 0.533732 | 1.86e-04 | 1.077 | 7 | 2320.8 | false | 0.0365 (3314) | 0.0221 (707) |
| 16 | 3 | 1.13 | 6092 | haar | 1.032336 | 1.52e-04 | 0.520316 | 2.03e-04 | 1.198 | 8 | 2086.6 | false | 0.0416 (4755) | 0.0272 (1548) |
| 16 | 3 | 1.13 | 6093 | haar | 1.032347 | 2.63e-04 | 0.520340 | 3.20e-04 | 1.237 | 8 | 2021.0 | false | 0.0422 (804) | 0.0286 (804) |
| 16 | 3 | 1.13 | 6094 | aligned | 1.032384 | 1.70e-04 | 0.520409 | 2.57e-04 | 1.260 | 8 | 1984.0 | false | 0.0361 (2508) | 0.0228 (3772) |
| 16 | 4 | 1.14 | 6096 | haar | 1.444253 | 3.46e-04 | 0.044728 | 3.73e-04 | 3.924 | 24 | 637.1 | false | 0.0360 (373) | 0.0228 (1859) |
| 16 | 4 | 1.14 | 6097 | haar | 1.444323 | 2.61e-04 | 0.044377 | 2.74e-04 | 3.370 | 21 | 741.9 | false | 0.0279 (3700) | 0.0203 (1043) |
| 16 | 4 | 1.14 | 6098 | aligned | 1.054759 | 2.82e-04 | 0.505002 | 2.85e-04 | 1.390 | 9 | 1798.5 | false | 0.0372 (1846) | 0.0237 (1555) |
| 16 | 5 | 1.15 | 6100 | haar | 1.457843 | 1.52e-04 | 0.039344 | 1.56e-04 | 2.060 | 13 | 1213.9 | false | 0.0292 (880) | 0.0202 (4422) |
| 16 | 5 | 1.15 | 6101 | haar | 1.457836 | 2.32e-04 | 0.039185 | 1.81e-04 | 2.195 | 14 | 1138.9 | false | 0.0290 (3625) | 0.0206 (2438) |
| 16 | 5 | 1.15 | 6102 | aligned | 1.080578 | 2.78e-04 | 0.486334 | 3.07e-04 | 1.751 | 11 | 1427.7 | false | 0.0406 (4154) | 0.0244 (1602) |
| 16 | 6 | 1.16 | 6104 | haar | 1.468427 | 2.04e-04 | 0.036446 | 1.83e-04 | 1.557 | 10 | 1605.3 | false | 0.0320 (4882) | 0.0210 (4613) |
| 16 | 6 | 1.16 | 6105 | haar | 1.468512 | 1.83e-04 | 0.036360 | 1.26e-04 | 1.431 | 9 | 1747.2 | false | 0.0257 (1435) | 0.0181 (3592) |
| 16 | 6 | 1.16 | 6106 | aligned | 1.110434 | 3.58e-04 | 0.463998 | 3.55e-04 | 2.563 | 16 | 975.4 | false | 0.0366 (4821) | 0.0254 (1765) |
| 16 | 7 | 1.17 | 6108 | haar | 1.477070 | 1.64e-04 | 0.034455 | 1.02e-04 | 1.314 | 8 | 1902.7 | false | 0.0269 (2084) | 0.0205 (2183) |
| 16 | 7 | 1.17 | 6109 | haar | 1.477072 | 1.19e-04 | 0.034321 | 1.00e-04 | 1.202 | 8 | 2080.1 | false | 0.0250 (4419) | 0.0192 (107) |
| 16 | 7 | 1.17 | 6110 | aligned | 1.154929 | 8.73e-04 | 0.428150 | 8.88e-04 | 7.393 | 45 | 338.2 | false | 0.0475 (4230) | 0.0294 (2397) |
| 16 | 8 | 1.18 | 6112 | haar | 1.484370 | 1.11e-04 | 0.032793 | 9.73e-05 | 1.073 | 7 | 2329.8 | false | 0.0255 (635) | 0.0174 (4605) |
| 16 | 8 | 1.18 | 6113 | haar | 1.484518 | 1.34e-04 | 0.032770 | 8.23e-05 | 1.062 | 7 | 2353.7 | false | 0.0263 (1625) | 0.0211 (3066) |
| 16 | 8 | 1.18 | 6114 | aligned | 1.484555 | 9.74e-05 | 0.032919 | 8.58e-05 | 1.072 | 7 | 2331.1 | false | 0.0251 (2049) | 0.0185 (4367) |
| 16 | 9 | 1.20 | 6116 | haar | 1.497260 | 9.04e-05 | 0.030629 | 8.02e-05 | 0.830 | 5 | 3011.7 | false | 0.0236 (2796) | 0.0201 (4387) |
| 16 | 9 | 1.20 | 6117 | haar | 1.497316 | 7.30e-05 | 0.030558 | 8.14e-05 | 0.798 | 5 | 3131.8 | false | 0.0229 (2586) | 0.0175 (435) |
| 16 | 9 | 1.20 | 6118 | aligned | 1.497199 | 9.31e-05 | 0.030811 | 1.09e-04 | 0.753 | 5 | 3318.4 | false | 0.0269 (2996) | 0.0196 (1144) |

## Primary

| L | dF*(L) | T*(L) (t) | sigma*(L) | V_min(L) at T | bins [lo, hi] | de at T* |
|---|---|---|---|---|---|---|
| 8 | 7.4262 | 1.16 (6) | 1.1915 | 0.644226 at 1.16 | [0.85935, 1.55212] | 0.3695 |
| 12 | 7.8256 | 1.14 (4) | 1.6729 | 0.635118 at 1.14 | [0.88740, 1.53135] | 0.3864 |
| 16 | 7.9421 | 1.14 (4) | 5.2948 | 0.643988 at 1.14 | [0.91560, 1.51571] | 0.3901 |

Leave-one-seed-out dF at each L's T*(L): L=8 7.4262, 7.2579, 5.5607; L=12 5.2575, 7.7035, 7.8256; L=16 7.9421, 7.9421, 0.0000

## Rule evaluation (precedence (a) -> (b) -> (c))

- eps(16,12) = 11.1055 ; eps(12,8) = 4.1077
- (a) dF*(16) = 7.9421 >= ln 2 = 0.6931 ? true
- (a) dF*(16) = 7.9421 >= dF*(12) - eps(16,12) = -3.2798 ? true
- (a) dF*(12) = 7.8256 >= dF*(8) - eps(12,8) = 3.3185 ? true
- (a) clauses all true ? true
- (a)-side gate: any undersampled run at (16, T*(16) = 1.14) ? false
- (a) fires ? true
- (b) dF_16(T) = 0 and dF_12(T) = 0 at every T ? false
- (b)-side gate: undersampled run at any (L in {12,16}, T) ? true
- (b)-side gate: start-dependent point at any (L in {12,16}, T) ? true (start-dependent without a resolved pair: false)
- (b) fires ? false

**OUTCOME: H-FO by rule (a)**

## Secondaries (non-gating)

- V_min: L=8 0.644226, L=12 0.635118, L=16 0.643988; two-point 1/L^3 extrapolation V* = 0.650461 (2/3 = 0.666667)
- at (16, T*(16) = 1.14): de (peak separation) = 0.3901; phase-locking count = 3 of 3 seeds
- de trend at each L's own T*: L=8 0.3695, L=12 0.3864, L=16 0.3901 (0 = no resolved pair there)
- no coexistence T readable at L = 16 (4 bimodal grid point(s); needs >= 2 with an equal-weight crossing)
- weights at the L=16 resolved points (w_low - w_high)/total: T=1.14 -0.333, T=1.15 -0.333, T=1.16 -0.333, T=1.17 -0.333
- S histograms: 9 of 27 points resolved-bimodal (descriptive only)

## Recompute vs frozen analyzer (analyzer text parsed for this table only)

Differences are |recompute - analyzer| on the analyzer's printed precision; a flag mismatch prints MISMATCH.

| L | t | T | d dF | d sigma_dF | d V_L | d D_e | d D_S | d h_lower | d h_valley | peaks | resolved | start-dep | undersampled | S bimodal | d tau (3 seeds) | d <e> (3 seeds) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 8 | 0 | 1.08 | 0.0e+00 | 0.0e+00 | 9.2e-08 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.2e-07/3.7e-07/1.8e-07 |
| 8 | 1 | 1.10 | 0.0e+00 | 0.0e+00 | 7.8e-08 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 1.7e-07/4.3e-07/3.7e-07 |
| 8 | 2 | 1.12 | 0.0e+00 | 0.0e+00 | 2.3e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.8e-08/1.2e-07/3.1e-07 |
| 8 | 4 | 1.14 | 0.0e+00 | 0.0e+00 | 2.8e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.4e-07/2.9e-07/4.4e-07 |
| 8 | 6 | 1.16 | 4.8e-05 | 4.1e-05 | 1.1e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.6e-07/2.0e-07/4.9e-07 |
| 8 | 8 | 1.18 | 0.0e+00 | 0.0e+00 | 4.8e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.8e-07/2.6e-08/1.3e-07 |
| 8 | 9 | 1.20 | 0.0e+00 | 0.0e+00 | 2.2e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 2.0e-07/1.0e-07/4.7e-07 |
| 12 | 0 | 1.08 | 0.0e+00 | 0.0e+00 | 3.1e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 6.7e-08/2.1e-07/2.4e-07 |
| 12 | 1 | 1.10 | 0.0e+00 | 0.0e+00 | 2.4e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.1e-07/2.3e-07/4.0e-07 |
| 12 | 2 | 1.12 | 0.0e+00 | 0.0e+00 | 3.4e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.1e-07/1.1e-07/8.2e-08 |
| 12 | 3 | 1.13 | 0.0e+00 | 0.0e+00 | 1.9e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.9e-08/2.1e-07/1.2e-07 |
| 12 | 4 | 1.14 | 4.5e-05 | 4.1e-05 | 4.3e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 1.5e-07/1.1e-07/2.2e-07 |
| 12 | 5 | 1.15 | 4.6e-05 | 3.1e-05 | 3.0e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 2.4e-07/2.4e-07/4.5e-07 |
| 12 | 6 | 1.16 | 2.2e-05 | 1.9e-05 | 5.0e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.7e-07/7.0e-08/2.0e-07 |
| 12 | 7 | 1.17 | 2.2e-05 | 1.9e-05 | 1.3e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 1.7e-07/1.6e-07/2.2e-07 |
| 12 | 8 | 1.18 | 0.0e+00 | 0.0e+00 | 1.5e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.0e-07/8.8e-08/4.6e-07 |
| 12 | 9 | 1.20 | 0.0e+00 | 0.0e+00 | 2.1e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.3e-07/2.3e-07/3.8e-07 |
| 16 | 0 | 1.08 | 0.0e+00 | 0.0e+00 | 3.2e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 7.1e-08/2.5e-08/3.6e-07 |
| 16 | 1 | 1.10 | 0.0e+00 | 0.0e+00 | 3.2e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 9.1e-09/3.3e-07/4.1e-07 |
| 16 | 2 | 1.12 | 0.0e+00 | 0.0e+00 | 2.0e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 1.6e-07/3.3e-07/2.5e-07 |
| 16 | 3 | 1.13 | 0.0e+00 | 0.0e+00 | 3.0e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.7e-07/3.5e-08/3.8e-07 |
| 16 | 4 | 1.14 | 2.5e-05 | 5.0e-05 | 2.8e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 5.7e-08/1.8e-08/3.5e-07 |
| 16 | 5 | 1.15 | 2.5e-05 | 1.7e-05 | 2.9e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.0e-07/4.8e-07/2.2e-07 |
| 16 | 6 | 1.16 | 2.3e-05 | 1.6e-05 | 3.7e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 7.3e-08/1.8e-07/3.2e-07 |
| 16 | 7 | 1.17 | 1.7e-05 | 2.2e-05 | 1.6e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 4.1e-07/1.2e-07/5.3e-08 |
| 16 | 8 | 1.18 | 0.0e+00 | 0.0e+00 | 2.6e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.9e-07/4.7e-08/1.6e-07 |
| 16 | 9 | 1.20 | 0.0e+00 | 0.0e+00 | 4.7e-07 | 0.00 | 0.00 | 0.0 | 0.0 | ok | ok | ok | ok | ok | 0.000/0.000/0.000 | 3.7e-07/1.9e-07/2.1e-07 |

Primary / rule comparison:

| quantity | recompute | analyzer | abs diff |
|---|---|---|---|
| dF_star(L=8) | 7.4262 | 7.4262 | 4.8e-05 |
| T_star(L=8) | 1.16 | 1.16 | 0.0e+00 |
| sigma_star(L=8) | 1.1915 | 1.1915 | 4.1e-05 |
| V_min(L=8) | 0.644226 | 0.644226 | 1.1e-07 |
| de_star(L=8) | 0.3695 | 0.3695 | 2.0e-05 |
| dF_star(L=12) | 7.8256 | 7.8256 | 4.5e-05 |
| T_star(L=12) | 1.14 | 1.14 | 0.0e+00 |
| sigma_star(L=12) | 1.6729 | 1.6729 | 4.1e-05 |
| V_min(L=12) | 0.635118 | 0.635118 | 4.3e-07 |
| de_star(L=12) | 0.3864 | 0.3864 | 2.9e-05 |
| dF_star(L=16) | 7.9421 | 7.9421 | 2.5e-05 |
| T_star(L=16) | 1.14 | 1.14 | 0.0e+00 |
| sigma_star(L=16) | 5.2948 | 5.2948 | 5.0e-05 |
| V_min(L=16) | 0.643988 | 0.643988 | 2.8e-07 |
| de_star(L=16) | 0.3901 | 0.3901 | 2.9e-05 |
| eps_16_12 | 11.1055 | 11.1055 | 3.5e-05 |
| eps_12_8 | 4.1077 | 4.1077 | 3.5e-05 |
| v_star | 0.650461 | 0.650461 | 1.3e-07 |
| de_16 | 0.3901 | 0.3901 | 2.9e-05 |
| phase-lock count (16,T*) | 3 | 3 | ok |
| S-bimodal count | 9 | 9 | ok |
| coexistence T (16) | None | None | ok |
| OUTCOME | H-FO by rule (a) | H-FO by rule (a) | ok |

Max absolute differences over all 27 points / 81 runs: dF 4.78e-05, sigma_dF 4.98e-05, V_L 4.98e-07, D_e 4.96e-03, D_S 4.88e-03, h_lower 3.33e-02, h_valley 3.33e-02, depth/sigma 4.83e-03, tau_int 5.00e-04, n_eff 4.89e-02, <e> 4.90e-07, <S> 4.92e-07, SE250 (relative) 4.20e-03

No flag, peak-index, Sokal-W, max-step or outcome mismatch.

Agreement to the analyzer's printed precision: **YES**

Plots written: kz-g2-r3-eseries-hot-cold.png, kz-g2-r3-hist-panels.png, kz-g2-r3-VL.png, kz-g2-r3-S-vs-T.png, kz-g2-r3-traces-L16-T114.png (dpi 110)

## Diff summary vs the frozen analyzer

Every one of the 27 per-point rows and 81 per-run rows agrees with `analyze-eq.out` to its printed precision: max |Δ| dF 4.8e-05 (printed to 1e-4), σ_ΔF 5.0e-05, V_L 5.0e-07 (printed to 1e-6), D_e 5.0e-03 and D_S 4.9e-03 (printed to 1e-2), h_lower / h_valley 3.3e-02 (printed to 0.1; the ⅓-count smoothing residue), depth/σ 4.8e-03, τ_int 5.0e-04 (printed to 1e-3), n_eff 4.9e-02 (printed to 0.1), ⟨e⟩ and ⟨S⟩ 4.9e-07 (printed to 1e-6), SE250 4.2e-03 relative (printed to 3 significant figures). All peak/valley bin indices, Sokal W values, resolved / start-dependent / undersampled / S-bimodal flags, max-step magnitudes and indices, the primary table (ΔF*, T*, σ*, V_min, Δe), ε(16,12) = 11.1055, ε(12,8) = 4.1077, V* = 0.650461, phase-locking 3 of 3, "no coexistence T readable", 9 of 27 S-bimodal, and the OUTCOME line (H-FO by rule (a), no sub-label) are identical. No disagreement; no code was adjusted to match (the one change made during development, the max-step index convention, is a labelling convention the frozen text does not fix, declared above; the magnitudes agreed before and after).

Independent reading from the raw series: **H-FO by rule (a)** — ΔF*(16) = 7.9421 ≥ ln 2; ΔF*(16) ≥ ΔF*(12) − ε(16,12) = −3.2798; ΔF*(12) = 7.8256 ≥ ΔF*(8) − ε(12,8) = 3.3185; no undersampled run at (16, T*(16) = 1.14). Rule (b) is defeated on all three counts (resolved pairs at four T at each of L = 12, 16; undersampled runs at (12, 1.14); start-dependent points at (12, 1.14–1.17) and (16, 1.14–1.17)); every start-dependent point at L ∈ {12, 16} carries a resolved pair, so the "(metastability)" sub-label condition is not met and (a) is not gate-blocked, so no "(sampling)" sub-label. The large σ*(16) = 5.29 is the leave-the-cold-seed-out subsample reading ΔF = 0 (its two hot seeds sit in one phase, so that subsample is unimodal); it enters only through ε and loosens the L-trend clauses toward (c), as the frozen note for the notary anticipated.

## What the plots show (Human Visual Review material; descriptive only)

`kz-g2-r3-eseries-hot-cold.png` and `kz-g2-r3-S-vs-T.png` (3 rows, L = 8/12/16; per-seed ⟨e⟩ and ⟨S⟩ vs T, hot seeds as two blue circles, cold seed as a red square, error bars 3× the 250-record blocked SE, shaded T = start-dependent): below T = 1.14 and above T = 1.17 the three seeds coincide at every L (error bars invisible); in the window T = 1.14–1.17 at L = 12 and L = 16 the two hot seeds sit on the high-e / low-S branch and the cold seed on the low-e / high-S branch with a gap of about 0.4 in e and 0.45 in S, far outside any error bar; at L = 8 only T = 1.16 is split, and there one hot seed (6025) carries a visible error bar because it crosses between branches; at (12, 1.14) hot seed 6056 also carries a large error bar (it visits both branches). `kz-g2-r3-hist-panels.png` (columns L = 8/12/16, rows T = 1.14 and 1.16; 3-bin-smoothed pooled e histograms with the hot and cold contributions stacked): at (8, 1.14) a single peak with all three seeds overlapping; at every other panel two separated peaks with an empty valley between them (dashed line at the valley bin, ΔF and σ annotated), the cold seed forming the low-e peak and the hot seeds the high-e peak except at (8, 1.16) and (12, 1.14), where a hot seed contributes to both. `kz-g2-r3-VL.png`: V_L(T) sits at 2/3 away from the window and dips to V_min(8) = 0.6442 at 1.16, V_min(12) = 0.6351 at 1.14, V_min(16) = 0.6440 at 1.14, with the dip at L = 12 and 16 spanning 1.14–1.17. `kz-g2-r3-traces-L16-T114.png`: at (16, 1.14) the two hot traces stay near e ≈ 1.45 and the cold trace near e ≈ 1.05 for all 5,000 records, neither crossing the valley centre e = 1.121 (phase-locking 3 of 3); at (8, 1.16) hot seed 6025 drops from the high branch to the low branch at about record 4,100 and stays there, while seed 6024 remains high and the cold seed 6026 remains low (phase-locking 2 of 3). These are the pictures behind the ΔF, D_e / D_S, V_L and phase-locking numbers above; they say nothing beyond the frozen claim scope (this sigma model, Model-A sampler at η = 0.1, periodic L ≤ 16).

## Files

- `qbp-kz-g2-r3-recompute.py` — the script (sha256 in the hand-back).
- `recompute-tables.md` — the script's full stdout (all tables, rule lines, comparison).
- `kz-g2-r3-eseries-hot-cold.png`, `kz-g2-r3-hist-panels.png`, `kz-g2-r3-VL.png`, `kz-g2-r3-S-vs-T.png`, `kz-g2-r3-traces-L16-T114.png` — dpi 110.
