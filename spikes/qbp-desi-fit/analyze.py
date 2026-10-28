"""Analysis for the qbp-desi-fit round-1 spike. Reads the raw JSON ONLY and applies section 4 of
spikes/prereg/qbp-desi-fit-r1-prereg-FROZEN-v1.md verbatim. Prints Markdown.

Usage: python3 analyze.py raw/qbp-desi-fit-r1-raw-2026-10-27.json
"""

import hashlib
import json
import sys

# Frozen section-4 thresholds (quoted verbatim in the output)
AIC_FAVOURED = -2.0  # "A favoured iff dAIC(A - LCDM) <= -2"
AIC_DISFAVOURED = 2.0  # "A disfavoured iff dAIC >= +2"
B_VS_CPL = 2.0  # "B as good as CPL iff dchi2(B - CPL) <= +2, with one parameter fewer"
SH0ES_H0, SH0ES_SIG = 73.0, 1.0  # "within 2 sigma of SH0ES (73.0 +/- 1.0)"
PRED_SHIFT = 1.0  # "the shift from LCDM is <= 1 km/s/Mpc"


def main(path):
    raw = json.load(open(path))
    sha = hashlib.sha256(open(path, "rb").read()).hexdigest()
    F = raw["fits"]
    A, B, L, C = F["A"], F["B"], F["LCDM"], F["CPL"]
    out = []
    p = out.append

    p(
        f"Raw: `{path}` sha256 `{sha}`; code commit `{raw['code_commit']}` (dirty={raw['code_dirty']}); "
        f"frozen sha256 `{raw['frozen_sha256']}`; run {raw['run_utc']}; wall {raw['wall_seconds']:.0f} s; "
        f"max RSS {raw['max_rss_MB']:.0f} MB; {raw['chi2_evaluations']} likelihood evaluations; quick_mode={raw['quick_mode']}."
    )
    N = raw["N_data"]
    p(
        f"Data points: BAO {N['bao']}, SNe {N['sne']} (zHD > {raw['sne_cuts']['zHD_min']}, no Cepheid distances), Planck {N['planck']}; N = {N['total']}."
    )
    p("")
    p("## Fits (section 3 arms)")
    p("")
    p(
        "| Model | k | χ² total | χ² BAO | χ² SNe (M-marg.) | χ² Planck | AIC | BIC | Ω_m | h | ω_b | extra | at bound |"
    )
    p("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for m in ["A", "B", "LCDM", "CPL", "A_zt0.718"]:
        f = F[m]
        q = f["params"]
        extra = ", ".join(f"{k}={q[k]:.4f}" for k in q if k not in ("Om", "h", "ob"))
        ab = ", ".join(k for k, v in f["at_bound"].items() if v) or "—"
        c = f["chi2_parts"]
        p(
            f"| {m} | {f['k']} | {f['chi2']:.3f} | {c['bao']:.3f} | {c['sne']:.3f} | {c['planck']:.3f} | {f['AIC']:.3f} | {f['BIC']:.3f} "
            f"| {q['Om']:.4f} | {q['h']:.4f} | {q['ob']:.5f} | {extra} | {ab} |"
        )
    p("")
    p("## Q1 (fit) — section 4, verbatim rules")
    p("")
    p("| Comparison | Δχ² | ΔAIC | ΔBIC | Rule (frozen) | Verdict |")
    p("|---|---|---|---|---|---|")

    def d(x, y, key):
        return x[key] - y[key]

    dAIC_A = d(A, L, "AIC")
    if dAIC_A <= AIC_FAVOURED:
        vA = "**A favoured**"
    elif dAIC_A >= AIC_DISFAVOURED:
        vA = "**A disfavoured**"
    else:
        vA = "**indistinguishable**"
    p(
        f"| A − ΛCDM | {d(A, L, 'chi2'):+.3f} | {dAIC_A:+.3f} | {d(A, L, 'BIC'):+.3f} | favoured iff ΔAIC ≤ −2; disfavoured iff ΔAIC ≥ +2; else indistinguishable | {vA} |"
    )
    p(
        f"| B − ΛCDM | {d(B, L, 'chi2'):+.3f} | {d(B, L, 'AIC'):+.3f} | {d(B, L, 'BIC'):+.3f} | reported (no threshold frozen for B vs ΛCDM) | reported |"
    )
    dchi_BC = d(B, C, "chi2")
    vB = (
        "**B as good as CPL** (one parameter fewer)"
        if dchi_BC <= B_VS_CPL
        else "**B not as good as CPL**"
    )
    p(
        f"| B − CPL | {dchi_BC:+.3f} | {d(B, C, 'AIC'):+.3f} | {d(B, C, 'BIC'):+.3f} | as good as CPL iff Δχ²(B − CPL) ≤ +2 | {vB} |"
    )
    R = F["A_zt0.718"]
    p(
        f"| robustness: A(z_t=0.718) − ΛCDM | {d(R, L, 'chi2'):+.3f} | {d(R, L, 'AIC'):+.3f} | {d(R, L, 'BIC'):+.3f} | reported, not an arm | "
        f"{'same bin as A' if (d(R, L, 'AIC') <= AIC_FAVOURED) == (dAIC_A <= AIC_FAVOURED) and (d(R, L, 'AIC') >= AIC_DISFAVOURED) == (dAIC_A >= AIC_DISFAVOURED) else 'DIFFERENT bin from A'} |"
    )
    p("")
    p("## Q2 (H₀) — section 4, verbatim rules")
    p("")
    p(
        "| Model | H₀ (km/s/Mpc) | ±1σ (profile) | shift from ΛCDM | within 2σ of SH0ES 73.0 ± 1.0 (|H₀ − 73.0| ≤ 2.0)? |"
    )
    p("|---|---|---|---|---|")
    for m in ["A", "B", "LCDM"]:
        f = F[m]
        sig = f.get("H0_profile", {}).get("sigma_H0", float("nan"))
        shift = f["H0"] - L["H0"]
        res = abs(f["H0"] - SH0ES_H0) <= 2 * SH0ES_SIG
        word = "**yes — “resolved”**" if res else "no — not resolved"
        p(f"| {m} | {f['H0']:.3f} | {sig:.3f} | {shift:+.3f} | {word} |")
    shiftA, shiftB = A["H0"] - L["H0"], B["H0"] - L["H0"]
    ok = abs(shiftA) <= PRED_SHIFT and abs(shiftB) <= PRED_SHIFT
    p("")
    p(
        f"Prediction on file (studybuddy note): shift from ΛCDM ≤ 1 km/s/Mpc → **{'holds' if ok else 'does not hold'}** "
        f"(A {shiftA:+.3f}, B {shiftB:+.3f})."
    )
    p("")
    p("## Section 5 rows that fire")
    p("")
    rows = []
    if vA != "**A disfavoured**":
        rows.append(
            "| A favoured or indistinguishable | Propose PRED-w-not-minus-1 E: unconfronted → **consistent (post-hoc)** (F stays napkin). Not `validated`. | @qbp-oppenheimer → steward |"
        )
    else:
        rows.append(
            "| A disfavoured | Propose a **falsified candidate** for PRED-w-not-minus-1, with kill-condition review. Report on QBP#772. | @qbp-oppenheimer |"
        )
    if dchi_BC <= B_VS_CPL and vA == "**A disfavoured**":
        rows.append(
            "| B good but A not | Record \"the curve's *form* fits, the *recorded* z_t doesn't\". z_t provenance check → theory lane. Nothing adopted. | @qbp-oppenheimer |"
        )
    anyres = any(abs(F[m]["H0"] - SH0ES_H0) <= 2 * SH0ES_SIG for m in ["A", "B"])
    if anyres:
        rows.append(
            '| H₀ "resolved" | Recorded as a surprise. A second, independent pipeline must reproduce it before any proposal. | @qbp-architecture |'
        )
    else:
        rows.append(
            "| H₀ not resolved (predicted) | Recorded. **No anchor may claim H₀-tension relief** from this model. | @qbp-oppenheimer |"
        )
    rows.append(
        "| Every outcome | The COMP-cmb-power-spectrum-accretion CAMB re-run stays on QBP#772 AC3. Separate from this spike. | @qbp-oppenheimer |"
    )
    p("| Outcome | Change | Owner |")
    p("|---|---|---|")
    out.extend(rows)
    p("")
    p("## z_t profile for arm B (χ² with Ω_m, h, ω_b minimised at each z_t)")
    p("")
    p("| z_t | χ² | Δχ² vs B best | H₀ | Ω_m |")
    p("|---|---|---|---|---|")
    for r in raw["zt_profile_B"]:
        p(
            f"| {r['zt']:.2f} | {r['chi2']:.3f} | {r['chi2'] - B['chi2']:+.3f} | {r['H0']:.2f} | {r['Om']:.4f} |"
        )
    p("")
    p("## Diagnostic — NOT pre-registered, no verdict (see deviations)")
    p("")
    p("| Model | k | χ² | ΔAIC vs ΛCDM | Ω_m | h | extra |")
    p("|---|---|---|---|---|---|---|")
    for m in ["DIAG_mirror_zt0.70", "DIAG_mirror_ztfree"]:
        f = F[m]
        q = f["params"]
        extra = ", ".join(f"{k}={q[k]:.4f}" for k in q if k not in ("Om", "h", "ob"))
        p(
            f"| {m} | {f['k']} | {f['chi2']:.3f} | {f['AIC'] - L['AIC']:+.3f} | {q['Om']:.4f} | {q['h']:.4f} | {extra} |"
        )
    print("\n".join(out))


if __name__ == "__main__":
    main(sys.argv[1])
