#!/usr/bin/env python3
"""REF anchors for the verified Efimov-state experiments (#669) + the Moretti–Oppio reduction theorem
+ one FLAG recording that the hosted quantum layer has no composite-system rule on record.

Tier 2 (documentation of external results; no theory claim, no proof anchor, no root, no kill on any
root). Every value below was read from the paper's own text or abstract by the literature sweep
(docs/research/efimov-experiments-2026-09-21.md, 'verified' tier only); partial/unverified entries are
NOT encoded. Written through the confined writer (#654 D7). QBP's own claim is limited to the FLAG.
Usage: python3 scripts/encode_efimov_reference_anchors.py [--dry-run]
"""

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DATE = "2026-09-21T00:00:00Z"
NOTE = "docs/research/efimov-substrate-test-2026-09-21.md"
SWEEP = "docs/research/efimov-experiments-2026-09-21.md"


def ref(
    aid,
    name,
    desc,
    src,
    mv=None,
    pv=None,
    unit=None,
    merr=None,
    kind="experiment",
    notes=None,
    chain=None,
    tier=2,
):
    r = {
        "id": aid,
        "name": name,
        "tier": tier,
        "provenance": "E",
        "provenance_kind": kind,
        "status": "coherent",
        "description": desc,
        "measured_source": src,
        "prediction_chain": chain or [],
        "last_tested_at": DATE,
        "intake_source": f"#669 Efimov side project (beekeeper 2026-09-21); {SWEEP} (verified tier)",
    }
    if mv is not None:
        r["measured_value"] = mv
    if merr is not None:
        r["measured_error"] = merr
    if pv is not None:
        r["predicted_value"] = pv
    if unit:
        r["predicted_unit"] = unit
    if notes:
        r["notes"] = notes
    return r


UNIV = (
    "Universal prediction from zero-range three-body theory (Efimov 1970; Braaten & Hammer, Phys. Rep. 428, 259 "
    "(2006)): consecutive Efimov features scale by e^{π/s₀} = 22.694 for three identical bosons (s₀ = 1.00624)."
)

ANCHORS = [
    ref(
        "REF-efimov-kraemer-2006",
        "Kraemer et al. (2006): first Efimov signature — Cs-133 three-body recombination resonance at a₋ = −850(20) a₀",
        "Innsbruck (Grimm/Nägerl). Ultracold Cs-133: a giant three-body recombination loss resonance at scattering "
        "length a₋ = −850(20) a₀ (Bohr radii), the signature of an Efimov trimer crossing the three-atom threshold; an "
        "atom–dimer resonance at a₊ = 1060(70) a₀; the ratio a₊/|a₋| = 1.25(9) against the zero-range prediction "
        "0.96(3). The first experimental evidence for Efimov states. QBP relevance (#669): a three-body bound-state "
        "spectrum — the observable against which any hosted-layer composite-system rule is tested.",
        "Kraemer, T., Mark, M., Waldburger, P., Danzl, J. G., Chin, C., Engeser, B., Lange, A. D., Pilch, K., Jaakkola, A., "
        "Nägerl, H.-C., Grimm, R., Nature 440, 315–318 (2006). doi:10.1038/nature04626",
        mv=1.25,
        merr=0.09,
        pv=0.96,
        unit="a₊/|a₋| (dimensionless)",
        notes=(
            "a₋ = −850(20) a₀; a₊ = 1060(70) a₀. The 0.96(3) is the zero-range universal prediction; the ≈3σ gap is "
            "understood in the subsequent literature through finite-range corrections to that baseline. The record's "
            "status describes the ledger record (an external result on file), not agreement with zero-range theory."
        ),
    ),
    ref(
        "REF-efimov-gross-2009",
        "Gross et al. (2009): Li-7 Efimov resonance a₋ = −264(11) a₀ and recombination minimum a₊ = 243(35) a₀; ratio 0.92(14)",
        "Bar-Ilan (Khaykovich). Li-7 in a single spin state: three-body recombination resonance at a₋ = −264(11) a₀ and "
        "recombination minimum at a₊ = 243(35) a₀ (the paper's term; not an atom–dimer resonance); ratio a₊/|a₋| = 0.92(14), "
        "consistent with the zero-range prediction 0.96(3) "
        "(where Cs gave 1.25(9)).",
        "Gross, N., Shotan, Z., Kokkelmans, S., Khaykovich, L., Phys. Rev. Lett. 103, 163202 (2009). doi:10.1103/PhysRevLett.103.163202",
        mv=0.92,
        merr=0.14,
        pv=0.96,
        unit="a₊/|a₋| (dimensionless)",
    ),
    ref(
        "REF-efimov-pollack-2009",
        "Pollack, Dries, Hulet (2009): two consecutive Efimov trimer pairs in Li-7; ratios 22.5(22)(11) and 21.1(11)(24) vs 22.7",
        "Rice (Hulet). Li-7 across a broad Feshbach resonance: three-body loss features on both sides, giving two "
        "consecutive trimer features whose scattering-length ratios are 22.5(22)(11) and 21.1(11)(24) (statistical)(systematic), "
        "against the universal 22.7; also four-body (tetramer) features tied to the trimers. The first measurement of the "
        "Efimov scaling factor itself.",
        "Pollack, S. E., Dries, D., Hulet, R. G., Science 326, 1683–1685 (2009). doi:10.1126/science.1182840",
        mv=22.5,
        merr=2.2,
        pv=22.694,
        unit="ratio of consecutive Efimov feature positions a_{n+1}/a_n (dimensionless)",
        notes=(
            "Two independent ratios: 22.5(22)(11) and 21.1(11)(24) (statistical)(systematic); measured_error is the "
            "statistical error of the first. Caveat: the same group reanalysed exactly these positions with finite-range "
            "corrections — Dyke, Pollack & Hulet, Phys. Rev. A 88, 023625 (2013) — recorded here as a caveat only (not "
            "re-read in the sweep). " + UNIV
        ),
    ),
    ref(
        "REF-efimov-huang-2014",
        "Huang, Sidorenkov, Grimm, Hutson (2014): second triatomic Efimov resonance in Cs-133; scaling factor 21.0(1.3) vs 22.7",
        "Innsbruck. Cs-133 at large scattering length: observation of the second (excited) triatomic recombination "
        "resonance and its ratio to the first, λ = 21.0(1.3), against the universal e^{π/s₀} = 22.694: the 1σ width is "
        "6.2 % of the value and the central offset is 7.5 % below the universal number — a test of discrete scale "
        "invariance in a homonuclear system. QBP relevance (#669): the cleanest three-body number in physics; the "
        "observable any hosted composite-system rule must reproduce (FLAG-hosted-composite-rule-open). No QBP "
        "prediction is recorded here.",
        "Huang, B., Sidorenkov, L. A., Grimm, R., Hutson, J. M., Phys. Rev. Lett. 112, 190401 (2014). doi:10.1103/PhysRevLett.112.190401",
        mv=21.0,
        merr=1.3,
        pv=22.694,
        unit="Efimov scaling factor λ = a₋⁽¹⁾/a₋⁽⁰⁾ (dimensionless)",
        notes=UNIV,
    ),
    ref(
        "REF-efimov-li6-three-component-2009",
        "Huckans et al.; Williams et al. (2009): Efimov trimers in three-component Li-6 (distinguishable fermions)",
        "Penn State (O'Hara) and Heidelberg (Jochim). A three-component Fermi gas of Li-6 (three lowest hyperfine states) "
        "shows three-body loss resonances from Efimov trimers: ground trimers near 130 G and 500 G, an excited trimer near "
        "895 G; all three pairwise scattering lengths approach a_t → −2140 a₀ at high field. Efimov physics with three distinguishable "
        "fermions rather than identical bosons.",
        "Ottenstein, T. B., Lompe, T., Kohnen, M., Wenz, A. N., Jochim, S., Phys. Rev. Lett. 101, 203202 (2008). "
        "doi:10.1103/PhysRevLett.101.203202 (the 130 G loss feature); Huckans, J. H., Williams, J. R., Hazlett, E. L., "
        "Stites, R. W., O'Hara, K. M., Phys. Rev. Lett. 102, 165302 (2009). doi:10.1103/PhysRevLett.102.165302 (a_t → "
        "−2140 a₀; loss vs field); Williams, J. R. et al., Phys. Rev. Lett. 103, 130404 (2009). "
        "doi:10.1103/PhysRevLett.103.130404 (excited trimer near 895 G; 130 G and 500 G identified as ground trimers)",
        notes=(
            "Qualitative record by design: the abstracts give loss-feature positions in gauss and a_t → −2140 a₀, with no "
            "universal-ratio comparison, so no measured/predicted pair is encoded. The 130 G feature was first reported by "
            "Ottenstein 2008 (whose abstract does not name Efimov) and identified as a ground-state Efimov trimer by "
            "Williams 2009."
        ),
    ),
    ref(
        "REF-efimov-ulmanis-2016",
        "Ulmanis et al. (2016): consecutive heteronuclear Cs–Cs–Li Efimov resonances; scaling 4.0(3) vs universal 4.9",
        "Heidelberg (Weidemüller). Li-6/Cs-133 mixture (heavy-heavy-light): consecutive Cs–Cs–Li Efimov resonances with "
        "measured scaling 4.0(3) against the mass-ratio-universal e^{π/s₀} ≈ 4.9 for this system — the scaling factor "
        "depends on masses and statistics, not on the species' potentials. The paper attributes the deviation from 4.9 to "
        "the Cs–Cs intraspecies scattering length (the three-body parameter's dependence on it).",
        "Ulmanis, J., Häfner, S., Pires, R., Kuhnle, E. D., Wang, Y., Greene, C. H., Weidemüller, M., Phys. Rev. Lett. 117, "
        "153201 (2016). doi:10.1103/PhysRevLett.117.153201",
        mv=4.0,
        merr=0.3,
        pv=4.9,
        unit="heteronuclear Efimov scaling factor (dimensionless)",
    ),
    ref(
        "REF-moretti-oppio-2019",
        "Moretti & Oppio (2019): a quaternionic Hilbert-space quantum theory with Poincaré symmetry reduces to standard complex QM",
        "For a quaternionic Hilbert space carrying a locally faithful, irreducible, strongly continuous unitary representation of "
        "the Poincaré group with non-negative squared-mass operator, there is a unique (up to sign) Poincaré-invariant complex "
        "structure commuting with the observables; the theory is physically equivalent to a complex Hilbert-space theory in "
        "which all self-adjoint operators are observables, Noether's theorem holds, and composite systems are given by tensor "
        "products. QBP relevance (#669; theory doc docs/theory/quaternionic_si_definitions.md §8.2): if the hosted quantum layer "
        "is such a theory, its three-body (Efimov) physics is standard by theorem — fidelity, not discrimination. Caveat: the "
        "premise is Poincaré symmetry; cold-atom Efimov physics is Galilean, so the application assumes the non-relativistic "
        "effective theory inherits the reduction from the fundamental layer.",
        "Moretti, V., Oppio, M., Rev. Math. Phys. 31, 1950013 (2019); arXiv:1709.09246. (The theory doc's reference [7] "
        "gives this title under the 2017 coordinates RMP 29(4) 1750021 / arXiv:1611.09029, which belong to the authors' "
        "real-Hilbert-space paper — a mis-citation, tracked as #671.)",
        kind="theory-external",
    ),
    {
        "id": "FLAG-hosted-composite-rule-open",
        "name": "The hosted quantum layer has no composite-system (multi-particle) rule on record — Efimov data force one",
        "tier": 2,
        "provenance": "T",
        "provenance_kind": "theory",
        "status": "marginal",
        "description": (
            "QBP's hosted quantum mechanics is developed for single-particle interference (the double-slit model, "
            "DERIV-doubleslit-visibility-model, Model A — choice open per #387); docs/theory/quaternionic_si_definitions.md "
            "§8.2 records quaternionic tensor products as non-trivial (Moretti–Oppio) and §8.4 says multi-particle "
            "entanglement is future work. No rule for composing two- or three-particle states exists on record. Efimov "
            "trimers are the sharpest composite-system observable: an infinite ladder scaling by e^{π/s₀} = 22.694 "
            "(measured 21.0(1.3), REF-efimov-huang-2014). Any candidate composite rule that fails to reproduce the ladder is "
            "killed. Under the Moretti–Oppio premises (REF-moretti-oppio-2019) the answer is standard QM; whether the hosted "
            "layer satisfies those premises is itself unrecorded. No QBP prediction is recorded: "
            "PROOF-associative-composition-iff concerns composing left-multiplication operators in the algebra, not the "
            "composition of multi-particle states, and no prediction follows from a rule that does not exist. "
            "See " + NOTE + " §3–§6."
        ),
        "prediction_chain": ["DERIV-doubleslit-visibility-model"],
        "testable_when": (
            "When a composite-system rule for the hosted layer is written: it must reproduce s₀ = 1.00624 (λ = 22.694) for "
            "identical bosons and the mass-ratio-dependent factors (≈ 4.9 for Cs–Cs–Li) within the measured errors."
        ),
        "notes": (
            "Tracking anchor only (route OPEN; no root, no claim). It closes when the gap closes: a composite-system rule on "
            "record for the hosted layer, tested against the verified Efimov table (a rule that fails the table is dead, "
            "the gap stays open); or a record that the hosted layer meets the Moretti–Oppio premises (then the rule is the "
            "standard tensor product, by theorem). Same gap as link 4 of the matter-conservation question (#635 records)."
        ),
        "foundation_batch": "#669-efimov",
        "last_tested_at": DATE,
    },
]

CHANGELOG = {
    "version": "6.5.0",
    "date": DATE,
    "note": (
        "qbp-oppenheimer: Efimov side project (#669, beekeeper 2026-09-21) — six REF anchors for the VERIFIED Efimov-state "
        "experiments (Kraemer 2006; Gross 2009; Pollack/Dries/Hulet 2009; Huang 2014 λ = 21.0(1.3) vs 22.694; Li-6 "
        "three-component 2009; Ulmanis 2016 heteronuclear 4.0(3) vs 4.9), REF-moretti-oppio-2019 (quaternionic Hilbert + "
        "Poincaré ⇒ complex QM), and FLAG-hosted-composite-rule-open (the hosted layer has no multi-particle composition rule; "
        "Efimov data force one; no QBP prediction recorded). Tier 2: documentation of external results; "
        "no theory claim, no root, no kill on any root. Partial/unverified sweep entries NOT encoded. (Renumbered 6.5.0 at "
        "rebase after #665 → 6.2.0, #666 → 6.3.0 and #667 → 6.4.0 landed.)"
    ),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        have = {a["id"] for a in L["anchors"]}
        for a in ANCHORS:
            if a["id"] in have:
                raise SystemExit(f"already applied: {a['id']}")
            ed.append("anchors", a)
        L["version"] = CHANGELOG["version"]
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")
    print(f"{'DRY ' if args.dry_run else ''}applied: {len(ANCHORS)} anchors")


if __name__ == "__main__":
    main()
