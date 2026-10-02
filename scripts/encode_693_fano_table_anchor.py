#!/usr/bin/env python3
"""Issue #693 — mint the companion Fano-table anchor the silicon pins (ruling (b) on QBP#692).

qbp-compute-unit's required gate `gcg-fano-proof-tie.yml` pins the TABLE: it checks out QBP,
requires `proofs/QBP/Foundations/fanoTableF4.snapshot` + `fanoTableF4.axioms.txt` (fail-closed)
and diffs the ROMs / emulator fanoLUT against the 64 rows exported from the kernel-proven
`QBP.Foundations.FanoOrientationF3.fanoTableF4`, whose provenance theorem is

    fanoTableF4_eq_cayleyDickson : ∀ i j : Fin 8, Omul (e i) (e j) = signedBasis (fanoTableF4 i j)

(FanoOrientationF3.lean:150, kernel `decide`, `#print axioms` = [propext]).  The ledger anchor the
ROM maps to today, `PROOF-cd-structure-constant-tables`, is headlined by
`CDAlg.mulCoeff_three_eq_fano` (mulCoeff ↔ table) — which the consumer never pins and the Coq
cross-prover never sees.  qbp-architecture ruled (live-test seq 2315/2316/2323, 2026-10-02):
(b) is structural — an anchor must name what the consumer actually pins, so the companion gets its
own anchor and the ROM maps to it (qbp-compute-unit#77); the existing anchor grades honestly on its
own evidence until (a), the mulCoeff n=3 Coq port, lands.

This encoder does exactly three things, all through the confined writer (scripts/cth_ledger_edit.py):

  1. MINTS `PROOF-fano-table-equals-cd-products` (Foundations, layer_tag T): proof_file
     FanoOrientationF3.lean, headline fanoTableF4_eq_cayleyDickson, companions = the declarations the
     statement names (fanoTableF4, Omul, e, signedBasis), verification block from the bounded build.
  2. CHAIN DIRECTION — none, read from the two statements.  #693 drafted
     `prediction_chain → [PROOF-cd-structure-constant-tables]` on the NEW anchor.  Evidence:
     CDAlg.lean:33 imports FanoOrientationF3; CDAlg.lean:145-148 `mulCoeff_three_eq_fano` states
     `mulCoeff 3 i j = (QBP.Foundations.FanoOrientationF3.fanoTableF4 i j).1` — it names the DEFINITION
     `fanoTableF4`, not the theorem — and its proof is `by decide` (l.148); FanoOrientationF3.lean:150-152
     `fanoTableF4_eq_cayleyDickson` is `by decide` too, and the file has no imports.  Neither proof uses
     the other theorem: two independent kernel `decide`s over the same table definition.  A
     `prediction_chain` entry is a derivation edge in this ledger (#690; the #692 PA engine folds every
     entry as `derivation`, which can only LOWER the source's effective PA), and no genuine derivation
     edge exists in either direction — so the new anchor's chain is EMPTY, the existing anchor is NOT
     edited, and the relation (shared table definition; one kernel today; separately pinned) is recorded
     in the new anchor's description only.  A typed relevance edge arrives with the Phase-1 edge typing.
  3. `version` 6.14.0 → 6.15.0, one `changelog` entry, one manifest entry
     (docs/cth/anchor-worthy-manifest.json, shape of the #689/#690 siblings).

Does NOT set pa_local / pa_effective / proof_assistants on the new anchor — that is the #692 encoder's
job (`scripts/encode_pa_from_evidence.py --pinned-master origin/master`, re-run after this).

Idempotent-guarded: refuses if the new anchor exists, if the ledger is not at 6.14.0, or if any
witness fails to resolve in the Lean source.

Usage: python3 scripts/encode_693_fano_table_anchor.py [--dry-run]
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cth_ledger_edit import ledger_edit  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
MANIFEST = ROOT / "docs/cth/anchor-worthy-manifest.json"
TOOLCHAIN = (ROOT / "proofs/lean-toolchain").read_text().strip()

DATE = "2026-10-02T00:00:00Z"
FROM_VERSION = "6.14.0"
VERSION = "6.15.0"
BATCH = "#693-fano-table-anchor"

NEW_ID = "PROOF-fano-table-equals-cd-products"
CD_ID = "PROOF-cd-structure-constant-tables"  # related, NOT chained (module doc §2); untouched

NS = "QBP.Foundations.FanoOrientationF3."
F_FANO = "proofs/QBP/Foundations/FanoOrientationF3.lean"
F_GEN = "proofs/FanoSnapshotGen.lean"
F_SNAP = "proofs/QBP/Foundations/fanoTableF4.snapshot"
F_AX = "proofs/QBP/Foundations/fanoTableF4.axioms.txt"
F_CDALG = "proofs/QBP/Foundations/CDAlg.lean"

MAIN = NS + "fanoTableF4_eq_cayleyDickson"
# The declarations the theorem's STATEMENT names, in order of appearance; all are `def`s in the
# same file (the table, the F3 doubling product on 𝕆, the basis element, the signed basis element).
COMPANIONS = [NS + "fanoTableF4", NS + "Omul", NS + "e", NS + "signedBasis"]
WITNESSES = [MAIN] + COMPANIONS

# (decl keyword, short name) — the pre-flight checks each resolves as a real declaration in F_FANO.
DECLS = [
    ("theorem", "fanoTableF4_eq_cayleyDickson"),
    ("def", "fanoTableF4"),
    ("def", "Omul"),
    ("def", "e"),
    ("def", "signedBasis"),
]

NEW_NAME = (
    "The Fano/F3 multiplication table fanoTableF4 equals the Cayley–Dickson products at level 3: "
    "for all basis indices i, j, Omul (e i) (e j) = signedBasis (fanoTableF4 i j) — kernel decide, "
    "closure [propext]. This is the table qbp-compute-unit bakes into its octonion ROMs / FANO opcode "
    "(consumer pin: gcg-fano-proof-tie.yml checks out QBP and requires fanoTableF4.snapshot + "
    "fanoTableF4.axioms.txt, fail-closed)"
)

NEW_DESC = (
    f"{F_FANO} (Foundations layer, namespace QBP.Foundations.FanoOrientationF3; the file has NO imports "
    "— core Lean only, no Mathlib, so nothing in the ledger sits upstream of it). Statement: "
    "`fanoTableF4_eq_cayleyDickson : ∀ i j : Fin 8, Omul (e i) (e j) = signedBasis (fanoTableF4 i j)`, "
    "where `fanoTableF4 : Fin 8 → Fin 8 → Int × Fin 8` is the verbatim transcription of the F4 doc "
    "table (docs/conventions/fano-orientation.md: 64 entries (sign, index); 0 = e₀, 1..7 = e₁..e₇), "
    "`Omul` is the literal F3 doubling product (a₁,a₂)(b₁,b₂) = (a₁b₁ − conj(b₂)·a₂, b₂·a₁ + "
    "a₂·conj(b₁)) applied along ℝ → ℂ → ℍ → 𝕆 on nested Int pairs (docs/conventions/cd-doubling.md; "
    "ℍ-triad e₁ = i, e₂ = j, e₃ = k), `e i` the octonion with a 1 in coordinate i, and "
    "`signedBasis (s, k)` = s·e_k. Proof shape: one kernel `decide` over the 64 basis pairs — finite "
    "data with decidable equality; no native_decide, no sorry, no vacuous `True`; `#print axioms` = "
    "[propext] (Classical.choice and Quot.sound do not occur: nothing in the file is classical). "
    "Consequence: the F4 orientation (the seven oriented triples 123, 145, 167, 246, 257, 347, 356) is "
    "FORCED by F3, not pinned from the literature. Snapshot / attestation pipeline: "
    f"{F_GEN} (`snapLines`; deliberately outside the QBP.Foundations aggregator, run via `lake env "
    "lean`) emits the 64 lines `i j sign index` from fanoTableF4 plus the `#print axioms` lines of "
    "fanoTableF4_eq_cayleyDickson and CDAlg.mulCoeff_three_eq_fano; scripts/regen_fano_snapshot.sh "
    f"writes them to {F_SNAP} and {F_AX}; .github/workflows/fano-snapshot-drift.yml rebuilds "
    "FanoOrientationF3 + CDAlg on every change to those files and hard-fails on any diff (producer-side "
    "tamper evidence, QBP #604 / qbp-cu #65). Consumer pin — the reach of this anchor: "
    "qbp-compute-unit's required check `.github/workflows/gcg-fano-proof-tie.yml` (qbp-cu issue #59) "
    "checks out JamesPagetButler/QBP, hard-fails if fanoTableF4.snapshot is absent on a successful "
    "fetch or if fanoTableF4.axioms.txt is missing, does not reference fanoTableF4_eq_cayleyDickson, "
    "or lists any axiom outside {propext, Classical.choice, Quot.sound}, then runs "
    "emulator/fano_proof_tie_test.go (TestFanoProofTie_MatchesKernelProvenTable with FANO_SNAPSHOT set): "
    "it parses exactly 64 rows and compares every entry against the octonion ROMs "
    "(roms/octonion_idx.hex, 64 indices; roms/octonion_signs.hex, 49 imaginary signs) and the emulator "
    "fanoLUT behind the FANO ISA opcode, plus the XOR-index and identity-row invariants; only a failed "
    "QBP checkout soft-passes (infra, not drift; escalating to hard fail after 3 consecutive — qbp-cu "
    "#66/#68). The chain the silicon rests on is therefore CD product (kernel decide) → fanoTableF4 → "
    "snapshot → ROMs + fanoLUT → FANO opcode, and THIS theorem is the link the consumer pins; "
    "qbp-compute-unit#77 maps its ROM↔claim entry to this id. Relation to "
    f"{CD_ID}: that anchor's headline `QBP.Foundations.CDAlg.mulCoeff_three_eq_fano` states "
    "`mulCoeff 3 i j = (fanoTableF4 i j).1` — the structure-constant recursion agrees with the SIGN "
    f"column of this same table ({F_CDALG} imports FanoOrientationF3; one Lean kernel covers both "
    "today). Chain direction, read from the two statements (direction evidence): CDAlg.lean:33 "
    "imports FanoOrientationF3; CDAlg.lean:145-148 names the DEFINITION fanoTableF4, not this theorem, "
    "and is closed `by decide` (l.148); FanoOrientationF3.lean:150-152 is closed `by decide` and the "
    "file imports nothing. Neither proof uses the other theorem — two independent kernel decides over "
    "the same table definition — so there is NO derivation edge between the two anchors in either "
    f"direction: this anchor's prediction_chain is empty and {CD_ID} is not edited (#693 drafted the "
    f"edge NEW → {CD_ID}; as a derivation edge that would have let the #692 PA engine cap this anchor "
    "at the mulCoeff anchor's grade — the outcome ruling (b) exists to prevent — and no such dependence "
    "exists). The relation is recorded here in prose only; a typed relevance edge arrives with the "
    "Phase-1 edge typing. The two anchors are separate because "
    "they are pinned separately: the consumer pins the table (this anchor), the Coq cross-prover "
    "re-proves the table, and neither sees mulCoeff. NOT claimed: anything about `mulCoeff` or the "
    "structure-constant recursion (mulCoeff_three_eq_fano, mulCoeff_four_eq_sgnTable — the headline of "
    f"{CD_ID}; its second-kernel port is follow-up (a) of the QBP#692 ruling, the notary's call on "
    "cost); the other FanoOrientationF3 theorems (cayleyDickson8_sq_neg_one, "
    "cayleyDickson8_alternative_on_basis, fanoTriples_oriented, archiveTable_disagrees_cd) stay "
    f"companions of {CD_ID} and are not re-anchored here; the Coq cross-prover record (notary cycle 8) "
    "is EVIDENCE for this claim, attached via `proof_assistants` by the QBP#692 encoder "
    "(scripts/encode_pa_from_evidence.py) once promoted into inter/notary-evidence/, never claimed by "
    "this record; the ROM contents themselves (that is qbp-compute-unit's gate, not a QBP theorem)."
)

VERIFIER = (
    "run-bounded 6G 1800 taskset -c 3-5 lake build QBP.Foundations.FanoOrientationF3 — exit 0, 2 jobs "
    "(fresh worktree .lake: one-time Mathlib cache fetch 8283 files / 422 s, then the module in 11 s; "
    "the module itself imports nothing); `#print axioms "
    "QBP.Foundations.FanoOrientationF3.fanoTableF4_eq_cayleyDickson` via `run-bounded 4G 600 lake env "
    "lean` on a scratch file = [propext] (matches the committed "
    f"{F_AX} attestation line); statement re-read fully qualified (`#check` with full names) — "
    "Omul / e / signedBasis / fanoTableF4 all resolve in QBP.Foundations.FanoOrientationF3, Omul the F3 "
    "doubling on H × H; 0 sorry, 0 native_decide, 0 vacuous `True`; gates 0 — "
    "check_lean_foundations.py exit 0, check_layer_imports.py exit 0 (qbp-oppenheimer via lean-prover sub-agent, 2026-10-02, "
    "isolated worktree probe-692-pa, branch cth/692-pa-encoder-backfill; #693, ruling (b) on QBP#692 "
    "live-test seq 2315/2316/2323; pending Tier-3 review with the #692 PR — #693 AC3)"
)


def _libs():
    """Copied from PROOF-cd-structure-constant-tables (same toolchain pin, same Mathlib rev) — the
    module imports no Mathlib, but the ledger records the project pin the build ran under.
    """
    return {
        "mathlib": {
            "ref": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
            "sha": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        }
    }


def new_anchor():
    # Field set and order of PROOF-cd-structure-constant-tables (the template), plus layer_tag after
    # tier as on the #689/#690 Foundations PROOF anchors.
    return {
        "id": NEW_ID,
        "name": NEW_NAME,
        "tier": 1,
        "layer_tag": "T",
        "provenance": "T",
        "status": "coherent",
        "description": NEW_DESC,
        "prediction_chain": [],
        "provenance_kind": "proof",
        "proof_system": "lean4",
        "proof_language": "lean4",
        "proof_file": F_FANO,
        "sorry_count": 0,
        "proof_state": "verified",
        "lean_theorem": MAIN,
        "lean_companion_theorems": COMPANIONS,
        "theorems": [{"name": "fanoTableF4_eq_cayleyDickson", "status": "verified"}],
        "foundation_batch": BATCH,
        "last_tested_at": DATE,
        "verification": {
            "toolchain": TOOLCHAIN,
            "libraries": _libs(),
            "verified_at": DATE,
            "verifier": VERIFIER,
            "result": "verified",
            "axiom_closure": ["propext"],
            "witnesses": WITNESSES,
        },
    }


CHANGELOG = {
    "version": VERSION,
    "date": DATE,
    "note": (
        f"#693: {NEW_ID} minted (Foundations) — the companion Fano table the silicon pins; "
        "no existing anchor changed. "
        "Ruling (b) on QBP#692 (qbp-architecture, live-test seq 2315/2316/2323, 2026-10-02; staleness "
        "key = claim-source manifest, issuecomment-5954304165): an anchor must name what the consumer "
        "actually pins. qbp-compute-unit's gcg-fano-proof-tie.yml pins fanoTableF4.snapshot + "
        "fanoTableF4.axioms.txt, i.e. QBP.Foundations.FanoOrientationF3.fanoTableF4_eq_cayleyDickson "
        "(∀ i j : Fin 8, Omul (e i) (e j) = signedBasis (fanoTableF4 i j); kernel decide; #print axioms "
        f"= [propext]) — not CDAlg.mulCoeff_three_eq_fano, the headline of {CD_ID}. MINTED: proof_file "
        f"{F_FANO}, companions fanoTableF4 / Omul / e / signedBasis (the declarations the statement "
        "names), verification from the bounded build of 2026-10-02, manifest entry added. CHAIN "
        f"DIRECTION: #693 drafted the edge NEW → {CD_ID}; read from the statements, CDAlg.lean:33 "
        "imports FanoOrientationF3, CDAlg.lean:145-148 names the DEFINITION fanoTableF4 (not this "
        "theorem) and is `by decide`, FanoOrientationF3.lean:150-152 is `by decide` with no imports — "
        "neither proof uses the other theorem, so no derivation edge exists in either direction (a "
        "chain entry is a derivation edge the #692 engine folds; the drafted direction would have let "
        "it cap the companion at the mulCoeff anchor's grade — the outcome ruling (b) prevents). Encoded "
        f"accordingly: {NEW_ID}.prediction_chain = [], {CD_ID} untouched; the relation (same table "
        "definition, one kernel today, separately pinned) is prose in the new anchor's description; a "
        "typed relevance edge comes with the Phase-1 edge typing. NOT "
        "claimed by the new anchor: mulCoeff / the structure-constant recursion (follow-up (a) of the "
        "QBP#692 ruling, the mulCoeff n=3 Coq port, notary's call); the Coq cross-prover record (notary "
        "cycle 8) is evidence attached by the #692 encoder when promoted, not a claim here. pa_local / "
        "pa_effective on the new anchor are NOT set by this encode — the #692 encoder "
        "(scripts/encode_pa_from_evidence.py) grades it on the next run (0/0 until the cycle-8 v2 "
        "record lands). qbp-compute-unit#77: the silicon gate's ROM↔claim map targets this id. "
        "(Version 6.15.0: encoded on 6.14.0/344 → 345.)"
    ),
}


def preflight():
    src_path = ROOT / F_FANO
    if not src_path.exists():
        raise SystemExit(f"proof_file missing on this head: {F_FANO}")
    src = src_path.read_text(encoding="utf-8")
    for kw, short in DECLS:
        if not re.search(rf"^\s*{kw} {re.escape(short)}\b", src, re.M):
            raise SystemExit(f"witness does not resolve as `{kw} {short}` in {F_FANO}")
    if "decide" not in src.split("theorem fanoTableF4_eq_cayleyDickson", 1)[1][:200]:
        raise SystemExit(
            "fanoTableF4_eq_cayleyDickson is no longer closed by `decide` — re-verify"
        )
    for f in (F_GEN, F_SNAP, F_AX):
        if not (ROOT / f).exists():
            raise SystemExit(f"snapshot pipeline file missing on this head: {f}")
    if "fanoTableF4_eq_cayleyDickson' depends on axioms: [propext]" not in (
        ROOT / F_AX
    ).read_text(encoding="utf-8"):
        raise SystemExit(
            f"{F_AX} does not attest [propext] for the headline — re-verify"
        )
    if "import QBP.Foundations.FanoOrientationF3" not in (ROOT / F_CDALG).read_text(
        encoding="utf-8"
    ):
        raise SystemExit(
            "CDAlg.lean no longer imports FanoOrientationF3 — chain direction must be re-read"
        )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    preflight()
    rec = new_anchor()

    with ledger_edit(LEDGER, dry_run=args.dry_run) as ed:
        L = ed.ledger
        if L.get("version") != FROM_VERSION:
            raise SystemExit(
                f"ledger is {L.get('version')}, expected {FROM_VERSION}: refusing"
            )
        have = {a["id"] for a in L["anchors"]}
        if NEW_ID in have:
            raise SystemExit(f"already applied: {NEW_ID} present")
        if CD_ID not in have:
            raise SystemExit(
                f"related anchor named in the description is missing from ledger: {CD_ID}"
            )
        cd = next(
            a for a in L["anchors"] if a["id"] == CD_ID
        )  # read-only: NOT declared, NOT edited
        if cd.get("lean_theorem") != "QBP.Foundations.CDAlg.mulCoeff_three_eq_fano":
            raise SystemExit(
                f"{CD_ID} is not the mulCoeff-headlined record: description would lie"
            )
        ed.append("anchors", rec)
        L["version"] = VERSION
        ed.touch("version")
        if L.get("last_updated") != DATE:
            L["last_updated"] = DATE
            ed.touch("last_updated")
        L["changelog"].append(CHANGELOG)
        ed.touch("changelog")

    m = json.loads(MANIFEST.read_text(encoding="utf-8"))
    ids = {e["anchor_id"] for e in m["entries"]}
    if NEW_ID not in ids:
        m["entries"].append(
            {
                "anchor_id": NEW_ID,
                "declared_by": BATCH,
                "proof_system": "lean4",
                "witnesses": WITNESSES,
            }
        )
    if not args.dry_run:
        MANIFEST.write_text(
            json.dumps(m, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )

    print(
        f"  minted  {NEW_ID}  main={MAIN.removeprefix(NS)}  companions={len(COMPANIONS)}  "
        f"chain={rec['prediction_chain']}  axioms={rec['verification']['axiom_closure']}"
    )
    print(
        f"  chain   [] — no derivation edge to/from {CD_ID} (independent kernel decides); untouched"
    )
    print(
        f"{'DRY ' if args.dry_run else ''}applied: 1 minted, 0 revised; ledger {FROM_VERSION} -> {VERSION}; "
        f"manifest entries {len(m['entries'])}"
    )


if __name__ == "__main__":
    main()
