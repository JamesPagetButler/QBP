#!/usr/bin/env python3
"""C1/C2/C3 manifest-enforcement gate — FAULT-S4-005 Step 3.

The root cause of FAULT-S4-005: the inverse-anchor-audit ratchet counted EVERY
`grep theorem` (640, mostly auxiliary lemmas) as an anchor candidate, so anchoring
all of them was impossible and the only viable response was silently raising the
baseline — which turned the ratchet into a logbook, not a gate.

The fix — ONE manifest (docs/cth/anchor-worthy-manifest.json), three clauses:
  C1  candidate set = the DECLARED anchor-worthy deliverables (top-level, non-private,
      named in an issue-AC / #474-row) — NOT `grep theorem`. (640 -> ~dozen.)
  C2  a declared deliverable whose anchor_id is ABSENT from the CTH ledger is a
      HARD FAIL. It cannot be baselined away — no raisable soft-escape.
  C3  a declared anchor's WITNESSES must RESOLVE in source on the PR head (the ledger
      anchor's proof_file exists AND each witness theorem name appears in it). Catches
      the #613/#615 class: a `provenance_kind:proof` anchor whose witnesses/proof_file
      don't resolve. HARD FAIL on real drift, no escape.
      (Clauses a/b of qbp-cu #66's run-pattern. Clause (c) infra-soft-pass is
      fetch-conditional — N/A here, C3 is intra-QBP, no cross-repo fetch; per
      qbp-cu-implementor seq=1021. #68 persistent-infra escalation inherited later.)

C3-FULL (full-ledger, "extend C3 to full-ledger audit" — beekeeper-directed):
  C3 above only checks the manifest-DECLARED anchors. C3-FULL generalises it to the
  WHOLE ledger: EVERY `provenance_kind:proof` anchor's `proof_file` must resolve on
  this head. A proof anchor pointing at a file that does not exist is an over-claim
  (the #613/#615 class). The first run found 21 of 31 proof anchors citing a 404.
  The known-legacy set lives in a SHRINK-ONLY, issue-linked register
  (docs/cth/proof-anchor-remediation.json). C3-FULL HARD-FAILS if:
    (a) a proof anchor's proof_file 404s and is NOT in the register — a NEW over-claim; or
    (b) a register entry's proof_file now RESOLVES (or the anchor is gone / no longer a
        proof) — the entry is stale and must be removed (the register can only shrink); or
    (c) a register entry has no tracking issue.
  Adding a register entry is a visible, reviewed commit — NOT a silent CI baseline-raise
  (that silent raise is exactly what defeated the FAULT-S4-005 ratchet).

Usage: check_anchor_manifest.py [--manifest F] [--ledger F] [--root DIR]
                                [--register F] [--skip-witnesses] [--skip-full-ledger]
Exit 0 = clean; 1 = C1/C2 (declared-but-unanchored), C3 (declared witness unresolved),
or C3-FULL (a proof anchor's proof_file 404s off-register, or a stale register entry).
"""

import argparse
import json
import os
import sys

DEFAULT_MANIFEST = "docs/cth/anchor-worthy-manifest.json"
DEFAULT_LEDGER = "archive/cth-inventory/confluent-trust-inventory-v5_3.v0.3.json"
DEFAULT_REGISTER = "docs/cth/proof-anchor-remediation.json"


def load_ledger(path):
    with open(path, encoding="utf-8") as f:
        return {a["id"]: a for a in json.load(f).get("anchors", [])}


def _short(qualified):
    # last dotted component: "QBP.Foundations.CPPhase.cos_sq_delta_CP" -> "cos_sq_delta_CP";
    # "S3FromCD.S³-HSpace" -> "S³-HSpace".
    return qualified.rsplit(".", 1)[-1]


def check_witnesses_resolve(entries, ledger_by_id, root="."):
    """C3: each declared anchor's witnesses must resolve in source. Returns a list of
    (anchor_id, reason) for anything that does not resolve (real drift → caller hard-fails).
    """
    unresolved = []
    for e in entries:
        anchor = ledger_by_id.get(e["anchor_id"])
        if anchor is None:
            continue  # C1/C2 already reported this as an orphan
        pf = anchor.get("proof_file")
        if not pf:
            unresolved.append((e["anchor_id"], "ledger anchor has no proof_file"))
            continue
        path = os.path.join(root, pf)
        if not os.path.exists(path):
            unresolved.append((e["anchor_id"], f"proof_file does not exist: {pf}"))
            continue
        with open(path, encoding="utf-8") as f:
            src = f.read()
        for w in e.get("witnesses", []):
            if _short(w) not in src:
                unresolved.append((e["anchor_id"], f"witness not found in {pf}: {w}"))
    return unresolved


def _proof_file_resolves(anchor, root):
    """True iff the anchor's proof_file exists on this head."""
    pf = anchor.get("proof_file")
    return bool(pf) and os.path.exists(os.path.join(root, pf))


def check_full_ledger_proofs(ledger_by_id, register, root="."):
    """C3-FULL: every provenance_kind:proof anchor's proof_file must resolve on this
    head, unless the anchor is a known-legacy entry in the shrink-only register.
    Returns (new_over_claims, stale_register, register_no_issue):
      new_over_claims   — proof anchor with a 404 proof_file that is NOT registered (fail)
      stale_register    — registered anchor whose proof_file now resolves, or which is no
                          longer a provenance_kind:proof anchor: the entry must be removed
      register_no_issue — register entries lacking a tracking issue (fail)
    """
    reg_ids = {e["anchor_id"] for e in register}

    new_over_claims = []
    for aid, a in ledger_by_id.items():
        if a.get("provenance_kind") != "proof":
            continue
        if _proof_file_resolves(a, root):
            continue
        if aid not in reg_ids:
            new_over_claims.append((aid, a.get("proof_file") or "(no proof_file)"))

    stale_register = []
    for e in register:
        aid = e["anchor_id"]
        a = ledger_by_id.get(aid)
        if a is None:
            stale_register.append((aid, "anchor no longer in ledger — remove entry"))
        elif a.get("provenance_kind") != "proof":
            stale_register.append(
                (
                    aid,
                    "anchor is no longer provenance_kind:proof — resolved, remove entry",
                )
            )
        elif _proof_file_resolves(a, root):
            stale_register.append(
                (aid, "proof_file now resolves — resolved, remove entry")
            )

    register_no_issue = [
        e["anchor_id"] for e in register if not str(e.get("issue", "")).strip()
    ]
    return new_over_claims, stale_register, register_no_issue


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", default=DEFAULT_MANIFEST)
    ap.add_argument("--ledger", default=DEFAULT_LEDGER)
    ap.add_argument("--register", default=DEFAULT_REGISTER)
    ap.add_argument(
        "--root", default=".", help="repo root for resolving proof_file paths"
    )
    ap.add_argument(
        "--skip-witnesses",
        action="store_true",
        help="skip C3 (witnesses-resolve) — e.g. when source is not checked out",
    )
    ap.add_argument(
        "--skip-full-ledger",
        action="store_true",
        help="skip C3-FULL (every proof anchor's proof_file resolves) — source not checked out",
    )
    args = ap.parse_args()

    with open(args.manifest, encoding="utf-8") as f:
        entries = json.load(f).get("entries", [])
    ledger_by_id = load_ledger(args.ledger)

    print(
        f"Anchor-worthiness manifest: {len(entries)} declared deliverable(s); "
        f"ledger carries {len(ledger_by_id)} anchors."
    )

    # C1/C2: declared deliverable absent from the ledger = hard fail (no baselining).
    orphans = [e for e in entries if e["anchor_id"] not in ledger_by_id]
    if orphans:
        print(
            "::error::C1/C2 — declared anchor-worthy deliverable(s) are NOT anchored in the "
            "CTH ledger. A declared deliverable MUST ship its anchor (it cannot be baselined "
            "away — FAULT-S4-005). Add the anchor, or remove the manifest entry if declared in "
            "error:"
        )
        for e in orphans:
            print(
                f"  - {e['anchor_id']} (declared_by {e.get('declared_by','?')}, "
                f"{e.get('proof_system','?')})"
            )
        return 1

    # C3: each declared anchor's witnesses must resolve in source (real drift = hard fail).
    if not args.skip_witnesses:
        unresolved = check_witnesses_resolve(entries, ledger_by_id, args.root)
        if unresolved:
            print(
                "::error::C3 — declared anchor witness(es) do not resolve in source (the "
                "proof_file or a witness theorem is missing on this head — a proof anchor "
                "whose witnesses don't exist, #613/#615 class):"
            )
            for aid, reason in unresolved:
                print(f"  - {aid}: {reason}")
            return 1
        print("PASS (C3): every declared anchor's witnesses resolve in source.")

    # C3-FULL: every provenance_kind:proof anchor's proof_file must resolve (whole ledger).
    if not args.skip_full_ledger:
        register = []
        if os.path.exists(args.register):
            with open(args.register, encoding="utf-8") as f:
                register = json.load(f).get("entries", [])
        new_over, stale_reg, no_issue = check_full_ledger_proofs(
            ledger_by_id, register, args.root
        )
        n_proof = sum(
            1 for a in ledger_by_id.values() if a.get("provenance_kind") == "proof"
        )
        print(
            f"C3-FULL: {n_proof} provenance_kind:proof anchor(s); "
            f"{len(register)} on the remediation register."
        )
        fail = False
        if new_over:
            fail = True
            print(
                "::error::C3-FULL — proof anchor(s) cite a proof_file that does NOT resolve "
                "on this head and are NOT on the remediation register (a NEW over-claim — a "
                "provenance_kind:proof anchor with a phantom proof_file, #613/#615 class). "
                "Write+verify the proof, reclassify the anchor, or (legacy only) add it to "
                "docs/cth/proof-anchor-remediation.json with a tracking issue:"
            )
            for aid, pf in new_over:
                print(f"  - {aid}: proof_file 404 -> {pf}")
        if stale_reg:
            fail = True
            print(
                "::error::C3-FULL — remediation register is SHRINK-ONLY, but entr(ies) are "
                "now resolved (proof_file resolves, or the anchor is gone / no longer a proof). "
                "Remove the stale entr(ies) from docs/cth/proof-anchor-remediation.json:"
            )
            for aid, why in stale_reg:
                print(f"  - {aid}: {why}")
        if no_issue:
            fail = True
            print(
                "::error::C3-FULL — every remediation-register entry MUST carry a tracking "
                "issue (a register add is a visible, tracked act, not a silent baseline-raise):"
            )
            for aid in no_issue:
                print(f"  - {aid}: missing 'issue'")
        if fail:
            return 1
        print(
            "PASS (C3-FULL): every proof anchor resolves or is a tracked, shrink-only "
            "register entry."
        )

    print(
        "PASS: every declared anchor-worthy deliverable is anchored (C1/C2)"
        + ("" if args.skip_witnesses else ", its witnesses resolve (C3)")
        + ("" if args.skip_full_ledger else ", every proof anchor resolves (C3-FULL)")
        + "."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
