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

C3-FULL (full-ledger EVIDENCE BAR — beekeeper-directed: "if you're claiming it's proven,
you have to have the evidence that it's proven to submit it"):
  C3 above only checks the manifest-DECLARED anchors. C3-FULL generalises it to the WHOLE
  ledger AND raises the bar from file-existence to proof-EVIDENCE. EVERY
  `provenance_kind:proof` anchor must CARRY its proof:
    - proof_state == "verified";
    - a `verification` block whose `axiom_closure` is clean FOR ITS LANGUAGE
      (Lean: closure ⊆ {propext, Classical.choice, Quot.sound} — native_decide/sorryAx are
       NOT clean; Agda: closure attests `--safe`);
    - sorry_count == 0;
    - a `proof_file` that RESOLVES on this head AND is sorry-free (comment-stripped scan for
      the language's hole tokens: Lean sorry/admit/sorryAx/native_decide; Agda postulate/holes;
      Coq Admitted/admit).
  Miss any → the anchor does not carry its proof and the gate HARD-FAILS. The first run found
  only 10 of 31 proof anchors carry strong evidence; 21 do not (17 phantom-file + 4 written/
  no-verification).

  G1 (FAULT-S4-007, cth schema ruling seq=1041): the SAME clean bar applies to a `derivation`
  anchor that SHOWS verification (carries any of proof_file/verification/proof_state/theorems) —
  a derivation shows either CLEAN Lean or none, so a dirty proof can't be laundered as a
  derivation to dodge the bar. `proof` is REQUIRED to carry evidence; a `derivation` is not, but
  if it shows a footing that footing must be clean. (G2: a `derivation` never flips inter#57 to
  PROVEN — that needs `proof` AND `coherent`. G3: derivations are not manifest deliverables; the
  C1/C2 manifest candidate set stays proof-only.) The known-legacy set lives in a SHRINK-ONLY, issue-linked register
  (docs/cth/proof-anchor-remediation.json). C3-FULL HARD-FAILS if:
    (a) a proof anchor FAILS the evidence bar and is NOT in the register — a NEW over-claim; or
    (b) a register entry now MEETS the bar (or the anchor is gone / no longer a proof) — the
        entry is stale and must be removed (the register can only SHRINK as debt burns down); or
    (c) a register entry has no tracking issue.
  Adding a register entry is a visible, reviewed commit — NOT a silent CI baseline-raise
  (that silent raise is exactly what defeated the FAULT-S4-005 ratchet). NOTE: the JSON+source
  check is a strong NECESSARY gate but a hand-authored verification block is still data; the
  AIRTIGHT layer (re-run #print axioms / agda --safe in CI and diff against the claim) rides on
  the existing Lean/Agda foundations CI — tracked as the authoritative follow-on.

Usage: check_anchor_manifest.py [--manifest F] [--ledger F] [--root DIR]
                                [--register F] [--skip-witnesses] [--skip-full-ledger]
Exit 0 = clean; 1 = C1/C2 (declared-but-unanchored), C3 (declared witness unresolved),
or C3-FULL (a proof anchor's proof_file 404s off-register, or a stale register entry).
"""

import argparse
import json
import os
import re
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


# Lean kernel axiom-clean set; a proof whose #print axioms closure is a subset is clean.
_CLEAN_LEAN = {"propext", "Classical.choice", "Quot.sound"}
# Per-language "not actually proven" source tokens (hard) — scanned comment-stripped.
_HARD_TOKENS = {
    "lean": [r"\bsorry\b", r"\badmit\b", r"\bsorryAx\b", r"\bnative_decide\b"],
    "agda": [r"\bpostulate\b", r"\{!"],
    "coq": [r"\bAdmitted\b", r"\badmit\b"],
}


def _lang_of(pf, proof_system):
    ps = (proof_system or "").lower()
    if pf and pf.endswith(".agda") or "agda" in ps:
        return "agda"
    if pf and pf.endswith(".v") or "coq" in ps:
        return "coq"
    return "lean"  # default; .lean and lean4


def _strip_comments(src, lang):
    if lang in ("lean", "agda"):
        opn, cls = (r"/-", r"-/") if lang == "lean" else (r"\{-", r"-\}")
        src = re.sub(opn + r".*?" + cls, " ", src, flags=re.S)
        src = re.sub(r"--[^\n]*", " ", src)
    elif lang == "coq":
        src = re.sub(r"\(\*.*?\*\)", " ", src, flags=re.S)
    return src


def _source_holes(anchor, root):
    """Return a list of real (comment-stripped) 'not-proven' tokens in the proof_file,
    or None if the file does not resolve. [] means the source is hole-free."""
    pf = anchor.get("proof_file")
    if not pf:
        return None
    path = os.path.join(root, pf)
    if not os.path.exists(path):
        return None
    lang = _lang_of(pf, anchor.get("proof_system"))
    with open(path, encoding="utf-8", errors="replace") as f:
        s = _strip_comments(f.read(), lang)
    return sorted(
        {m.group(0) for p in _HARD_TOKENS.get(lang, []) for m in re.finditer(p, s)}
    )


def _axiom_closure_clean(anchor):
    """(clean: bool, reason: str) — is the recorded verification axiom_closure clean for
    the anchor's language? Lean: subset of the kernel-clean set. Agda: attests --safe.
    """
    v = anchor.get("verification") or {}
    ac = v.get("axiom_closure")
    if ac is None:
        return False, "verification has no axiom_closure"
    items = ac if isinstance(ac, list) else [ac]
    lang = _lang_of(anchor.get("proof_file"), anchor.get("proof_system"))
    if lang == "agda":
        ok = any("--safe" in str(x) for x in items)
        return ok, ("--safe attested" if ok else "agda closure does not attest --safe")
    # lean / coq: every element must be in the kernel-clean set
    extra = [x for x in items if x not in _CLEAN_LEAN]
    return (not extra), ("axiom-clean" if not extra else f"non-clean axioms: {extra}")


def _evidence_reasons(anchor, root):
    """The evidence bar for a provenance_kind:proof anchor. Returns [] if the anchor
    CARRIES its proof (verified + clean axiom audit + sorry-free resolving source), else a
    list of the ways it falls short. This is the 'you must submit the evidence' contract.
    """
    reasons = []
    holes = _source_holes(anchor, root)
    if holes is None:
        reasons.append(
            f"proof_file does not resolve: {anchor.get('proof_file') or '(none)'}"
        )
    elif holes:
        reasons.append(f"source is not discharged (found {holes})")
    if anchor.get("proof_state") != "verified":
        reasons.append(f"proof_state is {anchor.get('proof_state')!r}, not 'verified'")
    if not anchor.get("verification"):
        reasons.append("no verification block")
    else:
        clean, why = _axiom_closure_clean(anchor)
        if not clean:
            reasons.append(why)
    if anchor.get("sorry_count") not in (0,):
        reasons.append(f"sorry_count is {anchor.get('sorry_count')!r}, not 0")
    return reasons


# Verification/proof fields the schema (post-S4-007 relaxed C1) allows on {proof, derivation}.
_PROOF_FIELDS = ("proof_file", "verification", "proof_state", "theorems")


def _shows_verification(anchor):
    """True if the anchor carries any verification/proof field — i.e. it CLAIMS a
    machine-checked footing. A bare anchor (none of these) shows no proof."""
    return any(anchor.get(f) for f in _PROOF_FIELDS)


def _requires_evidence(anchor):
    """Which anchors the clean-evidence bar applies to (FAULT-S4-007 G1):
      - `proof`      — MUST carry the evidence (the verified thing IS the claim);
      - `derivation` — only IF it SHOWS verification (a derivation shows either clean Lean
                       or none — a shown footing must meet the same clean bar as a proof).
    A bare derivation / theory / experiment / etc. is exempt (no proof shown)."""
    pk = anchor.get("provenance_kind")
    return pk == "proof" or (pk == "derivation" and _shows_verification(anchor))


def _evidence_reasons_for_kind(anchor, root):
    """[] if the anchor is honest for its kind, else the ways it falls short. `proof` and
    `derivation`-showing-verification get the full clean bar; everything else is exempt.
    """
    return _evidence_reasons(anchor, root) if _requires_evidence(anchor) else []


def check_full_ledger_proofs(ledger_by_id, register, root="."):
    """C3-FULL (evidence bar): every anchor to which the bar applies — a `proof` (required),
    or a `derivation` that SHOWS verification (G1) — must CARRY clean evidence (verified +
    axiom-clean audit + sorry-free resolving source), unless it is a known-legacy entry in the
    shrink-only register. Returns (new_over_claims, stale_register, register_no_issue):
      new_over_claims   — a bar-applicable anchor that fails and is NOT registered (fail)
      stale_register    — registered anchor now HONEST for its kind (clean proof / clean
                          derivation / reclassified) or gone: resolved, remove entry (shrink-only)
      register_no_issue — register entries lacking a tracking issue (fail)
    """
    reg_ids = {e["anchor_id"] for e in register}

    new_over_claims = []
    for aid, a in ledger_by_id.items():
        if not _requires_evidence(a):
            continue
        if aid in reg_ids:
            continue
        reasons = _evidence_reasons(a, root)
        if reasons:
            new_over_claims.append((aid, "; ".join(reasons)))

    stale_register = []
    for e in register:
        aid = e["anchor_id"]
        a = ledger_by_id.get(aid)
        if a is None:
            stale_register.append((aid, "anchor no longer in ledger — remove entry"))
        elif not _evidence_reasons_for_kind(a, root):
            stale_register.append(
                (
                    aid,
                    "anchor now honest for its kind (clean proof / clean derivation / "
                    "reclassified) — resolved, remove entry",
                )
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

    # C3-FULL: every provenance_kind:proof anchor must CARRY its proof evidence (verified +
    # axiom-clean audit + sorry-free resolving source), else be a tracked, shrink-only legacy.
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
        n_deriv = sum(
            1
            for a in ledger_by_id.values()
            if a.get("provenance_kind") == "derivation" and _shows_verification(a)
        )
        print(
            f"C3-FULL (evidence bar): {n_proof} proof + {n_deriv} verification-showing "
            f"derivation anchor(s) under the clean bar (G1); "
            f"{len(register)} on the remediation register."
        )
        fail = False
        if new_over:
            fail = True
            print(
                "::error::C3-FULL — proof anchor(s) do NOT carry their proof evidence and are "
                "NOT on the remediation register. A provenance_kind:proof anchor MUST ship the "
                "evidence: proof_state:verified + a verification block with a language-clean "
                "axiom_closure + sorry_count:0 + a resolving, sorry-free proof_file. Supply the "
                "evidence, reclassify the anchor, or (legacy only) add it to "
                "docs/cth/proof-anchor-remediation.json with a tracking issue:"
            )
            for aid, why in new_over:
                print(f"  - {aid}: {why}")
        if stale_reg:
            fail = True
            print(
                "::error::C3-FULL — remediation register is SHRINK-ONLY, but entr(ies) now MEET "
                "the evidence bar (or the anchor is gone / no longer a proof). Remove the "
                "resolved entr(ies) from docs/cth/proof-anchor-remediation.json:"
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
            "PASS (C3-FULL): every proof anchor carries its evidence or is a tracked, "
            "shrink-only register entry."
        )

    print(
        "PASS: every declared anchor-worthy deliverable is anchored (C1/C2)"
        + ("" if args.skip_witnesses else ", its witnesses resolve (C3)")
        + (
            ""
            if args.skip_full_ledger
            else ", every proof anchor carries its evidence (C3-FULL)"
        )
        + "."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
