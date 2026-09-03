#!/usr/bin/env python3
"""Tests for the C1/C2/C3 manifest-enforcement gate (scripts/check_anchor_manifest.py).

C1/C2: a declared anchor-worthy deliverable absent from the ledger is a HARD FAIL
(cannot be baselined away); the candidate set is the manifest, not `grep theorem`.
C3: a declared anchor whose witnesses don't resolve in source is a HARD FAIL.
C3-FULL (evidence bar): every provenance_kind:proof anchor must CARRY its proof —
proof_state:verified + language-clean axiom_closure + sorry_count:0 + a resolving,
sorry-free source — or be a tracked, shrink-only register entry (#613/#615/#617 class).
Run: python3 scripts/test_check_anchor_manifest.py
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "check_anchor_manifest.py")


def run(manifest, ledger, *, skip_witnesses=True, root=None):
    with tempfile.TemporaryDirectory() as d:
        mf = os.path.join(d, "m.json")
        open(mf, "w", encoding="utf-8").write(json.dumps(manifest, ensure_ascii=False))
        lf = os.path.join(d, "l.json")
        open(lf, "w", encoding="utf-8").write(json.dumps(ledger, ensure_ascii=False))
        cmd = [
            sys.executable,
            SCRIPT,
            "--manifest",
            mf,
            "--ledger",
            lf,
            "--root",
            root or d,
        ]
        if skip_witnesses:
            cmd.append("--skip-witnesses")
        # No register on disk in this temp dir -> register empty -> C3-FULL trivially
        # passes for the C1/C2/C3 fixtures (their anchors carry no provenance_kind:proof).
        cmd += ["--register", os.path.join(d, "no-register.json")]
        return subprocess.run(cmd, capture_output=True, text=True).returncode


def run_full_ledger(ledger, register, *, root):
    """Exercise C3-FULL: empty manifest, witnesses skipped, given ledger + register."""
    with tempfile.TemporaryDirectory() as d:
        mf = os.path.join(d, "m.json")
        open(mf, "w", encoding="utf-8").write(
            json.dumps({"manifest_version": "t", "entries": []})
        )
        lf = os.path.join(d, "l.json")
        open(lf, "w", encoding="utf-8").write(json.dumps(ledger, ensure_ascii=False))
        rf = os.path.join(d, "r.json")
        open(rf, "w", encoding="utf-8").write(
            json.dumps({"entries": register}, ensure_ascii=False)
        )
        cmd = [
            sys.executable,
            SCRIPT,
            "--manifest",
            mf,
            "--ledger",
            lf,
            "--register",
            rf,
            "--root",
            root,
            "--skip-witnesses",
        ]
        return subprocess.run(cmd, capture_output=True, text=True).returncode


def led(*items):  # items: id or (id, proof_file)
    anchors = []
    for it in items:
        if isinstance(it, tuple):
            anchors.append({"id": it[0], "proof_file": it[1]})
        else:
            anchors.append({"id": it})
    return {"anchors": anchors}


def man(*entries):  # entries: id or (id, [witnesses], proof_system)
    out = []
    for e in entries:
        if isinstance(e, tuple):
            out.append(
                {
                    "anchor_id": e[0],
                    "proof_system": e[2] if len(e) > 2 else "lean4",
                    "declared_by": "#1",
                    "witnesses": e[1],
                }
            )
        else:
            out.append(
                {
                    "anchor_id": e,
                    "proof_system": "lean4",
                    "declared_by": "#1",
                    "witnesses": [],
                }
            )
    return {"manifest_version": "test", "entries": out}


def main():
    failures = 0

    # ---- C1/C2 (witnesses skipped) ----
    c12 = [
        ("C1: all declared present → PASS", man("A", "B"), led("A", "B", "aux1"), 0),
        ("C2: declared anchor missing → HARD FAIL", man("A", "B"), led("A"), 1),
        ("empty manifest → PASS", man(), led("A"), 0),
        ("auxiliary lemma not in manifest does not fail", man("A"), led("A"), 0),
    ]
    for name, m, l, exp in c12:
        got = run(m, l, skip_witnesses=True)
        ok = got == exp
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})")
        failures += not ok

    # ---- C3 (witnesses-resolve, needs source) ----
    with tempfile.TemporaryDirectory() as root:
        os.makedirs(os.path.join(root, "proofs"), exist_ok=True)
        src = os.path.join("proofs", "X.lean")
        open(os.path.join(root, src), "w").write("theorem foo : True := trivial\n")
        c3 = [
            (
                "C3: witness resolves in source → PASS",
                man(("A", ["Mod.foo"])),
                led(("A", src)),
                0,
            ),
            (
                "C3: witness NOT in source → HARD FAIL",
                man(("A", ["Mod.bar_missing"])),
                led(("A", src)),
                1,
            ),
            (
                "C3: proof_file missing → HARD FAIL",
                man(("A", ["Mod.foo"])),
                led(("A", "proofs/nope.lean")),
                1,
            ),
        ]
        for name, m, l, exp in c3:
            got = run(m, l, skip_witnesses=False, root=root)
            ok = got == exp
            print(
                f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})"
            )
            failures += not ok

    # ---- C3-FULL (full-ledger EVIDENCE BAR + shrink-only register) ----
    with tempfile.TemporaryDirectory() as root:
        os.makedirs(os.path.join(root, "proofs"), exist_ok=True)
        clean = os.path.join("proofs", "Clean.lean")
        open(os.path.join(root, clean), "w").write("theorem t : True := trivial\n")
        withsorry = os.path.join("proofs", "Sorry.lean")
        open(os.path.join(root, withsorry), "w").write("theorem t : True := by sorry\n")
        withnd = os.path.join("proofs", "Nd.lean")
        open(os.path.join(root, withnd), "w").write(
            "theorem t : True := by native_decide\n"
        )
        commented = os.path.join("proofs", "Commented.lean")
        open(os.path.join(root, commented), "w").write(
            "-- Completeness: zero sorry, zero native_decide.\ntheorem t : True := trivial\n"
        )
        agda = os.path.join("proofs", "S.agda")
        open(os.path.join(root, agda), "w").write(
            "t : Set\nt = ?\n"
        )  # body irrelevant to closure

        LEAN_CLEAN = ["propext", "Classical.choice", "Quot.sound"]

        def anc(aid, **kw):
            d = {"id": aid, "provenance_kind": "proof"}
            d.update(kw)
            return d

        def verified(pf, closure=LEAN_CLEAN, system="lean4"):
            # a fully-evidenced proof anchor
            return dict(
                proof_file=pf,
                proof_state="verified",
                sorry_count=0,
                proof_system=system,
                verification={"result": "pass", "axiom_closure": closure},
            )

        def led2(*anchors):
            return {"anchors": list(anchors)}

        def reg(*items):  # items: (id, issue) or id
            out = []
            for it in items:
                if isinstance(it, tuple):
                    out.append({"anchor_id": it[0], "issue": it[1]})
                else:
                    out.append({"anchor_id": it, "issue": "#1"})
            return out

        cf = [
            (
                "evidence: verified+clean+sorry-free (Lean) -> PASS",
                led2(anc("A", **verified(clean))),
                reg(),
                0,
            ),
            (
                "evidence: verified+--safe (Agda) -> PASS",
                led2(
                    anc(
                        "A",
                        **verified(
                            agda,
                            closure=["--safe transitive (Agda 2.8.0)"],
                            system="agda",
                        ),
                    )
                ),
                reg(),
                0,
            ),
            (
                "evidence: comment says 'zero sorry' but proof is real -> PASS (comment-stripped)",
                led2(anc("A", **verified(commented))),
                reg(),
                0,
            ),
            (
                "non-proof anchor is ignored -> PASS",
                led2(
                    {
                        "id": "A",
                        "provenance_kind": "theory",
                        "proof_file": "proofs/nope.lean",
                    }
                ),
                reg(),
                0,
            ),
            (
                "no verification block, off-register -> HARD FAIL",
                led2(anc("A", proof_file=clean, proof_state="written")),
                reg(),
                1,
            ),
            (
                "proof_state written (not verified) -> HARD FAIL",
                led2(
                    anc(
                        "A",
                        proof_file=clean,
                        sorry_count=0,
                        verification={"result": "pass", "axiom_closure": LEAN_CLEAN},
                    )
                ),
                reg(),
                1,
            ),
            (
                "dirty axiom closure (extra axiom) -> HARD FAIL",
                led2(
                    anc(
                        "A",
                        **verified(clean, closure=LEAN_CLEAN + ["Lean.ofReduceBool"]),
                    )
                ),
                reg(),
                1,
            ),
            (
                "source contains sorry -> HARD FAIL",
                led2(anc("A", **verified(withsorry))),
                reg(),
                1,
            ),
            (
                "source contains native_decide -> HARD FAIL",
                led2(anc("A", **verified(withnd))),
                reg(),
                1,
            ),
            (
                "proof_file 404 -> HARD FAIL",
                led2(anc("A", **verified("proofs/nope.lean"))),
                reg(),
                1,
            ),
            (
                "sorry_count != 0 -> HARD FAIL",
                led2(anc("A", **{**verified(clean), "sorry_count": 2})),
                reg(),
                1,
            ),
            (
                "failing anchor but registered -> PASS",
                led2(anc("A", proof_file="proofs/nope.lean", proof_state="written")),
                reg(("A", "#615")),
                0,
            ),
            (
                "registered anchor now MEETS the bar -> HARD FAIL (stale, shrink-only)",
                led2(anc("A", **verified(clean))),
                reg(("A", "#615")),
                1,
            ),
            (
                "registered anchor reclassified to theory -> HARD FAIL (stale)",
                led2(
                    {
                        "id": "A",
                        "provenance_kind": "theory",
                        "proof_file": "proofs/nope.lean",
                    }
                ),
                reg(("A", "#615")),
                1,
            ),
            (
                "register entry missing issue -> HARD FAIL",
                led2(anc("A", proof_file="proofs/nope.lean", proof_state="written")),
                reg(("A", "")),
                1,
            ),
            # ---- G1: derivation-showing-verification under the same clean bar ----
            (
                "G1: clean derivation (verified+clean+sorry-free) -> PASS",
                led2(anc("A", provenance_kind="derivation", **verified(clean))),
                reg(),
                0,
            ),
            (
                "G1: bare derivation (no proof-fields) -> PASS (exempt)",
                led2({"id": "A", "provenance_kind": "derivation"}),
                reg(),
                0,
            ),
            (
                "G1: derivation SHOWS verification but source has sorry -> HARD FAIL",
                led2(anc("A", provenance_kind="derivation", **verified(withsorry))),
                reg(),
                1,
            ),
            (
                "G1: derivation with proof_file but NO verification block -> HARD FAIL",
                led2(
                    anc(
                        "A",
                        provenance_kind="derivation",
                        proof_file=clean,
                        proof_state="written",
                    )
                ),
                reg(),
                1,
            ),
            (
                "G1: dirty derivation-showing-verification but registered -> PASS",
                led2(anc("A", provenance_kind="derivation", **verified(withsorry))),
                reg(("A", "#617")),
                0,
            ),
            (
                "G1: registered anchor reclassified to CLEAN derivation -> stale FAIL",
                led2(anc("A", provenance_kind="derivation", **verified(clean))),
                reg(("A", "#617")),
                1,
            ),
            (
                "G1: registered anchor reclassified to BARE derivation -> stale FAIL (resolved)",
                led2({"id": "A", "provenance_kind": "derivation"}),
                reg(("A", "#617")),
                1,
            ),
        ]
        for name, l, r, exp in cf:
            got = run_full_ledger(l, r, root=root)
            ok = got == exp
            print(
                f"  [{'PASS' if ok else 'FAIL'}] {name}  (exit {got}, expected {exp})"
            )
            failures += not ok

    if failures:
        print(f"\n{failures} test(s) FAILED")
        return 1
    print("\nAll manifest-gate tests passed (C1/C2/C3/C3-FULL).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
