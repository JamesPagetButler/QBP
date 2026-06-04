#!/usr/bin/env python3
"""Lean foundations gate — enforces the zero-sorry / no-vacuous-stub / no-native_decide
standard on proofs/QBP/Foundations/** (issue #481; policy: inter/lean-proof-best-practices.md
Rule 4 + docs/foundations/scope-deliberation-2026-05-31.md).

Two enforcement tiers:

  HARD-BAN (zero tolerance, any occurrence fails):
    - native_decide          — trusted-compiler escape; kernel `decide` only
    - `: True := by trivial`  — the vacuous-proof cardinal sin (the archive octonionMul
                                pattern: a named theorem that proves only True)

  RATCHET (baseline count in .lean-gate-baseline.json; must not INCREASE):
    - sorry                   — honest unproven placeholder; allowed in the skeleton but
                                may only go down (Phase-2..4 proofs replace stubs)
    - vacuous `: True :=` thm — a theorem typed `True` asserts nothing; the breakdown
                                ✗-cells must become real statements (scope-deliberation
                                exit gate), so this count must only go down

Comments are stripped before matching (doc-comments legitimately mention "sorry").

Usage: check_lean_foundations.py [--dir proofs/QBP/Foundations] [--baseline <path>] [--update-baseline]
Exit 0 = pass, 1 = violation.
"""

import argparse
import glob
import json
import os
import re
import sys

HARD_BAN = {
    "native_decide": re.compile(r"\bnative_decide\b"),
    "vacuous-proof `: True := by trivial`": re.compile(
        r":\s*True\s*:=\s*by\s+trivial\b"
    ),
}
RATCHET = {
    "sorry": re.compile(r"\bsorry\b"),
    "vacuous-`: True :=` theorem": re.compile(r":\s*True\s*:="),
}


def strip_comments(src: str) -> str:
    # block comments /- ... -/ (Lean nests, but a non-greedy single pass is enough for our files);
    # then line comments -- ... to EOL.
    src = re.sub(r"/-.*?-/", "", src, flags=re.DOTALL)
    src = re.sub(r"--.*", "", src)
    return src


def scan(lean_dir):
    hard = {k: 0 for k in HARD_BAN}
    ratchet = {k: 0 for k in RATCHET}
    hard_hits = []
    for path in sorted(
        glob.glob(os.path.join(lean_dir, "**", "*.lean"), recursive=True)
    ):
        with open(path, encoding="utf-8") as f:
            raw = f.read()
        code = strip_comments(raw)
        for name, rx in HARD_BAN.items():
            n = len(rx.findall(code))
            hard[name] += n
            if n:
                hard_hits.append((path, name, n))
        for name, rx in RATCHET.items():
            ratchet[name] += len(rx.findall(code))
    return hard, ratchet, hard_hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="proofs/QBP/Foundations")
    ap.add_argument(
        "--baseline", default="proofs/QBP/Foundations/.lean-gate-baseline.json"
    )
    ap.add_argument(
        "--update-baseline",
        action="store_true",
        help="rewrite the baseline to current counts (use ONLY when intentionally reducing)",
    )
    args = ap.parse_args()

    hard, ratchet, hard_hits = scan(args.dir)

    if args.update_baseline:
        with open(args.baseline, "w", encoding="utf-8") as f:
            json.dump(ratchet, f, indent=2, sort_keys=True)
            f.write("\n")
        print(f"baseline updated: {ratchet}")
        return 0

    failed = False

    # HARD bans
    for name, count in hard.items():
        if count:
            print(
                f"::error::HARD-BAN violated — {name}: {count} occurrence(s) in {args.dir}"
            )
            failed = True
    for path, name, n in hard_hits:
        print(f"::error file={path}::{n}× {name}")

    # RATCHET
    try:
        with open(args.baseline, encoding="utf-8") as f:
            baseline = json.load(f)
    except FileNotFoundError:
        print(
            f"::error::baseline {args.baseline} missing — run with --update-baseline to create it"
        )
        return 1

    for name, count in ratchet.items():
        base = baseline.get(name, 0)
        if count > base:
            print(
                f"::error::RATCHET violated — {name}: {count} > baseline {base}. "
                f"New {name} is not allowed; the count may only decrease."
            )
            failed = True
        elif count < base:
            print(
                f"::warning::{name} decreased {base} → {count}. "
                f"Run check_lean_foundations.py --update-baseline and commit the lowered baseline."
            )
        else:
            print(f"ok: {name} at baseline ({count})")

    if failed:
        print(
            "\nLean foundations gate FAILED. Policy: inter/lean-proof-best-practices.md Rule 4."
        )
        return 1
    print("\nLean foundations gate PASSED.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
