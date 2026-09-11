#!/usr/bin/env python3
"""Ruling bundle, Decision 2 — update the guardrail docstrings that say the crystal's ℍ is "NOT identified with the
observer's ℍ … pending flag 3", plus the Substrate README, once the beekeeper has ruled PR #652. Refuses to run
while RULED is False. Idempotent (guards on the marker string). Sites (PR #652 §2): proofs/QBP/Substrate/Hosting.lean
(module docstring item 2; universe_hosts_quaternion docstring; §11 boundary bullet); proofs/QBP/Foundations/
CrystalHosting.lean (interpretation guardrail; vacuum_hosts_quaternion docstring); proofs/QBP/Substrate/README.md.
Usage: python3 scripts/apply_ruling_bundle_docstrings.py    (edit RULED / RULING_DATE / RULING_URL_BUNDLE first)
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RULED = False
RULING_DATE = "<ruling date>"
RULING_URL_BUNDLE = "<URL of the beekeeper's ruling comment on PR #652>"
MARKER = "ruled with the flag-3 split"
NEW = (
    f"identified with the observer's ℍ under hosting clause (a) — definition D + premise P1′ (observers are entities "
    f"of clause (a)) — as {MARKER} (POST-observer-associativity; beekeeper {RULING_DATE}, {RULING_URL_BUNDLE}); "
    f"exclusivity remains the postulate's content"
)
PATTERNS = [
    (
        "proofs/QBP/Substrate/Hosting.lean",
        r"NOT identified with \"the observer's ℍ\"\.\*\*\s+DERIV-holographic\s+flag 3 is pending the beekeeper's ruling\.",
        f"{NEW}.**",
    ),
    (
        "proofs/QBP/Substrate/Hosting.lean",
        r"No identification with \"the observer's ℍ\" is made here\s+\(DERIV-holographic flag 3 pending\)\.",
        f"The hosted ℍ is {NEW}.",
    ),
    (
        "proofs/QBP/Substrate/Hosting.lean",
        r"DERIV-holographic flag 3 \(identifying `ℍ_s` with \"the observer's ℍ\"\)\s+is pending the beekeeper's ruling\.",
        f"The identification of `ℍ_s` with the observer's ℍ is {NEW}.",
    ),
    (
        "proofs/QBP/Foundations/CrystalHosting.lean",
        r"\"is the observer's ℍ\" or carries any DERIV-holographic reading — that\s+interpretation is pending the beekeeper's ruling on ledger flag 3 and is\s+deliberately absent from every statement here\.",
        f'"is the observer\'s ℍ" as a theorem — that identification is {NEW}, and is deliberately absent from every statement here.',
    ),
    (
        "proofs/QBP/Foundations/CrystalHosting.lean",
        r"No identification of it with \"the observer's ℍ\", and\s+no DERIV-holographic reading, is claimed here \(pending the beekeeper's ruling\s+on ledger flag 3\)\.",
        f"The identification with the observer's ℍ is {NEW}; no theorem here claims it.",
    ),
    (
        "proofs/QBP/Substrate/README.md",
        r"does \*\*not\*\* identify the crystal's ℍ with \"the\s+observer's ℍ\" \(DERIV-holographic flag 3 pending\)\.",
        f"identifies the crystal's ℍ with the observer's ℍ only as a postulate ({NEW}).",
    ),
]


def main():
    if not RULED:
        print("REFUSING: RULED is False — the beekeeper has not ruled PR #652.")
        sys.exit(2)
    total = 0
    for rel, pat, rep in PATTERNS:
        p = os.path.join(ROOT, rel)
        s = open(p, encoding="utf-8").read()
        s2, n = re.subn(pat, rep, s, count=1)
        if n == 0:
            print(
                f"{'already applied' if MARKER in s else 'WARNING: pattern not found'}: {rel} :: {pat[:50]}"
            )
            continue
        open(p, "w", encoding="utf-8").write(s2)
        total += n
    print(f"docstrings updated: {total}")


if __name__ == "__main__":
    main()
