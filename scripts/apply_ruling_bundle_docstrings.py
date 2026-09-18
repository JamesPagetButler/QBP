#!/usr/bin/env python3
"""#652 encode (PR #662): rewrite the guardrail docstrings that said "NOT identified with the
observer's ℍ … pending flag 3 / the beekeeper's ruling" at the sites the ruling bundle v0.7 §2
lists — Hosting.lean 73–75 / 288–289 / 586–589, CrystalHosting.lean 82–83 / 555–557,
HolographicSubalgebra.lean 7–12, Substrate README 26, substrate-hosting-definition §3.
Nothing is ruled: the flag-3 split is an editorial split applied by the encode; the
identification is POST-observer-associativity, an OPEN root with a kill list. Each site is an
exact-text replacement that must match exactly once; the script refuses otherwise. Idempotent
(a site already rewritten is skipped). Comment/prose only — no Lean code line is touched.
"""

import sys

SITES = [
    (
        "proofs/QBP/Substrate/Hosting.lean",
        "2. **The crystal's ℍ is NOT identified with \"the observer's ℍ\".**  DERIV-holographic\n   flag 3 is pending the beekeeper's ruling.",
        "2. **The crystal's ℍ is NOT derived to be \"the observer's ℍ\".**  That identification is\n   the content of POST-observer-associativity — an OPEN root with a kill list (the flag-3\n   split applied by the #652 encode, ruling bundle v0.7 §2; nothing ruled).",
    ),
    (
        "proofs/QBP/Substrate/Hosting.lean",
        'No identification with "the observer\'s ℍ" is made here\n    (DERIV-holographic flag 3 pending).',
        'No identification with "the observer\'s ℍ" is made here\n    (that is POST-observer-associativity, an OPEN root — flag-3 split, ruling bundle v0.7 §2).',
    ),
    (
        "proofs/QBP/Substrate/Hosting.lean",
        "AXIOM-2 says the boundary encoding is 𝕆; the\n  `Universe` structure above carries NO boundary field and no holography\n  semantics.  DERIV-holographic flag 3 (identifying `ℍ_s` with \"the observer's ℍ\")\n  is pending the beekeeper's ruling.",
        'POST-boundary-encoding (AXIOM-2, re-rooted) says each universe has an\n  encoding octonion, at the level DERIV-encoding-level derives; the `Universe` structure\n  above carries NO boundary field and no holography semantics.  The identification of\n  `ℍ_s` with "the observer\'s ℍ" is POST-observer-associativity, an OPEN root (flag-3\n  split, ruling bundle v0.7 §2; nothing ruled).',
    ),
    (
        "proofs/QBP/Foundations/CrystalHosting.lean",
        "\"is the observer's ℍ\" or carries any DERIV-holographic reading — that\ninterpretation is pending the beekeeper's ruling on ledger flag 3 and is",
        '"is the observer\'s ℍ" or carries any holographic reading — that identification\nis POST-observer-associativity, an OPEN root with a kill list (flag-3 split, ruling\nbundle v0.7 §2; nothing ruled), and is',
    ),
    (
        "proofs/QBP/Foundations/CrystalHosting.lean",
        "observable; that reading is the (still open) DERIV-holographic flag 3. -/",
        "observable; that reading is INTERP-holographic-boundary — an OPEN root, the P2 vs P2′\n    pair (ruling bundle v0.7 §1). -/",
    ),
    (
        "proofs/QBP/Foundations/HolographicSubalgebra.lean",
        '  `DERIV-holographic` currently reads: *"Observers require associativity.  The\n  largest associative subalgebra of 𝕆 is ℍ (dim 4).  The 4D gap is the\n  holographic boundary."*  It carries constitutional flag 3 (#473 rounds 13–15)\n  because it was supported only through Prop 16 via `ℓ`.  This file splits the\n  principle into its provable and its non-provable parts and proves the provable\n  ones, so that the flag can be re-scoped to exactly what remains a postulate.',
        '  `DERIV-holographic` read: *"Observers require associativity.  The largest\n  associative subalgebra of 𝕆 is ℍ (dim 4).  The 4D gap is the holographic\n  boundary."*  It carried constitutional flag 3 (#473 rounds 13–15) because it was\n  supported only through Prop 16 via `ℓ`.  The #652 encode (ruling bundle v0.7 §2)\n  split it: the proved parts are `DERIV-holographic-theorem` (this file); the\n  postulate parts are `POST-observer-associativity` and `POST-observation`; the\n  reading is `INTERP-holographic-boundary` — all three OPEN roots with kill lists\n  (nothing ruled).  This file proves the provable parts.',
    ),
    (
        "proofs/QBP/Substrate/README.md",
        "observer's ℍ\" (DERIV-holographic flag 3 pending).",
        "observer's ℍ\" (that is POST-observer-associativity, an OPEN root — flag-3 split,\n  ruling bundle v0.7 §2).",
    ),
    (
        "docs/foundations/substrate-hosting-definition-2026-09-07.md",
        '- It does not identify ℍ_s with "the observer\'s ℍ" (DERIV-holographic, flag 3).',
        '- It does not identify ℍ_s with "the observer\'s ℍ" (that identification is POST-observer-associativity, an OPEN root — flag-3 split applied by the #652 encode, ruling bundle v0.7 §2; nothing ruled).',
    ),
]


def main():
    done = 0
    for path, old, new in SITES:
        with open(path, encoding="utf-8") as f:
            s = f.read()
        if new in s:
            continue
        if s.count(old) != 1:
            print(f"REFUSING: {path}: expected exactly one match, found {s.count(old)}")
            sys.exit(2)
        with open(path, "w", encoding="utf-8") as f:
            f.write(s.replace(old, new, 1))
        done += 1
    print(f"docstrings updated: {done} (of {len(SITES)} sites)")


if __name__ == "__main__":
    main()
