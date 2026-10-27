#!/usr/bin/env python3
"""#633 cross-check for proofs/QBP/Foundations/Octonion32Count.lean (independent of Lean).

Reads the committed Lean file and checks, in Python:
  1. the 32 bit-packed row masks in `sgnRowMask` are exactly the `![...]` `sgnTable`
     (bit b of mask a set  <=>  sgnTable a b == -1);
  2. `subspaces.filter (any >= 16)` == `crossingData.map (.2.2)` as ORDERED lists
     (the identity `crossing_subspaces_eq_crossingData` kernel-checks);
  3. the counts the module proves: 50 alternative of 155, split 8 (base) + 42 (crossing);
     the D1 discriminator `predPass` agrees with brute-force alternativity on all 140.
Exit 0 iff everything agrees. Usage: python3 crosscheck_sgn_masks.py [path-to-lean-file]
"""

import re
import sys

path = (
    sys.argv[1] if len(sys.argv) > 1 else "proofs/QBP/Foundations/Octonion32Count.lean"
)
src = open(path, encoding="utf-8").read()

tab_src = src[src.index("def sgnTable") : src.index("/-- Sign accessor")]
T = [[int(x) for x in r.split(",")] for r in re.findall(r"!\[([-0-9, ]+)\]", tab_src)]
assert len(T) == 32 and all(len(r) == 32 for r in T), "sgnTable is not 32x32"

mask_src = src[src.index("def sgnRowMask") : src.index("def sgnFast")]
masks = [int(m, 16) for m in re.findall(r"0x([0-9a-fA-F]{8})", mask_src)]
assert len(masks) == 32, f"expected 32 masks, found {len(masks)}"
expected = [sum(1 << b for b in range(32) if T[a][b] == -1) for a in range(32)]
assert masks == expected, "sgnRowMask does not match sgnTable"
print("1. sgnRowMask == bit-packed sgnTable: OK (32 masks)")

sub_src = src[src.index("def subspaces") : src.index("/-- The 35 GF(2)-lines")]
subspaces = [
    [int(x) for x in r.split(",")] for r in re.findall(r"\[([0-9, ]+)\]", sub_src)
]
assert len(subspaces) == 155, len(subspaces)
cross_src = src[src.index("def crossingData") : src.index("/-! ## 5.")]
cross = re.findall(r"\(\[([0-9, ]+)\], (\d+), \[([0-9, ]+)\]\)", cross_src)
assert len(cross) == 140, len(cross)
crossH = [[int(x) for x in t[2].split(",")] for t in cross]
filt = [H for H in subspaces if any(x >= 16 for x in H)]
assert (
    filt == crossH
), "filter(any>=16) subspaces != crossingData.map(.2.2) as ordered lists"
print("2. subspaces.filter(any >= 16) == crossingData.map(.2.2), in order: OK (140)")


def assoc(a, b, c):
    return T[a][b] * T[a ^ b][c] - T[b][c] * T[a][b ^ c]


def alt(H):
    return all(
        assoc(a, b, c) == -assoc(b, a, c) and assoc(a, b, c) == -assoc(a, c, b)
        for a in H
        for b in H
        for c in H
    )


def span4(L):
    return [0] + L


def is_fano(L):
    return all(1 <= x <= 7 for x in L)


def twisted(L):
    return [8 ^ v for v in range(8) if v >= 1 and v not in span4(L)]


def pred_pass(L, c):
    return (c in span4(L)) or (is_fano(L) and c in twisted(L))


flags = [alt([0] + H) for H in subspaces]
total = sum(flags)
base = sum(1 for H, f in zip(subspaces, flags) if f and all(x < 16 for x in H))
crossing = sum(1 for H, f in zip(subspaces, flags) if f and any(x >= 16 for x in H))
assert (total, base, crossing) == (50, 8, 42), (total, base, crossing)
for t in cross:
    L = [int(x) for x in t[0].split(",")]
    c = int(t[1])
    H = [int(x) for x in t[2].split(",")]
    assert alt([0] + H) == pred_pass(L, c), ("discriminator mismatch", L, c)
print("3. counts 50 = 8 + 42 and D1 discriminator on all 140 crossing pairs: OK")
print("all checks passed")
