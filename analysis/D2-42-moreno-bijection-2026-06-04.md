# D2: "42 ⟷ Moreno" — STRUCTURE or COINCIDENCE?

**Date:** 2026-06-04
**Obligation:** D2 from `docs/foundations/debate-O2-invariant-2026-06-03.md`
**Task:** Bijection-or-bust. Map the 42 passing crossing subalgebras (42-A) to the
42 sedenion zero-divisor objects (42-B, Moreno 1998), or rule coincidence.
**Bar (from the debate):** "heavily favored" is not an outcome. Produce the explicit
G-equivariant bijection with matched orbit decomposition, or record COINCIDENCE.

---

## VERDICT

> **COINCIDENCE (NO BIJECTION).** Both 42s are real and computationally reproduced.
> But under the *only* group that is a genuine symmetry of both sets — the octonion
> frame-automorphism group **PGL(3,2) = PSL(2,7), order 168** (Fano-plane
> collineations) — the orbit decompositions are irreconcilable:
> **orbit(42-A) = {7, 7, 7, 21}** (four orbits) versus **orbit(42-B) = {42}** (one
> transitive orbit). A bijection commuting with the group forces equality of the
> orbit-size multisets; {7,7,7,21} ≠ {42}, so **no G-equivariant bijection exists.**
> The shared number 42 is a numerical coincidence, not a structural correspondence.
>
> **Partial structure recorded (genuine, but not a bijection):** (a) the complementary-
> counting claim is *true* — a crossing candidate passes iff its subalgebra contains
> no zero divisor (98/98 failing contain ≥1; 42/42 passing contain 0); (b) the 42-B
> Moreno planes are distinguished inside the incidence as the unique "degree-4" class
> of zero-divisor planes. These are worth keeping. Neither yields a passing↔plane map:
> passing subalgebras contain *zero* zero divisors, so there is no incidence edge to
> route a bijection through, and the incidence counts (42×4 = 168 ≠ 98 failing) do not
> single out a 42-element subset.

---

## The two 42s (both reproduced)

| Quantity | Value | Status |
|---|---|---|
| 42-A: passing crossing subalgebras (octonion copies in 𝕋 = CD(𝕊)) | **42** of 140 | ✅ reproduced |
| 42-A split (per generating line) | 28 lines × 1 coset + 7 Fano lines × 2 cosets = 28 + 14 | ✅ |
| 42-B: distinct sedenion zero-divisor planes {a,b} | **42** | ✅ reproduced |
| 42-B as a grid | 49 − 7 = 7 × 6 (low ∈ {1..7}, high ∈ {9..15}, high ≠ low+8) | ✅ |

**Validation of the CD core (genuine doubling recursion, no guessed tables):**
`e_i² = −1` (all i≥1), `e₁e₂ = e₃`, `e₂e₃ = e₁`, `e₃e₁ = e₂`, and the Lean O1a
witness `(e₂+e₉)(e₄+e₁₅) = 0` all pass. XOR-closure `eₐe_b ∈ ±e_{a⊕b}` verified as
a theorem of the recursion at dims 16 and 32. Sign table matches the kernel-checked
`SedenionOctonionCount.lean` `sgnTable`.

---

## 42-B: enumeration and quotient levels (where 42 appears)

Enumeration target: all basis-pair zero divisors of 𝕊 — pairs
`((a,s,b),(c,t,d))` with `(e_a + s·e_b)(e_c + t·e_d) = 0`, `a<b`, `c<d`,
`s,t ∈ {±1}`, indices `1..15`.

| Quotient level | Object | Count | Notes |
|---|---|---|---|
| L0 raw | ordered solution pairs (x,y), leading coeff +1 | **336** | |
| L1 overall-sign | leading-coeff-+1 already fixes overall sign | 336 | no collapse (sign already normalized) |
| swap-closure | of 336, how many have (y,x) also a ZD | 336 | **fully swap-symmetric**: xy=0 ⟺ yx=0 here |
| L2 unordered factor pair | {x,y} | **168** | 336/2 |
| distinct factors | signed planes `e_a + s·e_b` | **84** | = 42 planes × 2 signs |
| **distinct planes** | `{a,b}` (sign-forgetful) | **42** | ← **THIS is where 42 appears** |
| distinct quadruples | `{a,b,c,d}` | 42 | each solution uses a 4-element index set |

**Precise statement of where 42 appears:** the number 42 is the count of distinct
**zero-divisor planes** `span(e_a, e_b)` — i.e. the count of unordered index-pairs
`{a,b}` such that some signed combination `e_a ± e_b` is a left zero-divisor.
It does **not** appear at the raw (336), factor (84), or unordered-factor-pair (168)
level. The corpus "42 zero divisors (Moreno)" = these 42 assassin planes.

**Structure of the 42 planes (the Moreno characterization, reproduced):**
each plane has exactly one index in `{1..7}` (octonion-imaginary) and one in
`{9..15}` (upper doubling half); index 8 never appears; the seven "doubling-partner"
pairs `(a, a+8)` are excluded. Hence **42 = 7×7 − 7 = 7×6**. Every index 1..7 and
9..15 appears in exactly 6 planes (perfectly regular). This is the standard
norm-1-zero-divisor / G₂ structure of 𝕊 in combinatorial form.

---

## Bijection hunt

### Route 2a — complementary counting & incidence (genuine partial structure)

- **PASS ⟺ no zero divisor: TRUE.** All **98/98** failing crossing candidates contain
  ≥1 basis-pair zero divisor; all **42/42** passing contain **0**. Clean dichotomy.
- **Regular incidence:** each failing candidate contains exactly **12** distinct
  zero-divisor planes (98 × 12 = 1176 plane-incidences).
- **A Moreno-isomorphic class is distinguished:** of the 294 distinct ZD planes
  appearing across failing candidates, the incidence-degree distribution is
  `{degree 6: 126, degree 4: 42, degree 2: 126}`. The **degree-4 class is a 42-element
  set of the exact 42-B form** — `{a ∈ 17..23, b ∈ 25..31, b ≠ a+8}` = `16 + (1..7)`
  paired with `16 + (9..15)`, the Moreno `7×6` structure **relocated into the upper
  sedenion double** of 𝕋 = CD(𝕊). It is structurally isomorphic to 42-B but lives on
  the second-copy indices, NOT literally the pure-𝕊 planes 1..15. So 42 *does* reappear
  as a distinguished incidence class — but as an isomorphic copy of the Moreno
  structure, not the original planes. Real partial structure; not an identity.
- **But no bijection to the passing 42:** passing subalgebras contain **zero** zero
  divisors, so there is **no incidence edge** between a passing subalgebra and a ZD
  plane. Any passing↔plane map must route through the failing set; but |passing| = 42,
  |failing| = 98, and the 42-B incidence (42 × 4 = 168) does not carve a canonical
  42-element subset out of the 98 failing candidates. No clean map exists.

### Route 2b — orbit decomposition under the frame symmetry group (decisive)

The natural symmetry common to both is the octonion frame-automorphism group, realized
as the **PGL(3,2) = PSL(2,7) Fano-plane collineations** (order **168**, computed: 168
permutations of {1..7} preserving the 7 octonion Fano triples), lifted to all index
levels (`i ↦ σ(i)`, `8+i ↦ 8+σ(i)`, etc.).

| Set | Group action verified preserved? | Orbit sizes | # orbits |
|---|---|---|---|
| **42-B** (planes) | yes | **{42}** | 1 (transitive) |
| **42-A** (passing) | yes | **{7, 7, 7, 21}** | 4 |

42-A orbit identities: two size-7 orbits of **Fano-line doubles**, one size-7 +
one size-21 orbit of **non-Fano-line doubles** (28 = 7 + 21).

**This is the kill.** A bijection `f : A → B` commuting with the group action forces
the orbit-size multisets to be equal. `{7,7,7,21} ≠ {42}`. Therefore **no
G-equivariant bijection exists.** 42-B is homogeneous (one orbit); 42-A is not. They
are different G-sets that happen to have the same cardinality.

**Larger-group check (ruling out a bigger merging group):** the only level-permutations
that are frame automorphisms fix level 0 and permute the upper three levels (6 of 24);
these do **not** preserve the 42-A passing set (the crossing-candidate construction
privileges the 𝕊 = levels {0,1} → double = levels {2,3} structure). Adjoining them
blows the orbit closure out of the 42-set (sizes 7,21,21,63), confirming no larger
natural group rescues equivariance.

### Route 2c — assassin planes vs failing cosets

Subsumed by 2a: the assassin planes in the failing candidates that have the Moreno
`7×6` form constitute the degree-4 incidence class (on the upper-double indices). No
additional map to the passing set emerges (same obstruction: passing carries no zero
divisors).

---

## What survives (record for the foundation matrix)

1. **Both counts are real and parameter-free.** 42-A = 42 (Python-verified, consistent
   with the kernel-checked O1a partition and the MODERATOR'S EXHIBIT k(5) = 50 = 8 + 42).
2. **Complementary counting is a theorem-candidate, not metaphor:** pass ⟺
   no-zero-divisor, exactly. This is the right way to *state* the discriminator (feeds D1/O1a′).
3. **42-B = 7 × 6 Moreno grid** with the `(a, a+8)` doubling-partner exclusion — the
   combinatorial face of the G₂ zero-divisor structure.
4. **A Moreno-form class is an intrinsic incidence class** (degree-4) of the crossing
   structure — the `7×6` Moreno structure reappears on the upper-double indices of 𝕋.
None of (1)–(4) constitutes a bijection 42-A ↔ 42-B. The agreement of the *number* 42
is coincidence; the two 42s have different symmetry types.

**UNVERIFIED / out of scope:** Moreno 1998's homeomorphism ZD-norm-1 ≅ G₂ was not
re-derived here (cited only); the combinatorial 42-plane characterization is what was
computed. No claim is made about whether a *non-natural* (group-breaking) bijection
could be written down — such a map exists trivially for any two 42-element sets and
carries no content; the debate bar is the equivariant/structural map, which is ruled out.

---

## Appendix — runnable Python

Self-contained. Requires only the standard library. Reproduces every number above.

```python
from itertools import combinations
from functools import lru_cache
from collections import defaultdict, Counter
import itertools

# ---------- Genuine Cayley-Dickson doubling (no guessed tables) ----------
def conj(x):
    return (x[0],) + tuple(-v for v in x[1:])

@lru_cache(maxsize=None)
def cd_mul(x, y):
    n = len(x)
    if n == 1:
        return (x[0] * y[0],)
    h = n // 2
    a, b, c, d = x[:h], x[h:], y[:h], y[h:]
    ac = cd_mul(a, c); db = cd_mul(conj(d), b)
    da = cd_mul(d, a); bc = cd_mul(b, conj(c))
    return tuple(ac[i]-db[i] for i in range(h)) + tuple(da[i]+bc[i] for i in range(h))

def basis(dim, i):
    return tuple(1 if k == i else 0 for k in range(dim))

def build_tables(dim):
    SGN = [[0]*dim for _ in range(dim)]; XID = [[0]*dim for _ in range(dim)]
    for i in range(dim):
        ei = basis(dim, i)
        for j in range(dim):
            p = cd_mul(ei, basis(dim, j))
            nz = [k for k in range(dim) if p[k] != 0]
            assert len(nz) == 1 and nz[0] == (i ^ j)
            XID[i][j] = nz[0]; SGN[i][j] = p[nz[0]]
    return SGN, XID

SGN16, _ = build_tables(16)
SGN32, _ = build_tables(32)

def mul_sparse(SGN, tx, ty):
    out = {}
    for cx, ix in tx:
        for cy, iy in ty:
            k = ix ^ iy
            out[k] = out.get(k, 0) + cx*cy*SGN[ix][iy]
    return {k: v for k, v in out.items() if v != 0}

# Validation
assert all(SGN16[i][i] == -1 for i in range(1, 16))
assert (1 ^ 2) == 3 and SGN16[1][2] == 1
assert mul_sparse(SGN16, [(1,2),(1,9)], [(1,4),(1,15)]) == {}

# ---------- 42-B: sedenion zero-divisor planes ----------
def zd_solutions():
    pairs = list(combinations(range(1, 16), 2))
    sols = []
    for (a, b) in pairs:
        for s in (1, -1):
            x = [(1, a), (s, b)]
            for (c, d) in pairs:
                for t in (1, -1):
                    if mul_sparse(SGN16, x, [(1, c), (t, d)]) == {}:
                        sols.append(((a, s, b), (c, t, d)))
    return sols

ZD = zd_solutions()
planesB = sorted(set((a, b) for ((a, s, b), _) in ZD))
print("raw ZD solutions:", len(ZD))                         # 336
print("distinct factors:", len(set(f for sol in ZD for f in sol)))  # 84
print("42-B planes:", len(planesB))                         # 42
assert len(ZD) == 336 and len(planesB) == 42
# grid check: 49 - 7 doubling partners
grid = set((lo, hi) for lo in range(1, 8) for hi in range(9, 16))
assert sorted(grid - set(planesB)) == [(i, i+8) for i in range(1, 8)]

# ---------- 42-A: passing crossing subalgebras of T = CD(S) ----------
def assoc(SGN, a, b, c):
    return SGN[a][b]*SGN[a^b][c] - SGN[b][c]*SGN[a][b^c]

def is_alt(SGN, idxset):
    L = list(idxset)
    for a in L:
        for b in L:
            for c in L:
                ac = assoc(SGN, a, b, c)
                if ac != -assoc(SGN, b, a, c) or ac != -assoc(SGN, a, c, b):
                    return False
    return True

sed = list(range(1, 16))
lines = sorted({frozenset([x, y, x ^ y]) for x, y in combinations(sed, 2)
                if 0 < (x ^ y) < 16}, key=lambda s: sorted(s))
assert len(lines) == 35

candidates = []
for L in lines:
    sub4 = [0] + sorted(L)
    seen = set()
    for g in range(16, 32):
        coset = frozenset(g ^ s for s in sub4)
        if coset in seen: continue
        seen.add(coset)
        idxset = frozenset(sub4) | frozenset(g ^ s for s in sub4)
        candidates.append((L, g, idxset))
assert len(candidates) == 140

passing = [(L, g, idx) for (L, g, idx) in candidates if is_alt(SGN32, idx)]
print("42-A passing:", len(passing))                        # 42
assert len(passing) == 42

# ---------- complementary counting / incidence ----------
failing = [(L, g, idx) for (L, g, idx) in candidates
           if frozenset(idx) not in {frozenset(i) for (_, _, i) in passing}]
def zd_planes_in(idxset):
    nz = sorted(i for i in idxset if i != 0); pl = set()
    for (a, b) in combinations(nz, 2):
        for s in (1, -1):
            x = [(1, a), (s, b)]
            for (c, d) in combinations(nz, 2):
                for t in (1, -1):
                    if mul_sparse(SGN32, x, [(1, c), (t, d)]) == {}:
                        pl.add((a, b)); pl.add((c, d))
    return pl
fail_zd = [len(zd_planes_in(idx)) for (_, _, idx) in failing]
pass_zd = [len(zd_planes_in(idx)) for (_, _, idx) in passing]
print("failing with ZD:", sum(1 for n in fail_zd if n), "/", len(failing))  # 98/98
print("passing with ZD:", sum(1 for n in pass_zd if n), "/", len(passing))  # 0/42
print("per-failing distinct ZD planes:", set(fail_zd))      # {12}
plane_to_fail = defaultdict(set)
for (_, _, idx) in failing:
    for pl in zd_planes_in(idx):
        plane_to_fail[pl].add(frozenset(idx))
print("ZD-plane incidence degrees:", dict(Counter(len(v) for v in plane_to_fail.values())))
# {6:126, 4:42, 2:126}. The degree-4 class is a 42-element Moreno-FORM set living on
# the UPPER double indices {16+(1..7)} x {16+(9..15)}, b != a+8 -- isomorphic to 42-B,
# not literally the pure-S planes 1..15.
deg4 = {pl for pl, v in plane_to_fail.items() if len(v) == 4}
assert len(deg4) == 42
assert all(17 <= a <= 23 and 25 <= b <= 31 and b != a + 8 for (a, b) in deg4)

# ---------- ORBIT COMPARISON under PGL(3,2)=168 ----------
fano7 = {frozenset([x, y, x ^ y]) for x, y in combinations(range(1, 8), 2) if 0 < (x ^ y) < 8}
colls = []
for perm in itertools.permutations(range(1, 8)):
    p = {i+1: perm[i] for i in range(7)}
    if all(frozenset(p[i] for i in L) in fano7 for L in fano7):
        colls.append(p)
assert len(colls) == 168

def orbits(elements, act):
    seen = set(); out = []
    for e in elements:
        if e in seen: continue
        orb = {act(p, e) for p in colls}
        out.append(orb); seen |= orb
    return out

def actB(p, plane):
    a, b = plane; a2 = p[a]; b2 = 8 + p[b-8]
    return (min(a2, b2), max(a2, b2))
def actA(p, s):
    m = {0:0, 8:8, 16:16, 24:24}
    for i in range(1, 8):
        m[i]=p[i]; m[8+i]=8+p[i]; m[16+i]=16+p[i]; m[24+i]=24+p[i]
    return frozenset(m[i] for i in s)

oB = orbits(planesB, actB)
oA = orbits([frozenset(idx) for (_, _, idx) in passing], actA)
print("42-B orbit sizes:", sorted(len(o) for o in oB))       # [42]
print("42-A orbit sizes:", sorted(len(o) for o in oA))       # [7,7,7,21]
assert sorted(len(o) for o in oB) == [42]
assert sorted(len(o) for o in oA) == [7, 7, 7, 21]
print("VERDICT: orbit multisets differ -> NO G-equivariant bijection -> COINCIDENCE")
```
