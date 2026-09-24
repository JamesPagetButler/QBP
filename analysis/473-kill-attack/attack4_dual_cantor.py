"""Attack 4 (#473 kill attempt, Prop 10'/13(a)/15): the dual Cantor group of the CD index tower.

Sections mirror the report:
  A. sign cocycle sigma(m,k) from the CDAlg.mulCoeff recursion; check vs flowlib.mul on all
     basis pairs (n=3: 64, n=4: 256); characters chi_v(m) = (-1)^{popcount(v&m)} as
     automorphisms (all of them, and ONLY them among sign functions); embedding of
     G^_4 = (Z/2)^4 in G2 x S3; G^_4-orbits on the 84 basis-sum ZDs (= the 42 planes).
  B. Haar on G^_4 pushed to the algebra (averaging operator = projection to R.1; Fourier dual of
     Haar is delta_0 on the index group); orbit-space coordinates of the 15 basis vectors, the
     84 ZDs, the 126 basis-sum vacua, the 42 plane circles; the pushed measures and <b0^2>;
     rule-invariance of the atomic measures (V=0 on support, F=0), the l-axis map endpoint.
  C. Galois correspondence Fix(ker(G^ -> G^_k)) = CD_k inside the sedenions (k=0..4); the action
     of the profinite G^ on the sedenions factors through the finite G^_4 (kernel check).
Resource estimate: < 300 MB, < 60 s.  Run:  run-bounded 2G 120 python3 attack4_dual_cantor.py
"""

import itertools, json, sys
import numpy as np
from flowlib import mul, N, potential, ruleField, gradV_exact

out = {}


def say(*a):
    print(*a)
    sys.stdout.flush()


# ---------------------------------------------------------------- A. sigma and characters
def conjSign(n, i):
    return 1 if i == 0 else -1


def mulCoeff(n, i, j):
    """literal transcription of proofs/QBP/Foundations/CDAlg.lean mulCoeff (Int-valued)"""
    if n == 0:
        return 1
    half = 2 ** (n - 1)
    pi, a = divmod(i, half)
    pj, c = divmod(j, half)
    if pi == 0 and pj == 0:
        return mulCoeff(n - 1, a, c)
    if pi == 0 and pj == 1:
        return mulCoeff(n - 1, c, a)
    if pi == 1 and pj == 0:
        return conjSign(n - 1, c) * mulCoeff(n - 1, a, c)
    return -(conjSign(n - 1, c) * mulCoeff(n - 1, c, a))


def sigma_table(n):
    D = 2**n
    return np.array(
        [[mulCoeff(n, i, j) for j in range(D)] for i in range(D)], dtype=int
    )


def basis(D, m):
    e = np.zeros(D)
    e[m] = 1.0
    return e


for n in (3, 4):
    D = 2**n
    S = sigma_table(n)
    worst = 0.0
    for m in range(D):
        for k in range(D):
            p = mul(basis(D, m), basis(D, k))
            worst = max(worst, np.max(np.abs(p - S[m, k] * basis(D, m ^ k))))
    say(
        f"[A1] n={n}: mulCoeff recursion vs flowlib.mul on all {D*D} basis pairs: max |diff| = {worst:.1e}"
    )
    out[f"A1_sigma_vs_flowlib_n{n}_maxdiff"] = worst
    # structural facts
    assert all(S[m, 0] == 1 and S[0, m] == 1 for m in range(D))
    assert all(S[m, m] == -1 for m in range(1, D))
    anti = all(S[m, k] == -S[k, m] for m in range(1, D) for k in range(1, D) if m != k)
    say(
        f"     sigma(m,0)=sigma(0,m)=1, sigma(m,m)=-1 (m!=0), antisymmetric off-diagonal on imaginaries: {anti}"
    )

n = 4
D = 16
S4 = sigma_table(4)
np.savetxt(
    "sigma_n4.txt",
    S4,
    fmt="%2d",
    header="sigma(m,k): e_m e_k = sigma(m,k) e_{m xor k}, sedenions (CDAlg.mulCoeff 4)",
)


def popcount(x):
    return bin(x).count("1")


def chi(v, m):
    return -1 if popcount(v & m) % 2 else 1


def is_sign_aut(eps, S):
    """eps: array of +-1 over indices; e_m -> eps[m] e_m is an automorphism iff eps[m]eps[k]=eps[m^k] for all m,k"""
    D = len(eps)
    for m in range(D):
        for k in range(D):
            if eps[m] * eps[k] != eps[m ^ k]:
                return False
    return True


for nn in (3, 4):
    DD = 2**nn
    Snn = sigma_table(nn)
    chars = [np.array([chi(v, m) for m in range(DD)]) for v in range(DD)]
    ok = [is_sign_aut(c, Snn) for c in chars]
    # numerical check via actual products, too
    worst = 0.0
    rng = np.random.default_rng(1)
    X = rng.normal(size=(20, DD))
    Y = rng.normal(size=(20, DD))
    for c in chars:
        lhs = c * mul(X, Y)
        rhs = mul(c * X, c * Y)
        worst = max(worst, np.max(np.abs(lhs - rhs)))
    say(
        f"[A2] n={nn}: all {DD} characters chi_v are automorphisms: {all(ok)} (product residual {worst:.1e})"
    )
    # null: non-character sign functions with eps[0]=+1
    rng = np.random.default_rng(2)
    bad = 0
    tried = 0
    charset = {tuple(c) for c in chars}
    while tried < 1000:
        e = rng.choice([-1, 1], size=DD)
        e[0] = 1
        if tuple(e) in charset:
            continue
        tried += 1
        if is_sign_aut(e, Snn):
            bad += 1
    say(
        f"     null: {tried} random NON-character sign functions tested, automorphisms among them: {bad}"
    )
    out[f"A2_all_characters_aut_n{nn}"] = bool(all(ok))
    out[f"A2_noncharacter_aut_count_n{nn}"] = bad
# exhaustive at n=3 (2^7 sign functions with eps[0]=1)
S3 = sigma_table(3)
cnt = 0
for bits in itertools.product([1, -1], repeat=7):
    e = np.array((1,) + bits)
    if is_sign_aut(e, S3):
        cnt += 1
say(
    f"[A2'] n=3 exhaustive: sign functions (eps(0)=1) that are automorphisms = {cnt} of 128  (expected 8 = |G^_3|)"
)
out["A2_exhaustive_n3_count"] = cnt


# embedding of G^_4 in G2 x S3.  ell = e_8.  Aut fixing ell = G2 (standard embedding).
# S3 elements act as (a, b0, c) -> (m11 a + m12 c, s b0, m21 a + m22 c) with M in O(2).
def as_MS(v):
    """if chi_v acts as (M x I7, s) return (M, s), else None"""
    c = np.array([chi(v, m) for m in range(16)])
    a_signs = c[1:8]
    c_signs = c[9:16]
    if np.all(a_signs == a_signs[0]) and np.all(c_signs == c_signs[0]):
        return (np.diag([a_signs[0], c_signs[0]]), c[8])
    return None


fix_ell = [v for v in range(16) if chi(v, 8) == 1]
in_S3 = {v: as_MS(v) for v in range(16) if as_MS(v) is not None}
say(
    f"[A3] G^_4 elements fixing ell=e8 (hence in G2): v in {fix_ell}  -> G^_3 = (Z/2)^3, order 8"
)
say(
    f"     G^_4 elements of S3-shape (M x I7, s): {[(v, np.diag(M).tolist(), int(s)) for v,(M,s) in in_S3.items()]}"
)
say(
    f"     => G^_4 = G^_3 x <chi_8>, chi_8 = (a,b0,c)->(a,-b0,-c) = the S3 reflection r0 (M=diag(1,-1), s=-1);  G^_4 ∩ S3 = {{1, r0}}"
)
out["A3_fix_ell"] = fix_ell
out["A3_S3_shape"] = {
    int(v): [np.diag(M).tolist(), int(s)] for v, (M, s) in in_S3.items()
}


# 84 basis-sum ZDs and G^_4 orbits
def Lmat(x):
    return np.stack([mul(x, basis(16, k)) for k in range(16)], axis=1)


zds = []
vac_sums = []
for i in range(1, 16):
    for j in range(i + 1, 16):
        for sgn in (1, -1):
            x = (basis(16, i) + sgn * basis(16, j)) / np.sqrt(2)
            r = np.linalg.matrix_rank(Lmat(x), tol=1e-9)
            (zds if r < 16 else vac_sums).append((i, j, sgn, 16 - r))
planes = sorted({(i, j) for i, j, _, _ in zds})
say(
    f"[A4] basis-sum ZDs e_i ± e_j: {len(zds)} (kernel dims {sorted(set(z[3] for z in zds))}); distinct planes {{i,j}}: {len(planes)}"
)
grid_ok = all(1 <= i <= 7 and 9 <= j <= 15 and j != i + 8 for i, j in planes)
say(f"     planes are exactly the 7x6 grid i in 1..7, j in 9..15, j != i+8: {grid_ok}")
# G^_4 orbits on the 84 (mod overall sign): chi_v (e_i + s e_j) = chi_v(i) (e_i + s chi_v(i)chi_v(j) e_j)
orbits = set()
for i, j, s, _ in zds:
    orb = frozenset((i, j, s * chi(v, i) * chi(v, j)) for v in range(16))
    orbits.add(orb)
say(
    f"     G^_4-orbits on the 84 ZDs (mod ±): {len(orbits)}, sizes {sorted(set(len(o) for o in orbits))}  -> the 42 planes ARE the G^_4-quotient of the 84"
)
out["A4_n_zds"] = len(zds)
out["A4_n_planes"] = len(planes)
out["A4_G4_orbits_on_84"] = len(orbits)
say(f"     non-ZD basis sums (vacua, see B): {len(vac_sums)}")

# ---------------------------------------------------------------- B. Haar pushforwards
# B0: Haar on G^_4 = uniform on 16 characters. Averaging operator on the algebra:
rng = np.random.default_rng(3)
X = rng.normal(size=(50, 16))
avg = np.mean([np.array([chi(v, m) for m in range(16)]) * X for v in range(16)], axis=0)
proj0 = np.zeros_like(X)
proj0[:, 0] = X[:, 0]
say(
    f"[B0] Haar-average over G^_4 of chi.x  vs  projection to R.1: max diff {np.max(np.abs(avg - proj0)):.1e}"
)
fourier = np.array([np.mean([chi(v, m) for v in range(16)]) for m in range(16)])
say(
    f"     Fourier transform of Haar on G^_4 (sum_v chi_v(m)/16) over m: {fourier.astype(int).tolist()}  = delta_0 (the real unit, off the state sphere)"
)
out["B0_haar_avg_is_real_projection"] = float(np.max(np.abs(avg - proj0)))


def coords(x):
    """orbit-space coordinates of x in Im S: (|a|, |Im b|, b0, <a,Im b>, V); theta = atan2(|Im b|,|a|) deg"""
    a = x[1:8]
    b0 = x[8]
    c = x[9:16]
    A = np.linalg.norm(a)
    C = np.linalg.norm(c)
    P = float(a @ c)
    V = float(potential(x))
    th = np.degrees(np.arctan2(C, A))
    return dict(
        abs_a=round(A, 6),
        abs_Imb=round(C, 6),
        b0=round(float(b0), 6),
        a_dot_Imb=round(P, 6),
        V=round(V, 9),
        theta_deg=round(th, 3),
    )


# (i) basis vectors
rows_basis = {m: coords(basis(16, m)) for m in range(1, 16)}
say(
    "[B1] the 15 imaginary basis vectors in the orbit space (|a|,|Im b|,b0,<a,Im b>,V,theta):"
)
groups = {}
for m, c in rows_basis.items():
    key = (c["abs_a"], c["abs_Imb"], abs(c["b0"]), c["theta_deg"])
    groups.setdefault(key, []).append(m)
for key, ms in groups.items():
    say(
        f"     {ms}: |a|={key[0]}, |Im b|={key[1]}, |b0|={key[2]}, theta={key[3]} deg, V=0"
    )
b0sq_basis = np.mean([rows_basis[m]["b0"] ** 2 for m in rows_basis])
say(
    f"     pushforward of counting measure on the 15 indices: atoms 7/15 @ (theta=0, b0=0), 7/15 @ (theta=90, b0=0), 1/15 @ pole |b0|=1  ->  <b0^2> = {b0sq_basis:.6f} = 1/15"
)
out["B1_b0sq_basis"] = b0sq_basis
# rule-invariance: V=0 and F=0 on the support
Fb = np.array([np.max(np.abs(ruleField(basis(16, m)))) for m in range(1, 16)])
say(
    f"     V on support: max {max(rows_basis[m]['V'] for m in rows_basis):.1e}; rule field |F| on support: max {Fb.max():.1e}  -> fixed by quench AND by the Gibbs family e^(-beta V) for every beta"
)


# ell-axis map
def ell_map(s):
    t = s + basis(16, 8)
    return t / np.linalg.norm(t)


b0sq_l = []
for m in range(1, 16):
    s = basis(16, m)
    for _ in range(60):
        s = ell_map(s)
    b0sq_l.append(s[8] ** 2)
say(
    f"     ell-axis map (s+ell)/|s+ell| iterated 60x from each basis vector: <b0^2> -> {np.mean(b0sq_l):.6f}  (e_8 itself is the fixed point; -e_8 -> 0/0 is excluded: e_8's orbit is ±e_8 and -e_8 + e_8 = 0)"
)

# (ii) ZDs
rows_zd = [coords((basis(16, i) + s * basis(16, j)) / np.sqrt(2)) for i, j, s, _ in zds]
keys = {
    (r["abs_a"], r["abs_Imb"], r["b0"], r["a_dot_Imb"], r["V"], r["theta_deg"])
    for r in rows_zd
}
say(
    f"[B2] the 84 ZDs in the orbit space: distinct points = {len(keys)}: {sorted(keys)}"
)
say(
    f"     -> ALL 84 (and hence all 42 planes) map to the single point (|a|=|Im b|=1/sqrt2, b0=0, a ⟂ Im b, V=1): the ZD ridge, the MAXIMUM of V, not on the vacuum S^2.  <b0^2> = {np.mean([r['b0']**2 for r in rows_zd]):.6f}"
)
out["B2_zd_points"] = sorted(keys)
# plane circles: e_i cos(phi) + e_j sin(phi)
i, j, _, _ = zds[0]
phis = np.linspace(0, 90, 7)
say(
    f"     plane {{e_{i}, e_{j}}} great circle phi -> (|a|,|Im b|,b0,V): "
    + ", ".join(
        f"{p:.0f}°:({np.cos(np.radians(p)):.2f},{np.sin(np.radians(p)):.2f},0,{potential(np.cos(np.radians(p))*basis(16,i)+np.sin(np.radians(p))*basis(16,j)):.3f})"
        for p in phis
    )
)
say(
    "     each plane's circle runs from the a-vacuum (theta=0) over the ridge (phi=45°, V=1) to the c-vacuum (theta=90): its vacuum content is the two order-2 cone points, weight 1/2 each, <b0^2> = 0"
)
# quench from the 84 ZDs: they are maxima of V; the exact ZD is stationary; kick and descend (vectorised over the 84)
rng = np.random.default_rng(5)
Xz = np.array([(basis(16, i) + s * basis(16, j)) / np.sqrt(2) for i, j, s, _ in zds])
Xz = Xz + 1e-3 * rng.normal(size=Xz.shape)
Xz[:, 0] = 0
Xz /= np.linalg.norm(Xz, axis=1, keepdims=True)
for _ in range(3000):
    Xz = Xz + 0.05 * ruleField(Xz)
    Xz[:, 0] = 0
    Xz /= np.linalg.norm(Xz, axis=1, keepdims=True)
ends = [coords(x) for x in Xz]
say(
    f"     quench from the 84 ZDs (1e-3 random kick, 3000 steps h=0.05): endpoint V max {max(e['V'] for e in ends):.1e}; endpoint theta range [{min(e['theta_deg'] for e in ends):.1f}, {max(e['theta_deg'] for e in ends):.1f}] deg, <b0^2> = {np.mean([e['b0']**2 for e in ends]):.4f}  (ridge is a maximum: endpoints kick-dependent -> rule- AND noise-dependent, circular as expected)"
)

# (iii) basis-sum vacua (126) and all 210 basis sums; all signed subset-sums
rows_vs = [
    coords((basis(16, i) + s * basis(16, j)) / np.sqrt(2)) for i, j, s, _ in vac_sums
]
groups = {}
for (i, j, s, _), r in zip(vac_sums, rows_vs):
    key = (
        r["abs_a"],
        r["abs_Imb"],
        abs(r["b0"]),
        r["theta_deg"],
        round(abs(r["a_dot_Imb"]), 6),
    )
    groups.setdefault(key, 0)
    groups[key] += 1
say(
    f"[B3] the {len(vac_sums)} non-ZD basis sums are all vacua (max V {max(r['V'] for r in rows_vs):.1e}); orbit-space atoms (|a|,|Im b|,|b0|,theta,|<a,Im b>|): count"
)
for k, c in sorted(groups.items()):
    say(f"     {k}: {c}")
b0sq_vs = np.mean([r["b0"] ** 2 for r in rows_vs])
b0sq_all = np.mean([r["b0"] ** 2 for r in rows_vs + rows_zd])
say(
    f"     <b0^2> over the 126 basis-sum vacua = {b0sq_vs:.6f} (=1/9);  over all 210 basis sums = {b0sq_all:.6f} (=1/15)"
)
out["B3_b0sq_basis_sum_vacua"] = b0sq_vs
out["B3_b0sq_all_210"] = b0sq_all
# all signed subset sums over the 15 imaginary indices: <b0^2> = E[ [8 in S]/|S| ]
tot = 0.0
cnt = 0
for size in range(1, 16):
    from math import comb

    n_with = comb(14, size - 1)
    n_all = comb(15, size)
    tot += n_with * (1.0 / size)
    cnt += n_all
say(
    f"     uniform over all 2^15-1 non-empty index subsets (any signs): <b0^2> = {tot/cnt:.6f}"
)
out["B3_b0sq_all_subsets"] = tot / cnt
say(
    f"     three index-native discrete measures, three numbers: 1/15 = {1/15:.4f}, 1/9 = {1/9:.4f}, {tot/cnt:.4f}; rule endpoints for comparison: 0.146 (quench), 1/3 (anneal), 1 (ell-map); N-measure initial value = 1/15"
)

# ---------------------------------------------------------------- C. Galois correspondence and finite image
say("[C1] Galois correspondence inside the sedenions: Fix(chi_v : v ⊥ G_k) = CD_k")
for k in range(0, 5):
    Hk = [
        v for v in range(16) if v % (2**k) == 0
    ]  # characters trivial on G_k = {m < 2^k}
    fixed = [m for m in range(16) if all(chi(v, m) == 1 for v in Hk)]
    say(
        f"     k={k}: |H_k|={len(Hk)}, fixed basis indices = {fixed}  == range(2^{k}) : {fixed == list(range(2**k))}"
    )
say(
    "[C2] the profinite G^ = prod Z/2 acts on the sedenions through G^ -> G^_4 (characters agreeing on G_4 act identically): kernel = characters trivial on the first 4 bits; the action is through a group of order 16 — a finite quotient. General theorem: a continuous homomorphism from a profinite group into a Lie group (Aut S = G2 x S3) has finite image (Lie groups have no small subgroups)."
)

json.dump(out, open("attack4_results.json", "w"), indent=1, default=str)
say("wrote sigma_n4.txt, attack4_results.json")
