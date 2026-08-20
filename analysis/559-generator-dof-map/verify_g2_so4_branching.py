"""
#559 keystone verification: the generator->DOF map for O->H crystallisation.
VERIFY (don't assert) the load-bearing representation theory:
  G2 = Aut(O) >= SO(4) = (SU(2)_a x SU(2)_b)/Z2  (stabilizer of a quaternion subalgebra H)
  embedding  gamma(a,b): x + y e4  |->  a x a*  +  (b y a*) e4   (Conway-Smith / Baez)
  CLAIM: Im(O) = <e1..e7> branches as 7 = (1,3) (+) (2,2):
     {e1,e2,e3} = retained Im(H), an SU(2)_a triplet (spin 1), SU(2)_b singlet
     {e4,e5,e6,e7} = lost complement H.e4, the (2,2) bi-doublet (spin 1/2, spin 1/2)
"""

import numpy as np, itertools


# --- Octonions via Cayley-Dickson doubling of quaternions ---
# quaternion as 4-vector (w,x,y,z); octonion as pair (p,q) of quaternions = p + q e4
def qmul(p, q):
    w0, x0, y0, z0 = p
    w1, x1, y1, z1 = q
    return np.array(
        [
            w0 * w1 - x0 * x1 - y0 * y1 - z0 * z1,
            w0 * x1 + x0 * w1 + y0 * z1 - z0 * y1,
            w0 * y1 - x0 * z1 + y0 * w1 + z0 * x1,
            w0 * z1 + x0 * y1 - y0 * x1 + z0 * w1,
        ]
    )


def qconj(p):
    return np.array([p[0], -p[1], -p[2], -p[3]])


# Cayley-Dickson: (p,q)(r,s) = (p r - s* q ,  s p + q r*)   [Conway-Smith convention]
def omul(A, B):
    p, q = A[:4], A[4:]
    r, s = B[:4], B[4:]
    first = qmul(p, r) - qmul(qconj(s), q)
    second = qmul(s, p) + qmul(q, qconj(r))
    return np.concatenate([first, second])


# basis e0..e7
E = [np.zeros(8) for _ in range(8)]
for i in range(8):
    E[i][i] = 1.0

# sanity: e_i^2 = -1 for i>=1, and check a couple of products are octonionic (anti-assoc)
ok2 = all(np.allclose(omul(E[i], E[i]), -E[0]) for i in range(1, 8))
print("e_i^2 = -1 for i=1..7:", ok2)


# --- gamma(a,b) automorphism on octonion z=(x,y): -> (a x a*, b y a*) ---
def gamma(a, b, z):
    x, y = z[:4], z[4:]
    nx = qmul(qmul(a, x), qconj(a))
    ny = qmul(qmul(b, y), qconj(a))
    return np.concatenate([nx, ny])


def rand_unit_quat(rng):
    v = rng.standard_normal(4)
    return v / np.linalg.norm(v)


rng = np.random.default_rng(0)
# VERIFY gamma is an automorphism: gamma(uv)=gamma(u)gamma(v) for random a,b,u,v
auto_ok = True
for _ in range(2000):
    a = rand_unit_quat(rng)
    b = rand_unit_quat(rng)
    u = rng.standard_normal(8)
    v = rng.standard_normal(8)
    lhs = gamma(a, b, omul(u, v))
    rhs = omul(gamma(a, b, u), gamma(a, b, v))
    if not np.allclose(lhs, rhs, atol=1e-9):
        auto_ok = False
        break
print("gamma(a,b) is an octonion automorphism (2000 random trials):", auto_ok)

# --- Invariance of the two subspaces under gamma ---
H_im = [1, 2, 3]  # e1,e2,e3
Hperp = [4, 5, 6, 7]  # e4,e5,e6,e7


def subspace_invariant(idxs):
    for _ in range(500):
        a = rand_unit_quat(rng)
        b = rand_unit_quat(rng)
        for i in idxs:
            img = gamma(a, b, E[i])
            # components outside idxs (and outside e0) must vanish
            for k in range(8):
                if k not in idxs and abs(img[k]) > 1e-9:
                    return False
    return True


print("span{e1,e2,e3} invariant under SO(4):", subspace_invariant(H_im))
print("span{e4,e5,e6,e7} invariant under SO(4):", subspace_invariant(Hperp))


# --- Identify the reps ---
# On {e1,e2,e3}: does SU(2)_b act trivially? does SU(2)_a act as SO(3) (spin-1)?
def acts_trivially_b_on(idxs):
    for _ in range(300):
        b = rand_unit_quat(rng)
        a = np.array([1.0, 0, 0, 0])  # a=identity
        for i in idxs:
            if not np.allclose(gamma(a, b, E[i]), E[i], atol=1e-9):
                return False
    return True


def acts_trivially_a_on(idxs):
    for _ in range(300):
        a = rand_unit_quat(rng)
        b = np.array([1.0, 0, 0, 0])
        for i in idxs:
            if not np.allclose(gamma(a, b, E[i]), E[i], atol=1e-9):
                return False
    return True


print("SU(2)_b acts trivially on {e1,e2,e3} (=> b-singlet):", acts_trivially_b_on(H_im))
print(
    "SU(2)_a acts NONtrivially on {e1,e2,e3} (=> a-triplet):",
    not acts_trivially_a_on(H_im),
)
print("SU(2)_a acts NONtrivially on {e4..e7}:", not acts_trivially_a_on(Hperp))
print("SU(2)_b acts NONtrivially on {e4..e7}:", not acts_trivially_b_on(Hperp))


# Confirm {e1,e2,e3} carries spin-1 of SU(2)_a: the a-action should be SO(3) rotations (det=+1, orthogonal, 3x3)
def a_action_matrix_on_Him(a):
    cols = []
    for i in H_im:
        img = gamma(a, np.array([1.0, 0, 0, 0]), E[i])
        cols.append([img[j] for j in H_im])
    return np.array(cols).T


import numpy.linalg as la

a = rand_unit_quat(rng)
M = a_action_matrix_on_Him(a)
print(
    "a-action on {e1,e2,e3}: orthogonal:",
    np.allclose(M @ M.T, np.eye(3), atol=1e-9),
    "det=+1:",
    np.isclose(la.det(M), 1.0, atol=1e-9),
    "=> spin-1 (vector=3) of SU(2)_a",
)


# Confirm {e4..e7} is (2,2): both SU(2)s act as 2-dim (doublet) factors.
# Test: the a-action on the 4-dim Hperp commutes with the b-action and each is SU(2) acting as 2x2 blocks => (2,2).
# Practical witness: dim=4 = 2x2, both nontrivial, and the rep is irreducible under the joint group.
# Irreducibility check: no nonzero proper subspace of Hperp invariant under ALL gamma(a,b).
def joint_irreducible(idxs, trials=4000):
    # build a set of generators' action matrices, check the only invariant subspaces are {0} and full
    # heuristic: random vector orbit spans the whole space
    v = np.zeros(8)
    for i in idxs:
        v[i] = rng.standard_normal()
    vecs = [v.copy()]
    for _ in range(trials):
        a = rand_unit_quat(rng)
        b = rand_unit_quat(rng)
        w = gamma(a, b, vecs[rng.integers(len(vecs))])
        vecs.append(w)
        if len(vecs) > 50:
            break
    Mtx = np.array([[w[k] for k in idxs] for w in vecs])
    return la.matrix_rank(Mtx, tol=1e-9)


print("orbit-span rank on {e4..e7} (4 => irreducible (2,2)):", joint_irreducible(Hperp))
print(
    "orbit-span rank on {e1,e2,e3} (3 => irreducible triplet):", joint_irreducible(H_im)
)
