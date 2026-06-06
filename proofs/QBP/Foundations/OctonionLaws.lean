/-
  QBP.Foundations.OctonionLaws
  ============================

  The octonion (𝕆 = `CDAlg ℝ 3`) ✓-cells of the operations-complete matrix
  (#474 PR-C1): the *named structure laws that genuinely hold at 𝕆* — flexibility,
  the three Moufang identities, power-associativity, and norm composition
  (the multiplicativity half of Hurwitz at level 3).

  All of these are quadratic-or-worse in a repeated variable, so each is lifted
  from a finite integer basis fact through the multilinear metalemmas of
  `CDLifting` — exactly the merged polarized-alternativity pattern, one arity up:

    * **Flexibility** `(xy)x = x(yx)`:  the flexor `F(x,y,z) = (xy)z − x(yz)` is the
      associator, already trilinear (`assoc_trilinear`).  Polarized flexibility
      `[x,y,z] + [z,y,x] = 0` is a TRILINEAR basis fact (8³ ℤ-decide), lifted by
      `lift_trilinear_eq`, then specialized `z := x` (no division needed — the two
      diagonal terms are equal, giving `2·[x,y,x] = 0`, ÷2 confined to ℝ).

    * **Moufang ×3** `x(y(xz))=((xy)x)z`, `((zx)y)x=z(x(yx))`, `(xy)(zx)=x((yz)x)`:
      each is QUADRATIC in `x`.  Polarize the repeated `x` into two independent
      slots `a,b` and symmetrize → a genuinely QUADRILINEAR map `M(a,b,y,z)` with
      `M(x,x,y,z) = 2·(defect)`.  `M` vanishes on all 8⁴ = 4096 basis 4-tuples
      (kernel ℤ-decide), lifts by `lift_quadrilinear_eq`, diagonalize `a=b=x`,
      ÷2 in ℝ.  (Schafer, *An Introduction to Nonassociative Algebras*, §3.4;
      Conway–Smith, *On Quaternions and Octonions*, ch. 6 — the three standard
      Moufang identities in their usual left / right / middle forms.)

    * **Norm composition** `N(xy) = N(x)·N(y)`:  QUADRATIC in each of `x,y`.
      Route chosen (reported): the *bilinear-form polarization*.  Let
      `bil x y = ∑ xᵢyᵢ` be the polar form of `N` (`N x = bil x x`).  The
      4-linear map `M_N(a,b,c,d) = bil(ac)(bd) + bil(bc)(ad) − 2·bil a b·bil c d`
      has `M_N(x,x,y,y) = 2·(N(xy) − N x·N y)`.  Its basis value is an explicit
      integer (`normMoufCoeffZ`), vanishing on all 4096 4-tuples (ℤ-decide);
      lift, diagonalize, ÷2 in ℝ.

    * **Power-associativity** `x²·x = x·x²` and `(x²)² = x²·x²`:  immediate from
      flexibility (`x²x = x(xx) = (xx)x` by left/right alternativity) and from the
      quadratic identity; stated in the honest bounded forms 𝕆 supports.

  Completeness (federation Lean standard, ~/Documents/inter/lean-proof-best-practices.md):
  zero `sorry`, zero `native_decide`, zero vacuous `True`.  Every `decide` is the
  KERNEL `decide` (never `native_decide`).  Every ÷2 step is confined to ℝ via
  `two_ne_zero`.  `#print axioms` audit at the bottom — each main result depends
  only on `{propext, Classical.choice, Quot.sound}`.
-/
import QBP.Foundations.CDLifting

/- The multilinearity-instance proofs below are ~24 structurally identical field
   discharges (`simp only [<map>, mul_add_*, mul_smul_*, smul_sub, smul_add]; abel`).
   Per field, some bilinearity lemma in the uniform list is genuinely unused (e.g.
   additivity-in-slot-1 only fires `mul_add_left`).  We keep the uniform list for
   maintainability and disable the `unusedSimpArgs` STYLE linter for this file; this
   is not a soundness concern (the `decide`/`#print axioms` gates are untouched) and
   the simp calls remain terminal. -/
set_option linter.unusedSimpArgs false

namespace QBP.Foundations.CDAlg

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ## 1. Flexibility at 𝕆 (`(x·y)·x = x·(y·x)`)

The flexor is the associator `[x,y,z] = (xy)z − x(yz)`.  Flexibility is the
diagonal `[x,y,x] = 0`.  Its polarized (trilinear) form `[x,y,z] + [z,y,x] = 0`
is a basis fact, lifted by the trilinear keystone. -/

/-- Polarized-flexibility map `[x,y,z] + [z,y,x]`, trilinear (symmetrize slots 1,3). -/
def flMap (x y z : CDAlg R n) : CDAlg R n := assoc x y z + assoc z y x

theorem flMap_trilinear : IsTrilinear (flMap : CDAlg R n → _ → _ → _) where
  add_left x x' y z := by
    simp only [flMap, assoc_trilinear.add_left, assoc_trilinear.add_right]; abel
  smul_left r x y z := by
    simp only [flMap, assoc_trilinear.smul_left, assoc_trilinear.smul_right, smul_add]
  add_mid x y y' z := by
    simp only [flMap, assoc_trilinear.add_mid]; abel
  smul_mid r x y z := by
    simp only [flMap, assoc_trilinear.smul_mid, smul_add]
  add_right x y z z' := by
    simp only [flMap, assoc_trilinear.add_right, assoc_trilinear.add_left]; abel
  smul_right r x y z := by
    simp only [flMap, assoc_trilinear.smul_right, assoc_trilinear.smul_left, smul_add]

/-- **Integer basis fact (kernel `decide`).**  The octonion associator is
    flexible-alternating on all 8³ = 512 basis triples:
    `[eᵢ,e_j,e_k] + [e_k,e_j,eᵢ] = 0` at the integer-coefficient level. -/
theorem octonion_assocCoeffZ_flex :
    ∀ i j k : Fin (2^3), assocCoeffZ 3 i j k + assocCoeffZ 3 k j i = 0 := by decide

theorem octonion_flMap_basis (i j k : Fin (2^3)) :
    (flMap (e i) (e j) (e k) : CDAlg ℝ 3) = 0 := by
  rw [flMap, assoc_e, assoc_e]
  have h1 : (k ^^^ j ^^^ i : Fin (2^3)) = (i ^^^ j ^^^ k : Fin (2^3)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [h1, ← add_smul]
  rw [show ((assocCoeffZ 3 i j k : ℝ) + (assocCoeffZ 3 k j i : ℝ))
        = (((assocCoeffZ 3 i j k + assocCoeffZ 3 k j i : Int)) : ℝ) by push_cast; ring,
     octonion_assocCoeffZ_flex i j k]
  simp

/-- **Octonion flexibility, polarized form** (lifted): `[x,y,z] + [z,y,x] = 0`. -/
theorem octonion_flexible_polarized (x y z : CDAlg ℝ 3) :
    assoc x y z + assoc z y x = 0 :=
  lift_trilinear_eq flMap_trilinear octonion_flMap_basis x y z

theorem assoc_diag_flex (x y : CDAlg ℝ 3) : assoc x y x = 0 := by
  have h2 : (2 : ℝ) • assoc x y x = 0 := by
    rw [two_smul]; exact octonion_flexible_polarized x y x
  rcases smul_eq_zero.mp h2 with hz | hz
  · exact absurd hz two_ne_zero
  · exact hz

/-- **PAYOFF: octonion flexibility.**  𝕆 = `CDAlg ℝ 3` is flexible:
    for all `x y`, `(x·y)·x = x·(y·x)`.  (Equivalently the associator
    `[x,y,x] = 0`.)  Lifted from `octonion_assocCoeffZ_flex` via the trilinear
    keystone, ÷2 confined to ℝ. -/
theorem octonion_flexible (x y : CDAlg ℝ 3) : (x * y) * x = x * (y * x) := by
  have := assoc_diag_flex x y; rwa [assoc, sub_eq_zero] at this

/-! ## 2. Moufang identities at 𝕆 — quadrilinear polarization machinery

Each Moufang identity is quadratic in `x`.  We define, for each, the 4-linear
*defect-polarization* map `M(a,b,y,z)` obtained by splitting the two `x`
occurrences into independent slots `a,b` and symmetrizing.  Quadrilinearity comes
straight from bilinearity of `*` (six `mul_add_*`/`mul_smul_*` rewrites per slot).
The basis vanishing is a 4096-case ℤ-decide on an integer coefficient. -/

/-! ### 2a. Left Moufang `x·(y·(x·z)) = ((x·y)·x)·z`

Defect `D_L(x,y,z) = x(y(xz)) − ((xy)x)z`.  Polarize `x → a,b`:
`M_L(a,b,y,z) = a(y(bz)) − ((ay)b)z + b(y(az)) − ((by)a)z`, with
`M_L(x,x,y,z) = 2·D_L(x,y,z)`. -/

/-- Left-Moufang polarization map (4-linear; diagonal = `2 ·` left-Moufang defect). -/
def mLeftMap (a b y z : CDAlg R n) : CDAlg R n :=
  (a * (y * (b * z)) - ((a * y) * b) * z) + (b * (y * (a * z)) - ((b * y) * a) * z)

theorem mLeftMap_quadrilinear : IsQuadrilinear (mLeftMap : CDAlg R n → _ → _ → _ → _) where
  add_1 w w' x y z := by
    simp only [mLeftMap, mul_add_left, mul_add_right]; abel
  smul_1 r w x y z := by
    simp only [mLeftMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_2 w x x' y z := by
    simp only [mLeftMap, mul_add_left, mul_add_right]; abel
  smul_2 r w x y z := by
    simp only [mLeftMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_3 w x y y' z := by
    simp only [mLeftMap, mul_add_left, mul_add_right]; abel
  smul_3 r w x y z := by
    simp only [mLeftMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_4 w x y z z' := by
    simp only [mLeftMap, mul_add_left, mul_add_right]; abel
  smul_4 r w x y z := by
    simp only [mLeftMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]

/-! ### 2b. Right Moufang `((z·x)·y)·x = z·(x·(y·x))`

Defect `D_R(x,y,z) = ((zx)y)x − z(x(yx))`.  Polarize `x → a,b`:
`M_R(a,b,y,z) = ((za)y)b − z(a(yb)) + ((zb)y)a − z(b(ya))`. -/

/-- Right-Moufang polarization map (4-linear; diagonal = `2 ·` right-Moufang defect).
    Slots are `(a, b, y, z)`. -/
def mRightMap (a b y z : CDAlg R n) : CDAlg R n :=
  (((z * a) * y) * b - z * (a * (y * b))) + (((z * b) * y) * a - z * (b * (y * a)))

theorem mRightMap_quadrilinear : IsQuadrilinear (mRightMap : CDAlg R n → _ → _ → _ → _) where
  add_1 w w' x y z := by
    simp only [mRightMap, mul_add_left, mul_add_right]; abel
  smul_1 r w x y z := by
    simp only [mRightMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_2 w x x' y z := by
    simp only [mRightMap, mul_add_left, mul_add_right]; abel
  smul_2 r w x y z := by
    simp only [mRightMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_3 w x y y' z := by
    simp only [mRightMap, mul_add_left, mul_add_right]; abel
  smul_3 r w x y z := by
    simp only [mRightMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_4 w x y z z' := by
    simp only [mRightMap, mul_add_left, mul_add_right]; abel
  smul_4 r w x y z := by
    simp only [mRightMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]

/-! ### 2c. Middle Moufang `(x·y)·(z·x) = x·((y·z)·x)`

Defect `D_M(x,y,z) = (xy)(zx) − x((yz)x)`.  Polarize `x → a,b`:
`M_M(a,b,y,z) = (ay)(zb) − a((yz)b) + (by)(za) − b((yz)a)`. -/

/-- Middle-Moufang polarization map (4-linear; diagonal = `2 ·` middle-Moufang
    defect).  Slots are `(a, b, y, z)`. -/
def mMidMap (a b y z : CDAlg R n) : CDAlg R n :=
  ((a * y) * (z * b) - a * ((y * z) * b)) + ((b * y) * (z * a) - b * ((y * z) * a))

theorem mMidMap_quadrilinear : IsQuadrilinear (mMidMap : CDAlg R n → _ → _ → _ → _) where
  add_1 w w' x y z := by
    simp only [mMidMap, mul_add_left, mul_add_right]; abel
  smul_1 r w x y z := by
    simp only [mMidMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_2 w x x' y z := by
    simp only [mMidMap, mul_add_left, mul_add_right]; abel
  smul_2 r w x y z := by
    simp only [mMidMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_3 w x y y' z := by
    simp only [mMidMap, mul_add_left, mul_add_right]; abel
  smul_3 r w x y z := by
    simp only [mMidMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]
  add_4 w x y z z' := by
    simp only [mMidMap, mul_add_left, mul_add_right]; abel
  smul_4 r w x y z := by
    simp only [mMidMap, mul_smul_left, mul_smul_right, smul_sub, smul_add]

/-! ### 2d. Generic basis-product bracketing lemmas

Each Moufang map sends a basis 4-tuple to an integer multiple of a single basis
vector (`a⊕b⊕y⊕z`, the same for every term since XOR is associative-commutative).

Every nested product of basis vectors collapses to a single `mulCoeff`-product
times one basis vector.  We give the two bracketings of a triple product and the
four bracketings of a quadruple product that the Moufang terms use.  The XOR
target is always normalised to the fully-left-associated `i⊕j⊕k(⊕l)`; mismatched
bracketings are reconciled with `Fin.ext; ac_rfl` (XOR is associative-commutative).
All scalar coefficients live in `R` via `push_cast`-free `Int`→`R` coercion. -/

/-- `(eᵢ·e_j)·e_k = mc i j · mc (i⊕j) k • e_{i⊕j⊕k}`. -/
theorem e3_LL (i j k : Fin (2^n)) :
    (((e i) * (e j)) * (e k) : CDAlg R n)
      = ((mulCoeff n i j * mulCoeff n (i ^^^ j) k : Int) : R) • e (i ^^^ j ^^^ k) := by
  rw [e_mul_e, mul_smul_left, e_mul_e, smul_smul]; push_cast; ring_nf

/-- `eᵢ·(e_j·e_k) = mc j k · mc i (j⊕k) • e_{i⊕j⊕k}`. -/
theorem e3_LR (i j k : Fin (2^n)) :
    ((e i) * ((e j) * (e k)) : CDAlg R n)
      = ((mulCoeff n j k * mulCoeff n i (j ^^^ k) : Int) : R) • e (i ^^^ j ^^^ k) := by
  rw [e_mul_e, mul_smul_right, e_mul_e, smul_smul]
  have hx : (i ^^^ (j ^^^ k) : Fin (2^n)) = (i ^^^ j ^^^ k : Fin (2^n)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [hx]; push_cast; ring_nf

/-- `((eᵢ·e_j)·e_k)·e_l`, fully left-associated. -/
theorem e4_LLL (i j k l : Fin (2^n)) :
    ((((e i) * (e j)) * (e k)) * (e l) : CDAlg R n)
      = ((mulCoeff n i j * mulCoeff n (i ^^^ j) k * mulCoeff n (i ^^^ j ^^^ k) l : Int) : R)
        • e (i ^^^ j ^^^ k ^^^ l) := by
  rw [e3_LL, mul_smul_left, e_mul_e, smul_smul]; push_cast; ring_nf

/-- `eᵢ·(e_j·(e_k·e_l))`, fully right-associated. -/
theorem e4_RRR (i j k l : Fin (2^n)) :
    ((e i) * ((e j) * ((e k) * (e l))) : CDAlg R n)
      = ((mulCoeff n k l * mulCoeff n j (k ^^^ l) * mulCoeff n i (j ^^^ (k ^^^ l)) : Int) : R)
        • e (i ^^^ j ^^^ k ^^^ l) := by
  rw [e3_LR, mul_smul_right, e_mul_e, smul_smul]
  have hx : (i ^^^ (j ^^^ k ^^^ l) : Fin (2^n)) = (i ^^^ j ^^^ k ^^^ l : Fin (2^n)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  have hy : (j ^^^ (k ^^^ l) : Fin (2^n)) = (j ^^^ k ^^^ l : Fin (2^n)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [hx, hy]; push_cast; ring_nf

/-- `(eᵢ·e_j)·(e_k·e_l)`, the "middle" bracketing. -/
theorem e4_LLRR (i j k l : Fin (2^n)) :
    (((e i) * (e j)) * ((e k) * (e l)) : CDAlg R n)
      = ((mulCoeff n i j * mulCoeff n k l * mulCoeff n (i ^^^ j) (k ^^^ l) : Int) : R)
        • e (i ^^^ j ^^^ k ^^^ l) := by
  rw [e_mul_e, e_mul_e, mul_smul_left, mul_smul_right, e_mul_e, smul_smul, smul_smul]
  have hx : ((i ^^^ j) ^^^ (k ^^^ l) : Fin (2^n)) = (i ^^^ j ^^^ k ^^^ l : Fin (2^n)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [hx]; push_cast; ring_nf

/-- `eᵢ·((e_j·e_k)·e_l)`, the "outer-left inner" bracketing used by middle Moufang. -/
theorem e4_LRLL (i j k l : Fin (2^n)) :
    ((e i) * (((e j) * (e k)) * (e l)) : CDAlg R n)
      = ((mulCoeff n j k * mulCoeff n (j ^^^ k) l * mulCoeff n i (j ^^^ k ^^^ l) : Int) : R)
        • e (i ^^^ j ^^^ k ^^^ l) := by
  rw [e3_LL, mul_smul_right, e_mul_e, smul_smul]
  have hx : (i ^^^ (j ^^^ k ^^^ l) : Fin (2^n)) = (i ^^^ j ^^^ k ^^^ l : Fin (2^n)) := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [hx]; push_cast; ring_nf

/-! ### 2f. Integer coefficient of each Moufang polarization map on basis 4-tuples

For each map we collect the per-term coefficients (signs are `+,+` from the two
symmetrized halves, and each half is `(first term) − (second term)`).  The basis
value is `coeff • e (a⊕b⊕y⊕z)`; vanishing on all 8⁴ tuples is the ℤ-decide. -/

/-- Integer coefficient of `mLeftMap (eₐ)(e_b)(e_y)(e_z)`.  Slots `(a,b,y,z)`. -/
def mLeftCoeffZ (n : ℕ) (a b y z : Fin (2^n)) : Int :=
  (mulCoeff n b z * mulCoeff n y (b ^^^ z) * mulCoeff n a (y ^^^ b ^^^ z)
    - mulCoeff n a y * mulCoeff n (a ^^^ y) b * mulCoeff n (a ^^^ y ^^^ b) z)
  + (mulCoeff n a z * mulCoeff n y (a ^^^ z) * mulCoeff n b (y ^^^ a ^^^ z)
    - mulCoeff n b y * mulCoeff n (b ^^^ y) a * mulCoeff n (b ^^^ y ^^^ a) z)

theorem mLeftMap_e (i j k l : Fin (2^3)) :
    (mLeftMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3)
      = ((mLeftCoeffZ 3 i j k l : Int) : ℝ) • e (i ^^^ j ^^^ k ^^^ l) := by
  -- mLeftMap a b y z = (a(y(bz)) − ((ay)b)z) + (b(y(az)) − ((by)a)z), slots a=i b=j y=k z=l
  unfold mLeftMap
  -- term 1: i·(k·(j·l)) = e4_RRR i k j l with target i⊕k⊕j⊕l
  rw [show (e i) * ((e k) * ((e j) * (e l)))
        = ((mulCoeff 3 j l * mulCoeff 3 k (j ^^^ l)
              * mulCoeff 3 i (k ^^^ (j ^^^ l)) : Int) : ℝ) • e (i ^^^ k ^^^ j ^^^ l) from
      e4_RRR i k j l]
  rw [show ((e i) * (e k)) * (e j) * (e l)
        = ((mulCoeff 3 i k * mulCoeff 3 (i ^^^ k) j
              * mulCoeff 3 (i ^^^ k ^^^ j) l : Int) : ℝ) • e (i ^^^ k ^^^ j ^^^ l) from
      e4_LLL i k j l]
  rw [show (e j) * ((e k) * ((e i) * (e l)))
        = ((mulCoeff 3 i l * mulCoeff 3 k (i ^^^ l)
              * mulCoeff 3 j (k ^^^ (i ^^^ l)) : Int) : ℝ) • e (j ^^^ k ^^^ i ^^^ l) from
      e4_RRR j k i l]
  rw [show ((e j) * (e k)) * (e i) * (e l)
        = ((mulCoeff 3 j k * mulCoeff 3 (j ^^^ k) i
              * mulCoeff 3 (j ^^^ k ^^^ i) l : Int) : ℝ) • e (j ^^^ k ^^^ i ^^^ l) from
      e4_LLL j k i l]
  have t1 : (i ^^^ k ^^^ j ^^^ l : Fin (2^3)) = i ^^^ j ^^^ k ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  have t2 : (j ^^^ k ^^^ i ^^^ l : Fin (2^3)) = i ^^^ j ^^^ k ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [t1, t2, mLeftCoeffZ]
  rw [← sub_smul, ← sub_smul, ← add_smul]
  congr 1
  push_cast
  have e1 : (k ^^^ (j ^^^ l) : Fin (2^3)) = k ^^^ j ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  have e2 : (k ^^^ (i ^^^ l) : Fin (2^3)) = k ^^^ i ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [e1, e2]

/-- Integer coefficient of `mRightMap (eₐ)(e_b)(e_y)(e_z)`.  Slots `(a,b,y,z)`.
    Defect `((za)y)b − z(a(yb)) + ((zb)y)a − z(b(ya))`. -/
def mRightCoeffZ (n : ℕ) (a b y z : Fin (2^n)) : Int :=
  (mulCoeff n z a * mulCoeff n (z ^^^ a) y * mulCoeff n (z ^^^ a ^^^ y) b
    - mulCoeff n y b * mulCoeff n a (y ^^^ b) * mulCoeff n z (a ^^^ y ^^^ b))
  + (mulCoeff n z b * mulCoeff n (z ^^^ b) y * mulCoeff n (z ^^^ b ^^^ y) a
    - mulCoeff n y a * mulCoeff n b (y ^^^ a) * mulCoeff n z (b ^^^ y ^^^ a))

theorem mRightMap_e (i j k l : Fin (2^3)) :
    (mRightMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3)
      = ((mRightCoeffZ 3 i j k l : Int) : ℝ) • e (i ^^^ j ^^^ k ^^^ l) := by
  -- mRightMap a b y z = (((za)y)b − z(a(yb))) + (((zb)y)a − z(b(ya))), a=i b=j y=k z=l
  unfold mRightMap
  rw [show ((e l) * (e i)) * (e k) * (e j)
        = ((mulCoeff 3 l i * mulCoeff 3 (l ^^^ i) k
              * mulCoeff 3 (l ^^^ i ^^^ k) j : Int) : ℝ) • e (l ^^^ i ^^^ k ^^^ j) from
      e4_LLL l i k j]
  rw [show (e l) * ((e i) * ((e k) * (e j)))
        = ((mulCoeff 3 k j * mulCoeff 3 i (k ^^^ j)
              * mulCoeff 3 l (i ^^^ (k ^^^ j)) : Int) : ℝ) • e (l ^^^ i ^^^ k ^^^ j) from
      e4_RRR l i k j]
  rw [show ((e l) * (e j)) * (e k) * (e i)
        = ((mulCoeff 3 l j * mulCoeff 3 (l ^^^ j) k
              * mulCoeff 3 (l ^^^ j ^^^ k) i : Int) : ℝ) • e (l ^^^ j ^^^ k ^^^ i) from
      e4_LLL l j k i]
  rw [show (e l) * ((e j) * ((e k) * (e i)))
        = ((mulCoeff 3 k i * mulCoeff 3 j (k ^^^ i)
              * mulCoeff 3 l (j ^^^ (k ^^^ i)) : Int) : ℝ) • e (l ^^^ j ^^^ k ^^^ i) from
      e4_RRR l j k i]
  have t1 : (l ^^^ i ^^^ k ^^^ j : Fin (2^3)) = i ^^^ j ^^^ k ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  have t2 : (l ^^^ j ^^^ k ^^^ i : Fin (2^3)) = i ^^^ j ^^^ k ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [t1, t2, mRightCoeffZ]
  rw [← sub_smul, ← sub_smul, ← add_smul]
  congr 1
  push_cast
  have e1 : (i ^^^ (k ^^^ j) : Fin (2^3)) = i ^^^ k ^^^ j := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  have e2 : (j ^^^ (k ^^^ i) : Fin (2^3)) = j ^^^ k ^^^ i := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  -- mRightCoeffZ uses (z⊕a)=(l⊕i), (z⊕a⊕y)=(l⊕i⊕k), (a⊕y⊕b)=(i⊕k⊕j),
  -- (z⊕b)=(l⊕j), (z⊕b⊕y)=(l⊕j⊕k), (b⊕y⊕a)=(j⊕k⊕i): all already left-assoc; rw closes by rfl
  rw [e1, e2]

/-- Integer coefficient of `mMidMap (eₐ)(e_b)(e_y)(e_z)`.  Slots `(a,b,y,z)`.
    Defect `(ay)(zb) − a((yz)b) + (by)(za) − b((yz)a)`. -/
def mMidCoeffZ (n : ℕ) (a b y z : Fin (2^n)) : Int :=
  (mulCoeff n a y * mulCoeff n z b * mulCoeff n (a ^^^ y) (z ^^^ b)
    - mulCoeff n y z * mulCoeff n (y ^^^ z) b * mulCoeff n a (y ^^^ z ^^^ b))
  + (mulCoeff n b y * mulCoeff n z a * mulCoeff n (b ^^^ y) (z ^^^ a)
    - mulCoeff n y z * mulCoeff n (y ^^^ z) a * mulCoeff n b (y ^^^ z ^^^ a))

theorem mMidMap_e (i j k l : Fin (2^3)) :
    (mMidMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3)
      = ((mMidCoeffZ 3 i j k l : Int) : ℝ) • e (i ^^^ j ^^^ k ^^^ l) := by
  -- mMidMap a b y z = ((ay)(zb) − a((yz)b)) + ((by)(za) − b((yz)a)), a=i b=j y=k z=l
  unfold mMidMap
  rw [show ((e i) * (e k)) * ((e l) * (e j))
        = ((mulCoeff 3 i k * mulCoeff 3 l j
              * mulCoeff 3 (i ^^^ k) (l ^^^ j) : Int) : ℝ) • e (i ^^^ k ^^^ l ^^^ j) from
      e4_LLRR i k l j]
  rw [show (e i) * (((e k) * (e l)) * (e j))
        = ((mulCoeff 3 k l * mulCoeff 3 (k ^^^ l) j
              * mulCoeff 3 i (k ^^^ l ^^^ j) : Int) : ℝ) • e (i ^^^ k ^^^ l ^^^ j) from
      e4_LRLL i k l j]
  rw [show ((e j) * (e k)) * ((e l) * (e i))
        = ((mulCoeff 3 j k * mulCoeff 3 l i
              * mulCoeff 3 (j ^^^ k) (l ^^^ i) : Int) : ℝ) • e (j ^^^ k ^^^ l ^^^ i) from
      e4_LLRR j k l i]
  rw [show (e j) * (((e k) * (e l)) * (e i))
        = ((mulCoeff 3 k l * mulCoeff 3 (k ^^^ l) i
              * mulCoeff 3 j (k ^^^ l ^^^ i) : Int) : ℝ) • e (j ^^^ k ^^^ l ^^^ i) from
      e4_LRLL j k l i]
  have t1 : (i ^^^ k ^^^ l ^^^ j : Fin (2^3)) = i ^^^ j ^^^ k ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  have t2 : (j ^^^ k ^^^ l ^^^ i : Fin (2^3)) = i ^^^ j ^^^ k ^^^ l := by
    apply Fin.ext; simp only [Fin.xor_val_of_two_pow]; ac_rfl
  rw [t1, t2, mMidCoeffZ]
  rw [← sub_smul, ← sub_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-! ### 2g. Integer basis facts (kernel `decide`) and the lifts

Each Moufang polarization coefficient vanishes on ALL 8⁴ = 4096 basis 4-tuples.
These are the three big kernel ℤ-`decide`s (no `native_decide`). -/

/-- **Integer basis fact (kernel `decide`, 4096 cases).**  The left-Moufang
    polarization vanishes on every octonion basis 4-tuple. -/
theorem octonion_mLeftCoeffZ_zero :
    ∀ a b y z : Fin (2^3), mLeftCoeffZ 3 a b y z = 0 := by decide

/-- **Integer basis fact (kernel `decide`, 4096 cases).**  The right-Moufang
    polarization vanishes on every octonion basis 4-tuple. -/
theorem octonion_mRightCoeffZ_zero :
    ∀ a b y z : Fin (2^3), mRightCoeffZ 3 a b y z = 0 := by decide

/-- **Integer basis fact (kernel `decide`, 4096 cases).**  The middle-Moufang
    polarization vanishes on every octonion basis 4-tuple. -/
theorem octonion_mMidCoeffZ_zero :
    ∀ a b y z : Fin (2^3), mMidCoeffZ 3 a b y z = 0 := by decide

theorem mLeftMap_basis (i j k l : Fin (2^3)) :
    (mLeftMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3) = 0 := by
  rw [mLeftMap_e, octonion_mLeftCoeffZ_zero]; simp

theorem mRightMap_basis (i j k l : Fin (2^3)) :
    (mRightMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3) = 0 := by
  rw [mRightMap_e, octonion_mRightCoeffZ_zero]; simp

theorem mMidMap_basis (i j k l : Fin (2^3)) :
    (mMidMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3) = 0 := by
  rw [mMidMap_e, octonion_mMidCoeffZ_zero]; simp

/-- The left-Moufang polarization vanishes everywhere (quadrilinear lift). -/
theorem octonion_mLeftMap_zero (a b y z : CDAlg ℝ 3) : mLeftMap a b y z = 0 :=
  lift_quadrilinear_eq mLeftMap_quadrilinear mLeftMap_basis a b y z

/-- The right-Moufang polarization vanishes everywhere (quadrilinear lift). -/
theorem octonion_mRightMap_zero (a b y z : CDAlg ℝ 3) : mRightMap a b y z = 0 :=
  lift_quadrilinear_eq mRightMap_quadrilinear mRightMap_basis a b y z

/-- The middle-Moufang polarization vanishes everywhere (quadrilinear lift). -/
theorem octonion_mMidMap_zero (a b y z : CDAlg ℝ 3) : mMidMap a b y z = 0 :=
  lift_quadrilinear_eq mMidMap_quadrilinear mMidMap_basis a b y z

/-! ### 2h. Diagonalize `a = b = x` (÷2 confined to ℝ) → the Moufang identities -/

/-- **Octonion LEFT Moufang identity.**  𝕆 = `CDAlg ℝ 3` satisfies
    `x·(y·(x·z)) = ((x·y)·x)·z` for all `x y z`.  (Schafer §3.4 / Conway–Smith
    ch. 6, left Moufang.)  Lifted from `octonion_mLeftCoeffZ_zero` via the
    quadrilinear keystone; the repeated `x` is recovered by diagonalizing the
    polarization (`mLeftMap x x y z = 2·defect`), ÷2 confined to ℝ. -/
theorem octonion_moufang_left (x y z : CDAlg ℝ 3) :
    x * (y * (x * z)) = ((x * y) * x) * z := by
  have hpol : mLeftMap x x y z = 0 := octonion_mLeftMap_zero x x y z
  -- mLeftMap x x y z = 2 · (x(y(xz)) − ((xy)x)z)
  have hdiag : mLeftMap x x y z
      = (2 : ℝ) • (x * (y * (x * z)) - ((x * y) * x) * z) := by
    unfold mLeftMap; rw [two_smul]
  rw [hdiag] at hpol
  rcases smul_eq_zero.mp hpol with hz | hz
  · exact absurd hz two_ne_zero
  · rw [sub_eq_zero] at hz; exact hz

/-- **Octonion RIGHT Moufang identity.**  `((z·x)·y)·x = z·(x·(y·x))`.
    (Schafer §3.4 / Conway–Smith ch. 6, right Moufang.) -/
theorem octonion_moufang_right (x y z : CDAlg ℝ 3) :
    ((z * x) * y) * x = z * (x * (y * x)) := by
  have hpol : mRightMap x x y z = 0 := octonion_mRightMap_zero x x y z
  have hdiag : mRightMap x x y z
      = (2 : ℝ) • (((z * x) * y) * x - z * (x * (y * x))) := by
    unfold mRightMap; rw [two_smul]
  rw [hdiag] at hpol
  rcases smul_eq_zero.mp hpol with hz | hz
  · exact absurd hz two_ne_zero
  · rw [sub_eq_zero] at hz; exact hz

/-- **Octonion MIDDLE Moufang identity.**  `(x·y)·(z·x) = x·((y·z)·x)`.
    (Schafer §3.4 / Conway–Smith ch. 6, middle Moufang.) -/
theorem octonion_moufang_middle (x y z : CDAlg ℝ 3) :
    (x * y) * (z * x) = x * ((y * z) * x) := by
  have hpol : mMidMap x x y z = 0 := octonion_mMidMap_zero x x y z
  have hdiag : mMidMap x x y z
      = (2 : ℝ) • ((x * y) * (z * x) - x * ((y * z) * x)) := by
    unfold mMidMap; rw [two_smul]
  rw [hdiag] at hpol
  rcases smul_eq_zero.mp hpol with hz | hz
  · exact absurd hz two_ne_zero
  · rw [sub_eq_zero] at hz; exact hz

/-! ## 3. Norm composition at 𝕆 (`N(x·y) = N x · N y`) — Hurwitz multiplicativity

Route (reported): bilinear-form polarization.  `bil x y = ∑ xᵢyᵢ` is the polar
form of `N` (`N x = bil x x`).  The 4-linear map
`M_N(a,b,c,d) = bil(ac)(bd) + bil(bc)(ad) − 2·bil a b·bil c d` has
`M_N(x,x,y,y) = 2·(N(xy) − N x·N y)`.  Basis value is an explicit integer
(`normCoeffZ`); vanishing on all 4096 4-tuples is the fourth ℤ-decide. -/

/-- The polar bilinear form of `N`:  `bil x y = ∑ᵢ xᵢ·yᵢ`.  `N x = bil x x`. -/
def bil (x y : CDAlg R n) : R := ∑ i, x.coord i * y.coord i

@[simp] theorem bil_def (x y : CDAlg R n) : bil x y = ∑ i, x.coord i * y.coord i := rfl

theorem N_eq_bil (x : CDAlg R n) : N x = bil x x := by
  simp only [N_def, bil_def]; exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `bil` is additive in the left slot. -/
theorem bil_add_left (x x' y : CDAlg R n) : bil (x + x') y = bil x y + bil x' y := by
  simp only [bil_def, add_coord, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `bil` is additive in the right slot. -/
theorem bil_add_right (x y y' : CDAlg R n) : bil x (y + y') = bil x y + bil x y' := by
  simp only [bil_def, add_coord, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `bil` is `R`-homogeneous in the left slot. -/
theorem bil_smul_left (r : R) (x y : CDAlg R n) : bil (r • x) y = r * bil x y := by
  simp only [bil_def, smul_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `bil` is `R`-homogeneous in the right slot. -/
theorem bil_smul_right (r : R) (x y : CDAlg R n) : bil x (r • y) = r * bil x y := by
  simp only [bil_def, smul_coord, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `bil` on basis vectors is the Kronecker delta:  `bil eᵢ e_j = δᵢⱼ`. -/
theorem bil_e (i j : Fin (2^n)) : (bil (e i) (e j) : R) = if i = j then 1 else 0 := by
  simp only [bil_def, e_coord]
  rw [Finset.sum_eq_single i]
  · -- summand at i is (e i).coord i · (e j).coord i = 1 · (if i = j) = if i = j
    rw [if_pos rfl, one_mul]
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The norm-composition polarization map, cast into `CDAlg` as a scalar multiple
    of `e₀` so the quadrilinear lifting metalemma applies:
    `M_N(a,b,c,d) = (bil(ac)(bd) + bil(bc)(ad) − 2·bil a b·bil c d) • e₀`. -/
def normMap (a b c d : CDAlg R n) : CDAlg R n :=
  (bil (a * c) (b * d) + bil (b * c) (a * d) - 2 * bil a b * bil c d) • (e 0)

theorem normMap_quadrilinear : IsQuadrilinear (normMap : CDAlg R n → _ → _ → _ → _) where
  add_1 w w' x y z := by
    simp only [normMap, mul_add_left, bil_add_left, bil_add_right]
    rw [← add_smul]; congr 1; ring
  smul_1 r w x y z := by
    simp only [normMap, mul_smul_left, bil_smul_left, bil_smul_right, smul_smul]
    congr 1; ring
  add_2 w x x' y z := by
    simp only [normMap, mul_add_left, bil_add_left, bil_add_right]
    rw [← add_smul]; congr 1; ring
  smul_2 r w x y z := by
    simp only [normMap, mul_smul_left, bil_smul_left, bil_smul_right, smul_smul]
    congr 1; ring
  add_3 w x y y' z := by
    simp only [normMap, mul_add_right, bil_add_left, bil_add_right]
    rw [← add_smul]; congr 1; ring
  smul_3 r w x y z := by
    simp only [normMap, mul_smul_right, bil_smul_left, bil_smul_right, smul_smul]
    congr 1; ring
  add_4 w x y z z' := by
    simp only [normMap, mul_add_right, bil_add_left, bil_add_right]
    rw [← add_smul]; congr 1; ring
  smul_4 r w x y z := by
    simp only [normMap, mul_smul_right, bil_smul_left, bil_smul_right, smul_smul]
    congr 1; ring

/-- Integer norm-composition coefficient on basis 4-tuples.
    `bil(eᵢ e_k)(e_j e_l) = mc i k · mc j l · δ_{i⊕k, j⊕l}` (etc.), and
    `bil eᵢ e_j = δᵢⱼ`. -/
def normCoeffZ (n : ℕ) (i j k l : Fin (2^n)) : Int :=
  (mulCoeff n i k * mulCoeff n j l * (if (i ^^^ k) = (j ^^^ l) then 1 else 0)
    + mulCoeff n j k * mulCoeff n i l * (if (j ^^^ k) = (i ^^^ l) then 1 else 0))
  - 2 * (if i = j then 1 else 0) * (if k = l then 1 else 0)

theorem normMap_e (i j k l : Fin (2^3)) :
    (normMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3)
      = ((normCoeffZ 3 i j k l : Int) : ℝ) • e 0 := by
  unfold normMap
  rw [e_mul_e, e_mul_e, e_mul_e, e_mul_e]
  rw [bil_smul_left, bil_smul_right, bil_smul_left, bil_smul_right]
  rw [bil_e, bil_e, bil_e, bil_e]
  rw [normCoeffZ]
  congr 1
  push_cast
  ring

/-- **Integer basis fact (kernel `decide`, 4096 cases).**  The norm-composition
    polarization vanishes on every octonion basis 4-tuple. -/
theorem octonion_normCoeffZ_zero :
    ∀ i j k l : Fin (2^3), normCoeffZ 3 i j k l = 0 := by decide

theorem normMap_basis (i j k l : Fin (2^3)) :
    (normMap (e i) (e j) (e k) (e l) : CDAlg ℝ 3) = 0 := by
  rw [normMap_e, octonion_normCoeffZ_zero]; simp

/-- The norm-composition polarization vanishes everywhere (quadrilinear lift). -/
theorem octonion_normMap_zero (a b c d : CDAlg ℝ 3) : normMap a b c d = 0 :=
  lift_quadrilinear_eq normMap_quadrilinear normMap_basis a b c d

/-- The `e₀`-coordinate of `normMap a b c d` is the scalar defect. -/
theorem normMap_coord0 (a b c d : CDAlg ℝ 3) :
    (normMap a b c d).coord 0 = bil (a * c) (b * d) + bil (b * c) (a * d) - 2 * bil a b * bil c d := by
  rw [normMap, smul_coord, e_coord, if_pos rfl, mul_one]

/-- **PAYOFF: octonion norm composition (Hurwitz multiplicativity at 𝕆).**
    For all `x y : CDAlg ℝ 3`, the norm FORM `N` is multiplicative:
    `N(x·y) = N x · N y`.  Lifted from `octonion_normCoeffZ_zero` via the
    quadrilinear keystone (bilinear-form polarization), diagonalized `a=b=x`,
    `c=d=y`, ÷2 confined to ℝ.  (This is the composition-algebra / Hurwitz
    property; with division it is what makes 𝕆 a normed division algebra.) -/
theorem octonion_norm_composition (x y : CDAlg ℝ 3) : N (x * y) = N x * N y := by
  have hpol : (normMap x x y y).coord 0 = 0 := by rw [octonion_normMap_zero]; rfl
  rw [normMap_coord0] at hpol
  -- bil(xy)(xy) + bil(xy)(xy) − 2·bil x x·bil y y = 0  ⟹  2·(N(xy) − N x·N y) = 0
  rw [← N_eq_bil, ← N_eq_bil, ← N_eq_bil] at hpol
  -- hpol : N (x*y) + N (x*y) - 2 * N x * N y = 0  ⟹  N(x*y) = N x · N y
  have hpol' : (2 : ℝ) * (N (x * y) - N x * N y) = 0 := by linear_combination hpol
  rcases mul_eq_zero.mp hpol' with hz | hz
  · exact absurd hz two_ne_zero
  · rwa [sub_eq_zero] at hz

/-! ## 4. Power-associativity at 𝕆

Power-associativity (every singly-generated subalgebra is associative) at the
bounded forms the operations-complete matrix needs.  At 𝕆 these follow from
flexibility and alternativity (which give `x²·x = x·x²`) and from `cdAlg_sq_eq`. -/

/-- **Octonion power-associativity, degree-3 form.**  `x²·x = x·x²` for all `x`.
    (Special case of flexibility: `(x·x)·x = x·(x·x)`.) -/
theorem octonion_power_associative (x : CDAlg ℝ 3) : (x * x) * x = x * (x * x) := by
  have := assoc_diag_left x x; rwa [assoc, sub_eq_zero] at this

/-- **Octonion power-associativity, degree-4 form.**  `(x·x)·(x·x) = x·(x·(x·x))`.
    This is exactly the vanishing of the associator `[x, x, x·x]`, which holds by
    LEFT-alternativity (the diagonal `assoc x x (x·x) = 0`, from
    `octonion_alternative` / `assoc_diag_left`).  Together with
    `octonion_power_associative` (`x²·x = x·x²`) this gives the degree-≤4 instances
    of power-associativity the operations-complete matrix records for 𝕆.  (Full
    power-associativity of all alternative algebras is Artin's theorem; only these
    bounded instances are claimed here — scope documented.) -/
theorem octonion_power_associative_4 (x : CDAlg ℝ 3) :
    (x * x) * (x * x) = x * (x * (x * x)) := by
  -- [x, x, x*x] = 0 by left-alternativity (assoc_diag_left x (x*x))
  have := assoc_diag_left x (x * x); rwa [assoc, sub_eq_zero] at this

/-! ## 5. Completeness audit — `#print axioms` -/

#print axioms octonion_flexible
#print axioms octonion_flexible_polarized
#print axioms octonion_moufang_left
#print axioms octonion_moufang_right
#print axioms octonion_moufang_middle
#print axioms octonion_norm_composition
#print axioms octonion_power_associative
#print axioms octonion_power_associative_4
#print axioms octonion_mLeftCoeffZ_zero
#print axioms octonion_mRightCoeffZ_zero
#print axioms octonion_mMidCoeffZ_zero
#print axioms octonion_normCoeffZ_zero

end QBP.Foundations.CDAlg
