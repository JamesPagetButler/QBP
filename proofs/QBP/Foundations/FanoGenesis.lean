/-
  QBP.Foundations.FanoGenesis — Fano plane, Aut = 168, G₂ → SU(3) anchors
  =======================================================================

  Fold of `archive/historical/lean-standalone/QBP_FanoGenesis.lean`
  (Session 12, 2026-04-14, toolchain v4.18.0) into the Foundations layer
  (#466 item 1), migrated from `native_decide` to kernel `decide`.

  ── FOLD AUDIT FINDING (surfaced, #472-class) ───────────────────────────────
  The archived file's hand-transcribed `octSign` table is NOT a valid
  octonion table: numerical audit during this fold (2026-08-21) shows it
  fails alternativity and the composition law N(xy) = N(x)N(y).  Its
  orientation of the Fano line {1,6,7} — positive triple (1,6,7) — is
  flipped relative to every valid octonion convention containing its other
  six triples.  (The archived theorems T4–T8 were still true as stated —
  they never claimed alternativity — but folding the table forward under the
  name "octonion multiplication" would perpetuate a mislabel.)

  RESOLUTION: this fold does not transcribe the archived table.  The sign
  table here is the kernel-verified Cayley–Dickson convention
  `CDAlg.mulCoeff 3` (pinned to the F3 construction by
  `CDAlg.mulCoeff_three_eq_fano`, and to the sedenion table at n = 4 by
  `CDAlg.mulCoeff_four_eq_sgnTable`), with index map `i ⊕ j` (XOR).  Under
  this convention the positive triple on {1,6,7} is (1,7,6); all other six
  positive triples agree with the archive.  The Fano LINE SET (unordered) is
  identical, so all automorphism-group results (T2, T3, T9–T13) are
  unchanged.

  Verified results (archive numbering, ALL kernel-checked, zero sorry,
  zero native_decide):
    T1.  Fano plane has exactly 7 lines of 3 points each        (by construction + decide)
    T2.  Each point lies on exactly 3 lines                     `every_point_on_three_lines`
    T3.  Two distinct points determine a unique line            `two_points_unique_line`
    T4.  Octonion multiplication closes on each Fano line       `fano_line_closure`, `fano_line_positive`
    T5.  Each Fano triple is anti-commutative                   `fano_anticommutative`
    T6.  Each Fano triple + 1 is associative (quaternion subalg)`fano_associative`
         — strengthened vs the archive: ALL 64 ordered basis triples from
         {e₀, e_a, e_b, e_c} are checked, not one.
    T7.  All imaginary octonion units square to −1              `imaginary_units_square_neg_one`
    T8.  Octonions are NOT associative (explicit witness)       `octonion_non_associative`
    T9.  |Aut(Fano)| = 168 = |PSL(2,7)|                         `aut_fano_168`
    T10/T11. Aut(Fano) acts transitively on the 7 lines         `aut_transitive_on_lines`
    T12. Stabiliser of a line has order 24 = |S₄|               `stabiliser_order_24`
    T13. The stabiliser acts transitively on the other 6 lines  `stabiliser_transitive`
    T14. Dimension bookkeeping 14 = 8 + 3 + 3 (G₂ ⊃ SU(3))      `g2_decomposition_14_8_3_3`

  RIGOR UPGRADE vs the archive: the archived counting theorems ran over an
  unverified `nthPerm` enumeration (no completeness, no duplicate-freedom).
  Here the enumeration `perms7` is proven to be a COMPLETE, IRREDUNDANT
  listing of S₇: `mem_permsOf` (`p ∈ perms7 ↔ p ~ [0..6]`) and
  `perms7_nodup`, both by structural induction.  The transitivity theorems
  (T10–T13) are proven by explicit witness tables kernel-checked per pair —
  no 5040-element search per pair.

  Kernel cost note: the two counting theorems (`aut_fano_168`,
  `stabiliser_order_24`) each kernel-reduce ~5040 permutation checks
  (`decide +kernel`, ~30 s each) — same order as the accepted Sedenion
  kernel checks (#482 note in `proofs/lakefile.lean`).
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import QBP.Foundations.CDAlg

namespace QBP.Foundations.FanoGenesis

open QBP.Foundations.CDAlg (mulCoeff)

/-! ## 1. Octonion sign and index, anchored to the Cayley–Dickson recursion

No hand-transcribed table (see fold audit finding above): the sign is
`CDAlg.mulCoeff 3`, whose provenance is pinned by kernel `decide` in
`CDAlg.lean` (`mulCoeff_three_eq_fano`, `mulCoeff_four_eq_sgnTable`). -/

/-- Sign of `e_i · e_j` in 𝕆: the Cayley–Dickson structure constant. -/
def octSign (i j : Fin 8) : Int := mulCoeff 3 i j

/-- Index of `e_i · e_j` in 𝕆: XOR of the basis indices. -/
def octIdx (i j : Fin 8) : Fin 8 := i ^^^ j

/-- T8 companion: `e₀` is the identity at the sign level. -/
theorem identity_element : ∀ j : Fin 8, octSign 0 j = 1 ∧ octSign j 0 = 1 := by
  decide

/-- T7: every imaginary unit squares to −1 (`e_i² = −e₀` for `i ≠ 0`). -/
theorem imaginary_units_square_neg_one :
    ∀ i : Fin 8, i ≠ 0 → octSign i i = -1 ∧ octIdx i i = 0 := by
  decide

/-! ## 2. The Fano plane -/

/-- The 7 Fano lines, as ordered triples of POINTS `0..6` (point `p`
    corresponds to the imaginary unit `e_{p+1}`).  The cyclic order of each
    triple is the positive orientation under the CD convention: line 6 is
    `(0,6,5)` (units `(1,7,6)`), NOT the archived `(0,5,6)` — see the fold
    audit finding in the header. -/
def fanoLines : List (Nat × Nat × Nat) :=
  [(0,1,2), (0,3,4), (1,3,5), (1,4,6), (2,3,6), (2,5,4), (0,6,5)]

/-- The same 7 lines as ordered triples of UNIT indices `1..7` in `Fin 8`. -/
def fanoLineUnits : List (Fin 8 × Fin 8 × Fin 8) :=
  [(1,2,3), (1,4,5), (2,4,6), (2,5,7), (3,4,7), (3,6,5), (1,7,6)]

/-- Consistency of the two presentations: units = points + 1, line by line. -/
theorem lines_units_consistent :
    fanoLineUnits.map (fun L => (L.1.val - 1, L.2.1.val - 1, L.2.2.val - 1))
      = fanoLines := by decide

/-- T1 (half): there are exactly 7 lines. -/
theorem fano_lines_count : fanoLines.length = 7 := rfl

/-- T1 (other half): each line consists of 3 DISTINCT points `< 7`. -/
theorem fano_lines_wellformed :
    fanoLines.all (fun L =>
      decide (L.1 < 7) && decide (L.2.1 < 7) && decide (L.2.2 < 7) &&
      (L.1 != L.2.1) && (L.2.1 != L.2.2) && (L.1 != L.2.2)) = true := by decide

/-- Is point `x` on the line (triple) `L`? -/
def onLine (x : Nat) (L : Nat × Nat × Nat) : Bool :=
  x == L.1 || x == L.2.1 || x == L.2.2

/-- The `l`-th Fano line. -/
def lineOf (l : Nat) : Nat × Nat × Nat := fanoLines.getD l (0, 0, 0)

/-- Is point `p` on line number `l`? -/
def pointOnLine (p l : Nat) : Bool := onLine p (lineOf l)

/-- T2: every point lies on exactly 3 lines. -/
theorem every_point_on_three_lines :
    ((List.range 7).all fun p =>
      ((List.range 7).countP fun l => pointOnLine p l) == 3) = true := by decide

/-- T3: any two distinct points lie on exactly one common line. -/
theorem two_points_unique_line :
    ((List.range 7).all fun p => (List.range 7).all fun q =>
      p == q ||
        ((List.range 7).countP fun l => pointOnLine p l && pointOnLine q l)
          == 1) = true := by decide

/-! ## 3. Octonion structure on the Fano lines (T4–T6, T8) -/

/-- T4 (index level): multiplication closes on each line — the XOR of any
    two of a line's unit indices is the third, cyclically. -/
theorem fano_line_closure :
    fanoLineUnits.all (fun L =>
      (L.1 ^^^ L.2.1 == L.2.2) && (L.2.1 ^^^ L.2.2 == L.1) &&
        (L.2.2 ^^^ L.1 == L.2.1)) = true := by decide

/-- T4 (sign level): each line triple `(a, b, c)` is POSITIVELY oriented —
    `e_a e_b = +e_c`, `e_b e_c = +e_a`, `e_c e_a = +e_b`. -/
theorem fano_line_positive :
    fanoLineUnits.all (fun L =>
      (octSign L.1 L.2.1 == 1) && (octSign L.2.1 L.2.2 == 1) &&
        (octSign L.2.2 L.1 == 1)) = true := by decide

/-- T5: each line's units pairwise anticommute
    (`e_a e_b = −e_b e_a` for distinct units on a common line). -/
theorem fano_anticommutative :
    fanoLineUnits.all (fun L =>
      (octSign L.1 L.2.1 == -octSign L.2.1 L.1) &&
      (octSign L.2.1 L.2.2 == -octSign L.2.2 L.2.1) &&
      (octSign L.2.2 L.1 == -octSign L.1 L.2.2)) = true := by decide

/-- T6 (strengthened): each Fano line spans an ASSOCIATIVE subalgebra —
    for ALL 64 ordered triples `(u,v,w)` of basis indices drawn from
    `{e₀, e_a, e_b, e_c}`, the sign-level associator vanishes:
    `sgn(u,v)·sgn(u⊕v, w) = sgn(v,w)·sgn(u, v⊕w)`.  (Index associativity is
    automatic: XOR is associative.)  Together with T4/T5/T7 this is the
    quaternion-subalgebra property of each line. -/
theorem fano_associative :
    fanoLineUnits.all (fun L =>
      let S : List (Fin 8) := [0, L.1, L.2.1, L.2.2]
      S.all fun u => S.all fun v => S.all fun w =>
        octSign u v * octSign (u ^^^ v) w
          == octSign v w * octSign u (v ^^^ w)) = true := by decide

/-- T8: the octonions are NOT associative — explicit witness `(e₁, e₂, e₄)`:
    `(e₁e₂)e₄ = e₃e₄ = +e₇` but `e₁(e₂e₄) = e₁e₆ = −e₇`. -/
theorem octonion_non_associative :
    ∃ u v w : Fin 8,
      octSign u v * octSign (u ^^^ v) w
        ≠ octSign v w * octSign u (v ^^^ w) :=
  ⟨1, 2, 4, by decide⟩

/-! ## 4. Complete, irredundant enumeration of S₇

The archived file counted over an unverified `nthPerm` factoradic
enumeration.  Here `permsOf` is a structurally recursive enumerator with a
PROOF that it lists exactly the permutations of its input, without
duplicates (`mem_permsOf`, `nodup_permsOf`).  Everything kernel-reduces
(no well-founded recursion), so the counting theorems below are honest
kernel-checked cardinalities. -/

/-- All insertions of `x` into `q` (one list per insertion position). -/
def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

/-- All permutations of `l`, by iterated insertion. -/
def permsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (permsOf xs).flatMap (insertAll x)

/-- Membership in `insertAll x q` = being `q` with one `x` inserted. -/
theorem mem_insertAll {x : Nat} {q p : List Nat} :
    p ∈ insertAll x q ↔ ∃ s t, q = s ++ t ∧ p = s ++ x :: t := by
  induction q generalizing p with
  | nil =>
    simp only [insertAll, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨[], [], rfl, rfl⟩
    · rintro ⟨s, t, hq, hp⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hq.symm
      simpa using hp
  | cons y ys ih =>
    simp only [insertAll, List.mem_cons, List.mem_map]
    constructor
    · rintro (rfl | ⟨p', hp', rfl⟩)
      · exact ⟨[], y :: ys, rfl, rfl⟩
      · obtain ⟨s, t, rfl, rfl⟩ := ih.mp hp'
        exact ⟨y :: s, t, rfl, rfl⟩
    · rintro ⟨s, t, hq, rfl⟩
      cases s with
      | nil =>
        left
        simp only [List.nil_append] at hq ⊢
        rw [← hq]
      | cons a s' =>
        right
        rw [List.cons_append] at hq
        injection hq with h1 h2
        subst h1
        exact ⟨s' ++ x :: t, ih.mpr ⟨s', t, h2, rfl⟩, rfl⟩

/-- An insertion of `x` into `q` is a permutation of `x :: q`. -/
theorem perm_of_mem_insertAll {x : Nat} {q p : List Nat}
    (h : p ∈ insertAll x q) : p.Perm (x :: q) := by
  obtain ⟨s, t, rfl, rfl⟩ := mem_insertAll.mp h
  exact List.perm_middle

/-- **Completeness + soundness of the enumeration:**
    `p ∈ permsOf l ↔ p` is a permutation of `l`. -/
theorem mem_permsOf : ∀ {l p : List Nat}, p ∈ permsOf l ↔ p.Perm l := by
  intro l
  induction l with
  | nil =>
    intro p
    simp [permsOf, List.perm_nil]
  | cons x xs ih =>
    intro p
    simp only [permsOf, List.mem_flatMap]
    constructor
    · rintro ⟨q, hq, hp⟩
      exact (perm_of_mem_insertAll hp).trans ((ih.mp hq).cons x)
    · intro hp
      have hx : x ∈ p := hp.mem_iff.mpr (by simp)
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hx
      have h1 : (s ++ t).Perm xs :=
        (List.perm_middle.symm.trans hp).cons_inv
      exact ⟨s ++ t, ih.mpr h1, mem_insertAll.mpr ⟨s, t, rfl, rfl⟩⟩

/-- If `x ∉ q`, the insertions of `x` into `q` are pairwise distinct. -/
theorem nodup_insertAll {x : Nat} : ∀ {q : List Nat}, x ∉ q →
    (insertAll x q).Nodup := by
  intro q
  induction q with
  | nil => intro _; simp [insertAll]
  | cons y ys ih =>
    intro hx
    have hxy : x ≠ y := fun h => hx (by simp [h])
    have hxys : x ∉ ys := fun h => hx (by simp [h])
    have hinj : Function.Injective (y :: · : List Nat → List Nat) := by
      intro a b h; injection h
    rw [insertAll, List.nodup_cons]
    refine ⟨?_, (ih hxys).map hinj⟩
    intro hmem
    obtain ⟨p', _, heq⟩ := List.mem_map.mp hmem
    injection heq with h1 _
    exact hxy h1.symm

/-- Uniqueness of the insertion position: if `x` occurs in neither prefix,
    the decompositions coincide. -/
theorem insert_pos_unique {x : Nat} : ∀ {s s' t t' : List Nat},
    x ∉ s → x ∉ s' → s ++ x :: t = s' ++ x :: t' → s = s' ∧ t = t' := by
  intro s
  induction s with
  | nil =>
    intro s' t t' _ hxs' heq
    cases s' with
    | nil => simpa using heq
    | cons a s'' =>
      rw [List.nil_append, List.cons_append] at heq
      injection heq with h1 _
      exact absurd (h1 ▸ List.mem_cons_self ..) hxs'
  | cons a s'' ih =>
    intro s' t t' hxs hxs' heq
    cases s' with
    | nil =>
      rw [List.nil_append, List.cons_append] at heq
      injection heq with h1 _
      exact absurd (h1 ▸ List.mem_cons_self ..) (h1 ▸ hxs)
    | cons b s''' =>
      simp only [List.cons_append] at heq
      injection heq with h1 h2
      subst h1
      have hxs2 : x ∉ s'' := fun h => hxs (by simp [h])
      have hxs3 : x ∉ s''' := fun h => hxs' (by simp [h])
      obtain ⟨hs, ht⟩ := ih hxs2 hxs3 h2
      exact ⟨by rw [hs], ht⟩

/-- **Irredundancy of the enumeration:** if `l` has no duplicates, neither
    does `permsOf l`. -/
theorem nodup_permsOf : ∀ {l : List Nat}, l.Nodup → (permsOf l).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp [permsOf]
  | cons x xs ih =>
    intro hl
    have hx : x ∉ xs := (List.nodup_cons.mp hl).1
    have hxs : xs.Nodup := (List.nodup_cons.mp hl).2
    rw [permsOf, List.nodup_flatMap]
    refine ⟨fun q hq => nodup_insertAll
      (fun h => hx ((mem_permsOf.mp hq).mem_iff.mp h)), ?_⟩
    refine (ih hxs).imp_of_mem ?_
    intro q q' hq hq' hne p hp hp'
    obtain ⟨s, t, rfl, rfl⟩ := mem_insertAll.mp hp
    obtain ⟨s', t', rfl, heq⟩ := mem_insertAll.mp hp'
    have hxq : x ∉ s ++ t :=
      fun h => hx ((mem_permsOf.mp hq).mem_iff.mp h)
    have hxq' : x ∉ s' ++ t' :=
      fun h => hx ((mem_permsOf.mp hq').mem_iff.mp h)
    have hxs0 : x ∉ s := fun h => hxq (by simp [h])
    have hxs0' : x ∉ s' := fun h => hxq' (by simp [h])
    obtain ⟨hs, ht⟩ := insert_pos_unique hxs0 hxs0' heq
    exact hne (by rw [hs, ht])

/-- The 5040 permutations of the 7 Fano points. -/
def perms7 : List (List Nat) := permsOf (List.range 7)

/-- `perms7` lists exactly the permutations of `[0,…,6]`. -/
theorem perms7_complete (p : List Nat) : p ∈ perms7 ↔ p.Perm (List.range 7) :=
  mem_permsOf

/-- `perms7` has no duplicates. -/
theorem perms7_nodup : perms7.Nodup := nodup_permsOf (List.nodup_range)

/-- `|S₇| = 5040`. -/
theorem perms7_length : perms7.length = 5040 := by decide +kernel

/-! ## 5. The automorphism group: |Aut(Fano)| = 168, stabiliser order 24 -/

/-- Apply a permutation (as a list) to a point. -/
def applyPerm (p : List Nat) (x : Nat) : Nat := p.getD x 0

/-- Does `p` (assumed a permutation of `[0..6]`) preserve the line set? -/
def isAuto (p : List Nat) : Bool :=
  fanoLines.all fun L =>
    fanoLines.any fun M =>
      onLine (applyPerm p L.1) M && onLine (applyPerm p L.2.1) M &&
        onLine (applyPerm p L.2.2) M

/-- Does automorphism `p` map line `l1` onto line `l2` (as point sets)? -/
def mapsLineTo (p : List Nat) (l1 l2 : Nat) : Bool :=
  let L1 := lineOf l1
  let L2 := lineOf l2
  onLine (applyPerm p L1.1) L2 && onLine (applyPerm p L1.2.1) L2 &&
    onLine (applyPerm p L1.2.2) L2

/-- **T9: |Aut(Fano)| = 168.**  A kernel-checked count over the complete,
    irredundant enumeration `perms7` (see `perms7_complete`, `perms7_nodup`):
    exactly 168 of the 5040 permutations of the 7 points preserve the line
    set.  168 = |PSL(2,7)| = |GL(3,𝔽₂)|. -/
theorem aut_fano_168 : perms7.countP isAuto = 168 := by decide +kernel

/-- **T12: the stabiliser of line 0 has order 24 = |S₄|.**  Kernel-checked
    count over the same enumeration. -/
theorem stabiliser_order_24 :
    perms7.countP (fun p => isAuto p && mapsLineTo p 0 0) = 24 := by
  decide +kernel

/-- Orbit–stabiliser bookkeeping for the line action: 168 = 24 · 7. -/
theorem orbit_stabiliser_bookkeeping : 168 = 24 * 7 := by norm_num

/-! ## 6. Transitivity (T10/T11, T13) via explicit witness tables

Instead of re-searching all 5040 permutations per line pair (the archived
approach), each pair gets an explicit witness automorphism, kernel-verified
in one pass.  Witness tables were computed offline and are VERIFIED here —
nothing is trusted from the computation that produced them. -/

/-- Witness table: entry `(l1, l2)` is an automorphism mapping line `l1` to
    line `l2`. -/
def transTable : List (List (List Nat)) :=
  [ [[0,1,2,3,4,5,6], [0,3,4,1,2,5,6], [1,3,5,0,2,4,6], [1,4,6,0,2,3,5],
     [2,3,6,0,1,4,5], [2,4,5,0,1,3,6], [0,5,6,1,2,3,4]],
    [[0,3,4,1,2,5,6], [0,1,2,3,4,5,6], [1,0,2,3,5,4,6], [1,0,2,4,6,3,5],
     [2,0,1,3,6,4,5], [2,0,1,4,5,3,6], [0,1,2,5,6,3,4]],
    [[3,0,4,1,5,2,6], [1,0,2,3,5,4,6], [0,1,2,3,4,5,6], [0,1,2,4,3,6,5],
     [0,2,1,3,4,6,5], [0,2,1,4,3,5,6], [1,0,2,5,3,6,4]],
    [[3,0,4,5,1,6,2], [1,0,2,5,3,6,4], [0,1,2,4,3,6,5], [0,1,2,3,4,5,6],
     [0,2,1,4,3,5,6], [0,2,1,3,4,6,5], [1,0,2,3,5,4,6]],
    [[3,4,0,1,5,6,2], [1,2,0,3,5,6,4], [0,2,1,3,4,6,5], [0,2,1,4,3,5,6],
     [0,1,2,3,4,5,6], [0,1,2,4,3,6,5], [1,2,0,5,3,4,6]],
    [[3,4,0,5,1,2,6], [1,2,0,5,3,4,6], [0,2,1,4,3,5,6], [0,2,1,3,4,6,5],
     [0,1,2,4,3,6,5], [0,1,2,3,4,5,6], [1,2,0,3,5,6,4]],
    [[0,3,4,5,6,1,2], [0,1,2,5,6,3,4], [1,0,2,4,6,3,5], [1,0,2,3,5,4,6],
     [2,0,1,4,5,3,6], [2,0,1,3,6,4,5], [0,1,2,3,4,5,6]] ]

/-- The witness automorphism mapping line `l1` to line `l2`. -/
def transWitness (l1 l2 : Nat) : List Nat := (transTable.getD l1 []).getD l2 []

/-- Kernel verification of the whole witness table: every entry is a genuine
    permutation of `[0..6]`, is an automorphism, and maps `l1` to `l2`. -/
theorem transWitness_works :
    ∀ l1 l2 : Fin 7,
      (transWitness l1.val l2.val).isPerm (List.range 7) = true ∧
      isAuto (transWitness l1.val l2.val) = true ∧
      mapsLineTo (transWitness l1.val l2.val) l1.val l2.val = true := by
  decide

/-- **T10/T11: Aut(Fano) acts transitively on the 7 lines** — for every pair
    of lines there is an automorphism carrying one to the other (the G₂
    transitivity that makes the ℍ-crystallisation choice physically unique). -/
theorem aut_transitive_on_lines :
    ∀ l1 l2 : Fin 7, ∃ p : List Nat,
      p.isPerm (List.range 7) = true ∧ isAuto p = true ∧
        mapsLineTo p l1.val l2.val = true :=
  fun l1 l2 => ⟨transWitness l1.val l2.val, transWitness_works l1 l2⟩

/-- Witness table for the stabiliser action: entry `(l1, l2)` (0-indexed over
    lines 1..6) is an automorphism FIXING line 0 and mapping line `l1+1` to
    line `l2+1`. -/
def stabTable : List (List (List Nat)) :=
  [ [[0,1,2,3,4,5,6], [1,0,2,3,5,4,6], [1,0,2,4,6,3,5], [2,0,1,3,6,4,5],
     [2,0,1,4,5,3,6], [0,1,2,5,6,3,4]],
    [[1,0,2,3,5,4,6], [0,1,2,3,4,5,6], [0,1,2,4,3,6,5], [0,2,1,3,4,6,5],
     [0,2,1,4,3,5,6], [1,0,2,5,3,6,4]],
    [[1,0,2,5,3,6,4], [0,1,2,4,3,6,5], [0,1,2,3,4,5,6], [0,2,1,4,3,5,6],
     [0,2,1,3,4,6,5], [1,0,2,3,5,4,6]],
    [[1,2,0,3,5,6,4], [0,2,1,3,4,6,5], [0,2,1,4,3,5,6], [0,1,2,3,4,5,6],
     [0,1,2,4,3,6,5], [1,2,0,5,3,4,6]],
    [[1,2,0,5,3,4,6], [0,2,1,4,3,5,6], [0,2,1,3,4,6,5], [0,1,2,4,3,6,5],
     [0,1,2,3,4,5,6], [1,2,0,3,5,6,4]],
    [[0,1,2,5,6,3,4], [1,0,2,4,6,3,5], [1,0,2,3,5,4,6], [2,0,1,4,5,3,6],
     [2,0,1,3,6,4,5], [0,1,2,3,4,5,6]] ]

/-- The stabiliser witness mapping line `l1+1` to line `l2+1` while fixing
    line 0. -/
def stabWitness (l1 l2 : Nat) : List Nat := (stabTable.getD l1 []).getD l2 []

/-- Kernel verification of the stabiliser witness table. -/
theorem stabWitness_works :
    ∀ l1 l2 : Fin 6,
      (stabWitness l1.val l2.val).isPerm (List.range 7) = true ∧
      isAuto (stabWitness l1.val l2.val) = true ∧
      mapsLineTo (stabWitness l1.val l2.val) 0 0 = true ∧
      mapsLineTo (stabWitness l1.val l2.val) (l1.val + 1) (l2.val + 1)
        = true := by
  decide

/-- **T13: the stabiliser of line 0 acts transitively on the remaining 6
    lines** — for every pair of non-fixed lines there is an automorphism
    fixing line 0 and carrying one to the other. -/
theorem stabiliser_transitive :
    ∀ l1 l2 : Fin 6, ∃ p : List Nat,
      p.isPerm (List.range 7) = true ∧ isAuto p = true ∧
        mapsLineTo p 0 0 = true ∧
        mapsLineTo p (l1.val + 1) (l2.val + 1) = true :=
  fun l1 l2 => ⟨stabWitness l1.val l2.val, stabWitness_works l1 l2⟩

/-! ## 7. G₂ → SU(3) dimension bookkeeping (T14) -/

/-- T14: the dimension bookkeeping of the branching `G₂ ⊃ SU(3)`:
    `dim G₂ = 14 = 8 + 3 + 3̄ = dim su(3) + dim 3 + dim 3̄`.
    HONESTY NOTE: this is the arithmetic identity only.  The
    representation-theoretic content (that the adjoint of G₂ decomposes as
    `8 ⊕ 3 ⊕ 3̄` under the SU(3) stabiliser of a quaternionic line) is a
    Type-3 external fact (e.g. Günaydin–Gürsey 1973) and is NOT formalised
    here — the archived T14 was the same arithmetic check behind a grander
    name. -/
theorem g2_decomposition_14_8_3_3 : 14 = 8 + 3 + 3 := by norm_num

/-! ## Completeness audit — `#print axioms` -/

#print axioms identity_element
#print axioms imaginary_units_square_neg_one
#print axioms lines_units_consistent
#print axioms every_point_on_three_lines
#print axioms two_points_unique_line
#print axioms fano_line_closure
#print axioms fano_line_positive
#print axioms fano_anticommutative
#print axioms fano_associative
#print axioms octonion_non_associative
#print axioms mem_permsOf
#print axioms nodup_permsOf
#print axioms perms7_length
#print axioms aut_fano_168
#print axioms stabiliser_order_24
#print axioms transWitness_works
#print axioms aut_transitive_on_lines
#print axioms stabWitness_works
#print axioms stabiliser_transitive
#print axioms g2_decomposition_14_8_3_3

end QBP.Foundations.FanoGenesis
