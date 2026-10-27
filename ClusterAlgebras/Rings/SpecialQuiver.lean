/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.SpecialWiring
public import ClusterAlgebras.Rings.Seeds
public import ClusterAlgebras.Rings.Omega
public import ClusterAlgebras.Rings.SLMinors

/-!
# The quiver of the special wiring diagram and its exchanges

Let `D₀` be the special wiring diagram on `k ≥ 3` strands, whose chambers are named by their
chamber sets, the solid intervals `[a, d]` with `d - a ≤ k - 2`. For a bounded chamber
`Y = [b, c]`, `2 ≤ b ≤ c ≤ k - 1`, the arrows of `Q(D₀)` at `Y` are few and explicit: the
arrows into `Y` come from `[b - 1, c - 1]`, `[b, c + 1]` and (when `b < c`) `[b + 1, c]`, and the
arrows out of `Y` go to `[b + 1, c + 1]`, `[b - 1, c]` and (when `b < c`) `[b, c - 1]`.

Consequently the exchange relations of the seed `Σ(D₀, λ)` are three-term relations of flag
minors. At a chamber `{b}` of gap one the new cluster variable is the flag minor `P_{b-1,b+1}`,
and at a chamber `[b, c]` with `b < c` it is
`Ω = P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}`, in the notation `a = b - 1`, `d = c + 1`,
`J = [b + 1, c - 1]` of the formula for `Ω`.

## Main results

* `ClusterAlgebras.wiringArrows_into_bounded_specialWiringDiagram`,
  `ClusterAlgebras.wiringArrows_out_of_bounded_specialWiringDiagram`: the arrows of `Q(D₀)` into
  and out of a bounded chamber.
* `ClusterAlgebras.seedMutation_wiringSeed_special_bottom`: the exchange at a chamber of gap
  one.
* `ClusterAlgebras.extExchangeMatrix_wiringSeed_specialWiringDiagram`: the column of
  `B̃(D₀, λ)` at a mutable index.
* `ClusterAlgebras.seedMutation_wiringSeed_special_omega`: the exchange at a chamber `[b, c]`
  with `b < c`, whose new entry is `Ω`.
* `ClusterAlgebras.seedMutation_wiringSeed_extCluster_self`: for any wiring diagram, the new
  entry of a mutation of `Σ(D, λ)` is the sum of the products of the chamber minors at the
  tails and at the heads of the arrows at the mutated chamber, divided by its chamber minor.

## Implementation notes

The diagram `D₀` on `k = n + 2` strands is `specialWiringDiagram n`, and everything is 0-based,
as in `ClusterAlgebras.Rings.SpecialWiring`: a chamber `c` of `D₀` has chamber set the
interval `[c.idx, c.idx + c.gap]` of `Fin (n + 2)`, so the 1-based chamber `[b, c]` is the
chamber with `idx = b - 1` and `idx + gap = c - 1`. It is bounded exactly when `2 ≤ b` and
`c ≤ k - 1`, which is the hypothesis `Y.Bounded` of the quiver lemma.

The quiver lemma covers the cases `b = c` and `b < c` at once: the chambers `[b + 1, c]` and
`[b, c - 1]`, which exist only when `b < c`, are listed by conditions on the ends of their
chamber sets that no chamber satisfies when `b = c`.

The proof computes the ends of every chamber of `D₀` in closed form: the chamber with chamber set
`[i, e]` (0-based) has left position `binom(e, 2) + i` when `i ≥ 1` and right position
`binom(e + 1, 2) + i + 1` when `e ≤ n`. The arrow conditions then become comparisons of such
numbers, which are lexicographic in the pair `(e, i)`.

In the exchange lemmas the mutated chamber is given by its chamber set, a `Finset` of 0-based
strands, and the condition `k ≥ 3` is implied by the columns named in the statement.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open WiringDiagram

variable {n : ℕ}

/-! ### The ends of the chambers of `D₀` in closed form -/

private theorem choose_two_succ' (x : ℕ) : (x + 1).choose 2 = x.choose 2 + x := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

private theorem choose_two_add_le {x y : ℕ} (h : x < y) : x.choose 2 + x ≤ y.choose 2 := by
  rw [← choose_two_succ']
  exact Nat.choose_le_choose 2 h

/-- The binomial coefficients `binom(x, 2)` and `binom(y, 2)` compared, in five cases according
to the position of `y` relative to `x - 1, x, x + 1`. -/
private theorem choose_two_cases (x y : ℕ) :
    (x + 2 ≤ y ∧ x.choose 2 + 2 * x + 1 ≤ y.choose 2) ∨
      (x + 1 = y ∧ y.choose 2 = x.choose 2 + x) ∨ (x = y ∧ x.choose 2 = y.choose 2) ∨
      (y + 1 = x ∧ x.choose 2 = y.choose 2 + y) ∨
      (y + 2 ≤ x ∧ y.choose 2 + 2 * y + 1 ≤ x.choose 2) := by
  have key : ∀ x y : ℕ, x + 2 ≤ y → x.choose 2 + 2 * x + 1 ≤ y.choose 2 := by
    intro x y h
    have h1 := choose_two_succ' x
    have h2 := choose_two_add_le (show x + 1 < y by omega)
    omega
  obtain h | h | h | h | h : x + 2 ≤ y ∨ x + 1 = y ∨ x = y ∨ y + 1 = x ∨ y + 2 ≤ x := by omega
  · exact Or.inl ⟨h, key x y h⟩
  · subst h; exact Or.inr (Or.inl ⟨rfl, choose_two_succ' x⟩)
  · subst h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · subst h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, choose_two_succ' y⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, key y x h⟩)))

/-- **The left position of a chamber of `D₀`.** The chamber with chamber set `[i, e]` starts at
`binom(e, 2) + i` when `i ≥ 1`, and has no left end when `i = 0`. -/
theorem left_specialWiringDiagram_eq (c : (specialWiringDiagram n).Chamber) :
    c.left = if c.idx = 0 then 0 else (c.idx + c.gap).choose 2 + c.idx := by
  split_ifs with h
  · exact c.left_eq_zero_iff.2 h
  · rw [left_specialWiringDiagram c (by omega), specialPos,
      show (c.gap : ℕ) + c.idx - 1 + 1 = c.idx + c.gap by omega]
    omega

/-- **The right position of a chamber of `D₀`.** The chamber with chamber set `[i, e]` ends at
`binom(e + 1, 2) + i + 1` when `e ≤ n`, and has no right end when `e = n + 1`. -/
theorem right_specialWiringDiagram_eq (c : (specialWiringDiagram n).Chamber) :
    c.right = if c.idx + c.gap ≤ n then (c.idx + c.gap + 1).choose 2 + c.idx + 1
      else (n + 2).choose 2 + 1 := by
  have hidx := c.idx_le
  rw [multiplicity_specialWiringDiagram] at hidx
  split_ifs with h
  · rw [right_specialWiringDiagram c (by omega), specialPos,
      show (c.gap : ℕ) + c.idx + 1 = c.idx + c.gap + 1 by omega]
    omega
  · rw [c.right_eq_top_iff.2 (by rw [multiplicity_specialWiringDiagram]; omega),
      word_specialWiringDiagram, length_specialWord]

/-- **The arrow condition of `D₀` at a bounded chamber, as arithmetic.** For a bounded chamber
`Y` of `D₀` and any chamber `c`, the arrow condition between them in either order is a statement
about the ends `c.idx`, `c.idx + c.gap`, `Y.idx`, `Y.idx + Y.gap` of their chamber sets. -/
private theorem arrow_bounded_specialWiringDiagram_iff {Y : (specialWiringDiagram n).Chamber}
    (hY : Y.Bounded) (c : (specialWiringDiagram n).Chamber) :
    ((specialWiringDiagram n).Arrow c Y ↔
      (c.idx + 1 = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) ∨
        (c.idx = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
        (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap)) ∧
    ((specialWiringDiagram n).Arrow Y c ↔
      (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
        (c.idx + 1 = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap) ∨
        (c.idx = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap)) := by
  rw [bounded_specialWiringDiagram_iff] at hY
  have hc := c.idx_le
  rw [multiplicity_specialWiringDiagram] at hc
  rw [WiringDiagram.Arrow, WiringDiagram.Arrow, bounded_specialWiringDiagram_iff,
    bounded_specialWiringDiagram_iff, left_specialWiringDiagram_eq c,
    left_specialWiringDiagram_eq Y, right_specialWiringDiagram_eq c,
    right_specialWiringDiagram_eq Y, Fin.ext_iff, Fin.ext_iff,
    if_neg (show Y.idx ≠ 0 by omega), if_pos hY.2]
  have h1 := choose_two_cases (c.idx + c.gap) (Y.idx + Y.gap)
  have h2 := choose_two_succ' (c.idx + c.gap)
  have h3 := choose_two_succ' (Y.idx + Y.gap)
  have h4 := choose_two_add_le (show Y.idx + Y.gap + 1 < n + 2 by omega)
  generalize (c.gap : ℕ) = g, (Y.gap : ℕ) = h at *
  generalize c.idx = i, Y.idx = j at *
  have h5 : i + g ≤ n → (i + g + 1).choose 2 + (i + g + 1) ≤ (n + 2).choose 2 := fun he =>
    choose_two_add_le (by omega)
  generalize (i + g + 1).choose 2 = A, (i + g).choose 2 = B, (j + h + 1).choose 2 = C,
    (j + h).choose 2 = D, (n + 2).choose 2 = E at *
  by_cases hi : i = 0 <;> by_cases he : i + g ≤ n
  · specialize h5 he
    rw [if_pos hi, if_pos he]
    constructor <;> omega
  · clear h5
    rw [if_pos hi, if_neg he]
    constructor <;> omega
  · specialize h5 he
    rw [if_neg hi, if_pos he]
    constructor <;> omega
  · clear h5
    rw [if_neg hi, if_neg he]
    constructor <;> omega

/-! ### The arrows at a bounded chamber of `D₀` -/

/-- **The arrows of `Q(D₀)` into a bounded chamber.** Let `Y` be a bounded chamber of `D₀`, with
chamber set `[Y.idx, Y.idx + Y.gap]`. A chamber `c`, with chamber set
`[c.idx, c.idx + c.gap]`, has an arrow to `Y` exactly when its chamber set is that of `Y`
shifted down by one, or extended up by one, or shrunk from below by one. -/
theorem arrow_into_bounded_specialWiringDiagram_iff {Y : (specialWiringDiagram n).Chamber}
    (hY : Y.Bounded) (c : (specialWiringDiagram n).Chamber) :
    (specialWiringDiagram n).Arrow c Y ↔
      (c.idx + 1 = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) ∨
        (c.idx = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
        (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap) :=
  (arrow_bounded_specialWiringDiagram_iff hY c).1

/-- **The arrows of `Q(D₀)` out of a bounded chamber.** Let `Y` be a bounded chamber of `D₀`,
with chamber set `[Y.idx, Y.idx + Y.gap]`. It has an arrow to a chamber `c`, with chamber set
`[c.idx, c.idx + c.gap]`, exactly when the chamber set of `c` is that of `Y` shifted up by one,
or extended down by one, or shrunk from above by one. -/
theorem arrow_out_of_bounded_specialWiringDiagram_iff {Y : (specialWiringDiagram n).Chamber}
    (hY : Y.Bounded) (c : (specialWiringDiagram n).Chamber) :
    (specialWiringDiagram n).Arrow Y c ↔
      (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
        (c.idx + 1 = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap) ∨
        (c.idx = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) :=
  (arrow_bounded_specialWiringDiagram_iff hY c).2

/-- **The quiver of the special wiring diagram, arrows in.** Let `Y` be the chamber of `D₀` with
chamber set `[b, c]`, `2 ≤ b ≤ c ≤ k - 1` (1-based), that is, a bounded chamber; 0-based, its
chamber set is `[Y.idx, Y.idx + Y.gap]`. The arrows into `Y` are exactly `[b - 1, c - 1] → Y`,
`[b, c + 1] → Y` and, when `b < c`, `[b + 1, c] → Y`; for `b = c` these are `{b - 1} → Y` and
`{b, b + 1} → Y`. Here a chamber `c'` is named by its chamber set `[c'.idx, c'.idx + c'.gap]`,
and `Q(D₀)` carries one arrow from each listed chamber and none from any other. -/
@[cluster_algebras "lem_special_wiring_quiver"]
theorem wiringArrows_into_bounded_specialWiringDiagram {Y : (specialWiringDiagram n).Chamber}
    (hY : Y.Bounded) (c : (specialWiringDiagram n).Chamber) :
    (specialWiringDiagram n).wiringArrows c Y =
      if (c.idx + 1 = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) ∨
        (c.idx = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
        (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap) then 1 else 0 :=
  if_congr (arrow_into_bounded_specialWiringDiagram_iff hY c) rfl rfl

/-- **The quiver of the special wiring diagram, arrows out.** Let `Y` be the chamber of `D₀` with
chamber set `[b, c]`, `2 ≤ b ≤ c ≤ k - 1` (1-based), that is, a bounded chamber; 0-based, its
chamber set is `[Y.idx, Y.idx + Y.gap]`. The arrows out of `Y` are exactly `Y → [b + 1, c + 1]`,
`Y → [b - 1, c]` and, when `b < c`, `Y → [b, c - 1]`; for `b = c` these are `Y → {b + 1}` and
`Y → {b - 1, b}`. Here a chamber `c'` is named by its chamber set `[c'.idx, c'.idx + c'.gap]`,
and `Q(D₀)` carries one arrow to each listed chamber and none to any other. -/
@[cluster_algebras "lem_special_wiring_quiver"]
theorem wiringArrows_out_of_bounded_specialWiringDiagram {Y : (specialWiringDiagram n).Chamber}
    (hY : Y.Bounded) (c : (specialWiringDiagram n).Chamber) :
    (specialWiringDiagram n).wiringArrows Y c =
      if (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
        (c.idx + 1 = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap) ∨
        (c.idx = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) then 1 else 0 :=
  if_congr (arrow_out_of_bounded_specialWiringDiagram_iff hY c) rfl rfl

/-- A chamber of `D₀` is `specialChamber a d` exactly when its chamber set `[c.idx, c.idx + c.gap]`
has ends `a` and `d`. -/
theorem eq_specialChamber_iff_idx (c : (specialWiringDiagram n).Chamber) {a d : ℕ} (had : a ≤ d)
    (hd : d ≤ n + 1) (hda : d ≤ a + n) :
    c = specialChamber a d had hd hda ↔ c.idx = a ∧ c.idx + c.gap = d := by
  constructor
  · rintro rfl
    exact ⟨rfl, by rw [idx_specialChamber, gap_specialChamber]; omega⟩
  · rintro ⟨h1, h2⟩
    exact Chamber.ext' (Fin.ext (by rw [gap_specialChamber]; omega)) (by simp [h1])

/-- A chamber of `D₀` with chamber set `Finset.Icc b c` has ends `b` and `c`. -/
theorem idx_eq_of_chamberSet_eq_Icc {Y : (specialWiringDiagram n).Chamber} {b c : Fin (n + 2)}
    (hY : Y.chamberSet = Finset.Icc b c) : Y.idx = b ∧ Y.idx + Y.gap = c := by
  have hidx := Y.idx_le
  rw [multiplicity_specialWiringDiagram] at hidx
  have h : ∀ v, v ∈ Finset.Icc b c ↔ Y.idx ≤ (v : ℕ) ∧ (v : ℕ) ≤ Y.idx + Y.gap := fun v => by
    rw [← hY]
    exact mem_chamberSet_specialWiringDiagram Y v
  have h1 := h b
  have h2 := h c
  have h3 := h ⟨Y.idx, by omega⟩
  have h4 := h ⟨Y.idx + Y.gap, by omega⟩
  simp only [Finset.mem_Icc, Fin.le_def] at h1 h2 h3 h4
  omega

/-- The chamber `specialChamber a d` has chamber set `S` when `S` is the interval `[a, d]`. -/
theorem chamberSet_specialChamber_eq {a d : ℕ} (had : a ≤ d) (hd : d ≤ n + 1) (hda : d ≤ a + n)
    {S : Finset (Fin (n + 2))} (hS : ∀ v : Fin (n + 2), v ∈ S ↔ a ≤ (v : ℕ) ∧ (v : ℕ) ≤ d) :
    (specialChamber a d had hd hda).chamberSet = S :=
  Finset.ext fun v => (mem_chamberSet_specialChamber had hd hda v).trans (hS v).symm

/-! ### The exchange relations of the seed of a wiring diagram -/

/-- For a two-cycle-free arrow system, the positive part of the signed count is the arrow
count. -/
theorem TwoCycleFree.toNat_signedCount {V : Type*} {a : V → V → ℕ} (h : TwoCycleFree a)
    (x y : V) : (signedCount a x y).toNat = a x y := by
  rcases h x y with h0 | h0 <;> simp [signedCount, h0]

/-- A flag minor of the generic square matrix over `ℂ` is a nonzero polynomial. -/
theorem flagMinor_complexGenericMatrix_ne_zero {k : ℕ} (J : Finset (Fin k)) :
    flagMinor (complexGenericMatrix k k) J ≠ 0 :=
  minor_complexGenericMatrix_ne_zero
    (card_initialRows (J.card_le_univ.trans_eq (Fintype.card_fin k)))

section WiringSeed

variable {p m n' : ℕ} (D : WiringDiagram p) (L : Labelling D.wiringQuiver m n')

/-- **The positive exchange monomial of `Σ(D, λ)`** in direction `q`: the product of the chamber
minors of the chambers with an arrow to the chamber `λ(q)`. -/
theorem exchangeMonomialPos_wiringSeed (q : Fin n') :
    exchangeMonomialPos (wiringSeed D L).extCluster (wiringSeed D L).extExchangeMatrix q =
      ∏ c, algebraMap (ComplexPoly (p + 2) (p + 2)) (FractionRing (ComplexPoly (p + 2) (p + 2)))
          (flagMinor (complexGenericMatrix (p + 2) (p + 2)) c.chamberSet) ^
        D.wiringArrows c (L.equiv (Fin.castLE L.le q)) := by
  rw [exchangeMonomialPos_eq_prod]
  refine Fintype.prod_equiv L.equiv _ _ fun i => ?_
  simp only [wiringSeed, extExchangeMatrix, Matrix.of_apply, arrows_wiringQuiver,
    D.twoCycleFree_wiringArrows.toNat_signedCount]

/-- **The negative exchange monomial of `Σ(D, λ)`** in direction `q`: the product of the chamber
minors of the chambers with an arrow from the chamber `λ(q)`. -/
theorem exchangeMonomialNeg_wiringSeed (q : Fin n') :
    exchangeMonomialNeg (wiringSeed D L).extCluster (wiringSeed D L).extExchangeMatrix q =
      ∏ c, algebraMap (ComplexPoly (p + 2) (p + 2)) (FractionRing (ComplexPoly (p + 2) (p + 2)))
          (flagMinor (complexGenericMatrix (p + 2) (p + 2)) c.chamberSet) ^
        D.wiringArrows (L.equiv (Fin.castLE L.le q)) c := by
  rw [exchangeMonomialNeg_eq_prod]
  refine Fintype.prod_equiv L.equiv _ _ fun i => ?_
  simp only [wiringSeed, extExchangeMatrix, Matrix.of_apply, arrows_wiringQuiver,
    neg_signedCount, D.twoCycleFree_wiringArrows.toNat_signedCount]

/-- **The exchange relation of `Σ(D, λ)`.** Mutating in direction `q` replaces the chamber minor
of `Y = λ(q)` by the sum of the product of the chamber minors at the tails of the arrows into `Y`
and the product of those at the heads of the arrows out of `Y`, divided by the chamber minor of
`Y`. -/
theorem seedMutation_wiringSeed_extCluster_self (q : Fin n') :
    (seedMutation L.le (wiringSeed D L) q).extCluster (Fin.castLE L.le q) =
      ((∏ c, algebraMap (ComplexPoly (p + 2) (p + 2)) (FractionRing (ComplexPoly (p + 2) (p + 2)))
          (flagMinor (complexGenericMatrix (p + 2) (p + 2)) c.chamberSet) ^
            D.wiringArrows c (L.equiv (Fin.castLE L.le q))) +
        ∏ c, algebraMap (ComplexPoly (p + 2) (p + 2)) (FractionRing (ComplexPoly (p + 2) (p + 2)))
          (flagMinor (complexGenericMatrix (p + 2) (p + 2)) c.chamberSet) ^
            D.wiringArrows (L.equiv (Fin.castLE L.le q)) c) /
        algebraMap (ComplexPoly (p + 2) (p + 2)) (FractionRing (ComplexPoly (p + 2) (p + 2)))
          (flagMinor (complexGenericMatrix (p + 2) (p + 2))
            (L.equiv (Fin.castLE L.le q)).chamberSet) := by
  simp only [seedMutation, Function.update_self]
  rw [exchangeMonomialPos_wiringSeed D L, exchangeMonomialNeg_wiringSeed D L]
  rfl

end WiringSeed

/-! ### The exchanges at the special wiring diagram -/

/-- A product of powers with exponents the indicator of `s` is the product over `s`. -/
private theorem prod_pow_ite_mem {V F : Type*} [Fintype V] [DecidableEq V] [CommMonoid F]
    (s : Finset V) (f : V → F) {w : V → ℕ} (hw : ∀ c, w c = if c ∈ s then 1 else 0) :
    ∏ c, f c ^ w c = ∏ c ∈ s, f c := by
  rw [← Finset.prod_subset (f := fun c => f c ^ w c) s.subset_univ
    fun c _ hc => by rw [hw, if_neg hc, pow_zero]]
  exact Finset.prod_congr rfl fun c hc => by rw [hw, if_pos hc, pow_one]

/-- At a bounded chamber `Y` of `D₀`, a product weighted by the arrows into `Y` is the product
over the tails of those arrows. -/
private theorem prod_pow_wiringArrows_into {F : Type*} [CommMonoid F]
    {Y : (specialWiringDiagram n).Chamber} (hY : Y.Bounded)
    (s : Finset (specialWiringDiagram n).Chamber)
    (hs : ∀ c, c ∈ s ↔ (c.idx + 1 = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) ∨
      (c.idx = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
      (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap))
    (f : (specialWiringDiagram n).Chamber → F) :
    ∏ c, f c ^ (specialWiringDiagram n).wiringArrows c Y = ∏ c ∈ s, f c :=
  prod_pow_ite_mem s f fun c =>
    (wiringArrows_into_bounded_specialWiringDiagram hY c).trans (if_congr (hs c).symm rfl rfl)

/-- At a bounded chamber `Y` of `D₀`, a product weighted by the arrows out of `Y` is the product
over the heads of those arrows. -/
private theorem prod_pow_wiringArrows_out_of {F : Type*} [CommMonoid F]
    {Y : (specialWiringDiagram n).Chamber} (hY : Y.Bounded)
    (s : Finset (specialWiringDiagram n).Chamber)
    (hs : ∀ c, c ∈ s ↔ (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
      (c.idx + 1 = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap) ∨
      (c.idx = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap))
    (f : (specialWiringDiagram n).Chamber → F) :
    ∏ c, f c ^ (specialWiringDiagram n).wiringArrows Y c = ∏ c ∈ s, f c :=
  prod_pow_ite_mem s f fun c =>
    (wiringArrows_out_of_bounded_specialWiringDiagram hY c).trans (if_congr (hs c).symm rfl rfl)

/-- The tails of the arrows into the chamber `[b, c]`, `b < c`, of `D₀` are the chambers with
chamber sets `J ∪ {a, b}`, `J ∪ {b, c, d}` and `J ∪ {c}`, where `J = (b, c)`, `a = b - 1` and
`d = c + 1`. -/
private theorem prod_pow_wiringArrows_into_Icc {F : Type*} [CommMonoid F]
    (f : Finset (Fin (n + 2)) → F) {Y : (specialWiringDiagram n).Chamber}
    {a b c d : Fin (n + 2)} (hab : (a : ℕ) + 1 = b) (hbc : b < c) (hcd : (c : ℕ) + 1 = d)
    (hY : Y.chamberSet = Finset.Icc b c) :
    ∏ x, f x.chamberSet ^ (specialWiringDiagram n).wiringArrows x Y =
      f (Finset.Ioo b c ∪ {a, b}) *
        (f (Finset.Ioo b c ∪ {b, c, d}) * f (Finset.Ioo b c ∪ {c})) := by
  have hd2 := d.isLt
  have hbc' := Fin.lt_def.1 hbc
  obtain ⟨hY1, hY2⟩ := idx_eq_of_chamberSet_eq_Icc hY
  have hb : Y.Bounded := by rw [bounded_specialWiringDiagram_iff]; omega
  set A₁ := specialChamber (n := n) a (c - 1) (by omega) (by omega) (by omega)
  set A₂ := specialChamber (n := n) b d (by omega) (by omega) (by omega)
  set A₃ := specialChamber (n := n) (b + 1) c (by omega) (by omega) (by omega)
  have hA₁ : A₁ ∉ ({A₂, A₃} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, A₂, A₃, eq_specialChamber_iff_idx, A₁,
      idx_specialChamber, gap_specialChamber]
    omega
  have hA₂ : A₂ ≠ A₃ := by
    simp only [ne_eq, A₂, A₃, eq_specialChamber_iff_idx, idx_specialChamber, gap_specialChamber]
    omega
  have cA₁ : A₁.chamberSet = Finset.Ioo b c ∪ {a, b} :=
    chamberSet_specialChamber_eq _ _ _ fun v => by
      simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_insert, Finset.mem_singleton,
        Fin.lt_def, Fin.ext_iff]
      omega
  have cA₂ : A₂.chamberSet = Finset.Ioo b c ∪ {b, c, d} :=
    chamberSet_specialChamber_eq _ _ _ fun v => by
      simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_insert, Finset.mem_singleton,
        Fin.lt_def, Fin.ext_iff]
      omega
  have cA₃ : A₃.chamberSet = Finset.Ioo b c ∪ {c} :=
    chamberSet_specialChamber_eq _ _ _ fun v => by
      simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
      omega
  rw [prod_pow_wiringArrows_into hb {A₁, A₂, A₃} (fun x => by
      simp only [Finset.mem_insert, Finset.mem_singleton, A₁, A₂, A₃, eq_specialChamber_iff_idx]
      omega), Finset.prod_insert hA₁, Finset.prod_pair hA₂, cA₁, cA₂, cA₃]

/-- The heads of the arrows out of the chamber `[b, c]`, `b < c`, of `D₀` are the chambers with
chamber sets `J ∪ {c, d}`, `J ∪ {a, b, c}` and `J ∪ {b}`, where `J = (b, c)`, `a = b - 1` and
`d = c + 1`. -/
private theorem prod_pow_wiringArrows_out_of_Icc {F : Type*} [CommMonoid F]
    (f : Finset (Fin (n + 2)) → F) {Y : (specialWiringDiagram n).Chamber}
    {a b c d : Fin (n + 2)} (hab : (a : ℕ) + 1 = b) (hbc : b < c) (hcd : (c : ℕ) + 1 = d)
    (hY : Y.chamberSet = Finset.Icc b c) :
    ∏ x, f x.chamberSet ^ (specialWiringDiagram n).wiringArrows Y x =
      f (Finset.Ioo b c ∪ {c, d}) *
        (f (Finset.Ioo b c ∪ {a, b, c}) * f (Finset.Ioo b c ∪ {b})) := by
  have hd2 := d.isLt
  have hbc' := Fin.lt_def.1 hbc
  obtain ⟨hY1, hY2⟩ := idx_eq_of_chamberSet_eq_Icc hY
  have hb : Y.Bounded := by rw [bounded_specialWiringDiagram_iff]; omega
  set B₁ := specialChamber (n := n) (b + 1) d (by omega) (by omega) (by omega)
  set B₂ := specialChamber (n := n) a c (by omega) (by omega) (by omega)
  set B₃ := specialChamber (n := n) b (c - 1) (by omega) (by omega) (by omega)
  have hB₁ : B₁ ∉ ({B₂, B₃} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, B₂, B₃, eq_specialChamber_iff_idx, B₁,
      idx_specialChamber, gap_specialChamber]
    omega
  have hB₂ : B₂ ≠ B₃ := by
    simp only [ne_eq, B₂, B₃, eq_specialChamber_iff_idx, idx_specialChamber, gap_specialChamber]
    omega
  have cB₁ : B₁.chamberSet = Finset.Ioo b c ∪ {c, d} :=
    chamberSet_specialChamber_eq _ _ _ fun v => by
      simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_insert, Finset.mem_singleton,
        Fin.lt_def, Fin.ext_iff]
      omega
  have cB₂ : B₂.chamberSet = Finset.Ioo b c ∪ {a, b, c} :=
    chamberSet_specialChamber_eq _ _ _ fun v => by
      simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_insert, Finset.mem_singleton,
        Fin.lt_def, Fin.ext_iff]
      omega
  have cB₃ : B₃.chamberSet = Finset.Ioo b c ∪ {b} :=
    chamberSet_specialChamber_eq _ _ _ fun v => by
      simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff]
      omega
  rw [prod_pow_wiringArrows_out_of hb {B₁, B₂, B₃} (fun x => by
      simp only [Finset.mem_insert, Finset.mem_singleton, B₁, B₂, B₃, eq_specialChamber_iff_idx]
      omega), Finset.prod_insert hB₁, Finset.prod_pair hB₂, cB₁, cB₂, cB₃]

section Special

variable {m n' : ℕ}

/-- **The column of `B̃(D₀, λ)` at a mutable index `q`.** With `Y = λ(q)`, a bounded chamber, and
`c = λ(i)`, the entry in row `i` is `1` when `c` is one of the chambers with an arrow to `Y`
(`arrow_into_bounded_specialWiringDiagram_iff`), `-1` when it is one of those with an arrow from
`Y` (`arrow_out_of_bounded_specialWiringDiagram_iff`), and `0` otherwise. -/
theorem extExchangeMatrix_wiringSeed_specialWiringDiagram
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n') (i : Fin m) (q : Fin n')
    {c Y : (specialWiringDiagram n).Chamber} (hc : L.equiv i = c)
    (hY : L.equiv (Fin.castLE L.le q) = Y) :
    (wiringSeed (specialWiringDiagram n) L).extExchangeMatrix i q =
      if (c.idx + 1 = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) ∨
          (c.idx = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
          (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap) then 1
      else if (c.idx = Y.idx + 1 ∧ c.idx + c.gap = Y.idx + Y.gap + 1) ∨
          (c.idx + 1 = Y.idx ∧ c.idx + c.gap = Y.idx + Y.gap) ∨
          (c.idx = Y.idx ∧ c.idx + c.gap + 1 = Y.idx + Y.gap) then -1
      else 0 := by
  have hb : Y.Bounded := by
    have := L.notMem_frozen q
    rwa [hY, mem_frozen_wiringQuiver, not_not] at this
  simp only [wiringSeed, extExchangeMatrix, Matrix.of_apply, arrows_wiringQuiver, signedCount,
    hc, hY, wiringArrows_into_bounded_specialWiringDiagram hb,
    wiringArrows_out_of_bounded_specialWiringDiagram hb]
  split_ifs <;> omega

/-- **The exchange at a chamber of gap one.** Let `λ` be a chamber labelling of `D₀`, and let `q`
be the index with `λ(q) = Y`, the chamber with chamber set `{b}` for a strand `b` with neighbours
`a = b - 1` and `c = b + 1`. Then the entry in position `q` of `μ_q(Σ(D₀, λ))` is the flag minor
`P_{a, c}(z)`, read in `ℂ(z)`.

In 1-based terms, `b ∈ [2, k - 1]` and the new entry is `P_{b-1, b+1}(z)`; the condition
`k ≥ 3` is implied by the three strands `a < b < c`. -/
@[cluster_algebras "lem_special_bottom_exchange"]
theorem seedMutation_wiringSeed_special_bottom
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n')
    {a b c : Fin (n + 2)} (hab : (a : ℕ) + 1 = b) (hbc : (b : ℕ) + 1 = c) (q : Fin n')
    (hq : (L.equiv (Fin.castLE L.le q)).chamberSet = {b}) :
    (seedMutation L.le (wiringSeed (specialWiringDiagram n) L) q).extCluster (Fin.castLE L.le q) =
      algebraMap (ComplexPoly (n + 2) (n + 2)) (FractionRing (ComplexPoly (n + 2) (n + 2)))
        (flagMinor (complexGenericMatrix (n + 2) (n + 2)) {a, c}) := by
  have hc2 := c.isLt
  obtain ⟨hY1, hY2⟩ :=
    idx_eq_of_chamberSet_eq_Icc (hq.trans (Finset.Icc_self b).symm)
  set Y := L.equiv (Fin.castLE L.le q) with hYdef
  have hb : Y.Bounded := by rw [bounded_specialWiringDiagram_iff]; omega
  set A₁ := specialChamber (n := n) a a le_rfl (by omega) (by omega)
  set A₂ := specialChamber (n := n) b c (by omega) (by omega) (by omega)
  set B₁ := specialChamber (n := n) c c le_rfl (by omega) (by omega)
  set B₂ := specialChamber (n := n) a b (by omega) (by omega) (by omega)
  have hA : A₁ ≠ A₂ := by
    simp only [ne_eq, A₁, A₂, eq_specialChamber_iff_idx, idx_specialChamber, gap_specialChamber]
    omega
  have hB : B₁ ≠ B₂ := by
    simp only [ne_eq, B₁, B₂, eq_specialChamber_iff_idx, idx_specialChamber, gap_specialChamber]
    omega
  have hA₁ : A₁.chamberSet = {a} := chamberSet_specialChamber_eq _ _ _ fun v => by
    simp only [Finset.mem_singleton, Fin.ext_iff]
    omega
  have hA₂ : A₂.chamberSet = {b, c} := chamberSet_specialChamber_eq _ _ _ fun v => by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  have hB₁ : B₁.chamberSet = {c} := chamberSet_specialChamber_eq _ _ _ fun v => by
    simp only [Finset.mem_singleton, Fin.ext_iff]
    omega
  have hB₂ : B₂.chamberSet = {a, b} := chamberSet_specialChamber_eq _ _ _ fun v => by
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [seedMutation_wiringSeed_extCluster_self, ← hYdef,
    prod_pow_wiringArrows_into hb {A₁, A₂} (fun x => by
      simp only [Finset.mem_insert, Finset.mem_singleton, A₁, A₂, eq_specialChamber_iff_idx]
      omega),
    prod_pow_wiringArrows_out_of hb {B₁, B₂} (fun x => by
      simp only [Finset.mem_insert, Finset.mem_singleton, B₁, B₂, eq_specialChamber_iff_idx]
      omega),
    Finset.prod_pair hA, Finset.prod_pair hB, hA₁, hA₂, hB₁, hB₂, hq,
    div_eq_iff ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (flagMinor_complexGenericMatrix_ne_zero _))]
  have h := congrArg (algebraMap (ComplexPoly (n + 2) (n + 2))
      (FractionRing (ComplexPoly (n + 2) (n + 2))))
    (flagMinor_singleton_three_term (complexGenericMatrix (n + 2) (n + 2))
      (show a < b by rw [Fin.lt_def]; omega) (show b < c by rw [Fin.lt_def]; omega))
  simp only [map_add, map_mul] at h
  rw [h, mul_comm]

/-- **The exchange at a chamber `[b, c]` with `b < c`.** Let `λ` be a chamber labelling of `D₀`,
and let `q` be the index with `λ(q) = Y`, the chamber with chamber set `[b, c]`, with neighbours
`a = b - 1` and `d = c + 1`. Writing `J = (b, c)` for the strands strictly between `b` and `c`,
`Ja = J ∪ {a}` and so on, and `P_X` for the flag minor `P_X(z)`, the entry in position `q` of
`μ_q(Σ(D₀, λ))` is `Ω = P_{Jb} P_{Jacd} - P_{Ja} P_{Jbcd}`, read in `ℂ(z)`.

In 1-based terms, `2 ≤ b < c ≤ k - 1` and `J = [b + 1, c - 1]`; the condition
`k ≥ 3` is implied by the four strands `a < b < c < d`. -/
theorem seedMutation_wiringSeed_special_omega
    (L : Labelling (specialWiringDiagram n).wiringQuiver m n')
    {a b c d : Fin (n + 2)} (hab : (a : ℕ) + 1 = b) (hbc : b < c) (hcd : (c : ℕ) + 1 = d)
    (q : Fin n') (hq : (L.equiv (Fin.castLE L.le q)).chamberSet = Finset.Icc b c) :
    (seedMutation L.le (wiringSeed (specialWiringDiagram n) L) q).extCluster (Fin.castLE L.le q) =
      algebraMap (ComplexPoly (n + 2) (n + 2)) (FractionRing (ComplexPoly (n + 2) (n + 2)))
        (flagMinor (complexGenericMatrix (n + 2) (n + 2)) (Finset.Ioo b c ∪ {b}) *
            flagMinor (complexGenericMatrix (n + 2) (n + 2)) (Finset.Ioo b c ∪ {a, c, d}) -
          flagMinor (complexGenericMatrix (n + 2) (n + 2)) (Finset.Ioo b c ∪ {a}) *
            flagMinor (complexGenericMatrix (n + 2) (n + 2)) (Finset.Ioo b c ∪ {b, c, d})) := by
  have hbc' := Fin.lt_def.1 hbc
  have cY : (L.equiv (Fin.castLE L.le q)).chamberSet = Finset.Ioo b c ∪ {b, c} := by
    rw [hq]
    ext v
    simp only [Finset.mem_union, Finset.mem_Ioo, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton, Fin.lt_def, Fin.le_def, Fin.ext_iff]
    omega
  rw [seedMutation_wiringSeed_extCluster_self,
    prod_pow_wiringArrows_into_Icc (fun S => algebraMap (ComplexPoly (n + 2) (n + 2))
      (FractionRing (ComplexPoly (n + 2) (n + 2)))
        (flagMinor (complexGenericMatrix (n + 2) (n + 2)) S)) hab hbc hcd hq,
    prod_pow_wiringArrows_out_of_Icc (fun S => algebraMap (ComplexPoly (n + 2) (n + 2))
      (FractionRing (ComplexPoly (n + 2) (n + 2)))
        (flagMinor (complexGenericMatrix (n + 2) (n + 2)) S)) hab hbc hcd hq, cY,
    div_eq_iff ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (flagMinor_complexGenericMatrix_ne_zero _))]
  have h := congrArg (algebraMap (ComplexPoly (n + 2) (n + 2))
      (FractionRing (ComplexPoly (n + 2) (n + 2))))
    (flagMinor_complexGenericMatrix_omega hab hbc hcd)
  simp only [map_add, map_sub, map_mul] at h ⊢
  linear_combination -h

end Special

end ClusterAlgebras
