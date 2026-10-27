/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.DoubleWiring.Commutation
public import ClusterAlgebras.TotalPositivity.DoubleMoves
public import ClusterAlgebras.TotalPositivity.Permutation

/-!
# Chamber labels of double wiring diagrams at a moment

Let `D` be a double wiring diagram. At a moment `t` (after the first `t` crossings of the
interleaved word) and in a gap `G`, the curves of each colour lying at or below `G` form a set, and
the pair of these sets — thin curves numbered from the top, thick ones from the bottom — is the
label `λ^g_t(D)` of `D` at that moment. A chamber's label is the label at any moment of its span,
and this file shows that this is well defined and that every label at a moment is a chamber's.

Two consequences follow. Every pair `(I, J)` of nonempty subsets of the same size is the label of
a chamber of some double wiring diagram, so every minor `Δ_{I,J}` is a chamber minor. And a swap
or a braid changes the labels of a double wiring diagram only at the chamber it acts on: every
other chamber of the new diagram has the label of a chamber of the old one. This is what drives the
induction in the theorem of Fomin and Zelevinsky.

## Main definitions

* `ClusterAlgebras.DoubleWiringDiagram.labelAt`: the label `λ^g_t(D)` of `D` at the moment `t` in
  a gap, one set per colour.

## Main results

* `ClusterAlgebras.DoubleWiringDiagram.exists_chamber_of_levelAt_eq`: two consecutive crossings of
  a gap, at positions `a < b`, bound a chamber of that gap with span `(a + 1, b + 1)`.
* `ClusterAlgebras.DoubleWiringDiagram.labelAt_eq_labelAt`: the label is constant along the span
  of a chamber.
* `ClusterAlgebras.DoubleWiringDiagram.card_label`: each half of the label of a chamber of gap `G`
  has `G + 1` elements.
* `ClusterAlgebras.DoubleWiringDiagram.exists_chamber_label_eq_labelAt`: every moment and gap give
  a chamber whose label is the label at that moment.
* `ClusterAlgebras.DoubleWiringDiagram.exists_label_eq`: every minor is a chamber minor.
* `ClusterAlgebras.DoubleWiringDiagram.IsSwap.exists_label_eq`: a swap changes only the label of
  the chamber between the two swapped crossings.
* `ClusterAlgebras.DoubleWiringDiagram.IsBraid.exists_label_eq`: a braid changes only the label of
  its site.

## Implementation notes

* Positions in the word are `0`-based and a moment `t` means "after the first `t` crossings", so
  FWZ's position `k` is the index `k - 1` and their moment `t` is the moment `t`. A chamber's
  `left` is FWZ's `L(c)` (with `0` for `-∞`) and its `right` is `R(c)` (with `M + 1` for
  `+∞`), so FWZ's condition `max(L(c), 0) ≤ t < R(c)` reads `c.left ≤ t < c.right`. A swap
  or a braid at the index `p` acts on FWZ's positions `p + 1, p + 2 (, p + 3)`; the chamber
  between two swapped crossings therefore has span `(p + 1, p + 2)`, and the site of a braid has
  span `(p + 1, p + 3)`.
* The label at a moment is computed from the product of each colour's subword of the first `t`
  crossings (`mem_labelAt`), so the label at `t` depends only on these products
  (`labelAt_eq_labelAt_of_prod_eq`).
* For a swap or a braid, the labels before and after the moved block agree
  (`labelAt_eq_of_word_eq_append`). After the block this is shown without the braid relation: in
  each colour, both words spell `w₀`, so cancelling the common prefix and suffix shows that the
  two blocks have the same product. This covers both cases of FWZ's argument for swaps and
  stands in for their appeal to the braid relation.
* FWZ's `[1, n]`-valued indices are `0`-based here: there are `n + 2` strands, gaps are
  `Fin (n + 2)`, and FWZ's gap `g` is `G = g - 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

namespace DoubleWiringDiagram

variable (D : DoubleWiringDiagram n)

/-! ### Subwords of a coloured word -/

/-- The subword of a word all of whose letters have the colour `e'`. -/
@[simp]
theorem subword_map_pair (l : List (Fin (n + 1))) (e e' : Colour) :
    subword (l.map fun i => (i, e')) e = if e' = e then l else [] := by
  by_cases h : e' = e <;> simp [subword, List.filter_map, Function.comp_def, h]

/-- **The subword of a prefix is a prefix of the subword**, of the length it has. -/
theorem take_subword (w : List (Fin (n + 1) × Colour)) (e : Colour) (t : ℕ) :
    (subword w e).take (subword (w.take t) e).length = subword (w.take t) e := by
  have h : subword w e = subword (w.take t) e ++ subword (w.drop t) e := by
    rw [← subword_append, List.take_append_drop]
  rw [h, List.take_left' rfl]

/-- The **label of `D` at the moment `t` in the gap `G`**, one set per colour: the curves of
colour `e` lying at or below the gap `G` after the first `t` crossings of the interleaved word,
named by that colour's numbering. The pair `λ^g_t(D) = (I, J)` with `g = G + 1` is
`(D.labelAt .thin t G, D.labelAt .thick t G)`. -/
@[cluster_algebras "def_double_label_at_time"]
def labelAt (e : Colour) (t : ℕ) (G : Fin (n + 2)) : Finset (Fin (n + 2)) :=
  D.belowSet e (D.colourCountUpTo e t) G

/-! ### The label at a moment as a function of the prefix -/

/-- The colour count up to `t` is the length of that colour's subword of the first `t`
crossings. -/
theorem colourCountUpTo_eq_length (e : Colour) (t : ℕ) :
    D.colourCountUpTo e t = (subword (D.word.take t) e).length := by
  simp [colourCountUpTo, subword]

/-- The wire permutation of the colour `e` at the moment `t` is the product of that colour's
subword of the first `t` crossings. -/
theorem wire_colourCountUpTo (e : Colour) (t : ℕ) :
    (D.toWiringDiagram e).wire (D.colourCountUpTo e t) =
      ((subword (D.word.take t) e).map gapSwap).prod := by
  rw [WiringDiagram.wire, word_toWiringDiagram, ← List.map_take, colourCountUpTo_eq_length,
    take_subword]

/-- Membership in the label at a moment, in terms of the product of the prefix's subword. -/
theorem mem_labelAt {e : Colour} {t : ℕ} {G v : Fin (n + 2)} :
    v ∈ D.labelAt e t G ↔
      (((subword (D.word.take t) e).map gapSwap).prod).symm ((Colour.numbering e).symm v) ≤ G :=
  by rw [labelAt, mem_belowSet, WiringDiagram.levelOf, wire_colourCountUpTo]

/-- **The label at a moment depends only on the product of the prefix**, colour by colour. -/
theorem labelAt_eq_labelAt_of_prod_eq {D D' : DoubleWiringDiagram n} {e : Colour} {t t' : ℕ}
    (h : ((subword (D.word.take t) e).map gapSwap).prod =
      ((subword (D'.word.take t') e).map gapSwap).prod) (G : Fin (n + 2)) :
    D.labelAt e t G = D'.labelAt e t' G := by
  ext v
  rw [mem_labelAt, mem_labelAt, h]

end DoubleWiringDiagram

/-- A crossing at a gap other than `G` does not move any level across `G`. -/
theorem gapSwap_le_iff {g : Fin (n + 1)} {G y : Fin (n + 2)} (h : g.castSucc ≠ G) :
    gapSwap g y ≤ G ↔ y ≤ G := by
  have hne : (g : ℕ) ≠ G := fun hc => h (Fin.ext (by simpa using hc))
  rw [Fin.le_def, Fin.le_def, gapSwap_val]
  split_ifs <;> omega

namespace DoubleWiringDiagram

variable (D : DoubleWiringDiagram n)

/-- The level of the crossing at a genuine position, read off the word. -/
theorem levelAt_eq_getElem {t : ℕ} (ht : t < D.word.length) :
    D.levelAt t = (D.word[t]).1.castSucc := by
  simp [levelAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

/-- **A crossing at another gap does not change the label in `G`.** -/
theorem labelAt_succ_of_ne {t : ℕ} (ht : t < D.word.length) {G : Fin (n + 2)}
    (h : D.levelAt t ≠ G) (e : Colour) : D.labelAt e (t + 1) G = D.labelAt e t G := by
  ext v
  rw [mem_labelAt, mem_labelAt, List.take_add_one, List.getElem?_eq_getElem ht]
  rw [D.levelAt_eq_getElem ht] at h
  by_cases hx : D.word[t].2 = e
  · simp only [Option.toList_some, subword_append, subword_singleton, hx, if_true,
      List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, Equiv.Perm.mul_def, Equiv.symm_trans_apply]
    rw [gapSwap, Equiv.symm_swap, ← gapSwap, gapSwap_le_iff h]
  · simp only [Option.toList_some, subword_append, subword_singleton, hx, if_false,
      List.append_nil]

/-! ### Counting crossings of a gap -/

/-- Each position raises a gap's count by at most one. -/
theorem countUpTo_succ_le (g : Fin (n + 2)) (t : ℕ) :
    D.countUpTo g (t + 1) ≤ D.countUpTo g t + 1 := by
  rcases lt_or_ge t D.word.length with ht | ht
  · rw [D.countUpTo_succ ht]
    split_ifs <;> omega
  · have h1 : D.levels.take (t + 1) = D.levels := List.take_of_length_le (by simp; omega)
    have h2 : D.levels.take t = D.levels := List.take_of_length_le (by simp; omega)
    simp only [countUpTo, h1, h2]
    omega

/-- A gap's count never exceeds its multiplicity. -/
theorem countUpTo_le_multiplicity (g : Fin (n + 2)) (t : ℕ) :
    D.countUpTo g t ≤ D.multiplicity g :=
  List.Sublist.count_le g (List.take_sublist t D.levels)

/-- A gap's count is constant after a position `a` until the next crossing of that gap. -/
private theorem countUpTo_eq_of_forall_ne (E : DoubleWiringDiagram n) {G : Fin (n + 2)}
    {a b : ℕ} (hb : b < E.word.length) (hno : ∀ u, a < u → u < b → E.levelAt u ≠ G) :
    ∀ k, a + 1 + k ≤ b → E.countUpTo G (a + 1 + k) = E.countUpTo G (a + 1) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [← add_assoc, E.countUpTo_succ (by omega), if_neg (hno _ (by omega) (by omega)),
      ih (by omega)]
    simp

/-- **Consecutive crossings of a gap bound a chamber.** If the crossings at the positions `a < b`
both have level `G` and none between them does, then `G` has a chamber with span
`(a + 1, b + 1)`. -/
theorem exists_chamber_of_levelAt_eq (E : DoubleWiringDiagram n) {G : Fin (n + 2)} {a b : ℕ}
    (hab : a < b) (hb : b < E.word.length) (ha : E.levelAt a = G) (hb' : E.levelAt b = G)
    (hno : ∀ u, a < u → u < b → E.levelAt u ≠ G) :
    ∃ Y : E.Chamber, Y.gap = G ∧ Y.left = a + 1 ∧ Y.right = b + 1 := by
  set j := E.countUpTo G (a + 1) with hj
  have hconst := countUpTo_eq_of_forall_ne E hb hno
  have hjb : E.countUpTo G b = j := by
    simpa [show a + 1 + (b - (a + 1)) = b by omega] using hconst (b - (a + 1)) (by omega)
  have hb1 : E.countUpTo G (b + 1) = j + 1 := by
    rw [E.countUpTo_succ hb, if_pos hb', hjb]
  have hle : ∀ s, s ≤ b → E.countUpTo G s ≤ j := by
    intro s hs
    by_cases h : s ≤ a + 1
    · exact E.countUpTo_le_of_le h
    · have := hconst (s - (a + 1)) (by omega)
      rw [show a + 1 + (s - (a + 1)) = s by omega] at this
      omega
  have hmult : j + 1 ≤ E.multiplicity G := by
    rw [← hb1, ← E.countUpTo_length]
    exact E.countUpTo_le_of_le (by omega)
  refine ⟨⟨G, j, by omega⟩, rfl, ?_, ?_⟩
  · change spanStart G j E.levels = a + 1
    refine spanStart_eq_of_count G rfl fun s hs => ?_
    have h1 : E.countUpTo G s ≤ E.countUpTo G a := E.countUpTo_le_of_le (by omega)
    have h2 : j = E.countUpTo G a + 1 := by rw [hj, E.countUpTo_succ (by omega), if_pos ha]
    change E.countUpTo G s ≠ j
    omega
  · change (if j = E.multiplicity G then _ else _) = b + 1
    rw [if_neg (by omega)]
    refine spanStart_eq_of_count G hb1 fun s hs => ?_
    change E.countUpTo G s ≠ j + 1
    have := hle s (by omega)
    omega

namespace Chamber

variable {D} (c : D.Chamber)

/-- **The right position is at most any position where the count has exceeded the index**,
since the count climbs in steps of at most one. -/
theorem right_le_of_le_countUpTo (h : c.idx ≠ D.multiplicity c.gap) {t : ℕ}
    (hc : c.idx + 1 ≤ D.countUpTo c.gap t) : c.right ≤ t := by
  induction t with
  | zero => simp at hc
  | succ t ih =>
    by_cases hlt : c.idx + 1 ≤ D.countUpTo c.gap t
    · exact (ih hlt).trans (Nat.le_succ t)
    · have := D.countUpTo_succ_le c.gap t
      rw [right, if_neg h]
      exact spanStart_le_of_count c.gap (c.idx + 1) (t + 1) D.levels
        (show D.countUpTo c.gap (t + 1) = c.idx + 1 by omega)

/-- **A position of the span precedes the chamber's right position.** -/
theorem lt_right_of_inSpan {t : ℕ} (ht : t ≤ D.word.length) (h : c.InSpan t) : t < c.right := by
  by_cases hlast : c.idx = D.multiplicity c.gap
  · rw [right, if_pos hlast]
    omega
  · by_contra hcon
    have hmono := D.countUpTo_le_of_le (g := c.gap) (Nat.le_of_not_lt hcon)
    have := c.countUpTo_right hlast
    rw [InSpan] at h
    omega

/-- **A position between the chamber's two positions lies in its span.** -/
theorem inSpan_of_le_of_lt {t : ℕ} (h1 : c.left ≤ t) (h2 : t < c.right) : c.InSpan t := by
  have hmono := D.countUpTo_le_of_le (g := c.gap) h1
  have hleft := c.inSpan_left
  rw [InSpan] at hleft ⊢
  by_cases hlast : c.idx = D.multiplicity c.gap
  · have := D.countUpTo_le_multiplicity c.gap t
    omega
  · by_contra hcon
    have := c.right_le_of_le_countUpTo hlast (t := t) (by omega)
    omega

/-- **A chamber's span is the interval `L(c) ≤ t < R(c)`.** -/
theorem inSpan_iff_le_lt {t : ℕ} (ht : t ≤ D.word.length) :
    c.InSpan t ↔ c.left ≤ t ∧ t < c.right :=
  ⟨fun h => ⟨c.left_le h, c.lt_right_of_inSpan ht h⟩, fun h => c.inSpan_of_le_of_lt h.1 h.2⟩

end Chamber

/-! ### The label is constant on a chamber -/

/-- Along the span of a chamber the label in its gap is the one at its left position. -/
theorem labelAt_eq_labelAt_left {c : D.Chamber} {t : ℕ} (ht : c.left ≤ t) (ht' : t < c.right)
    (e : Colour) : D.labelAt e t c.gap = D.labelAt e c.left c.gap := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ s hs ih =>
    have hsr := c.right_le_top
    have hs1 := c.inSpan_of_le_of_lt (t := s) hs (by omega)
    have hs2 := c.inSpan_of_le_of_lt (t := s + 1) (by omega) ht'
    have hlen : s < D.word.length := by omega
    have hne : D.levelAt s ≠ c.gap := by
      intro hc
      rw [Chamber.InSpan, D.countUpTo_succ hlen, if_pos hc] at hs2
      rw [Chamber.InSpan] at hs1
      omega
    rw [D.labelAt_succ_of_ne hlen hne, ih (by omega)]

/-- **The label is constant on a chamber**: any two moments `t`, `t'` of the span
`L(c) ≤ t, t' < R(c)` of a chamber `c` give the same label in its gap. -/
@[cluster_algebras "lem_double_label_well_defined"]
theorem labelAt_eq_labelAt {c : D.Chamber} {t t' : ℕ} (ht : c.left ≤ t) (ht' : t < c.right)
    (hs : c.left ≤ t') (hs' : t' < c.right) (e : Colour) :
    D.labelAt e t c.gap = D.labelAt e t' c.gap := by
  rw [D.labelAt_eq_labelAt_left ht ht', D.labelAt_eq_labelAt_left hs hs']

/-- A chamber's label is the label at its left position. -/
theorem label_eq_labelAt (c : D.Chamber) (e : Colour) :
    D.label c e = D.labelAt e c.left c.gap := rfl

/-- **Each half of a chamber's label has one curve per level at or below its gap**: the curves of
a colour sit at distinct levels at any moment, so the label of a chamber of gap `G` has `G + 1`
elements, whatever the colour. -/
theorem card_label (D : DoubleWiringDiagram n) (c : D.Chamber) (e : Colour) :
    (D.label c e).card = (c.gap : ℕ) + 1 := by
  set σ : Equiv.Perm (Fin (n + 2)) :=
    (Colour.numbering e).symm.trans ((D.toWiringDiagram e).wire (D.colourCountUpTo e c.left)).symm
  have : D.label c e = (Finset.Iic c.gap).map σ.symm.toEmbedding := by
    ext v
    rw [mem_label, Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_Iic]
    rfl
  rw [this, Finset.card_map, Fin.card_Iic]

/-- **Every moment and gap gives a chamber**: for `t ≤ M` and a gap `G` there is a chamber `c` of
gap `G` whose span contains `t` and whose label is the label at the moment `t`. -/
@[cluster_algebras "lem_double_label_at_time"]
theorem exists_chamber_label_eq_labelAt {t : ℕ} (ht : t ≤ D.word.length) (G : Fin (n + 2)) :
    ∃ c : D.Chamber, c.gap = G ∧ c.left ≤ t ∧ t < c.right ∧
      ∀ e, D.label c e = D.labelAt e t G := by
  set c := D.chamberAt G t ht
  have h1 : c.left ≤ t := c.left_le (D.inSpan_chamberAt G t ht)
  have h2 : t < c.right := c.lt_right_of_inSpan ht (D.inSpan_chamberAt G t ht)
  exact ⟨c, rfl, h1, h2, D.labelAt_eq_labelAt le_rfl c.left_lt_right h1 h2⟩

/-! ### Every minor is a chamber minor -/

/-- **Every minor is a chamber minor**: for nonempty `I`, `J` of the same size there are a double
wiring diagram `E` and a chamber `c` of `E` with label `(I(c), J(c)) = (I, J)`. -/
@[cluster_algebras "lem_minor_is_double_chamber_minor"]
theorem exists_label_eq {I J : Finset (Fin (n + 2))} (hI : I.Nonempty)
    (hIJ : I.card = J.card) :
    ∃ (E : DoubleWiringDiagram n) (c : E.Chamber),
      E.label c .thin = I ∧ E.label c .thick = J := by
  classical
  have hpos := hI.card_pos
  have hle : I.card ≤ n + 2 := by simpa using I.card_le_univ
  let G : Fin (n + 2) := ⟨I.card - 1, by omega⟩
  have hcard : (Finset.Iic G).card = I.card := by
    simp [G]
    omega
  obtain ⟨u, hu⟩ := Equiv.Perm.exists_map_finset_eq (Finset.Iic G) J (hcard.trans hIJ)
  obtain ⟨v, hv⟩ := Equiv.Perm.exists_map_finset_eq (Finset.Iic G)
    (I.map Fin.revPerm.toEmbedding) (by simpa using hcard)
  obtain ⟨D₁, t₁, ht₁, hw₁⟩ := WiringDiagram.exists_wire_eq u
  obtain ⟨D₂, t₂, ht₂, hw₂⟩ := WiringDiagram.exists_wire_eq v
  set A := (D₁.word.take t₁).map fun i => (i, Colour.thick)
  set B := (D₂.word.take t₂).map fun i => (i, Colour.thin)
  set w := A ++ B ++ ((D₁.word.drop t₁).map fun i => (i, Colour.thick)) ++
    ((D₂.word.drop t₂).map fun i => (i, Colour.thin)) with hw
  have hthick : subword w .thick = D₁.word := by
    simp only [w, A, B, subword_append, subword_map_pair, reduceCtorEq, ↓reduceIte,
      List.append_nil, List.take_append_drop]
  have hthin : subword w .thin = D₂.word := by
    simp only [w, A, B, subword_append, subword_map_pair, reduceCtorEq, ↓reduceIte,
      List.append_nil, List.nil_append, List.take_append_drop]
  let E : DoubleWiringDiagram n :=
    { word := w
      length_subword := fun e => by
        cases e
        · rw [hthick, D₁.length_eq]
        · rw [hthin, D₂.length_eq]
      prod_subword := fun e => by
        cases e
        · rw [hthick, D₁.prod_eq]
        · rw [hthin, D₂.prod_eq] }
  have hAB : (A ++ B).length = t₁ + t₂ := by
    simp [A, B, Nat.min_eq_left ht₁, Nat.min_eq_left ht₂]
  have htake : E.word.take (t₁ + t₂) = A ++ B := by
    change w.take (t₁ + t₂) = A ++ B
    rw [hw, List.append_assoc, List.take_left' hAB]
  have hlen : t₁ + t₂ ≤ E.word.length := by
    change t₁ + t₂ ≤ w.length
    rw [hw, List.append_assoc, List.length_append, hAB]
    omega
  have hp₁ : ((D₁.word.take t₁).map gapSwap).prod = u := by
    rw [List.map_take, ← hw₁]
    rfl
  have hp₂ : ((D₂.word.take t₂).map gapSwap).prod = v := by
    rw [List.map_take, ← hw₂]
    rfl
  obtain ⟨c, -, -, -, hc⟩ := E.exists_chamber_label_eq_labelAt hlen G
  refine ⟨E, c, ?_, ?_⟩
  · ext x
    rw [hc, mem_labelAt, htake]
    simp only [subword_append, subword_map_pair, A, B, if_true, reduceCtorEq, if_false,
      List.nil_append, hp₂, Colour.numbering]
    rw [← Finset.mem_Iic, ← Finset.mem_map_equiv, hv, Finset.mem_map_equiv]
    simp
  · ext x
    rw [hc, mem_labelAt, htake]
    simp only [subword_append, subword_map_pair, A, B, if_true, reduceCtorEq, if_false,
      List.append_nil, hp₁, Colour.numbering]
    rw [← Finset.mem_Iic, ← Finset.mem_map_equiv, hu]
    simp

/-! ### Labels under swaps and braids -/

/-- **Replacing a block of the word leaves the labels outside it unchanged.** If `D` and `D'`
have words `l ++ m ++ r` and `l ++ m' ++ r` with `m`, `m'` of the same length, then their labels
agree at every moment not strictly inside the block. Before the block the prefixes coincide;
after it, the products of the two blocks' subwords agree, since both words spell `w₀` in each
colour. -/
theorem labelAt_eq_of_word_eq_append {D D' : DoubleWiringDiagram n}
    {l m m' r : List (Fin (n + 1) × Colour)} (hD : D.word = l ++ m ++ r)
    (hD' : D'.word = l ++ m' ++ r) (hm : m.length = m'.length) {t : ℕ}
    (ht : t ≤ l.length ∨ l.length + m.length ≤ t) (e : Colour) (G : Fin (n + 2)) :
    D'.labelAt e t G = D.labelAt e t G := by
  apply labelAt_eq_labelAt_of_prod_eq
  rcases ht with ht | ht
  · rw [hD, hD', List.append_assoc, List.append_assoc, List.take_append_of_le_length ht,
      List.take_append_of_le_length ht]
  · have key : ((subword m' e).map gapSwap).prod = ((subword m e).map gapSwap).prod := by
      have h1 := D.prod_subword e
      have h2 := D'.prod_subword e
      simp only [hD, hD', subword_append, List.map_append, List.prod_append] at h1 h2
      exact mul_right_cancel (mul_left_cancel (h2.trans h1.symm))
    have htk : ∀ k : List (Fin (n + 1) × Colour), k.length = m.length →
        (l ++ k ++ r).take t = l ++ k ++ r.take (t - l.length - m.length) := by
      intro k hk
      rw [List.take_append, List.take_of_length_le (by simp; omega)]
      simp [hk]
      omega
    rw [hD, hD', htk m rfl, htk m' hm.symm]
    simp only [subword_append, List.map_append, List.prod_append, key]

/-- If two diagrams' words differ only in a block of equal length, every chamber of the second
with a moment of its span outside the block has the label of a chamber of the first. -/
theorem exists_label_eq_of_word_eq_append {D D' : DoubleWiringDiagram n}
    {l m m' r : List (Fin (n + 1) × Colour)} (hD : D.word = l ++ m ++ r)
    (hD' : D'.word = l ++ m' ++ r) (hm : m.length = m'.length) (c' : D'.Chamber) {t : ℕ}
    (ht1 : c'.left ≤ t) (ht2 : t < c'.right) (htp : t ≤ l.length ∨ l.length + m.length ≤ t) :
    ∃ c : D.Chamber, ∀ e, D.label c e = D'.label c' e := by
  have hlen : D'.word.length = D.word.length := by simp [hD, hD', hm]
  have := c'.right_le_top
  obtain ⟨c, -, -, -, hc⟩ := D.exists_chamber_label_eq_labelAt (t := t) (by omega) c'.gap
  refine ⟨c, fun e => ?_⟩
  rw [hc e, ← labelAt_eq_of_word_eq_append hD hD' hm htp, label_eq_labelAt,
    D'.labelAt_eq_labelAt le_rfl c'.left_lt_right ht1 ht2]

/-- **A swap changes only the label of a chamber between the swapped crossings**: for a swap at
the 0-based position `p` (the 1-based positions `p + 1`, `p + 2`), every chamber of `D'` not of
span `(p + 1, p + 2)` has the label of a chamber of `D`. -/
@[cluster_algebras "lem_double_swap_labels"]
theorem IsSwap.exists_label_eq {D D' : DoubleWiringDiagram n} {p : ℕ} (h : D.IsSwap D' p)
    (c' : D'.Chamber) (hc' : ¬(c'.left = p + 1 ∧ c'.right = p + 2)) :
    ∃ c : D.Chamber, ∀ e, D.label c e = D'.label c' e := by
  obtain ⟨l, r, a, b, hl, hD, hD'⟩ := h
  obtain ⟨t, ht1, ht2, htp⟩ : ∃ t, c'.left ≤ t ∧ t < c'.right ∧ (t ≤ p ∨ p + 2 ≤ t) := by
    have := c'.left_lt_right
    by_cases hL : c'.left = p + 1
    · have : c'.right ≠ p + 2 := fun hR => hc' ⟨hL, hR⟩
      exact ⟨p + 2, by omega, by omega, Or.inr le_rfl⟩
    · exact ⟨c'.left, le_rfl, this, by omega⟩
  exact exists_label_eq_of_word_eq_append hD hD' rfl c' ht1 ht2 (by simpa [hl] using htp)

/-- The level of a crossing inside a block of the word. -/
theorem levelAt_of_word_eq_append {l m r : List (Fin (n + 1) × Colour)}
    (hD : D.word = l ++ m ++ r) {i : ℕ} (hi : i < m.length) :
    D.levelAt (l.length + i) = (m[i]).1.castSucc := by
  have hlt : l.length + i < D.word.length := by simp [hD]; omega
  rw [D.levelAt_eq_getElem hlt]
  simp only [hD, List.append_assoc, List.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem_append_left hi]

/-- **A braid changes only the label of its site**: for a braid at the 0-based position `p`,
every chamber of `D'` not of span `(p + 1, p + 3)` has the label of a chamber of `D`. -/
@[cluster_algebras "lem_double_braid_labels"]
theorem IsBraid.exists_label_eq {D D' : DoubleWiringDiagram n} {p : ℕ} (h : D.IsBraid D' p)
    (c' : D'.Chamber) (hc' : ¬(c'.left = p + 1 ∧ c'.right = p + 3)) :
    ∃ c : D.Chamber, ∀ e, D.label c e = D'.label c' e := by
  obtain ⟨l, r, ε, g, k, hgk, hl, hD, hD'⟩ := h
  have hne : g.castSucc ≠ k.castSucc := by
    rw [Ne, Fin.castSucc_inj, Fin.ext_iff]
    omega
  have hlen' : D'.word.length = p + 3 + r.length := by simp [hD', hl]; omega
  have h0 : D'.levelAt p = k.castSucc := by
    simpa [hl] using D'.levelAt_of_word_eq_append hD' (i := 0) (by simp)
  have h1 : D'.levelAt (p + 1) = g.castSucc := by
    simpa [hl] using D'.levelAt_of_word_eq_append hD' (i := 1) (by simp)
  have h2 : D'.levelAt (p + 2) = k.castSucc := by
    simpa [hl] using D'.levelAt_of_word_eq_append hD' (i := 2) (by simp)
  have hlr := c'.left_lt_right
  have hrt := c'.right_le_top
  obtain ⟨t, ht1, ht2, htp⟩ : ∃ t, c'.left ≤ t ∧ t < c'.right ∧ (t ≤ p ∨ p + 3 ≤ t) := by
    by_cases hL1 : c'.left = p + 1
    · -- the chamber starts at the first crossing of the block, at level `k`, so it ends at the
      -- third one, which is its site
      exfalso
      have hgap : k.castSucc = c'.gap := h0 ▸ c'.levelAt_of_left_eq_succ hL1
      have hs1 : c'.InSpan (p + 1) := hL1 ▸ c'.inSpan_left
      have hs2 : c'.InSpan (p + 2) := by
        rw [Chamber.InSpan, D'.countUpTo_succ (by omega),
          if_neg (by rw [h1, ← hgap]; exact hne)]
        exact hs1
      have hs3 : ¬c'.InSpan (p + 3) := by
        rw [Chamber.InSpan, D'.countUpTo_succ (by omega), if_pos (by rw [h2, hgap])]
        rw [Chamber.InSpan] at hs2
        omega
      have hr2 := c'.lt_right_of_inSpan (by omega) hs2
      have hr3 : c'.right ≤ p + 3 := by
        by_contra hcon
        exact hs3 (c'.inSpan_of_le_of_lt (by omega) (by omega))
      exact hc' ⟨hL1, by omega⟩
    · by_cases hL2 : c'.left = p + 2
      · -- the chamber starts at the middle crossing, at level `g`, and survives the third
        have hgap : g.castSucc = c'.gap := h1 ▸ c'.levelAt_of_left_eq_succ hL2
        have hs2 : c'.InSpan (p + 2) := hL2 ▸ c'.inSpan_left
        have hs3 : c'.InSpan (p + 3) := by
          rw [Chamber.InSpan, D'.countUpTo_succ (by omega),
            if_neg (by rw [h2, ← hgap]; exact hne.symm)]
          exact hs2
        exact ⟨p + 3, by omega, c'.lt_right_of_inSpan (by omega) hs3, Or.inr le_rfl⟩
      · exact ⟨c'.left, le_rfl, hlr, by omega⟩
  exact exists_label_eq_of_word_eq_append hD hD' rfl c' ht1 ht2 (by simpa [hl] using htp)

end DoubleWiringDiagram

end ClusterAlgebras
