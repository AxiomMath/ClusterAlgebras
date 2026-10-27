/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.DoubleLabel
public import ClusterAlgebras.TotalPositivity.DesnanotJacobi
public import ClusterAlgebras.TotalPositivity.ChamberCluster

/-!
# The exchange relations at a swap and at a braid

Let `D'` be obtained from a double wiring diagram `D` by a move at the position `p`, and let `Y`
be the chamber of `D`, and `Z` the chamber of `D'`, at which the move happens. The product of the
chamber minors `Δ(Y) Δ(Z)` of the generic matrix is then a sum of two products of chamber minors
of `D` other than `Δ(Y)`:

* at a **swap** of a thick and a thin crossing of the same level `g`, the identity is the
  Desnanot–Jacobi identity `minor_desnanot_jacobi`, whose four outer minors are the labels of `D`
  at the moments just before and just after the two crossings, in the gaps `g - 1`, `g`, `g + 1`
  (with `1` in place of the minor of the gap `g - 1` when there is no such gap);
* at a **braid** of three crossings of one colour and levels `g, h, g` with `|g - h| = 1`, it is
  the three-term relation for nested row sets `minor_nested_three_term`, applied to the generic
  matrix when the colour is thick and to its transpose when it is thin; the four chambers are those
  of the gaps `min(g, h)` and `min(g, h) + 1` just before and just after the three crossings.

In both cases the proof writes every label involved as the image, under the wire positions of each
colour just before the move, of a set of levels; the sets of levels are explicit, and the order of
the three or four wires involved comes from `WiringDiagram.wire_castSucc_lt_wire_succ`.

## Main results

* `ClusterAlgebras.DoubleWiringDiagram.IsSwap.exists_exchange`: the exchange relation at a swap of
  two crossings of the same level and different colours.
* `ClusterAlgebras.DoubleWiringDiagram.IsBraid.exists_exchange`: the exchange relation at a braid.

## Implementation notes

* Positions are `0`-based word indices: the swap or braid at `p` acts on the letters at `p`,
  `p + 1` (and `p + 2`), FWZ's positions `p + 1`, `p + 2` (and `p + 3`), and FWZ's
  moment `p - 1`, just before the move, is the moment `p` here. The chambers at which the move
  happens have span `(p + 1, p + 2)`, respectively `(p + 1, p + 3)`.
* FWZ assume `n ≥ 2` for the swap and `n ≥ 3` for the braid. With `n + 2` strands these
  hypotheses are automatic: two crossings of the same level exist only on at least two strands, and
  two adjacent levels only on at least three.
* For the swap at level `g = 1` (the gap `0` here) FWZ put `b₁ = 1`, there being no gap
  below; the identity is then the Desnanot–Jacobi identity with `I' = S = ∅`, which
  `minor_desnanot_jacobi` covers, and `minor z ∅ ∅ = 1`.
* At a braid FWZ read the two chambers after the move at their moments `p + 1` and `p + 2`,
  which are the moments `p + 2` and `p + 3` here. Both are read at the moment `p + 3` here: the
  third crossing does not cut the gap read at `p + 2`, so the label is the same. A chamber whose
  span contains the moment `p + 3` has right end beyond `p + 3`, so it does not have span
  `(p + 1, p + 3)`; this replaces FWZ's argument about left ends.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 1–3*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

variable {n : ℕ}

/-! ### Minors -/

/-- A minor of the transpose is the minor with the roles of rows and columns exchanged. -/
private theorem minor_transpose {R ι κ : Type*} [CommRing R] [LinearOrder ι] [LinearOrder κ]
    (z : Matrix ι κ R) (I : Finset κ) (J : Finset ι) :
    minor z.transpose I J = minor z J I := by
  by_cases h : J.card = I.card
  · rw [minor_of_card_eq z.transpose rfl h, minor_of_card_eq z h rfl,
      ← Matrix.transpose_submatrix, Matrix.det_transpose]
  · rw [minor, dif_neg h, minor, dif_neg (Ne.symm h)]

/-- The empty minor is `1`. -/
private theorem minor_empty {R ι κ : Type*} [CommRing R] [LinearOrder ι] [LinearOrder κ]
    (z : Matrix ι κ R) : minor z ∅ ∅ = 1 := by
  rw [minor_of_card_eq z (k := 0) rfl rfl]
  exact Matrix.det_isEmpty

/-! ### Sets of levels -/

/-- The levels at or below `g.castSucc`. -/
private theorem Iic_castSucc_eq (g : Fin (n + 1)) :
    Iic g.castSucc = Iio g.castSucc ∪ {g.castSucc} := by
  ext x
  simp [le_iff_lt_or_eq]

/-- The levels at or below `g.succ`. -/
private theorem Iic_succ_eq (g : Fin (n + 1)) :
    Iic g.succ = Iio g.castSucc ∪ {g.castSucc, g.succ} := by
  ext x
  simp only [mem_Iic, mem_union, mem_Iio, mem_insert, mem_singleton, Fin.le_iff_val_le_val,
    Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

/-- After a crossing of level `g`, the levels at or below `g.castSucc` hold the wires that were at
the levels below `g.castSucc` and at `g.succ`. -/
private theorem map_gapSwap_Iic_castSucc (g : Fin (n + 1)) :
    (Iic g.castSucc).map (gapSwap g).toEmbedding = Iio g.castSucc ∪ {g.succ} := by
  ext x
  simp only [mem_map_equiv, gapSwap, Equiv.symm_swap, mem_Iic, mem_union, mem_Iio,
    mem_singleton, Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at * <;> omega

/-- Mapping by a product of permutations is mapping twice. -/
private theorem map_perm_mul (s : Finset (Fin (n + 2))) (σ τ : Equiv.Perm (Fin (n + 2))) :
    s.map (σ * τ).toEmbedding = (s.map τ.toEmbedding).map σ.toEmbedding := by
  rw [map_map]
  rfl

/-- Mapping by the identity permutation does nothing. -/
private theorem map_one_perm (s : Finset (Fin (n + 2))) :
    s.map (1 : Equiv.Perm (Fin (n + 2))).toEmbedding = s :=
  map_refl

section Braid

variable {lo hi : Fin (n + 1)}

/-- The levels at or below `hi.castSucc`, for `hi = lo + 1`. -/
private theorem Iic_castSucc_eq_of_succ (h : (lo : ℕ) + 1 = hi) :
    Iic hi.castSucc = Iio lo.castSucc ∪ {lo.castSucc, hi.castSucc} := by
  ext x
  simp only [mem_Iic, mem_union, mem_Iio, mem_insert, mem_singleton, Fin.le_iff_val_le_val,
    Fin.lt_def, Fin.ext_iff, Fin.val_castSucc]
  omega

/-- After a crossing of level `hi = lo + 1`, the levels at or below `hi.castSucc` hold the wires
that were at the levels below `lo.castSucc`, at `lo.castSucc` and at `hi.succ`. -/
private theorem map_gapSwap_Iic_castSucc_of_succ (h : (lo : ℕ) + 1 = hi) :
    (Iic hi.castSucc).map (gapSwap hi).toEmbedding =
      Iio lo.castSucc ∪ {lo.castSucc, hi.succ} := by
  ext x
  simp only [mem_map_equiv, gapSwap, Equiv.symm_swap, mem_Iic, mem_union, mem_Iio,
    mem_singleton, mem_insert, Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at * <;> omega

/-- After crossings of levels `lo, hi, lo` with `hi = lo + 1`, the levels at or below
`lo.castSucc` hold the wires that were below `lo.castSucc` and at `hi.succ`. -/
private theorem map_braid_Iic_castSucc (h : (lo : ℕ) + 1 = hi) :
    (((Iic lo.castSucc).map (gapSwap lo).toEmbedding).map (gapSwap hi).toEmbedding).map
        (gapSwap lo).toEmbedding = Iio lo.castSucc ∪ {hi.succ} := by
  ext x
  simp only [mem_map_equiv, gapSwap, Equiv.symm_swap, mem_Iic, mem_union, mem_Iio,
    mem_singleton, Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ, not_true_eq_false] at * <;> omega

/-- After crossings of levels `lo, hi, lo` with `hi = lo + 1`, the levels at or below
`hi.castSucc` hold the wires that were below `lo.castSucc`, at `hi.castSucc` and at `hi.succ`. -/
private theorem map_braid_Iic_castSucc_of_succ (h : (lo : ℕ) + 1 = hi) :
    (((Iic hi.castSucc).map (gapSwap lo).toEmbedding).map (gapSwap hi).toEmbedding).map
        (gapSwap lo).toEmbedding = Iio lo.castSucc ∪ {hi.castSucc, hi.succ} := by
  ext x
  simp only [mem_map_equiv, gapSwap, Equiv.symm_swap, mem_Iic, mem_union, mem_Iio,
    mem_singleton, mem_insert, Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ, not_true_eq_false] at * <;> omega

end Braid

/-! ### The wire positions of one colour after a prefix of the word -/

/-- The product of the adjacent transpositions of the crossings of colour `e` of a list of coloured
crossings: the wire positions of colour `e` after reading the list. -/
private def subwordPerm (l : List (Fin (n + 1) × Colour)) (e : Colour) :
    Equiv.Perm (Fin (n + 2)) :=
  ((subword l e).map gapSwap).prod

/-- Reading two lists in turn composes their wire positions. -/
private theorem subwordPerm_append (l m : List (Fin (n + 1) × Colour)) (e : Colour) :
    subwordPerm (l ++ m) e = subwordPerm l e * subwordPerm m e := by
  simp [subwordPerm, subword, List.filter_append]

/-- A single crossing moves the wires of its own colour only. -/
private theorem subwordPerm_singleton (x : Fin (n + 1) × Colour) (e : Colour) :
    subwordPerm [x] e = if x.2 = e then gapSwap x.1 else 1 := by
  by_cases h : x.2 = e <;> simp [subwordPerm, subword, List.filter, h]

/-- A single crossing of colour `e` moves the wires of colour `e` by its transposition. -/
private theorem subwordPerm_single (a : Fin (n + 1)) (e : Colour) :
    subwordPerm [(a, e)] e = gapSwap a := by
  simp [subwordPerm_singleton]

/-- A single crossing of colour `e` does not move the wires of the other colour. -/
private theorem subwordPerm_single_swap (a : Fin (n + 1)) (e : Colour) :
    subwordPerm [(a, e)] e.swap = 1 := by
  simp [subwordPerm_singleton, (Colour.swap_ne e).symm]

/-- Three crossings of colour `e` move the wires of colour `e` by their product. -/
private theorem subwordPerm_triple (a b : Fin (n + 1)) (e : Colour) :
    subwordPerm [(a, e), (b, e), (a, e)] e = gapSwap a * gapSwap b * gapSwap a := by
  simp [subwordPerm, subword, mul_assoc]

/-- Three crossings of colour `e` do not move the wires of the other colour. -/
private theorem subwordPerm_triple_swap (a b : Fin (n + 1)) (e : Colour) :
    subwordPerm [(a, e), (b, e), (a, e)] e.swap = 1 := by
  simp [subwordPerm, subword, (Colour.swap_ne e).symm]

/-- The two sides of a braid of colour `e` give the same wire positions of every colour. -/
private theorem subwordPerm_braid {lo hi : Fin (n + 1)} (hlh : (lo : ℕ) + 1 = hi) (e c : Colour) :
    subwordPerm [(lo, e), (hi, e), (lo, e)] c = subwordPerm [(hi, e), (lo, e), (hi, e)] c := by
  by_cases he : e = c
  · subst he
    rw [subwordPerm_triple, subwordPerm_triple, gapSwap_braid hlh]
  · simp [subwordPerm, subword, he]

namespace DoubleWiringDiagram

/-- The minor `Δ_{I,J}(z)` of the generic matrix of the label `(I, J)` of `D` at the moment `t`
in the gap `G`. -/
private noncomputable def labelAtMinor (D : DoubleWiringDiagram n) (t : ℕ) (G : Fin (n + 2)) :
    MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ :=
  minor (genericMatrix (Fin (n + 2)) (Fin (n + 2))) (D.labelAt .thin t G) (D.labelAt .thick t G)

/-- The chamber minor of a chamber is the minor of the label at its left end. -/
private theorem doubleExtendedCluster_eq_labelAtMinor {D : DoubleWiringDiagram n}
    (c : D.Chamber) {t : ℕ} {G : Fin (n + 2)} (ht : c.left = t) (hG : c.gap = G) :
    doubleExtendedCluster D c = D.labelAtMinor t G := by
  subst ht hG
  rfl

/-- Every moment and gap give a chamber whose chamber minor is the minor of the label there. -/
private theorem exists_chamber_labelAtMinor (D : DoubleWiringDiagram n) {t : ℕ}
    (ht : t ≤ D.word.length) (G : Fin (n + 2)) : ∃ c : D.Chamber, c.left ≤ t ∧ t < c.right ∧
      doubleExtendedCluster D c = D.labelAtMinor t G := by
  obtain ⟨c, -, hl, hr, hc⟩ := D.exists_chamber_label_eq_labelAt ht G
  exact ⟨c, hl, hr, by rw [doubleExtendedCluster, hc, hc]; rfl⟩

/-- **The label after a prefix of the word**: if the word of `D` begins with `l`, the label of
colour `e` after `l` in the gap `G` is the image of the levels at or below `G` under the wire
positions of colour `e` after `l`, numbered by that colour's numbering. -/
private theorem labelAt_eq_map (D : DoubleWiringDiagram n) {l r : List (Fin (n + 1) × Colour)}
    (hw : D.word = l ++ r) (e : Colour) (G : Fin (n + 2)) :
    D.labelAt e l.length G =
      (Iic G).map ((subwordPerm l e).trans (Colour.numbering e)).toEmbedding := by
  have hc : D.colourCountUpTo e l.length = (subword l e).length := by
    simp [colourCountUpTo, hw, subword]
  have hwire : (D.toWiringDiagram e).wire (subword l e).length = subwordPerm l e := by
    simp [WiringDiagram.wire, hw, subword, List.filter_append, subwordPerm]
  ext v
  rw [mem_map_equiv]
  simp [labelAt, hc, WiringDiagram.levelOf, hwire]

/-- `labelAt_eq_map` after a further stretch `m` of the word. -/
private theorem labelAt_append_eq_map (D : DoubleWiringDiagram n)
    {l m r : List (Fin (n + 1) × Colour)} (hw : D.word = l ++ m ++ r) (e : Colour)
    (G : Fin (n + 2)) :
    D.labelAt e (l.length + m.length) G =
      ((Iic G).map (subwordPerm m e).toEmbedding).map
        ((subwordPerm l e).trans (Colour.numbering e)).toEmbedding := by
  rw [← List.length_append, D.labelAt_eq_map hw, subwordPerm_append, map_map]
  rfl

/-- **At a crossing the wire arriving from below has the smaller label**, read off the prefix of
the word before the crossing. -/
private theorem lt_of_word_eq (D : DoubleWiringDiagram n) {l r : List (Fin (n + 1) × Colour)}
    {x : Fin (n + 1) × Colour} (hw : D.word = l ++ x :: r) :
    subwordPerm l x.2 x.1.castSucc < subwordPerm l x.2 x.1.succ := by
  set W := D.toWiringDiagram x.2
  have hW : W.word = subword l x.2 ++ x.1 :: subword r x.2 := by
    simp [W, hw, subword, List.filter_append]
  have ht : (subword l x.2).length < W.word.length := by simp [hW]
  have hlev : W.levelAt (subword l x.2).length = x.1 := by
    rw [W.levelAt_eq_getElem ht]; simp [hW]
  have hwire : W.wire (subword l x.2).length = subwordPerm l x.2 := by
    simp [WiringDiagram.wire, hW, subwordPerm]
  have := W.wire_castSucc_lt_wire_succ ht
  rwa [hlev, hwire] at this

/-- The level and colour of the crossing after a prefix `l` of the word. -/
private theorem levelAt_colourAt_of_word_eq (D : DoubleWiringDiagram n)
    {l r : List (Fin (n + 1) × Colour)} {x : Fin (n + 1) × Colour} (hw : D.word = l ++ x :: r) :
    D.levelAt l.length = x.1.castSucc ∧ D.colourAt l.length = x.2 := by
  simp [levelAt, colourAt, hw, List.getD_eq_getElem?_getD]

/-! ### The swap -/

/-- Below the gap `g.castSucc`, after a prefix `l` of the word, the minor of the labels is `1`
(there being no gap) or the chamber minor of a chamber whose left end is at most `l.length`. -/
private theorem exists_minor_Iio_castSucc (D : DoubleWiringDiagram n)
    {l r : List (Fin (n + 1) × Colour)} (hw : D.word = l ++ r) (g : Fin (n + 1)) :
    ∃ b, (b = 1 ∨ ∃ c : D.Chamber, c.left ≤ l.length ∧ b = doubleExtendedCluster D c) ∧
      b = minor (genericMatrix (Fin (n + 2)) (Fin (n + 2)))
        ((Iio g.castSucc).map ((subwordPerm l .thin).trans (Colour.numbering .thin)).toEmbedding)
        ((Iio g.castSucc).map
          ((subwordPerm l .thick).trans (Colour.numbering .thick)).toEmbedding) := by
  rcases Nat.eq_zero_or_pos g with hg0 | hg0
  · refine ⟨1, Or.inl rfl, ?_⟩
    have h0 : Iio g.castSucc = ∅ :=
      eq_empty_of_forall_notMem fun x hx => by
        simp only [mem_Iio, Fin.lt_def, Fin.val_castSucc] at hx; omega
    rw [h0, map_empty, map_empty, minor_empty]
  · let G' : Fin (n + 2) := ⟨g - 1, by omega⟩
    have hG' : Iic G' = Iio g.castSucc := by
      ext x
      simp only [mem_Iic, mem_Iio, Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_castSucc, G']
      omega
    obtain ⟨c, hcl, -, hc⟩ := D.exists_chamber_labelAtMinor (t := l.length) (by simp [hw]) G'
    refine ⟨_, Or.inr ⟨c, hcl, rfl⟩, ?_⟩
    rw [hc, labelAtMinor, D.labelAt_eq_map hw, D.labelAt_eq_map hw, hG']

/-- At a swap of two crossings `(g, ea)`, `(g, eb)` of different colours after a prefix `l` of the
word, the wires of each colour at the levels `g.castSucc` and `g.succ` are in increasing order. -/
private theorem lt_of_swap (D : DoubleWiringDiagram n) {l r : List (Fin (n + 1) × Colour)}
    {g : Fin (n + 1)} {ea eb : Colour} (hcol : ea ≠ eb) (hw : D.word = l ++ (g, ea) :: (g, eb) :: r)
    (e : Colour) : subwordPerm l e g.castSucc < subwordPerm l e g.succ := by
  by_cases he : ea = e
  · subst he
    exact D.lt_of_word_eq (x := (g, ea)) hw
  · obtain rfl : eb = e := by cases ea <;> cases eb <;> cases e <;> simp_all
    simpa [subwordPerm_append, subwordPerm_singleton, he] using
      D.lt_of_word_eq (l := l ++ [(g, ea)]) (x := (g, eb)) (r := r) (by simp [hw])

/-- Two crossings of the same level `g` and different colours permute the wires of each colour by
the transposition `gapSwap g`. -/
private theorem subwordPerm_pair_of_ne {g : Fin (n + 1)} {ea eb : Colour} (hcol : ea ≠ eb)
    (e : Colour) : subwordPerm [(g, ea), (g, eb)] e = gapSwap g := by
  rw [show [(g, ea), (g, eb)] = [(g, ea)] ++ [(g, eb)] from rfl, subwordPerm_append,
    subwordPerm_singleton, subwordPerm_singleton]
  cases ea <;> cases eb <;> cases e <;> simp_all

/-- **The Desnanot–Jacobi identity among the labels at a swap**, with `φT`, `φN` the thick and
thin wire positions before the swap, numbered, and `g` the common level. -/
private theorem minor_swap_identity (φT φN : Equiv.Perm (Fin (n + 2))) (g : Fin (n + 1))
    (hT : φT g.castSucc < φT g.succ) (hN : φN g.succ < φN g.castSucc) :
    let z := genericMatrix (Fin (n + 2)) (Fin (n + 2))
    let s := Iic g.castSucc
    let s' := s.map (gapSwap g).toEmbedding
    minor z (s.map φN.toEmbedding) (s'.map φT.toEmbedding) *
        minor z (s'.map φN.toEmbedding) (s.map φT.toEmbedding) =
      minor z (s.map φN.toEmbedding) (s.map φT.toEmbedding) *
          minor z (s'.map φN.toEmbedding) (s'.map φT.toEmbedding) +
        minor z ((Iio g.castSucc).map φN.toEmbedding) ((Iio g.castSucc).map φT.toEmbedding) *
          minor z ((Iic g.succ).map φN.toEmbedding) ((Iic g.succ).map φT.toEmbedding) := by
  intro z s s'
  simp only [s, s', Iic_castSucc_eq, map_gapSwap_Iic_castSucc, Iic_succ_eq, map_union,
    map_singleton, map_insert, Equiv.coe_toEmbedding]
  rw [pair_comm (φN g.castSucc)]
  have hle : ¬g.succ < g.castSucc := not_lt.2 Fin.castSucc_lt_succ.le
  exact minor_desnanot_jacobi (by simp) (by simp [hle]) (by simp) hN (by simp) (by simp [hle]) hT

/-- **The exchange at a swap of two crossings of the same level.** Let `D'` be obtained from `D`
by the swap at the 0-based position `p`, where the two crossings have the same level and
different colours, and let `Y` and `Z` be the chambers of `D` and of `D'` in that level's gap with
span `(p + 1, p + 2)`. Then `Δ(Y) Δ(Z) = a₁ a₂ + b₁ b₂`, each of `a₁, a₂, b₁, b₂` being `1` or the
chamber minor of a chamber of `D` not of span `(p + 1, p + 2)`. -/
@[cluster_algebras "lem_double_swap_exchange"]
theorem IsSwap.exists_exchange {D D' : DoubleWiringDiagram n} {p : ℕ} (h : D.IsSwap D' p)
    (hlev : D.levelAt p = D.levelAt (p + 1)) (hcol : D.colourAt p ≠ D.colourAt (p + 1))
    (Y : D.Chamber) (hY : Y.gap = D.levelAt p ∧ Y.left = p + 1 ∧ Y.right = p + 2)
    (Z : D'.Chamber) (hZ : Z.gap = D.levelAt p ∧ Z.left = p + 1 ∧ Z.right = p + 2) :
    ∃ a₁ a₂ b₁ b₂ : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ,
      (∀ w ∈ [a₁, a₂, b₁, b₂], w = 1 ∨ ∃ c : D.Chamber,
        ¬(c.left = p + 1 ∧ c.right = p + 2) ∧ w = doubleExtendedCluster D c) ∧
      doubleExtendedCluster D Y * doubleExtendedCluster D' Z = a₁ * a₂ + b₁ * b₂ := by
  obtain ⟨l, r, ⟨g, ea⟩, ⟨g', eb⟩, rfl, hD, hD'⟩ := h
  obtain ⟨ha1, ha2⟩ := D.levelAt_colourAt_of_word_eq (l := l) (x := (g, ea))
    (r := (g', eb) :: r) (by simp [hD])
  obtain ⟨hb1, hb2⟩ := D.levelAt_colourAt_of_word_eq (l := l ++ [(g, ea)]) (x := (g', eb))
    (r := r) (by simp [hD])
  simp only [List.length_append, List.length_singleton] at hb1 hb2
  rw [ha1, hb1, Fin.castSucc_inj] at hlev
  rw [ha2, hb2] at hcol
  subst hlev
  rw [ha1] at hY hZ
  have hlen : D.word.length = l.length + 2 + r.length := by simp [hD]; omega
  -- the wire positions of each colour before the swap, numbered
  set φ : Colour → Equiv.Perm (Fin (n + 2)) := fun e =>
    (subwordPerm l e).trans (Colour.numbering e)
  have hw : D.word = l ++ (g, ea) :: (g, eb) :: r := by simp [hD]
  have hL0 : ∀ e G, D.labelAt e l.length G = (Iic G).map (φ e).toEmbedding :=
    D.labelAt_eq_map hw
  have hL1 : ∀ e G, D.labelAt e (l.length + 1) G =
      ((Iic G).map (subwordPerm [(g, ea)] e).toEmbedding).map (φ e).toEmbedding :=
    D.labelAt_append_eq_map (l := l) (m := [(g, ea)]) (r := (g, eb) :: r) (by simp [hD])
  have hL1' : ∀ e G, D'.labelAt e (l.length + 1) G =
      ((Iic G).map (subwordPerm [(g, eb)] e).toEmbedding).map (φ e).toEmbedding :=
    D'.labelAt_append_eq_map (l := l) (m := [(g, eb)]) (r := (g, ea) :: r) (by simp [hD'])
  have hL2 : ∀ e G, D.labelAt e (l.length + 2) G =
      ((Iic G).map (subwordPerm [(g, ea), (g, eb)] e).toEmbedding).map (φ e).toEmbedding :=
    D.labelAt_append_eq_map (l := l) (m := [(g, ea), (g, eb)]) (r := r) hD
  have hperm2 := subwordPerm_pair_of_ne (g := g) hcol
  -- the chambers of `D` at the moments before and after the swap
  obtain ⟨c0, hc0l, -, hc0⟩ := D.exists_chamber_labelAtMinor (t := l.length) (by omega) g.castSucc
  obtain ⟨c2, -, hc2r, hc2⟩ := D.exists_chamber_labelAtMinor (t := l.length + 2) (by omega)
    g.castSucc
  obtain ⟨c3, hc3l, -, hc3⟩ := D.exists_chamber_labelAtMinor (t := l.length) (by omega) g.succ
  obtain ⟨b₁, hb₁, hb₁eq⟩ := D.exists_minor_Iio_castSucc hw g
  refine ⟨doubleExtendedCluster D c0, doubleExtendedCluster D c2, b₁,
    doubleExtendedCluster D c3, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro w (rfl | rfl | rfl | rfl)
    exacts [Or.inr ⟨c0, by omega, rfl⟩, Or.inr ⟨c2, by omega, rfl⟩,
      hb₁.imp_right fun ⟨c, hc, hb⟩ => ⟨c, by omega, hb⟩, Or.inr ⟨c3, by omega, rfl⟩]
  · rw [doubleExtendedCluster_eq_labelAtMinor Y hY.2.1 hY.1,
      doubleExtendedCluster_eq_labelAtMinor Z hZ.2.1 hZ.1, hc0, hc2, hc3, hb₁eq]
    simp only [labelAtMinor]
    rw [hL0, hL0, hL0, hL0, hL1, hL1, hL1', hL1', hL2, hL2, hperm2, hperm2]
    have hA := minor_swap_identity (φ .thick) (φ .thin) g
      (by simpa [φ] using D.lt_of_swap hcol hw .thick)
      (by simpa [φ] using D.lt_of_swap hcol hw .thin)
    cases ea <;> cases eb <;>
      simp only [subwordPerm_singleton, reduceCtorEq, if_true, if_false, map_one_perm] <;>
      first | exact absurd rfl hcol | exact hA | exact (mul_comm _ _).trans hA

/-! ### The braid -/

/-- At a braid `lo, hi, lo` with `hi = lo + 1` after a prefix `l` of the word, the wires of its
colour at the levels `lo.castSucc`, `hi.castSucc`, `hi.succ` are in increasing order. -/
private theorem lt_of_braid (D : DoubleWiringDiagram n) {l r : List (Fin (n + 1) × Colour)}
    {e : Colour} {lo hi : Fin (n + 1)} (hlh : (lo : ℕ) + 1 = hi)
    (hw : D.word = l ++ [(lo, e), (hi, e), (lo, e)] ++ r) :
    subwordPerm l e lo.castSucc < subwordPerm l e hi.castSucc ∧
      subwordPerm l e hi.castSucc < subwordPerm l e hi.succ := by
  have hb : lo.succ = hi.castSucc := Fin.ext (by simpa using hlh)
  refine ⟨by simpa [hb] using
    D.lt_of_word_eq (l := l) (x := (lo, e)) (r := (hi, e) :: (lo, e) :: r) (by simp [hw]), ?_⟩
  have := D.lt_of_word_eq (l := l ++ [(lo, e), (hi, e)]) (x := (lo, e)) (r := r) (by simp [hw])
  have h1 : lo.castSucc ≠ hi.castSucc := by
    simp only [Ne, Fin.ext_iff, Fin.val_castSucc]
    omega
  have h2 : lo.castSucc ≠ hi.succ := by
    simp only [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
    omega
  have h4 : hi.succ ≠ lo.succ := by
    simp only [Ne, Fin.ext_iff, Fin.val_succ]
    omega
  have h2perm : subwordPerm [(lo, e), (hi, e)] e = gapSwap lo * gapSwap hi := by
    simp [subwordPerm, subword]
  rw [subwordPerm_append, h2perm] at this
  simpa only [Equiv.Perm.mul_apply, gapSwap_of_ne _ h1 h2, gapSwap_castSucc, hb,
    gapSwap_of_ne _ h2.symm h4] using this

/-- **The three-term relation for the minors at a braid** `lo, hi, lo` with `hi = lo + 1`, of a
matrix `z` with rows numbered by `φN` and columns by `φT`, the columns of the three wires involved
being in increasing or in decreasing order. -/
private theorem minor_braid_identity {R : Type*} [CommRing R]
    (z : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (φN φT : Equiv.Perm (Fin (n + 2)))
    {lo hi : Fin (n + 1)} (hlh : (lo : ℕ) + 1 = hi)
    (hT : φT lo.castSucc < φT hi.castSucc ∧ φT hi.castSucc < φT hi.succ ∨
      φT hi.succ < φT hi.castSucc ∧ φT hi.castSucc < φT lo.castSucc) :
    minor z ((Iic lo.castSucc).map φN.toEmbedding)
        (((Iic lo.castSucc).map (gapSwap lo).toEmbedding).map φT.toEmbedding) *
      minor z ((Iic hi.castSucc).map φN.toEmbedding)
        (((Iic hi.castSucc).map (gapSwap hi).toEmbedding).map φT.toEmbedding) =
    minor z ((Iic lo.castSucc).map φN.toEmbedding) ((Iic lo.castSucc).map φT.toEmbedding) *
        minor z ((Iic hi.castSucc).map φN.toEmbedding)
          (((((Iic hi.castSucc).map (gapSwap lo).toEmbedding).map (gapSwap hi).toEmbedding).map
            (gapSwap lo).toEmbedding).map φT.toEmbedding) +
      minor z ((Iic lo.castSucc).map φN.toEmbedding)
          (((((Iic lo.castSucc).map (gapSwap lo).toEmbedding).map (gapSwap hi).toEmbedding).map
            (gapSwap lo).toEmbedding).map φT.toEmbedding) *
        minor z ((Iic hi.castSucc).map φN.toEmbedding) ((Iic hi.castSucc).map φT.toEmbedding) := by
  have hb : lo.succ = hi.castSucc := Fin.ext (by simpa using hlh)
  have hb' : (Iic lo.castSucc).map (gapSwap lo).toEmbedding = Iio lo.castSucc ∪ {hi.castSucc} := by
    rw [map_gapSwap_Iic_castSucc, hb]
  have hlohi : lo.castSucc ≤ hi.castSucc := by
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc]
    omega
  have hn1 : ¬hi.castSucc < lo.castSucc := not_lt.2 hlohi
  have hn2 : ¬hi.succ < lo.castSucc := by
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    omega
  have hsub : (Iic lo.castSucc).map φN.toEmbedding ⊆ (Iic hi.castSucc).map φN.toEmbedding :=
    map_subset_map.2 (Iic_subset_Iic.2 hlohi)
  have hc0 : ((Iic lo.castSucc).map φN.toEmbedding).card =
      ((Iio lo.castSucc).map φT.toEmbedding).card + 1 := by
    simp
  have hc1 : ((Iic hi.castSucc).map φN.toEmbedding).card =
      ((Iio lo.castSucc).map φT.toEmbedding).card + 2 := by
    simp
    omega
  rw [map_braid_Iic_castSucc hlh, map_braid_Iic_castSucc_of_succ hlh, hb',
    map_gapSwap_Iic_castSucc_of_succ hlh]
  set K0 := (Iic lo.castSucc).map φN.toEmbedding
  set K1 := (Iic hi.castSucc).map φN.toEmbedding
  rw [Iic_castSucc_eq, Iic_castSucc_eq_of_succ hlh]
  simp only [map_union, map_singleton, map_insert, Equiv.coe_toEmbedding]
  rcases hT with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact minor_nested_three_term (by omega) z _ (by simp) (by simp [hn1]) (by simp [hn2]) h₁ h₂
      hsub hc0 hc1
  · have := minor_nested_three_term (by omega) z ((Iio lo.castSucc).map φT.toEmbedding)
      (by simp [hn2]) (by simp [hn1]) (by simp) h₁ h₂ hsub hc0 hc1
    rw [pair_comm (φT hi.succ) (φT lo.castSucc), pair_comm (φT hi.succ) (φT hi.castSucc),
      pair_comm (φT hi.castSucc) (φT lo.castSucc)] at this
    exact this.trans (add_comm _ _)

/-- **The three-term relation among the labels at a braid.** For `E` with the crossings
`lo, hi, lo` and `F` with `hi, lo, hi` after a common prefix `l`, where `hi = lo + 1`, the minors
of the labels of `E` and `F` in between satisfy the three-term relation whose other four minors
are labels of `E` before and after the three crossings. -/
private theorem braid_identity {E F : DoubleWiringDiagram n} {l r : List (Fin (n + 1) × Colour)}
    {e : Colour} {lo hi : Fin (n + 1)} (hlh : (lo : ℕ) + 1 = hi)
    (hE : E.word = l ++ [(lo, e), (hi, e), (lo, e)] ++ r)
    (hF : F.word = l ++ [(hi, e), (lo, e), (hi, e)] ++ r) :
    E.labelAtMinor (l.length + 1) lo.castSucc * F.labelAtMinor (l.length + 1) hi.castSucc =
      E.labelAtMinor l.length lo.castSucc * E.labelAtMinor (l.length + 3) hi.castSucc +
        E.labelAtMinor (l.length + 3) lo.castSucc * E.labelAtMinor l.length hi.castSucc := by
  set φ : Colour → Equiv.Perm (Fin (n + 2)) := fun c =>
    (subwordPerm l c).trans (Colour.numbering c)
  have hE0 : ∀ c G, E.labelAt c l.length G = (Iic G).map (φ c).toEmbedding :=
    E.labelAt_eq_map (l := l) (r := (lo, e) :: (hi, e) :: (lo, e) :: r) (by simp [hE])
  have hE1 : ∀ c G, E.labelAt c (l.length + 1) G =
      ((Iic G).map (subwordPerm [(lo, e)] c).toEmbedding).map (φ c).toEmbedding :=
    E.labelAt_append_eq_map (l := l) (m := [(lo, e)]) (r := (hi, e) :: (lo, e) :: r) (by simp [hE])
  have hF1 : ∀ c G, F.labelAt c (l.length + 1) G =
      ((Iic G).map (subwordPerm [(hi, e)] c).toEmbedding).map (φ c).toEmbedding :=
    F.labelAt_append_eq_map (l := l) (m := [(hi, e)]) (r := (lo, e) :: (hi, e) :: r) (by simp [hF])
  have hE3 : ∀ c G, E.labelAt c (l.length + 3) G =
      ((Iic G).map (subwordPerm [(lo, e), (hi, e), (lo, e)] c).toEmbedding).map
        (φ c).toEmbedding :=
    E.labelAt_append_eq_map (l := l) (m := [(lo, e), (hi, e), (lo, e)]) (r := r) hE
  obtain ⟨hπ1, hπ2⟩ := E.lt_of_braid hlh hE
  -- the labels, as images of sets of levels
  have h3 : ∀ G, (Iic G).map (gapSwap lo * gapSwap hi * gapSwap lo).toEmbedding =
      (((Iic G).map (gapSwap lo).toEmbedding).map (gapSwap hi).toEmbedding).map
        (gapSwap lo).toEmbedding := fun G => by
    rw [map_perm_mul, map_perm_mul]
  have hO : ∀ G, (Iic G).map (subwordPerm [(lo, e), (hi, e), (lo, e)] e.swap).toEmbedding =
      Iic G := fun G => by rw [subwordPerm_triple_swap, map_one_perm]
  have hO1 : ∀ (x : Fin (n + 1)) G, (Iic G).map (subwordPerm [(x, e)] e.swap).toEmbedding =
      Iic G := fun x G => by rw [subwordPerm_single_swap, map_one_perm]
  simp only [labelAtMinor]
  rw [hE0, hE0, hE0, hE0, hE1, hE1, hF1, hF1, hE3, hE3, hE3, hE3]
  cases e
  · -- thick: the three-term relation for the generic matrix
    simp only [Colour.swap_thick] at hO hO1
    rw [hO, hO, hO1, hO1, subwordPerm_single, subwordPerm_single, subwordPerm_triple, h3, h3]
    exact minor_braid_identity _ (φ .thin) (φ .thick) hlh (Or.inl ⟨hπ1, hπ2⟩)
  · -- thin: the three-term relation for the transpose of the generic matrix
    simp only [Colour.swap_thin] at hO hO1
    rw [hO, hO, hO1, hO1, subwordPerm_single, subwordPerm_single, subwordPerm_triple, h3, h3]
    simpa only [minor_transpose] using
      minor_braid_identity (genericMatrix (Fin (n + 2)) (Fin (n + 2))).transpose (φ .thick)
        (φ .thin) hlh (Or.inr ⟨Fin.rev_lt_rev.2 hπ2, Fin.rev_lt_rev.2 hπ1⟩)

/-- The two sides of a braid give the same labels before and after it. -/
private theorem labelAtMinor_braid {E F : DoubleWiringDiagram n}
    {l r : List (Fin (n + 1) × Colour)} {e : Colour} {lo hi : Fin (n + 1)}
    (hlh : (lo : ℕ) + 1 = hi) (hE : E.word = l ++ [(lo, e), (hi, e), (lo, e)] ++ r)
    (hF : F.word = l ++ [(hi, e), (lo, e), (hi, e)] ++ r) (G : Fin (n + 2)) :
    F.labelAtMinor l.length G = E.labelAtMinor l.length G ∧
      F.labelAtMinor (l.length + 3) G = E.labelAtMinor (l.length + 3) G := by
  have h0 : ∀ c, F.labelAt c l.length G = E.labelAt c l.length G := fun c => by
    rw [F.labelAt_eq_map (l := l) (r := [(hi, e), (lo, e), (hi, e)] ++ r) (by simp [hF]),
      E.labelAt_eq_map (l := l) (r := [(lo, e), (hi, e), (lo, e)] ++ r) (by simp [hE])]
  have h3 : ∀ c, F.labelAt c (l.length + 3) G = E.labelAt c (l.length + 3) G := fun c => by
    have a : F.labelAt c (l.length + 3) G = _ :=
      F.labelAt_append_eq_map (l := l) (m := [(hi, e), (lo, e), (hi, e)]) (r := r) hF c G
    have b : E.labelAt c (l.length + 3) G = _ :=
      E.labelAt_append_eq_map (l := l) (m := [(lo, e), (hi, e), (lo, e)]) (r := r) hE c G
    rw [a, b, subwordPerm_braid hlh]
  exact ⟨by rw [labelAtMinor, labelAtMinor, h0, h0], by rw [labelAtMinor, labelAtMinor, h3, h3]⟩

/-- **The exchange at a braid.** Let `D'` be obtained from `D` by the braid at the 0-based
position `p`, and let `Y` (of gap the level of `D` at `p`) and `Z` (of gap the level of `D'` at
`p`) be the chambers of `D` and `D'` with span `(p + 1, p + 3)`. Then there are chambers
`c₁, c₂, c₃, c₄` of `D`, none of span `(p + 1, p + 3)`, with
`Δ(Y) Δ(Z) = Δ(c₁) Δ(c₂) + Δ(c₃) Δ(c₄)`. -/
@[cluster_algebras "lem_double_braid_exchange"]
theorem IsBraid.exists_exchange {D D' : DoubleWiringDiagram n} {p : ℕ} (h : D.IsBraid D' p)
    (Y : D.Chamber) (hY : Y.gap = D.levelAt p ∧ Y.left = p + 1 ∧ Y.right = p + 3)
    (Z : D'.Chamber) (hZ : Z.gap = D'.levelAt p ∧ Z.left = p + 1 ∧ Z.right = p + 3) :
    ∃ c₁ c₂ c₃ c₄ : D.Chamber,
      (∀ c ∈ [c₁, c₂, c₃, c₄], ¬(c.left = p + 1 ∧ c.right = p + 3)) ∧
      doubleExtendedCluster D Y * doubleExtendedCluster D' Z =
        doubleExtendedCluster D c₁ * doubleExtendedCluster D c₂ +
          doubleExtendedCluster D c₃ * doubleExtendedCluster D c₄ := by
  obtain ⟨l, r, e, g, h, hgh, rfl, hD, hD'⟩ := h
  rw [(D.levelAt_colourAt_of_word_eq (l := l) (x := (g, e)) (r := (h, e) :: (g, e) :: r)
    (by simp [hD])).1] at hY
  rw [(D'.levelAt_colourAt_of_word_eq (l := l) (x := (h, e)) (r := (g, e) :: (h, e) :: r)
    (by simp [hD'])).1] at hZ
  have hlen : D.word.length = l.length + 3 + r.length := by simp [hD]; omega
  rw [doubleExtendedCluster_eq_labelAtMinor Y hY.2.1 hY.1,
    doubleExtendedCluster_eq_labelAtMinor Z hZ.2.1 hZ.1]
  -- the chambers of `D` at the moments before and after the braid, in the two gaps
  obtain ⟨cg0, hcg0, -, hcg0'⟩ := D.exists_chamber_labelAtMinor (t := l.length) (by omega)
    g.castSucc
  obtain ⟨ch0, hch0, -, hch0'⟩ := D.exists_chamber_labelAtMinor (t := l.length) (by omega)
    h.castSucc
  obtain ⟨cg3, -, hcg3, hcg3'⟩ := D.exists_chamber_labelAtMinor (t := l.length + 3) (by omega)
    g.castSucc
  obtain ⟨ch3, -, hch3, hch3'⟩ := D.exists_chamber_labelAtMinor (t := l.length + 3) (by omega)
    h.castSucc
  rcases hgh with hgh | hgh
  · -- `D` has the crossings `g, g + 1, g`
    refine ⟨cg0, ch3, cg3, ch0, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl | rfl) <;> omega
    · rw [hcg0', hch3', hcg3', hch0']
      exact braid_identity hgh hD hD'
  · -- `D'` has the crossings `h, h + 1, h`
    refine ⟨ch0, cg3, ch3, cg0, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl | rfl) <;> omega
    · rw [hcg0', hch3', hcg3', hch0', mul_comm, (labelAtMinor_braid hgh hD' hD _).1,
        (labelAtMinor_braid hgh hD' hD _).1, (labelAtMinor_braid hgh hD' hD _).2,
        (labelAtMinor_braid hgh hD' hD _).2]
      exact braid_identity hgh hD' hD

end DoubleWiringDiagram

end ClusterAlgebras
