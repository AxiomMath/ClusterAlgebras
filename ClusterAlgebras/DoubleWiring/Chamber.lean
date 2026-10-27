/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.DoubleWiring.Basic

/-!
# Chambers of a double wiring diagram

A chamber is a gap together with a count of how many of that gap's crossings lie to its left,
exactly as in `ClusterAlgebras.WiringDiagram.Chamber` — the only differences being that the
crossings of a gap are pooled over both colours, and that the gap set has one more element, whose
multiplicity is zero.

## Main results

* `card_chamber`: a double wiring diagram has `(n + 2) ^ 2` chambers, since each gap holds
  `multiplicity g + 1` chambers and the multiplicities sum to the word's length.
* `card_bounded_chamber`: exactly `(n + 1) ^ 2` of the chambers are bounded.

Neither count depends on the word.
-/

@[expose] public section

namespace ClusterAlgebras

namespace DoubleWiringDiagram

variable {n : ℕ} (D : DoubleWiringDiagram n)

/-- **Every gap but the top one is crossed.** The thick family alone crosses it, by
`one_le_multiplicity` for that family's own wiring diagram; pooling the colours can only
raise the count. This is what makes each such gap's two unbounded chambers distinct. -/
theorem one_le_multiplicity {g : Fin (n + 1)} : 1 ≤ D.multiplicity g.castSucc := by
  have h1 : 1 ≤ (D.toWiringDiagram .thick).multiplicity g :=
    (D.toWiringDiagram .thick).one_le_multiplicity g
  rw [WiringDiagram.multiplicity, word_toWiringDiagram] at h1
  have hmem : g ∈ subword D.word Colour.thick := List.count_pos_iff.1 h1
  rw [subword, List.mem_map] at hmem
  obtain ⟨x, hx, rfl⟩ := hmem
  rw [List.mem_filter] at hx
  rw [multiplicity, Nat.one_le_iff_ne_zero, ne_eq, List.count_eq_zero, not_not, levels]
  exact List.mem_map.2 ⟨x, hx.1, rfl⟩

/-- A gap is crossed exactly when it is not the top one. -/
theorem multiplicity_eq_zero_iff {g : Fin (n + 2)} :
    D.multiplicity g = 0 ↔ g = Fin.last _ := by
  refine ⟨fun h => ?_, fun h => by rw [h, D.multiplicity_last]⟩
  by_contra hg
  obtain ⟨g', rfl⟩ := Fin.exists_castSucc_eq.2 hg
  have := D.one_le_multiplicity (g := g')
  omega

/-- Nothing precedes the first position. -/
@[simp]
theorem countUpTo_zero (g : Fin (n + 2)) : D.countUpTo g 0 = 0 := by
  simp [countUpTo]

/-- By the end of the word a gap's count has reached its multiplicity. -/
theorem countUpTo_length (g : Fin (n + 2)) :
    D.countUpTo g D.word.length = D.multiplicity g := by
  rw [countUpTo, List.take_of_length_le (by simp), multiplicity]

/-- Each position raises a gap's count by one if it is crossed there, and not otherwise. -/
theorem countUpTo_succ {g : Fin (n + 2)} {t : ℕ} (ht : t < D.word.length) :
    D.countUpTo g (t + 1) = D.countUpTo g t + if D.levelAt t = g then 1 else 0 := by
  have htl : t < D.levels.length := by simpa using ht
  rw [countUpTo, countUpTo, List.take_add_one, List.count_append,
    List.getElem?_eq_getElem htl]
  simp [List.count_cons, D.levels_getElem ht]

/-- The count is monotone in the position. -/
theorem countUpTo_le_of_le {g : Fin (n + 2)} {s t : ℕ} (h : s ≤ t) :
    D.countUpTo g s ≤ D.countUpTo g t :=
  count_take_mono g h

attribute [cluster_algebras "def_double_chamber"] Chamber

namespace Chamber

variable {D} (c : D.Chamber)

/-- Two chambers agreeing in gap and index are equal. -/
theorem ext' {c c' : D.Chamber} (hg : c.gap = c'.gap) (hi : c.idx = c'.idx) : c = c' := by
  cases c
  cases c'
  subst hg hi
  rfl

/-- Chambers are a gap and an index, so equality is decidable. -/
instance instDecidableEq : DecidableEq D.Chamber := fun c c' =>
  decidable_of_iff (c.gap = c'.gap ∧ c.idx = c'.idx)
    ⟨fun h => ext' h.1 h.2, fun h => by simp [h]⟩

/-- The positions the chamber spans: those preceded by exactly `c.idx` crossings of its gap. -/
def InSpan (t : ℕ) : Prop := D.countUpTo c.gap t = c.idx

attribute [cluster_algebras "def_double_chamber_ends"] HasLeftEnd

attribute [cluster_algebras "def_double_chamber_ends"] HasRightEnd

attribute [cluster_algebras "def_double_chamber_ends"] Bounded

/-- **The colour of the left end**: an end is a crossing, and the crossing bounding the span on
the left sits at the position just before it. Meaningful only when `c.HasLeftEnd`. -/
@[cluster_algebras "def_double_chamber_ends"]
def leftEndColour : Colour := D.colourAt (c.left - 1)

/-- **The colour of the right end.** Meaningful only when `c.HasRightEnd`. -/
@[cluster_algebras "def_double_chamber_ends"]
def rightEndColour : Colour := D.colourAt (c.right - 1)

/-- Reading the chamber's count at its own left position gives its index. -/
theorem inSpan_left : c.InSpan c.left :=
  countUpTo_take_spanStart c.gap c.idx D.levels c.idx_le

/-- A chamber lacks its left end exactly when it is the first of its gap. -/
theorem left_eq_zero_iff : c.left = 0 ↔ c.idx = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [left, h, spanStart_zero]⟩
  simpa [InSpan, h, eq_comm] using c.inSpan_left

/-- A chamber lacks its right end exactly when it is the last of its gap. -/
theorem right_eq_top_iff : c.right = D.word.length + 1 ↔ c.idx = D.multiplicity c.gap := by
  refine ⟨fun h => ?_, fun h => by rw [right, if_pos h]⟩
  by_contra hi
  rw [right, if_neg hi] at h
  have hle : c.idx + 1 ≤ D.multiplicity c.gap := Nat.lt_of_le_of_ne c.idx_le hi
  have := spanStart_le_length c.gap (c.idx + 1) D.levels hle
  rw [D.length_levels] at this
  omega

/-- **An unbounded chamber is the first or the last of its gap.** For a gap other than the top
one those are two different chambers, each with one end; the top gap has the single chamber
`(last, 0)`, which is both and so has no end at all. -/
@[cluster_algebras "def_double_chamber_ends"]
theorem not_bounded_iff : ¬c.Bounded ↔ c.idx = 0 ∨ c.idx = D.multiplicity c.gap := by
  rw [Bounded, HasLeftEnd, HasRightEnd, not_and_or, not_ne_iff, not_ne_iff,
    c.left_eq_zero_iff, c.right_eq_top_iff]

/-! ### Where a chamber's ends are

The quiver's arrow conditions are inequalities between the two ends of two chambers, and its
two-cycle-freeness turns on one fact that the inequalities do not carry: **a crossing bounding a
chamber lies in that chamber's own gap**, so two chambers in different gaps cannot share an end.
Everything below exists to supply that. -/

/-- A chamber's left position is a genuine position. -/
theorem left_le_length : c.left ≤ D.word.length := by
  have := spanStart_le_length c.gap c.idx D.levels c.idx_le
  rwa [D.length_levels] at this

/-- A chamber's right position is at most the `+∞` sentinel. -/
theorem right_le_top : c.right ≤ D.word.length + 1 := by
  by_cases h : c.idx = D.multiplicity c.gap
  · rw [right, if_pos h]
  · rw [right, if_neg h]
    have := spanStart_le_length c.gap (c.idx + 1) D.levels (Nat.lt_of_le_of_ne c.idx_le h)
    rw [D.length_levels] at this
    omega

/-- The left position is the least position of the span. -/
theorem left_le {t : ℕ} (h : c.InSpan t) : c.left ≤ t :=
  spanStart_le_of_count c.gap c.idx t D.levels h

/-- Where a bounded-on-the-right chamber's gap is next crossed. -/
theorem countUpTo_right (h : c.idx ≠ D.multiplicity c.gap) :
    D.countUpTo c.gap c.right = c.idx + 1 := by
  rw [right, if_neg h]
  exact countUpTo_take_spanStart c.gap (c.idx + 1) D.levels (Nat.lt_of_le_of_ne c.idx_le h)

/-- **A chamber's span is nonempty**, which is what makes a loop impossible in the quiver. -/
theorem left_lt_right : c.left < c.right := by
  by_cases h : c.idx = D.multiplicity c.gap
  · rw [right, if_pos h]
    have := c.left_le_length
    omega
  · by_contra hc
    have h1 := c.inSpan_left
    have h2 := c.countUpTo_right h
    have h3 := D.countUpTo_le_of_le (g := c.gap) (Nat.le_of_not_lt hc)
    rw [InSpan] at h1
    omega

/-- **The crossing at a chamber's left end lies in the chamber's own gap.** -/
theorem levelAt_of_left_eq_succ {t : ℕ} (h : c.left = t + 1) : D.levelAt t = c.gap := by
  by_contra hne
  have ht : t < D.word.length := by
    have := c.left_le_length
    omega
  have hs : D.countUpTo c.gap (t + 1) = c.idx := by simpa [InSpan, h] using c.inSpan_left
  rw [D.countUpTo_succ ht, if_neg hne] at hs
  have := c.left_le (t := t) (by rw [InSpan]; omega)
  omega

/-- **The crossing at a chamber's right end lies in the chamber's own gap**, the mirror. -/
theorem levelAt_of_right_eq_succ {t : ℕ} (h : c.right = t + 1) (ht : t < D.word.length) :
    D.levelAt t = c.gap := by
  have hne : c.idx ≠ D.multiplicity c.gap := fun hc => by
    have := c.right_eq_top_iff.2 hc
    omega
  by_contra hcon
  have hs : D.countUpTo c.gap (t + 1) = c.idx + 1 := h ▸ c.countUpTo_right hne
  rw [D.countUpTo_succ ht, if_neg hcon] at hs
  have hs' : (D.levels.take t).count c.gap = c.idx + 1 := by
    simpa [countUpTo] using hs
  have hle : c.right ≤ t := by
    rw [right, if_neg hne]
    exact spanStart_le_of_count c.gap (c.idx + 1) t D.levels hs'
  omega

/-- **Two chambers in different gaps do not begin at the same crossing.** A shared left end would
be one position carrying a crossing of each of their gaps. -/
theorem left_eq_zero_of_gap_ne {c c' : D.Chamber} (hg : c.gap ≠ c'.gap)
    (h : c.left = c'.left) : c.left = 0 := by
  by_contra h0
  have h1 := c.levelAt_of_left_eq_succ (by omega : c.left = (c.left - 1) + 1)
  have h2 := c'.levelAt_of_left_eq_succ (by omega : c'.left = (c.left - 1) + 1)
  exact hg (h1.symm.trans h2)

/-- **Two chambers in different gaps do not end at the same crossing.** -/
theorem right_eq_top_of_gap_ne {c c' : D.Chamber} (hg : c.gap ≠ c'.gap)
    (h : c.right = c'.right) : c.right = D.word.length + 1 := by
  by_contra hne
  have hle := c.right_le_top
  have hpos := c.left_lt_right
  have ht : c.right - 1 < D.word.length := by omega
  have h1 := c.levelAt_of_right_eq_succ (by omega : c.right = (c.right - 1) + 1) ht
  have h2 := c'.levelAt_of_right_eq_succ (by omega : c'.right = (c.right - 1) + 1) ht
  exact hg (h1.symm.trans h2)

/-- **Chambers in adjacent gaps cannot have the same span.** This is the one fact the arrow
inequalities do not carry, and the only place two-cycle-freeness needs more than arithmetic:
equal ends force both to be the sentinels, so each chamber is the only one of its gap, so each
gap is uncrossed -- and only the top gap is. -/
theorem not_span_eq_of_gap_adjacent {c c' : D.Chamber}
    (hadj : (c'.gap : ℕ) + 1 = (c.gap : ℕ) ∨ (c.gap : ℕ) + 1 = (c'.gap : ℕ))
    (hl : c.left = c'.left) (hr : c.right = c'.right) : False := by
  have hg : c.gap ≠ c'.gap := fun h => by rw [h] at hadj; omega
  have h0 : c.idx = 0 := c.left_eq_zero_iff.1 (left_eq_zero_of_gap_ne hg hl)
  have h0' : c'.idx = 0 := c'.left_eq_zero_iff.1 (left_eq_zero_of_gap_ne hg.symm hl.symm)
  have h1 : c.idx = D.multiplicity c.gap :=
    c.right_eq_top_iff.1 (right_eq_top_of_gap_ne hg hr)
  have h1' : c'.idx = D.multiplicity c'.gap :=
    c'.right_eq_top_iff.1 (right_eq_top_of_gap_ne hg.symm hr.symm)
  have e1 := D.multiplicity_eq_zero_iff.1 (by omega : D.multiplicity c.gap = 0)
  have e2 := D.multiplicity_eq_zero_iff.1 (by omega : D.multiplicity c'.gap = 0)
  exact hg (e1.trans e2.symm)

end Chamber

/-- **A double wiring diagram has `(n + 2) ^ 2` chambers.**

The count does not depend on the word. Each gap holds `multiplicity g + 1` chambers and the
multiplicities sum to the word's length, which is `(n + 2) * (n + 1)`, so the total is
`(n + 2) * (n + 1) + (n + 2)`. -/
@[cluster_algebras "lem_double_chamber_count"]
theorem card_chamber : Fintype.card D.Chamber = (n + 2) ^ 2 := by
  rw [Fintype.card_congr D.chamberEquiv, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_add_distrib, D.sum_multiplicity, D.length_word]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  ring

/-! ### The bounded chambers

An unbounded chamber is the first or the last of its gap, so the unbounded ones are covered by two
families indexed by the gaps. The two families are each injective and meet only at the top gap,
where the single chamber is both first and last — which is inclusion–exclusion, and is where the
top gap's multiplicity being zero does its work. -/

/-- The first chamber of a gap: the one with nothing of its gap to its left. -/
def firstChamber (g : Fin (n + 2)) : D.Chamber := ⟨g, 0, Nat.zero_le _⟩

/-- The last chamber of a gap: the one with all of its gap to its left. -/
def lastChamber (g : Fin (n + 2)) : D.Chamber := ⟨g, D.multiplicity g, le_rfl⟩

/-- Distinct gaps have distinct first chambers, the gap being recoverable. -/
theorem firstChamber_injective : Function.Injective D.firstChamber :=
  fun _ _ h => congrArg Chamber.gap h

/-- Distinct gaps have distinct last chambers. -/
theorem lastChamber_injective : Function.Injective D.lastChamber :=
  fun _ _ h => congrArg Chamber.gap h

/-- **The unbounded chambers are exactly the first and last of each gap.** -/
theorem filter_not_bounded :
    Finset.univ.filter (fun c : D.Chamber => ¬c.Bounded) =
      Finset.image D.firstChamber Finset.univ ∪ Finset.image D.lastChamber Finset.univ := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
  rw [c.not_bounded_iff]
  exact or_congr ⟨fun h => ⟨c.gap, Chamber.ext' rfl h.symm⟩, fun ⟨_, hg⟩ => hg ▸ rfl⟩
    ⟨fun h => ⟨c.gap, Chamber.ext' rfl h.symm⟩, fun ⟨_, hg⟩ => hg ▸ rfl⟩

/-- The two families meet only over the top gap, whose one chamber is both first and last. -/
theorem image_first_inter_image_last :
    Finset.image D.firstChamber Finset.univ ∩ Finset.image D.lastChamber Finset.univ =
      {D.firstChamber (Fin.last _)} := by
  ext c
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨g, hg⟩, ⟨g', rfl⟩⟩
    -- the chamber is last of its gap and also first, so that gap is crossed no times
    have hidx : (0 : ℕ) = D.multiplicity g' := congrArg Chamber.idx hg
    exact Chamber.ext' (D.multiplicity_eq_zero_iff.1 hidx.symm) hidx.symm
  · rintro rfl
    exact ⟨⟨Fin.last _, rfl⟩, ⟨Fin.last _, Chamber.ext' rfl D.multiplicity_last⟩⟩

/-- **Of the `(n + 2) ^ 2` chambers, exactly `(n + 1) ^ 2` are bounded.**

Each of the `n + 2` gaps contributes a first and a last chamber, and those coincide only for the
top gap, so `2 * (n + 2) - 1 = 2 * n + 3` chambers are unbounded. -/
@[cluster_algebras "lem_double_chamber_count"]
theorem card_bounded_chamber :
    (Finset.univ.filter (fun c : D.Chamber => c.Bounded)).card = (n + 1) ^ 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset D.Chamber)) (p := fun c => c.Bounded)
  -- omega cannot see through `^ 2`, so the two squares are bridged by `ring` first
  have hbridge : (n + 1) ^ 2 + (2 * n + 3) = (n + 2) ^ 2 := by ring
  have hun : (Finset.univ.filter (fun c : D.Chamber => ¬c.Bounded)).card = 2 * n + 3 := by
    have hie := Finset.card_union_add_card_inter
      (Finset.image D.firstChamber Finset.univ) (Finset.image D.lastChamber Finset.univ)
    rw [D.image_first_inter_image_last, Finset.card_singleton,
      Finset.card_image_of_injective _ D.firstChamber_injective,
      Finset.card_image_of_injective _ D.lastChamber_injective, Finset.card_univ,
      Fintype.card_fin] at hie
    rw [D.filter_not_bounded]
    omega
  rw [Finset.card_univ, D.card_chamber] at hsplit
  omega

end DoubleWiringDiagram

end ClusterAlgebras
