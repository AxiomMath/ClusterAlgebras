/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.WiringDiagram.Basic

/-!
# Chambers of a wiring diagram, and its quiver

For each gap, the crossings of that gap cut the position axis into pieces; these pieces are the
chambers, and the quiver `Q(D)` has them as its vertices. This file defines chambers and
their ends, the chamber set each carries, the chamber at a given position, and `Q(D)` itself.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

namespace WiringDiagram

variable (D : WiringDiagram n)

/-! ### Chambers

For each gap, the crossings of that gap cut the position axis into stretches, the chambers of
that gap. The stretch a position lies in is recorded by the number of crossings of the gap before
it, so a chamber's span is described by a count rather than by a pair of extended integers. Its
left and right positions are the ends of that stretch, with `0` and `word.length + 1` standing
for `-∞` and `+∞`; these sentinels compare correctly with the positions `1, …, N`. -/

/-- `countUpTo` is the count over a prefix of the word, by definition. -/
theorem countUpTo_def (g : Fin (n + 1)) (t : ℕ) :
    D.countUpTo g t = (D.word.take t).count g := rfl

/-- No crossings precede the first position. -/
@[simp]
theorem countUpTo_zero (g : Fin (n + 1)) : D.countUpTo g 0 = 0 := by simp [countUpTo]

/-- Passing a position increments the count exactly when that crossing has the given gap. -/
theorem countUpTo_succ {g : Fin (n + 1)} {t : ℕ} (ht : t < D.word.length) :
    D.countUpTo g (t + 1) = D.countUpTo g t + (if D.levelAt t = g then 1 else 0) := by
  rw [countUpTo, countUpTo, List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some,
    List.count_append, levelAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    Option.getD_some]
  by_cases h : D.word[t] = g <;> simp [h]

/-- Counting over the whole word gives the multiplicity. -/
theorem countUpTo_length (g : Fin (n + 1)) :
    D.countUpTo g D.word.length = D.multiplicity g := by
  rw [countUpTo, List.take_of_length_le le_rfl, multiplicity]

/-- The count climbs by at most one per position. -/
theorem countUpTo_succ_le {g : Fin (n + 1)} {t : ℕ} (ht : t < D.word.length) :
    D.countUpTo g (t + 1) ≤ D.countUpTo g t + 1 := by
  rw [D.countUpTo_succ ht]
  split_ifs <;> omega

/-- The count is monotone in the position. -/
theorem countUpTo_le_of_le {g : Fin (n + 1)} {t t' : ℕ} (h : t ≤ t')
    (_ht' : t' ≤ D.word.length) : D.countUpTo g t ≤ D.countUpTo g t' :=
  count_take_mono g h

/-- **The count of a gap's crossings takes every value up to its value at `t`.** It starts at
zero and climbs in steps of at most one, so it omits nothing along the way. -/
theorem exists_countUpTo_eq_le {g : Fin (n + 1)} {j t : ℕ} (ht : t ≤ D.word.length)
    (hj : j ≤ D.countUpTo g t) : ∃ s ≤ t, D.countUpTo g s = j := by
  induction t with
  | zero =>
    rw [D.countUpTo_zero] at hj
    exact ⟨0, le_rfl, by rw [D.countUpTo_zero]; omega⟩
  | succ r ih =>
    have hstep := D.countUpTo_succ (g := g) (t := r) (by omega)
    by_cases h : j ≤ D.countUpTo g r
    · obtain ⟨s, hs, hse⟩ := ih (by omega) h
      exact ⟨s, by omega, hse⟩
    · refine ⟨r + 1, le_rfl, ?_⟩
      split_ifs at hstep <;> omega

/-- **The count of a gap's crossings takes every value up to its multiplicity.** This is what
makes a chamber's span nonempty. -/
theorem exists_countUpTo_eq {g : Fin (n + 1)} {j : ℕ} (hj : j ≤ D.multiplicity g) :
    ∃ t ≤ D.word.length, D.countUpTo g t = j :=
  D.exists_countUpTo_eq_le le_rfl (by rw [D.countUpTo_length]; exact hj)

attribute [cluster_algebras "def_chamber"] Chamber

namespace Chamber

variable {D} (c : D.Chamber)

/-- The positions the chamber spans: those preceded by exactly `c.idx` crossings of its gap. -/
def InSpan (t : ℕ) : Prop := D.countUpTo c.gap t = c.idx

/-- Whether a position lies in a chamber's span is decidable, being an equation between two
natural numbers. -/
instance instDecidablePredInSpan : DecidablePred c.InSpan := fun t =>
  inferInstanceAs (Decidable (D.countUpTo c.gap t = c.idx))

/-- Some position lies in the chamber's span. -/
theorem exists_inSpan : ∃ t, c.InSpan t :=
  (D.exists_countUpTo_eq c.idx_le).imp fun _ h => h.2

/-- The left position of a chamber lies in its span. -/
theorem inSpan_left : c.InSpan c.left :=
  countUpTo_take_spanStart c.gap c.idx D.word c.idx_le

/-- The left position is the least position of the span. -/
theorem left_le {t : ℕ} (h : c.InSpan t) : c.left ≤ t :=
  spanStart_le_of_count c.gap c.idx t D.word h

/-- The chamber's gap is crossed at least `c.idx + 1` times unless the chamber is the last of
its gap; that is what makes its right position a genuine position. -/
theorem le_multiplicity_succ (h : c.idx ≠ D.multiplicity c.gap) :
    c.idx + 1 ≤ D.multiplicity c.gap := Nat.lt_of_le_of_ne c.idx_le h

/-- The right position of a bounded-on-the-right chamber is where its gap is next crossed. -/
theorem countUpTo_right (h : c.idx ≠ D.multiplicity c.gap) :
    D.countUpTo c.gap c.right = c.idx + 1 := by
  rw [right, if_neg h]
  exact countUpTo_take_spanStart c.gap (c.idx + 1) D.word (c.le_multiplicity_succ h)

/-- A chamber that is not the last of its gap has a genuine right position. -/
theorem right_le_length (h : c.idx ≠ D.multiplicity c.gap) : c.right ≤ D.word.length := by
  rw [right, if_neg h]
  exact spanStart_le_length c.gap (c.idx + 1) D.word (c.le_multiplicity_succ h)

attribute [cluster_algebras "def_chamber_ends"] HasLeftEnd

attribute [cluster_algebras "def_chamber_ends"] HasRightEnd

attribute [cluster_algebras "def_chamber_ends"] Bounded

/-- A chamber lacks its left end exactly when it is the first of its gap. -/
theorem left_eq_zero_iff : c.left = 0 ↔ c.idx = 0 :=
  ⟨fun h => by
    have hs := c.inSpan_left
    rw [InSpan, h, D.countUpTo_zero] at hs
    exact hs.symm,
   fun h => Nat.le_zero.1 (c.left_le (by rw [InSpan, D.countUpTo_zero, h]))⟩

/-- A chamber lacks its right end exactly when it is the last of its gap. -/
theorem right_eq_top_iff : c.right = D.word.length + 1 ↔ c.idx = D.multiplicity c.gap :=
  ⟨fun heq => by
    -- otherwise the right position is a genuine position, so cannot be the `+∞` sentinel
    by_contra h
    have := c.right_le_length h
    omega,
   fun h => by rw [right, if_pos h]⟩

/-- **An unbounded chamber has exactly one end.** A chamber fails to be bounded exactly when
it is the first or the last of its gap; the first lacks only its left end and the last only its
right end. -/
@[cluster_algebras "lem_unbounded_one_end"]
theorem not_bounded_iff : ¬c.Bounded ↔ c.idx = 0 ∨ c.idx = D.multiplicity c.gap := by
  rw [Bounded, HasLeftEnd, HasRightEnd, not_and_or, not_ne_iff, not_ne_iff,
    c.left_eq_zero_iff, c.right_eq_top_iff]

/-- **The first and last chambers of a gap are distinct**, so each gap has two unbounded
chambers rather than one. -/
@[cluster_algebras "lem_unbounded_one_end"]
theorem idx_ne_multiplicity_of_eq_zero (h : c.idx = 0) : c.idx ≠ D.multiplicity c.gap := by
  rw [h]
  exact fun hc => absurd (D.one_le_multiplicity c.gap) (by omega)

/-- A chamber's left position is a genuine position, or the `-∞` sentinel. -/
theorem left_le_length : c.left ≤ D.word.length := by
  obtain ⟨t, htle, hteq⟩ := D.exists_countUpTo_eq c.idx_le
  exact le_trans (c.left_le hteq) htle

/-- **The right position is the least position at which the gap's count exceeds the index**, the
counterpart of `Chamber.left_le` for the other end. -/
theorem right_le_of_countUpTo (h : c.idx ≠ D.multiplicity c.gap) {t : ℕ}
    (ht : D.countUpTo c.gap t = c.idx + 1) : c.right ≤ t := by
  rw [right, if_neg h]
  exact spanStart_le_of_count c.gap (c.idx + 1) t D.word ht

/-- **The right position is at most any position where the count has already exceeded the
index**, since the count climbs in steps of at most one and so hits `idx + 1` no later. -/
theorem right_le_of_le_countUpTo (h : c.idx ≠ D.multiplicity c.gap) {t : ℕ}
    (ht : t ≤ D.word.length) (hc : c.idx + 1 ≤ D.countUpTo c.gap t) : c.right ≤ t := by
  obtain ⟨s, hs, hse⟩ := D.exists_countUpTo_eq_le ht hc
  exact le_trans (c.right_le_of_countUpTo h hse) hs

/-- **The crossing at a chamber's left end lies in the chamber's own gap.** Were it at another
gap the preceding position would already lie in the span, contradicting minimality. This is what
pins a chamber's gap down from that one end. -/
theorem levelAt_of_left_eq_succ {t : ℕ} (h : c.left = t + 1) : D.levelAt t = c.gap := by
  by_contra hne
  have ht : t < D.word.length := by have := c.left_le_length; omega
  have hs : D.countUpTo c.gap (t + 1) = c.idx := by
    have := c.inSpan_left
    rwa [InSpan, h] at this
  rw [D.countUpTo_succ ht, if_neg hne] at hs
  have := c.left_le (t := t) (by rw [InSpan]; omega)
  omega

/-- **The crossing at a chamber's right end lies in the chamber's own gap**, the mirror of
`Chamber.levelAt_of_left_eq_succ`. -/
theorem levelAt_of_right_eq_succ {t : ℕ} (h : c.right = t + 1) (ht : t < D.word.length) :
    D.levelAt t = c.gap := by
  have hne : c.idx ≠ D.multiplicity c.gap := fun hc => by
    have := c.right_eq_top_iff.2 hc
    omega
  by_contra hcon
  have hs : D.countUpTo c.gap (t + 1) = c.idx + 1 := by
    rw [← h]
    exact c.countUpTo_right hne
  rw [D.countUpTo_succ ht, if_neg hcon] at hs
  have := c.right_le_of_countUpTo hne (t := t) (by omega)
  omega

/-- **A position of the span precedes the chamber's right end.** -/
theorem lt_right_of_inSpan {t : ℕ} (ht : t ≤ D.word.length) (h : c.InSpan t) : t < c.right := by
  by_cases hlast : c.idx = D.multiplicity c.gap
  · rw [right, if_pos hlast]
    omega
  · by_contra hcon
    have hmono := D.countUpTo_le_of_le (g := c.gap) (t := c.right) (t' := t) (by omega) ht
    have := c.countUpTo_right hlast
    rw [InSpan] at h
    omega

/-- **A position between the chamber's two ends lies in its span.** -/
theorem inSpan_of_le_of_lt {t : ℕ} (ht : t ≤ D.word.length) (h1 : c.left ≤ t)
    (h2 : t < c.right) : c.InSpan t := by
  have hmono := D.countUpTo_le_of_le (g := c.gap) (t := c.left) (t' := t) h1 ht
  have hleft := c.inSpan_left
  rw [InSpan] at hleft ⊢
  by_cases hlast : c.idx = D.multiplicity c.gap
  · have : D.countUpTo c.gap t ≤ D.multiplicity c.gap := by
      rw [← D.countUpTo_length]
      exact D.countUpTo_le_of_le ht le_rfl
    omega
  · by_contra hcon
    have := c.right_le_of_le_countUpTo hlast ht (by omega)
    omega

/-- **A chamber's span is the interval its two ends bound**: `L(c) ≤ t < R(c)`. -/
theorem inSpan_iff_le_lt {t : ℕ} (ht : t ≤ D.word.length) :
    c.InSpan t ↔ c.left ≤ t ∧ t < c.right :=
  ⟨fun h => ⟨c.left_le h, c.lt_right_of_inSpan ht h⟩,
    fun h => c.inSpan_of_le_of_lt ht h.1 h.2⟩

/-- **Two chambers of the same gap meet exactly when they are consecutive**: the right end of
`c` is the left end of `c'` if and only if `c.idx + 1 = c'.idx`. -/
theorem right_eq_left_iff {c c' : D.Chamber} (hg : c.gap = c'.gap) :
    c.right = c'.left ↔ c.idx + 1 = c'.idx := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hlast : c.idx ≠ D.multiplicity c.gap := fun hc => by
      have h1 := c.right_eq_top_iff.2 hc
      have h2 := c'.left_le_length
      omega
    have h1 := c.countUpTo_right hlast
    have h2 := c'.inSpan_left
    rw [InSpan, ← hg, ← h] at h2
    omega
  · have hlast : c.idx ≠ D.multiplicity c.gap := by
      have := c'.idx_le
      rw [← hg] at this
      omega
    rw [right, if_neg hlast, left, ← hg, ← h]

/-- **A chamber starting at a crossing also holds the position after the next one**, provided that
next crossing is at another gap: passing it leaves the chamber's own count alone. -/
theorem inSpan_add_two_of_left {q : ℕ} (hq : q + 1 < D.word.length)
    (hne : D.levelAt (q + 1) ≠ D.levelAt q) (hl : c.left = q + 1) : c.InSpan (q + 2) := by
  have hgap : D.levelAt q = c.gap := c.levelAt_of_left_eq_succ hl
  have h1 : c.InSpan (q + 1) := hl ▸ c.inSpan_left
  rw [InSpan] at h1 ⊢
  rw [D.countUpTo_succ (t := q + 1) hq, if_neg (hgap ▸ hne)]
  omega

/-- The **next chamber** of the same gap, when the gap is crossed again. -/
def succ (h : c.idx ≠ D.multiplicity c.gap) : D.Chamber :=
  ⟨c.gap, c.idx + 1, c.le_multiplicity_succ h⟩

/-- The next chamber lies in the same gap. -/
@[simp]
theorem gap_succ (h : c.idx ≠ D.multiplicity c.gap) : (c.succ h).gap = c.gap := rfl

/-- The next chamber has the next index. -/
@[simp]
theorem idx_succ (h : c.idx ≠ D.multiplicity c.gap) : (c.succ h).idx = c.idx + 1 := rfl

/-- **A chamber ends where the next chamber of its gap begins.** -/
theorem right_eq_left_succ (h : c.idx ≠ D.multiplicity c.gap) : c.right = (c.succ h).left := by
  rw [right, if_neg h, left, gap_succ, idx_succ]

/-! ### The chamber set -/

/-- Inside a chamber's span no crossing has the chamber's own gap: the count of such crossings
is what the span holds fixed. -/
theorem levelAt_ne_gap {t : ℕ} (ht : t < D.word.length) (h1 : c.InSpan t)
    (h2 : c.InSpan (t + 1)) : D.levelAt t ≠ c.gap := by
  rw [InSpan, D.countUpTo_succ ht] at h2
  rw [InSpan] at h1
  intro hc
  rw [if_pos hc, h1] at h2
  omega

/-- **The wires below a chamber's gap are the same at every position of its span.** -/
theorem belowSet_eq_of_inSpan {t t' : ℕ} (htt' : t ≤ t') (ht' : t' ≤ D.word.length)
    (h1 : c.InSpan t) (h2 : c.InSpan t') :
    D.belowSet t c.gap = D.belowSet t' c.gap := by
  induction t' with
  | zero =>
    rw [Nat.le_zero.1 htt']
  | succ r ih =>
    rcases Nat.eq_or_lt_of_le htt' with h | h
    · rw [h]
    · -- `r` is in the span too, being sandwiched between two positions of it
      have hrle : r ≤ D.word.length := by omega
      have hr : c.InSpan r := by
        rw [InSpan]
        have hmono1 : D.countUpTo c.gap t ≤ D.countUpTo c.gap r :=
          D.countUpTo_le_of_le (by omega) hrle
        have hmono2 : D.countUpTo c.gap r ≤ D.countUpTo c.gap (r + 1) :=
          D.countUpTo_le_of_le (by omega) ht'
        rw [InSpan] at h1 h2
        omega
      rw [ih (by omega) hrle hr,
        D.belowSet_succ_of_ne (by omega) (c.levelAt_ne_gap (by omega) hr h2)]

attribute [cluster_algebras "def_chamber_set"] chamberSet

/-- **The chamber set is well defined**: reading it at any position of the chamber's span gives
the same set. -/
@[cluster_algebras "lem_chamber_set_well_defined"]
theorem chamberSet_eq_belowSet {t : ℕ} (ht : t ≤ D.word.length) (h : c.InSpan t) :
    c.chamberSet = D.belowSet t c.gap := by
  rw [chamberSet]
  rcases le_total c.left t with hle | hle
  · exact c.belowSet_eq_of_inSpan hle ht c.inSpan_left h
  · exact (c.belowSet_eq_of_inSpan hle c.left_le_length h c.inSpan_left).symm

/-- **A chamber set has one wire per level at or below the gap.** The wires sit at distinct levels,
so counting the chamber set is counting those levels, of which there are `gp(c) + 1`. -/
theorem card_chamberSet : c.chamberSet.card = (c.gap : ℕ) + 1 := by
  have hset : c.chamberSet
      = Finset.map (D.wire c.left).toEmbedding (Finset.Iic c.gap.castSucc) := by
    ext v
    rw [chamberSet, mem_belowSet, Finset.mem_map]
    constructor
    · exact fun h => ⟨D.levelOf c.left v, Finset.mem_Iic.2 h, by simp [levelOf]⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [levelOf] using Finset.mem_Iic.1 hx
  rw [hset, Finset.card_map, Fin.card_Iic, Fin.val_castSucc]

/-- **A chamber's gap is determined by its chamber set**, being one less than its size. So a
bijection of chambers matching chamber sets — between two diagrams on the same strands, as much as
within one — must send each chamber to one at the same gap. -/
theorem gap_eq_of_chamberSet_eq {D E : WiringDiagram n} {c : D.Chamber} {c' : E.Chamber}
    (h : c.chamberSet = c'.chamberSet) : c.gap = c'.gap := by
  have h1 := c.card_chamberSet
  have h2 := c'.card_chamberSet
  rw [h, h2] at h1
  exact Fin.ext (by omega)

end Chamber

/-! ### The chamber at a position

Every chamber is the chamber of its gap containing any position of its span, so naming a gap and
a position names a chamber. -/

/-- The chamber of gap `g` whose span contains the position `t`. -/
def chamberAt (g : Fin (n + 1)) (t : ℕ) (ht : t ≤ D.word.length) : D.Chamber where
  gap := g
  idx := D.countUpTo g t
  idx_le := by
    rw [← D.countUpTo_length]
    exact D.countUpTo_le_of_le ht le_rfl

/-- The chamber at a position lies in the gap it was named with. -/
@[simp]
theorem gap_chamberAt (g : Fin (n + 1)) {t : ℕ} (ht : t ≤ D.word.length) :
    (D.chamberAt g t ht).gap = g := rfl

/-- The index of the chamber at a position counts its gap's crossings before that position. -/
@[simp]
theorem idx_chamberAt (g : Fin (n + 1)) {t : ℕ} (ht : t ≤ D.word.length) :
    (D.chamberAt g t ht).idx = D.countUpTo g t := rfl

/-- The position used to name the chamber lies in its span, as the name suggests. -/
@[simp]
theorem inSpan_chamberAt (g : Fin (n + 1)) {t : ℕ} (ht : t ≤ D.word.length) :
    (D.chamberAt g t ht).InSpan t := rfl

/-- The chamber at a position begins no later than that position. -/
theorem left_chamberAt_le (g : Fin (n + 1)) {t : ℕ} (ht : t ≤ D.word.length) :
    (D.chamberAt g t ht).left ≤ t :=
  Chamber.left_le _ (D.inSpan_chamberAt g ht)

/-- **A chamber of gap `g` begins at a crossing of gap `g`**: the chamber holding the position
just after such a crossing begins exactly there, since the count of `g`'s crossings rises as the
crossing is passed and so was smaller at every earlier position. -/
theorem left_chamberAt_succ {g : Fin (n + 1)} {t : ℕ} (ht : t + 1 ≤ D.word.length)
    (hg : D.levelAt t = g) : (D.chamberAt g (t + 1) ht).left = t + 1 := by
  have hsucc : D.countUpTo g (t + 1) = D.countUpTo g t + 1 := by
    rw [D.countUpTo_succ (by omega), if_pos hg]
  rw [Chamber.left, idx_chamberAt, gap_chamberAt]
  refine spanStart_eq_of_count _ (D.countUpTo_def _ _).symm ?_
  intro s hs hc
  have hmono := count_take_mono g (l := D.word) (s := s) (t := t) (by omega)
  rw [D.countUpTo_def, D.countUpTo_def] at hsucc
  rw [D.countUpTo_def] at hc
  omega

/-- **A chamber of gap `g` ends at the next crossing of gap `g`**: the chamber holding the
position of such a crossing ends just after it. -/
theorem right_chamberAt {g : Fin (n + 1)} {t : ℕ} (ht : t < D.word.length)
    (hg : D.levelAt t = g) (htl : t ≤ D.word.length) :
    (D.chamberAt g t htl).right = t + 1 := by
  have hsucc : D.countUpTo g (t + 1) = D.countUpTo g t + 1 := by
    rw [D.countUpTo_succ ht, if_pos hg]
  have hne : (D.chamberAt g t htl).idx ≠ D.multiplicity (D.chamberAt g t htl).gap := by
    rw [idx_chamberAt, gap_chamberAt]
    have hm : D.countUpTo g (t + 1) ≤ D.multiplicity g := by
      rw [← D.countUpTo_length]
      exact D.countUpTo_le_of_le (by omega) le_rfl
    omega
  rw [Chamber.right, if_neg hne, idx_chamberAt, gap_chamberAt, ← hsucc]
  exact D.left_chamberAt_succ (by omega) hg

/-- A crossing **lies directly above** the chamber `c` when its level is the gap just above
`c`'s and it happens strictly inside `c`'s span. -/
@[cluster_algebras "def_directly_above"]
def DirectlyAbove (c : D.Chamber) (k : ℕ) : Prop :=
  (D.levelAt k : ℕ) = (c.gap : ℕ) + 1 ∧ c.left < k ∧ k < c.right

/-- A crossing **lies directly below** the chamber `c` when its level is the gap just below
`c`'s and it happens strictly inside `c`'s span. -/
@[cluster_algebras "def_directly_above"]
def DirectlyBelow (c : D.Chamber) (k : ℕ) : Prop :=
  (D.levelAt k : ℕ) + 1 = (c.gap : ℕ) ∧ c.left < k ∧ k < c.right

/-! ### The quiver of a wiring diagram -/

namespace Chamber

variable {D} (c : D.Chamber)

/-- Chambers are determined by their gap and their index; the bound on the index is a
proposition and so carries no information. -/
theorem ext' {c c' : D.Chamber} (h1 : c.gap = c'.gap) (h2 : c.idx = c'.idx) : c = c' := by
  cases c
  cases c'
  simp_all

/-- **A chamber is determined by its gap and its left position**, since the index counts the
crossings of the gap preceding that position. -/
theorem eq_of_gap_left {c c' : D.Chamber} (hg : c.gap = c'.gap) (hl : c.left = c'.left) :
    c = c' := by
  refine ext' hg ?_
  have h1 := c.inSpan_left
  have h2 := c'.inSpan_left
  rw [InSpan] at h1 h2
  rw [← h1, ← h2, hg, hl]

/-- **A chamber is determined by its gap and its right position.** -/
theorem eq_of_gap_right {c c' : D.Chamber} (hg : c.gap = c'.gap) (hr : c.right = c'.right) :
    c = c' := by
  refine ext' hg ?_
  by_cases h : c.idx = D.multiplicity c.gap
  · have h' : c'.idx = D.multiplicity c'.gap :=
      c'.right_eq_top_iff.1 (hr ▸ c.right_eq_top_iff.2 h)
    rw [h, h', hg]
  · have h' : c'.idx ≠ D.multiplicity c'.gap := fun hc =>
      h (c.right_eq_top_iff.1 (hr.trans (c'.right_eq_top_iff.2 hc)))
    have e1 := c.countUpTo_right h
    have e2 := c'.countUpTo_right h'
    rw [← hg, ← hr] at e2
    omega

/-- A chamber's span is nonempty, so its left position is strictly before its right one. -/
theorem left_lt_right : c.left < c.right := by
  by_cases h : c.idx = D.multiplicity c.gap
  · rw [right, if_pos h]
    have := c.left_le_length
    omega
  · -- otherwise the count is one larger at the right position than at the left
    by_contra hcon
    have hr : D.countUpTo c.gap c.right = c.idx + 1 := c.countUpTo_right h
    have hmono : D.countUpTo c.gap c.right ≤ D.countUpTo c.gap c.left :=
      D.countUpTo_le_of_le (by omega) c.left_le_length
    have hl : D.countUpTo c.gap c.left = c.idx := c.inSpan_left
    omega

/-- **Distinct chambers of one gap carry distinct chamber sets.** At the crossing that separates
them the wire arriving from below leaves the set and the wire arriving from above enters it. Those
two wires never cross again, so from then on the one that entered stays below the one that left. So
the later chamber's set either omits the wire that left — which the earlier one contains — or
contains it, and then contains the wire that entered as well, which the earlier one does not.

This is where the word being reduced is used: it is what makes the two wires cross only once. -/
private theorem chamberSet_ne_of_idx_lt {c c' : D.Chamber} (hg : c.gap = c'.gap)
    (hlt : c.idx < c'.idx) : c.chamberSet ≠ c'.chamberSet := by
  intro hset
  -- `c` ends at a crossing of its own gap, at position `r + 1`
  have hmult : c.idx ≠ D.multiplicity c.gap := by
    have := c'.idx_le
    rw [← hg] at this
    omega
  have hrle : c.right ≤ D.word.length := c.right_le_length hmult
  have hlr := c.left_lt_right
  obtain ⟨r, hr⟩ : ∃ r, c.right = r + 1 := ⟨c.right - 1, by omega⟩
  have hrlt : r < D.word.length := by omega
  have hlev : D.levelAt r = c.gap := c.levelAt_of_right_eq_succ hr hrlt
  set u := D.wire r c.gap.castSucc with hu
  set v := D.wire r c.gap.succ with hv
  have hpair : D.crossedPair r = s(u, v) := by rw [crossedPair, hlev, hu, hv]
  have hlu : D.levelOf r u = c.gap.castSucc := by rw [hu, levelOf, Equiv.symm_apply_apply]
  have hlv : D.levelOf r v = c.gap.succ := by rw [hv, levelOf, Equiv.symm_apply_apply]
  -- read `c`'s chamber set just before that crossing: it holds `u` and not `v`
  have hspan : c.InSpan r := (c.inSpan_iff_le_lt (by omega)).2 ⟨by omega, by omega⟩
  have hJc : c.chamberSet = D.belowSet r c.gap := c.chamberSet_eq_belowSet (by omega) hspan
  have huc : u ∈ c.chamberSet := by rw [hJc, mem_belowSet, hlu]
  have hvc : v ∉ c.chamberSet := by
    rw [hJc, mem_belowSet, hlv]
    simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
    omega
  -- `c'` begins at or after that crossing, and by then `v` lies below `u` for good
  have hcl : c.right ≤ c'.left :=
    c.right_le_of_le_countUpTo hmult c'.left_le_length (by
      have h1 := c'.inSpan_left
      rw [InSpan, ← hg] at h1
      omega)
  have hcll : c'.left ≤ D.word.length := c'.left_le_length
  have hpair' : D.crossedPair r = s(v, u) := hpair.trans Sym2.eq_swap
  have hno : ∀ s, r + 1 ≤ s → s < c'.left → D.crossedPair s ≠ s(v, u) := by
    intro s hs1 hs2 hc
    have := D.crossedPair_injOn (by omega) hrlt (hc.trans hpair'.symm)
    omega
  have hord0 : D.levelOf (r + 1) v < D.levelOf (r + 1) u := by
    rw [D.levelOf_succ hrlt, D.levelOf_succ hrlt, hlu, hlv, hlev, gapSwap_succ, gapSwap_castSucc]
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
    omega
  have hordt : D.levelOf c'.left v < D.levelOf c'.left u :=
    (D.levelOf_lt_iff_of_le (v := v) (w := u) (r := r + 1) c'.left (by omega) hcll hno).2 hord0
  -- so `c'` cannot hold `u` without holding `v`, and it cannot fail to hold `u` either
  by_cases hu' : u ∈ c'.chamberSet
  · refine hvc ?_
    rw [chamberSet, mem_belowSet] at hu'
    rw [hset, chamberSet, mem_belowSet]
    exact le_trans (le_of_lt hordt) hu'
  · exact hu' (hset ▸ huc)

/-- **Two chambers at different gaps do not begin at the same crossing**, an end being a crossing
of the chamber's own gap. So a shared left end can only be the `-∞` sentinel. -/
theorem left_eq_zero_of_left_eq {c c' : D.Chamber} (hg : c.gap ≠ c'.gap)
    (h : c.left = c'.left) : c.left = 0 := by
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t, c.left = t + 1 := ⟨c.left - 1, by omega⟩
  exact hg ((c.levelAt_of_left_eq_succ ht).symm.trans
    (c'.levelAt_of_left_eq_succ (h.symm.trans ht)))

/-- **Two chambers at different gaps do not end at the same crossing**, so a shared right end can
only be the `+∞` sentinel. -/
theorem right_eq_top_of_right_eq {c c' : D.Chamber} (hg : c.gap ≠ c'.gap)
    (h : c.right = c'.right) : c.right = D.word.length + 1 := by
  by_contra hne
  have h1 : c.idx ≠ D.multiplicity c.gap := fun hc => hne (c.right_eq_top_iff.2 hc)
  have hrl := c.right_le_length h1
  have hlr := c.left_lt_right
  obtain ⟨t, ht⟩ : ∃ t, c.right = t + 1 := ⟨c.right - 1, by omega⟩
  exact hg ((c.levelAt_of_right_eq_succ ht (by omega)).symm.trans
    (c'.levelAt_of_right_eq_succ (h.symm.trans ht) (by omega)))

/-- **One chamber's left end is never another's right end, at different gaps.** -/
theorem left_ne_right {c c' : D.Chamber} (hg : c.gap ≠ c'.gap) : c.left ≠ c'.right := by
  intro h
  have hlr := c'.left_lt_right
  have hle := c.left_le_length
  obtain ⟨t, ht⟩ : ∃ t, c.left = t + 1 := ⟨c.left - 1, by omega⟩
  exact hg ((c.levelAt_of_left_eq_succ ht).symm.trans
    (c'.levelAt_of_right_eq_succ (h.symm.trans ht) (by omega)))

/-- **One chamber's right end is never another's left end, at different gaps.** -/
theorem right_ne_left {c c' : D.Chamber} (hg : c.gap ≠ c'.gap) : c.right ≠ c'.left :=
  fun h => left_ne_right (Ne.symm hg) h.symm

/-- **Two chambers of one gap either coincide or have disjoint spans.** This is what makes the
arrow comparison finite: within a gap there is nothing between being equal and being separated. -/
theorem spans_of_gap_eq {c c' : D.Chamber} (hg : c.gap = c'.gap) :
    (c.left = c'.left ∧ c.right = c'.right) ∨ c.right ≤ c'.left ∨ c'.right ≤ c.left := by
  rcases lt_trichotomy c.idx c'.idx with h | h | h
  · refine Or.inr (Or.inl (c.right_le_of_le_countUpTo ?_ c'.left_le_length ?_))
    · have := c'.idx_le
      rw [← hg] at this
      omega
    · have h1 := c'.inSpan_left
      rw [InSpan, ← hg] at h1
      omega
  · rw [ext' hg h]
    exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr (Or.inr (c'.right_le_of_le_countUpTo ?_ c.left_le_length ?_))
    · have := c.idx_le
      rw [hg] at this
      omega
    · have h1 := c.inSpan_left
      rw [InSpan, hg] at h1
      omega

/-- **A chamber is determined by its gap and its chamber set.** -/
theorem eq_of_gap_of_chamberSet {c c' : D.Chamber} (hg : c.gap = c'.gap)
    (h : c.chamberSet = c'.chamberSet) : c = c' := by
  rcases lt_trichotomy c.idx c'.idx with hlt | heq | hlt
  · exact absurd h (chamberSet_ne_of_idx_lt hg hlt)
  · exact ext' hg heq
  · exact absurd h.symm (chamberSet_ne_of_idx_lt hg.symm hlt)

end Chamber

attribute [cluster_algebras "def_wiring_quiver"] Arrow

attribute [cluster_algebras "def_wiring_quiver"] wiringArrows

/-- **The arrow condition between two chambers of one gap**: they meet, which by
`Chamber.right_eq_left_iff` says they are consecutive. -/
theorem arrow_iff_of_gap_eq {c c' : D.Chamber} (h : c.gap = c'.gap) :
    D.Arrow c c' ↔ (c.Bounded ∨ c'.Bounded) ∧ c.idx + 1 = c'.idx := by
  rw [Arrow]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (⟨-, hr⟩ | ⟨hg, -, -, -⟩)
    · exact (Chamber.right_eq_left_iff h).1 hr
    · rw [h] at hg
      omega
  · exact fun hidx => Or.inl ⟨h, (Chamber.right_eq_left_iff h).2 hidx⟩

/-- **The arrow condition between chambers of different gaps**: at least one is bounded, the gaps
are adjacent, and the spans interleave strictly. -/
theorem arrow_iff_of_gap_ne {c c' : D.Chamber} (h : c.gap ≠ c'.gap) :
    D.Arrow c c' ↔ (c.Bounded ∨ c'.Bounded) ∧
      (((c'.gap : ℕ) + 1 = (c.gap : ℕ) ∨ (c.gap : ℕ) + 1 = (c'.gap : ℕ)) ∧
        c'.left < c.left ∧ c.left < c'.right ∧ c'.right < c.right) := by
  rw [Arrow]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (⟨hg, -⟩ | hcond)
    · exact absurd hg h
    · exact hcond
  · exact Or.inr

/-- **The arrow condition `Arrow`, as arithmetic in two chambers' gaps and ends**: at least one
of them is bounded, and either the gaps are equal and the first chamber ends where the second
begins, or the gaps are adjacent and the spans interleave strictly. -/
def ArrowArith (len Lu Ru gu Lv Rv gv : ℕ) : Prop :=
  ((Lu ≠ 0 ∧ Ru ≠ len + 1) ∨ (Lv ≠ 0 ∧ Rv ≠ len + 1)) ∧
    ((gu = gv ∧ Ru = Lv) ∨ ((gv + 1 = gu ∨ gu + 1 = gv) ∧ Lv < Lu ∧ Lu < Rv ∧ Rv < Ru))

/-- The arithmetic arrow condition is decidable, being built from comparisons of naturals. -/
instance instDecidableArrowArith (len Lu Ru gu Lv Rv gv : ℕ) :
    Decidable (ArrowArith len Lu Ru gu Lv Rv gv) := by
  unfold ArrowArith
  infer_instance

/-- **The arrow condition is the arithmetic one**: the gaps by their values, boundedness by the two
ends. This is the form the comparison of two diagrams' quivers is carried out in. -/
theorem arrow_iff_arith (c c' : D.Chamber) : D.Arrow c c' ↔
    ArrowArith D.word.length c.left c.right c.gap c'.left c'.right c'.gap := by
  rw [Arrow, ArrowArith, Chamber.Bounded, Chamber.Bounded, Chamber.HasLeftEnd,
    Chamber.HasLeftEnd, Chamber.HasRightEnd, Chamber.HasRightEnd, ← Fin.val_inj]

/-- **`Q(D)` has no loops.** -/
@[cluster_algebras "lem_wiring_quiver_is_quiver"]
theorem isArrowSystem_wiringArrows (c : D.Chamber) : D.wiringArrows c c = 0 := by
  rw [wiringArrows, if_neg]
  rintro ⟨-, (⟨-, hr⟩ | ⟨-, hl, -, -⟩)⟩
  · exact absurd hr (by have := c.left_lt_right; omega)
  · omega

/-- **`Q(D)` carries no arrow between two unbounded chambers.** -/
@[cluster_algebras "lem_wiring_quiver_is_quiver"]
theorem wiringArrows_eq_zero_of_not_bounded {c c' : D.Chamber} (hc : ¬c.Bounded)
    (hc' : ¬c'.Bounded) : D.wiringArrows c c' = 0 := by
  rw [wiringArrows, if_neg]
  rintro ⟨(h | h), -⟩
  · exact hc h
  · exact hc' h

/-- **`Q(D)` is two-cycle-free.** -/
@[cluster_algebras "lem_wiring_quiver_is_quiver"]
theorem twoCycleFree_wiringArrows : TwoCycleFree (D.wiringArrows) := by
  intro c c'
  by_cases h : D.Arrow c c'
  · right
    rw [wiringArrows, if_neg]
    rintro ⟨-, hc'⟩
    obtain ⟨-, hc⟩ := h
    have hlr : c.left < c.right := c.left_lt_right
    have hlr' : c'.left < c'.right := c'.left_lt_right
    rcases hc with ⟨hg, hrl⟩ | ⟨hg, h1, h2, h3⟩
    · rcases hc' with ⟨-, hrl'⟩ | ⟨hg', -, -, -⟩
      · omega
      · rw [hg] at hg'
        omega
    · rcases hc' with ⟨hg', -⟩ | ⟨-, h1', -, -⟩
      · rw [hg'] at hg
        omega
      · omega
  · left
    rw [wiringArrows, if_neg h]

/-- The **quiver of the wiring diagram `D`**: its vertices are the chambers, its frozen
vertices the unbounded ones, and its arrows those of `Arrow`. -/
@[cluster_algebras "def_wiring_quiver"]
def wiringQuiver : Quiver D.Chamber where
  frozen := {c ∈ Finset.univ | ¬c.Bounded}
  arrows := D.wiringArrows
  isArrowSystem := D.isArrowSystem_wiringArrows
  twoCycleFree := D.twoCycleFree_wiringArrows
  frozen_eq_zero c hc c' hc' :=
    D.wiringArrows_eq_zero_of_not_bounded (by simpa using hc) (by simpa using hc')

/-- The arrows of `Q(D)` are the arrow counts, by definition. -/
@[simp]
theorem arrows_wiringQuiver : D.wiringQuiver.arrows = D.wiringArrows := rfl

/-- The frozen vertices of `Q(D)` are the unbounded chambers, by definition. -/
@[simp]
theorem mem_frozen_wiringQuiver (c : D.Chamber) : c ∈ D.wiringQuiver.frozen ↔ ¬c.Bounded := by
  simp [wiringQuiver]

/-- Boundedness in terms of the two ends. -/
theorem bounded_iff_arith (c : D.Chamber) :
    c.Bounded ↔ (c.left ≠ 0 ∧ c.right ≠ D.word.length + 1) := by
  rw [Chamber.Bounded, Chamber.HasLeftEnd, Chamber.HasRightEnd]

/-- **The arrow count, entirely in arithmetic.** With this the quivers of two diagrams can be
compared without any reference to `Arrow`, whose decidability procedure is expensive to unfold. -/
theorem wiringArrows_eq_ite (u v : D.Chamber) : D.wiringArrows u v =
    if ArrowArith D.word.length u.left u.right u.gap v.left v.right v.gap then 1 else 0 := by
  rw [wiringArrows, if_congr (D.arrow_iff_arith u v) rfl rfl]

/-- **No ordered pair of chambers carries more than one arrow.** -/
@[cluster_algebras "lem_wiring_quiver_is_quiver"]
theorem wiringArrows_le_one (c c' : D.Chamber) : D.wiringArrows c c' ≤ 1 := by
  rw [wiringArrows]
  split_ifs <;> omega

end WiringDiagram

end ClusterAlgebras
