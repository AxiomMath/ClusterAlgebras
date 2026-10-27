/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.QuiverOps
public import ClusterAlgebras.WiringDiagram.Chamber

/-!
# The commutation move does not change the quiver

Sliding two crossings at non-adjacent gaps past one another changes the word but not the picture,
and the quiver `Q(D)` does not change either: matching chambers by their gap and their chamber set
is an isomorphism `Q(D) ≃ Q(D')`.

The gaps being non-adjacent enters three times, and the third is the one that does the work:

* the two transpositions commute, so `D'` is a wiring diagram at all (that is `commutationMove`);
* a chamber's gap is crossed at one of the two positions at most, so each of its ends either stays
  put or moves between `p + 1` and `p + 2`;
* and no two chambers at *adjacent* gaps can both have an end that moves. So in the arrow
  conditions between chambers of adjacent gaps, which compare the two chambers' ends, one
  chamber's ends are fixed and avoid both `p + 1` and `p + 2` — and a comparison against a position
  that is neither cannot tell the two apart. The arrow condition between chambers of the same gap
  needs no such argument: it is a condition on indices alone (`Chamber.right_eq_left_iff`), and
  the move changes no index.

## Main definitions

* `WiringDiagram.commEquiv`: The bijection between the chambers of `D` and of `D'` keeping the gap
  and the index.
* `WiringDiagram.commutationIso`: The isomorphism `Q(D) ≃ Q(D')` given by `commEquiv`.

## Main results

* `WiringDiagram.chamberSet_commEquiv`: `commEquiv` keeps the chamber set.
* `WiringDiagram.eq_commEquiv_of_chamberSet`: `commEquiv` is the only map keeping chamber sets.
* `WiringDiagram.arrow_commEquiv_iff`: The two quivers have the same arrows.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

namespace WiringDiagram

variable (D : WiringDiagram n) {p : ℕ}

/-! ### The word after the move -/

/-- The commutation move does not change the length of the word. -/
theorem length_word_commutationMove (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    (D.commutationMove p hp hne).word.length = D.word.length := by
  rw [commutationMove, word_splice, length_spliceWord (by simpa using hp)]

/-- The two swapped crossings lie at different gaps. -/
theorem levelAt_succ_ne_levelAt
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    D.levelAt (p + 1) ≠ D.levelAt p := fun hc => by rw [hc] at hne; omega

/-- Before the two swapped positions the word is unchanged. -/
theorem levelAt_commutationMove_of_lt (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) {k : ℕ} (hk : k < p) :
    (D.commutationMove p hp hne).levelAt k = D.levelAt k := by
  rw [levelAt_eq_getElem?, levelAt_eq_getElem?, commutationMove, word_splice,
    getElem?_spliceWord_left (by omega) hk]

/-- After the two swapped positions the word is unchanged. -/
theorem levelAt_commutationMove_of_ge (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) {k : ℕ} (hk : p + 2 ≤ k) :
    (D.commutationMove p hp hne).levelAt k = D.levelAt k := by
  rw [levelAt_eq_getElem?, levelAt_eq_getElem?, commutationMove, word_splice,
    getElem?_spliceWord_right (by omega) (by simpa using hk)]

/-- **The two swapped crossings, read off the moved diagram.** -/
theorem levelAt_commutationMove (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    (D.commutationMove p hp hne).levelAt p = D.levelAt (p + 1) ∧
      (D.commutationMove p hp hne).levelAt (p + 1) = D.levelAt p := by
  have hmid : ∀ i : ℕ, i < 2 → (D.commutationMove p hp hne).word[p + i]? =
      ([D.levelAt (p + 1), D.levelAt p] : List (Fin (n + 1)))[i]? := by
    intro i hi
    rw [commutationMove, word_splice]
    exact getElem?_spliceWord_mid (by omega) (by simpa using hi)
  have h0 : (D.commutationMove p hp hne).word[p]? = some (D.levelAt (p + 1)) := by
    simpa using hmid 0 (by omega)
  have h1 : (D.commutationMove p hp hne).word[p + 1]? = some (D.levelAt p) := by
    simpa using hmid 1 (by omega)
  exact ⟨by rw [levelAt_eq_getElem?, h0]; rfl, by rw [levelAt_eq_getElem?, h1]; rfl⟩

/-! ### The counts and the wires after the move

Both the crossing counts and the partial products are read off the same two facts: the word is
unchanged outside the two positions, and the two crossings there have merely been exchanged. So
both agree with `D`'s before `p` and again from `p + 2` on, and only the single position `p + 1`
between the two crossings sees a difference. -/

/-- Before the two swapped positions the counts are unchanged. -/
theorem countUpTo_commutationMove_of_le (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (g : Fin (n + 1)) :
    ∀ t ≤ p, (D.commutationMove p hp hne).countUpTo g t = D.countUpTo g t := by
  have hlen := D.length_word_commutationMove hp hne
  intro t
  induction t with
  | zero => intro _; rw [countUpTo_zero, countUpTo_zero]
  | succ r ih =>
    intro hr
    rw [(D.commutationMove p hp hne).countUpTo_succ (g := g) (t := r) (by rw [hlen]; omega),
      D.countUpTo_succ (g := g) (t := r) (by omega), ih (by omega),
      D.levelAt_commutationMove_of_lt hp hne (by omega)]

/-- After the two swapped positions the counts are unchanged: the same two crossings have been
passed, in the other order. -/
theorem countUpTo_commutationMove_of_ge (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (g : Fin (n + 1)) :
    ∀ t, p + 2 ≤ t → t ≤ D.word.length →
      (D.commutationMove p hp hne).countUpTo g t = D.countUpTo g t := by
  have hlen := D.length_word_commutationMove hp hne
  obtain ⟨e0, e1⟩ := D.levelAt_commutationMove hp hne
  intro t h2
  induction t, h2 using Nat.le_induction with
  | base =>
    intro _
    rw [(D.commutationMove p hp hne).countUpTo_succ (g := g) (t := p + 1) (by rw [hlen]; omega),
      (D.commutationMove p hp hne).countUpTo_succ (g := g) (t := p) (by rw [hlen]; omega),
      D.countUpTo_succ (g := g) (t := p + 1) (by omega),
      D.countUpTo_succ (g := g) (t := p) (by omega),
      D.countUpTo_commutationMove_of_le hp hne g p le_rfl, e0, e1]
    split_ifs <;> omega
  | succ r hr ih =>
    intro ht
    rw [(D.commutationMove p hp hne).countUpTo_succ (g := g) (t := r) (by rw [hlen]; omega),
      D.countUpTo_succ (g := g) (t := r) (by omega), ih (by omega),
      D.levelAt_commutationMove_of_ge hp hne (by omega)]

/-- **Away from the position between the two swapped crossings, the counts are unchanged.** -/
theorem countUpTo_commutationMove (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (g : Fin (n + 1)) {t : ℕ}
    (ht : t ≤ D.word.length) (htne : t ≠ p + 1) :
    (D.commutationMove p hp hne).countUpTo g t = D.countUpTo g t := by
  by_cases h : t ≤ p
  · exact D.countUpTo_commutationMove_of_le hp hne g t h
  · exact D.countUpTo_commutationMove_of_ge hp hne g t (by omega) ht

/-- **The commutation move changes no gap multiplicity**, so the two diagrams have the same
chambers. -/
theorem multiplicity_commutationMove (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (g : Fin (n + 1)) :
    (D.commutationMove p hp hne).multiplicity g = D.multiplicity g := by
  rw [← (D.commutationMove p hp hne).countUpTo_length, ← D.countUpTo_length,
    D.length_word_commutationMove hp hne]
  exact D.countUpTo_commutationMove_of_ge hp hne g _ (by omega) le_rfl

/-- Before the two swapped positions the wires are where they were. -/
theorem wire_commutationMove_of_le (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    ∀ t ≤ p, (D.commutationMove p hp hne).wire t = D.wire t := by
  have hlen := D.length_word_commutationMove hp hne
  intro t
  induction t with
  | zero => intro _; rw [wire_zero, wire_zero]
  | succ r ih =>
    intro hr
    rw [(D.commutationMove p hp hne).wire_succ (t := r) (by rw [hlen]; omega),
      D.wire_succ (t := r) (by omega), ih (by omega),
      D.levelAt_commutationMove_of_lt hp hne (by omega)]

/-- After the two swapped positions the wires are where they were: the two transpositions commute,
so the partial product past both of them is the same. -/
theorem wire_commutationMove_of_ge (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    ∀ t, p + 2 ≤ t → t ≤ D.word.length →
      (D.commutationMove p hp hne).wire t = D.wire t := by
  have hlen := D.length_word_commutationMove hp hne
  obtain ⟨e0, e1⟩ := D.levelAt_commutationMove hp hne
  intro t h2
  induction t, h2 using Nat.le_induction with
  | base =>
    intro _
    rw [(D.commutationMove p hp hne).wire_succ (t := p + 1) (by rw [hlen]; omega),
      (D.commutationMove p hp hne).wire_succ (t := p) (by rw [hlen]; omega),
      D.wire_succ (t := p + 1) (by omega), D.wire_succ (t := p) (by omega),
      D.wire_commutationMove_of_le hp hne p le_rfl, e0, e1, mul_assoc, mul_assoc,
      gapSwap_comm hne]
  | succ r hr ih =>
    intro ht
    rw [(D.commutationMove p hp hne).wire_succ (t := r) (by rw [hlen]; omega),
      D.wire_succ (t := r) (by omega), ih (by omega),
      D.levelAt_commutationMove_of_ge hp hne (by omega)]

/-- **Away from the position between the two swapped crossings, the wires are unchanged.** -/
theorem wire_commutationMove (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) {t : ℕ} (ht : t ≤ D.word.length)
    (htne : t ≠ p + 1) : (D.commutationMove p hp hne).wire t = D.wire t := by
  by_cases h : t ≤ p
  · exact D.wire_commutationMove_of_le hp hne t h
  · exact D.wire_commutationMove_of_ge hp hne t (by omega) ht

/-- **Away from that one position, the same wires lie below each gap.** -/
theorem belowSet_commutationMove (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) {t : ℕ} (ht : t ≤ D.word.length)
    (htne : t ≠ p + 1) (g : Fin (n + 1)) :
    (D.commutationMove p hp hne).belowSet t g = D.belowSet t g := by
  ext v
  rw [mem_belowSet, mem_belowSet, levelOf, levelOf, D.wire_commutationMove hp hne ht htne]

/-! ### The chambers correspond

The move changes no multiplicity, so a gap and an index name a chamber of `D'` exactly when they
name one of `D`. That is the correspondence; it keeps the gap, and it keeps the chamber set. -/

/-- **The chambers of the two diagrams correspond**, by keeping the gap and the index. -/
@[cluster_algebras "lem_commutation_invariance"]
def commEquiv (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    D.Chamber ≃ (D.commutationMove p hp hne).Chamber where
  toFun c := ⟨c.gap, c.idx, by rw [D.multiplicity_commutationMove hp hne]; exact c.idx_le⟩
  invFun c := ⟨c.gap, c.idx, by
    have := c.idx_le
    rwa [D.multiplicity_commutationMove hp hne] at this⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

/-- The correspondence keeps the gap. -/
@[simp]
theorem gap_commEquiv (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) :
    (D.commEquiv hp hne c).gap = c.gap := rfl

/-- The correspondence keeps the index. -/
@[simp]
theorem idx_commEquiv (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) :
    (D.commEquiv hp hne c).idx = c.idx := rfl

/-- **The two spans agree away from the one position between the two swapped crossings.** -/
theorem inSpan_commEquiv_iff (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) {t : ℕ}
    (ht : t ≤ D.word.length) (htne : t ≠ p + 1) :
    (D.commEquiv hp hne c).InSpan t ↔ c.InSpan t := by
  rw [Chamber.InSpan, Chamber.InSpan, gap_commEquiv, idx_commEquiv,
    D.countUpTo_commutationMove hp hne _ ht htne]

/-- Every chamber spans a position other than the one between the two swapped crossings: if it
starts there, then it also holds the position after, that crossing being at the other gap. -/
theorem exists_inSpan_ne (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) :
    ∃ t ≤ D.word.length, t ≠ p + 1 ∧ c.InSpan t := by
  by_cases h : c.left = p + 1
  · exact ⟨p + 2, by omega, by omega,
      c.inSpan_add_two_of_left (by omega) (D.levelAt_succ_ne_levelAt hne) h⟩
  · exact ⟨c.left, c.left_le_length, h, c.inSpan_left⟩

/-- **The correspondence keeps the chamber set.** -/
@[cluster_algebras "lem_commutation_invariance"]
theorem chamberSet_commEquiv (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) :
    (D.commEquiv hp hne c).chamberSet = c.chamberSet := by
  obtain ⟨t, ht, htne, hspan⟩ := D.exists_inSpan_ne hp hne c
  rw [(D.commEquiv hp hne c).chamberSet_eq_belowSet
      (by rw [D.length_word_commutationMove hp hne]; exact ht)
      ((D.inSpan_commEquiv_iff hp hne c ht htne).2 hspan),
    c.chamberSet_eq_belowSet ht hspan, gap_commEquiv,
    D.belowSet_commutationMove hp hne ht htne]

/-- **The correspondence is the only map matching chamber sets**: any map from the chambers of `D`
to those of `D'` keeping every chamber set is `commEquiv`. -/
@[cluster_algebras "lem_commutation_invariance"]
theorem eq_commEquiv_of_chamberSet (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ))
    {e : D.Chamber → (D.commutationMove p hp hne).Chamber}
    (h : ∀ c, (e c).chamberSet = c.chamberSet) (c : D.Chamber) :
    e c = D.commEquiv hp hne c := by
  refine Chamber.eq_of_gap_of_chamberSet ?_ ?_
  · rw [Chamber.gap_eq_of_chamberSet_eq (h c), gap_commEquiv]
  · rw [h c, D.chamberSet_commEquiv hp hne]

/-- **The correspondence keeps boundedness**: a chamber is bounded exactly when its image is. -/
theorem bounded_commEquiv_iff (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) :
    (D.commEquiv hp hne c).Bounded ↔ c.Bounded := by
  rw [← not_iff_not, Chamber.not_bounded_iff, Chamber.not_bounded_iff, idx_commEquiv,
    gap_commEquiv, D.multiplicity_commutationMove hp hne]

/-! ### How far the ends move -/

/-- **A chamber's left end either stays put or moves between the two swapped positions**
`p + 1` and `p + 2`. -/
theorem left_commEquiv (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) :
    (D.commEquiv hp hne c).left = c.left ∨
      (c.left = p + 1 ∧ (D.commEquiv hp hne c).left = p + 2) ∨
      (c.left = p + 2 ∧ (D.commEquiv hp hne c).left = p + 1) := by
  have hlen := D.length_word_commutationMove hp hne
  have hLD : c.left ≤ D.word.length := c.left_le_length
  have hLE : (D.commEquiv hp hne c).left ≤ D.word.length := by
    have := (D.commEquiv hp hne c).left_le_length
    rwa [hlen] at this
  have hdown : ∀ t ≤ D.word.length, t ≠ p + 1 → c.InSpan t →
      (D.commEquiv hp hne c).left ≤ t := fun t ht htne h =>
    Chamber.left_le _ ((D.inSpan_commEquiv_iff hp hne c ht htne).2 h)
  have hup : ∀ t ≤ D.word.length, t ≠ p + 1 → (D.commEquiv hp hne c).InSpan t → c.left ≤ t :=
    fun t ht htne h => c.left_le ((D.inSpan_commEquiv_iff hp hne c ht htne).1 h)
  by_cases h1 : c.left = p + 1
  · have hs2 : c.InSpan (p + 2) :=
      c.inSpan_add_two_of_left (by omega) (D.levelAt_succ_ne_levelAt hne) h1
    have hle : (D.commEquiv hp hne c).left ≤ p + 2 := hdown (p + 2) (by omega) (by omega) hs2
    have hge : p + 1 ≤ (D.commEquiv hp hne c).left := by
      by_contra hcon
      have := hup _ (by omega) (by omega) (D.commEquiv hp hne c).inSpan_left
      omega
    rcases Nat.eq_or_lt_of_le hge with he | he
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
  by_cases h2 : (D.commEquiv hp hne c).left = p + 1
  · have hs2 : (D.commEquiv hp hne c).InSpan (p + 2) :=
      (D.commEquiv hp hne c).inSpan_add_two_of_left (by rw [hlen]; omega)
        (by
          obtain ⟨e0, e1⟩ := D.levelAt_commutationMove hp hne
          rw [e0, e1]
          exact (D.levelAt_succ_ne_levelAt hne).symm)
        h2
    have hle : c.left ≤ p + 2 := hup (p + 2) (by omega) (by omega) hs2
    have hge : p + 1 ≤ c.left := by
      by_contra hcon
      have := hdown _ (by omega) (by omega) c.inSpan_left
      omega
    exact Or.inr (Or.inr ⟨by omega, h2⟩)
  · exact Or.inl (le_antisymm (hdown _ hLD h1 c.inSpan_left)
      (hup _ hLE h2 (D.commEquiv hp hne c).inSpan_left))

/-- **A chamber's right end either stays put or moves between the two swapped positions**, being
the left end of the next chamber of its gap when it is a position at all. -/
theorem right_commEquiv (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c : D.Chamber) :
    (D.commEquiv hp hne c).right = c.right ∨
      (c.right = p + 1 ∧ (D.commEquiv hp hne c).right = p + 2) ∨
      (c.right = p + 2 ∧ (D.commEquiv hp hne c).right = p + 1) := by
  by_cases hlast : c.idx = D.multiplicity c.gap
  · refine Or.inl ?_
    have h1 : c.right = D.word.length + 1 := c.right_eq_top_iff.2 hlast
    have h2 : (D.commEquiv hp hne c).right = (D.commutationMove p hp hne).word.length + 1 :=
      (D.commEquiv hp hne c).right_eq_top_iff.2 (by
        rw [idx_commEquiv, gap_commEquiv, D.multiplicity_commutationMove hp hne]
        exact hlast)
    rw [h1, h2, D.length_word_commutationMove hp hne]
  · have hlast' : (D.commEquiv hp hne c).idx ≠
        (D.commutationMove p hp hne).multiplicity (D.commEquiv hp hne c).gap := by
      rw [idx_commEquiv, gap_commEquiv, D.multiplicity_commutationMove hp hne]
      exact hlast
    have hsucc : D.commEquiv hp hne (c.succ hlast) = (D.commEquiv hp hne c).succ hlast' :=
      Chamber.ext' rfl rfl
    rw [c.right_eq_left_succ hlast, (D.commEquiv hp hne c).right_eq_left_succ hlast', ← hsucc]
    exact D.left_commEquiv hp hne (c.succ hlast)

/-- **A chamber whose gap is neither of the two keeps its left end**, which is at neither of the
two swapped positions: an end is a crossing of the chamber's own gap. -/
theorem left_commEquiv_of_gap_ne (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) {c : D.Chamber}
    (h1 : c.gap ≠ D.levelAt p) (h2 : c.gap ≠ D.levelAt (p + 1)) :
    (D.commEquiv hp hne c).left = c.left ∧ c.left ≠ p + 1 ∧ c.left ≠ p + 2 := by
  have e1 : c.left ≠ p + 1 := fun hc => h1 (c.levelAt_of_left_eq_succ hc).symm
  have e2 : c.left ≠ p + 2 := fun hc =>
    h2 (c.levelAt_of_left_eq_succ (t := p + 1) (by omega)).symm
  refine ⟨?_, e1, e2⟩
  rcases D.left_commEquiv hp hne c with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h e1
  · exact absurd h e2

/-- A chamber whose gap is neither of the two swapped gaps keeps its right end, which is at
neither of the two swapped positions. -/
theorem right_commEquiv_of_gap_ne (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) {c : D.Chamber}
    (h1 : c.gap ≠ D.levelAt p) (h2 : c.gap ≠ D.levelAt (p + 1)) :
    (D.commEquiv hp hne c).right = c.right ∧ c.right ≠ p + 1 ∧ c.right ≠ p + 2 := by
  have e1 : c.right ≠ p + 1 := fun hc =>
    h1 (c.levelAt_of_right_eq_succ hc (by omega)).symm
  have e2 : c.right ≠ p + 2 := fun hc =>
    h2 (c.levelAt_of_right_eq_succ (t := p + 1) (by omega) (by omega)).symm
  refine ⟨?_, e1, e2⟩
  rcases D.right_commEquiv hp hne c with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h e1
  · exact absurd h e2

/-! ### The arrows are the same -/

/-- **The arrow condition between chambers of one gap is unchanged**: it says the two are
consecutive, which is a condition on indices, and no index changes. -/
theorem consecutive_commEquiv_iff (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c c' : D.Chamber) :
    ((D.commEquiv hp hne c).gap = (D.commEquiv hp hne c').gap ∧
        (D.commEquiv hp hne c).right = (D.commEquiv hp hne c').left) ↔
      (c.gap = c'.gap ∧ c.right = c'.left) := by
  simp only [gap_commEquiv]
  refine and_congr_right fun hg => ?_
  rw [Chamber.right_eq_left_iff (c := D.commEquiv hp hne c) (c' := D.commEquiv hp hne c') hg,
    Chamber.right_eq_left_iff hg, idx_commEquiv, idx_commEquiv]

/-- **The overlap condition between chambers of adjacent gaps is unchanged**: for chambers `c`,
`c'` at adjacent gaps, `c'.left < c.left < c'.right < c.right` holds after the move exactly when it
held before. -/
theorem overlap_commEquiv_iff (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) {c c' : D.Chamber}
    (hadj : (c'.gap : ℕ) + 1 = (c.gap : ℕ) ∨ (c.gap : ℕ) + 1 = (c'.gap : ℕ)) :
    ((D.commEquiv hp hne c').left < (D.commEquiv hp hne c).left ∧
        (D.commEquiv hp hne c).left < (D.commEquiv hp hne c').right ∧
        (D.commEquiv hp hne c').right < (D.commEquiv hp hne c).right) ↔
      (c'.left < c.left ∧ c.left < c'.right ∧ c'.right < c.right) := by
  have hval : ∀ {x y : Fin (n + 1)}, x = y → (x : ℕ) = (y : ℕ) := fun h => by rw [h]
  by_cases hc : c.gap = D.levelAt p ∨ c.gap = D.levelAt (p + 1)
  · have h1 : c'.gap ≠ D.levelAt p := fun hcon => by
      rcases hc with h | h
      · have := hval h; have := hval hcon; omega
      · have := hval h; have := hval hcon; omega
    have h2 : c'.gap ≠ D.levelAt (p + 1) := fun hcon => by
      rcases hc with h | h
      · have := hval h; have := hval hcon; omega
      · have := hval h; have := hval hcon; omega
    obtain ⟨e1, e2, e3⟩ := D.left_commEquiv_of_gap_ne hp hne h1 h2
    obtain ⟨f1, f2, f3⟩ := D.right_commEquiv_of_gap_ne hp hne h1 h2
    have hl := D.left_commEquiv hp hne c
    have hr := D.right_commEquiv hp hne c
    rw [e1, f1]
    omega
  · rw [not_or] at hc
    obtain ⟨hca, hcb⟩ := hc
    obtain ⟨e1, e2, e3⟩ := D.left_commEquiv_of_gap_ne hp hne hca hcb
    obtain ⟨f1, f2, f3⟩ := D.right_commEquiv_of_gap_ne hp hne hca hcb
    have hl := D.left_commEquiv hp hne c'
    have hr := D.right_commEquiv hp hne c'
    rw [e1, f1]
    omega

/-- **The two quivers have the same arrows.** -/
theorem arrow_commEquiv_iff (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) (c c' : D.Chamber) :
    (D.commutationMove p hp hne).Arrow (D.commEquiv hp hne c) (D.commEquiv hp hne c') ↔
      D.Arrow c c' := by
  rw [Arrow, Arrow]
  exact and_congr (or_congr (D.bounded_commEquiv_iff hp hne c) (D.bounded_commEquiv_iff hp hne c'))
    (or_congr (D.consecutive_commEquiv_iff hp hne c c')
      (and_congr_right fun hadj => D.overlap_commEquiv_iff hp hne hadj))

/-- **The commutation move does not change the quiver**: `commEquiv`, which keeps a chamber's gap
(`gap_commEquiv`) and its chamber set (`chamberSet_commEquiv`), is an isomorphism of quivers. -/
@[cluster_algebras "lem_commutation_invariance"]
def commutationIso (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    D.wiringQuiver.Iso (D.commutationMove p hp hne).wiringQuiver where
  equiv := D.commEquiv hp hne
  mem_frozen_iff v := by
    simp only [wiringQuiver, Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_congr (D.bounded_commEquiv_iff hp hne v)
  arrows_eq u v := by
    simp only [wiringQuiver, wiringArrows]
    exact if_congr (D.arrow_commEquiv_iff hp hne u v) rfl rfl

/-- The underlying bijection of `commutationIso` is `commEquiv`. -/
@[simp]
theorem commutationIso_equiv (hp : p + 2 ≤ D.word.length)
    (hne : (D.levelAt p : ℕ) + 1 < (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 < (D.levelAt p : ℕ)) :
    (D.commutationIso hp hne).equiv = D.commEquiv hp hne := rfl

/-! ### A worked example: four strands

The commutation move needs two gaps at distance at least two, so the smallest diagram that admits
one has four strands. Every claim below is checked by `decide`. -/

/-- Four strands, crossing at gaps `1, 2, 1, 3, 2, 1` numbering the gaps from `1` — a reduced word
for `w₀` on four strands. -/
def wiringFour : WiringDiagram 2 where
  word := [0, 1, 0, 2, 1, 0]
  length_eq := rfl
  prod_eq := by decide

/-- **The commutation move slides the crossing at the top gap past the one at the bottom gap**,
those two being at distance two. -/
theorem commutationMove_wiringFour :
    (wiringFour.commutationMove 2 (by decide) (by decide)).word = [0, 1, 2, 0, 1, 0] := by
  decide

/-- **The two quivers carry the same number of arrows**, which `commutationIso` asserts of them
and `decide` confirms here over all 9 chambers of each. -/
theorem sum_wiringArrows_commutationMove_wiringFour :
    ∑ c : (wiringFour.commutationMove 2 (by decide) (by decide)).Chamber,
        ∑ c' : (wiringFour.commutationMove 2 (by decide) (by decide)).Chamber,
          (wiringFour.commutationMove 2 (by decide) (by decide)).wiringArrows c c' =
      ∑ c : wiringFour.Chamber, ∑ c' : wiringFour.Chamber, wiringFour.wiringArrows c c' := by
  decide

end WiringDiagram

end ClusterAlgebras
