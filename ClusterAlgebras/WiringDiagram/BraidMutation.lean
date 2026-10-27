/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.QuiverOps
public import ClusterAlgebras.WiringDiagram.Braid
public import ClusterAlgebras.WiringDiagram.BraidArith

/-!
# What a braid move does to the counts, the wires, and the chambers

A braid move replaces the factor `(g, h, g)` at `p` by `(h, g, h)`. Unlike the commutation move it
changes the gap multiplicities — `g` is crossed once less and `h` once more — so the two
diagrams do NOT have the same chambers, and the correspondence between them is genuinely piecewise.

This file collects what the correspondence is built from. Everything follows from two facts, as it
did for the commutation move: the word is unchanged outside the three positions, and inside
them the two gaps have exchanged roles. So

* the counts agree before `p`, and from `p + 3` on they differ by a fixed amount — one less for
  the outer gap, one more for the middle one (`countUpTo_braidMove_of_ge`, and hence
  `multiplicity_braidMove`);
* the wires agree before `p` and again from `p + 3` on, this time by the braid relation rather than
  by commutativity (`wire_braidMove_of_ge`);
* and a count that is off by one is a chamber that is missing, which is why no bijection of
  chambers can match every chamber set (`not_exists_equiv_chamberSet`). The site is the chamber
  with no chamber-set partner, and that is the exchange the mutation performs;
* away from the site, `braidChamber` sends a chamber to the chamber of the moved diagram with the
  same gap at `braidWitness`, and the site to `braidReplacement`. This is a bijection
  `braidEquiv`, which preserves chamber sets off the site (`chamberSet_braidChamber_of_ne`), ends
  away from the three crossings (`ends_braidChamber`), and boundedness
  (`bounded_braidChamber_iff`).
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

namespace WiringDiagram

variable (D : WiringDiagram n) {p : ℕ}

/-! ### The word after the move -/

/-- Before the three positions the word is unchanged. -/
theorem levelAt_braidMove_of_lt (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {k : ℕ} (hk : k < p) :
    (D.braidMove p hp hgh hgg).levelAt k = D.levelAt k := by
  rw [levelAt_eq_getElem?, levelAt_eq_getElem?, braidMove, word_splice,
    getElem?_spliceWord_left (by omega) hk]

/-- After the three positions the word is unchanged. -/
theorem levelAt_braidMove_of_ge (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {k : ℕ} (hk : p + 3 ≤ k) :
    (D.braidMove p hp hgh hgg).levelAt k = D.levelAt k := by
  rw [levelAt_eq_getElem?, levelAt_eq_getElem?, braidMove, word_splice,
    getElem?_spliceWord_right (by omega) (by simpa using hk)]

/-! ### The counts after the move -/

/-- Before the three positions the counts are unchanged. -/
theorem countUpTo_braidMove_of_le (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (g : Fin (n + 1)) :
    ∀ t ≤ p, (D.braidMove p hp hgh hgg).countUpTo g t = D.countUpTo g t := by
  have hlen := D.length_word_braidMove hp hgh hgg
  intro t
  induction t with
  | zero =>
    intro _
    rw [countUpTo_zero, countUpTo_zero]
  | succ r ih =>
    intro hr
    rw [(D.braidMove p hp hgh hgg).countUpTo_succ (g := g) (t := r) (by rw [hlen]; omega),
      D.countUpTo_succ (g := g) (t := r) (by omega), ih (by omega),
      D.levelAt_braidMove_of_lt hp hgh hgg (by omega)]

/-- **From the third position on, the counts differ by a fixed amount**: the outer gap has been
crossed once less and the middle gap once more. -/
theorem countUpTo_braidMove_of_ge (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (g : Fin (n + 1)) :
    ∀ t, p + 3 ≤ t → t ≤ D.word.length →
      (D.braidMove p hp hgh hgg).countUpTo g t + (if D.levelAt p = g then 1 else 0) =
        D.countUpTo g t + (if D.levelAt (p + 1) = g then 1 else 0) := by
  have hlen := D.length_word_braidMove hp hgh hgg
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  intro t h3
  induction t, h3 using Nat.le_induction with
  | base =>
    intro _
    rw [(D.braidMove p hp hgh hgg).countUpTo_succ (g := g) (t := p + 2) (by rw [hlen]; omega),
      (D.braidMove p hp hgh hgg).countUpTo_succ (g := g) (t := p + 1) (by rw [hlen]; omega),
      (D.braidMove p hp hgh hgg).countUpTo_succ (g := g) (t := p) (by rw [hlen]; omega),
      D.countUpTo_succ (g := g) (t := p + 2) (by omega),
      D.countUpTo_succ (g := g) (t := p + 1) (by omega),
      D.countUpTo_succ (g := g) (t := p) (by omega),
      D.countUpTo_braidMove_of_le hp hgh hgg g p le_rfl, e0, e1, e2, hgg]
    split_ifs <;> omega
  | succ r hr ih =>
    intro ht
    rw [(D.braidMove p hp hgh hgg).countUpTo_succ (g := g) (t := r) (by rw [hlen]; omega),
      D.countUpTo_succ (g := g) (t := r) (by omega),
      D.levelAt_braidMove_of_ge hp hgh hgg (by omega)]
    have := ih (by omega)
    omega

/-- **The braid move crosses the outer gap once less and the middle gap once more.** -/
theorem multiplicity_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (g : Fin (n + 1)) :
    (D.braidMove p hp hgh hgg).multiplicity g + (if D.levelAt p = g then 1 else 0) =
      D.multiplicity g + (if D.levelAt (p + 1) = g then 1 else 0) := by
  have h := D.countUpTo_braidMove_of_ge hp hgh hgg g D.word.length (by omega) le_rfl
  rw [D.countUpTo_length] at h
  rwa [← (D.braidMove p hp hgh hgg).countUpTo_length,
    D.length_word_braidMove hp hgh hgg]

/-- The outer gap is crossed once less. -/
theorem multiplicity_braidMove_outer (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidMove p hp hgh hgg).multiplicity (D.levelAt p) + 1 = D.multiplicity (D.levelAt p) := by
  have h := D.multiplicity_braidMove hp hgh hgg (D.levelAt p)
  rw [if_pos rfl, if_neg (D.levelAt_succ_ne (Or.inl hgh))] at h
  omega

/-- The middle gap is crossed once more. -/
theorem multiplicity_braidMove_middle (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidMove p hp hgh hgg).multiplicity (D.levelAt (p + 1)) =
      D.multiplicity (D.levelAt (p + 1)) + 1 := by
  have h := D.multiplicity_braidMove hp hgh hgg (D.levelAt (p + 1))
  rw [if_pos rfl, if_neg (Ne.symm (D.levelAt_succ_ne (Or.inl hgh)))] at h
  omega

/-- Every other gap is crossed as often as before. -/
theorem multiplicity_braidMove_of_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {g : Fin (n + 1)} (hga : D.levelAt p ≠ g)
    (hgb : D.levelAt (p + 1) ≠ g) :
    (D.braidMove p hp hgh hgg).multiplicity g = D.multiplicity g := by
  have h := D.multiplicity_braidMove hp hgh hgg g
  rw [if_neg hga, if_neg hgb] at h
  omega

/-! ### The wires after the move -/

/-- Before the three positions the wires are where they were. -/
theorem wire_braidMove_of_le (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    ∀ t ≤ p, (D.braidMove p hp hgh hgg).wire t = D.wire t := by
  have hlen := D.length_word_braidMove hp hgh hgg
  intro t
  induction t with
  | zero =>
    intro _
    rw [wire_zero, wire_zero]
  | succ r ih =>
    intro hr
    rw [(D.braidMove p hp hgh hgg).wire_succ (t := r) (by rw [hlen]; omega),
      D.wire_succ (t := r) (by omega), ih (by omega),
      D.levelAt_braidMove_of_lt hp hgh hgg (by omega)]

/-- **From the third position on the wires are where they were**, by the braid relation. -/
theorem wire_braidMove_of_ge (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    ∀ t, p + 3 ≤ t → t ≤ D.word.length →
      (D.braidMove p hp hgh hgg).wire t = D.wire t := by
  have hlen := D.length_word_braidMove hp hgh hgg
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  intro t h3
  induction t, h3 using Nat.le_induction with
  | base =>
    intro _
    rw [(D.braidMove p hp hgh hgg).wire_succ (t := p + 2) (by rw [hlen]; omega),
      (D.braidMove p hp hgh hgg).wire_succ (t := p + 1) (by rw [hlen]; omega),
      (D.braidMove p hp hgh hgg).wire_succ (t := p) (by rw [hlen]; omega),
      D.wire_succ (t := p + 2) (by omega), D.wire_succ (t := p + 1) (by omega),
      D.wire_succ (t := p) (by omega), D.wire_braidMove_of_le hp hgh hgg p le_rfl, e0, e1, e2,
      hgg]
    have hbr := (gapSwap_braid hgh).symm
    simp only [mul_assoc] at hbr ⊢
    rw [hbr]
  | succ r hr ih =>
    intro ht
    rw [(D.braidMove p hp hgh hgg).wire_succ (t := r) (by rw [hlen]; omega),
      D.wire_succ (t := r) (by omega), ih (by omega),
      D.levelAt_braidMove_of_ge hp hgh hgg (by omega)]

/-- **Outside the three positions the same wires lie below each gap.** -/
theorem belowSet_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {t : ℕ} (ht : t ≤ D.word.length)
    (htp : t ≤ p ∨ p + 3 ≤ t) (g : Fin (n + 1)) :
    (D.braidMove p hp hgh hgg).belowSet t g = D.belowSet t g := by
  have hw : (D.braidMove p hp hgh hgg).wire t = D.wire t := by
    rcases htp with h | h
    · exact D.wire_braidMove_of_le hp hgh hgg t h
    · exact D.wire_braidMove_of_ge hp hgh hgg t h ht
  ext v
  rw [mem_belowSet, mem_belowSet, levelOf, levelOf, hw]

/-! ### A chamber is missing

The chambers of a gap are counted by its multiplicity, so the outer gap has one chamber fewer after
the move. A bijection matching chamber sets would have to preserve gaps, and there is no
gap-preserving bijection to be had. -/

/-- The chambers at a given gap are counted by the gap's multiplicity. -/
def gapFiberEquiv (g : Fin (n + 1)) :
    {c : D.Chamber // c.gap = g} ≃ Fin (D.multiplicity g + 1) where
  toFun := fun ⟨c, hc⟩ => ⟨c.idx, by
    have := c.idx_le
    rw [hc] at this
    omega⟩
  invFun j := ⟨⟨g, j, by have := j.isLt; omega⟩, rfl⟩
  left_inv := fun ⟨_, hc⟩ => Subtype.ext (Chamber.ext' hc.symm rfl)
  right_inv j := rfl

/-- **No bijection of chambers can match every chamber set across a braid move.** The chamber with
no partner is the site, whose chamber set is replaced rather than preserved. -/
theorem not_exists_equiv_chamberSet (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    ¬∃ e : D.Chamber ≃ (D.braidMove p hp hgh hgg).Chamber,
      ∀ c, (e c).chamberSet = c.chamberSet := by
  rintro ⟨e, he⟩
  -- the bijection preserves gaps, so it restricts to the chambers at the outer gap
  have hgap : ∀ c : D.Chamber, (e c).gap = c.gap := fun c =>
    Chamber.gap_eq_of_chamberSet_eq (he c)
  set g := D.levelAt p with hgdef
  have hcard := Fintype.card_congr
    (e.subtypeEquiv (p := fun c => c.gap = g) (q := fun c' => c'.gap = g) fun c => by
      rw [hgap])
  -- but that gap has one chamber fewer after the move
  rw [Fintype.card_congr (D.gapFiberEquiv g),
    Fintype.card_congr ((D.braidMove p hp hgh hgg).gapFiberEquiv g), Fintype.card_fin,
    Fintype.card_fin] at hcard
  have hout := D.multiplicity_braidMove_outer hp hgh hgg
  rw [← hgdef] at hout
  omega

/-! ### The correspondence

A chamber other than the site is read at a position of its span lying outside the three crossings,
and the chamber of the moved diagram at that same position is its partner. The site is exactly the
chamber for which this fails: its span is the two positions `p + 1` and `p + 2` and nothing else,
which is why it is the chamber whose chamber set is not preserved. -/

/-- The position at which a chamber is read: its left end, or `p + 3` when that end is the middle
one of the three crossings. -/
def braidWitness (p : ℕ) (c : D.Chamber) : ℕ := if c.left = p + 2 then p + 3 else c.left

/-- The witness is a genuine position. -/
theorem braidWitness_le (hp : p + 3 ≤ D.word.length) (c : D.Chamber) :
    D.braidWitness p c ≤ D.word.length := by
  rw [braidWitness]
  split_ifs
  · omega
  · exact c.left_le_length

/-- A chamber beginning at the first of the three crossings is the site. -/
theorem eq_braidSite_of_left (hp : p + 3 ≤ D.word.length) {c : D.Chamber} (h : c.left = p + 1) :
    c = D.braidSite hp := by
  refine Chamber.ext' (c.levelAt_of_left_eq_succ h).symm ?_
  have h1 := c.inSpan_left
  rw [Chamber.InSpan, h, ← c.levelAt_of_left_eq_succ h] at h1
  rw [idx_braidSite, ← h1]

/-- A chamber beginning at the middle crossing is the one of the adjacent gap starting there. -/
theorem eq_braidAdjSucc_of_left (hp : p + 3 ≤ D.word.length) {c : D.Chamber}
    (h : c.left = p + 2) : c = D.braidAdjSucc hp := by
  refine Chamber.ext' (c.levelAt_of_left_eq_succ (t := p + 1) (by omega)).symm ?_
  have h1 := c.inSpan_left
  rw [Chamber.InSpan, h, ← c.levelAt_of_left_eq_succ (t := p + 1) (by omega)] at h1
  rw [idx_braidAdjSucc, ← h1]

/-- A chamber beginning after the three crossings is the one of the outer gap starting there. -/
theorem eq_braidSucc_of_left (hp : p + 3 ≤ D.word.length)
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (h : c.left = p + 3) :
    c = D.braidSucc hp := by
  have hgap : D.levelAt (p + 2) = c.gap := c.levelAt_of_left_eq_succ (t := p + 2) (by omega)
  refine Chamber.ext' (by rw [gap_braidSucc, ← hgg, hgap]) ?_
  have h1 := c.inSpan_left
  rw [Chamber.InSpan, h, ← hgap, hgg] at h1
  rw [idx_braidSucc, ← h1]

/-- A chamber ending at the first of the three crossings is `A`. -/
theorem eq_braidPred_of_right (hp : p + 3 ≤ D.word.length) {c : D.Chamber}
    (h : c.right = p + 1) : c = D.braidPred hp := by
  have hgap : D.levelAt p = c.gap := c.levelAt_of_right_eq_succ h (by omega)
  have hlast : c.idx ≠ D.multiplicity c.gap := fun hlast => by
    have := c.right_eq_top_iff.2 hlast
    omega
  have hcr := c.countUpTo_right hlast
  rw [h, ← hgap] at hcr
  have hsucc := D.countUpTo_braidSite_succ hp
  refine Chamber.ext' (by rw [gap_braidPred, hgap]) ?_
  rw [idx_braidPred]
  omega

/-- A chamber ending at the middle crossing is `B`. -/
theorem eq_braidAdjPred_of_right (hp : p + 3 ≤ D.word.length) {c : D.Chamber}
    (h : c.right = p + 2) : c = D.braidAdjPred hp := by
  have hgap : D.levelAt (p + 1) = c.gap :=
    c.levelAt_of_right_eq_succ (t := p + 1) (by omega) (by omega)
  have hlast : c.idx ≠ D.multiplicity c.gap := fun hlast => by
    have := c.right_eq_top_iff.2 hlast
    omega
  have hcr := c.countUpTo_right hlast
  rw [h, ← hgap] at hcr
  have hstep : D.countUpTo (D.levelAt (p + 1)) (p + 2) =
      D.countUpTo (D.levelAt (p + 1)) (p + 1) + 1 := by
    rw [D.countUpTo_succ (g := D.levelAt (p + 1)) (t := p + 1) (by omega), if_pos rfl]
  refine Chamber.ext' (by rw [gap_braidAdjPred, hgap]) ?_
  rw [idx_braidAdjPred]
  omega

/-- **The witness lies in the chamber's span.** -/
theorem inSpan_braidWitness (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    c.InSpan (D.braidWitness p c) := by
  rw [braidWitness]
  split_ifs with h
  · rw [D.eq_braidAdjSucc_of_left hp h]
    refine Chamber.inSpan_of_le_of_lt _ (by omega) ?_ (D.lt_right_braidAdjSucc hp hadj hgg)
    rw [D.left_braidAdjSucc hp]
    omega
  · exact c.inSpan_left

/-- **The witness of a chamber other than the site lies outside the three crossings.** -/
theorem braidWitness_outside (hp : p + 3 ≤ D.word.length) {c : D.Chamber}
    (hc : c ≠ D.braidSite hp) :
    D.braidWitness p c ≤ p ∨ p + 3 ≤ D.braidWitness p c := by
  rw [braidWitness]
  split_ifs with h
  · omega
  · by_cases h1 : c.left = p + 1
    · exact absurd (D.eq_braidSite_of_left hp h1) hc
    · have := c.left_le_length
      omega

/-- **The moved diagram's count of the middle gap** at the three positions: that gap is now crossed
at the first and the third of them. -/
theorem countUpTo_braidMove_middle (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidMove p hp hgh hgg).countUpTo (D.levelAt (p + 1)) (p + 1) =
        D.countUpTo (D.levelAt (p + 1)) p + 1 ∧
      (D.braidMove p hp hgh hgg).countUpTo (D.levelAt (p + 1)) (p + 2) =
        D.countUpTo (D.levelAt (p + 1)) p + 1 ∧
      (D.braidMove p hp hgh hgg).countUpTo (D.levelAt (p + 1)) (p + 3) =
        D.countUpTo (D.levelAt (p + 1)) p + 2 := by
  have hlen := D.length_word_braidMove hp hgh hgg
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  have hb := D.countUpTo_braidMove_of_le hp hgh hgg (D.levelAt (p + 1)) p le_rfl
  have hne := D.levelAt_succ_ne (Or.inl hgh)
  have h1 : (D.braidMove p hp hgh hgg).countUpTo (D.levelAt (p + 1)) (p + 1) =
      D.countUpTo (D.levelAt (p + 1)) p + 1 := by
    rw [(D.braidMove p hp hgh hgg).countUpTo_succ (t := p) (by rw [hlen]; omega), e0, if_pos rfl,
      hb]
  refine ⟨h1, ?_, ?_⟩
  · rw [(D.braidMove p hp hgh hgg).countUpTo_succ (t := p + 1) (by rw [hlen]; omega), e1,
      if_neg (Ne.symm hne), h1]
  · rw [(D.braidMove p hp hgh hgg).countUpTo_succ (t := p + 2) (by rw [hlen]; omega), e2,
      if_pos rfl,
      (D.braidMove p hp hgh hgg).countUpTo_succ (t := p + 1) (by rw [hlen]; omega), e1,
      if_neg (Ne.symm hne), h1]

/-- **The moved diagram's count of the outer gap** at the three positions: that gap is now crossed
at the middle one alone. -/
theorem countUpTo_braidMove_outer (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidMove p hp hgh hgg).countUpTo (D.levelAt p) (p + 1) = D.countUpTo (D.levelAt p) p ∧
      (D.braidMove p hp hgh hgg).countUpTo (D.levelAt p) (p + 2) =
        D.countUpTo (D.levelAt p) p + 1 ∧
      (D.braidMove p hp hgh hgg).countUpTo (D.levelAt p) (p + 3) =
        D.countUpTo (D.levelAt p) p + 1 := by
  have hlen := D.length_word_braidMove hp hgh hgg
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  have ha := D.countUpTo_braidMove_of_le hp hgh hgg (D.levelAt p) p le_rfl
  have hne := D.levelAt_succ_ne (Or.inl hgh)
  have h1 : (D.braidMove p hp hgh hgg).countUpTo (D.levelAt p) (p + 1) =
      D.countUpTo (D.levelAt p) p := by
    rw [(D.braidMove p hp hgh hgg).countUpTo_succ (t := p) (by rw [hlen]; omega), e0, if_neg hne,
      ha]
    omega
  have h2 : (D.braidMove p hp hgh hgg).countUpTo (D.levelAt p) (p + 2) =
      D.countUpTo (D.levelAt p) p + 1 := by
    rw [(D.braidMove p hp hgh hgg).countUpTo_succ (t := p + 1) (by rw [hlen]; omega), e1,
      if_pos rfl, h1]
  refine ⟨h1, h2, ?_⟩
  rw [(D.braidMove p hp hgh hgg).countUpTo_succ (t := p + 2) (by rw [hlen]; omega), e2,
    if_neg hne, h2]

/-- **The chamber of the moved diagram corresponding to `c`.** The site goes to the replacement;
every other chamber goes to the chamber of its own gap at the position where it is read, and so
carries the same chamber set. -/
def braidChamber (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    (D.braidMove p hp hgh hgg).Chamber :=
  if c = D.braidSite hp then D.braidReplacement hp hgh hgg
  else (D.braidMove p hp hgh hgg).chamberAt c.gap (D.braidWitness p c)
    (by rw [D.length_word_braidMove hp hgh hgg]; exact D.braidWitness_le hp c)

/-- The site corresponds to the replacement. -/
@[simp]
theorem braidChamber_braidSite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.braidChamber hp hgh hgg (D.braidSite hp) = D.braidReplacement hp hgh hgg := if_pos rfl

/-- Every other chamber corresponds to the chamber of its gap at its witness. -/
theorem braidChamber_of_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    D.braidChamber hp hgh hgg c = (D.braidMove p hp hgh hgg).chamberAt c.gap (D.braidWitness p c)
      (by rw [D.length_word_braidMove hp hgh hgg]; exact D.braidWitness_le hp c) := if_neg hc

/-- **The correspondence keeps the gap**, away from the site. -/
theorem gap_braidChamber_of_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    (D.braidChamber hp hgh hgg c).gap = c.gap := by
  rw [D.braidChamber_of_ne hp hgh hgg hc, gap_chamberAt]

/-- The index of the corresponding chamber, away from the site. -/
theorem idx_braidChamber_of_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    (D.braidChamber hp hgh hgg c).idx =
      (D.braidMove p hp hgh hgg).countUpTo c.gap (D.braidWitness p c) := by
  rw [D.braidChamber_of_ne hp hgh hgg hc, idx_chamberAt]

/-- **The correspondence keeps the chamber set**, away from the site: the witness lies in the span
and outside the three crossings, and there the two diagrams have the same wires. This is the
first-direction case of `IsBraidMove.exists_iso`. -/
theorem chamberSet_braidChamber_of_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    (D.braidChamber hp hgh hgg c).chamberSet = c.chamberSet := by
  have hw := D.braidWitness_le hp c
  have hout := D.braidWitness_outside hp hc
  rw [D.braidChamber_of_ne hp hgh hgg hc,
    Chamber.chamberSet_eq_belowSet _ (by rw [D.length_word_braidMove hp hgh hgg]; exact hw)
      ((D.braidMove p hp hgh hgg).inSpan_chamberAt c.gap _),
    gap_chamberAt, D.belowSet_braidMove hp hgh hgg hw hout,
    c.chamberSet_eq_belowSet hw (D.inSpan_braidWitness hp (Or.inl hgh) hgg c)]

/-! ### The five affected chambers

The site goes to the replacement, and its four neighbours go to the four neighbours of the
replacement — the same four chambers, with the roles of the two gaps exchanged. -/

/-- The outer gap is crossed twice among the three positions. -/
theorem countUpTo_outer_add_three (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.countUpTo (D.levelAt p) (p + 3) = D.countUpTo (D.levelAt p) p + 2 := by
  have hne := D.levelAt_succ_ne (Or.inl hgh)
  rw [D.countUpTo_succ (g := D.levelAt p) (t := p + 2) (by omega), hgg, if_pos rfl,
    D.countUpTo_succ (g := D.levelAt p) (t := p + 1) (by omega), if_neg hne,
    D.countUpTo_succ (g := D.levelAt p) (t := p) (by omega), if_pos rfl]

/-- The middle gap is not crossed at the first of the three positions. -/
theorem countUpTo_middle_eq (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ)) :
    D.countUpTo (D.levelAt (p + 1)) (p + 1) = D.countUpTo (D.levelAt (p + 1)) p := by
  rcases Nat.lt_or_ge p D.word.length with h | h
  · rw [D.countUpTo_succ (g := D.levelAt (p + 1)) (t := p) h,
      if_neg (Ne.symm (D.levelAt_succ_ne (Or.inl hgh)))]
    omega
  · rw [countUpTo, countUpTo, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

/-- **`A` is not the site**: the two share the site's gap but `A` ends where the site begins, so
they differ already in their index. -/
theorem braidPred_ne_braidSite (hp : p + 3 ≤ D.word.length) :
    D.braidPred hp ≠ D.braidSite hp := fun hc => by
  have h : (D.braidPred hp).idx = (D.braidSite hp).idx := by rw [hc]
  rw [idx_braidSite, D.countUpTo_braidSite_succ hp] at h
  simp only [braidPred, idx_chamberAt] at h
  omega

/-- **`F` is not the site**: same gap again, but `F` begins where the site ends, one index on. -/
theorem braidSucc_ne_braidSite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) : D.braidSucc hp ≠ D.braidSite hp := fun hc => by
  have h : (D.braidSucc hp).idx = (D.braidSite hp).idx := by rw [hc]
  rw [idx_braidSite, D.countUpTo_braidSite_succ hp] at h
  simp only [braidSucc, idx_chamberAt] at h
  rw [D.countUpTo_outer_add_three hp hgh hgg] at h
  omega

/-- **`B` is not the site**, for a different reason from `A` and `F`: it lies in the gap above,
and the two gaps are distinct because the braid site's levels are adjacent. -/
theorem braidAdjPred_ne_braidSite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ)) :
    D.braidAdjPred hp ≠ D.braidSite hp := fun hc => by
  have h : (D.braidAdjPred hp).gap = (D.braidSite hp).gap := by rw [hc]
  rw [gap_braidSite, gap_braidAdjPred] at h
  exact D.levelAt_succ_ne (Or.inl hgh) h

/-- **`C` is not the site**, by the same gap argument as `B`. -/
theorem braidAdjSucc_ne_braidSite (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ)) :
    D.braidAdjSucc hp ≠ D.braidSite hp := fun hc => by
  have h : (D.braidAdjSucc hp).gap = (D.braidSite hp).gap := by rw [hc]
  rw [gap_braidSite, gap_braidAdjSucc] at h
  exact D.levelAt_succ_ne (Or.inl hgh) h

/-- `A` begins at or before the first of the three positions. -/
theorem left_braidPred_le (hp : p + 3 ≤ D.word.length) : (D.braidPred hp).left ≤ p :=
  D.left_chamberAt_le _ (by omega)

/-- `B` begins at or before the first of the three positions, its gap not being crossed there. -/
theorem left_braidAdjPred_le' (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ)) : (D.braidAdjPred hp).left ≤ p :=
  D.left_braidAdjPred_le hp (Or.inl hgh)

/-- **`A` corresponds to the chamber of the moved diagram ending at the middle crossing.** -/
theorem braidChamber_braidPred (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.braidChamber hp hgh hgg (D.braidPred hp) =
      (D.braidMove p hp hgh hgg).braidAdjPred (p := p)
        (by rw [D.length_word_braidMove hp hgh hgg]; omega) := by
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  have hle := D.left_braidPred_le hp
  have hw : D.braidWitness p (D.braidPred hp) = (D.braidPred hp).left := by
    rw [braidWitness, if_neg (by omega)]
  rw [D.braidChamber_of_ne hp hgh hgg (D.braidPred_ne_braidSite hp)]
  refine Chamber.ext' (by rw [gap_chamberAt, gap_braidAdjPred, e1, gap_braidPred]) ?_
  rw [idx_chamberAt, hw, braidAdjPred, idx_chamberAt, e1,
    D.countUpTo_braidMove_of_le hp hgh hgg _ _ hle, (D.countUpTo_braidMove_outer hp hgh hgg).1]
  exact (D.braidPred hp).inSpan_left

/-- **`B` corresponds to the chamber of the moved diagram ending at the first crossing.** -/
theorem braidChamber_braidAdjPred (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.braidChamber hp hgh hgg (D.braidAdjPred hp) =
      (D.braidMove p hp hgh hgg).braidPred (p := p)
        (by rw [D.length_word_braidMove hp hgh hgg]; omega) := by
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  have hle := D.left_braidAdjPred_le' hp hgh
  have hw : D.braidWitness p (D.braidAdjPred hp) = (D.braidAdjPred hp).left := by
    rw [braidWitness, if_neg (by omega)]
  rw [D.braidChamber_of_ne hp hgh hgg (D.braidAdjPred_ne_braidSite hp hgh)]
  refine Chamber.ext' (by rw [gap_chamberAt, gap_braidPred, e0, gap_braidAdjPred]) ?_
  rw [idx_chamberAt, hw, braidPred, idx_chamberAt, e0,
    D.countUpTo_braidMove_of_le hp hgh hgg _ _ hle,
    D.countUpTo_braidMove_of_le hp hgh hgg _ _ le_rfl, gap_braidAdjPred]
  have h1 := (D.braidAdjPred hp).inSpan_left
  rw [Chamber.InSpan, gap_braidAdjPred, idx_braidAdjPred] at h1
  rw [h1]
  exact D.countUpTo_middle_eq hgh

/-- **`C` corresponds to the chamber of the moved diagram beginning after the three crossings.** -/
theorem braidChamber_braidAdjSucc (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.braidChamber hp hgh hgg (D.braidAdjSucc hp) =
      (D.braidMove p hp hgh hgg).braidSucc (p := p)
        (by rw [D.length_word_braidMove hp hgh hgg]; omega) := by
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  have hw : D.braidWitness p (D.braidAdjSucc hp) = p + 3 := by
    rw [braidWitness, if_pos (D.left_braidAdjSucc hp)]
  rw [D.braidChamber_of_ne hp hgh hgg (D.braidAdjSucc_ne_braidSite hp hgh)]
  refine Chamber.ext' (by rw [gap_chamberAt, gap_braidSucc, e0, gap_braidAdjSucc]) ?_
  rw [idx_chamberAt, hw, braidSucc, idx_chamberAt, e0, gap_braidAdjSucc]

/-- **`F` corresponds to the chamber of the moved diagram beginning at the middle crossing.** -/
theorem braidChamber_braidSucc (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.braidChamber hp hgh hgg (D.braidSucc hp) =
      (D.braidMove p hp hgh hgg).braidAdjSucc (p := p)
        (by rw [D.length_word_braidMove hp hgh hgg]; omega) := by
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  have hw : D.braidWitness p (D.braidSucc hp) = p + 3 := by
    rw [braidWitness, if_neg (by rw [D.left_braidSucc hp hgg]; omega), D.left_braidSucc hp hgg]
  rw [D.braidChamber_of_ne hp hgh hgg (D.braidSucc_ne_braidSite hp hgh hgg)]
  refine Chamber.ext' (by rw [gap_chamberAt, gap_braidAdjSucc, e1, gap_braidSucc]) ?_
  rw [idx_chamberAt, hw, braidAdjSucc, idx_chamberAt, e1, gap_braidSucc,
    (D.countUpTo_braidMove_outer hp hgh hgg).2.1, (D.countUpTo_braidMove_outer hp hgh hgg).2.2]

/-! ### The correspondence is a bijection -/

/-- **No chamber but the site corresponds to the replacement.** A chamber read outside the three
crossings has its gap's count either below the replacement's index or above it, never equal. -/
theorem braidChamber_ne_braidReplacement (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    D.braidChamber hp hgh hgg c ≠ D.braidReplacement hp hgh hgg := by
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  obtain ⟨m1, -, m3⟩ := D.countUpTo_braidMove_middle hp hgh hgg
  have hlen := D.length_word_braidMove hp hgh hgg
  have hw := D.braidWitness_le hp c
  have hout := D.braidWitness_outside hp hc
  intro heq
  -- the replacement lies at the middle gap, so `c` does too
  have hZgap : (D.braidReplacement hp hgh hgg).gap = D.levelAt (p + 1) := by
    rw [braidReplacement, gap_braidSite, e0]
  have hgap : c.gap = D.levelAt (p + 1) := by
    rw [← D.gap_braidChamber_of_ne hp hgh hgg hc, heq, hZgap]
  -- and its index would have to be the replacement's
  have hZidx : (D.braidReplacement hp hgh hgg).idx = D.countUpTo (D.levelAt (p + 1)) p + 1 := by
    rw [braidReplacement, idx_braidSite, e0, m1]
  have hidx : (D.braidMove p hp hgh hgg).countUpTo (D.levelAt (p + 1)) (D.braidWitness p c) =
      D.countUpTo (D.levelAt (p + 1)) p + 1 := by
    rw [← hZidx, ← heq, D.braidChamber_of_ne hp hgh hgg hc, idx_chamberAt, hgap]
  rcases hout with h | h
  · -- read before the three crossings, the count is at most the count at `p`
    have hmono := (D.braidMove p hp hgh hgg).countUpTo_le_of_le (g := D.levelAt (p + 1))
      (t := D.braidWitness p c) (t' := p) h (by rw [hlen]; omega)
    rw [D.countUpTo_braidMove_of_le hp hgh hgg _ _ le_rfl] at hmono
    omega
  · -- read after them, it is at least the count at `p + 3`
    have hmono := (D.braidMove p hp hgh hgg).countUpTo_le_of_le (g := D.levelAt (p + 1))
      (t := p + 3) (t' := D.braidWitness p c) h (by rw [hlen]; exact hw)
    omega

/-- **The correspondence is injective**: away from the site a chamber is pinned down by its gap and
its chamber set, both of which it keeps. -/
theorem braidChamber_injective (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    Function.Injective (D.braidChamber hp hgh hgg) := by
  intro c c' h
  by_cases hc : c = D.braidSite hp
  · by_cases hc' : c' = D.braidSite hp
    · rw [hc, hc']
    · rw [hc, D.braidChamber_braidSite hp hgh hgg] at h
      exact absurd h.symm (D.braidChamber_ne_braidReplacement hp hgh hgg hc')
  · by_cases hc' : c' = D.braidSite hp
    · rw [hc', D.braidChamber_braidSite hp hgh hgg] at h
      exact absurd h (D.braidChamber_ne_braidReplacement hp hgh hgg hc)
    · refine Chamber.eq_of_gap_of_chamberSet ?_ ?_
      · rw [← D.gap_braidChamber_of_ne hp hgh hgg hc,
          ← D.gap_braidChamber_of_ne hp hgh hgg hc', h]
      · rw [← D.chamberSet_braidChamber_of_ne hp hgh hgg hc,
          ← D.chamberSet_braidChamber_of_ne hp hgh hgg hc', h]

/-- The move redistributes the crossings among the gaps without changing how many there are. -/
theorem sum_multiplicity_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    ∑ g : Fin (n + 1), (D.braidMove p hp hgh hgg).multiplicity g =
      ∑ g : Fin (n + 1), D.multiplicity g := by
  have hsum := Finset.sum_congr rfl
    (fun (g : Fin (n + 1)) (_ : g ∈ Finset.univ) => D.multiplicity_braidMove hp hgh hgg g)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq] at hsum
  simpa using hsum

/-- **The two diagrams have the same number of chambers**, one gap having gained a chamber and
another lost one. -/
theorem card_chamber_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    Fintype.card D.Chamber = Fintype.card (D.braidMove p hp hgh hgg).Chamber := by
  rw [Fintype.card_congr D.chamberEquiv,
    Fintype.card_congr (D.braidMove p hp hgh hgg).chamberEquiv, Fintype.card_sigma,
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, D.sum_multiplicity_braidMove hp hgh hgg]

/-- **The chambers of the two diagrams correspond**: the site to the replacement, and every other
chamber to the one of its gap carrying the same chamber set. This is the bijection of
`IsBraidMove.existsUnique_equiv` for the first-direction move. -/
def braidEquiv (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.Chamber ≃ (D.braidMove p hp hgh hgg).Chamber :=
  have hbij : Function.Bijective (D.braidChamber hp hgh hgg) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨D.braidChamber_injective hp hgh hgg, D.card_chamber_braidMove hp hgh hgg⟩
  { toFun := D.braidChamber hp hgh hgg
    invFun := Fintype.bijInv hbij
    left_inv := Fintype.leftInverse_bijInv hbij
    right_inv := Fintype.rightInverse_bijInv hbij }

/-- The equivalence acts by `braidChamber`; `Fintype.bijInv` supplies only its inverse. -/
@[simp]
theorem braidEquiv_apply (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    D.braidEquiv hp hgh hgg c = D.braidChamber hp hgh hgg c := rfl

/-! ### Where the ends go

The counts of the two diagrams agree before the three crossings, and differ by a fixed amount from
the third on. So a chamber read before them keeps its span there, and one read after them keeps its
span there; either way its ends are unchanged, unless an end is one of the three positions. Only
the four neighbours of the site have such an end, and for those the ends are read off the
identifications above. -/

/-- **Before the three crossings the two spans agree**, for a chamber read there. -/
theorem inSpan_braidChamber_iff_of_le (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (hw : D.braidWitness p c ≤ p) {t : ℕ} (ht : t ≤ p) :
    (D.braidChamber hp hgh hgg c).InSpan t ↔ c.InSpan t := by
  have hspan := D.inSpan_braidWitness hp (Or.inl hgh) hgg c
  rw [Chamber.InSpan] at hspan
  rw [Chamber.InSpan, Chamber.InSpan, D.gap_braidChamber_of_ne hp hgh hgg hc,
    D.idx_braidChamber_of_ne hp hgh hgg hc, D.countUpTo_braidMove_of_le hp hgh hgg _ _ ht,
    D.countUpTo_braidMove_of_le hp hgh hgg _ _ hw, hspan]

/-- **From the third crossing on the two spans agree**, for a chamber read there: both counts have
moved by the same amount. -/
theorem inSpan_braidChamber_iff_of_ge (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (hw : p + 3 ≤ D.braidWitness p c) {t : ℕ} (ht : p + 3 ≤ t) (htl : t ≤ D.word.length) :
    (D.braidChamber hp hgh hgg c).InSpan t ↔ c.InSpan t := by
  have hspan := D.inSpan_braidWitness hp (Or.inl hgh) hgg c
  rw [Chamber.InSpan] at hspan
  have h1 := D.countUpTo_braidMove_of_ge hp hgh hgg c.gap t ht htl
  have h2 := D.countUpTo_braidMove_of_ge hp hgh hgg c.gap (D.braidWitness p c) hw
    (D.braidWitness_le hp c)
  rw [Chamber.InSpan, Chamber.InSpan, D.gap_braidChamber_of_ne hp hgh hgg hc,
    D.idx_braidChamber_of_ne hp hgh hgg hc, ← hspan]
  omega

/-- **A chamber read before the three crossings begins where it began.** -/
theorem left_braidChamber_of_le (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (h : c.left ≤ p) : (D.braidChamber hp hgh hgg c).left = c.left := by
  have hw : D.braidWitness p c = c.left := by rw [braidWitness, if_neg (by omega)]
  have hwle : D.braidWitness p c ≤ p := by omega
  refine le_antisymm (Chamber.left_le _
    ((D.inSpan_braidChamber_iff_of_le hp hgh hgg hc hwle h).2 c.inSpan_left)) ?_
  by_contra hcon
  have h1 := (D.inSpan_braidChamber_iff_of_le hp hgh hgg hc hwle
    (t := (D.braidChamber hp hgh hgg c).left) (by omega)).1
    (D.braidChamber hp hgh hgg c).inSpan_left
  have := c.left_le h1
  omega

/-- **A chamber read after the three crossings begins where it began.** -/
theorem left_braidChamber_of_ge (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (h : p + 4 ≤ c.left) : (D.braidChamber hp hgh hgg c).left = c.left := by
  have hlen := D.length_word_braidMove hp hgh hgg
  have hw : D.braidWitness p c = c.left := by rw [braidWitness, if_neg (by omega)]
  have hwge : p + 3 ≤ D.braidWitness p c := by omega
  have hcl := c.left_le_length
  refine le_antisymm (Chamber.left_le _
    ((D.inSpan_braidChamber_iff_of_ge hp hgh hgg hc hwge (by omega) hcl).2 c.inSpan_left)) ?_
  by_contra hcon
  by_cases h2 : p + 3 ≤ (D.braidChamber hp hgh hgg c).left
  · -- both ends are read after the three crossings, so the spans agree and the minima do too
    have h1 := (D.inSpan_braidChamber_iff_of_ge hp hgh hgg hc hwge h2
      (by have := (D.braidChamber hp hgh hgg c).left_le_length; omega)).1
      (D.braidChamber hp hgh hgg c).inSpan_left
    have := c.left_le h1
    omega
  · -- otherwise the moved chamber would begin at or before `p + 2`, yet its gap is crossed
    -- at the position just before `c.left`, so its count there is already too large
    exfalso
    obtain ⟨m, hm⟩ : ∃ m, c.left = m + 1 := ⟨c.left - 1, by omega⟩
    have hgap : (D.braidMove p hp hgh hgg).levelAt m = c.gap := by
      rw [D.levelAt_braidMove_of_ge hp hgh hgg (by omega)]
      exact c.levelAt_of_left_eq_succ hm
    have hstep := (D.braidMove p hp hgh hgg).countUpTo_succ (g := c.gap) (t := m)
      (by rw [hlen]; omega)
    rw [hgap, if_pos rfl] at hstep
    have hm1 := (D.braidMove p hp hgh hgg).countUpTo_le_of_le (g := c.gap)
      (t := (D.braidChamber hp hgh hgg c).left) (t' := m) (by omega) (by rw [hlen]; omega)
    have hidx := (D.braidChamber hp hgh hgg c).inSpan_left
    rw [Chamber.InSpan, D.gap_braidChamber_of_ne hp hgh hgg hc,
      D.idx_braidChamber_of_ne hp hgh hgg hc, hw, hm] at hidx
    omega

/-- **A gap other than the two keeps all its counts**: neither of the two letters exchanged by the
move is that gap, so no count of it moves anywhere. -/
theorem countUpTo_braidMove_of_gap_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {g : Fin (n + 1)} (hga : D.levelAt p ≠ g)
    (hgb : D.levelAt (p + 1) ≠ g) :
    ∀ t ≤ D.word.length, (D.braidMove p hp hgh hgg).countUpTo g t = D.countUpTo g t := by
  have hlen := D.length_word_braidMove hp hgh hgg
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  intro t
  induction t with
  | zero =>
    intro _
    rw [countUpTo_zero, countUpTo_zero]
  | succ r ih =>
    intro hr
    have hstep : (if (D.braidMove p hp hgh hgg).levelAt r = g then 1 else 0) =
        (if D.levelAt r = g then 1 else 0) := by
      rcases Nat.lt_or_ge r p with h | h
      · rw [D.levelAt_braidMove_of_lt hp hgh hgg h]
      · rcases Nat.lt_or_ge r (p + 3) with h2 | h2
        · obtain ⟨k, hk⟩ : ∃ k, r = p + k := ⟨r - p, by omega⟩
          have hk3 : k < 3 := by omega
          subst hk
          interval_cases k
          · simp only [Nat.add_zero, e0]
            rw [if_neg hgb, if_neg hga]
          · simp only [e1]
            rw [if_neg hga, if_neg hgb]
          · simp only [e2, hgg]
            rw [if_neg hgb, if_neg hga]
        · rw [D.levelAt_braidMove_of_ge hp hgh hgg h2]
    rw [(D.braidMove p hp hgh hgg).countUpTo_succ (g := g) (t := r) (by rw [hlen]; omega),
      D.countUpTo_succ (g := g) (t := r) (by omega), ih (by omega), hstep]

/-- **A chamber at a gap other than the two keeps both its ends.** -/
theorem ends_braidChamber_of_gap_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (hga : D.levelAt p ≠ c.gap) (hgb : D.levelAt (p + 1) ≠ c.gap) :
    (D.braidChamber hp hgh hgg c).left = c.left ∧
      (D.braidChamber hp hgh hgg c).right = c.right := by
  have hlen := D.length_word_braidMove hp hgh hgg
  have hcnt := D.countUpTo_braidMove_of_gap_ne hp hgh hgg hga hgb
  have hspan := D.inSpan_braidWitness hp (Or.inl hgh) hgg c
  rw [Chamber.InSpan] at hspan
  -- the two chambers have the same gap and the same index, and their gap has the same counts
  have hidx : (D.braidChamber hp hgh hgg c).idx = c.idx := by
    rw [D.idx_braidChamber_of_ne hp hgh hgg hc, hcnt _ (D.braidWitness_le hp c), hspan]
  have hiff : ∀ t ≤ D.word.length, (D.braidChamber hp hgh hgg c).InSpan t ↔ c.InSpan t := by
    intro t ht
    rw [Chamber.InSpan, Chamber.InSpan, D.gap_braidChamber_of_ne hp hgh hgg hc, hidx, hcnt t ht]
  have hmult : (D.braidMove p hp hgh hgg).multiplicity c.gap = D.multiplicity c.gap := by
    rw [← (D.braidMove p hp hgh hgg).countUpTo_length, ← D.countUpTo_length, hlen,
      hcnt _ le_rfl]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact Chamber.left_le _ ((hiff _ c.left_le_length).2 c.inSpan_left)
  · exact c.left_le ((hiff _ (by have := (D.braidChamber hp hgh hgg c).left_le_length; omega)).1
      (D.braidChamber hp hgh hgg c).inSpan_left)
  · by_cases hlast : c.idx = D.multiplicity c.gap
    · rw [c.right_eq_top_iff.2 hlast, (D.braidChamber hp hgh hgg c).right_eq_top_iff.2
        (by rwa [hidx, D.gap_braidChamber_of_ne hp hgh hgg hc, hmult]), hlen]
    · have hlast' : (D.braidChamber hp hgh hgg c).idx ≠
          (D.braidMove p hp hgh hgg).multiplicity (D.braidChamber hp hgh hgg c).gap := by
        rwa [hidx, D.gap_braidChamber_of_ne hp hgh hgg hc, hmult]
      have h1 := c.countUpTo_right hlast
      have h2 := (D.braidChamber hp hgh hgg c).countUpTo_right hlast'
      have hrle : (D.braidChamber hp hgh hgg c).right ≤ D.word.length := by
        have := (D.braidChamber hp hgh hgg c).right_le_length hlast'
        omega
      rw [hidx, D.gap_braidChamber_of_ne hp hgh hgg hc, hcnt _ hrle] at h2
      refine le_antisymm ?_ ?_
      · refine (D.braidChamber hp hgh hgg c).right_le_of_le_countUpTo hlast'
          (by rw [hlen]; exact c.right_le_length hlast) ?_
        rw [hidx, D.gap_braidChamber_of_ne hp hgh hgg hc, hcnt _ (c.right_le_length hlast)]
        omega
      · exact c.right_le_of_le_countUpTo hlast hrle (by omega)

/-- The moved diagram's own braid data at `p`: the two gaps are adjacent the other way round, and
its outer gap is again the one crossed twice. -/
theorem adj_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (((D.braidMove p hp hgh hgg).levelAt p : ℕ) + 1 =
        ((D.braidMove p hp hgh hgg).levelAt (p + 1) : ℕ) ∨
      ((D.braidMove p hp hgh hgg).levelAt (p + 1) : ℕ) + 1 =
        ((D.braidMove p hp hgh hgg).levelAt p : ℕ)) := by
  obtain ⟨e0, e1, -⟩ := D.levelAt_braidMove hp hgh hgg
  rw [e0, e1]
  exact Or.inr hgh

/-- **The moved diagram is again a braid site**, in the second of the two conditions: its first and
third of the three crossings still share a level. -/
theorem gg_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidMove p hp hgh hgg).levelAt (p + 2) = (D.braidMove p hp hgh hgg).levelAt p := by
  obtain ⟨e0, -, e2⟩ := D.levelAt_braidMove hp hgh hgg
  rw [e0, e2]

/-- The corresponding chamber begins no later than the position its partner was read at. -/
theorem left_braidChamber_le (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    (D.braidChamber hp hgh hgg c).left ≤ D.braidWitness p c := by
  rw [D.braidChamber_of_ne hp hgh hgg hc]
  exact left_chamberAt_le _ _ _

/-- **A chamber ending before the three crossings ends where it ended.** -/
theorem right_braidChamber_of_le (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (h : c.right ≤ p) : (D.braidChamber hp hgh hgg c).right = c.right := by
  have hlen := D.length_word_braidMove hp hgh hgg
  have hlr := c.left_lt_right
  have hw : D.braidWitness p c = c.left := by rw [braidWitness, if_neg (by omega)]
  have hwle : D.braidWitness p c ≤ p := by omega
  have hspan : c.InSpan (c.right - 1) :=
    c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
  refine le_antisymm ?_ ?_
  · -- `c.right` is not in the moved chamber's span, and that chamber begins before it
    have h1 : ¬(D.braidChamber hp hgh hgg c).InSpan c.right := by
      rw [D.inSpan_braidChamber_iff_of_le hp hgh hgg hc hwle h]
      exact fun hcon => lt_irrefl _ (c.lt_right_of_inSpan (by omega) hcon)
    have h4 := mt ((D.braidChamber hp hgh hgg c).inSpan_iff_le_lt (t := c.right)
      (by rw [hlen]; omega)).2 h1
    have h3 := D.left_braidChamber_le hp hgh hgg hc
    omega
  · have h1 := (D.inSpan_braidChamber_iff_of_le hp hgh hgg hc hwle (t := c.right - 1)
      (by omega)).2 hspan
    have := (D.braidChamber hp hgh hgg c).lt_right_of_inSpan (by rw [hlen]; omega) h1
    omega

/-- **A chamber read after the three crossings ends where it ended**, provided its right end is
past them too. -/
theorem right_braidChamber_of_ge (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (hwge : p + 3 ≤ D.braidWitness p c) (hr : p + 4 ≤ c.right) :
    (D.braidChamber hp hgh hgg c).right = c.right := by
  have hlen := D.length_word_braidMove hp hgh hgg
  have hidx := D.idx_braidChamber_of_ne hp hgh hgg hc
  have hrel := D.countUpTo_braidMove_of_ge hp hgh hgg c.gap (D.braidWitness p c) hwge
    (D.braidWitness_le hp c)
  have hspanw := D.inSpan_braidWitness hp (Or.inl hgh) hgg c
  have hwlt : D.braidWitness p c < c.right :=
    c.lt_right_of_inSpan (D.braidWitness_le hp c) hspanw
  have hleft := D.left_braidChamber_le hp hgh hgg hc
  rw [Chamber.InSpan] at hspanw
  by_cases hlast : c.idx = D.multiplicity c.gap
  · -- both are the last chamber of their gap, so both ends are the `+∞` sentinel
    have hmult := D.multiplicity_braidMove hp hgh hgg c.gap
    rw [c.right_eq_top_iff.2 hlast, (D.braidChamber hp hgh hgg c).right_eq_top_iff.2
      (by rw [hidx, D.gap_braidChamber_of_ne hp hgh hgg hc]; omega), hlen]
  · have hrl := c.right_le_length hlast
    have hlr := c.left_lt_right
    have hspan : c.InSpan (c.right - 1) := c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
    refine le_antisymm ?_ ?_
    · have h1 : ¬(D.braidChamber hp hgh hgg c).InSpan c.right := by
        rw [D.inSpan_braidChamber_iff_of_ge hp hgh hgg hc hwge (by omega) hrl]
        exact fun hcon => lt_irrefl _ (c.lt_right_of_inSpan hrl hcon)
      have h4 := mt ((D.braidChamber hp hgh hgg c).inSpan_iff_le_lt (t := c.right)
        (by rw [hlen]; omega)).2 h1
      omega
    · have h1 := (D.inSpan_braidChamber_iff_of_ge hp hgh hgg hc hwge (t := c.right - 1)
        (by omega) (by omega)).2 hspan
      have := (D.braidChamber hp hgh hgg c).lt_right_of_inSpan (by rw [hlen]; omega) h1
      omega

/-- A chamber ending just after the third of the three crossings is the site. -/
theorem eq_braidSite_of_right (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (h : c.right = p + 3) :
    c = D.braidSite hp := by
  have hgap : D.levelAt (p + 2) = c.gap :=
    c.levelAt_of_right_eq_succ (t := p + 2) (by omega) (by omega)
  have hga : c.gap = D.levelAt p := by rw [← hgap, hgg]
  have hlast : c.idx ≠ D.multiplicity c.gap := fun hlast => by
    have := c.right_eq_top_iff.2 hlast
    omega
  have hcr := c.countUpTo_right hlast
  rw [h, hga] at hcr
  have h5 := D.countUpTo_outer_add_three hp hgh hgg
  have h6 := D.countUpTo_braidSite_succ hp
  refine Chamber.ext' (by rw [gap_braidSite, hga]) ?_
  rw [idx_braidSite]
  omega

/-- **A chamber with no end among the three crossings keeps both its ends.** The four neighbours of
the site are exactly the chambers with such an end. -/
theorem ends_braidChamber (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (h1 : c.left ≠ p + 2) (h2 : c.left ≠ p + 3) (h3 : c.right ≠ p + 1)
    (h4 : c.right ≠ p + 2) :
    (D.braidChamber hp hgh hgg c).left = c.left ∧
      (D.braidChamber hp hgh hgg c).right = c.right := by
  have hlr := c.left_lt_right
  have hnl : c.left ≠ p + 1 := fun hcon => hc (D.eq_braidSite_of_left hp hcon)
  have hnr : c.right ≠ p + 3 := fun hcon => hc (D.eq_braidSite_of_right hp hgh hgg hcon)
  rcases Nat.lt_or_ge c.left (p + 1) with hl | hl
  · rcases Nat.lt_or_ge c.right (p + 1) with hr | hr
    · exact ⟨D.left_braidChamber_of_le hp hgh hgg hc (by omega),
        D.right_braidChamber_of_le hp hgh hgg hc (by omega)⟩
    · -- the span covers all three crossings, so the gap is neither of the two
      have hs1 : c.InSpan p := c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
      have hs2 : c.InSpan (p + 1) := c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
      have hs3 : c.InSpan (p + 2) := c.inSpan_of_le_of_lt (by omega) (by omega) (by omega)
      exact D.ends_braidChamber_of_gap_ne hp hgh hgg hc
        (c.levelAt_ne_gap (by omega) hs1 hs2) (c.levelAt_ne_gap (by omega) hs2 hs3)
  · have hw : D.braidWitness p c = c.left := by rw [braidWitness, if_neg (by omega)]
    exact ⟨D.left_braidChamber_of_ge hp hgh hgg hc (by omega),
      D.right_braidChamber_of_ge hp hgh hgg hc (by omega) (by omega)⟩

/-! ### The ends of the four neighbours

Each of the four has exactly one end among the three crossings, and that end moves by one place;
its other end stays. -/

/-- `A` keeps its left end. -/
theorem left_braidChamber_braidPred (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidPred hp)).left = (D.braidPred hp).left :=
  D.left_braidChamber_of_le hp hgh hgg (D.braidPred_ne_braidSite hp) (D.left_braidPred_le hp)

/-- **`A`'s right end moves from the first crossing to the middle one.** -/
theorem right_braidChamber_braidPred (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidPred hp)).right = p + 2 := by
  rw [D.braidChamber_braidPred hp hgh hgg]
  exact right_braidAdjPred _ _

/-- `B` keeps its left end. -/
theorem left_braidChamber_braidAdjPred (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidAdjPred hp)).left = (D.braidAdjPred hp).left :=
  D.left_braidChamber_of_le hp hgh hgg (D.braidAdjPred_ne_braidSite hp hgh)
    (D.left_braidAdjPred_le' hp hgh)

/-- **`B`'s right end moves from the middle crossing to the first one.** -/
theorem right_braidChamber_braidAdjPred (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidAdjPred hp)).right = p + 1 := by
  rw [D.braidChamber_braidAdjPred hp hgh hgg]
  exact right_braidPred _ _

/-- **`C`'s left end moves from the middle crossing to the third one.** -/
theorem left_braidChamber_braidAdjSucc (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidAdjSucc hp)).left = p + 3 := by
  rw [D.braidChamber_braidAdjSucc hp hgh hgg]
  exact left_braidSucc _ _ (D.gg_braidMove hp hgh hgg)

/-- `C` keeps its right end. -/
theorem right_braidChamber_braidAdjSucc (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidAdjSucc hp)).right = (D.braidAdjSucc hp).right := by
  have hw : D.braidWitness p (D.braidAdjSucc hp) = p + 3 := by
    rw [braidWitness, if_pos (D.left_braidAdjSucc hp)]
  exact D.right_braidChamber_of_ge hp hgh hgg (D.braidAdjSucc_ne_braidSite hp hgh) (by omega)
    (by have := D.lt_right_braidAdjSucc hp (Or.inl hgh) hgg; omega)

/-- **`F`'s left end moves from the third crossing to the middle one.** -/
theorem left_braidChamber_braidSucc (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidSucc hp)).left = p + 2 := by
  rw [D.braidChamber_braidSucc hp hgh hgg]
  exact left_braidAdjSucc _ _

/-- `F` keeps its right end. -/
theorem right_braidChamber_braidSucc (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidChamber hp hgh hgg (D.braidSucc hp)).right = (D.braidSucc hp).right := by
  have hlf := D.left_braidSucc hp hgg
  have hw : D.braidWitness p (D.braidSucc hp) = p + 3 := by
    rw [braidWitness, if_neg (by omega), hlf]
  exact D.right_braidChamber_of_ge hp hgh hgg (D.braidSucc_ne_braidSite hp hgh hgg) (by omega)
    (by have := (D.braidSucc hp).left_lt_right; omega)

/-- **A chamber other than the site keeps its left end**, unless that end is the middle or the
third of the three crossings. -/
theorem left_braidChamber_eq (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp)
    (h1 : c.left ≠ p + 2) (h2 : c.left ≠ p + 3) :
    (D.braidChamber hp hgh hgg c).left = c.left := by
  have hnl : c.left ≠ p + 1 := fun hcon => hc (D.eq_braidSite_of_left hp hcon)
  rcases Nat.lt_or_ge c.left (p + 1) with hl | hl
  · exact D.left_braidChamber_of_le hp hgh hgg hc (by omega)
  · exact D.left_braidChamber_of_ge hp hgh hgg hc (by omega)

/-- **The correspondence matches the unbounded chambers.** Each of the four neighbours has one end
among the three crossings, and that end moves to another of the three; since all three are genuine
positions, neither the `-∞` nor the `+∞` sentinel is created or destroyed. -/
theorem bounded_braidChamber_iff (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) {c : D.Chamber} (hc : c ≠ D.braidSite hp) :
    (D.braidChamber hp hgh hgg c).Bounded ↔ c.Bounded := by
  have hlen := D.length_word_braidMove hp hgh hgg
  rw [Chamber.Bounded, Chamber.Bounded, Chamber.HasLeftEnd, Chamber.HasLeftEnd,
    Chamber.HasRightEnd, Chamber.HasRightEnd, hlen]
  by_cases h1 : c.left = p + 2
  · obtain rfl := D.eq_braidAdjSucc_of_left hp h1
    rw [D.left_braidChamber_braidAdjSucc hp hgh hgg,
      D.right_braidChamber_braidAdjSucc hp hgh hgg, D.left_braidAdjSucc hp]
    simp
  by_cases h2 : c.left = p + 3
  · obtain rfl := D.eq_braidSucc_of_left hp hgg h2
    rw [D.left_braidChamber_braidSucc hp hgh hgg, D.right_braidChamber_braidSucc hp hgh hgg,
      D.left_braidSucc hp hgg]
    simp
  · rw [D.left_braidChamber_eq hp hgh hgg hc h1 h2]
    by_cases h3 : c.right = p + 1
    · obtain rfl := D.eq_braidPred_of_right hp h3
      rw [D.right_braidChamber_braidPred hp hgh hgg, D.right_braidPred hp]
      omega
    by_cases h4 : c.right = p + 2
    · obtain rfl := D.eq_braidAdjPred_of_right hp h4
      rw [D.right_braidChamber_braidAdjPred hp hgh hgg, D.right_braidAdjPred hp]
      omega
    · rw [(D.ends_braidChamber hp hgh hgg hc h1 h2 h3 h4).2]

end WiringDiagram

end ClusterAlgebras
