/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.WiringDiagram.Chamber

/-!
# The braid move: its site, its replacement, and their neighbours

A braid move replaces a factor `(g, h, g)` of the word by `(h, g, h)`, where `|g - h| = 1`, in
either direction (`WiringDiagram.IsBraidMove`). It exchanges one chamber for another across three
fixed crossings — the site and the replacement — and this file identifies both, together with the
site's four neighbours in `Q(D)`. It ends with the three-strand diagram `wiringThree`.

## Implementation notes

* `WiringDiagram.IsBraidMove D D' p` is the braid move, as a relation: both
  `h = g + 1` and `h + 1 = g` are allowed. `WiringDiagram.braidMove` constructs the moved diagram
  in the first direction, `(g, g + 1, g) ↦ (g + 1, g, g + 1)`; a move in the second direction
  from `D` to `D'` is the first-direction move from `D'` to `D`
  (`WiringDiagram.IsBraidMove.eq_braidMove_or`).
* The site of `IsBraidMove D D' p` is `D.braidSite` and its replacement is `D'.braidSite`: the
  replacement is the moved diagram's chamber in the gap of its outer two crossings, spanning the
  same three positions. In the first direction it is `D.braidReplacement`, by definition.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n : ℕ}

/-! ### Braid moves, in either direction -/

namespace WiringDiagram

/-- A wiring diagram is determined by the levels of its crossings. -/
theorem eq_of_levelAt {D E : WiringDiagram n}
    (h : ∀ k < D.word.length, D.levelAt k = E.levelAt k) : D = E :=
  ext' (List.ext_getElem (by rw [D.length_eq, E.length_eq]) fun k h1 h2 => by
    rw [← D.levelAt_eq_getElem h1, ← E.levelAt_eq_getElem h2, h k h1])

/-- `D'` is obtained from `D` by the **braid move** at `p`: the letters at `p`, `p + 1`, `p + 2`
are `(g, h, g)` with `|g - h| = 1`, and `D'` replaces them by `(h, g, h)`, leaving every other
letter alone. Both directions `h = g + 1` and `h + 1 = g` are allowed. -/
@[cluster_algebras "def_braid_move"]
def IsBraidMove (D D' : WiringDiagram n) (p : ℕ) : Prop :=
  p + 3 ≤ D.word.length ∧ D.levelAt (p + 2) = D.levelAt p ∧
    ((D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ)) ∧
    D'.word = spliceWord D.word p [D.levelAt (p + 1), D.levelAt p, D.levelAt (p + 1)]

namespace IsBraidMove

variable {D D' : WiringDiagram n} {p : ℕ}

/-- The two words have the same length, as any two wiring diagrams on the same strands do. -/
theorem length_word (_h : IsBraidMove D D' p) : D'.word.length = D.word.length := by
  rw [D'.length_eq, D.length_eq]

/-- The three positions of the move lie in the moved word too, so its site — the replacement — is
defined there. -/
theorem length_le (h : IsBraidMove D D' p) : p + 3 ≤ D'.word.length :=
  h.1.trans_eq h.length_word.symm

/-- Before the three positions the words agree. -/
theorem levelAt_of_lt (h : IsBraidMove D D' p) {k : ℕ} (hk : k < p) :
    D'.levelAt k = D.levelAt k := by
  have := h.1
  rw [levelAt_eq_getElem?, levelAt_eq_getElem?, h.2.2.2, getElem?_spliceWord_left (by omega) hk]

/-- After the three positions the words agree. -/
theorem levelAt_of_ge (h : IsBraidMove D D' p) {k : ℕ} (hk : p + 3 ≤ k) :
    D'.levelAt k = D.levelAt k := by
  have := h.1
  rw [levelAt_eq_getElem?, levelAt_eq_getElem?, h.2.2.2,
    getElem?_spliceWord_right (by omega) (by simpa using hk)]

/-- **The three crossings of the move, read off the moved diagram.** -/
theorem levelAt_eq (h : IsBraidMove D D' p) :
    D'.levelAt p = D.levelAt (p + 1) ∧ D'.levelAt (p + 1) = D.levelAt p ∧
      D'.levelAt (p + 2) = D.levelAt (p + 1) := by
  have := h.1
  have hmid : ∀ i : ℕ, i < 3 → D'.word[p + i]? =
      ([D.levelAt (p + 1), D.levelAt p, D.levelAt (p + 1)] : List (Fin (n + 1)))[i]? := by
    intro i hi
    rw [h.2.2.2]
    exact getElem?_spliceWord_mid (by omega) (by simpa using hi)
  have h0 : D'.word[p]? = some (D.levelAt (p + 1)) := by simpa using hmid 0 (by omega)
  have h1 : D'.word[p + 1]? = some (D.levelAt p) := by simpa using hmid 1 (by omega)
  have h2 : D'.word[p + 2]? = some (D.levelAt (p + 1)) := by simpa using hmid 2 (by omega)
  exact ⟨by rw [levelAt_eq_getElem?, h0]; rfl, by rw [levelAt_eq_getElem?, h1]; rfl,
    by rw [levelAt_eq_getElem?, h2]; rfl⟩

end IsBraidMove

end WiringDiagram

/-! ### The site and the replacement of a braid move

The braid move at `p` has its three crossings at word indices `p`, `p + 1`, `p + 2`, so their
positions are `p + 1`, `p + 2`, `p + 3`. -/

namespace WiringDiagram

variable (D : WiringDiagram n) {p : ℕ}

/-- The **site** of the braid move at `p`: the chamber of `D` in the gap of the outer two
crossings, spanning from the first of the three to the third. -/
@[cluster_algebras "def_braid_move"]
def braidSite (hp : p + 3 ≤ D.word.length) : D.Chamber :=
  D.chamberAt (D.levelAt p) (p + 1) (by omega)

/-- The site lies in the gap of the outer two crossings. -/
@[simp]
theorem gap_braidSite (hp : p + 3 ≤ D.word.length) : (D.braidSite hp).gap = D.levelAt p := rfl

/-- The site's index counts the crossings of its gap up to and including the first of the three. -/
@[simp]
theorem idx_braidSite (hp : p + 3 ≤ D.word.length) :
    (D.braidSite hp).idx = D.countUpTo (D.levelAt p) (p + 1) := rfl

/-- The count of the site's gap climbs by one at the first of the three crossings. -/
theorem countUpTo_braidSite_succ (hp : p + 3 ≤ D.word.length) :
    D.countUpTo (D.levelAt p) (p + 1) = D.countUpTo (D.levelAt p) p + 1 := by
  rw [D.countUpTo_succ (g := D.levelAt p) (by omega), if_pos rfl]

/-- **The site's left position is the first of the three crossings**, that crossing lying at the
site's own gap. -/
theorem left_braidSite (hp : p + 3 ≤ D.word.length) : (D.braidSite hp).left = p + 1 :=
  D.left_chamberAt_succ (by omega) rfl

/-- **The site's right position is the third of the three crossings**, the middle one lying at
the other gap. -/
theorem right_braidSite (hp : p + 3 ≤ D.word.length)
    (hne1 : D.levelAt (p + 1) ≠ D.levelAt p)
    (hgg : D.levelAt (p + 2) = D.levelAt p) : (D.braidSite hp).right = p + 3 := by
  have h2 : D.countUpTo (D.levelAt p) (p + 2) = D.countUpTo (D.levelAt p) (p + 1) := by
    rw [D.countUpTo_succ (g := D.levelAt p) (by omega), if_neg hne1]
    omega
  have h3 : D.countUpTo (D.levelAt p) (p + 3) = D.countUpTo (D.levelAt p) (p + 1) + 1 := by
    rw [D.countUpTo_succ (g := D.levelAt p) (by omega), h2, if_pos hgg]
  -- the site is not the last chamber of its gap, since its gap is crossed again at `p + 2`
  have hlt : (D.braidSite hp).idx ≠ D.multiplicity (D.braidSite hp).gap := by
    rw [idx_braidSite, gap_braidSite, ← D.countUpTo_length]
    have hm := D.countUpTo_le_of_le (g := D.levelAt p) (t := p + 3) (t' := D.word.length)
      (by omega) le_rfl
    omega
  rw [Chamber.right, if_neg hlt, idx_braidSite, gap_braidSite]
  refine spanStart_eq_of_count _ ?_ ?_
  · rw [← D.countUpTo_def]; exact h3
  · intro s hs hc
    have hmono := count_take_mono (D.levelAt p) (l := D.word) (s := s) (t := p + 2) (by omega)
    rw [← D.countUpTo_def, ← D.countUpTo_def, h2] at hmono
    rw [← D.countUpTo_def] at hc
    omega

/-- The braid move's word has the same length. -/
theorem length_word_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidMove p hp hgh hgg).word.length = D.word.length := by
  rw [braidMove, word_splice, length_spliceWord (by simpa using hp)]

/-- **The three crossings of the braid move, read off the moved diagram**: the outer gap and the
middle one have been exchanged. -/
theorem levelAt_braidMove (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidMove p hp hgh hgg).levelAt p = D.levelAt (p + 1) ∧
      (D.braidMove p hp hgh hgg).levelAt (p + 1) = D.levelAt p ∧
      (D.braidMove p hp hgh hgg).levelAt (p + 2) = D.levelAt (p + 1) :=
  (show IsBraidMove D (D.braidMove p hp hgh hgg) p from ⟨hp, hgg, Or.inl hgh, rfl⟩).levelAt_eq

/-- The **replacement** of the braid move at `p`, in the direction `braidMove` constructs: the
chamber of the moved diagram in the gap of its outer two crossings, spanning the same three
positions as the site did. For a braid move `IsBraidMove D D' p` in either direction the
replacement is `D'.braidSite`, of which this is the first-direction case. -/
def braidReplacement (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) : (D.braidMove p hp hgh hgg).Chamber :=
  (D.braidMove p hp hgh hgg).braidSite (p := p)
    (by rw [D.length_word_braidMove hp hgh hgg]; omega)

/-- **The replacement lies in the gap above the site's.** -/
theorem gap_braidReplacement (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    ((D.braidReplacement hp hgh hgg).gap : ℕ) = (D.levelAt p : ℕ) + 1 := by
  obtain ⟨e0, -, -⟩ := D.levelAt_braidMove hp hgh hgg
  rw [braidReplacement, gap_braidSite, e0]
  exact hgh.symm

/-- **The replacement starts where the site did.** -/
theorem left_braidReplacement (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidReplacement hp hgh hgg).left = p + 1 :=
  left_braidSite _ _

/-- **The replacement ends where the site did**, so the move exchanges one chamber for another
across the same three crossings. -/
theorem right_braidReplacement (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidReplacement hp hgh hgg).right = p + 3 := by
  obtain ⟨e0, e1, e2⟩ := D.levelAt_braidMove hp hgh hgg
  rw [braidReplacement]
  refine right_braidSite _ _ ?_ ?_
  · -- the middle crossing of the moved diagram lies at the site's gap, not the replacement's
    rw [e0, e1]
    intro hc
    rw [hc] at hgh
    omega
  · rw [e0, e2]

/-- **The braid move does not preserve the site's chamber set.** The replacement lies one gap up
from the site, and a chamber set determines its gap (`Chamber.gap_eq_of_chamberSet_eq`), so the two
sets differ. That difference is not a defect of the correspondence but the whole point of it: the
site is the one chamber whose set changes, and exchanging it is what a mutation does. -/
theorem chamberSet_braidReplacement_ne (hp : p + 3 ≤ D.word.length)
    (hgh : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidReplacement hp hgh hgg).chamberSet ≠ (D.braidSite hp).chamberSet := by
  intro h
  have hg := Chamber.gap_eq_of_chamberSet_eq h
  have h1 := D.gap_braidReplacement hp hgh hgg
  rw [hg, gap_braidSite] at h1
  omega

/-! ### The neighbours of the site

The site `Y` has four neighbours, named by the crossings they abut: `A` and `F` are the chambers
of the site's own gap immediately before and after it, and `B` and `C` those of the adjacent gap
before and after the middle crossing. Each is the chamber of its gap at one of the positions `p`,
`p + 1`, `p + 2`, `p + 3`, the site itself being the one of the outer gap at `p + 1`. -/

/-- The chamber `A` of the site's own gap immediately **before** the site. -/
@[cluster_algebras "lem_braid_neighbours"]
def braidPred (hp : p + 3 ≤ D.word.length) : D.Chamber :=
  D.chamberAt (D.levelAt p) p (by omega)

/-- The chamber `F` of the site's own gap immediately **after** the site. -/
@[cluster_algebras "lem_braid_neighbours"]
def braidSucc (hp : p + 3 ≤ D.word.length) : D.Chamber :=
  D.chamberAt (D.levelAt p) (p + 3) (by omega)

/-- The chamber `B` of the adjacent gap **ending at** the middle crossing. -/
@[cluster_algebras "lem_braid_neighbours"]
def braidAdjPred (hp : p + 3 ≤ D.word.length) : D.Chamber :=
  D.chamberAt (D.levelAt (p + 1)) (p + 1) (by omega)

/-- The chamber `C` of the adjacent gap **starting at** the middle crossing. -/
@[cluster_algebras "lem_braid_neighbours"]
def braidAdjSucc (hp : p + 3 ≤ D.word.length) : D.Chamber :=
  D.chamberAt (D.levelAt (p + 1)) (p + 2) (by omega)

/-- `A` lies in the gap of the outer two crossings. -/
@[simp]
theorem gap_braidPred (hp : p + 3 ≤ D.word.length) : (D.braidPred hp).gap = D.levelAt p := rfl

/-- `F` lies in the gap of the outer two crossings. -/
@[simp]
theorem gap_braidSucc (hp : p + 3 ≤ D.word.length) : (D.braidSucc hp).gap = D.levelAt p := rfl

/-- `B` lies in the gap of the middle crossing. -/
@[simp]
theorem gap_braidAdjPred (hp : p + 3 ≤ D.word.length) :
    (D.braidAdjPred hp).gap = D.levelAt (p + 1) := rfl

/-- `C` lies in the gap of the middle crossing. -/
@[simp]
theorem gap_braidAdjSucc (hp : p + 3 ≤ D.word.length) :
    (D.braidAdjSucc hp).gap = D.levelAt (p + 1) := rfl

/-- `A`'s index counts the crossings of its gap strictly before the three. -/
@[simp]
theorem idx_braidPred (hp : p + 3 ≤ D.word.length) :
    (D.braidPred hp).idx = D.countUpTo (D.levelAt p) p := rfl

/-- `F`'s index counts the crossings of its gap up to and including all three. -/
@[simp]
theorem idx_braidSucc (hp : p + 3 ≤ D.word.length) :
    (D.braidSucc hp).idx = D.countUpTo (D.levelAt p) (p + 3) := rfl

/-- `B`'s index counts the crossings of its gap strictly before the middle one. -/
@[simp]
theorem idx_braidAdjPred (hp : p + 3 ≤ D.word.length) :
    (D.braidAdjPred hp).idx = D.countUpTo (D.levelAt (p + 1)) (p + 1) := rfl

/-- `C`'s index counts the crossings of its gap up to and including the middle one. -/
@[simp]
theorem idx_braidAdjSucc (hp : p + 3 ≤ D.word.length) :
    (D.braidAdjSucc hp).idx = D.countUpTo (D.levelAt (p + 1)) (p + 2) := rfl

/-- The middle of the three crossings lies at a different gap from the outer two, the two gaps
differing by one. -/
theorem levelAt_succ_ne (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ)) :
    D.levelAt (p + 1) ≠ D.levelAt p := fun hc => by rw [hc] at hadj; omega

/-- **`A` ends where the site begins**, at the first of the three crossings. -/
theorem right_braidPred (hp : p + 3 ≤ D.word.length) : (D.braidPred hp).right = p + 1 :=
  D.right_chamberAt (by omega) rfl _

/-- **`F` begins where the site ends**, at the third of the three crossings. -/
theorem left_braidSucc (hp : p + 3 ≤ D.word.length) (hgg : D.levelAt (p + 2) = D.levelAt p) :
    (D.braidSucc hp).left = p + 3 :=
  D.left_chamberAt_succ (t := p + 2) (by omega) hgg

/-- **`B` ends at the middle crossing.** -/
theorem right_braidAdjPred (hp : p + 3 ≤ D.word.length) : (D.braidAdjPred hp).right = p + 2 :=
  D.right_chamberAt (t := p + 1) (by omega) rfl _

/-- **`C` begins at the middle crossing.** -/
theorem left_braidAdjSucc (hp : p + 3 ≤ D.word.length) : (D.braidAdjSucc hp).left = p + 2 :=
  D.left_chamberAt_succ (t := p + 1) (by omega) rfl

/-- **`B` begins before the first of the three crossings**, whose gap is not `B`'s. -/
theorem left_braidAdjPred_le (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ)) :
    (D.braidAdjPred hp).left ≤ p := by
  refine Chamber.left_le _ ?_
  rw [Chamber.InSpan, braidAdjPred, idx_chamberAt, gap_chamberAt,
    D.countUpTo_succ (g := D.levelAt (p + 1)) (by omega),
    if_neg (Ne.symm (D.levelAt_succ_ne hadj))]
  omega

/-- **`C` ends after the last of the three crossings**, whose gap is not `C`'s. -/
theorem lt_right_braidAdjSucc (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) : p + 3 < (D.braidAdjSucc hp).right := by
  by_cases hlast : (D.braidAdjSucc hp).idx = D.multiplicity (D.braidAdjSucc hp).gap
  · rw [Chamber.right, if_pos hlast]
    omega
  · have hne2 : D.levelAt (p + 2) ≠ D.levelAt (p + 1) := by
      rw [hgg]
      exact Ne.symm (D.levelAt_succ_ne hadj)
    have h3 : D.countUpTo (D.levelAt (p + 1)) (p + 3)
        = D.countUpTo (D.levelAt (p + 1)) (p + 2) := by
      rw [D.countUpTo_succ (g := D.levelAt (p + 1)) (by omega), if_neg hne2]
      omega
    have hr := (D.braidAdjSucc hp).countUpTo_right hlast
    rw [gap_braidAdjSucc, idx_braidAdjSucc] at hr
    by_contra hcon
    have hmono := D.countUpTo_le_of_le (g := D.levelAt (p + 1))
      (t := (D.braidAdjSucc hp).right) (t' := p + 3) (by omega) (by omega)
    omega

/-- **The site is bounded**, spanning the first of the three crossings to the third. -/
theorem bounded_braidSite (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) : (D.braidSite hp).Bounded := by
  have hl := D.left_braidSite hp
  have hr := D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg
  exact ⟨by rw [Chamber.HasLeftEnd, hl]; omega, by rw [Chamber.HasRightEnd, hr]; omega⟩

/-- **`A → Y`.** `A` lies in the site's gap and ends where the site begins. -/
theorem arrow_braidPred_braidSite (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.Arrow (D.braidPred hp) (D.braidSite hp) :=
  ⟨Or.inr (D.bounded_braidSite hp hadj hgg),
    Or.inl ⟨rfl, by rw [D.right_braidPred hp, D.left_braidSite hp]⟩⟩

/-- **`C → Y`.** `C` lies in an adjacent gap, begins inside the site's span and ends beyond
it. -/
theorem arrow_braidAdjSucc_braidSite (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.Arrow (D.braidAdjSucc hp) (D.braidSite hp) := by
  refine ⟨Or.inr (D.bounded_braidSite hp hadj hgg), Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [gap_braidSite, gap_braidAdjSucc]
    exact hadj
  · rw [D.left_braidSite hp, D.left_braidAdjSucc hp]
    omega
  · rw [D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg, D.left_braidAdjSucc hp]
    omega
  · rw [D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg]
    exact D.lt_right_braidAdjSucc hp hadj hgg

/-- **`Y → F`.** `F` lies in the site's gap and begins where the site ends. -/
theorem arrow_braidSite_braidSucc (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.Arrow (D.braidSite hp) (D.braidSucc hp) :=
  ⟨Or.inl (D.bounded_braidSite hp hadj hgg),
    Or.inl ⟨rfl, by
      rw [D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg, D.left_braidSucc hp hgg]⟩⟩

/-- **`Y → B`.** `B` lies in an adjacent gap, begins before the site's span and ends inside
it. -/
theorem arrow_braidSite_braidAdjPred (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    D.Arrow (D.braidSite hp) (D.braidAdjPred hp) := by
  refine ⟨Or.inl (D.bounded_braidSite hp hadj hgg), Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [gap_braidSite, gap_braidAdjPred]
    exact hadj.symm
  · rw [D.left_braidSite hp]
    have := D.left_braidAdjPred_le hp hadj
    omega
  · rw [D.left_braidSite hp, D.right_braidAdjPred hp]
    omega
  · rw [D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg, D.right_braidAdjPred hp]
    omega

/-- **The arrows of `Q(D)` into the site are exactly `A → Y` and `C → Y`.** A chamber pointing at
the site either lies in its gap and ends where it begins, making it `A`, or lies in an adjacent
gap with span overlapping the site's on the left, which forces it to begin at the middle crossing,
making it `C`. -/
@[cluster_algebras "lem_braid_neighbours"]
theorem arrow_braidSite_iff (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    D.Arrow c (D.braidSite hp) ↔ c = D.braidPred hp ∨ c = D.braidAdjSucc hp := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, ⟨hg, hr⟩ | ⟨-, h1, h2, -⟩⟩
    · exact Or.inl (Chamber.eq_of_gap_right (by rw [hg, gap_braidSite, gap_braidPred])
        (by rw [hr, D.left_braidSite hp, D.right_braidPred hp]))
    · rw [D.left_braidSite hp] at h1
      rw [D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg] at h2
      have hcl : c.left = p + 2 := by omega
      refine Or.inr (Chamber.eq_of_gap_left ?_ ?_)
      · rw [gap_braidAdjSucc, ← c.levelAt_of_left_eq_succ (t := p + 1) (by omega)]
      · rw [hcl, D.left_braidAdjSucc hp]
  · rintro (rfl | rfl)
    · exact D.arrow_braidPred_braidSite hp hadj hgg
    · exact D.arrow_braidAdjSucc_braidSite hp hadj hgg

/-- **The arrows of `Q(D)` out of the site are exactly `Y → F` and `Y → B`**, the mirror of
`arrow_braidSite_iff`: a chamber the site points at either begins where the site ends, giving `F`,
or ends at the middle crossing, giving `B`. -/
@[cluster_algebras "lem_braid_neighbours"]
theorem braidSite_arrow_iff (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) (c : D.Chamber) :
    D.Arrow (D.braidSite hp) c ↔ c = D.braidSucc hp ∨ c = D.braidAdjPred hp := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, ⟨hg, hl⟩ | ⟨-, -, h2, h3⟩⟩
    · exact Or.inl (Chamber.eq_of_gap_left (by rw [← hg, gap_braidSite, gap_braidSucc])
        (by rw [← hl, D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg,
          D.left_braidSucc hp hgg]))
    · rw [D.left_braidSite hp] at h2
      rw [D.right_braidSite hp (D.levelAt_succ_ne hadj) hgg] at h3
      have hcr : c.right = p + 2 := by omega
      refine Or.inr (Chamber.eq_of_gap_right ?_ ?_)
      · rw [gap_braidAdjPred, ← c.levelAt_of_right_eq_succ (t := p + 1) (by omega) (by omega)]
      · rw [hcr, D.right_braidAdjPred hp]
  · rintro (rfl | rfl)
    · exact D.arrow_braidSite_braidSucc hp hadj hgg
    · exact D.arrow_braidSite_braidAdjPred hp hadj hgg

/-- `A` and `C` lie at different gaps, so the site's two in-neighbours are distinct. -/
theorem braidPred_ne_braidAdjSucc (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ)) :
    D.braidPred hp ≠ D.braidAdjSucc hp := fun hc =>
  D.levelAt_succ_ne hadj (congrArg Chamber.gap hc).symm

/-- `F` and `B` lie at different gaps, so the site's two out-neighbours are distinct. -/
theorem braidSucc_ne_braidAdjPred (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ)) :
    D.braidSucc hp ≠ D.braidAdjPred hp := fun hc =>
  D.levelAt_succ_ne hadj (congrArg Chamber.gap hc).symm

/-- The site's in-neighbours are the two chambers `A` and `C`. -/
theorem filter_arrow_braidSite (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    Finset.univ.filter (fun c => D.Arrow c (D.braidSite hp))
      = {D.braidPred hp, D.braidAdjSucc hp} := by
  ext c
  simp [D.arrow_braidSite_iff hp hadj hgg]

/-- The site's out-neighbours are the two chambers `F` and `B`. -/
theorem filter_braidSite_arrow (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    Finset.univ.filter (fun c => D.Arrow (D.braidSite hp) c)
      = {D.braidSucc hp, D.braidAdjPred hp} := by
  ext c
  simp [D.braidSite_arrow_iff hp hadj hgg]

/-- **The site has exactly four incident arrows**, two in and two out. -/
@[cluster_algebras "lem_braid_neighbours"]
theorem sum_wiringArrows_braidSite (hp : p + 3 ≤ D.word.length)
    (hadj : (D.levelAt p : ℕ) + 1 = (D.levelAt (p + 1) : ℕ) ∨
      (D.levelAt (p + 1) : ℕ) + 1 = (D.levelAt p : ℕ))
    (hgg : D.levelAt (p + 2) = D.levelAt p) :
    ∑ c : D.Chamber, D.wiringArrows c (D.braidSite hp) = 2 ∧
      ∑ c : D.Chamber, D.wiringArrows (D.braidSite hp) c = 2 := by
  simp only [wiringArrows]
  rw [← Finset.sum_filter, ← Finset.sum_filter, D.filter_arrow_braidSite hp hadj hgg,
    D.filter_braidSite_arrow hp hadj hgg]
  exact ⟨by simp [Finset.card_pair (D.braidPred_ne_braidAdjSucc hp hadj)],
    by simp [Finset.card_pair (D.braidSucc_ne_braidAdjPred hp hadj)]⟩

end WiringDiagram

/-! ### A worked example: three strands

The word `[0, 1, 0]` on three strands, in which every claim is checked by `decide`. -/

/-- The wiring diagram on three strands with word `[0, 1, 0]`. -/
def wiringThree : WiringDiagram 1 where
  word := [0, 1, 0]
  length_eq := rfl
  prod_eq := by decide

/-- The gap multiplicities of `wiringThree`: the lower gap is crossed twice and the upper
once. -/
theorem multiplicity_wiringThree :
    wiringThree.multiplicity 0 = 2 ∧ wiringThree.multiplicity 1 = 1 := by decide

/-- `wiringThree` has five chambers. -/
theorem card_chamber_wiringThree : Fintype.card wiringThree.Chamber = 5 := by decide

/-- **Each of the three pairs of strands crosses exactly once**, read off the three positions
of `wiringThree`. -/
theorem crossedPair_wiringThree :
    wiringThree.crossedPair 0 = s(0, 1) ∧ wiringThree.crossedPair 1 = s(0, 2) ∧
      wiringThree.crossedPair 2 = s(1, 2) := by decide

/-- **`wiringThree` has exactly one bounded chamber**, so its quiver has one mutable vertex and
four frozen ones. -/
theorem card_bounded_wiringThree :
    ((Finset.univ : Finset wiringThree.Chamber).filter (fun c => c.Bounded)).card = 1 := by
  decide

/-- **`Q(wiringThree)` has four arrows in all.** -/
theorem sum_wiringArrows_wiringThree :
    ∑ c : wiringThree.Chamber, ∑ c' : wiringThree.Chamber,
      wiringThree.wiringArrows c c' = 4 := by decide

/-- **The braid move carries `[0, 1, 0]` to `[1, 0, 1]`**, the other reduced word for `w₀` on
three strands. -/
theorem braidMove_wiringThree :
    (wiringThree.braidMove 0 (by decide) (by decide) (by decide)).word = [1, 0, 1] := by
  decide

/-- **The site of the braid move at `0` in `wiringThree`** lies in gap `0` and spans the first
crossing to the third. -/
theorem braidSite_wiringThree :
    (wiringThree.braidSite (p := 0) (by decide)).gap = 0 ∧
      (wiringThree.braidSite (p := 0) (by decide)).left = 1 ∧
      (wiringThree.braidSite (p := 0) (by decide)).right = 3 := by decide

/-- **The replacement lies in the other gap, over the same span as the site.** -/
theorem braidReplacement_wiringThree :
    (wiringThree.braidReplacement (p := 0) (by decide) (by decide) (by decide)).gap = 1 ∧
      (wiringThree.braidReplacement (p := 0) (by decide) (by decide) (by decide)).left = 1 ∧
      (wiringThree.braidReplacement (p := 0) (by decide) (by decide) (by decide)).right = 3 := by
  decide

/-- **The site's four neighbours in `wiringThree` are the four unbounded chambers.** -/
theorem braidNeighbours_wiringThree :
    ({wiringThree.braidPred (p := 0) (by decide),
      wiringThree.braidSucc (p := 0) (by decide),
      wiringThree.braidAdjPred (p := 0) (by decide),
      wiringThree.braidAdjSucc (p := 0) (by decide)} : Finset wiringThree.Chamber)
      = Finset.univ.filter (fun c => ¬c.Bounded) := by
  decide

/-- **No chamber of the moved diagram has the site's chamber set**, so there is no bijection of
chambers preserving every chamber set. -/
theorem chamberSet_ne_braidSite_wiringThree :
    ∀ c : (wiringThree.braidMove 0 (by decide) (by decide) (by decide)).Chamber,
      c.chamberSet ≠ (wiringThree.braidSite (p := 0) (by decide)).chamberSet := by
  decide

/-- **Every chamber of `wiringThree` other than the site has its chamber set realised by a chamber
of the moved diagram.** -/
theorem exists_chamberSet_eq_wiringThree :
    ∀ c : wiringThree.Chamber, c ≠ wiringThree.braidSite (p := 0) (by decide) →
      ∃ c' : (wiringThree.braidMove 0 (by decide) (by decide) (by decide)).Chamber,
        c'.chamberSet = c.chamberSet := by
  decide

end ClusterAlgebras
