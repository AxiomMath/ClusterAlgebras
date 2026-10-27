/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.DoubleWiring.Quiver
public import ClusterAlgebras.QuiverOps

/-!
# A commutation does not change the quiver of a double wiring diagram

Sliding two crossings on disjoint pairs of wires past one another changes the interleaved word
but not the quiver `Q(D)`. This is the combinatorial content of the statement that `Q(D)` depends
only on the isotopy type of `D`, a double wiring diagram being modelled here as a word.

## Implementation notes

* The move carries each letter's colour along with its level, so it covers both the case of two
  crossings of the same colour and the case of two of different colours. Only the first needs the
  levels to be non-adjacent; the second leaves each colour's subword untouched, which is
  `subword_swap_of_colour_ne`. Here the two cases are handled uniformly instead, by computing each
  colour's subword of the exchanged pair.

* `WiringDiagram.commutationMove` splices a list of levels; this one splices a list of letters, so
  `spliceWord` is reused (it is generic in the element type) but the two conditions defining a
  double wiring diagram have to be re-established per colour rather than once.
-/

@[expose] public section

namespace ClusterAlgebras

namespace DoubleWiringDiagram

variable {n : ℕ} (D : DoubleWiringDiagram n)

/-! ### Subwords of a concatenation -/

/-- Taking a colour's subword commutes with concatenation, being a filter followed by a map. -/
theorem subword_append (l r : List (Fin (n + 1) × Colour)) (e : Colour) :
    subword (l ++ r) e = subword l e ++ subword r e := by
  simp [subword, List.filter_append]

/-- A colour's subword of a single letter is that letter's level, or nothing. -/
theorem subword_singleton (a : Fin (n + 1) × Colour) (e : Colour) :
    subword [a] e = if a.2 = e then [a.1] else [] := by
  by_cases h : a.2 = e <;> simp [subword, h]

/-- A colour's subword of a pair of letters. -/
theorem subword_pair (a b : Fin (n + 1) × Colour) (e : Colour) :
    subword [a, b] e = subword [a] e ++ subword [b] e := by
  rw [show ([a, b] : List (Fin (n + 1) × Colour)) = [a] ++ [b] from rfl, subword_append]

/-- The `gapSwap` product of a one-letter subword. -/
theorem prod_map_subword_singleton (a : Fin (n + 1) × Colour) (e : Colour) :
    ((subword [a] e).map gapSwap).prod = if a.2 = e then gapSwap a.1 else 1 := by
  by_cases h : a.2 = e <;> simp [subword_singleton, h]

/-- **Exchanging two letters at non-adjacent levels changes no colour's subword product.** If
either letter has the other colour its factor is `1`; if both have this colour the two factors are
transpositions of non-adjacent gaps, which commute. -/
theorem prod_map_subword_pair_comm {a b : Fin (n + 1) × Colour}
    (hne : ((a.1 : ℕ) + 1 < (b.1 : ℕ)) ∨ ((b.1 : ℕ) + 1 < (a.1 : ℕ))) (e : Colour) :
    ((subword [b, a] e).map gapSwap).prod = ((subword [a, b] e).map gapSwap).prod := by
  rw [subword_pair, subword_pair]
  simp only [List.map_append, List.prod_append, prod_map_subword_singleton]
  by_cases ha : a.2 = e <;> by_cases hb : b.2 = e <;> simp only [ha, hb, if_true, if_false,
    one_mul, mul_one]
  exact gapSwap_comm hne.symm

/-- Exchanging two letters changes no colour's subword length. -/
theorem length_subword_pair_comm (a b : Fin (n + 1) × Colour) (e : Colour) :
    (subword [b, a] e).length = (subword [a, b] e).length := by
  rw [subword_pair, subword_pair, List.length_append, List.length_append]
  omega

/-! ### Exchanging two adjacent entries of a list

The counting facts behind the whole lemma, stated for an arbitrary list because they are about
`spanStart` and not about wiring diagrams. Throughout, `L ++ [a, b] ++ R` is exchanged for
`L ++ [b, a] ++ R`, and `p = L.length` is the position of the first of the two. -/

section Swap

variable {α : Type*} [DecidableEq α] (a b : α) (L R : List α)

/-- Counts agree in every prefix except possibly the one ending between the two entries. -/
theorem count_take_swap (g : α) {t : ℕ} (ht : t ≠ L.length + 1) :
    ((L ++ [b, a] ++ R).take t).count g = ((L ++ [a, b] ++ R).take t).count g := by
  by_cases h : t ≤ L.length
  · rw [List.append_assoc, List.append_assoc, List.take_append_of_le_length h,
      List.take_append_of_le_length h]
  · obtain ⟨k, rfl⟩ : ∃ k, t = L.length + (2 + k) := ⟨t - L.length - 2, by omega⟩
    have e : ∀ x y : α, ([x, y] ++ R).take (2 + k) = [x, y] ++ R.take k := fun x y =>
      List.take_length_add_append (l₁ := [x, y]) k
    rw [List.append_assoc, List.append_assoc, List.take_length_add_append,
      List.take_length_add_append, e, e]
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega

/-- The prefix ending between the two entries sees the first of them. -/
theorem count_take_swap_mid (g : α) :
    ((L ++ [b, a] ++ R).take (L.length + 1)).count g = L.count g + if b = g then 1 else 0 := by
  rw [List.append_assoc, List.take_length_add_append,
    show ([b, a] ++ R).take 1 = [b] from rfl]
  simp only [List.count_append, List.count_cons, List.count_nil]
  by_cases hbg : b = g <;> simp [hbg]

/-- The mid-prefix count with the prefix length named, so that rewriting with it cannot disturb
an unrelated `+ 1` in the goal. -/
theorem count_take_swap_mid' (g : α) {q : ℕ} (hq : L.length = q) :
    ((L ++ [b, a] ++ R).take (q + 1)).count g = L.count g + if b = g then 1 else 0 := by
  subst hq; exact count_take_swap_mid a b L R g

/-- The total count is unaffected by the exchange. -/
theorem count_swap (g : α) : (L ++ [b, a] ++ R).count g = (L ++ [a, b] ++ R).count g := by
  simp only [List.count_append, List.count_cons, List.count_nil]
  omega

/-- When neither exchanged entry is `g`, every prefix count agrees, so `spanStart` at `g` cannot
tell the two lists apart. -/
theorem spanStart_swap_of_ne (g : α) (hag : a ≠ g) (hbg : b ≠ g) {j : ℕ}
    (hj : j ≤ (L ++ [a, b] ++ R).count g) :
    spanStart g j (L ++ [b, a] ++ R) = spanStart g j (L ++ [a, b] ++ R) := by
  have hcount : ∀ t, ((L ++ [b, a] ++ R).take t).count g
      = ((L ++ [a, b] ++ R).take t).count g := by
    intro t
    rcases eq_or_ne t (L.length + 1) with rfl | ht
    · rw [count_take_swap_mid, count_take_swap_mid]
      simp [hag, hbg]
    · exact count_take_swap a b L R g ht
  refine spanStart_eq_of_count g ?_ ?_
  · rw [hcount]
    exact countUpTo_take_spanStart g j _ hj
  · intro s hs
    rw [hcount]
    intro hc
    exact absurd (spanStart_le_of_count g j s _ hc) (by omega)

/-- The count in the prefix ending just before the two entries. -/
theorem count_take_length (g : α) : ((L ++ [b, a] ++ R).take L.length).count g = L.count g := by
  rw [List.append_assoc, List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl]

/-- The count in the prefix ending just after the two entries. -/
theorem count_take_add_two (g : α) :
    ((L ++ [b, a] ++ R).take (L.length + 2)).count g
      = L.count g + (if a = g then 1 else 0) + (if b = g then 1 else 0) := by
  rw [List.append_assoc, List.take_length_add_append,
    show ([b, a] ++ R).take 2 = [b, a] from rfl]
  simp only [List.count_append, List.count_cons, List.count_nil]
  by_cases ha : a = g <;> by_cases hb : b = g <;> simp [ha, hb]

/-- **`spanStart` moves only if it lands on one of the two positions the exchange can move.**

The two candidate landing places are `L.length + 1` and `L.length + 2`. Away from them the
characterisation of `spanStart` transfers: the count at the target is unchanged, and no earlier
prefix can reach it — including the one prefix whose count did change, because its count is one of
the two neighbouring counts, and both of those are already known to miss. -/
theorem spanStart_swap_of_notMem (g : α) (hab : a ≠ b) {j : ℕ}
    (hj : j ≤ (L ++ [a, b] ++ R).count g)
    (h1 : spanStart g j (L ++ [a, b] ++ R) ≠ L.length + 1)
    (h2 : spanStart g j (L ++ [a, b] ++ R) ≠ L.length + 2) :
    spanStart g j (L ++ [b, a] ++ R) = spanStart g j (L ++ [a, b] ++ R) := by
  set s := spanStart g j (L ++ [a, b] ++ R) with hs
  have hmin : ∀ t, ((L ++ [a, b] ++ R).take t).count g = j → s ≤ t := fun t ht =>
    spanStart_le_of_count g j t _ ht
  have hat : ((L ++ [a, b] ++ R).take s).count g = j := countUpTo_take_spanStart g j _ hj
  refine spanStart_eq_of_count g ?_ ?_
  · rw [count_take_swap a b L R g h1]
    exact hat
  · intro t hts hc
    rcases eq_or_ne t (L.length + 1) with rfl | ht
    · -- the one prefix whose count changed; its count is one of the two neighbouring counts
      rw [count_take_swap_mid] at hc
      have hlt : L.length < s := by omega
      have hlt2 : L.length + 2 < s := by omega
      have e0 : ((L ++ [a, b] ++ R).take L.length).count g = L.count g :=
        count_take_length b a L R g
      have e2 : ((L ++ [a, b] ++ R).take (L.length + 2)).count g
          = L.count g + (if b = g then 1 else 0) + (if a = g then 1 else 0) :=
        count_take_add_two b a L R g
      have n0 : L.count g ≠ j := fun h => absurd (hmin _ (e0.trans h)) (by omega)
      have n2 : L.count g + (if b = g then 1 else 0) + (if a = g then 1 else 0) ≠ j := fun h =>
        absurd (hmin _ (e2.trans h)) (by omega)
      by_cases hbg : b = g
      · have hag : a ≠ g := fun h => hab (h.trans hbg.symm)
        simp only [hbg, hag, if_true, if_false, add_zero] at hc n2
        omega
      · simp only [hbg, if_false, add_zero] at hc
        exact n0 hc
    · rw [count_take_swap a b L R g ht] at hc
      exact absurd (hmin t hc) (by omega)

end Swap

/-! ### The move -/

/-- The **letter at position `t`** — its level and its colour together. -/
def letterAt (t : ℕ) : Fin (n + 1) × Colour := D.word.getD t (0, default)

/-- A position's level is the level of the letter there. -/
theorem levelAt_eq_letterAt (t : ℕ) : D.levelAt t = (D.letterAt t).1.castSucc := rfl

/-- A position's colour is the colour of the letter there. -/
theorem colourAt_eq_letterAt (t : ℕ) : D.colourAt t = (D.letterAt t).2 := rfl

/-- At a genuine position the letter is the word's entry there. -/
theorem letterAt_eq_getElem {t : ℕ} (ht : t < D.word.length) : D.letterAt t = D.word[t] := by
  rw [letterAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]

/-- The two entries of the word at positions `p` and `p + 1`. -/
theorem take_two_drop_word {p : ℕ} (hp : p + 2 ≤ D.word.length) :
    (D.word.drop p).take 2 = [D.letterAt p, D.letterAt (p + 1)] := by
  have h1 : p < D.word.length := by omega
  have h2 : p + 1 < D.word.length := by omega
  rw [D.letterAt_eq_getElem h1, D.letterAt_eq_getElem h2,
    List.drop_eq_getElem_cons h1, List.take_succ_cons, List.drop_eq_getElem_cons h2,
    List.take_succ_cons]
  simp

/-- The word of the diagram, split around the two positions to be exchanged. -/
theorem word_eq_append {p : ℕ} (hp : p + 2 ≤ D.word.length) :
    D.word = D.word.take p ++ [D.letterAt p, D.letterAt (p + 1)] ++ D.word.drop (p + 2) := by
  conv_lhs => rw [eq_take_append_middle (l := D.word) (p := p) (k := 2)]
  rw [D.take_two_drop_word hp]
  simp

/-- The **word after exchanging the crossings at `p` and `p + 1`**, each carrying its colour. -/
def commutationWord (p : ℕ) : List (Fin (n + 1) × Colour) :=
  spliceWord D.word p [D.letterAt (p + 1), D.letterAt p]

/-- The exchanged word, split around the two positions. -/
theorem commutationWord_eq_append (p : ℕ) :
    D.commutationWord p =
      D.word.take p ++ [D.letterAt (p + 1), D.letterAt p] ++ D.word.drop (p + 2) := by
  rw [commutationWord, spliceWord]
  simp

/-- Each colour's subword of the exchanged word, in three pieces. -/
theorem subword_commutationWord (p : ℕ) (e : Colour) :
    subword (D.commutationWord p) e =
      subword (D.word.take p) e ++ subword [D.letterAt (p + 1), D.letterAt p] e ++
        subword (D.word.drop (p + 2)) e := by
  rw [commutationWord_eq_append, subword_append, subword_append]

/-- Each colour's subword of the original word, in the same three pieces. -/
theorem subword_word_eq {p : ℕ} (hp : p + 2 ≤ D.word.length) (e : Colour) :
    subword D.word e =
      subword (D.word.take p) e ++ subword [D.letterAt p, D.letterAt (p + 1)] e ++
        subword (D.word.drop (p + 2)) e := by
  conv_lhs => rw [D.word_eq_append hp]
  rw [subword_append, subword_append]

/-- **The commutation move**: exchanging the crossings at positions `p` and `p + 1` when their
levels are non-adjacent. It produces a double wiring diagram — the first assertion of the lemma.

This is the first of the three declarations carrying the entity's tag: this one is its part (i),
`commEquiv` and `commutationIso` are its part (ii). -/
@[cluster_algebras "lem_double_commutation_invariance"]
def commutationMove (p : ℕ) (hp : p + 2 ≤ D.word.length)
    (hne : ((D.letterAt p).1 : ℕ) + 1 < ((D.letterAt (p + 1)).1 : ℕ) ∨
      ((D.letterAt (p + 1)).1 : ℕ) + 1 < ((D.letterAt p).1 : ℕ)) : DoubleWiringDiagram n where
  word := D.commutationWord p
  length_subword e := by
    rw [D.subword_commutationWord p e]
    have h := D.length_subword e
    rw [D.subword_word_eq hp e] at h
    simp only [List.length_append] at h ⊢
    rw [length_subword_pair_comm]
    exact h
  prod_subword e := by
    rw [D.subword_commutationWord p e]
    have h := D.prod_subword e
    rw [D.subword_word_eq hp e] at h
    simp only [List.map_append, List.prod_append] at h ⊢
    rw [prod_map_subword_pair_comm hne]
    exact h

/-- The word of the move is the exchanged word, by definition. -/
@[simp]
theorem word_commutationMove {p : ℕ} {hp hne} :
    (D.commutationMove p hp hne).word = D.commutationWord p := rfl

/-! ### Levels, multiplicities and prefix counts

`levels` is the word with the colours forgotten, so the exchange acts on it as the exchange of two
adjacent entries — which is what the section above is about. -/

/-- The list of levels, split around the two positions to be exchanged. -/
theorem levels_eq_append {p : ℕ} (hp : p + 2 ≤ D.word.length) :
    D.levels = D.levels.take p ++ [D.levelAt p, D.levelAt (p + 1)] ++ D.levels.drop (p + 2) := by
  conv_lhs => rw [levels, D.word_eq_append hp]
  simp [levels, List.map_take, List.map_drop, levelAt_eq_letterAt]

/-- The list of levels of the exchanged diagram: the same two entries, exchanged. -/
theorem levels_commutationMove {p : ℕ} {hp hne} :
    (D.commutationMove p hp hne).levels =
      D.levels.take p ++ [D.levelAt (p + 1), D.levelAt p] ++ D.levels.drop (p + 2) := by
  rw [levels, word_commutationMove, commutationWord_eq_append]
  simp [levels, List.map_take, List.map_drop, levelAt_eq_letterAt]

/-- The prefix of the level list has the expected length. -/
theorem length_take_levels {p : ℕ} (hp : p + 2 ≤ D.word.length) :
    (D.levels.take p).length = p := by
  rw [List.length_take, D.length_levels]
  omega

/-- **Every gap has the same multiplicity after the exchange.** -/
theorem multiplicity_commutationMove {p : ℕ} (hp : p + 2 ≤ D.word.length) {hne}
    (g : Fin (n + 2)) : (D.commutationMove p hp hne).multiplicity g = D.multiplicity g := by
  rw [multiplicity, multiplicity, levels_commutationMove]
  conv_rhs => rw [D.levels_eq_append hp]
  exact count_swap _ _ _ _ g

/-- **Away from the position between the two exchanged crossings, prefix counts agree.** -/
theorem countUpTo_commutationMove {p : ℕ} (hp : p + 2 ≤ D.word.length) {hne}
    (g : Fin (n + 2)) {t : ℕ} (ht : t ≠ p + 1) :
    (D.commutationMove p hp hne).countUpTo g t = D.countUpTo g t := by
  rw [countUpTo, countUpTo, levels_commutationMove]
  conv_rhs => rw [D.levels_eq_append hp]
  exact count_take_swap _ _ _ _ g (by rwa [D.length_take_levels hp])

/-- **A gap crossed at neither of the two positions has every prefix count unchanged.** -/
theorem countUpTo_commutationMove_of_gap_ne {p : ℕ} (hp : p + 2 ≤ D.word.length) {hne}
    {g : Fin (n + 2)} (hg : g ≠ D.levelAt p) (hg' : g ≠ D.levelAt (p + 1)) (t : ℕ) :
    (D.commutationMove p hp hne).countUpTo g t = D.countUpTo g t := by
  rcases eq_or_ne t (p + 1) with rfl | ht
  · rw [countUpTo, countUpTo, levels_commutationMove]
    conv_rhs => rw [D.levels_eq_append hp]
    rw [count_take_swap_mid' _ _ _ _ g (D.length_take_levels hp),
      count_take_swap_mid' _ _ _ _ g (D.length_take_levels hp)]
    simp [Ne.symm hg, Ne.symm hg']
  · exact D.countUpTo_commutationMove hp g ht

/-! ### Chambers and their ends -/

variable {p : ℕ}

/-- The exchange does not change the length of the word. -/
@[simp]
theorem length_word_commutationMove (hp : p + 2 ≤ D.word.length) {hne} :
    (D.commutationMove p hp hne).word.length = D.word.length := by
  rw [word_commutationMove, commutationWord, length_spliceWord (by simpa using hp)]

/-- The two exchanged levels are distinct, non-adjacent levels being distinct. -/
theorem levelAt_ne_levelAt
    (hne : ((D.letterAt p).1 : ℕ) + 1 < ((D.letterAt (p + 1)).1 : ℕ) ∨
      ((D.letterAt (p + 1)).1 : ℕ) + 1 < ((D.letterAt p).1 : ℕ)) :
    D.levelAt p ≠ D.levelAt (p + 1) := by
  intro h
  have h2 : ((D.letterAt p).1 : ℕ) = ((D.letterAt (p + 1)).1 : ℕ) := by
    simpa [levelAt_eq_letterAt] using congrArg Fin.val h
  omega

/-- **The chambers of the two diagrams correspond**, by keeping the gap and the index. Every
multiplicity is unchanged, so the index bound transfers. -/
@[cluster_algebras "lem_double_commutation_invariance"]
def commEquiv (hp : p + 2 ≤ D.word.length) {hne} :
    D.Chamber ≃ (D.commutationMove p hp hne).Chamber where
  toFun c := ⟨c.gap, c.idx, by rw [D.multiplicity_commutationMove hp]; exact c.idx_le⟩
  invFun c := ⟨c.gap, c.idx, by
    have h := c.idx_le
    rwa [D.multiplicity_commutationMove hp] at h⟩
  left_inv _ := Chamber.ext' rfl rfl
  right_inv _ := Chamber.ext' rfl rfl

/-- The correspondence keeps a chamber's gap. -/
@[simp]
theorem gap_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).gap = c.gap := rfl

/-- The correspondence keeps a chamber's index. -/
@[simp]
theorem idx_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).idx = c.idx := rfl

/-- The index bound of a chamber, read as a count on the decomposed list of levels. -/
theorem idx_le_count (hp : p + 2 ≤ D.word.length) (c : D.Chamber) :
    c.idx ≤ (D.levels.take p ++ [D.levelAt p, D.levelAt (p + 1)] ++
      D.levels.drop (p + 2)).count c.gap := by
  have h := c.idx_le
  rw [multiplicity] at h
  rwa [← D.levels_eq_append hp]

/-- **A chamber whose gap is crossed at neither exchanged position keeps its left end.** -/
theorem left_commEquiv_of_gap_ne (hp : p + 2 ≤ D.word.length) {hne} {c : D.Chamber}
    (hg : c.gap ≠ D.levelAt p) (hg' : c.gap ≠ D.levelAt (p + 1)) :
    (D.commEquiv hp (hne := hne) c).left = c.left := by
  change spanStart c.gap c.idx (D.commutationMove p hp hne).levels
    = spanStart c.gap c.idx D.levels
  rw [levels_commutationMove]
  conv_rhs => rw [D.levels_eq_append hp]
  exact spanStart_swap_of_ne _ _ _ _ _ (Ne.symm hg) (Ne.symm hg') (D.idx_le_count hp c)

/-- **The same chamber keeps its right end**, the multiplicity and the length being unchanged. -/
theorem right_commEquiv_of_gap_ne (hp : p + 2 ≤ D.word.length) {hne} {c : D.Chamber}
    (hg : c.gap ≠ D.levelAt p) (hg' : c.gap ≠ D.levelAt (p + 1)) :
    (D.commEquiv hp (hne := hne) c).right = c.right := by
  rw [Chamber.right, Chamber.right, idx_commEquiv, gap_commEquiv,
    D.multiplicity_commutationMove hp, D.length_word_commutationMove hp]
  by_cases h : c.idx = D.multiplicity c.gap
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rw [levels_commutationMove]
    conv_rhs => rw [D.levels_eq_append hp]
    refine spanStart_swap_of_ne _ _ _ _ _ (Ne.symm hg) (Ne.symm hg') ?_
    have hlt : c.idx + 1 ≤ D.multiplicity c.gap := Nat.lt_of_le_of_ne c.idx_le h
    rw [multiplicity] at hlt
    rwa [← D.levels_eq_append hp]

/-- **The ends of such a chamber are not the two positions the exchange can move.** A chamber's
end names a crossing of its own gap, and neither exchanged crossing is one. -/
theorem left_ne_of_gap_ne {c : D.Chamber} (hg : c.gap ≠ D.levelAt p)
    (hg' : c.gap ≠ D.levelAt (p + 1)) : c.left ≠ p + 1 ∧ c.left ≠ p + 2 := by
  refine ⟨fun h => hg (c.levelAt_of_left_eq_succ h).symm,
    fun h => hg' (c.levelAt_of_left_eq_succ (by omega)).symm⟩

/-- A chamber whose gap is crossed at neither exchanged position has its right end at neither
`p + 1` nor `p + 2`. -/
theorem right_ne_of_gap_ne (hp : p + 2 ≤ D.word.length) {c : D.Chamber}
    (hg : c.gap ≠ D.levelAt p) (hg' : c.gap ≠ D.levelAt (p + 1)) :
    c.right ≠ p + 1 ∧ c.right ≠ p + 2 := by
  refine ⟨fun h => hg (c.levelAt_of_right_eq_succ h (by omega)).symm,
    fun h => hg' (c.levelAt_of_right_eq_succ (by omega : c.right = (p + 1) + 1) (by omega)).symm⟩

/-! ### The letters, and hence the end colours

The exchange moves two letters and changes nothing else, each letter carrying its colour. So the
colour a chamber reads at an end is the colour of the crossing bounding it, before and after. -/

/-- The letter at a position, read through `getElem?` so that the splice lemmas apply. -/
theorem letterAt_eq_getElem? (t : ℕ) : D.letterAt t = D.word[t]?.getD (0, default) := by
  rw [letterAt, List.getD_eq_getElem?_getD]

/-- Before the two exchanged positions the word is unchanged. -/
theorem letterAt_commutationMove_of_lt (hp : p + 2 ≤ D.word.length) {hne} {t : ℕ} (ht : t < p) :
    (D.commutationMove p hp hne).letterAt t = D.letterAt t := by
  rw [letterAt_eq_getElem?, letterAt_eq_getElem?, word_commutationMove, commutationWord,
    getElem?_spliceWord_left (by omega) ht]

/-- After them it is unchanged as well. -/
theorem letterAt_commutationMove_of_ge (hp : p + 2 ≤ D.word.length) {hne} {t : ℕ}
    (ht : p + 2 ≤ t) : (D.commutationMove p hp hne).letterAt t = D.letterAt t := by
  rw [letterAt_eq_getElem?, letterAt_eq_getElem?, word_commutationMove, commutationWord,
    getElem?_spliceWord_right (by omega) (by simpa using ht)]

/-- **The two exchanged letters, read off the moved diagram.** Each carries its own colour with
it, which is what makes the end colours below agree. -/
theorem letterAt_commutationMove (hp : p + 2 ≤ D.word.length) {hne} :
    (D.commutationMove p hp hne).letterAt p = D.letterAt (p + 1) ∧
      (D.commutationMove p hp hne).letterAt (p + 1) = D.letterAt p := by
  have hmid : ∀ i : ℕ, i < 2 → (D.commutationMove p hp hne).word[p + i]? =
      ([D.letterAt (p + 1), D.letterAt p] : List (Fin (n + 1) × Colour))[i]? := by
    intro i hi
    rw [word_commutationMove, commutationWord]
    exact getElem?_spliceWord_mid (by omega) (by simpa using hi)
  have h0 : (D.commutationMove p hp hne).word[p]? = some (D.letterAt (p + 1)) := by
    simpa using hmid 0 (by omega)
  have h1 : (D.commutationMove p hp hne).word[p + 1]? = some (D.letterAt p) := by
    simpa using hmid 1 (by omega)
  exact ⟨by rw [letterAt_eq_getElem?, h0]; rfl, by rw [letterAt_eq_getElem?, h1]; rfl⟩

/-! ### How an end moves

An end moves only between `p + 1` and `p + 2`, and it moves exactly when the crossing bounding it
is one of the two exchanged. Everything is stated for the left end; the right end of a chamber is
the left end of the next chamber of its gap (`right_eq_left_succ`), so the right-end facts
follow. -/

/-- The count between the two exchanged positions, in the moved diagram. -/
theorem countUpTo_commutationMove_mid (hp : p + 2 ≤ D.word.length) {hne} (g : Fin (n + 2)) :
    (D.commutationMove p hp hne).countUpTo g (p + 1)
      = D.countUpTo g p + if D.levelAt (p + 1) = g then 1 else 0 := by
  rw [countUpTo, levels_commutationMove,
    count_take_swap_mid' _ _ _ _ g (D.length_take_levels hp), countUpTo]

/-- **The right end of a chamber is the left end of the next chamber of its gap.** -/
theorem right_eq_left_succ {c : D.Chamber} (h : c.idx ≠ D.multiplicity c.gap) :
    c.right = (⟨c.gap, c.idx + 1, Nat.lt_of_le_of_ne c.idx_le h⟩ : D.Chamber).left := by
  rw [Chamber.right, if_neg h]
  rfl

/-- **An end away from the two exchanged positions does not move.** -/
theorem left_commEquiv_of_ne (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber)
    (h1 : c.left ≠ p + 1) (h2 : c.left ≠ p + 2) :
    (D.commEquiv hp (hne := hne) c).left = c.left := by
  change spanStart c.gap c.idx (D.commutationMove p hp hne).levels
    = spanStart c.gap c.idx D.levels
  rw [levels_commutationMove]
  conv_rhs => rw [D.levels_eq_append hp]
  refine spanStart_swap_of_notMem _ _ _ _ _ (D.levelAt_ne_levelAt hne)
    (D.idx_le_count hp c) ?_ ?_
  · rw [← D.levels_eq_append hp, D.length_take_levels hp]
    exact h1
  · rw [← D.levels_eq_append hp, D.length_take_levels hp]
    exact h2

/-- **An end at the first exchanged crossing moves to the second.** -/
theorem left_commEquiv_of_eq_succ (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber)
    (h : c.left = p + 1) : (D.commEquiv hp (hne := hne) c).left = p + 2 := by
  have hgap : D.levelAt p = c.gap := c.levelAt_of_left_eq_succ h
  have hb : D.levelAt (p + 1) ≠ c.gap := fun hc =>
    D.levelAt_ne_levelAt hne (hgap.trans hc.symm)
  have hidx : D.countUpTo c.gap (p + 1) = c.idx := by
    have := c.inSpan_left; rwa [Chamber.InSpan, h] at this
  have hstep : D.countUpTo c.gap (p + 1) = D.countUpTo c.gap p + 1 := by
    rw [D.countUpTo_succ (by omega), if_pos hgap]
  change spanStart c.gap c.idx (D.commutationMove p hp hne).levels = p + 2
  refine spanStart_eq_of_count _ ?_ ?_
  · change (D.commutationMove p hp hne).countUpTo c.gap (p + 2) = c.idx
    rw [D.countUpTo_commutationMove hp _ (by omega),
      D.countUpTo_succ (g := c.gap) (t := p + 1) (by omega), if_neg hb, hidx, add_zero]
  · intro s hs hc
    have hcs : (D.commutationMove p hp hne).countUpTo c.gap s = c.idx := hc
    rcases eq_or_ne s (p + 1) with rfl | hsne
    · rw [D.countUpTo_commutationMove_mid hp, if_neg hb] at hcs
      omega
    · rw [D.countUpTo_commutationMove hp _ hsne] at hcs
      have := D.countUpTo_le_of_le (g := c.gap) (show s ≤ p by omega)
      omega

/-- **An end at the second exchanged crossing moves to the first.** -/
theorem left_commEquiv_of_eq_succ_succ (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber)
    (h : c.left = p + 2) : (D.commEquiv hp (hne := hne) c).left = p + 1 := by
  have hgap : D.levelAt (p + 1) = c.gap := c.levelAt_of_left_eq_succ (by omega)
  have ha : D.levelAt p ≠ c.gap := fun hc => D.levelAt_ne_levelAt hne (hc.trans hgap.symm)
  have hidx : D.countUpTo c.gap (p + 2) = c.idx := by
    have := c.inSpan_left; rwa [Chamber.InSpan, h] at this
  have hstep : D.countUpTo c.gap (p + 2) = D.countUpTo c.gap (p + 1) + 1 := by
    rw [D.countUpTo_succ (g := c.gap) (t := p + 1) (by omega), if_pos hgap]
  have hstep' : D.countUpTo c.gap (p + 1) = D.countUpTo c.gap p := by
    rw [D.countUpTo_succ (by omega), if_neg ha, add_zero]
  change spanStart c.gap c.idx (D.commutationMove p hp hne).levels = p + 1
  refine spanStart_eq_of_count _ ?_ ?_
  · change (D.commutationMove p hp hne).countUpTo c.gap (p + 1) = c.idx
    rw [D.countUpTo_commutationMove_mid hp, if_pos hgap]
    omega
  · intro s hs hc
    have hcs : (D.commutationMove p hp hne).countUpTo c.gap s = c.idx := hc
    rw [D.countUpTo_commutationMove hp _ (by omega)] at hcs
    have := D.countUpTo_le_of_le (g := c.gap) (show s ≤ p by omega)
    omega

/-! ### The end colours -/

/-- **A chamber keeps the colour of its left end.** The colour read at an end is the colour of the
crossing bounding it; the exchange moves crossings without recolouring them, so when the end moves
the colour moves with it. -/
theorem leftEndColour_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber)
    (hl : c.HasLeftEnd) :
    (D.commEquiv hp (hne := hne) c).leftEndColour = c.leftEndColour := by
  have hpos : c.left ≠ 0 := hl
  simp only [Chamber.leftEndColour, colourAt_eq_letterAt]
  rcases eq_or_ne c.left (p + 1) with h1 | h1
  · rw [D.left_commEquiv_of_eq_succ hp c h1, h1, show p + 2 - 1 = p + 1 from rfl,
      show p + 1 - 1 = p from rfl, (D.letterAt_commutationMove hp).2]
  · rcases eq_or_ne c.left (p + 2) with h2 | h2
    · rw [D.left_commEquiv_of_eq_succ_succ hp c h2, h2, show p + 1 - 1 = p from rfl,
        show p + 2 - 1 = p + 1 from rfl, (D.letterAt_commutationMove hp).1]
    · rw [D.left_commEquiv_of_ne hp c h1 h2]
      by_cases hlt : c.left ≤ p
      · rw [D.letterAt_commutationMove_of_lt hp (by omega)]
      · rw [D.letterAt_commutationMove_of_ge hp (by omega)]

/-! ### Every end moves by one involution of the positions

An end is carried to `endMap p` of itself: the identity, except that `p + 1` and `p + 2` trade
places. That single description replaces the three movement lemmas in everything below, and it is
what makes the arrow conditions transfer: `endMap p` is injective, so an EQUALITY of ends is
preserved outright, and it fixes every position other than those two, so a comparison against a
fixed end is preserved as well. -/

/-- The exchange's effect on positions: `p + 1` and `p + 2` trade places. -/
def endMap (p : ℕ) (t : ℕ) : ℕ := if t = p + 1 then p + 2 else if t = p + 2 then p + 1 else t

/-- Exchanging the two positions twice restores them. -/
theorem endMap_involutive (p : ℕ) : Function.Involutive (endMap p) := fun t => by
  unfold endMap; split_ifs <;> omega

/-- Being an involution, the position map is injective — which is what carries condition (i)
of the arrow rule across, that condition being an equality of ends. -/
theorem endMap_injective (p : ℕ) : Function.Injective (endMap p) :=
  (endMap_involutive p).injective

/-- Away from the two positions, `endMap` is the identity. -/
theorem endMap_eq_self {p t : ℕ} (h1 : t ≠ p + 1) (h2 : t ≠ p + 2) : endMap p t = t := by
  unfold endMap; split_ifs <;> omega

/-- **Comparisons against a position `endMap` fixes are unaffected.** -/
theorem lt_endMap_iff {p x y : ℕ} (h1 : x ≠ p + 1) (h2 : x ≠ p + 2) :
    x < endMap p y ↔ x < y := by
  unfold endMap; split_ifs <;> omega

/-- `endMap p y < x` iff `y < x`, for `x ≠ p + 2`. -/
theorem endMap_lt_iff {p x y : ℕ} (h2 : x ≠ p + 2) :
    endMap p y < x ↔ y < x := by
  unfold endMap; split_ifs <;> omega

/-- `x ≤ endMap p y` iff `x ≤ y`, for `x ≠ p + 2`. -/
theorem le_endMap_iff {p x y : ℕ} (h2 : x ≠ p + 2) :
    x ≤ endMap p y ↔ x ≤ y := by
  unfold endMap; split_ifs <;> omega

/-- `endMap p y ≤ x` iff `y ≤ x`, for `x` a position `endMap p` fixes. -/
theorem endMap_le_iff {p x y : ℕ} (h1 : x ≠ p + 1) (h2 : x ≠ p + 2) :
    endMap p y ≤ x ↔ y ≤ x := by
  unfold endMap; split_ifs <;> omega

/-- **The left end is carried by `endMap`.** -/
theorem left_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).left = endMap p c.left := by
  rcases eq_or_ne c.left (p + 1) with h1 | h1
  · rw [D.left_commEquiv_of_eq_succ hp c h1, h1, endMap, if_pos rfl]
  · rcases eq_or_ne c.left (p + 2) with h2 | h2
    · rw [D.left_commEquiv_of_eq_succ_succ hp c h2, h2, endMap, if_neg (by omega), if_pos rfl]
    · rw [D.left_commEquiv_of_ne hp c h1 h2, endMap_eq_self h1 h2]

/-- **The right end is carried by `endMap` too**, being the left end of the next chamber of the
gap — or, for the last chamber, one past the word, which `endMap` fixes. -/
theorem right_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).right = endMap p c.right := by
  by_cases hi : c.idx = D.multiplicity c.gap
  · have hi' : (D.commEquiv hp (hne := hne) c).idx
        = (D.commutationMove p hp hne).multiplicity (D.commEquiv hp (hne := hne) c).gap := by
      simpa [D.multiplicity_commutationMove hp] using hi
    rw [Chamber.right, if_pos hi', Chamber.right, if_pos hi, D.length_word_commutationMove hp,
      endMap_eq_self (by omega) (by omega)]
  · have hi' : (D.commEquiv hp (hne := hne) c).idx
        ≠ (D.commutationMove p hp hne).multiplicity (D.commEquiv hp (hne := hne) c).gap := by
      simpa [D.multiplicity_commutationMove hp] using hi
    rw [D.right_eq_left_succ hi, ← D.left_commEquiv hp,
      (D.commutationMove p hp hne).right_eq_left_succ hi']
    rfl

/-- **A chamber keeps the colour of its right end**, by the same argument one chamber along. -/
theorem rightEndColour_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).rightEndColour = c.rightEndColour := by
  have hrpos : c.right ≠ 0 := by have := c.left_lt_right; omega
  simp only [Chamber.rightEndColour, colourAt_eq_letterAt, D.right_commEquiv hp]
  rcases eq_or_ne c.right (p + 1) with h1 | h1
  · rw [h1, endMap, if_pos rfl, show p + 2 - 1 = p + 1 from rfl,
      show p + 1 - 1 = p from rfl, (D.letterAt_commutationMove hp).2]
  · rcases eq_or_ne c.right (p + 2) with h2 | h2
    · rw [h2, endMap, if_neg (by omega), if_pos rfl, show p + 1 - 1 = p from rfl,
        show p + 2 - 1 = p + 1 from rfl, (D.letterAt_commutationMove hp).1]
    · rw [endMap_eq_self h1 h2]
      by_cases hlt : c.right ≤ p
      · rw [D.letterAt_commutationMove_of_lt hp (by omega)]
      · rw [D.letterAt_commutationMove_of_ge hp (by omega)]

/-! ### The arrows -/

/-- Having a left end depends only on the index, which the correspondence keeps. -/
theorem hasLeftEnd_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).HasLeftEnd ↔ c.HasLeftEnd := by
  simp only [Chamber.HasLeftEnd, ne_eq, Chamber.left_eq_zero_iff, idx_commEquiv]

/-- Having a right end depends only on the index and the multiplicity, both kept. -/
theorem hasRightEnd_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).HasRightEnd ↔ c.HasRightEnd := by
  simp only [Chamber.HasRightEnd, ne_eq, Chamber.right_eq_top_iff, idx_commEquiv, gap_commEquiv,
    D.multiplicity_commutationMove hp]

/-- Boundedness is kept. -/
theorem bounded_commEquiv (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) :
    (D.commEquiv hp (hne := hne) c).Bounded ↔ c.Bounded :=
  and_congr (D.hasLeftEnd_commEquiv hp c) (D.hasRightEnd_commEquiv hp c)

/-- The left end, existing and of a given colour, is kept. -/
theorem hasLeftEnd_and_colour_iff (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber) (x : Colour) :
    ((D.commEquiv hp (hne := hne) c).HasLeftEnd ∧
        (D.commEquiv hp (hne := hne) c).leftEndColour = x) ↔
      (c.HasLeftEnd ∧ c.leftEndColour = x) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hc := (D.hasLeftEnd_commEquiv hp c).1 h1
    exact ⟨hc, by rwa [D.leftEndColour_commEquiv hp c hc] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(D.hasLeftEnd_commEquiv hp c).2 h1, by rwa [D.leftEndColour_commEquiv hp c h1]⟩

/-- The right end, existing and of a given colour, is kept. -/
theorem hasRightEnd_and_colour_iff (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber)
    (x : Colour) :
    ((D.commEquiv hp (hne := hne) c).HasRightEnd ∧
        (D.commEquiv hp (hne := hne) c).rightEndColour = x) ↔
      (c.HasRightEnd ∧ c.rightEndColour = x) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hc := (D.hasRightEnd_commEquiv hp c).1 h1
    exact ⟨hc, by rwa [D.rightEndColour_commEquiv hp c] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(D.hasRightEnd_commEquiv hp c).2 h1, by rwa [D.rightEndColour_commEquiv hp c]⟩

/-- **Adjacent gaps cannot both be exchanged levels**, the exchanged levels being non-adjacent. So
in each of conditions (ii)–(v) of `Arrow`, at least one of the two chambers has both ends fixed. -/
theorem gap_ne_or_gap_ne
    (hne : ((D.letterAt p).1 : ℕ) + 1 < ((D.letterAt (p + 1)).1 : ℕ) ∨
      ((D.letterAt (p + 1)).1 : ℕ) + 1 < ((D.letterAt p).1 : ℕ)) {γ γ' : Fin (n + 2)}
    (hadj : (γ' : ℕ) + 1 = (γ : ℕ) ∨ (γ : ℕ) + 1 = (γ' : ℕ)) :
    (γ ≠ D.levelAt p ∧ γ ≠ D.levelAt (p + 1)) ∨
      (γ' ≠ D.levelAt p ∧ γ' ≠ D.levelAt (p + 1)) := by
  have ha : ((D.levelAt p : Fin (n + 2)) : ℕ) = ((D.letterAt p).1 : ℕ) := rfl
  have hb : ((D.levelAt (p + 1) : Fin (n + 2)) : ℕ) = ((D.letterAt (p + 1)).1 : ℕ) := rfl
  simp only [ne_eq, Fin.ext_iff, ha, hb]
  omega

/-- Boundedness together with both end colours is kept. -/
theorem bounded_and_colours_iff (hp : p + 2 ≤ D.word.length) {hne} (c : D.Chamber)
    (x y : Colour) :
    ((D.commEquiv hp (hne := hne) c).Bounded ∧
        (D.commEquiv hp (hne := hne) c).leftEndColour = x ∧
        (D.commEquiv hp (hne := hne) c).rightEndColour = y) ↔
      (c.Bounded ∧ c.leftEndColour = x ∧ c.rightEndColour = y) := by
  rw [Chamber.Bounded, Chamber.Bounded, and_and_and_comm, and_and_and_comm (a := c.HasLeftEnd),
    D.hasLeftEnd_and_colour_iff hp c x, D.hasRightEnd_and_colour_iff hp c y]

/-- **No arrow of the quiver changes.**

Condition (i) compares two chambers of one gap by an EQUALITY of ends, and `endMap p` is injective,
so it transfers outright. Conditions (ii)--(v) compare chambers at adjacent gaps; by
`gap_ne_or_gap_ne` one of the two has both ends fixed and away from `p + 1` and `p + 2`, and a
comparison against such a position cannot tell `endMap p y` from `y`. The colours are read only at
ends the conditions force to exist. -/
theorem arrow_commEquiv_iff (hp : p + 2 ≤ D.word.length) {hne} (c c' : D.Chamber) :
    (D.commutationMove p hp hne).Arrow (D.commEquiv hp (hne := hne) c)
        (D.commEquiv hp (hne := hne) c') ↔ D.Arrow c c' := by
  rw [Arrow, Arrow]
  simp only [gap_commEquiv]
  refine and_congr (or_congr (D.bounded_commEquiv hp c) (D.bounded_commEquiv hp c'))
    (or_congr (and_congr Iff.rfl (or_congr ?_ ?_)) (and_congr_right fun hadj => ?_))
  · refine and_congr ?_ (D.hasRightEnd_and_colour_iff hp c _)
    rw [D.right_commEquiv hp, D.left_commEquiv hp]
    exact ⟨fun h => endMap_injective p h, fun h => by rw [h]⟩
  · refine and_congr ?_ (D.hasLeftEnd_and_colour_iff hp c _)
    rw [D.left_commEquiv hp, D.right_commEquiv hp]
    exact ⟨fun h => endMap_injective p h, fun h => by rw [h]⟩
  · rcases D.gap_ne_or_gap_ne hne hadj with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
    · -- the first chamber's gap is untouched, so its ends are fixed and avoid both positions
      have hcl := D.left_commEquiv_of_gap_ne hp (hne := hne) (c := c) hg1 hg2
      have hcr := D.right_commEquiv_of_gap_ne hp (hne := hne) (c := c) hg1 hg2
      obtain ⟨hl1, hl2⟩ := D.left_ne_of_gap_ne (c := c) hg1 hg2
      obtain ⟨hr1, hr2⟩ := D.right_ne_of_gap_ne hp (c := c) hg1 hg2
      rw [hcl, hcr, D.left_commEquiv hp c', D.right_commEquiv hp c']
      refine or_congr ?_ (or_congr ?_ (or_congr ?_ ?_))
      · exact and_congr (le_endMap_iff hl2)
          (and_congr (endMap_le_iff hr1 hr2) (D.bounded_and_colours_iff hp c' _ _))
      · exact and_congr (endMap_le_iff hl1 hl2)
          (and_congr (le_endMap_iff hr2) (D.bounded_and_colours_iff hp c _ _))
      · rw [lt_endMap_iff hl1 hl2, endMap_lt_iff hr2, lt_endMap_iff hr1 hr2]
        refine and_congr_right fun h1 => and_congr_right fun _ => and_congr_right fun h3 => ?_
        have hL : c'.HasLeftEnd := by have := c.left_lt_right; unfold Chamber.HasLeftEnd; omega
        rw [D.leftEndColour_commEquiv hp c' hL, D.rightEndColour_commEquiv hp c]
      · rw [endMap_lt_iff hl2, lt_endMap_iff hl1 hl2, endMap_lt_iff hr2]
        refine and_congr_right fun h1 => and_congr_right fun _ => and_congr_right fun h3 => ?_
        have hL : c.HasLeftEnd := by unfold Chamber.HasLeftEnd; omega
        rw [D.leftEndColour_commEquiv hp c hL, D.rightEndColour_commEquiv hp c']
    · -- the second chamber's gap is untouched
      have hcl := D.left_commEquiv_of_gap_ne hp (hne := hne) (c := c') hg1 hg2
      have hcr := D.right_commEquiv_of_gap_ne hp (hne := hne) (c := c') hg1 hg2
      obtain ⟨hl1, hl2⟩ := D.left_ne_of_gap_ne (c := c') hg1 hg2
      obtain ⟨hr1, hr2⟩ := D.right_ne_of_gap_ne hp (c := c') hg1 hg2
      rw [hcl, hcr, D.left_commEquiv hp c, D.right_commEquiv hp c]
      refine or_congr ?_ (or_congr ?_ (or_congr ?_ ?_))
      · exact and_congr (endMap_le_iff hl1 hl2)
          (and_congr (le_endMap_iff hr2) (D.bounded_and_colours_iff hp c' _ _))
      · exact and_congr (le_endMap_iff hl2)
          (and_congr (endMap_le_iff hr1 hr2) (D.bounded_and_colours_iff hp c _ _))
      · rw [endMap_lt_iff hl2, lt_endMap_iff hl1 hl2, endMap_lt_iff hr2]
        refine and_congr_right fun h1 => and_congr_right fun _ => and_congr_right fun h3 => ?_
        have hL : c'.HasLeftEnd := by have := c.left_lt_right; unfold Chamber.HasLeftEnd; omega
        rw [D.leftEndColour_commEquiv hp c' hL, D.rightEndColour_commEquiv hp c]
      · rw [lt_endMap_iff hl1 hl2, endMap_lt_iff hr2, lt_endMap_iff hr1 hr2]
        refine and_congr_right fun h1 => and_congr_right fun _ => and_congr_right fun h3 => ?_
        have hL : c.HasLeftEnd := by unfold Chamber.HasLeftEnd; omega
        rw [D.leftEndColour_commEquiv hp c hL, D.rightEndColour_commEquiv hp c']

/-- **The correspondence is an isomorphism of quivers.** The frozen vertices are the unbounded
chambers, and boundedness is kept; the arrows are the arrow counts, and no arrow changes. -/
@[cluster_algebras "lem_double_commutation_invariance"]
def commutationIso (hp : p + 2 ≤ D.word.length) {hne} :
    D.wiringQuiver.Iso (D.commutationMove p hp hne).wiringQuiver where
  equiv := D.commEquiv hp
  mem_frozen_iff v := by
    simp only [wiringQuiver, Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_congr (D.bounded_commEquiv hp v)
  arrows_eq u v := by
    simp only [wiringQuiver, wiringArrows]
    exact if_congr (D.arrow_commEquiv_iff hp u v) rfl rfl

end DoubleWiringDiagram

end ClusterAlgebras
