/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Quiver

/-!
# Words, splices, and the adjacent transpositions

The list and permutation groundwork a wiring diagram is built from: locating the `j`-th
occurrence of a letter in a word, replacing one stretch of a word by another, and the two
relations the adjacent transpositions satisfy. None of it mentions wiring diagrams, and all of
it is used by `ClusterAlgebras.WiringDiagram.Basic` onwards.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Locating the `j`-th occurrence in a list

A chamber's left and right positions are the ends of a stretch of the position axis, and both
are "the first position preceded by exactly `j` crossings of a given gap". Written with
`Nat.find` that is one line, but `Nat.find` goes through well-founded recursion and the KERNEL
does not reduce it, which would put every concrete wiring diagram out of reach of `decide`.
`spanStart` is the same function by structural recursion on the word, so it evaluates. Only its
three specifications are used below, so nothing downstream depends on which definition is
chosen. -/

section SpanStart

variable {α : Type*} [DecidableEq α]

/-- No entries need be consumed before zero occurrences. -/
@[simp]
theorem spanStart_zero (g : α) (l : List α) : spanStart g 0 l = 0 := by cases l <;> rfl

/-- Consuming a matching head uses one entry and one occurrence. -/
theorem spanStart_cons_self (g : α) (j : ℕ) (l : List α) :
    spanStart g (j + 1) (g :: l) = spanStart g j l + 1 := by simp [spanStart]

/-- Consuming a non-matching head uses one entry and no occurrence. -/
theorem spanStart_cons_of_ne {g a : α} (h : a ≠ g) (j : ℕ) (l : List α) :
    spanStart g (j + 1) (a :: l) = spanStart g (j + 1) l + 1 := by simp [spanStart, h]

/-- **`spanStart` lands where the count is `j`.** -/
theorem countUpTo_take_spanStart (g : α) : ∀ (j : ℕ) (l : List α), j ≤ l.count g →
    (l.take (spanStart g j l)).count g = j := by
  intro j l
  induction l generalizing j with
  | nil => simp +contextual
  | cons a l ih =>
    match j with
    | 0 => simp
    | j + 1 =>
      intro h
      rw [List.count_cons] at h
      rcases eq_or_ne a g with rfl | hag
      · rw [spanStart_cons_self, List.take_succ_cons, List.count_cons, ih j (by simp at h; omega)]
        simp
      · rw [spanStart_cons_of_ne hag, List.take_succ_cons, List.count_cons,
          ih (j + 1) (by simp [hag] at h; omega)]
        simp [hag]

/-- **`spanStart` is the least such position.** -/
theorem spanStart_le_of_count (g : α) : ∀ (j t : ℕ) (l : List α),
    (l.take t).count g = j → spanStart g j l ≤ t := by
  intro j t l
  induction l generalizing j t with
  | nil => cases j <;> simp [spanStart]
  | cons a l ih =>
    match j, t with
    | 0, _ => simp
    | j + 1, 0 => simp
    | j + 1, t + 1 =>
      intro h
      rw [List.take_succ_cons, List.count_cons] at h
      rcases eq_or_ne a g with rfl | hag
      · rw [spanStart_cons_self]
        exact Nat.succ_le_succ (ih j t (by simp at h; omega))
      · rw [spanStart_cons_of_ne hag]
        exact Nat.succ_le_succ (ih (j + 1) t (by simp [hag] at h; omega))

/-- **`spanStart` is a genuine position.** -/
theorem spanStart_le_length (g : α) : ∀ (j : ℕ) (l : List α), j ≤ l.count g →
    spanStart g j l ≤ l.length := by
  intro j l
  induction l generalizing j with
  | nil => simp +contextual
  | cons a l ih =>
    match j with
    | 0 => simp
    | j + 1 =>
      intro h
      rw [List.count_cons] at h
      rcases eq_or_ne a g with rfl | hag
      · rw [spanStart_cons_self]
        exact Nat.succ_le_succ (ih j (by simp at h; omega))
      · rw [spanStart_cons_of_ne hag]
        exact Nat.succ_le_succ (ih (j + 1) (by simp [hag] at h; omega))

/-- The count over a prefix is monotone in the prefix. -/
theorem count_take_mono (g : α) {l : List α} {s t : ℕ} (h : s ≤ t) :
    (l.take s).count g ≤ (l.take t).count g :=
  (List.take_sublist_take_left h).count_le g

/-- **`spanStart` is pinned down by two conditions**: the count is right at `t`, and wrong at
every earlier position. -/
theorem spanStart_eq_of_count (g : α) {l : List α} {j t : ℕ}
    (ht : (l.take t).count g = j) (hprev : ∀ s < t, (l.take s).count g ≠ j) :
    spanStart g j l = t := by
  have hjle : j ≤ l.count g := ht ▸ List.Sublist.count_le g (List.take_sublist t l)
  refine le_antisymm (spanStart_le_of_count g j t l ht) ?_
  by_contra hcon
  exact hprev _ (by omega) (countUpTo_take_spanStart g j l hjle)

end SpanStart

/-! ### Replacing a stretch of a word

Both moves of this section — sliding two crossings at non-adjacent levels past one another, and
the braid move — replace a short stretch of the word by another of the same length whose product
is the same. That is one construction, done here once. -/

section Splice

variable {α : Type*}

/-- A list splits at `p` and at `p + k`. -/
theorem eq_take_append_middle {l : List α} {p k : ℕ} :
    l = l.take p ++ ((l.drop p).take k ++ l.drop (p + k)) := by
  conv_lhs => rw [← List.take_append_drop p l]
  congr 1
  conv_lhs => rw [← List.take_append_drop k (l.drop p)]
  rw [List.drop_drop]

/-- Splicing in a stretch of the same length does not change the length. -/
theorem length_spliceWord {l new : List α} {p : ℕ} (h : p + new.length ≤ l.length) :
    (spliceWord l p new).length = l.length := by
  simp only [spliceWord, List.length_append, List.length_take, List.length_drop]
  omega

/-- Inside the spliced stretch the entries are the new ones. Stated with `getElem?`, which is
total, so that no index proof has to be transported across the unfolding of `spliceWord`. -/
theorem getElem?_spliceWord_mid {l new : List α} {p i : ℕ} (hp : p ≤ l.length)
    (hi : i < new.length) : (spliceWord l p new)[p + i]? = new[i]? := by
  have hlen : (l.take p).length = p := by rw [List.length_take]; omega
  rw [spliceWord, List.getElem?_append_left (by rw [List.length_append, hlen]; omega),
    List.getElem?_append_right (by omega), hlen]
  congr 1
  omega

/-- Before the spliced stretch the entries are the old ones. -/
theorem getElem?_spliceWord_left {l new : List α} {p i : ℕ} (hp : p ≤ l.length) (h : i < p) :
    (spliceWord l p new)[i]? = l[i]? := by
  have hlen : (l.take p).length = p := by rw [List.length_take]; omega
  rw [spliceWord, List.getElem?_append_left (by rw [List.length_append]; omega),
    List.getElem?_append_left (by omega), List.getElem?_take_of_lt h]

/-- After the spliced stretch the entries are the old ones. -/
theorem getElem?_spliceWord_right {l new : List α} {p i : ℕ} (hp : p ≤ l.length)
    (h : p + new.length ≤ i) : (spliceWord l p new)[i]? = l[i]? := by
  have hlen : ((l.take p) ++ new).length = p + new.length := by
    rw [List.length_append, List.length_take]; omega
  rw [spliceWord, List.getElem?_append_right (by omega), hlen, List.getElem?_drop]
  congr 1
  omega

/-- Splicing in a stretch with the same product does not change the product. -/
theorem prod_map_spliceWord {M : Type*} [Monoid M] (f : α → M) {l new : List α} {p : ℕ}
    (hprod : (new.map f).prod = (((l.drop p).take new.length).map f).prod) :
    ((spliceWord l p new).map f).prod = (l.map f).prod := by
  rw [spliceWord]
  conv_rhs => rw [eq_take_append_middle (l := l) (p := p) (k := new.length)]
  simp only [List.map_append, List.prod_append, hprod, mul_assoc]

end Splice

variable {n : ℕ}

/-- The lower of the two levels a crossing exchanges becomes the upper. -/
@[simp]
theorem gapSwap_castSucc (g : Fin (n + 1)) : gapSwap g g.castSucc = g.succ := by
  simp [gapSwap]

/-- The upper of the two levels a crossing exchanges becomes the lower. -/
@[simp]
theorem gapSwap_succ (g : Fin (n + 1)) : gapSwap g g.succ = g.castSucc := by
  simp [gapSwap]

/-- A crossing leaves every other level alone. -/
theorem gapSwap_of_ne (g : Fin (n + 1)) {x : Fin (n + 2)} (h1 : x ≠ g.castSucc)
    (h2 : x ≠ g.succ) : gapSwap g x = x :=
  Equiv.swap_apply_of_ne_of_ne h1 h2

/-- The value of a swapped level in closed form. Having it turns every comparison of levels
across a crossing into arithmetic, which is what makes the order lemmas below routine. -/
theorem gapSwap_val (g : Fin (n + 1)) (z : Fin (n + 2)) :
    ((gapSwap g z : Fin (n + 2)) : ℕ) =
      if (z : ℕ) = (g : ℕ) then (g : ℕ) + 1
      else if (z : ℕ) = (g : ℕ) + 1 then (g : ℕ) else (z : ℕ) := by
  rw [gapSwap, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- **An adjacent transposition reverses the order of exactly one pair of levels.** Comparing
two levels is unaffected unless they are precisely the two levels being exchanged — which is
where the adjacency of `g.castSucc` and `g.succ` is used, since no level lies between them. -/
theorem gapSwap_lt_iff {g : Fin (n + 1)} {x y : Fin (n + 2)}
    (h1 : ¬((x : ℕ) = (g : ℕ) ∧ (y : ℕ) = (g : ℕ) + 1))
    (h2 : ¬((x : ℕ) = (g : ℕ) + 1 ∧ (y : ℕ) = (g : ℕ))) :
    (gapSwap g x < gapSwap g y ↔ x < y) := by
  simp only [Fin.lt_def, gapSwap_val]
  split_ifs <;> omega

/-- **Crossings at non-adjacent gaps commute.** Adjacent transpositions at gaps `g` and `h` with
`|g - h| > 1` commute. -/
theorem gapSwap_comm {g h : Fin (n + 1)}
    (hgh : (g : ℕ) + 1 < (h : ℕ) ∨ (h : ℕ) + 1 < (g : ℕ)) :
    gapSwap g * gapSwap h = gapSwap h * gapSwap g := by
  ext z
  simp only [Equiv.Perm.mul_apply, gapSwap_val]
  split_ifs <;> omega

/-- **The braid relation at adjacent gaps.** For gaps `g` and `h = g + 1`, the adjacent
transpositions satisfy `s_g s_h s_g = s_h s_g s_h`; both sides are the transposition of the two
outer levels. -/
theorem gapSwap_braid {g h : Fin (n + 1)} (hgh : (g : ℕ) + 1 = (h : ℕ)) :
    gapSwap g * gapSwap h * gapSwap g = gapSwap h * gapSwap g * gapSwap h := by
  have hb : g.succ = h.castSucc := Fin.ext (by simpa using hgh)
  have hca : (h.succ : Fin (n + 2)) ≠ g.castSucc := by
    simp only [Ne, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  have hcb : (h.succ : Fin (n + 2)) ≠ g.succ := by
    simp only [Ne, Fin.ext_iff, Fin.val_succ]
    omega
  have hig : (gapSwap g)⁻¹ = gapSwap g := Equiv.swap_inv _ _
  have hih : (gapSwap h)⁻¹ = gapSwap h := Equiv.swap_inv _ _
  have hL : gapSwap g * gapSwap h * gapSwap g = Equiv.swap g.castSucc h.succ := by
    rw [gapSwap.eq_1 h]
    nth_rewrite 2 [← hig]
    rw [← Equiv.swap_apply_apply, ← hb, gapSwap_succ, gapSwap_of_ne _ hca hcb]
  have hR : gapSwap h * gapSwap g * gapSwap h = Equiv.swap g.castSucc h.succ := by
    rw [gapSwap.eq_1 g]
    nth_rewrite 2 [← hih]
    rw [← Equiv.swap_apply_apply, hb, gapSwap_castSucc,
      gapSwap_of_ne _ (hb ▸ Fin.castSucc_lt_succ.ne) hca.symm]
  rw [hL, hR]

end ClusterAlgebras
