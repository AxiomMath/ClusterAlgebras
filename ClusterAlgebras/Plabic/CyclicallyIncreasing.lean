/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Sort

/-!
# Cyclically increasing sequences

A finite sequence `(c₁, …, c_m)`, `m ≥ 1`, is *cyclically increasing* if one of its rotations
`(c_s, …, c_m, c₁, …, c_{s-1})` is strictly increasing. Such a sequence has pairwise distinct
entries, and every rotation of it is again cyclically increasing.

Putting `c_{m+1} = c₁`, the pairs `(c_k, c_{k+1})`, `k ∈ [1, m]`, are the pairs of cyclically
consecutive entries. A sequence is cyclically increasing if and only if exactly one of these
pairs is a *weak descent*, `c_k ≥ c_{k+1}`. Two consequences: a nonempty subsequence of a
rotation of a cyclically increasing sequence is cyclically increasing, and if
`(α, A₁, …, A_k, β)` and `(β, B₁, …, B_l, α)` are cyclically increasing then so is
`(α, A₁, …, A_k, β, B₁, …, B_l)`.

## Main definitions

* `ClusterAlgebras.CyclicallyIncreasing`: a cyclically increasing sequence.
* `ClusterAlgebras.cyclicPairs`: the list of pairs of cyclically consecutive entries.

## Main results

* `ClusterAlgebras.cyclicallyIncreasing_iff_existsUnique_le`: a sequence is cyclically increasing
  if and only if it has exactly one cyclic weak descent.
* `ClusterAlgebras.CyclicallyIncreasing.ofFn_getElem_rotate`: subsequences of rotations of a
  cyclically increasing sequence are cyclically increasing; its sublist form is
  `ClusterAlgebras.CyclicallyIncreasing.of_sublist_rotate`.
* `ClusterAlgebras.CyclicallyIncreasing.merge`: merging two cyclically increasing sequences.

## Implementation notes

* A finite sequence is a `List`, and positions are `0`-based: the entry `c_k` above is `c[k-1]`,
  and the rotation starting at `c_s` is `c.rotate (s - 1)`. The entries lie in an arbitrary
  preorder (a linear order for the statements about descents) rather than in `ℤ`.
* The condition `m ≥ 1` is built in: the empty list is not cyclically increasing, since it has
  no rotation index `s < 0`.
* The number of cyclic weak descents is `(cyclicPairs c).countP fun p => p.2 ≤ p.1`, where
  `cyclicPairs c = c.zip (c.rotate 1)`. It is invariant under rotation, since the cyclic pairs of a
  rotation are the rotation of the cyclic pairs.
-/

@[expose] public section

namespace ClusterAlgebras

open List

variable {α : Type*}

section Preorder

variable [Preorder α]

/-- A finite sequence `c` is *cyclically increasing* if some rotation `c.rotate s`, `s < c.length`,
is strictly increasing. In particular the empty list is not cyclically increasing. -/
@[cluster_algebras "def_cyclically_increasing"]
def CyclicallyIncreasing (c : List α) : Prop :=
  ∃ s < c.length, (c.rotate s).SortedLT

/-- A list is cyclically increasing if and only if it is nonempty and some rotation of it, by any
amount, is strictly increasing. -/
theorem cyclicallyIncreasing_iff_exists_rotate {c : List α} :
    CyclicallyIncreasing c ↔ c ≠ [] ∧ ∃ s, (c.rotate s).SortedLT := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨ne_nil_of_length_pos (by omega), s, h⟩
  · rintro ⟨hc, s, h⟩
    refine ⟨s % c.length, Nat.mod_lt _ (length_pos_iff.2 hc), ?_⟩
    rwa [rotate_mod]

/-- A cyclically increasing list is nonempty. -/
theorem CyclicallyIncreasing.ne_nil {c : List α} (h : CyclicallyIncreasing c) : c ≠ [] :=
  (cyclicallyIncreasing_iff_exists_rotate.1 h).1

/-- The empty list is not cyclically increasing. -/
@[simp]
theorem not_cyclicallyIncreasing_nil : ¬ CyclicallyIncreasing ([] : List α) :=
  fun h => h.ne_nil rfl

/-- A one-element list is cyclically increasing. -/
@[simp]
theorem cyclicallyIncreasing_singleton (a : α) : CyclicallyIncreasing [a] :=
  ⟨0, by simp, by simp [sortedLT_iff_pairwise]⟩

/-- A list is cyclically increasing if and only if it is nonempty and is a rotation of a strictly
increasing list. -/
theorem cyclicallyIncreasing_iff_isRotated {c : List α} :
    CyclicallyIncreasing c ↔ c ≠ [] ∧ ∃ l, c ~r l ∧ l.SortedLT := by
  rw [cyclicallyIncreasing_iff_exists_rotate]
  constructor
  · rintro ⟨hc, s, h⟩
    exact ⟨hc, _, ⟨s, rfl⟩, h⟩
  · rintro ⟨hc, l, ⟨s, rfl⟩, h⟩
    exact ⟨hc, s, h⟩

/-- A rotation of a cyclically increasing list is cyclically increasing. -/
theorem CyclicallyIncreasing.of_isRotated {c c' : List α} (h : CyclicallyIncreasing c)
    (hc : c ~r c') : CyclicallyIncreasing c' := by
  obtain ⟨hne, l, hl, hs⟩ := cyclicallyIncreasing_iff_isRotated.1 h
  refine cyclicallyIncreasing_iff_isRotated.2 ⟨?_, l, hc.symm.trans hl, hs⟩
  rintro rfl
  exact hne (isRotated_nil_iff.1 hc)

/-- Every rotation `c.rotate n` of a cyclically increasing list `c` is cyclically increasing. -/
theorem CyclicallyIncreasing.rotate {c : List α} (h : CyclicallyIncreasing c) (n : ℕ) :
    CyclicallyIncreasing (c.rotate n) :=
  h.of_isRotated ⟨n, rfl⟩

/-- A rotation `c.rotate n` is cyclically increasing if and only if `c` is. -/
@[simp]
theorem cyclicallyIncreasing_rotate {c : List α} {n : ℕ} :
    CyclicallyIncreasing (c.rotate n) ↔ CyclicallyIncreasing c :=
  ⟨fun h => h.of_isRotated (IsRotated.symm ⟨n, rfl⟩), fun h => h.rotate n⟩

/-- A cyclically increasing list has pairwise distinct entries. -/
theorem CyclicallyIncreasing.nodup {c : List α} (h : CyclicallyIncreasing c) : c.Nodup := by
  obtain ⟨s, -, h⟩ := h
  exact nodup_rotate.1 h.pairwise.nodup

/-- A nonempty sublist of a cyclically increasing list is cyclically increasing. -/
theorem CyclicallyIncreasing.of_sublist {c l : List α} (hc : CyclicallyIncreasing c)
    (hl : l <+ c) (hne : l ≠ []) : CyclicallyIncreasing l := by
  obtain ⟨s, hs, h⟩ := hc
  rw [rotate_eq_drop_append_take hs.le] at h
  rw [← take_append_drop s c] at hl
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := sublist_append_iff.1 hl
  refine cyclicallyIncreasing_iff_exists_rotate.2 ⟨hne, l₁.length, ?_⟩
  rw [rotate_append_length_eq]
  exact (h.pairwise.sublist (h₂.append h₁)).sortedLT

/-- A nonempty sublist of a rotation of a cyclically increasing list is cyclically increasing. -/
theorem CyclicallyIncreasing.of_sublist_rotate {c l : List α} (hc : CyclicallyIncreasing c)
    (s : ℕ) (hl : l <+ c.rotate s) (hne : l ≠ []) : CyclicallyIncreasing l :=
  (hc.rotate s).of_sublist hl hne

/-- **Subsequences of rotations.** Let `c` be cyclically increasing, let `c' = c.rotate s` be a
rotation of it, and let `k₀ < k₁ < ⋯ < k_{n-1}` be `n ≥ 1` positions of `c'`. Then
`(c'[k₀], …, c'[k_{n-1}])` is cyclically increasing. Any `s` is allowed. -/
@[cluster_algebras "lem_cyclically_increasing_sub"]
theorem CyclicallyIncreasing.ofFn_getElem_rotate {c : List α} (hc : CyclicallyIncreasing c)
    (s : ℕ) {n : ℕ} (hn : 0 < n) (k : Fin n → Fin c.length) (hk : StrictMono k) :
    CyclicallyIncreasing (List.ofFn fun j => (c.rotate s)[(k j : ℕ)]'(by simp)) := by
  refine hc.of_sublist_rotate s ?_ ?_
  · rw [sublist_iff_exists_fin_orderEmbedding_get_eq]
    refine ⟨(Fin.castOrderIso length_ofFn).toOrderEmbedding.trans
      ((OrderEmbedding.ofStrictMono k hk).trans
        (Fin.castOrderIso (length_rotate c s).symm).toOrderEmbedding), fun i => ?_⟩
    simp
    rfl
  · simp
    omega

end Preorder

/-! ### Cyclic weak descents -/

/-- The pairs `(c[k], c[(k + 1) % c.length])` of cyclically consecutive entries of `c`, in
order. -/
def cyclicPairs (c : List α) : List (α × α) :=
  c.zip (c.rotate 1)

/-- A list has as many cyclic pairs as entries. -/
@[simp]
theorem length_cyclicPairs (c : List α) : (cyclicPairs c).length = c.length := by
  simp [cyclicPairs]

/-- The empty list has no cyclic pairs. -/
@[simp]
theorem cyclicPairs_nil : cyclicPairs ([] : List α) = [] := rfl

/-- The only cyclic pair of a one-element list `[a]` is `(a, a)`. -/
@[simp]
theorem cyclicPairs_singleton (a : α) : cyclicPairs [a] = [(a, a)] := by
  simp [cyclicPairs]

/-- The cyclic pairs of `a :: t` are the pairs of consecutive entries of `a :: t ++ [a]`. -/
theorem cyclicPairs_cons (a : α) (t : List α) :
    cyclicPairs (a :: t) = (a :: t).zip (t ++ [a]) := by
  simp [cyclicPairs, rotate_cons_succ]

/-- The `k`-th cyclic pair of `c` is `(c[k], c[(k + 1) % c.length])`. -/
theorem cyclicPairs_eq_ofFn (c : List α) :
    cyclicPairs c = List.ofFn fun k : Fin c.length =>
      (c[k], c[((k : ℕ) + 1) % c.length]'(Nat.mod_lt _ k.pos)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [cyclicPairs, getElem_rotate]

/-- The cyclic pairs of a rotation are the rotation of the cyclic pairs. -/
theorem cyclicPairs_rotate (c : List α) (n : ℕ) :
    cyclicPairs (c.rotate n) = (cyclicPairs c).rotate n := by
  unfold cyclicPairs
  rw [rotate_rotate, add_comm, ← rotate_rotate]
  exact (zipWith_rotate_distrib Prod.mk c (c.rotate 1) n (by simp)).symm

/-- The cyclic pairs of `x :: t ++ [z]` are the consecutive pairs of `x :: t ++ [z]` followed by
the closing pair `(z, x)`. -/
theorem cyclicPairs_cons_append_singleton (x z : α) (t : List α) :
    cyclicPairs (x :: t ++ [z]) = (x :: t).zip (t ++ [z]) ++ [(z, x)] := by
  rw [cons_append, cyclicPairs_cons, ← cons_append, zip_append (by simp)]
  simp

private theorem countP_ofFn {β : Type*} {n : ℕ} (f : Fin n → β) (p : β → Bool) :
    (List.ofFn f).countP p = (Finset.univ.filter fun k => p (f k)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, ih, Finset.card_filter, Finset.card_filter,
      Fin.sum_univ_succ, add_comm]

private theorem isChain_cons_iff_forall_zip {R : α → α → Prop} (a : α) (t : List α) :
    IsChain R (a :: t) ↔ ∀ p ∈ (a :: t).zip t, R p.1 p.2 := by
  induction t generalizing a with
  | nil => simp
  | cons b t ih => simp [isChain_cons_cons, ih]

section LinearOrder

variable [LinearOrder α]

private theorem sortedLT_cons_append_singleton_iff (x z : α) (t : List α) :
    (x :: t ++ [z]).SortedLT ↔
      ((x :: t).zip (t ++ [z])).countP (fun p => decide (p.2 ≤ p.1)) = 0 := by
  have hz : (x :: (t ++ [z])).zip (t ++ [z]) = (x :: t).zip (t ++ [z]) := by
    rw [← cons_append, ← append_nil (t ++ [z]), zip_append (by simp)]
    simp
  rw [sortedLT_iff_pairwise, ← isChain_iff_pairwise, cons_append, isChain_cons_iff_forall_zip, hz,
    countP_eq_zero]
  simp

private theorem countP_cyclicPairs_rotate (c : List α) (n : ℕ) :
    (cyclicPairs (c.rotate n)).countP (fun p => decide (p.2 ≤ p.1)) =
      (cyclicPairs c).countP (fun p => decide (p.2 ≤ p.1)) := by
  rw [cyclicPairs_rotate]
  exact (rotate_perm _ _).countP_eq _

/-- A cyclically increasing list has exactly one weak descent among its pairs of cyclically
consecutive entries. -/
theorem CyclicallyIncreasing.countP_cyclicPairs_eq_one {c : List α}
    (hc : CyclicallyIncreasing c) :
    (cyclicPairs c).countP (fun p => decide (p.2 ≤ p.1)) = 1 := by
  obtain ⟨s, hs, h⟩ := hc
  rw [← countP_cyclicPairs_rotate c s]
  have hL : c.rotate s ≠ [] := by
    rw [← length_pos_iff, length_rotate]
    omega
  generalize c.rotate s = L at h hL
  rcases L with _ | ⟨x, t⟩
  · exact absurd rfl hL
  rcases eq_nil_or_concat t with rfl | ⟨t', z, rfl⟩
  · simp [cyclicPairs]
  · rw [concat_eq_append, ← cons_append] at h ⊢
    rw [cyclicPairs_cons_append_singleton, countP_append,
      (sortedLT_cons_append_singleton_iff x z t').1 h]
    have hxz : x < z := rel_of_pairwise_cons h.pairwise (by simp)
    simp [hxz.le]

/-- A list with exactly one weak descent among its pairs of cyclically consecutive entries is
cyclically increasing. -/
theorem cyclicallyIncreasing_of_countP_cyclicPairs_eq_one {c : List α}
    (h : (cyclicPairs c).countP (fun p => decide (p.2 ≤ p.1)) = 1) :
    CyclicallyIncreasing c := by
  have hpos : 0 < (cyclicPairs c).countP (fun p => decide (p.2 ≤ p.1)) := by omega
  obtain ⟨p, hpmem, hp⟩ := countP_pos_iff.1 hpos
  obtain ⟨k, hk, rfl⟩ := mem_iff_getElem.1 hpmem
  have hc : c ≠ [] := by
    rintro rfl
    simp at h
  refine cyclicallyIncreasing_iff_exists_rotate.2 ⟨hc, k + 1, ?_⟩
  have hcount := (countP_cyclicPairs_rotate c (k + 1)).trans h
  have hlast : ∀ hne, decide (((cyclicPairs (c.rotate (k + 1))).getLast hne).2 ≤
      ((cyclicPairs (c.rotate (k + 1))).getLast hne).1) = true := by
    intro hne
    have hk' : (cyclicPairs c).length - 1 + (k + 1) = k + (cyclicPairs c).length := by omega
    simp only [cyclicPairs_rotate, getLast_eq_getElem, getElem_rotate, length_rotate, hk',
      Nat.add_mod_right, Nat.mod_eq_of_lt hk]
    exact hp
  generalize c.rotate (k + 1) = L at hcount hlast
  rcases L with _ | ⟨x, t⟩
  · simp at hcount
  rcases eq_nil_or_concat t with rfl | ⟨t', z, rfl⟩
  · simp [sortedLT_iff_pairwise]
  · rw [concat_eq_append, ← cons_append] at hcount hlast ⊢
    rw [sortedLT_cons_append_singleton_iff]
    simp only [cyclicPairs_cons_append_singleton, getLast_append_singleton] at hcount hlast
    have hzx := hlast (by simp)
    rw [countP_append] at hcount
    simp only [decide_eq_true_eq] at hzx
    simpa [hzx] using hcount

/-- A list is cyclically increasing if and only if exactly one of its pairs of cyclically
consecutive entries is a weak descent. -/
theorem cyclicallyIncreasing_iff_countP_cyclicPairs_eq_one {c : List α} :
    CyclicallyIncreasing c ↔ (cyclicPairs c).countP (fun p => decide (p.2 ≤ p.1)) = 1 :=
  ⟨CyclicallyIncreasing.countP_cyclicPairs_eq_one,
    cyclicallyIncreasing_of_countP_cyclicPairs_eq_one⟩

/-- **Cyclic descents.** A list `c` is cyclically increasing if and only if there is exactly one
position `k` with `c[k] ≥ c[(k + 1) % c.length]`, that is, exactly one weak descent among its pairs
of cyclically consecutive entries. -/
@[cluster_algebras "lem_cyclically_increasing_descent"]
theorem cyclicallyIncreasing_iff_existsUnique_le {c : List α} :
    CyclicallyIncreasing c ↔
      ∃! k : Fin c.length, c[((k : ℕ) + 1) % c.length]'(Nat.mod_lt _ k.pos) ≤ c[k] := by
  rw [cyclicallyIncreasing_iff_countP_cyclicPairs_eq_one, cyclicPairs_eq_ofFn, countP_ofFn,
    Fintype.existsUnique_iff_card_one]
  simp

/-- Two distinct entries, in either order, form a cyclically increasing list. -/
theorem cyclicallyIncreasing_pair {a b : α} (h : a ≠ b) : CyclicallyIncreasing [a, b] := by
  rw [cyclicallyIncreasing_iff_countP_cyclicPairs_eq_one]
  rcases h.lt_or_gt with h | h <;> simp [cyclicPairs, h.le, not_le.2 h]

/-- **Merging two cyclically increasing sequences.** If `(a, A₁, …, A_k, b)` and
`(b, B₁, …, B_l, a)` are cyclically increasing, then so is `(a, A₁, …, A_k, b, B₁, …, B_l)`. -/
@[cluster_algebras "lem_cyclically_increasing_merge"]
theorem CyclicallyIncreasing.merge {a b : α} {A B : List α}
    (hA : CyclicallyIncreasing (a :: A ++ [b])) (hB : CyclicallyIncreasing (b :: B ++ [a])) :
    CyclicallyIncreasing (a :: A ++ b :: B) := by
  have hab : a ≠ b := by
    have := hA.nodup
    simp only [cons_append, nodup_cons, mem_append, mem_singleton, not_or] at this
    exact this.1.2
  rw [cyclicallyIncreasing_iff_countP_cyclicPairs_eq_one] at hA hB ⊢
  rw [cyclicPairs_cons_append_singleton, countP_append] at hA hB
  have hsplit : cyclicPairs (a :: A ++ b :: B) =
      (a :: A).zip (A ++ [b]) ++ (b :: B).zip (B ++ [a]) := by
    rw [cons_append, cyclicPairs_cons, ← zip_append (by simp)]
    simp
  rw [hsplit, countP_append]
  rcases hab.lt_or_gt with h | h
  · have e₁ : [(b, a)].countP (fun p => decide (p.2 ≤ p.1)) = 1 := by simp [h.le]
    have e₂ : [(a, b)].countP (fun p => decide (p.2 ≤ p.1)) = 0 := by simp [not_le.2 h]
    omega
  · have e₁ : [(b, a)].countP (fun p => decide (p.2 ≤ p.1)) = 0 := by simp [not_le.2 h]
    have e₂ : [(a, b)].countP (fun p => decide (p.2 ≤ p.1)) = 1 := by simp [h.le]
    omega

end LinearOrder

end ClusterAlgebras
