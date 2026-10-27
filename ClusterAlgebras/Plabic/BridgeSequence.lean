/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.AffinePermutation
public import ClusterAlgebras.Plabic.SwapProducts

/-!
# Bridge sequences

Let `f` be an `(a, b)`-bounded affine permutation and `(i, j)` a bridge pair of `f`. Swapping the
values of `f` at the positions `i + m b` and `j + m b` for all `m`, i.e. passing to
`f ∘ s_{i,j}` for the affine transposition `s_{i,j}`, gives again an `(a, b)`-bounded affine
permutation, whose length is `ℓ(f) + 1`. Iterating, one obtains a *bridge sequence* for `f`: a
sequence of pairs `((i₁, j₁), …, (i_r, j_r))` such that `(i_t, j_t)` is a bridge pair of the
partial product `f_{t-1}` and every integer is a fixed point of `f_r` modulo `b`. This is the
algorithm by which [FWZ] factor a bounded affine permutation into bridges.

Along a bridge sequence the length grows by one at each step, and it equals `a (b - a)` exactly
for the maps equivalent to the identity modulo `b`; hence the length of a bridge sequence is
`a (b - a) - ℓ(f)`. A fixed point of a partial product in `[1, b]` lies in no later pair; in
particular bridge sequences are nested.

## Main definitions

* `ClusterAlgebras.IsBridgeSequence b f s`: `s` is a bridge sequence for `f`.

## Main results

* `ClusterAlgebras.IsBoundedAffinePerm.comp_affineTransposition`: a swap at a bridge pair stays
  bounded.
* `ClusterAlgebras.IsBoundedAffinePerm.affineLength_comp_affineTransposition`: a swap at a bridge
  pair increases the length by one.
* `ClusterAlgebras.IsBridgeSequence.isBoundedAffinePerm_swapProduct`: the partial products of a
  bridge sequence are bounded.
* `ClusterAlgebras.IsBridgeSequence.affineLength_swapProduct`: `ℓ(f_t) = ℓ(f) + t`.
* `ClusterAlgebras.IsBoundedAffinePerm.exists_isBridgeSequence`: bridge sequences exist.
* `ClusterAlgebras.IsBoundedAffinePerm.affineLength_eq_iff`: `ℓ(f) = a (b - a)` if and only if
  every integer is a fixed point modulo `b`.
* `ClusterAlgebras.IsBridgeSequence.ne_of_isFixedPointMod`: fixed points stay out of later pairs.
* `ClusterAlgebras.IsBridgeSequence.isNestedPairSequence`: bridge sequences are nested.
* `ClusterAlgebras.IsBoundedAffinePerm.length_eq_of_isBridgeSequence`: the length of a bridge
  sequence is `a (b - a) - ℓ(f)`.

## Implementation notes

* Sequences of pairs are lists `List (ℤ × ℤ)`, indexed from `0`: the pair `(i_t, j_t)`,
  `t ∈ [1, r]`, of [FWZ] is `s[t - 1]`, and it is a bridge pair of
  `swapProduct b f s (t - 1)`. The condition `1 ≤ i_t < j_t ≤ b` on the pairs is part of
  being a bridge pair.
* The length lives in `ℕ∞`; it is finite for bounded affine permutations, and for them it is the
  cardinality of the finite set of inversions `(p, q)` with `1 ≤ p ≤ b` and `q ≤ 2 b`
  (`affineLength_eq_card_filter`).
* For the length of `f ∘ s_{i,j}`, the inversions of `f ∘ s_{i,j}` in this box are carried by
  `(p, q) ↦ (s_{i,j} p, s_{i,j} q)`, a bijection of the box, onto the pairs `(p, q)` of the box
  with `f p > f q` and `s_{i,j} p < s_{i,j} q`. These differ from the inversions of `f` in the box
  only at pairs reversed by `s_{i,j}`, which are listed by `affineTransposition_lt_iff`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function

/-! ### Bridge sequences -/

/-- A **bridge sequence** for `f : ℤ → ℤ` (for `b`) is a finite sequence of pairs
`s = ((i₁, j₁), …, (i_r, j_r))` such that, with partial products `f₀ = f, …, f_r`, each
`(i_t, j_t)` is a bridge pair of `f_{t-1}` and every integer is a fixed point of `f_r` modulo `b`.
The sequence is indexed from `0`: `s[t]` is a bridge pair of `swapProduct b f s t`. Being a bridge
pair includes `1 ≤ i_t < j_t ≤ b`. The length of the sequence is `s.length`. -/
@[cluster_algebras "def_bridge_sequence"]
structure IsBridgeSequence (b : ℕ) (f : ℤ → ℤ) (s : List (ℤ × ℤ)) : Prop where
  /-- The pair `s[t]` is a bridge pair of the partial product `f_t`. -/
  isBridgePair : ∀ (t : ℕ) (ht : t < s.length), IsBridgePair b (swapProduct b f s t) s[t].1 s[t].2
  /-- Every integer is a fixed point modulo `b` of the last partial product. -/
  isFixedPointMod : ∀ n, IsFixedPointMod b (swapProduct b f s s.length) n

section BridgeSequence

variable {b : ℕ} {f : ℤ → ℤ}

/-- The empty sequence is a bridge sequence for `f` iff every integer is a fixed point of `f`
modulo `b`. -/
theorem isBridgeSequence_nil_iff : IsBridgeSequence b f [] ↔ ∀ n, IsFixedPointMod b f n :=
  ⟨fun h => by simpa using h.isFixedPointMod,
    fun h => ⟨fun t ht => absurd ht (by simp), by simpa using h⟩⟩

/-- `(p :: s)` is a bridge sequence for `f` iff `p` is a bridge pair of `f` and `s` is a bridge
sequence for `f ∘ s_p`. -/
theorem isBridgeSequence_cons_iff {p : ℤ × ℤ} {s : List (ℤ × ℤ)} :
    IsBridgeSequence b f (p :: s) ↔
      IsBridgePair b f p.1 p.2 ∧ IsBridgeSequence b (f ∘ affineTransposition b p.1 p.2) s := by
  constructor
  · intro h
    refine ⟨h.isBridgePair 0 (by simp), fun t ht => ?_, by simpa using h.isFixedPointMod⟩
    have := h.isBridgePair (t + 1) (by simpa using ht)
    rwa [swapProduct_cons_succ] at this
  · rintro ⟨hp, hs⟩
    refine ⟨fun t ht => ?_, by simpa using hs.isFixedPointMod⟩
    cases t with
    | zero => exact hp
    | succ t =>
      rw [swapProduct_cons_succ]
      exact hs.isBridgePair t (by simpa using ht)

/-- The pairs of a bridge sequence lie in `[1, b]`. -/
theorem IsBridgeSequence.mem_Icc {s : List (ℤ × ℤ)} (hs : IsBridgeSequence b f s) :
    ∀ p ∈ s, (1 ≤ p.1 ∧ p.1 ≤ b) ∧ (1 ≤ p.2 ∧ p.2 ≤ b) := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
  have h := hs.isBridgePair t ht
  have := h.one_le
  have := h.lt
  have := h.le
  omega

end BridgeSequence

/-! ### A swap at a bridge pair -/

section Swap

variable {a b : ℕ} {f : ℤ → ℤ}

/-- **A swap at a bridge pair stays bounded.** If `f` is an `(a, b)`-bounded affine permutation
and `(i, j)` a bridge pair of `f`, then `f ∘ s_{i,j}` is an `(a, b)`-bounded affine
permutation. -/
@[cluster_algebras "lem_swap_bounded"]
theorem IsBoundedAffinePerm.comp_affineTransposition (hf : IsBoundedAffinePerm a b f) {i j : ℤ}
    (h : IsBridgePair b f i j) : IsBoundedAffinePerm a b (f ∘ affineTransposition b i j) := by
  obtain ⟨hji, -, hjb'⟩ := hf.isBridgePair_values h
  have hi := h.one_le
  have hij := h.lt
  have hjb := h.le
  have hjb2 : j < i + b := by omega
  have hb : (0 : ℤ) < b := by omega
  have hinv := affineTransposition_involutive (b := b) hij hjb2
  have hlt := h.apply_lt_apply
  refine ⟨hf.bijective.comp hinv.bijective, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · simp only [Function.comp_apply, affineTransposition_add, hf.apply_add]
  · obtain ⟨x, m, hx, hx', rfl⟩ := exists_eq_add_mul_of_pos hb i n
    simp only [Function.comp_apply, affineTransposition_add_mul,
      affineTransposition_of_le_of_lt hij hjb2 hx hx', apply_add_mul_of_apply_add hf.apply_add]
    have := hf.le_apply x
    split_ifs with h1 h2 <;> subst_vars <;> omega
  · obtain ⟨x, m, hx, hx', rfl⟩ := exists_eq_add_mul_of_pos hb i n
    simp only [Function.comp_apply, affineTransposition_add_mul,
      affineTransposition_of_le_of_lt hij hjb2 hx hx', apply_add_mul_of_apply_add hf.apply_add]
    have := hf.apply_le x
    split_ifs with h1 h2 <;> subst_vars <;> omega
  · rw [← hf.sum_sub_eq, sum_congr rfl (g := fun n => f (Equiv.swap i j n) - n) (fun n hn => by
      rw [mem_Icc] at hn
      simp only [Function.comp_apply]
      rw [affineTransposition_eq_swap ⟨hi, by omega⟩ ⟨by omega, hjb⟩ hn]),
      sum_sub_distrib, sum_sub_distrib,
      Equiv.Perm.sum_comp (Equiv.swap i j) _ f (fun x hx => ?_)]
    simp only [Set.mem_setOf_eq] at hx
    simp only [coe_Icc, Set.mem_Icc]
    rcases eq_or_ne x i with rfl | hxi
    · omega
    rcases eq_or_ne x j with rfl | hxj
    · omega
    exact absurd (Equiv.swap_apply_of_ne_of_ne hxi hxj) hx

/-- The length of a map with `n ≤ f n ≤ n + b` is the number of its inversions `(p, q)` with
`1 ≤ p ≤ b` and `1 ≤ q ≤ 2 b`. -/
theorem affineLength_eq_card_filter (h₁ : ∀ n, n ≤ f n) (h₂ : ∀ n, f n ≤ n + b) :
    affineLength b f = ((Icc (1 : ℤ) b ×ˢ Icc (1 : ℤ) (2 * b)).filter
      (fun x => x.1 < x.2 ∧ f x.2 < f x.1)).card := by
  rw [affineLength, ← Set.encard_coe_eq_coe_finsetCard]
  congr 1
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, coe_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨hp1, hpb, hinv⟩
    have := hinv.lt_add h₁ h₂
    exact ⟨⟨⟨hp1, hpb⟩, by have := hinv.1; omega, by omega⟩, hinv⟩
  · rintro ⟨⟨⟨hp1, hpb⟩, -, -⟩, hinv⟩
    exact ⟨hp1, hpb, hinv⟩

/-- If `x` and `x + m b` both lie in `[1, b]`, then `m = 0`. -/
theorem eq_zero_of_add_mul_mem_Icc {m x : ℤ} (h₁ : 1 ≤ x) (h₂ : x ≤ b) (h₃ : 1 ≤ x + m * b)
    (h₄ : x + m * b ≤ b) : m = 0 := by
  have hb : (0 : ℤ) < b := by omega
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have : m * b ≤ -b := by nlinarith
    omega
  · exact hm
  · have : b ≤ m * b := by nlinarith
    omega

/-- For `i < j < i + b`, the affine transposition `s_{i,j}` maps `i` to `j`. -/
theorem affineTransposition_left {i j : ℤ} (hij : i < j) (hjb : j < i + b) :
    affineTransposition b i j i = j := by
  simpa using affineTransposition_left_add_mul (b := b) hij hjb 0

/-- For `i < j < i + b`, the affine transposition `s_{i,j}` maps `j` to `i`. -/
theorem affineTransposition_right {i j : ℤ} (hij : i < j) (hjb : j < i + b) :
    affineTransposition b i j j = i := by
  simpa using affineTransposition_right_add_mul (b := b) hij hjb 0

/-- For `i < j < i + b`, the affine transposition `s_{i,j}` fixes every `x` with `i < x < j`. -/
theorem affineTransposition_of_lt_of_lt {i j x : ℤ} (hij : i < j) (hjb : j < i + b)
    (h₁ : i < x) (h₂ : x < j) : affineTransposition b i j x = x := by
  rw [affineTransposition_of_le_of_lt hij hjb h₁.le (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- For `1 ≤ i < j ≤ b`, the affine transposition `s_{i,j}` maps `[1, b]` to itself. -/
theorem affineTransposition_mem_Icc {i j x : ℤ} (hi : 1 ≤ i) (hij : i < j) (hjb : j ≤ b)
    (h₁ : 1 ≤ x) (h₂ : x ≤ b) :
    1 ≤ affineTransposition b i j x ∧ affineTransposition b i j x ≤ b := by
  rw [affineTransposition_eq_swap ⟨hi, by omega⟩ ⟨by omega, hjb⟩ ⟨h₁, h₂⟩, Equiv.swap_apply_def]
  split_ifs <;> omega

/-- For `1 ≤ i < j ≤ b`, the affine transposition `s_{i,j}` maps `[1, 2 b]` to itself. -/
theorem affineTransposition_mem_Icc_two_mul {i j x : ℤ} (hi : 1 ≤ i) (hij : i < j)
    (hjb : j ≤ b) (h₁ : 1 ≤ x) (h₂ : x ≤ 2 * b) :
    1 ≤ affineTransposition b i j x ∧ affineTransposition b i j x ≤ 2 * b := by
  rcases le_or_gt x b with hx | hx
  · have := affineTransposition_mem_Icc hi hij hjb h₁ hx
    omega
  · have e : affineTransposition b i j x = affineTransposition b i j (x - b) + b := by
      rw [← affineTransposition_add, sub_add_cancel]
    have := affineTransposition_mem_Icc (x := x - b) hi hij hjb (by omega) (by omega)
    omega

/-- Strictly between the entries of a bridge pair of a bounded affine permutation `f`, `f` either
fixes a point or shifts it by `b`. -/
theorem IsBoundedAffinePerm.eq_or_eq_add_of_lt_of_lt (hf : IsBoundedAffinePerm a b f)
    {i j x : ℤ} (h : IsBridgePair b f i j) (h₁ : i < x) (h₂ : x < j) :
    f x = x ∨ f x = x + b :=
  (h.isFixedPointMod_of_lt_of_lt x h₁ h₂).eq_or_eq_add (hf.le_apply x) (hf.apply_le x)

/-- The inversions `(p, q)` of `f` with `1 ≤ p ≤ b`, `q ≤ 2 b` that are reversed by `s_{i,j}`, at
a bridge pair `(i, j)` of a bounded affine permutation `f`: they are `(i, x)` and `(x, j)` for
`i < x < j`, according to whether `f x = x`. -/
theorem IsBoundedAffinePerm.filter_not_lt_affineTransposition_eq
    (hf : IsBoundedAffinePerm a b f) {i j : ℤ} (h : IsBridgePair b f i j) :
    (((Icc (1 : ℤ) b ×ˢ Icc (1 : ℤ) (2 * b)).filter fun x => x.1 < x.2 ∧ f x.2 < f x.1).filter
      fun x => ¬ affineTransposition b i j x.1 < affineTransposition b i j x.2) =
      (Ioo i j).image fun x => if f x = x then (i, x) else (x, j) := by
  obtain ⟨hji, hlt, hjb'⟩ := hf.isBridgePair_values h
  have hi := h.one_le
  have hij := h.lt
  have hjb := h.le
  have hjb2 : j < i + b := by omega
  have hfix := fun x => hf.eq_or_eq_add_of_lt_of_lt h (x := x)
  ext ⟨p, q⟩
  simp only [mem_filter, mem_product, mem_Icc, mem_image, mem_Ioo]
  constructor
  · rintro ⟨⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hpq, hfpq⟩, hspq⟩
    have hspq' : affineTransposition b i j q < affineTransposition b i j p :=
      lt_of_le_of_ne (not_lt.1 hspq) (fun e => hpq.ne
        ((affineTransposition_involutive (b := b) hij hjb2).injective e).symm)
    obtain ⟨m, x, y, hix, hxy, hyj, hxy', rfl, rfl⟩ :=
      (affineTransposition_lt_iff hi hij hjb hpq).1 hspq'
    obtain rfl := eq_zero_of_add_mul_mem_Icc (x := x) (by omega) (by omega) hp1 hp2
    simp only [zero_mul, add_zero] at hfpq ⊢
    rcases eq_or_ne y j with rfl | hyj'
    · rcases eq_or_ne x i with rfl | hxi
      · omega
      refine ⟨x, ⟨by omega, hxy⟩, ?_⟩
      rcases hfix x (by omega) hxy with e | e
      · omega
      · simp only [e, if_neg (show ¬ x + b = x by omega)]
    · obtain rfl := hxy'.resolve_right hyj'
      refine ⟨y, ⟨hxy, by omega⟩, ?_⟩
      rcases hfix y hxy (by omega) with e | e
      · simp only [e, if_true]
      · omega
  · rintro ⟨x, ⟨hix, hxj⟩, e⟩
    rcases hfix x hix hxj with hx | hx
    · simp only [hx, if_true, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨⟨⟨⟨hi, by omega⟩, by omega, by omega⟩, hix, by omega⟩, ?_⟩
      rw [affineTransposition_left hij hjb2, affineTransposition_of_lt_of_lt hij hjb2 hix hxj]
      omega
    · simp only [hx, if_neg (show ¬ x + b = x by omega), Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, hxj, by omega⟩, ?_⟩
      rw [affineTransposition_right hij hjb2, affineTransposition_of_lt_of_lt hij hjb2 hix hxj]
      omega

/-- At a bridge pair `(i, j)` of a bounded affine permutation `f`, exactly `j - i - 1` of the
inversions of `f` with `1 ≤ p ≤ b`, `q ≤ 2 b` are reversed by `s_{i,j}`. -/
theorem IsBoundedAffinePerm.card_filter_not_lt_affineTransposition
    (hf : IsBoundedAffinePerm a b f) {i j : ℤ} (h : IsBridgePair b f i j) :
    (((Icc (1 : ℤ) b ×ˢ Icc (1 : ℤ) (2 * b)).filter fun x => x.1 < x.2 ∧ f x.2 < f x.1).filter
      fun x => ¬ affineTransposition b i j x.1 < affineTransposition b i j x.2).card =
      (j - i - 1).toNat := by
  rw [hf.filter_not_lt_affineTransposition_eq h, card_image_of_injOn, Int.card_Ioo]
  intro x hx y hy e
  simp only [coe_Ioo, Set.mem_Ioo] at hx hy
  dsimp only at e
  split_ifs at e <;> simp only [Prod.mk.injEq] at e <;> omega

/-- The pairs `(p, q)` with `1 ≤ p ≤ b`, `q ≤ 2 b`, `q ≤ p`, `f q < f p` and
`s_{i,j} p < s_{i,j} q`, at a bridge pair `(i, j)` of a bounded affine permutation `f`: they are
`(j, i)`, and `(j, x)` and `(x, i)` for `i < x < j`, according to whether `f x = x`. -/
theorem IsBoundedAffinePerm.filter_affineTransposition_lt_not_lt_eq
    (hf : IsBoundedAffinePerm a b f) {i j : ℤ} (h : IsBridgePair b f i j) :
    (((Icc (1 : ℤ) b ×ˢ Icc (1 : ℤ) (2 * b)).filter fun x =>
      affineTransposition b i j x.1 < affineTransposition b i j x.2 ∧ f x.2 < f x.1).filter
      fun x => ¬ x.1 < x.2) =
      insert (j, i) ((Ioo i j).image fun x => if f x = x then (j, x) else (x, i)) := by
  obtain ⟨hji, hlt, hjb'⟩ := hf.isBridgePair_values h
  have hi := h.one_le
  have hij := h.lt
  have hjb := h.le
  have hjb2 : j < i + b := by omega
  have hfix := fun x => hf.eq_or_eq_add_of_lt_of_lt h (x := x)
  ext ⟨p, q⟩
  simp only [mem_filter, mem_product, mem_Icc, mem_insert, mem_image, mem_Ioo, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hspq, hfpq⟩, hpq⟩
    have hqp : q < p := lt_of_le_of_ne (not_lt.1 hpq) (fun e => hspq.ne (by rw [e]))
    obtain ⟨m, x, y, hix, hxy, hyj, hxy', rfl, rfl⟩ :=
      (affineTransposition_lt_iff hi hij hjb hqp).1 hspq
    obtain rfl := eq_zero_of_add_mul_mem_Icc (x := y) (by omega) (by omega) hp1 hp2
    simp only [zero_mul, add_zero] at hfpq ⊢
    rcases eq_or_ne y j with rfl | hyj'
    · rcases eq_or_ne x i with rfl | hxi
      · exact Or.inl ⟨rfl, rfl⟩
      refine Or.inr ⟨x, ⟨by omega, hxy⟩, ?_⟩
      rcases hfix x (by omega) hxy with e | e
      · simp only [e, if_true]
      · omega
    · obtain rfl := hxy'.resolve_right hyj'
      refine Or.inr ⟨y, ⟨hxy, by omega⟩, ?_⟩
      rcases hfix y hxy (by omega) with e | e
      · omega
      · simp only [e, if_neg (show ¬ y + b = y by omega)]
  · rintro (⟨rfl, rfl⟩ | ⟨x, ⟨hix, hxj⟩, e⟩)
    · refine ⟨⟨⟨⟨by omega, hjb⟩, hi, by omega⟩, ?_, hlt⟩, by omega⟩
      rwa [affineTransposition_left hij hjb2, affineTransposition_right hij hjb2]
    rcases hfix x hix hxj with hx | hx
    · simp only [hx, if_true, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨⟨⟨⟨by omega, hjb⟩, by omega, by omega⟩, ?_, by omega⟩, by omega⟩
      rwa [affineTransposition_right hij hjb2, affineTransposition_of_lt_of_lt hij hjb2 hix hxj]
    · simp only [hx, if_neg (show ¬ x + b = x by omega), Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      refine ⟨⟨⟨⟨by omega, by omega⟩, hi, by omega⟩, ?_, by omega⟩, by omega⟩
      rwa [affineTransposition_left hij hjb2, affineTransposition_of_lt_of_lt hij hjb2 hix hxj]

/-- At a bridge pair `(i, j)` of a bounded affine permutation `f`, there are exactly `j - i`
pairs `(p, q)` with `1 ≤ p ≤ b`, `q ≤ 2 b`, `q ≤ p`, `f q < f p` and `s_{i,j} p < s_{i,j} q`. -/
theorem IsBoundedAffinePerm.card_filter_affineTransposition_lt_not_lt
    (hf : IsBoundedAffinePerm a b f) {i j : ℤ} (h : IsBridgePair b f i j) :
    (((Icc (1 : ℤ) b ×ˢ Icc (1 : ℤ) (2 * b)).filter fun x =>
      affineTransposition b i j x.1 < affineTransposition b i j x.2 ∧ f x.2 < f x.1).filter
      fun x => ¬ x.1 < x.2).card = (j - i - 1).toNat + 1 := by
  rw [hf.filter_affineTransposition_lt_not_lt_eq h, card_insert_of_notMem, card_image_of_injOn,
    Int.card_Ioo]
  · intro x hx y hy e
    simp only [coe_Ioo, Set.mem_Ioo] at hx hy
    dsimp only at e
    split_ifs at e <;> simp only [Prod.mk.injEq] at e <;> omega
  · rw [mem_image]
    rintro ⟨x, hx, e⟩
    rw [mem_Ioo] at hx
    split_ifs at e <;> simp only [Prod.mk.injEq] at e <;> omega

/-- **A swap at a bridge pair increases the length by one.** If `f` is an `(a, b)`-bounded affine
permutation and `(i, j)` a bridge pair of `f`, then `ℓ(f ∘ s_{i,j}) = ℓ(f) + 1`. -/
@[cluster_algebras "lem_swap_length"]
theorem IsBoundedAffinePerm.affineLength_comp_affineTransposition
    (hf : IsBoundedAffinePerm a b f) {i j : ℤ} (h : IsBridgePair b f i j) :
    affineLength b (f ∘ affineTransposition b i j) = affineLength b f + 1 := by
  have hg := hf.comp_affineTransposition h
  have hi := h.one_le
  have hij := h.lt
  have hjb := h.le
  have hinv := affineTransposition_involutive (b := b) hij (by omega)
  set s := affineTransposition b i j
  set B := Icc (1 : ℤ) b ×ˢ Icc (1 : ℤ) (2 * b) with hB
  rw [affineLength_eq_card_filter hg.le_apply hg.apply_le,
    affineLength_eq_card_filter hf.le_apply hf.apply_le]
  have hre : (B.filter fun x => x.1 < x.2 ∧ (f ∘ s) x.2 < (f ∘ s) x.1).card =
      (B.filter fun x => s x.1 < s x.2 ∧ f x.2 < f x.1).card := by
    refine card_bij' (fun x _ => (s x.1, s x.2)) (fun x _ => (s x.1, s x.2)) ?_ ?_ ?_ ?_
    · rintro ⟨p, q⟩ hx
      simp only [hB, mem_filter, mem_product, mem_Icc, Function.comp_apply] at hx ⊢
      obtain ⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hpq, hfpq⟩ := hx
      exact ⟨⟨affineTransposition_mem_Icc hi hij hjb hp1 hp2,
        affineTransposition_mem_Icc_two_mul hi hij hjb hq1 hq2⟩, by rwa [hinv p, hinv q], hfpq⟩
    · rintro ⟨p, q⟩ hx
      simp only [hB, mem_filter, mem_product, mem_Icc, Function.comp_apply] at hx ⊢
      obtain ⟨⟨⟨hp1, hp2⟩, hq1, hq2⟩, hpq, hfpq⟩ := hx
      exact ⟨⟨affineTransposition_mem_Icc hi hij hjb hp1 hp2,
        affineTransposition_mem_Icc_two_mul hi hij hjb hq1 hq2⟩, hpq, by rwa [hinv p, hinv q]⟩
    all_goals
      rintro ⟨p, q⟩ -
      simp [hinv p, hinv q]
  rw [hre]
  set A := B.filter fun x => x.1 < x.2 ∧ f x.2 < f x.1 with hA
  set A' := B.filter fun x => s x.1 < s x.2 ∧ f x.2 < f x.1 with hA'
  have h1 := card_filter_add_card_filter_not (s := A) (fun x => s x.1 < s x.2)
  have h2 := card_filter_add_card_filter_not (s := A') (fun x => x.1 < x.2)
  have hcommon : A.filter (fun x => s x.1 < s x.2) = A'.filter (fun x => x.1 < x.2) := by
    ext x
    simp only [hA, hA', mem_filter]
    tauto
  have e1 : (A.filter fun x => ¬ s x.1 < s x.2).card = (j - i - 1).toNat :=
    hf.card_filter_not_lt_affineTransposition h
  have e2 : (A'.filter fun x => ¬ x.1 < x.2).card = (j - i - 1).toNat + 1 :=
    hf.card_filter_affineTransposition_lt_not_lt h
  rw [e1] at h1
  rw [e2, ← hcommon] at h2
  rw [← h1, ← h2]
  push_cast
  ring

end Swap

/-! ### Length along a bridge sequence -/

section Sequence

variable {a b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- **Partial products of a bridge sequence are bounded.** If `f` is an `(a, b)`-bounded affine
permutation and `s` a bridge sequence for `f`, then every partial product `f_t`, `t ∈ ℕ`, is an
`(a, b)`-bounded affine permutation. -/
@[cluster_algebras "lem_bridge_sequence_bounded"]
theorem IsBridgeSequence.isBoundedAffinePerm_swapProduct (hs : IsBridgeSequence b f s)
    (hf : IsBoundedAffinePerm a b f) (t : ℕ) : IsBoundedAffinePerm a b (swapProduct b f s t) := by
  induction t with
  | zero => simpa using hf
  | succ t ih =>
    rcases lt_or_ge t s.length with ht | ht
    · rw [swapProduct_succ ht]
      exact ih.comp_affineTransposition (hs.isBridgePair t ht)
    · rw [swapProduct_of_length_le (by omega), ← swapProduct_of_length_le ht]
      exact ih

/-- **Length along a bridge sequence.** If `f` is an `(a, b)`-bounded affine permutation and `s` a
bridge sequence for `f` of length `r`, then `ℓ(f_t) = ℓ(f) + t` for every `t ∈ [0, r]`. -/
@[cluster_algebras "lem_bridge_sequence_length"]
theorem IsBridgeSequence.affineLength_swapProduct (hs : IsBridgeSequence b f s)
    (hf : IsBoundedAffinePerm a b f) {t : ℕ} (ht : t ≤ s.length) :
    affineLength b (swapProduct b f s t) = affineLength b f + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t < s.length := ht
    rw [swapProduct_succ ht', (hs.isBoundedAffinePerm_swapProduct hf
      t).affineLength_comp_affineTransposition (hs.isBridgePair t ht'), ih ht'.le]
    push_cast
    rw [add_assoc]

/-- **Bridge sequences exist.** Every `(a, b)`-bounded affine permutation has a bridge
sequence. -/
@[cluster_algebras "lem_bridge_sequence_exists"]
theorem IsBoundedAffinePerm.exists_isBridgeSequence (hf : IsBoundedAffinePerm a b f) :
    ∃ s, IsBridgeSequence b f s := by
  have hbound : ∀ {g : ℤ → ℤ}, IsBoundedAffinePerm a b g →
      (affineLength b g).toNat ≤ b * (2 * b) := by
    intro g hg
    rw [affineLength_eq_card_filter hg.le_apply hg.apply_le, ENat.toNat_coe]
    refine (card_filter_le _ _).trans ?_
    rw [card_product, Int.card_Icc, Int.card_Icc]
    simp only [add_sub_cancel_right, Int.toNat_natCast]
    rw [show (2 * (b : ℤ)).toNat = 2 * b by omega]
  induction hN : b * (2 * b) - (affineLength b f).toNat using Nat.strong_induction_on
      generalizing f with
  | _ N ih =>
    by_cases hfix : ∀ n, IsFixedPointMod b f n
    · exact ⟨[], isBridgeSequence_nil_iff.2 hfix⟩
    · push Not at hfix
      obtain ⟨i, j, hij⟩ := hf.exists_isBridgePair hfix
      have hg := hf.comp_affineTransposition hij
      have hlen' : (affineLength b (f ∘ affineTransposition b i j)).toNat =
          (affineLength b f).toNat + 1 := by
        rw [hf.affineLength_comp_affineTransposition hij, ENat.toNat_add
          (affineLength_ne_top (b := b) hf.le_apply hf.apply_le) ENat.one_ne_top]
        rfl
      have := hbound hg
      obtain ⟨s, hs⟩ := ih _ (by omega) hg rfl
      exact ⟨(i, j) :: s, isBridgeSequence_cons_iff.2 ⟨hij, hs⟩⟩

/-- **Maximal length.** An `(a, b)`-bounded affine permutation `f` has length `ℓ(f) = a (b - a)`
if and only if every integer is a fixed point of `f` modulo `b`. -/
@[cluster_algebras "lem_affine_length_max"]
theorem IsBoundedAffinePerm.affineLength_eq_iff (hf : IsBoundedAffinePerm a b f) :
    affineLength b f = (a * (b - a) : ℕ) ↔ ∀ n, IsFixedPointMod b f n := by
  refine ⟨fun hl => ?_, hf.affineLength_eq_of_forall_isFixedPointMod⟩
  by_contra hfix
  obtain ⟨s, hs⟩ := hf.exists_isBridgeSequence
  have hr : s ≠ [] := by
    rintro rfl
    exact hfix (isBridgeSequence_nil_iff.1 hs)
  have h1 := hs.affineLength_swapProduct hf le_rfl
  rw [(hs.isBoundedAffinePerm_swapProduct hf _).affineLength_eq_of_forall_isFixedPointMod
    hs.isFixedPointMod, hl] at h1
  have h2 : s.length ≠ 0 := by simpa using hr
  norm_cast at h1
  omega

/-- **The number of bridges.** If `f` is an `(a, b)`-bounded affine permutation and `s` a bridge
sequence for `f` of length `r`, then `r = a (b - a) - ℓ(f)`. -/
@[cluster_algebras "prop_number_of_bridges"]
theorem IsBoundedAffinePerm.length_eq_of_isBridgeSequence (hf : IsBoundedAffinePerm a b f)
    (hs : IsBridgeSequence b f s) :
    (s.length : ℕ∞) = (a * (b - a) : ℕ) - affineLength b f := by
  have h1 := hs.affineLength_swapProduct hf le_rfl
  rw [(hs.isBoundedAffinePerm_swapProduct hf _).affineLength_eq_of_forall_isFixedPointMod
    hs.isFixedPointMod] at h1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (affineLength_ne_top (b := b) hf.le_apply hf.apply_le)
  rw [← hn] at h1 ⊢
  norm_cast at h1 ⊢
  omega

end Sequence

/-! ### Fixed points and nestedness -/

section Nested

variable {b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- A fixed point `h ∈ [1, b]` of a partial product `f_t` of a bridge sequence remains a fixed
point of all later partial products. -/
theorem IsBridgeSequence.isFixedPointMod_swapProduct (hs : IsBridgeSequence b f s) {t : ℕ}
    {h : ℤ} (hh : 1 ≤ h ∧ h ≤ b) (hfix : IsFixedPointMod b (swapProduct b f s t) h) {u : ℕ}
    (hu : t ≤ u) : IsFixedPointMod b (swapProduct b f s u) h := by
  induction u, hu using Nat.le_induction with
  | base => exact hfix
  | succ u _ ih =>
    rcases lt_or_ge u s.length with hul | hul
    · have hp := hs.isBridgePair u hul
      have hi : h ≠ s[u].1 := fun e => hp.not_isFixedPointMod_left (e ▸ ih)
      have hj : h ≠ s[u].2 := fun e => hp.not_isFixedPointMod_right (e ▸ ih)
      have hmem := hs.mem_Icc _ (List.getElem_mem hul)
      rw [swapProduct_succ hul, IsFixedPointMod, Function.comp_apply,
        affineTransposition_eq_swap hmem.1 hmem.2 hh, Equiv.swap_apply_of_ne_of_ne hi hj]
      exact ih
    · rw [swapProduct_of_length_le (by omega), ← swapProduct_of_length_le hul]
      exact ih

/-- **Fixed points stay out of later pairs.** Let `s` be a bridge sequence for `f`, and let
`h ∈ [1, b]` be a fixed point modulo `b` of the partial product `f_t`. Then `h` is not an entry
of any later pair: `h ∉ {i_{t'}, j_{t'}}` for `t' ∈ [t + 1, r]`, i.e. (indexing from `0`)
`h ≠ s[u].1` and `h ≠ s[u].2` for `t ≤ u < r`. -/
@[cluster_algebras "lem_bridge_sequence_fixed_persist"]
theorem IsBridgeSequence.ne_of_isFixedPointMod (hs : IsBridgeSequence b f s) {t : ℕ} {h : ℤ}
    (hh : 1 ≤ h ∧ h ≤ b) (hfix : IsFixedPointMod b (swapProduct b f s t) h) {u : ℕ}
    (hu : u < s.length) (htu : t ≤ u) : h ≠ s[u].1 ∧ h ≠ s[u].2 := by
  have ih := hs.isFixedPointMod_swapProduct hh hfix htu
  have hp := hs.isBridgePair u hu
  exact ⟨fun e => hp.not_isFixedPointMod_left (e ▸ ih),
    fun e => hp.not_isFixedPointMod_right (e ▸ ih)⟩

/-- **Bridge sequences are nested.** -/
@[cluster_algebras "lem_bridge_sequence_nested"]
theorem IsBridgeSequence.isNestedPairSequence (hs : IsBridgeSequence b f s) :
    IsNestedPairSequence s := by
  rw [isNestedPairSequence_iff]
  intro t t' ht ht' htt' h h1 h2
  have hp := hs.isBridgePair t ht
  have := hp.one_le
  have := hp.le
  exact hs.ne_of_isFixedPointMod ⟨by omega, by omega⟩ (hp.isFixedPointMod_of_lt_of_lt h h1 h2)
    ht' htt'.le

end Nested

end ClusterAlgebras
