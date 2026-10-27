/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.Defs

/-!
# Mutation at a set of pairwise unlinked indices

Let `B = (b_{ij})` be an `m × n` integer matrix and `K` a set of columns with `b_{kk'} = 0` for
all `k, k' ∈ K`. Mutating `B` along the increasing sequence `s_K` of `K` negates every row and
column indexed by `K`, and adds to every other entry the corrections of all the directions of
`K` at once:
`μ_{s_K}(B)_{ij} = -b_{ij}` if `i ∈ K` or `j ∈ K`, and
`μ_{s_K}(B)_{ij} = b_{ij} + ∑_{k ∈ K} c(b_{ik}, b_{kj})` otherwise,
where `c` is the mutation correction. In particular the result does not depend on the order in
which the directions of `K` are taken. This is the computation underlying FWZ's Lemma 4.4.5,
that mutation at an orbit commutes with folding.

## Main results

* `ClusterAlgebras.matrixMutation_apply_of_ne_eq_mutationCorrection`: off row and column `k`,
  `μ_k(B)_{ij} = b_{ij} + c(b_{ik}, b_{kj})`.
* `ClusterAlgebras.increasingSeq_insert_of_forall_lt`: `s_{K ∪ {a}}` is `s_K` followed by `a`
  when `a` exceeds every element of `K`.
* `ClusterAlgebras.matrixMutationList_increasingSeq_apply`: the entries of `μ_{s_K}(B)`.

The file also records the values of the correction `c(x, y)` according to the signs of `x` and
`y` (`ClusterAlgebras.mutationCorrection_of_nonneg` and its siblings).

## Implementation notes

* Indices are `Fin m`, and the row carrying the column `k : Fin n` is `Fin.castLE hmn k`. The
  condition `i ∈ K` on a row index therefore reads `∃ k ∈ K, i = Fin.castLE hmn k`.

* The proof is by induction on `|K|`, run as `Finset.induction_on_max`: the largest element `a`
  of `K` is the last direction of `s_K`, and the first `|K| - 1` mutations leave row and column
  `a` untouched because `b_{ka} = b_{ak} = 0` for `k ∈ K`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### The mutation correction -/

/-- `c(0, y) = 0`. -/
@[simp]
theorem mutationCorrection_zero_left (y : ℤ) : mutationCorrection 0 y = 0 := by
  simp [mutationCorrection]

/-- `c(x, 0) = 0`. -/
@[simp]
theorem mutationCorrection_zero_right (x : ℤ) : mutationCorrection x 0 = 0 := by
  simp [mutationCorrection]

/-- The mutation correction is symmetric: `c(x, y) = c(y, x)`. -/
theorem mutationCorrection_comm (x y : ℤ) : mutationCorrection x y = mutationCorrection y x := by
  unfold mutationCorrection
  split_ifs <;> first | ring1 | (exfalso; omega)

/-- `c(x, y) = xy` when `x, y ≥ 0`. -/
theorem mutationCorrection_of_nonneg {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    mutationCorrection x y = x * y := by
  unfold mutationCorrection
  split_ifs with h₁ h₂
  · rfl
  · omega
  · rcases (by omega : x = 0 ∨ y = 0) with rfl | rfl <;> simp

/-- `c(x, y) = -(xy)` when `x, y ≤ 0`. -/
theorem mutationCorrection_of_nonpos {x y : ℤ} (hx : x ≤ 0) (hy : y ≤ 0) :
    mutationCorrection x y = -(x * y) := by
  unfold mutationCorrection
  split_ifs with h₁ h₂
  · omega
  · rfl
  · rcases (by omega : x = 0 ∨ y = 0) with rfl | rfl <;> simp

/-- `c(x, y) = 0` when `x` and `y` have weakly opposite signs, that is `xy ≤ 0`. -/
theorem mutationCorrection_of_mul_nonpos {x y : ℤ} (h : x * y ≤ 0) :
    mutationCorrection x y = 0 := by
  unfold mutationCorrection
  split_ifs with h₁ h₂
  · exact absurd h (mul_pos h₁.1 h₁.2).not_ge
  · exact absurd h (mul_pos_of_neg_of_neg h₂.1 h₂.2).not_ge
  · rfl

/-- `c(x, y) = 0` when `x ≥ 0 ≥ y`. -/
theorem mutationCorrection_of_nonneg_of_nonpos {x y : ℤ} (hx : 0 ≤ x) (hy : y ≤ 0) :
    mutationCorrection x y = 0 :=
  mutationCorrection_of_mul_nonpos (mul_nonpos_of_nonneg_of_nonpos hx hy)

/-- `c(x, y) = 0` when `x ≤ 0 ≤ y`. -/
theorem mutationCorrection_of_nonpos_of_nonneg {x y : ℤ} (hx : x ≤ 0) (hy : 0 ≤ y) :
    mutationCorrection x y = 0 :=
  mutationCorrection_of_mul_nonpos (mul_nonpos_of_nonpos_of_nonneg hx hy)

/-- Negating both arguments negates the correction: `c(-x, -y) = -c(x, y)`. -/
theorem mutationCorrection_neg_neg (x y : ℤ) :
    mutationCorrection (-x) (-y) = -mutationCorrection x y := by
  unfold mutationCorrection
  split_ifs <;> first | ring1 | (exfalso; omega)

/-- The correction in the closed form of `ClusterAlgebras.matrixMutation_apply_of_ne_eq_max`:
`c(x, y) = [x]₊[y]₊ - [-x]₊[-y]₊`. -/
theorem mutationCorrection_eq_max (x y : ℤ) :
    mutationCorrection x y = max 0 x * max 0 y - max 0 (-x) * max 0 (-y) := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [mutationCorrection_of_nonneg hx hy, max_eq_right hx, max_eq_right hy,
      max_eq_left (neg_nonpos.2 hx)]
    ring
  · rw [mutationCorrection_of_nonneg_of_nonpos hx hy, max_eq_left hy,
      max_eq_left (neg_nonpos.2 hx)]
    ring
  · rw [mutationCorrection_of_nonpos_of_nonneg hx hy, max_eq_left hx,
      max_eq_left (neg_nonpos.2 hy)]
    ring
  · rw [mutationCorrection_of_nonpos hx hy, max_eq_left hx, max_eq_left hy,
      max_eq_right (neg_nonneg.2 hx), max_eq_right (neg_nonneg.2 hy)]
    ring

variable {m n : ℕ}

/-- Off row and column `k`, mutation adds the correction:
`μ_k(B)_{ij} = b_{ij} + c(b_{ik}, b_{kj})` for `i ≠ k` and `j ≠ k`. -/
theorem matrixMutation_apply_of_ne_eq_mutationCorrection (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) {i : Fin m} {j : Fin n}
    (hi : i ≠ Fin.castLE hmn k) (hj : j ≠ k) :
    matrixMutation hmn B k i j = B i j + mutationCorrection (B i k) (B (Fin.castLE hmn k) j) := by
  rw [matrixMutation_apply_of_ne hmn B k hi hj, mutationCorrection]
  split_ifs <;> ring

/-! ### The increasing sequence of a set -/

/-- The increasing sequence of `K ∪ {a}`, for `a` larger than every element of `K`, is that of
`K` followed by `a`. -/
theorem increasingSeq_insert_of_forall_lt {K : Finset (Fin n)} {a : Fin n}
    (h : ∀ x ∈ K, x < a) : increasingSeq (insert a K) = increasingSeq K ++ [a] := by
  unfold increasingSeq
  have hnd : (K.sort (· ≤ ·) ++ [a]).Nodup := by
    refine List.nodup_append.2 ⟨Finset.sort_nodup _ _, List.nodup_singleton a, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact (h x ((Finset.mem_sort _).1 hx)).ne
  rw [show insert a K = (K.sort (· ≤ ·) ++ [a]).toFinset by ext; simp]
  refine (List.toFinset_sort _ hnd).2 (List.pairwise_append.2 ⟨Finset.pairwise_sort _ _,
    List.pairwise_singleton _ a, ?_⟩)
  intro x hx y hy
  rw [List.mem_singleton] at hy
  subst hy
  exact (h x ((Finset.mem_sort _).1 hx)).le

/-! ### Mutation along the increasing sequence of a set -/

variable {hmn : n ≤ m} {B : Matrix (Fin m) (Fin n) ℤ}

/-- **Mutation at a set of non-interacting indices.** If `b_{kk'} = 0` for all
`k, k' ∈ K`, then `μ_{s_K}(B)_{ij} = -b_{ij}` when `i ∈ K` or `j ∈ K`, and
`μ_{s_K}(B)_{ij} = b_{ij} + ∑_{k ∈ K} c(b_{ik}, b_{kj})` otherwise. -/
@[cluster_algebras "lem_set_mutation_formula"]
theorem matrixMutationList_increasingSeq_apply {K : Finset (Fin n)}
    (hK : ∀ k ∈ K, ∀ k' ∈ K, B (Fin.castLE hmn k) k' = 0) (i : Fin m) (j : Fin n) :
    matrixMutationList hmn B (increasingSeq K) i j =
      if (∃ k ∈ K, i = Fin.castLE hmn k) ∨ j ∈ K then -B i j
      else B i j + ∑ k ∈ K, mutationCorrection (B i k) (B (Fin.castLE hmn k) j) := by
  induction K using Finset.induction_on_max generalizing i j with
  | empty => simp [increasingSeq]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hK' : ∀ k ∈ s, ∀ k' ∈ s, B (Fin.castLE hmn k) k' = 0 := fun k hk k' hk' =>
      hK k (Finset.mem_insert_of_mem hk) k' (Finset.mem_insert_of_mem hk')
    have hBka : ∀ k ∈ s, B (Fin.castLE hmn k) a = 0 := fun k hk =>
      hK k (Finset.mem_insert_of_mem hk) a (Finset.mem_insert_self a s)
    have hBak : ∀ k ∈ s, B (Fin.castLE hmn a) k = 0 := fun k hk =>
      hK a (Finset.mem_insert_self a s) k (Finset.mem_insert_of_mem hk)
    specialize ih hK'
    set C := matrixMutationList hmn B (increasingSeq s) with hC
    have hcol : ∀ i, C i a = B i a := by
      intro i
      rw [ih]
      split_ifs with h
      · rcases h with ⟨k, hk, rfl⟩ | h
        · rw [hBka k hk, neg_zero]
        · exact absurd h has
      · rw [Finset.sum_eq_zero fun k hk => by rw [hBka k hk, mutationCorrection_zero_right],
          add_zero]
    have hrow : ∀ j, C (Fin.castLE hmn a) j = B (Fin.castLE hmn a) j := by
      intro j
      rw [ih]
      split_ifs with h
      · rcases h with ⟨k, hk, hak⟩ | h
        · exact absurd (Fin.castLE_injective hmn hak ▸ hk) has
        · rw [hBak j h, neg_zero]
      · rw [Finset.sum_eq_zero fun k hk => by rw [hBak k hk, mutationCorrection_zero_left],
          add_zero]
    rw [increasingSeq_insert_of_forall_lt ha, matrixMutationList_append,
      matrixMutationList_singleton, ← hC]
    by_cases hia : i = Fin.castLE hmn a ∨ j = a
    · rw [matrixMutation_apply_of_eq hmn C a hia, if_pos]
      · rcases hia with rfl | rfl
        · rw [hrow]
        · rw [hcol]
      · rcases hia with rfl | rfl
        · exact Or.inl ⟨a, Finset.mem_insert_self a s, rfl⟩
        · exact Or.inr (Finset.mem_insert_self _ s)
    · obtain ⟨hia, hja⟩ := not_or.1 hia
      rw [matrixMutation_apply_of_ne_eq_mutationCorrection hmn C a hia hja, hcol, hrow, ih i j]
      by_cases hij : (∃ k ∈ s, i = Fin.castLE hmn k) ∨ j ∈ s
      · rw [if_pos hij, if_pos (hij.imp (fun ⟨k, hk, h⟩ => ⟨k, Finset.mem_insert_of_mem hk, h⟩)
          Finset.mem_insert_of_mem)]
        rcases hij with ⟨k, hk, rfl⟩ | hj
        · rw [hBka k hk, mutationCorrection_zero_left, add_zero]
        · rw [hBak j hj, mutationCorrection_zero_right, add_zero]
      · rw [if_neg hij, if_neg, Finset.sum_insert has]
        · ring
        · rintro (⟨k, hk, hik⟩ | hj)
          · rcases Finset.mem_insert.1 hk with rfl | hk
            · exact hia hik
            · exact hij (Or.inl ⟨k, hk, hik⟩)
          · rcases Finset.mem_insert.1 hj with rfl | hj
            · exact hja rfl
            · exact hij (Or.inr hj)

/-- Column `j ∈ K` of `μ_{s_K}(B)` is column `j` of `B`, negated. -/
theorem matrixMutationList_increasingSeq_apply_of_mem_right {K : Finset (Fin n)}
    (hK : ∀ k ∈ K, ∀ k' ∈ K, B (Fin.castLE hmn k) k' = 0) (i : Fin m) {j : Fin n}
    (hj : j ∈ K) : matrixMutationList hmn B (increasingSeq K) i j = -B i j := by
  rw [matrixMutationList_increasingSeq_apply hK, if_pos (Or.inr hj)]

/-- Row `k ∈ K` of `μ_{s_K}(B)` is row `k` of `B`, negated. -/
theorem matrixMutationList_increasingSeq_apply_of_mem_left {K : Finset (Fin n)}
    (hK : ∀ k ∈ K, ∀ k' ∈ K, B (Fin.castLE hmn k) k' = 0) {k : Fin n} (hk : k ∈ K)
    (j : Fin n) :
    matrixMutationList hmn B (increasingSeq K) (Fin.castLE hmn k) j =
      -B (Fin.castLE hmn k) j := by
  rw [matrixMutationList_increasingSeq_apply hK, if_pos (Or.inl ⟨k, hk, rfl⟩)]

/-- Off the rows and columns indexed by `K`, `μ_{s_K}(B)` adds the corrections of all the
directions of `K`. -/
theorem matrixMutationList_increasingSeq_apply_of_notMem {K : Finset (Fin n)}
    (hK : ∀ k ∈ K, ∀ k' ∈ K, B (Fin.castLE hmn k) k' = 0) {i : Fin m} {j : Fin n}
    (hi : ∀ k ∈ K, i ≠ Fin.castLE hmn k) (hj : j ∉ K) :
    matrixMutationList hmn B (increasingSeq K) i j =
      B i j + ∑ k ∈ K, mutationCorrection (B i k) (B (Fin.castLE hmn k) j) := by
  rw [matrixMutationList_increasingSeq_apply hK, if_neg]
  rintro (⟨k, hk, hik⟩ | h)
  exacts [hi k hk hik, hj h]

end ClusterAlgebras
