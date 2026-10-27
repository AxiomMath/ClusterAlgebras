/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.SetMutation
public import ClusterAlgebras.Subpattern.SeedReindex

/-!
# Seed mutation at a set of pairwise unlinked indices

Let `(x̃, B̃)` be a seed in a field `F` and `K` a set of mutable indices with `b_{kk'} = 0` for
all `k, k' ∈ K`. Mutating `(x̃, B̃)` along the increasing sequence `s_K` of `K` replaces each
`x_k`, `k ∈ K`, by `(M⁺_k(x̃, B̃) + M⁻_k(x̃, B̃)) / x_k`, computed from the *initial* seed, and
keeps every other entry of the extended cluster. So the directions of `K` are mutated
simultaneously and independently, and the order in which they are taken does not matter. The
extended exchange matrix of the result is `μ_{s_K}(B̃)`, computed in
`ClusterAlgebras.matrixMutationList_increasingSeq_apply`.

## Main results

* `ClusterAlgebras.seedMutationSeq_extCluster_of_forall_ne`: mutation along any sequence keeps
  the entries of the extended cluster at the positions not in the sequence.
* `ClusterAlgebras.seedMutationSeq_increasingSeq_extCluster_of_mem`: the entry of the mutated
  extended cluster at `k ∈ K`.
* `ClusterAlgebras.seedMutationSeq_increasingSeq_extCluster_of_notMem`: the entries at the
  positions outside `K`.

## Implementation notes

* Indices are `Fin m`, and the position carrying the mutable index `k : Fin n` is
  `Fin.castLE hmn k`, so a position `i ∉ K` is one with `∀ k ∈ K, i ≠ Fin.castLE hmn k`.

* [FWZ] assumes `x_k ≠ 0` for `k ∈ K`, so that each mutation is defined. Seed mutation is total
  here (`ClusterAlgebras.seedMutation` divides in a field, with `x / 0 = 0`), and the formula holds
  without that hypothesis, so it is dropped. The condition `b_{kk'} = 0` is not needed for the
  entries outside `K` either, and is dropped there.

* The proof is by induction on `|K|`, run as `Finset.induction_on_max`: the largest element `a`
  of `K` is the last direction of `s_K`, and the first `|K| - 1` mutations leave column `a` of
  the matrix and the entries of the cluster in the rows where that column is nonzero untouched.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n : ℕ} {hmn : n ≤ m} {F : Type*} [Field F]

/-- Mutation along a sequence `s` keeps the entry of the extended cluster at every position
that is not a direction of `s`. -/
theorem seedMutationSeq_extCluster_of_forall_ne (S : SeedData F m n) {s : List (Fin n)}
    {i : Fin m} (hi : ∀ k ∈ s, i ≠ Fin.castLE hmn k) :
    (seedMutationSeq hmn S s).extCluster i = S.extCluster i := by
  induction s generalizing S with
  | nil => rfl
  | cons k s ih =>
    rw [seedMutationSeq_cons, ih _ fun k' hk' => hi k' (List.mem_cons_of_mem k hk')]
    exact Function.update_of_ne (hi k List.mem_cons_self) _ _

/-- **Seed mutation at a set of indices, outside the set.** Mutation along the increasing
sequence `s_K` keeps the entry of the extended cluster at every position outside `K`. -/
@[cluster_algebras "lem_set_mutation_seed_formula"]
theorem seedMutationSeq_increasingSeq_extCluster_of_notMem (S : SeedData F m n)
    {K : Finset (Fin n)} {i : Fin m} (hi : ∀ k ∈ K, i ≠ Fin.castLE hmn k) :
    (seedMutationSeq hmn S (increasingSeq K)).extCluster i = S.extCluster i :=
  seedMutationSeq_extCluster_of_forall_ne S fun k hk =>
    hi k ((Finset.mem_sort _).1 hk)

/-- **Seed mutation at a set of non-interacting indices.** If `b_{kk'} = 0` for all
`k, k' ∈ K`, then mutation along the increasing sequence `s_K` puts
`(M⁺_k(x̃, B̃) + M⁻_k(x̃, B̃)) / x_k` at each position `k ∈ K`. -/
@[cluster_algebras "lem_set_mutation_seed_formula"]
theorem seedMutationSeq_increasingSeq_extCluster_of_mem (S : SeedData F m n)
    {K : Finset (Fin n)}
    (hK : ∀ k ∈ K, ∀ k' ∈ K, S.extExchangeMatrix (Fin.castLE hmn k) k' = 0) {k : Fin n}
    (hk : k ∈ K) :
    (seedMutationSeq hmn S (increasingSeq K)).extCluster (Fin.castLE hmn k) =
      (exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
          exchangeMonomialNeg S.extCluster S.extExchangeMatrix k) /
        S.extCluster (Fin.castLE hmn k) := by
  induction K using Finset.induction_on_max generalizing k with
  | empty => exact absurd hk (Finset.notMem_empty k)
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hK' : ∀ k ∈ s, ∀ k' ∈ s, S.extExchangeMatrix (Fin.castLE hmn k) k' = 0 :=
      fun k hk k' hk' => hK k (Finset.mem_insert_of_mem hk) k' (Finset.mem_insert_of_mem hk')
    have hBka : ∀ k ∈ s, S.extExchangeMatrix (Fin.castLE hmn k) a = 0 := fun k hk =>
      hK k (Finset.mem_insert_of_mem hk) a (Finset.mem_insert_self a s)
    set T := seedMutationSeq hmn S (increasingSeq s) with hT
    rw [increasingSeq_insert_of_forall_lt ha, seedMutationSeq_append, ← hT,
      seedMutationSeq_cons, seedMutationSeq_nil]
    rcases Finset.mem_insert.1 hk with rfl | hks
    · have hcol : ∀ i, T.extExchangeMatrix i k = S.extExchangeMatrix i k := by
        intro i
        rw [hT, seedMutationSeq_extExchangeMatrix_eq_matrixMutationList,
          matrixMutationList_increasingSeq_apply hK']
        split_ifs with h
        · rcases h with ⟨k', hk', rfl⟩ | h
          · rw [hBka k' hk', neg_zero]
          · exact absurd h has
        · rw [Finset.sum_eq_zero fun k' hk' => by rw [hBka k' hk', mutationCorrection_zero_right],
            add_zero]
      have hx : ∀ i, S.extExchangeMatrix i k ≠ 0 → T.extCluster i = S.extCluster i :=
        fun i hi => seedMutationSeq_increasingSeq_extCluster_of_notMem S
          fun k' hk' hik' => hi (hik' ▸ hBka k' hk')
      have hxk : T.extCluster (Fin.castLE hmn k) = S.extCluster (Fin.castLE hmn k) :=
        seedMutationSeq_increasingSeq_extCluster_of_notMem S
          fun k' hk' h => has (Fin.castLE_injective hmn h ▸ hk')
      simp only [seedMutation, Function.update_self]
      rw [exchangeMonomialPos_congr hx hcol, exchangeMonomialNeg_congr hx hcol, hxk]
    · have hka : Fin.castLE hmn k ≠ Fin.castLE hmn a := fun h =>
        has (Fin.castLE_injective hmn h ▸ hks)
      simp only [seedMutation]
      rw [Function.update_of_ne hka, ih hK' hks]

end ClusterAlgebras
