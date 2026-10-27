/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.CaseOne
public import ClusterAlgebras.Laurent.Denominators

/-!
# The Laurent phenomenon: the inductive step when the two directions commute

Let `(x̃, B̃)` be a labeled seed over a field of characteristic zero, let `j, k` be directions
with `b_jk = 0`, and let `q` be a row with `b_qj = 1` and `b_qk = 0`. Mutations in directions
`j` and `k` commute, so `μ_{(j,k,s)}(x̃, B̃)` is both `μ_{(k,s)}(μⱼ(x̃, B̃))` and
`μ_{(j,s)}(μₖ(x̃, B̃))`. Suppose every entry `z` of its extended cluster is an integer Laurent
polynomial in the extended cluster of `μⱼ(x̃, B̃)` and in that of `μₖ(x̃, B̃)`. These differ from
`x̃` only in the positions of `j` and `k`, by the new variables `x'ⱼ` and `x'ₖ`, which lie in
`L = ℤ[x̃^{±1}]`. Clearing denominators gives `a, b ∈ ℕ` with `z (x'ⱼ)^a ∈ L` and
`z (x'ₖ)^b ∈ L`. The variable `x'ⱼ` is prime in `L` and does not divide `x'ₖ`, hence does not
divide `(x'ₖ)^b`; so `z ∈ L`.

This is the first case of the inductive step in the proof of the Laurent phenomenon along a
sequence of mutations, isolated as a statement about one labeled seed.

## Main results

* `ClusterAlgebras.IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring_of_eq_zero`:
  if `b_jk = 0` and some row `q` has `b_qj = 1` and `b_qk = 0`, and the entries of
  `μ_{(j,k,s)}(x̃, B̃)` are Laurent in the extended clusters of `μⱼ(x̃, B̃)` and of `μₖ(x̃, B̃)`,
  then they are Laurent in `x̃`.

## Implementation notes

In FWZ the row `q` is an added frozen row with entry `1` in column `j` and `0`
elsewhere. Only its entries in columns `j` and `k` are used, so the statement assumes just
`b_qj = 1` and `b_qk = 0`; these also force `j ≠ k`, which is therefore not assumed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra K F] {m n : ℕ}

/-- **The inductive step of the Laurent phenomenon, commuting case.** Let `S` be a labeled seed
over a field of characteristic zero, `j, k` directions with `b_jk = 0`, and `q` a row with
`b_qj = 1` and `b_qk = 0`. If every entry of the extended cluster of `μ_{(k,s)}(μⱼ S)` is Laurent
in the extended cluster of `μⱼ S`, and every entry of that of `μ_{(j,s)}(μₖ S)` is Laurent in the
extended cluster of `μₖ S`, then every entry of the extended cluster of `μ_{(j,k,s)} S` is
Laurent in the extended cluster of `S`. -/
theorem IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring_of_eq_zero [CharZero K]
    (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) {j k : Fin n}
    (hb : S.extExchangeMatrix (Fin.castLE hmn j) k = 0) {q : Fin m}
    (hqj : S.extExchangeMatrix q j = 1) (hqk : S.extExchangeMatrix q k = 0) (s : List (Fin n))
    (h₁ : ∀ i, (ClusterAlgebras.seedMutationSeq hmn (ClusterAlgebras.seedMutation hmn S j)
      (k :: s)).extCluster i ∈ laurentSubring (ClusterAlgebras.seedMutation hmn S j).extCluster)
    (h₂ : ∀ i, (ClusterAlgebras.seedMutationSeq hmn (ClusterAlgebras.seedMutation hmn S k)
      (j :: s)).extCluster i ∈ laurentSubring (ClusterAlgebras.seedMutation hmn S k).extCluster)
    (i : Fin m) :
    (ClusterAlgebras.seedMutationSeq hmn S (j :: k :: s)).extCluster i ∈
      laurentSubring S.extCluster := by
  have hjk : j ≠ k := by
    rintro rfl
    rw [hqj] at hqk
    exact one_ne_zero hqk
  set z := (ClusterAlgebras.seedMutationSeq hmn S (j :: k :: s)).extCluster i
  have hz₁ : z ∈ laurentSubring (ClusterAlgebras.seedMutation hmn S j).extCluster := h₁ i
  have hz₂ : z ∈ laurentSubring (ClusterAlgebras.seedMutation hmn S k).extCluster := by
    have := h₂ i
    rw [seedMutationSeq_cons, ← seedMutation_comm hmn hS hjk hb] at this
    exact this
  -- clearing the new variable in each of the two neighbouring extended clusters
  have hclear (l : Fin n)
      (hz : z ∈ laurentSubring (ClusterAlgebras.seedMutation hmn S l).extCluster) :
      ∃ a : ℕ, z * (ClusterAlgebras.seedMutation hmn S l).extCluster (Fin.castLE hmn l) ^ a ∈
        laurentSubring S.extCluster := by
    obtain ⟨a, ha⟩ := exists_mul_prod_pow_mem_laurentSubring (T := {Fin.castLE hmn l})
      (fun i hi => seedMutation_extCluster_of_ne hmn S (Finset.notMem_singleton.1 hi))
      (fun i _ => seedMutation_extCluster_mem_laurentSubring_self hmn S l i) hz
    exact ⟨a (Fin.castLE hmn l), by simpa using ha⟩
  obtain ⟨a, ha⟩ := hclear j hz₁
  obtain ⟨b, hb'⟩ := hclear k hz₂
  have hp := hS.prime_seedMutation_extCluster_castLE_self hmn j hqj
  refine mem_of_mul_pow_mem_of_mul_mem _ hp (fun h => ?_) a ha
    (w := ⟨_, seedMutation_extCluster_mem_laurentSubring_self hmn S k (Fin.castLE hmn k)⟩ ^ b)
    (by simpa using hb')
  exact hS.not_dvd_seedMutation_extCluster_castLE_self hmn hqj hqk (hp.dvd_of_dvd_pow h)

end ClusterAlgebras
