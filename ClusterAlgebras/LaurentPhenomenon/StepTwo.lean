/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Laurent.Denominators
public import ClusterAlgebras.LaurentPhenomenon.CaseTwoJJ
public import ClusterAlgebras.LaurentPhenomenon.CaseTwoK

/-!
# The inductive step of the Laurent phenomenon when `bⱼₖ < 0`

Let `(x̃, B̃)` be a labeled seed, `j ≠ k` directions with `bⱼₖ < 0`, and `q, r` rows of `B̃`
such that row `q` has `1` in column `j` and `0` elsewhere, row `r` has `1` in column `k` and
`0` elsewhere, and `q` is frozen. Write `L = ℤ[x̃^{±1}]`, `Σ₁ = μⱼ(x̃, B̃)`, `Σ₂ = μₖ(Σ₁)` and
`Σ₃ = μⱼ(Σ₂)`. Mutation is an involution, so `Σ₂ = μⱼ(Σ₃)`, and for every sequence `s` the seed
`μ_{(j, k, s)}(x̃, B̃)` is both `μ_{(k, s)}(Σ₁)` and `μ_{(j, s)}(Σ₃)`.

Suppose an entry `z` of its extended cluster is a Laurent polynomial in the extended cluster of
`Σ₁` and in that of `Σ₃`. The first differs from `x̃` only by `x'ⱼ` in position `j`, the second
only by `x''ⱼ` in position `j` and by `x'ₖ`, the new entry of `Σ₂`, in position `k`; all three
lie in `L`. Clearing denominators gives `z (x'ⱼ)ᵃ ∈ L` and `z (x'ₖ)ᵇ (x''ⱼ)ᶜ ∈ L`. The variable
`x'ⱼ` is prime in `L` and divides neither `x'ₖ` nor `x''ⱼ`, hence not `(x'ₖ)ᵇ (x''ⱼ)ᶜ`; so
`z ∈ L`.

## Main results

* `ClusterAlgebras.IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring_of_neg`: the
  inductive step of the Laurent phenomenon along a sequence of mutations, in the case
  `bⱼₖ < 0`.

## Implementation notes

This is the second case of the inductive step of the proof of the Laurent phenomenon along a
sequence of mutations, isolated as a statement about one labeled seed: the two inductive
hypotheses, for `Σ₁` and `Σ₃`, appear as hypotheses. In FWZ the rows `q` and `r` are the
two frozen rows `m + 1` and `m + 2` of the augmented seed. Of this only the frozenness of `q` is
used, and only to know that `q` is not the row indexed by `k`; the row `r` may be any row, and
`q ≠ r` is not assumed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra K F] {m n : ℕ}

/-- **The inductive step of the Laurent phenomenon when `bⱼₖ < 0`.** Let `S` be a labeled seed
over a field of characteristic zero, `j ≠ k` directions with `bⱼₖ < 0`, and `q, r` rows with
`q` frozen, row `q` the unit row with `1` in column `j` and row `r` the unit row with `1` in
column `k`. Let `s` be a sequence of directions such that the entries of the extended cluster
of `μ_{(k, s)}(μⱼ(S))` are Laurent in the extended cluster of `μⱼ(S)`, and those of
`μ_{(j, s)}(Σ₃)`, where `Σ₃ = μⱼ(μₖ(μⱼ(S)))`, are Laurent in the extended cluster of `Σ₃`.
Then every entry of the extended cluster of `μ_{(j, k, s)}(S)` lies in `ℤ[x̃^{±1}]`. -/
theorem IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring_of_neg [CharZero K]
    (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) {j k : Fin n}
    (hjk : j ≠ k) (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) {q r : Fin m}
    (hqn : n ≤ (q : ℕ)) (hqrow : ∀ l, S.extExchangeMatrix q l = if l = j then 1 else 0)
    (hrrow : ∀ l, S.extExchangeMatrix r l = if l = k then 1 else 0) (s : List (Fin n))
    (h₁ : ∀ i, (ClusterAlgebras.seedMutationSeq hmn (ClusterAlgebras.seedMutation hmn S j)
      (k :: s)).extCluster i ∈ laurentSubring (ClusterAlgebras.seedMutation hmn S j).extCluster)
    (h₃ : ∀ i, (ClusterAlgebras.seedMutationSeq hmn (ClusterAlgebras.seedMutation hmn
        (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k) j)
          (j :: s)).extCluster i ∈
      laurentSubring (ClusterAlgebras.seedMutation hmn
        (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k) j).extCluster)
    (i : Fin m) :
    (ClusterAlgebras.seedMutationSeq hmn S (j :: k :: s)).extCluster i ∈
      laurentSubring S.extCluster := by
  classical
  set S₁ := ClusterAlgebras.seedMutation hmn S j
  set S₂ := ClusterAlgebras.seedMutation hmn S₁ k
  set S₃ := ClusterAlgebras.seedMutation hmn S₂ j
  set L := laurentSubring S.extCluster
  set cj := Fin.castLE hmn j
  set ck := Fin.castLE hmn k
  have hqj : S.extExchangeMatrix q j = 1 := (hqrow j).trans (if_pos rfl)
  have hq : q ≠ ck := fun h => by
    have : (q : ℕ) = k := congrArg Fin.val h
    omega
  have hc : cj ≠ ck := fun h => hjk (Fin.castLE_injective hmn h)
  have h₂₃ : ClusterAlgebras.seedMutation hmn S₃ j = S₂ :=
    seedMutation_seedMutation hmn ((hS.seedMutation hmn j).seedMutation hmn k) j
  -- the entry `z` as an entry of a mutation of `Σ₁` and of `Σ₃`
  have hz₁ := h₁ i
  have hz₃ := h₃ i
  rw [seedMutationSeq_cons, h₂₃] at hz₃
  -- the three new variables and their membership in `L`
  have hxj : S₁.extCluster cj ∈ L :=
    hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j hqj
  have hxk : S₂.extCluster ck ∈ L :=
    hS.seedMutation_seedMutation_extCluster_castLE_mem_laurentSubring hmn hjk hqj
  have hxjj : S₃.extCluster cj ∈ L :=
    hS.seedMutation_jkj_extCluster_mem_laurentSubring hmn hjk hb
  have hS₃k : S₃.extCluster ck = S₂.extCluster ck :=
    seedMutation_extCluster_of_ne hmn S₂ hc.symm
  -- clearing denominators
  obtain ⟨a, ha⟩ := exists_mul_prod_pow_mem_laurentSubring (y := S.extCluster)
    (y' := S₁.extCluster) (T := {cj})
    (fun l hl => seedMutation_extCluster_of_ne hmn S (Finset.notMem_singleton.1 hl))
    (fun l hl => (Finset.mem_singleton.1 hl) ▸ hxj) hz₁
  obtain ⟨e, he⟩ := exists_mul_prod_pow_mem_laurentSubring (y := S.extCluster)
    (y' := S₃.extCluster) (T := {cj, ck})
    (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      rw [seedMutation_extCluster_of_ne hmn S₂ hl.1, seedMutation_extCluster_of_ne hmn S₁ hl.2,
        seedMutation_extCluster_of_ne hmn S hl.1])
    (fun l hl => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact hxjj
      · exact hS₃k ▸ hxk) hz₃
  rw [Finset.prod_singleton] at ha
  rw [Finset.prod_pair hc, hS₃k] at he
  -- coprimality
  have hp := hS.prime_seedMutation_extCluster_castLE_self hmn j hqj
  have hk := hS.not_dvd_seedMutation_seedMutation_extCluster_castLE hmn hjk hb hqj
    ((hrrow j).trans (if_neg hjk)) ((hrrow k).trans (if_pos rfl))
  have hjj := hS.not_dvd_seedMutation_jkj_extCluster_castLE_self hmn hjk hb hq hqrow hrrow
  refine mem_of_mul_pow_mem_of_mul_mem L hp
    (w := (⟨_, hxk⟩ : L) ^ e ck * (⟨_, hxjj⟩ : L) ^ e cj) ?_ (a cj) ha ?_
  · intro hdvd
    rcases hp.dvd_or_dvd hdvd with h | h
    · exact hk (hp.dvd_of_dvd_pow h)
    · exact hjj (hp.dvd_of_dvd_pow h)
  · change (ClusterAlgebras.seedMutationSeq hmn S₂ s).extCluster i * _ ∈ L
    simpa [mul_comm (S₃.extCluster cj ^ e cj), mul_assoc] using he

end ClusterAlgebras
