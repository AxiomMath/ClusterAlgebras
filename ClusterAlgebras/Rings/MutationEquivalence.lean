/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Basic
public import ClusterAlgebras.TypeD.Reduction

/-!
# Mutation equivalent seeds have the same cluster algebra

If `Σ₂ = (μₛ(Σ₁))^π` for a mutation sequence `s` and a bijective restriction map `π` from
`(m, n)` to itself, and `Σ₁` is a labeled seed, then `Σ₁` and `Σ₂` generate the same cluster
algebra: `𝒜(Σ₁) = 𝒜(Σ₂)`. Mutation moves along a seed pattern through `Σ₁`, and relabelling a
seed pattern along `π` gives a seed pattern through `Σ₂` whose seeds have the same cluster
variables and the same frozen variables as those of the first, because `π` permutes the
mutable positions `[1, n]` and the frozen positions `[n + 1, m]` separately.

## Main results

* `ClusterAlgebras.clusterVariables_reindex_self`: reindexing along a reindexing map from
  `(m, n)` to itself keeps the cluster variables.
* `ClusterAlgebras.frozenVariables_reindex_self`: reindexing along a restriction map from
  `(m, n)` to itself keeps the frozen variables.
* `ClusterAlgebras.IsLabeledSeed.reindex_self`: reindexing a labeled seed along a reindexing map
  from `(m, n)` to itself gives a labeled seed in the same field.
* `ClusterAlgebras.IsMutationEquivalent.isLabeledSeed`: a seed mutation equivalent to a labeled
  seed is a labeled seed in the same field.
* `ClusterAlgebras.IsMutationEquivalent.clusterAlgebraOfSeed_eq`: mutation equivalent seeds have
  the same cluster algebra.

## Implementation notes

Only `Σ₁` is assumed to be a labeled seed: that `Σ₂` is one follows
(`IsMutationEquivalent.isLabeledSeed`). The hypothesis that `μₛ(Σ₁)` is
defined, part of `IsMutationEquivalent`, is not used: the entries of a labeled seed and of all
its mutations are nonzero.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

section Reindex

omit [Field F] in
/-- **Reindexing along a reindexing map from `(m, n)` to itself keeps the cluster variables**:
such a map permutes the mutable positions. -/
theorem clusterVariables_reindex_self (hmn : n ≤ m) (S : SeedData F m n)
    (r : ReindexingMap m n m n) :
    clusterVariables hmn (S.reindex hmn r) = clusterVariables hmn S := by
  have h : cluster hmn (S.reindex hmn r) = cluster hmn S ∘ r.col hmn := by
    funext i
    simp only [cluster, SeedData.reindex_extCluster, Function.comp_apply,
      ReindexingMap.castLE_col]
  rw [clusterVariables, clusterVariables, h,
    (Finite.surjective_of_injective (r.col_injective hmn)).range_comp]

omit [Field F] in
/-- **Reindexing along a restriction map from `(m, n)` to itself keeps the frozen variables**:
such a map permutes the frozen positions. -/
theorem frozenVariables_reindex_self (hmn : n ≤ m) (S : SeedData F m n)
    {r : ReindexingMap m n m n} (hr : r.IsRestriction) :
    frozenVariables (S.reindex hmn r) = frozenVariables S := by
  have himage : (r : Fin m → Fin m) '' {i | n ≤ (i : ℕ)} = {i : Fin m | n ≤ (i : ℕ)} := by
    ext j
    refine ⟨?_, fun hj => ?_⟩
    · rintro ⟨i, hi, rfl⟩
      exact hr i hi
    · obtain ⟨i, rfl⟩ := Finite.surjective_of_injective r.injective j
      exact ⟨i, not_lt.1 fun h => not_lt.2 hj ((hr.val_lt_iff i).2 h), rfl⟩
  rw [frozenVariables, frozenVariables, SeedData.reindex_extCluster, Set.image_comp, himage]

/-- A labeled seed reindexed along a reindexing map from `(m, n)` to itself is a labeled seed in
the same field. -/
theorem IsLabeledSeed.reindex_self (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (r : ReindexingMap m n m n) :
    IsLabeledSeed K hmn (S.reindex hmn r) := by
  refine ⟨⟨hS.1.1.comp r r.injective, ?_⟩, hS.2.matrixReindex hmn hmn r⟩
  rw [SeedData.reindex_extCluster,
    (Finite.surjective_of_injective (f := ⇑r) r.injective).range_comp]
  exact hS.1.2

end Reindex

section MutationEquivalent

/-- **A seed mutation equivalent to a labeled seed is a labeled seed** in the same field. -/
theorem IsMutationEquivalent.isLabeledSeed [CharZero K] (hmn : n ≤ m) {S₁ S₂ : SeedData F m n}
    (hS₁ : IsLabeledSeed K hmn S₁) (h : IsMutationEquivalent hmn S₁ S₂) :
    IsLabeledSeed K hmn S₂ := by
  obtain ⟨s, π, -, -, -, rfl⟩ := h
  exact (hS₁.seedMutationSeq hmn s).reindex_self hmn π

/-- **Mutation equivalent seeds have the same cluster algebra**: if `Σ₁` is a labeled seed in
`F` over `K` and `Σ₂ = (μₛ(Σ₁))^π` is mutation equivalent to it, then `𝒜(Σ₁) = 𝒜(Σ₂)`. -/
@[cluster_algebras "lem_mutation_equivalent_same_algebra"]
theorem IsMutationEquivalent.clusterAlgebraOfSeed_eq [CharZero K] (hmn : n ≤ m)
    {S₁ S₂ : SeedData F m n} (hS₁ : IsLabeledSeed K hmn S₁) (h : IsMutationEquivalent hmn S₁ S₂) :
    clusterAlgebraOfSeed K hmn S₁ = clusterAlgebraOfSeed K hmn S₂ := by
  obtain ⟨s, π, hπ, -, -, rfl⟩ := h
  obtain ⟨P, hP, hP₀⟩ := exists_isSeedPattern hmn RegularTree.root hS₁
  obtain ⟨t₁, ht₁⟩ := hP.seedMutationSeq_mem_range hmn RegularTree.root s
  obtain ⟨P', hP', hP'₁, -, -, hvars, -⟩ :=
    hP.exists_isSeedPattern_reindex hmn π t₁ t₁
  rw [← hP₀, ← ht₁, ← hP'₁, ← hP.clusterAlgebra_eq hmn, ← hP'.clusterAlgebra_eq hmn]
  have hground : groundRing K P' = groundRing K P := by
    rw [hP.groundRing_eq hmn t₁, hP'.groundRing_eq hmn t₁, hP'₁,
      frozenVariables_reindex_self hmn _ hπ]
  unfold clusterAlgebra
  rw [hground]
  exact congrArg (fun X => Algebra.adjoin K ((groundRing K P : Set F) ∪ X)) hvars.symm

end MutationEquivalent

end ClusterAlgebras
