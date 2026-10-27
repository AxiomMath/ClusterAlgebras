/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Tropical.TripleMutation

/-!
# The pattern of triples of a seed pattern

Let `Σ` be a seed pattern of rank `n` in `F` over `K`. Assigning to each vertex `t` of `𝕋ₙ` the
triple of the seed `Σ(t)` gives a labeled seed pattern of triples. Its frozen variables are those
of any one seed `Σ(t₀)`: seed mutation does not change the frozen variables, and any two
vertices of `𝕋ₙ` are joined by a walk, so all the seeds of `Σ` have the same frozen variables.

Each triple is a labeled seed triple, since its extended cluster, with the frozen variables of the
seed, is the extended cluster of the seed, and its exchange matrix is the principal part of the
extended exchange matrix of the seed. The edge condition is the agreement of seed mutation with
mutation of triples, `SeedData.toSeedTriple_seedMutation`.

## Main results

* `ClusterAlgebras.SeedData.extCluster_toSeedTriple`: the extended cluster of the triple of a
  seed, with the frozen variables of the seed, is the extended cluster of the seed.
* `ClusterAlgebras.IsLabeledSeed.isSeedTriple_toSeedTriple`: the triple of a labeled seed is a
  labeled seed triple.
* `ClusterAlgebras.IsSeedPattern.frozenTuple_eq`: all seeds of a seed pattern have the same
  frozen variables.
* `ClusterAlgebras.IsSeedPattern.isTriplePattern_toSeedTriple`: the triples of a seed pattern
  form a labeled seed pattern of triples.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

omit [Field F] in
/-- The extended cluster of the triple of a seed `(x̃, B̃)`, with the frozen variables of
`(x̃, B̃)`, is `x̃`. -/
@[simp]
theorem SeedData.extCluster_toSeedTriple (hmn : n ≤ m) (S : SeedData F m n) :
    (S.toSeedTriple hmn).extCluster S.frozenTuple = S.extCluster := by
  funext i
  by_cases hi : (i : ℕ) < n
  · simp only [SeedTriple.extCluster, hi, dite_true, SeedData.toSeedTriple, cluster]
    rfl
  · simp only [SeedTriple.extCluster, hi, dite_false, SeedData.frozenTuple]

/-- **The triple of a labeled seed is a labeled seed triple**, with the frozen variables of the
seed. -/
theorem IsLabeledSeed.isSeedTriple_toSeedTriple (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) : IsSeedTriple K S.frozenTuple (S.toSeedTriple hmn) := by
  refine ⟨?_, hS.2⟩
  rw [SeedData.extCluster_toSeedTriple]
  exact hS.1

/-- Seed mutation along any sequence does not change the frozen variables. -/
@[simp]
theorem SeedData.frozenTuple_seedMutationSeq (hmn : n ≤ m) (S : SeedData F m n)
    (s : List (Fin n)) : (seedMutationSeq hmn S s).frozenTuple = S.frozenTuple := by
  induction s generalizing S with
  | nil => rfl
  | cons k s ih => rw [seedMutationSeq_cons, ih, SeedData.frozenTuple_seedMutation]

/-- **All seeds of a seed pattern have the same frozen variables.** -/
theorem IsSeedPattern.frozenTuple_eq (hmn : n ≤ m) {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (t t' : RegularTree n) :
    (P t).frozenTuple = (P t').frozenTuple := by
  rw [hP.apply_eq_seedMutationSeq hmn t' t, SeedData.frozenTuple_seedMutationSeq]

/-- **The triples of a seed pattern form a pattern of triples.** Assigning to each vertex `t` of
`𝕋ₙ` the triple of the seed `Σ(t)` is a labeled seed pattern of triples, whose frozen variables
are those of `Σ(t₀)` for any vertex `t₀`. -/
@[cluster_algebras "lem_triple_pattern_of_seed_pattern"]
theorem IsSeedPattern.isTriplePattern_toSeedTriple (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n) :
    IsTriplePattern K (P t₀).frozenTuple fun t => (P t).toSeedTriple hmn := by
  refine ⟨fun t => ?_, fun k t t' h => ?_⟩
  · rw [hP.frozenTuple_eq hmn t₀ t]
    exact (hP.1 t).isSeedTriple_toSeedTriple hmn
  · dsimp only
    rw [hP.2 k t t' h, SeedData.toSeedTriple_seedMutation, hP.frozenTuple_eq hmn t₀ t]

end ClusterAlgebras
