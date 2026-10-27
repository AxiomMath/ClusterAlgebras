/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.AugmentedSeed
public import ClusterAlgebras.LaurentPhenomenon.StepOne
public import ClusterAlgebras.LaurentPhenomenon.StepTwo
public import ClusterAlgebras.SeedPattern

/-!
# The Laurent phenomenon

Let `(x̃, B̃)` be a labeled seed in a field `F` over a field `𝕜` of characteristic zero. For
every finite sequence `s` of directions, every entry of the extended cluster of `μ_s(x̃, B̃)` is
an integer Laurent polynomial in `x̃`, that is, lies in `ℤ[x̃^{±1}]`. Consequently, in a seed
pattern `Σ`, every cluster variable of `Σ(t)` is an integer Laurent polynomial in the extended
cluster of `Σ(t₀)`, for any two vertices `t₀, t` of the regular tree.

The proof is by strong induction on the length `d` of `s`, over all fields `F` at once.
For `d = 0` there is nothing to show, and for `d = 1` the new entry is `(M⁺ + M⁻) / xₖ` with
`xₖ` a unit of `ℤ[x̃^{±1}]`. For `s = (j, k, s'')` with `j = k` the first two mutations
cancel. For `j ≠ k`, after replacing `B̃` by `-B̃` if needed, `b_jk ≤ 0`. The seed is then
augmented by two frozen rows, the unit rows in columns `j` and `k`, over the field `F(u, v)`;
specialization reduces the claim to the augmented seed, where the two inductive steps
(`b_jk = 0` and `b_jk < 0`) apply, their hypotheses being instances of the statement at length
`d - 1` for seeds in `F(u, v)`.

## Main results

* `ClusterAlgebras.IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring`: the Laurent
  phenomenon along a sequence of mutations.
* `ClusterAlgebras.IsSeedPattern.clusterVariables_subset_laurentSubring`: the Laurent
  phenomenon for a seed pattern.

## Implementation notes

FWZ's induction quantifies over the ground field `𝕜` as well as over `F`. The ground
field never changes in the proof (the augmented seed is a labeled seed over the same `𝕜`), so
here `𝕜` is fixed and the induction is over the fields `F` of one universe, the augmented
field `F(u, v)` lying in the universe of `F`. FWZ assume `n ≥ 1`; this is not used.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

universe u v

variable {K : Type v} [Field K] {n : ℕ}

/-- The inductive step of the Laurent phenomenon along a sequence `(j, k, s)` with `j ≠ k` and
`b_jk ≤ 0`, given the statement for all sequences of length `s.length + 1` over all fields of
the universe of `F`. -/
private theorem IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring_of_nonpos
    [CharZero K] {F : Type u} [Field F] [Algebra K F] {m : ℕ} (hmn : n ≤ m)
    {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) {j k : Fin n} (hjk : j ≠ k)
    (hb : S.extExchangeMatrix (Fin.castLE hmn j) k ≤ 0) (s : List (Fin n))
    (ih : ∀ (F' : Type u) [Field F'] [Algebra K F'] (m' : ℕ) (hmn' : n ≤ m')
      (S' : SeedData F' m' n), IsLabeledSeed K hmn' S' → ∀ s' : List (Fin n),
        s'.length = s.length + 1 → ∀ i,
          (ClusterAlgebras.seedMutationSeq hmn' S' s').extCluster i ∈
            laurentSubring S'.extCluster)
    (i : Fin m) :
    (ClusterAlgebras.seedMutationSeq hmn S (j :: k :: s)).extCluster i ∈
      laurentSubring S.extCluster := by
  have hmn' : n ≤ m + 2 := by omega
  obtain ⟨F', _, _, S', hS', -, hprin, hq, hr, hspec⟩ := hS.exists_augmentedSeed hmn hmn' j k
  refine hspec _ i ?_
  have hqj : S'.extExchangeMatrix ⟨m, by omega⟩ j = 1 := by rw [hq]; simp
  have hb' : S'.extExchangeMatrix (Fin.castLE hmn' j) k ≤ 0 := by rw [hprin]; exact hb
  rcases hb'.lt_or_eq with hlt | heq
  · refine hS'.seedMutationSeq_extCluster_mem_laurentSubring_of_neg hmn' hjk hlt
      (q := ⟨m, by omega⟩) (r := ⟨m + 1, by omega⟩) (by simpa using hmn) hq hr s
      (ih F' _ hmn' _ (hS'.seedMutation hmn' j) (k :: s) rfl)
      (ih F' _ hmn' _ (((hS'.seedMutation hmn' j).seedMutation hmn' k).seedMutation hmn' j)
        (j :: s) rfl) _
  · refine hS'.seedMutationSeq_extCluster_mem_laurentSubring_of_eq_zero hmn' heq hqj
      (by rw [hq]; simp [Ne.symm hjk]) s
      (ih F' _ hmn' _ (hS'.seedMutation hmn' j) (k :: s) rfl)
      (ih F' _ hmn' _ (hS'.seedMutation hmn' k) (j :: s) rfl) _

/-- The Laurent phenomenon along sequences of mutations of length `d`, for all fields of one
universe at once. -/
private theorem IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring_of_length_eq
    [CharZero K] (d : ℕ) :
    ∀ (F : Type u) [Field F] [Algebra K F] (m : ℕ) (hmn : n ≤ m) (S : SeedData F m n),
      IsLabeledSeed K hmn S → ∀ s : List (Fin n), s.length = d → ∀ i,
        (ClusterAlgebras.seedMutationSeq hmn S s).extCluster i ∈ laurentSubring S.extCluster := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F _ _ m hmn S hS s hs i
  rcases s with _ | ⟨j, _ | ⟨k, s⟩⟩
  · exact mem_laurentSubring _ i
  · exact seedMutation_extCluster_mem_laurentSubring S.extCluster hmn
      (mem_laurentSubring _) j (isUnit_mem_laurentSubring _ (hS.1.1.ne_zero _)) i
  simp only [List.length_cons] at hs
  by_cases hjk : j = k
  · subst hjk
    rw [seedMutationSeq_cons, seedMutationSeq_cons, seedMutation_seedMutation hmn hS]
    exact ih s.length (by omega) F m hmn S hS s rfl i
  have ih' := ih (s.length + 1) (by omega)
  rcases le_or_gt (S.extExchangeMatrix (Fin.castLE hmn j) k) 0 with hb | hb
  · exact seedMutationSeq_extCluster_mem_laurentSubring_of_nonpos hmn hS hjk hb s ih' i
  · have h := seedMutationSeq_extCluster_mem_laurentSubring_of_nonpos hmn (hS.neg hmn) hjk
      (by simp only [Matrix.neg_apply]; omega) s ih' i
    rwa [seedMutationSeq_neg hmn hS] at h

/-- **The Laurent phenomenon along a sequence of mutations.** Let `(x̃, B̃)` be a labeled seed
in `F` over a field `𝕜` of characteristic zero, and let `s` be a finite sequence of directions.
Then every entry of the extended cluster of `μ_s(x̃, B̃)` lies in `ℤ[x̃^{±1}]`. -/
@[cluster_algebras "prop_laurent_sequences"]
theorem IsLabeledSeed.seedMutationSeq_extCluster_mem_laurentSubring {F : Type u} [Field F]
    [Algebra K F] [CharZero K] {m : ℕ} (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (s : List (Fin n)) (i : Fin m) :
    (ClusterAlgebras.seedMutationSeq hmn S s).extCluster i ∈ laurentSubring S.extCluster :=
  seedMutationSeq_extCluster_mem_laurentSubring_of_length_eq s.length F m hmn S hS s rfl i

/-- **The Laurent phenomenon**, per cluster variable. In a seed pattern `Σ` of rank `n` over a
field of characteristic zero, the `i`-th cluster variable of `Σ(t)` is an integer Laurent
polynomial in the extended cluster of `Σ(t₀)`. -/
theorem IsSeedPattern.cluster_mem_laurentSubring {F : Type u} [Field F] [Algebra K F]
    [CharZero K] {m : ℕ} (hmn : n ≤ m) {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (t₀ t : RegularTree n) (i : Fin n) :
    cluster hmn (P t) i ∈ laurentSubring (P t₀).extCluster := by
  obtain ⟨s, hs⟩ := hP.exists_seedMutationSeq_eq hmn t₀ t
  rw [cluster, hs]
  exact (hP.1 t₀).seedMutationSeq_extCluster_mem_laurentSubring hmn s _

/-- **The Laurent phenomenon.** Let `Σ` be a seed pattern of rank `n` in `F` over a field of
characteristic zero, and let `t₀, t` be vertices of `𝕋ₙ`. Then every cluster variable of
`Σ(t)` is an integer Laurent polynomial in the extended cluster of `Σ(t₀)`. -/
@[cluster_algebras "thm_laurent"]
theorem IsSeedPattern.clusterVariables_subset_laurentSubring {F : Type u} [Field F]
    [Algebra K F] [CharZero K] {m : ℕ} (hmn : n ≤ m) {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (t₀ t : RegularTree n) :
    clusterVariables hmn (P t) ⊆ laurentSubring (P t₀).extCluster := by
  rintro _ ⟨i, rfl⟩
  exact hP.cluster_mem_laurentSubring hmn t₀ t i

end ClusterAlgebras
