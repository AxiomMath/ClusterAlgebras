/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Cartan.Counterpart
public import ClusterAlgebras.FiniteType.RankTwo
public import ClusterAlgebras.LaurentPhenomenon.SharperStep
public import ClusterAlgebras.Subpattern.Freezing
public import ClusterAlgebras.TypeA.Finite
public import ClusterAlgebras.TypeBC.TypeB
public import ClusterAlgebras.TypeBC.TypeC
public import ClusterAlgebras.TypeD.Reduction
public import ClusterAlgebras.TypeE.Finite
public import ClusterAlgebras.TypeFG.Finite

/-!
# Decomposable types

When the exchange matrix of one seed is *split* by a partition `[1, n] = I ⊔ J` of the mutable
indices, mutations in `I` and in `J` do not interact, and the seed pattern splits into the two
patterns through the seeds obtained by freezing `J`, respectively `I`. This gives finite type and
the counts for decomposable types from those of the blocks, completes the proof that a Cartan
counterpart of finite type forces finite type, and settles the rank-two case.

## Main definitions

* `ClusterAlgebras.IsSplitBy hmn B J`: the matrix `B` is split by `(Jᶜ, J)`.
* `ClusterAlgebras.BlockMatch hmn S J S'`: the `Jᶜ`-part of the seed `S` is read off from the
  seed `S'` through the freezing map `φ_J`.

## Main results

* `ClusterAlgebras.IsSplitBy.matrixMutation`, `ClusterAlgebras.seedMutation_part_of_isSplitBy`:
  mutation in one block leaves the other block alone.
* `ClusterAlgebras.IsSeedPattern.blockSeeds`: the seeds, finite type, cluster variables and
  clusters of a pattern with a split exchange matrix.
* `ClusterAlgebras.isPatternOfType_of_freeze`: the blocks have the types of the blocks of the
  Cartan counterpart.
* `ClusterAlgebras.IsSeedPattern.exists_blocks_of_isPatternOfType`: decomposable types.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_of_isCartanFiniteType`: a Cartan counterpart of
  finite type gives finite type.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_iff_of_rankTwo`: the finite type classification
  in rank two.

## Implementation notes

* The partition is `(Jᶜ, J)` for a `Finset J` of mutable indices, so FWZ's `I` is `Jᶜ`.
  The seed `Fr_J(Σ∘)` is `SeedData.freeze`; its mutable indices `0, …, |I| - 1`
  correspond through `φ_J` to the elements of `I` in increasing order. Freezing only reorders
  the extended cluster, so `Fr_J(Σ∘)` is a labeled seed in the same field `F`, and the block
  patterns `Π_I`, `Π_J` are taken in `F`, as in FWZ.
* FWZ's `I`-part of a seed is the family `(xᵢ)_{i ∈ I}` together with the columns
  `(b_{•j})_{j ∈ I}`. That the `I`-part of `Σ(t)` is read off from `Π_I(u)` through `φ_J` is
  `BlockMatch`: the frozen seed `Fr_J(Σ(t))` has the cluster and the extended exchange matrix of
  `Π_I(u)`. The two seeds may differ only in the entries at the positions of `J`, which are
  frozen in `Π_I`.
* Mutation in one block needs no seed condition, so `IsSplitBy.matrixMutation` and
  `seedMutation_part_of_isSplitBy` are stated for arbitrary seed data, a generalisation.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.8.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-! ### Split matrices and mutation in one block -/

/-- An `m × n` matrix `B̃` is **split** by the partition `(Jᶜ, J)` of the mutable indices when
`bᵢⱼ = bⱼᵢ = 0` for all `i ∉ J` and `j ∈ J`. -/
def IsSplitBy (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) (J : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, i ∉ J → j ∈ J → B (Fin.castLE hmn i) j = 0 ∧ B (Fin.castLE hmn j) i = 0

/-- Being split by `(Jᶜ, J)` is symmetric in the two blocks. -/
theorem isSplitBy_compl_iff {hmn : n ≤ m} {B : Matrix (Fin m) (Fin n) ℤ} {J : Finset (Fin n)} :
    IsSplitBy hmn B Jᶜ ↔ IsSplitBy hmn B J := by
  constructor <;> exact fun h i j hi hj => (h j i (by simpa using hj) (by simpa using hi)).symm

/-- **Mutation in one block leaves the other block alone**: the matrix part. If `B̃` is split by
`(Jᶜ, J)` and `k ∉ J`, then `μ_k(B̃)` is split by `(Jᶜ, J)`. With `isSplitBy_compl_iff` the same
holds for `k ∈ J`. -/
@[cluster_algebras "lem_block_mutation"]
theorem IsSplitBy.matrixMutation (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) ℤ}
    {J : Finset (Fin n)} (hB : IsSplitBy hmn B J) {k : Fin n} (hk : k ∉ J) :
    IsSplitBy hmn (ClusterAlgebras.matrixMutation hmn B k) J := by
  intro i j hi hj
  have hjk : j ≠ k := fun h => hk (h ▸ hj)
  constructor
  · by_cases hik : i = k
    · subst hik
      rw [matrixMutation_apply_row, (hB i j hi hj).1, neg_zero]
    · rw [matrixMutation_apply_of_eq_zero hmn B k
        (fun h => hik (Fin.castLE_injective hmn h)) hjk (Or.inr (hB k j hk hj).1)]
      exact (hB i j hi hj).1
  · by_cases hik : i = k
    · subst hik
      rw [matrixMutation_apply_col, (hB i j hi hj).2, neg_zero]
    · rw [matrixMutation_apply_of_eq_zero hmn B k
        (fun h => hjk (Fin.castLE_injective hmn h)) hik (Or.inl (hB k j hk hj).2)]
      exact (hB i j hi hj).2

/-- **Mutation in one block leaves the other block alone**: the seed part. If the matrix of `S`
is split by `(Jᶜ, J)` and `k ∉ J`, then `μ_k(S)` has the `J`-part of `S` — the same entries
`xⱼ` and the same columns `b_{•j}` for `j ∈ J` — and the same frozen variables, entry by entry.
No seed condition is needed. With `isSplitBy_compl_iff` the same holds with the blocks
exchanged. -/
@[cluster_algebras "lem_block_mutation"]
theorem seedMutation_part_of_isSplitBy (hmn : n ≤ m) {S : SeedData F m n} {J : Finset (Fin n)}
    (hS : IsSplitBy hmn S.extExchangeMatrix J) {k : Fin n} (hk : k ∉ J) :
    (∀ j ∈ J, (seedMutation hmn S k).extCluster (Fin.castLE hmn j) =
        S.extCluster (Fin.castLE hmn j) ∧
      ∀ i, (seedMutation hmn S k).extExchangeMatrix i j = S.extExchangeMatrix i j) ∧
    ∀ i : Fin m, n ≤ (i : ℕ) → (seedMutation hmn S k).extCluster i = S.extCluster i := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have hjk : j ≠ k := fun h => hk (h ▸ hj)
    exact ⟨Function.update_of_ne (fun h => hjk (Fin.castLE_injective hmn h)) _ _,
      fun i => matrixMutation_apply_of_castLE_eq_zero hmn hjk (hS k j hk hj).1 i⟩
  · refine Function.update_of_ne (fun h => ?_) _ _
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega

/-! ### Seeds of a pattern with a split exchange matrix -/

/-- The `Jᶜ`-part of the seed `S` is **read off from** the seed `S'` of rank `n - |J|` through
the freezing map `φ_J`: the frozen seed `Fr_J(S)` has the cluster and the extended exchange
matrix of `S'`. That is, `x_{φ_J(q)} = x'_q` for the mutable indices `q` of `S'`, and
`b_{φ_J(p) φ_J(q)} = b'_{pq}` for all `p, q`. -/
def BlockMatch (hmn : n ≤ m) (S : SeedData F m n) (J : Finset (Fin n))
    (S' : SeedData F m (n - J.card)) : Prop :=
  (S.freeze hmn J).extExchangeMatrix = S'.extExchangeMatrix ∧
    cluster (sub_card_le_of_le hmn J) (S.freeze hmn J) = cluster (sub_card_le_of_le hmn J) S'

/-! ### Agreement of a frozen seed with a seed of a block -/

/-- The freezing map sends the row index of a remaining mutable index `q` to the row index of
the mutable index `φ_J(q)` it lists. -/
private theorem freezingFun_castLE (hmn : n ≤ m) (J : Finset (Fin n)) (h' : n - J.card ≤ m)
    (q : Fin (n - J.card)) :
    freezingFun hmn J (Fin.castLE h' q) = Fin.castLE hmn ((freezingMap hmn J).col h' q) := by
  rw [freezingFun_of_lt hmn J (by simp), freezingMap_col]
  rfl

/-- Outside the positions `[n - |J|, n)`, the freezing map avoids the row indices of `J`. -/
private theorem freezingFun_ne_castLE_of_mem (hmn : n ≤ m) {J : Finset (Fin n)} {k : Fin n}
    (hk : k ∈ J) {p : Fin m} (hp : (p : ℕ) < n - J.card ∨ n ≤ (p : ℕ)) :
    freezingFun hmn J p ≠ Fin.castLE hmn k := by
  rcases hp with hp | hp
  · rw [freezingFun_of_lt hmn J hp]
    intro h
    have hmem := Jᶜ.orderEmbOfFin_mem (card_compl_eq_sub_card J) ⟨p, hp⟩
    rw [Fin.castLE_injective hmn h, Finset.mem_compl] at hmem
    exact hmem hk
  · rw [freezingFun_of_le hmn J hp]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega

omit [Field F] in
/-- The cluster of a seed `S'` read off from `S` through `φ_J`: its entry `q` is the entry of
the extended cluster of `S` at `φ_J(q)`. -/
theorem BlockMatch.cluster_apply {hmn : n ≤ m} {S : SeedData F m n} {J : Finset (Fin n)}
    {S' : SeedData F m (n - J.card)} (h : BlockMatch hmn S J S') (q : Fin (n - J.card)) :
    cluster (sub_card_le_of_le hmn J) S' q =
      S.extCluster (Fin.castLE hmn ((freezingMap hmn J).col (sub_card_le_of_le hmn J) q)) := by
  rw [← h.2]
  simp only [cluster, SeedData.freeze_extCluster, Function.comp_apply, freezingFun_castLE]

/-- The seed `S'` of rank `n - |J|` **agrees with** the frozen seed `Fr_J(S)` away from the
positions `[n - |J|, n)` of `J`: they have the same extended exchange matrix and the same entries
outside these positions. -/
def BlockAgree (hmn : n ≤ m) (S : SeedData F m n) (J : Finset (Fin n))
    (S' : SeedData F m (n - J.card)) : Prop :=
  (S.freeze hmn J).extExchangeMatrix = S'.extExchangeMatrix ∧
    ∀ p : Fin m, ((p : ℕ) < n - J.card ∨ n ≤ (p : ℕ)) →
      (S.freeze hmn J).extCluster p = S'.extCluster p

omit [Field F] in
/-- A frozen seed agrees with itself. -/
theorem blockAgree_freeze (hmn : n ≤ m) (S : SeedData F m n) (J : Finset (Fin n)) :
    BlockAgree hmn S J (S.freeze hmn J) :=
  ⟨rfl, fun _ _ => rfl⟩

omit [Field F] in
/-- Agreement away from `J` gives the `Jᶜ`-part. -/
theorem BlockAgree.blockMatch {hmn : n ≤ m} {S : SeedData F m n} {J : Finset (Fin n)}
    {S' : SeedData F m (n - J.card)} (h : BlockAgree hmn S J S') : BlockMatch hmn S J S' :=
  ⟨h.1, funext fun q => h.2 _ (Or.inl (by simp))⟩

/-- Mutation in any direction preserves the split. -/
theorem IsSplitBy.seedMutation (hmn : n ≤ m) {S : SeedData F m n} {J : Finset (Fin n)}
    (hS : IsSplitBy hmn S.extExchangeMatrix J) (k : Fin n) :
    IsSplitBy hmn (seedMutation hmn S k).extExchangeMatrix J := by
  by_cases hk : k ∈ J
  · rw [← isSplitBy_compl_iff] at hS ⊢
    exact hS.matrixMutation hmn (by simpa using hk)
  · exact hS.matrixMutation hmn hk

/-- Mutation along any sequence preserves the split. -/
theorem IsSplitBy.seedMutationSeq (hmn : n ≤ m) {S : SeedData F m n} {J : Finset (Fin n)}
    (hS : IsSplitBy hmn S.extExchangeMatrix J) (s : List (Fin n)) :
    IsSplitBy hmn (seedMutationSeq hmn S s).extExchangeMatrix J := by
  induction s generalizing S with
  | nil => exact hS
  | cons k s ih => exact ih (hS.seedMutation hmn k)

/-- Mutation in a direction `k ∈ J` keeps the agreement with the same seed. -/
theorem BlockAgree.seedMutation_of_mem {hmn : n ≤ m} {S : SeedData F m n}
    {J : Finset (Fin n)} {S' : SeedData F m (n - J.card)} (h : BlockAgree hmn S J S')
    (hS : IsSplitBy hmn S.extExchangeMatrix J) {k : Fin n} (hk : k ∈ J) :
    BlockAgree hmn (seedMutation hmn S k) J S' := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [← h.1]
    ext p q
    have hq := freezingMap_col_notMem hmn J (sub_card_le_of_le hmn J) q
    exact matrixMutation_apply_of_castLE_eq_zero hmn (by rintro rfl; exact hq hk)
      (hS _ k hq hk).2 _
  · rw [← h.2 p hp]
    exact Function.update_of_ne (freezingFun_ne_castLE_of_mem hmn hk hp) _ _

/-- Mutation in the direction `φ_J(q) ∉ J` corresponds to mutation in direction `q`. -/
theorem BlockAgree.seedMutation_col {hmn : n ≤ m} {S : SeedData F m n}
    {J : Finset (Fin n)} {S' : SeedData F m (n - J.card)} (h : BlockAgree hmn S J S')
    (hS : IsSplitBy hmn S.extExchangeMatrix J) (q : Fin (n - J.card)) :
    BlockAgree hmn (seedMutation hmn S ((freezingMap hmn J).col (sub_card_le_of_le hmn J) q)) J
      (seedMutation (sub_card_le_of_le hmn J) S' q) := by
  set h' := sub_card_le_of_le hmn J
  rw [BlockAgree, SeedData.freeze_seedMutation hmn J h' S rfl]
  set T := S.freeze hmn J
  have hzero : ∀ p : Fin m, ¬((p : ℕ) < n - J.card ∨ n ≤ (p : ℕ)) →
      T.extExchangeMatrix p q = 0 := by
    intro p hp
    simp only [not_or, not_lt, not_le] at hp
    obtain ⟨j, hj, hpj⟩ := exists_mem_freezingFun_eq_castLE hmn J hp.1 hp.2
    change S.extExchangeMatrix (freezingFun hmn J p) ((freezingMap hmn J).col h' q) = 0
    rw [hpj]
    exact (hS _ j (freezingMap_col_notMem hmn J h' q) hj).2
  have hx : ∀ i, T.extExchangeMatrix i q ≠ 0 → S'.extCluster i = T.extCluster i := by
    intro i hi
    by_cases hc : (i : ℕ) < n - J.card ∨ n ≤ (i : ℕ)
    · exact (h.2 i hc).symm
    · exact absurd (hzero i hc) hi
  have hB : ∀ i, S'.extExchangeMatrix i q = T.extExchangeMatrix i q := fun i => by rw [h.1]
  refine ⟨?_, fun p hp => ?_⟩
  · change matrixMutation h' T.extExchangeMatrix q = matrixMutation h' S'.extExchangeMatrix q
    rw [h.1]
  · change Function.update T.extCluster _ _ p = Function.update S'.extCluster _ _ p
    by_cases hpq : p = Fin.castLE h' q
    · subst hpq
      rw [Function.update_self, Function.update_self, exchangeMonomialPos_congr hx hB,
        exchangeMonomialNeg_congr hx hB, h.2 _ (Or.inl (by simp))]
    · rw [Function.update_of_ne hpq, Function.update_of_ne hpq, h.2 p hp]

/-- Mutation along any sequence keeps the agreement with some mutation of the block seed. -/
theorem BlockAgree.exists_seedMutationSeq {hmn : n ≤ m} {S : SeedData F m n}
    {J : Finset (Fin n)} {S' : SeedData F m (n - J.card)} (h : BlockAgree hmn S J S')
    (hS : IsSplitBy hmn S.extExchangeMatrix J) (s : List (Fin n)) :
    ∃ r : List (Fin (n - J.card)),
      BlockAgree hmn (seedMutationSeq hmn S s) J
        (seedMutationSeq (sub_card_le_of_le hmn J) S' r) := by
  induction s generalizing S S' with
  | nil => exact ⟨[], h⟩
  | cons k s ih =>
    by_cases hk : k ∈ J
    · exact ih (h.seedMutation_of_mem hS hk) (hS.seedMutation hmn k)
    · obtain ⟨q, rfl⟩ := exists_freezingMap_col_eq hmn J (sub_card_le_of_le hmn J) hk
      obtain ⟨r, hr⟩ := ih (h.seedMutation_col hS q) (hS.seedMutation hmn _)
      exact ⟨q :: r, hr⟩

/-- Mutation along the image `φ_J(r)` of a sequence corresponds to mutation along `r`. -/
theorem BlockAgree.seedMutationSeq_map_col {hmn : n ≤ m} {S : SeedData F m n}
    {J : Finset (Fin n)} {S' : SeedData F m (n - J.card)} (h : BlockAgree hmn S J S')
    (hS : IsSplitBy hmn S.extExchangeMatrix J) (r : List (Fin (n - J.card))) :
    BlockAgree hmn
      (seedMutationSeq hmn S (r.map ((freezingMap hmn J).col (sub_card_le_of_le hmn J)))) J
      (seedMutationSeq (sub_card_le_of_le hmn J) S' r) := by
  induction r generalizing S S' with
  | nil => exact h
  | cons q r ih => exact ih (h.seedMutation_col hS q) (hS.seedMutation hmn _)

/-- Mutation along a sequence of directions in `J` keeps the agreement with the same seed. -/
theorem BlockAgree.seedMutationSeq_of_forall_mem {hmn : n ≤ m} {S : SeedData F m n}
    {J : Finset (Fin n)} {S' : SeedData F m (n - J.card)} (h : BlockAgree hmn S J S')
    (hS : IsSplitBy hmn S.extExchangeMatrix J) {s : List (Fin n)} (hs : ∀ k ∈ s, k ∈ J) :
    BlockAgree hmn (seedMutationSeq hmn S s) J S' := by
  induction s generalizing S with
  | nil => exact h
  | cons k s ih =>
    exact ih (h.seedMutation_of_mem hS (hs k (by simp))) (hS.seedMutation hmn k)
      fun k' hk' => hs k' (by simp [hk'])

/-- All seeds of a seed pattern have the same entries at the frozen positions. -/
private theorem IsSeedPattern.extCluster_eq_of_le (hmn : n ≤ m) {P : RegularTree n → SeedData F m n}
    (hP : IsSeedPattern K hmn P) (t t' : RegularTree n) {i : Fin m} (hi : n ≤ (i : ℕ)) :
    (P t).extCluster i = (P t').extCluster i := by
  obtain ⟨s, hs⟩ := hP.exists_seedMutationSeq_eq hmn t' t
  rw [hs, seedMutationSeq_extCluster_of_le hmn _ s hi]

/-- Two seeds of a seed pattern with the same extended exchange matrix and the same cluster are
equal. -/
private theorem IsSeedPattern.eq_of_extExchangeMatrix_eq_of_cluster_eq (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t t' : RegularTree n}
    (hB : (P t).extExchangeMatrix = (P t').extExchangeMatrix)
    (hx : cluster hmn (P t) = cluster hmn (P t')) : P t = P t' := by
  refine SeedData.ext (funext fun i => ?_) hB
  rcases lt_or_ge (i : ℕ) n with hi | hi
  · exact congrFun hx ⟨i, hi⟩
  · exact hP.extCluster_eq_of_le hmn t t' hi

omit [Field F] in
/-- A seed is determined by its frozen variables and the data it gives to the two blocks. -/
private theorem SeedData.eq_of_blockMatch (hmn : n ≤ m) {S S' : SeedData F m n} (J : Finset (Fin n))
    (hJ : BlockMatch hmn S J (S'.freeze hmn J)) (hI : BlockMatch hmn S Jᶜ (S'.freeze hmn Jᶜ))
    (hfr : ∀ i : Fin m, n ≤ (i : ℕ) → S.extCluster i = S'.extCluster i) : S = S' := by
  have key : ∀ (L : Finset (Fin n)),
      BlockMatch hmn S L (S'.freeze hmn L) →
      ∀ a : Fin n, a ∉ L → S.extCluster (Fin.castLE hmn a) = S'.extCluster (Fin.castLE hmn a) ∧
        ∀ i, S.extExchangeMatrix i a = S'.extExchangeMatrix i a := by
    intro L hL a ha
    obtain ⟨q, rfl⟩ := exists_freezingMap_col_eq hmn L (sub_card_le_of_le hmn L) ha
    refine ⟨?_, fun i => ?_⟩
    · simpa only [cluster, SeedData.freeze_extCluster, Function.comp_apply,
        freezingFun_castLE] using congrFun hL.2 q
    · obtain ⟨p, rfl⟩ := freezingMap_surjective hmn L i
      exact congrFun (congrFun hL.1 p) q
  have key' : ∀ a : Fin n,
      S.extCluster (Fin.castLE hmn a) = S'.extCluster (Fin.castLE hmn a) ∧
        ∀ i, S.extExchangeMatrix i a = S'.extExchangeMatrix i a := by
    intro a
    by_cases ha : a ∈ J
    · exact key Jᶜ hI a (by simpa using ha)
    · exact key J hJ a ha
  refine SeedData.ext (funext fun i => ?_) (Matrix.ext fun i a => (key' a).2 i)
  rcases lt_or_ge (i : ℕ) n with hi | hi
  · exact (key' ⟨i, hi⟩).1
  · exact hfr i hi

omit [Field F] in
/-- The cluster variables of a seed are those of the seeds its two blocks are read off from. -/
theorem BlockMatch.clusterVariables_eq_union {hmn : n ≤ m} {S : SeedData F m n}
    {J : Finset (Fin n)} {S' : SeedData F m (n - J.card)} {S'' : SeedData F m (n - Jᶜ.card)}
    (h : BlockMatch hmn S J S') (h' : BlockMatch hmn S Jᶜ S'') :
    clusterVariables hmn S =
      clusterVariables (sub_card_le_of_le hmn J) S' ∪
        clusterVariables (sub_card_le_of_le hmn Jᶜ) S'' := by
  ext x
  simp only [clusterVariables, Set.mem_union, Set.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    by_cases ha : a ∈ J
    · obtain ⟨q, hq⟩ := exists_freezingMap_col_eq hmn Jᶜ (sub_card_le_of_le hmn Jᶜ)
        (by simpa using ha)
      exact Or.inr ⟨q, by rw [h'.cluster_apply, hq]; rfl⟩
    · obtain ⟨q, hq⟩ := exists_freezingMap_col_eq hmn J (sub_card_le_of_le hmn J) ha
      exact Or.inl ⟨q, by rw [h.cluster_apply, hq]; rfl⟩
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨_, (h.cluster_apply q).symm⟩
    · exact ⟨_, (h'.cluster_apply q).symm⟩

/-- **(a), first half**: if `Σ(t₀)` is split by `(Jᶜ, J)` and the block patterns pass through
the frozen seeds of `Σ(t₀)`, then every `Σ(t)` is split, and its two blocks are read off from
seeds of the block patterns. -/
private theorem IsSeedPattern.exists_blockMatch_of_isSplitBy (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    {J : Finset (Fin n)} (hsplit : IsSplitBy hmn (P t₀).extExchangeMatrix J)
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    (hPI : IsSeedPattern K (sub_card_le_of_le hmn J) PI) {uI : RegularTree (n - J.card)}
    (huI : PI uI = (P t₀).freeze hmn J)
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (hPJ : IsSeedPattern K (sub_card_le_of_le hmn Jᶜ) PJ) {uJ : RegularTree (n - Jᶜ.card)}
    (huJ : PJ uJ = (P t₀).freeze hmn Jᶜ) (t : RegularTree n) :
    IsSplitBy hmn (P t).extExchangeMatrix J ∧
      ∃ u w, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w) := by
  obtain ⟨s, hs⟩ := hP.exists_seedMutationSeq_eq hmn t₀ t
  rw [hs]
  obtain ⟨r, hr⟩ := (blockAgree_freeze hmn (P t₀) J).exists_seedMutationSeq hsplit s
  obtain ⟨r', hr'⟩ := (blockAgree_freeze hmn (P t₀) Jᶜ).exists_seedMutationSeq
    (isSplitBy_compl_iff.2 hsplit) s
  obtain ⟨u, hu⟩ := hPI.seedMutationSeq_mem_range (sub_card_le_of_le hmn J) uI r
  obtain ⟨w, hw⟩ := hPJ.seedMutationSeq_mem_range (sub_card_le_of_le hmn Jᶜ) uJ r'
  rw [huI] at hu
  rw [huJ] at hw
  exact ⟨hsplit.seedMutationSeq hmn s, u, w, hu ▸ hr.blockMatch, hw ▸ hr'.blockMatch⟩

/-- **(a), second half**: under the assumptions of `exists_blockMatch_of_isSplitBy`, every pair
of seeds of the two block patterns is read off from one seed `Σ(t)`. -/
private theorem IsSeedPattern.exists_blockMatch_pair (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    {J : Finset (Fin n)} (hsplit : IsSplitBy hmn (P t₀).extExchangeMatrix J)
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    (hPI : IsSeedPattern K (sub_card_le_of_le hmn J) PI) {uI : RegularTree (n - J.card)}
    (huI : PI uI = (P t₀).freeze hmn J)
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (hPJ : IsSeedPattern K (sub_card_le_of_le hmn Jᶜ) PJ) {uJ : RegularTree (n - Jᶜ.card)}
    (huJ : PJ uJ = (P t₀).freeze hmn Jᶜ) (u : RegularTree (n - J.card))
    (w : RegularTree (n - Jᶜ.card)) :
    ∃ t, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w) := by
  set hJ' := sub_card_le_of_le hmn J
  set hI' := sub_card_le_of_le hmn Jᶜ
  have hsplitc : IsSplitBy hmn (P t₀).extExchangeMatrix Jᶜ := isSplitBy_compl_iff.2 hsplit
  obtain ⟨r, hr⟩ := hPI.exists_seedMutationSeq_eq hJ' uI u
  obtain ⟨r', hr'⟩ := hPJ.exists_seedMutationSeq_eq hI' uJ w
  obtain ⟨t, ht⟩ := hP.seedMutationSeq_mem_range hmn t₀
    (r.map ((freezingMap hmn J).col hJ') ++ r'.map ((freezingMap hmn Jᶜ).col hI'))
  refine ⟨t, ?_, ?_⟩
  · rw [hr, huI, ht, seedMutationSeq_append]
    refine (((blockAgree_freeze hmn (P t₀) J).seedMutationSeq_map_col hsplit r
      ).seedMutationSeq_of_forall_mem (hsplit.seedMutationSeq hmn _) ?_).blockMatch
    intro k hk
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hk
    simpa using freezingMap_col_notMem hmn Jᶜ hI' q
  · rw [hr', huJ, ht, seedMutationSeq_append]
    refine ((((blockAgree_freeze hmn (P t₀) Jᶜ).seedMutationSeq_of_forall_mem hsplitc
      ?_).seedMutationSeq_map_col (hsplitc.seedMutationSeq hmn _) r')).blockMatch
    intro k hk
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hk
    simpa using freezingMap_col_notMem hmn J hJ' q

omit [Field F] in
/-- If the blocks of every seed of `Σ` are read off from seeds of `Π_I` and `Π_J`, and every
pair of such seeds arises, then `𝒳(Σ) = 𝒳(Π_I) ∪ 𝒳(Π_J)`. -/
private theorem patternClusterVariables_eq_union_of_blockMatch (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} {J : Finset (Fin n)}
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (h₁ : ∀ t, ∃ u w, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w))
    (h₂ : ∀ u w, ∃ t, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w)) :
    patternClusterVariables hmn P =
      patternClusterVariables (sub_card_le_of_le hmn J) PI ∪
        patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ := by
  set hJ' := sub_card_le_of_le hmn J
  set hI' := sub_card_le_of_le hmn Jᶜ
  apply subset_antisymm
  · refine Set.iUnion_subset fun t => ?_
    obtain ⟨u, w, h, h'⟩ := h₁ t
    rw [h.clusterVariables_eq_union h']
    exact Set.union_subset_union (Set.subset_iUnion (fun u => clusterVariables hJ' (PI u)) u)
      (Set.subset_iUnion (fun w => clusterVariables hI' (PJ w)) w)
  · refine Set.union_subset (Set.iUnion_subset fun u => ?_) (Set.iUnion_subset fun w => ?_)
    · obtain ⟨t, h, h'⟩ := h₂ u .root
      exact (h.clusterVariables_eq_union h' ▸ Set.subset_union_left).trans
        (Set.subset_iUnion (fun t => clusterVariables hmn (P t)) t)
    · obtain ⟨t, h, h'⟩ := h₂ .root w
      exact (h.clusterVariables_eq_union h' ▸ Set.subset_union_right).trans
        (Set.subset_iUnion (fun t => clusterVariables hmn (P t)) t)

omit [Field F] in
/-- If every pair of seeds of `Π_I` and `Π_J` is read off from one seed of `Σ`, whose extended
clusters are injective, then `𝒳(Π_I)` and `𝒳(Π_J)` are disjoint. -/
private theorem disjoint_patternClusterVariables_of_blockMatch (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : ∀ t, Function.Injective (P t).extCluster)
    {J : Finset (Fin n)} {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (h₂ : ∀ u w, ∃ t, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w)) :
    Disjoint (patternClusterVariables (sub_card_le_of_le hmn J) PI)
      (patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ) := by
  refine Set.disjoint_left.2 fun v hv hv' => ?_
  simp only [patternClusterVariables, Set.mem_iUnion, clusterVariables, Set.mem_range] at hv hv'
  obtain ⟨u, q, rfl⟩ := hv
  obtain ⟨w, q', hq'⟩ := hv'
  obtain ⟨t, h, h'⟩ := h₂ u w
  rw [h.cluster_apply, h'.cluster_apply] at hq'
  have hq := freezingMap_col_notMem hmn Jᶜ (sub_card_le_of_le hmn Jᶜ) q'
  rw [Fin.castLE_injective hmn (hP t hq'), Finset.mem_compl, not_not] at hq
  exact freezingMap_col_notMem hmn J (sub_card_le_of_le hmn J) q hq

omit [Field F] in
/-- Under the assumptions of `patternClusterVariables_eq_union_of_blockMatch`, the map
`C ↦ (C ∩ 𝒳(Π_I), C ∩ 𝒳(Π_J))` is a bijection from the clusters of `Σ` onto the pairs of
clusters of `Π_I` and `Π_J`. -/
private theorem bijOn_patternClusters_of_blockMatch (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} {J : Finset (Fin n)}
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (h₁ : ∀ t, ∃ u w, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w))
    (h₂ : ∀ u w, ∃ t, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w))
    (hX : patternClusterVariables hmn P =
      patternClusterVariables (sub_card_le_of_le hmn J) PI ∪
        patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ)
    (hdisj : Disjoint (patternClusterVariables (sub_card_le_of_le hmn J) PI)
      (patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ)) :
    Set.BijOn
      (fun C => (C ∩ patternClusterVariables (sub_card_le_of_le hmn J) PI,
        C ∩ patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ))
      (patternClusters hmn P)
      (patternClusters (sub_card_le_of_le hmn J) PI ×ˢ
        patternClusters (sub_card_le_of_le hmn Jᶜ) PJ) := by
  set hJ' := sub_card_le_of_le hmn J
  set hI' := sub_card_le_of_le hmn Jᶜ
  have hcl : ∀ t u w, BlockMatch hmn (P t) J (PI u) → BlockMatch hmn (P t) Jᶜ (PJ w) →
      clusterVariables hmn (P t) ∩ patternClusterVariables hJ' PI = clusterVariables hJ' (PI u) ∧
        clusterVariables hmn (P t) ∩ patternClusterVariables hI' PJ =
          clusterVariables hI' (PJ w) := by
    intro t u w h h'
    have hA : clusterVariables hJ' (PI u) ⊆ patternClusterVariables hJ' PI :=
      Set.subset_iUnion (fun u => clusterVariables hJ' (PI u)) u
    have hB : clusterVariables hI' (PJ w) ⊆ patternClusterVariables hI' PJ :=
      Set.subset_iUnion (fun w => clusterVariables hI' (PJ w)) w
    rw [h.clusterVariables_eq_union h', Set.union_inter_distrib_right,
      Set.union_inter_distrib_right, Set.inter_eq_left.2 hA, Set.inter_eq_left.2 hB,
      Set.disjoint_iff_inter_eq_empty.1 (hdisj.mono_right hB).symm, Set.union_empty,
      Set.disjoint_iff_inter_eq_empty.1 (hdisj.mono_left hA), Set.empty_union]
    exact ⟨rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨u, w, h, h'⟩ := h₁ t
    obtain ⟨e₁, e₂⟩ := hcl t u w h h'
    exact ⟨⟨u, e₁.symm⟩, ⟨w, e₂.symm⟩⟩
  · rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ htt
    have hsub : ∀ t, clusterVariables hmn (P t) =
        clusterVariables hmn (P t) ∩ patternClusterVariables hJ' PI ∪
          clusterVariables hmn (P t) ∩ patternClusterVariables hI' PJ := fun t => by
      rw [← Set.inter_union_distrib_left, ← hX]
      exact (Set.inter_eq_left.2
        (Set.subset_iUnion (fun t => clusterVariables hmn (P t)) t)).symm
    have e₁ : clusterVariables hmn (P t) ∩ patternClusterVariables hJ' PI =
        clusterVariables hmn (P t') ∩ patternClusterVariables hJ' PI := congrArg Prod.fst htt
    have e₂ : clusterVariables hmn (P t) ∩ patternClusterVariables hI' PJ =
        clusterVariables hmn (P t') ∩ patternClusterVariables hI' PJ := congrArg Prod.snd htt
    change clusterVariables hmn (P t) = clusterVariables hmn (P t')
    rw [hsub t, hsub t', e₁, e₂]
  · rintro ⟨_, _⟩ ⟨⟨u, rfl⟩, ⟨w, rfl⟩⟩
    obtain ⟨t, h, h'⟩ := h₂ u w
    obtain ⟨e₁, e₂⟩ := hcl t u w h h'
    exact ⟨_, ⟨t, rfl⟩, Prod.ext e₁ e₂⟩

/-- **(b)**: under the assumptions of `patternClusterVariables_eq_union_of_blockMatch`, `Σ` is
of finite type exactly when `Π_I` and `Π_J` are. -/
private theorem IsSeedPattern.isFiniteType_iff_of_blockMatch (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {J : Finset (Fin n)}
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    (hPI : IsSeedPattern K (sub_card_le_of_le hmn J) PI)
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (hPJ : IsSeedPattern K (sub_card_le_of_le hmn Jᶜ) PJ)
    (h₁ : ∀ t, ∃ u w, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w))
    (h₂ : ∀ u w, ∃ t, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w)) :
    IsFiniteType P ↔ IsFiniteType PI ∧ IsFiniteType PJ := by
  set hJ' := sub_card_le_of_le hmn J
  set hI' := sub_card_le_of_le hmn Jᶜ
  let gJ := fun S' : SeedData F m (n - J.card) => (S'.extExchangeMatrix, cluster hJ' S')
  let gI := fun S' : SeedData F m (n - Jᶜ.card) => (S'.extExchangeMatrix, cluster hI' S')
  refine ⟨fun hfin => ⟨?_, ?_⟩, fun hfin => ?_⟩
  · refine Set.Finite.of_finite_image (f := gJ)
      ((hfin.image fun S => gJ (S.freeze hmn J)).subset ?_) ?_
    · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      obtain ⟨t, h, -⟩ := h₂ u .root
      exact ⟨P t, ⟨t, rfl⟩, Prod.ext h.1 h.2⟩
    · rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩ huu
      exact hPI.eq_of_extExchangeMatrix_eq_of_cluster_eq hJ' (congrArg Prod.fst huu)
        (congrArg Prod.snd huu)
  · refine Set.Finite.of_finite_image (f := gI)
      ((hfin.image fun S => gI (S.freeze hmn Jᶜ)).subset ?_) ?_
    · rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      obtain ⟨t, -, h⟩ := h₂ .root w
      exact ⟨P t, ⟨t, rfl⟩, Prod.ext h.1 h.2⟩
    · rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ hww
      exact hPJ.eq_of_extExchangeMatrix_eq_of_cluster_eq hI' (congrArg Prod.fst hww)
        (congrArg Prod.snd hww)
  · obtain ⟨hfI, hfJ⟩ := hfin
    refine Set.Finite.of_finite_image (f := fun S => (gJ (S.freeze hmn J), gI (S.freeze hmn Jᶜ)))
      (((hfI.image gJ).prod (hfJ.image gI)).subset ?_) ?_
    · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨u, w, h, h'⟩ := h₁ t
      exact ⟨⟨PI u, ⟨u, rfl⟩, (Prod.ext h.1 h.2).symm⟩, ⟨PJ w, ⟨w, rfl⟩, (Prod.ext h'.1 h'.2).symm⟩⟩
    · rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ htt
      have e₁ := congrArg Prod.fst htt
      have e₂ := congrArg Prod.snd htt
      exact SeedData.eq_of_blockMatch hmn J ⟨congrArg Prod.fst e₁, congrArg Prod.snd e₁⟩
        ⟨congrArg Prod.fst e₂, congrArg Prod.snd e₂⟩ fun i hi => hP.extCluster_eq_of_le hmn t t' hi

/-- `IsSeedPattern.blockSeeds` without the assumption that the two blocks are nonempty: an empty
block gives a pattern of rank `0`, with a single seed. -/
theorem IsSeedPattern.blockSeeds_of_isSplitBy (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    {J : Finset (Fin n)} (hsplit : IsSplitBy hmn (P t₀).extExchangeMatrix J)
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    (hPI : IsSeedPattern K (sub_card_le_of_le hmn J) PI) {uI : RegularTree (n - J.card)}
    (huI : PI uI = (P t₀).freeze hmn J)
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (hPJ : IsSeedPattern K (sub_card_le_of_le hmn Jᶜ) PJ) {uJ : RegularTree (n - Jᶜ.card)}
    (huJ : PJ uJ = (P t₀).freeze hmn Jᶜ) :
    ((∀ t, IsSplitBy hmn (P t).extExchangeMatrix J ∧
        ∃ u w, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w)) ∧
      ∀ u w, ∃ t, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w)) ∧
    (IsFiniteType P ↔ IsFiniteType PI ∧ IsFiniteType PJ) ∧
    (patternClusterVariables hmn P =
        patternClusterVariables (sub_card_le_of_le hmn J) PI ∪
          patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ ∧
      Disjoint (patternClusterVariables (sub_card_le_of_le hmn J) PI)
        (patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ) ∧
      Set.BijOn
        (fun C => (C ∩ patternClusterVariables (sub_card_le_of_le hmn J) PI,
          C ∩ patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ))
        (patternClusters hmn P)
        (patternClusters (sub_card_le_of_le hmn J) PI ×ˢ
          patternClusters (sub_card_le_of_le hmn Jᶜ) PJ)) := by
  have ha₁ := hP.exists_blockMatch_of_isSplitBy hmn hsplit hPI huI hPJ huJ
  have h₁ t := (ha₁ t).2
  have h₂ := hP.exists_blockMatch_pair hmn hsplit hPI huI hPJ huJ
  have hX := patternClusterVariables_eq_union_of_blockMatch hmn h₁ h₂
  have hdisj := disjoint_patternClusterVariables_of_blockMatch hmn
    (fun t => (hP.1 t).1.1.injective) h₂
  exact ⟨⟨ha₁, h₂⟩, hP.isFiniteType_iff_of_blockMatch hmn hPI hPJ h₁ h₂, hX, hdisj,
    bijOn_patternClusters_of_blockMatch hmn h₁ h₂ hX hdisj⟩

/-- **Seeds of a pattern with a split exchange matrix.** Let the matrix of `Σ(t₀)` be split by
`(I, J)`, `I = Jᶜ`, with `I` and `J` nonempty, and let `Π_I`, `Π_J` be seed patterns through
`Fr_J(Σ(t₀))` and `Fr_I(Σ(t₀))`. Then:

* (a) every `Σ(t)` has a matrix split by `(I, J)`, its `I`-part is read off from some `Π_I(u)`
  and its `J`-part from some `Π_J(w)`, and every pair `(u, w)` arises from some `t`;
* (b) `Σ` is of finite type if and only if `Π_I` and `Π_J` are;
* (c) `𝒳(Σ)` is the disjoint union of `𝒳(Π_I)` and `𝒳(Π_J)`, and `C ↦ (C ∩ 𝒳(Π_I), C ∩ 𝒳(Π_J))`
  is a bijection from the clusters of `Σ` onto the pairs of a cluster of `Π_I` and a cluster of
  `Π_J`. -/
@[cluster_algebras "lem_block_seeds"]
theorem IsSeedPattern.blockSeeds (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    {J : Finset (Fin n)} (_hJ : J.Nonempty) (_hI : Jᶜ.Nonempty)
    (hsplit : IsSplitBy hmn (P t₀).extExchangeMatrix J)
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)}
    (hPI : IsSeedPattern K (sub_card_le_of_le hmn J) PI) {uI : RegularTree (n - J.card)}
    (huI : PI uI = (P t₀).freeze hmn J)
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    (hPJ : IsSeedPattern K (sub_card_le_of_le hmn Jᶜ) PJ) {uJ : RegularTree (n - Jᶜ.card)}
    (huJ : PJ uJ = (P t₀).freeze hmn Jᶜ) :
    ((∀ t, IsSplitBy hmn (P t).extExchangeMatrix J ∧
        ∃ u w, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w)) ∧
      ∀ u w, ∃ t, BlockMatch hmn (P t) J (PI u) ∧ BlockMatch hmn (P t) Jᶜ (PJ w)) ∧
    (IsFiniteType P ↔ IsFiniteType PI ∧ IsFiniteType PJ) ∧
    (patternClusterVariables hmn P =
        patternClusterVariables (sub_card_le_of_le hmn J) PI ∪
          patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ ∧
      Disjoint (patternClusterVariables (sub_card_le_of_le hmn J) PI)
        (patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ) ∧
      Set.BijOn
        (fun C => (C ∩ patternClusterVariables (sub_card_le_of_le hmn J) PI,
          C ∩ patternClusterVariables (sub_card_le_of_le hmn Jᶜ) PJ))
        (patternClusters hmn P)
        (patternClusters (sub_card_le_of_le hmn J) PI ×ˢ
          patternClusters (sub_card_le_of_le hmn Jᶜ) PJ)) :=
  hP.blockSeeds_of_isSplitBy hmn hsplit hPI huI hPJ huJ

/-- The principal part of a frozen matrix `Fr_J(B̃)` is the principal submatrix `B_{Jᶜ}` of the
principal part of `B̃`, with `Jᶜ` listed in increasing order. -/
private theorem principalPart_matrixFreeze {R : Type*} (hmn : n ≤ m) (J : Finset (Fin n))
    (B : Matrix (Fin m) (Fin n) R) :
    principalPart (sub_card_le_of_le hmn J) (matrixFreeze hmn J B) =
      (principalPart hmn B).submatrix (Jᶜ.orderEmbOfFin (card_compl_eq_sub_card J))
        (Jᶜ.orderEmbOfFin (card_compl_eq_sub_card J)) := by
  ext p q
  simp only [principalPart, Matrix.submatrix_apply, id, matrixFreeze_apply]
  rw [freezingFun_of_lt hmn J (by simp)]
  rfl

/-- The Cartan counterpart commutes with taking the submatrix along an injective map. -/
private theorem cartanCounterpart_submatrix {k : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    {e : Fin k → Fin n} (he : Function.Injective e) :
    cartanCounterpart (B.submatrix e e) = (cartanCounterpart B).submatrix e e := by
  ext i j
  simp only [cartanCounterpart, Matrix.of_apply, Matrix.submatrix_apply, he.eq_iff]

/-- The increasing enumeration of a finset along any proof that its size is `k` is the
enumeration along `rfl`, up to the cast `Fin k ≃ Fin s.card`. -/
private theorem orderEmbOfFin_eq_orderEmbOfFin_rfl_cast {α : Type*} [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i = s.orderEmbOfFin rfl (Fin.cast h.symm i) := by
  subst h
  rfl

/-- Being of type `X` is invariant under reindexing along a bijection `e : Fin a ≃ Fin b`:
if `M` is of type `X`, so is `(M_{e(i) e(j)})_{i, j}`. -/
theorem IsOfDynkinType.submatrix_equiv {a b : ℕ} {M : Matrix (Fin b) (Fin b) ℤ}
    {Xs : List DynkinSymbol} (h : IsOfDynkinType M Xs) (e : Fin a ≃ Fin b) :
    IsOfDynkinType (M.submatrix e e) Xs :=
  let ⟨σ, hσ⟩ := h
  ⟨e.trans σ, fun _ _ => hσ _ _⟩

omit [Field F] in
/-- **The two blocks have the types of the two blocks of the Cartan counterpart.** If a seed of
`Π_I` is `Fr_J(Σ(t₀))` and the principal submatrix `A(B)_I` of the Cartan counterpart of the
exchange matrix `B` of `Σ(t₀)`, with `I = Jᶜ` listed in increasing order, is of type `X`, then
`Π_I` is of type `X`. Applied to `Jᶜ` it gives the statement for `Π_J`. Neither the split nor
the seed pattern conditions are needed, so they are not assumed. -/
@[cluster_algebras "lem_block_type"]
theorem isPatternOfType_of_freeze (hmn : n ≤ m) {P : RegularTree n → SeedData F m n}
    {t₀ : RegularTree n} {J : Finset (Fin n)}
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)} {uI : RegularTree (n - J.card)}
    (huI : PI uI = (P t₀).freeze hmn J) {Xs : List DynkinSymbol}
    (hX : IsOfDynkinType ((cartanCounterpart (principalPart hmn (P t₀).extExchangeMatrix)).submatrix
      (Jᶜ.orderEmbOfFin rfl) (Jᶜ.orderEmbOfFin rfl)) Xs) :
    IsPatternOfType (sub_card_le_of_le hmn J) PI Xs := by
  refine ⟨uI, ?_⟩
  have he := (Jᶜ.orderEmbOfFin (card_compl_eq_sub_card J)).injective
  rw [huI, SeedData.freeze_extExchangeMatrix, principalPart_matrixFreeze,
    cartanCounterpart_submatrix _ he]
  have he' : ⇑(Jᶜ.orderEmbOfFin (card_compl_eq_sub_card J)) =
      Jᶜ.orderEmbOfFin rfl ∘ Fin.cast (card_compl_eq_sub_card J).symm :=
    funext fun i => orderEmbOfFin_eq_orderEmbOfFin_rfl_cast _ _ i
  rw [he', ← Matrix.submatrix_submatrix]
  exact hX.submatrix_equiv (finCongr (card_compl_eq_sub_card J).symm)

/-! ### Decomposable types and finite type -/

/-- **Freezing a labeled seed gives a labeled seed** in the same field: freezing only reorders
the extended cluster. -/
private theorem IsLabeledSeed.freeze (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (J : Finset (Fin n)) :
    IsLabeledSeed K (sub_card_le_of_le hmn J) (S.freeze hmn J) := by
  refine ⟨⟨hS.1.1.comp _ (freezingFun_injective hmn J), ?_⟩,
    hS.2.matrixReindex hmn (sub_card_le_of_le hmn J) (freezingMap hmn J)⟩
  rw [SeedData.freeze_extCluster, (freezingFun_bijective hmn J).2.range_comp]
  exact hS.1.2

variable (K) in
/-- A pattern of rank `a` is a pattern of rank `b` when `a = b`, with the same properties. -/
private theorem exists_pattern_rank_cast {a b : ℕ} (h : a = b) (ha : a ≤ m)
    (P : RegularTree a → SeedData F m a) :
    ∃ (hb : b ≤ m) (Q : RegularTree b → SeedData F m b),
      (IsSeedPattern K ha P → IsSeedPattern K hb Q) ∧
      (∀ Xs, IsPatternOfType ha P Xs → IsPatternOfType hb Q Xs) ∧
      (IsFiniteType P ↔ IsFiniteType Q) ∧
      patternClusterVariables ha P = patternClusterVariables hb Q ∧
      patternClusters ha P = patternClusters hb Q := by
  subst h
  exact ⟨ha, P, id, fun _ => id, Iff.rfl, rfl, rfl⟩

/-- A block of a bijection `σ : [0, n) ≃ [0, N)`: the preimage `S` of the image of an embedding
`g : [0, c) ↪ [0, N)`, listed in increasing order, is carried by `σ` onto that image through a
bijection `[0, |S|) ≃ [0, c)`. -/
private theorem exists_equiv_of_mem_iff_mem_range {N c : ℕ} (σ : Fin n ≃ Fin N) (g : Fin c ↪ Fin N)
    (S : Finset (Fin n)) (hS : ∀ i, i ∈ S ↔ σ i ∈ Set.range g) :
    ∃ τ : Fin S.card ≃ Fin c, ∀ i, σ (S.orderEmbOfFin rfl i) = g (τ i) := by
  refine ⟨(S.orderIsoOfFin rfl).toEquiv.trans
    ((σ.subtypeEquiv hS).trans (Equiv.ofInjective g g.injective).symm), fun i => ?_⟩
  simp only [Equiv.trans_apply, Equiv.apply_ofInjective_symm, Equiv.subtypeEquiv_apply]
  exact congrArg σ (S.coe_orderIsoOfFin_apply rfl i).symm

/-- The diagonal block `C(X)` of `C(X, X², …)`. -/
private theorem listCartan_cons_castAdd_castAdd (X : DynkinSymbol) (Xs : List DynkinSymbol)
    (a b : Fin X.rank) :
    DynkinSymbol.listCartan (X :: Xs) (Fin.castAdd _ a) (Fin.castAdd _ b) = X.cartan a b := by
  simp [DynkinSymbol.listCartan, finSumFinEquiv_symm_apply_castAdd]

/-- The diagonal block `C(X², …)` of `C(X, X², …)`. -/
private theorem listCartan_cons_natAdd_natAdd (X : DynkinSymbol) (Xs : List DynkinSymbol)
    (a b : Fin (DynkinSymbol.listRank Xs)) :
    DynkinSymbol.listCartan (X :: Xs) (Fin.natAdd _ a) (Fin.natAdd _ b) =
      DynkinSymbol.listCartan Xs a b := by
  simp [DynkinSymbol.listCartan, finSumFinEquiv_symm_apply_natAdd]

/-- The off-diagonal blocks of `C(X, X², …)` vanish. -/
private theorem listCartan_cons_eq_zero (X : DynkinSymbol) (Xs : List DynkinSymbol)
    {k l : Fin (DynkinSymbol.listRank (X :: Xs))} (hk : (k : ℕ) < X.rank)
    (hl : X.rank ≤ (l : ℕ)) :
    DynkinSymbol.listCartan (X :: Xs) k l = 0 ∧ DynkinSymbol.listCartan (X :: Xs) l k = 0 := by
  induction k using Fin.addCases with
  | right a => simp at hk
  | left a =>
    induction l using Fin.addCases with
    | left b =>
      simp at hl
      omega
    | right b =>
      simp only [DynkinSymbol.listCartan, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, and_self]

omit [Field F] in
/-- A seed pattern of rank `0` is of finite type, with no cluster variables and the one empty
cluster. -/
private theorem isFiniteType_and_patternClusters_of_rankZero (hmn : 0 ≤ m)
    (P : RegularTree 0 → SeedData F m 0) :
    IsFiniteType P ∧ patternClusterVariables hmn P = ∅ ∧ patternClusters hmn P = {∅} := by
  have hroot : ∀ t : RegularTree 0, t = .root := by
    rintro ⟨_ | ⟨a, _⟩, _⟩
    · rfl
    · exact a.elim0
  have hcv : ∀ t, clusterVariables hmn (P t) = ∅ := fun t => by
    simp [clusterVariables, Set.range_eq_empty]
  refine ⟨(Set.finite_singleton (P .root)).subset ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    rw [hroot t]
    rfl
  · simp [patternClusterVariables, hcv]
  · haveI : Nonempty (RegularTree 0) := ⟨.root⟩
    rw [patternClusters, funext hcv, Set.range_const]

/-- If `C(X, X², …)` is the Cartan counterpart of the principal part of `B` read through `σ`, then
`B` is split by `(Jᶜ, J)` for the set `J` of indices that `σ` sends past the block of `X`. -/
private theorem isSplitBy_of_cons (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) ℤ} {X : DynkinSymbol}
    {Xs : List DynkinSymbol} {σ : Fin n ≃ Fin (DynkinSymbol.listRank (X :: Xs))}
    (hσ : ∀ i j, cartanCounterpart (principalPart hmn B) i j =
      DynkinSymbol.listCartan (X :: Xs) (σ i) (σ j))
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ X.rank ≤ (σ i : ℕ)) : IsSplitBy hmn B J := by
  intro i j hi hj
  rw [hJ, not_le] at hi
  rw [hJ] at hj
  have hij : i ≠ j := by
    rintro rfl
    omega
  obtain ⟨h₁, h₂⟩ := listCartan_cons_eq_zero X Xs hi hj
  have e₁ := (hσ i j).trans h₁
  have e₂ := (hσ j i).trans h₂
  simp only [cartanCounterpart, Matrix.of_apply, if_neg hij, if_neg (Ne.symm hij),
    neg_eq_zero, abs_eq_zero] at e₁ e₂
  exact ⟨e₁, e₂⟩

omit [Field F] in
/-- Under the assumptions of `isSplitBy_of_cons`, a pattern through `Fr_J(Σ(t₀))` is of type
`X`. -/
private theorem isPatternOfType_freeze_of_cons_left (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} {t₀ : RegularTree n} {X : DynkinSymbol}
    {Xs : List DynkinSymbol} {σ : Fin n ≃ Fin (DynkinSymbol.listRank (X :: Xs))}
    (hσ : ∀ i j, cartanCounterpart (principalPart hmn (P t₀).extExchangeMatrix) i j =
      DynkinSymbol.listCartan (X :: Xs) (σ i) (σ j))
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ X.rank ≤ (σ i : ℕ))
    {PI : RegularTree (n - J.card) → SeedData F m (n - J.card)} {uI : RegularTree (n - J.card)}
    (huI : PI uI = (P t₀).freeze hmn J) : IsPatternOfType (sub_card_le_of_le hmn J) PI [X] := by
  obtain ⟨τ, hτ⟩ := exists_equiv_of_mem_iff_mem_range σ (Fin.castAddEmb _) Jᶜ fun i => by
    rw [Finset.mem_compl, hJ, not_le]
    exact ⟨fun h => ⟨⟨σ i, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.isLt⟩
  refine isPatternOfType_of_freeze hmn huI
    ⟨τ.trans (finCongr (by simp [DynkinSymbol.listRank])), fun i j => ?_⟩
  have e : ∀ i, (finCongr (by simp [DynkinSymbol.listRank]) (τ i) :
      Fin (DynkinSymbol.listRank [X])) = Fin.castAdd 0 (τ i) := fun i => rfl
  rw [Matrix.submatrix_apply, hσ, hτ, hτ, Equiv.trans_apply, Equiv.trans_apply, e, e]
  exact (listCartan_cons_castAdd_castAdd X Xs _ _).trans
    (listCartan_cons_castAdd_castAdd X [] _ _).symm

omit [Field F] in
/-- Under the assumptions of `isSplitBy_of_cons`, a pattern through `Fr_{Jᶜ}(Σ(t₀))` is of type
`(X², …)`. -/
private theorem isPatternOfType_freeze_of_cons_right (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} {t₀ : RegularTree n} {X : DynkinSymbol}
    {Xs : List DynkinSymbol} {σ : Fin n ≃ Fin (DynkinSymbol.listRank (X :: Xs))}
    (hσ : ∀ i j, cartanCounterpart (principalPart hmn (P t₀).extExchangeMatrix) i j =
      DynkinSymbol.listCartan (X :: Xs) (σ i) (σ j))
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ X.rank ≤ (σ i : ℕ))
    {PJ : RegularTree (n - Jᶜ.card) → SeedData F m (n - Jᶜ.card)}
    {uJ : RegularTree (n - Jᶜ.card)} (huJ : PJ uJ = (P t₀).freeze hmn Jᶜ) :
    IsPatternOfType (sub_card_le_of_le hmn Jᶜ) PJ Xs := by
  obtain ⟨τ', hτ'⟩ := exists_equiv_of_mem_iff_mem_range σ (Fin.natAddEmb X.rank) Jᶜᶜ fun i => by
    rw [compl_compl, hJ]
    refine ⟨fun h => ⟨⟨σ i - X.rank, ?_⟩, Fin.ext ?_⟩, fun ⟨a, ha⟩ => ?_⟩
    · have : (σ i : ℕ) < X.rank + DynkinSymbol.listRank Xs := (σ i).isLt
      omega
    · change X.rank + ((σ i : ℕ) - X.rank) = σ i
      omega
    · rw [← ha]
      exact Nat.le_add_right _ _
  refine isPatternOfType_of_freeze hmn huJ ⟨τ', fun i j => ?_⟩
  rw [Matrix.submatrix_apply, hσ, hτ', hτ']
  exact listCartan_cons_natAdd_natAdd X Xs _ _

/-- **Decomposable types.** A seed pattern `Σ` of type `X = (X¹, …, X^r)`, for any `r ≥ 0`, has
seed patterns `Π_s` (here `Q s`) of type `X^s`, `s ∈ [1, r]`, in the same field and with the same
number of rows, such that `Σ` is of finite type if and only if every `Π_s` is, and then
`|𝒳(Σ)| = ∑ₛ |𝒳(Π_s)|` and the number of clusters of `Σ` is the product of those of the
`Π_s`. -/
@[cluster_algebras "lem_decomposable_counts"]
theorem IsSeedPattern.exists_blocks_of_isPatternOfType [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {Xs : List DynkinSymbol}
    (hX : IsPatternOfType hmn P Xs) :
    ∃ (hle : ∀ s : Fin Xs.length, (Xs.get s).rank ≤ m)
      (Q : (s : Fin Xs.length) → RegularTree (Xs.get s).rank → SeedData F m (Xs.get s).rank),
      (∀ s, IsSeedPattern K (hle s) (Q s) ∧ IsPatternOfType (hle s) (Q s) [Xs.get s]) ∧
      (IsFiniteType P ↔ ∀ s, IsFiniteType (Q s)) ∧
      (IsFiniteType P →
        (patternClusterVariables hmn P).encard =
            ∑ s, (patternClusterVariables (hle s) (Q s)).encard ∧
          (patternClusters hmn P).encard = ∏ s, (patternClusters (hle s) (Q s)).encard) := by
  classical
  induction Xs generalizing n with
  | nil =>
    obtain ⟨t₀, σ, -⟩ := hX
    have hn : n = 0 := by simpa [DynkinSymbol.listRank] using Fintype.card_congr σ
    subst hn
    obtain ⟨hfin, hcv, hcl⟩ := isFiniteType_and_patternClusters_of_rankZero hmn P
    refine ⟨fun s => s.elim0, fun s => s.elim0, fun s => s.elim0,
      iff_of_true hfin fun s => s.elim0, fun _ => ?_⟩
    simp [hcv, hcl]
  | cons X Xs ih =>
    obtain ⟨t₀, σ, hσ⟩ := hX
    set J : Finset (Fin n) := Finset.univ.filter fun i => X.rank ≤ (σ i : ℕ)
    have hmemJ : ∀ i, i ∈ J ↔ X.rank ≤ (σ i : ℕ) := fun i => by simp [J]
    have hfreeze := fun L => IsLabeledSeed.freeze hmn (hP.1 t₀) L
    obtain ⟨PI, hPI, huI⟩ := exists_isSeedPattern (sub_card_le_of_le hmn J) .root (hfreeze J)
    obtain ⟨PJ, hPJ, huJ⟩ := exists_isSeedPattern (sub_card_le_of_le hmn Jᶜ) .root (hfreeze Jᶜ)
    have hTI := isPatternOfType_freeze_of_cons_left hmn hσ hmemJ huI
    obtain ⟨hle', Q', hQ', hfinQ', hcountQ'⟩ :=
      ih (sub_card_le_of_le hmn Jᶜ) hPJ (isPatternOfType_freeze_of_cons_right hmn hσ hmemJ huJ)
    obtain ⟨-, hfin, hXeq, hdisj, hbij⟩ :=
      hP.blockSeeds_of_isSplitBy hmn (isSplitBy_of_cons hmn hσ hmemJ) hPI huI hPJ huJ
    have hrank : n - J.card = ((X :: Xs).get 0).rank := by
      obtain ⟨-, σ', -⟩ := hTI
      simpa [DynkinSymbol.listRank] using Fintype.card_congr σ'
    obtain ⟨hb, Q₀, hQ₀p, hQ₀t, hQ₀f, hQ₀x, hQ₀c⟩ :=
      exists_pattern_rank_cast K hrank (sub_card_le_of_le hmn J) PI
    have hX0 : [(X :: Xs).get 0] = [X] := by rw [List.get_cons_zero]
    refine ⟨Fin.cons hb hle', Fin.cons Q₀ Q',
      Fin.cons ⟨hQ₀p hPI, hX0 ▸ hQ₀t _ hTI⟩ hQ', ?_, ?_⟩
    · change _ ↔ ∀ s : Fin (Xs.length + 1), _
      rw [hfin, Fin.forall_fin_succ, hQ₀f, hfinQ']
      rfl
    · intro hP'
      obtain ⟨hfI, hfJ⟩ := hfin.1 hP'
      obtain ⟨hcvQ', hclQ'⟩ := hcountQ' hfJ
      constructor
      · change _ = ∑ s : Fin (Xs.length + 1), _
        rw [hXeq, Set.encard_union_eq hdisj, hcvQ', Fin.sum_univ_succ, hQ₀x]
        rfl
      · change _ = ∏ s : Fin (Xs.length + 1), _
        rw [← hbij.injOn.encard_image, hbij.image_eq, Set.encard_prod, hclQ',
          Fin.prod_univ_succ, hQ₀c]
        rfl

/-- A seed pattern of type `X` for a single Dynkin symbol `X` is of finite type: according to
the symbol, by the finite type theorem for that type. -/
private theorem IsSeedPattern.isFiniteType_of_isPatternOfType_singleton [CharZero K]
    {X : DynkinSymbol} (hle : X.rank ≤ m) {Q : RegularTree X.rank → SeedData F m X.rank}
    (hQ : IsSeedPattern K hle Q) (hX : IsPatternOfType hle Q [X]) : IsFiniteType Q := by
  cases X with
  | A k hk => exact hQ.isFiniteType_of_typeA hk hle hX
  | B k hk => exact hQ.isFiniteType_of_isPatternOfType_B hle hk hX
  | C k hk => exact hQ.isFiniteType_of_isPatternOfType_C hle hk hX
  | D k hk => exact hQ.isFiniteType_of_isPatternOfType_D hk hle hX
  | E k hk => exact hQ.isFiniteType_of_isPatternOfType_E hk hle hX
  | F₄ => exact hQ.isFiniteType_of_isPatternOfType_F₄ hle hX
  | G₂ => exact hQ.isFiniteType_of_isPatternOfType_G₂ hle hX

/-- **A Cartan counterpart of finite type gives finite type.** The "if" direction of the finite
type classification: if for some vertex `t₀` the Cartan counterpart of the exchange matrix of
`Σ(t₀)` is a Cartan matrix of finite type, then `Σ` is of finite type. -/
@[cluster_algebras "thm_finite_type_if"]
theorem IsSeedPattern.isFiniteType_of_isCartanFiniteType [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) {t₀ : RegularTree n}
    (hA : IsCartanFiniteType (cartanCounterpart (principalPart hmn (P t₀).extExchangeMatrix))) :
    IsFiniteType P := by
  obtain ⟨Xs, hXs⟩ := isOfDynkinType_of_isCartanFiniteType hA
  obtain ⟨hle, Q, hQ, hfin, -⟩ := hP.exists_blocks_of_isPatternOfType hmn ⟨t₀, hXs⟩
  exact hfin.2 fun s =>
    IsSeedPattern.isFiniteType_of_isPatternOfType_singleton (hle s) (hQ s).1 (hQ s).2

/-- The Cartan counterpart of `ε [[0, b], [-c, 0]]`, for `ε = ±1` and `b, c ≥ 0`. -/
private theorem cartanCounterpart_smul_rankTwo {ε b c : ℤ} (hε : ε = 1 ∨ ε = -1) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : cartanCounterpart (ε • !![0, b; -c, 0]) = !![2, -b; -c, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rcases hε with rfl | rfl <;>
    simp [cartanCounterpart, abs_of_nonneg hb, abs_of_nonneg hc]

/-- The matrix `[[2, -b], [-c, 2]]`, for `b, c` both positive or both zero, is a Cartan matrix of
finite type when `bc ≤ 3`: with a symmetrizer `(d₁, d₂)`, `d₁b = d₂c`, the quadratic form of
`DA` has discriminant `4d₁d₂(bc - 4) < 0`. -/
private theorem isCartanFiniteType_rankTwo {b c : ℤ} (hbc : (0 < b ∧ 0 < c) ∨ (b = 0 ∧ c = 0))
    (h3 : b * c ≤ 3) : IsCartanFiniteType !![2, -b; -c, 2] := by
  obtain ⟨d, hd, hpos⟩ : ∃ d : Fin 2 → ℤ, IsSymmetrizer !![2, -b; -c, 2] d ∧ 0 < d 0 * d 1 := by
    rcases hbc with ⟨hb, hc⟩ | ⟨rfl, rfl⟩
    · refine ⟨![c, b], ⟨fun i => by fin_cases i <;> simp [hb, hc], fun i j => ?_⟩,
        by simpa using mul_pos hc hb⟩
      fin_cases i <;> fin_cases j <;> simp <;> ring
    · refine ⟨![1, 1], ⟨fun i => by fin_cases i <;> simp, fun i j => ?_⟩, by simp⟩
      fin_cases i <;> fin_cases j <;> simp
  refine ⟨⟨fun i => by fin_cases i <;> simp, fun i j hij => ?_, d, hd⟩, d, hd, fun v hv => ?_⟩
  · rcases hbc with ⟨hb, hc⟩ | ⟨rfl, rfl⟩ <;>
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  · have hd0 : (0 : ℝ) < d 0 := by exact_mod_cast hd.1 0
    have hd1 : (0 : ℝ) < d 1 := by exact_mod_cast hd.1 1
    have hsym : (d 0 : ℝ) * b = d 1 * c := by
      have := hd.2 0 1
      simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val_zero, mul_neg, neg_inj] at this
      exact_mod_cast (by linarith : d 0 * b = d 1 * c)
    have hbc' : (d 0 : ℝ) * b * (d 1 * c) ≤ 3 * (d 0 * d 1) := by
      have : (b : ℝ) * c ≤ 3 := by exact_mod_cast h3
      nlinarith [mul_pos hd0 hd1]
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal, Matrix.mul_apply, Matrix.of_apply,
      Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_fin_one, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Fin.sum_univ_two, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_ofNat, Int.cast_neg, mul_neg, neg_mul,
      gt_iff_lt]
    rw [← hsym] at hbc' ⊢
    set e : ℝ := d 0 * b
    have hv : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    have key : 2 * d 0 * (v 0 * (d 0 * 2 * v 0 + -(e * v 1)) + v 1 * (-(e * v 0) + d 1 * 2 * v 1))
        = (2 * d 0 * v 0 - e * v 1) ^ 2 + (4 * (d 0 * d 1) - e * e) * v 1 ^ 2 := by ring
    by_cases hv1 : v 1 = 0
    · have hv0 : v 0 ≠ 0 := hv.resolve_right (not_not.2 hv1)
      rw [hv1]
      nlinarith [sq_pos_of_ne_zero hv0]
    · have h1 : 0 < (4 * (d 0 * d 1) - e * e) * v 1 ^ 2 :=
        mul_pos (by nlinarith [mul_pos hd0 hd1]) (by positivity)
      have h2 := sq_nonneg (2 * d 0 * v 0 - e * v 1)
      have hd0' : 0 < 2 * (d 0 : ℝ) := by positivity
      by_contra hneg
      push Not at hneg
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hd0'.le hneg]

/-- **Finite type classification in rank two.** If the exchange matrix of one seed of a
seed pattern of rank two is `ε [[0, b], [-c, 0]]` with `ε = ±1` and integers `b, c` both positive
or both zero, the pattern is of finite type if and only if `bc ≤ 3`. -/
@[cluster_algebras "thm_finite_type_rank_two"]
theorem IsSeedPattern.isFiniteType_iff_of_rankTwo [CharZero K] (hm : 2 ≤ m)
    {P : RegularTree 2 → SeedData F m 2} (hP : IsSeedPattern K hm P) {t₀ : RegularTree 2}
    {ε b c : ℤ} (hε : ε = 1 ∨ ε = -1) (hbc : (0 < b ∧ 0 < c) ∨ (b = 0 ∧ c = 0))
    (hB : principalPart hm (P t₀).extExchangeMatrix = ε • !![0, b; -c, 0]) :
    IsFiniteType P ↔ b * c ≤ 3 := by
  have hb : 0 ≤ b := by rcases hbc with ⟨hb, -⟩ | ⟨rfl, -⟩ <;> omega
  have hc : 0 ≤ c := by rcases hbc with ⟨-, hc⟩ | ⟨-, rfl⟩ <;> omega
  refine ⟨fun hfin => ?_, fun h3 => ?_⟩
  · by_contra h
    rcases hbc with ⟨hb, hc⟩ | ⟨rfl, rfl⟩
    · exact (hP.infinite_patternClusterVariables_of_rankTwo hm t₀ hε hb hc (by omega) hB).2 hfin
    · simp at h
  · refine hP.isFiniteType_of_isCartanFiniteType hm (t₀ := t₀) ?_
    rw [hB, cartanCounterpart_smul_rankTwo hε hb hc]
    exact isCartanFiniteType_rankTwo hbc h3

end ClusterAlgebras
