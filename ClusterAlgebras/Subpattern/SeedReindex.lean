/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Seed
public import ClusterAlgebras.Restriction.Reindexing

/-!
# Reindexing a seed along a reindexing map

FWZ's Section 4.2 freezes mutable variables, restricts seeds to a subset of their indices,
and renumbers. All three are instances of one operation: given a reindexing map `r` from
`(m', n')` to `(m, n)`, the seed `(x̃, B̃)` is pulled back to
`(x̃, B̃)ʳ = ((x_{r(1)}, …, x_{r(m')}), B̃ʳ)` (`ClusterAlgebras.SeedData.reindex`).

Pulling back commutes with mutation in a direction `q` exactly when no variable outside the
image of `r` enters the exchange relation in direction `r(q)`, that is, when `r` is
*closed* for `B̃` (`ClusterAlgebras.ReindexingMap.IsClosedFor`). Closedness survives the
mutations it allows and composition, and under it
`μ_q((x̃, B̃)ʳ) = (μ_{r(q)}(x̃, B̃))ʳ` (`ClusterAlgebras.seedMutation_reindex`), which
generalises FWZ's Lemma 4.2.4 from restricted seeds to closed reindexing maps. Finally a
reindexed labeled seed is a labeled seed in the subfield `K(x_{r(1)}, …, x_{r(m')})`
(`ClusterAlgebras.IsLabeledSeed.reindexAdjoin`).

## Main definitions

* `ClusterAlgebras.SeedData.reindex`: the reindexing `(x̃, B̃)ʳ` of a seed along `r`.
* `ClusterAlgebras.ReindexingMap.IsClosedFor`: `r` is closed for a matrix `B̃`.
* `ClusterAlgebras.SeedData.reindexAdjoin`: `(x̃, B̃)ʳ` as a seed in
  `K(x_{r(1)}, …, x_{r(m')})`.
* `ClusterAlgebras.SeedData.map`: a seed with a function applied to its extended cluster.

## Main results

* `ClusterAlgebras.ReindexingMap.IsClosedFor.matrixMutation`: if `r` is closed for `B̃`,
  it is closed for `μ_{r(q)}(B̃)`.
* `ClusterAlgebras.ReindexingMap.IsClosedFor.comp`: closed reindexing maps compose.
* `ClusterAlgebras.seedMutation_reindex`: reindexing along a closed map commutes with seed
  mutation; `ClusterAlgebras.seedMutationSeq_reindex` is its form for sequences.
* `ClusterAlgebras.IsLabeledSeed.reindexAdjoin`: a reindexed labeled seed is a labeled seed.
* `ClusterAlgebras.seedMutation_map`: a ring homomorphism of fields commutes with seed
  mutation.

## Implementation notes

* Indices are `Fin m`, so the indices `1, …, m` of [FWZ17] are `0, …, m - 1`, and the
  mutable indices are those of value below `n`. The column `q` of the reindexed matrix is sent
  along `r` by `ReindexingMap.col`, and `Fin.castLE h (r.col h' q) = r (Fin.castLE h' q)` holds
  by definition.

* `SeedData.reindex` needs no field structure: it is defined for seeds with entries in an
  arbitrary type.

* `seedMutation_reindex` does not assume `x_{r(q)} ≠ 0`: `seedMutation` is total, division
  being total, and both sides divide by the same element `x_{r(q)}`. The hypothesis that `r` is
  closed makes the exchange monomials of `(x̃, B̃)ʳ` in direction `q` those of `(x̃, B̃)` in
  direction `r(q)`.

* `IsLabeledSeed` does not require `n ≥ 1`, so `IsLabeledSeed.reindexAdjoin` does not assume
  `n' ≥ 1`. The seed in the subfield `F' = K(x_{r(1)}, …, x_{r(m')})` is
  `SeedData.reindexAdjoin`, whose entries are those of `(x̃, B̃)ʳ` read in `F'`
  (`SeedData.map_val_reindexAdjoin`).

* `SeedData.map` and `seedMutation_map` let a seed pattern in a subfield be compared with
  seeds in the ambient field, along the inclusion. They are stated for any map in a
  `RingHomClass`, so that the inclusion `IntermediateField.val` of an intermediate field
  applies directly.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 4–5*][FWZ17]
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n m' n' m'' n'' : ℕ}

/-! ### Reindexing a seed -/

section Reindex

variable {F : Type*}

/-- The **reindexing** `(x̃, B̃)ʳ` of a seed along a reindexing map `r` from `(m', n')` to
`(m, n)`: its extended cluster is `(x_{r(1)}, …, x_{r(m')})` and its extended exchange
matrix is the reindexed matrix `B̃ʳ`. -/
@[cluster_algebras "def_seed_reindexing"]
def SeedData.reindex (h' : n' ≤ m') (S : SeedData F m n) (r : ReindexingMap m' n' m n) :
    SeedData F m' n' where
  extCluster := S.extCluster ∘ r
  extExchangeMatrix := matrixReindex h' S.extExchangeMatrix r

/-- The extended cluster of a reindexed seed. -/
@[simp]
theorem SeedData.reindex_extCluster (h' : n' ≤ m') (S : SeedData F m n)
    (r : ReindexingMap m' n' m n) : (S.reindex h' r).extCluster = S.extCluster ∘ r :=
  rfl

/-- The extended exchange matrix of a reindexed seed. -/
@[simp]
theorem SeedData.reindex_extExchangeMatrix (h' : n' ≤ m') (S : SeedData F m n)
    (r : ReindexingMap m' n' m n) :
    (S.reindex h' r).extExchangeMatrix = matrixReindex h' S.extExchangeMatrix r :=
  rfl

/-- Reindexing along the identity does nothing. -/
@[simp]
theorem SeedData.reindex_id (h : n ≤ m) (S : SeedData F m n) :
    S.reindex h (ReindexingMap.id m n) = S :=
  rfl

/-- **Reindexing twice is reindexing along the composite**: `((x̃, B̃)ʳ)ˢ = (x̃, B̃)^{r ∘ s}`. -/
theorem SeedData.reindex_reindex (h' : n' ≤ m') (h'' : n'' ≤ m'') (S : SeedData F m n)
    (r : ReindexingMap m' n' m n) (s : ReindexingMap m'' n'' m' n') :
    (S.reindex h' r).reindex h'' s = S.reindex h'' (r.comp s) :=
  rfl

end Reindex

/-! ### Closed reindexing maps -/

namespace ReindexingMap

section Closed

variable {R : Type*}

/-- A reindexing map `r` from `(m', n')` to `(m, n)` is **closed for** an `m × n` matrix `B`
when every row `i` with `b_{i r(q)} ≠ 0` for some column `q < n'` lies in the image of `r`.
For a restriction to a set `I` of indices this is FWZ's condition in their Definition
4.2.3: no variable outside `I` occurs in an exchange relation at an index of `I`. -/
@[cluster_algebras "def_reindexing_closed"]
def IsClosedFor [Zero R] (r : ReindexingMap m' n' m n) (h' : n' ≤ m')
    (B : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ q : Fin n', ∀ i : Fin m, B i (r.col h' q) ≠ 0 → i ∈ Set.range r

variable [Zero R] {r : ReindexingMap m' n' m n} {h' : n' ≤ m'} {B : Matrix (Fin m) (Fin n) R}

/-- If `r` is closed for `B`, then the entry of `B` in column `r(q)` is zero at every row
outside the image of `r`. -/
theorem IsClosedFor.eq_zero (hr : r.IsClosedFor h' B) (q : Fin n') {i : Fin m}
    (hi : i ∉ Set.range r) : B i (r.col h' q) = 0 :=
  not_not.1 fun h => hi (hr q i h)

/-- **A surjective reindexing map is closed for every matrix.** -/
theorem isClosedFor_of_surjective (hr : Function.Surjective r) (h' : n' ≤ m')
    (B : Matrix (Fin m) (Fin n) R) : r.IsClosedFor h' B :=
  fun _ i _ => hr i

/-- The identity reindexing map is closed for every matrix. -/
theorem isClosedFor_id (h : n ≤ m) (B : Matrix (Fin m) (Fin n) R) :
    (ReindexingMap.id m n).IsClosedFor h B :=
  isClosedFor_of_surjective Function.surjective_id h B

/-- **Closed reindexing maps compose**: if `r` is closed for `B` and `s` is closed for `Bʳ`,
then `r ∘ s` is closed for `B`. -/
@[cluster_algebras "lem_reindexing_closed_comp"]
theorem IsClosedFor.comp {h'' : n'' ≤ m''} {s : ReindexingMap m'' n'' m' n'}
    (hr : r.IsClosedFor h' B) (hs : s.IsClosedFor h'' (matrixReindex h' B r)) :
    (r.comp s).IsClosedFor h'' B := by
  intro q i hi
  obtain ⟨p, rfl⟩ := hr (s.col h'' q) i hi
  obtain ⟨p'', rfl⟩ := hs q p hi
  exact ⟨p'', rfl⟩

end Closed

section Mutation

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {r : ReindexingMap m' n' m n} {h' : n' ≤ m'} {B : Matrix (Fin m) (Fin n) R}

/-- **Closedness survives mutation**: if `r` is closed for `B`, it is closed for
`μ_{r(q)}(B)` for every `q < n'`. -/
@[cluster_algebras "lem_reindexing_closed_mutation"]
theorem IsClosedFor.matrixMutation (h : n ≤ m) (hr : r.IsClosedFor h' B) (q : Fin n') :
    r.IsClosedFor h' (ClusterAlgebras.matrixMutation h B (r.col h' q)) := by
  intro q' i hi
  by_contra hni
  have hik : i ≠ Fin.castLE h (r.col h' q) := by
    rintro rfl
    exact hni ⟨_, rfl⟩
  apply hi
  by_cases hl : r.col h' q' = r.col h' q
  · rw [matrixMutation_apply_of_eq h B _ (Or.inr hl), hl, hr.eq_zero q hni, neg_zero]
  · rw [matrixMutation_apply_of_eq_zero h B _ hik hl (Or.inl (hr.eq_zero q hni)),
      hr.eq_zero q' hni]

/-- **Closedness survives mutation along a sequence** of directions in the image of `r`. -/
theorem IsClosedFor.matrixMutationList (h : n ≤ m) (hr : r.IsClosedFor h' B)
    (s : List (Fin n')) :
    r.IsClosedFor h' (ClusterAlgebras.matrixMutationList h B (s.map (r.col h'))) := by
  induction s generalizing B with
  | nil => exact hr
  | cons q s ih =>
    rw [List.map_cons, matrixMutationList_cons]
    exact ih (hr.matrixMutation h q)

end Mutation

end ReindexingMap

/-! ### Reindexing commutes with seed mutation -/

section SeedMutation

variable {F : Type*} [Field F]

/-- If `e` is injective and column `k'` of `B'` is column `k` of `B` read along `e`, every row
of `B` outside the image of `e` vanishing in column `k`, then the positive exchange monomial
of `(x ∘ e, B')` in direction `k'` is that of `(x, B)` in direction `k`. -/
theorem exchangeMonomialPos_comp_of_injective {x : Fin m → F} {B : Matrix (Fin m) (Fin n) ℤ}
    {B' : Matrix (Fin m') (Fin n') ℤ} {e : Fin m' → Fin m} (he : Function.Injective e)
    {k : Fin n} {k' : Fin n'} (hB : ∀ p, B' p k' = B (e p) k)
    (h0 : ∀ i ∉ Set.range e, B i k = 0) :
    exchangeMonomialPos (x ∘ e) B' k' = exchangeMonomialPos x B k := by
  rw [exchangeMonomialPos_eq_prod, exchangeMonomialPos_eq_prod]
  refine Fintype.prod_of_injective e he _ _ (fun i hi => ?_) fun p => ?_
  · rw [h0 i hi, Int.toNat_zero, pow_zero]
  · rw [hB, Function.comp_apply]

/-- If `e` is injective and column `k'` of `B'` is column `k` of `B` read along `e`, every row
of `B` outside the image of `e` vanishing in column `k`, then the negative exchange monomial
of `(x ∘ e, B')` in direction `k'` is that of `(x, B)` in direction `k`. -/
theorem exchangeMonomialNeg_comp_of_injective {x : Fin m → F} {B : Matrix (Fin m) (Fin n) ℤ}
    {B' : Matrix (Fin m') (Fin n') ℤ} {e : Fin m' → Fin m} (he : Function.Injective e)
    {k : Fin n} {k' : Fin n'} (hB : ∀ p, B' p k' = B (e p) k)
    (h0 : ∀ i ∉ Set.range e, B i k = 0) :
    exchangeMonomialNeg (x ∘ e) B' k' = exchangeMonomialNeg x B k := by
  rw [exchangeMonomialNeg_eq_prod, exchangeMonomialNeg_eq_prod]
  refine Fintype.prod_of_injective e he _ _ (fun i hi => ?_) fun p => ?_
  · rw [h0 i hi, neg_zero, Int.toNat_zero, pow_zero]
  · rw [hB, Function.comp_apply]

/-- **Passing to a closed reindexing commutes with seed mutation**:
`μ_q((x̃, B̃)ʳ) = (μ_{r(q)}(x̃, B̃))ʳ` when `r` is closed for `B̃`. -/
@[cluster_algebras "lem_seed_mutation_reindex"]
theorem seedMutation_reindex (h : n ≤ m) (h' : n' ≤ m') (S : SeedData F m n)
    {r : ReindexingMap m' n' m n} (hr : r.IsClosedFor h' S.extExchangeMatrix) (q : Fin n') :
    seedMutation h' (S.reindex h' r) q = (seedMutation h S (r.col h' q)).reindex h' r := by
  have h0 : ∀ i ∉ Set.range r, S.extExchangeMatrix i (r.col h' q) = 0 :=
    fun _ => hr.eq_zero q
  refine SeedData.ext ?_ (matrixMutation_matrixReindex h h' _ r q)
  simp only [seedMutation, SeedData.reindex_extCluster, SeedData.reindex_extExchangeMatrix]
  rw [ReindexingMap.castLE_col r h' h, Function.update_comp_eq_of_injective (f := ⇑r) _ r.injective,
    exchangeMonomialPos_comp_of_injective (B' := matrixReindex h' S.extExchangeMatrix r)
      (e := ⇑r) (k' := q) r.injective (fun _ => rfl) h0,
    exchangeMonomialNeg_comp_of_injective (B' := matrixReindex h' S.extExchangeMatrix r)
      (e := ⇑r) (k' := q) r.injective (fun _ => rfl) h0]
  rfl

/-- The extended exchange matrix after mutation along a sequence is the matrix mutated along
that sequence. -/
theorem seedMutationSeq_extExchangeMatrix_eq_matrixMutationList (h : n ≤ m)
    (S : SeedData F m n) (s : List (Fin n)) :
    (seedMutationSeq h S s).extExchangeMatrix = matrixMutationList h S.extExchangeMatrix s := by
  induction s generalizing S with
  | nil => rfl
  | cons k s ih =>
    rw [seedMutationSeq_cons, ih, matrixMutationList_cons]
    rfl

/-- **Closedness survives seed mutation along a sequence** of directions in the image of
`r`. -/
theorem ReindexingMap.IsClosedFor.seedMutationSeq (h : n ≤ m) {h' : n' ≤ m'}
    {S : SeedData F m n} {r : ReindexingMap m' n' m n}
    (hr : r.IsClosedFor h' S.extExchangeMatrix) (s : List (Fin n')) :
    r.IsClosedFor h'
      (ClusterAlgebras.seedMutationSeq h S (s.map (r.col h'))).extExchangeMatrix := by
  rw [seedMutationSeq_extExchangeMatrix_eq_matrixMutationList]
  exact hr.matrixMutationList h s

/-- **Passing to a closed reindexing commutes with mutation along a sequence**:
`μ_s((x̃, B̃)ʳ) = (μ_{r(s)}(x̃, B̃))ʳ` when `r` is closed for `B̃`, where `r(s)` applies the
column map of `r` to each direction. -/
theorem seedMutationSeq_reindex (h : n ≤ m) (h' : n' ≤ m') (S : SeedData F m n)
    {r : ReindexingMap m' n' m n} (hr : r.IsClosedFor h' S.extExchangeMatrix)
    (s : List (Fin n')) :
    seedMutationSeq h' (S.reindex h' r) s
      = (seedMutationSeq h S (s.map (r.col h'))).reindex h' r := by
  induction s generalizing S with
  | nil => rfl
  | cons q s ih =>
    rw [seedMutationSeq_cons, seedMutation_reindex h h' S hr q, List.map_cons,
      seedMutationSeq_cons, ih _ (hr.matrixMutation h q)]

end SeedMutation

/-! ### Mapping the entries of a seed -/

section Map

variable {F F' F'' : Type*}

/-- The seed obtained by applying `f` to every entry of the extended cluster of `S`, keeping
its extended exchange matrix. -/
def SeedData.map (f : F → F') (S : SeedData F m n) : SeedData F' m n where
  extCluster := f ∘ S.extCluster
  extExchangeMatrix := S.extExchangeMatrix

/-- The extended cluster of a mapped seed. -/
@[simp]
theorem SeedData.map_extCluster (f : F → F') (S : SeedData F m n) :
    (S.map f).extCluster = f ∘ S.extCluster :=
  rfl

/-- The extended exchange matrix of a mapped seed. -/
@[simp]
theorem SeedData.map_extExchangeMatrix (f : F → F') (S : SeedData F m n) :
    (S.map f).extExchangeMatrix = S.extExchangeMatrix :=
  rfl

/-- Mapping along the identity does nothing. -/
@[simp]
theorem SeedData.map_id (S : SeedData F m n) : S.map id = S :=
  rfl

/-- Mapping twice is mapping along the composite. -/
theorem SeedData.map_map (f : F → F') (g : F' → F'') (S : SeedData F m n) :
    (S.map f).map g = S.map (g ∘ f) :=
  rfl

/-- **Mapping commutes with reindexing.** -/
theorem SeedData.map_reindex (f : F → F') (h' : n' ≤ m') (S : SeedData F m n)
    (r : ReindexingMap m' n' m n) : (S.reindex h' r).map f = (S.map f).reindex h' r :=
  rfl

variable [Field F] [Field F'] {G : Type*} [FunLike G F F'] [RingHomClass G F F']

/-- A ring homomorphism carries the positive exchange monomial of `x` to that of `f ∘ x`. -/
theorem map_exchangeMonomialPos (f : G) (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n) : f (exchangeMonomialPos x B k) = exchangeMonomialPos (f ∘ x) B k := by
  simp only [exchangeMonomialPos, map_prod, map_zpow₀, Function.comp_apply]

/-- A ring homomorphism carries the negative exchange monomial of `x` to that of `f ∘ x`. -/
theorem map_exchangeMonomialNeg (f : G) (x : Fin m → F) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n) : f (exchangeMonomialNeg x B k) = exchangeMonomialNeg (f ∘ x) B k := by
  simp only [exchangeMonomialNeg, map_prod, map_zpow₀, Function.comp_apply]

/-- **A ring homomorphism of fields commutes with seed mutation.** -/
theorem seedMutation_map (h : n ≤ m) (f : G) (S : SeedData F m n) (k : Fin n) :
    (seedMutation h S k).map f = seedMutation h (S.map f) k := by
  refine SeedData.ext ?_ rfl
  simp only [seedMutation, SeedData.map_extCluster, SeedData.map_extExchangeMatrix,
    Function.comp_update, map_div₀, map_add, map_exchangeMonomialPos,
    map_exchangeMonomialNeg, Function.comp_apply]

/-- **A ring homomorphism of fields commutes with mutation along a sequence.** -/
theorem seedMutationSeq_map (h : n ≤ m) (f : G) (S : SeedData F m n) (s : List (Fin n)) :
    (seedMutationSeq h S s).map f = seedMutationSeq h (S.map f) s := by
  induction s generalizing S with
  | nil => rfl
  | cons k s ih => rw [seedMutationSeq_cons, ih, seedMutation_map, seedMutationSeq_cons]

end Map

/-! ### A reindexed labeled seed is a labeled seed -/

section LabeledSeed

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]

/-- The reindexing `(x̃, B̃)ʳ` of a seed, read as a seed in the subfield
`K(x_{r(1)}, …, x_{r(m')})` of `F` generated by its extended cluster. -/
def SeedData.reindexAdjoin (h' : n' ≤ m') (S : SeedData F m n) (r : ReindexingMap m' n' m n) :
    SeedData (IntermediateField.adjoin K (Set.range (S.extCluster ∘ r))) m' n' where
  extCluster a := ⟨S.extCluster (r a), IntermediateField.subset_adjoin K _ ⟨a, rfl⟩⟩
  extExchangeMatrix := matrixReindex h' S.extExchangeMatrix r

/-- The entries of the extended cluster of `SeedData.reindexAdjoin`, read in `F`. -/
@[simp]
theorem SeedData.coe_reindexAdjoin_extCluster (h' : n' ≤ m') (S : SeedData F m n)
    (r : ReindexingMap m' n' m n) (a : Fin m') :
    ((S.reindexAdjoin K h' r).extCluster a : F) = S.extCluster (r a) :=
  rfl

/-- The extended exchange matrix of `SeedData.reindexAdjoin`. -/
@[simp]
theorem SeedData.reindexAdjoin_extExchangeMatrix (h' : n' ≤ m') (S : SeedData F m n)
    (r : ReindexingMap m' n' m n) :
    (S.reindexAdjoin K h' r).extExchangeMatrix = matrixReindex h' S.extExchangeMatrix r :=
  rfl

/-- Read in `F`, the seed `SeedData.reindexAdjoin` is the reindexed seed `(x̃, B̃)ʳ`. -/
theorem SeedData.map_val_reindexAdjoin (h' : n' ≤ m') (S : SeedData F m n)
    (r : ReindexingMap m' n' m n) :
    (S.reindexAdjoin K h' r).map (IntermediateField.val _) = S.reindex h' r :=
  rfl

/-- **A reindexed labeled seed is a labeled seed**: if `(x̃, B̃)` is a labeled seed in `F` over
`K`, then `(x̃, B̃)ʳ` is a labeled seed in `K(x_{r(1)}, …, x_{r(m')})` over `K`. -/
@[cluster_algebras "lem_seed_reindex_is_seed"]
theorem IsLabeledSeed.reindexAdjoin (h : n ≤ m) (h' : n' ≤ m') {S : SeedData F m n}
    (hS : IsLabeledSeed K h S) (r : ReindexingMap m' n' m n) :
    IsLabeledSeed K h' (S.reindexAdjoin K h' r) := by
  refine ⟨⟨AlgebraicIndependent.of_comp (IntermediateField.val _)
    (hS.1.1.comp r r.injective), IntermediateField.map_injective (IntermediateField.val _) ?_⟩,
    hS.2.matrixReindex h h' r⟩
  rw [IntermediateField.adjoin_map, ← Set.range_comp]
  exact (IntermediateField.lift_top K _).symm

end LabeledSeed

end ClusterAlgebras
