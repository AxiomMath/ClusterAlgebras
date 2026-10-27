/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.Coefficients.ZSpanRescaling
public import ClusterAlgebras.FiniteType.External
public import ClusterAlgebras.Subpattern.SeedReindex
public import ClusterAlgebras.TypeD.Seed

/-!
# Seed patterns of type `D_n` are of finite type

We prove that every seed pattern of type `D_n`, with arbitrary coefficients, is of finite type. A
seed pattern of type `D_n` is first relabelled and rebased so that its exchange matrices are
exactly those of the explicit pattern `Σ•_n`: relabel by the permutation in the definition of
"type", pass between orientations of the tree `D_n` by mutations at sources and sinks, and move
the base vertex. The `ℤ`-span condition, which holds because the initial extended exchange matrix
of `Σ•_n` has full rank, then transfers finiteness from `Σ•_n`.

## Main results

* `ClusterAlgebras.isFiniteTree_dynkinTreeD`: the graph `D_m` is a finite tree.
* `ClusterAlgebras.IsSeedPattern.principalPart_apply_eq_of_apply_eq`: equal exchange matrices at
  one vertex are equal everywhere.
* `ClusterAlgebras.IsSeedPattern.exists_isSeedPattern_reindex`: relabelling a seed pattern.
* `ClusterAlgebras.IsSeedPattern.exists_reindex_principalPart_eq_dPattern`: the reduction of a
  pattern of type `D_n` to the exchange matrices of `Σ•_n`.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_of_isPatternOfType_D`: every seed pattern of type
  `D_n` is of finite type.

## Implementation notes

* "The same exchange matrix" is equality of principal parts.
* A pattern of type `D_n` is `IsPatternOfType hmn P [DynkinSymbol.D n hn]`.
* In the reduction, `Σ•_n` is taken over the same ground field `𝕜` as the given pattern.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.4][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

/-- Adjacency in `D_m` unfolds to the edge relation in either direction. -/
private theorem dynkinTreeD_adj_iff {m : ℕ} (i j : Fin m) :
    (dynkinTreeD m).Adj i j ↔ i ≠ j ∧ (dynkinTreeDRel m i j ∨ dynkinTreeDRel m j i) :=
  SimpleGraph.fromRel_adj _ _ _

/-- The graph `D_m` is connected for `m ≥ 4`: every vertex is joined to `0`. -/
private theorem dynkinTreeD_connected {m : ℕ} (hm : 4 ≤ m) : (dynkinTreeD m).Connected := by
  have h0 : ∀ k (hk : k < m), (dynkinTreeD m).Reachable ⟨0, by omega⟩ ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact SimpleGraph.Reachable.refl _
      · by_cases hkm : k + 1 = m
        · refine (ih (m - 3) (by omega) (by omega)).trans (SimpleGraph.Adj.reachable ?_)
          rw [dynkinTreeD_adj_iff]
          refine ⟨fun h => by simp [Fin.ext_iff] at h; omega, Or.inl (Or.inr ⟨?_, ?_⟩)⟩ <;>
            simp <;> omega
        · refine (ih (k - 1) (by omega) (by omega)).trans (SimpleGraph.Adj.reachable ?_)
          rw [dynkinTreeD_adj_iff]
          refine ⟨fun h => by simp [Fin.ext_iff] at h; omega, Or.inl (Or.inl ⟨?_, ?_⟩)⟩ <;>
            simp <;> omega
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  exact SimpleGraph.Connected.mk fun u v => (h0 u u.isLt).symm.trans (h0 v v.isLt)

/-- The edges of `D_m`, numbered: `k ↦ {k, k + 1}` for `k + 2 < m`, and the last one is
`{m - 3, m - 1}`. -/
private def dynkinTreeDEdge {m : ℕ} (hm : 4 ≤ m) (k : Fin (m - 1)) : Sym2 (Fin m) :=
  if h : (k : ℕ) + 2 < m then s(⟨k, by omega⟩, ⟨k + 1, by omega⟩)
  else s(⟨m - 3, by omega⟩, ⟨m - 1, by omega⟩)

/-- Each numbered edge is an edge of `D_m`. -/
private theorem dynkinTreeDEdge_mem {m : ℕ} (hm : 4 ≤ m) (k : Fin (m - 1)) :
    dynkinTreeDEdge hm k ∈ (dynkinTreeD m).edgeSet := by
  unfold dynkinTreeDEdge
  split_ifs with h
  · rw [SimpleGraph.mem_edgeSet, dynkinTreeD_adj_iff]
    refine ⟨fun h => by simp [Fin.ext_iff] at h, Or.inl (Or.inl ⟨rfl, ?_⟩)⟩
    simp
    omega
  · rw [SimpleGraph.mem_edgeSet, dynkinTreeD_adj_iff]
    refine ⟨fun h => by simp [Fin.ext_iff] at h; omega, Or.inl (Or.inr ⟨?_, ?_⟩)⟩ <;>
      simp <;> omega

/-- Distinct numbers give distinct edges. -/
private theorem dynkinTreeDEdge_injective {m : ℕ} (hm : 4 ≤ m) :
    Function.Injective (dynkinTreeDEdge hm) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  unfold dynkinTreeDEdge at hab
  split_ifs at hab with h1 h2 h2 <;>
    simp only [Sym2.eq_iff, Fin.ext_iff] at hab <;> apply Fin.ext <;> omega

/-- Every edge of `D_m` is numbered. -/
private theorem dynkinTreeDEdge_surjective {m : ℕ} (hm : 4 ≤ m) (e : Sym2 (Fin m))
    (he : e ∈ (dynkinTreeD m).edgeSet) : ∃ k, dynkinTreeDEdge hm k = e := by
  induction e using Sym2.ind with
  | _ i j =>
    rw [SimpleGraph.mem_edgeSet, dynkinTreeD_adj_iff] at he
    obtain ⟨hne, h⟩ := he
    have hi := i.isLt
    have hj := j.isLt
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    unfold dynkinTreeDRel at h
    rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨⟨i, by omega⟩, ?_⟩
      unfold dynkinTreeDEdge
      rw [dif_pos (by simp; omega)]
      simp only [Sym2.eq_iff, Fin.ext_iff, true_and]
      omega
    · refine ⟨⟨m - 2, by omega⟩, ?_⟩
      unfold dynkinTreeDEdge
      rw [dif_neg (by simp; omega)]
      simp only [Sym2.eq_iff, Fin.ext_iff]
      omega
    · refine ⟨⟨j, by omega⟩, ?_⟩
      unfold dynkinTreeDEdge
      rw [dif_pos (by simp; omega)]
      simp only [Sym2.eq_iff, Fin.ext_iff, true_and]
      omega
    · refine ⟨⟨m - 2, by omega⟩, ?_⟩
      unfold dynkinTreeDEdge
      rw [dif_neg (by simp; omega)]
      simp only [Sym2.eq_iff, Fin.ext_iff]
      omega

/-- **The tree `D_n` is a finite tree**: for `m ≥ 4`, the graph `D_m` is a finite tree. -/
@[cluster_algebras "lem_dynkin_tree_D_tree"]
theorem isFiniteTree_dynkinTreeD {m : ℕ} (hm : 4 ≤ m) : IsFiniteTree (dynkinTreeD m) := by
  rw [IsFiniteTree, SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨dynkinTreeD_connected hm, ?_⟩
  have e : Fin (m - 1) ≃ (dynkinTreeD m).edgeSet :=
    Equiv.ofBijective (fun k => ⟨dynkinTreeDEdge hm k, dynkinTreeDEdge_mem hm k⟩)
      ⟨fun a b h => dynkinTreeDEdge_injective hm (congrArg Subtype.val h),
        fun ⟨e, he⟩ => (dynkinTreeDEdge_surjective hm e he).imp fun _ h => Subtype.ext h⟩
  rw [← Nat.card_congr e, Nat.card_fin, Nat.card_fin]
  omega

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Algebra K F] [Field F'] [Algebra K F']
  {m m' n : ℕ}

/-- **Equal exchange matrices at one vertex are equal everywhere**: two seed patterns of rank `n`
over `𝕜`, in possibly different fields and with possibly different numbers of frozen variables,
with the same exchange matrix at `t₀` have the same exchange matrix at every vertex. -/
@[cluster_algebras "lem_pattern_same_principal_parts"]
theorem IsSeedPattern.principalPart_apply_eq_of_apply_eq (hmn : n ≤ m) (hm' : n ≤ m')
    {P : RegularTree n → SeedData F m n} {P' : RegularTree n → SeedData F' m' n}
    (hP : IsSeedPattern K hmn P) (hP' : IsSeedPattern K hm' P') {t₀ : RegularTree n}
    (h₀ : principalPart hmn (P t₀).extExchangeMatrix = principalPart hm' (P' t₀).extExchangeMatrix)
    (t : RegularTree n) :
    principalPart hmn (P t).extExchangeMatrix = principalPart hm' (P' t).extExchangeMatrix :=
  hP.principalPart_eq_of_principalPart_eq hmn hm' hP' h₀ t

/-- A reindexing map from `(m, n)` to itself is surjective. -/
private theorem ReindexingMap.surjective_self (r : ReindexingMap m n m n) :
    Function.Surjective r :=
  Finite.surjective_of_injective r.injective

/-- The column map of a reindexing map from `(m, n)` to itself is surjective. -/
private theorem ReindexingMap.col_surjective_self (hmn : n ≤ m) (r : ReindexingMap m n m n) :
    Function.Surjective (r.col hmn) :=
  Finite.surjective_of_injective (r.col_injective hmn)

omit [Field F] in
/-- Reindexing along a reindexing map from `(m, n)` to itself is injective. -/
private theorem SeedData.reindex_injective_self (hmn : n ≤ m) (r : ReindexingMap m n m n) :
    Function.Injective fun S : SeedData F m n => S.reindex hmn r := by
  intro S T h
  have hx := congrArg SeedData.extCluster h
  have hB := congrArg SeedData.extExchangeMatrix h
  simp only [SeedData.reindex_extCluster, SeedData.reindex_extExchangeMatrix] at hx hB
  refine SeedData.ext (r.surjective_self.injective_comp_right hx) (Matrix.ext fun i j => ?_)
  obtain ⟨p, rfl⟩ := r.surjective_self i
  obtain ⟨q, rfl⟩ := r.col_surjective_self hmn j
  exact congrFun (congrFun hB p) q

omit [Field F] in
/-- Reindexing along a reindexing map from `(m, n)` to itself keeps the cluster variables. -/
private theorem clusterVariables_reindex_self (hmn : n ≤ m) (S : SeedData F m n)
    (r : ReindexingMap m n m n) :
    clusterVariables hmn (S.reindex hmn r) = clusterVariables hmn S := by
  have h : cluster hmn (S.reindex hmn r) = cluster hmn S ∘ r.col hmn := by
    funext i
    simp only [cluster, SeedData.reindex_extCluster, Function.comp_apply,
      ReindexingMap.castLE_col]
  rw [clusterVariables, clusterVariables, h, (r.col_surjective_self hmn).range_comp]

/-- A labeled seed reindexed along a reindexing map from `(m, n)` to itself is a labeled seed in
the same field. -/
private theorem IsLabeledSeed.reindex_self (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) (r : ReindexingMap m n m n) :
    IsLabeledSeed K hmn (S.reindex hmn r) := by
  refine ⟨⟨hS.1.1.comp r r.injective, ?_⟩, hS.2.matrixReindex hmn hmn r⟩
  rw [SeedData.reindex_extCluster, r.surjective_self.range_comp]
  exact hS.1.2

omit [Field F] in
/-- The cluster variables of `P` are those of the seeds in its range. -/
private theorem patternClusterVariables_eq_biUnion (hmn : n ≤ m)
    (P : RegularTree n → SeedData F m n) :
    patternClusterVariables hmn P = ⋃ S ∈ Set.range P, clusterVariables hmn S := by
  rw [Set.biUnion_range]
  rfl

omit [Field F] in
/-- The clusters of `P` are those of the seeds in its range. -/
private theorem patternClusters_eq_image (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) :
    patternClusters hmn P = clusterVariables hmn '' Set.range P := by
  rw [← Set.range_comp]
  rfl

/-- **Relabelling a seed pattern**: for a seed pattern `Σ` of rank `n` in `F` with matrices of
size `m × n`, a reindexing map `r` from `(m, n)` to `(m, n)` and vertices `t₀, t₁`, there is a
seed pattern `Σ'` in `F` with `Σ'(t₁) = Σ(t₀)ʳ` whose seeds are the `Σ(t)ʳ`. Consequently `Σ'`
is of finite type if and only if `Σ` is, and the two patterns have the same cluster variables and
the same clusters. -/
@[cluster_algebras "lem_pattern_relabel"]
theorem IsSeedPattern.exists_isSeedPattern_reindex [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (r : ReindexingMap m n m n) (t₀ t₁ : RegularTree n) :
    ∃ P' : RegularTree n → SeedData F m n, IsSeedPattern K hmn P' ∧
      P' t₁ = (P t₀).reindex hmn r ∧
      Set.range P' = (fun S => S.reindex hmn r) '' Set.range P ∧
      (IsFiniteType P' ↔ IsFiniteType P) ∧
      patternClusterVariables hmn P' = patternClusterVariables hmn P ∧
      patternClusters hmn P' = patternClusters hmn P := by
  obtain ⟨P', hP', h₁⟩ := exists_isSeedPattern hmn t₁ ((hP.1 t₀).reindex_self hmn r)
  have hcl : ∀ S : SeedData F m n, r.IsClosedFor hmn S.extExchangeMatrix :=
    fun S => ReindexingMap.isClosedFor_of_surjective r.surjective_self hmn _
  have hrange : Set.range P' = (fun S => S.reindex hmn r) '' Set.range P := by
    ext S
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := hP'.exists_seedMutationSeq_eq hmn t₁ t
      refine ⟨_, hP.seedMutationSeq_mem_range hmn t₀ (s.map (r.col hmn)), ?_⟩
      rw [hs, h₁, seedMutationSeq_reindex hmn hmn _ (hcl _)]
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨s', hs'⟩ := hP.exists_seedMutationSeq_eq hmn t₀ t
      obtain ⟨g, hg⟩ := (r.col_surjective_self hmn).hasRightInverse
      have hmap : (s'.map g).map (r.col hmn) = s' := by
        rw [List.map_map, hg.comp_eq_id, List.map_id]
      obtain ⟨t', ht'⟩ := hP'.seedMutationSeq_mem_range hmn t₁ (s'.map g)
      refine ⟨t', ?_⟩
      rw [ht', h₁, seedMutationSeq_reindex hmn hmn _ (hcl _), hmap, hs']
  refine ⟨P', hP', h₁, hrange, ?_, ?_, ?_⟩
  · rw [IsFiniteType, IsFiniteType, hrange]
    exact Set.finite_image_iff (SeedData.reindex_injective_self hmn r).injOn
  · rw [patternClusterVariables_eq_biUnion, patternClusterVariables_eq_biUnion, hrange,
      Set.biUnion_image]
    simp only [clusterVariables_reindex_self]
  · rw [patternClusters_eq_image, patternClusters_eq_image, hrange, Set.image_image]
    simp only [clusterVariables_reindex_self]

end Generic

section Quivers

variable {V : Type*} [Fintype V] [DecidableEq V] {m n : ℕ}

omit [DecidableEq V] in
/-- The extended exchange matrix depends only on the quiver and the numbering of its vertices. -/
private theorem typeD_extExchangeMatrix_congr {Q₁ Q₂ : Quiver V} (L₁ : Labelling Q₁ m n)
    (L₂ : Labelling Q₂ m n) (hQ : Q₁ = Q₂) (hL : L₁.equiv = L₂.equiv) :
    extExchangeMatrix Q₁ L₁ = extExchangeMatrix Q₂ L₂ := by
  subst hQ
  ext i j
  simp only [extExchangeMatrix, Matrix.of_apply, hL]

/-- Along a mutation path, the extended exchange matrix of the result, in the same numbering of
the vertices, is a mutation of the initial one along a sequence of directions. -/
private theorem typeD_exists_extExchangeMatrix_result {Q : Quiver V} (p : Q.MutationPath)
    (L : Labelling Q m n) :
    ∃ (s : List (Fin n)) (L' : Labelling p.result m n), L'.equiv = L.equiv ∧
      extExchangeMatrix p.result L' = matrixMutationList L.le (extExchangeMatrix Q L) s := by
  induction p with
  | nil Q => exact ⟨[], L, rfl, rfl⟩
  | @cons Q k hk p ih =>
    have hj : ((L.equiv.symm k : Fin m) : ℕ) < n := by
      have h := (L.mem_frozen_iff (L.equiv.symm k)).not.1 (by simpa using hk)
      omega
    let j : Fin n := ⟨_, hj⟩
    have hkj : k = L.equiv (Fin.castLE L.le j) := by simp [j]
    have key : ∀ (k' : V) (hk' : k' ∉ Q.frozen), k' = L.equiv (Fin.castLE L.le j) →
        extExchangeMatrix (Q.mutate hk') (L.mutate hk') =
          matrixMutation L.le (extExchangeMatrix Q L) j := by
      rintro k' hk' rfl
      exact extExchangeMatrix_mutate Q L j
    obtain ⟨s, L', hL', h⟩ := ih (L.mutate hk)
    refine ⟨j :: s, L', hL', ?_⟩
    rwa [matrixMutationList_cons, ← key k hk hkj]

end Quivers

section TypeD

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {m : ℕ}

/-- The principal part of a mutation sequence is the corresponding sequence of mutations of the
principal part. -/
private theorem typeD_principalPart_seedMutationSeq {n : ℕ} (hmn : n ≤ m) (S : SeedData F m n)
    (s : List (Fin n)) :
    principalPart hmn (seedMutationSeq hmn S s).extExchangeMatrix =
      matrixMutationList le_rfl (principalPart hmn S.extExchangeMatrix) s := by
  induction s generalizing S with
  | nil => rfl
  | cons k s ih =>
    rw [seedMutationSeq_cons, ih, matrixMutationList_cons]
    congr 1
    exact principalPart_matrixMutation hmn _ k

/-- If `dₐ x = -(d_b y)` with `dₐ, d_b > 0` and `|x| = |y| ≤ 1`, then `y = -x`: the shape of a
pair of mirror entries of a skew-symmetrizable matrix with symmetric Cartan counterpart. -/
private theorem typeD_eq_neg_of_abs_eq {x y da db : ℤ} (hda : 0 < da) (hdb : 0 < db)
    (h : da * x = -(db * y)) (hx : |x| ≤ 1) (hxy : |x| = |y|) : y = -x := by
  have hy : |y| ≤ 1 := hxy ▸ hx
  rw [abs_le] at hx hy
  have hx' : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  have hy' : y = -1 ∨ y = 0 ∨ y = 1 := by omega
  rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
    simp at h hxy ⊢ <;> omega

/-- The Cartan matrix of the list `[D_n]` is `C(D_n)`. -/
private theorem listCartan_D {n : ℕ} (hn : 4 ≤ n) (a b : Fin n) :
    DynkinSymbol.listCartan [.D n hn] a b = cartanD n a b := by
  have h : ∀ i : Fin n, (finSumFinEquiv (m := n) (n := 0)).symm i = Sum.inl i :=
    fun i => finSumFinEquiv_symm_apply_castAdd (n := 0) i
  change Matrix.fromBlocks (cartanD n) (0 : Matrix (Fin n) (Fin 0) ℤ) 0 0
    ((finSumFinEquiv (m := n) (n := 0)).symm (a : Fin (n + 0)))
    ((finSumFinEquiv (m := n) (n := 0)).symm (b : Fin (n + 0))) = cartanD n a b
  rw [h, h, Matrix.fromBlocks_apply₁₁]

/-- A skew-symmetrizable matrix with Cartan counterpart `C(D_n)` has zero diagonal, entries of
absolute value `1` exactly on the edges of `D_n`, and is skew-symmetric. -/
private theorem typeD_entries {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    (hcart : ∀ a b, cartanCounterpart B a b = cartanD n a b) :
    (∀ a, B a a = 0) ∧ (∀ a b, a ≠ b → |B a b| = if (dynkinTreeD n).Adj a b then 1 else 0) ∧
      ∀ a b, B b a = -B a b := by
  obtain ⟨d, hdpos, hd⟩ := hB
  simp only [Int.cast_id] at hd
  have hcD : ∀ a b, cartanD n a b =
      if a = b then 2 else if (dynkinTreeD n).Adj a b then -1 else 0 := fun a b => rfl
  have hdiag : ∀ a, B a a = 0 := fun a => by nlinarith [hd a a, hdpos a]
  have habs : ∀ a b, a ≠ b → |B a b| = if (dynkinTreeD n).Adj a b then 1 else 0 := by
    intro a b hab
    have h := hcart a b
    rw [hcD, if_neg hab] at h
    simp only [cartanCounterpart, Matrix.of_apply, if_neg hab] at h
    split_ifs at h ⊢ <;> omega
  refine ⟨hdiag, habs, fun a b => ?_⟩
  rcases eq_or_ne a b with rfl | hab
  · rw [hdiag, neg_zero]
  · refine typeD_eq_neg_of_abs_eq (hdpos a) (hdpos b) (hd a b) ?_ ?_
    · rw [habs a b hab]
      split_ifs <;> norm_num
    · rw [habs a b hab, habs b a hab.symm]
      simp only [SimpleGraph.adj_comm]

/-- A skew-symmetric matrix with zero diagonal whose entries have absolute value `1` exactly on
the edges of `D_n` is the exchange matrix of an orientation of `D_n`: the quiver with an arrow
`a → b` exactly when `b_{ab} = 1`. -/
private theorem typeD_exists_orientation {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hdiag : ∀ a, B a a = 0)
    (habs : ∀ a b, a ≠ b → |B a b| = if (dynkinTreeD n).Adj a b then 1 else 0)
    (hanti : ∀ a b, B b a = -B a b) :
    ∃ (Q : Quiver (Fin n)) (L : Labelling Q n n), Q.IsTreeOrientation (dynkinTreeD n) ∧
      L.equiv = Equiv.refl _ ∧ extExchangeMatrix Q L = B := by
  have hval : ∀ a b, B a b = -1 ∨ B a b = 0 ∨ B a b = 1 := fun a b => by
    rcases eq_or_ne a b with rfl | hab
    · exact Or.inr (Or.inl (hdiag a))
    · have h : |B a b| ≤ 1 := by
        rw [habs a b hab]
        split_ifs <;> norm_num
      rw [abs_le] at h
      omega
  obtain ⟨Q, hQa, hQf, hQ⟩ := orientation_of_arrow_counts (dynkinTreeD n)
    (fun a b => if B a b = 1 then 1 else 0)
    (fun v => by simp [hdiag v])
    (fun u v huv => by
      have h := habs u v huv.ne
      rw [if_pos huv] at h
      rw [hanti u v]
      rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 h with h' | h' <;> simp [h'])
    (fun u v huv hadj => by
      have h := habs u v huv
      rw [if_neg hadj, abs_eq_zero] at h
      simp [h])
  let L : Labelling Q n n := ⟨Equiv.refl _, le_rfl, fun i => by simp [hQf, i.isLt]⟩
  refine ⟨Q, L, hQ, rfl, ?_⟩
  ext a b
  simp only [extExchangeMatrix, Matrix.of_apply, signedCount, hQa, L, Equiv.refl_apply,
    Fin.castLE_rfl]
  have h' := hanti a b
  rcases hval a b with h | h | h <;> rw [h] at h' <;> simp [h, h']

open TypeD in
/-- A skew-symmetrizable matrix with Cartan counterpart `C(D_n)` is obtained from `B_D` by a
sequence of mutations: it is the exchange matrix of an orientation of the tree `D_n`, and any two
orientations of a tree are related by mutations at sources and sinks. -/
private theorem typeD_exists_eq_matrixMutationList {n : ℕ} (hn : 4 ≤ n)
    {B : Matrix (Fin n) (Fin n) ℤ} (hB : SkewSymmetrizable B)
    (hcart : ∀ a b, cartanCounterpart B a b = cartanD n a b) :
    ∃ s : List (Fin n), B = matrixMutationList le_rfl (dynkinExchangeD n) s := by
  obtain ⟨hdiag, habs, hanti⟩ := typeD_entries hB hcart
  obtain ⟨Q, L, hQ, hL, hQB⟩ := typeD_exists_orientation hdiag habs hanti
  obtain ⟨QD, LD, hQD, hLD, hBD, -⟩ := exists_orientation_dynkinExchangeD hn
  obtain ⟨p, -, hp⟩ := Quiver.exists_mutationPath_of_isTreeOrientation
    (isFiniteTree_dynkinTreeD hn) hQD hQ
  obtain ⟨s, L', hL', hs⟩ := typeD_exists_extExchangeMatrix_result p LD
  refine ⟨s, ?_⟩
  rw [← hQB, typeD_extExchangeMatrix_congr L L' hp.symm (by rw [hL', hLD, hL]), hs, ← hBD]
  rfl

open TypeD in
/-- **Reduction of a pattern of type `D_n` to the exchange matrices of `Σ•_n`**: for `n ≥ 4` and a
seed pattern `Σ̄` of type `D_n` in `F̄` over `𝕜` with matrices of size `m̄ × n`, there are a
reindexing map `r` from `(m̄, n)` to `(m̄, n)` and a seed pattern `Σ̄*` in `F̄` whose seeds are the
`Σ̄(t)ʳ` and whose exchange matrix at every `t` is that of `Σ•_n(t)`. In particular `Σ̄*` and `Σ̄`
have the same cluster variables and clusters, and `Σ̄*` is of finite type if and only if `Σ̄` is.
-/
@[cluster_algebras "lem_D_reduction"]
theorem IsSeedPattern.exists_reindex_principalPart_eq_dPattern [CharZero K] {n : ℕ} [NeZero n]
    (hn : 4 ≤ n) (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.D n hn]) :
    ∃ (r : ReindexingMap m n m n) (P' : RegularTree n → SeedData F m n),
      IsSeedPattern K hmn P' ∧ Set.range P' = (fun S => S.reindex hmn r) '' Set.range P ∧
      (∀ t, principalPart hmn (P' t).extExchangeMatrix =
        principalPart (le_two_mul_add_two n) (dPattern K n t).extExchangeMatrix) ∧
      patternClusterVariables hmn P' = patternClusterVariables hmn P ∧
      patternClusters hmn P' = patternClusters hmn P ∧ (IsFiniteType P' ↔ IsFiniteType P) := by
  obtain ⟨t₁, σ, hσ⟩ := hX
  let τ : Equiv.Perm (Fin n) := σ
  let ρ : Equiv.Perm (Fin n) := τ.symm
  let r : ReindexingMap m n m n := ReindexingMap.ofMutablePerm hmn ρ
  set Bb := principalPart hmn (P t₁).extExchangeMatrix
  set B' := Bb.submatrix ρ ρ
  have hS₁ : principalPart hmn ((P t₁).reindex hmn r).extExchangeMatrix = B' :=
    SeedData.principalPart_reindex_ofMutablePerm hmn _ ρ
  have hcart : ∀ a b, cartanCounterpart B' a b = cartanD n a b := by
    intro a b
    have h : cartanCounterpart Bb (ρ a) (ρ b) = cartanD n (τ (ρ a)) (τ (ρ b)) :=
      (hσ (ρ a) (ρ b)).trans (listCartan_D hn _ _)
    simp only [ρ, Equiv.apply_symm_apply] at h
    have h2 : cartanCounterpart B' a b = cartanCounterpart Bb (ρ a) (ρ b) := by
      simp only [cartanCounterpart, Matrix.of_apply, B', Matrix.submatrix_apply,
        ρ.injective.eq_iff]
    exact h2.trans h
  have hB' : SkewSymmetrizable B' := hS₁ ▸ ((hP.1 t₁).reindex_self hmn r).2
  obtain ⟨s, hB's⟩ := typeD_exists_eq_matrixMutationList hn hB' hcart
  have hD := (isSeedPattern_dPattern K (n := n) (by omega)).1
  obtain ⟨t₂, ht₂⟩ := hD.seedMutationSeq_mem_range (le_two_mul_add_two n) (dynkinWordD n) s
  have hpp₂ : principalPart (le_two_mul_add_two n) (dPattern K n t₂).extExchangeMatrix = B' := by
    rw [ht₂, typeD_principalPart_seedMutationSeq, principalPart_dPattern_dynkinWordD K hn, hB's]
  obtain ⟨P', hP', hP't₂, hrange, hfin, hcv, hcl⟩ := hP.exists_isSeedPattern_reindex hmn r t₁ t₂
  exact ⟨r, P', hP', hrange, hP'.principalPart_apply_eq_of_apply_eq hmn (le_two_mul_add_two n) hD
    (t₀ := t₂) (by rw [hP't₂, hS₁, hpp₂]), hcv, hcl, hfin⟩

/-- **Seed patterns of type `D_n` are of finite type**: for `n ≥ 4`, every seed pattern of type
`D_n` is of finite type. -/
@[cluster_algebras "thm_type_D_finite"]
theorem IsSeedPattern.isFiniteType_of_isPatternOfType_D [CharZero K] {n : ℕ} (hn : 4 ≤ n)
    (hmn : n ≤ m) {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P)
    (hX : IsPatternOfType hmn P [.D n hn]) : IsFiniteType P := by
  have : NeZero n := ⟨by omega⟩
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CharZero (TypeD.DField K n) :=
    charZero_of_injective_algebraMap (algebraMap K (TypeD.DField K n)).injective
  obtain ⟨-, P', hP', -, hpp, -, -, hfin⟩ := hP.exists_reindex_principalPart_eq_dPattern hn hmn hX
  refine hfin.1 ?_
  obtain ⟨hD, hD₀⟩ := TypeD.isSeedPattern_dPattern K (n := n) (by omega)
  have hZ : ZSpanCondition (P' .root).extExchangeMatrix
      (TypeD.dPattern K n .root).extExchangeMatrix := by
    refine zSpanCondition_of_span_eq_top ?_ _
    rw [hD₀]
    exact TypeD.span_labelledMatrix_initial (by omega)
  classical
  let g : SeedData (TypeD.DField K n) (2 * n + 2) n → SeedData F m n := fun S =>
    if h : ∃ t, TypeD.dPattern K n t = S then P' h.choose else P' .root
  have hg : ∀ t, g (TypeD.dPattern K n t) = P' t := fun t => by
    have h : ∃ t', TypeD.dPattern K n t' = TypeD.dPattern K n t := ⟨t, rfl⟩
    simpa only [g, dif_pos h] using hD.eq_of_eq_of_zSpanCondition (TypeD.le_two_mul_add_two n)
      hmn hP' (hpp .root).symm hZ h.choose_spec
  rw [IsFiniteType, show P' = g ∘ TypeD.dPattern K n from funext fun t => (hg t).symm,
    Set.range_comp]
  exact (TypeD.isFiniteType_dPattern K (n := n) (by omega)).image g

end TypeD

end ClusterAlgebras
