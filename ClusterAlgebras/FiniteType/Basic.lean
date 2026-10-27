/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.SeedPattern

/-!
# Seed patterns of finite type

A seed pattern is *of finite type* when it has finitely many labeled seeds. Its *cluster
variables* are the entries of the clusters of all of its seeds, and its *clusters* are the sets of
entries of those clusters. Finite type is the same as finitely many cluster variables.

## Main definitions

* `ClusterAlgebras.IsFiniteType P`: the seed pattern `P` has finitely many labeled seeds.
* `ClusterAlgebras.patternClusterVariables hmn P`: the set `𝒳(P)` of cluster variables of `P`.
* `ClusterAlgebras.patternClusters hmn P`: the set of clusters of `P`, each a set of cluster
  variables.

## Main statements

* `ClusterAlgebras.IsFiniteType.finite_iUnion_clusterVariables`: a pattern of finite type has
  finitely many cluster variables.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_iff`: finite type is equivalent to finitely many
  cluster variables.

## Implementation notes

* FWZ count seeds up to a simultaneous relabelling; each such class has at most `n!` labeled
  seeds, so finitely many seeds in their sense is finitely many labeled seeds, which is what
  `IsFiniteType` says.
* Like `clusterAlgebra`, the definitions here are stated for an arbitrary assignment of seed data
  to the vertices of `𝕋ₙ`; the results that need a seed pattern assume it.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- A seed pattern `P` is **of finite type** when the set `{P t : t ∈ 𝕋ₙ}` of its labeled seeds
is finite. -/
@[cluster_algebras "def_finite_type"]
def IsFiniteType (P : RegularTree n → SeedData F m n) : Prop :=
  (Set.range P).Finite

omit [Field F] in
/-- **A seed pattern of finite type has finitely many cluster variables**: the union of the sets
of cluster variables of its finitely many distinct seeds is finite. -/
@[cluster_algebras "lem_finite_type_finite_cluster_variables"]
theorem IsFiniteType.finite_iUnion_clusterVariables (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsFiniteType P) :
    (⋃ t, clusterVariables hmn (P t)).Finite := by
  have h : (⋃ t, clusterVariables hmn (P t)) = ⋃ S ∈ Set.range P, clusterVariables hmn S := by
    ext x
    simp
  rw [h]
  exact hP.biUnion fun S _ => Set.finite_range _

/-- The **cluster variables of a seed pattern** `P`: the set
`𝒳(P) = {x_{i;t} : t ∈ 𝕋ₙ, i ∈ [1, n]}` of the entries of the clusters of all its seeds. -/
@[cluster_algebras "def_pattern_clusters"]
def patternClusterVariables (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) : Set F :=
  ⋃ t, clusterVariables hmn (P t)

omit [Field F] in
/-- Membership in the cluster variables of a seed pattern. -/
@[simp]
theorem mem_patternClusterVariables {hmn : n ≤ m} {P : RegularTree n → SeedData F m n} {y : F} :
    y ∈ patternClusterVariables hmn P ↔ ∃ t, y ∈ clusterVariables hmn (P t) :=
  Set.mem_iUnion

/-- The **clusters of a seed pattern** `P`: the sets `{x_{1;t}, …, x_{n;t}}`, `t ∈ 𝕋ₙ`, of the
entries of the clusters of its seeds. A cluster is a set, so two seeds whose clusters differ by
a permutation have the same cluster. -/
@[cluster_algebras "def_pattern_clusters"]
def patternClusters (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) : Set (Set F) :=
  Set.range fun t => clusterVariables hmn (P t)

/-- **An exchange binomial determines its column up to sign.** If the entries of `x` are
algebraically independent over a field of characteristic zero, the binomial
`∏ xᵢ ^ [cᵢ]₊ + ∏ xᵢ ^ [-cᵢ]₊` determines the integer vector `c` up to sign. -/
theorem eq_or_eq_neg_of_prod_pow_toNat_add_prod_pow_toNat_eq [CharZero K] {x : Fin m → F}
    (hx : AlgebraicIndependent K x) {c c' : Fin m → ℤ}
    (h : ∏ i, x i ^ (c i).toNat + ∏ i, x i ^ (-c i).toNat =
      ∏ i, x i ^ (c' i).toNat + ∏ i, x i ^ (-c' i).toNat) :
    c = c' ∨ c = -c' := by
  classical
  let e : (Fin m → ℤ) → (Fin m →₀ ℕ) := fun c =>
    Finsupp.equivFunOnFinite.symm fun i => (c i).toNat
  have hmono : ∀ f : Fin m →₀ ℕ,
      MvPolynomial.aeval x (MvPolynomial.monomial f (1 : K)) = ∏ i, x i ^ f i := fun f => by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ fun i => pow_zero _]
  have hp : MvPolynomial.monomial (e c) (1 : K) + MvPolynomial.monomial (e (-c)) 1 =
      MvPolynomial.monomial (e c') (1 : K) + MvPolynomial.monomial (e (-c')) 1 := by
    apply hx
    simpa [hmono, e] using h
  rw [← MvPolynomial.single_eq_monomial, ← MvPolynomial.single_eq_monomial,
    ← MvPolynomial.single_eq_monomial, ← MvPolynomial.single_eq_monomial] at hp
  have hp' : (Finsupp.single (e c) (1 : K) + Finsupp.single (e (-c)) 1 : (Fin m →₀ ℕ) →₀ K) =
      Finsupp.single (e c') 1 + Finsupp.single (e (-c')) 1 := hp
  rw [Finsupp.single_add_single_eq_single_add_single one_ne_zero one_ne_zero] at hp'
  have he : ∀ {c c' : Fin m → ℤ}, e c = e c' → ∀ i, (c i).toNat = (c' i).toNat := fun h i => by
    simpa [e] using DFunLike.congr_fun h i
  rcases hp' with ⟨h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨h0, -⟩
  · left
    funext i
    have := he h1 i
    have := he h2 i
    simp only [Pi.neg_apply] at *
    omega
  · right
    funext i
    have := he h1 i
    have := he h2 i
    simp only [Pi.neg_apply] at *
    omega
  · exact absurd h0 (by norm_num)

/-- Over a field of characteristic zero and an algebraically independent `x`, only finitely
many integer vectors `c` have their exchange binomial `∏ xᵢ ^ [cᵢ]₊ + ∏ xᵢ ^ [-cᵢ]₊` in a
given finite set. -/
theorem finite_setOf_prod_pow_toNat_add_prod_pow_toNat_mem [CharZero K] {x : Fin m → F}
    (hx : AlgebraicIndependent K x) {T : Set F} (hT : T.Finite) :
    {c : Fin m → ℤ | ∏ i, x i ^ (c i).toNat + ∏ i, x i ^ (-c i).toNat ∈ T}.Finite := by
  refine Set.Finite.preimage'
    (f := fun c : Fin m → ℤ => ∏ i, x i ^ (c i).toNat + ∏ i, x i ^ (-c i).toNat) hT
    fun y _ => ?_
  by_cases hy : ∃ c₀ : Fin m → ℤ, ∏ i, x i ^ (c₀ i).toNat + ∏ i, x i ^ (-c₀ i).toNat = y
  · obtain ⟨c₀, rfl⟩ := hy
    refine (Set.toFinite {c₀, -c₀}).subset fun c hc => ?_
    rcases eq_or_eq_neg_of_prod_pow_toNat_add_prod_pow_toNat_eq hx hc with h | h <;> simp [h]
  · convert Set.finite_empty
    ext c
    simpa using fun h => hy ⟨c, h⟩

/-- Mutation along a sequence does not change the entries of the extended cluster outside
the mutable positions. -/
theorem seedMutationSeq_extCluster_of_forall_ne_castLE (hmn : n ≤ m) (S : SeedData F m n)
    (s : List (Fin n)) {i : Fin m} (hi : ∀ k : Fin n, i ≠ Fin.castLE hmn k) :
    (seedMutationSeq hmn S s).extCluster i = S.extCluster i := by
  induction s generalizing S with
  | nil => rfl
  | cons k s ih =>
    rw [seedMutationSeq_cons, ih]
    exact Function.update_of_ne (hi k) _ _

/-- **Finite type is equivalent to finitely many cluster variables.** Over a field of
characteristic zero, a seed pattern `P` has finitely many labeled seeds if and only if its set
`𝒳(P)` of cluster variables is finite. -/
@[cluster_algebras "lem_finite_type_iff_finite_cluster_variables"]
theorem IsSeedPattern.isFiniteType_iff [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) :
    IsFiniteType P ↔ (patternClusterVariables hmn P).Finite := by
  classical
  refine ⟨fun h => h.finite_iUnion_clusterVariables hmn, fun hX => ?_⟩
  set X := patternClusterVariables hmn P
  set x₀ := (P .root).extCluster
  have hext : ((fun S : SeedData F m n => S.extCluster) '' Set.range P).Finite := by
    refine (Set.Finite.pi (t := fun _ => X ∪ Set.range x₀)
      fun _ => hX.union (Set.finite_range _)).subset ?_
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩ i -
    by_cases hi : ∃ k : Fin n, i = Fin.castLE hmn k
    · obtain ⟨k, rfl⟩ := hi
      exact Or.inl (mem_patternClusterVariables.2 ⟨t, k, rfl⟩)
    · push Not at hi
      refine Or.inr ⟨i, ?_⟩
      change x₀ i = (P t).extCluster i
      rw [hP.apply_eq_seedMutationSeq_root hmn t,
        seedMutationSeq_extCluster_of_forall_ne_castLE hmn _ _ hi]
  have hrange : Set.range P = ⋃ x ∈ (fun S : SeedData F m n => S.extCluster) '' Set.range P,
      {S ∈ Set.range P | S.extCluster = x} := by
    ext S
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun h => ⟨_, ⟨S, h, rfl⟩, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
  change (Set.range P).Finite
  rw [hrange]
  refine hext.biUnion ?_
  rintro _ ⟨_, ⟨t₀, rfl⟩, rfl⟩
  set x := (P t₀).extCluster
  have hx : AlgebraicIndependent K x := (hP.1 t₀).1.1
  let C : Fin n → Set (Fin m → ℤ) := fun j =>
    {c | ∏ i, x i ^ (c i).toNat + ∏ i, x i ^ (-c i).toNat ∈ (· * x (Fin.castLE hmn j)) '' X}
  have hC : ∀ j, (C j).Finite := fun j =>
    finite_setOf_prod_pow_toNat_add_prod_pow_toNat_mem hx (hX.image _)
  refine ((Set.Finite.pi (t := C) hC).image
    fun f => (⟨x, Matrix.of fun i j => f j i⟩ : SeedData F m n)).subset ?_
  rintro S ⟨⟨t, rfl⟩, hSx⟩
  refine ⟨fun j i => (P t).extExchangeMatrix i j, fun j _ => ?_, SeedData.ext hSx.symm rfl⟩
  obtain ⟨t', ht'⟩ := hP.seedMutationSeq_mem_range hmn t [j]
  have hne : (P t).extCluster (Fin.castLE hmn j) ≠ 0 := (hP.1 t).1.1.ne_zero _
  refine ⟨cluster hmn (P t') j, mem_patternClusterVariables.2 ⟨t', j, rfl⟩, ?_⟩
  have hxt : x = (P t).extCluster := hSx.symm
  simp only [cluster, ht', seedMutationSeq_cons, seedMutationSeq_nil, seedMutation,
    Function.update_self]
  rw [hxt, div_mul_cancel₀ _ hne, exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod]

end ClusterAlgebras
