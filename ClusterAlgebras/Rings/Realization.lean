/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.FreeTuple
public import ClusterAlgebras.FiniteType.Basic
public import ClusterAlgebras.ClusterAlgebra
public import ClusterAlgebras.Subpattern.SeedReindex

/-!
# The realization criterion

Let `Σ` be a seed pattern of rank `n` in `F` over `𝕜`, with `m × n` matrices, cluster variables
`𝒳(Σ)` and frozen variables `x_{n+1}, …, x_m`, and let `R` be an integral domain. A
*realization* of `Σ` in `R` assigns a nonzero element `φ(z)` of `R` to every cluster variable
`z` and a nonzero element `φᵢ` of `R` to every frozen index `i`, so that every exchange
relation of `Σ` becomes an identity in `R` once each cluster variable `z` is replaced by `φ(z)`
and each frozen variable `xᵢ` by `φᵢ`.

The realization criterion [FWZ] says when a realization identifies the cluster algebra `𝒜` of
`Σ` with `R`: if `R` is a `𝕜`-algebra whose fraction field has transcendence degree `m` over `𝕜`
and the values of the realization generate `R` as a `𝕜`-algebra, then exactly one `𝕜`-algebra
isomorphism `𝒜 ≃ R` sends every cluster variable `z` to `φ(z)` and every frozen variable `xᵢ` to
`φᵢ`.

The proof runs through the fraction field `K` of `R`. Along any walk in `𝕋ₙ` the realization
relations determine the tuples `φ̃(t)` from one another, so the tuple `φ̃(t₀)` at any vertex
generates `K` as a field; having `m` entries, it is a free generating tuple of `K`. The field
isomorphism `θ : F ≃ K` with `θ(x̃(t₀)) = φ̃(t₀)` then carries `x̃(t)` to `φ̃(t)` at every
vertex, and so restricts to the required isomorphism `𝒜 ≃ R`.

## Main definitions

* `ClusterAlgebras.realizationTuple`: the tuple `φ̃(t) = (φ(x_{1;t}), …, φ(x_{n;t}), φ_{n+1}, …,
  φ_m)` built from an assignment of values to the cluster and the frozen variables.
* `ClusterAlgebras.Realization`: a realization of a seed pattern in an integral domain.
* `ClusterAlgebras.Realization.tuple`: the tuple `φ̃(t)` of a realization.

## Main results

* `ClusterAlgebras.Realization.isFreeGeneratingTuple`: a generating realization gives a free
  generating tuple `φ̃(t₀)` of the fraction field.
* `ClusterAlgebras.Realization.map_extCluster`: a field homomorphism with
  `θ(x̃(t₀)) = φ̃(t₀)` has `θ(x̃(t)) = φ̃(t)` at every vertex.
* `ClusterAlgebras.Realization.existsUnique_algEquiv`: the realization criterion.

## Implementation notes

* FWZ state the criterion for the coordinate ring of a rational irreducible affine variety of
  dimension `m`. Their proof uses only that it is a domain whose fraction field has
  transcendence degree `m`, which is the generality here.
* The frozen values `φᵢ` are indexed by the positions `i : Fin m` with `n ≤ i`, and the
  cluster values by the elements of `𝒳(Σ)`, so that a realization carries exactly the data of
  [FWZ].
* The exchange monomials have integer exponents and are defined over a field, so the
  realization relations are stated in the fraction field `FractionRing R`; all exponents
  involved are nonnegative, so both sides lie in `R`.
* The definition of a realization uses neither the seed conditions on `P` nor a `𝕜`-algebra
  structure on `R`, so it assumes neither. The agreement lemma is stated for any ring
  homomorphism `θ` from `F` to the fraction field of `R`; in [FWZ] `θ` is a `𝕜`-algebra
  isomorphism.
* The frozen variables `xᵢ` are the same at every vertex of a seed pattern, and the criterion
  asks `ψ(x_{i;t}) = φᵢ` for every vertex `t` and every frozen position `i`.
* The ground field is not assumed to have characteristic zero: nothing here uses it.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

/-- **Induction along the edges of `𝕋ₙ`**: a property of vertices that holds at one vertex and
passes along every edge holds at every vertex. -/
theorem RegularTree.induction_of_adj {n : ℕ} {Q : RegularTree n → Prop} {t₀ : RegularTree n}
    (h₀ : Q t₀) (h : ∀ k t t', RegularTree.Adj k t t' → Q t → Q t') (t : RegularTree n) :
    Q t := by
  obtain ⟨d, s, κ, hs₀, hsd, hs⟩ := RegularTree.exists_walk t₀ t
  have key : ∀ i : Fin (d + 1), Q (s i) := fun i => by
    induction i using Fin.induction with
    | zero => exact hs₀ ▸ h₀
    | succ i ih => exact h _ _ _ (hs i) ih
  exact hsd ▸ key (Fin.last d)

section Membership

variable {F : Type*} {m n : ℕ}

/-- The cluster variable `x_{k;t}` is a cluster variable of the pattern. -/
theorem cluster_mem_patternClusterVariables (hmn : n ≤ m) (P : RegularTree n → SeedData F m n)
    (t : RegularTree n) (k : Fin n) : cluster hmn (P t) k ∈ patternClusterVariables hmn P :=
  Set.mem_iUnion.2 ⟨t, k, rfl⟩

variable (𝕜 : Type*) [Field 𝕜] [Field F] [Algebra 𝕜 F]

/-- The cluster variables of a pattern lie in its cluster algebra. -/
theorem patternClusterVariables_subset_clusterAlgebra (hmn : n ≤ m)
    (P : RegularTree n → SeedData F m n) :
    patternClusterVariables hmn P ⊆ clusterAlgebra 𝕜 hmn P :=
  Set.subset_union_right.trans Algebra.subset_adjoin

/-- Every entry `x_{i;t}` of an extended cluster of a pattern lies in its cluster algebra. -/
theorem extCluster_mem_clusterAlgebra (hmn : n ≤ m) (P : RegularTree n → SeedData F m n)
    (t : RegularTree n) (i : Fin m) : (P t).extCluster i ∈ clusterAlgebra 𝕜 hmn P := by
  by_cases hi : (i : ℕ) < n
  · exact patternClusterVariables_subset_clusterAlgebra 𝕜 hmn P
      (cluster_mem_patternClusterVariables hmn P t ⟨i, hi⟩)
  · exact Algebra.subset_adjoin
      (Set.subset_union_left (Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨t, i, not_lt.1 hi, rfl⟩)))

/-- The cluster algebra of a pattern is generated over `𝕜` by the entries `x_{i;t}` of all its
extended clusters. -/
theorem clusterAlgebra_eq_adjoin_extCluster (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) :
    clusterAlgebra 𝕜 hmn P = Algebra.adjoin 𝕜 (⋃ t, Set.range (P t).extCluster) := by
  refine le_antisymm (Algebra.adjoin_le (Set.union_subset ?_ ?_)) (Algebra.adjoin_le ?_)
  · refine Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin ?_
    obtain ⟨t, i, -, rfl⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨t, i, rfl⟩
  · intro _ hx
    obtain ⟨t, k, rfl⟩ := Set.mem_iUnion.1 hx
    exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨t, _, rfl⟩)
  · intro _ hx
    obtain ⟨t, i, rfl⟩ := Set.mem_iUnion.1 hx
    exact extCluster_mem_clusterAlgebra 𝕜 hmn P t i

end Membership

variable {F R : Type*} {m n : ℕ}

/-- The tuple `φ̃(t) = (φ(x_{1;t}), …, φ(x_{n;t}), φ_{n+1}, …, φ_m)` built from values `φ(z)`
of the cluster variables `z ∈ 𝒳(P)` and values `φᵢ` at the frozen positions `i`. -/
@[cluster_algebras "def_realization"]
def realizationTuple (hmn : n ≤ m) (P : RegularTree n → SeedData F m n)
    (φ : patternClusterVariables hmn P → R) (φfr : {i : Fin m // n ≤ (i : ℕ)} → R)
    (t : RegularTree n) (i : Fin m) : R :=
  if h : (i : ℕ) < n then φ ⟨_, cluster_mem_patternClusterVariables hmn P t ⟨i, h⟩⟩
  else φfr ⟨i, not_lt.1 h⟩

variable [CommRing R] [IsDomain R]

variable (R) in
/-- A **realization** of the seed pattern `P` (of rank `n`, with `m × n` matrices) in the
integral domain `R`: nonzero values `φ(z) ∈ R` of the cluster variables `z ∈ 𝒳(P)` and nonzero
values `φᵢ ∈ R` at the frozen positions `i ∈ [n+1, m]` such that, writing
`φ̃(t) = (φ(x_{1;t}), …, φ(x_{n;t}), φ_{n+1}, …, φ_m)`,
`φ(x_{k;t}) φ(x_{k;t'}) = M⁺ₖ(φ̃(t), B̃(t)) + M⁻ₖ(φ̃(t), B̃(t))` whenever `t —k— t'`. The
exchange monomials are computed in the fraction field of `R`. -/
@[cluster_algebras "def_realization"]
structure Realization (hmn : n ≤ m) (P : RegularTree n → SeedData F m n) where
  /-- The value `φ(z)` of a cluster variable `z`. -/
  clusterValue : patternClusterVariables hmn P → R
  /-- The value `φᵢ` at a frozen position `i`. -/
  frozenValue : {i : Fin m // n ≤ (i : ℕ)} → R
  /-- The values of the cluster variables are nonzero. -/
  clusterValue_ne_zero : ∀ z, clusterValue z ≠ 0
  /-- The values at the frozen positions are nonzero. -/
  frozenValue_ne_zero : ∀ i, frozenValue i ≠ 0
  /-- The realization relations: the exchange relations hold for the values. -/
  exchange : ∀ (k : Fin n) (t t' : RegularTree n), RegularTree.Adj k t t' →
    algebraMap R (FractionRing R)
        (clusterValue ⟨_, cluster_mem_patternClusterVariables hmn P t k⟩ *
          clusterValue ⟨_, cluster_mem_patternClusterVariables hmn P t' k⟩) =
      exchangeMonomialPos
          (algebraMap R (FractionRing R) ∘ realizationTuple hmn P clusterValue frozenValue t)
          (P t).extExchangeMatrix k +
        exchangeMonomialNeg
          (algebraMap R (FractionRing R) ∘ realizationTuple hmn P clusterValue frozenValue t)
          (P t).extExchangeMatrix k

namespace Realization

variable {hmn : n ≤ m} {P : RegularTree n → SeedData F m n} (φ : Realization R hmn P)

/-- The tuple `φ̃(t) = (φ(x_{1;t}), …, φ(x_{n;t}), φ_{n+1}, …, φ_m)` of a realization. -/
def tuple (t : RegularTree n) : Fin m → R :=
  realizationTuple hmn P φ.clusterValue φ.frozenValue t

/-- The entry of `φ̃(t)` in a mutable position `k` is `φ(x_{k;t})`. -/
theorem tuple_castLE (t : RegularTree n) (k : Fin n) :
    φ.tuple t (Fin.castLE hmn k) =
      φ.clusterValue ⟨_, cluster_mem_patternClusterVariables hmn P t k⟩ := by
  simp [tuple, realizationTuple, k.isLt]

/-- The entry of `φ̃(t)` in a frozen position `i` is `φᵢ`. -/
theorem tuple_of_le (t : RegularTree n) (i : Fin m) (hi : n ≤ (i : ℕ)) :
    φ.tuple t i = φ.frozenValue ⟨i, hi⟩ := by
  simp [tuple, realizationTuple, not_lt.2 hi]

/-- The entries of `φ̃(t)` are nonzero. -/
theorem tuple_ne_zero (t : RegularTree n) (i : Fin m) : φ.tuple t i ≠ 0 := by
  unfold tuple realizationTuple
  split_ifs
  exacts [φ.clusterValue_ne_zero _, φ.frozenValue_ne_zero _]

/-- Along an edge `t —k— t'`, the realization relation computes the entry of `φ̃(t')` in
position `k` from `φ̃(t)`, in the fraction field. -/
theorem algebraMap_tuple_of_adj {k : Fin n} {t t' : RegularTree n}
    (h : RegularTree.Adj k t t') :
    algebraMap R (FractionRing R) (φ.tuple t' (Fin.castLE hmn k)) =
      (exchangeMonomialPos (algebraMap R (FractionRing R) ∘ φ.tuple t) (P t).extExchangeMatrix k +
          exchangeMonomialNeg (algebraMap R (FractionRing R) ∘ φ.tuple t)
            (P t).extExchangeMatrix k) /
        algebraMap R (FractionRing R) (φ.tuple t (Fin.castLE hmn k)) := by
  have hne : algebraMap R (FractionRing R) (φ.tuple t (Fin.castLE hmn k)) ≠ 0 :=
    (IsFractionRing.injective R (FractionRing R)).ne_iff' (map_zero _) |>.2
      (φ.tuple_ne_zero t _)
  rw [eq_div_iff hne, mul_comm, ← map_mul, φ.tuple_castLE, φ.tuple_castLE]
  exact φ.exchange k t t' h

section Pattern

variable [Field F] {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 F]

/-- Along an edge `t —k— t'` of a seed pattern, `φ̃(t')` agrees with `φ̃(t)` away from
position `k`. -/
theorem tuple_eq_of_adj (hP : IsSeedPattern 𝕜 hmn P) {k : Fin n} {t t' : RegularTree n}
    (h : RegularTree.Adj k t t') {i : Fin m} (hi : i ≠ Fin.castLE hmn k) :
    φ.tuple t' i = φ.tuple t i := by
  by_cases hin : (i : ℕ) < n
  · have hx : cluster hmn (P t') ⟨i, hin⟩ = cluster hmn (P t) ⟨i, hin⟩ := by
      simp only [cluster, hP.2 k t t' h, seedMutation]
      exact Function.update_of_ne hi _ _
    simp only [tuple, realizationTuple, hin, dif_pos]
    exact congrArg φ.clusterValue (Subtype.ext hx)
  · rw [φ.tuple_of_le _ _ (not_lt.1 hin), φ.tuple_of_le _ _ (not_lt.1 hin)]

/-- If a ring homomorphism `θ` from `F` to the fraction field of `R` carries the extended
cluster `x̃(t₀)` entrywise to `φ̃(t₀)`, then it carries `x̃(t)` entrywise to `φ̃(t)` for every
vertex `t`. -/
@[cluster_algebras "lem_realization_agrees"]
theorem map_extCluster {G : Type*} [FunLike G F (FractionRing R)]
    [RingHomClass G F (FractionRing R)] (hP : IsSeedPattern 𝕜 hmn P) (θ : G)
    {t₀ : RegularTree n}
    (h₀ : ∀ i, θ ((P t₀).extCluster i) = algebraMap R (FractionRing R) (φ.tuple t₀ i))
    (t : RegularTree n) (i : Fin m) :
    θ ((P t).extCluster i) = algebraMap R (FractionRing R) (φ.tuple t i) := by
  revert i
  refine RegularTree.induction_of_adj (Q := fun t => ∀ i, θ ((P t).extCluster i) =
    algebraMap R (FractionRing R) (φ.tuple t i)) h₀ (fun k t t' h ht i => ?_) t
  rw [hP.2 k t t' h]
  by_cases hi : i = Fin.castLE hmn k
  · subst hi
    have hθ : θ ∘ (P t).extCluster = algebraMap R (FractionRing R) ∘ φ.tuple t := funext ht
    simp only [seedMutation, Function.update_self]
    rw [φ.algebraMap_tuple_of_adj h, map_div₀, map_add, map_exchangeMonomialPos,
      map_exchangeMonomialNeg, hθ, ht]
  · simp only [seedMutation, Function.update_of_ne hi]
    rw [φ.tuple_eq_of_adj hP h hi, ht]

variable [Algebra 𝕜 R]

/-- **A generating realization gives a free generating tuple.** Let `R` be a `𝕜`-algebra and an
integral domain whose fraction field `K` has transcendence degree `m` over `𝕜`, and let `φ` be a
realization of the seed pattern `P` in `R` whose values generate `R` as a `𝕜`-algebra. Then for
every vertex `t₀`, the tuple `φ̃(t₀)` is a free generating tuple of `K` over `𝕜`. -/
@[cluster_algebras "lem_realization_generates"]
theorem isFreeGeneratingTuple (hP : IsSeedPattern 𝕜 hmn P)
    (htr : Algebra.trdeg 𝕜 (FractionRing R) = m)
    (hgen : Algebra.adjoin 𝕜 (Set.range φ.clusterValue ∪ Set.range φ.frozenValue) = ⊤)
    (t₀ : RegularTree n) :
    IsFreeGeneratingTuple 𝕜 (algebraMap R (FractionRing R) ∘ φ.tuple t₀) := by
  set K := FractionRing R
  set L := IntermediateField.adjoin 𝕜 (Set.range (algebraMap R K ∘ φ.tuple t₀))
  have hL : ∀ t i, algebraMap R K (φ.tuple t i) ∈ L := by
    refine RegularTree.induction_of_adj (t₀ := t₀)
      (fun i => IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩) fun k t t' h ht i => ?_
    by_cases hi : i = Fin.castLE hmn k
    · subst hi
      rw [φ.algebraMap_tuple_of_adj h]
      exact div_mem (exchangeMonomialPos_add_exchangeMonomialNeg_mem 𝕜 L.toSubalgebra
        fun j _ => ht j) (ht _)
    · rw [φ.tuple_eq_of_adj hP h hi]
      exact ht i
  have hR : ∀ r : R, algebraMap R K r ∈ L := by
    have hle : Algebra.adjoin 𝕜 (Set.range φ.clusterValue ∪ Set.range φ.frozenValue) ≤
        L.toSubalgebra.comap (IsScalarTower.toAlgHom 𝕜 R K) := by
      refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
      · rintro _ ⟨⟨z, hz⟩, rfl⟩
        obtain ⟨t, k, rfl⟩ := Set.mem_iUnion.1 hz
        change algebraMap R K _ ∈ L
        rw [← φ.tuple_castLE t k]
        exact hL t _
      · rintro _ ⟨⟨i, hi⟩, rfl⟩
        change algebraMap R K _ ∈ L
        rw [← φ.tuple_of_le t₀ i hi]
        exact hL t₀ i
    rw [hgen] at hle
    exact fun r => hle Algebra.mem_top
  refine isFreeGeneratingTuple_of_trdeg_eq htr (eq_top_iff.2 fun z _ => ?_)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  exact div_mem (hR a) (hR b)

/-- A `𝕜`-algebra isomorphism from the cluster algebra to `R` sends every cluster variable `z` to
`φ(z)` and every frozen variable `xᵢ` to `φᵢ` iff it sends every `x_{i;t}` to the entry `i` of
`φ̃(t)`. -/
private theorem forall_clusterValue_and_frozenValue_iff (ψ : clusterAlgebra 𝕜 hmn P ≃ₐ[𝕜] R) :
    ((∀ (z : F) (hz : z ∈ patternClusterVariables hmn P),
        ψ ⟨z, patternClusterVariables_subset_clusterAlgebra 𝕜 hmn P hz⟩ =
          φ.clusterValue ⟨z, hz⟩) ∧
      ∀ (t : RegularTree n) (i : Fin m) (hi : n ≤ (i : ℕ)),
        ψ ⟨(P t).extCluster i, extCluster_mem_clusterAlgebra 𝕜 hmn P t i⟩ =
          φ.frozenValue ⟨i, hi⟩) ↔
      ∀ t i, ψ ⟨(P t).extCluster i, extCluster_mem_clusterAlgebra 𝕜 hmn P t i⟩ = φ.tuple t i := by
  refine ⟨fun ⟨h₁, h₂⟩ t i => ?_, fun h => ⟨fun z hz => ?_, fun t i hi => ?_⟩⟩
  · by_cases hi : (i : ℕ) < n
    · simp only [tuple, realizationTuple, hi, dif_pos]
      exact h₁ _ _
    · rw [φ.tuple_of_le t i (not_lt.1 hi)]
      exact h₂ t i _
  · obtain ⟨t, k, rfl⟩ := Set.mem_iUnion.1 hz
    exact (h t (Fin.castLE hmn k)).trans (φ.tuple_castLE t k)
  · exact (h t i).trans (φ.tuple_of_le t i hi)

/-- A `𝕜`-algebra map `θ : F → Frac(R)` with `θ(x̃(t)) = φ̃(t)` at every vertex carries the
cluster algebra onto the image of `R`, when the values of `φ` generate `R`. -/
private theorem map_clusterAlgebra_eq_range (θ : F →ₐ[𝕜] FractionRing R)
    (hθ : ∀ t i, θ ((P t).extCluster i) = algebraMap R (FractionRing R) (φ.tuple t i))
    (hgen : Algebra.adjoin 𝕜 (Set.range φ.clusterValue ∪ Set.range φ.frozenValue) = ⊤) :
    (clusterAlgebra 𝕜 hmn P).map θ = (IsScalarTower.toAlgHom 𝕜 R (FractionRing R)).range := by
  rw [clusterAlgebra_eq_adjoin_extCluster 𝕜 hmn P, AlgHom.map_adjoin, ← Algebra.map_top, ← hgen,
    AlgHom.map_adjoin]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨_, hw, rfl⟩
    obtain ⟨t, i, rfl⟩ := Set.mem_iUnion.1 hw
    refine Algebra.subset_adjoin ⟨φ.tuple t i, ?_, (hθ t i).symm⟩
    unfold tuple realizationTuple
    split_ifs
    exacts [Or.inl ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩]
  · rintro _ ⟨r, ⟨⟨z, hz⟩, rfl⟩ | ⟨⟨i, hi⟩, rfl⟩, rfl⟩
    · obtain ⟨t, k, rfl⟩ := Set.mem_iUnion.1 hz
      refine Algebra.subset_adjoin ⟨_, Set.mem_iUnion.2 ⟨t, Fin.castLE hmn k, rfl⟩, ?_⟩
      rw [hθ, φ.tuple_castLE]
      rfl
    · refine Algebra.subset_adjoin ⟨_, Set.mem_iUnion.2 ⟨.root, i, rfl⟩, ?_⟩
      rw [hθ, φ.tuple_of_le _ i hi]
      rfl

/-- **The realization criterion.** Let `P` be a seed pattern of rank `n` in `F` over `𝕜`, with
`m × n` matrices, and let `R` be a `𝕜`-algebra and an integral domain whose fraction field has
transcendence degree `m` over `𝕜`. If `φ` is a realization of `P` in `R` whose values generate
`R` as a `𝕜`-algebra, then exactly one `𝕜`-algebra isomorphism `ψ` from the cluster algebra of
`P` to `R` has `ψ(z) = φ(z)` for every cluster variable `z` and `ψ(xᵢ) = φᵢ` for every frozen
variable `xᵢ`. -/
@[cluster_algebras "prop_geom_realization"]
theorem existsUnique_algEquiv (hP : IsSeedPattern 𝕜 hmn P)
    (htr : Algebra.trdeg 𝕜 (FractionRing R) = m)
    (hgen : Algebra.adjoin 𝕜 (Set.range φ.clusterValue ∪ Set.range φ.frozenValue) = ⊤) :
    ∃! ψ : clusterAlgebra 𝕜 hmn P ≃ₐ[𝕜] R,
      (∀ (z : F) (hz : z ∈ patternClusterVariables hmn P),
        ψ ⟨z, patternClusterVariables_subset_clusterAlgebra 𝕜 hmn P hz⟩ =
          φ.clusterValue ⟨z, hz⟩) ∧
      ∀ (t : RegularTree n) (i : Fin m) (hi : n ≤ (i : ℕ)),
        ψ ⟨(P t).extCluster i, extCluster_mem_clusterAlgebra 𝕜 hmn P t i⟩ =
          φ.frozenValue ⟨i, hi⟩ := by
  set K := FractionRing R
  set A := clusterAlgebra 𝕜 hmn P
  have hx := (hP.1 .root).1
  have hy := φ.isFreeGeneratingTuple hP htr hgen .root
  set θ := hx.algEquiv hy
  have hθ : ∀ t i, θ ((P t).extCluster i) = algebraMap R K (φ.tuple t i) :=
    φ.map_extCluster hP θ (hx.algEquiv_apply hy)
  set ι := IsScalarTower.toAlgHom 𝕜 R K
  have hι : Function.Injective ι := IsFractionRing.injective R K
  let ψ : A ≃ₐ[𝕜] R := (A.equivMapOfInjective (θ : F →ₐ[𝕜] K) θ.injective).trans
    ((Subalgebra.equivOfEq _ _ (φ.map_clusterAlgebra_eq_range (θ : F →ₐ[𝕜] K) hθ hgen)).trans
      (AlgEquiv.ofInjective ι hι).symm)
  have hψ : ∀ a : A, ι (ψ a) = θ a := fun a => by
    rw [← AlgEquiv.ofInjective_apply ι hι]
    simp only [ψ, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    rfl
  have hψt : ∀ t i, ψ ⟨(P t).extCluster i, extCluster_mem_clusterAlgebra 𝕜 hmn P t i⟩ =
      φ.tuple t i := fun t i => hι ((hψ _).trans (hθ t i))
  refine ⟨ψ, (φ.forall_clusterValue_and_frozenValue_iff ψ).2 hψt,
    fun ψ' h' => AlgEquiv.coe_algHom_injective ?_⟩
  refine AlgHom.ext_of_eq_adjoin (clusterAlgebra_eq_adjoin_extCluster 𝕜 hmn P) fun z hz => ?_
  obtain ⟨t, i, rfl⟩ := Set.mem_iUnion.1 hz
  exact ((φ.forall_clusterValue_and_frozenValue_iff ψ').1 h' t i).trans (hψt t i).symm

end Pattern

end Realization

end ClusterAlgebras
