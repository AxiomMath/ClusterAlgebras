/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.Classification
public import ClusterAlgebras.TwoFinite.CartanProducts
public import ClusterAlgebras.Decomposable.Basic

/-!
# The finite type classification

A `2`-finite exchange matrix is mutation equivalent to one whose Cartan counterpart is a Cartan
matrix of finite type. Together with the finiteness of seed patterns whose exchange matrix has
a Cartan counterpart of finite type, this shows that a seed pattern is of finite type if and
only if its exchange matrix is `2`-finite, if and only if some exchange matrix of the pattern
has a Cartan counterpart of finite type.

## Main results

* `ClusterAlgebras.IsTwoFinite.exists_mutationEquiv_isCartanFiniteType`: a `2`-finite matrix is
  mutation equivalent to a matrix whose Cartan counterpart is of finite type.
* `ClusterAlgebras.IsSeedPattern.exists_principalPart_matrixMutationList`: the exchange matrix
  of the seed reached by a sequence of mutations is the matrix mutation of the original one
  along that sequence.
* `ClusterAlgebras.IsSeedPattern.tfae_isFiniteType`: for a seed pattern, being of finite type,
  `2`-finiteness of an exchange matrix, and mutation equivalence of that matrix to one with a
  Cartan counterpart of finite type are equivalent.
* `ClusterAlgebras.IsSeedPattern.isFiniteType_iff_exists_isCartanFiniteType`: a seed pattern is
  of finite type if and only if some exchange matrix has a Cartan counterpart of finite type.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

variable {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] {m n : ℕ}

/-- **A `2`-finite matrix has a mutation with Cartan counterpart of finite type**: some `B'`
mutation equivalent to `B` has `A(B')` a Cartan matrix of finite type. -/
@[cluster_algebras "prop_two_finite_cartan_counterpart"]
theorem IsTwoFinite.exists_mutationEquiv_isCartanFiniteType {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsTwoFinite B) :
    ∃ B' : Matrix (Fin n) (Fin n) ℤ, MutationEquiv B B' ∧
      IsCartanFiniteType (cartanCounterpart B') := by
  obtain ⟨Xs, hrank, C, ⟨σ, hσ⟩, hBC⟩ := hB.exists_isOfDynkinClass
  subst hrank
  obtain ⟨B₀, hBB₀, hdiag⟩ := hBC.exists_mutationEquiv
  have h₂ : IsTwoFinite B₀ := by
    obtain ⟨s, π, rfl⟩ := hBB₀
    exact (hB.matrixMutationList s).submatrix π.toEmbedding
  have hskew : SkewSymmetrizable (B₀.submatrix σ σ) :=
    h₂.1.submatrix_embedding σ.toEmbedding
  have hdiagσ := diagram_submatrix_eq_of_diagram_eq hdiag σ.toEmbedding
  simp only [Equiv.coe_toEmbedding] at hdiagσ
  have hw := ((hskew.diagram_eq_iff hσ.1).1 hdiagσ).1
  have horient : IsOrientationOfWeighted (B₀.submatrix σ σ) (dynkinWeightedGraph Xs) :=
    ⟨hskew, fun i j => (hw i j).trans (hσ.2 i j)⟩
  refine ⟨B₀, hBB₀, ?_⟩
  have := horient.isCartanFiniteType_cartanCounterpart.submatrix_perm σ.symm
  rwa [← cartanCounterpart_submatrix_perm, Matrix.submatrix_submatrix,
    Equiv.self_comp_symm, Matrix.submatrix_id_id] at this

/-- **Exchange matrices along a sequence of mutations**: for a seed pattern `P`, a vertex
`t₀` and a sequence `s`, some vertex `t` has `P t = μ_s(P t₀)`, and the exchange matrix of
`P t` is `μ_s` of the exchange matrix of `P t₀`. -/
@[cluster_algebras "lem_pattern_exchange_matrix_walk"]
theorem IsSeedPattern.exists_principalPart_matrixMutationList (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n)
    (s : List (Fin n)) :
    ∃ t, P t = seedMutationSeq hmn (P t₀) s ∧
      principalPart hmn (P t).extExchangeMatrix =
        matrixMutationList le_rfl (principalPart hmn (P t₀).extExchangeMatrix) s := by
  have key : ∀ S : SeedData F m n, principalPart hmn (seedMutationSeq hmn S s).extExchangeMatrix =
      matrixMutationList le_rfl (principalPart hmn S.extExchangeMatrix) s := by
    induction s with
    | nil => exact fun _ => rfl
    | cons k s ih =>
      intro S
      rw [seedMutationSeq_cons, ih, matrixMutationList_cons]
      exact congrArg (matrixMutationList le_rfl · s) (principalPart_matrixMutation hmn _ k)
  obtain ⟨t, ht⟩ := hP.seedMutationSeq_mem_range hmn t₀ s
  exact ⟨t, ht, by rw [ht]; exact key _⟩

/-- A matrix mutation equivalent to the exchange matrix of a seed of a pattern, with Cartan
counterpart of finite type, gives a vertex whose exchange matrix has Cartan counterpart of
finite type. -/
private theorem IsSeedPattern.exists_isCartanFiniteType_of_mutationEquiv (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n)
    {B' : Matrix (Fin n) (Fin n) ℤ}
    (hB' : MutationEquiv (principalPart hmn (P t₀).extExchangeMatrix) B')
    (hA : IsCartanFiniteType (cartanCounterpart B')) :
    ∃ t, IsCartanFiniteType (cartanCounterpart (principalPart hmn (P t).extExchangeMatrix)) := by
  obtain ⟨s, π, rfl⟩ := hB'
  obtain ⟨t, -, ht⟩ := hP.exists_principalPart_matrixMutationList hmn t₀ s
  refine ⟨t, ?_⟩
  have := hA.submatrix_perm π.symm
  rwa [← cartanCounterpart_submatrix_perm, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id, ← ht] at this

/-- **Finite type, Cartan counterparts and `2`-finiteness.** For a seed pattern `P` and a
vertex `t₀` with exchange matrix `B`, the following are equivalent: (1) some `B'` mutation
equivalent to `B` has `A(B')` of finite type; (2) `P` is of finite type; (3) `B` is
`2`-finite. -/
@[cluster_algebras "thm_finite_type_bound_by_three"]
theorem IsSeedPattern.tfae_isFiniteType [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) (t₀ : RegularTree n) :
    List.TFAE
      [∃ B' : Matrix (Fin n) (Fin n) ℤ,
          MutationEquiv (principalPart hmn (P t₀).extExchangeMatrix) B' ∧
            IsCartanFiniteType (cartanCounterpart B'),
        IsFiniteType P,
        IsTwoFinite (principalPart hmn (P t₀).extExchangeMatrix)] := by
  tfae_have 1 → 2 := fun ⟨_, hB', hA⟩ => by
    obtain ⟨_, ht⟩ := hP.exists_isCartanFiniteType_of_mutationEquiv hmn t₀ hB' hA
    exact hP.isFiniteType_of_isCartanFiniteType hmn ht
  tfae_have 2 → 3 := fun hfin => hP.isTwoFinite_of_isFiniteType hmn hfin t₀
  tfae_have 3 → 1 := IsTwoFinite.exists_mutationEquiv_isCartanFiniteType
  tfae_finish

/-- **The finite type classification.** A seed pattern is of finite type if and only if, for
some vertex `t`, the Cartan counterpart of the exchange matrix of `P t` is a Cartan matrix of
finite type. -/
@[cluster_algebras "thm_finite_type_classification"]
theorem IsSeedPattern.isFiniteType_iff_exists_isCartanFiniteType [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) :
    IsFiniteType P ↔
      ∃ t, IsCartanFiniteType (cartanCounterpart (principalPart hmn (P t).extExchangeMatrix)) := by
  refine ⟨fun hfin => ?_, fun ⟨_, ht⟩ => hP.isFiniteType_of_isCartanFiniteType hmn ht⟩
  obtain ⟨B', hB', hA⟩ := ((hP.tfae_isFiniteType hmn RegularTree.root).out 1 0).1 hfin
  exact hP.exists_isCartanFiniteType_of_mutationEquiv hmn _ hB' hA

end ClusterAlgebras
