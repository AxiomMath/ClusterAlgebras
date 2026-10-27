/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Enumeration.Counts
public import ClusterAlgebras.TypeBC.TypeC
public import ClusterAlgebras.TwoFinite.Defs

/-!
# Reindexing, Cartan counterparts, and the Dynkin type of mutation classes

Reindexing a skew-symmetrizable matrix along an injective map
commutes with taking the Cartan counterpart, and simultaneous permutations compose; so having
the same type is an equivalence relation. Matrices whose Cartan counterparts are of types
`B_n` and `C_n` are not mutation equivalent, and mutation equivalent matrices whose Cartan
counterparts are of single Dynkin types have the same Dynkin symbol.

## Main results

* `ClusterAlgebras.cartanCounterpart_submatrix`: `A(B^r) = A(B)^r`.
* `ClusterAlgebras.SameCartanType.trans` and companions: same type is an equivalence relation.
* `ClusterAlgebras.not_mutationEquiv_of_isOfDynkinType_B_C`: types `B_n` and `C_n` are not
  mutation equivalent.
* `ClusterAlgebras.MutationEquiv.eq_of_isOfDynkinType`: mutation equivalent matrices whose
  Cartan counterparts are of single Dynkin types have the same Dynkin symbol.

## Implementation notes

* `B^r` for an injective `r : [1, n'] → [1, n]` is `B.submatrix r r`; it is `matrixReindex`
  along `squareReindexingMap r` (`matrixReindex_squareReindexingMap`).
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n n' : ℕ}

/-! ### Reindexing and types -/

/-- **Reindexing along an injective map preserves skew-symmetrizability.** -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem SkewSymmetrizable.submatrix_embedding {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (r : Fin n' ↪ Fin n) : SkewSymmetrizable (B.submatrix r r) := by
  obtain ⟨d, hd⟩ := hB
  exact ⟨d ∘ r, fun i => hd.1 (r i), fun i j => hd.2 (r i) (r j)⟩

/-- **Reindexing commutes with the Cartan counterpart**: `A(B^r) = A(B)^r` for an injective
`r`. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem cartanCounterpart_submatrix (B : Matrix (Fin n) (Fin n) ℤ) (r : Fin n' ↪ Fin n) :
    cartanCounterpart (B.submatrix r r) = (cartanCounterpart B).submatrix r r := by
  ext i j
  simp [cartanCounterpart, r.injective.eq_iff]

/-- **Simultaneous permutations compose**: `(M^σ)^τ = M^{σ ∘ τ}`, and `M^{id} = M`. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem submatrix_perm_submatrix_perm {α : Type*} (M : Matrix (Fin n) (Fin n) α)
    (σ τ : Equiv.Perm (Fin n)) :
    (M.submatrix σ σ).submatrix τ τ = M.submatrix (σ ∘ τ) (σ ∘ τ) ∧
      M.submatrix (Equiv.refl (Fin n)) (Equiv.refl (Fin n)) = M :=
  ⟨rfl, rfl⟩

/-- Having the same type is reflexive. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem SameCartanType.refl (A : Matrix (Fin n) (Fin n) ℤ) : SameCartanType A A :=
  ⟨1, fun _ _ => rfl⟩

/-- Having the same type is symmetric. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem SameCartanType.symm {A A' : Matrix (Fin n) (Fin n) ℤ} (h : SameCartanType A A') :
    SameCartanType A' A := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.symm, fun i j => by simp [hσ]⟩

/-- Having the same type is transitive. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem SameCartanType.trans {A A' A'' : Matrix (Fin n) (Fin n) ℤ} (h : SameCartanType A A')
    (h' : SameCartanType A' A'') : SameCartanType A A'' := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨τ, hτ⟩ := h'
  exact ⟨τ.trans σ, fun i j => by simp [hτ, hσ]⟩

/-- **A matrix of the size of `C(X)` is of type `X` exactly when it is `C(X)^σ`** for a
permutation `σ`. -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem isOfDynkinType_iff_exists_perm {Xs : List DynkinSymbol}
    (M : Matrix (Fin (DynkinSymbol.listRank Xs)) (Fin (DynkinSymbol.listRank Xs)) ℤ) :
    IsOfDynkinType M Xs ↔
      ∃ σ : Equiv.Perm (Fin (DynkinSymbol.listRank Xs)),
        M = (DynkinSymbol.listCartan Xs).submatrix σ σ :=
  ⟨fun ⟨σ, hσ⟩ => ⟨σ, Matrix.ext hσ⟩, fun ⟨σ, hσ⟩ => ⟨σ, fun i j => by simp [hσ]⟩⟩

/-- **A simultaneous permutation of a matrix of type `X` is of type `X`.** -/
@[cluster_algebras "lem_cartan_counterpart_reindex"]
theorem IsOfDynkinType.submatrix_perm {M : Matrix (Fin n) (Fin n) ℤ} {Xs : List DynkinSymbol}
    (hM : IsOfDynkinType M Xs) (τ : Equiv.Perm (Fin n)) :
    IsOfDynkinType (M.submatrix τ τ) Xs := by
  obtain ⟨σ, hσ⟩ := hM
  exact ⟨τ.trans σ, fun i j => by simp [hσ]⟩

/-! ### Types `B_n` and `C_n` -/

/-- Two mutation equivalent skew-symmetrizable matrices whose Cartan counterparts are of types
`X` and `Y` are exchange matrices of one seed pattern, which is then of both types. -/
private theorem exists_isPatternOfType_of_mutationEquiv {B' B'' : Matrix (Fin n) (Fin n) ℤ}
    (hB' : SkewSymmetrizable B') (h : MutationEquiv B' B'') {Xs Ys : List DynkinSymbol}
    (hX : IsOfDynkinType (cartanCounterpart B') Xs)
    (hY : IsOfDynkinType (cartanCounterpart B'') Ys) :
    ∃ P : RegularTree n → SeedData (FractionRing (MvPolynomial (Fin n) ℚ)) n n,
      IsSeedPattern ℚ le_rfl P ∧ IsPatternOfType le_rfl P Xs ∧
        IsPatternOfType le_rfl P Ys := by
  have hpp : ∀ M : Matrix (Fin n) (Fin n) ℤ, principalPart le_rfl M = M := fun _ => rfl
  have hext : ExtSkewSymmetrizable le_rfl B' := by
    rwa [ExtSkewSymmetrizable, ← principalPart, hpp]
  obtain ⟨P, hP, hP₀⟩ :=
    exists_isSeedPattern le_rfl RegularTree.root (isLabeledSeed_genericSeed le_rfl hext)
  obtain ⟨ks, π, rfl⟩ := h
  obtain ⟨u, hu⟩ := hP.seedMutationSeq_mem_range le_rfl RegularTree.root ks
  refine ⟨P, hP, ⟨RegularTree.root, by rwa [hP₀, hpp]⟩, ⟨u, ?_⟩⟩
  rw [hu, hpp, seedMutationSeq_extExchangeMatrix_eq_matrixMutationList, hP₀]
  set G := matrixMutationList le_rfl (genericSeed B').extExchangeMatrix ks
  have hG : G = (G.submatrix π π).submatrix π.symm π.symm := by simp
  have hc := cartanCounterpart_submatrix (G.submatrix π π) π.symm.toEmbedding
  rw [Equiv.coe_toEmbedding] at hc
  rw [hG, hc]
  exact hY.submatrix_perm π.symm

/-- **Matrices of types `B_n` and `C_n` are not mutation equivalent.** For `n ≥ 3`, if one of
the Cartan counterparts of the skew-symmetrizable matrices `B'`, `B''` is of type `B_n` and the
other of type `C_n`, then `B'` and `B''` are not mutation equivalent. -/
@[cluster_algebras "lem_type_B_C_not_mutation_equivalent"]
theorem not_mutationEquiv_of_isOfDynkinType_B_C (hn : 3 ≤ n) {B' B'' : Matrix (Fin n) (Fin n) ℤ}
    (hB' : SkewSymmetrizable B') (hB'' : SkewSymmetrizable B'')
    (htype : (IsOfDynkinType (cartanCounterpart B') [DynkinSymbol.B n (by omega)] ∧
        IsOfDynkinType (cartanCounterpart B'') [DynkinSymbol.C n hn]) ∨
      (IsOfDynkinType (cartanCounterpart B') [DynkinSymbol.C n hn] ∧
        IsOfDynkinType (cartanCounterpart B'') [DynkinSymbol.B n (by omega)])) :
    ¬MutationEquiv B' B'' := by
  intro h
  rcases htype with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · obtain ⟨P, hP, hPX, hPY⟩ := exists_isPatternOfType_of_mutationEquiv hB' h hX hY
    exact hP.not_isPatternOfType_B_and_C le_rfl hn ⟨hPX, hPY⟩
  · obtain ⟨P, hP, hPY, hPX⟩ := exists_isPatternOfType_of_mutationEquiv hB'' h.symm hY hX
    exact hP.not_isPatternOfType_B_and_C le_rfl hn ⟨hPY, hPX⟩

/-! ### The indecomposable case -/

/-- **Mutation equivalent matrices of indecomposable finite type have the same Dynkin
symbol.** If the skew-symmetrizable matrices `B'` and `B''` are mutation equivalent and
`A(B')`, `A(B'')` are of types `X` and `Y` for Dynkin symbols `X`, `Y`, then `X = Y`. -/
@[cluster_algebras "lem_mut_equiv_same_symbol"]
theorem MutationEquiv.eq_of_isOfDynkinType {B' B'' : Matrix (Fin n) (Fin n) ℤ}
    (hB' : SkewSymmetrizable B') (hB'' : SkewSymmetrizable B'') (h : MutationEquiv B' B'')
    {X Y : DynkinSymbol} (hX : IsOfDynkinType (cartanCounterpart B') [X])
    (hY : IsOfDynkinType (cartanCounterpart B'') [Y]) : X = Y := by
  obtain ⟨P, hP, hPX, hPY⟩ := exists_isPatternOfType_of_mutationEquiv hB' h hX hY
  obtain ⟨-, ⟨N, hN, hNX⟩, k, hk, hkX⟩ := hP.counts_of_isPatternOfType le_rfl hPX
  obtain ⟨-, ⟨N', hN', hNY⟩, k', hk', hkY⟩ := hP.counts_of_isPatternOfType le_rfl hPY
  have hNN : N = N' := by exact_mod_cast hN.symm.trans hN'
  have hkk : k = k' := by exact_mod_cast hk.symm.trans hk'
  subst hNN hkk
  simp only [DynkinSymbol.listNumClusterVariables, DynkinSymbol.listNumClusters, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.prod_cons, List.prod_nil,
    mul_one] at hNX hNY hkX hkY
  obtain ⟨σ, -⟩ := id hX
  obtain ⟨τ, -⟩ := id hY
  have hXn : X.rank = n := by simpa [DynkinSymbol.listRank] using (Fintype.card_congr σ).symm
  have hYn : Y.rank = n := by simpa [DynkinSymbol.listRank] using (Fintype.card_congr τ).symm
  rcases DynkinSymbol.eq_or_B_C_of_counts (hXn.trans hYn.symm) (hNX.symm.trans hNY)
    (hkX.symm.trans hkY) with hXY | ⟨n₀, hn₀, ⟨hXB, hYC⟩ | ⟨hXC, hYB⟩⟩
  · exact hXY
  · rw [hXB] at hX hXn
    rw [hYC] at hY
    obtain rfl : n₀ = n := hXn
    exact absurd h (not_mutationEquiv_of_isOfDynkinType_B_C hn₀ hB' hB'' (Or.inl ⟨hX, hY⟩))
  · rw [hXC] at hX hXn
    rw [hYB] at hY
    obtain rfl : n₀ = n := hXn
    exact absurd h (not_mutationEquiv_of_isOfDynkinType_B_C hn₀ hB' hB'' (Or.inr ⟨hX, hY⟩))

end ClusterAlgebras
