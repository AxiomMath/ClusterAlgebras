/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.SkewSymmetrization
public import ClusterAlgebras.TwoFinite.Weights

/-!
# Mutation equivalence of diagrams and `2`-finiteness

Mutation equivalence of diagrams `B ∼ B'` is an equivalence relation on skew-symmetrizable
matrices; mutations of a subdiagram can be performed inside the whole diagram; and
`2`-finiteness is a property of the diagram, invariant under `∼` and inherited by subdiagrams.

## Main results

* `ClusterAlgebras.DiagramEquiv.refl`, `ClusterAlgebras.DiagramEquiv.symm`,
  `ClusterAlgebras.DiagramEquiv.trans`: `∼` is an equivalence relation.
* `ClusterAlgebras.DiagramEquiv.exists_submatrix`: if `B^r ∼ C` for an injective `r`, the
  corresponding mutations can be performed inside `B`.
* `ClusterAlgebras.SkewSymmetrizable.isTwoFinite_iff`: a skew-symmetrizable `B` is `2`-finite
  exactly when every mutation of `B` has all weights at most `3`.
* `ClusterAlgebras.DiagramEquiv.isTwoFinite_iff`: `2`-finiteness is invariant under `∼`.
* `ClusterAlgebras.IsTwoFinite.submatrix`: subdiagrams of a `2`-finite matrix are `2`-finite.
-/

@[expose] public section

namespace ClusterAlgebras

variable {n m : ℕ}

/-! ### Diagrams of reindexed matrices -/

section Reindex

/-- If `B` and `B'` have the same diagram, so do `B.submatrix π π` and `B'.submatrix π π`. -/
private theorem diagram_submatrix_perm_eq_of_diagram_eq {B B' : Matrix (Fin n) (Fin n) ℤ}
    (h : diagram (B.map (Int.cast : ℤ → ℝ)) = diagram (B'.map (Int.cast : ℤ → ℝ)))
    (π : Equiv.Perm (Fin n)) :
    diagram ((B.submatrix π π).map (Int.cast : ℤ → ℝ)) =
      diagram ((B'.submatrix π π).map (Int.cast : ℤ → ℝ)) := by
  simpa using diagram_submatrix_eq_of_diagram_eq h π.toEmbedding

end Reindex

/-! ### Properties of mutation equivalence of diagrams -/

section Props

variable {B B' B'' : Matrix (Fin n) (Fin n) ℤ}

/-- Matrices with the same diagram have mutations along any sequence with the same diagram. -/
@[cluster_algebras "lem_diagram_equivalence_props"]
theorem diagram_matrixMutationList_eq_of_diagram_eq (hB : SkewSymmetrizable B)
    (hB' : SkewSymmetrizable B')
    (h : diagram (B.map (Int.cast : ℤ → ℝ)) = diagram (B'.map (Int.cast : ℤ → ℝ)))
    (t : List (Fin n)) :
    diagram ((matrixMutationList le_rfl B t).map (Int.cast : ℤ → ℝ)) =
      diagram ((matrixMutationList le_rfl B' t).map (Int.cast : ℤ → ℝ)) := by
  induction t generalizing B B' with
  | nil => simpa using h
  | cons k t ih =>
    refine ih (skewSymmetrizable_matrixMutationList hB [k])
      (skewSymmetrizable_matrixMutationList hB' [k]) ?_
    rw [matrixMutation_map_intCast, matrixMutation_map_intCast]
    exact diagram_matrixMutation_eq_of_diagram_eq (skewSymmetrizable_map_intCast hB)
      (skewSymmetrizable_map_intCast hB') h le_rfl k

/-- Mutation equivalent matrices have mutation equivalent diagrams. -/
@[cluster_algebras "lem_diagram_equivalence_props"]
theorem MutationEquiv.diagramEquiv (h : MutationEquiv B B') : DiagramEquiv B B' := by
  obtain ⟨s, π, rfl⟩ := h
  exact ⟨s, π, rfl⟩

/-- Matrices with the same diagram have mutation equivalent diagrams. -/
@[cluster_algebras "lem_diagram_equivalence_props"]
theorem diagramEquiv_of_diagram_eq
    (h : diagram (B.map (Int.cast : ℤ → ℝ)) = diagram (B'.map (Int.cast : ℤ → ℝ))) :
    DiagramEquiv B B' :=
  ⟨[], 1, by simpa using h⟩

/-- The relation `∼` is reflexive. -/
@[cluster_algebras "lem_diagram_equivalence_props"]
theorem DiagramEquiv.refl (B : Matrix (Fin n) (Fin n) ℤ) : DiagramEquiv B B :=
  diagramEquiv_of_diagram_eq rfl

/-- The relation `∼` is symmetric on skew-symmetrizable matrices. -/
@[cluster_algebras "lem_diagram_equivalence_props"]
theorem DiagramEquiv.symm (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B')
    (h : DiagramEquiv B B') : DiagramEquiv B' B := by
  obtain ⟨s, π, h⟩ := h
  refine ⟨s.reverse.map π.symm, π.symm, ?_⟩
  have hX := skewSymmetrizable_submatrix (skewSymmetrizable_matrixMutationList hB s) π
  have key := diagram_submatrix_perm_eq_of_diagram_eq
    (diagram_matrixMutationList_eq_of_diagram_eq hX hB' h (s.reverse.map π.symm)) π.symm
  rw [← key, matrixMutationList_submatrix, Matrix.submatrix_submatrix, List.map_map,
    Equiv.self_comp_symm, List.map_id, matrixMutationList_reverse_matrixMutationList,
    Matrix.submatrix_id_id]

/-- The relation `∼` is transitive on skew-symmetrizable matrices. -/
@[cluster_algebras "lem_diagram_equivalence_props"]
theorem DiagramEquiv.trans (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B')
    (h : DiagramEquiv B B') (h' : DiagramEquiv B' B'') : DiagramEquiv B B'' := by
  obtain ⟨s, π, h⟩ := h
  obtain ⟨t, ρ, h'⟩ := h'
  refine ⟨s ++ t.map π, π * ρ, ?_⟩
  have hX := skewSymmetrizable_submatrix (skewSymmetrizable_matrixMutationList hB s) π
  have key := diagram_submatrix_perm_eq_of_diagram_eq
    (diagram_matrixMutationList_eq_of_diagram_eq hX hB' h t) ρ
  rw [← h', ← key, matrixMutationList_submatrix, Matrix.submatrix_submatrix,
    ← matrixMutationList_append, Equiv.Perm.coe_mul]

/-- Being of Dynkin class `X` is transported backwards along `∼`: if `B ∼ B'` and `B'` is of
Dynkin class `X`, so is `B`. -/
theorem IsOfDynkinClass.of_diagramEquiv (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B')
    (h : DiagramEquiv B B') {Xs : List DynkinSymbol} (h' : IsOfDynkinClass B' Xs) :
    IsOfDynkinClass B Xs :=
  let ⟨C, hC, hC'⟩ := h'
  ⟨C, hC, h.trans hB hB' hC'⟩

/-- If `B ∼ B'`, some matrix mutation equivalent to `B` has the diagram of `B'`. -/
@[cluster_algebras "lem_diagram_equivalence_props"]
theorem DiagramEquiv.exists_mutationEquiv (h : DiagramEquiv B B') :
    ∃ B''' : Matrix (Fin n) (Fin n) ℤ, MutationEquiv B B''' ∧
      diagram (B'''.map (Int.cast : ℤ → ℝ)) = diagram (B'.map (Int.cast : ℤ → ℝ)) := by
  obtain ⟨s, π, h⟩ := h
  exact ⟨_, ⟨s, π, rfl⟩, h⟩

end Props

/-! ### Mutating a subdiagram inside a diagram -/

/-- **Mutating a subdiagram inside a diagram.** If `B^r ∼ C` for an injective `r`, there are a
sequence `s̃` of elements of the image of `r` and a permutation `π` of `[1, m]` such that
`B̃ = μ_{s̃}(B)`, which is mutation equivalent to `B`, and `r̃ = r ∘ π`, which has the image of
`r`, satisfy `Γ(B̃^{r̃}) = Γ(C)`. -/
@[cluster_algebras "lem_diagram_transport"]
theorem DiagramEquiv.exists_submatrix {B : Matrix (Fin n) (Fin n) ℤ} (r : Fin m ↪ Fin n)
    {C : Matrix (Fin m) (Fin m) ℤ} (h : DiagramEquiv (B.submatrix r r) C) :
    ∃ (s : List (Fin n)) (π : Equiv.Perm (Fin m)), (∀ x ∈ s, x ∈ Set.range r) ∧
      MutationEquiv B (matrixMutationList le_rfl B s) ∧
      Set.range (r ∘ π) = Set.range r ∧
      diagram (((matrixMutationList le_rfl B s).submatrix (r ∘ π) (r ∘ π)).map
        (Int.cast : ℤ → ℝ)) = diagram (C.map (Int.cast : ℤ → ℝ)) := by
  obtain ⟨s, π, h⟩ := h
  refine ⟨s.map r, π, fun x hx => ?_, mutationEquiv_matrixMutationList B _, ?_, ?_⟩
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨y, rfl⟩
  · exact π.surjective.range_comp r
  · rw [← h, matrixMutationList_submatrix_embedding, Matrix.submatrix_submatrix]

/-! ### `2`-finiteness of diagrams -/

/-- A skew-symmetrizable matrix is `2`-finite exactly when every mutation `μ_s(B)` has all
weights at most `3`. -/
@[cluster_algebras "lem_two_finite_diagram"]
theorem SkewSymmetrizable.isTwoFinite_iff {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) :
    IsTwoFinite B ↔ ∀ (s : List (Fin n)) (i j : Fin n),
      diagramWeight (matrixMutationList le_rfl B s) i j ≤ 3 := by
  refine ⟨fun h s i j => ?_, fun h => ⟨hB, fun B' ⟨s, π, hB'⟩ i j => ?_⟩⟩
  · rw [diagramWeight, ← Int.ofNat_le, Int.natCast_natAbs]
    exact h.2 _ (mutationEquiv_matrixMutationList B s) i j
  · subst hB'
    have := h s (π i) (π j)
    rwa [diagramWeight, ← Int.ofNat_le, Int.natCast_natAbs] at this

/-- A `2`-finite matrix has all weights at most `3`. -/
@[cluster_algebras "lem_two_finite_diagram"]
theorem IsTwoFinite.diagramWeight_le_three {B : Matrix (Fin n) (Fin n) ℤ} (hB : IsTwoFinite B)
    (i j : Fin n) : diagramWeight B i j ≤ 3 :=
  (SkewSymmetrizable.isTwoFinite_iff hB.1).1 hB [] i j

/-- Mutations of a `2`-finite matrix are `2`-finite. -/
@[cluster_algebras "lem_two_finite_diagram"]
theorem IsTwoFinite.matrixMutationList {B : Matrix (Fin n) (Fin n) ℤ} (hB : IsTwoFinite B)
    (s : List (Fin n)) : IsTwoFinite (matrixMutationList le_rfl B s) := by
  refine ((skewSymmetrizable_matrixMutationList hB.1 s).isTwoFinite_iff).2 fun t i j => ?_
  rw [← matrixMutationList_append]
  exact (hB.1.isTwoFinite_iff).1 hB (s ++ t) i j

/-- `2`-finiteness is transported along `∼`. -/
private theorem isTwoFinite_of_diagramEquiv {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') (h : DiagramEquiv B B')
    (h2 : IsTwoFinite B) : IsTwoFinite B' := by
  obtain ⟨s, π, h⟩ := h
  refine (hB'.isTwoFinite_iff).2 fun t i j => ?_
  have hX := skewSymmetrizable_submatrix (skewSymmetrizable_matrixMutationList hB s) π
  have key := diagram_matrixMutationList_eq_of_diagram_eq hX hB' h t
  rw [matrixMutationList_submatrix, ← matrixMutationList_append] at key
  have hY := skewSymmetrizable_submatrix
    (skewSymmetrizable_matrixMutationList hB (s ++ t.map π)) π
  rw [← ((hY.diagram_eq_iff (skewSymmetrizable_matrixMutationList hB' t)).1 key).1 i j]
  have := (diagramWeight_submatrix (matrixMutationList le_rfl B (s ++ t.map π))
    π.toEmbedding i j).1
  simp only [Equiv.coe_toEmbedding] at this
  rw [this]
  exact (hB.isTwoFinite_iff).1 h2 _ _ _

/-- `2`-finiteness is invariant under mutation equivalence of diagrams. -/
@[cluster_algebras "lem_two_finite_diagram"]
theorem DiagramEquiv.isTwoFinite_iff {B B' : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (hB' : SkewSymmetrizable B') (h : DiagramEquiv B B') :
    IsTwoFinite B ↔ IsTwoFinite B' :=
  ⟨isTwoFinite_of_diagramEquiv hB hB' h, isTwoFinite_of_diagramEquiv hB' hB (h.symm hB hB')⟩

/-- Subdiagrams of a `2`-finite matrix are `2`-finite: `B^r` is `2`-finite for every injective
`r`. -/
@[cluster_algebras "lem_two_finite_diagram"]
theorem IsTwoFinite.submatrix {B : Matrix (Fin n) (Fin n) ℤ} (hB : IsTwoFinite B)
    (r : Fin m ↪ Fin n) : IsTwoFinite (B.submatrix r r) := by
  refine ((skewSymmetrizable_submatrix hB.1 r).isTwoFinite_iff).2 fun t i j => ?_
  rw [matrixMutationList_submatrix_embedding, (diagramWeight_submatrix _ r i j).1]
  exact (hB.1.isTwoFinite_iff).1 hB _ _ _

end ClusterAlgebras
