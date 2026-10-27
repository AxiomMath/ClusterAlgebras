/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.MatrixMutation
public import ClusterAlgebras.External

/-!
# Mutation equivalence of matrices

Two square matrices `B` and `B'` are mutation equivalent when some finite sequence of mutations
`k₁, …, k_r` and some permutation `π` of the indices satisfy
`B'ᵢⱼ = (μ_{k_r} ⋯ μ_{k₁}(B))_{π(i)π(j)}` for all `i, j`. Mutation equivalence is an equivalence
relation: reflexivity is witnessed by the empty sequence and the identity permutation, symmetry
by the reversed sequence, since each mutation is an involution, and transitivity by
concatenation.

## Main definitions

* `matrixMutationList`: Mutation along a finite sequence of directions.
* `MutationEquiv`: Mutation equivalence of square matrices.

## Main results

* `matrixMutation_submatrix`: Mutating `B.submatrix π π` in direction `k` is mutating `B` in
  direction `π k`, then relabelling.
* `mutationEquiv_iff`: Mutation equivalence in entrywise form.
* `mutationEquiv_equivalence`: Mutation equivalence is an equivalence relation.

## Implementation notes

The relabelling is an `Equiv.Perm (Fin n)` acting through `Matrix.submatrix`, and the sequence
of directions is a `List (Fin n)` read left to right. Mutation equivalence is usually stated
for skew-symmetrizable matrices; that hypothesis plays no part in the relation, so it is
defined here for an arbitrary square matrix.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-! ### Iterated mutation -/

/-- Mutation along a finite sequence of directions:
`matrixMutationList hmn B [k₁, …, k_r]` is `μ_{k_r} ⋯ μ_{k₁}(B)`, the list being
read left to right. -/
def matrixMutationList (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (ks : List (Fin n)) :
    Matrix (Fin m) (Fin n) R :=
  ks.foldl (matrixMutation hmn) B

omit [IsStrictOrderedRing R] in
/-- Mutating along the empty sequence of directions leaves the matrix alone. -/
@[simp]
theorem matrixMutationList_nil (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) :
    matrixMutationList hmn B [] = B := rfl

omit [IsStrictOrderedRing R] in
/-- Mutating along `k :: ks` mutates at `k` first, then along `ks`. -/
@[simp]
theorem matrixMutationList_cons (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (ks : List (Fin n)) :
    matrixMutationList hmn B (k :: ks) = matrixMutationList hmn (matrixMutation hmn B k) ks := rfl

omit [IsStrictOrderedRing R] in
/-- Mutating along a one-element sequence is a single mutation. -/
theorem matrixMutationList_singleton (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n) :
    matrixMutationList hmn B [k] = matrixMutation hmn B k := rfl

omit [IsStrictOrderedRing R] in
/-- Mutating along `ks` and then along `ls` is mutating along the concatenation. -/
theorem matrixMutationList_append (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R)
    (ks ls : List (Fin n)) :
    matrixMutationList hmn B (ks ++ ls) =
      matrixMutationList hmn (matrixMutationList hmn B ks) ls :=
  List.foldl_append

/-- Mutating along `ks` and then along `ks.reverse` returns the original matrix. -/
@[simp]
theorem matrixMutationList_reverse_matrixMutationList (hmn : n ≤ m)
    (B : Matrix (Fin m) (Fin n) R) (ks : List (Fin n)) :
    matrixMutationList hmn (matrixMutationList hmn B ks) ks.reverse = B := by
  induction ks generalizing B with
  | nil => rfl
  | cons k ks ih =>
    rw [List.reverse_cons, matrixMutationList_cons, matrixMutationList_append, ih,
      matrixMutationList_singleton, matrixMutation_matrixMutation]

/-! ### Mutation and simultaneous relabelling -/

/-- Mutation is equivariant for a simultaneous relabelling of the rows and the
columns: mutating `B ∘ (π, π)` in direction `k` is mutating `B` in direction
`π k`. -/
theorem matrixMutation_submatrix (hnn : n ≤ n) (B : Matrix (Fin n) (Fin n) R)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    matrixMutation hnn (B.submatrix π π) k = (matrixMutation hnn B (π k)).submatrix π π := by
  ext i j
  rw [submatrix_apply]
  by_cases h : i = k ∨ j = k
  · have h' : π i = Fin.castLE hnn (π k) ∨ π j = π k := by
      simpa using h.imp (fun hi => by rw [hi]) (fun hj => by rw [hj])
    rw [matrixMutation_apply_of_eq hnn _ k (by simpa using h),
      matrixMutation_apply_of_eq hnn B (π k) h', submatrix_apply]
  · rw [not_or] at h
    obtain ⟨hi, hj⟩ := h
    have hi' : π i ≠ Fin.castLE hnn (π k) := by
      simpa using fun hh : π i = π k => hi (π.injective hh)
    have hj' : π j ≠ π k := fun hh => hj (π.injective hh)
    rw [matrixMutation_apply_of_ne_eq_max hnn _ k (by simpa using hi) hj,
      matrixMutation_apply_of_ne_eq_max hnn B (π k) hi' hj']
    simp

/-- The list form of `matrixMutation_submatrix`: relabelling commutes with a
whole sequence of mutations, the sequence of directions being relabelled too. -/
theorem matrixMutationList_submatrix (hnn : n ≤ n) (B : Matrix (Fin n) (Fin n) R)
    (π : Equiv.Perm (Fin n)) (ks : List (Fin n)) :
    matrixMutationList hnn (B.submatrix π π) ks =
      (matrixMutationList hnn B (ks.map π)).submatrix π π := by
  induction ks generalizing B with
  | nil => rfl
  | cons k ks ih => rw [matrixMutationList_cons, matrixMutation_submatrix, ih, List.map_cons,
      matrixMutationList_cons]

/-! ### Mutation equivalence -/

/-- `B` and `B'` are **mutation equivalent** if some finite sequence of
mutations `k₁, …, k_r` and some permutation `π` of the indices satisfy
`B' = μ_{k_r} ⋯ μ_{k₁}(B) ∘ (π, π)`, that is
`B'ᵢⱼ = (μ_{k_r} ⋯ μ_{k₁}(B))_{π(i)π(j)}` for all `i, j`. -/
@[cluster_algebras "def_mut_equiv_matrices"]
def MutationEquiv (B B' : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ (ks : List (Fin n)) (π : Equiv.Perm (Fin n)),
    B' = (matrixMutationList le_rfl B ks).submatrix π π

omit [IsStrictOrderedRing R] in
/-- `B` and `B'` are mutation equivalent if and only if, for some sequence of directions `ks` and
some permutation `π`, `B' i j` is the `(π i, π j)` entry of the mutation of `B` along `ks`. -/
theorem mutationEquiv_iff {B B' : Matrix (Fin n) (Fin n) R} :
    MutationEquiv B B' ↔ ∃ (ks : List (Fin n)) (π : Equiv.Perm (Fin n)),
      ∀ i j, B' i j = matrixMutationList le_rfl B ks (π i) (π j) := by
  refine exists_congr fun ks => exists_congr fun π => ?_
  constructor
  · exact fun h i j => by rw [h, submatrix_apply]
  · exact fun h => by ext i j; rw [h i j, submatrix_apply]

omit [IsStrictOrderedRing R] in
/-- Every matrix is mutation equivalent to itself, by the empty sequence. -/
@[refl]
theorem MutationEquiv.refl (B : Matrix (Fin n) (Fin n) R) : MutationEquiv B B :=
  ⟨[], 1, by simp⟩

omit [IsStrictOrderedRing R] in
/-- A matrix is mutation equivalent to any single mutation of it. -/
theorem mutationEquiv_matrixMutation (B : Matrix (Fin n) (Fin n) R) (k : Fin n) :
    MutationEquiv B (matrixMutation le_rfl B k) :=
  ⟨[k], 1, by simp⟩

omit [IsStrictOrderedRing R] in
/-- A matrix is mutation equivalent to any iterated mutation of it. -/
theorem mutationEquiv_matrixMutationList (B : Matrix (Fin n) (Fin n) R) (ks : List (Fin n)) :
    MutationEquiv B (matrixMutationList le_rfl B ks) :=
  ⟨ks, 1, by simp⟩

omit [IsStrictOrderedRing R] in
/-- A matrix is mutation equivalent to any simultaneous relabelling of it. -/
theorem mutationEquiv_submatrix (B : Matrix (Fin n) (Fin n) R) (π : Equiv.Perm (Fin n)) :
    MutationEquiv B (B.submatrix π π) :=
  ⟨[], π, by simp⟩

/-- Mutation equivalence of matrices is symmetric. -/
@[symm]
theorem MutationEquiv.symm {B B' : Matrix (Fin n) (Fin n) R} (h : MutationEquiv B B') :
    MutationEquiv B' B := by
  obtain ⟨ks, π, rfl⟩ := h
  refine ⟨ks.reverse.map π.symm, π.symm, ?_⟩
  rw [matrixMutationList_submatrix, Matrix.submatrix_submatrix, List.map_map,
    Equiv.self_comp_symm, List.map_id, matrixMutationList_reverse_matrixMutationList,
    submatrix_id_id]

/-- Mutation equivalence of matrices is transitive. -/
@[trans]
theorem MutationEquiv.trans {B B' B'' : Matrix (Fin n) (Fin n) R} (h : MutationEquiv B B')
    (h' : MutationEquiv B' B'') : MutationEquiv B B'' := by
  obtain ⟨ks, π, rfl⟩ := h
  obtain ⟨ls, ρ, rfl⟩ := h'
  refine ⟨ks ++ ls.map π, π * ρ, ?_⟩
  rw [matrixMutationList_submatrix, Matrix.submatrix_submatrix, ← matrixMutationList_append,
    Equiv.Perm.coe_mul]

/-- Mutation equivalence is an equivalence relation. -/
theorem mutationEquiv_equivalence :
    Equivalence (MutationEquiv (R := R) (n := n)) :=
  ⟨MutationEquiv.refl, MutationEquiv.symm, MutationEquiv.trans⟩

end ClusterAlgebras
