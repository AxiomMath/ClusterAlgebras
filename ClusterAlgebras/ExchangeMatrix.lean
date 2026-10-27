/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Quiver
public import ClusterAlgebras.MatrixMutation

/-!
# Exchange matrices, and quiver mutation seen as matrix mutation

A labelling numbers the vertices of a quiver so that the mutable ones come first. Reading the
signed count off in that numbering gives the extended exchange matrix, an `m × n` integer matrix
whose rows run over all the vertices and whose columns run over the mutable ones only.

## Main definitions

* `exchangeMatrix`: The square submatrix of the extended exchange matrix whose rows and columns
  are both indexed by mutable vertices.

## Main results

* `exchangeMatrix_transpose`: The exchange matrix is skew-symmetric.
* `extExchangeMatrix_mutate`: The extended exchange matrix of the mutation of a quiver at a
  mutable vertex is the matrix mutation of its extended exchange matrix in the corresponding
  direction.
-/
@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {V : Type*} {m n : ℕ}

/-- Negating a signed count swaps its arguments. -/
theorem neg_signedCount (a : V → V → ℕ) (x y : V) :
    -signedCount a x y = signedCount a y x := by
  simp only [signedCount]
  ring

/-- For a two-cycle-free arrow system, `max 0` of the signed count from `x` to `y` is the
number of arrows from `x` to `y`. -/
theorem max_zero_signedCount {a : V → V → ℕ} (h : TwoCycleFree a) (x y : V) :
    max 0 (signedCount a x y) = (a x y : ℤ) := by
  rcases h x y with h0 | h0
  · rw [max_eq_left, h0, Nat.cast_zero]
    simp only [signedCount, h0, Nat.cast_zero, zero_sub, neg_nonpos]
    positivity
  · rw [max_eq_right]
    · simp [signedCount, h0]
    · simp only [signedCount, h0, Nat.cast_zero, sub_zero]
      positivity

section Labelling

variable [Fintype V]

attribute [cluster_algebras "def_labelling"] Labelling

variable {Q : Quiver V}

/-- The vertex named by a column index is mutable. -/
theorem Labelling.notMem_frozen (L : Labelling Q m n) (j : Fin n) :
    L.equiv (Fin.castLE L.le j) ∉ Q.frozen := by
  rw [L.mem_frozen_iff, Fin.val_castLE]
  have := j.isLt
  omega

attribute [cluster_algebras "def_extended_exchange_matrix"] extExchangeMatrix

/-- The **exchange matrix**: the first `n` rows of the extended exchange matrix, so that both
indices name mutable vertices. -/
@[cluster_algebras "def_exchange_matrix"]
def exchangeMatrix (Q : Quiver V) (L : Labelling Q m n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => extExchangeMatrix Q L (Fin.castLE L.le i) j

/-- The exchange matrix is skew-symmetric. -/
@[cluster_algebras "lem_exchange_matrix_skew"]
theorem exchangeMatrix_transpose (Q : Quiver V) (L : Labelling Q m n) :
    (exchangeMatrix Q L)ᵀ = -exchangeMatrix Q L := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, exchangeMatrix, extExchangeMatrix,
    Matrix.of_apply]
  exact (neg_signedCount _ _ _).symm

end Labelling

section Mutation

variable [Fintype V] [DecidableEq V] {Q : Quiver V}

/-- The labelling of a mutated quiver induced by `L` has the same numbering of vertices as
`L`. -/
@[simp]
theorem Labelling.equiv_mutate (L : Labelling Q m n) {k : V} (hk : k ∉ Q.frozen) :
    (L.mutate hk).equiv = L.equiv := rfl

/-- If `x = w` or `y = w`, then the reversal at `w` of `Q.stepOne w` has as many arrows from
`x` to `y` as `Q` has from `y` to `x`. -/
theorem reversal_stepOne_of_eq (Q : Quiver V) (w x y : V) (h : x = w ∨ y = w) :
    reversal (Q.stepOne w) w x y = Q.arrows y x := by
  rw [reversal, if_pos h]
  rcases h with h | h
  · exact h ▸ Q.stepOne_self_right w y
  · exact h ▸ Q.stepOne_self_left w x

/-- If `x ≠ w`, `y ≠ w` and at least one of `x`, `y` is mutable, then the reversal at `w` of
`Q.stepOne w` has, from `x` to `y`, the arrows of `Q` from `x` to `y` plus the number of paths
`x → w → y` in `Q`. -/
theorem reversal_stepOne_of_ne (Q : Quiver V) (w x y : V) (hx : x ≠ w) (hy : y ≠ w)
    (hf : x ∉ Q.frozen ∨ y ∉ Q.frozen) :
    reversal (Q.stepOne w) w x y = Q.arrows x y + Q.arrows x w * Q.arrows w y := by
  rw [reversal, if_neg (not_or.mpr ⟨hx, hy⟩), Quiver.stepOne]
  rcases hf with hf | hf
  · rw [if_neg (not_and_of_not_left _ hf)]
  · rw [if_neg (not_and_of_not_right _ hf)]

/-- **Mutating the quiver is mutating its matrix.** The extended exchange matrix of the
mutation of `Q` at the vertex labelled by `k` is the matrix mutation, in direction `k`, of the
extended exchange matrix of `Q`. -/
@[cluster_algebras "lem_adjmatrix"]
theorem extExchangeMatrix_mutate (Q : Quiver V) (L : Labelling Q m n) (k : Fin n) :
    extExchangeMatrix (Q.mutate (L.notMem_frozen k)) (L.mutate (L.notMem_frozen k))
      = matrixMutation L.le (extExchangeMatrix Q L) k := by
  ext i j
  simp only [extExchangeMatrix, Matrix.of_apply, Labelling.equiv_mutate,
    Quiver.arrows_mutate, Quiver.mutationArrows, signedCount_cancellation]
  by_cases h : i = Fin.castLE L.le k ∨ j = k
  · have hvert : L.equiv i = L.equiv (Fin.castLE L.le k)
        ∨ L.equiv (Fin.castLE L.le j) = L.equiv (Fin.castLE L.le k) := by
      rcases h with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    have e1 := reversal_stepOne_of_eq Q (L.equiv (Fin.castLE L.le k)) (L.equiv i)
      (L.equiv (Fin.castLE L.le j)) hvert
    have e2 := reversal_stepOne_of_eq Q (L.equiv (Fin.castLE L.le k))
      (L.equiv (Fin.castLE L.le j)) (L.equiv i) hvert.symm
    rw [matrixMutation_apply_of_eq L.le _ k h]
    simp only [Matrix.of_apply, signedCount, e1, e2]
    ring
  · rw [not_or] at h
    obtain ⟨hi, hj⟩ := h
    have hune : L.equiv i ≠ L.equiv (Fin.castLE L.le k) := fun h' => hi (L.equiv.injective h')
    have hvne : L.equiv (Fin.castLE L.le j) ≠ L.equiv (Fin.castLE L.le k) :=
      fun h' => hj (Fin.castLE_injective L.le (L.equiv.injective h'))
    have hvfree := L.notMem_frozen j
    have e1 := reversal_stepOne_of_ne Q (L.equiv (Fin.castLE L.le k)) (L.equiv i)
      (L.equiv (Fin.castLE L.le j)) hune hvne (Or.inr hvfree)
    have e2 := reversal_stepOne_of_ne Q (L.equiv (Fin.castLE L.le k))
      (L.equiv (Fin.castLE L.le j)) (L.equiv i) hvne hune (Or.inl hvfree)
    rw [matrixMutation_apply_of_ne_eq_max L.le _ k hi hj]
    simp only [Matrix.of_apply, neg_signedCount, max_zero_signedCount Q.twoCycleFree]
    simp only [signedCount, e1, e2, Nat.cast_add, Nat.cast_mul]
    ring

end Mutation

end ClusterAlgebras
