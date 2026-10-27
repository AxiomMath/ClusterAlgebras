/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib
public import ClusterAlgebras.Attr

/-!
# The three matrices that factor a matrix mutation

Matrix mutation in direction `k` is conjugation-like: it is left multiplication by
`J + E` and right multiplication by `J + F`, where `J` flips one sign on the
diagonal and `E`, `F` collect the clipped entries `max 0 (±ε bᵢⱼ)` of the mutated
column and row. This file defines those three matrices, together with the API a
reader needs to use them without unfolding: their entries, and — for `E` and `F`,
whose whole purpose is to be multiplied against `B` — the single entry of the
products `E * B` and `B * F`.

## Design decisions

* The **sign-flip matrix** `signFlipMatrix R k` is indexed by an arbitrary type
  with decidable equality rather than by `Fin N`. Nothing about it needs the
  order or the size, and the factorisation instantiates it twice, once at `Fin m`
  and once at `Fin n`. Since it is `Matrix.diagonal` of an updated `1`, the
  definition asks only for `Zero`, `One` and `Neg`; the multiplicative facts add
  hypotheses where they are used.
* The sign `ε` is an arbitrary ring element, not a proof-carrying `±1`. Both
  factors are defined for any `ε`, because neither definition needs `ε² = 1`;
  the lemmas that do need it (the factorisation of a mutation, and the value of
  the determinants) can take `ε = 1 ∨ ε = -1` as a hypothesis where FWZ
  do.
* Following `ClusterAlgebras.matrixMutation`, the rows of `B` are indexed by
  `Fin m` and the columns by `Fin n` with `n ≤ m`, so the row carrying the index
  of the column `k` is `Fin.castLE hmn k`. That is also the distinguished COLUMN
  of the `m × m` matrix `E`, which is why `E` needs `hmn` as well.
* `E` and `F` are `Matrix.updateCol` and `Matrix.updateRow` of the zero matrix
  rather than hand-rolled `if`s: a matrix supported in one column is exactly
  that, and Mathlib's lemmas for it come along.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

section SignFlip

variable {ι : Type*} [DecidableEq ι]

/-- The **sign-flip matrix** `J_{ι,k}`: the diagonal matrix whose diagonal entries
are all `1` except the `(k, k)` entry, which is `-1`. -/
@[cluster_algebras "def_matrix_J"]
def signFlipMatrix (R : Type*) [Zero R] [One R] [Neg R] (k : ι) : Matrix ι ι R :=
  diagonal (Function.update 1 k (-1))

variable (R : Type*) [Zero R] [One R] [Neg R] (k : ι)

/-- Every entry of the sign-flip matrix at once. -/
theorem signFlipMatrix_apply (i j : ι) :
    signFlipMatrix R k i j = if i = j then (if i = k then -1 else 1) else 0 := by
  simp [signFlipMatrix, diagonal_apply, Function.update_apply]

/-- The sign-flip matrix vanishes off the diagonal. -/
@[simp]
theorem signFlipMatrix_apply_ne {i j : ι} (h : i ≠ j) : signFlipMatrix R k i j = 0 :=
  diagonal_apply_ne _ h

/-- The flipped diagonal entry. -/
@[simp]
theorem signFlipMatrix_apply_self : signFlipMatrix R k k k = -1 := by
  simp [signFlipMatrix]

/-- Away from `k` the diagonal entries are `1`. -/
@[simp]
theorem signFlipMatrix_apply_diag_of_ne {i : ι} (h : i ≠ k) : signFlipMatrix R k i i = 1 := by
  simp [signFlipMatrix, h]

/-- The sign-flip matrix is symmetric. -/
@[simp]
theorem signFlipMatrix_transpose : (signFlipMatrix R k)ᵀ = signFlipMatrix R k :=
  diagonal_transpose _

/-- The sign-flip matrix is an involution. -/
@[simp]
theorem signFlipMatrix_mul_self [Fintype ι] {R : Type*} [Ring R] :
    signFlipMatrix R k * signFlipMatrix R k = 1 := by
  rw [signFlipMatrix, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases h : i = k <;> simp [h]

/-- The sign-flip matrix has determinant `-1`: it is the identity with one sign
reversed. -/
@[simp]
theorem det_signFlipMatrix [Fintype ι] {R : Type*} [CommRing R] :
    (signFlipMatrix R k).det = -1 := by
  rw [signFlipMatrix, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ k)]
  simp

end SignFlip

variable {R : Type*} [CommRing R] [LinearOrder R] {m n : ℕ}

/-- The **left mutation factor** `E_k` of `B` for the sign `ε`: the `m × m` matrix
whose `(i, k)` entry is `max 0 (-(ε * bᵢₖ))` and whose other entries vanish. It is
the factor that, added to a sign-flip matrix, multiplies `B` on the left to mutate
it in direction `k`. -/
@[cluster_algebras "def_matrix_E"]
def leftMutationFactor (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (ε : R) (k : Fin n) :
    Matrix (Fin m) (Fin m) R :=
  (0 : Matrix (Fin m) (Fin m) R).updateCol (Fin.castLE hmn k) fun i => max 0 (-(ε * B i k))

/-- The **right mutation factor** `F_k` of `B` for the sign `ε`: the `n × n` matrix
whose `(k, j)` entry is `max 0 (ε * bₖⱼ)` and whose other entries vanish. It is the
factor that, added to a sign-flip matrix, multiplies `B` on the right to mutate it
in direction `k`. -/
@[cluster_algebras "def_matrix_F"]
def rightMutationFactor (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (ε : R) (k : Fin n) :
    Matrix (Fin n) (Fin n) R :=
  (0 : Matrix (Fin n) (Fin n) R).updateRow k fun j => max 0 (ε * B (Fin.castLE hmn k) j)

variable (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (ε : R) (k : Fin n)

/-- Every entry of the left mutation factor at once. -/
theorem leftMutationFactor_apply (i j : Fin m) :
    leftMutationFactor hmn B ε k i j =
      if j = Fin.castLE hmn k then max 0 (-(ε * B i k)) else 0 := by
  rw [leftMutationFactor, updateCol_apply]
  split <;> simp

/-- The distinguished column of the left mutation factor. -/
@[simp]
theorem leftMutationFactor_apply_col (i : Fin m) :
    leftMutationFactor hmn B ε k i (Fin.castLE hmn k) = max 0 (-(ε * B i k)) :=
  updateCol_self ..

/-- The left mutation factor is supported in column `k`. -/
@[simp]
theorem leftMutationFactor_apply_of_ne {i j : Fin m} (h : j ≠ Fin.castLE hmn k) :
    leftMutationFactor hmn B ε k i j = 0 :=
  (updateCol_ne h).trans rfl

/-- The diagonal entry of the left mutation factor in the mutated direction
vanishes as soon as the corresponding entry of `B` does. This is what makes the
determinant of `signFlipMatrix + leftMutationFactor` insensitive to `ε`. -/
theorem leftMutationFactor_diag_eq_zero (h : B (Fin.castLE hmn k) k = 0) :
    leftMutationFactor hmn B ε k (Fin.castLE hmn k) (Fin.castLE hmn k) = 0 := by
  rw [leftMutationFactor_apply_col, h]
  simp

/-- Multiplying `B` on the left by its left mutation factor keeps only the column
`k` of the factor and the row `k` of `B`. -/
theorem leftMutationFactor_mul_apply (i : Fin m) (j : Fin n) :
    (leftMutationFactor hmn B ε k * B) i j =
      max 0 (-(ε * B i k)) * B (Fin.castLE hmn k) j := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single_of_mem (Fin.castLE hmn k) (Finset.mem_univ _)
      fun l _ hl => by rw [leftMutationFactor_apply_of_ne hmn B ε k hl, zero_mul],
    leftMutationFactor_apply_col]

/-- Every entry of the right mutation factor at once. -/
theorem rightMutationFactor_apply (i j : Fin n) :
    rightMutationFactor hmn B ε k i j =
      if i = k then max 0 (ε * B (Fin.castLE hmn k) j) else 0 := by
  rw [rightMutationFactor, updateRow_apply]
  split <;> simp

/-- The distinguished row of the right mutation factor. -/
@[simp]
theorem rightMutationFactor_apply_row (j : Fin n) :
    rightMutationFactor hmn B ε k k j = max 0 (ε * B (Fin.castLE hmn k) j) :=
  congrFun (updateRow_self ..) j

/-- The right mutation factor is supported in row `k`. -/
@[simp]
theorem rightMutationFactor_apply_of_ne {i j : Fin n} (h : i ≠ k) :
    rightMutationFactor hmn B ε k i j = 0 :=
  (congrFun (updateRow_ne h) j).trans rfl

/-- The diagonal entry of the right mutation factor in the mutated direction
vanishes as soon as the corresponding entry of `B` does. -/
theorem rightMutationFactor_diag_eq_zero (h : B (Fin.castLE hmn k) k = 0) :
    rightMutationFactor hmn B ε k k k = 0 := by
  rw [rightMutationFactor_apply_row, h]
  simp

/-- Multiplying `B` on the right by its right mutation factor keeps only the column
`k` of `B` and the row `k` of the factor. -/
theorem mul_rightMutationFactor_apply (i : Fin m) (j : Fin n) :
    (B * rightMutationFactor hmn B ε k) i j =
      B i k * max 0 (ε * B (Fin.castLE hmn k) j) := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single_of_mem k (Finset.mem_univ _)
      fun l _ hl => by rw [rightMutationFactor_apply_of_ne hmn B ε k hl, mul_zero],
    rightMutationFactor_apply_row]

end ClusterAlgebras
