/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib
public import ClusterAlgebras.Attr
public import ClusterAlgebras.Definitions

/-!
# Matrix mutation

Mutation of an `m × n` matrix in a direction `k`, over a linearly ordered commutative ring.
The direction `k` ranges over the columns while the rule reads both the column entry `b i k`
and the row entry `b k j`, so the first `n` rows are indexed by the columns: hence `n ≤ m`,
and the row carrying the index of a column `k` is `Fin.castLE hmn k`. Taking `m = n` gives
the square case.

Mutation is defined on an arbitrary matrix, with no condition on the diagonal. Mutation does
not preserve a vanishing diagonal in general, because the second clause at `i = j` asks for
`b i k > 0` and `b k i > 0` together, which a matrix with zero diagonal may satisfy. Under
`SignAntisymmetric`, a vanishing diagonal is preserved (`matrixMutation_diag_eq_zero`).

`matrixMutation` is defined by four cases, and `matrixMutation_apply_of_ne_eq_max` rewrites
the three non-negating cases as the single closed form

  `b i j + max 0 (b i k) * max 0 (b k j) - max 0 (-b i k) * max 0 (-b k j)`,

which agrees with them because a product `max 0 a * max 0 c` is nonzero only when `a` and
`c` are both positive.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-- Embedding a column index into the rows does nothing when the matrix is
square. -/
@[simp]
theorem castLE_self (h : n ≤ n) (k : Fin n) : Fin.castLE h k = k := rfl

attribute [cluster_algebras "def_matrix_mutation"] matrixMutation

omit [IsStrictOrderedRing R] in
/-- On row or column `k`, mutation is negation. -/
theorem matrixMutation_apply_of_eq (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    {i : Fin m} {j : Fin n} (h : i = Fin.castLE hmn k ∨ j = k) :
    matrixMutation hmn B k i j = -B i j := by
  simp [matrixMutation, h]

omit [IsStrictOrderedRing R] in
/-- Column `k` is negated. -/
@[simp]
theorem matrixMutation_apply_col (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (i : Fin m) : matrixMutation hmn B k i k = -B i k :=
  matrixMutation_apply_of_eq hmn B k (Or.inr rfl)

omit [IsStrictOrderedRing R] in
/-- Row `k` is negated. -/
@[simp]
theorem matrixMutation_apply_row (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (j : Fin n) :
    matrixMutation hmn B k (Fin.castLE hmn k) j = -B (Fin.castLE hmn k) j :=
  matrixMutation_apply_of_eq hmn B k (Or.inl rfl)

omit [IsStrictOrderedRing R] in
/-- Off row and column `k`, mutation adds the sign-governed correction. -/
theorem matrixMutation_apply_of_ne (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    {i : Fin m} {j : Fin n} (hi : i ≠ Fin.castLE hmn k) (hj : j ≠ k) :
    matrixMutation hmn B k i j =
      if 0 < B i k ∧ 0 < B (Fin.castLE hmn k) j then
        B i j + B i k * B (Fin.castLE hmn k) j
      else if B i k < 0 ∧ B (Fin.castLE hmn k) j < 0 then
        B i j - B i k * B (Fin.castLE hmn k) j
      else B i j := by
  simp [matrixMutation, hi, hj]

/-- Off row and column `k`, the mutated entry in closed form:
`B i j + max 0 (B i k) * max 0 (B k j) - max 0 (-B i k) * max 0 (-B k j)`. -/
theorem matrixMutation_apply_of_ne_eq_max (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R)
    (k : Fin n) {i : Fin m} {j : Fin n} (hi : i ≠ Fin.castLE hmn k) (hj : j ≠ k) :
    matrixMutation hmn B k i j =
      B i j + max 0 (B i k) * max 0 (B (Fin.castLE hmn k) j)
        - max 0 (-B i k) * max 0 (-B (Fin.castLE hmn k) j) := by
  rw [matrixMutation_apply_of_ne hmn B k hi hj]
  rcases lt_trichotomy (B i k) 0 with hx | hx | hx <;>
    rcases lt_trichotomy (B (Fin.castLE hmn k) j) 0 with hy | hy | hy
  · rw [if_neg (not_and_of_not_left _ (not_lt.mpr hx.le)), if_pos ⟨hx, hy⟩,
      max_eq_left hx.le, max_eq_left hy.le, max_eq_right (by linarith),
      max_eq_right (by linarith)]
    ring
  · rw [if_neg (not_and_of_not_left _ (not_lt.mpr hx.le)),
      if_neg (not_and_of_not_right _ (not_lt.mpr (le_of_eq hy.symm))), hy]
    simp [max_eq_left hx.le]
  · rw [if_neg (not_and_of_not_left _ (not_lt.mpr hx.le)),
      if_neg (not_and_of_not_right _ (not_lt.mpr hy.le))]
    simp [max_eq_left hx.le, max_eq_left (by linarith : -B (Fin.castLE hmn k) j ≤ 0)]
  · rw [if_neg (not_and_of_not_left _ (not_lt.mpr (le_of_eq hx))),
      if_neg (not_and_of_not_left _ (not_lt.mpr (le_of_eq hx.symm))), hx]
    simp
  · rw [if_neg (not_and_of_not_left _ (not_lt.mpr (le_of_eq hx))),
      if_neg (not_and_of_not_left _ (not_lt.mpr (le_of_eq hx.symm))), hx]
    simp
  · rw [if_neg (not_and_of_not_left _ (not_lt.mpr (le_of_eq hx))),
      if_neg (not_and_of_not_left _ (not_lt.mpr (le_of_eq hx.symm))), hx]
    simp
  · rw [if_neg (not_and_of_not_right _ (not_lt.mpr hy.le)),
      if_neg (not_and_of_not_left _ (not_lt.mpr hx.le))]
    simp [max_eq_left hy.le, max_eq_left (by linarith : -B i k ≤ 0)]
  · rw [if_neg (not_and_of_not_right _ (not_lt.mpr (le_of_eq hy))),
      if_neg (not_and_of_not_left _ (not_lt.mpr hx.le)), hy]
    simp [max_eq_left (by linarith : -B i k ≤ 0)]
  · rw [if_pos ⟨hx, hy⟩, max_eq_right hx.le, max_eq_right hy.le,
      max_eq_left (by linarith : -B i k ≤ 0),
      max_eq_left (by linarith : -B (Fin.castLE hmn k) j ≤ 0)]
    ring

/-- If either entry governing the correction vanishes, mutation leaves the entry
alone. This is what makes two mutations at non-adjacent vertices independent. -/
theorem matrixMutation_apply_of_eq_zero (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    {i : Fin m} {j : Fin n} (hi : i ≠ Fin.castLE hmn k) (hj : j ≠ k)
    (h : B i k = 0 ∨ B (Fin.castLE hmn k) j = 0) :
    matrixMutation hmn B k i j = B i j := by
  rw [matrixMutation_apply_of_ne_eq_max hmn B k hi hj]
  rcases h with h | h <;> rw [h] <;> simp

/-- `B` is **sign-antisymmetric** when its top `n × n` diagonal vanishes and an
entry there is positive exactly when its mirror is negative. -/
@[cluster_algebras "def_sign_antisymmetric"]
def SignAntisymmetric (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) : Prop :=
  (∀ i : Fin n, B (Fin.castLE hmn i) i = 0) ∧
    ∀ i j : Fin n, 0 < B (Fin.castLE hmn i) j ↔ B (Fin.castLE hmn j) i < 0

/-- Mutating a sign-antisymmetric matrix keeps its top `n × n` diagonal zero. -/
@[cluster_algebras "lem_matmut_preserves_diagonal"]
theorem matrixMutation_diag_eq_zero (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    (hB : SignAntisymmetric hmn B) (k i : Fin n) :
    matrixMutation hmn B k (Fin.castLE hmn i) i = 0 := by
  obtain ⟨hdiag, hsign⟩ := hB
  by_cases hik : i = k
  · subst hik
    rw [matrixMutation_apply_row, hdiag i, neg_zero]
  · have hi : Fin.castLE hmn i ≠ Fin.castLE hmn k := fun h =>
      hik (by simpa [Fin.ext_iff] using h)
    rw [matrixMutation_apply_of_ne_eq_max hmn B k hi hik, hdiag i]
    rcases lt_trichotomy (B (Fin.castLE hmn i) k) 0 with hx | hx | hx
    · have hy : 0 < B (Fin.castLE hmn k) i := (hsign k i).mpr hx
      rw [max_eq_left hx.le, max_eq_left (by linarith : -B (Fin.castLE hmn k) i ≤ 0)]
      ring
    · rw [hx]; simp
    · have hy : B (Fin.castLE hmn k) i < 0 := (hsign i k).mp hx
      rw [max_eq_left hy.le, max_eq_left (by linarith : -B (Fin.castLE hmn i) k ≤ 0)]
      ring

/-- A nonnegative scalar passes through `max 0`. -/
theorem max_zero_mul_of_nonneg {c a : R} (hc : 0 ≤ c) : max 0 (c * a) = c * max 0 a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonneg hc h)]
  · rw [max_eq_left h, mul_zero, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc h)]

/-- For `0 ≤ c`, `max 0 (-(c * a)) = c * max 0 (-a)`. -/
theorem max_zero_neg_mul_of_nonneg {c a : R} (hc : 0 ≤ c) :
    max 0 (-(c * a)) = c * max 0 (-a) := by
  rw [← mul_neg, max_zero_mul_of_nonneg hc]

section DiagonalConjugation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Conjugating by a positive diagonal commutes with mutation: if
`C a b = t a / t b * B a b` for a positive vector `t`, then mutating `C` gives the
same rescaling of the mutated `B`. -/
@[cluster_algebras "lem_matmut_diagonal_conjugation"]
theorem matrixMutation_conj (hmn : n ≤ m) (B C : Matrix (Fin m) (Fin n) K) (t : Fin m → K)
    (ht : ∀ i, 0 < t i) (hC : ∀ a b, C a b = t a / t (Fin.castLE hmn b) * B a b) (k : Fin n)
    (i : Fin m) (j : Fin n) :
    matrixMutation hmn C k i j = t i / t (Fin.castLE hmn j) * matrixMutation hmn B k i j := by
  have hk0 : t (Fin.castLE hmn k) ≠ 0 := ne_of_gt (ht _)
  have hj0 : t (Fin.castLE hmn j) ≠ 0 := ne_of_gt (ht _)
  have p1 : (0 : K) ≤ t i / t (Fin.castLE hmn k) := (div_pos (ht i) (ht _)).le
  have p2 : (0 : K) ≤ t (Fin.castLE hmn k) / t (Fin.castLE hmn j) :=
    (div_pos (ht _) (ht _)).le
  by_cases h : i = Fin.castLE hmn k ∨ j = k
  · rw [matrixMutation_apply_of_eq hmn C k h, matrixMutation_apply_of_eq hmn B k h, hC]
    ring
  · rw [not_or] at h
    obtain ⟨hi, hj⟩ := h
    rw [matrixMutation_apply_of_ne_eq_max hmn C k hi hj,
      matrixMutation_apply_of_ne_eq_max hmn B k hi hj]
    simp only [hC, max_zero_mul_of_nonneg p1, max_zero_mul_of_nonneg p2,
      max_zero_neg_mul_of_nonneg p1, max_zero_neg_mul_of_nonneg p2]
    field_simp

end DiagonalConjugation

end ClusterAlgebras
