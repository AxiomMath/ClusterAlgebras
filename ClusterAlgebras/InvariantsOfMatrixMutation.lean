/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.MatrixMutation
public import ClusterAlgebras.Defs.InvariantsOfMatrixMutation
public import ClusterAlgebras.External

/-!
# Invariants of matrix mutation

For an `m × n` matrix `B` with `B (Fin.castLE hmn k) k = 0` and a sign `ε = ±1`, mutation in
direction `k` factors as

  `μ_k B = (J + E) * B * (J + F)`,

with `J` a sign-flip matrix and `E`, `F` the one-column and one-row mutation factors
`leftMutationFactor` and `rightMutationFactor`. Both outer factors have determinant `-1`, so
mutation preserves the determinant (in the square case) and the rank. The gcd of the entries of
an integer matrix is also invariant under mutation.

## Main results

* `matrixMutation_eq_mul_mul`: the factorisation `μ_k B = (J + E) * B * (J + F)`.
* `det_matrixMutation`: mutation of a square matrix preserves the determinant.
* `rank_matrixMutation`: mutation preserves the rank.
* `gcd_matrixMutation`: mutation preserves the gcd of the entries of an integer matrix.

## Implementation notes

* Only the entry `B (Fin.castLE hmn k) k` at the mutated index is assumed to vanish, rather
  than the whole diagonal; it is the only diagonal entry that enters the factorisation.
* `matrixMutation_apply_eq_sign` holds with no hypothesis on the diagonal.
* `gcd_matrixMutation` assumes neither sign-skew-symmetry nor skew-symmetrizability.
* `rank_matrixMutation` is stated over a linearly ordered commutative ring rather than a field.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

/-! ### A matrix differing from the identity in one column -/

/-- **A matrix agreeing with the identity off column `k` has determinant its
`(k, k)` entry.** Expanding by multilinearity in column `k` writes that column as
`∑ i, M i k • eᵢ`; the summand at `i ≠ k` repeats the `i`th column and dies, and the
summand at `i = k` is the identity. -/
@[cluster_algebras "lem_det_one_column"]
theorem det_eq_of_eq_one_off_col {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*} [CommRing R]
    {M : Matrix ι ι R} {k : ι} (h : ∀ i j, j ≠ k → M i j = (1 : Matrix ι ι R) i j) :
    M.det = M k k := by
  have hM : M = (1 : Matrix ι ι R).updateCol k fun i => ∑ l, M l k • (1 : Matrix ι ι R) i l := by
    ext i j
    by_cases hj : j = k
    · subst hj
      rw [Matrix.updateCol_self]
      simp [Matrix.one_apply, Finset.sum_ite_eq]
    · rw [Matrix.updateCol_ne hj]
      exact h i j hj
  rw [hM, Matrix.det_updateCol_sum, Matrix.det_one, smul_eq_mul, mul_one, Matrix.updateCol_self]
  simp [Matrix.one_apply, Finset.sum_ite_eq]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-! ### Mutation restated with a sign parameter -/

/-- Clipping an element and its negative recovers it. -/
theorem max_zero_sub_max_zero_neg (a : R) : max 0 a - max 0 (-a) = a := by
  rw [max_comm 0 a, max_comm 0 (-a)]
  exact max_zero_sub_max_neg_zero_eq_self a

/-- Off row and column `k`, the mutated entry read with a sign parameter
`ε = ±1`. Only one of the two governing entries is clipped in each summand, and the
two clippings recover the entry itself, which is what makes this the same
correction as `matrixMutation_apply_of_ne_eq_max`. -/
theorem matrixMutation_apply_of_ne_eq_sign (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) {ε : R}
    (hε : ε = 1 ∨ ε = -1) (k : Fin n) {i : Fin m} {j : Fin n} (hi : i ≠ Fin.castLE hmn k)
    (hj : j ≠ k) :
    matrixMutation hmn B k i j =
      B i j + max 0 (-(ε * B i k)) * B (Fin.castLE hmn k) j
        + B i k * max 0 (ε * B (Fin.castLE hmn k) j) := by
  have hx := max_zero_sub_max_zero_neg (B i k)
  have hy := max_zero_sub_max_zero_neg (B (Fin.castLE hmn k) j)
  rw [matrixMutation_apply_of_ne_eq_max hmn B k hi hj]
  rcases hε with rfl | rfl
  · simp only [one_mul]
    linear_combination max 0 (B (Fin.castLE hmn k) j) * hx + max 0 (-B i k) * hy
  · simp only [neg_mul, one_mul, neg_neg]
    linear_combination max 0 (-B (Fin.castLE hmn k) j) * hx + max 0 (B i k) * hy

/-- **Mutation restated with a sign parameter.** For either sign `ε = ±1`, mutation
negates row and column `k` and elsewhere adds
`max (0, -ε bᵢₖ) bₖⱼ + bᵢₖ max (0, ε bₖⱼ)`. This is the shape the factorisation of a
mutation into a triple matrix product needs: each summand is linear in one row or
one column of `B`. -/
@[cluster_algebras "lem_matrix_mutation_restated"]
theorem matrixMutation_apply_eq_sign (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) {ε : R}
    (hε : ε = 1 ∨ ε = -1) (k : Fin n) (i : Fin m) (j : Fin n) :
    matrixMutation hmn B k i j =
      if i = Fin.castLE hmn k ∨ j = k then -B i j
      else B i j + max 0 (-(ε * B i k)) * B (Fin.castLE hmn k) j
        + B i k * max 0 (ε * B (Fin.castLE hmn k) j) := by
  by_cases h : i = Fin.castLE hmn k ∨ j = k
  · rw [if_pos h]
    exact matrixMutation_apply_of_eq hmn B k h
  · rw [if_neg h, not_or] at *
    exact matrixMutation_apply_of_ne_eq_sign hmn B hε k h.1 h.2

/-! ### Mutation as a matrix product -/

/-- **Mutation is a triple matrix product.** Left multiplication by
`J + E` negates row `k` and adds `max (0, -ε bᵢₖ)` times row `k`; right
multiplication by `J + F` negates column `k` and adds column `k` times
`max (0, ε bₖⱼ)`. The `(k, k)` entries of `E` and `F` vanish because `bₖₖ` does, so
the two corrections never interfere on row or column `k`. -/
@[cluster_algebras "lem_mutation_product"]
theorem matrixMutation_eq_mul_mul (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) {ε : R}
    (hε : ε = 1 ∨ ε = -1) (k : Fin n) (hk : B (Fin.castLE hmn k) k = 0) :
    matrixMutation hmn B k =
      (signFlipMatrix R (Fin.castLE hmn k) + leftMutationFactor hmn B ε k) * B *
        (signFlipMatrix R k + rightMutationFactor hmn B ε k) := by
  have hJl : ∀ (i : Fin m) (j : Fin n), (signFlipMatrix R (Fin.castLE hmn k) * B) i j =
      if i = Fin.castLE hmn k then -B i j else B i j := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
      fun l _ hl => by rw [signFlipMatrix_apply_ne _ _ (Ne.symm hl), zero_mul]]
    by_cases h : i = Fin.castLE hmn k
    · subst h
      rw [signFlipMatrix_apply_self, if_pos rfl, neg_one_mul]
    · rw [signFlipMatrix_apply_diag_of_ne _ _ h, if_neg h, one_mul]
  have hJr : ∀ (C : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n),
      (C * signFlipMatrix R k) i j = if j = k then -C i j else C i j := by
    intro C i j
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ _)
      fun l _ hl => by rw [signFlipMatrix_apply_ne _ _ hl, mul_zero]]
    by_cases h : j = k
    · subst h
      rw [signFlipMatrix_apply_self, if_pos rfl, mul_neg_one]
    · rw [signFlipMatrix_apply_diag_of_ne _ _ h, if_neg h, mul_one]
  have hFr : ∀ (C : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n),
      (C * rightMutationFactor hmn B ε k) i j =
        C i k * max 0 (ε * B (Fin.castLE hmn k) j) := by
    intro C i j
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem k (Finset.mem_univ _)
      fun l _ hl => by rw [rightMutationFactor_apply_of_ne hmn B ε k hl, mul_zero],
      rightMutationFactor_apply_row]
  have hC : ∀ (i : Fin m) (j : Fin n),
      ((signFlipMatrix R (Fin.castLE hmn k) + leftMutationFactor hmn B ε k) * B) i j =
        (if i = Fin.castLE hmn k then -B i j else B i j) +
          max 0 (-(ε * B i k)) * B (Fin.castLE hmn k) j := by
    intro i j
    rw [Matrix.add_mul, Matrix.add_apply, hJl, leftMutationFactor_mul_apply]
  ext i j
  rw [Matrix.mul_add, Matrix.add_apply, hJr, hFr, hC, hC,
    matrixMutation_apply_eq_sign hmn B hε k i j]
  by_cases hj : j = k
  · subst hj
    rw [if_pos (Or.inr rfl), if_pos rfl, hk]
    simp only [mul_zero, max_self, add_zero]
    by_cases hi : i = Fin.castLE hmn j
    · rw [if_pos hi, hi, hk]
      simp
    · rw [if_neg hi]
  · rw [if_neg hj]
    by_cases hi : i = Fin.castLE hmn k
    · subst hi
      rw [if_pos (Or.inl rfl), hk]
      simp
    · rw [if_neg (not_or.mpr ⟨hi, hj⟩), if_neg hi, if_neg hi, hk, mul_zero, add_zero]

/-! ### The mutation factors have determinant minus one -/

omit [IsStrictOrderedRing R] in
/-- **The left mutation factor added to a sign-flip matrix has determinant `-1`.**
`E` is supported in column `k`, so the sum agrees with the identity off that
column, and its `(k, k)` entry is `-1 + 0`. -/
@[cluster_algebras "lem_det_factor"]
theorem det_signFlipMatrix_add_leftMutationFactor (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R)
    (ε : R) (k : Fin n) (hk : B (Fin.castLE hmn k) k = 0) :
    (signFlipMatrix R (Fin.castLE hmn k) + leftMutationFactor hmn B ε k).det = -1 := by
  have h : ∀ i j : Fin m, j ≠ Fin.castLE hmn k →
      (signFlipMatrix R (Fin.castLE hmn k) + leftMutationFactor hmn B ε k) i j =
        (1 : Matrix (Fin m) (Fin m) R) i j := by
    intro i j hj
    rw [Matrix.add_apply, leftMutationFactor_apply_of_ne hmn B ε k hj, add_zero,
      signFlipMatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [hj]
    · simp [hij]
  rw [det_eq_of_eq_one_off_col h, Matrix.add_apply, signFlipMatrix_apply_self,
    leftMutationFactor_diag_eq_zero hmn B ε k hk, add_zero]

omit [IsStrictOrderedRing R] in
/-- **The right mutation factor added to a sign-flip matrix has determinant `-1`.**
`F` is supported in row `k`, so the transpose agrees with the identity off column
`k` and the previous lemma's argument applies to it. -/
@[cluster_algebras "lem_det_factor"]
theorem det_signFlipMatrix_add_rightMutationFactor (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R)
    (ε : R) (k : Fin n) (hk : B (Fin.castLE hmn k) k = 0) :
    (signFlipMatrix R k + rightMutationFactor hmn B ε k).det = -1 := by
  have h : ∀ i j : Fin n, j ≠ k →
      (signFlipMatrix R k + rightMutationFactor hmn B ε k)ᵀ i j =
        (1 : Matrix (Fin n) (Fin n) R) i j := by
    intro i j hj
    rw [Matrix.transpose_apply, Matrix.add_apply, rightMutationFactor_apply_of_ne hmn B ε k hj,
      add_zero, signFlipMatrix_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [hj]
    · simp [hij, Ne.symm hij]
  rw [← Matrix.det_transpose, det_eq_of_eq_one_off_col h, Matrix.transpose_apply,
    Matrix.add_apply, signFlipMatrix_apply_self,
    rightMutationFactor_diag_eq_zero hmn B ε k hk, add_zero]

/-! ### Determinant and rank -/

/-- **Mutation preserves the determinant.** The two outer factors of the
factorisation have determinant `-1`, and determinants are multiplicative. -/
@[cluster_algebras "thm_det_invariant"]
theorem det_matrixMutation (hnn : n ≤ n) (B : Matrix (Fin n) (Fin n) R) (k : Fin n)
    (hk : B k k = 0) : (matrixMutation hnn B k).det = B.det := by
  have hk' : B (Fin.castLE hnn k) k = 0 := hk
  rw [matrixMutation_eq_mul_mul hnn B (Or.inl rfl) k hk', Matrix.det_mul, Matrix.det_mul,
    det_signFlipMatrix_add_leftMutationFactor hnn B 1 k hk',
    det_signFlipMatrix_add_rightMutationFactor hnn B 1 k hk']
  ring

/-- **Mutation preserves the rank.** Both outer factors of the factorisation have
determinant `-1`, a unit, so neither changes the rank. -/
@[cluster_algebras "thm_rank_invariant"]
theorem rank_matrixMutation (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n)
    (hk : B (Fin.castLE hmn k) k = 0) : (matrixMutation hmn B k).rank = B.rank := by
  have hl : IsUnit (signFlipMatrix R (Fin.castLE hmn k) + leftMutationFactor hmn B 1 k).det := by
    rw [det_signFlipMatrix_add_leftMutationFactor hmn B 1 k hk]
    exact isUnit_one.neg
  have hr : IsUnit (signFlipMatrix R k + rightMutationFactor hmn B 1 k).det := by
    rw [det_signFlipMatrix_add_rightMutationFactor hmn B 1 k hk]
    exact isUnit_one.neg
  rw [matrixMutation_eq_mul_mul hmn B (Or.inl rfl) k hk,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hr, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hl]

/-! ### The greatest common divisor of the entries -/

omit [IsStrictOrderedRing R] in
/-- A common divisor of the entries of `B` divides every entry of `μ_k(B)`: each
mutated entry is `± bᵢⱼ` plus a multiple of `bₖⱼ`. -/
theorem dvd_matrixMutation_apply (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) R) (k : Fin n) {d : R}
    (h : ∀ i j, d ∣ B i j) (i : Fin m) (j : Fin n) : d ∣ matrixMutation hmn B k i j := by
  rw [matrixMutation]
  simp only [Matrix.of_apply]
  split
  · exact (h i j).neg_right
  split
  · exact dvd_add (h i j) ((h _ j).mul_left _)
  split
  · exact dvd_sub (h i j) ((h _ j).mul_left _)
  · exact h i j

/-- **Mutation preserves the greatest common divisor of the entries.** Each entry of
`μ_k(B)` is a `ℤ`-combination of entries of `B`, so the gcd of `B` divides that of
`μ_k(B)`; mutation is an involution, so the same argument run on `μ_k(B)` gives the
reverse divisibility.

This form takes the involutivity of mutation at `k` as a hypothesis;
`gcd_matrixMutation` is the same result resting on the assumed exercise. -/
theorem gcd_matrixMutation_of_involutive (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n)
    (hinv : matrixMutation hmn (matrixMutation hmn B k) k = B) :
    (Finset.univ.gcd fun p : Fin m × Fin n => matrixMutation hmn B k p.1 p.2) =
      Finset.univ.gcd fun p : Fin m × Fin n => B p.1 p.2 := by
  have key : ∀ C : Matrix (Fin m) (Fin n) ℤ,
      (Finset.univ.gcd fun p : Fin m × Fin n => C p.1 p.2) ∣
        Finset.univ.gcd fun p : Fin m × Fin n => matrixMutation hmn C k p.1 p.2 :=
    fun C => Finset.dvd_gcd fun p _ =>
      dvd_matrixMutation_apply hmn C k (fun i j => Finset.gcd_dvd (Finset.mem_univ (i, j))) p.1 p.2
  have hback := key (matrixMutation hmn B k)
  rw [hinv] at hback
  have := normalize_eq_normalize hback (key B)
  rwa [Finset.normalize_gcd, Finset.normalize_gcd] at this

/-- **Mutation preserves the greatest common divisor of the entries**, granted that mutation
at `k` is an involution. -/
@[cluster_algebras "lem_gcd_invariant"]
theorem gcd_matrixMutation (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ) (k : Fin n) :
    (Finset.univ.gcd fun p : Fin m × Fin n => matrixMutation hmn B k p.1 p.2) =
      Finset.univ.gcd fun p : Fin m × Fin n => B p.1 p.2 :=
  gcd_matrixMutation_of_involutive hmn B k (matrixMutation_matrixMutation hmn B k)

end ClusterAlgebras
