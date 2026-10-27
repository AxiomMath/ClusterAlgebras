/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import ClusterAlgebras.MatrixMutation

/-!
# Isolating rows under one and two matrix mutations

Let `B̃` be an `m × n` matrix, let `j, k` be column indices with `b_{jk} < 0`, and let `q, r`
be rows such that row `q` is the unit row with `1` in column `j` and row `r` is the unit row
with `1` in column `k`. This file computes the `2 × 2` block of `μ_j(B̃)` in rows `q, r` and
columns `j, k`, which is `[[-1, 0], [0, 1]]`, and, when moreover `b_{kj} > 0`, the same block of
`μ_k(μ_j(B̃))`, which is `[[-1, 0], [0, -1]]`. Both are direct readings of the four clauses of
matrix mutation. The proof of the Laurent phenomenon uses them to follow the coefficient-row
pattern of a seed through two mutations.

## Main results

* `ClusterAlgebras.matrixMutation_apply_unitRows`: the block of `μ_j(B̃)`.
* `ClusterAlgebras.matrixMutation_matrixMutation_apply_unitRows`: the block of `μ_k(μ_j(B̃))`.

## Implementation notes

The matrices have entries in an arbitrary linearly ordered commutative ring rather than `ℤ`,
and the statements are sharpened in several respects, all of which FWZ's hypotheses
imply.

* Of the two unit rows only the four entries in columns `j, k` are assumed: `b_{qj} = 1`,
  `b_{qk} = 0`, `b_{rj} = 0`, `b_{rk} = 1`. The entries of rows `q, r` in other columns
  do not enter the computation.
* The strict inequalities `b_{jk} < 0` and `b_{kj} > 0` are weakened to `b_{jk} ≤ 0` and
  `b_{kj} ≥ 0`.
* The conditions `j ≠ k` and `q ≠ r` are not assumed: the four entries force both.
* FWZ take `q, r ∈ [n+1, m]`. For one mutation no such condition is needed: the
  entry `b_{jk} ≤ 0` forces `r` to differ from the row indexed by `j`, and if `q` is that row
  then the entry `(q, k)` is negated from `0` to `0`. For two mutations the only condition
  used is that `q` is not the row indexed by `k`; without it the entry `(q, j)` of
  `μ_k(μ_j(B̃))` would be `1`. A frozen row `q` (with `n ≤ q`) satisfies it.

Rows are indexed by `Fin m` and columns by `Fin n`, and the row carrying the index of a column
`k` is `Fin.castLE hmn k`, as in `ClusterAlgebras.matrixMutation`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-- **Isolating rows after one mutation.** If `b_{jk} ≤ 0`, row `q` of `B` reads `1, 0` and
row `r` reads `0, 1` in columns `j, k`, then in `μ_j(B)` these entries become `-1, 0` and
`0, 1`. -/
@[cluster_algebras "lem_augmented_block_one"]
theorem matrixMutation_apply_unitRows (hmn : n ≤ m) {B : Matrix (Fin m) (Fin n) R}
    {j k : Fin n} {q r : Fin m} (hjk : B (Fin.castLE hmn j) k ≤ 0) (hqj : B q j = 1)
    (hqk : B q k = 0) (hrj : B r j = 0) (hrk : B r k = 1) :
    matrixMutation hmn B j q j = -1 ∧ matrixMutation hmn B j q k = 0 ∧
      matrixMutation hmn B j r j = 0 ∧ matrixMutation hmn B j r k = 1 := by
  have hkj : k ≠ j := by rintro rfl; simp [hqj] at hqk
  have hr : r ≠ Fin.castLE hmn j := by
    rintro rfl
    rw [hrk] at hjk
    exact absurd hjk (by norm_num)
  refine ⟨by simp [hqj], ?_, by simp [hrj], ?_⟩
  · by_cases hq : q = Fin.castLE hmn j
    · rw [matrixMutation_apply_of_eq hmn B j (Or.inl hq), hqk, neg_zero]
    · rw [matrixMutation_apply_of_ne_eq_max hmn B j hq hkj, hqk, hqj, max_eq_left hjk]
      simp
  · rw [matrixMutation_apply_of_ne_eq_max hmn B j hr hkj, hrk, hrj]
    simp

/-- **Isolating rows after two mutations.** If moreover `b_{kj} ≥ 0` and `q` is not the row
indexed by `k`, then in `μ_k(μ_j(B))` the entries of rows `q, r` in columns `j, k` are `-1, 0`
and `0, -1`. -/
@[cluster_algebras "lem_augmented_block_two"]
theorem matrixMutation_matrixMutation_apply_unitRows (hmn : n ≤ m)
    {B : Matrix (Fin m) (Fin n) R} {j k : Fin n} {q r : Fin m}
    (hjk : B (Fin.castLE hmn j) k ≤ 0) (hkj : 0 ≤ B (Fin.castLE hmn k) j)
    (hq : q ≠ Fin.castLE hmn k) (hqj : B q j = 1) (hqk : B q k = 0) (hrj : B r j = 0)
    (hrk : B r k = 1) :
    matrixMutation hmn (matrixMutation hmn B j) k q j = -1 ∧
      matrixMutation hmn (matrixMutation hmn B j) k q k = 0 ∧
      matrixMutation hmn (matrixMutation hmn B j) k r j = 0 ∧
      matrixMutation hmn (matrixMutation hmn B j) k r k = -1 := by
  have hjk' : j ≠ k := by rintro rfl; simp [hqj] at hqk
  obtain ⟨h1, h2, h3, h4⟩ := matrixMutation_apply_unitRows hmn hjk hqj hqk hrj hrk
  have h5 : matrixMutation hmn B j (Fin.castLE hmn k) j ≤ 0 := by simpa using hkj
  refine ⟨?_, by simp [h2], ?_, by simp [h4]⟩
  · rw [matrixMutation_apply_of_ne_eq_max hmn _ k hq hjk', h1, h2]
    simp
  · by_cases hr : r = Fin.castLE hmn k
    · rw [matrixMutation_apply_of_eq hmn _ k (Or.inl hr), h3, neg_zero]
    · rw [matrixMutation_apply_of_ne_eq_max hmn _ k hr hjk', h3, h4, max_eq_left h5]
      simp

end ClusterAlgebras
