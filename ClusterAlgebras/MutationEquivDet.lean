/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.InvariantsOfMatrixMutation
public import ClusterAlgebras.Defs.MatrixMutationEquiv

/-!
# Mutation equivalent matrices have equal determinant

Mutation equivalence (`ClusterAlgebras.MutationEquiv`) leaves the determinant of a
skew-symmetrizable square matrix unchanged. Each mutation preserves it by
`ClusterAlgebras.det_matrixMutation`, and a simultaneous relabelling of the rows and the columns
preserves it because a permutation matrix has determinant `±1`.

Call `c : Fin n → R` a **skew-symmetrizing weight** for `B` when every `c i` is positive and
`c i * bᵢⱼ = -(c j * bⱼᵢ)` for all `i, j`. A skew-symmetrizing vector
(`ClusterAlgebras.IsSkewSymmetrizingVector`) is the special case `c i = (dᵢ : R)` of a positive
integer tuple. A skew-symmetrizing weight for `B` is one for `μ_k(B)`, with the same weight
(`weight_matrixMutation`), and it forces `B` to be sign-antisymmetric
(`signAntisymmetric_of_weight`), hence to have vanishing diagonal.

## Main results

* `weight_matrixMutation`: a skew-symmetrizing weight for `B` is one for `μ_k(B)`.
* `det_matrixMutationList_of_weight`: iterated mutation of a matrix carrying a
  skew-symmetrizing weight preserves the determinant.
* `MutationEquiv.det_eq_of_weight`: mutation equivalent matrices have equal determinant when
  the first carries a skew-symmetrizing weight.
* `MutationEquiv.det_eq`: mutation equivalent skew-symmetrizable matrices have equal
  determinant.

## Implementation notes

The weights are valued in `R` rather than in `ℤ`: the argument uses only their positivity.
Weighting turns each clipped quantity into its mirror
(`mul_max_zero_eq_of_mul_eq_neg_mul`: `c k * max 0 bₖᵢ = c i * max 0 (-bᵢₖ)`), and `c k`
cancels because a strictly ordered ring has no zero divisors.

Neither sign-antisymmetry of `B` nor skew-symmetrizability of `B'` is assumed in
`MutationEquiv.det_eq`, both being consequences of skew-symmetrizability of `B`.

The relabelling is `Matrix.submatrix π π`, and its determinant is computed by
`Matrix.det_submatrix_equiv_self`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}

/-! ### Clipping across a sign-reversing weighted identity -/

/-- Two elements related by `c * x = -(c' * y)` with positive weights have opposite signs, so
weighting carries the clipping `max 0 ·` of one to that of the negative of the other. -/
theorem mul_max_zero_eq_of_mul_eq_neg_mul {c c' x y : R} (hc : 0 < c) (hc' : 0 < c')
    (h : c * x = -(c' * y)) : c' * max 0 y = c * max 0 (-x) := by
  rcases le_or_gt x 0 with hx | hx
  · have hy : 0 ≤ y := by
      by_contra hy
      nlinarith [mul_neg_of_pos_of_neg hc' (not_le.mp hy), mul_nonneg hc.le (neg_nonneg.mpr hx)]
    rw [max_eq_right hy, max_eq_right (neg_nonneg.mpr hx)]
    linarith
  · have hy : y < 0 := by
      by_contra hy
      nlinarith [mul_pos hc hx, mul_nonneg hc'.le (not_lt.mp hy)]
    rw [max_eq_left hy.le, max_eq_left (neg_nonpos.mpr hx.le)]
    ring

/-! ### A skew-symmetrizing weight implies sign-antisymmetry -/

/-- A matrix carrying a skew-symmetrizing weight is sign-antisymmetric. -/
theorem signAntisymmetric_of_weight {B : Matrix (Fin n) (Fin n) R} {c : Fin n → R}
    (hc : ∀ i, 0 < c i) (hB : ∀ i j, c i * B i j = -(c j * B j i)) :
    SignAntisymmetric le_rfl B := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · have h0 : c i * B i i = 0 := by linarith [hB i i]
    exact (mul_eq_zero.mp h0).resolve_left (hc i).ne'
  · simp only [castLE_self]
    refine ⟨fun h => lt_of_not_ge fun hji => ?_, fun h => lt_of_not_ge fun hij => ?_⟩
    · linarith [hB i j, mul_pos (hc i) h, mul_nonneg (hc j).le hji]
    · linarith [hB i j, mul_nonpos_of_nonneg_of_nonpos (hc i).le hij,
        mul_neg_of_pos_of_neg (hc j) h]

/-! ### Mutation preserves a skew-symmetrizing weight -/

/-- **A skew-symmetrizing weight for `B` is one for `μ_k(B)`**. -/
theorem weight_matrixMutation {B : Matrix (Fin n) (Fin n) R} {c : Fin n → R}
    (hc : ∀ i, 0 < c i) (hB : ∀ i j, c i * B i j = -(c j * B j i)) (k i j : Fin n) :
    c i * matrixMutation le_rfl B k i j = -(c j * matrixMutation le_rfl B k j i) := by
  by_cases h : i = k ∨ j = k
  · rw [matrixMutation_apply_of_eq le_rfl B k (by simpa using h),
      matrixMutation_apply_of_eq le_rfl B k (by simpa using h.symm), mul_neg, mul_neg, hB i j]
  · obtain ⟨hi, hj⟩ := not_or.mp h
    rw [matrixMutation_apply_of_ne_eq_max le_rfl B k (by simpa using hi) hj,
      matrixMutation_apply_of_ne_eq_max le_rfl B k (by simpa using hj) hi]
    simp only [castLE_self]
    have e1 : c k * max 0 (B k i) = c i * max 0 (-B i k) :=
      mul_max_zero_eq_of_mul_eq_neg_mul (hc i) (hc k) (hB i k)
    have e2 : c k * max 0 (-B k i) = c i * max 0 (B i k) := by
      simpa using mul_max_zero_eq_of_mul_eq_neg_mul (hc i) (hc k) (x := -B i k) (y := -B k i)
        (by rw [mul_neg, mul_neg, hB i k])
    have e3 : c j * max 0 (B j k) = c k * max 0 (-B k j) :=
      mul_max_zero_eq_of_mul_eq_neg_mul (hc k) (hc j) (hB k j)
    have e4 : c j * max 0 (-B j k) = c k * max 0 (B k j) := by
      simpa using mul_max_zero_eq_of_mul_eq_neg_mul (hc k) (hc j) (x := -B k j) (y := -B j k)
        (by rw [mul_neg, mul_neg, hB k j])
    have key : c k * (c i * (B i j + max 0 (B i k) * max 0 (B k j)
        - max 0 (-B i k) * max 0 (-B k j))
        + c j * (B j i + max 0 (B j k) * max 0 (B k i)
        - max 0 (-B j k) * max 0 (-B k i))) = 0 :=
      calc _ = c k * (c i * B i j + c j * B j i)
              + (c i * max 0 (B i k)) * (c k * max 0 (B k j))
              - (c i * max 0 (-B i k)) * (c k * max 0 (-B k j))
              + (c j * max 0 (B j k)) * (c k * max 0 (B k i))
              - (c j * max 0 (-B j k)) * (c k * max 0 (-B k i)) := by ring
        _ = 0 := by
          rw [← e1, ← e2, ← e3, ← e4, hB i j]
          ring
    have := (mul_eq_zero.mp key).resolve_left (hc k).ne'
    linarith

/-- A skew-symmetrizing weight for `B` is one for every iterated mutation of `B`. -/
theorem weight_matrixMutationList {B : Matrix (Fin n) (Fin n) R} {c : Fin n → R}
    (hc : ∀ i, 0 < c i) (hB : ∀ i j, c i * B i j = -(c j * B j i)) (ks : List (Fin n)) :
    ∀ i j, c i * matrixMutationList le_rfl B ks i j =
      -(c j * matrixMutationList le_rfl B ks j i) := by
  induction ks generalizing B with
  | nil => exact hB
  | cons k ks ih => exact ih (weight_matrixMutation hc hB k)

/-! ### The determinant along a sequence of mutations -/

/-- **A sequence of mutations of a matrix carrying a skew-symmetrizing weight leaves the
determinant unchanged.** -/
theorem det_matrixMutationList_of_weight {B : Matrix (Fin n) (Fin n) R} {c : Fin n → R}
    (hc : ∀ i, 0 < c i) (hB : ∀ i j, c i * B i j = -(c j * B j i)) (ks : List (Fin n)) :
    (matrixMutationList le_rfl B ks).det = B.det := by
  induction ks generalizing B with
  | nil => rfl
  | cons k ks ih =>
    rw [matrixMutationList_cons, ih (weight_matrixMutation hc hB k),
      det_matrixMutation le_rfl B k ((signAntisymmetric_of_weight hc hB).1 k)]

/-- **Mutation equivalent matrices have equal determinant**, for a matrix carrying a
skew-symmetrizing weight valued in `R`. -/
theorem MutationEquiv.det_eq_of_weight {B B' : Matrix (Fin n) (Fin n) R}
    (h : MutationEquiv B B') {c : Fin n → R} (hc : ∀ i, 0 < c i)
    (hB : ∀ i j, c i * B i j = -(c j * B j i)) : B'.det = B.det := by
  obtain ⟨ks, π, rfl⟩ := h
  rw [Matrix.det_submatrix_equiv_self, det_matrixMutationList_of_weight hc hB ks]

/-- **Mutation equivalent skew-symmetrizable matrices have equal determinant.**

Neither sign-antisymmetry of `B` nor skew-symmetrizability of `B'` is assumed, both being
consequences. -/
@[cluster_algebras "lem_mut_equiv_det"]
theorem MutationEquiv.det_eq {B B' : Matrix (Fin n) (Fin n) R} (h : MutationEquiv B B')
    (hB : SkewSymmetrizable B) : B'.det = B.det := by
  obtain ⟨d, hd, hdB⟩ := hB
  exact h.det_eq_of_weight (c := fun i => (d i : R)) (fun i => Int.cast_pos.mpr (hd i)) hdB

end ClusterAlgebras
