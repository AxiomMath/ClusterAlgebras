/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Tropical.Triple

/-!
# Tropical mutation of coefficient tuples

Let `B̃ = (bᵢⱼ)` be an `m × n` integer matrix, `k ∈ [1, n]`, and let `y = y(B̃)` and
`y' = y(μₖ(B̃))` be the coefficient tuples of `B̃` and of its mutation in direction `k`, in the
tropical semifield `Trop(q_{n+1}, …, q_m)`. Then `y'ₖ = yₖ⁻¹`, and for `j ≠ k`,
`y'ⱼ = yⱼ (yₖ ⊕ 1) ^ (-bₖⱼ)` if `bₖⱼ ≤ 0` and `y'ⱼ = yⱼ (yₖ⁻¹ ⊕ 1) ^ (-bₖⱼ)` if `bₖⱼ ≥ 0`.
So the coefficient tuple mutates by the tropical form of the coefficient mutation rule.

## Main results

* `ClusterAlgebras.coefficientTuple_matrixMutation`: the mutation rule for coefficient tuples.

## Implementation notes

The result is usually stated for an extended skew-symmetrizable matrix `B̃`. It holds for every
integer matrix `B̃`, so no hypothesis on `B̃` is assumed.
-/

@[expose] public section

namespace ClusterAlgebras

variable {m n : ℕ}

/-- A frozen position `i > n` is not the row `k ∈ [1, n]` of the principal part. -/
theorem FrozenIndex.val_ne_castLE (hmn : n ≤ m) (i : FrozenIndex m n) (k : Fin n) :
    i.1 ≠ Fin.castLE hmn k := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castLE] at this
  have := i.2
  omega

/-- The coefficient `y'ₖ` of `μₖ(B̃)` is `yₖ⁻¹`. -/
theorem coefficientTuple_matrixMutation_self (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    (k : Fin n) : coefficientTuple (matrixMutation hmn B k) k = (coefficientTuple B k)⁻¹ := by
  ext i
  simp

/-- For `j ≠ k` with `bₖⱼ ≤ 0`, the coefficient `y'ⱼ` of `μₖ(B̃)` is `yⱼ (yₖ ⊕ 1) ^ (-bₖⱼ)`. -/
theorem coefficientTuple_matrixMutation_of_nonpos (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    {k j : Fin n} (hj : j ≠ k) (hb : B (Fin.castLE hmn k) j ≤ 0) :
    coefficientTuple (matrixMutation hmn B k) j =
      coefficientTuple B j * (coefficientTuple B k + 1) ^ (-B (Fin.castLE hmn k) j) := by
  ext i
  simp only [exponent_coefficientTuple, TropicalSemifield.exponent_mul, Pi.add_apply,
    TropicalSemifield.exponent_zpow, Pi.smul_apply, smul_eq_mul, TropicalSemifield.exponent_add,
    TropicalSemifield.exponent_one, Pi.zero_apply,
    matrixMutation_apply_of_ne_eq_max hmn B k (FrozenIndex.val_ne_castLE hmn i k) hj,
    max_eq_left hb, max_eq_right (neg_nonneg.2 hb)]
  rcases le_total (B i.1 k) 0 with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonneg.2 h), min_eq_left h]
    ring
  · rw [max_eq_left (neg_nonpos.2 h), min_eq_right h]
    ring

/-- For `j ≠ k` with `bₖⱼ ≥ 0`, the coefficient `y'ⱼ` of `μₖ(B̃)` is
`yⱼ (yₖ⁻¹ ⊕ 1) ^ (-bₖⱼ)`. -/
theorem coefficientTuple_matrixMutation_of_nonneg (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    {k j : Fin n} (hj : j ≠ k) (hb : 0 ≤ B (Fin.castLE hmn k) j) :
    coefficientTuple (matrixMutation hmn B k) j =
      coefficientTuple B j * ((coefficientTuple B k)⁻¹ + 1) ^ (-B (Fin.castLE hmn k) j) := by
  ext i
  simp only [exponent_coefficientTuple, TropicalSemifield.exponent_mul, Pi.add_apply,
    TropicalSemifield.exponent_zpow, Pi.smul_apply, smul_eq_mul, TropicalSemifield.exponent_add,
    TropicalSemifield.exponent_inv, Pi.neg_apply, TropicalSemifield.exponent_one, Pi.zero_apply,
    matrixMutation_apply_of_ne_eq_max hmn B k (FrozenIndex.val_ne_castLE hmn i k) hj,
    max_eq_right hb, max_eq_left (neg_nonpos.2 hb)]
  rcases le_total (B i.1 k) 0 with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonneg.2 h), min_eq_right (neg_nonneg.2 h)]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonpos.2 h), min_eq_left (neg_nonpos.2 h)]
    ring

/-- **Tropical mutation of coefficient tuples.** Let `y = y(B̃)` and `y' = y(μₖ(B̃))` be the
coefficient tuples of `B̃` and of its mutation in direction `k`. Then `y'ₖ = yₖ⁻¹`, and for
`j ≠ k`, `y'ⱼ = yⱼ (yₖ ⊕ 1) ^ (-bₖⱼ)` if `bₖⱼ ≤ 0` and `y'ⱼ = yⱼ (yₖ⁻¹ ⊕ 1) ^ (-bₖⱼ)` if
`bₖⱼ ≥ 0`. -/
@[cluster_algebras "prop_tropical_mutation"]
theorem coefficientTuple_matrixMutation (hmn : n ≤ m) (B : Matrix (Fin m) (Fin n) ℤ)
    (k j : Fin n) :
    (j = k → coefficientTuple (matrixMutation hmn B k) j = (coefficientTuple B k)⁻¹) ∧
    (j ≠ k → B (Fin.castLE hmn k) j ≤ 0 →
      coefficientTuple (matrixMutation hmn B k) j =
        coefficientTuple B j * (coefficientTuple B k + 1) ^ (-B (Fin.castLE hmn k) j)) ∧
    (j ≠ k → 0 ≤ B (Fin.castLE hmn k) j →
      coefficientTuple (matrixMutation hmn B k) j =
        coefficientTuple B j * ((coefficientTuple B k)⁻¹ + 1) ^ (-B (Fin.castLE hmn k) j)) :=
  ⟨fun h => h ▸ coefficientTuple_matrixMutation_self hmn B k,
    coefficientTuple_matrixMutation_of_nonpos hmn B,
    coefficientTuple_matrixMutation_of_nonneg hmn B⟩

end ClusterAlgebras
