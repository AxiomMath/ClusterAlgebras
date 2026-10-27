/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.YPattern.Defs
public import ClusterAlgebras.LaurentPhenomenon.ThreeMutations

/-!
# The `ŷ`-tuple under seed mutation

Let `(x̃, B̃)` be a labeled seed with `B̃ = (bᵢⱼ)`, let `k ∈ [1, n]`, and let `ŷ` and `ŷ'` be
the `ŷ`-tuples of `(x̃, B̃)` and of `μₖ(x̃, B̃)`. Then `ŷ'` is determined by `ŷ` and the
exchange matrix alone:
* `ŷ'ₖ = ŷₖ⁻¹`,
* `ŷ'ⱼ = ŷⱼ (ŷₖ + 1) ^ (-bₖⱼ)` if `j ≠ k` and `bₖⱼ ≤ 0`,
* `ŷ'ⱼ = ŷⱼ (ŷₖ⁻¹ + 1) ^ (-bₖⱼ)` if `j ≠ k` and `bₖⱼ ≥ 0`.

The first case is a direct computation, using `bₖₖ = 0`. For the second, the exchange
binomial factors as `M⁺ₖ + M⁻ₖ = M⁻ₖ (ŷₖ + 1)`, and the mutated entries of column `j` are
`b'ᵢⱼ = bᵢⱼ + [-bᵢₖ]₊ bₖⱼ` off row `k`, so the new factors `(x'ₖ) ^ (-bₖⱼ)` and
`∏ᵢ xᵢ ^ ([-bᵢₖ]₊ bₖⱼ) = (M⁻ₖ) ^ bₖⱼ` combine to `(ŷₖ + 1) ^ (-bₖⱼ)`. The third case follows
from the second applied to `μₖ(x̃, B̃)`, since seed mutation is an involution.

## Main results

* `ClusterAlgebras.yHat_seedMutation_of_nonpos`: the case `j ≠ k`, `bₖⱼ ≤ 0`.
* `ClusterAlgebras.yHat_seedMutation`: the mutation rule for the `ŷ`-tuple, all three cases.

## Implementation notes

FWZ work over a ground field of characteristic zero; the statements about labeled
seeds carry `[CharZero K]`. The identities of the first two cases hold for any seed data whose
entries are nonzero and whose extended exchange matrix has `bₖₖ = 0`, and are proved in that
generality first.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {m n : ℕ}

section ExchangeMonomial

variable {x : Fin m → F} {B : Matrix (Fin m) (Fin n) ℤ} {k : Fin n}

/-- The negative exchange monomial of a tuple of nonzero elements is nonzero. -/
theorem exchangeMonomialNeg_ne_zero (hx : ∀ i, x i ≠ 0) : exchangeMonomialNeg x B k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hx i)

end ExchangeMonomial

section SeedData

variable {S : SeedData F m n}

/-- The `ŷ`-tuple of a seed whose entries are nonzero has nonzero entries. -/
theorem yHat_ne_zero (hx : ∀ i, S.extCluster i ≠ 0) (j : Fin n) : yHat S j ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hx i)

/-- For a seed whose entries are nonzero, the exchange binomial in direction `k` factors as
`M⁺ₖ + M⁻ₖ = M⁻ₖ (ŷₖ + 1)`. -/
theorem exchangeMonomialPos_add_exchangeMonomialNeg_eq_mul_yHat_add_one
    (hx : ∀ i, S.extCluster i ≠ 0) (k : Fin n) :
    exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
        exchangeMonomialNeg S.extCluster S.extExchangeMatrix k =
      exchangeMonomialNeg S.extCluster S.extExchangeMatrix k * (yHat S k + 1) :=
  exchangeMonomialPos_add_exchangeMonomialNeg_eq_mul hx

/-- **The `ŷ`-tuple under mutation, case `j = k`.** If `bₖₖ = 0`, then `ŷ'ₖ = ŷₖ⁻¹`, where
`ŷ'` is the `ŷ`-tuple of `μₖ(x̃, B̃)`. -/
theorem yHat_seedMutation_self_of_eq_zero (hmn : n ≤ m) {k : Fin n}
    (hkk : S.extExchangeMatrix (Fin.castLE hmn k) k = 0) :
    yHat (seedMutation hmn S k) k = (yHat S k)⁻¹ := by
  rw [yHat, yHat, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [seedMutation_extExchangeMatrix, matrixMutation_apply_col, zpow_neg]
  by_cases hi : i = Fin.castLE hmn k
  · rw [hi, hkk, zpow_zero, zpow_zero]
  · rw [seedMutation_extCluster_of_ne hmn S hi]

/-- **The `ŷ`-tuple under mutation, case `j ≠ k`, `bₖⱼ ≤ 0`, for seed data.** If the entries
of `x̃` are nonzero and `bₖₖ = 0`, then `ŷ'ⱼ = ŷⱼ (ŷₖ + 1) ^ (-bₖⱼ)` for `j ≠ k` with
`bₖⱼ ≤ 0`, where `ŷ'` is the `ŷ`-tuple of `μₖ(x̃, B̃)`. -/
theorem yHat_seedMutation_of_nonpos_of_ne_zero (hmn : n ≤ m) (hx : ∀ i, S.extCluster i ≠ 0)
    {k j : Fin n} (hkk : S.extExchangeMatrix (Fin.castLE hmn k) k = 0) (hjk : j ≠ k)
    (hb : S.extExchangeMatrix (Fin.castLE hmn k) j ≤ 0) :
    yHat (seedMutation hmn S k) j =
      yHat S j * (yHat S k + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j) := by
  classical
  have hMn := exchangeMonomialNeg_ne_zero (B := S.extExchangeMatrix) (k := k) hx
  have hyk : yHat S k + 1 =
      (exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
        exchangeMonomialNeg S.extCluster S.extExchangeMatrix k) /
        exchangeMonomialNeg S.extCluster S.extExchangeMatrix k := by
    rw [exchangeMonomialPos_add_exchangeMonomialNeg_eq_mul_yHat_add_one hx]
    field_simp
  calc yHat (seedMutation hmn S k) j
      = ∏ i, S.extCluster i ^ S.extExchangeMatrix i j *
          (S.extCluster i ^ (-S.extExchangeMatrix i k).toNat) ^
            S.extExchangeMatrix (Fin.castLE hmn k) j *
          (if i = Fin.castLE hmn k then
            (exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
              exchangeMonomialNeg S.extCluster S.extExchangeMatrix k) ^
                (-S.extExchangeMatrix (Fin.castLE hmn k) j) else 1) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [seedMutation_extExchangeMatrix]
        by_cases hi : i = Fin.castLE hmn k
        · rw [hi, if_pos rfl, matrixMutation_apply_row, seedMutation_extCluster_castLE_self, hkk,
            neg_zero, Int.toNat_zero, pow_zero, one_zpow, mul_one, div_zpow,
            zpow_neg (S.extCluster _), div_inv_eq_mul, mul_comm]
        · rw [if_neg hi, mul_one, seedMutation_extCluster_of_ne hmn S hi,
            matrixMutation_apply_of_ne_eq_max hmn _ k hi hjk, max_eq_left hb,
            max_eq_right (neg_nonneg.2 hb), ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hx i),
            Int.toNat_eq_max, max_comm (-S.extExchangeMatrix i k)]
          congr 1
          ring
    _ = yHat S j * exchangeMonomialNeg S.extCluster S.extExchangeMatrix k ^
          S.extExchangeMatrix (Fin.castLE hmn k) j *
          (exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
            exchangeMonomialNeg S.extCluster S.extExchangeMatrix k) ^
              (-S.extExchangeMatrix (Fin.castLE hmn k) j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
          if_pos (Finset.mem_univ _), Finset.prod_zpow, exchangeMonomialNeg_eq_prod]
        rfl
    _ = yHat S j * (yHat S k + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j) := by
        rw [hyk, div_zpow, zpow_neg (exchangeMonomialNeg _ _ _), div_inv_eq_mul]
        ring

end SeedData

section LabeledSeed

variable {K : Type*} [Field K] [Algebra K F] {S : SeedData F m n}

/-- The `ŷ`-tuple of a labeled seed has nonzero entries. -/
theorem IsLabeledSeed.yHat_ne_zero (hmn : n ≤ m) (hS : IsLabeledSeed K hmn S) (j : Fin n) :
    yHat S j ≠ 0 :=
  ClusterAlgebras.yHat_ne_zero hS.1.1.ne_zero j

/-- For a labeled seed over a field of characteristic zero, `ŷₖ + 1 ≠ 0`: it is the quotient
`(M⁺ₖ + M⁻ₖ) / M⁻ₖ` of the nonzero exchange binomial by a monomial. -/
theorem IsLabeledSeed.yHat_add_one_ne_zero [CharZero K] (hmn : n ≤ m)
    (hS : IsLabeledSeed K hmn S) (k : Fin n) : yHat S k + 1 ≠ 0 := by
  have h := hS.exchangeMonomialPos_add_exchangeMonomialNeg_ne_zero hmn k
  rw [exchangeMonomialPos_add_exchangeMonomialNeg_eq_mul_yHat_add_one hS.1.1.ne_zero] at h
  exact right_ne_zero_of_mul h

/-- **The `ŷ`-tuple under mutation, case `j = k`.** For a labeled seed, `ŷ'ₖ = ŷₖ⁻¹`, where
`ŷ'` is the `ŷ`-tuple of `μₖ(x̃, B̃)`. -/
theorem yHat_seedMutation_self (hmn : n ≤ m) (hS : IsLabeledSeed K hmn S) (k : Fin n) :
    yHat (seedMutation hmn S k) k = (yHat S k)⁻¹ :=
  yHat_seedMutation_self_of_eq_zero hmn (hS.extExchangeMatrix_castLE_self hmn k)

/-- **The `ŷ`-tuple under mutation, nonpositive case.** Let `(x̃, B̃)` be a labeled seed with
`B̃ = (bᵢⱼ)`, let `ŷ` and `ŷ'` be the `ŷ`-tuples of `(x̃, B̃)` and of `μₖ(x̃, B̃)`, and let
`j ≠ k` with `bₖⱼ ≤ 0`. Then `ŷ'ⱼ = ŷⱼ (ŷₖ + 1) ^ (-bₖⱼ)`. FWZ take the ground field
of characteristic zero; the identity does not need it. -/
@[cluster_algebras "lem_yhat_nonpositive"]
theorem yHat_seedMutation_of_nonpos (hmn : n ≤ m) (hS : IsLabeledSeed K hmn S) {k j : Fin n}
    (hjk : j ≠ k) (hb : S.extExchangeMatrix (Fin.castLE hmn k) j ≤ 0) :
    yHat (seedMutation hmn S k) j =
      yHat S j * (yHat S k + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j) :=
  yHat_seedMutation_of_nonpos_of_ne_zero hmn hS.1.1.ne_zero
    (hS.extExchangeMatrix_castLE_self hmn k) hjk hb

/-- **The `ŷ`-tuple under mutation, nonnegative case.** Let `(x̃, B̃)` be a labeled seed over
a field of characteristic zero with `B̃ = (bᵢⱼ)`, let `ŷ` and `ŷ'` be the `ŷ`-tuples of
`(x̃, B̃)` and of `μₖ(x̃, B̃)`, and let `j ≠ k` with `bₖⱼ ≥ 0`. Then
`ŷ'ⱼ = ŷⱼ (ŷₖ⁻¹ + 1) ^ (-bₖⱼ)`. -/
theorem yHat_seedMutation_of_nonneg [CharZero K] (hmn : n ≤ m) (hS : IsLabeledSeed K hmn S)
    {k j : Fin n} (hjk : j ≠ k) (hb : 0 ≤ S.extExchangeMatrix (Fin.castLE hmn k) j) :
    yHat (seedMutation hmn S k) j =
      yHat S j * ((yHat S k)⁻¹ + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j) := by
  have hS' := hS.seedMutation hmn k
  have hb' : (seedMutation hmn S k).extExchangeMatrix (Fin.castLE hmn k) j ≤ 0 := by
    rw [seedMutation_extExchangeMatrix, matrixMutation_apply_row]
    exact neg_nonpos.2 hb
  have h := yHat_seedMutation_of_nonpos hmn hS' hjk hb'
  have hne := hS'.yHat_add_one_ne_zero hmn k
  rw [seedMutation_seedMutation hmn hS, yHat_seedMutation_self hmn hS,
    seedMutation_extExchangeMatrix, matrixMutation_apply_row, neg_neg] at h
  rw [yHat_seedMutation_self hmn hS] at hne
  rw [h, mul_assoc, ← zpow_add₀ hne, add_neg_cancel, zpow_zero, mul_one]

/-- **Mutation of the `ŷ`-tuple is governed by the exchange matrix.** Let `(x̃, B̃)` be a
labeled seed over a field of characteristic zero with `B̃ = (bᵢⱼ)`, let `k ∈ [1, n]`, and let
`ŷ` and `ŷ'` be the `ŷ`-tuples of `(x̃, B̃)` and of `μₖ(x̃, B̃)`. Then for every `j`,
* `ŷ'ⱼ = ŷₖ⁻¹` if `j = k`,
* `ŷ'ⱼ = ŷⱼ (ŷₖ + 1) ^ (-bₖⱼ)` if `j ≠ k` and `bₖⱼ ≤ 0`,
* `ŷ'ⱼ = ŷⱼ (ŷₖ⁻¹ + 1) ^ (-bₖⱼ)` if `j ≠ k` and `bₖⱼ ≥ 0`. -/
@[cluster_algebras "thm_yhat"]
theorem yHat_seedMutation [CharZero K] (hmn : n ≤ m) (hS : IsLabeledSeed K hmn S)
    (k j : Fin n) :
    (j = k → yHat (seedMutation hmn S k) j = (yHat S k)⁻¹) ∧
      (j ≠ k → S.extExchangeMatrix (Fin.castLE hmn k) j ≤ 0 →
        yHat (seedMutation hmn S k) j =
          yHat S j * (yHat S k + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j)) ∧
      (j ≠ k → 0 ≤ S.extExchangeMatrix (Fin.castLE hmn k) j →
        yHat (seedMutation hmn S k) j =
          yHat S j * ((yHat S k)⁻¹ + 1) ^ (-S.extExchangeMatrix (Fin.castLE hmn k) j)) :=
  ⟨fun h => h ▸ yHat_seedMutation_self hmn hS k, yHat_seedMutation_of_nonpos hmn hS,
    yHat_seedMutation_of_nonneg hmn hS⟩

end LabeledSeed

end ClusterAlgebras
