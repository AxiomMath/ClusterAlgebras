/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.YPattern.YHat

/-!
# The `Y`-pattern of `ŷ`-tuples of a seed pattern

A labeled seed `(x̃, B̃)` determines a `Y`-seed `(ŷ, B)`: its `ŷ`-tuple together with the
principal part `B` of `B̃`, which is skew-symmetrizable because `B̃` is extended
skew-symmetrizable. Along a seed pattern `Σ`, the `Y`-seeds `(ŷ(t), B(t))` of the seeds `Σ(t)`
form a `Y`-pattern: at the two ends of an edge labelled `k` the principal parts are related by
matrix mutation, since mutation of `B̃` restricts to mutation of its principal part, and the
`ŷ`-tuples are related by the rule of `Y`-seed mutation, which is the mutation rule for the
`ŷ`-tuple.

## Main definitions

* `ClusterAlgebras.IsLabeledSeed.toYSeed`: the `Y`-seed `(ŷ, B)` of a labeled seed.

## Main results

* `ClusterAlgebras.IsSeedPattern.isYPattern_yHat`: the `Y`-seeds `(ŷ(t), B(t))` of a seed
  pattern form a `Y`-pattern.

## Implementation notes

FWZ work over a ground field of characteristic zero, and the main result carries
`[CharZero K]`: it is used to see that `ŷₖ ≠ -1`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra K F] {m n : ℕ}

/-- The **`Y`-seed** `(ŷ, B)` of a labeled seed `(x̃, B̃)`: its `ŷ`-tuple together with the
principal part `B` of `B̃`, which is skew-symmetrizable since `B̃` is extended
skew-symmetrizable. -/
def IsLabeledSeed.toYSeed (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) :
    YSeed F n :=
  ⟨yHat S, principalPart hmn S.extExchangeMatrix, hS.2⟩

/-- The tuple of the `Y`-seed of a labeled seed is its `ŷ`-tuple. -/
@[simp]
theorem IsLabeledSeed.toYSeed_y (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) : (hS.toYSeed hmn).y = yHat S :=
  rfl

/-- The exchange matrix of the `Y`-seed of a labeled seed is the principal part of its
extended exchange matrix. -/
@[simp]
theorem IsLabeledSeed.toYSeed_exchangeMatrix (hmn : n ≤ m) {S : SeedData F m n}
    (hS : IsLabeledSeed K hmn S) :
    (hS.toYSeed hmn).exchangeMatrix = principalPart hmn S.extExchangeMatrix :=
  rfl

/-- **The `ŷ`-tuples of a seed pattern form a `Y`-pattern.** Let `Σ` be a seed pattern of rank
`n` in `F` over a field `K` of characteristic zero, and for `t ∈ 𝕋ₙ` let `ŷ(t)` be the
`ŷ`-tuple of `Σ(t)` and `B(t)` the principal part of its extended exchange matrix. Then
`t ↦ (ŷ(t), B(t))` is a `Y`-pattern of rank `n` in `F`. -/
@[cluster_algebras "lem_yhat_pattern"]
theorem IsSeedPattern.isYPattern_yHat [CharZero K] (hmn : n ≤ m)
    {P : RegularTree n → SeedData F m n} (hP : IsSeedPattern K hmn P) :
    IsYPattern fun t => (hP.1 t).toYSeed hmn := by
  intro k t t' htt'
  have hS := hP.1 t
  have h := hP.2 k t t' htt'
  simp only [YSeed.IsMutation, IsLabeledSeed.toYSeed_y, IsLabeledSeed.toYSeed_exchangeMatrix, h]
  refine ⟨hS.yHat_ne_zero hmn k, fun h' => hS.yHat_add_one_ne_zero hmn k (by simp [h']),
    by rw [seedMutation_extExchangeMatrix, principalPart_matrixMutation],
    fun j => yHat_seedMutation hmn hS k j⟩

end ClusterAlgebras
