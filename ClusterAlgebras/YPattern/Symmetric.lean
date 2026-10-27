/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.External
public import ClusterAlgebras.YPattern.Defs

/-!
# `Y`-seed mutation is symmetric

If `(Y', B')` is obtained from `(Y, B)` by `Y`-seed mutation in direction `k`, then `(Y, B)` is
obtained from `(Y', B')` by `Y`-seed mutation in direction `k`. Indeed `Y'ₖ = Yₖ⁻¹` is neither
`0` nor `-1`, `μₖ(B') = μₖ(μₖ(B)) = B` since matrix mutation is an involution, and
`b'ₖⱼ = -bₖⱼ`, so for `j ≠ k` the factor `(Yₖ + 1) ^ (-bₖⱼ)` (resp. `(Yₖ⁻¹ + 1) ^ (-bₖⱼ)`)
introduced by the first mutation is cancelled by the factor `(Y'ₖ⁻¹ + 1) ^ (-b'ₖⱼ)`
(resp. `(Y'ₖ + 1) ^ (-b'ₖⱼ)`) introduced by the second.

## Main results

* `ClusterAlgebras.YSeed.IsMutation.symm`: `Y`-seed mutation in direction `k` is a symmetric
  relation.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {n : ℕ}

/-- **`Y`-seed mutation is symmetric.** If `(Y, B)` and `(Y', B')` are related by `Y`-seed
mutation in direction `k`, then so are `(Y', B')` and `(Y, B)`. -/
@[cluster_algebras "lem_y_seed_mutation_symmetric"]
theorem YSeed.IsMutation.symm {k : Fin n} {s s' : YSeed F n} (h : YSeed.IsMutation k s s') :
    YSeed.IsMutation k s' s := by
  obtain ⟨h0, h1, hB, hy⟩ := h
  have hyk : s'.y k = (s.y k)⁻¹ := (hy k).1 rfl
  have hrow (j : Fin n) : s'.exchangeMatrix k j = -s.exchangeMatrix k j := by
    rw [hB]
    exact matrixMutation_apply_of_eq le_rfl s.exchangeMatrix k (Or.inl rfl)
  have hinv : (s.y k)⁻¹ ≠ -1 := fun h ↦ h1 (by simpa using congrArg (·⁻¹) h)
  have hp : s.y k + 1 ≠ 0 := fun h ↦ h1 (eq_neg_of_add_eq_zero_left h)
  have hq : (s.y k)⁻¹ + 1 ≠ 0 := fun h ↦ hinv (eq_neg_of_add_eq_zero_left h)
  refine ⟨hyk ▸ inv_ne_zero h0, hyk ▸ hinv, ?_, fun j ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [hB, matrixMutation_matrixMutation]
  · rintro rfl
    rw [hyk, inv_inv]
  · intro hjk hb
    rw [hrow, neg_nonpos] at hb
    rw [(hy j).2.2 hjk hb, hyk, hrow, neg_neg, mul_assoc, ← zpow_add₀ hq, neg_add_cancel,
      zpow_zero, mul_one]
  · intro hjk hb
    rw [hrow, neg_nonneg] at hb
    rw [(hy j).2.1 hjk hb, hyk, inv_inv, hrow, neg_neg, mul_assoc, ← zpow_add₀ hp,
      neg_add_cancel, zpow_zero, mul_one]

end ClusterAlgebras
