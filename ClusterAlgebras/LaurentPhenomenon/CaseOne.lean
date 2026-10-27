/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.FirstPrime

/-!
# Case one: the two new variables are coprime

Let `(x̃, B̃)` be a labeled seed with `B̃ = (bᵢₗ)`, let `j, k` be directions and `q` a row with
`b_qj = 1` and `b_qk = 0`, and let `x'ⱼ` and `x'ₖ` be the entries in positions `j` and `k` of
the extended clusters of `μⱼ(x̃, B̃)` and `μₖ(x̃, B̃)`. The variable `x'ⱼ` is prime in
`ℤ[x̃^{±1}]` and has `q`-width `1`. Since `b_qk = 0`, neither exchange monomial `M^±ₖ` involves
`x_q`, so `x'ₖ = xₖ⁻¹ (M⁺ₖ + M⁻ₖ)` has `q`-width `0`. A factorization `x'ₖ = x'ⱼ g` would give
`x'ₖ` a `q`-width of at least `1`; so `x'ⱼ` does not divide `x'ₖ`, and as `x'ⱼ` is irreducible
every common divisor of the two is a unit.

## Main results

* `ClusterAlgebras.IsLabeledSeed.hasWidth_zero_seedMutation_extCluster_castLE_self`: when
  `b_qk = 0`, the variable `x'ₖ` has `q`-width `0`.
* `ClusterAlgebras.IsLabeledSeed.not_dvd_seedMutation_extCluster_castLE_self`: when
  `b_qj = 1` and `b_qk = 0`, the variable `x'ⱼ` does not divide `x'ₖ` in `ℤ[x̃^{±1}]`.
* `ClusterAlgebras.IsLabeledSeed.isRelPrime_seedMutation_extCluster_castLE_self`: the
  variables `x'ⱼ` and `x'ₖ` are relatively prime in `ℤ[x̃^{±1}]`: every common divisor is a unit.

Along the way:

* `ClusterAlgebras.seedMutation_extCluster_mem_laurentSubring_self`: every entry of the
  extended cluster of a mutation of any seed lies in the Laurent ring of the original extended
  cluster.

## Implementation notes

FWZ take `q` to be a frozen index, `q ∈ [n + 1, m]`, and `j ≠ k`. Neither is used:
`j ≠ k` follows from `b_qj = 1 ≠ 0 = b_qk`, and when `q` is the position of `k` the variable
`x'ₖ = (M⁺ₖ + M⁻ₖ) x_q⁻¹` still has `q`-width `0`, since `M^±ₖ` avoid `x_q` because the
diagonal entry `bₖₖ` vanishes. So the results are stated for every row `q` and every pair of
directions. FWZ take the ground field of characteristic zero; it is used through the
irreducibility of `x'ⱼ` and the uniqueness of widths.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra K F] {m n : ℕ}

/-- Every entry of the extended cluster of the mutation `μₗ(S)` of a seed `S` lies in
`ℤ[x̃^{±1}]`, where `x̃` is the extended cluster of `S`: the new entry is
`xₗ⁻¹ (M⁺ₗ + M⁻ₗ)`. -/
theorem seedMutation_extCluster_mem_laurentSubring_self (hmn : n ≤ m) (S : SeedData F m n)
    (l : Fin n) (i : Fin m) :
    (seedMutation hmn S l).extCluster i ∈ laurentSubring S.extCluster := by
  rcases eq_or_ne i (Fin.castLE hmn l) with rfl | hi
  · have hmem : ∀ i, S.extExchangeMatrix i l ≠ 0 → S.extCluster i ∈
        laurentSubring S.extCluster := fun i _ => mem_laurentSubring _ i
    rw [seedMutation_extCluster_castLE_self, div_eq_mul_inv]
    exact mul_mem (add_mem (exchangeMonomialPos_mem_of_mem _ hmem)
      (exchangeMonomialNeg_mem_of_mem _ hmem)) (inv_mem_laurentSubring _ _)
  · rw [seedMutation_extCluster_of_ne hmn S hi]
    exact mem_laurentSubring _ i

/-- **The second new variable has width zero.** For a seed `S`, a direction `k` and a row `q`
with `b_qk = 0`, if `xₖ` and `M⁺ₖ + M⁻ₖ` are nonzero then the entry `x'ₖ` of `μₖ(S)` has
`q`-width `0`: it is `(M⁺ₖ + M⁻ₖ) xₖ⁻¹`, and neither exchange monomial involves `x_q`. -/
theorem hasWidth_zero_seedMutation_extCluster_castLE_self (hmn : n ≤ m) (S : SeedData F m n)
    {k : Fin n} {q : Fin m} (hx : S.extCluster (Fin.castLE hmn k) ≠ 0)
    (hM : exchangeMonomialPos S.extCluster S.extExchangeMatrix k +
      exchangeMonomialNeg S.extCluster S.extExchangeMatrix k ≠ 0)
    (hqk : S.extExchangeMatrix q k = 0) :
    HasWidth S.extCluster q ((seedMutation hmn S k).extCluster (Fin.castLE hmn k)) 0 := by
  have hmem : ∀ i, S.extExchangeMatrix i k ≠ 0 → S.extCluster i ∈
      laurentSubringExcept S.extCluster q := fun i hi =>
    mem_laurentSubringExcept _ fun h => hi (h ▸ hqk)
  have hc := add_mem (exchangeMonomialPos_mem_of_mem _ hmem)
    (exchangeMonomialNeg_mem_of_mem _ hmem)
  rw [seedMutation_extCluster_castLE_self, div_eq_mul_inv, hasWidth_zero_iff]
  rcases eq_or_ne q (Fin.castLE hmn k) with rfl | hq
  · exact ⟨-1, _, hc, hM, by rw [zpow_neg_one]⟩
  · exact ⟨0, _, mul_mem hc (inv_mem_laurentSubringExcept _ (Ne.symm hq)),
      mul_ne_zero hM (inv_ne_zero hx), by rw [zpow_zero, mul_one]⟩

variable (hmn : n ≤ m) {S : SeedData F m n}

/-- **The second new variable has width zero.** For a labeled seed `S`, a direction `k` and a
row `q` with `b_qk = 0`, the entry `x'ₖ` of `μₖ(S)` has `q`-width `0`. -/
theorem IsLabeledSeed.hasWidth_zero_seedMutation_extCluster_castLE_self [CharZero K]
    (hS : IsLabeledSeed K hmn S) {k : Fin n} {q : Fin m} (hqk : S.extExchangeMatrix q k = 0) :
    HasWidth S.extCluster q
      ((ClusterAlgebras.seedMutation hmn S k).extCluster (Fin.castLE hmn k)) 0 :=
  ClusterAlgebras.hasWidth_zero_seedMutation_extCluster_castLE_self hmn S (hS.1.1.ne_zero _)
    (hS.exchangeMonomialPos_add_exchangeMonomialNeg_ne_zero hmn k) hqk

/-- **The first new variable does not divide the second.** For a labeled seed `S` over a field
of characteristic zero, directions `j, k` and a row `q` with `b_qj = 1` and `b_qk = 0`, the
entry `x'ⱼ` of `μⱼ(S)` does not divide the entry `x'ₖ` of `μₖ(S)` in `ℤ[x̃^{±1}]`: the former
has `q`-width `1` and the latter `q`-width `0`. -/
@[cluster_algebras "lem_case_one_coprime"]
theorem IsLabeledSeed.not_dvd_seedMutation_extCluster_castLE_self [CharZero K]
    (hS : IsLabeledSeed K hmn S) {j k : Fin n} {q : Fin m} (hqj : S.extExchangeMatrix q j = 1)
    (hqk : S.extExchangeMatrix q k = 0) :
    ¬ (⟨_, hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j hqj⟩ :
        laurentSubring S.extCluster) ∣
      ⟨_, seedMutation_extCluster_mem_laurentSubring_self hmn S k (Fin.castLE hmn k)⟩ := by
  haveI := Algebra.charZero_of_charZero K F
  rintro ⟨g, hg⟩
  have hk := hS.hasWidth_zero_seedMutation_extCluster_castLE_self hmn hqk
  rw [show (ClusterAlgebras.seedMutation hmn S k).extCluster (Fin.castLE hmn k) =
    (ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j) * g from
      congrArg Subtype.val hg] at hk
  exact absurd (hk.le_of_mul (hS.algebraicIndependent_rat hmn)
    (hS.hasWidth_seedMutation_extCluster_castLE_self hmn j hqj) g.2) (by decide)

/-- **Case one: the two new variables are coprime.** For a labeled seed `S` over a field of
characteristic zero, directions `j, k` and a row `q` with `b_qj = 1` and `b_qk = 0`, the
entry `x'ⱼ` of `μⱼ(S)` and the entry `x'ₖ` of `μₖ(S)` are relatively prime in `ℤ[x̃^{±1}]`:
every common divisor is a unit. -/
@[cluster_algebras "lem_case_one_coprime"]
theorem IsLabeledSeed.isRelPrime_seedMutation_extCluster_castLE_self [CharZero K]
    (hS : IsLabeledSeed K hmn S) {j k : Fin n} {q : Fin m} (hqj : S.extExchangeMatrix q j = 1)
    (hqk : S.extExchangeMatrix q k = 0) :
    IsRelPrime (⟨_, hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j hqj⟩ :
        laurentSubring S.extCluster)
      ⟨_, seedMutation_extCluster_mem_laurentSubring_self hmn S k (Fin.castLE hmn k)⟩ :=
  (hS.prime_seedMutation_extCluster_castLE_self hmn j hqj).irreducible.isRelPrime_iff_not_dvd.2
    (hS.not_dvd_seedMutation_extCluster_castLE_self hmn hqj hqk)

end ClusterAlgebras
