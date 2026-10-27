/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.LaurentPhenomenon.FirstPrime
public import ClusterAlgebras.LaurentPhenomenon.AugmentedBlock

/-!
# Case two of the Laurent phenomenon: the first two new variables are coprime

Let `(x̃, B̃)` be a labeled seed with `B̃ = (bᵢₗ)`, let `j, k` be directions with `bⱼₖ < 0`, and
let `q, r` be rows such that row `q` is the unit row with `1` in column `j` and row `r` is the
unit row with `1` in column `k`. Let `x'ⱼ` be the entry in position `j` of `μⱼ(x̃, B̃)` and
`x'ₖ` the entry in position `k` of `μₖ(μⱼ(x̃, B̃))`. Both lie in `L = ℤ[x̃^{±1}]`, and they are
relatively prime there.

Write `B̃₁ = μⱼ(B̃) = (b¹ᵢₗ)`. By the first new variable lemma, `x'ⱼ` is prime in `L`; since
`b_rj = 0` it does not involve `x_r`, so `x'ⱼ ∈ ℤ[x̃_r̂^{±1}]` and `x'ⱼ` has `r`-width `0`. On
the other hand `b¹_rk = b_rk = 1` and `b¹ⱼₖ = -bⱼₖ > 0`, so `x_r` occurs in `M⁺ₖ(μⱼ(x̃, B̃))`
with exponent `1`, and neither `x_r` nor `x'ⱼ` occurs in `M⁻ₖ(μⱼ(x̃, B̃))`. Hence
`x'ₖ = A x_r + B` with `A ≠ 0` in `ℤ[x̃_r̂^{±1}]` and `B` a unit there. If `x'ⱼ` divided `x'ₖ`,
the factor `x'ⱼ` of `r`-width `0` would be a unit, which a prime is not. Since `x'ⱼ` is
irreducible, not dividing `x'ₖ` is the same as being relatively prime to it.

## Main results

* `ClusterAlgebras.IsLabeledSeed.isRelPrime_seedMutation_seedMutation_extCluster_castLE`:
  every common divisor of `x'ⱼ` and `x'ₖ` in `ℤ[x̃^{±1}]` is a unit.

Along the way:

* `ClusterAlgebras.IsLabeledSeed.seedMutation_seedMutation_extCluster_castLE_mem_laurentSubring`:
  `x'ₖ ∈ ℤ[x̃^{±1}]`.
* `ClusterAlgebras.IsLabeledSeed.exists_seedMutation_seedMutation_extCluster_castLE_eq_mul_add`:
  the linear form `x'ₖ = A x_r + B`.
* `ClusterAlgebras.IsLabeledSeed.not_dvd_seedMutation_seedMutation_extCluster_castLE`: `x'ⱼ`
  does not divide `x'ₖ` in `ℤ[x̃^{±1}]`.

## Implementation notes

Relative primality is Mathlib's `IsRelPrime`: every common divisor is a unit.

FWZ take `q, r ∈ [n + 1, m]` frozen rows with `q ≠ r`. Neither is assumed: `q ≠ r`
follows from the entries of the two unit rows, `r` differs from the positions of `j` and `k`
because `b_rk = 1` differs from `bⱼₖ < 0` and from the diagonal entry `bₖₖ = 0`, and `q`
differs from the position of `j` because `b_qj = 1`. Of the two unit rows only the entries
`b_qj = 1`, `b_rj = 0` and `b_rk = 1` are used, and the intermediate results are stated under
exactly these; the main result keeps FWZ's form of the two rows. The condition `j ≠ k`,
which the entries also force, is kept as a hypothesis: it makes the entry of `μⱼ(S)` in
position `k` equal to `xₖ`, so it enters the membership of `x'ₖ` in `ℤ[x̃^{±1}]` on which the
statements depend. The linear form does not assume it.

FWZ write `M⁺ₖ` and `M⁻ₖ` as explicit products over the rows other than `j, k, q, r`;
here `M⁺ₖ = x_r P` with `P` the product over the rows other than `r`, and `M⁻ₖ` is kept whole,
since it involves neither `x_r` nor `x'ⱼ`. FWZ conclude that `x'ₖ` is irreducible and
compare widths in a factorization `x'ₖ = x'ⱼ g`; here the factor `x'ⱼ`, of `r`-width `0`, is
shown directly to be a unit, which is the step of the irreducibility argument that the
comparison of widths uses.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {K : Type*} [Field K] [Algebra K F] {m n : ℕ} (hmn : n ≤ m)
  {S : SeedData F m n}

/-- **The second new variable is Laurent.** For a labeled seed `S`, distinct directions
`j, k` and a row `q` with `b_qj = 1`, the entry `x'ₖ` of `μₖ(μⱼ(S))` lies in `ℤ[x̃^{±1}]`. -/
theorem IsLabeledSeed.seedMutation_seedMutation_extCluster_castLE_mem_laurentSubring
    (hS : IsLabeledSeed K hmn S) {j k : Fin n} (hjk : j ≠ k) {q : Fin m}
    (hqj : S.extExchangeMatrix q j = 1) :
    (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k).extCluster
      (Fin.castLE hmn k) ∈ laurentSubring S.extCluster := by
  have hS₁ : ∀ i, (ClusterAlgebras.seedMutation hmn S j).extCluster i ∈
      laurentSubring S.extCluster := fun i => by
    rcases eq_or_ne i (Fin.castLE hmn j) with rfl | hi
    · exact hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j hqj
    · rw [seedMutation_extCluster_of_ne hmn S hi]
      exact mem_laurentSubring _ i
  refine seedMutation_extCluster_mem_laurentSubring _ hmn hS₁ k ?_ _
  have h : Fin.castLE hmn k ≠ Fin.castLE hmn j := fun h => hjk (Fin.castLE_injective hmn h).symm
  have he : (⟨_, hS₁ (Fin.castLE hmn k)⟩ : laurentSubring S.extCluster) =
      ⟨S.extCluster (Fin.castLE hmn k), mem_laurentSubring _ _⟩ :=
    Subtype.ext (seedMutation_extCluster_of_ne hmn S h)
  rw [he]
  exact isUnit_mem_laurentSubring _ (hS.1.1.ne_zero _)

/-- **The linear form of the second new variable.** For a labeled seed `S`, directions `j, k`
with `bⱼₖ < 0` and a row `r` with `b_rj = 0` and `b_rk = 1`, the entry `x'ₖ` of `μₖ(μⱼ(S))`
is `A x_r + B` with `A ≠ 0` in `ℤ[x̃_r̂^{±1}]` and `B` a unit of `ℤ[x̃_r̂^{±1}]`. -/
theorem IsLabeledSeed.exists_seedMutation_seedMutation_extCluster_castLE_eq_mul_add
    [CharZero K] (hS : IsLabeledSeed K hmn S) {j k : Fin n}
    (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) {r : Fin m}
    (hrj : S.extExchangeMatrix r j = 0) (hrk : S.extExchangeMatrix r k = 1) :
    ∃ A B : laurentSubringExcept S.extCluster r, A ≠ 0 ∧ IsUnit B ∧
      (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k).extCluster
        (Fin.castLE hmn k) = A * S.extCluster r + B := by
  classical
  set x := S.extCluster
  set S₁ := ClusterAlgebras.seedMutation hmn S j
  have hkj : k ≠ j := by
    rintro rfl
    rw [hrj] at hrk
    exact zero_ne_one hrk
  have hc : Fin.castLE hmn k ≠ Fin.castLE hmn j := fun h => hkj (Fin.castLE_injective hmn h)
  have hrj' : r ≠ Fin.castLE hmn j := by
    rintro rfl
    rw [hrk] at hb
    exact absurd hb (by norm_num)
  have hck : Fin.castLE hmn k ≠ r :=
    (hS.ne_castLE_of_extExchangeMatrix_ne_zero hmn (by rw [hrk]; exact one_ne_zero)).symm
  have hx₁ : ∀ i, i ≠ Fin.castLE hmn j → S₁.extCluster i = x i := fun i hi =>
    seedMutation_extCluster_of_ne hmn S hi
  have hB₁rk : S₁.extExchangeMatrix r k = 1 := by
    change matrixMutation hmn S.extExchangeMatrix j r k = 1
    rw [matrixMutation_apply_of_eq_zero hmn _ j hrj' hkj (Or.inl hrj), hrk]
  have hB₁jk : 0 < S₁.extExchangeMatrix (Fin.castLE hmn j) k := by
    change 0 < matrixMutation hmn S.extExchangeMatrix j (Fin.castLE hmn j) k
    rw [matrixMutation_apply_row]
    exact neg_pos.2 hb
  have hmem : ∀ i, i ≠ r → S₁.extCluster i ∈ laurentSubringExcept x r := fun i hi => by
    rcases eq_or_ne i (Fin.castLE hmn j) with rfl | hij
    · exact seedMutation_extCluster_castLE_self_mem_laurentSubringExcept hmn S hrj' hrj
    · rw [hx₁ i hij]
      exact mem_laurentSubringExcept x hi
  set P := ∏ i ∈ Finset.univ.erase r, S₁.extCluster i ^ (S₁.extExchangeMatrix i k).toNat
  set N := ∏ i, x i ^ (-S₁.extExchangeMatrix i k).toNat
  have hN : ∀ i ∈ Finset.univ, (-S₁.extExchangeMatrix i k).toNat ≠ 0 → i ≠ r :=
    fun i _ h hir => h (by rw [hir, hB₁rk]; rfl)
  have hA : (x (Fin.castLE hmn k))⁻¹ * P ∈ laurentSubringExcept x r :=
    mul_mem (inv_mem_laurentSubringExcept x hck)
      (prod_mem fun i hi => pow_mem (hmem i (Finset.ne_of_mem_erase hi)) _)
  have hB : (x (Fin.castLE hmn k))⁻¹ * N ∈ laurentSubringExcept x r :=
    mul_mem (inv_mem_laurentSubringExcept x hck) (prod_pow_mem_laurentSubringExcept hN)
  have hxk := hS.1.1.ne_zero (Fin.castLE hmn k)
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
    pow_ne_zero _ (hS.seedMutation_extCluster_ne_zero hmn j i)
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hS.1.1.ne_zero i)
  refine ⟨⟨_, hA⟩, ⟨_, hB⟩, fun h => mul_ne_zero (inv_ne_zero hxk) hP0 (congrArg Subtype.val h),
    (Submonoid.isUnit_iff_of_ne_zero (mul_ne_zero (inv_ne_zero hxk) hN0)).2 ?_, ?_⟩
  · rw [mul_inv, inv_inv]
    exact mul_mem (mem_laurentSubringExcept x hck) (inv_prod_pow_mem_laurentSubringExcept hN)
  · have hpos : exchangeMonomialPos S₁.extCluster S₁.extExchangeMatrix k = x r * P := by
      rw [exchangeMonomialPos_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ r), hB₁rk,
        hx₁ r hrj']
      simp [P]
    have hneg : exchangeMonomialNeg S₁.extCluster S₁.extExchangeMatrix k = N := by
      rw [exchangeMonomialNeg_congr_of_neg (x := x) fun i hi => hx₁ i fun h => by
        rw [h] at hi
        exact hi.not_gt hB₁jk, exchangeMonomialNeg_eq_prod]
    rw [seedMutation_extCluster_castLE_self, hx₁ _ hc, hpos, hneg, div_eq_inv_mul]
    ring

/-- **The first new variable does not divide the second.** For a labeled seed `S` over a field
of characteristic zero, distinct directions `j, k` with `bⱼₖ < 0`, a row `q` with `b_qj = 1` and
a row `r` with `b_rj = 0` and `b_rk = 1`, the entry `x'ⱼ` of `μⱼ(S)` does not divide the entry
`x'ₖ` of `μₖ(μⱼ(S))` in `ℤ[x̃^{±1}]`. -/
theorem IsLabeledSeed.not_dvd_seedMutation_seedMutation_extCluster_castLE [CharZero K]
    (hS : IsLabeledSeed K hmn S) {j k : Fin n} (hjk : j ≠ k)
    (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) {q r : Fin m}
    (hqj : S.extExchangeMatrix q j = 1) (hrj : S.extExchangeMatrix r j = 0)
    (hrk : S.extExchangeMatrix r k = 1) :
    ¬ (⟨_, hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j hqj⟩ :
        laurentSubring S.extCluster) ∣
      ⟨_, hS.seedMutation_seedMutation_extCluster_castLE_mem_laurentSubring hmn hjk hqj⟩ := by
  haveI := Algebra.charZero_of_charZero K F
  have hy := hS.algebraicIndependent_rat hmn
  obtain ⟨A, B, hA, hB, hx⟩ :=
    hS.exists_seedMutation_seedMutation_extCluster_castLE_eq_mul_add hmn hb hrj hrk
  have hrj' : r ≠ Fin.castLE hmn j := by
    rintro rfl
    rw [hrk] at hb
    exact absurd hb (by norm_num)
  have hw : HasWidth S.extCluster r
      ((ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j)) 0 :=
    hasWidth_zero_of_mem_except
      (seedMutation_extCluster_castLE_self_mem_laurentSubringExcept hmn S hrj' hrj)
      (hS.seedMutation_extCluster_ne_zero hmn j _)
  rintro ⟨g, hg⟩
  have hg' : _ = _ * (g : F) := congrArg Subtype.val hg
  dsimp only at hg'
  have hk0 := hx ▸ (hasWidth_one_mul_add A.2 B.2 (fun h => hA (Subtype.ext h))
    (fun h => hB.ne_zero (Subtype.ext h))).ne_zero hy
  exact (hS.prime_seedMutation_extCluster_castLE_self hmn j hqj).not_unit
    (isUnit_of_hasWidth_zero_of_mul_eq hy hB hw g.2
      (fun h => hk0 (by rw [hg', h, mul_zero])) (hg'.symm.trans hx))

/-- **Case two: `x'ⱼ` and `x'ₖ` are coprime.** Let `S` be a labeled seed over a field of
characteristic zero, `j ≠ k` directions with `bⱼₖ < 0`, and `q, r` rows such that row `q` is
the unit row with `1` in column `j` and row `r` the unit row with `1` in column `k`. Then every
common divisor in `ℤ[x̃^{±1}]` of the entry `x'ⱼ` of `μⱼ(S)` and the entry `x'ₖ` of
`μₖ(μⱼ(S))` is a unit. -/
@[cluster_algebras "lem_case_two_coprime_k"]
theorem IsLabeledSeed.isRelPrime_seedMutation_seedMutation_extCluster_castLE
    [CharZero K] (hS : IsLabeledSeed K hmn S) {j k : Fin n} (hjk : j ≠ k)
    (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) {q r : Fin m}
    (hqrow : ∀ l, S.extExchangeMatrix q l = if l = j then 1 else 0)
    (hrrow : ∀ l, S.extExchangeMatrix r l = if l = k then 1 else 0) :
    IsRelPrime
      (⟨_, hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j
        ((hqrow j).trans (if_pos rfl))⟩ : laurentSubring S.extCluster)
      ⟨_, hS.seedMutation_seedMutation_extCluster_castLE_mem_laurentSubring hmn hjk
        ((hqrow j).trans (if_pos rfl))⟩ := by
  have hqj : S.extExchangeMatrix q j = 1 := (hqrow j).trans (if_pos rfl)
  exact (hS.prime_seedMutation_extCluster_castLE_self hmn j hqj).irreducible
    |>.isRelPrime_iff_not_dvd.2
    (hS.not_dvd_seedMutation_seedMutation_extCluster_castLE hmn hjk hb hqj
      ((hrrow j).trans (if_neg hjk)) ((hrrow k).trans (if_pos rfl)))

end ClusterAlgebras
