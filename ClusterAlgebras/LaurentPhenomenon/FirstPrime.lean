/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Seed
public import ClusterAlgebras.Laurent.Width
public import ClusterAlgebras.Laurent.UFD
public import ClusterAlgebras.LaurentPhenomenon.ThreeMutations

/-!
# The first new variable is prime when a frozen row isolates its direction

Let `(x̃, B̃)` be a labeled seed with `B̃ = (bᵢₗ)`, let `j` be a direction and `q` a row with
`b_qj = 1`, and let `x'ⱼ` be the entry in position `j` of the extended cluster of
`μⱼ(x̃, B̃)`. Since `b_qj > 0`, the variable `x_q` occurs in `M⁺ⱼ` with exponent `1` and not in
`M⁻ⱼ`; writing `M⁺ⱼ = x_q M̂` gives `x'ⱼ = (xⱼ⁻¹ M̂) x_q + xⱼ⁻¹ M⁻ⱼ`, and both coefficients are
Laurent monomials in the `xᵢ` with `i ≠ q`, hence units of `ℤ[x̃_q̂^{±1}]`. So `x'ⱼ` lies in
`ℤ[x̃^{±1}]` and has `q`-width `1`, and in characteristic zero it is irreducible, hence prime,
because `ℤ[x̃^{±1}]` is a unique factorization domain.

## Main results

* `ClusterAlgebras.IsLabeledSeed.seedMutation_extCluster_castLE_self_mem_laurentSubring`:
  `x'ⱼ ∈ ℤ[x̃^{±1}]`.
* `ClusterAlgebras.IsLabeledSeed.hasWidth_seedMutation_extCluster_castLE_self`: `x'ⱼ` has
  `q`-width `1`.
* `ClusterAlgebras.IsLabeledSeed.prime_seedMutation_extCluster_castLE_self`: `x'ⱼ` is a prime
  element of `ℤ[x̃^{±1}]`.

Along the way:

* `ClusterAlgebras.exists_seedMutation_extCluster_castLE_self_eq_mul_add`: the linear form
  `x'ⱼ = A x_q + B` with `A, B` units of `ℤ[x̃_q̂^{±1}]`, for any seed with nonzero entries and
  `q` distinct from the position of `j`.
* `ClusterAlgebras.seedMutation_extCluster_castLE_self_mem_laurentSubringExcept`: when
  `b_qj = 0`, the variable `x'ⱼ` lies in `ℤ[x̃_q̂^{±1}]`.
* `ClusterAlgebras.IsLabeledSeed.algebraicIndependent_rat`: the extended cluster of a labeled
  seed in a field of characteristic zero is algebraically independent over `ℚ`.

## Implementation notes

FWZ take `q` to be a frozen index, `q ∈ [n + 1, m]`, and use this only to know that
`q` is not the position of `j`. For a labeled seed that already follows from `b_qj = 1`, since
the diagonal entry `bⱼⱼ` vanishes, so the results here are stated for every row `q`. FWZ
take the ground field of characteristic zero throughout; the membership and the width
do not use it, and only primality assumes it; the field of the seed then has characteristic
zero too, being an algebra over the ground field (`Algebra.charZero_of_charZero`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F]

section Except

variable {ι : Type*} (y : ι → F) {q i : ι}

/-- An entry of the tuple other than the one in position `q` lies in `ℤ[ỹ_q̂^{±1}]`. -/
theorem mem_laurentSubringExcept (h : i ≠ q) : y i ∈ laurentSubringExcept y q :=
  mem_laurentSubring (fun i : {i // i ≠ q} => y i) ⟨i, h⟩

/-- The inverse of an entry of the tuple other than the one in position `q` lies in
`ℤ[ỹ_q̂^{±1}]`. -/
theorem inv_mem_laurentSubringExcept (h : i ≠ q) : (y i)⁻¹ ∈ laurentSubringExcept y q :=
  inv_mem_laurentSubring (fun i : {i // i ≠ q} => y i) ⟨i, h⟩

variable {y}

/-- A product of natural powers of entries of the tuple lies in `ℤ[ỹ_q̂^{±1}]` when the entry
in position `q` occurs with exponent `0`. -/
theorem prod_pow_mem_laurentSubringExcept {s : Finset ι} {e : ι → ℕ}
    (he : ∀ i ∈ s, e i ≠ 0 → i ≠ q) : ∏ i ∈ s, y i ^ e i ∈ laurentSubringExcept y q :=
  prod_mem fun i hi => by
    by_cases h0 : e i = 0
    · simp [h0]
    · exact pow_mem (mem_laurentSubringExcept y (he i hi h0)) _

/-- The inverse of a product of natural powers of entries of the tuple lies in
`ℤ[ỹ_q̂^{±1}]` when the entry in position `q` occurs with exponent `0`. -/
theorem inv_prod_pow_mem_laurentSubringExcept {s : Finset ι} {e : ι → ℕ}
    (he : ∀ i ∈ s, e i ≠ 0 → i ≠ q) : (∏ i ∈ s, y i ^ e i)⁻¹ ∈ laurentSubringExcept y q := by
  rw [← Finset.prod_inv_distrib]
  refine prod_mem fun i hi => ?_
  by_cases h0 : e i = 0
  · simp [h0]
  · rw [← inv_pow]
    exact pow_mem (inv_mem_laurentSubringExcept y (he i hi h0)) _

end Except

variable {K : Type*} [Field K] [Algebra K F] {m n : ℕ}

section LabeledSeed

variable (hmn : n ≤ m) {S : SeedData F m n}

/-- The extended cluster of a labeled seed in a field of characteristic zero is algebraically
independent over `ℚ`. -/
theorem IsLabeledSeed.algebraicIndependent_rat [CharZero F] (hS : IsLabeledSeed K hmn S) :
    AlgebraicIndependent ℚ S.extCluster :=
  haveI : CharZero K := (algebraMap K F).charZero
  hS.1.1.restrictScalars (algebraMap ℚ K).injective

/-- A row `q` of a labeled seed whose entry in column `j` is nonzero is not the position of
`j`, because the diagonal entry `bⱼⱼ` vanishes. -/
theorem IsLabeledSeed.ne_castLE_of_extExchangeMatrix_ne_zero (hS : IsLabeledSeed K hmn S)
    {j : Fin n} {q : Fin m} (hqj : S.extExchangeMatrix q j ≠ 0) : q ≠ Fin.castLE hmn j :=
  fun h => hqj (h ▸ hS.extExchangeMatrix_castLE_self hmn j)

/-- Every entry of the extended cluster of a mutation of a labeled seed is nonzero. -/
theorem IsLabeledSeed.seedMutation_extCluster_ne_zero [CharZero K] (hS : IsLabeledSeed K hmn S)
    (j : Fin n) (i : Fin m) : (ClusterAlgebras.seedMutation hmn S j).extCluster i ≠ 0 := by
  rcases eq_or_ne i (Fin.castLE hmn j) with rfl | hi
  · rw [seedMutation_extCluster_castLE_self]
    exact div_ne_zero (hS.exchangeMonomialPos_add_exchangeMonomialNeg_ne_zero hmn j)
      (hS.1.1.ne_zero _)
  · rw [seedMutation_extCluster_of_ne hmn S hi]
    exact hS.1.1.ne_zero i

end LabeledSeed

section LinearForm

variable (hmn : n ≤ m) {S : SeedData F m n} {j : Fin n} {q : Fin m}

/-- **The linear form of the first new variable.** For a seed with nonzero entries, a
direction `j` and a row `q` other than the position of `j` with `b_qj = 1`, the entry `x'ⱼ` of
`μⱼ(S)` is `A x_q + B` for units `A = xⱼ⁻¹ M̂` and `B = xⱼ⁻¹ M⁻ⱼ` of `ℤ[x̃_q̂^{±1}]`, where
`M⁺ⱼ = x_q M̂`. -/
theorem exists_seedMutation_extCluster_castLE_self_eq_mul_add (hx : ∀ i, S.extCluster i ≠ 0)
    (hq : q ≠ Fin.castLE hmn j) (hqj : S.extExchangeMatrix q j = 1) :
    ∃ A B : laurentSubringExcept S.extCluster q, IsUnit A ∧ IsUnit B ∧
      (seedMutation hmn S j).extCluster (Fin.castLE hmn j) = A * S.extCluster q + B := by
  classical
  set x := S.extCluster
  set c := Fin.castLE hmn j
  set P := ∏ i ∈ Finset.univ.erase q, x i ^ (S.extExchangeMatrix i j).toNat
  set N := ∏ i, x i ^ (-S.extExchangeMatrix i j).toNat
  have hP : ∀ i ∈ Finset.univ.erase q, (S.extExchangeMatrix i j).toNat ≠ 0 → i ≠ q :=
    fun i hi _ => Finset.ne_of_mem_erase hi
  have hN : ∀ i ∈ Finset.univ, (-S.extExchangeMatrix i j).toNat ≠ 0 → i ≠ q :=
    fun i _ h hiq => h (by rw [hiq, hqj]; rfl)
  have hc : c ≠ q := Ne.symm hq
  have hunit : ∀ {a : F} (ha : a ∈ laurentSubringExcept x q), a⁻¹ ∈ laurentSubringExcept x q →
      a ≠ 0 → IsUnit (⟨a, ha⟩ : laurentSubringExcept x q) := fun _ hia h0 =>
    (Submonoid.isUnit_iff_of_ne_zero h0).2 hia
  have hA : (x c)⁻¹ * P ∈ laurentSubringExcept x q :=
    mul_mem (inv_mem_laurentSubringExcept x hc) (prod_pow_mem_laurentSubringExcept hP)
  have hB : (x c)⁻¹ * N ∈ laurentSubringExcept x q :=
    mul_mem (inv_mem_laurentSubringExcept x hc) (prod_pow_mem_laurentSubringExcept hN)
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hx i)
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hx i)
  refine ⟨⟨_, hA⟩, ⟨_, hB⟩, hunit hA ?_ (mul_ne_zero (inv_ne_zero (hx c)) hP0),
    hunit hB ?_ (mul_ne_zero (inv_ne_zero (hx c)) hN0), ?_⟩
  · rw [mul_inv, inv_inv]
    exact mul_mem (mem_laurentSubringExcept x hc) (inv_prod_pow_mem_laurentSubringExcept hP)
  · rw [mul_inv, inv_inv]
    exact mul_mem (mem_laurentSubringExcept x hc) (inv_prod_pow_mem_laurentSubringExcept hN)
  · have hpos : exchangeMonomialPos x S.extExchangeMatrix j = x q * P := by
      rw [exchangeMonomialPos_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ q), hqj]
      simp [P]
    rw [seedMutation_extCluster_castLE_self, hpos, exchangeMonomialNeg_eq_prod, div_eq_inv_mul]
    ring

/-- **When `b_qj = 0`, the first new variable avoids `x_q`.** For a direction `j` and a row
`q` other than the position of `j` with `b_qj = 0`, the entry `x'ⱼ` of `μⱼ(S)` lies in
`ℤ[x̃_q̂^{±1}]`: neither exchange monomial involves `x_q`. -/
theorem seedMutation_extCluster_castLE_self_mem_laurentSubringExcept (S : SeedData F m n)
    (hq : q ≠ Fin.castLE hmn j) (hqj : S.extExchangeMatrix q j = 0) :
    (seedMutation hmn S j).extCluster (Fin.castLE hmn j) ∈
      laurentSubringExcept S.extCluster q := by
  have hmem : ∀ i, S.extExchangeMatrix i j ≠ 0 → S.extCluster i ∈
      laurentSubringExcept S.extCluster q := fun i hi =>
    mem_laurentSubringExcept _ fun h => hi (h ▸ hqj)
  rw [seedMutation_extCluster_castLE_self, div_eq_mul_inv]
  exact mul_mem (add_mem (exchangeMonomialPos_mem_of_mem _ hmem)
    (exchangeMonomialNeg_mem_of_mem _ hmem)) (inv_mem_laurentSubringExcept _ (Ne.symm hq))

/-- The linear form of the first new variable of a labeled seed: for a row `q` with
`b_qj = 1`, the entry `x'ⱼ` of `μⱼ(S)` is `A x_q + B` for units `A, B` of `ℤ[x̃_q̂^{±1}]`. -/
theorem IsLabeledSeed.exists_seedMutation_extCluster_castLE_self_eq_mul_add
    (hS : IsLabeledSeed K hmn S) (hqj : S.extExchangeMatrix q j = 1) :
    ∃ A B : laurentSubringExcept S.extCluster q, IsUnit A ∧ IsUnit B ∧
      (ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j) =
        A * S.extCluster q + B :=
  ClusterAlgebras.exists_seedMutation_extCluster_castLE_self_eq_mul_add hmn hS.1.1.ne_zero
    (hS.ne_castLE_of_extExchangeMatrix_ne_zero hmn (by rw [hqj]; exact one_ne_zero)) hqj

end LinearForm

section FirstPrime

variable (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) (j : Fin n)
  {q : Fin m} (hqj : S.extExchangeMatrix q j = 1)

include hS hqj

/-- **The first new variable is Laurent.** For a labeled seed `S`, a direction `j` and a row
`q` with `b_qj = 1`, the entry `x'ⱼ` of `μⱼ(S)` lies in `ℤ[x̃^{±1}]`. -/
@[cluster_algebras "lem_first_new_variable_prime"]
theorem IsLabeledSeed.seedMutation_extCluster_castLE_self_mem_laurentSubring :
    (ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j) ∈
      laurentSubring S.extCluster := by
  obtain ⟨A, B, -, -, h⟩ := hS.exists_seedMutation_extCluster_castLE_self_eq_mul_add hmn hqj
  exact h ▸ mul_add_mem_laurentSubring A B

/-- **The first new variable has width one.** For a labeled seed `S`, a direction `j` and a
row `q` with `b_qj = 1`, the entry `x'ⱼ` of `μⱼ(S)` has `q`-width `1`. -/
@[cluster_algebras "lem_first_new_variable_prime"]
theorem IsLabeledSeed.hasWidth_seedMutation_extCluster_castLE_self :
    HasWidth S.extCluster q
      ((ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j)) 1 := by
  obtain ⟨A, B, hA, hB, h⟩ := hS.exists_seedMutation_extCluster_castLE_self_eq_mul_add hmn hqj
  rw [h]
  exact hasWidth_one_mul_add A.2 B.2 (fun h => hA.ne_zero (Subtype.ext h))
    (fun h => hB.ne_zero (Subtype.ext h))

/-- **The first new variable is prime.** For a labeled seed `S` over a field of
characteristic zero, a direction `j` and a row `q` with `b_qj = 1`, the entry `x'ⱼ` of `μⱼ(S)`
is a prime element of `ℤ[x̃^{±1}]`. -/
@[cluster_algebras "lem_first_new_variable_prime"]
theorem IsLabeledSeed.prime_seedMutation_extCluster_castLE_self [CharZero K] :
    Prime (⟨_, hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j hqj⟩ :
      laurentSubring S.extCluster) := by
  haveI := Algebra.charZero_of_charZero K F
  obtain ⟨A, B, hA, hB, h⟩ := hS.exists_seedMutation_extCluster_castLE_self_eq_mul_add hmn hqj
  have hirr := irreducible_mul_add (hS.algebraicIndependent_rat hmn) hA.ne_zero hB
  have he : (⟨_, hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j hqj⟩ :
      laurentSubring S.extCluster) = ⟨A * S.extCluster q + B, mul_add_mem_laurentSubring A B⟩ :=
    Subtype.ext h
  rw [he]
  exact prime_of_irreducible_laurentSubring (hS.algebraicIndependent_rat hmn) hirr

end FirstPrime

end ClusterAlgebras
