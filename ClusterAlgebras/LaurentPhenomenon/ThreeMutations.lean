/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Seed
public import ClusterAlgebras.Laurent.Defs

/-!
# Laurentness after one and after three mutations

Two steps of the proof of the Laurent phenomenon.

The first says that one mutation keeps the entries of an extended cluster in `ℤ[ỹ^{±1}]` as
long as the entry that it replaces is a unit there: the new entry is `(M⁺ₗ + M⁻ₗ) wₗ⁻¹`, and
the exchange monomials are products of natural powers of the old entries.

The second concerns a labeled seed `(x̃, B̃)` and two directions `j ≠ k` with `b°ⱼₖ < 0`. It
says that the entry in position `j` of `μⱼ(μₖ(μⱼ(x̃, B̃)))` lies in `L = ℤ[x̃^{±1}]`. Write
`x'ⱼ`, `x'ₖ`, `x''ⱼ` for the new entries produced by the three mutations, `bᵢₗ` for the entries
of the matrix of `μⱼ(x̃, B̃)` and `b'ᵢₗ` for those of `μₖ(μⱼ(x̃, B̃))`, and put
`Pⱼ = ∏ᵢ xᵢ ^ bᵢⱼ + 1`. Then `x'ⱼ = xⱼ⁻¹ M⁻ⱼ Pⱼ`, `x'ₖ ≡ xₖ⁻¹ M⁻ₖ` modulo `Pⱼ L`, and
`x'ⱼ x''ⱼ = M⁻ⱼ N` with `N = (x'ₖ)^{b'ₖⱼ} ∏_{i ≠ k} xᵢ ^ b'ᵢⱼ + 1`, which is congruent to `Pⱼ`,
hence to `0`, modulo `Pⱼ L`; so `x''ⱼ` is a Laurent monomial times the element `N / Pⱼ` of `L`.

## Main results

* `seedMutation_extCluster_mem_laurentSubring`: one mutation at a unit keeps Laurentness.
* `IsLabeledSeed.seedMutation_jkj_extCluster_mem_laurentSubring`: the variable `x''ⱼ` obtained
  by mutating at `j`, `k`, `j` is an integer Laurent polynomial in the initial extended
  cluster.

The intermediate computations of `x'ⱼ`, `x'ₖ` and `N` are stated separately:
`seedMutation_extCluster_castLE_self_eq`, `exists_seedMutation_seedMutation_extCluster_eq`,
`prod_zpow_mutation_eq_prod_zpow`.

## Implementation notes

FWZ's congruences modulo `Pⱼ` are replaced by explicit identities in `F`: a congruence
`u ≡ v` is witnessed by an element `A ∈ L` with `u = v + Pⱼ A`, and the relation `u ∼ v` by an
explicit Laurent monomial. FWZ take the tuple `ỹ` of the first result to have nonzero
entries; the proof does not use that, so it is not assumed, and `ỹ` is indexed by an arbitrary
type.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {m n : ℕ}

section ExchangeMonomial

variable {x x' : Fin m → F} {B : Matrix (Fin m) (Fin n) ℤ} {k : Fin n}

/-- The positive exchange monomial lies in every subring containing the entries of the tuple
in the rows where column `k` is nonzero. -/
theorem exchangeMonomialPos_mem_of_mem (L : Subring F) (h : ∀ i, B i k ≠ 0 → x i ∈ L) :
    exchangeMonomialPos x B k ∈ L := by
  rw [exchangeMonomialPos_eq_prod]
  refine prod_mem fun i _ => ?_
  by_cases hi : B i k = 0
  · simp [hi]
  · exact pow_mem (h i hi) _

/-- The negative exchange monomial lies in every subring containing the entries of the tuple
in the rows where column `k` is nonzero. -/
theorem exchangeMonomialNeg_mem_of_mem (L : Subring F) (h : ∀ i, B i k ≠ 0 → x i ∈ L) :
    exchangeMonomialNeg x B k ∈ L := by
  rw [exchangeMonomialNeg_eq_prod]
  refine prod_mem fun i _ => ?_
  by_cases hi : B i k = 0
  · simp [hi]
  · exact pow_mem (h i hi) _

/-- The positive exchange monomial only reads the entries of the tuple in the rows where
column `k` is positive. -/
theorem exchangeMonomialPos_congr_of_pos (h : ∀ i, 0 < B i k → x' i = x i) :
    exchangeMonomialPos x' B k = exchangeMonomialPos x B k :=
  Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_filter.1 hi).2]

/-- The negative exchange monomial only reads the entries of the tuple in the rows where
column `k` is negative. -/
theorem exchangeMonomialNeg_congr_of_neg (h : ∀ i, B i k < 0 → x' i = x i) :
    exchangeMonomialNeg x' B k = exchangeMonomialNeg x B k :=
  Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_filter.1 hi).2]

/-- For a tuple of nonzero elements, `M⁺ₖ = M⁻ₖ ∏ᵢ xᵢ ^ bᵢₖ`. -/
theorem exchangeMonomialPos_eq_exchangeMonomialNeg_mul (hx : ∀ i, x i ≠ 0) :
    exchangeMonomialPos x B k = exchangeMonomialNeg x B k * ∏ i, x i ^ B i k := by
  rw [exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hx i)]
  congr 1
  omega

/-- For a tuple of nonzero elements, the exchange binomial factors as
`M⁺ₖ + M⁻ₖ = M⁻ₖ (∏ᵢ xᵢ ^ bᵢₖ + 1)`. -/
theorem exchangeMonomialPos_add_exchangeMonomialNeg_eq_mul (hx : ∀ i, x i ≠ 0) :
    exchangeMonomialPos x B k + exchangeMonomialNeg x B k =
      exchangeMonomialNeg x B k * (∏ i, x i ^ B i k + 1) := by
  rw [exchangeMonomialPos_eq_exchangeMonomialNeg_mul hx, mul_add, mul_one]

/-- Mutating the matrix in direction `k` swaps the two exchange monomials in direction `k`:
the positive one becomes the negative one. -/
theorem exchangeMonomialPos_matrixMutation_self (hmn : n ≤ m) :
    exchangeMonomialPos x (matrixMutation hmn B k) k = exchangeMonomialNeg x B k := by
  rw [exchangeMonomialPos_congr (x := x) (B := -B) (fun _ _ => rfl)
    (fun i => by rw [matrixMutation_apply_col, Matrix.neg_apply]), exchangeMonomialPos_neg]

/-- Mutating the matrix in direction `k` swaps the two exchange monomials in direction `k`:
the negative one becomes the positive one. -/
theorem exchangeMonomialNeg_matrixMutation_self (hmn : n ≤ m) :
    exchangeMonomialNeg x (matrixMutation hmn B k) k = exchangeMonomialPos x B k := by
  rw [exchangeMonomialNeg_congr (x := x) (B := -B) (fun _ _ => rfl)
    (fun i => by rw [matrixMutation_apply_col, Matrix.neg_apply]), exchangeMonomialNeg_neg]

/-- If `bₐₖ > 0` and the entries of the tuple lie in a subring `L`, then `M⁺ₖ` is `xₐ` times
an element of `L`. -/
theorem exists_exchangeMonomialPos_eq_mul (L : Subring F) (hx : ∀ i, x i ∈ L) {a : Fin m}
    (ha : 0 < B a k) : ∃ G ∈ L, exchangeMonomialPos x B k = x a * G := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, (B a k).toNat = t + 1 := ⟨(B a k).toNat - 1, by omega⟩
  refine ⟨x a ^ t * ∏ i ∈ Finset.univ.erase a, x i ^ (B i k).toNat,
    mul_mem (pow_mem (hx a) _) (prod_mem fun i _ => pow_mem (hx i) _), ?_⟩
  rw [exchangeMonomialPos_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ht,
    pow_succ']
  ring

/-- The negative exchange monomial of a tuple is an integer Laurent polynomial in it. -/
theorem exchangeMonomialNeg_mem_laurentSubring :
    exchangeMonomialNeg x B k ∈ laurentSubring x :=
  exchangeMonomialNeg_mem_of_mem _ fun i _ => mem_laurentSubring x i

/-- The inverse of the negative exchange monomial of a tuple is an integer Laurent polynomial
in it. -/
theorem inv_exchangeMonomialNeg_mem_laurentSubring :
    (exchangeMonomialNeg x B k)⁻¹ ∈ laurentSubring x := by
  rw [exchangeMonomialNeg_eq_prod, ← Finset.prod_inv_distrib]
  exact prod_mem fun i _ => by rw [← inv_pow]; exact pow_mem (inv_mem_laurentSubring x i) _

end ExchangeMonomial

section SeedMutation

variable (hmn : n ≤ m) (S : SeedData F m n)

/-- The entry of `μₗ(S)` in position `l` is `(M⁺ₗ + M⁻ₗ) / xₗ`. -/
theorem seedMutation_extCluster_castLE_self (l : Fin n) :
    (seedMutation hmn S l).extCluster (Fin.castLE hmn l) =
      (exchangeMonomialPos S.extCluster S.extExchangeMatrix l +
          exchangeMonomialNeg S.extCluster S.extExchangeMatrix l) /
        S.extCluster (Fin.castLE hmn l) :=
  Function.update_self _ _ _

/-- The entries of `μₗ(S)` outside position `l` are those of `S`. -/
theorem seedMutation_extCluster_of_ne {l : Fin n} {i : Fin m} (h : i ≠ Fin.castLE hmn l) :
    (seedMutation hmn S l).extCluster i = S.extCluster i :=
  Function.update_of_ne h _ _

/-- The extended exchange matrix of `μₗ(S)` is the mutation of that of `S` in direction
`l`. -/
theorem seedMutation_extExchangeMatrix (l : Fin n) :
    (seedMutation hmn S l).extExchangeMatrix = matrixMutation hmn S.extExchangeMatrix l :=
  rfl

end SeedMutation

/-- **One mutation keeps Laurentness when the old entry is a unit.** If every entry of the
extended cluster of `S` lies in `ℤ[ỹ^{±1}]` and the entry in position `l` is a unit of that
ring, then every entry of the extended cluster of `μₗ(S)` lies in `ℤ[ỹ^{±1}]`. FWZ
take `ỹ` to be an `m`-tuple of nonzero elements; neither condition is used. -/
@[cluster_algebras "lem_laurent_one_step"]
theorem seedMutation_extCluster_mem_laurentSubring {ι : Type*} (y : ι → F) (hmn : n ≤ m)
    {S : SeedData F m n} (hS : ∀ i, S.extCluster i ∈ laurentSubring y) (l : Fin n)
    (hl : IsUnit (⟨S.extCluster (Fin.castLE hmn l), hS _⟩ : laurentSubring y)) (i : Fin m) :
    (seedMutation hmn S l).extCluster i ∈ laurentSubring y := by
  obtain ⟨u, hu⟩ := hl
  rcases eq_or_ne i (Fin.castLE hmn l) with rfl | hi
  · have hu' : ((u : laurentSubring y) : F) = S.extCluster (Fin.castLE hmn l) :=
      congrArg Subtype.val hu
    have hinv : (S.extCluster (Fin.castLE hmn l))⁻¹ = ((u⁻¹ : (laurentSubring y)ˣ) : F) :=
      inv_eq_of_mul_eq_one_right <| by
        rw [← hu']
        exact congrArg Subtype.val u.mul_inv
    rw [seedMutation_extCluster_castLE_self, div_eq_mul_inv, hinv]
    exact mul_mem (add_mem (exchangeMonomialPos_mem_of_mem _ fun i _ => hS i)
      (exchangeMonomialNeg_mem_of_mem _ fun i _ => hS i)) (u⁻¹ : (laurentSubring y)ˣ).1.2
  · rw [seedMutation_extCluster_of_ne hmn S hi]
    exact hS i

section ThreeMutations

/-- **The first new variable.** For a seed with nonzero entries, the entry `x'ₗ` of `μₗ(S)`
satisfies `x'ₗ = xₗ⁻¹ M⁻ₗ(x̃, B̃₁) (∏ᵢ xᵢ ^ bᵢₗ + 1)`, where `B̃₁ = (bᵢₗ)` is the matrix of
`μₗ(S)`. -/
theorem seedMutation_extCluster_castLE_self_eq (hmn : n ≤ m) {S : SeedData F m n}
    (hx : ∀ i, S.extCluster i ≠ 0) (l : Fin n) :
    (seedMutation hmn S l).extCluster (Fin.castLE hmn l) =
      (S.extCluster (Fin.castLE hmn l))⁻¹ *
        exchangeMonomialNeg S.extCluster (seedMutation hmn S l).extExchangeMatrix l *
        (∏ i, S.extCluster i ^ (seedMutation hmn S l).extExchangeMatrix i l + 1) := by
  rw [seedMutation_extCluster_castLE_self, seedMutation_extExchangeMatrix,
    ← exchangeMonomialPos_matrixMutation_self hmn (B := S.extExchangeMatrix),
    ← exchangeMonomialNeg_matrixMutation_self hmn (B := S.extExchangeMatrix), add_comm,
    exchangeMonomialPos_add_exchangeMonomialNeg_eq_mul hx, div_eq_inv_mul, mul_assoc]

/-- **The second new variable.** For a seed with nonzero entries and `j ≠ k` with
`b°ⱼₖ < 0`, the entry `x'ₖ` of `μₖ(μⱼ(S))` is congruent to `xₖ⁻¹ M⁻ₖ(x̃, B̃₁)` modulo
`Pⱼ = ∏ᵢ xᵢ ^ bᵢⱼ + 1` in `ℤ[x̃^{±1}]`, where `B̃₁ = (bᵢₗ)` is the matrix of `μⱼ(S)`. -/
theorem exists_seedMutation_seedMutation_extCluster_eq (hmn : n ≤ m) {S : SeedData F m n}
    (hx : ∀ i, S.extCluster i ≠ 0) {j k : Fin n} (hjk : j ≠ k)
    (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) :
    ∃ A ∈ laurentSubring S.extCluster,
      (seedMutation hmn (seedMutation hmn S j) k).extCluster (Fin.castLE hmn k) =
        (S.extCluster (Fin.castLE hmn k))⁻¹ *
            exchangeMonomialNeg S.extCluster (seedMutation hmn S j).extExchangeMatrix k +
          (∏ i, S.extCluster i ^ (seedMutation hmn S j).extExchangeMatrix i j + 1) * A := by
  set x := S.extCluster
  set S₁ := seedMutation hmn S j
  set L := laurentSubring x
  have hc : Fin.castLE hmn j ≠ Fin.castLE hmn k := fun h => hjk (by simpa [Fin.ext_iff] using h)
  have hx₁ : ∀ i, i ≠ Fin.castLE hmn j → S₁.extCluster i = x i := fun i hi =>
    seedMutation_extCluster_of_ne hmn S hi
  have hxj := seedMutation_extCluster_castLE_self_eq hmn hx j
  have hx₁L : ∀ i, S₁.extCluster i ∈ L := fun i => by
    rcases eq_or_ne i (Fin.castLE hmn j) with rfl | hi
    · rw [hxj]
      exact mul_mem (mul_mem (inv_mem_laurentSubring x _) exchangeMonomialNeg_mem_laurentSubring)
        (add_mem (prod_mem fun i _ => zpow_mem_laurentSubring x i _) (one_mem _))
    · rw [hx₁ i hi]
      exact mem_laurentSubring x i
  have hpos : 0 < S₁.extExchangeMatrix (Fin.castLE hmn j) k := by
    change 0 < matrixMutation hmn S.extExchangeMatrix j (Fin.castLE hmn j) k
    rw [matrixMutation_apply_row]
    exact neg_pos.2 hb
  obtain ⟨G, hG, hMG⟩ := exists_exchangeMonomialPos_eq_mul L hx₁L hpos
  refine ⟨(x (Fin.castLE hmn k))⁻¹ *
      ((x (Fin.castLE hmn j))⁻¹ * exchangeMonomialNeg x S₁.extExchangeMatrix j) * G,
    mul_mem (mul_mem (inv_mem_laurentSubring x _)
      (mul_mem (inv_mem_laurentSubring x _) exchangeMonomialNeg_mem_laurentSubring)) hG, ?_⟩
  rw [seedMutation_extCluster_castLE_self, hx₁ _ hc.symm, hMG,
    exchangeMonomialNeg_congr_of_neg fun i hi => hx₁ i fun h => by
      rw [h] at hi
      exact hi.not_gt hpos,
    hxj]
  ring

/-- **The key identity for the third new variable.** Let `C = (cᵢₗ)` be an integer matrix with
`cₖⱼ < 0` and `cₖₖ = 0`, `j ≠ k`, and let `C' = (c'ᵢₗ)` be its mutation in direction `k`. Then
`(xₖ⁻¹ M⁻ₖ(x̃, C)) ^ (-cₖⱼ) ∏_{i ≠ k} xᵢ ^ c'ᵢⱼ = ∏ᵢ xᵢ ^ cᵢⱼ` for every tuple of nonzero
elements `x̃`. -/
theorem prod_zpow_mutation_eq_prod_zpow (hmn : n ≤ m) {x : Fin m → F} (hx : ∀ i, x i ≠ 0)
    {C : Matrix (Fin m) (Fin n) ℤ} {j k : Fin n} (hjk : j ≠ k)
    (hkj : C (Fin.castLE hmn k) j < 0) (hkk : C (Fin.castLE hmn k) k = 0) :
    ((x (Fin.castLE hmn k))⁻¹ * exchangeMonomialNeg x C k) ^ (-C (Fin.castLE hmn k) j).toNat *
        ∏ i ∈ Finset.univ.erase (Fin.castLE hmn k), x i ^ matrixMutation hmn C k i j =
      ∏ i, x i ^ C i j := by
  classical
  set c := Fin.castLE hmn k
  set e := (-C c j).toNat
  have he : (e : ℤ) = -C c j := Int.toNat_of_nonneg (by omega)
  have hM : exchangeMonomialNeg x C k = ∏ i ∈ Finset.univ.erase c, x i ^ (-C i k).toNat := by
    rw [exchangeMonomialNeg_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c), hkk,
      neg_zero, Int.toNat_zero, pow_zero, one_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), mul_pow, hM, ← Finset.prod_pow,
    mul_assoc, ← Finset.prod_mul_distrib, inv_pow, ← zpow_natCast, he, ← zpow_neg, neg_neg]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ (hx i),
    matrixMutation_apply_of_ne_eq_max hmn C k (Finset.ne_of_mem_erase hi) hjk,
    max_eq_left hkj.le, max_eq_right (by omega : (0 : ℤ) ≤ -C c j)]
  congr 1
  push_cast
  rw [he]
  rcases lt_or_ge (C i k) 0 with h | h
  · rw [Int.toNat_of_nonneg (by omega : 0 ≤ -C i k), max_eq_left h.le,
      max_eq_right (by omega : (0 : ℤ) ≤ -C i k)]
    ring
  · rw [Int.toNat_eq_zero.2 (by omega : -C i k ≤ 0), max_eq_left (by omega : -C i k ≤ 0)]
    ring

/-- A power of `a + b c` is `aᵉ + b d` for an element `d` of any subring containing `a`, `b`
and `c`. -/
theorem exists_add_mul_pow_eq {R : Type*} [CommRing R] {L : Subring R} {a b c : R} (ha : a ∈ L)
    (hb : b ∈ L) (hc : c ∈ L) (e : ℕ) : ∃ d ∈ L, (a + b * c) ^ e = a ^ e + b * d := by
  induction e with
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | succ e ih =>
    obtain ⟨d, hd, h⟩ := ih
    refine ⟨d * a + a ^ e * c + b * d * c,
      add_mem (add_mem (mul_mem hd ha) (mul_mem (pow_mem ha _) hc))
        (mul_mem (mul_mem hb hd) hc), ?_⟩
    rw [pow_succ, h]
    ring

variable {K : Type*} [Field K] [Algebra K F]

/-- **Three mutations: the variable `x''ⱼ` is Laurent.** Let `(x̃, B̃)` be a labeled seed and
let `j ≠ k` with `b°ⱼₖ < 0`. Then the entry in position `j` of the extended cluster of
`μⱼ(μₖ(μⱼ(x̃, B̃)))` lies in `ℤ[x̃^{±1}]`. -/
@[cluster_algebras "lem_three_mutations"]
theorem IsLabeledSeed.seedMutation_jkj_extCluster_mem_laurentSubring [CharZero K]
    (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) {j k : Fin n}
    (hjk : j ≠ k) (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) :
    (ClusterAlgebras.seedMutation hmn
      (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k) j).extCluster
        (Fin.castLE hmn j) ∈ laurentSubring S.extCluster := by
  classical
  have hS₁ := hS.seedMutation hmn j
  have hS₂ := hS₁.seedMutation hmn k
  set x := S.extCluster
  set S₁ := ClusterAlgebras.seedMutation hmn S j
  set S₂ := ClusterAlgebras.seedMutation hmn S₁ k
  set L := laurentSubring x
  set cj := Fin.castLE hmn j
  set ck := Fin.castLE hmn k
  have hx : ∀ i, x i ≠ 0 := hS.1.1.ne_zero
  have hc : cj ≠ ck := fun h => hjk (by simpa [cj, ck, Fin.ext_iff] using h)
  -- the matrix entries
  have hkj₀ : 0 < S.extExchangeMatrix ck j := ((hS.2.signAntisymmetric hmn).2 k j).2 hb
  have hkj₁ : S₁.extExchangeMatrix ck j < 0 := by
    change matrixMutation hmn S.extExchangeMatrix j ck j < 0
    rw [matrixMutation_apply_col]
    exact neg_neg_of_pos hkj₀
  have hkj₂ : S₂.extExchangeMatrix ck j = -S₁.extExchangeMatrix ck j :=
    matrixMutation_apply_row hmn _ k j
  have hjj₂ : S₂.extExchangeMatrix cj j = 0 := hS₂.extExchangeMatrix_castLE_self hmn j
  have hkk₁ : S₁.extExchangeMatrix ck k = 0 := hS₁.extExchangeMatrix_castLE_self hmn k
  -- the entries of the extended clusters
  have hx₁ : ∀ i, i ≠ cj → S₁.extCluster i = x i := fun i hi =>
    seedMutation_extCluster_of_ne hmn S hi
  have hx₂ : ∀ i, i ≠ ck → S₂.extCluster i = S₁.extCluster i := fun i hi =>
    seedMutation_extCluster_of_ne hmn S₁ hi
  -- the variable `x'ⱼ`
  set P := ∏ i, x i ^ S₁.extExchangeMatrix i j + 1
  set m₁ := (x cj)⁻¹ * exchangeMonomialNeg x S₁.extExchangeMatrix j
  have hxj : S₁.extCluster cj = m₁ * P := seedMutation_extCluster_castLE_self_eq hmn hx j
  have hxj₀ : m₁ * P ≠ 0 := hxj ▸ hS₁.1.1.ne_zero cj
  have hm₁ : m₁⁻¹ ∈ L := by
    rw [mul_inv, inv_inv]
    exact mul_mem (mem_laurentSubring x cj) inv_exchangeMonomialNeg_mem_laurentSubring
  -- the variable `x'ₖ`
  set m₂ := (x ck)⁻¹ * exchangeMonomialNeg x S₁.extExchangeMatrix k
  obtain ⟨A, hA, hxk⟩ := exists_seedMutation_seedMutation_extCluster_eq hmn hx hjk hb
  set e := (-S₁.extExchangeMatrix ck j).toNat
  obtain ⟨A', hA', hpow⟩ := exists_add_mul_pow_eq (L := L) (a := m₂) (b := P) (c := A)
    (mul_mem (inv_mem_laurentSubring x _) exchangeMonomialNeg_mem_laurentSubring)
    (add_mem (prod_mem fun i _ => zpow_mem_laurentSubring x i _) (one_mem _)) hA e
  -- the variable `x''ⱼ`
  set R := ∏ i ∈ Finset.univ.erase ck, x i ^ S₂.extExchangeMatrix i j
  have hR : R ∈ L := prod_mem fun i _ => zpow_mem_laurentSubring x i _
  have hkey : m₂ ^ e * R = P - 1 := by
    rw [add_sub_cancel_right]
    exact prod_zpow_mutation_eq_prod_zpow hmn hx hjk hkj₁ hkk₁
  have hT : ∏ i, S₂.extCluster i ^ S₂.extExchangeMatrix i j =
      S₂.extCluster ck ^ S₂.extExchangeMatrix ck j * R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ck)]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have hik := Finset.ne_of_mem_erase hi
    rcases eq_or_ne i cj with rfl | hij
    · rw [hjj₂, zpow_zero, zpow_zero]
    · rw [hx₂ i hik, hx₁ i hij]
  have hneg : exchangeMonomialNeg S₂.extCluster S₂.extExchangeMatrix j =
      exchangeMonomialNeg x S₂.extExchangeMatrix j :=
    exchangeMonomialNeg_congr_of_neg fun i hi => by
      have hik : i ≠ ck := fun h => by rw [h, hkj₂] at hi; linarith
      have hij : i ≠ cj := fun h => by rw [h, hjj₂] at hi; exact lt_irrefl 0 hi
      rw [hx₂ i hik, hx₁ i hij]
  have hform : (ClusterAlgebras.seedMutation hmn S₂ j).extCluster cj =
      exchangeMonomialNeg x S₂.extExchangeMatrix j * m₁⁻¹ * (1 + A' * R) := by
    rw [seedMutation_extCluster_castLE_self, exchangeMonomialPos_add_exchangeMonomialNeg_eq_mul
      (hS₂.1.1.ne_zero), hneg, hT, hx₂ cj hc, hxj, hkj₂,
      ← Int.toNat_of_nonneg (neg_nonneg.2 hkj₁.le), zpow_natCast, hxk, hpow,
      div_eq_iff hxj₀]
    have hinv : m₁⁻¹ * m₁ = 1 := inv_mul_cancel₀ (left_ne_zero_of_mul hxj₀)
    linear_combination exchangeMonomialNeg x S₂.extExchangeMatrix j * hkey -
      exchangeMonomialNeg x S₂.extExchangeMatrix j * (P + P * A' * R) * hinv
  rw [hform]
  exact mul_mem (mul_mem exchangeMonomialNeg_mem_laurentSubring hm₁)
    (add_mem (one_mem _) (mul_mem hA' hR))

end ThreeMutations

end ClusterAlgebras
