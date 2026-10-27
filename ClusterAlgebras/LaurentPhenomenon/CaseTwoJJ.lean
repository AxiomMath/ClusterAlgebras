/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Laurent.Denominators
public import ClusterAlgebras.LaurentPhenomenon.AugmentedBlock
public import ClusterAlgebras.LaurentPhenomenon.FirstPrime

/-!
# Case two of the Laurent phenomenon: `x'ⱼ` and `x''ⱼ` are coprime

Let `(x̃, B̃)` be a labeled seed with `B̃ = (bᵢₗ)`, let `j ≠ k` be directions with `bⱼₖ < 0`, and
let `q ≠ r` be rows such that row `q` of `B̃` is the unit row with `1` in column `j` and row `r`
is the unit row with `1` in column `k`. Write `x'ⱼ`, `x'ₖ`, `x''ⱼ` for the new variables
produced by mutating at `j`, then `k`, then `j`. Then every common divisor of `x'ⱼ` and `x''ⱼ`
in `L = ℤ[x̃^{±1}]` is a unit.

Write `L_r = ℤ[x̃_r̂^{±1}]` and `L_q = ℤ[x̃_q̂^{±1}]`. Reading column `k` of `μⱼ(B̃)` gives
`x'ₖ = A x_r + B` with `A, B ∈ L_r` and `B` a nonzero element of `L_q`, because `x'ⱼ ∈ L_r`
(as `b_rj = 0`). Reading column `j` of `μₖ(μⱼ(B̃))` gives
`x'ⱼ x''ⱼ = (x'ₖ)ᵉ Ê + x_q F̂` with `Ê, F̂` nonzero elements of `L_r ∩ L_q`. If `x'ⱼ` divided
`x''ⱼ`, then `(x'ⱼ)²` would divide `(A x_r + B)ᵉ Ê + x_q F̂` in `L`, hence would divide its
constant term `Bᵉ Ê + x_q F̂` in `x_r` inside `L_r`. That constant term has `q`-width `1`, while
`x'ⱼ` has `q`-width `1`, so every nonzero multiple of `(x'ⱼ)²` has `q`-width at least `2`. So
`x'ⱼ ∤ x''ⱼ`, and as `x'ⱼ` is irreducible, the two are relatively prime.

## Main results

* `ClusterAlgebras.IsLabeledSeed.not_dvd_seedMutation_jkj_extCluster_castLE_self`:
  `x'ⱼ ∤ x''ⱼ` in `ℤ[x̃^{±1}]`.
* `ClusterAlgebras.IsLabeledSeed.isRelPrime_seedMutation_jkj_extCluster_castLE_self`: every
  common divisor of `x'ⱼ` and `x''ⱼ` in `ℤ[x̃^{±1}]` is a unit.

Along the way:

* `ClusterAlgebras.dvd_coeff_zero_of_aeval_eq_mul`: an element `c` of `ℤ[ỹ_r̂^{±1}]` dividing,
  in `ℤ[ỹ^{±1}]`, a polynomial in `y_r` over `ℤ[ỹ_r̂^{±1}]` divides its constant term.
* `ClusterAlgebras.IsLabeledSeed.exists_seedMutation_seedMutation_extCluster_eq_mul_add`: the
  linear form `x'ₖ = A x_r + B`.
* `ClusterAlgebras.IsLabeledSeed.exists_mul_seedMutation_jkj_extCluster_eq`: the form
  `x'ⱼ x''ⱼ = (x'ₖ)ᵉ Ê + x_q F̂`.

## Implementation notes

FWZ compare `q`-widths inside `L_r`, as the ring of Laurent polynomials in the tuple
`(xᵢ)_{i ≠ r}`. Here the widths are taken in `L` with respect to the full extended cluster:
the constant term `Bᵉ Ê + x_q F̂`, the variable `x'ⱼ` and the cofactor all lie in `L_r ⊆ L`,
and widths in `L` add under multiplication just as well, so the comparison is the same. FWZ
extract the coefficient of `x_r⁰` of `x''ⱼ` and of a cofactor separately; here the
one-variable expansion `L ≃ L_r[x_r^{±1}]` is applied once, to `x'ⱼ x''ⱼ = (x'ⱼ)² g`, and a
Laurent polynomial whose product with a nonzero constant is a polynomial is itself a
polynomial (`ClusterAlgebras.exists_eq_toLaurent_of_eq_mul`).

The hypotheses are sharpened as follows, all implied by FWZ's. Of the two unit rows only
the four entries in columns `j, k` are used. The frozen conditions `q, r ∈ [n + 1, m]` are
used only to know that `q` is not the row indexed by `k`, and that is the hypothesis assumed;
that `q ≠ r`, and that `r` is not the row indexed by `j` or `k`, follow from the entries.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 3.
-/

@[expose] public section

open Polynomial

namespace ClusterAlgebras

variable {F : Type*} [Field F]

section Expansion

variable {ι : Type*} {y : ι → F}

/-- A product of natural powers of the entries of a tuple `y'` lies in `ℤ[ỹ_q̂^{±1}]` when each
factor with a nonzero exponent is an entry `yᵢ` of `ỹ` with `i ≠ q`. -/
theorem prod_pow_mem_laurentSubringExcept_of_eq {y' : ι → F} {s : Finset ι} {e : ι → ℕ}
    {q : ι} (h : ∀ i ∈ s, e i ≠ 0 → y' i = y i ∧ i ≠ q) :
    ∏ i ∈ s, y' i ^ e i ∈ laurentSubringExcept y q :=
  prod_mem fun i hi => by
    by_cases h0 : e i = 0
    · simp [h0]
    · obtain ⟨h₁, h₂⟩ := h i hi h0
      rw [h₁]
      exact pow_mem (mem_laurentSubringExcept y h₂) _

variable [CharZero F] (hy : AlgebraicIndependent ℚ y)

include hy

/-- **Divisibility passes to the constant term in one variable.** Let `P` be a polynomial over
`ℤ[ỹ_r̂^{±1}]` and `c` a nonzero element of `ℤ[ỹ_r̂^{±1}]`. If `P(y_r) = c g` for some
`g ∈ ℤ[ỹ^{±1}]`, then `c` divides the constant term of `P` in `ℤ[ỹ_r̂^{±1}]`. -/
theorem dvd_coeff_zero_of_aeval_eq_mul {r : ι} {P : (laurentSubringExcept y r)[X]}
    {c : laurentSubringExcept y r} (hc : c ≠ 0) {g : F} (hg : g ∈ laurentSubring y)
    (h : aeval (y r) P = c * g) : c ∣ P.coeff 0 := by
  set φ := laurentEquivOfExcept hy r
  obtain ⟨p, -, hp⟩ := exists_eq_toLaurent_of_eq_mul (P := P) (Q := C c)
    (L := φ.symm ⟨g, hg⟩) (by simpa using hc) <| φ.injective <| Subtype.ext <| by
      rw [map_mul, RingEquiv.apply_symm_apply, Subring.coe_mul,
        coe_laurentEquivOfExcept_toLaurent, coe_laurentEquivOfExcept_toLaurent, h, aeval_C]
      rfl
  exact ⟨p.coeff 0, by simpa using hp.symm⟩

/-- If `a ∈ ℤ[ỹ_r̂^{±1}]` has `q`-width `1` and the constant term in `y_r` of a polynomial `P`
over `ℤ[ỹ_r̂^{±1}]` is `v y_q + u` with `u, v` nonzero elements of `ℤ[ỹ_q̂^{±1}]`, then `P(y_r)`
is not a multiple of `a²` in `ℤ[ỹ^{±1}]`. -/
theorem aeval_ne_sq_mul_of_hasWidth_one {q r : ι} {a : laurentSubringExcept y r}
    (ha : HasWidth y q a 1) {P : (laurentSubringExcept y r)[X]} {u v : F}
    (hu : u ∈ laurentSubringExcept y q) (hv : v ∈ laurentSubringExcept y q) (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (hP : (P.coeff 0 : F) = v * y q + u) {g : F} (hg : g ∈ laurentSubring y) :
    aeval (y r) P ≠ (a : F) ^ 2 * g := by
  intro h
  have ha0 : a ≠ 0 := fun h0 => ha.ne_zero hy (by rw [h0, ZeroMemClass.coe_zero])
  obtain ⟨d, hd⟩ := dvd_coeff_zero_of_aeval_eq_mul hy (c := a ^ 2) (pow_ne_zero 2 ha0) hg
    (by rw [h, SubmonoidClass.coe_pow])
  have h1 : HasWidth y q ((a : F) ^ 2 * d) 1 := by
    have := hasWidth_one_mul_add hv hu hv0 hu0
    rwa [← hP, hd, Subring.coe_mul, SubmonoidClass.coe_pow] at this
  have h2 : HasWidth y q ((a : F) ^ 2) 2 := by simpa [sq] using ha.mul (hy.ne_zero q) ha
  exact absurd (h1.le_of_mul hy h2 (laurentSubringExcept_le y r d.2)) (by norm_num)

/-- **The key non-divisibility.** Let `q ≠ r`, let `a ∈ ℤ[ỹ_r̂^{±1}]` have `q`-width `1`, and let
`A, B, E, G ∈ ℤ[ỹ_r̂^{±1}]` be such that `Bᵉ E` and `G` are nonzero elements of
`ℤ[ỹ_q̂^{±1}]`. Then `(A y_r + B)ᵉ E + y_q G` is not a multiple of `a²` in `ℤ[ỹ^{±1}]`. -/
theorem pow_mul_add_mul_ne_sq_mul {q r : ι} (hqr : q ≠ r) {a : F}
    (ha : a ∈ laurentSubringExcept y r) (ha1 : HasWidth y q a 1) {A B E G : F} {e : ℕ}
    (hA : A ∈ laurentSubringExcept y r) (hB : B ∈ laurentSubringExcept y r)
    (hE : E ∈ laurentSubringExcept y r) (hG : G ∈ laurentSubringExcept y r)
    (hBE : B ^ e * E ∈ laurentSubringExcept y q) (hGq : G ∈ laurentSubringExcept y q)
    (hBE0 : B ^ e * E ≠ 0) (hG0 : G ≠ 0) {g : F} (hg : g ∈ laurentSubring y) :
    (A * y r + B) ^ e * E + y q * G ≠ a ^ 2 * g := by
  have hq : y q ∈ laurentSubringExcept y r := mem_laurentSubringExcept y hqr
  let P : (laurentSubringExcept y r)[X] :=
    (C ⟨A, hA⟩ * X + C ⟨B, hB⟩) ^ e * C ⟨E, hE⟩ + C (⟨y q, hq⟩ * ⟨G, hG⟩)
  have hPe : aeval (y r) P = (A * y r + B) ^ e * E + y q * G := by
    simp only [P, map_add, map_mul, map_pow, aeval_C, aeval_X]
    rfl
  have hP0 : (P.coeff 0 : F) = G * y q + B ^ e * E := by
    simp [P, coeff_zero_eq_eval_zero]
    ring
  rw [← hPe]
  exact aeval_ne_sq_mul_of_hasWidth_one hy (a := ⟨a, ha⟩) ha1 hBE hGq hBE0 hG0 hP0 hg

end Expansion

section Seed

variable {K : Type*} [Field K] [Algebra K F] {m n : ℕ} (hmn : n ≤ m) {S : SeedData F m n}
  (hS : IsLabeledSeed K hmn S) {j k : Fin n} {q r : Fin m}
  (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0)
  (hqj : S.extExchangeMatrix q j = 1) (hqk : S.extExchangeMatrix q k = 0)
  (hrj : S.extExchangeMatrix r j = 0) (hrk : S.extExchangeMatrix r k = 1)

include hS hb hqj hqk hrj hrk

/-- **The shape of `x'ₖ`.** Under the unit-row hypotheses, the entry `x'ₖ` of `μₖ(μⱼ(x̃, B̃))`
is `A x_r + B` with `A, B ∈ ℤ[x̃_r̂^{±1}]` and `B` a nonzero element of `ℤ[x̃_q̂^{±1}]`: namely
`A = xₖ⁻¹ ∏_{i ≠ r} (x'ᵢ)^{max(b'ᵢₖ, 0)}` and `B = xₖ⁻¹ M⁻ₖ(x̃, μⱼ(B̃))`. -/
theorem IsLabeledSeed.exists_seedMutation_seedMutation_extCluster_eq_mul_add
    (hq : q ≠ Fin.castLE hmn k) :
    ∃ A B : F, A ∈ laurentSubringExcept S.extCluster r ∧
      B ∈ laurentSubringExcept S.extCluster r ∧ B ∈ laurentSubringExcept S.extCluster q ∧
      B ≠ 0 ∧
      (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k).extCluster
        (Fin.castLE hmn k) = A * S.extCluster r + B := by
  classical
  set x := S.extCluster
  set S₁ := ClusterAlgebras.seedMutation hmn S j
  set cj := Fin.castLE hmn j
  set ck := Fin.castLE hmn k
  have hx : ∀ i, x i ≠ 0 := hS.1.1.ne_zero
  obtain ⟨-, h1qk, -, h1rk⟩ : S₁.extExchangeMatrix q j = -1 ∧ S₁.extExchangeMatrix q k = 0 ∧
      S₁.extExchangeMatrix r j = 0 ∧ S₁.extExchangeMatrix r k = 1 :=
    matrixMutation_apply_unitRows hmn hb.le hqj hqk hrj hrk
  have h1jk : 0 < S₁.extExchangeMatrix cj k := by
    rw [seedMutation_extExchangeMatrix, matrixMutation_apply_row]
    exact neg_pos.2 hb
  have hjk : j ≠ k := by
    rintro rfl
    omega
  have hcjk : ck ≠ cj := fun h => hjk (Fin.castLE_injective hmn h).symm
  have hrcj : r ≠ cj := by
    rintro rfl
    omega
  have hrck : r ≠ ck := by
    rintro rfl
    rw [hS.extExchangeMatrix_castLE_self] at hrk
    exact zero_ne_one hrk
  have hx₁ : ∀ i, i ≠ cj → S₁.extCluster i = x i := fun i hi =>
    seedMutation_extCluster_of_ne hmn S hi
  have hx₁r : ∀ i, i ≠ r → S₁.extCluster i ∈ laurentSubringExcept x r := fun i hi => by
    rcases eq_or_ne i cj with rfl | h
    · exact seedMutation_extCluster_castLE_self_mem_laurentSubringExcept hmn S hrcj hrj
    · rw [hx₁ i h]
      exact mem_laurentSubringExcept x hi
  set G := ∏ i ∈ Finset.univ.erase r, S₁.extCluster i ^ (S₁.extExchangeMatrix i k).toNat
  have hG : G ∈ laurentSubringExcept x r :=
    prod_mem fun i hi => pow_mem (hx₁r i (Finset.ne_of_mem_erase hi)) _
  have hpos : exchangeMonomialPos S₁.extCluster S₁.extExchangeMatrix k = x r * G := by
    rw [exchangeMonomialPos_eq_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ r), h1rk,
      hx₁ r hrcj]
    simp [G]
  set D := ∏ i, x i ^ (-S₁.extExchangeMatrix i k).toNat
  have hneg : exchangeMonomialNeg S₁.extCluster S₁.extExchangeMatrix k = D := by
    rw [exchangeMonomialNeg_congr_of_neg fun i hi => hx₁ i fun h => by
      rw [h] at hi
      exact hi.not_gt h1jk, exchangeMonomialNeg_eq_prod]
  have hD : ∀ p, (∀ i, S₁.extExchangeMatrix i k < 0 → i ≠ p) → D ∈ laurentSubringExcept x p :=
    fun p hp => prod_pow_mem_laurentSubringExcept fun i _ hi => hp i (by omega)
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hx i)
  refine ⟨(x ck)⁻¹ * G, (x ck)⁻¹ * D,
    mul_mem (inv_mem_laurentSubringExcept x hrck.symm) hG,
    mul_mem (inv_mem_laurentSubringExcept x hrck.symm)
      (hD r fun i hi h => by rw [h, h1rk] at hi; norm_num at hi),
    mul_mem (inv_mem_laurentSubringExcept x hq.symm)
      (hD q fun i hi h => by rw [h, h1qk] at hi; exact lt_irrefl 0 hi),
    mul_ne_zero (inv_ne_zero (hx ck)) hD0, ?_⟩
  rw [seedMutation_extCluster_castLE_self, hpos, hneg, hx₁ ck hcjk, div_eq_inv_mul]
  ring

/-- **The shape of `x'ⱼ x''ⱼ`.** Under the unit-row hypotheses, the entries `x'ⱼ` of
`μⱼ(x̃, B̃)`, `x'ₖ` of `μₖ(μⱼ(x̃, B̃))` and `x''ⱼ` of `μⱼ(μₖ(μⱼ(x̃, B̃)))` satisfy
`x'ⱼ x''ⱼ = (x'ₖ)ᵉ E + x_q G` for a natural number `e` and nonzero elements `E, G` of
`ℤ[x̃_r̂^{±1}] ∩ ℤ[x̃_q̂^{±1}]`. -/
theorem IsLabeledSeed.exists_mul_seedMutation_jkj_extCluster_eq [CharZero K]
    (hq : q ≠ Fin.castLE hmn k) :
    ∃ (e : ℕ) (E G : F), E ∈ laurentSubringExcept S.extCluster r ∧
      E ∈ laurentSubringExcept S.extCluster q ∧ E ≠ 0 ∧
      G ∈ laurentSubringExcept S.extCluster r ∧ G ∈ laurentSubringExcept S.extCluster q ∧
      G ≠ 0 ∧
      (ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j) *
          (ClusterAlgebras.seedMutation hmn
            (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k)
              j).extCluster (Fin.castLE hmn j) =
        (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k).extCluster
            (Fin.castLE hmn k) ^ e * E + S.extCluster q * G := by
  classical
  have hS₁ := hS.seedMutation hmn j
  have hS₂ := hS₁.seedMutation hmn k
  set x := S.extCluster
  set S₁ := ClusterAlgebras.seedMutation hmn S j
  set S₂ := ClusterAlgebras.seedMutation hmn S₁ k
  set cj := Fin.castLE hmn j
  set ck := Fin.castLE hmn k
  have hkj₀ : 0 < S.extExchangeMatrix ck j := ((hS.2.signAntisymmetric hmn).2 k j).2 hb
  obtain ⟨h2qj, -, h2rj, -⟩ : S₂.extExchangeMatrix q j = -1 ∧ S₂.extExchangeMatrix q k = 0 ∧
      S₂.extExchangeMatrix r j = 0 ∧ S₂.extExchangeMatrix r k = -1 :=
    matrixMutation_matrixMutation_apply_unitRows hmn hb.le hkj₀.le hq hqj hqk hrj hrk
  have h2kj : 0 ≤ S₂.extExchangeMatrix ck j := by
    rw [seedMutation_extExchangeMatrix, seedMutation_extExchangeMatrix, matrixMutation_apply_row,
      matrixMutation_apply_col, neg_neg]
    exact hkj₀.le
  have h2jj : S₂.extExchangeMatrix cj j = 0 := hS₂.extExchangeMatrix_castLE_self hmn j
  have hjk : j ≠ k := by
    rintro rfl
    omega
  have hcjk : cj ≠ ck := fun h => hjk (Fin.castLE_injective hmn h)
  have hqcj : q ≠ cj :=
    hS.ne_castLE_of_extExchangeMatrix_ne_zero hmn (by simp [hqj])
  have hx₂ : ∀ i, i ≠ ck → i ≠ cj → S₂.extCluster i = x i := fun i hik hij => by
    rw [seedMutation_extCluster_of_ne hmn S₁ hik, seedMutation_extCluster_of_ne hmn S hij]
  set E := ∏ i ∈ Finset.univ.erase ck, S₂.extCluster i ^ (S₂.extExchangeMatrix i j).toNat
  set G := ∏ i ∈ Finset.univ.erase q, S₂.extCluster i ^ (-S₂.extExchangeMatrix i j).toNat
  have hE : ∀ p, (∀ i, 0 < S₂.extExchangeMatrix i j → i ≠ p) →
      E ∈ laurentSubringExcept x p := fun p hp =>
    prod_pow_mem_laurentSubringExcept_of_eq fun i hi h0 => by
      have hpos : 0 < S₂.extExchangeMatrix i j := by omega
      refine ⟨hx₂ i (Finset.ne_of_mem_erase hi) fun h => ?_, hp i hpos⟩
      rw [h, h2jj] at hpos
      exact lt_irrefl 0 hpos
  have hG : ∀ p, (∀ i ∈ Finset.univ.erase q, S₂.extExchangeMatrix i j < 0 → i ≠ p) →
      G ∈ laurentSubringExcept x p := fun p hp =>
    prod_pow_mem_laurentSubringExcept_of_eq fun i hi h0 => by
      have hneg : S₂.extExchangeMatrix i j < 0 := by omega
      refine ⟨hx₂ i (fun h => ?_) fun h => ?_, hp i hi hneg⟩
      · rw [h] at hneg
        exact hneg.not_ge h2kj
      · rw [h, h2jj] at hneg
        exact lt_irrefl 0 hneg
  have hne : ∀ (s : Finset (Fin m)) (f : Fin m → ℕ), ∏ i ∈ s, S₂.extCluster i ^ f i ≠ 0 :=
    fun s f => Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hS₂.1.1.ne_zero i)
  refine ⟨(S₂.extExchangeMatrix ck j).toNat, E, G,
    hE r (fun i hi h => by rw [h, h2rj] at hi; exact lt_irrefl 0 hi),
    hE q (fun i hi h => by rw [h, h2qj] at hi; norm_num at hi), hne _ _,
    hG r (fun i _ hi h => by rw [h, h2rj] at hi; exact lt_irrefl 0 hi),
    hG q (fun i hi _ => Finset.ne_of_mem_erase hi), hne _ _, ?_⟩
  rw [seedMutation_extCluster_castLE_self hmn S₂ j, seedMutation_extCluster_of_ne hmn S₁ hcjk,
    mul_div_cancel₀ _ (hS₁.1.1.ne_zero cj),
    exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod,
    ← Finset.mul_prod_erase Finset.univ
      (fun i => S₂.extCluster i ^ (S₂.extExchangeMatrix i j).toNat) (Finset.mem_univ ck),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => S₂.extCluster i ^ (-S₂.extExchangeMatrix i j).toNat) (Finset.mem_univ q),
    h2qj, hx₂ q hq hqcj]
  norm_num
  rfl

end Seed

section Coprime

variable {K : Type*} [Field K] [Algebra K F] {m n : ℕ}

/-- **Case two: `x'ⱼ` does not divide `x''ⱼ`.** Let `(x̃, B̃)` be a labeled seed, `j ≠ k` with
`bⱼₖ < 0`, and `q, r` rows such that row `q` of `B̃` has `1` in column `j` and `0` elsewhere and
row `r` has `1` in column `k` and `0` elsewhere, with `q` not the row indexed by `k`. Then the
entry `x'ⱼ` of `μⱼ(x̃, B̃)` does not divide the entry `x''ⱼ` of `μⱼ(μₖ(μⱼ(x̃, B̃)))` in
`ℤ[x̃^{±1}]`. -/
theorem IsLabeledSeed.not_dvd_seedMutation_jkj_extCluster_castLE_self [CharZero K]
    (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) {j k : Fin n}
    (hjk : j ≠ k) (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) {q r : Fin m}
    (hq : q ≠ Fin.castLE hmn k)
    (hqrow : ∀ l, S.extExchangeMatrix q l = if l = j then 1 else 0)
    (hrrow : ∀ l, S.extExchangeMatrix r l = if l = k then 1 else 0) :
    ¬ (⟨(ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j),
        hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j
          ((hqrow j).trans (if_pos rfl))⟩ : laurentSubring S.extCluster) ∣
      ⟨(ClusterAlgebras.seedMutation hmn
        (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k) j).extCluster
          (Fin.castLE hmn j), hS.seedMutation_jkj_extCluster_mem_laurentSubring hmn hjk hb⟩ := by
  have := Algebra.charZero_of_charZero K F
  have hqj : S.extExchangeMatrix q j = 1 := (hqrow j).trans (if_pos rfl)
  have hqk : S.extExchangeMatrix q k = 0 := (hqrow k).trans (if_neg hjk.symm)
  have hrj : S.extExchangeMatrix r j = 0 := (hrrow j).trans (if_neg hjk)
  have hrk : S.extExchangeMatrix r k = 1 := (hrrow k).trans (if_pos rfl)
  have hqr : q ≠ r := by
    rintro rfl
    omega
  have hrcj : r ≠ Fin.castLE hmn j := by
    rintro rfl
    omega
  rintro ⟨g, hg⟩
  obtain ⟨A, B, hA, hB, hBq, hB0, hxk⟩ :=
    hS.exists_seedMutation_seedMutation_extCluster_eq_mul_add hmn hb hqj hqk hrj hrk hq
  obtain ⟨e, E, G, hE, hEq, hE0, hG, hGq, hG0, hN⟩ :=
    hS.exists_mul_seedMutation_jkj_extCluster_eq hmn hb hqj hqk hrj hrk hq
  refine pow_mul_add_mul_ne_sq_mul (hS.algebraicIndependent_rat hmn) hqr
    (seedMutation_extCluster_castLE_self_mem_laurentSubringExcept hmn S hrcj hrj)
    (hS.hasWidth_seedMutation_extCluster_castLE_self hmn j hqj) hA hB hE hG
    (mul_mem (pow_mem hBq e) hEq) hGq (mul_ne_zero (pow_ne_zero e hB0) hE0) hG0 g.2 ?_
  have hg' := congrArg Subtype.val hg
  simp only [Subring.coe_mul] at hg'
  rw [← hxk, ← hN, hg']
  ring

/-- **Case two: `x'ⱼ` and `x''ⱼ` are coprime.** Let `(x̃, B̃)` be a labeled seed, `j ≠ k` with
`bⱼₖ < 0`, and `q, r` rows such that row `q` of `B̃` has `1` in column `j` and `0` elsewhere and
row `r` has `1` in column `k` and `0` elsewhere, with `q` not the row indexed by `k` (for
instance `q` frozen). Then every common divisor in `ℤ[x̃^{±1}]` of the entry `x'ⱼ` of
`μⱼ(x̃, B̃)` and the entry `x''ⱼ` of `μⱼ(μₖ(μⱼ(x̃, B̃)))` is a unit. -/
@[cluster_algebras "lem_case_two_coprime_jj"]
theorem IsLabeledSeed.isRelPrime_seedMutation_jkj_extCluster_castLE_self [CharZero K]
    (hmn : n ≤ m) {S : SeedData F m n} (hS : IsLabeledSeed K hmn S) {j k : Fin n}
    (hjk : j ≠ k) (hb : S.extExchangeMatrix (Fin.castLE hmn j) k < 0) {q r : Fin m}
    (hq : q ≠ Fin.castLE hmn k)
    (hqrow : ∀ l, S.extExchangeMatrix q l = if l = j then 1 else 0)
    (hrrow : ∀ l, S.extExchangeMatrix r l = if l = k then 1 else 0) :
    IsRelPrime (⟨(ClusterAlgebras.seedMutation hmn S j).extCluster (Fin.castLE hmn j),
        hS.seedMutation_extCluster_castLE_self_mem_laurentSubring hmn j
          ((hqrow j).trans (if_pos rfl))⟩ : laurentSubring S.extCluster)
      ⟨(ClusterAlgebras.seedMutation hmn
        (ClusterAlgebras.seedMutation hmn (ClusterAlgebras.seedMutation hmn S j) k) j).extCluster
          (Fin.castLE hmn j), hS.seedMutation_jkj_extCluster_mem_laurentSubring hmn hjk hb⟩ :=
  (hS.prime_seedMutation_extCluster_castLE_self hmn j
    ((hqrow j).trans (if_pos rfl))).irreducible.isRelPrime_iff_not_dvd.2
      (hS.not_dvd_seedMutation_jkj_extCluster_castLE_self hmn hjk hb hq hqrow hrrow)

end Coprime

end ClusterAlgebras
