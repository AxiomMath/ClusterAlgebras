/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Laurent.Expansion

/-!
# Widths of integer Laurent polynomials in one variable

Let `F` be a field of characteristic zero, `ỹ` a tuple of elements of `F` algebraically
independent over `ℚ`, and `q` an index. An element `z` of `F` has `q`-width `w` when
`z = ∑_{e=0}^{w} c_e y_q^{e₀ + e}` with coefficients `c_e ∈ ℤ[ỹ_q̂^{±1}]` and `c₀ ≠ 0 ≠ c_w`
(`ClusterAlgebras.HasWidth`). Every nonzero `z ∈ ℤ[ỹ^{±1}]` has exactly one `q`-width, widths
add under multiplication, and units have width `0`. Consequently `A y_q + B` is irreducible in
`ℤ[ỹ^{±1}]` when `A ≠ 0` and `B` is a unit of `ℤ[ỹ_q̂^{±1}]`: in a factorization one factor has
width `0`, hence is `c y_qᵉ`, and comparing constant terms in `y_q` shows that `c` divides `B`.

## Main results

* `ClusterAlgebras.existsUnique_hasWidth`: a nonzero element of `ℤ[ỹ^{±1}]` has exactly one
  `q`-width; separately `ClusterAlgebras.exists_hasWidth` and `ClusterAlgebras.HasWidth.unique`.
* `ClusterAlgebras.HasWidth.mul`: widths add under multiplication.
* `ClusterAlgebras.hasWidth_zero_of_isUnit`: units of `ℤ[ỹ^{±1}]` have `q`-width `0`.
* `ClusterAlgebras.irreducible_mul_add`: `A y_q + B` is irreducible in `ℤ[ỹ^{±1}]`.
* `ClusterAlgebras.HasWidth.exists_of_mul`, `ClusterAlgebras.HasWidth.of_mul`: the width of a
  cofactor is the difference of the widths.
* `ClusterAlgebras.HasWidth.not_isUnit_of_pos`: elements of positive width are not units.

## Implementation notes

An element of `q`-width `w` is written here as `y_q^{e₀} P(y_q)` for a polynomial `P` over
`ℤ[ỹ_q̂^{±1}]` of degree `w` with nonzero constant term
(`ClusterAlgebras.hasWidth_iff_exists_polynomial`). Rather than grouping the Laurent monomials of
`z` according to their exponent of `y_q`, uniqueness of the pair `(e₀, P)` is deduced from the
transcendence of `y_q` over `ℤ[ỹ_q̂^{±1}]`, and existence from writing the one-variable Laurent
expansion of `z` as a power of `y_q` times a polynomial and removing the largest power of the
variable dividing that polynomial. Additivity of widths is the multiplicativity of degrees and
constant terms of polynomials over the domain `ℤ[ỹ_q̂^{±1}]`. It uses only `y_q ≠ 0`, not the
characteristic or the algebraic independence, and is stated under that hypothesis. The tuple is
indexed by an arbitrary type rather than by `[1, m]`.
-/

@[expose] public section

open Polynomial

namespace ClusterAlgebras

variable {F ι : Type*} [Field F] {y : ι → F} {q : ι} {z z' g h : F} {v w w' : ℕ}

section Basic

/-- An element of `q`-width `w` is an integer Laurent polynomial in `ỹ`. -/
theorem HasWidth.mem_laurentSubring (hz : HasWidth y q z w) : z ∈ laurentSubring y := by
  obtain ⟨e₀, c, hc, -, -, rfl⟩ := hz
  exact Subring.sum_mem _ fun e he => mul_mem
    (laurentSubringExcept_le y q (hc e (Nat.lt_succ_iff.1 (Finset.mem_range.1 he))))
    (zpow_mem_laurentSubring y q _)

/-- An element has `q`-width `0` exactly when it is `c y_qᵉ` for an integer `e` and a nonzero
`c ∈ ℤ[ỹ_q̂^{±1}]`. -/
theorem hasWidth_zero_iff :
    HasWidth y q z 0 ↔ ∃ (e : ℤ) (c : F), c ∈ laurentSubringExcept y q ∧ c ≠ 0 ∧
      z = c * y q ^ e := by
  constructor
  · rintro ⟨e₀, c, hc, h0, -, rfl⟩
    exact ⟨e₀, c 0, hc 0 le_rfl, h0, by simp⟩
  · rintro ⟨e, c, hc, h0, rfl⟩
    exact ⟨e, fun _ => c, fun _ _ => hc, h0, h0, by simp⟩

/-- A nonzero element of `ℤ[ỹ_q̂^{±1}]` has `q`-width `0`. -/
theorem hasWidth_zero_of_mem_except (hz : z ∈ laurentSubringExcept y q) (hz0 : z ≠ 0) :
    HasWidth y q z 0 :=
  hasWidth_zero_iff.2 ⟨0, z, hz, hz0, by simp⟩

/-- `A y_q + B` has `q`-width `1` for nonzero `A, B ∈ ℤ[ỹ_q̂^{±1}]`. -/
theorem hasWidth_one_mul_add {A B : F} (hA : A ∈ laurentSubringExcept y q)
    (hB : B ∈ laurentSubringExcept y q) (hA0 : A ≠ 0) (hB0 : B ≠ 0) :
    HasWidth y q (A * y q + B) 1 := by
  refine ⟨0, fun e => if e = 0 then B else A, fun e _ => ?_, by simpa using hB0,
    by simpa using hA0, ?_⟩
  · dsimp only
    split_ifs
    exacts [hB, hA]
  · simp [Finset.sum_range_succ, add_comm]

/-- `A y_q + B` lies in `ℤ[ỹ^{±1}]` for `A, B ∈ ℤ[ỹ_q̂^{±1}]`. -/
theorem mul_add_mem_laurentSubring (A B : laurentSubringExcept y q) :
    (A * y q + B : F) ∈ laurentSubring y :=
  add_mem (mul_mem (laurentSubringExcept_le y q A.2) (mem_laurentSubring y q))
    (laurentSubringExcept_le y q B.2)

end Basic

section Polynomial

/-- For `y_q ≠ 0`, an element has `q`-width `w` exactly when it is `y_q^{e₀} P(y_q)` for an
integer `e₀` and a polynomial `P` over `ℤ[ỹ_q̂^{±1}]` of degree `w` with nonzero constant
term. -/
theorem hasWidth_iff_exists_polynomial (hq : y q ≠ 0) :
    HasWidth y q z w ↔ ∃ (e₀ : ℤ) (P : (laurentSubringExcept y q)[X]),
      P.natDegree = w ∧ P.coeff 0 ≠ 0 ∧ z = y q ^ e₀ * aeval (y q) P := by
  constructor
  · rintro ⟨e₀, c, hc, h0, hw, rfl⟩
    classical
    let d : ℕ → laurentSubringExcept y q := fun e => if he : e ≤ w then ⟨c e, hc e he⟩ else 0
    have hd : ∀ e ≤ w, (d e : F) = c e := fun e he => by simp [d, he]
    set P := ∑ e ∈ Finset.range (w + 1), monomial e (d e)
    have hP : ∀ k, P.coeff k = if k ≤ w then d k else 0 := fun k => by
      simp [P, coeff_monomial]
    have hPw : P.coeff w ≠ 0 := by
      rw [hP, if_pos le_rfl]
      exact fun h => hw (by rw [← hd w le_rfl, h, ZeroMemClass.coe_zero])
    have hP0 : P.coeff 0 ≠ 0 := by
      rw [hP, if_pos (Nat.zero_le _)]
      exact fun h => h0 (by rw [← hd 0 (Nat.zero_le _), h, ZeroMemClass.coe_zero])
    refine ⟨e₀, P, natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_le_iff_coeff_eq_zero.2 fun N hN => by rw [hP, if_neg hN.not_ge]) hPw, hP0, ?_⟩
    simp only [P, map_sum, aeval_monomial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    change _ = _ * ((d e : F) * _)
    rw [hd e (Nat.lt_succ_iff.1 (Finset.mem_range.1 he)), zpow_add₀ hq, zpow_natCast]
    ring
  · rintro ⟨e₀, P, rfl, h0, rfl⟩
    have hP : P ≠ 0 := fun h => h0 (by simp [h])
    refine ⟨e₀, fun e => P.coeff e, fun e _ => (P.coeff e).2,
      fun h => h0 (Subtype.ext h), fun h => leadingCoeff_ne_zero.2 hP (Subtype.ext h), ?_⟩
    rw [aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [zpow_add₀ hq, zpow_natCast, Subring.smul_def, smul_eq_mul]
    ring

/-- **Widths add under multiplication**: if `z` and `z'` have `q`-widths `w` and `w'`, then
`z z'` has `q`-width `w + w'`. Only `y_q ≠ 0` is used. -/
@[cluster_algebras "lem_width_additive"]
theorem HasWidth.mul (hq : y q ≠ 0) (hz : HasWidth y q z w) (hz' : HasWidth y q z' w') :
    HasWidth y q (z * z') (w + w') := by
  obtain ⟨e₀, P, rfl, h0, rfl⟩ := (hasWidth_iff_exists_polynomial hq).1 hz
  obtain ⟨e₀', P', rfl, h0', rfl⟩ := (hasWidth_iff_exists_polynomial hq).1 hz'
  have hP : P ≠ 0 := fun h => h0 (by simp [h])
  have hP' : P' ≠ 0 := fun h => h0' (by simp [h])
  refine (hasWidth_iff_exists_polynomial hq).2 ⟨e₀ + e₀', P * P', natDegree_mul hP hP',
    by simpa using mul_ne_zero h0 h0', ?_⟩
  rw [zpow_add₀ hq, map_mul]
  ring

end Polynomial

section Unique

variable [CharZero F] (hy : AlgebraicIndependent ℚ y)

include hy

/-- Evaluation at `y_q` of polynomials over `ℤ[ỹ_q̂^{±1}]` is injective. -/
theorem aeval_except_injective (q : ι) :
    Function.Injective (aeval (R := laurentSubringExcept y q) (y q)) :=
  transcendental_iff_injective.1 (transcendental_laurentSubringExcept hy q)

/-- If `y_q^{e₀} P(y_q) = y_q^{e₀'} P'(y_q)` with `e₀ ≤ e₀'` and `P(0) ≠ 0`, then `e₀ = e₀'`
and `P = P'`. -/
theorem eq_of_zpow_mul_aeval_eq_of_le {e₀ e₀' : ℤ} {P P' : (laurentSubringExcept y q)[X]}
    (hP : P.coeff 0 ≠ 0) (he : e₀ ≤ e₀')
    (h : y q ^ e₀ * aeval (y q) P = y q ^ e₀' * aeval (y q) P') : e₀ = e₀' ∧ P = P' := by
  obtain ⟨n, rfl⟩ := Int.exists_add_of_le he
  have hq := hy.ne_zero q
  rw [zpow_add₀ hq, zpow_natCast, mul_assoc] at h
  have hPP : P = X ^ n * P' := aeval_except_injective hy q <| by
    rw [mul_left_cancel₀ (zpow_ne_zero _ hq) h, map_mul, map_pow, aeval_X]
  have hn : n = 0 := by
    by_contra hn
    apply hP
    rw [hPP, coeff_X_pow_mul', if_neg (by omega)]
  subst hn
  simpa using hPP

/-- **Uniqueness of the form `y_q^{e₀} P(y_q)`**: if `y_q^{e₀} P(y_q) = y_q^{e₀'} P'(y_q)` for
polynomials `P, P'` over `ℤ[ỹ_q̂^{±1}]` with nonzero constant terms, then `e₀ = e₀'` and
`P = P'`. -/
theorem eq_of_zpow_mul_aeval_eq {e₀ e₀' : ℤ} {P P' : (laurentSubringExcept y q)[X]}
    (hP : P.coeff 0 ≠ 0) (hP' : P'.coeff 0 ≠ 0)
    (h : y q ^ e₀ * aeval (y q) P = y q ^ e₀' * aeval (y q) P') : e₀ = e₀' ∧ P = P' := by
  rcases le_total e₀ e₀' with he | he
  · exact eq_of_zpow_mul_aeval_eq_of_le hy hP he h
  · exact (eq_of_zpow_mul_aeval_eq_of_le hy hP' he h.symm).imp Eq.symm Eq.symm

/-- Every nonzero element of `ℤ[ỹ^{±1}]` is `y_q^{e₀} P(y_q)` for an integer `e₀` and a
polynomial `P` over `ℤ[ỹ_q̂^{±1}]` with nonzero constant term. -/
theorem exists_zpow_mul_aeval (q : ι) (hz : z ∈ laurentSubring y) (hz0 : z ≠ 0) :
    ∃ (e₀ : ℤ) (P : (laurentSubringExcept y q)[X]), P.coeff 0 ≠ 0 ∧
      z = y q ^ e₀ * aeval (y q) P := by
  have hq := hy.ne_zero q
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow ((laurentEquivOfExcept hy q).symm ⟨z, hz⟩)
  have hf' : aeval (y q) f = z * y q ^ n := by
    simpa [map_mul] using congrArg (fun p => (laurentEquivOfExcept hy q p : F)) hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hf'
    exact mul_ne_zero hz0 (pow_ne_zero _ hq) hf'.symm
  obtain ⟨P, hfP, hP⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  rw [map_zero, sub_zero, X_dvd_iff] at hP
  refine ⟨rootMultiplicity 0 f - n, P, hP, ?_⟩
  rw [hfP, map_mul, map_zero, sub_zero, map_pow, aeval_X] at hf'
  rw [zpow_sub₀ hq, zpow_natCast, zpow_natCast, div_mul_eq_mul_div, hf',
    mul_div_cancel_right₀ _ (pow_ne_zero _ hq)]

/-- An element with a `q`-width is nonzero. -/
theorem HasWidth.ne_zero (hz : HasWidth y q z w) : z ≠ 0 := by
  obtain ⟨e₀, P, -, h0, rfl⟩ := (hasWidth_iff_exists_polynomial (hy.ne_zero q)).1 hz
  refine mul_ne_zero (zpow_ne_zero _ (hy.ne_zero q)) fun h => h0 ?_
  rw [(aeval_except_injective hy q).eq_iff' (map_zero _) |>.1 h, coeff_zero]

/-- **Uniqueness of the width**: an element has at most one `q`-width. -/
theorem HasWidth.unique (hz : HasWidth y q z w) (hz' : HasWidth y q z w') : w = w' := by
  obtain ⟨e₀, P, rfl, h0, rfl⟩ := (hasWidth_iff_exists_polynomial (hy.ne_zero q)).1 hz
  obtain ⟨e₀', P', rfl, h0', h⟩ := (hasWidth_iff_exists_polynomial (hy.ne_zero q)).1 hz'
  rw [(eq_of_zpow_mul_aeval_eq hy h0 h0' h).2]

/-- **Existence of the width**: every nonzero element of `ℤ[ỹ^{±1}]` has a `q`-width. -/
theorem exists_hasWidth (q : ι) (hz : z ∈ laurentSubring y) (hz0 : z ≠ 0) :
    ∃ w, HasWidth y q z w := by
  obtain ⟨e₀, P, h0, rfl⟩ := exists_zpow_mul_aeval hy q hz hz0
  exact ⟨P.natDegree, (hasWidth_iff_exists_polynomial (hy.ne_zero q)).2 ⟨e₀, P, rfl, h0, rfl⟩⟩

/-- **Every nonzero Laurent polynomial has exactly one width**: a nonzero element of
`ℤ[ỹ^{±1}]` has exactly one `q`-width. -/
@[cluster_algebras "lem_width_exists_unique"]
theorem existsUnique_hasWidth (q : ι) (hz : z ∈ laurentSubring y) (hz0 : z ≠ 0) :
    ∃! w, HasWidth y q z w :=
  let ⟨w, hw⟩ := exists_hasWidth hy q hz hz0
  ⟨w, hw, fun _ hw' => (hw.unique hy hw').symm⟩

end Unique

section Consequences

variable [CharZero F] (hy : AlgebraicIndependent ℚ y)

include hy

/-- **Widths of factors**: if `g h` has `q`-width `w` and `g` has `q`-width `v`, for `h` in
`ℤ[ỹ^{±1}]`, then `h` has a `q`-width `u` with `w = v + u`. -/
theorem HasWidth.exists_of_mul (hz : HasWidth y q (g * h) w) (hg : HasWidth y q g v)
    (hh : h ∈ laurentSubring y) : ∃ u, HasWidth y q h u ∧ w = v + u := by
  obtain ⟨u, hu⟩ := exists_hasWidth hy q hh (right_ne_zero_of_mul (hz.ne_zero hy))
  exact ⟨u, hu, hz.unique hy (hg.mul (hy.ne_zero q) hu)⟩

/-- If `g h` has `q`-width `w` and `g` has `q`-width `v`, for `h ∈ ℤ[ỹ^{±1}]`, then `v ≤ w`. -/
theorem HasWidth.le_of_mul (hz : HasWidth y q (g * h) w) (hg : HasWidth y q g v)
    (hh : h ∈ laurentSubring y) : v ≤ w := by
  obtain ⟨u, -, rfl⟩ := hz.exists_of_mul hy hg hh
  exact Nat.le_add_right v u

/-- If `g h` has `q`-width `w` and `g` has `q`-width `v`, for `h ∈ ℤ[ỹ^{±1}]`, then `h` has
`q`-width `w - v`. -/
theorem HasWidth.of_mul (hz : HasWidth y q (g * h) w) (hg : HasWidth y q g v)
    (hh : h ∈ laurentSubring y) : HasWidth y q h (w - v) := by
  obtain ⟨u, hu, rfl⟩ := hz.exists_of_mul hy hg hh
  rwa [Nat.add_sub_cancel_left]

/-- **Units have width zero**: every unit of `ℤ[ỹ^{±1}]` has `q`-width `0`. -/
@[cluster_algebras "lem_unit_width_zero"]
theorem hasWidth_zero_of_isUnit (q : ι) {u : laurentSubring y} (hu : IsUnit u) :
    HasWidth y q u 0 := by
  obtain ⟨u, rfl⟩ := hu
  have h1 : HasWidth y q ((u : laurentSubring y) * (u⁻¹ : (laurentSubring y)ˣ) : F) 0 := by
    rw [← Subring.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    exact hasWidth_zero_of_mem_except (one_mem _) one_ne_zero
  obtain ⟨w, hw⟩ := exists_hasWidth hy q (Subtype.coe_prop (u : laurentSubring y))
    fun h => u.ne_zero (Subtype.ext h)
  obtain rfl := Nat.le_zero.1 (h1.le_of_mul hy hw (Subtype.coe_prop _))
  exact hw

/-- An element of positive `q`-width is not a unit of `ℤ[ỹ^{±1}]`. -/
theorem HasWidth.not_isUnit_of_pos (hz : HasWidth y q z w) (hw : 0 < w) :
    ¬ IsUnit (⟨z, hz.mem_laurentSubring⟩ : laurentSubring y) := fun hu =>
  hw.ne' (hz.unique hy (hasWidth_zero_of_isUnit hy q hu))

/-- If `g h = A y_q + B` with `A, B ∈ ℤ[ỹ_q̂^{±1}]` and `B` a unit there, `g` of `q`-width `0`
and `h ∈ ℤ[ỹ^{±1}]` nonzero, then `g` is a unit of `ℤ[ỹ^{±1}]`. -/
theorem isUnit_of_hasWidth_zero_of_mul_eq {A B : laurentSubringExcept y q} (hB : IsUnit B)
    (hg : HasWidth y q g 0) (hh : h ∈ laurentSubring y) (hh0 : h ≠ 0)
    (hgh : g * h = A * y q + B) : IsUnit (⟨g, hg.mem_laurentSubring⟩ : laurentSubring y) := by
  have hq := hy.ne_zero q
  obtain ⟨e, c, hc, hc0, rfl⟩ := hasWidth_zero_iff.1 hg
  obtain ⟨f, Q, hQ, rfl⟩ := exists_zpow_mul_aeval hy q hh hh0
  set c' : laurentSubringExcept y q := ⟨c, hc⟩
  have key := eq_of_zpow_mul_aeval_eq hy (e₀ := e + f) (e₀' := 0) (P := C c' * Q)
    (P' := C A * X + C B) ?_ (by simpa using hB.ne_zero) ?_
  · have h0 := congrArg (coeff · 0) key.2
    simp only [coeff_C_mul, coeff_add, coeff_C_zero] at h0
    have hcU : IsUnit c' := isUnit_of_dvd_unit ⟨_, (h0.trans (by simp)).symm⟩ hB
    have : (⟨c * y q ^ e, hg.mem_laurentSubring⟩ : laurentSubring y) =
        laurentEquivOfExcept hy q (LaurentPolynomial.C c' * LaurentPolynomial.T e) := by
      ext
      simp [c']
    rw [this]
    exact ((hcU.map LaurentPolynomial.C).mul (LaurentPolynomial.isUnit_T e)).map _
  · rw [coeff_C_mul]
    exact mul_ne_zero (fun h => hc0 (congrArg Subtype.val h)) hQ
  · simp only [zpow_zero, one_mul, map_add, map_mul, aeval_C, aeval_X, zpow_add₀ hq]
    change _ * ((c : F) * _) = (A : F) * _ + (B : F)
    rw [← hgh]
    ring

/-- **A Laurent polynomial linear in one variable with a unit term is irreducible**: for
`A, B ∈ ℤ[ỹ_q̂^{±1}]` with `A ≠ 0` and `B` a unit of `ℤ[ỹ_q̂^{±1}]`, the element `A y_q + B` is
irreducible in `ℤ[ỹ^{±1}]`. -/
@[cluster_algebras "lem_linear_irreducible"]
theorem irreducible_mul_add {A B : laurentSubringExcept y q} (hA : A ≠ 0) (hB : IsUnit B) :
    Irreducible (⟨A * y q + B, mul_add_mem_laurentSubring A B⟩ : laurentSubring y) := by
  have hz : HasWidth y q (A * y q + B) 1 := hasWidth_one_mul_add A.2 B.2
    (fun h => hA (Subtype.ext h)) (fun h => hB.ne_zero (Subtype.ext h))
  refine irreducible_iff.2 ⟨hz.not_isUnit_of_pos hy one_pos, fun g h hgh => ?_⟩
  have hgh' : (g * h : F) = A * y q + B := (congrArg Subtype.val hgh).symm
  have hgh0 : (g * h : F) ≠ 0 := hgh' ▸ hz.ne_zero hy
  obtain ⟨v, hv⟩ := exists_hasWidth hy q g.2 (left_ne_zero_of_mul hgh0)
  obtain ⟨u, hu, hvu⟩ := (hgh' ▸ hz : HasWidth y q (g * h : F) 1).exists_of_mul hy hv h.2
  rcases Nat.add_eq_one_iff.1 hvu.symm with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact .inl (isUnit_of_hasWidth_zero_of_mul_eq hy hB hv h.2 (right_ne_zero_of_mul hgh0) hgh')
  · exact .inr (isUnit_of_hasWidth_zero_of_mul_eq hy hB hu g.2 (left_ne_zero_of_mul hgh0)
      (by rw [mul_comm, hgh']))

end Consequences

end ClusterAlgebras
