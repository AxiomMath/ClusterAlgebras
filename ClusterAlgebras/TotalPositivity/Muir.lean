/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.SchurComplement
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Muir's law of extensible minors

Muir's law says that a homogeneous polynomial identity among minors of the generic matrix
survives when the same rows `R` and the same columns `C` are adjoined to every minor:
if `F(Δ_{A_1,B_1}(z), …, Δ_{A_r,B_r}(z)) = 0` with `F` homogeneous, `|R| = |C|`, `R` disjoint
from the `A_s` and `C` from the `B_s`, then `F(Δ_{A_1 ∪ R,B_1 ∪ C}(z), …) = 0`. The case of
flag minors `P_B(z) = Δ_{[1,|B|],B}(z)` follows by shifting the rows by `|C|`.

The proof works over the fraction field `K` of `ℤ[z]`. With `d = Δ_{R,C}(z) ≠ 0` and `S` the
Schur complement `z/(R,C)`, the ring homomorphism `ψ : ℤ[z] → K` sending `z_{ab}` to
`(-1)^{ν({a},R) + ν({b},C)} S_{ab}` satisfies `d ψ(Δ_{A,B}(z)) = Δ_{A ∪ R, B ∪ C}(z)` by the
formula for minors through a Schur complement; homogeneity of `F` then gives
`F(Δ_{A_s ∪ R, B_s ∪ C}(z))_s = d^D ψ(F(Δ_{A_s,B_s}(z))_s) = 0`.

## Main results

* `ClusterAlgebras.muir_law`: Muir's law of extensible minors.
* `ClusterAlgebras.muir_law_flag`: Muir's law for flag minors.

## Implementation notes

* Rows and columns are indexed by arbitrary linear orders, and the polynomials `F` by an
  arbitrary type `σ`, rather than by the positive integers and `[1, r]`; the nonemptiness
  hypotheses on the `A_s`, `B_s` are dropped, the empty minor being `1`.
* The homomorphism `ψ` is defined by `z_{ab} ↦ (-1)^{ν({a},R) + ν({b},C)} S_{ab}` for every
  `(a, b)`, not only for `a ∉ R`, `b ∉ C`: only the entries in rows `A_s` and columns `B_s` are
  ever evaluated, and these lie outside `R` and `C`.
* For flag minors the rows are indexed by `ℕ`, 0-based, so `[1, k]` is `Finset.range k`; the
  row shift is the endomorphism `MvPolynomial.rename` of `z_{ij} ↦ z_{i + |C|, j}`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 1.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset MvPolynomial

/-- The shuffle count is additive in its first argument: `ν(A, R) = ∑_{a ∈ A} ν({a}, R)`. -/
theorem shuffleCount_eq_sum_singleton {ι : Type*} [LinearOrder ι] (A R : Finset ι) :
    shuffleCount A R = ∑ a ∈ A, shuffleCount {a} R := by
  classical
  simp only [shuffleCount, card_filter, sum_product, singleton_product]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_map]
  rfl

/-- Scaling the rows of a matrix by `u` and its columns by `v` multiplies its minor `Δ_{I,J}` by
`∏_{a ∈ I} u_a ∏_{b ∈ J} v_b`. (Both sides are `0` when `|I| ≠ |J|`.) -/
theorem minor_of_mul_mul {R : Type*} [CommRing R] {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (u : ι → R) (v : κ → R) (M : Matrix ι κ R) (I : Finset ι) (J : Finset κ) :
    minor (Matrix.of fun a b => u a * v b * M a b) I J =
      (∏ a ∈ I, u a) * (∏ b ∈ J, v b) * minor M I J := by
  by_cases h : J.card = I.card
  · rw [minor_of_card_eq _ rfl h, minor_of_card_eq _ rfl h]
    have hI : ∏ i : Fin I.card, u (I.orderEmbOfFin rfl i) = ∏ a ∈ I, u a := by
      rw [← prod_coe_sort I]
      exact Fintype.prod_equiv (I.orderIsoOfFin rfl).toEquiv _ _ fun i => rfl
    have hJ : ∏ i : Fin I.card, v (J.orderEmbOfFin h i) = ∏ b ∈ J, v b := by
      rw [← prod_coe_sort J]
      exact Fintype.prod_equiv (J.orderIsoOfFin h).toEquiv _ _ fun i => rfl
    rw [← hI, ← hJ, mul_assoc, ← Matrix.det_mul_row, ← Matrix.det_mul_column]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    ring
  · simp [minor, h]

/-- Reindexing rows and columns along order embeddings `f`, `g` carries the minor `Δ_{I,J}` to
the minor `Δ_{f(I), g(J)}`: an order embedding preserves the increasing enumerations. -/
theorem minor_submatrix_orderEmbedding {R : Type*} [CommRing R] {ι κ ι' κ' : Type*}
    [LinearOrder ι] [LinearOrder κ] [LinearOrder ι'] [LinearOrder κ']
    (M : Matrix ι κ R) (f : ι' ↪o ι) (g : κ' ↪o κ) (I : Finset ι') (J : Finset κ') :
    minor (M.submatrix f g) I J = minor M (I.map f.toEmbedding) (J.map g.toEmbedding) := by
  by_cases h : J.card = I.card
  · rw [minor_of_card_eq _ rfl h, minor_of_card_eq _ (card_map _) (by rw [card_map, h])]
    have hI := orderEmbOfFin_unique (s := I.map f.toEmbedding) (card_map _)
      (f := fun i => f (I.orderEmbOfFin rfl i)) (fun i => by simp)
      (f.strictMono.comp (I.orderEmbOfFin rfl).strictMono)
    have hJ := orderEmbOfFin_unique (s := J.map g.toEmbedding) (by rw [card_map, h])
      (f := fun i => g (J.orderEmbOfFin h i)) (fun i => by simp)
      (g.strictMono.comp (J.orderEmbOfFin h).strictMono)
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [← congrFun hI i, ← congrFun hJ j]
  · simp [minor, h]

/-- A ring homomorphism commutes with evaluating an integer polynomial. -/
theorem map_aeval_int {σ S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T]
    (g : S →+* T) (f : σ → S)
    (F : MvPolynomial σ ℤ) : g (aeval f F) = aeval (fun s => g (f s)) F := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

/-- A homogeneous polynomial `F` of degree `D` satisfies
`F(d y₁, …, d y_r) = d^D F(y₁, …, y_r)`. -/
theorem aeval_const_mul_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] {F : MvPolynomial σ R} {D : ℕ} (hF : F.IsHomogeneous D) (d : S) (y : σ → S) :
    aeval (fun s => d * y s) F = d ^ D * aeval y F := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : (∑ i ∈ m.support, m i) = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum] using hF (mem_support_iff.mp hm)
  simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hm']
  ring

/-- **Muir's law of extensible minors.** Let `z` be the generic matrix and `F` a homogeneous
integer polynomial with `F(Δ_{A_1,B_1}(z), …, Δ_{A_r,B_r}(z)) = 0`, where `|A_s| = |B_s|`. If
`|R| = |C|`, `R` is disjoint from every `A_s` and `C` from every `B_s`, then
`F(Δ_{A_1 ∪ R, B_1 ∪ C}(z), …, Δ_{A_r ∪ R, B_r ∪ C}(z)) = 0`. -/
@[cluster_algebras "thm_muir_law"]
theorem muir_law {ι κ σ : Type*} [LinearOrder ι] [LinearOrder κ] (A : σ → Finset ι)
    (B : σ → Finset κ) (hAB : ∀ s, (B s).card = (A s).card) {F : MvPolynomial σ ℤ} {D : ℕ}
    (hF : F.IsHomogeneous D)
    (h0 : MvPolynomial.aeval (fun s => minor (genericMatrix ι κ) (A s) (B s)) F = 0)
    (R : Finset ι) (C : Finset κ) (hRC : C.card = R.card) (hR : ∀ s, Disjoint R (A s))
    (hC : ∀ s, Disjoint C (B s)) :
    MvPolynomial.aeval (fun s => minor (genericMatrix ι κ) (A s ∪ R) (B s ∪ C)) F = 0 := by
  classical
  let K := FractionRing (MvPolynomial (ι × κ) ℤ)
  let φ : MvPolynomial (ι × κ) ℤ →+* K := algebraMap _ K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  let x : Matrix ι κ K := (genericMatrix ι κ).map φ
  have hd : minor x R C ≠ 0 := by
    rw [← RingHom.map_minor]
    exact (map_ne_zero_iff φ hφ).mpr (minor_genericMatrix_ne_zero hRC.symm)
  let M : Matrix ι κ K := Matrix.of fun a b =>
    (-1) ^ shuffleCount {a} R * (-1) ^ shuffleCount {b} C * schurComplement x R C a b
  let ψ := MvPolynomial.eval₂Hom (Int.castRingHom K) fun p : ι × κ => M p.1 p.2
  have claim : ∀ s, φ (minor (genericMatrix ι κ) (A s ∪ R) (B s ∪ C)) =
      minor x R C * ψ (minor (genericMatrix ι κ) (A s) (B s)) := fun s => by
    rw [RingHom.map_minor, RingHom.map_minor, genericMatrix_map_eval₂Hom,
      minor_union_eq_schurComplement x hRC hd (hR s).symm (hC s).symm (hAB s),
      minor_of_mul_mul, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, ← shuffleCount_eq_sum_singleton,
      ← shuffleCount_eq_sum_singleton, pow_add]
    ring
  apply hφ
  rw [map_zero, map_aeval_int, funext claim, aeval_const_mul_of_isHomogeneous hF,
    ← map_aeval_int, h0, map_zero, mul_zero]

/-- **Muir's law for flag minors.** With `z` the generic matrix with rows indexed by `ℕ`
(0-based) and `P_B(z) = Δ_{[1,|B|],B}(z)`, here `minor z (range #B) B`: if `F` is homogeneous
with `F(P_{B_1}(z), …, P_{B_r}(z)) = 0` and `C` is disjoint from every `B_s`, then
`F(P_{B_1 ∪ C}(z), …, P_{B_r ∪ C}(z)) = 0`. -/
@[cluster_algebras "prop_muir_flag"]
theorem muir_law_flag {κ σ : Type*} [LinearOrder κ] (B : σ → Finset κ)
    {F : MvPolynomial σ ℤ} {D : ℕ} (hF : F.IsHomogeneous D)
    (h0 : MvPolynomial.aeval
      (fun s => minor (genericMatrix ℕ κ) (range (B s).card) (B s)) F = 0)
    (C : Finset κ) (hC : ∀ s, Disjoint C (B s)) :
    MvPolynomial.aeval
      (fun s => minor (genericMatrix ℕ κ) (range (B s ∪ C).card) (B s ∪ C)) F = 0 := by
  classical
  let e : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono (· + C.card) fun a b h => by simpa using h
  let A : σ → Finset ℕ := fun s => (range (B s).card).map e.toEmbedding
  let σc : MvPolynomial (ℕ × κ) ℤ →+* MvPolynomial (ℕ × κ) ℤ :=
    (rename fun p : ℕ × κ => (p.1 + C.card, p.2)).toRingHom
  have hshift : ∀ s, σc (minor (genericMatrix ℕ κ) (range (B s).card) (B s)) =
      minor (genericMatrix ℕ κ) (A s) (B s) := by
    intro s
    rw [RingHom.map_minor]
    have : (genericMatrix ℕ κ).map σc =
        (genericMatrix ℕ κ).submatrix e (OrderIso.refl κ).toOrderEmbedding := by
      ext i j
      simp [σc, e, genericMatrix, Matrix.mvPolynomialX_apply]
    rw [this, minor_submatrix_orderEmbedding]
    congr 1
    ext b
    simp
  have h1 := muir_law A B (fun s => by simp [A]) hF
    (by simpa only [map_zero, map_aeval_int, hshift] using congrArg σc h0)
    (range C.card) C (by simp)
    (fun s => disjoint_left.2 fun a ha hb => by
      simp [A, e] at ha hb
      omega) hC
  convert h1 using 3
  funext s
  congr 1
  rw [card_union_of_disjoint (hC s).symm]
  ext a
  simp only [A, e, mem_union, mem_map, mem_range, RelEmbedding.coe_toEmbedding,
    OrderEmbedding.coe_ofStrictMono]
  constructor
  · intro h
    by_cases hc : a < C.card
    · exact Or.inr hc
    · exact Or.inl ⟨a - C.card, by omega, by omega⟩
  · rintro (⟨b, hb, rfl⟩ | h) <;> omega

end ClusterAlgebras
