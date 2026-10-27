/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Laurent.Defs
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Clearing denominators

This file proves three facts about clearing denominators.

* An element `z` of a commutative ring without zero divisors lies in a subring `L` as soon as it
  does after multiplication by a power of a prime `p` of `L` and after multiplication by an
  element `w` of `L` not divisible by `p`.
* If a tuple `ỹ'` agrees with `ỹ` outside a finite set `T` of positions, and its entries in the
  positions of `T` lie in `ℤ[ỹ^{±1}]`, then every element of `ℤ[ỹ'^{±1}]` is carried into
  `ℤ[ỹ^{±1}]` by multiplication with a monomial in the `y'ᵢ`, `i ∈ T`.
* If `P = Q L` for polynomials `P` and `Q` over a semiring without zero divisors and a Laurent
  polynomial `L`, and `Q` has a nonzero constant term, then `L` is a polynomial, and the constant
  terms satisfy `Q(0) L(0) = P(0)`.

## Main definitions

* `ClusterAlgebras.mvPolynomialToLaurent`: the embedding of the polynomials over `S` in variables
  indexed by `σ` into the Laurent polynomials over `S` in the same variables.

## Main results

* `ClusterAlgebras.mem_of_mul_pow_mem_of_mul_mem`: clearing a denominator coprime to a prime.
* `ClusterAlgebras.exists_mul_prod_pow_mem_laurentSubring`: clearing the new variables of a
  nearby cluster.
* `ClusterAlgebras.exists_eq_mvPolynomialToLaurent_of_eq_mul`: a Laurent polynomial in several
  variables whose product with a polynomial with nonzero constant term is a polynomial is itself
  a polynomial.
* `ClusterAlgebras.exists_eq_toLaurent_of_eq_mul`: the same statement in one variable, for
  Mathlib's `LaurentPolynomial`.

## Implementation notes

Laurent polynomials over `S` in variables indexed by `σ` are modelled as the additive monoid
algebra `AddMonoidAlgebra S (σ →₀ ℤ)`, just as Mathlib's `LaurentPolynomial S` is
`AddMonoidAlgebra S ℤ`; polynomials enter through `mvPolynomialToLaurent`, the ring
homomorphism induced by the inclusion of exponent vectors `(σ →₀ ℕ) → (σ →₀ ℤ)`.

The tuples in `exists_mul_prod_pow_mem_laurentSubring` are indexed by an arbitrary type, and
their entries need not be nonzero: an entry `y'ᵢ = 0` has `(y'ᵢ)⁻¹ = 0`, which lies in every
subring.

`exists_eq_mvPolynomialToLaurent_of_eq_mul` is proved one variable at a time: the least exponent
`e` of the variable `Yᵢ` in `L` cannot be negative, because the product of the terms of `Q` in
which `Yᵢ` does not occur with the terms of `L` in which `Yᵢ` has exponent `e` is nonzero. This
nonvanishing is obtained from the existence of a uniquely attained sum of exponents
(`UniqueSums`), as in `AddMonoidAlgebra.nonneg_of_mem_support_of_mul`.
-/

@[expose] public section

namespace ClusterAlgebras

section Coprime

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- **Clearing a denominator coprime to a prime.** Let `L` be a subring of `R`, let `p` be a
prime of `L` and `w` an element of `L` not divisible by `p`. If `z * p ^ a` and `z * w` lie in
`L`, then so does `z`. -/
@[cluster_algebras "lem_coprime_denominators"]
theorem mem_of_mul_pow_mem_of_mul_mem (L : Subring R) {p w : L} (hp : Prime p) (hpw : ¬p ∣ w)
    (a : ℕ) {z : R} (h₁ : z * (p : R) ^ a ∈ L) (h₂ : z * w ∈ L) : z ∈ L := by
  induction a with
  | zero => simpa using h₁
  | succ a ih =>
    set u : L := ⟨z * (p : R) ^ (a + 1), h₁⟩
    set v : L := ⟨z * w, h₂⟩
    have huv : u * w = p * (p ^ a * v) := Subtype.ext <| by simp [u, v]; ring
    obtain ⟨u', hu'⟩ := (hp.dvd_or_dvd ⟨_, huv⟩).resolve_right hpw
    have hp₀ : (p : R) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine ih ?_
    have : z * (p : R) ^ a = u' := by
      apply mul_left_cancel₀ hp₀
      have := congrArg Subtype.val hu'
      simp only [u, Subring.coe_mul] at this
      rw [← this]; ring
    exact this ▸ u'.2

end Coprime

section ClearDenominators

variable {F ι : Type*} [Field F]

/-- **Clearing the new variables of a nearby cluster.** Let `ỹ'` agree with `ỹ` outside a
finite set `T` of positions, and let `y'ᵢ ∈ ℤ[ỹ^{±1}]` for `i ∈ T`. Then every
`z ∈ ℤ[ỹ'^{±1}]` has a multiple `z ∏_{i ∈ T} (y'ᵢ)^{aᵢ}` in `ℤ[ỹ^{±1}]`. -/
@[cluster_algebras "lem_laurent_clear_denominators"]
theorem exists_mul_prod_pow_mem_laurentSubring {y y' : ι → F} {T : Finset ι}
    (hT : ∀ i ∉ T, y' i = y i) (hT' : ∀ i ∈ T, y' i ∈ laurentSubring y) {z : F}
    (hz : z ∈ laurentSubring y') :
    ∃ a : ι → ℕ, z * ∏ i ∈ T, y' i ^ a i ∈ laurentSubring y := by
  classical
  have hprod (a : ι → ℕ) : ∏ i ∈ T, y' i ^ a i ∈ laurentSubring y :=
    Subring.prod_mem _ fun i hi => pow_mem (hT' i hi) _
  have hmem {x : F} (hx : x ∈ laurentSubring y) :
      ∃ a : ι → ℕ, x * ∏ i ∈ T, y' i ^ a i ∈ laurentSubring y :=
    ⟨0, by simpa using hx⟩
  have hy' (j : ι) : y' j ∈ laurentSubring y := by
    by_cases hj : j ∈ T
    · exact hT' j hj
    · exact hT j hj ▸ mem_laurentSubring y j
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact hmem (hy' j)
    · by_cases hj : j ∈ T
      · by_cases h₀ : y' j = 0
        · exact hmem (by simp [h₀])
        refine ⟨Pi.single j 1, ?_⟩
        rw [Finset.prod_eq_single_of_mem j hj fun i _ hij => by simp [hij]]
        simp [h₀]
      · exact hmem (by simpa [hT j hj] using inv_mem_laurentSubring y j)
  | zero => exact hmem (zero_mem _)
  | one => exact hmem (one_mem _)
  | add x x' _ _ hx hx' =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hx'
    refine ⟨a + b, ?_⟩
    have key (c d : ι → ℕ) :
        ∏ i ∈ T, y' i ^ (c + d) i = (∏ i ∈ T, y' i ^ c i) * ∏ i ∈ T, y' i ^ d i := by
      simp [pow_add, Finset.prod_mul_distrib]
    rw [add_mul]
    refine add_mem ?_ ?_
    · rw [key, ← mul_assoc]; exact mul_mem ha (hprod b)
    · rw [add_comm a b, key, ← mul_assoc]; exact mul_mem hb (hprod a)
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, by simpa [neg_mul] using neg_mem ha⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hx'
    refine ⟨a + b, ?_⟩
    have : x * x' * ∏ i ∈ T, y' i ^ (a + b) i =
        (x * ∏ i ∈ T, y' i ^ a i) * (x' * ∏ i ∈ T, y' i ^ b i) := by
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]; ring
    exact this ▸ mul_mem ha hb

end ClearDenominators

section LaurentImpliesPolynomial

variable {S A : Type*} [Semiring S] [NoZeroDivisors S] [AddMonoid A] [UniqueSums A]

/-- Let `D` be an integer-valued grading of the exponents. If every term of `Q` has
nonnegative degree, some term of `Q` has degree zero, and every term of `Q * L` has nonnegative
degree, then every term of `L` has nonnegative degree. -/
theorem AddMonoidAlgebra.nonneg_of_mem_support_of_mul {D : A →+ ℤ}
    {Q L : AddMonoidAlgebra S A} (hQ : ∀ g ∈ Q.support, 0 ≤ D g)
    (hQ₀ : ∃ g ∈ Q.support, D g = 0) (hQL : ∀ f ∈ (Q * L).support, 0 ≤ D f) {f : A}
    (hf : f ∈ L.support) : 0 ≤ D f := by
  classical
  by_contra hneg
  obtain ⟨m, hm, hmin⟩ := L.support.exists_min_image D ⟨f, hf⟩
  have hB : (Q.support.filter fun g => D g = 0).Nonempty := by
    obtain ⟨g, hg, hg₀⟩ := hQ₀
    exact ⟨g, Finset.mem_filter.2 ⟨hg, hg₀⟩⟩
  have hA : (L.support.filter fun f' => D f' = D m).Nonempty :=
    ⟨m, Finset.mem_filter.2 ⟨hm, rfl⟩⟩
  obtain ⟨b₀, hb₀, a₀, ha₀, huniq⟩ := UniqueSums.uniqueAdd_of_nonempty hB hA
  rw [Finset.mem_filter] at hb₀ ha₀
  have huniq' : UniqueAdd Q.support L.support b₀ a₀ := by
    intro g f' hg hf' hsum
    have hD := congrArg D hsum
    rw [map_add, map_add, hb₀.2, ha₀.2] at hD
    have h₁ := hQ g hg
    have h₂ := hmin f' hf'
    exact huniq (Finset.mem_filter.2 ⟨hg, by omega⟩) (Finset.mem_filter.2 ⟨hf', by omega⟩) hsum
  have hne : b₀ + a₀ ∈ (Q * L).support := by
    rw [Finsupp.mem_support_iff, AddMonoidAlgebra.mul_apply_add_eq_mul_of_uniqueAdd huniq']
    exact mul_ne_zero (Finsupp.mem_support_iff.1 hb₀.1) (Finsupp.mem_support_iff.1 ha₀.1)
  have := hQL _ hne
  rw [map_add, hb₀.2, ha₀.2] at this
  have := hmin f hf
  omega

end LaurentImpliesPolynomial

section MvLaurent

variable (σ S : Type*) [CommSemiring S]

/-- The embedding of the polynomials over `S` in variables indexed by `σ` into the Laurent
polynomials `AddMonoidAlgebra S (σ →₀ ℤ)`, induced by the inclusion `(σ →₀ ℕ) → (σ →₀ ℤ)` of
exponent vectors. -/
noncomputable def mvPolynomialToLaurent : MvPolynomial σ S →+* AddMonoidAlgebra S (σ →₀ ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom S (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ))

variable {σ S}

/-- The inclusion of exponent vectors `(σ →₀ ℕ) → (σ →₀ ℤ)` is injective. -/
private theorem mapRange_natCast_injective :
    Function.Injective (Finsupp.mapRange ((↑) : ℕ → ℤ) Nat.cast_zero : (σ →₀ ℕ) → σ →₀ ℤ) :=
  Finsupp.mapRange_injective _ _ Nat.cast_injective

/-- The coefficient of a polynomial at a nonnegative exponent vector is unchanged by passing to
Laurent polynomials. -/
theorem mvPolynomialToLaurent_apply_mapRange (P : MvPolynomial σ S) (g : σ →₀ ℕ) :
    mvPolynomialToLaurent σ S P (g.mapRange (↑) Nat.cast_zero) = P.coeff g :=
  Finsupp.mapDomain_apply mapRange_natCast_injective P g

/-- The constant term of a polynomial is unchanged by passing to Laurent polynomials. -/
theorem mvPolynomialToLaurent_apply_zero (P : MvPolynomial σ S) :
    mvPolynomialToLaurent σ S P 0 = MvPolynomial.constantCoeff P := by
  simpa [MvPolynomial.constantCoeff_eq] using mvPolynomialToLaurent_apply_mapRange P 0

/-- Passing from polynomials to Laurent polynomials is injective. -/
theorem mvPolynomialToLaurent_injective :
    Function.Injective (mvPolynomialToLaurent σ S) :=
  Finsupp.mapDomain_injective mapRange_natCast_injective

/-- Every exponent vector in the support of a polynomial, seen as a Laurent polynomial, is
nonnegative. -/
theorem nonneg_of_mem_support_mvPolynomialToLaurent {P : MvPolynomial σ S} {f : σ →₀ ℤ}
    (hf : f ∈ (mvPolynomialToLaurent σ S P).support) (i : σ) : 0 ≤ f i := by
  classical
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hf)
  simp

/-- A Laurent polynomial all of whose exponent vectors are nonnegative is a polynomial. -/
theorem exists_eq_mvPolynomialToLaurent {L : AddMonoidAlgebra S (σ →₀ ℤ)}
    (hL : ∀ f ∈ L.support, ∀ i, 0 ≤ f i) :
    ∃ M : MvPolynomial σ S, L = mvPolynomialToLaurent σ S M := by
  refine ⟨Finsupp.comapDomain _ L mapRange_natCast_injective.injOn,
    (Finsupp.mapDomain_comapDomain _ mapRange_natCast_injective L fun f hf => ?_).symm⟩
  refine ⟨f.mapRange Int.toNat (by simp), Finsupp.ext fun i => ?_⟩
  simp [Int.toNat_of_nonneg (hL f hf i)]

/-- **A Laurent polynomial whose product with a polynomial is a polynomial.** Let `P` and `Q` be
polynomials over a semiring without zero divisors, the constant term of `Q` being nonzero, and
let `L` be a Laurent polynomial with `P = Q L`. Then `L` is a polynomial, and the constant
terms satisfy `Q(0) L(0) = P(0)`. -/
@[cluster_algebras "lem_laurent_implies_poly"]
theorem exists_eq_mvPolynomialToLaurent_of_eq_mul [NoZeroDivisors S] {P Q : MvPolynomial σ S}
    (hQ : MvPolynomial.constantCoeff Q ≠ 0) {L : AddMonoidAlgebra S (σ →₀ ℤ)}
    (h : mvPolynomialToLaurent σ S P = mvPolynomialToLaurent σ S Q * L) :
    ∃ M : MvPolynomial σ S, L = mvPolynomialToLaurent σ S M ∧
      MvPolynomial.constantCoeff Q * MvPolynomial.constantCoeff M =
        MvPolynomial.constantCoeff P := by
  obtain ⟨M, rfl⟩ := exists_eq_mvPolynomialToLaurent fun f hf i =>
    AddMonoidAlgebra.nonneg_of_mem_support_of_mul (D := Finsupp.applyAddHom i)
      (Q := mvPolynomialToLaurent σ S Q)
      (fun g hg => nonneg_of_mem_support_mvPolynomialToLaurent hg i)
      ⟨0, by simpa [Finsupp.mem_support_iff, mvPolynomialToLaurent_apply_zero] using hQ, rfl⟩
      (fun f hf => nonneg_of_mem_support_mvPolynomialToLaurent (h.symm ▸ hf) i) hf
  refine ⟨M, rfl, ?_⟩
  rw [← map_mul, mvPolynomialToLaurent_injective (h.trans (map_mul _ _ _).symm)]

end MvLaurent

section Laurent

open Polynomial LaurentPolynomial

variable {S : Type*} [Semiring S]

/-- Every exponent in the support of a polynomial, seen as a Laurent polynomial, is
nonnegative. -/
theorem nonneg_of_mem_support_toLaurent {P : S[X]} {n : ℤ} (hn : n ∈ P.toLaurent.support) :
    0 ≤ n := by
  rw [toLaurent_support] at hn
  obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 hn
  simp

/-- A Laurent polynomial all of whose exponents are nonnegative is a polynomial. -/
theorem exists_eq_toLaurent {L : S[T;T⁻¹]} (hL : ∀ n ∈ L.support, 0 ≤ n) :
    ∃ p : S[X], L = p.toLaurent := by
  refine ⟨.ofFinsupp (Finsupp.comapDomain _ L Nat.cast_injective.injOn), ?_⟩
  rw [toLaurent_apply]
  exact (Finsupp.mapDomain_comapDomain _ Nat.cast_injective L fun n hn =>
    ⟨n.toNat, Int.toNat_of_nonneg (hL n hn)⟩).symm

/-- **A Laurent polynomial whose product with a polynomial is a polynomial**, in one variable.
Let `P` and `Q` be polynomials over a semiring without zero divisors, the constant term of `Q`
being nonzero, and let `L` be a Laurent polynomial with `P = Q L`. Then `L` is a polynomial `p`,
and `Q(0) p(0) = P(0)`. -/
@[cluster_algebras "lem_laurent_implies_poly"]
theorem exists_eq_toLaurent_of_eq_mul [NoZeroDivisors S] {P Q : S[X]} (hQ : Q.coeff 0 ≠ 0)
    {L : S[T;T⁻¹]} (h : P.toLaurent = Q.toLaurent * L) :
    ∃ p : S[X], L = p.toLaurent ∧ Q.coeff 0 * p.coeff 0 = P.coeff 0 := by
  obtain ⟨p, rfl⟩ := exists_eq_toLaurent fun n hn =>
    AddMonoidAlgebra.nonneg_of_mem_support_of_mul (D := AddMonoidHom.id ℤ) (Q := Q.toLaurent)
      (fun g hg => nonneg_of_mem_support_toLaurent hg)
      ⟨0, by simpa [toLaurent_support] using hQ, rfl⟩
      (fun f hf => nonneg_of_mem_support_toLaurent (h.symm ▸ hf)) hn
  refine ⟨p, rfl, ?_⟩
  rw [← mul_coeff_zero, toLaurent_injective (h.trans (map_mul _ _ _).symm)]

end Laurent

end ClusterAlgebras
