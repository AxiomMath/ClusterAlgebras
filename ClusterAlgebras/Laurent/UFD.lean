/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Laurent.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Integer Laurent polynomials in algebraically independent elements form a UFD

Let `F` be a field of characteristic zero and `ỹ` a tuple of elements of `F` algebraically
independent over `ℚ`. Then `ℤ[ỹ^{±1}]` is a unique factorization domain, so each of its
irreducible elements is prime.

Evaluation at `ỹ` identifies the polynomial ring `ℤ[Y]` with `ℤ[ỹ]`, and `ℤ[ỹ^{±1}]` is its
localization at the elements that become units, among them the variables. The polynomial ring
is a unique factorization domain, and so is each of its localizations at a submonoid of
non-zero-divisors: the image of a prime is a unit if the prime divides an element of the
submonoid, and is again prime otherwise.

## Main results

* `ClusterAlgebras.IsLocalization.uniqueFactorizationMonoid`: a localization of a unique
  factorization monoid at a submonoid of non-zero-divisors, which is a domain, is a unique
  factorization monoid.
* `ClusterAlgebras.laurentSubring_uniqueFactorizationMonoid`: `ℤ[ỹ^{±1}]` is a unique
  factorization domain.
* `ClusterAlgebras.prime_of_irreducible_laurentSubring`: every irreducible element of
  `ℤ[ỹ^{±1}]` is prime.

## Implementation notes

FWZ index the tuple by `[1, m]`; here the index type is arbitrary. The argument only
uses algebraic independence over `ℤ`, which is
`ClusterAlgebras.laurentSubring_uniqueFactorizationMonoid_of_int` and holds in any
characteristic; independence over `ℚ` in characteristic zero implies it.

The ring `ℤ[ỹ^{±1}]` is identified with the localization of `ℤ[Y]` at the submonoid of
polynomials whose value at `ỹ` is a unit of `ℤ[ỹ^{±1}]`, rather than at the submonoid generated
by the variables: the two localizations agree, and the first choice makes the universal
property apply without further work.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras*, Chapter 3.
-/

@[expose] public section

namespace ClusterAlgebras

section Localization

variable {R : Type*} [CommRing R] {M : Submonoid R} {A : Type*} [CommRing A] [Algebra R A]
  [IsLocalization M A]

/-- In a localization at a submonoid of non-zero-divisors, the image of a prime element is
prime or a unit: a unit when the prime divides an element of the submonoid, prime otherwise. -/
theorem IsLocalization.prime_or_isUnit_algebraMap (hM : M ≤ nonZeroDivisors R) {p : R}
    (hp : Prime p) : Prime (algebraMap R A p) ∨ IsUnit (algebraMap R A p) := by
  by_cases h : ∃ m ∈ M, p ∣ m
  · obtain ⟨m, hm, hpm⟩ := h
    exact .inr <| isUnit_of_dvd_unit (map_dvd _ hpm) (IsLocalization.map_units A ⟨m, hm⟩)
  · refine .inl ?_
    have hne : algebraMap R A p ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R A), (IsLocalization.injective A hM).eq_iff]
      exact hp.ne_zero
    rw [← Ideal.span_singleton_prime hne, ← Set.image_singleton, ← Ideal.map_span]
    refine IsLocalization.isPrime_of_isPrime_disjoint M A _
      ((Ideal.span_singleton_prime hp.ne_zero).2 hp) ?_
    rw [Set.disjoint_left]
    exact fun m hm hm' => h ⟨m, hm, Ideal.mem_span_singleton.1 hm'⟩

variable [UniqueFactorizationMonoid R] [IsDomain A]

/-- A localization of a unique factorization monoid at a submonoid of non-zero-divisors is a
unique factorization monoid, provided it is a domain. -/
theorem IsLocalization.uniqueFactorizationMonoid (hM : M ≤ nonZeroDivisors R) :
    UniqueFactorizationMonoid A := by
  have key (r : R) : r ≠ 0 → ∃ f : Multiset A, (∀ b ∈ f, Prime b) ∧
      Associated f.prod (algebraMap R A r) := by
    induction r using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact fun h => absurd rfl h
    | h₂ x hx => exact fun _ => ⟨0, by simp, (associated_one_iff_isUnit.2 (hx.map _)).symm⟩
    | h₃ x p hx hp ih =>
      intro _
      obtain ⟨f, hf, hfx⟩ := ih hx
      rcases IsLocalization.prime_or_isUnit_algebraMap (A := A) hM hp with hp' | hp'
      · refine ⟨algebraMap R A p ::ₘ f, ?_, ?_⟩
        · simpa using ⟨hp', hf⟩
        · rw [Multiset.prod_cons, map_mul]
          exact hfx.mul_left _
      · refine ⟨f, hf, ?_⟩
        rw [map_mul]
        exact hfx.trans (associated_unit_mul_left _ _ hp').symm
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun a ha => ?_
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj M a
  have hs := IsLocalization.map_units A s
  have hr : r ≠ 0 := by
    rintro rfl
    rw [map_zero, hs.mul_left_eq_zero] at hrs
    exact ha hrs
  obtain ⟨f, hf, hfr⟩ := key r hr
  exact ⟨f, hf, hfr.trans (hrs ▸ associated_mul_unit_left a _ hs)⟩

end Localization

variable {F ι : Type*} [Field F] {y : ι → F}

open MvPolynomial in
/-- If the entries of `y` are algebraically independent over `ℤ`, then `ℤ[ỹ^{±1}]` is a unique
factorization domain. -/
theorem laurentSubring_uniqueFactorizationMonoid_of_int (hy : AlgebraicIndependent ℤ y) :
    UniqueFactorizationMonoid (laurentSubring y) := by
  let φ : MvPolynomial ι ℤ →+* laurentSubring y :=
    (aeval fun i => (⟨y i, mem_laurentSubring y i⟩ : laurentSubring y)).toRingHom
  have hφ : (laurentSubring y).subtype.comp φ = (aeval y).toRingHom :=
    ringHom_ext (fun r => by simp [φ]) fun i => by simp [φ]
  have φinj : Function.Injective φ := by
    intro p q h
    apply algebraicIndependent_iff_injective_aeval.1 hy
    have := congr_arg (laurentSubring y).subtype h
    rwa [← RingHom.comp_apply, ← RingHom.comp_apply, hφ] at this
  let M := (IsUnit.submonoid (laurentSubring y)).comap φ
  have hM : M ≤ nonZeroDivisors (MvPolynomial ι ℤ) :=
    le_nonZeroDivisors_of_noZeroDivisors fun h => by simp [M, IsUnit.mem_submonoid_iff] at h
  have := IsLocalization.isDomain_localization hM
  let ψ : Localization M →+* laurentSubring y :=
    IsLocalization.lift (M := M) (S := Localization M) (g := φ) fun m => m.2
  have ψinj : Function.Injective ψ := (IsLocalization.lift_injective_iff _).2 fun p q =>
    (IsLocalization.injective _ hM).eq_iff.trans φinj.eq_iff.symm
  have ψX (i : ι) :
      ψ (algebraMap _ _ (X i : MvPolynomial ι ℤ)) = ⟨y i, mem_laurentSubring y i⟩ := by
    simp [ψ, φ]
  have ψsurj : Function.Surjective ψ := by
    have hle : laurentSubring y ≤ ψ.range.map (laurentSubring y).subtype := by
      refine laurentSubring_le fun i => ⟨⟨_, ⟨_, ψX i⟩, rfl⟩, ?_⟩
      have hXi : X i ∈ M := by
        simpa [M, IsUnit.mem_submonoid_iff, φ] using isUnit_mem_laurentSubring y (hy.ne_zero i)
      set u := (IsLocalization.map_units (Localization M) (⟨X i, hXi⟩ : M)).unit
      refine ⟨ψ ↑u⁻¹, ⟨_, rfl⟩, ?_⟩
      have h1 : ψ ↑u⁻¹ * ψ ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      rw [IsUnit.unit_spec, ψX] at h1
      exact eq_inv_of_mul_eq_one_left (congr_arg Subtype.val h1)
    intro z
    obtain ⟨x, ⟨w, rfl⟩, hw⟩ := Subring.mem_map.1 (hle z.2)
    exact ⟨w, Subtype.ext hw⟩
  exact (RingEquiv.ofBijective ψ ⟨ψinj, ψsurj⟩).toMulEquiv.uniqueFactorizationMonoid
    (IsLocalization.uniqueFactorizationMonoid hM)

/-- **`ℤ[ỹ^{±1}]` is a unique factorization domain.** If `F` has characteristic zero and the
entries of `y` are algebraically independent over `ℚ`, then the ring of integer Laurent
polynomials in `y` is a unique factorization domain. -/
@[cluster_algebras "lem_laurent_subring_ufd"]
theorem laurentSubring_uniqueFactorizationMonoid [CharZero F]
    (hy : AlgebraicIndependent ℚ y) : UniqueFactorizationMonoid (laurentSubring y) :=
  laurentSubring_uniqueFactorizationMonoid_of_int (hy.restrictScalars Int.cast_injective)

/-- Every irreducible element of `ℤ[ỹ^{±1}]` is prime, when `F` has characteristic zero and the
entries of `y` are algebraically independent over `ℚ`. -/
@[cluster_algebras "lem_laurent_subring_ufd"]
theorem prime_of_irreducible_laurentSubring [CharZero F] (hy : AlgebraicIndependent ℚ y)
    {p : laurentSubring y} (hp : Irreducible p) : Prime p :=
  have := laurentSubring_uniqueFactorizationMonoid hy
  UniqueFactorizationMonoid.irreducible_iff_prime.1 hp

end ClusterAlgebras
