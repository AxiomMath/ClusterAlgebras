/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Invariants of one-parameter substitutions in a factorial ring

Let `A` be an `R`-algebra and let `(Θ_λ)_{λ ∈ Λ}` be a family of `R`-algebra homomorphisms
`Θ_λ : A → A[t]` into the polynomial ring in one indeterminate, each of which is the identity
after evaluation at `t = 0`. The elements `f ∈ A` with `Θ_λ(f) = f` (a constant polynomial) for
every `λ` form an `R`-subalgebra `A^Θ` of `A`. When `A` is a domain, degrees in `t` add, so
every divisor of a nonzero element of `A^Θ` lies again in `A^Θ`; consequently, when `A` is
moreover factorial, so is `A^Θ`: the prime factors in `A` of an element of `A^Θ` lie in `A^Θ`
and remain prime there.

## Main definitions

* `ClusterAlgebras.fixedSubalgebra Θ`: the subalgebra `A^Θ` of elements `f` with
  `Θ_λ(f) = C f` for every `λ`.

## Main results

* `ClusterAlgebras.mem_fixedSubalgebra_of_mul_eq`: if `f ∈ A^Θ` is nonzero and `f = g h`, then
  `g ∈ A^Θ`.
* `ClusterAlgebras.uniqueFactorizationMonoid_fixedSubalgebra`: if `A` is a factorial domain,
  then so is `A^Θ`.

## Implementation notes

* FWZ work over `ℂ`; nothing uses it, so the base ring is an arbitrary commutative ring
  `R` (a commutative semiring for the definition and the divisor lemma).
* That `A^Θ` is a subring of `A` containing the scalars is the statement that it is an
  `R`-subalgebra, which is how it is defined; that it is a domain is then the instance making a
  subalgebra of a domain a domain.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open Polynomial

variable {R A Λ : Type*}

section Semiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The subalgebra `A^Θ` of elements `f ∈ A` fixed by every `Θ_λ : A → A[t]` of a family, that
is, with `Θ_λ(f) = C f` the constant polynomial `f`. -/
@[cluster_algebras "lem_invariant_divisors"]
def fixedSubalgebra (Θ : Λ → A →ₐ[R] A[X]) : Subalgebra R A where
  carrier := {f | ∀ l, Θ l f = C f}
  mul_mem' {f g} hf hg l := by simp [map_mul, hf l, hg l]
  add_mem' {f g} hf hg l := by simp [map_add, hf l, hg l]
  algebraMap_mem' r l := by simp [AlgHom.commutes, Polynomial.algebraMap_apply]

variable {Θ : Λ → A →ₐ[R] A[X]}

/-- `f` lies in `A^Θ` iff `Θ_λ(f) = C f` for every `λ`. -/
theorem mem_fixedSubalgebra {f : A} : f ∈ fixedSubalgebra Θ ↔ ∀ l, Θ l f = C f := Iff.rfl

/-- **Divisors of an invariant are invariant.** If every `Θ_λ` is the identity at `t = 0` and
`A` has no zero divisors, a factor `g` of a nonzero `f = g h ∈ A^Θ` lies in `A^Θ`. -/
@[cluster_algebras "lem_invariant_divisors"]
theorem mem_fixedSubalgebra_of_mul_eq [NoZeroDivisors A] (hΘ : ∀ l f, (Θ l f).eval 0 = f)
    {f g h : A} (hf : f ∈ fixedSubalgebra Θ) (hf0 : f ≠ 0) (hfgh : f = g * h) :
    g ∈ fixedSubalgebra Θ := by
  intro l
  have hprod : Θ l g * Θ l h = C f := by rw [← map_mul, ← hfgh, hf l]
  have hne : Θ l g * Θ l h ≠ 0 := hprod ▸ C_ne_zero.2 hf0
  have hdeg : (Θ l g).natDegree = 0 := by
    have := congrArg natDegree hprod
    rw [natDegree_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne), natDegree_C] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, coeff_zero_eq_eval_zero, hΘ]

/-- A divisor in `A` of a nonzero element of `A^Θ` lies in `A^Θ`. -/
theorem mem_fixedSubalgebra_of_dvd [NoZeroDivisors A] (hΘ : ∀ l f, (Θ l f).eval 0 = f)
    {f g : A} (hf : f ∈ fixedSubalgebra Θ) (hf0 : f ≠ 0) (hgf : g ∣ f) :
    g ∈ fixedSubalgebra Θ := by
  obtain ⟨h, rfl⟩ := hgf
  exact mem_fixedSubalgebra_of_mul_eq hΘ hf hf0 rfl

/-- Divisibility of a nonzero element in `A^Θ` is divisibility in `A`. -/
theorem fixedSubalgebra_dvd_iff [NoZeroDivisors A] (hΘ : ∀ l f, (Θ l f).eval 0 = f)
    {x y : fixedSubalgebra Θ} (hy : y ≠ 0) : (x : A) ∣ y ↔ x ∣ y := by
  refine ⟨fun ⟨v, hv⟩ => ?_, fun h => by exact_mod_cast map_dvd (fixedSubalgebra Θ).val h⟩
  have hy' : (y : A) ≠ 0 := by exact_mod_cast hy
  have hv' : v ∈ fixedSubalgebra Θ :=
    mem_fixedSubalgebra_of_dvd hΘ y.2 hy' ⟨x, by rw [hv, mul_comm]⟩
  exact ⟨⟨v, hv'⟩, Subtype.ext hv⟩

end Semiring

section Ring

variable [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]

/-- **Invariants of a factorial ring form a factorial ring.** If `A` is a factorial domain and
every `Θ_λ : A → A[t]` is the identity at `t = 0`, then the subalgebra `A^Θ` of `Θ`-invariants
(a subring of `A` containing the scalars, and a domain) is a unique factorization domain. -/
@[cluster_algebras "lem_invariant_ufd"]
theorem uniqueFactorizationMonoid_fixedSubalgebra [UniqueFactorizationMonoid A]
    {Θ : Λ → A →ₐ[R] A[X]} (hΘ : ∀ l f, (Θ l f).eval 0 = f) :
    UniqueFactorizationMonoid (fixedSubalgebra Θ) := by
  set S := fixedSubalgebra Θ
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun a ha => ?_
  have ha' : (a : A) ≠ 0 := by exact_mod_cast ha
  obtain ⟨s, hs, ⟨u, hu⟩⟩ := UniqueFactorizationMonoid.exists_prime_factors (a : A) ha'
  have hmem : ∀ p ∈ s, p ∈ S := fun p hp =>
    mem_fixedSubalgebra_of_dvd hΘ a.2 ha' <|
      (Multiset.dvd_prod hp).trans ⟨u, hu.symm⟩
  have hprime : ∀ p (hp : p ∈ s), Prime (⟨p, hmem p hp⟩ : S) := by
    intro p hp
    have hpA := hs p hp
    have hdvd : ∀ z : S, p ∣ (z : A) → (⟨p, hmem p hp⟩ : S) ∣ z := fun z hz => by
      obtain rfl | hz0 := eq_or_ne z 0
      exacts [dvd_zero _, (fixedSubalgebra_dvd_iff hΘ hz0).mp hz]
    refine ⟨fun h0 => hpA.ne_zero (congrArg Subtype.val h0),
      fun hunit => hpA.not_unit (hunit.map S.val),
      fun x y hxy => (hpA.dvd_or_dvd ?_).imp (hdvd x) (hdvd y)⟩
    exact_mod_cast map_dvd S.val hxy
  have huS : (u : A) ∈ S :=
    mem_fixedSubalgebra_of_dvd hΘ a.2 ha' ⟨s.prod, by rw [← hu, mul_comm]⟩
  have huinvS : ((u⁻¹ : Aˣ) : A) ∈ S :=
    mem_fixedSubalgebra_of_dvd hΘ S.one_mem one_ne_zero ⟨u, by simp⟩
  let uS : Sˣ := ⟨⟨u, huS⟩, ⟨_, huinvS⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  refine ⟨s.attach.map fun p => ⟨p.1, hmem p.1 p.2⟩, ?_, ⟨uS, ?_⟩⟩
  · simp only [Multiset.mem_map, Multiset.mem_attach, true_and, Subtype.exists]
    rintro b ⟨p, hp, rfl⟩
    exact hprime p hp
  · apply Subtype.ext
    rw [← hu]
    simp [uS]

end Ring

end ClusterAlgebras
