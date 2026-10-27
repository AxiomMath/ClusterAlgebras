/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Semifield.Universal

/-!
# Monotonicity of the universal semifield

Let `F` be a field of characteristic zero and `ỹ` a family of elements of `F` algebraically
independent over `ℚ`. If every entry of a family `ũ` lies in the universal semifield `ℚ_sf(ỹ)`,
then `ℚ_sf(ũ) ⊆ ℚ_sf(ỹ)`. Indeed `ℚ_sf(ỹ)` contains `1` and is closed under the product, the sum
and the inverse of `F`, so it contains the value `P(ũ)` of every nonzero polynomial `P` with
coefficients in `ℕ`, a nonempty sum of monomials with positive coefficients. If `Q(ũ) z = P(ũ)`,
then `Q(ũ) ∈ ℚ_sf(ỹ)` is nonzero, since `0 ∉ ℚ_sf(ỹ)`, and `z = P(ũ) Q(ũ)⁻¹ ∈ ℚ_sf(ỹ)`.

## Main results

* `ClusterAlgebras.aeval_mem_universalSemifield_of_forall_mem`: if every `uⱼ` lies in
  `ℚ_sf(ỹ)`, so does `P(u)` for every nonzero polynomial `P` with coefficients in `ℕ`.
* `ClusterAlgebras.universalSemifield_subset_of_forall_mem`: if every `uⱼ` lies in `ℚ_sf(ỹ)`,
  then `ℚ_sf(ũ) ⊆ ℚ_sf(ỹ)`.
* `ClusterAlgebras.universalSemifield_eq_of_forall_mem`: two algebraically independent families
  each of whose entries lies in the universal semifield of the other have the same universal
  semifield.

## Implementation notes

FWZ index both families by initial segments of the positive integers and assume
`ũ` algebraically independent over `ℚ`. Here they are indexed by arbitrary types, and the
inclusion does not assume `ũ` algebraically independent, since its proof never uses it. The
closure statement `aeval_mem_universalSemifield_of_forall_mem` needs neither characteristic zero
nor algebraic independence.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

variable {F ι κ : Type*} [Field F] {y : ι → F} {u : κ → F}

/-- If every entry `uⱼ` of a family `u` lies in `ℚ_sf(y)`, then so does the value `P(u)` of every
nonzero polynomial `P` with coefficients in `ℕ`. -/
theorem aeval_mem_universalSemifield_of_forall_mem (hu : ∀ j, u j ∈ universalSemifield y)
    {P : MvPolynomial κ ℕ} (hP : P ≠ 0) : aeval u P ∈ universalSemifield y := by
  rw [P.as_sum, map_sum]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => add_mem_universalSemifield)
    (support_nonempty.2 hP) fun s hs => ?_
  rw [aeval_monomial]
  refine mul_mem_universalSemifield ?_ (Finset.prod_induction _ _
    (fun _ _ => mul_mem_universalSemifield) one_mem_universalSemifield
    fun j _ => pow_mem_universalSemifield (hu j) _)
  simpa using aeval_mem_universalSemifield y (C_ne_zero.2 (mem_support_iff.1 hs))

/-- **Monotonicity of the universal semifield.** If `F` has characteristic zero, `y` is
algebraically independent over `ℚ` and every entry `uⱼ` of `u` lies in `ℚ_sf(y)`, then
`ℚ_sf(u) ⊆ ℚ_sf(y)`. -/
@[cluster_algebras "lem_universal_semifield_mono"]
theorem universalSemifield_subset_of_forall_mem [CharZero F] (hy : AlgebraicIndependent ℚ y)
    (hu : ∀ j, u j ∈ universalSemifield y) : universalSemifield u ⊆ universalSemifield y := by
  rintro z ⟨P, Q, hP, hQ, h⟩
  have hQy := aeval_mem_universalSemifield_of_forall_mem hu hQ
  have hQ0 : aeval u Q ≠ 0 := fun h0 => zero_notMem_universalSemifield hy (h0 ▸ hQy)
  rw [show z = aeval u P / aeval u Q from eq_div_of_mul_eq hQ0 (by rw [mul_comm, h])]
  exact div_mem_universalSemifield (aeval_mem_universalSemifield_of_forall_mem hu hP) hQy

/-- If `F` has characteristic zero, `y` and `u` are algebraically independent over `ℚ`, every
`uⱼ` lies in `ℚ_sf(y)` and every `yᵢ` lies in `ℚ_sf(u)`, then `ℚ_sf(u) = ℚ_sf(y)`. -/
theorem universalSemifield_eq_of_forall_mem [CharZero F] (hy : AlgebraicIndependent ℚ y)
    (hu : AlgebraicIndependent ℚ u) (huy : ∀ j, u j ∈ universalSemifield y)
    (hyu : ∀ i, y i ∈ universalSemifield u) : universalSemifield u = universalSemifield y :=
  (universalSemifield_subset_of_forall_mem hy huy).antisymm
    (universalSemifield_subset_of_forall_mem hu hyu)

end ClusterAlgebras
