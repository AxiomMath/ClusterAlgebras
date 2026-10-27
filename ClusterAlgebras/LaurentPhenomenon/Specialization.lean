/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Laurent.Expansion
public import ClusterAlgebras.Semifield.Universal

/-!
# Specializing variables to one preserves Laurentness

Let `F` be a field of characteristic zero, `ỹ` a tuple in `F` algebraically independent over
`ℚ`, and `ψ : ℚ_sf(ỹ) → ℚ_sf(ỹ')` a semifield homomorphism sending some of the `yᵢ` to `1` and
the others to the entries of `ỹ'`. If `z ∈ ℚ_sf(ỹ)` is an integer Laurent polynomial in `ỹ`,
then `ψ(z)` is an integer Laurent polynomial in `ỹ'`.

Write `ỹ''` for the tuple of the `ψ(yᵢ)`. Each `ψ(yᵢ)` is a unit of `ℤ[ỹ'^{±1}]`, so there is a
ring homomorphism `ρ : ℤ[ỹ^{±1}] → ℤ[ỹ'^{±1}]` with `ρ(yᵢ) = ψ(yᵢ)`, and `ρ(P(ỹ)) = P(ỹ'')` for
every polynomial `P` with coefficients in `ℕ`. Choose nonzero `P, Q` with `Q(ỹ) z = P(ỹ)`.
Applying `ρ` gives `Q(ỹ'') ρ(z) = P(ỹ'')`; applying `ψ`, which preserves products and sums,
gives `Q(ỹ'') ψ(z) = P(ỹ'')`. As `Q(ỹ'') ≠ 0`, `ψ(z) = ρ(z)`.

## Main results

* `ClusterAlgebras.FZSemifieldHom.coe_apply_mem_laurentSubring`: if every `ψ(yᵢ)` is a unit of
  `ℤ[ỹ'^{±1}]`, then `ψ` sends `ℚ_sf(ỹ) ∩ ℤ[ỹ^{±1}]` into `ℤ[ỹ'^{±1}]`.
* `ClusterAlgebras.FZSemifieldHom.coe_apply_mem_laurentSubring_of_comp`: the same when `ψ`
  sends `y_{e(a)}` to `y'_a` for a map `e` of index sets and every other `yᵢ` to `1`.
* `ClusterAlgebras.FZSemifieldHom.coe_apply_mem_laurentSubring_subtype`: FWZ's statement,
  where `ỹ'` is the subfamily of the `yᵢ` with `i ∉ J`.

## Implementation notes

FWZ take `ψ : ℚ_sf(ỹ) → ℚ_sf(ỹ')` with `ỹ'` the subfamily of the `yᵢ`, `i ∉ J`, in the
same field `F`. The proof only uses that each `ψ(yᵢ)` and its inverse lie in `ℤ[ỹ'^{±1}]`, so the
general statement allows an arbitrary field `F'` of characteristic zero and an arbitrary tuple
`ỹ'` in `F'` algebraically independent over `ℚ`, related to `ỹ` by a map `e` of index sets with
`ψ(y_{e(a)}) = y'_a` and `ψ(yᵢ) = 1` off the range of `e`; injectivity of `e` is not needed. FWZ's
statement is the special case `F' = F`, `e` the inclusion of `{i | i ∉ J}`.

FWZ prove `Q(ỹ'') ≠ 0` by noting that it is the value at `ỹ'` of the nonzero polynomial
obtained from `Q` by setting the variables `Yᵢ`, `i ∈ J`, to `1`. Here `Q(ỹ'')` is the image
under `ψ` of `Q(ỹ)`, an element of `ℚ_sf(ỹ')`, which does not contain `0`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial FZSemifield

variable {F F' ι κ : Type*} [Field F] [Field F'] [CharZero F] [CharZero F'] {y : ι → F}
  {y' : κ → F'} [Fact (AlgebraicIndependent ℚ y)] [Fact (AlgebraicIndependent ℚ y')]

omit [CharZero F] in
/-- A subfamily of a family algebraically independent over `ℚ` is algebraically independent. -/
instance instFactAlgebraicIndependentSubtype {p : ι → Prop} :
    Fact (AlgebraicIndependent ℚ fun i : {i // p i} => y i) :=
  ⟨(Fact.out : AlgebraicIndependent ℚ y).comp Subtype.val Subtype.val_injective⟩

namespace FZSemifieldHom

section General

variable (ψ : FZSemifieldHom (universalSemifield y) (universalSemifield y'))

/-- **Specialization preserves Laurentness.** If a semifield homomorphism
`ψ : ℚ_sf(ỹ) → ℚ_sf(ỹ')` sends each `yᵢ` to a unit of `ℤ[ỹ'^{±1}]`, that is, to an element
which lies in `ℤ[ỹ'^{±1}]` together with its inverse, then it sends every element of
`ℚ_sf(ỹ) ∩ ℤ[ỹ^{±1}]` into `ℤ[ỹ'^{±1}]`. -/
theorem coe_apply_mem_laurentSubring
    (h : ∀ i, (ψ ⟨y i, mem_universalSemifield_self y i⟩ : F') ∈ laurentSubring y' ∧
      (ψ ⟨y i, mem_universalSemifield_self y i⟩ : F')⁻¹ ∈ laurentSubring y')
    {z : F} (hz : z ∈ universalSemifield y) (hzL : z ∈ laurentSubring y) :
    (ψ ⟨z, hz⟩ : F') ∈ laurentSubring y' := by
  set f : ι → universalSemifield y' := fun i => ψ ⟨y i, mem_universalSemifield_self y i⟩
  have hf : ∀ i, (f i : F') ≠ 0 := fun i => universalSemifield.coe_ne_zero Fact.out (f i)
  let w : ι → (laurentSubring y')ˣ := fun i =>
    ⟨⟨f i, (h i).1⟩, ⟨(f i : F')⁻¹, (h i).2⟩, Subtype.ext (mul_inv_cancel₀ (hf i)),
      Subtype.ext (inv_mul_cancel₀ (hf i))⟩
  let σ : laurentSubring y →+* F' := (laurentSubring y').subtype.comp (laurentLift Fact.out w)
  let g : ι → laurentSubring y := fun i => ⟨y i, mem_laurentSubring y i⟩
  have hσ (P : MvPolynomial ι ℕ) : σ (aeval g P) = aeval (fun i => (f i : F')) P := by
    refine (comp_aeval_apply (f := g) σ.toNatAlgHom P).trans (congrArg (aeval · P) ?_)
    ext i
    simp [σ, w, g]
  have hg (P : MvPolynomial ι ℕ) : ((aeval g P : laurentSubring y) : F) = aeval y P :=
    comp_aeval_apply (f := g) (laurentSubring y).subtype.toNatAlgHom P
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := hz
  have h₁ : aeval g Q * ⟨z, hzL⟩ = aeval g P := Subtype.ext (by
    rw [Subring.coe_mul, hg, hg, hPQ])
  have h₂ := congrArg σ h₁
  rw [map_mul, hσ, hσ] at h₂
  have hψz := congrArg Subtype.val (ψ.apply_of_mul_eq ⟨P, Q, hP, hQ, hPQ⟩ hP hQ hPQ)
  rw [universalSemifield.coe_div, universalSemifield.coe_polyValue _ hP,
    universalSemifield.coe_polyValue _ hQ] at hψz
  have hQ0 : aeval (fun i => (f i : F')) Q ≠ 0 := by
    rw [← universalSemifield.coe_polyValue _ hQ]
    exact universalSemifield.coe_ne_zero Fact.out _
  rw [hψz, ← h₂, mul_div_cancel_left₀ _ hQ0]
  exact (laurentLift Fact.out w ⟨z, hzL⟩).2

/-- **Specializing variables to one preserves Laurentness.** Let `ψ : ℚ_sf(ỹ) → ℚ_sf(ỹ')` be a
semifield homomorphism sending `y_{e(a)}` to `y'_a` for every `a`, and every `yᵢ` with `i` outside
the range of `e` to `1`. Then `ψ` sends every element of `ℚ_sf(ỹ) ∩ ℤ[ỹ^{±1}]` into
`ℤ[ỹ'^{±1}]`.

FWZ take `F' = F` and `e` the inclusion of the complement of a set `J` of indices, see
`FZSemifieldHom.coe_apply_mem_laurentSubring_subtype`; the proof does not use that `e` is
injective, so it is not assumed. -/
@[cluster_algebras "lem_specialization_laurent"]
theorem coe_apply_mem_laurentSubring_of_comp {e : κ → ι}
    (hψ : ∀ a, (ψ ⟨y (e a), mem_universalSemifield_self y (e a)⟩ : F') = y' a)
    (hψ₁ : ∀ i ∉ Set.range e, ψ ⟨y i, mem_universalSemifield_self y i⟩ = 1)
    {z : F} (hz : z ∈ universalSemifield y) (hzL : z ∈ laurentSubring y) :
    (ψ ⟨z, hz⟩ : F') ∈ laurentSubring y' := by
  refine ψ.coe_apply_mem_laurentSubring (fun i => ?_) hz hzL
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    rw [hψ]
    exact ⟨mem_laurentSubring y' a, inv_mem_laurentSubring y' a⟩
  · rw [hψ₁ i hi, universalSemifield.coe_one, inv_one]
    exact ⟨one_mem _, one_mem _⟩

end General

/-- **Specializing variables to one preserves Laurentness**, in FWZ's form. Let
`J` be a set of indices, `ỹ'` the subfamily of the `yᵢ` with `i ∉ J`, and
`ψ : ℚ_sf(ỹ) → ℚ_sf(ỹ')` a semifield homomorphism with `ψ(yᵢ) = 1` for `i ∈ J` and
`ψ(yᵢ) = yᵢ` for `i ∉ J`. If `z ∈ ℚ_sf(ỹ) ∩ ℤ[ỹ^{±1}]`, then `ψ(z) ∈ ℤ[ỹ'^{±1}]`. -/
@[cluster_algebras "lem_specialization_laurent"]
theorem coe_apply_mem_laurentSubring_subtype {J : Set ι}
    (ψ : FZSemifieldHom (universalSemifield y) (universalSemifield fun i : {i // i ∉ J} => y i))
    (hψ : ∀ i : {i // i ∉ J}, (ψ ⟨y i, mem_universalSemifield_self y i⟩ : F) = y i)
    (hψ₁ : ∀ i ∈ J, ψ ⟨y i, mem_universalSemifield_self y i⟩ = 1)
    {z : F} (hz : z ∈ universalSemifield y) (hzL : z ∈ laurentSubring y) :
    (ψ ⟨z, hz⟩ : F) ∈ laurentSubring fun i : {i // i ∉ J} => y i :=
  ψ.coe_apply_mem_laurentSubring_of_comp (e := Subtype.val) hψ
    (fun i hi => hψ₁ i (not_not.1 fun h => hi ⟨⟨i, h⟩, rfl⟩)) hz hzL

end FZSemifieldHom

end ClusterAlgebras
