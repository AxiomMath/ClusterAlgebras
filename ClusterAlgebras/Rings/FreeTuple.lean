/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.ClusterAlgebra

/-!
# Free generating tuples

Two facts about free generating tuples (`ClusterAlgebras.IsFreeGeneratingTuple`), following
[FWZ, Chapter 6]. First, an `m`-tuple generating a field `K` of transcendence degree `m` over `𝕜`
is automatically algebraically independent, hence a free generating tuple. Second, a free
generating `m`-tuple `x̃` of `F` identifies `F` with the field of rational functions
`𝕜(X₁, …, Xₘ)`, sending `Xᵢ` to `xᵢ`; so free generating `m`-tuples `x̃` of `F` and `ỹ` of `K`
determine exactly one `𝕜`-algebra isomorphism `θ : F ≃ K` with `θ(xᵢ) = yᵢ`.

## Main definitions

* `ClusterAlgebras.IsFreeGeneratingTuple.fractionRingEquiv`: the isomorphism
  `𝕜(X₁, …, Xₘ) ≃ F`, `Xᵢ ↦ xᵢ`, for a free generating tuple `x̃` of `F`.
* `ClusterAlgebras.IsFreeGeneratingTuple.algEquiv`: the isomorphism `F ≃ K`, `xᵢ ↦ yᵢ`, for free
  generating tuples `x̃` of `F` and `ỹ` of `K`.

## Main results

* `ClusterAlgebras.isFreeGeneratingTuple_of_trdeg_eq`: a generating `m`-tuple of a field of
  transcendence degree `m` is free.
* `ClusterAlgebras.IsFreeGeneratingTuple.existsUnique_algEquiv`: free generating tuples determine
  a unique field isomorphism.

## Implementation notes

[FWZ] takes `𝕜` of characteristic zero; neither result uses it, so it is not assumed. The field
of rational functions `𝕜(X₁, …, Xₘ)` is `FractionRing (MvPolynomial (Fin m) 𝕜)`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

open MvPolynomial

variable {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] {m : ℕ}

/-- **A generating tuple of the right length is free.** If `K` has transcendence degree `m` over
`k` and the `m`-tuple `y` generates `K` as a field over `k`, then `y` is a free generating tuple
of `K` over `k`. -/
@[cluster_algebras "lem_generating_tuple_free"]
theorem isFreeGeneratingTuple_of_trdeg_eq (h : Algebra.trdeg k K = m) {y : Fin m → K}
    (hy : IntermediateField.adjoin k (Set.range y) = ⊤) : IsFreeGeneratingTuple k y := by
  have := isAlgebraic_adjoin_of_adjoin_eq_top hy
  refine ⟨(Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k y ?_).1, hy⟩
  simp [h]

/-- Two `k`-algebra homomorphisms out of a field generated over `k` by a family `x` are equal as
soon as they agree on the entries of `x`. -/
theorem algHom_ext_of_adjoin_range_eq_top {ι A : Type*} [Semiring A] [Algebra k A] {x : ι → F}
    (hx : IntermediateField.adjoin k (Set.range x) = ⊤) ⦃φ₁ φ₂ : F →ₐ[k] A⦄
    (h : ∀ i, φ₁ (x i) = φ₂ (x i)) : φ₁ = φ₂ := by
  have h' : φ₁.comp (IntermediateField.topEquiv (F := k) (E := F)).toAlgHom =
      φ₂.comp (IntermediateField.topEquiv (F := k) (E := F)).toAlgHom :=
    IntermediateField.algHom_ext_of_eq_adjoin k hx.symm (by rintro _ ⟨i, rfl⟩; simpa using h i)
  ext a
  simpa using DFunLike.congr_fun h' ⟨a, IntermediateField.mem_top⟩

namespace IsFreeGeneratingTuple

/-- The `k`-algebra isomorphism `k(X₁, …, Xₘ) ≃ F` sending `Xᵢ` to `xᵢ`, for a free generating
tuple `x` of `F` over `k`. -/
noncomputable def fractionRingEquiv {x : Fin m → F} (hx : IsFreeGeneratingTuple k x) :
    FractionRing (MvPolynomial (Fin m) k) ≃ₐ[k] F :=
  hx.1.aevalEquivField.trans
    ((IntermediateField.equivOfEq hx.2).trans IntermediateField.topEquiv)

/-- `fractionRingEquiv` evaluates a polynomial at `x`. -/
@[simp]
theorem fractionRingEquiv_algebraMap {x : Fin m → F} (hx : IsFreeGeneratingTuple k x)
    (p : MvPolynomial (Fin m) k) :
    hx.fractionRingEquiv (algebraMap _ _ p) = aeval x p := by
  simp [fractionRingEquiv]

/-- `fractionRingEquiv` sends `Xᵢ` to `xᵢ`. -/
theorem fractionRingEquiv_algebraMap_X {x : Fin m → F} (hx : IsFreeGeneratingTuple k x)
    (i : Fin m) : hx.fractionRingEquiv (algebraMap _ _ (X i : MvPolynomial (Fin m) k)) = x i := by
  simp

/-- The `k`-algebra isomorphism `F ≃ K` sending `xᵢ` to `yᵢ`, for free generating tuples `x` of
`F` and `y` of `K` over `k`. -/
noncomputable def algEquiv {x : Fin m → F} {y : Fin m → K} (hx : IsFreeGeneratingTuple k x)
    (hy : IsFreeGeneratingTuple k y) : F ≃ₐ[k] K :=
  hx.fractionRingEquiv.symm.trans hy.fractionRingEquiv

/-- `algEquiv` sends `xᵢ` to `yᵢ`. -/
@[simp]
theorem algEquiv_apply {x : Fin m → F} {y : Fin m → K} (hx : IsFreeGeneratingTuple k x)
    (hy : IsFreeGeneratingTuple k y) (i : Fin m) : hx.algEquiv hy (x i) = y i := by
  rw [algEquiv, AlgEquiv.trans_apply, ← hx.fractionRingEquiv_algebraMap_X i,
    AlgEquiv.symm_apply_apply, fractionRingEquiv_algebraMap_X]

/-- **Free generating tuples determine a field isomorphism.** If `x` is a free generating
`m`-tuple of `F` and `y` one of `K`, both over `k`, then exactly one `k`-algebra isomorphism
`θ : F ≃ K` has `θ(xᵢ) = yᵢ` for every `i`. -/
@[cluster_algebras "lem_free_tuple_field_iso"]
theorem existsUnique_algEquiv {x : Fin m → F} {y : Fin m → K} (hx : IsFreeGeneratingTuple k x)
    (hy : IsFreeGeneratingTuple k y) : ∃! θ : F ≃ₐ[k] K, ∀ i, θ (x i) = y i := by
  refine ⟨hx.algEquiv hy, hx.algEquiv_apply hy, fun θ hθ => ?_⟩
  refine AlgEquiv.coe_algHom_injective (algHom_ext_of_adjoin_range_eq_top hx.2 fun i => ?_)
  simp [hθ]

end IsFreeGeneratingTuple

end ClusterAlgebras
