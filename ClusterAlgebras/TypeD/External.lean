/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Sorokin
-/
module

public import ClusterAlgebras.MatrixMutation
public import ClusterAlgebras.TypeD.Matrix

/-!
# Flips of tagged triangulations of a once-punctured polygon

Two facts about tagged triangulations of a once-punctured `n`-gon: every tagged triangulation is
reached from the radius triangulation by a sequence of flips, and a flip mutates the extended
exchange matrix `B̃•(T)`, including its rows `λ, λ̄`.

## Main results

* `reflTransGen_dFlip_radiusTriangulation`: every tagged triangulation is reached from
  `radiusTriangulation n` by a sequence of flips.
* `labelledMatrix_dFlip`: the labelled matrix of a flip in direction `k` is the mutation in
  direction `k` of the labelled matrix.

## Implementation notes

Both statements are exercises of [FWZ, Section 5.4] and are stated as axioms.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

variable {n : ℕ} [NeZero n]

/-- For `3 ≤ n`, every tagged triangulation `T` is reached from the radius triangulation by
flips: there are tagged triangulations `radiusTriangulation n = T₀, T₁, …, T_r = T` such that each
`Tᵢ` is the flip of `Tᵢ₋₁` at some element of `Tᵢ₋₁`. -/
@[cluster_algebras "lem_D_connected"]
axiom reflTransGen_dFlip_radiusTriangulation (hn : 3 ≤ n) {T : Finset (TaggedArc n)}
    (hT : IsTaggedTriangulation T) :
    Relation.ReflTransGen
      (fun T₁ T₂ : Finset (TaggedArc n) => ∃ γ γ', IsDFlipReplacement T₁ γ γ' ∧ T₂ = dFlip T₁ γ γ')
      (radiusTriangulation n) T

/-- Let `T` be a tagged triangulation with labelling `ℓ`, let `k : Fin n`, and let `γ'` be the
replacement of `ℓ k`. Then the labelled matrix of the flip with the flipped labelling is the
mutation in direction `k` of the labelled matrix of `T`: `B̃•(T', ℓ') = μ_k(B̃•(T, ℓ))`. -/
@[cluster_algebras "lem_D_flip_mutation"]
axiom labelledMatrix_dFlip (hn : 3 ≤ n) {T : Finset (TaggedArc n)} {ℓ : Fin n → TaggedArc n}
    (hℓ : IsLabelling T ℓ) {k : Fin n} {γ' : TaggedArc n} (h : IsDFlipReplacement T (ℓ k) γ') :
    labelledMatrix (dFlip T (ℓ k) γ') (flipLabelling ℓ k γ') =
      matrixMutation (le_two_mul_add_two n) (labelledMatrix T ℓ) k

end ClusterAlgebras.TypeD
