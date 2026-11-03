/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.Definitions
public import ClusterAlgebras.MatrixMutation
public import ClusterAlgebras.TypeD.Matrix

/-!
# Flips of tagged triangulations of a once-punctured polygon

Two facts about tagged triangulations of a once-punctured `n`-gon: every tagged triangulation is
reached from the radius triangulation by a sequence of flips, and a flip mutates the extended
exchange matrix `B̃•(T)`, including its rows `λ, λ̄`. Both are exercises of [FWZ, Section 5.4];
each is a hypothesis `def` carrying its citation.

## Main definitions

* `ReflTransGenDFlipRadiusTriangulation`: every tagged triangulation is reached from
  `radiusTriangulation n` by a sequence of flips.
* `LabelledMatrixDFlip`: the labelled matrix of a flip in direction `k` is the mutation in
  direction `k` of the labelled matrix.

## Implementation notes

Both are stated with the definitions of `ClusterAlgebras.TypeD.Triangulation` and
`ClusterAlgebras.TypeD.Matrix`, as `Prop`s that the results depending on them take as explicit
hypotheses.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras.TypeD

variable {n : ℕ} [NeZero n]

/-- **Every tagged triangulation is reached from the radius triangulation by flips.** For `3 ≤ n`
and every tagged triangulation `T` there are tagged triangulations
`radiusTriangulation n = T₀, T₁, …, T_r = T` such that each `Tᵢ` is the flip of `Tᵢ₋₁` at some
element of `Tᵢ₋₁`.

This is FWZ's exercise that any two tagged triangulations of `P_n^•` are connected via a sequence
of flips (Section 5.4), in the special case of the radius triangulation, which is equivalent since
flips can be reversed. -/
@[cluster_algebras "lem_D_connected"]
def ReflTransGenDFlipRadiusTriangulation : Prop :=
  ∀ {n : ℕ} [NeZero n] (_ : 3 ≤ n) {T : Finset (TaggedArc n)} (_ : IsTaggedTriangulation T),
    Relation.ReflTransGen
      (fun T₁ T₂ : Finset (TaggedArc n) => ∃ γ γ', IsDFlipReplacement T₁ γ γ' ∧ T₂ = dFlip T₁ γ γ')
      (radiusTriangulation n) T

attribute [cluster_algebras "lem_D_flip_mutation"] ClusterAlgebras.TypeD.LabelledMatrixDFlip

end ClusterAlgebras.TypeD
