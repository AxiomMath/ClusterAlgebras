/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.Defs

/-!
# Exercises of FWZ's Section 5.10 on `2`-finite diagrams

Two exercises of [FWZ, Chapter 5] used in the classification of `2`-finite diagrams, each stated
as an `axiom`, so that `#print axioms` on a downstream result reports which of them it rests on:
the crown `S^s_{p,q,r}` is mutation equivalent to the tree `T_{p+r-1,q,s}`; a chordless cycle of
a `2`-finite matrix is cyclically oriented with weights in `L_m`; and the square with weights
`(2, 1, 2, 1)` mutates to a path of type `F₄`.

## Main results

* `exists_isTShape_matrixMutationList_of_isCrownShape`: a skew-symmetrizable matrix of crown
  shape `S^s_{p,q,r}` has a mutation of shape `T_{p+r-1,q,s}`.
* `IsChordlessCycle.isCyclicallyOriented_of_isTwoFinite`: a chordless cycle of a `2`-finite
  matrix is cyclically oriented, with admissible cycle weights.
* `isInducedPath_matrixMutationList_of_cycleWeights_eq_two_one`: the oriented square with
  weights `(2, 1, 2, 1)` mutates to an induced path with weights `(1, 2, 1)`.

## Implementation notes

The statement that oriented unit cycles are not `2`-finite is not assumed: it is the case
`p = q = r = 1` of `exists_isTShape_matrixMutationList_of_isCrownShape`, and is proved from it in
`ClusterAlgebras.TwoFinite.Cycles`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5.
-/


@[expose] public section

namespace ClusterAlgebras

/-- **The crown `S^s_{p,q,r}` is mutation equivalent to the tree `T_{p+r-1,q,s}`.** If the
skew-symmetrizable `N × N` integer matrix `B` is of crown shape `S^s_{p,q,r}`, then some
mutation `μ_t(B)` is of shape `T_{p+r-1,q,s}`.

This is an exercise of [FWZ, Section 5.10]. -/
@[cluster_algebras "lem_crown"]
axiom exists_isTShape_matrixMutationList_of_isCrownShape {N : ℕ}
    {B : Matrix (Fin N) (Fin N) ℤ} (hB : SkewSymmetrizable B) {s p q r : ℕ}
    (hS : IsCrownShape B s p q r) :
    ∃ t : List (Fin N), IsTShape (diagramWeight (matrixMutationList le_rfl B t)) (p + r - 1) q s

/-- **A chordless cycle of a `2`-finite cycle diagram is cyclically oriented, with weights in
`L_m`.** If `m ≥ 3`, `B` is a skew-symmetrizable `m × m` integer matrix, and the enumeration
`(v₁, …, v_m)` of `[1, m]` is a chordless cycle of `B`, then `B` `2`-finite implies that the
cycle is cyclically oriented and that its weights `(w₁, …, w_m)` lie in `L_m`.

This is part (a) of an exercise of [FWZ, Section 5.10]. -/
@[cluster_algebras "lem_cycle_diagrams"]
axiom IsChordlessCycle.isCyclicallyOriented_of_isTwoFinite {m : ℕ}
    {B : Matrix (Fin m) (Fin m) ℤ} {v : Fin m ≃ Fin m} (hv : IsChordlessCycle B v)
    (hB : IsTwoFinite B) :
    IsCyclicallyOriented B v ∧ IsAdmissibleCycleWeights (cycleWeights B v)

/-- **The square with weights `(2, 1, 2, 1)` mutates to a path of type `F₄`.** If
`(v₁, v₂, v₃, v₄)` is an enumeration of `[1, 4]` which is a chordless cycle of the
skew-symmetrizable `4 × 4` integer matrix `B`, with `v_p → v_{p+1}` for all `p` and weights
`(2, 1, 2, 1)`, then `(v₃, v₂, v₁, v₄)` is an induced path of `μ_{(v₁, v₂, v₁)}(B)` with weights
`(1, 2, 1)`.

This is part (c) of an exercise of [FWZ, Section 5.10]. -/
@[cluster_algebras "lem_cycle_diagrams"]
axiom isInducedPath_matrixMutationList_of_cycleWeights_eq_two_one
    {B : Matrix (Fin 4) (Fin 4) ℤ} (hB : SkewSymmetrizable B) {v : Fin 4 ≃ Fin 4}
    (hv : IsChordlessCycle B v) (hor : ∀ p, 0 < B (v p) (v (finRotate 4 p)))
    (hw : cycleWeights B v = ![2, 1, 2, 1]) :
    IsInducedPath (matrixMutationList le_rfl B [v 0, v 1, v 0]) ![v 2, v 1, v 0, v 3] ∧
      diagramWeight (matrixMutationList le_rfl B [v 0, v 1, v 0]) (v 2) (v 1) = 1 ∧
      diagramWeight (matrixMutationList le_rfl B [v 0, v 1, v 0]) (v 1) (v 0) = 2 ∧
      diagramWeight (matrixMutationList le_rfl B [v 0, v 1, v 0]) (v 0) (v 3) = 1

end ClusterAlgebras
