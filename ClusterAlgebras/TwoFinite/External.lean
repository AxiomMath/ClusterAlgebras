/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.Definitions
public import ClusterAlgebras.TwoFinite.Defs

/-!
# Exercises of FWZ's Section 5.10 on `2`-finite diagrams

Three exercises of [FWZ, Chapter 5], each stated as a hypothesis `def`: the crown `S^s_{p,q,r}` is
mutation equivalent to the tree `T_{p+r-1,q,s}`; a chordless cycle of a `2`-finite matrix is
cyclically oriented with weights in `L_m`; and the square with weights `(2, 1, 2, 1)` mutates to a
path of type `F₄`.

## Main results

* `ExistsIsTShapeMatrixMutationListOfIsCrownShape`: a skew-symmetrizable matrix of crown
  shape `S^s_{p,q,r}` has a mutation of shape `T_{p+r-1,q,s}`.
* `IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite`: a chordless cycle of a `2`-finite
  matrix is cyclically oriented, with admissible cycle weights.
* `IsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne`: the oriented square with
  weights `(2, 1, 2, 1)` mutates to an induced path with weights `(1, 2, 1)`.

## Implementation notes

The statement that oriented unit cycles are not `2`-finite is not assumed: it is the case
`p = q = r = 1` of `ExistsIsTShapeMatrixMutationListOfIsCrownShape`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 5.
-/

@[expose] public section

namespace ClusterAlgebras

attribute [cluster_algebras "lem_crown"]
    ClusterAlgebras.ExistsIsTShapeMatrixMutationListOfIsCrownShape
attribute [cluster_algebras "lem_cycle_diagrams"]
    ClusterAlgebras.IsChordlessCycle.IsCyclicallyOrientedOfIsTwoFinite
attribute [cluster_algebras "lem_cycle_diagrams"]
    ClusterAlgebras.IsInducedPathMatrixMutationListOfCycleWeightsEqTwoOne

end ClusterAlgebras
