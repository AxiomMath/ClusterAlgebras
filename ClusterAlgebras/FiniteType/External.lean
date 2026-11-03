/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.Definitions
public import ClusterAlgebras.External
public import ClusterAlgebras.PolygonTriangulation
public import ClusterAlgebras.QuiverOps
public import ClusterAlgebras.TreeOrientation

/-!
# Flips, tree orientations and mutations

Two exercises of Fomin–Williams–Zelevinsky, assumed as hypotheses: a flip of a triangulation of a
polygon is a mutation of its quiver, and any two orientations of a finite tree are joined by
mutations at sources and sinks.

## Main definitions

* `flipTriangulation`: The set of diagonals `(T \ {γ}) ∪ {γ'}` obtained from `T` by replacing
  `γ` with `γ'`.
* `IsFlipReplacement`: `γ'` replaces `γ` in a flip of the triangulation `T`.

## Main results

* `PolygonQuiverMutateIsoFlip`: The quiver of a flipped triangulation is isomorphic to the
  mutation of the original quiver at the flipped diagonal.
* `Quiver.ExistsMutationPathOfIsTreeOrientation`: Any two orientations of a finite tree are
  joined by a mutation path at sources and sinks.

## Implementation notes

Both results are exercises in FWZ and are stated as hypothesis `def`s, taken as explicit
arguments.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Flips are mutations -/

section Flip

variable {m : ℕ} [NeZero m]

attribute [cluster_algebras "def_flip"] ClusterAlgebras.flipTriangulation
attribute [cluster_algebras "def_flip"] ClusterAlgebras.IsFlipReplacement
attribute [cluster_algebras "lem_flip_is_mutation"] ClusterAlgebras.PolygonQuiverMutateIsoFlip
attribute [cluster_algebras "lem_tree_orientations_equivalent"]
    ClusterAlgebras.Quiver.ExistsMutationPathOfIsTreeOrientation

end Flip

/-! ### Orientations of a tree -/

universe u

end ClusterAlgebras
