/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.MutationTransport
public import ClusterAlgebras.Plabic.BivalentMoves
public import ClusterAlgebras.Plabic.EdgeContractionMoves
public import ClusterAlgebras.Plabic.LocalMoves
public import ClusterAlgebras.Plabic.SquareQuiver

/-!
# Local moves and mutations of the quiver of a plabic graph

Let `G'` be obtained from a plabic graph `G` by a local move. If the move is a square move at an
internal face `q = (c₁, c₂, c₃, c₄)`, assume moreover that for each `k` (modulo `4`) the faces to
the left of `c_k` and of `c_{k+1}` are distinct. Then the quivers `Q(G)` and `Q(G')` are mutation
equivalent.

For a square move, `Q(G')` is isomorphic to the quiver of the square move `G_q`, which is the
mutation `μ_q(Q(G))`; so the mutation path of length one at `q` has a result isomorphic to `Q(G')`.
For the removal or insertion of a bivalent vertex and for the contraction or splitting of an edge,
`Q(G)` and `Q(G')` are already isomorphic, and the mutation path of length zero serves.

## Main results

* `ClusterAlgebras.PlabicGraph.mutationEquivalent_quiver_of_squareMove`: a square move at a face
  whose consecutive left faces are distinct gives mutation-equivalent quivers.
* `ClusterAlgebras.PlabicGraph.IsLocalMove.mutationEquivalent_quiver`: a local move gives
  mutation-equivalent quivers.

## Implementation notes

* The face `q = (c₁, c₂, c₃, c₄)` of a square move is given by its first dart `c = c₁`, with
  `c_{k+1} = squareCorner c k` for the `0`-indexed `k : Fin 4`, as in
  `ClusterAlgebras.Plabic.SquareMove`. A local move of type (M1) only asserts that some
  square move of `G` is isomorphic to `G'`; the hypothesis on the left faces concerns the square
  move being performed, so for (M1) the statement asks for a face `c` at which `G'` is (up to
  isomorphism) the square move and at which the left faces are distinct.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicGraph

variable {b : ℕ} {G G' : PlabicGraph b}

/-- If `G'` is isomorphic to the square move of the plabic graph `G` at a face
`q = (c₁, c₂, c₃, c₄)` with `c₁ = c`, and for each `k` the faces to the left of `c_k` and of
`c_{k+1}` are distinct, then `Q(G)` and `Q(G')` are mutation equivalent. -/
@[cluster_algebras "prop_plabic_moves_mutation"]
theorem mutationEquivalent_quiver_of_squareMove {c : G.Dart} (hq : G.data.IsSquareMoveFace c)
    (hF : ∀ k, G.data.leftFace (G.data.squareCorner c k) ≠
      G.data.leftFace (G.data.squareCorner c (k + 1)))
    (h : G'.data.Isomorphic (G.data.squareMove c)) :
    G.data.quiver.MutationEquivalent G'.data.quiver := by
  obtain ⟨θ⟩ := h
  let q : G.data.faces :=
    ⟨G.data.faceOf c, (G.data.mem_internalFaces.1 hq.faceOf_mem_internalFaces).1⟩
  have hk := hq.notMem_frozen_quiver (q := q) rfl
  have e : (G.data.quiver.mutate hk).Iso G'.data.quiver :=
    hq.quiver_squareMove G.isPlabicGraph hF (q := q) rfl ▸ θ.quiverIso.symm
  exact ⟨.cons hk (.nil _), ⟨e⟩⟩

/-- If `G'` is isomorphic to the removal of a bivalent vertex of `G`, then `Q(G)` and `Q(G')` are
isomorphic. -/
private theorem nonempty_quiverIso_of_isBivalentRemoval (h : G.IsBivalentRemoval G') :
    Nonempty (G.data.quiver.Iso G'.data.quiver) := by
  obtain ⟨d, hd, ⟨θ⟩⟩ := h
  obtain ⟨e, -⟩ := PlabicData.exists_quiverIso_bivalentRemoval G.isPlabicGraph hd
  exact ⟨e.trans θ.quiverIso.symm⟩

/-- If `G'` is isomorphic to the contraction of `G` along an edge, then `Q(G)` and `Q(G')` are
isomorphic. -/
private theorem nonempty_quiverIso_of_isEdgeContraction {d : G.Dart}
    (h : G.IsEdgeContraction G' d) : Nonempty (G.data.quiver.Iso G'.data.quiver) := by
  obtain ⟨he, ⟨θ⟩⟩ := h
  obtain ⟨e, -⟩ := PlabicData.exists_quiverIso_contractEdge G.isPlabicGraph he
  exact ⟨e.trans θ.quiverIso.symm⟩

/-- Let `G'` be obtained from the plabic graph `G` by a local move of type `t`. If the move is a
square move (type (M1)) at `q = (c₁, c₂, c₃, c₄)`, assume moreover that for each `k` the faces to
the left of `c_k` and of `c_{k+1}` are distinct; that is, `G'` is isomorphic to the square move of
`G` at a face `c` with this property. Then `Q(G)` and `Q(G')` are mutation equivalent. -/
@[cluster_algebras "prop_plabic_moves_mutation"]
theorem IsLocalMove.mutationEquivalent_quiver {t : LocalMoveType} (h : IsLocalMove t G G')
    (hsq : t = .m1 → ∃ c : G.Dart, G.data.IsSquareMoveFace c ∧
      (∀ k, G.data.leftFace (G.data.squareCorner c k) ≠
        G.data.leftFace (G.data.squareCorner c (k + 1))) ∧
      G'.data.Isomorphic (G.data.squareMove c)) :
    G.data.quiver.MutationEquivalent G'.data.quiver := by
  cases t with
  | m1 =>
    obtain ⟨c, hq, hF, hc⟩ := hsq rfl
    exact mutationEquivalent_quiver_of_squareMove hq hF hc
  | m2 =>
    rcases h with h | h
    · exact .of_iso (nonempty_quiverIso_of_isBivalentRemoval h).some
    · exact .of_iso (nonempty_quiverIso_of_isBivalentRemoval h).some.symm
  | m3 =>
    rcases h with ⟨d, h⟩ | ⟨d, h⟩
    · exact .of_iso (nonempty_quiverIso_of_isEdgeContraction h).some
    · exact .of_iso (nonempty_quiverIso_of_isEdgeContraction h).some.symm

end PlabicGraph

end ClusterAlgebras
