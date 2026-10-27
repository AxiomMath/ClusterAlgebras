/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.StrandGlue
public import ClusterAlgebras.Plabic.NormalMoves

/-!
# Three descriptions of the same equivalence of normal plabic graphs

For normal plabic graphs `G` and `G'` the following are equivalent:

1. `G ∘∼ G'`, i.e. `G` and `G'` are related by local moves avoiding the contraction of an edge
   joining a white internal leaf to a white vertex with at least three darts;
2. `G` and `G'` are normal-move-equivalent (urban renewals and normal flips);
3. their triple diagrams are move-equivalent, `X(G) ∼ X(G')`.

The implication (2) ⇒ (1) is `NormalMoveEquivalent.circMoveEquivalent`, and (3) ⇒ (2) is
`normalMoveEquivalent_iff_moveEquivalent`. For (1) ⇒ (3): `X(G)` is a generalized triple diagram
of `G` that is a triple diagram, so by `CircMoveEquivalent.exists_moveEquivalent` the graph `G'`
has a generalized triple diagram `X'` that is a triple diagram with `X(G) ∼ X'`; and `X(G')` is a
generalized triple diagram of `G'`, so `X' ∼ X(G')` by the uniqueness of generalized triple
diagrams up to swivel moves, `PlabicData.IsGeneralizedTripleDiagram.exists_moveEquivalent`.

## Main results

* `ClusterAlgebras.PlabicGraph.CircMoveEquivalent.moveEquivalent_toTripleDiagram`: if `G ∘∼ G'`
  for normal plabic graphs, then `X(G) ∼ X(G')`.
* `ClusterAlgebras.PlabicGraph.tfae_circMoveEquivalent_normalMoveEquivalent_moveEquivalent`: the
  three relations agree on normal plabic graphs.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras, Chapter 7*.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicGraph

variable {b : ℕ}

/-- If `G` and `G'` are normal plabic graphs with `G ∘∼ G'`, then `X(G) ∼ X(G')`. -/
@[cluster_algebras "lem_circ_normal_swivel"]
theorem CircMoveEquivalent.moveEquivalent_toTripleDiagram {G G' : PlabicGraph b}
    (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph)
    (h : G.CircMoveEquivalent G') :
    hG.toTripleDiagram.MoveEquivalent hG'.toTripleDiagram := by
  obtain ⟨X', hX', hm⟩ :=
    h.exists_moveEquivalent hG.toTripleDiagram hG.isGeneralizedTripleDiagram_tripleOfNormal
  obtain ⟨_, hm'⟩ := PlabicData.IsGeneralizedTripleDiagram.exists_moveEquivalent G'.isPlabicGraph
    hX' hG'.isGeneralizedTripleDiagram_tripleOfNormal X'.isTripleDiagram
  exact hm.trans hm'

/-- For normal plabic graphs `G` and `G'`, the following are equivalent: (1) `G ∘∼ G'`; (2) `G`
and `G'` are normal-move-equivalent; (3) `X(G) ∼ X(G')`. -/
@[cluster_algebras "prop_normal_moves_equivalent"]
theorem tfae_circMoveEquivalent_normalMoveEquivalent_moveEquivalent {G G' : PlabicGraph b}
    (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph) :
    List.TFAE [G.CircMoveEquivalent G', G.NormalMoveEquivalent G',
      hG.toTripleDiagram.MoveEquivalent hG'.toTripleDiagram] := by
  tfae_have 2 → 1 := NormalMoveEquivalent.circMoveEquivalent
  tfae_have 1 → 3 := CircMoveEquivalent.moveEquivalent_toTripleDiagram hG hG'
  tfae_have 3 → 2 := (normalMoveEquivalent_iff_moveEquivalent hG hG').2
  tfae_finish

end PlabicGraph

end ClusterAlgebras
