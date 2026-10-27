/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BridgeBadgons
public import ClusterAlgebras.Plabic.BridgeDecomposition
public import ClusterAlgebras.Plabic.MinimalTheorems
public import ClusterAlgebras.Plabic.ReducedIffMinimal
public import ClusterAlgebras.Plabic.ReducedRecolouring
public import ClusterAlgebras.Plabic.TripleMoves

/-!
# Bridge decompositions are reduced

Let `π̃` be a decorated permutation on `b` letters and `s` a bridge sequence for its affinization
`f_π̃`. The bridge decomposition `G = G(π̃, s)` is a reduced plabic graph. Its strand diagram
`X° = X°(G, ∅)` is a triple diagram with no monogon and no parallel digon, hence with no badgon,
hence minimal. A normalization `N` of `G` has `X(N) ≅ X°`, so `X(N)` is minimal, the normal graph
`N` is reduced, and so is `G`.

As bridge sequences exist for every bounded affine permutation, and the decorated trip
permutation of `G(π̃, s)` is `π̃`, every decorated permutation is the decorated trip permutation of
a reduced plabic graph.

## Main results

* `ClusterAlgebras.DecoratedPerm.isReduced_bridgeDecomposition`: the bridge decomposition
  `G(π̃, s)` is a reduced plabic graph.
* `ClusterAlgebras.DecoratedPerm.exists_isReduced_decoratedTripPerm_eq`: every decorated
  permutation is the decorated trip permutation of a reduced plabic graph.

## Implementation notes

* As for every plabic graph, `b ≥ 1` is assumed.
* Labels are `0`-indexed: `x : Fin b` is FWZ's label `x + 1`.
* The decorated trip permutation of a plabic graph is defined given the bijectivity of its trip
  permutation, so `exists_isReduced_decoratedTripPerm_eq` provides that bijectivity together with
  the graph.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.10.
-/

@[expose] public section

namespace ClusterAlgebras

namespace DecoratedPerm

variable {b : ℕ}

/-- Let `π̃` be a decorated permutation on `b ≥ 1` letters and `s` a bridge sequence for its
affinization `f_π̃`. Then the bridge decomposition `G(π̃, s)` is a reduced plabic graph. -/
@[cluster_algebras "thm_bridge_decomposition"]
theorem isReduced_bridgeDecomposition (hb : 1 ≤ b) (π : DecoratedPerm b) {s : List (ℤ × ℤ)}
    (hs : IsBridgeSequence b π.affinization s) :
    (⟨BridgeDart b s, π.bridgeDecomposition s, π.isPlabicGraph_bridgeDecomposition hb hs⟩ :
      PlabicGraph b).IsReduced := by
  set γ : Fin b → Shade := fun x => if h : π.perm x = x then π.colour ⟨x, h⟩ else .black
  have hbd := hs.forall_mem_bounds
  have hn := hs.isNestedPairSequence
  change (bridgePlabicGraph hb hbd hn γ).IsReduced
  obtain ⟨N, hN, hθ⟩ := exists_isNormalization_bridgeGraph hb hbd hn γ
  let X : TripleDiagram b :=
    ⟨_, (bridgeGraph b s γ).strandDiagram (isPlabicGraph_bridgeGraph hb hbd hn γ)
      (isWhiteDatum_empty_bridgeGraph γ), isTripleDiagram_strandDiagram_bridgeGraph hb hbd hn γ⟩
  have hX : X.IsMinimal := by
    refine TripleDiagram.isMinimal_iff_not_hasBadgon.2 ?_
    rintro (h | h)
    · exact hs.not_hasMonogon_strandDiagram_bridgeGraph hb γ h
    · exact hs.not_hasParallelDigon_strandDiagram_bridgeGraph hb
        π.isBoundedAffinePerm_affinization γ h
  exact hN.isReduced_iff.2 ((PlabicGraph.isReduced_iff_isMinimal ⟨N.isPlabicGraph, hN.1⟩).2
    (hX.of_moveEquivalent (TripleDiagram.MoveEquivalent.of_isomorphic hθ).symm))

/-- Let `π̃` be a decorated permutation on `b ≥ 1` letters. Then there is a reduced plabic graph
`G` with `b` boundary vertices whose trip permutation is a bijection and whose decorated trip
permutation is `π̃_G = π̃`. -/
@[cluster_algebras "prop_reduced_exists"]
theorem exists_isReduced_decoratedTripPerm_eq (hb : 1 ≤ b) (π : DecoratedPerm b) :
    ∃ (G : PlabicGraph b) (h : Function.Bijective G.data.tripPerm),
      G.IsReduced ∧ G.data.decoratedTripPerm h = π := by
  obtain ⟨s, hs⟩ := π.isBoundedAffinePerm_affinization.exists_isBridgeSequence
  exact ⟨_, π.bijective_tripPerm_bridgeDecomposition hs, π.isReduced_bridgeDecomposition hb hs,
    π.decoratedTripPerm_bridgeDecomposition hs _⟩

end DecoratedPerm

end ClusterAlgebras
