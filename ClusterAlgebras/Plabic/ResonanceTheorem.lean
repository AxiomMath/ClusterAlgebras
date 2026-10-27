/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BridgeDecompositionTheorem
public import ClusterAlgebras.Plabic.FundamentalTheorem
public import ClusterAlgebras.Plabic.NearlyLeaflessSequences
public import ClusterAlgebras.Plabic.ReducedRecolouring
public import ClusterAlgebras.Plabic.ResonanceMoves

/-!
# The resonance criterion

Let `G` be a plabic graph in which every internal leaf is a lollipop, that is, a nearly leafless
plabic graph. Then `G` is reduced if and only if `G` has the resonance property (Kodama–Williams).

If `G` has the resonance property but is not reduced, then `G` is nearly leafless equivalent to a
plabic graph containing a hollow digon; the resonance property passes along nearly leafless
equivalences, and a hollow digon violates it.

If `G` is reduced, let `π̃_G` be its decorated trip permutation and `B = G(π̃_G, s)` a bridge
decomposition for a bridge sequence `s` of the affinization of `π̃_G`. Then `B` is reduced, has
decorated trip permutation `π̃_G` and has the resonance property; in particular it is nearly
leafless. By the fundamental theorem `G ∼ B`, so `G` and `B` are nearly leafless equivalent, and
`G` has the resonance property.

## Main results

* `ClusterAlgebras.PlabicGraph.isReduced_iff_hasResonanceProperty`: a nearly leafless plabic
  graph is reduced if and only if it has the resonance property.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.11.
* [KW] Y. Kodama, L. Williams, *KP solitons and total positivity for the Grassmannian*,
  Theorem 10.5.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicGraph

variable {b : ℕ}

/-- A graph with the resonance property is nearly leafless: an internal vertex that is not a
lollipop satisfies the resonance condition, so it has at least two darts. -/
private theorem isNearlyLeafless_of_hasResonanceProperty {H : Type*} [Fintype H] [DecidableEq H]
    {G : PlabicData H b} (h : G.HasResonanceProperty) : G.IsNearlyLeafless := by
  intro v hv
  by_contra hno
  have := (h v hv.1 fun i hi => hno ⟨i, hi⟩).1
  have := hv.2
  omega

/-- A reduced nearly leafless plabic graph has the resonance property. -/
theorem IsReduced.hasResonanceProperty {G : PlabicGraph b} (hred : G.IsReduced)
    (hnl : G.data.IsNearlyLeafless) : G.data.HasResonanceProperty := by
  have hb : 1 ≤ b := G.isPlabicGraph.one_le
  have hπ := G.isPlabicGraph.tripPerm_bijective
  set π := G.data.decoratedTripPerm hπ
  obtain ⟨s, hs⟩ := π.isBoundedAffinePerm_affinization.exists_isBridgeSequence
  let B : PlabicGraph b :=
    ⟨BridgeDart b s, π.bridgeDecomposition s, π.isPlabicGraph_bridgeDecomposition hb hs⟩
  have hBπ : Function.Bijective B.data.tripPerm := π.bijective_tripPerm_bridgeDecomposition hs
  have hBres : B.data.HasResonanceProperty := π.hasResonanceProperty_bridgeDecomposition hs
  have hGB : MoveEquivalent Set.univ G B :=
    (hred.moveEquivalent_iff_decoratedTripPerm_eq (π.isReduced_bridgeDecomposition hb hs) hπ
      hBπ).2 (π.decoratedTripPerm_bridgeDecomposition hs hBπ).symm
  exact ((hred.nearlyLeaflessEquivalent hnl
    (isNearlyLeafless_of_hasResonanceProperty hBres) hGB).hasResonanceProperty_iff).2 hBres

/-- **The resonance criterion** (Kodama–Williams). Let `G` be a plabic graph in which every
internal leaf is a lollipop (that is, `G` is nearly leafless). Then `G` is reduced if and only if
`G` has the resonance property. -/
@[cluster_algebras "thm_resonance"]
theorem isReduced_iff_hasResonanceProperty {G : PlabicGraph b}
    (hG : ∀ v, G.data.IsInternalLeaf v → ∃ i, G.data.IsLollipop i v) :
    G.IsReduced ↔ G.data.HasResonanceProperty := by
  refine ⟨fun hred => hred.hasResonanceProperty hG, fun hres => ?_⟩
  by_contra hred
  obtain ⟨X, hGX, f, hf⟩ := (not_isReduced_iff hG).1 hred
  exact X.isPlabicGraph.not_hasResonanceProperty_of_isHollowDigon hf
    (hGX.hasResonanceProperty_iff.1 hres)

end PlabicGraph

end ClusterAlgebras
