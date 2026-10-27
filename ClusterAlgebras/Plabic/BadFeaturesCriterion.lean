/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BadFeatureBadgon
public import ClusterAlgebras.Plabic.MinimalTheorems
public import ClusterAlgebras.Plabic.ReducedIffMinimal

/-!
# The bad features criterion

Let `G` be a normal plabic graph and `X(G)` its triple diagram. By the equivalence of reducedness
of `G` and minimality of `X(G)`, and the characterization of minimal triple diagrams as those
without badgons, `G` is reduced if and only if `X(G)` has no badgon. Translating badgons of `X(G)`
into bad features of `G` (roundtrips, essential self-intersections and bad double crossings)
gives the bad features criterion, a version of Postnikov's Theorem 13.2: a normal plabic graph is
reduced if and only if it has no bad feature.

## Main results

* `ClusterAlgebras.PlabicGraph.isReduced_iff_not_hasBadgon`: a normal plabic graph is reduced
  exactly when its triple diagram has no badgon.
* `ClusterAlgebras.PlabicGraph.isReduced_iff_not_hasBadFeature`: a normal plabic graph is reduced
  exactly when it has no bad feature.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
* [Pos06] A. Postnikov, *Total positivity, Grassmannians, and networks*, arXiv:math/0609764,
  Theorem 13.2.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicGraph

variable {b : ℕ}

/-- A normal plabic graph `G` is reduced if and only if its triple diagram `X(G)` has no badgon. -/
@[cluster_algebras "prop_normal_reduced_criteria"]
theorem isReduced_iff_not_hasBadgon {G : PlabicGraph b} (hG : G.data.IsNormalPlabicGraph) :
    G.IsReduced ↔ ¬hG.toTripleDiagram.data.HasBadgon :=
  (isReduced_iff_isMinimal hG).trans TripleDiagram.isMinimal_iff_not_hasBadgon

/-- **The bad features criterion**, a version of Postnikov's Theorem 13.2: a normal plabic graph
`G` is reduced if and only if it has no bad feature, that is, no roundtrip, no essential
self-intersection and no bad double crossing. -/
@[cluster_algebras "thm_bad_features_criterion"]
theorem isReduced_iff_not_hasBadFeature {G : PlabicGraph b} (hG : G.data.IsNormalPlabicGraph) :
    G.IsReduced ↔ ¬G.data.HasBadFeature :=
  (isReduced_iff_not_hasBadgon hG).trans (not_congr hG.hasBadFeature_iff_hasBadgon.symm)

end PlabicGraph

end ClusterAlgebras
