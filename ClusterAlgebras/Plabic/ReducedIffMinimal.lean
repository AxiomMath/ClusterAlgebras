/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.ClosedStrands
public import ClusterAlgebras.Plabic.EarStrands
public import ClusterAlgebras.Plabic.LoopDecomposition
public import ClusterAlgebras.Plabic.MinimalMonogon
public import ClusterAlgebras.Plabic.MinimalTheorems
public import ClusterAlgebras.Plabic.NonReduced
public import ClusterAlgebras.Plabic.NormalMovesEquivalent
public import ClusterAlgebras.Plabic.NormalOfTriple
public import ClusterAlgebras.Plabic.Reduced

/-!
# A normal plabic graph is reduced exactly when its triple diagram is minimal

Let `G` be a normal plabic graph and `X(G)` its triple diagram. Then `G` is reduced if and only if
`X(G)` is minimal.

If `X(G)` is not minimal, some triple diagram `X' ∼ X(G)` has a hollow monogon; the normal plabic
graph `G' = G(X')` has `X(G') ≅ X'`, so `X(G')` has a hollow monogon and `G` and `G'` are
move-equivalent. Then `G'` contains a hollow digon or an internal leaf which is neither a lollipop
nor (`G'` being normal) a vertex of a collapsible tree, so `G` is not reduced.

Conversely, if `G` is not reduced, some `G' ∘∼ G` contains a hollow digon or an internal leaf whose
dart runs to a crossing. Carrying `X(G)` along `G ∘∼ G'` gives a generalized triple diagram `X'`
of `G'` with `X(G) ∼ X'`, and every strand diagram `X°(G', D)` is a triple diagram move-equivalent
to `X'`. Choosing the white datum `D` near the forbidden configuration, `X°(G', D)` has a hollow
monogon or a closed strand, so it is not minimal, and neither is `X(G)`.

## Main results

* `ClusterAlgebras.PlabicGraph.isReduced_iff_isMinimal`: a normal plabic graph is reduced exactly
  when its triple diagram is minimal.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras, Chapter 7*
  (`red-minimal`).
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicGraph

variable {b : ℕ}

/-- A hollow monogon pulls back along an isomorphism of triple data. -/
private theorem isHollowMonogon_of_iso {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H']
    [DecidableEq H'] {X : TripleData H b} {X' : TripleData H' b} (θ : X.Iso X') {c : H'}
    (hc : X'.IsHollowMonogon {c}) : X.IsHollowMonogon {θ.toEquiv.symm c} := by
  obtain ⟨hcB, hφ⟩ := hc.facePerm_eq
  refine X.isHollowMonogon_singleton ?_ ?_
  · rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply]
  · apply θ.toEquiv.injective
    rw [θ.map_facePerm, Equiv.apply_symm_apply, hφ]

/-- Changing a white datum at one vertex to a corner triangulation of that vertex (whenever it is
a crossing) gives a white datum. -/
private theorem isWhiteDatum_update {H : Type} [Fintype H] [DecidableEq H] {G : PlabicData H b}
    {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) {w : Finset H}
    {T : Finset (Sym2 H)} (hT : G.IsCrossing w → G.IsCornerTriangulation w T) :
    G.IsWhiteDatum (Function.update D w T) := by
  intro w' hw'
  by_cases h : w' = w
  · subst h
    rw [Function.update_self]
    exact hT hw'
  · rw [Function.update_of_ne h]
    exact hD w' hw'

section Forbidden

variable {H : Type} [Fintype H] [DecidableEq H] {G : PlabicData H b} (hG : G.IsPlabicGraph)
  {D₀ : Finset H → Finset (Sym2 H)} (hD₀ : G.IsWhiteDatum D₀)

include hG hD₀

/-- A hollow digon `{d₁, d₂}` with `v(d₁)` black and `v(d₂)` a crossing: changing `D₀` at `v(d₂)`
gives a white datum whose strand diagram has a dart outside `B°` fixed by `φ°`. -/
private theorem exists_isWhiteDatum_facePerm_eq_of_black {d₁ d₂ : H}
    (h : G.IsHollowDigon {d₁, d₂}) (hb : G.colour d₁ = .black)
    (hc : G.IsCrossing (G.vertexOf d₂)) :
    ∃ D, ∃ hD : G.IsWhiteDatum D, ∃ c, c ∉ (G.strandDiagram hG hD).bdry ∧
      (G.strandDiagram hG hD).facePerm c = c := by
  obtain ⟨-, -, -, ⟨-, hi₁, -, hr₂⟩⟩ := hG.toIsDiskMap.hollowDigon_shape h
  obtain ⟨T, hT, hτ⟩ := hc.exists_isCornerTriangulation_isCornerTriangle hi₁
  have hrot : G.rot (G.inv d₁) = d₂ := by rw [← hr₂, Equiv.apply_symm_apply]
  rw [hrot] at hτ
  have hD := isWhiteDatum_update hD₀ (w := G.vertexOf d₂) fun _ => hT
  obtain ⟨_, hB, hφ⟩ := PlabicData.IsWhiteDatum.strandDiagram_facePerm_xPlus_of_isHollowDigon hG
    hD h hb hc (by rw [Function.update_self]; exact hτ)
  exact ⟨_, hD, _, hB, hφ⟩

/-- A hollow digon `{d₁, d₂}` with `v(d₁)` a crossing and `v(d₂)` white: changing `D₀` at the
crossings among `v(d₁), v(d₂)` gives a white datum whose strand diagram has a closed strand. -/
private theorem exists_isWhiteDatum_isClosedStrand_of_white {d₁ d₂ : H}
    (h : G.IsHollowDigon {d₁, d₂}) (hc : G.IsCrossing (G.vertexOf d₁))
    (hw : G.colour d₂ = .white) :
    ∃ D, ∃ hD : G.IsWhiteDatum D, ∃ C, (G.strandDiagram hG hD).IsClosedStrand C := by
  obtain ⟨-, -, ⟨-, hi₂, -, hr₁⟩, ⟨-, hi₁, -, hr₂⟩⟩ := hG.toIsDiskMap.hollowDigon_shape h
  have hne := PlabicData.vertexOf_ne_of_isHollowDigon h
  obtain ⟨T₁, hT₁, hτ₁⟩ := hc.exists_isCornerTriangulation_isCornerTriangle hi₂
  have hrot₁ : G.rot (G.inv d₂) = d₁ := by rw [← hr₁, Equiv.apply_symm_apply]
  rw [hrot₁] at hτ₁
  have hD₁ := isWhiteDatum_update hD₀ (w := G.vertexOf d₁) fun _ => hT₁
  by_cases hc₂ : G.IsCrossing (G.vertexOf d₂)
  · obtain ⟨T₂, hT₂, hτ₂⟩ := hc₂.exists_isCornerTriangulation_isCornerTriangle hi₁
    have hrot₂ : G.rot (G.inv d₁) = d₂ := by rw [← hr₂, Equiv.apply_symm_apply]
    rw [hrot₂] at hτ₂
    have hD := isWhiteDatum_update hD₁ (w := G.vertexOf d₂) fun _ => hT₂
    exact ⟨_, hD, PlabicData.IsWhiteDatum.exists_isClosedStrand_of_isHollowDigon hG hD h hc hw
      (by rw [Function.update_of_ne hne, Function.update_self]; exact hτ₁)
      fun _ => by rw [Function.update_self]; exact hτ₂⟩
  · exact ⟨_, hD₁, PlabicData.IsWhiteDatum.exists_isClosedStrand_of_isHollowDigon hG hD₁ h hc hw
      (by rw [Function.update_self]; exact hτ₁) fun h' => absurd h' hc₂⟩

/-- If every orbit of the trip map of `G` contains an initial dart, and `G` has a hollow digon or
an internal leaf whose dart runs to a crossing, then some white datum `D` of `G` has a strand
diagram with a dart outside `B°` fixed by `φ°`, or with a closed strand. -/
private theorem exists_isWhiteDatum_of_forbidden
    (hinit : ∀ d ∉ G.bdry, ∃ e ∈ G.trip d, G.IsInitial e)
    (h : (∃ f, G.IsHollowDigon f) ∨
      ∃ u, G.IsInternalLeaf u ∧ ∃ k ∈ u, G.IsCrossing (G.vertexOf (G.inv k))) :
    ∃ D, ∃ hD : G.IsWhiteDatum D,
      (∃ c, c ∉ (G.strandDiagram hG hD).bdry ∧ (G.strandDiagram hG hD).facePerm c = c) ∨
        ∃ C, (G.strandDiagram hG hD).IsClosedStrand C := by
  rcases h with ⟨f, hf⟩ | ⟨u, hu, k, hk, hc⟩
  · obtain ⟨d₁, d₂, rfl, -⟩ := hf.2
    have hf' : G.IsHollowDigon {d₂, d₁} := by rwa [Finset.pair_comm]
    have hd₁B : d₁ ∉ G.bdry := disjoint_left.1 (G.mem_internalFaces.1 hf.1).2 (by simp)
    by_cases hc₁ : G.IsCrossing (G.vertexOf d₁)
    · cases hcol : G.colour d₂ with
      | white =>
        obtain ⟨D, hD, h⟩ := exists_isWhiteDatum_isClosedStrand_of_white hG hD₀ hf hc₁ hcol
        exact ⟨D, hD, Or.inr h⟩
      | black =>
        obtain ⟨D, hD, h⟩ := exists_isWhiteDatum_facePerm_eq_of_black hG hD₀ hf' hcol hc₁
        exact ⟨D, hD, Or.inl h⟩
    · by_cases hc₂ : G.IsCrossing (G.vertexOf d₂)
      · cases hcol : G.colour d₁ with
        | white =>
          obtain ⟨D, hD, h⟩ := exists_isWhiteDatum_isClosedStrand_of_white hG hD₀ hf' hc₂ hcol
          exact ⟨D, hD, Or.inr h⟩
        | black =>
          obtain ⟨D, hD, h⟩ := exists_isWhiteDatum_facePerm_eq_of_black hG hD₀ hf hcol hc₂
          exact ⟨D, hD, Or.inl h⟩
      · obtain ⟨-, hno⟩ := hG.trip_eq_of_isHollowDigon hf hc₁ hc₂
        obtain ⟨e, he, hi⟩ := hinit d₁ hd₁B
        exact absurd hi (hno e he)
  · obtain ⟨_, hB, hφ⟩ :=
      PlabicData.IsWhiteDatum.strandDiagram_facePerm_xMinus_of_isInternalLeaf hG hD₀ hu hk hc
    exact ⟨D₀, hD₀, Or.inl ⟨_, hB, hφ⟩⟩

end Forbidden

/-- If a strand diagram `X°(G, D)` has a dart outside `B°` fixed by `φ°` or a closed strand, then
no generalized triple diagram of `G` that is a triple diagram is minimal. -/
private theorem not_isMinimal_of_strandDiagram {H : Type} [Fintype H] [DecidableEq H]
    {G : PlabicData H b} (hG : G.IsPlabicGraph) {X : TripleDiagram b}
    (hX : G.IsGeneralizedTripleDiagram hG X.data) {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D)
    (h : (∃ c, c ∉ (G.strandDiagram hG hD).bdry ∧ (G.strandDiagram hG hD).facePerm c = c) ∨
      ∃ C, (G.strandDiagram hG hD).IsClosedStrand C) : ¬X.IsMinimal := by
  intro hmin
  have hY : G.IsGeneralizedTripleDiagram hG (G.strandDiagram hG hD) :=
    ⟨PlabicData.isPreTripleDiagram_strandDiagram hG hD, hX.2.1, D, hD,
      ⟨TripleData.Iso.refl _⟩⟩
  obtain ⟨hY', hm⟩ :=
    PlabicData.IsGeneralizedTripleDiagram.exists_moveEquivalent hG hX hY X.isTripleDiagram
  have hmin' := hmin.of_moveEquivalent hm
  rcases h with ⟨c, hcB, hφ⟩ | ⟨C, hC⟩
  · exact TripleDiagram.not_isMinimal_of_isHollowMonogon _
      ((G.strandDiagram hG hD).isHollowMonogon_singleton hcB hφ) hmin'
  · exact hmin'.not_isClosedStrand C hC

/-- A reduced normal plabic graph has a minimal triple diagram. -/
private theorem isMinimal_of_isReduced {G : PlabicGraph b} (hG : G.data.IsNormalPlabicGraph)
    (hred : G.IsReduced) : hG.toTripleDiagram.IsMinimal := by
  by_contra hmin
  obtain ⟨X', hm, c, hc⟩ :=
    TripleDiagram.exists_moveEquivalent_isHollowMonogon_of_not_isMinimal hmin
  have hX' := X'.isTripleDiagram
  have hN := hX'.isNormalPlabicGraph_normalOfTriple
  let G' : PlabicGraph b :=
    ⟨_, X'.data.normalOfTriple hX'.toIsPreTripleDiagram, hN.toIsPlabicGraph⟩
  have hN' : G'.data.IsNormalPlabicGraph := hN
  let θ := hX'.toIsPreTripleDiagram.tripleOfNormalIso
  have hc' : (G'.data.tripleOfNormal hN'.isNormalPlabicPregraph).IsHollowMonogon
      {θ.toEquiv.symm c} := isHollowMonogon_of_iso θ hc
  have hm' : hG.toTripleDiagram.MoveEquivalent hN'.toTripleDiagram :=
    hm.trans (TripleDiagram.MoveEquivalent.of_isomorphic ⟨θ⟩).symm
  have hcirc :=
    ((tfae_circMoveEquivalent_normalMoveEquivalent_moveEquivalent hG hN').out 0 2).2 hm'
  obtain ⟨hdig, hleaf⟩ := hred G' hcirc.moveEquivalent.symm
  rcases hN'.exists_isHollowDigon_or_isInternalLeaf hc' with ⟨f, hf⟩ | ⟨v, hv, hnl⟩
  · exact hdig f hf
  · rcases hleaf v hv with ⟨i, hi⟩ | ⟨T, hT, -⟩
    · exact hnl i hi
    · exact hN'.not_isCollapsible T hT

/-- A normal plabic graph whose triple diagram is minimal is reduced. -/
private theorem isReduced_of_isMinimal {G : PlabicGraph b} (hG : G.data.IsNormalPlabicGraph)
    (hmin : hG.toTripleDiagram.IsMinimal) : G.IsReduced := by
  by_contra hred
  obtain ⟨G', hcirc, hforb⟩ := hG.exists_circMoveEquivalent_of_not_isReduced hred
  obtain ⟨X', hgen, hm⟩ :=
    hcirc.exists_moveEquivalent hG.toTripleDiagram hG.isGeneralizedTripleDiagram_tripleOfNormal
  obtain ⟨-, hinit, D₀, hD₀, -⟩ := id hgen
  obtain ⟨D, hD, h⟩ := exists_isWhiteDatum_of_forbidden G'.isPlabicGraph hD₀ hinit hforb
  exact not_isMinimal_of_strandDiagram G'.isPlabicGraph hgen hD h (hmin.of_moveEquivalent hm)

/-- A normal plabic graph `G` is reduced if and only if its triple diagram `X(G)` is minimal. -/
@[cluster_algebras "thm_reduced_iff_minimal"]
theorem isReduced_iff_isMinimal {G : PlabicGraph b} (hG : G.data.IsNormalPlabicGraph) :
    G.IsReduced ↔ hG.toTripleDiagram.IsMinimal :=
  ⟨isMinimal_of_isReduced hG, isReduced_of_isMinimal hG⟩

end PlabicGraph

end ClusterAlgebras
