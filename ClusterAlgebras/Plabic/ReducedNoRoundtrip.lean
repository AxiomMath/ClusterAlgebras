/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Excision
public import ClusterAlgebras.Plabic.ReducedCollapse
public import ClusterAlgebras.Plabic.ReducedRecolouring
public import ClusterAlgebras.Plabic.ReducedToNormal
public import ClusterAlgebras.Plabic.RoundtripMoves

/-!
# Reduced plabic graphs: normalizations, roundtrips and loops

Let `G` be a reduced plabic graph. Then `G` is move-equivalent to a nearly leafless plabic graph
`G₁`, which is again reduced. Recolouring the white lollipops of `G₁` one at a time gives a
reduced nearly leafless graph `G₂` without white lollipops: each recolouring `R_i` is applied to a
nearly leafless graph, keeps it nearly leafless and reduced, and turns one white dart black.
Then `G₂` is move-equivalent to a normal plabic graph `N`, and the sequence `G ∼ G₁`, the
recolourings, `G₂ ∼ N` shows that `N` is a normalization of `G`.

The normalization `N` is reduced, so its triple diagram `X(N)` is minimal and has no closed
strand; hence `N` has no roundtrip. Local moves, isomorphisms and recolourings keep roundtrips
(recolouring does not change the trip map or the legs), so `G` has no roundtrip either. Since a
loop of a plabic graph gives a roundtrip, a reduced plabic graph has no loop.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.not_hasRoundtrip`: a reduced plabic graph has no
  roundtrip.
* `ClusterAlgebras.PlabicGraph.IsReduced.vertexOf_inv_ne`: a reduced plabic graph has no loop.
* `ClusterAlgebras.PlabicGraph.IsReduced.exists_isNormalization`: a reduced plabic graph has a
  normalization.

## Implementation notes

* The normalization algorithm of [FWZ] reaches a normal graph from a reduced nearly leafless
  graph without white lollipops by removing bivalent vertices, contracting edges between black
  vertices, splitting white vertices and inserting black vertices. Here this last part is supplied
  by the statement that a reduced nearly leafless graph without white lollipops is move-equivalent
  to a normal one (`IsReduced.exists_moveEquivalent_isNormalPlabicGraph`), so the normalization is
  built from three stages: moves to a nearly leafless graph, recolourings of white lollipops, and
  moves to a normal graph. In particular the normalization is constructed before, and
  independently of, the absence of loops.
* The recolouring stage is an induction on the number of white darts, which each recolouring of a
  white lollipop lowers by one.
* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

open Finset

namespace ClusterAlgebras

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- Recolouring a lollipop keeps roundtrips: it changes neither the trip map, nor `B`, nor the
legs. -/
theorem hasRoundtrip_recolourLollipop (i : Fin b) :
    (G.recolourLollipop i).HasRoundtrip ↔ G.HasRoundtrip := by
  rw [hasRoundtrip_iff, hasRoundtrip_iff, tripMap_recolourLollipop]
  rfl

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- A step of a normalization keeps roundtrips. -/
theorem NormalizationStep.hasRoundtrip_iff {G G' : PlabicGraph b} (h : NormalizationStep G G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  rcases h with h | ⟨-, i, rfl⟩
  · exact h.hasRoundtrip_iff
  · exact (hasRoundtrip_recolourLollipop i).symm

/-- A sequence of normalization steps keeps roundtrips. -/
theorem hasRoundtrip_iff_of_reflTransGen_normalizationStep {G G' : PlabicGraph b}
    (h : Relation.ReflTransGen NormalizationStep G G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hst ih => exact ih.trans hst.hasRoundtrip_iff

/-- A plabic graph has a roundtrip exactly when any of its normalizations has one. -/
theorem IsNormalization.hasRoundtrip_iff {G N : PlabicGraph b} (h : IsNormalization G N) :
    G.data.HasRoundtrip ↔ N.data.HasRoundtrip :=
  hasRoundtrip_iff_of_reflTransGen_normalizationStep h.2

/-- The colour of the dart `ḡ_i` of a white lollipop at `i` is turned black by `R_i`, and no
other colour changes; so `R_i` has fewer white darts. -/
private theorem card_white_recolourLollipop_lt {G : PlabicGraph b} {i : Fin b} {v : Finset G.Dart}
    (hv : G.data.IsLollipopOfColour i .white v) :
    (univ.filter fun d : G.Dart => (G.data.recolourLollipop i).colour d = .white).card <
      (univ.filter fun d : G.Dart => G.data.colour d = .white).card := by
  have hveq := hv.1.eq_singleton_inv_leg G.isPlabicGraph
  set x := G.data.inv (G.data.leg i)
  have hxv : x ∈ v := hveq ▸ mem_singleton_self x
  have hvx : G.data.vertexOf x = v := by
    obtain ⟨y, rfl⟩ := G.data.mem_vertices.1 (G.data.mem_internalVertices.1 hv.1.1.1).1
    exact G.data.vertexOf_eq_of_mem hxv
  have hleaf : G.data.IsInternalLeaf (G.data.vertexOf x) := hvx ▸ hv.1.1
  have hxw : G.data.colour x = .white := hv.2 x hxv
  have hcol : ∀ d, d ≠ x → (G.data.recolourLollipop i).colour d = G.data.colour d := by
    intro d hd
    refine colour_recolourLollipop_of_notMem fun h => hd ?_
    rw [hvx, hveq] at h
    exact mem_singleton.1 h.2
  have hxb : (G.data.recolourLollipop i).colour x = .black := by
    rw [colour_recolourLollipop_of_mem hleaf (G.data.self_mem_vertexOf x), hxw]
    rfl
  refine card_lt_card ⟨fun d hd => ?_, fun h => ?_⟩
  · rw [mem_filter] at hd ⊢
    refine ⟨mem_univ _, ?_⟩
    by_cases hdx : d = x
    · rw [hdx, hxb] at hd
      exact absurd hd.2 (by decide)
    · rw [← hcol d hdx]
      exact hd.2
  · have := (mem_filter.1 (h (mem_filter.2 ⟨mem_univ x, hxw⟩))).2
    rw [hxb] at this
    exact absurd this (by decide)

/-- **Recolouring the white lollipops**: a reduced nearly leafless plabic graph `G` is joined by
normalization steps (recolourings of white lollipops) to a reduced nearly leafless plabic graph
without white lollipops. -/
private theorem exists_reflTransGen_noWhiteLollipop {G : PlabicGraph b} (hred : G.IsReduced)
    (hnl : G.data.IsNearlyLeafless) :
    ∃ G' : PlabicGraph b, Relation.ReflTransGen NormalizationStep G G' ∧ G'.IsReduced ∧
      G'.data.IsNearlyLeafless ∧ ∀ i v, ¬G'.data.IsLollipopOfColour i .white v := by
  induction hn : (univ.filter fun d : G.Dart => G.data.colour d = .white).card
    using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hw : ∀ i v, ¬G.data.IsLollipopOfColour i .white v
  · exact ⟨G, .refl, hred, hnl, hw⟩
  push Not at hw
  obtain ⟨i, v, hv⟩ := hw
  have hlt := card_white_recolourLollipop_lt hv
  rw [hn] at hlt
  obtain ⟨G', hG', h'⟩ := ih _ hlt (G := G.recolourLollipop i)
    ((isReduced_iff_isReduced_recolourLollipop hnl i).1 hred) (hnl.recolourLollipop i) rfl
  exact ⟨G', Relation.ReflTransGen.head (Or.inr ⟨hnl, i, rfl⟩) hG', h'⟩

/-- If `G` is a reduced plabic graph, then some normal plabic graph `N` is a normalization of
`G`. -/
@[cluster_algebras "lem_normalization_exists"]
theorem IsReduced.exists_isNormalization {G : PlabicGraph b} (hG : G.IsReduced) :
    ∃ N : PlabicGraph b, G.IsNormalization N := by
  obtain ⟨G₁, hnl₁, h₁⟩ := hG.exists_moveEquivalent_isNearlyLeafless
  have h₁' : MoveEquivalent Set.univ G G₁ := h₁.mono (Set.subset_univ _)
  obtain ⟨G₂, h₁₂, hred₂, hnl₂, hw₂⟩ :=
    exists_reflTransGen_noWhiteLollipop (hG.of_moveEquivalent h₁') hnl₁
  obtain ⟨N, h₂N, hN⟩ := hred₂.exists_moveEquivalent_isNormalPlabicGraph hnl₂ hw₂
  exact ⟨N, hN.toIsNormal,
    ((Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) h₁').trans h₁₂).trans
      (Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) h₂N)⟩

/-- A reduced plabic graph has no roundtrip: every orbit of its trip map on `H \ B` contains a
leg. -/
@[cluster_algebras "lem_reduced_no_roundtrip"]
theorem IsReduced.not_hasRoundtrip {G : PlabicGraph b} (hG : G.IsReduced) :
    ¬G.data.HasRoundtrip := by
  obtain ⟨N, hN⟩ := hG.exists_isNormalization
  have hNP : N.data.IsNormalPlabicGraph := ⟨N.isPlabicGraph, hN.1⟩
  have hmin := (isReduced_iff_isMinimal hNP).1 (hN.isReduced_iff.1 hG)
  rw [hN.hasRoundtrip_iff, hNP.hasRoundtrip_iff_exists_isClosedStrand]
  rintro ⟨C, hC⟩
  exact hmin.not_isClosedStrand C hC

/-- A reduced plabic graph has no loop: no edge `{d, d̄}` of the graph (`d ∉ B`) has
`v(d) = v(d̄)`. -/
@[cluster_algebras "lem_reduced_no_loop"]
theorem IsReduced.vertexOf_inv_ne {G : PlabicGraph b} (hG : G.IsReduced) {d : G.Dart}
    (hd : d ∉ G.data.bdry) : G.data.vertexOf (G.data.inv d) ≠ G.data.vertexOf d :=
  fun h => hG.not_hasRoundtrip (G.isPlabicGraph.hasRoundtrip_of_loop hd h)

end PlabicGraph

end ClusterAlgebras
