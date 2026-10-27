/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CornerTriangulation
public import ClusterAlgebras.Plabic.ExcisionLemmas
public import ClusterAlgebras.Plabic.NearlyLeaflessSequences
public import ClusterAlgebras.Plabic.NormalPlabic

/-!
# Non-reduced plabic graphs

Two consequences of the characterisation of non-reduced nearly leafless plabic graphs as those
that are nearly leafless equivalent to a plabic graph with a hollow digon.

*Normal graphs.* A normal plabic graph `G` that is not reduced satisfies `G ∘∼ G'` for a plabic
graph `G'` containing a hollow digon or an internal leaf whose dart runs to a crossing. If `G` has
an internal leaf that is not a lollipop, that leaf is black and its dart runs to a white trivalent
vertex, so `G' = G` works. Otherwise `G` is nearly leafless, and the moves of a nearly leafless
equivalence are steps of `∘∼`: an edge contracted in a nearly leafless graph cannot have an
internal leaf as an endpoint, since that leaf would be a lollipop and its dart runs to the other,
internal, endpoint.

*Fewer faces.* A nearly leafless plabic graph `G` that is not reduced is move-equivalent to a
plabic graph `K` with a hollow digon, with the faces and the trip permutation of `G`. Excising one
side of the digon (same colours) or both sides (different colours) and pruning stray leaves gives a
nearly leafless plabic graph with the trip permutation of `G` and fewer faces.

## Main results

* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.exists_circMoveEquivalent_of_not_isReduced`: a
  non-reduced normal graph reaches a forbidden configuration.
* `ClusterAlgebras.PlabicGraph.exists_isNearlyLeafless_card_faces_lt_of_not_isReduced`: a
  non-reduced graph without stray leaves has a smaller relative.

## Implementation notes

* Plabic graphs with `b` boundary vertices are elements of `ClusterAlgebras.PlabicGraph b`, so the
  conclusion "with as many boundary vertices as `G`" is part of the type of the graph produced.
* A crossing is a white internal vertex with at least three darts
  (`ClusterAlgebras.PlabicData.IsCrossing`); the dart of an internal leaf `u` runs to a crossing
  when, for the dart `k ∈ u`, the vertex `v(k̄)` is a crossing.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- The dart of a lollipop `v(x)` runs to a boundary vertex. -/
private theorem isBoundaryVertex_inv_of_isLollipop (hG : G.IsPlabicGraph) {i : Fin b} {x : H}
    (h : G.IsLollipop i (G.vertexOf x)) : G.IsBoundaryVertex (G.vertexOf (G.inv x)) := by
  obtain ⟨⟨-, hcard⟩, e, he, hinv⟩ := h
  obtain ⟨a, ha⟩ := card_eq_one.1 hcard
  have hx : x = a := mem_singleton.1 (ha ▸ G.self_mem_vertexOf x)
  have he' : e = a := mem_singleton.1 (ha ▸ he)
  subst hx he'
  rw [G.vertexOf_eq_of_mem hinv]
  exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

/-- In a nearly leafless plabic graph, a contractible edge does not join a white internal leaf to a
white vertex: neither of its endpoints is an internal leaf. -/
private theorem IsContractibleEdge.not_isWhiteLeafEdge (hG : G.IsPlabicGraph)
    (hnl : G.IsNearlyLeafless) {d : H} (he : G.IsContractibleEdge d) : ¬G.IsWhiteLeafEdge d := by
  rintro (⟨hl, -⟩ | ⟨hl, -⟩)
  · obtain ⟨i, hi⟩ := hnl _ hl
    exact he.not_isBoundaryVertex_inv (isBoundaryVertex_inv_of_isLollipop hG hi)
  · obtain ⟨i, hi⟩ := hnl _ hl
    have := isBoundaryVertex_inv_of_isLollipop hG hi
    rw [hG.inv_involutive d] at this
    exact he.not_isBoundaryVertex this

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

/-- A step of a nearly leafless equivalence from a nearly leafless plabic graph is a step of the
relation `∘∼`. -/
private theorem NearlyLeaflessStep.circStep {G G' : PlabicGraph b} (hG : G.data.IsNearlyLeafless)
    (h : NearlyLeaflessStep G G') : CircStep G G' := by
  obtain ⟨hG', h⟩ := h
  rcases h with θ | ⟨t, -, h⟩
  · exact Or.inl θ
  cases t with
  | m1 => exact Or.inr (Or.inl h)
  | m2 => exact Or.inr (Or.inr (Or.inl h))
  | m3 =>
    refine Or.inr (Or.inr (Or.inr ?_))
    rcases h with ⟨d, hd⟩ | ⟨d, hd⟩
    · exact Or.inl ⟨d, hd.1.not_isWhiteLeafEdge G.isPlabicGraph hG, hd⟩
    · exact Or.inr ⟨d, hd.1.not_isWhiteLeafEdge G'.isPlabicGraph hG', hd⟩

/-- A nearly leafless equivalence `G ≈ G'` gives `G ∘∼ G'`. -/
private theorem NearlyLeaflessEquivalent.circMoveEquivalent {G G' : PlabicGraph b}
    (h : NearlyLeaflessEquivalent G G') : CircMoveEquivalent G G' := by
  obtain ⟨h0, h⟩ := h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail B C hBC hst ih =>
    exact ih.tail (hst.circStep (NearlyLeaflessEquivalent.isNearlyLeafless_right ⟨h0, hBC⟩))

end PlabicGraph

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- **A non-reduced normal graph reaches a forbidden configuration**. Let `G` be a normal plabic
graph that is not reduced. Then there is a plabic graph `G'` with `G ∘∼ G'` that contains a hollow
digon or an internal leaf `u` whose dart `k ∈ u` runs to a crossing `v(k̄)`. -/
@[cluster_algebras "lem_not_reduced_circ"]
theorem IsNormalPlabicGraph.exists_circMoveEquivalent_of_not_isReduced
    (hG : G.IsNormalPlabicGraph) (hred : ¬(⟨H, G, hG.toIsPlabicGraph⟩ : PlabicGraph b).IsReduced) :
    ∃ G' : PlabicGraph b, PlabicGraph.CircMoveEquivalent ⟨H, G, hG.toIsPlabicGraph⟩ G' ∧
      ((∃ f, G'.data.IsHollowDigon f) ∨
        ∃ u, G'.data.IsInternalLeaf u ∧
          ∃ k ∈ u, G'.data.IsCrossing (G'.data.vertexOf (G'.data.inv k))) := by
  by_cases hnl : G.IsNearlyLeafless
  · obtain ⟨X, hX, f, hf⟩ :=
      (PlabicGraph.not_isReduced_iff (G := ⟨H, G, hG.toIsPlabicGraph⟩) hnl).1 hred
    exact ⟨X, hX.circMoveEquivalent, Or.inl ⟨f, hf⟩⟩
  simp only [IsNearlyLeafless, not_forall, not_exists, exists_prop] at hnl
  obtain ⟨u, hu, hnot⟩ := hnl
  obtain ⟨k, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hu.1).1
  have hk : ¬G.IsBoundaryVertex (G.vertexOf k) := G.vertexOf_mem_internalVertices.1 hu.1
  have hw : ¬G.IsBoundaryVertex (G.vertexOf (G.inv k)) := by
    intro hb
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hb)
    exact hnot i ⟨hu, k, G.self_mem_vertexOf k, hi ▸ G.self_mem_vertexOf _⟩
  have hblack : G.colour k = .black := by
    cases hc : G.colour k
    · have := hG.card_vertexOf_of_white k hk hc
      rw [hu.2] at this
      exact absurd this (by norm_num)
    · rfl
  have hwhite : G.colour (G.inv k) = .white := by
    have := hG.colour_inv_ne k hk hw
    rw [hblack] at this
    cases hc : G.colour (G.inv k)
    · rfl
    · exact absurd hc this
  refine ⟨⟨H, G, hG.toIsPlabicGraph⟩, Relation.ReflTransGen.refl, Or.inr
    ⟨G.vertexOf k, hu, k, G.self_mem_vertexOf k, G.vertexOf_mem_internalVertices.2 hw,
      fun d hd => (hG.colour_eq_of_mem_vertexOf hw hd).trans hwhite, ?_⟩⟩
  exact (hG.card_vertexOf_of_white _ hw hwhite).ge

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- **A non-reduced graph without stray leaves has a smaller relative**. Let `G` be a nearly
leafless plabic graph that is not reduced. Then there is a nearly leafless plabic graph `G''` with
as many boundary vertices as `G`, `π_{G''} = π_G`, and fewer faces than `G`. -/
@[cluster_algebras "lem_nonreduced_fewer_faces"]
theorem exists_isNearlyLeafless_card_faces_lt_of_not_isReduced {G : PlabicGraph b}
    (hG : G.data.IsNearlyLeafless) (hred : ¬G.IsReduced) :
    ∃ G'' : PlabicGraph b, G''.data.IsNearlyLeafless ∧ G''.data.tripPerm = G.data.tripPerm ∧
      G''.data.faces.card < G.data.faces.card := by
  obtain ⟨K, hGK, f, hf⟩ := (not_isReduced_iff hG).1 hred
  have hmove := hGK.moveEquivalent
  have hπ := MoveEquivalent.tripPerm_eq hmove
  have hcard := (MoveEquivalent.card_eq hmove).2.1
  have hK := K.isPlabicGraph
  obtain ⟨hfi, d₁, d₂, rfl, -⟩ := id hf
  have hdisj := (K.data.mem_internalFaces.1 hfi).2
  have hd₁ : d₁ ∉ K.data.bdry := disjoint_left.1 hdisj (by simp)
  have hd₂ : d₂ ∉ K.data.bdry := disjoint_left.1 hdisj (by simp)
  have hB : ∀ d ∉ K.data.bdry, Disjoint ({d, K.data.inv d} : Finset K.Dart) K.data.bdry :=
    fun d hd => by
      rw [disjoint_insert_left, disjoint_singleton_left]
      exact ⟨hd, fun h => hd (hK.inv_mem_bdry_iff.1 h)⟩
  by_cases hc : K.data.colour d₁ = K.data.colour d₂
  · have h𝓔 : {{d₂, K.data.inv d₂}} ⊆ K.data.edges :=
      singleton_subset_iff.2 (pair_inv_mem_edges _ _)
    have h𝓔B : ∀ e ∈ ({{d₂, K.data.inv d₂}} : Finset (Finset K.Dart)), Disjoint e K.data.bdry := by
      intro e he
      rw [mem_singleton.1 he]
      exact hB d₂ hd₂
    obtain ⟨hK1, hπ1, hf1⟩ := hK.edgeExcision_of_isHollowDigon_of_colour_eq hf h𝓔 h𝓔B hc
    obtain ⟨G'', hnl, hπ'', hf''⟩ := hK1.exists_isNearlyLeafless
    exact ⟨G'', hnl, hπ''.trans (hπ1.trans hπ.symm), by omega⟩
  · have h𝓔 : {{d₁, K.data.inv d₁}, {d₂, K.data.inv d₂}} ⊆ K.data.edges := by
      intro e he
      rcases mem_insert.1 he with rfl | he
      · exact pair_inv_mem_edges _ _
      · rw [mem_singleton.1 he]
        exact pair_inv_mem_edges _ _
    have h𝓔B : ∀ e ∈ ({{d₁, K.data.inv d₁}, {d₂, K.data.inv d₂}} : Finset (Finset K.Dart)),
        Disjoint e K.data.bdry := by
      intro e he
      rcases mem_insert.1 he with rfl | he
      · exact hB d₁ hd₁
      · rw [mem_singleton.1 he]
        exact hB d₂ hd₂
    obtain ⟨hK1, hπ1, hf1⟩ := hK.edgeExcision_of_isHollowDigon_of_colour_ne hf h𝓔 h𝓔B hc
    obtain ⟨G'', hnl, hπ'', hf''⟩ := hK1.exists_isNearlyLeafless
    exact ⟨G'', hnl, hπ''.trans (hπ1.trans hπ.symm), by omega⟩

end PlabicGraph

end ClusterAlgebras
