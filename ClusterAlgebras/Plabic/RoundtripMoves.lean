/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BivalentMoves
public import ClusterAlgebras.Plabic.EdgeContractionMoves
public import ClusterAlgebras.Plabic.LocalMoves
public import ClusterAlgebras.Plabic.SquareTrips

/-!
# Roundtrips persist under local moves

A plabic graph `G` has a *roundtrip* if some orbit of its trip map on `H \ B` contains no leg.
This file shows that having a roundtrip is invariant under move equivalence: if `G ∼ G'`, then `G`
has a roundtrip if and only if `G'` has one.

An isomorphism `θ : K → K'` of plabic graphs commutes with the trip maps (`Iso.map_tripMap`) and
maps `H \ B` onto `H' \ B'` (`Iso.bijOn_compl_bdry`), and it maps the leg `g_i` to the leg `g'_i`;
so it maps the orbits of the trip map of `K` containing no leg onto those of `K'`. A square move,
the removal of a bivalent vertex and the contraction of an edge each keep roundtrips
(`IsPlabicGraph.hasRoundtrip_squareMove_iff`, `IsPlabicGraph.hasRoundtrip_bivalentRemoval_iff`,
`IsPlabicGraph.hasRoundtrip_contractEdge_iff`). Combining these, each step of a move equivalence
keeps roundtrips, and the result follows by induction on the length of the sequence of steps.

## Main results

* `ClusterAlgebras.PlabicData.Iso.hasRoundtrip_iff`: isomorphic plabic graphs have roundtrips
  simultaneously.
* `ClusterAlgebras.PlabicGraph.IsLocalMove.hasRoundtrip_iff`: a local move keeps roundtrips.
* `ClusterAlgebras.PlabicGraph.MoveEquivalent.hasRoundtrip_iff`: roundtrips persist under local
  moves.

## Implementation notes

* The invariance is proved for `S`-equivalence for an arbitrary set `S` of move types; the
  move equivalence `G ∼ G'` of FWZ is the case `S = Set.univ`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicData

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {G : PlabicData H b} {G' : PlabicData H' b}

namespace Iso

/-- An isomorphism commutes with the iterates of the trip maps. -/
theorem map_iterate_tripMap (θ : G.Iso G') (n : ℕ) (d : H) :
    θ.toEquiv (G.tripMap^[n] d) = G'.tripMap^[n] (θ.toEquiv d) :=
  Function.Semiconj.iterate_right (f := θ.toEquiv) θ.map_tripMap n d

/-- An isomorphism of plabic graphs maps legs to legs, and darts that are not legs to darts that
are not legs. -/
theorem isLeg_apply_iff (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (θ : G.Iso G') (d : H) :
    G'.IsLeg (θ.toEquiv d) ↔ G.IsLeg d := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, θ.toEquiv.injective (by rw [θ.map_leg hG hG', hj])⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, (θ.map_leg hG hG' j).symm⟩

/-- **Isomorphic plabic graphs have roundtrips simultaneously**: an isomorphism of plabic graphs
maps the orbits of the trip map containing no leg onto the orbits containing no leg. -/
theorem hasRoundtrip_iff (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (θ : G.Iso G') :
    G.HasRoundtrip ↔ G'.HasRoundtrip := by
  rw [PlabicData.hasRoundtrip_iff, PlabicData.hasRoundtrip_iff]
  constructor
  · rintro ⟨d, hd, h⟩
    refine ⟨θ.toEquiv d, by rwa [θ.mem_bdry_iff], fun n hn => h n ?_⟩
    rwa [← θ.map_iterate_tripMap, θ.isLeg_apply_iff hG hG'] at hn
  · rintro ⟨d, hd, h⟩
    refine ⟨θ.toEquiv.symm d, by rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply],
      fun n hn => h n ?_⟩
    rwa [← θ.isLeg_apply_iff hG hG', θ.map_iterate_tripMap, Equiv.apply_symm_apply] at hn

end Iso

/-- Isomorphic plabic graphs have roundtrips simultaneously. -/
theorem Isomorphic.hasRoundtrip_iff (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (h : G.Isomorphic G') : G.HasRoundtrip ↔ G'.HasRoundtrip :=
  h.elim fun θ => θ.hasRoundtrip_iff hG hG'

end PlabicData

namespace PlabicGraph

variable {b : ℕ} {G G' : PlabicGraph b}

/-- Isomorphic plabic graphs have roundtrips simultaneously. -/
theorem Isomorphic.hasRoundtrip_iff (h : G.Isomorphic G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip :=
  PlabicData.Isomorphic.hasRoundtrip_iff G.isPlabicGraph G'.isPlabicGraph h

/-- A square move (M1) keeps roundtrips. -/
theorem IsSquareMove.hasRoundtrip_iff (h : G.IsSquareMove G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  obtain ⟨c, hq, hiso⟩ := h
  rw [← G.isPlabicGraph.hasRoundtrip_squareMove_iff hq]
  exact (hiso.hasRoundtrip_iff G'.isPlabicGraph (G.isPlabicGraph.squareMove c)).symm

/-- The removal of a bivalent vertex (M2) keeps roundtrips. -/
theorem IsBivalentRemoval.hasRoundtrip_iff (h : G.IsBivalentRemoval G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  obtain ⟨d, hd, hiso⟩ := h
  rw [G.isPlabicGraph.hasRoundtrip_bivalentRemoval_iff hd]
  exact (hiso.hasRoundtrip_iff G'.isPlabicGraph
    (PlabicData.isPlabicGraph_bivalentRemoval G.isPlabicGraph hd)).symm

/-- The contraction of an edge (M3) keeps roundtrips. -/
theorem IsEdgeContraction.hasRoundtrip_iff {d : G.Dart} (h : G.IsEdgeContraction G' d) :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  obtain ⟨he, hiso⟩ := h
  rw [← G.isPlabicGraph.hasRoundtrip_contractEdge_iff he]
  exact (hiso.hasRoundtrip_iff G'.isPlabicGraph (G.isPlabicGraph.contractEdge he)).symm

/-- A local move keeps roundtrips. -/
theorem IsLocalMove.hasRoundtrip_iff {t : LocalMoveType} (h : IsLocalMove t G G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  cases t with
  | m1 => exact IsSquareMove.hasRoundtrip_iff h
  | m2 =>
    rcases h with h | h
    · exact h.hasRoundtrip_iff
    · exact h.hasRoundtrip_iff.symm
  | m3 =>
    rcases h with ⟨d, h⟩ | ⟨d, h⟩
    · exact h.hasRoundtrip_iff
    · exact h.hasRoundtrip_iff.symm

/-- A step of an `S`-equivalence keeps roundtrips. -/
theorem MoveStep.hasRoundtrip_iff {S : Set LocalMoveType} (h : MoveStep S G G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  rcases h with h | ⟨t, -, h⟩
  · exact h.hasRoundtrip_iff.symm
  · exact h.hasRoundtrip_iff

/-- **Roundtrips persist under local moves**: if `G` and `G'` are `S`-equivalent plabic graphs,
for any set `S` of move types, then `G` has a roundtrip if and only if `G'` has one. In
particular this holds when `G ∼ G'`, the case `S = Set.univ`. -/
@[cluster_algebras "lem_roundtrip_move_invariant"]
theorem MoveEquivalent.hasRoundtrip_iff {S : Set LocalMoveType} (h : MoveEquivalent S G G') :
    G.data.HasRoundtrip ↔ G'.data.HasRoundtrip := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.hasRoundtrip_iff

end PlabicGraph

end ClusterAlgebras
