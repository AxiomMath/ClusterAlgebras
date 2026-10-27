/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CollapseTrips
public import ClusterAlgebras.Plabic.External
public import ClusterAlgebras.Plabic.FaceLabels
public import ClusterAlgebras.Plabic.FixedTripClosed
public import ClusterAlgebras.Plabic.ReducedNoRoundtrip
public import ClusterAlgebras.Plabic.ResonanceTheorem

/-!
# Face labels of a reduced plabic graph have the same size

Let `G` be a reduced plabic graph with `b` boundary vertices. A one-way trip of `G` from a label
`i` with `π_G(i) ≠ i` has pendant self-crossings: every edge it traverses in both directions lies
in a part of the graph attached to the rest at a single vertex, whose edges the trip traverses
either in both directions or not at all. This is proved by induction on the number of darts: a
nearly leafless reduced graph has the resonance property, which forbids any edge traversed both
ways by such a trip; otherwise a collapsible tree is collapsed and the pendant sets are lifted
back.

Consequently the winding function `h_i` of the trip takes only the values `0` and `1`, so every
face lies either to the right or to the left of the trip. Crossing an edge `{d, d̄}` with
`d ∈ darts(i)` and `d̄ ∈ darts(j)` from the face `f(d)` to the face `f(d̄)` removes `j` from the
source label and adds `i`. Since a face next to the exterior has a source label of size the number
`a` of anti-excedances of the decorated trip permutation `π̃_G`, and every face is reached from the
exterior by crossing edges, all source labels, and hence all target labels, have `a` elements.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.hasPendantSelfCrossings`: trips of reduced graphs have
  pendant self-crossings.
* `ClusterAlgebras.PlabicGraph.IsReduced.tripWinding_eq_zero_or_eq_one`: the winding function of
  a trip of a reduced graph takes the values `0` and `1`.
* `ClusterAlgebras.PlabicGraph.IsReduced.sourceLabel_indicator_sub`: crossing an edge exchanges
  one label element.
* `ClusterAlgebras.PlabicGraph.IsReduced.card_sourceLabel_eq_and_card_targetLabel_eq`: face
  labels have `a` elements.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`, FWZ's
  `d ∈ darts(i)` is `d ∈ G.data.oneWayTrip i`, and FWZ's orbit `f(d)` of `φ` is
  `G.data.faceOf d` (as a subtype of the orbits, `G.data.toFaceOrbit d`).
* FWZ assume `b ≥ 2` for the winding function of a trip; it follows from `π_G(i) ≠ i`
  and is not assumed.
* FWZ's Iverson brackets `[P]` are the integers `if P then 1 else 0`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- A dart of a one-way trip is not in `B`. -/
private theorem notMem_bdry_of_mem_oneWayTrip (hG : G.IsPlabicGraph) {i : Fin b} {d : H}
    (hd : d ∈ G.oneWayTrip i) : d ∉ G.bdry := by
  obtain ⟨k, -, rfl⟩ := mem_oneWayTrip.1 hd
  clear hd
  induction k with
  | zero => exact hG.leg_notMem_bdry i
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact fun h => ih ((tripMap_mem_bdry_iff hG _).1 h)

/-- The only leg on the one-way trip from `i` is `g_i`. -/
private theorem eq_leg_of_mem_oneWayTrip_of_isLeg {i : Fin b} {d : H}
    (hd : d ∈ G.oneWayTrip i) (hl : G.IsLeg d) : d = G.leg i := by
  obtain ⟨k, hk, rfl⟩ := mem_oneWayTrip.1 hd
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  · exact absurd hl (not_isLeg_of_lt_tripLength hk0 hk)

/-- If `x` and `x̄` lie on the one-way trip from `i` and `x̄` is a leg, then `π_G(i) = i`. -/
private theorem tripPerm_eq_self_of_inv_isLeg (hG : G.IsPlabicGraph) {i : Fin b} {x : H}
    (hx : x ∈ G.oneWayTrip i) (hx' : G.inv x ∈ G.oneWayTrip i) (hl : G.IsLeg (G.inv x)) :
    G.tripPerm i = i := by
  have hgi : G.inv x = G.leg i := eq_leg_of_mem_oneWayTrip_of_isLeg hx' hl
  obtain ⟨n, hn, rfl⟩ := mem_oneWayTrip.1 hx
  have hstep : G.tripMap^[n + 1] (G.leg i) = G.leg i := by
    rw [Function.iterate_succ_apply', tripMap_apply, hgi,
      turn_of_isBoundaryVertex (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))]
  have hle : G.tripLength i ≤ n + 1 := tripLength_le (Nat.succ_pos n) ⟨i, hstep.symm⟩
  rw [hG.tripPerm_eq_iff, show G.tripLength i = n + 1 by omega, hstep]

/-- An edge traversed in both directions by the one-way trip from `i` has the label `{i}`. -/
private theorem edgeLabel_edgeOf_eq_singleton (hG : G.IsPlabicGraph) {i : Fin b} {x : H}
    (hx : x ∈ G.oneWayTrip i) (hx' : G.inv x ∈ G.oneWayTrip i) :
    G.edgeLabel (G.edgeOf x) = {i} := by
  ext k
  simp only [mem_edgeLabel, G.mem_edgeOf, mem_singleton]
  constructor
  · rintro ⟨d, hd | hd, hdk⟩ <;> subst hd
    · exact hG.eq_of_mem_oneWayTrip hdk hx
    · exact hG.eq_of_mem_oneWayTrip hdk hx'
  · rintro rfl
    exact ⟨x, Or.inl rfl, hx⟩

/-- In a plabic graph with the resonance property, a one-way trip from `i` with `π_G(i) ≠ i`
traverses no edge in both directions. -/
private theorem false_of_mem_of_inv_mem (hG : G.IsPlabicGraph) (hres : G.HasResonanceProperty)
    {i : Fin b} (hi : G.tripPerm i ≠ i) {x : H} (hx : x ∈ G.oneWayTrip i)
    (hx' : G.inv x ∈ G.oneWayTrip i) : False := by
  have hinv := hG.inv_involutive
  by_cases hl : G.IsLeg (G.inv x)
  · exact hi (tripPerm_eq_self_of_inv_isLeg hG hx hx' hl)
  by_cases hl' : G.IsLeg x
  · exact hi (tripPerm_eq_self_of_inv_isLeg hG hx' (by rwa [hinv]) (by rwa [hinv]))
  have hxB := notMem_bdry_of_mem_oneWayTrip hG hx
  have hxB' := notMem_bdry_of_mem_oneWayTrip hG hx'
  have hint : ¬G.IsBoundaryVertex (G.vertexOf x) := fun h => by
    obtain ⟨j, hj⟩ := hG.exists_eq_leg_of_isBoundaryVertex h hxB
    exact hl' ⟨j, hj.symm⟩
  by_cases hlol : ∃ j, G.IsLollipop j (G.vertexOf x)
  · -- `v(x)` is a lollipop: then `x̄` lies at a boundary vertex, so it is a leg
    obtain ⟨j, ⟨-, hcard⟩, d, hd, hdj⟩ := hlol
    obtain rfl : d = x := by
      obtain ⟨a, ha⟩ := card_eq_one.1 hcard
      have hx₀ := G.self_mem_vertexOf x
      rw [ha, mem_singleton] at hd hx₀
      rw [hd, hx₀]
    have hb : G.IsBoundaryVertex (G.vertexOf (G.inv d)) := by
      rw [G.vertexOf_eq_of_mem hdj]
      exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
    obtain ⟨j', hj'⟩ := hG.exists_eq_leg_of_isBoundaryVertex hb hxB'
    exact hl ⟨j', hj'.symm⟩
  · -- otherwise the resonance condition gives the edge of `x` a label of two elements
    push Not at hlol
    have h2 := (hres _ (G.vertexOf_mem_internalVertices.2 hint) hlol).card_edgeLabel
      (G.self_mem_vertexOf x)
    rw [edgeLabel_edgeOf_eq_singleton hG hx hx', card_singleton] at h2
    omega

/-- The darts `D_T` of a rooted tree are pendant at its root. -/
private theorem RootedTree.isPendantAt_root_darts (hG : G.IsPlabicGraph) (T : G.RootedTree) :
    G.IsPendantAt T.root (T.darts : Set H) where
  notMem_bdry d hd := T.notMem_bdry_of_mem_darts hd
  inv_mem d hd := T.inv_mem_darts hG hd
  vertexOf_mem_internalVertices d hd hne := by
    rcases T.vertexOf_mem_or_eq_root hG hd with h | h
    · exact T.nonRoot_subset h
    · exact absurd h hne
  mem_of_mem_vertexOf d hd hne e he := by
    rcases T.vertexOf_mem_or_eq_root hG hd with h | h
    · exact T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_eq_of_mem he])
    · exact absurd h hne

/-- If `G` has no roundtrip and a rooted tree with root `β(y₀)`, then `π_G(y₀) = y₀`. -/
private theorem RootedTree.tripPerm_eq_self_of_root_eq (hG : G.IsPlabicGraph)
    (hR : ¬G.HasRoundtrip) (T : G.RootedTree) {y₀ : Fin b} (hT0 : T.root = G.bvertex y₀) :
    G.tripPerm y₀ = y₀ := by
  have hb : G.IsBoundaryVertex T.root :=
    hT0 ▸ G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem y₀)
  have hentry : T.tripEntry = G.leg y₀ := by
    rw [T.tripEntry_of_isBoundaryVertex hb, T.intervalStart_eq_leg hG hT0]
  obtain ⟨N, hinj, hX, hN⟩ := T.exists_tripChain hG hR
  rw [hentry] at hinj hX hN
  rw [T.tripExit_of_isBoundaryVertex hb, T.intervalStart_eq_leg hG hT0] at hN
  have hstep : G.tripMap^[N + 1] (G.leg y₀) = G.leg y₀ := by
    rw [Function.iterate_succ_apply', hN, tripMap_apply, hG.inv_involutive,
      turn_of_isBoundaryVertex (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem y₀))]
  have hle : G.tripLength y₀ ≤ N + 1 := tripLength_le (Nat.succ_pos N) ⟨y₀, hstep.symm⟩
  have heq : G.tripLength y₀ = N + 1 := by
    by_contra hne
    have hlt : G.tripLength y₀ ≤ N := by omega
    obtain ⟨hpos, hleg⟩ := tripLength_spec (hG.exists_isLeg_iterate_tripMap y₀)
    have hmem : G.tripMap^[G.tripLength y₀] (G.leg y₀) ∈ T.darts := by
      rw [hX]
      exact mem_image.2 ⟨_, mem_range.2 (by omega), rfl⟩
    have h1 := T.eq_tripEntry_of_isLeg hG hmem hleg
    rw [hentry] at h1
    have := hinj (Set.mem_Iic.2 hlt) (Set.mem_Iic.2 (Nat.zero_le N)) (by simpa using h1)
    omega
  rw [hG.tripPerm_eq_iff, heq, hstep]

/-- A fixed point `k` of `π_G` lies in the source label of a face exactly when it is a white
fixed point of `π̃_G`. -/
private theorem mem_sourceLabel_iff_isWhiteFixed (hG : G.IsPlabicGraph) {k : Fin b}
    (hk : G.tripPerm k = k) (f : Finset H) :
    k ∈ G.sourceLabel f ↔ (G.decoratedTripPerm hG.tripPerm_bijective).IsWhiteFixed k := by
  rw [mem_sourceLabel, isLeftOfTrip_iff_of_eq hk,
    DecoratedPerm.isWhiteFixed_iff_of_perm_apply_eq _ hk]
  rfl

/-- For a dart `e` of the exterior, the source label of the orbit `f(ē)` has `a(π̃_G)`
elements. -/
private theorem card_sourceLabel_faceOf_inv_of_mem_exterior (hG : G.IsPlabicGraph) {e : H}
    (he : e ∈ G.exterior) :
    #(G.sourceLabel (G.faceOf (G.inv e))) =
      (G.decoratedTripPerm hG.tripPerm_bijective).numAntiExcedances := by
  have heB : e ∈ G.bdry := G.exterior_subset_bdry he
  have hinvext : G.inv e ∉ G.exterior := fun h =>
    disjoint_left.1 hG.disjoint_exterior_map_inv h (mem_map_of_mem _ he)
  obtain ⟨y, hy⟩ := hG.exists_bvertex_eq _
    (G.vertexOf_mem_boundaryVertices.2 (G.isBoundaryVertex_vertexOf_of_mem heB))
  set x := (finRotate b).symm y
  have hxy : finRotate b x = y := Equiv.apply_symm_apply _ _
  rw [← (G.decoratedTripPerm hG.tripPerm_bijective).card_cyclicIco_add_card_isWhiteFixed x,
    ← card_union_of_disjoint]
  · congr 1
    ext k
    simp only [mem_union, mem_filter, mem_univ, true_and, decoratedTripPerm_perm_apply]
    by_cases hk : G.tripPerm k = k
    · rw [mem_sourceLabel_iff_isWhiteFixed hG hk]
      exact ⟨Or.inr, fun h => h.elim (fun h' => absurd hk h'.1) id⟩
    have hnw : ¬(G.decoratedTripPerm hG.tripPerm_bijective).IsWhiteFixed k := fun h =>
      hk h.perm_apply_eq
    obtain ⟨h, hW, -⟩ := hG.existsUnique_isTripWinding hk
    rw [mem_sourceLabel, hG.isLeftOfTrip_iff hk hW (G.faceOf_mem_faceOrbits _)]
    have hc := hW.sub_eq_tripCycle e
    have h0 : h ⟨G.faceOf e, G.faceOf_mem_faceOrbits e⟩ = 0 :=
      hW.eq_zero_of_eq_exterior _ (hG.toIsDiskMap.faceOf_eq_exterior he)
    have hiff : (∃ x' ∈ cyclicIco k (G.tripPerm k),
        G.vertexOf e = G.bvertex (finRotate b x')) ↔ x ∈ cyclicIco k (G.tripPerm k) := by
      refine ⟨fun ⟨x', hx', hv⟩ => ?_, fun hx => ⟨x, hx, by rw [hxy, hy]⟩⟩
      exact (finRotate b).injective
        ((hG.bvertex_injective (hv.symm.trans hy.symm)).trans hxy.symm) ▸ hx'
    rw [h0, sub_zero, tripCycle_of_mem_bdry heB] at hc
    simp only [he, true_and, hiff, hinvext, false_and, if_false] at hc
    rw [hc]
    by_cases hx : x ∈ cyclicIco k (G.tripPerm k) <;> simp [hx, hk, hnw]
  · exact disjoint_filter.2 fun k _ h hw => h.1 hw.perm_apply_eq

/-- In a plabic graph without roundtrip, the trip of a dart off `B` contains a leg. -/
theorem exists_leg_mem_trip_of_notMem_bdry (hR : ¬G.HasRoundtrip) {y : H} (hy : y ∉ G.bdry) :
    ∃ j, G.leg j ∈ G.trip y := by
  by_contra hcon
  push Not at hcon
  exact hR (hasRoundtrip_iff.2 ⟨y, hy, fun n ⟨j, hj⟩ => hcon j ⟨n, hj.symm⟩⟩)

/-- Collapsing a rooted tree with internal root `T` keeps the trip permutation:
`π_G = π_{G/{(T, c)}}`. -/
theorem RootedTree.tripPerm_eq_tripPerm_collapse (hG : G.IsPlabicGraph) (hR : ¬G.HasRoundtrip)
    (T : G.RootedTree) (c : Shade) (hroot : ¬G.IsBoundaryVertex T.root)
    (h1 : (G.collapse {(T, c)}).IsPlabicGraph) :
    G.tripPerm = (G.collapse {(T, c)}).tripPerm := by
  let e : {x | x ∈ G.collapseDarts {(T, c)} ∧ x ∉ G.bdry} ≃
      {x : G.collapseDarts {(T, c)} | x ∉ (G.collapse {(T, c)}).bdry} :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun h => x.2.2 (mem_collapse_bdry.1 h)⟩
      invFun := fun x => ⟨x.1.1, x.1.2, fun h => x.2 (mem_collapse_bdry.2 h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine hG.tripPerm_eq_of_firstReturn h1 e
    (fun j => ⟨⟨G.collapseCore_subset _ (G.leg_mem_collapseCore _ j),
      hG.leg_notMem_bdry j⟩, rfl⟩) fun y => ?_
  apply Subtype.ext
  have hmemY : h1.tripEquiv (e y : G.collapseDarts {(T, c)}) ∈
      {x : G.collapseDarts {(T, c)} | x ∉ (G.collapse {(T, c)}).bdry} :=
    fun h => (e y).2 ((tripMap_mem_bdry_iff h1 _).1 h)
  rw [coe_firstReturn_of_apply_mem (π := h1.tripEquiv) hmemY]
  exact Subtype.ext (T.coe_tripMap_collapse hG hR c hroot ⟨y.1, y.2.1⟩ y.2.2).symm

/-- **Lifting pendant self-crossings along a collapse with boundary root.** Let `T` be a rooted
tree with root `β(y₀)` and `i ≠ y₀` with `π_G(i) ≠ i`. If the one-way trip from `i` in
`G/{(T, c)}` has pendant self-crossings, so does the one-way trip from `i` in `G`. -/
theorem RootedTree.hasPendantSelfCrossings_of_collapse_of_eq_bvertex (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (c : Shade) {y₀ i : Fin b} (hT0 : T.root = G.bvertex y₀) (hi : i ≠ y₀)
    (h1 : (G.collapse {(T, c)}).IsPlabicGraph) (hpi : G.tripPerm i ≠ i)
    (ih : (G.collapse {(T, c)}).tripPerm i ≠ i →
      (G.collapse {(T, c)}).HasPendantSelfCrossings i) :
    G.HasPendantSelfCrossings i := by
  intro x hx hx'
  have hcoe := fun m => T.coe_iterate_tripMap_collapse_leg hG c hT0 hi m
  have hleg : ∀ y : G.collapseDarts {(T, c)},
      (G.collapse {(T, c)}).IsLeg y ↔ G.IsLeg (y : H) := fun y =>
    ⟨fun ⟨j, hj⟩ => ⟨j, congrArg Subtype.val hj⟩, fun ⟨j, hj⟩ => ⟨j, Subtype.ext hj⟩⟩
  have hlen : (G.collapse {(T, c)}).tripLength i = G.tripLength i := by
    unfold tripLength
    congr 1
    ext m
    simp only [Set.mem_setOf_eq, hleg, hcoe]
  have hπ : (G.collapse {(T, c)}).tripPerm i = G.tripPerm i := by
    rw [h1.tripPerm_eq_iff, hlen]
    exact Subtype.ext ((hcoe _).trans (hG.leg_tripPerm i).symm)
  obtain ⟨k, hk, rfl⟩ := mem_oneWayTrip.1 hx
  obtain ⟨l, hl, hl'⟩ := mem_oneWayTrip.1 hx'
  have hx'1 : (G.collapse {(T, c)}).tripMap^[k] ((G.collapse {(T, c)}).leg i) ∈
      (G.collapse {(T, c)}).oneWayTrip i :=
    mem_oneWayTrip.2 ⟨k, by rwa [hlen], rfl⟩
  have hx'2 : (G.collapse {(T, c)}).inv
      ((G.collapse {(T, c)}).tripMap^[k] ((G.collapse {(T, c)}).leg i)) ∈
      (G.collapse {(T, c)}).oneWayTrip i := by
    have : (G.collapse {(T, c)}).inv
        ((G.collapse {(T, c)}).tripMap^[k] ((G.collapse {(T, c)}).leg i)) =
        (G.collapse {(T, c)}).tripMap^[l] ((G.collapse {(T, c)}).leg i) :=
      Subtype.ext (by rw [coe_collapse_inv hG, hcoe k, hcoe l, hl'])
    rw [this]
    exact mem_oneWayTrip.2 ⟨l, by rwa [hlen], rfl⟩
  obtain ⟨w', hw', D', hD', hxD', hsym⟩ := ih (by rwa [hπ]) _ hx'1 hx'2
  obtain ⟨w, hw, D, hD, hsub, hDsym⟩ :=
    T.exists_isPendantAt_of_collapse_of_eq_bvertex hG c hT0 hi hw' hD' hsym
  exact ⟨w, hw, D, hD, hsub ⟨_, hxD', hcoe k⟩, hDsym⟩

/-- **Lifting pendant self-crossings along a collapse with internal root.** Let `T` be a
collapsible tree of colour `c` with internal root and `π_G(i) ≠ i`. If the one-way trip from `i`
in `G/{(T, c)}` has pendant self-crossings, so does the one-way trip from `i` in `G`. -/
theorem RootedTree.IsCollapsibleOfColour.hasPendantSelfCrossings_of_collapse
    (hG : G.IsPlabicGraph) (hR : ¬G.HasRoundtrip) {T : G.RootedTree} {c : Shade}
    (hT : T.IsCollapsibleOfColour c) (hroot : ¬G.IsBoundaryVertex T.root) {i : Fin b}
    (h1 : (G.collapse {(T, c)}).IsPlabicGraph) (hpi : G.tripPerm i ≠ i)
    (ih : (G.collapse {(T, c)}).tripPerm i ≠ i →
      (G.collapse {(T, c)}).HasPendantSelfCrossings i) :
    G.HasPendantSelfCrossings i := by
  intro x hx hx'
  by_cases hxT : x ∈ T.darts
  · exact ⟨T.root, T.root_mem_vertices, T.darts, T.isPendantAt_root_darts hG, hxT,
      fun y hy => T.mem_oneWayTrip_iff_inv_mem hG hR hroot i hy⟩
  have hmem : ∀ y, y ∉ T.darts → y ∈ G.collapseDarts {(T, c)} := fun y hy =>
    Or.inl (Or.inl fun h => hy (by simpa [familyDarts] using h))
  have hxB := notMem_bdry_of_mem_oneWayTrip hG hx
  have hxB' := notMem_bdry_of_mem_oneWayTrip hG hx'
  let x' : G.collapseDarts {(T, c)} := ⟨x, hmem x hxT⟩
  have hinv' : ((G.collapse {(T, c)}).inv x' : H) = G.inv x := coe_collapse_inv hG x'
  have hx'1 : x' ∈ (G.collapse {(T, c)}).oneWayTrip i :=
    (hT.mem_oneWayTrip_collapse_iff hG hR hroot i x' hxB).2 hx
  have hx'2 : (G.collapse {(T, c)}).inv x' ∈ (G.collapse {(T, c)}).oneWayTrip i :=
    (hT.mem_oneWayTrip_collapse_iff hG hR hroot i _ (by rwa [hinv'])).2 (by rwa [hinv'])
  obtain ⟨w', hw', D', hD', hxD', hsym⟩ :=
    ih (by rwa [← T.tripPerm_eq_tripPerm_collapse hG hR c hroot h1]) x' hx'1 hx'2
  obtain ⟨w, hw, D, hD, hsub, hDsym⟩ :=
    hT.exists_isPendantAt_of_collapse hG hR hroot i hw' hD' hsym
  exact ⟨w, hw, D, hD, hsub ⟨x', hxD', rfl⟩, hDsym⟩

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- Let `G` be a reduced plabic graph with `b` boundary vertices and let `i` be a label with
`π_G(i) ≠ i`. Then the one-way trip from `i` has pendant self-crossings. -/
@[cluster_algebras "lem_reduced_trip_pendant"]
theorem IsReduced.hasPendantSelfCrossings {G : PlabicGraph b} (hG : G.IsReduced) {i : Fin b}
    (hi : G.data.tripPerm i ≠ i) : G.data.HasPendantSelfCrossings i := by
  induction hn : Fintype.card G.Dart using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  have hP := G.isPlabicGraph
  have hR := hG.not_hasRoundtrip
  intro x hx hx'
  by_cases hnl : G.data.IsNearlyLeafless
  · exact (false_of_mem_of_inv_mem hP ((isReduced_iff_hasResonanceProperty hnl).1 hG) hi hx
      hx').elim
  unfold IsNearlyLeafless at hnl
  push Not at hnl
  obtain ⟨v, hv, hvl⟩ := hnl
  rcases (hG G (.refl _ _)).2 v hv with ⟨j, hj⟩ | ⟨T, ⟨c, hT⟩, -⟩
  · exact absurd hj (hvl j)
  obtain ⟨h1, hmove⟩ := hT.moveEquivalent_collapse hP
  have hred : IsReduced ⟨_, G.data.collapse {(T, c)}, h1⟩ :=
    hG.of_moveEquivalent (hmove.mono (Set.subset_univ _))
  obtain ⟨z, hz⟩ := hT.exists_notMem_collapseDarts hP
  have hlt : Fintype.card (G.data.collapseDarts {(T, c)}) < n := by
    rw [← hn]
    exact Fintype.card_subtype_lt hz
  by_cases hroot : G.data.IsBoundaryVertex T.root
  · obtain ⟨y₀, hy₀⟩ := hP.exists_bvertex_eq _
      (G.data.mem_boundaryVertices.2 ⟨T.root_mem_vertices, hroot⟩)
    have hiy : i ≠ y₀ := by
      rintro rfl
      exact hi (T.tripPerm_eq_self_of_root_eq hP hR hy₀.symm)
    exact T.hasPendantSelfCrossings_of_collapse_of_eq_bvertex hP c hy₀.symm hiy h1 hi
      (fun h => ih _ hlt hred h rfl) x hx hx'
  · exact hT.hasPendantSelfCrossings_of_collapse hP hR hroot h1 hi
      (fun h => ih _ hlt hred h rfl) x hx hx'

/-- **Crossing a dart keeps the values of a winding function in `{0, 1}`.** Let `G` be a reduced
plabic graph, let `π_G(i) ≠ i`, and let `h` be a winding function of the one-way trip from `i`.
If `h(f(d)) ∈ {0, 1}`, then `h(f(d̄)) ∈ {0, 1}`. -/
theorem IsReduced.tripWinding_inv_eq_zero_or_eq_one {G : PlabicGraph b} (hG : G.IsReduced)
    {i : Fin b} (hi : G.data.tripPerm i ≠ i) {h : G.data.faceOrbits → ℤ}
    (hW : G.data.IsTripWinding i h) {d : G.Dart}
    (hd : h (G.data.toFaceOrbit d) = 0 ∨ h (G.data.toFaceOrbit d) = 1) :
    h (G.data.toFaceOrbit (G.data.inv d)) = 0 ∨ h (G.data.toFaceOrbit (G.data.inv d)) = 1 := by
  have hP := G.isPlabicGraph
  have hPS := hG.hasPendantSelfCrossings hi
  have hzero : ∀ d ∈ G.data.exterior, h (G.data.toFaceOrbit d) = 0 := fun d hd =>
    hW.eq_zero_of_eq_exterior _ (hP.toIsDiskMap.faceOf_eq_exterior hd)
  -- The two sides of a dart traversed by the trip in one direction only.
  have hside : ∀ d ∈ G.data.oneWayTrip i, G.data.inv d ∉ G.data.oneWayTrip i →
      h (G.data.toFaceOrbit d) = 0 ∧ h (G.data.toFaceOrbit (G.data.inv d)) = 1 := by
    intro d hd hd'
    obtain ⟨n, hn, rfl⟩ := mem_oneWayTrip.1 hd
    have := hP.tripWinding_right_eq_zero_and_left_eq_one hi hPS hW (n := n + 1) (by omega)
      (by omega) (by rwa [Nat.add_sub_cancel])
    rwa [Nat.add_sub_cancel] at this
  have hc := hW.sub_eq_tripCycle d
  change h (G.data.toFaceOrbit (G.data.inv d)) - h (G.data.toFaceOrbit d) = _ at hc
  by_cases hB : d ∈ G.data.bdry
  · rw [tripCycle_of_mem_bdry hB] at hc
    split_ifs at hc with h₁ h₂
    · rw [hzero d h₁.1] at hc
      exact Or.inr (by omega)
    · exact Or.inl (hzero _ h₂.1)
    · omega
  · rw [tripCycle_of_notMem_bdry hB] at hc
    by_cases h₁ : d ∈ G.data.oneWayTrip i <;> by_cases h₂ : G.data.inv d ∈ G.data.oneWayTrip i
    · simp only [h₁, h₂, if_true, sub_self] at hc
      omega
    · exact Or.inr (hside d h₁ h₂).2
    · exact Or.inl (hside _ h₂ (by rwa [hP.inv_involutive])).1
    · simp only [h₁, h₂, if_false, sub_self] at hc
      omega

/-- Let `G` be a reduced plabic graph, let `π_G(i) ≠ i`, and let `h` be a winding function of the
one-way trip from `i`. Then `h(f) ∈ {0, 1}` for every orbit `f` of `φ`. -/
@[cluster_algebras "lem_trip_winding_binary"]
theorem IsReduced.tripWinding_eq_zero_or_eq_one {G : PlabicGraph b} (hG : G.IsReduced)
    {i : Fin b} (hi : G.data.tripPerm i ≠ i) {h : G.data.faceOrbits → ℤ}
    (hW : G.data.IsTripWinding i h) (f : G.data.faceOrbits) : h f = 0 ∨ h f = 1 := by
  have hP := G.isPlabicGraph
  obtain ⟨k, F, d, hF0, hFk, hFd⟩ :=
    hP.toIsConnected.exists_face_chain hP.exterior_mem_faceOrbits f.2
  have key : ∀ s (hs : s < k + 1), ∃ e, G.data.faceOf e = F ⟨s, hs⟩ ∧
      (h (G.data.toFaceOrbit e) = 0 ∨ h (G.data.toFaceOrbit e) = 1) := by
    intro s
    induction s with
    | zero =>
      intro hs
      obtain ⟨d₀, hd₀⟩ := G.data.mem_faceOrbits.1 hP.exterior_mem_faceOrbits
      exact ⟨d₀, hd₀.trans hF0.symm, Or.inl (hW.eq_zero_of_eq_exterior _ hd₀)⟩
    | succ s ih =>
      intro hs
      obtain ⟨e, he, hhe⟩ := ih (by omega)
      have hd := hFd ⟨s, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hd
      have heq : G.data.toFaceOrbit (d ⟨s, by omega⟩) = G.data.toFaceOrbit e :=
        Subtype.ext (hd.1.trans he.symm)
      exact ⟨_, hd.2, hG.tripWinding_inv_eq_zero_or_eq_one hi hW (heq ▸ hhe)⟩
  obtain ⟨e, he, hhe⟩ := key k (by omega)
  have : f = G.data.toFaceOrbit e := Subtype.ext (by
    change (f : Finset G.Dart) = G.data.faceOf e
    rw [he, ← hFk]
    rfl)
  rwa [this]

/-- Let `G` be a reduced plabic graph, let `d ∉ B` be a dart with `d ∈ darts(i)` and
`d̄ ∈ darts(j)`. Then for every label `k`,
`[k ∈ I_src(f(d̄))] - [k ∈ I_src(f(d))] = [k = i] - [k = j]`. -/
@[cluster_algebras "lem_face_label_edge_step"]
theorem IsReduced.sourceLabel_indicator_sub {G : PlabicGraph b} (hG : G.IsReduced)
    {d : G.Dart} (hd : d ∉ G.data.bdry) {i j : Fin b} (hi : d ∈ G.data.oneWayTrip i)
    (hj : G.data.inv d ∈ G.data.oneWayTrip j) (k : Fin b) :
    ((if k ∈ G.data.sourceLabel (G.data.faceOf (G.data.inv d)) then 1 else 0 : ℤ) -
        if k ∈ G.data.sourceLabel (G.data.faceOf d) then 1 else 0) =
      (if k = i then 1 else 0) - if k = j then 1 else 0 := by
  have hP := G.isPlabicGraph
  have hdk : d ∈ G.data.oneWayTrip k ↔ k = i :=
    ⟨fun h => hP.eq_of_mem_oneWayTrip h hi, fun h => h ▸ hi⟩
  have hdk' : G.data.inv d ∈ G.data.oneWayTrip k ↔ k = j :=
    ⟨fun h => hP.eq_of_mem_oneWayTrip h hj, fun h => h ▸ hj⟩
  by_cases hk : G.data.tripPerm k = k
  · -- A fixed point lies on the same side of every face, and its trip is traversed both ways.
    have hsame : k ∈ G.data.sourceLabel (G.data.faceOf (G.data.inv d)) ↔
        k ∈ G.data.sourceLabel (G.data.faceOf d) := by
      rw [mem_sourceLabel, mem_sourceLabel, isLeftOfTrip_iff_of_eq hk, isLeftOfTrip_iff_of_eq hk]
    rw [if_congr hsame rfl rfl, sub_self]
    have hij : k = i ↔ k = j :=
      ⟨fun hki => hdk'.1 (hG.inv_mem_oneWayTrip_of_tripPerm_eq_self hk (hdk.2 hki)), fun hkj => by
        have := hG.inv_mem_oneWayTrip_of_tripPerm_eq_self hk (hdk'.2 hkj)
        rw [hP.inv_involutive] at this
        exact hdk.1 this⟩
    by_cases h₁ : k = i
    · simp [h₁, ← hij.1 h₁]
    · simp [h₁, (not_congr hij).1 h₁]
  · -- Otherwise the brackets are the values of the winding function `h_k`.
    obtain ⟨h, hW, -⟩ := hP.existsUnique_isTripWinding hk
    have hval : ∀ g (hg : g ∈ G.data.faceOrbits),
        (if k ∈ G.data.sourceLabel g then (1 : ℤ) else 0) = h ⟨g, hg⟩ := by
      intro g hg
      by_cases hm : k ∈ G.data.sourceLabel g
      · rw [if_pos hm, (hP.isLeftOfTrip_iff hk hW hg).1 (mem_sourceLabel.1 hm)]
      · rw [if_neg hm]
        rcases hG.tripWinding_eq_zero_or_eq_one hk hW ⟨g, hg⟩ with h0 | h0
        · rw [h0]
        · exact absurd (mem_sourceLabel.2 ((hP.isLeftOfTrip_iff hk hW hg).2 h0)) hm
    rw [hval _ (G.data.faceOf_mem_faceOrbits _), hval _ (G.data.faceOf_mem_faceOrbits _),
      hW.sub_eq_tripCycle d, tripCycle_of_notMem_bdry hd, if_congr hdk rfl rfl,
      if_congr hdk' rfl rfl]

/-- **Crossing a dart into a face keeps the size of the source label.** Let `G` be a reduced
plabic graph and `e` a dart with `f(ē)` not the exterior. If `f(e)` is the exterior or its source
label has `a(π̃_G)` elements, then the source label of `f(ē)` has `a(π̃_G)` elements. -/
theorem IsReduced.card_sourceLabel_faceOf_inv {G : PlabicGraph b} (hG : G.IsReduced) {e : G.Dart}
    (hne : G.data.faceOf (G.data.inv e) ≠ G.data.exterior)
    (hcard_faceOf : G.data.faceOf e ≠ G.data.exterior → #(G.data.sourceLabel (G.data.faceOf e)) =
      (G.data.decoratedTripPerm G.isPlabicGraph.tripPerm_bijective).numAntiExcedances) :
    #(G.data.sourceLabel (G.data.faceOf (G.data.inv e))) =
      (G.data.decoratedTripPerm G.isPlabicGraph.tripPerm_bijective).numAntiExcedances := by
  have hP := G.isPlabicGraph
  have hR := hG.not_hasRoundtrip
  by_cases heB : e ∈ G.data.bdry
  · have he : e ∈ G.data.exterior := by
      rw [← hP.exterior_union_map_inv, mem_union] at heB
      rcases heB with he | he
      · exact he
      · obtain ⟨a, ha, hae⟩ := mem_map.1 he
        refine absurd ?_ hne
        change G.data.inv a = e at hae
        rw [← hae, hP.inv_involutive]
        exact hP.toIsDiskMap.faceOf_eq_exterior ha
    exact card_sourceLabel_faceOf_inv_of_mem_exterior hP he
  have hfe : G.data.faceOf e ≠ G.data.exterior := fun h =>
    heB (G.data.exterior_subset_bdry (h ▸ G.data.self_mem_faceOf e))
  have heB' : G.data.inv e ∉ G.data.bdry := fun h => heB (hP.inv_mem_bdry_iff.1 h)
  obtain ⟨i, hi, -⟩ := hP.existsUnique_mem_oneWayTrip (exists_leg_mem_trip_of_notMem_bdry hR heB)
  obtain ⟨j, hj, -⟩ := hP.existsUnique_mem_oneWayTrip (exists_leg_mem_trip_of_notMem_bdry hR heB')
  have hcard : ∀ s : Finset (Fin b), (#s : ℤ) = ∑ k, if k ∈ s then (1 : ℤ) else 0 := fun s => by
    simp
  have hsum : (#(G.data.sourceLabel (G.data.faceOf (G.data.inv e))) : ℤ) -
      #(G.data.sourceLabel (G.data.faceOf e)) = 0 := by
    rw [hcard, hcard, ← sum_sub_distrib]
    simp_rw [hG.sourceLabel_indicator_sub heB hi hj]
    simp [sum_sub_distrib]
  have := hcard_faceOf hfe
  omega

/-- Let `G` be a reduced plabic graph with `b` boundary vertices, and let `a` be the number of
anti-excedances of its decorated trip permutation `π̃_G`. Then `|I_src(f)| = |I_tgt(f)| = a`
for every face `f` of `G`. -/
@[cluster_algebras "thm_face_labels_size"]
theorem IsReduced.card_sourceLabel_eq_and_card_targetLabel_eq {G : PlabicGraph b}
    (hG : G.IsReduced) {f : Finset G.Dart} (hf : f ∈ G.data.faces) :
    #(G.data.sourceLabel f) =
        (G.data.decoratedTripPerm G.isPlabicGraph.tripPerm_bijective).numAntiExcedances ∧
      #(G.data.targetLabel f) =
        (G.data.decoratedTripPerm G.isPlabicGraph.tripPerm_bijective).numAntiExcedances := by
  have hP := G.isPlabicGraph
  suffices hs : #(G.data.sourceLabel f) =
      (G.data.decoratedTripPerm hP.tripPerm_bijective).numAntiExcedances from
    ⟨hs, (card_targetLabel hP.tripPerm_bijective.injective f).trans hs⟩
  obtain ⟨hfne, hfo⟩ := G.data.mem_faces.1 hf
  obtain ⟨k, F, d, hF0, hFk, hFd⟩ :=
    hP.toIsConnected.exists_face_chain hP.exterior_mem_faceOrbits hfo
  have key : ∀ s (hs : s < k + 1), F ⟨s, hs⟩ ≠ G.data.exterior →
      #(G.data.sourceLabel (F ⟨s, hs⟩)) =
        (G.data.decoratedTripPerm hP.tripPerm_bijective).numAntiExcedances := by
    intro s
    induction s with
    | zero =>
      intro hs h0
      exact absurd hF0 h0
    | succ s ih =>
      intro hs hne
      have hd := hFd ⟨s, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hd
      rw [← hd.2] at hne ⊢
      exact hG.card_sourceLabel_faceOf_inv hne fun h => by
        have := ih (by omega) (by rwa [← hd.1])
        rwa [← hd.1] at this
  have := key k (by omega) (by
    change F (Fin.last k) ≠ _
    rwa [hFk])
  change #(G.data.sourceLabel (F (Fin.last k))) = _ at this
  rwa [hFk] at this

end PlabicGraph

end ClusterAlgebras
