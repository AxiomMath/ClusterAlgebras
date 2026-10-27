/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FixedLollipopProp
public import ClusterAlgebras.Plabic.ReducedNoRoundtrip
public import ClusterAlgebras.Plabic.TripSides

/-!
# The trip of a fixed point of a reduced graph is traversed both ways

Let `G` be a reduced plabic graph and let `k` be a fixed point of its trip permutation `π_G`.
Then the set of darts of the one-way trip from `k` is closed under `d ↦ d̄`: the trip runs out
along some edges and comes back along the same edges.

By `PlabicGraph.IsReduced.exists_isLollipop_or_isCollapsible_of_tripPerm_eq_self`, `G` has a
lollipop at `k` or a collapsible tree with root `β(k)`. For a lollipop `{λ}`, the one-way trip
from `k` is `(g_k, ḡ_k)` with `ḡ_k = λ`. For a collapsible tree `T = (β(k), W)`, the graph has no
roundtrip (`PlabicGraph.IsReduced.not_hasRoundtrip`), so the trip from `g_k` runs through the
darts `D_T` of `T` in one piece and ends at `ḡ_k` (`PlabicData.RootedTree.exists_tripChain`); the
next dart is `g_k` again, so the set of darts of the one-way trip is `D_T`, which is closed under
`d ↦ d̄`.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.inv_mem_oneWayTrip_of_tripPerm_eq_self`: the trip of a
  fixed point of a reduced graph is traversed both ways.

## Implementation notes

* Labels are `0`-indexed: `k : Fin b` is FWZ's label `k + 1`. FWZ's
  `d ∈ darts(k)` is `d ∈ G.data.oneWayTrip k`.
* Both cases go through one criterion: if `T^N(g_k) = ḡ_k`, no `Tⁿ(g_k)` with `1 ≤ n ≤ N` is a
  leg, and the darts `Tⁿ(g_k)`, `0 ≤ n ≤ N`, are closed under `d ↦ d̄`, then `m_k = N + 1` and
  the one-way trip from `k` consists of these darts.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- If the trip from `g_k` reaches `ḡ_k` after `N` steps without meeting a leg in between, and the
darts `Tⁿ(g_k)`, `0 ≤ n ≤ N`, are closed under `d ↦ d̄`, then so are the darts of the one-way trip
from `k`. -/
private theorem IsPlabicGraph.inv_mem_oneWayTrip_of_chain (hG : G.IsPlabicGraph) {k : Fin b}
    {N : ℕ} (hN : G.tripMap^[N] (G.leg k) = G.inv (G.leg k))
    (hleg : ∀ n, 0 < n → n ≤ N → ¬G.IsLeg (G.tripMap^[n] (G.leg k)))
    (hinv : ∀ n ≤ N, ∃ n' ≤ N, G.inv (G.tripMap^[n] (G.leg k)) = G.tripMap^[n'] (G.leg k))
    {d : H} (hd : d ∈ G.oneWayTrip k) : G.inv d ∈ G.oneWayTrip k := by
  have hb : G.IsBoundaryVertex (G.vertexOf (G.leg k)) :=
    (G.mem_boundaryVertices.1 (hG.bvertex_mem k)).2
  have hN1 : G.tripMap^[N + 1] (G.leg k) = G.leg k := by
    rw [Function.iterate_succ_apply', hN, tripMap_apply, hG.inv_involutive]
    exact turn_of_isBoundaryVertex hb
  have hle : G.tripLength k ≤ N + 1 := tripLength_le (Nat.succ_pos N) ⟨k, hN1.symm⟩
  obtain ⟨hpos, hm⟩ := tripLength_spec ⟨N + 1, Nat.succ_pos N, k, hN1.symm⟩
  have hlen : G.tripLength k = N + 1 := by
    by_contra h
    exact hleg _ hpos (by omega) hm
  obtain ⟨n, hn, rfl⟩ := mem_oneWayTrip.1 hd
  obtain ⟨n', hn', e⟩ := hinv n (by omega)
  exact mem_oneWayTrip.2 ⟨n', by omega, e.symm⟩

end PlabicData

namespace PlabicGraph

open PlabicData

/-- Let `G` be a reduced plabic graph with `b` boundary vertices, let `k : Fin b` be a fixed
point of the trip permutation `G.data.tripPerm`, and let `d` be a dart of the one-way trip from
`k`. Then `G.data.inv d` is also a dart of the one-way trip from `k`. -/
@[cluster_algebras "lem_fixed_trip_closed"]
theorem IsReduced.inv_mem_oneWayTrip_of_tripPerm_eq_self {b : ℕ} {G : PlabicGraph b}
    (hG : G.IsReduced) {k : Fin b} (hk : G.data.tripPerm k = k) {d : G.Dart}
    (hd : d ∈ G.data.oneWayTrip k) : G.data.inv d ∈ G.data.oneWayTrip k := by
  have hP := G.isPlabicGraph
  have hb : G.data.IsBoundaryVertex (G.data.vertexOf (G.data.leg k)) :=
    (G.data.mem_boundaryVertices.1 (hP.bvertex_mem k)).2
  rcases hG.exists_isLollipop_or_isCollapsible_of_tripPerm_eq_self hk with
    ⟨v, ⟨hv, hv1⟩, l, hl, hlk⟩ | ⟨T, hT, -⟩
  · /- A lollipop `{λ}` at `k`: the one-way trip is `(g_k, ḡ_k)` with `ḡ_k = λ`. -/
    obtain ⟨hvV, hvB⟩ := G.data.mem_internalVertices.1 hv
    obtain ⟨r, rfl⟩ := G.data.mem_vertices.1 hvV
    have hlv : G.data.vertexOf l = G.data.vertexOf r := G.data.vertexOf_eq_of_mem hl
    have hlB : l ∉ G.data.bdry :=
      notMem_bdry_of_mem_vertexOf (by rw [hlv]; exact hvB) (G.data.self_mem_vertexOf l)
    have hinvl : G.data.inv l = G.data.leg k :=
      DiskMap.eq_of_notMem_bdry hP.boundaryVertex_card hb hlk (G.data.self_mem_vertexOf _)
        (fun h => hlB (hP.inv_mem_bdry_iff.1 h)) (hP.leg_notMem_bdry k)
    have hinvk : G.data.inv (G.data.leg k) = l := by
      rw [← hinvl, hP.inv_involutive]
    have hturn : G.data.turn l = l := by
      have h1 := turn_mem_vertexOf (G := G.data) l
      rw [hlv] at h1
      obtain ⟨x, hx⟩ := card_eq_one.1 hv1
      rw [hx] at h1 hl
      rw [mem_singleton.1 h1, mem_singleton.1 hl]
    have h1 : G.data.tripMap^[1] (G.data.leg k) = l := by
      rw [Function.iterate_one, tripMap_apply, hinvk, hturn]
    have hlnot : ¬G.data.IsLeg l :=
      hP.not_isLeg_of_not_isBoundaryVertex (by rw [hlv]; exact hvB)
    refine hP.inv_mem_oneWayTrip_of_chain (N := 1) (by rw [h1, hinvk])
      (fun n hn hn1 => ?_) (fun n hn => ?_) hd
    · obtain rfl : n = 1 := by omega
      rw [h1]
      exact hlnot
    · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · exact ⟨1, le_rfl, by rw [h1, Function.iterate_zero, id, hinvk]⟩
      · exact ⟨0, Nat.zero_le _, by rw [h1, Function.iterate_zero, id, hinvl]⟩
  · /- A collapsible tree `T` with root `β(k)`: the one-way trip runs through `D_T`. -/
    have hR := hG.not_hasRoundtrip
    have hTb : G.data.IsBoundaryVertex T.root := by rw [hT]; exact hb
    have hs : T.tripEntry = G.data.leg k := by
      rw [T.tripEntry_of_isBoundaryVertex hTb]
      exact DiskMap.eq_of_notMem_bdry hP.boundaryVertex_card hb
        (by rw [← bvertex, ← hT]; exact T.intervalStart_mem_root) (G.data.self_mem_vertexOf _)
        (G.data.mem_treeDarts.1 T.intervalStart_mem_darts).1 (hP.leg_notMem_bdry k)
    have hz : T.tripExit = G.data.inv (G.data.leg k) := by
      rw [T.tripExit_of_isBoundaryVertex hTb, ← hs, T.tripEntry_of_isBoundaryVertex hTb]
    obtain ⟨N, hinj, hX, hN⟩ := T.exists_tripChain hP hR
    rw [hs] at hinj hX hN
    rw [hz] at hN
    have hmem : ∀ n ≤ N, G.data.tripMap^[n] (G.data.leg k) ∈ T.darts := fun n hn => by
      rw [hX]
      exact mem_image.2 ⟨n, mem_range.2 (by omega), rfl⟩
    refine hP.inv_mem_oneWayTrip_of_chain hN (fun n hn hnN hl => ?_) (fun n hn => ?_) hd
    · have h0 := hinj (Set.mem_Iic.2 hnN) (Set.mem_Iic.2 (Nat.zero_le N))
        ((T.eq_tripEntry_of_isLeg hP (hmem n hnN) hl).trans hs)
      omega
    · have h := T.inv_mem_darts hP (hmem n hn)
      rw [hX] at h
      obtain ⟨n', hn', e⟩ := mem_image.1 h
      exact ⟨n', by rw [mem_range] at hn'; omega, e.symm⟩

end PlabicGraph

end ClusterAlgebras
