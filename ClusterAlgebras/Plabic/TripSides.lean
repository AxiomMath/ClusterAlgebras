/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CycleSpace
public import ClusterAlgebras.Plabic.TripleDiagram
public import ClusterAlgebras.Plabic.TripRuns
public import ClusterAlgebras.Plabic.TripWinding
public import ClusterAlgebras.Plabic.Trees
public import ClusterAlgebras.Plabic.Winding

/-!
# The sides of a trip

Let `G` be a plabic graph and `i` a label with `j = π_G(i) ≠ i`. The cycle `c_i` of the one-way
trip `(d₁, …, d_m)` from `i`, closed up by the exterior arcs from `β(j)` back to `β(i)`, is
antisymmetric and sums to zero at every vertex; so it has exactly one winding function `h_i`,
a function on the orbits of `φ` vanishing at the exterior whose jump across every dart `d` is
`c_i(d)`. Walking along the trip, the sharpest-turn rule keeps the face on the right of the trip
at a black vertex and the face on the left at a white vertex; when the trip has pendant
self-crossings this shows that `h_i` is `0` on the right and `1` on the left of every dart of the
trip that the trip does not traverse in both directions.

A trip that enters a rooted tree `T = (v, W)` runs through all of its darts `D_T` in one piece,
from the first dart of the interval of `T` (or the last, at a white root) to the reverse of the
last (or the first); when the root is internal, it therefore traverses every edge of `T` in both
directions.

## Main definitions

* `ClusterAlgebras.PlabicData.RootedTree.intervalEnd`: the last dart `a_k` of the interval of a
  rooted tree.
* `ClusterAlgebras.PlabicData.RootedTree.tripEntry`,
  `ClusterAlgebras.PlabicData.RootedTree.tripExit`: the darts `s` and `z` at which a trip enters
  and leaves a rooted tree.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.existsUnique_isTripWinding`: a one-way trip has
  exactly one winding function.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripWinding_right_eq_zero_and_left_eq_one`: the
  winding function of a trip is `0` on the right and `1` on the left of a trip dart.
* `ClusterAlgebras.PlabicData.RootedTree.exists_tripChain`: a trip runs through a rooted tree in
  one piece.
* `ClusterAlgebras.PlabicData.RootedTree.mem_oneWayTrip_iff_inv_mem`: a trip traverses a tree with
  internal root in both directions.

## Implementation notes

* **Labels.** As throughout the chapter, the label set `[1, b]` is `Fin b`, `0`-indexed: the
  element `i : Fin b` is FWZ's label `i + 1`, FWZ's `x⁻` is `(finRotate b).symm x`
  and `β(x)` is `bvertex x`. FWZ's `n`-th dart `d_n` of the one-way trip from `i`
  (`1 ≤ n ≤ m_i`) is `T^{n-1}(g_i)`.
* **Superfluous hypotheses.** FWZ assume `b ≥ 2` for the existence of the winding
  function and for the two sides of a trip dart; it follows from `π_G(i) ≠ i` and is not assumed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- At an internal black vertex `v(d̄)` the trip turns into the orbit of `φ` of `d`:
`f(T(d)) = f(d)`. -/
private theorem toFaceOrbit_tripMap_of_black {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf (G.inv d))) (hc : G.colour (G.inv d) = .black) :
    G.toFaceOrbit (G.tripMap d) = G.toFaceOrbit d := by
  rw [tripMap_apply, turn_of_black hd hc]
  exact G.toFaceOrbit_facePerm d

section IsPlabicGraph

variable (hG : G.IsPlabicGraph)

include hG

/-! ### The values of the cycle at a boundary vertex -/

/-- The reverse of a dart of the exterior is not in the exterior. -/
private theorem inv_notMem_exterior {d : H} (hd : d ∈ G.exterior) : G.inv d ∉ G.exterior :=
  fun h => disjoint_left.1 hG.disjoint_exterior_map_inv h
    (mem_map_equiv.2 (by simpa using hd))

/-- The trip map sends the reverse of a leg to the leg. -/
private theorem tripMap_inv_leg (x : Fin b) : G.tripMap (G.inv (G.leg x)) = G.leg x := by
  rw [tripMap_apply, hG.inv_involutive]
  exact turn_of_isBoundaryVertex (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem x))

/-- The reverse of the leg `g_x` is a dart of the one-way trip from `i` exactly when
`π_G(i) = x`. -/
private theorem inv_leg_mem_oneWayTrip_iff {i x : Fin b} :
    G.inv (G.leg x) ∈ G.oneWayTrip i ↔ x = G.tripPerm i := by
  constructor
  · intro h
    obtain ⟨n, hn, hnd⟩ := mem_oneWayTrip.1 h
    have hleg : G.tripMap^[n + 1] (G.leg i) = G.leg x := by
      rw [Function.iterate_succ_apply', hnd, tripMap_inv_leg hG]
    have hle := tripLength_le (Nat.succ_pos n) ⟨x, hleg.symm⟩
    have hm : G.tripLength i = n + 1 := by omega
    exact ((hG.tripPerm_eq_iff).2 (by rw [hm, hleg])).symm
  · rintro rfl
    have hpos := hG.tripLength_pos i
    refine mem_oneWayTrip.2 ⟨G.tripLength i - 1, by omega, ?_⟩
    apply (tripMap_bijective hG).injective
    rw [tripMap_inv_leg hG, hG.leg_tripPerm, ← Function.iterate_succ_apply' G.tripMap,
      Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]

/-- The leg `g_x` is a dart of the one-way trip from `i` exactly when `x = i`. -/
private theorem leg_mem_oneWayTrip_iff {i x : Fin b} : G.leg x ∈ G.oneWayTrip i ↔ x = i := by
  rw [← mem_tripSet, hG.tripSet_leg, mem_singleton, eq_comm]

/-- The cycle at a leg: `c_i(g_x) = [x = i] - [x = π_G(i)]`. -/
private theorem tripCycle_leg (i x : Fin b) :
    G.tripCycle i (G.leg x) =
      (if x = i then 1 else 0) - if x = G.tripPerm i then 1 else 0 := by
  rw [tripCycle_of_notMem_bdry (hG.leg_notMem_bdry x)]
  simp only [leg_mem_oneWayTrip_iff hG, inv_leg_mem_oneWayTrip_iff hG]

/-- The cycle at the dart `p` of the exterior at `β(x)`: `c_i(p) = [x⁻ ∈ [i, π_G(i))_b]`. -/
private theorem tripCycle_of_mem_exterior {i x : Fin b} {p : H} (hp : p ∈ G.exterior)
    (hpx : p ∈ G.bvertex x) :
    G.tripCycle i p = if (finRotate b).symm x ∈ cyclicIco i (G.tripPerm i) then 1 else 0 := by
  have hv : G.vertexOf p = G.bvertex x := G.vertexOf_eq_of_mem hpx
  rw [tripCycle_of_mem_bdry (G.exterior_subset_bdry hp)]
  by_cases hc : (finRotate b).symm x ∈ cyclicIco i (G.tripPerm i)
  · rw [if_pos ⟨hp, _, hc, by rw [hv, Equiv.apply_symm_apply]⟩, if_pos hc]
  · rw [if_neg, if_neg (fun h => inv_notMem_exterior hG hp h.1), if_neg hc]
    rintro ⟨-, x', hx', hv'⟩
    obtain rfl := hG.bvertex_injective (hv.symm.trans hv')
    rw [Equiv.symm_apply_apply] at hc
    exact hc hx'

/-- The cycle at the reverse of the dart `q` of the exterior at `β(x + 1)`:
`c_i(q̄) = -[x ∈ [i, π_G(i))_b]`. -/
private theorem tripCycle_inv_of_mem_exterior {i x : Fin b} {q : H} (hq : q ∈ G.exterior)
    (hqx : q ∈ G.bvertex (finRotate b x)) :
    G.tripCycle i (G.inv q) = -if x ∈ cyclicIco i (G.tripPerm i) then 1 else 0 := by
  have hv : G.vertexOf q = G.bvertex (finRotate b x) := G.vertexOf_eq_of_mem hqx
  rw [tripCycle_of_mem_bdry (hG.inv_mem_bdry _ (G.exterior_subset_bdry hq)),
    if_neg (fun h => inv_notMem_exterior hG hq h.1), hG.inv_involutive]
  by_cases hc : x ∈ cyclicIco i (G.tripPerm i)
  · rw [if_pos ⟨hq, x, hc, hv⟩, if_pos hc]
  · rw [if_neg, if_neg hc, neg_zero]
    rintro ⟨-, x', hx', hv'⟩
    obtain rfl := (finRotate b).injective (hG.bvertex_injective (hv.symm.trans hv'))
    exact hc hx'

/-! ### A one-way trip has exactly one winding function -/

/-- The cycle of a one-way trip is antisymmetric: `c_i(d̄) = -c_i(d)`. -/
theorem tripCycle_inv (i : Fin b) (d : H) : G.tripCycle i (G.inv d) = -G.tripCycle i d := by
  by_cases hd : d ∈ G.bdry
  · rw [tripCycle_of_mem_bdry (hG.inv_mem_bdry _ hd), tripCycle_of_mem_bdry hd, hG.inv_involutive d]
    have hne : ¬(d ∈ G.exterior ∧ G.inv d ∈ G.exterior) := fun h =>
      inv_notMem_exterior hG h.1 h.2
    split_ifs <;> simp_all
  · have hd' : G.inv d ∉ G.bdry := fun h => hd (hG.inv_mem_bdry_iff.1 h)
    rw [tripCycle_of_notMem_bdry hd', tripCycle_of_notMem_bdry hd, hG.inv_involutive d]
    ring

/-- The cycle of a one-way trip sums to zero at every internal vertex. -/
private theorem sum_tripCycle_of_not_isBoundaryVertex (i : Fin b) {v : Finset H}
    (hv : v ∈ G.vertices) (hb : ¬G.IsBoundaryVertex v) : ∑ d ∈ v, G.tripCycle i d = 0 := by
  obtain ⟨d₀, rfl⟩ := G.mem_vertices.1 hv
  have hint : ∀ d ∈ G.vertexOf d₀, ¬G.IsBoundaryVertex (G.vertexOf d) := fun d hd => by
    rwa [G.vertexOf_eq_of_mem hd]
  have hmem : ∀ d ∈ G.vertexOf d₀, ∀ e ∈ G.vertexOf d, e ∈ G.vertexOf d₀ := fun d hd e he => by
    rwa [G.vertexOf_eq_of_mem hd] at he
  -- `[d̄ ∈ darts(i)] = [σ^{±1}(d) ∈ darts(i)]`, and the turn permutes the darts of the vertex.
  have hstep : ∀ d ∈ G.vertexOf d₀,
      (G.inv d ∈ G.oneWayTrip i ↔ G.turn d ∈ G.oneWayTrip i) := fun d hd => by
    have hT : G.tripMap (G.inv d) = G.turn d := by rw [tripMap_apply, hG.inv_involutive]
    have hnl : ¬G.IsLeg (G.tripMap (G.inv d)) := by
      rw [hT]
      exact hG.not_isLeg_of_not_isBoundaryVertex (by rw [vertexOf_turn]; exact hint d hd)
    rw [← mem_tripSet, ← mem_tripSet, ← hT, hG.tripSet_tripMap hnl]
  have hsum : ∑ d ∈ G.vertexOf d₀, (if G.inv d ∈ G.oneWayTrip i then (1 : ℤ) else 0) =
      ∑ d ∈ G.vertexOf d₀, (if d ∈ G.oneWayTrip i then (1 : ℤ) else 0) :=
    Finset.sum_nbij' G.turn G.turnInv (fun d hd => hmem d hd _ (turn_mem_vertexOf d))
      (fun d hd => hmem d hd _ (turnInv_mem_vertexOf d)) (fun d _ => turnInv_turn hG d)
      (fun d _ => turn_turnInv hG d) fun d hd => by simp only [hstep d hd]
  rw [Finset.sum_congr rfl fun d hd => tripCycle_of_notMem_bdry
    (notMem_bdry_of_mem_vertexOf (hint d₀ (G.self_mem_vertexOf d₀)) hd), Finset.sum_sub_distrib,
    hsum, sub_self]

/-- The cycle of a one-way trip from `i` with `π_G(i) ≠ i` sums to zero at every boundary
vertex `β(x)`. -/
private theorem sum_tripCycle_bvertex {i : Fin b} (hi : G.tripPerm i ≠ i) (x : Fin b) :
    ∑ d ∈ G.bvertex x, G.tripCycle i d = 0 := by
  obtain ⟨q, hq, hqx₁, hqx⟩ := hG.exists_exterior x
  obtain ⟨p, hp, hpx, -⟩ := hG.exists_exterior ((finRotate b).symm x)
  rw [Equiv.apply_symm_apply] at hpx
  obtain ⟨hset, -⟩ := DiskMap.rot_cycle_of_mem_boundaryVertices hG.inv_involutive
    hG.inv_mem_bdry hG.boundaryVertex_card hG.exists_orbit (hG.bvertex_mem x) hp hpx hq hqx
    (G.leg_mem_bvertex x) (hG.leg_notMem_bdry x)
  have hqB : G.inv q ∈ G.bdry := hG.inv_mem_bdry _ (G.exterior_subset_bdry hq)
  have hqp : G.inv q ≠ p := fun h => inv_notMem_exterior hG hq (h ▸ hp)
  have hqg : G.inv q ≠ G.leg x := fun h => hG.leg_notMem_bdry x (h ▸ hqB)
  have hpg : p ≠ G.leg x := fun h => hG.leg_notMem_bdry x (h ▸ G.exterior_subset_bdry hp)
  rw [hset, sum_insert (by simp [hqp, hqg]), sum_pair hpg, tripCycle_inv_of_mem_exterior hG hq hqx₁,
    tripCycle_of_mem_exterior hG hp hpx, tripCycle_leg hG]
  have := cyclicIco_ends (Ne.symm hi) x
  linarith

/-- The cycle of a one-way trip from `i` with `π_G(i) ≠ i` sums to zero at every vertex. -/
theorem sum_tripCycle_eq_zero {i : Fin b} (hi : G.tripPerm i ≠ i) {v : Finset H}
    (hv : v ∈ G.vertices) : ∑ d ∈ v, G.tripCycle i d = 0 := by
  by_cases hb : G.IsBoundaryVertex v
  · obtain ⟨x, rfl⟩ := hG.exists_bvertex_eq v (G.mem_boundaryVertices.2 ⟨hv, hb⟩)
    exact sum_tripCycle_bvertex hG hi x
  · exact sum_tripCycle_of_not_isBoundaryVertex hG i hv hb

/-- If `π_G(i) ≠ i`, the one-way trip from `i` has exactly one winding function. -/
@[cluster_algebras "lem_trip_side_exists"]
theorem IsPlabicGraph.existsUnique_isTripWinding {i : Fin b} (hi : G.tripPerm i ≠ i) :
    ∃! h : G.faceOrbits → ℤ, G.IsTripWinding i h := by
  obtain ⟨h, ⟨h0, hc⟩, huniq⟩ := hG.toIsDiskMap.existsUnique_faceFunction (G.tripCycle i)
    (tripCycle_inv hG i) fun v hv => sum_tripCycle_eq_zero hG hi hv
  refine ⟨h, ⟨fun f hf => ?_, hc⟩, fun h' hh' => huniq h' ⟨?_, hh'.sub_eq_tripCycle⟩⟩
  · rw [show f = ⟨G.exterior, hG.exterior_mem_faceOrbits⟩ from Subtype.ext hf]
    exact h0
  · exact hh'.eq_zero_of_eq_exterior _ rfl

/-! ### The two sides of a trip dart -/

/-- At an internal white vertex `v(d̄)` the trip keeps the orbit of `φ` on its left:
`f(T(d)‾) = f(d̄)`. -/
private theorem toFaceOrbit_inv_tripMap_of_white {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf (G.inv d))) (hc : G.colour (G.inv d) = .white) :
    G.toFaceOrbit (G.inv (G.tripMap d)) = G.toFaceOrbit (G.inv d) := by
  have : G.facePerm (G.inv (G.tripMap d)) = G.inv d := by
    rw [G.facePerm_apply, hG.inv_involutive, tripMap_apply, turn_of_white hd hc,
      Equiv.apply_symm_apply]
  rw [← this, G.toFaceOrbit_facePerm]

/-- The darts `T^t(g_i)` are not in `B`. -/
private theorem iterate_leg_notMem_bdry (i : Fin b) (t : ℕ) :
    G.tripMap^[t] (G.leg i) ∉ G.bdry := by
  induction t with
  | zero => exact hG.leg_notMem_bdry i
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact fun h => ih ((tripMap_mem_bdry_iff hG _).1 h)

/-- For `t + 1 < m_i`, the vertex `v(d̄)` of the dart `d = T^t(g_i)` is internal. -/
private theorem not_isBoundaryVertex_vertexOf_inv_iterate {i : Fin b} {t : ℕ}
    (ht : t + 1 < G.tripLength i) :
    ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.tripMap^[t] (G.leg i)))) := by
  intro hb
  have hdB : G.inv (G.tripMap^[t] (G.leg i)) ∉ G.bdry := fun h =>
    iterate_leg_notMem_bdry hG i t (hG.inv_mem_bdry_iff.1 h)
  obtain ⟨x, hx⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hb)
  have hleg : G.inv (G.tripMap^[t] (G.leg i)) = G.leg x :=
    DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hb (G.self_mem_vertexOf _)
      (by rw [← hx]; exact G.leg_mem_bvertex x) hdB (hG.leg_notMem_bdry x)
  refine not_isLeg_of_lt_tripLength (Nat.succ_pos t) ht ⟨x, ?_⟩
  rw [Function.iterate_succ_apply', tripMap_apply, turn_of_isBoundaryVertex hb, hleg]

/-- A winding function of the one-way trip from `i` vanishes on the orbit of `φ` of the leg
`g_i`, when `π_G(i) ≠ i`. -/
private theorem tripWinding_leg {i : Fin b} (hi : G.tripPerm i ≠ i) {h : G.faceOrbits → ℤ}
    (hW : G.IsTripWinding i h) : h (G.toFaceOrbit (G.leg i)) = 0 := by
  obtain ⟨q, hq, -, hqx⟩ := hG.exists_exterior i
  obtain ⟨p, hp, hpx, -⟩ := hG.exists_exterior ((finRotate b).symm i)
  rw [Equiv.apply_symm_apply] at hpx
  obtain ⟨-, -, hpg, -⟩ := DiskMap.rot_cycle_of_mem_boundaryVertices hG.inv_involutive
    hG.inv_mem_bdry hG.boundaryVertex_card hG.exists_orbit (hG.bvertex_mem i) hp hpx hq hqx
    (G.leg_mem_bvertex i) (hG.leg_notMem_bdry i)
  have hf : G.toFaceOrbit (G.leg i) = G.toFaceOrbit (G.inv p) := by
    rw [← hpg, ← G.toFaceOrbit_facePerm (G.inv p), G.facePerm_apply, hG.inv_involutive]
  have hp0 : h (G.toFaceOrbit p) = 0 :=
    hW.eq_zero_of_eq_exterior _ (hG.toIsDiskMap.faceOf_eq_exterior hp)
  have hw : h (G.toFaceOrbit (G.inv p)) - h (G.toFaceOrbit p) = G.tripCycle i p :=
    hW.sub_eq_tripCycle p
  rw [tripCycle_of_mem_exterior hG hp hpx] at hw
  have hiJ : i ∈ cyclicIco i (G.tripPerm i) := by
    rw [mem_cyclicIco]
    rcases lt_or_ge i (G.tripPerm i) with h | h
    exacts [Or.inl ⟨h, le_rfl, h⟩, Or.inr ⟨h, Or.inl le_rfl⟩]
  have he := cyclicIco_ends (Ne.symm hi) i
  rw [if_pos hiJ, if_neg (Ne.symm hi), if_pos rfl] at he
  rw [hf]
  split_ifs at hw he <;> linarith

/-- For `t < m_i`, if `T^t(g_i)‾` is not a dart of the trip then `h` is `0` and `1` on the two
sides of `T^t(g_i)`; otherwise, with `k < t` the last index at which the trip leaves a dart it does
not traverse back, `h` takes on both sides of `T^t(g_i)` the value `1` if `v(T^k(g_i)‾)` is white
and `0` if it is black. -/
private theorem tripWinding_sides_aux {i : Fin b} (hi : G.tripPerm i ≠ i)
    (hP : G.HasPendantSelfCrossings i) {h : G.faceOrbits → ℤ} (hW : G.IsTripWinding i h) :
    ∀ t, t < G.tripLength i →
      (G.inv (G.tripMap^[t] (G.leg i)) ∉ G.oneWayTrip i →
        h (G.toFaceOrbit (G.tripMap^[t] (G.leg i))) = 0 ∧
          h (G.toFaceOrbit (G.inv (G.tripMap^[t] (G.leg i)))) = 1) ∧
      (G.inv (G.tripMap^[t] (G.leg i)) ∈ G.oneWayTrip i →
        ∃ k < t, G.inv (G.tripMap^[k] (G.leg i)) ∉ G.oneWayTrip i ∧
          (∀ s, k < s → s ≤ t → G.inv (G.tripMap^[s] (G.leg i)) ∈ G.oneWayTrip i) ∧
          h (G.toFaceOrbit (G.tripMap^[t] (G.leg i))) =
            (if G.colour (G.inv (G.tripMap^[k] (G.leg i))) = .white then 1 else 0) ∧
          h (G.toFaceOrbit (G.inv (G.tripMap^[t] (G.leg i)))) =
            (if G.colour (G.inv (G.tripMap^[k] (G.leg i))) = .white then 1 else 0)) := by
  have hw : ∀ t, t < G.tripLength i →
      h (G.toFaceOrbit (G.inv (G.tripMap^[t] (G.leg i)))) -
        h (G.toFaceOrbit (G.tripMap^[t] (G.leg i))) =
        if G.inv (G.tripMap^[t] (G.leg i)) ∈ G.oneWayTrip i then 0 else 1 := by
    intro t ht
    refine (hW.sub_eq_tripCycle _).trans ?_
    split_ifs with hs
    · exact tripCycle_eq_zero_of_mem_of_inv_mem (iterate_leg_notMem_bdry hG i t)
        (iterate_mem_oneWayTrip ht) hs
    · exact tripCycle_eq_one (iterate_leg_notMem_bdry hG i t) (iterate_mem_oneWayTrip ht) hs
  intro t
  induction t with
  | zero =>
    intro h0
    have hR := tripWinding_leg hG hi hW
    have hs : G.inv (G.leg i) ∉ G.oneWayTrip i := fun h' =>
      hi ((inv_leg_mem_oneWayTrip_iff hG).1 h').symm
    have := hw 0 h0
    simp only [Function.iterate_zero, id] at this ⊢
    rw [if_neg hs] at this
    exact ⟨fun _ => ⟨hR, by linarith⟩, fun h' => absurd h' hs⟩
  | succ t ih =>
    intro ht
    obtain ⟨ihs, ihn⟩ := ih (by omega)
    have hint := not_isBoundaryVertex_vertexOf_inv_iterate hG ht
    have hwt := hw t (by omega)
    have hwt1 := hw (t + 1) ht
    have hsucc : ∀ s, s = t + 1 →
        G.inv (G.tripMap (G.tripMap^[t] (G.leg i))) ∈ G.oneWayTrip i →
        G.inv (G.tripMap^[s] (G.leg i)) ∈ G.oneWayTrip i := by
      rintro s rfl hs
      rwa [Function.iterate_succ_apply']
    rw [Function.iterate_succ_apply'] at hwt1 ⊢
    -- The colour of `v(T^k(g_i)‾)` at the start of a run of darts traversed both ways is the
    -- colour of `v(T^t(g_i)‾)` when the run ends at `t`.
    have hcol : ∀ k < t, G.inv (G.tripMap^[k] (G.leg i)) ∉ G.oneWayTrip i →
        (∀ s, k < s → s ≤ t → G.inv (G.tripMap^[s] (G.leg i)) ∈ G.oneWayTrip i) →
        G.inv (G.tripMap (G.tripMap^[t] (G.leg i))) ∉ G.oneWayTrip i →
        G.colour (G.inv (G.tripMap^[k] (G.leg i))) =
          G.colour (G.inv (G.tripMap^[t] (G.leg i))) := by
      intro k hk hsk hrun hs1
      have hv := hG.vertexOf_inv_eq_of_pendant hP (k := k + 1) (n := t + 1) (by omega)
        (by omega) ht (by simpa using hsk) (by rwa [Function.iterate_succ_apply'])
        (fun s h1 h2 => hrun (s - 1) (by omega) (by omega))
      simp only [Nat.add_sub_cancel] at hv
      have hintk : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.tripMap^[k] (G.leg i)))) := by
        rwa [← hv]
      exact (hG.colour_eq_of_mem_vertexOf hintk (by rw [← hv]; exact G.self_mem_vertexOf _)).symm
    cases hc : G.colour (G.inv (G.tripMap^[t] (G.leg i))) with
    | white =>
      have hL := toFaceOrbit_inv_tripMap_of_white hG hint hc
      rw [hL] at hwt1 ⊢
      by_cases hs1 : G.inv (G.tripMap (G.tripMap^[t] (G.leg i))) ∈ G.oneWayTrip i
      · rw [if_pos hs1] at hwt1
        refine ⟨fun h' => absurd hs1 h', fun _ => ?_⟩
        by_cases hs : G.inv (G.tripMap^[t] (G.leg i)) ∈ G.oneWayTrip i
        · obtain ⟨k, hk, hsk, hrun, hRk, hLk⟩ := ihn hs
          refine ⟨k, by omega, hsk, fun s h1 h2 => ?_, by linarith, hLk⟩
          rcases (show s ≤ t ∨ s = t + 1 by omega) with h3 | h3
          · exact hrun s h1 h3
          · exact hsucc s h3 hs1
        · obtain ⟨-, hL0⟩ := ihs hs
          refine ⟨t, by omega, hs, fun s h1 h2 => hsucc s (by omega) hs1, ?_, ?_⟩ <;>
            simp only [hc, if_pos] <;> linarith
      · rw [if_neg hs1] at hwt1
        refine ⟨fun _ => ?_, fun h' => absurd h' hs1⟩
        by_cases hs : G.inv (G.tripMap^[t] (G.leg i)) ∈ G.oneWayTrip i
        · obtain ⟨k, hk, hsk, hrun, -, hLk⟩ := ihn hs
          rw [hcol k hk hsk hrun hs1, hc, if_pos rfl] at hLk
          constructor <;> linarith
        · obtain ⟨-, hL0⟩ := ihs hs
          constructor <;> linarith
    | black =>
      have hR := toFaceOrbit_tripMap_of_black hint hc
      rw [hR] at hwt1 ⊢
      by_cases hs1 : G.inv (G.tripMap (G.tripMap^[t] (G.leg i))) ∈ G.oneWayTrip i
      · rw [if_pos hs1] at hwt1
        refine ⟨fun h' => absurd hs1 h', fun _ => ?_⟩
        by_cases hs : G.inv (G.tripMap^[t] (G.leg i)) ∈ G.oneWayTrip i
        · obtain ⟨k, hk, hsk, hrun, hRk, -⟩ := ihn hs
          refine ⟨k, by omega, hsk, fun s h1 h2 => ?_, hRk, by linarith⟩
          rcases (show s ≤ t ∨ s = t + 1 by omega) with h3 | h3
          · exact hrun s h1 h3
          · exact hsucc s h3 hs1
        · obtain ⟨hR0, -⟩ := ihs hs
          refine ⟨t, by omega, hs, fun s h1 h2 => hsucc s (by omega) hs1, ?_, ?_⟩ <;>
            simp only [hc, reduceCtorEq, if_false] <;> linarith
      · rw [if_neg hs1] at hwt1
        refine ⟨fun _ => ?_, fun h' => absurd h' hs1⟩
        by_cases hs : G.inv (G.tripMap^[t] (G.leg i)) ∈ G.oneWayTrip i
        · obtain ⟨k, hk, hsk, hrun, hRk, -⟩ := ihn hs
          rw [hcol k hk hsk hrun hs1, hc] at hRk
          simp only [reduceCtorEq, if_false] at hRk
          constructor <;> linarith
        · obtain ⟨hR0, -⟩ := ihs hs
          constructor <;> linarith

/-- Let `π_G(i) ≠ i`, let the one-way trip `(d₁, …, d_m)` from `i`, with `d_n = T^{n-1}(g_i)`,
have pendant self-crossings and let `h` be a winding function of it. Then `h(f(d_n)) = 0` and
`h(f(d̄_n)) = 1` for every `n ∈ [1, m]` with `d̄_n ∉ darts(i)`. -/
@[cluster_algebras "lem_trip_winding_sides"]
theorem IsPlabicGraph.tripWinding_right_eq_zero_and_left_eq_one {i : Fin b}
    (hi : G.tripPerm i ≠ i) (hP : G.HasPendantSelfCrossings i) {h : G.faceOrbits → ℤ}
    (hW : G.IsTripWinding i h) {n : ℕ} (hn : 1 ≤ n) (hnm : n ≤ G.tripLength i)
    (hs : G.inv (G.tripMap^[n - 1] (G.leg i)) ∉ G.oneWayTrip i) :
    h (G.toFaceOrbit (G.tripMap^[n - 1] (G.leg i))) = 0 ∧
      h (G.toFaceOrbit (G.inv (G.tripMap^[n - 1] (G.leg i)))) = 1 :=
  (tripWinding_sides_aux hG hi hP hW (n - 1) (by omega)).1 hs

end IsPlabicGraph

/-! ### Trips through rooted trees -/

namespace RootedTree

variable (T : G.RootedTree)

/-- The last dart `a_k = σ^{k-1}(a₁)` of the interval `(a₁, …, a_k)` of a rooted tree. -/
noncomputable def intervalEnd : H := (G.rot ^ (T.intervalLength - 1)) T.intervalStart

/-- The dart `s` at which a trip enters the rooted tree `T` with interval `(a₁, …, a_k)`: `a₁` if
the root is a boundary vertex or an internal black vertex, and `a_k` if it is an internal white
vertex. -/
noncomputable def tripEntry : H :=
  if G.IsBoundaryVertex T.root ∨ G.colour T.intervalStart = .black then T.intervalStart
  else T.intervalEnd

/-- The dart `z` at which a trip leaves the rooted tree `T` with interval `(a₁, …, a_k)`: `ā_k`
if the root is an internal black vertex, and `ā₁` if it is an internal white vertex or a
boundary vertex. -/
noncomputable def tripExit : H :=
  if ¬G.IsBoundaryVertex T.root ∧ G.colour T.intervalStart = .black then G.inv T.intervalEnd
  else G.inv T.intervalStart

/-- If the root of `T` is a boundary vertex, the entry dart of `T` is `a₁`. -/
theorem tripEntry_of_isBoundaryVertex (h : G.IsBoundaryVertex T.root) :
    T.tripEntry = T.intervalStart :=
  if_pos (Or.inl h)

/-- If the root of `T` is a boundary vertex, the exit dart of `T` is `ā₁`. -/
theorem tripExit_of_isBoundaryVertex (h : G.IsBoundaryVertex T.root) :
    T.tripExit = G.inv T.intervalStart :=
  if_neg fun h' => h'.1 h

/-- If `a₁` is black, the entry dart of `T` is `a₁`. -/
theorem tripEntry_of_black (hc : G.colour T.intervalStart = .black) :
    T.tripEntry = T.intervalStart :=
  if_pos (Or.inr hc)

/-- If the root of `T` is an internal vertex and `a₁` is black, the exit dart of `T` is `ā_k`. -/
theorem tripExit_of_black (h : ¬G.IsBoundaryVertex T.root)
    (hc : G.colour T.intervalStart = .black) : T.tripExit = G.inv T.intervalEnd :=
  if_pos ⟨h, hc⟩

/-- If the root of `T` is an internal vertex and `a₁` is white, the entry dart of `T` is `a_k`. -/
theorem tripEntry_of_white (h : ¬G.IsBoundaryVertex T.root)
    (hc : G.colour T.intervalStart = .white) : T.tripEntry = T.intervalEnd :=
  if_neg fun h' => h'.elim h (by simp [hc])

/-- If `a₁` is white, the exit dart of `T` is `ā₁`. -/
theorem tripExit_of_white (hc : G.colour T.intervalStart = .white) :
    T.tripExit = G.inv T.intervalStart :=
  if_neg fun h' => by simp [hc] at h'

/-- Every dart `σⁿ(a₁)` lies at the root of `T`. -/
theorem pow_intervalStart_mem_root (n : ℕ) : (G.rot ^ n) T.intervalStart ∈ T.root :=
  T.mem_root_iff.2 (by rw [G.vertexOf_pow_apply, ← T.root_eq_vertexOf_intervalStart])

/-- For `j < k`, the dart `σʲ(a₁)` is a dart of `T`. -/
theorem pow_intervalStart_mem_darts {j : ℕ} (hj : j < T.intervalLength) :
    (G.rot ^ j) T.intervalStart ∈ T.darts :=
  (T.mem_darts_iff_of_mem_root (T.pow_intervalStart_mem_root j)).2 ⟨j, hj, rfl⟩

/-- The last dart `a_k` of the interval lies at the root of `T`. -/
theorem intervalEnd_mem_root : T.intervalEnd ∈ T.root :=
  T.pow_intervalStart_mem_root _

/-- The last dart `a_k` of the interval is a dart of `T`. -/
theorem intervalEnd_mem_darts : T.intervalEnd ∈ T.darts :=
  T.pow_intervalStart_mem_darts (by have := T.one_le_intervalLength; omega)

/-- The entry dart of `T` lies at the root of `T`. -/
theorem tripEntry_mem_root : T.tripEntry ∈ T.root := by
  unfold tripEntry
  split_ifs
  exacts [T.intervalStart_mem_root, T.intervalEnd_mem_root]

/-- The entry dart of `T` is a dart of `T`. -/
theorem tripEntry_mem_darts : T.tripEntry ∈ T.darts := by
  unfold tripEntry
  split_ifs
  exacts [T.intervalStart_mem_darts, T.intervalEnd_mem_darts]

section IsPlabicGraph

variable (hG : G.IsPlabicGraph)

include hG

/-- The dart `σ(a_k)` following the interval of `T` is not a dart of `T`. -/
theorem rot_intervalEnd_notMem : G.rot T.intervalEnd ∉ T.darts := by
  have hex : ∃ d ∈ T.darts, G.rot d ∉ T.darts := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ n, (G.rot ^ n) T.intervalStart ∈ T.darts := by
      intro n
      induction n with
      | zero => exact T.intervalStart_mem_darts
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hcon _ ih
    obtain ⟨n, hn⟩ :=
      (G.mem_vertexOf.1 (G.rot_symm_mem_vertexOf T.intervalStart)).exists_nat_pow_eq
    exact T.rot_symm_intervalStart_notMem (hn ▸ hall n)
  obtain ⟨d, hd, hrd⟩ := hex
  have hdr : d ∈ T.root := by
    rcases T.vertexOf_mem_or_eq_root hG hd with hW | hR
    · exact absurd (T.rot_mem_darts_of_vertexOf_mem hW) hrd
    · exact T.mem_root_iff.2 hR
  obtain ⟨j, hj, rfl⟩ := (T.mem_darts_iff_of_mem_root hdr).1 hd
  by_cases hj1 : j + 1 < T.intervalLength
  · refine absurd ?_ hrd
    rw [← Equiv.Perm.mul_apply, ← pow_succ']
    exact T.pow_intervalStart_mem_darts hj1
  · rwa [intervalEnd, show T.intervalLength - 1 = j by omega]

/-- The reverse of the exit dart of `T` lies at the root of `T`. -/
theorem inv_tripExit_mem_root : G.inv T.tripExit ∈ T.root := by
  unfold tripExit
  split_ifs <;> rw [hG.inv_involutive]
  exacts [T.intervalEnd_mem_root, T.intervalStart_mem_root]

/-- At an internal root, every dart of the root has the colour of `a₁`. -/
private theorem colour_eq_of_mem_root (hb : ¬G.IsBoundaryVertex T.root) {d : H}
    (hd : d ∈ T.root) : G.colour d = G.colour T.intervalStart :=
  hG.colour_eq_of_mem_vertexOf (by rwa [← T.root_eq_vertexOf_intervalStart])
    (by rwa [← T.root_eq_vertexOf_intervalStart])

/-- The trip map sends a dart of `T` other than the exit `z` to a dart of `T`. -/
theorem tripMap_mem_darts {y : H} (hy : y ∈ T.darts) (hz : y ≠ T.tripExit) :
    G.tripMap y ∈ T.darts := by
  have hyi := T.inv_mem_darts hG hy
  have hv : G.vertexOf (G.tripMap y) = G.vertexOf (G.inv y) := vertexOf_turn _
  rcases T.vertexOf_mem_or_eq_root hG hyi with hW | hR
  · exact T.mem_darts_of_vertexOf_mem (hv ▸ hW)
  have hyr : G.inv y ∈ T.root := T.mem_root_iff.2 hR
  obtain ⟨j, hj, hjy⟩ := (T.mem_darts_iff_of_mem_root hyr).1 hyi
  have hyinv : y = G.inv ((G.rot ^ j) T.intervalStart) := by rw [hjy, hG.inv_involutive]
  by_cases hb : G.IsBoundaryVertex T.root
  · exfalso
    apply hz
    rw [T.tripExit_of_isBoundaryVertex hb, ← T.eq_intervalStart_of_isBoundaryVertex hG hb hyi hR,
      hG.inv_involutive]
  have hbv : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y)) := by rwa [hR]
  have hcol : G.colour (G.inv y) = G.colour T.intervalStart :=
    T.colour_eq_of_mem_root hG hb hyr
  rw [tripMap_apply]
  cases hc : G.colour T.intervalStart with
  | black =>
    rw [turn_of_black hbv (hcol.trans hc), ← hjy, ← Equiv.Perm.mul_apply, ← pow_succ']
    by_cases hj1 : j + 1 < T.intervalLength
    · exact T.pow_intervalStart_mem_darts hj1
    · exfalso
      apply hz
      rw [T.tripExit_of_black hb hc, hyinv, intervalEnd, show T.intervalLength - 1 = j by omega]
  | white =>
    rw [turn_of_white hbv (hcol.trans hc), ← hjy]
    rcases j with _ | j
    · exfalso
      apply hz
      rw [T.tripExit_of_white hc, hyinv, pow_zero, Equiv.Perm.one_apply]
    · rw [pow_succ', Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
      exact T.pow_intervalStart_mem_darts (by omega)

/-- The trip map does not send a dart of `T` other than the exit `z` to the entry `s`. -/
theorem tripMap_ne_tripEntry {y : H} (hy : y ∈ T.darts) (hz : y ≠ T.tripExit) :
    G.tripMap y ≠ T.tripEntry := by
  intro hT
  have hyi := T.inv_mem_darts hG hy
  have hR : G.vertexOf (G.inv y) = T.root := by
    have h1 : G.vertexOf (G.tripMap y) = G.vertexOf (G.inv y) := vertexOf_turn _
    rw [← h1, hT]
    exact T.mem_root_iff.1 T.tripEntry_mem_root
  by_cases hb : G.IsBoundaryVertex T.root
  · apply hz
    rw [tripMap_apply, turn_of_isBoundaryVertex (by rwa [hR]),
      T.tripEntry_of_isBoundaryVertex hb] at hT
    rw [T.tripExit_of_isBoundaryVertex hb, ← hT, hG.inv_involutive]
  have hbv : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y)) := by rwa [hR]
  have hcol : G.colour (G.inv y) = G.colour T.intervalStart :=
    T.colour_eq_of_mem_root hG hb (T.mem_root_iff.2 hR)
  rw [tripMap_apply] at hT
  cases hc : G.colour T.intervalStart with
  | black =>
    rw [turn_of_black hbv (hcol.trans hc), T.tripEntry_of_black hc] at hT
    apply T.rot_symm_intervalStart_notMem
    rw [← hT, Equiv.symm_apply_apply]
    exact hyi
  | white =>
    rw [turn_of_white hbv (hcol.trans hc), T.tripEntry_of_white hb hc] at hT
    apply T.rot_intervalEnd_notMem hG
    rw [← hT, Equiv.apply_symm_apply]
    exact hyi

/-- The only leg among the darts of `T` can be the entry `s`, when the root is a boundary
vertex. -/
theorem eq_tripEntry_of_isLeg {y : H} (hy : y ∈ T.darts) (hl : G.IsLeg y) : y = T.tripEntry := by
  obtain ⟨j, rfl⟩ := hl
  have hb : G.IsBoundaryVertex (G.vertexOf (G.leg j)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
  rcases T.vertexOf_mem_or_eq_root hG hy with hW | hR
  · exact absurd hb (G.mem_internalVertices.1 (T.nonRoot_subset hW)).2
  · rw [T.tripEntry_of_isBoundaryVertex (hR ▸ hb)]
    exact T.eq_intervalStart_of_isBoundaryVertex hG (hR ▸ hb) hy hR

/-- No dart of a rooted tree with internal root is a leg. -/
theorem not_isLeg_of_mem_darts (hroot : ¬G.IsBoundaryVertex T.root) {y : H}
    (hy : y ∈ T.darts) : ¬G.IsLeg y := by
  rintro ⟨j, rfl⟩
  have hb : G.IsBoundaryVertex (G.vertexOf (G.leg j)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
  rcases T.vertexOf_mem_or_eq_root hG hy with hW | hR
  · exact (G.mem_internalVertices.1 (T.nonRoot_subset hW)).2 hb
  · exact hroot (hR ▸ hb)

/-- As long as the exit has not been reached, the darts `Tⁿ(s)` are darts of `T`. -/
theorem iterate_tripMap_tripEntry_mem_darts {n : ℕ}
    (h : ∀ m < n, G.tripMap^[m] T.tripEntry ≠ T.tripExit) :
    G.tripMap^[n] T.tripEntry ∈ T.darts := by
  induction n with
  | zero => exact T.tripEntry_mem_darts
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact T.tripMap_mem_darts hG (ih fun m hm => h m (by omega)) (h n (by omega))

/-- As long as the exit has not been reached, the darts `Tⁿ(s)` are pairwise distinct. -/
theorem iterate_tripMap_tripEntry_ne_of_lt {p q : ℕ} (hpq : p < q)
    (h : ∀ m < q, G.tripMap^[m] T.tripEntry ≠ T.tripExit) :
    G.tripMap^[p] T.tripEntry ≠ G.tripMap^[q] T.tripEntry := by
  induction p generalizing q with
  | zero =>
    intro heq
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_zero, id] at heq
    exact T.tripMap_ne_tripEntry hG
      (T.iterate_tripMap_tripEntry_mem_darts hG fun m hm => h m (by omega)) (h q (by omega))
      heq.symm
  | succ p ih =>
    intro heq
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at heq
    exact ih (by omega) (fun m hm => h m (by omega)) ((tripMap_bijective hG).injective heq)

/-- Without roundtrip, every dart of `T` is one of the darts `Tⁿ(s)`, `n ≤ N`, where
`T^N(s) = z`. -/
theorem exists_iterate_tripMap_tripEntry_eq (hR : ¬G.HasRoundtrip) {N : ℕ}
    (hN : G.tripMap^[N] T.tripEntry = T.tripExit) {y : H} (hy : y ∈ T.darts) :
    ∃ n < N + 1, G.tripMap^[n] T.tripEntry = y := by
  by_contra hyP
  push Not at hyP
  let Y : Set H := {x | x ∈ T.darts ∧ ∀ n < N + 1, G.tripMap^[n] T.tripEntry ≠ x}
  have hY : Set.MapsTo G.tripMap Y Y := by
    rintro x ⟨hx, hxP⟩
    have hxz : x ≠ T.tripExit := fun h => hxP N (by omega) (hN.trans h.symm)
    refine ⟨T.tripMap_mem_darts hG hx hxz, fun n hn heq => ?_⟩
    rcases n with _ | n
    · exact T.tripMap_ne_tripEntry hG hx hxz heq.symm
    · rw [Function.iterate_succ_apply'] at heq
      exact hxP n (by omega) ((tripMap_bijective hG).injective heq)
  obtain ⟨n, hn⟩ : ∃ n, G.IsLeg (G.tripMap^[n] y) := by
    by_contra hcon
    push Not at hcon
    exact hR (hasRoundtrip_iff.2 ⟨y, (G.mem_treeDarts.1 hy).1, hcon⟩)
  obtain ⟨hn1, hn2⟩ := hY.iterate n ⟨hy, hyP⟩
  exact hn2 0 (by omega) (T.eq_tripEntry_of_isLeg hG hn1 hn).symm

/-- Let `G` be a plabic graph without roundtrip and `T = (v, W)` a rooted tree of `G` with
interval `(a₁, …, a_k)`, and put `(s, z) = (a₁, ā_k)` if `v` is an internal black vertex,
`(s, z) = (a_k, ā₁)` if `v` is an internal white vertex and `(s, z) = (a₁, ā₁)` if `v` is a
boundary vertex (`s = T.tripEntry`, `z = T.tripExit`). Then for some `N ≥ 0` the darts `Tⁿ(s)`,
`0 ≤ n ≤ N`, are pairwise distinct, they are the darts `D_T` of `T`, and `T^N(s) = z`. -/
@[cluster_algebras "lem_rooted_tree_trip_chain"]
theorem exists_tripChain (hR : ¬G.HasRoundtrip) :
    ∃ N, Set.InjOn (fun n => G.tripMap^[n] T.tripEntry) (Set.Iic N) ∧
      T.darts = (range (N + 1)).image (fun n => G.tripMap^[n] T.tripEntry) ∧
      G.tripMap^[N] T.tripEntry = T.tripExit := by
  have hex : ∃ n, G.tripMap^[n] T.tripEntry = T.tripExit := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, q, hpq, heq⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => G.tripMap^[n] T.tripEntry)
    rcases lt_or_gt_of_ne hpq with h | h
    · exact T.iterate_tripMap_tripEntry_ne_of_lt hG h (fun m _ => hcon m) heq
    · exact T.iterate_tripMap_tripEntry_ne_of_lt hG h (fun m _ => hcon m) heq.symm
  classical
  obtain ⟨N, hN, hmin⟩ : ∃ N, G.tripMap^[N] T.tripEntry = T.tripExit ∧
      ∀ m < N, G.tripMap^[m] T.tripEntry ≠ T.tripExit :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨N, ?_, ?_, hN⟩
  · intro p hp q hq heq
    simp only [Set.mem_Iic] at hp hq
    by_contra hpq
    rcases lt_or_gt_of_ne hpq with h | h
    · exact T.iterate_tripMap_tripEntry_ne_of_lt hG h (fun m hm => hmin m (by omega)) heq
    · exact T.iterate_tripMap_tripEntry_ne_of_lt hG h (fun m hm => hmin m (by omega)) heq.symm
  · ext y
    simp only [mem_image, mem_range]
    refine ⟨T.exists_iterate_tripMap_tripEntry_eq hG hR hN, fun ⟨n, hn, hny⟩ => hny ▸
      T.iterate_tripMap_tripEntry_mem_darts hG fun m hm => hmin m (by omega)⟩

/-- Let `G` be a plabic graph without roundtrip and `T` a rooted tree of `G` whose root is
internal. Then for every label `i` and every dart `y` of `T`, `y ∈ darts(i)` if and only if
`ȳ ∈ darts(i)`. -/
@[cluster_algebras "lem_internal_tree_trip_closed"]
theorem mem_oneWayTrip_iff_inv_mem (hR : ¬G.HasRoundtrip) (hroot : ¬G.IsBoundaryVertex T.root)
    (i : Fin b) {y : H} (hy : y ∈ T.darts) :
    y ∈ G.oneWayTrip i ↔ G.inv y ∈ G.oneWayTrip i := by
  obtain ⟨N, -, hX, hN⟩ := T.exists_tripChain hG hR
  -- If the trip from `i` meets `D_T`, it contains all of `D_T`.
  have key : ∀ d ∈ T.darts, d ∈ G.oneWayTrip i → ∀ d' ∈ T.darts, d' ∈ G.oneWayTrip i := by
    intro d hd hdi d' hd'
    rw [hX, mem_image] at hd hd'
    obtain ⟨n, hn, rfl⟩ := hd
    obtain ⟨n', hn', rfl⟩ := hd'
    rw [mem_range] at hn hn'
    have hleg : ∀ l, 0 < l → l ≤ N + 1 → ¬G.IsLeg (G.tripMap^[l] T.tripEntry) := by
      intro l _ hl
      rcases (show l ≤ N ∨ l = N + 1 by omega) with hl' | rfl
      · refine T.not_isLeg_of_mem_darts hG hroot ?_
        rw [hX]
        exact mem_image.2 ⟨l, mem_range.2 (by omega), rfl⟩
      · rw [Function.iterate_succ_apply', hN]
        apply hG.not_isLeg_of_not_isBoundaryVertex
        rwa [tripMap_apply, vertexOf_turn, T.mem_root_iff.1 (T.inv_tripExit_mem_root hG)]
    obtain ⟨p, hp, hpm⟩ :=
      hG.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip hleg (by omega : n ≤ N + 1) hdi
    exact mem_oneWayTrip.2 ⟨n' + p, by omega, by rw [Function.iterate_add_apply, hp]⟩
  exact ⟨fun h => key y hy h _ (T.inv_mem_darts hG hy),
    fun h => key _ (T.inv_mem_darts hG hy) h y hy⟩

end IsPlabicGraph

end RootedTree

end PlabicData

end ClusterAlgebras
