/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap

/-!
# Trips and the trip permutation

A trip in a plabic graph is a walk along the edges obeying the *rules of the road*: at a black
vertex it makes the sharpest right turn, at a white vertex the sharpest left turn. In the encoding
of a plabic graph by darts `(H, d ↦ d̄, σ, B, κ, β)`, a trip is an orbit of the *trip map*
`T : H \ B → H \ B`, `T(d) = σ(d̄)` if `v(d̄)` is an internal black vertex, `T(d) = σ⁻¹(d̄)` if it
is an internal white vertex, and `T(d) = d̄` if it is a boundary vertex. The trip map is a
permutation of `H \ B`, so every leg `g_i` lies on a cycle of `T`, and the *one-way trip* from `i`
runs from `g_i` until it first meets a leg `g_j`; the *trip permutation* sends `i` to `j`.

## Main definitions

* `ClusterAlgebras.PlabicData.tripMap`: the trip map `T`.
* `ClusterAlgebras.PlabicData.trip`, `ClusterAlgebras.PlabicData.IsRoundtrip`: the trips (orbits
  of `T`) and the roundtrips, the trips containing no leg.
* `ClusterAlgebras.PlabicData.tripLength`, `ClusterAlgebras.PlabicData.oneWayTrip`,
  `ClusterAlgebras.PlabicData.tripPerm`: the length `m_i` of the one-way trip from `i`, the
  one-way trip itself, and the trip permutation `π_G`.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripEquiv`: for a plabic graph, the trip map as a
  permutation of all darts.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripMap_bijOn`: the trip map is a bijection of `H \ B`.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.exists_isLeg_iterate_tripMap`: one-way trips end.
* `ClusterAlgebras.PlabicData.Iso.bijOn_compl_bdry`, `ClusterAlgebras.PlabicData.Iso.map_tripMap`:
  isomorphisms map `H \ B` onto `H' \ B'` and commute with the trip maps.

## Implementation notes

* **The trip map on all darts.** `tripMap` is the function `d ↦ R(d̄)` on all of `H`, where
  `R(z) = σ(z)`, `σ⁻¹(z)` or `z` according as `v(z)` is internal black, internal white or a
  boundary vertex (`PlabicData.turn`). On `H \ B` it is the trip map of [FWZ]. On `B` it is
  `d ↦ d̄`, since the reverse of a dart of `B` lies in `B`, at a boundary vertex; so for a plabic
  graph `tripMap` is a permutation of all of `H` preserving `H \ B` (`IsPlabicGraph.tripEquiv`),
  and the trip map of [FWZ] is its restriction `IsPlabicGraph.tripEquivCompl`. This lets the
  definition be stated without hypotheses, and lets orbit arguments use `Equiv.Perm`.
* **Trips.** The trip through `d` is the forward orbit `{Tⁿ(d) : n ≥ 0}` (`trip`); for a plabic
  graph it is the orbit of `d` under the permutation `tripEquiv`
  (`IsPlabicGraph.trip_eq_setOf_sameCycle`). A trip traverses the edge `{d, d̄}` along `d` when `d`
  is one of its darts, that is, `d ∈ G.trip e` or `d ∈ G.oneWayTrip i`; this is not a separate
  definition.
* **Labels.** The label set `[1, b]` of [FWZ] is `Fin b`, `0`-indexed: the element `i : Fin b`
  is the label `i + 1` of [FWZ].
* **Lengths.** `m_i` is `sInf {m | 0 < m ∧ Tᵐ(g_i) is a leg}`, which is `0` when the set is empty,
  as in [FWZ]. For a plabic graph the set is never empty
  (`IsPlabicGraph.exists_isLeg_iterate_tripMap`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### The trip map -/

/-- The **turn** `R(z)` of a trip arriving at the vertex `v(z)` along `z̄`: the next dart `σ(z)`
counterclockwise if `v(z)` is an internal black vertex, the previous dart `σ⁻¹(z)` if it is an
internal white vertex, and `z` itself if `v(z)` is a boundary vertex. -/
def turn (z : H) : H :=
  if G.IsBoundaryVertex (G.vertexOf z) then z
  else
    match G.colour z with
    | .black => G.rot z
    | .white => G.rot.symm z

/-- The **trip map** `T(d) = R(d̄)`: `T(d) = σ(d̄)` if `v(d̄)` is an internal black vertex,
`T(d) = σ⁻¹(d̄)` if it is an internal white vertex, and `T(d) = d̄` if it is a boundary vertex. It
is defined on all darts; for a plabic graph its restriction to `H \ B` is
`IsPlabicGraph.tripEquivCompl`. -/
@[cluster_algebras "def_trip_map"]
def tripMap (d : H) : H := G.turn (G.inv d)

variable {G}

/-- At a boundary vertex the turn is the identity. -/
theorem turn_of_isBoundaryVertex {z : H} (hz : G.IsBoundaryVertex (G.vertexOf z)) :
    G.turn z = z := by
  simp [turn, hz]

/-- At an internal black vertex the turn is `σ(z)`. -/
theorem turn_of_black {z : H} (hz : ¬G.IsBoundaryVertex (G.vertexOf z))
    (hc : G.colour z = .black) : G.turn z = G.rot z := by
  simp [turn, hz, hc]

/-- At an internal white vertex the turn is `σ⁻¹(z)`. -/
theorem turn_of_white {z : H} (hz : ¬G.IsBoundaryVertex (G.vertexOf z))
    (hc : G.colour z = .white) : G.turn z = G.rot.symm z := by
  simp [turn, hz, hc]

/-- The trip map is `d ↦ R(d̄)`. -/
theorem tripMap_apply (d : H) : G.tripMap d = G.turn (G.inv d) := rfl

/-- The turn `R(z)` lies at the vertex `v(z)`. -/
theorem turn_mem_vertexOf (z : H) : G.turn z ∈ G.vertexOf z := by
  unfold turn
  split_ifs
  · exact G.self_mem_vertexOf z
  · split
    · exact G.rot_mem_vertexOf z
    · exact G.rot_symm_mem_vertexOf z

/-- The turn `R(z)` and `z` lie at the same vertex. -/
theorem vertexOf_turn (z : H) : G.vertexOf (G.turn z) = G.vertexOf z :=
  G.vertexOf_eq_of_mem (turn_mem_vertexOf z)

/-- A dart at an internal vertex is not in `B`. -/
theorem notMem_bdry_of_mem_vertexOf {z e : H} (hz : ¬G.IsBoundaryVertex (G.vertexOf z))
    (he : e ∈ G.vertexOf z) : e ∉ G.bdry :=
  fun heB => hz ⟨e, he, heB⟩

/-- The inverse of the turn: `σ⁻¹(x)`, `σ(x)` or `x` according as `v(x)` is internal black,
internal white or a boundary vertex. -/
def turnInv (G : PlabicData H b) (x : H) : H :=
  if G.IsBoundaryVertex (G.vertexOf x) then x
  else
    match G.colour x with
    | .black => G.rot.symm x
    | .white => G.rot x

/-- The inverse turn of `x` lies at the vertex `v(x)`. -/
theorem turnInv_mem_vertexOf (x : H) : G.turnInv x ∈ G.vertexOf x := by
  unfold turnInv
  split_ifs
  · exact G.self_mem_vertexOf x
  · split
    · exact G.rot_symm_mem_vertexOf x
    · exact G.rot_mem_vertexOf x

section IsPlabicGraph

variable (hG : G.IsPlabicGraph)

include hG

/-- At an internal vertex the colour is constant along the rotation backwards. -/
private theorem colour_rot_symm {z : H} (hz : ¬G.IsBoundaryVertex (G.vertexOf z)) :
    G.colour (G.rot.symm z) = G.colour z := by
  have hz' : ¬G.IsBoundaryVertex (G.vertexOf (G.rot.symm z)) := by
    rwa [G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf z)]
  have := hG.colour_rot _ hz'
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

/-- In a plabic graph `turnInv` is a left inverse of the turn. -/
theorem turnInv_turn (z : H) : G.turnInv (G.turn z) = z := by
  by_cases hz : G.IsBoundaryVertex (G.vertexOf z)
  · rw [turn_of_isBoundaryVertex hz, turnInv, if_pos hz]
  · have hz' : ¬G.IsBoundaryVertex (G.vertexOf (G.turn z)) := by rwa [vertexOf_turn]
    cases hc : G.colour z
    · rw [turn_of_white hz hc, turnInv, if_neg (by rwa [turn_of_white hz hc] at hz'),
        colour_rot_symm hG hz, hc]
      simp
    · rw [turn_of_black hz hc, turnInv, if_neg (by rwa [turn_of_black hz hc] at hz'),
        hG.colour_rot _ hz, hc]
      simp

/-- In a plabic graph `turnInv` is a right inverse of the turn. -/
theorem turn_turnInv (x : H) : G.turn (G.turnInv x) = x := by
  by_cases hx : G.IsBoundaryVertex (G.vertexOf x)
  · rw [turnInv, if_pos hx, turn_of_isBoundaryVertex hx]
  · have hv : G.vertexOf (G.turnInv x) = G.vertexOf x :=
      G.vertexOf_eq_of_mem (turnInv_mem_vertexOf x)
    cases hc : G.colour x
    · have e : G.turnInv x = G.rot x := by simp [turnInv, hx, hc]
      have hx' : ¬G.IsBoundaryVertex (G.vertexOf (G.rot x)) := by rwa [← e, hv]
      rw [e, turn_of_white hx' (by rw [hG.colour_rot _ hx, hc])]
      simp
    · have e : G.turnInv x = G.rot.symm x := by simp [turnInv, hx, hc]
      have hx' : ¬G.IsBoundaryVertex (G.vertexOf (G.rot.symm x)) := by rwa [← e, hv]
      rw [e, turn_of_black hx' (by rw [colour_rot_symm hG hx, hc])]
      simp

/-- For a plabic graph the turn is a bijection of the darts. -/
theorem turn_bijective : Function.Bijective G.turn :=
  Function.bijective_iff_has_inverse.2 ⟨G.turnInv, turnInv_turn hG, turn_turnInv hG⟩

/-- On `B` the trip map is `d ↦ d̄`. -/
theorem tripMap_of_mem_bdry {d : H} (hd : d ∈ G.bdry) : G.tripMap d = G.inv d :=
  turn_of_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem (hG.inv_mem_bdry d hd))

/-- In a plabic graph `T(d) ∈ B` if and only if `d ∈ B`. -/
theorem tripMap_mem_bdry_iff (d : H) : G.tripMap d ∈ G.bdry ↔ d ∈ G.bdry := by
  by_cases hz : G.IsBoundaryVertex (G.vertexOf (G.inv d))
  · rw [tripMap_apply, turn_of_isBoundaryVertex hz, hG.inv_mem_bdry_iff]
  · refine iff_of_false (notMem_bdry_of_mem_vertexOf hz (turn_mem_vertexOf _)) fun hd => ?_
    exact notMem_bdry_of_mem_vertexOf hz (G.self_mem_vertexOf _) (hG.inv_mem_bdry d hd)

/-- For a plabic graph the trip map is a bijection of all darts. -/
theorem tripMap_bijective : Function.Bijective G.tripMap :=
  (turn_bijective hG).comp G.inv.bijective

/-- For a plabic graph, the trip map as a permutation of all darts. -/
noncomputable def IsPlabicGraph.tripEquiv : Equiv.Perm H :=
  Equiv.ofBijective G.tripMap (tripMap_bijective hG)

/-- The permutation `tripEquiv` acts as the trip map. -/
@[simp]
theorem IsPlabicGraph.tripEquiv_apply (d : H) : hG.tripEquiv d = G.tripMap d := rfl

/-- **The trip map is a permutation**: for a plabic graph, the trip map is a bijection of
`H \ B`. -/
@[cluster_algebras "lem_trip_map_bijective"]
theorem IsPlabicGraph.tripMap_bijOn :
    Set.BijOn G.tripMap {d | d ∉ G.bdry} {d | d ∉ G.bdry} :=
  hG.tripEquiv.bijOn fun d => not_congr (tripMap_mem_bdry_iff hG d)

/-- The `n`-th power of `tripEquiv` acts as the `n`-th iterate of the trip map. -/
theorem IsPlabicGraph.tripEquiv_pow_apply (n : ℕ) (d : H) :
    (hG.tripEquiv ^ n) d = G.tripMap^[n] d := by
  rw [Equiv.Perm.coe_pow]
  rfl

/-- For a plabic graph, the restriction of the trip map to a permutation of `H \ B`. -/
noncomputable def IsPlabicGraph.tripEquivCompl : Equiv.Perm {d // d ∉ G.bdry} :=
  hG.tripEquiv.subtypePerm fun d => not_congr (tripMap_mem_bdry_iff hG d)

/-- The permutation `tripEquivCompl` of `H \ B` acts as the trip map. -/
@[simp]
theorem IsPlabicGraph.coe_tripEquivCompl_apply (d : {d // d ∉ G.bdry}) :
    (hG.tripEquivCompl d : H) = G.tripMap d := rfl

end IsPlabicGraph

/-! ### Trips and the trip permutation -/

variable (G)

/-- A dart is a **leg** if it is `g_j` for some label `j`. -/
def IsLeg (d : H) : Prop := ∃ j, G.leg j = d

/-- Being a leg is decidable. -/
instance : DecidablePred G.IsLeg := fun _ => by unfold IsLeg; infer_instance

/-- The **trip** through `d`: the darts `Tⁿ(d)`, `n ≥ 0`. For a plabic graph and `d ∉ B` this is
the orbit of `d` under the trip map. -/
@[cluster_algebras "def_trip_permutation"]
def trip (d : H) : Set H := Set.range fun n : ℕ => G.tripMap^[n] d

/-- A **roundtrip**: an orbit of the trip map on `H \ B` containing no leg. -/
@[cluster_algebras "def_trip_permutation"]
def IsRoundtrip (O : Set H) : Prop := ∃ d ∉ G.bdry, G.trip d = O ∧ ∀ j, G.leg j ∉ O

/-- The length `m_i` of the one-way trip from `i`: the least `m ≥ 1` such that `Tᵐ(g_i)` is a
leg, and `0` if there is none. -/
@[cluster_algebras "def_trip_permutation"]
noncomputable def tripLength (i : Fin b) : ℕ :=
  sInf {m | 0 < m ∧ G.IsLeg (G.tripMap^[m] (G.leg i))}

/-- The **one-way trip** from `i`: the sequence of darts
`(g_i, T(g_i), …, T^{m_i - 1}(g_i))`. -/
@[cluster_algebras "def_trip_permutation"]
noncomputable def oneWayTrip (i : Fin b) : List H :=
  (List.range (G.tripLength i)).map fun k => G.tripMap^[k] (G.leg i)

/-- The **trip permutation** `π_G` of the labels `Fin b`: `i` is sent to the label `j` at which
the one-way trip from `i` ends, `T^{m_i}(g_i) = g_j`, and to `i` if `m_i = 0`. -/
@[cluster_algebras "def_trip_permutation"]
noncomputable def tripPerm (i : Fin b) : Fin b :=
  if h : 0 < G.tripLength i ∧ ∃ j, G.leg j = G.tripMap^[G.tripLength i] (G.leg i) then
    h.2.choose
  else i

/-- A plabic graph **has a roundtrip** if some orbit of its trip map on `H \ B` contains no
leg. -/
def HasRoundtrip : Prop := ∃ O, G.IsRoundtrip O

variable {G}

/-- Membership in a trip: `e` lies on the trip through `d` iff `e = Tⁿ(d)` for some `n`. -/
theorem mem_trip {d e : H} : e ∈ G.trip d ↔ ∃ n, G.tripMap^[n] d = e := Iff.rfl

omit [Fintype H] [DecidableEq H] in
/-- Every leg `g_j` is a leg. -/
@[simp]
theorem isLeg_leg (j : Fin b) : G.IsLeg (G.leg j) := ⟨j, rfl⟩

/-- Every dart lies on its own trip. -/
@[simp]
theorem mem_trip_self (d : H) : d ∈ G.trip d := ⟨0, rfl⟩

/-- Every iterate `Tⁿ(d)` lies on the trip through `d`. -/
@[simp]
theorem iterate_mem_trip (d : H) (n : ℕ) : G.tripMap^[n] d ∈ G.trip d := ⟨n, rfl⟩

/-- The darts of the one-way trip from `i` are the `Tᵏ(g_i)` with `k < m_i`. -/
theorem mem_oneWayTrip {i : Fin b} {d : H} :
    d ∈ G.oneWayTrip i ↔ ∃ k < G.tripLength i, G.tripMap^[k] (G.leg i) = d := by
  simp [oneWayTrip, eq_comm]

/-- The one-way trip from `i` has length `m_i`. -/
@[simp]
theorem length_oneWayTrip (i : Fin b) : (G.oneWayTrip i).length = G.tripLength i := by
  simp [oneWayTrip]

/-- There is a roundtrip if and only if some dart `d ∉ B` has no leg among its iterates `Tⁿ(d)`.
-/
theorem hasRoundtrip_iff :
    G.HasRoundtrip ↔ ∃ d ∉ G.bdry, ∀ n, ¬G.IsLeg (G.tripMap^[n] d) := by
  constructor
  · rintro ⟨O, d, hd, rfl, hO⟩
    exact ⟨d, hd, fun n ⟨j, hj⟩ => hO j (hj ▸ iterate_mem_trip d n)⟩
  · rintro ⟨d, hd, h⟩
    exact ⟨_, d, hd, rfl, fun j ⟨n, hn⟩ => h n ⟨j, hn.symm⟩⟩

/-- If some `Tᵐ(g_i)` with `m ≥ 1` is a leg, then `m_i ≥ 1` and `T^{m_i}(g_i)` is a leg. -/
theorem tripLength_spec {i : Fin b} (h : ∃ m, 0 < m ∧ G.IsLeg (G.tripMap^[m] (G.leg i))) :
    0 < G.tripLength i ∧ G.IsLeg (G.tripMap^[G.tripLength i] (G.leg i)) :=
  Nat.sInf_mem (s := {m | 0 < m ∧ G.IsLeg (G.tripMap^[m] (G.leg i))}) h

/-- No `Tᵏ(g_i)` with `1 ≤ k < m_i` is a leg. -/
theorem not_isLeg_of_lt_tripLength {i : Fin b} {k : ℕ} (hk : 0 < k) (hki : k < G.tripLength i) :
    ¬G.IsLeg (G.tripMap^[k] (G.leg i)) :=
  fun h => Nat.notMem_of_lt_sInf hki ⟨hk, h⟩

/-- If `Tᵏ(g_i)` is a leg for some `k ≥ 1`, then `m_i ≤ k`. -/
theorem tripLength_le {i : Fin b} {k : ℕ} (hk : 0 < k) (h : G.IsLeg (G.tripMap^[k] (G.leg i))) :
    G.tripLength i ≤ k :=
  Nat.sInf_le ⟨hk, h⟩

/-- If the one-way trip from `i` ends, it ends at the leg `g_{π_G(i)}`. -/
theorem leg_tripPerm {i : Fin b} (h : ∃ m, 0 < m ∧ G.IsLeg (G.tripMap^[m] (G.leg i))) :
    G.leg (G.tripPerm i) = G.tripMap^[G.tripLength i] (G.leg i) := by
  have h' : 0 < G.tripLength i ∧ ∃ j, G.leg j = G.tripMap^[G.tripLength i] (G.leg i) :=
    tripLength_spec h
  rw [tripPerm, dif_pos h']
  exact h'.2.choose_spec

/-! ### One-way trips end -/

section IsPlabicGraph

variable (hG : G.IsPlabicGraph)

include hG

/-- **One-way trips end**: in a plabic graph, for every label `i` there is `m ≥ 1` such that
`Tᵐ(g_i)` is a leg. -/
@[cluster_algebras "lem_trip_end_exists"]
theorem IsPlabicGraph.exists_isLeg_iterate_tripMap (i : Fin b) :
    ∃ m, 0 < m ∧ G.IsLeg (G.tripMap^[m] (G.leg i)) := by
  refine ⟨orderOf hG.tripEquiv, (isOfFinOrder_of_finite _).orderOf_pos, i, ?_⟩
  rw [← hG.tripEquiv_pow_apply, pow_orderOf_eq_one, Equiv.Perm.one_apply]

/-- In a plabic graph the legs are pairwise distinct. -/
theorem IsPlabicGraph.leg_injective : Function.Injective G.leg := fun i j h =>
  hG.bvertex_injective (by simp only [bvertex, h])

/-- In a plabic graph every one-way trip has positive length `m_i ≥ 1`. -/
theorem IsPlabicGraph.tripLength_pos (i : Fin b) : 0 < G.tripLength i :=
  (tripLength_spec (hG.exists_isLeg_iterate_tripMap i)).1

/-- In a plabic graph the one-way trip from `i` ends at the leg `g_{π_G(i)}`. -/
theorem IsPlabicGraph.leg_tripPerm (i : Fin b) :
    G.leg (G.tripPerm i) = G.tripMap^[G.tripLength i] (G.leg i) :=
  PlabicData.leg_tripPerm (hG.exists_isLeg_iterate_tripMap i)

/-- In a plabic graph `π_G(i) = j` exactly when `T^{m_i}(g_i) = g_j`. -/
theorem IsPlabicGraph.tripPerm_eq_iff {i j : Fin b} :
    G.tripPerm i = j ↔ G.tripMap^[G.tripLength i] (G.leg i) = G.leg j := by
  rw [← hG.leg_tripPerm, hG.leg_injective.eq_iff]

/-- In a plabic graph the trip through `d` is the orbit of `d` under the trip map. -/
theorem IsPlabicGraph.trip_eq_setOf_sameCycle (d : H) :
    G.trip d = {e | hG.tripEquiv.SameCycle d e} := by
  ext e
  refine ⟨fun ⟨n, hn⟩ => ⟨n, ?_⟩, fun h => ?_⟩
  · rw [zpow_natCast, hG.tripEquiv_pow_apply]
    exact hn
  · obtain ⟨n, hn⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq h
    exact ⟨n, (hG.tripEquiv_pow_apply n d).symm.trans hn⟩

end IsPlabicGraph

/-! ### Isomorphisms -/

namespace Iso

variable {H' : Type*} [Fintype H'] [DecidableEq H'] {G' : PlabicData H' b}

/-- An isomorphism commutes with the turns. -/
theorem map_turn (θ : G.Iso G') (z : H) : θ.toEquiv (G.turn z) = G'.turn (θ.toEquiv z) := by
  by_cases hz : G.IsBoundaryVertex (G.vertexOf z)
  · rw [turn_of_isBoundaryVertex hz,
      turn_of_isBoundaryVertex ((θ.isBoundaryVertex_vertexOf_iff z).2 hz)]
  · have hz' : ¬G'.IsBoundaryVertex (G'.vertexOf (θ.toEquiv z)) := by
      rwa [θ.isBoundaryVertex_vertexOf_iff]
    cases hc : G.colour z
    · rw [turn_of_white hz hc, turn_of_white hz' (by rw [θ.map_colour z hz, hc])]
      apply G'.rot.injective
      rw [← θ.map_rot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    · rw [turn_of_black hz hc, turn_of_black hz' (by rw [θ.map_colour z hz, hc]), θ.map_rot]

/-- **Isomorphisms commute with the trip maps**, first part: an isomorphism `θ : G → G'` maps
`H \ B` onto `H' \ B'`. -/
@[cluster_algebras "lem_trip_map_isomorphism"]
theorem bijOn_compl_bdry (θ : G.Iso G') :
    Set.BijOn θ.toEquiv {d | d ∉ G.bdry} {d | d ∉ G'.bdry} :=
  θ.toEquiv.bijOn fun d => not_congr (θ.mem_bdry_iff d)

/-- **Isomorphisms commute with the trip maps**, second part: `θ(T(d)) = T'(θ(d))`. This holds
for every dart `d`, not only for `d ∉ B`. -/
@[cluster_algebras "lem_trip_map_isomorphism"]
theorem map_tripMap (θ : G.Iso G') (d : H) :
    θ.toEquiv (G.tripMap d) = G'.tripMap (θ.toEquiv d) := by
  rw [tripMap_apply, tripMap_apply, map_turn, θ.map_inv]

end Iso

end PlabicData

end ClusterAlgebras
