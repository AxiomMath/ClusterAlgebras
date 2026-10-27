/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FirstReturn
public import ClusterAlgebras.Plabic.Trips

/-!
# Runs of one-way trips, trip sets and edge labels

Let `G` be a plabic graph with trip map `T` and legs `g_1, …, g_b`. The one-way trip from `i` is
the run `g_i, T(g_i), …, T^{m_i - 1}(g_i)` of the trip map up to the first return to a leg. Since
`T` is a permutation, a dart whose `T`-orbit contains a leg lies on exactly one one-way trip, and
a stretch `x, T(x), …, Tⁿ(x)` of darts that meets the one-way trip from `i` and passes no leg lies
on it in consecutive positions.

The *trip set* `tr(d)` of a dart `d` is the set of labels `i` such that `d` is a dart of the
one-way trip from `i`; it has at most one element. The *label* of an edge `{d, d̄}` is
`λ(d) = tr(d) ∪ tr(d̄)`, the set of one-way trips traversing the edge in either direction. At an
internal vertex, the *corner trip set* of a dart `e` records the one-way trip turning in the corner
between `e` and the dart following it clockwise, and the label of `e` is the union of the corner
trip sets of `e` and of `σ(e)`.

Finally, if `Y` is a set of darts containing every leg, the trip sets of the darts of `Y` and the
trip permutation are read off the first-return map `T_Y` of `T` to `Y`; so two plabic graphs whose
trip maps have the same first return to a common set `Y` of darts containing the legs have the
same trip permutation and the same trip sets on `Y`.

## Main definitions

* `ClusterAlgebras.PlabicData.edgeLabel`: the label `λ(e)` of an edge `e`.
* `ClusterAlgebras.PlabicData.tripSet`: the trip set `tr(d)` of a dart.
* `ClusterAlgebras.PlabicData.cornerTripSet`: the corner trip set `cr(e)`.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripPerm_eq_of_firstReturn`: trip permutations are
  determined by a first-return map containing the legs.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.existsUnique_mem_oneWayTrip`: a dart whose trip
  contains a leg lies on exactly one one-way trip.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip`:
  consecutive darts of a one-way trip.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripSet_leg`: `tr(g_i) = {i}`.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripSet_tripMap`: `tr(T(d)) = tr(d)` unless `T(d)` is
  a leg.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripSet_eq_of_firstReturn`: trip sets are determined
  by a first-return map.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.edgeLabel_edgeOf_eq_cornerTripSet_union`: labels from
  corners, `λ(e) = cr(e) ∪ cr(σ(e))`.

## Implementation notes

* **Labels.** The label set `[1, b]` is `Fin b`, `0`-indexed: the element `i : Fin b` is FWZ's
  label `i + 1`. Trip sets and edge labels are `Finset (Fin b)`.
* **Edges.** An edge `{d, d̄}` is the `Finset` `G.edgeOf d`, and the label of the edge of a
  dart `d`, written `λ(d)` in FWZ, is `G.edgeLabel (G.edgeOf d)`; it equals
  `G.tripSet d ∪ G.tripSet (G.inv d)` (`PlabicData.edgeLabel_edgeOf`).
* **Corner trip sets** are defined for every dart; FWZ define them only at internal
  vertices, where the colour of the dart decides between `tr(e)` and `tr(ē)`.
* **First-return maps.** The trip map of a plabic graph is the permutation
  `IsPlabicGraph.tripEquiv` of all darts, preserving `H \ B`; FWZ's trip map is its
  restriction to `H \ B`. For a set `Y ⊆ H \ B` both have the same first-return map to `Y`, and the
  results are stated for the first-return map `firstReturn hG.tripEquiv Y`. The inclusion
  `Y ⊆ H \ B` is then not needed and is not assumed: only the orbits of the legs, which lie in
  `H \ B`, are used.
* **Two dart sets.** In the comparison of two plabic graphs `G` and `G'` FWZ's common set
  `Y` of darts is a set `Y` of darts of `G` and a set `Y'` of darts of `G'` identified by a
  bijection `e : Y ≃ Y'`, which matches the legs and intertwines the first-return maps. For two
  graphs on one dart type, `e` is the identity
  (`IsPlabicGraph.tripPerm_eq_of_firstReturn_eq`, `IsPlabicGraph.tripSet_eq_of_firstReturn_eq`).
* **Superfluous hypotheses.** FWZ's hypotheses `d ∉ B` of
  `IsPlabicGraph.existsUnique_mem_oneWayTrip` and `IsPlabicGraph.tripSet_tripMap`, and `x ∉ B` of
  `IsPlabicGraph.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip`, are not needed and are not
  assumed.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Equiv Function

/-! ### Runs of a permutation and of its first-return map -/

section FirstReturnRuns

variable {X : Type*} [Finite X] {π : Perm X} {Y : Set X} {P : X → Prop}

/-- A run `y, π(y), …, π^k(y) = z` of `π` from `y ∈ Y` to `z ∈ Y`, `k ≥ 1`, along which `P` fails
strictly inside, is a run `y, π_Y(y), …, π_Y^s(y) = z` of the first-return map, `s ≥ 1`, along
which `P` fails strictly inside. -/
theorem exists_iterate_firstReturn_of_pow_avoiding (k : ℕ) (y : Y) {z : X} (hz : z ∈ Y)
    (hk : 0 < k) (hkz : (π ^ k) y = z) (hrun : ∀ t, 0 < t → t < k → ¬P ((π ^ t) y)) :
    ∃ s, 0 < s ∧ ((firstReturn π Y)^[s] y : X) = z ∧
      ∀ t, 0 < t → t < s → ¬P ((firstReturn π Y)^[t] y) := by
  induction k using Nat.strong_induction_on generalizing y z with
  | _ k ih =>
  have hle : firstReturnTime π Y y ≤ k := firstReturnTime_le hk (hkz ▸ hz)
  have hpos := firstReturnTime_pos (π := π) (Y := Y) y
  rcases hle.lt_or_eq with hlt | heq
  · have hR : (π ^ (k - firstReturnTime π Y y)) (firstReturn π Y y : X) = z := by
      rw [coe_firstReturn, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle, hkz]
    obtain ⟨s, hs, hsz, hsrun⟩ := ih (k - firstReturnTime π Y y) (by omega) (firstReturn π Y y)
      hz (by omega) hR (fun t ht htk => by
        rw [coe_firstReturn, ← Perm.mul_apply, ← pow_add]
        exact hrun _ (by omega) (by omega))
    refine ⟨s + 1, by omega, by rwa [iterate_succ_apply], fun t ht hts => ?_⟩
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · obtain rfl : t = 1 := by omega
      rw [iterate_one, coe_firstReturn]
      exact hrun _ hpos hlt
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      rw [iterate_succ_apply]
      exact hsrun u (by omega) (by omega)
  · refine ⟨1, one_pos, ?_, fun t ht ht1 => by omega⟩
    rw [iterate_one, coe_firstReturn, heq, hkz]

/-- Let `P` hold only on `Y`. A run `y, π_Y(y), …, π_Y^s(y)` of the first-return map, `s ≥ 1`,
along which `P` fails strictly inside, is a run `y, π(y), …, π^k(y) = π_Y^s(y)` of `π`, `k ≥ 1`,
along which `P` fails strictly inside. -/
theorem exists_pow_of_iterate_firstReturn_avoiding (hP : ∀ x, P x → x ∈ Y) (s : ℕ) (y : Y)
    (hs : 0 < s) (hrun : ∀ t, 0 < t → t < s → ¬P ((firstReturn π Y)^[t] y)) :
    ∃ k, 0 < k ∧ (π ^ k) y = ((firstReturn π Y)^[s] y : X) ∧
      ∀ t, 0 < t → t < k → ¬P ((π ^ t) y) := by
  induction s generalizing y with
  | zero => exact absurd hs (lt_irrefl 0)
  | succ s ih =>
  have hpos := firstReturnTime_pos (π := π) (Y := Y) y
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨firstReturnTime π Y y, hpos, by rw [iterate_one, coe_firstReturn],
      fun t ht htk hPt => ?_⟩
    exact pow_apply_notMem_of_lt_firstReturnTime ht htk (hP _ hPt)
  · obtain ⟨k, hk, hkz, hkrun⟩ := ih (firstReturn π Y y) hs (fun t ht hts => by
      rw [← iterate_succ_apply]
      exact hrun _ (by omega) (by omega))
    refine ⟨k + firstReturnTime π Y y, by omega, ?_, fun t ht htk => ?_⟩
    · rw [pow_add, Perm.mul_apply, ← coe_firstReturn, hkz, iterate_succ_apply]
    · rcases lt_trichotomy t (firstReturnTime π Y y) with hlt | heq | hgt
      · exact fun hPt => pow_apply_notMem_of_lt_firstReturnTime ht hlt (hP _ hPt)
      · have := hrun 1 one_pos (by omega)
        rwa [iterate_one, coe_firstReturn, ← heq] at this
      · have := hkrun (t - firstReturnTime π Y y) (by omega) (by omega)
        rwa [coe_firstReturn, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hgt.le] at this

end FirstReturnRuns

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### Trip sets, edge labels and corner trip sets -/

/-- The **trip set** `tr_G(d)` of a dart `d`: the set of labels `i` such that `d` is a dart of the
one-way trip from `i`. Labels are `0`-indexed, so `i : Fin b` stands for the label `i + 1`. -/
@[cluster_algebras "def_dart_trip_set"]
noncomputable def tripSet (d : H) : Finset (Fin b) := {i | d ∈ G.oneWayTrip i}

/-- The **label** `λ(e)` of an edge `e = {d, d̄}`: the set of labels `i` such that the one-way trip
from `i` traverses the edge along `d` or along `d̄`, that is, has a dart in `e`. Labels are
`0`-indexed, so `i : Fin b` stands for the label `i + 1`. The label of the edge of a dart `d` is
`G.edgeLabel (G.edgeOf d)`. -/
@[cluster_algebras "def_edge_labeling"]
noncomputable def edgeLabel (e : Finset H) : Finset (Fin b) := {i | ∃ d ∈ e, d ∈ G.oneWayTrip i}

/-- The **corner trip set** `cr(e)` of a dart `e`: `tr(e)` if `v(e)` is black and `tr(ē)` if `v(e)`
is white. At an internal vertex it records the one-way trip turning in the corner between `e` and
the dart following it clockwise. -/
@[cluster_algebras "def_corner_trip_set"]
noncomputable def cornerTripSet (e : H) : Finset (Fin b) :=
  match G.colour e with
  | .black => G.tripSet e
  | .white => G.tripSet (G.inv e)

variable {G}

/-- `i ∈ tr(d)` if and only if `d` is a dart of the one-way trip from `i`. -/
@[simp]
theorem mem_tripSet {d : H} {i : Fin b} : i ∈ G.tripSet d ↔ d ∈ G.oneWayTrip i := by
  simp [tripSet]

/-- `i ∈ λ(e)` if and only if the one-way trip from `i` has a dart in `e`. -/
@[simp]
theorem mem_edgeLabel {e : Finset H} {i : Fin b} :
    i ∈ G.edgeLabel e ↔ ∃ d ∈ e, d ∈ G.oneWayTrip i := by
  simp [edgeLabel]

/-- The label of the edge of `d` is `λ(d) = tr(d) ∪ tr(d̄)`. -/
theorem edgeLabel_edgeOf (d : H) :
    G.edgeLabel (G.edgeOf d) = G.tripSet d ∪ G.tripSet (G.inv d) := by
  ext i
  simp [RotationSystem.edgeOf]

/-- At a black vertex, `cr(e) = tr(e)`. -/
theorem cornerTripSet_of_black {e : H} (h : G.colour e = .black) :
    G.cornerTripSet e = G.tripSet e := by
  simp [cornerTripSet, h]

/-- At a white vertex, `cr(e) = tr(ē)`, the trip set of the reverse dart. -/
theorem cornerTripSet_of_white {e : H} (h : G.colour e = .white) :
    G.cornerTripSet e = G.tripSet (G.inv e) := by
  simp [cornerTripSet, h]

/-! ### One-way trips in a plabic graph -/

section IsPlabicGraph

variable (hG : G.IsPlabicGraph)

include hG

/-- The label of an edge does not depend on the dart chosen: `λ(d̄) = λ(d)`. -/
theorem IsPlabicGraph.edgeLabel_edgeOf_inv (d : H) :
    G.edgeLabel (G.edgeOf (G.inv d)) = G.edgeLabel (G.edgeOf d) := by
  rw [edgeLabel_edgeOf, edgeLabel_edgeOf, hG.inv_involutive d, Finset.union_comm]

/-- A dart at an internal vertex is not a leg. -/
theorem IsPlabicGraph.not_isLeg_of_not_isBoundaryVertex {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) : ¬G.IsLeg d := by
  rintro ⟨j, rfl⟩
  exact hd (G.mem_boundaryVertices.1 (hG.bvertex_mem j)).2

/-- Two darts `T^p(g_i)` and `T^q(g_j)` of the one-way trips from `i` and `j` coincide only if
`i = j` and `p = q`. -/
theorem IsPlabicGraph.eq_and_eq_of_iterate_leg_eq {i j : Fin b} {p q : ℕ}
    (hp : p < G.tripLength i) (hq : q < G.tripLength j)
    (h : G.tripMap^[p] (G.leg i) = G.tripMap^[q] (G.leg j)) : i = j ∧ p = q := by
  wlog hpq : p ≤ q generalizing i j p q
  · exact (this hq hp h.symm (le_of_not_ge hpq)).imp Eq.symm Eq.symm
  have h' : G.tripMap^[p] (G.tripMap^[q - p] (G.leg j)) = G.tripMap^[p] (G.leg i) := by
    rw [← iterate_add_apply, Nat.add_sub_cancel' hpq, h]
  have h2 := ((tripMap_bijective hG).injective.iterate p) h'
  rcases Nat.eq_zero_or_pos (q - p) with h0 | hpos
  · rw [h0, iterate_zero_apply] at h2
    exact ⟨(hG.leg_injective h2).symm, by omega⟩
  · exact ((not_isLeg_of_lt_tripLength hpos (by omega : q - p < G.tripLength j))
      ⟨i, h2.symm⟩).elim

/-- A dart lies on at most one one-way trip. -/
theorem IsPlabicGraph.eq_of_mem_oneWayTrip {d : H} {i j : Fin b} (hi : d ∈ G.oneWayTrip i)
    (hj : d ∈ G.oneWayTrip j) : i = j := by
  obtain ⟨p, hp, rfl⟩ := mem_oneWayTrip.1 hi
  obtain ⟨q, hq, hqp⟩ := mem_oneWayTrip.1 hj
  exact (hG.eq_and_eq_of_iterate_leg_eq hp hq hqp.symm).1

/-- Every dart `T^k(g_j)` lies on some one-way trip. -/
theorem IsPlabicGraph.exists_iterate_leg_mem_oneWayTrip (j : Fin b) (k : ℕ) :
    ∃ i, G.tripMap^[k] (G.leg j) ∈ G.oneWayTrip i := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
  by_cases hk : k < G.tripLength j
  · exact ⟨j, mem_oneWayTrip.2 ⟨k, hk, rfl⟩⟩
  · have hpos := hG.tripLength_pos j
    have e : G.tripMap^[k] (G.leg j) =
        G.tripMap^[k - G.tripLength j] (G.leg (G.tripPerm j)) := by
      rw [hG.leg_tripPerm, ← iterate_add_apply, Nat.sub_add_cancel (not_lt.1 hk)]
    rw [e]
    exact ih _ (by omega) _

/-- **A dart on a trip from the boundary lies on exactly one one-way trip**: if the trip of `d`
contains a leg, then `d` is a dart of the one-way trip from exactly one label `i`. -/
@[cluster_algebras "lem_trip_dart_unique"]
theorem IsPlabicGraph.existsUnique_mem_oneWayTrip {d : H} (h : ∃ j, G.leg j ∈ G.trip d) :
    ∃! i, d ∈ G.oneWayTrip i := by
  obtain ⟨j, hj⟩ := h
  have hj' : hG.tripEquiv.SameCycle d (G.leg j) := by
    rwa [hG.trip_eq_setOf_sameCycle] at hj
  obtain ⟨k, hk⟩ := hj'.symm.exists_nat_pow_eq
  rw [hG.tripEquiv_pow_apply] at hk
  obtain ⟨i, hi⟩ := hG.exists_iterate_leg_mem_oneWayTrip j k
  rw [hk] at hi
  exact ⟨i, hi, fun i' hi' => hG.eq_of_mem_oneWayTrip hi' hi⟩

/-- **Consecutive darts of a one-way trip**: if none of `T(x), …, Tⁿ(x)` is a leg and some
`T^j(x)`, `j ≤ n`, is a dart of the one-way trip from `i`, then `x = T^p(g_i)` with
`p + n ≤ m_i - 1`; so `x, T(x), …, Tⁿ(x)` are the darts of that one-way trip in the positions
`p, …, p + n`. -/
@[cluster_algebras "lem_trip_run"]
theorem IsPlabicGraph.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip {i : Fin b} {x : H}
    {n j : ℕ} (hleg : ∀ l, 0 < l → l ≤ n → ¬G.IsLeg (G.tripMap^[l] x)) (hjn : j ≤ n)
    (hj : G.tripMap^[j] x ∈ G.oneWayTrip i) :
    ∃ p, G.tripMap^[p] (G.leg i) = x ∧ p + n < G.tripLength i := by
  obtain ⟨q, hq, hqx⟩ := mem_oneWayTrip.1 hj
  have hinj := (tripMap_bijective hG).injective
  by_cases hqj : q < j
  · refine (hleg (j - q) (by omega) (by omega) ⟨i, ?_⟩).elim
    apply hinj.iterate q
    rw [← iterate_add_apply, Nat.add_sub_cancel' hqj.le, hqx]
  · have hpx : G.tripMap^[q - j] (G.leg i) = x := by
      apply hinj.iterate j
      rw [← iterate_add_apply, Nat.add_sub_cancel' (not_lt.1 hqj), hqx]
    refine ⟨q - j, hpx, ?_⟩
    by_contra hcon
    refine hleg (G.tripLength i - (q - j)) (by omega) (by omega) ⟨G.tripPerm i, ?_⟩
    rw [hG.leg_tripPerm, ← hpx, ← iterate_add_apply, Nat.sub_add_cancel (by omega)]

/-! ### Trip sets in a plabic graph -/

/-- A trip set has at most one element. -/
theorem IsPlabicGraph.card_tripSet_le_one (d : H) : (G.tripSet d).card ≤ 1 :=
  Finset.card_le_one.2 fun _ hi _ hj =>
    hG.eq_of_mem_oneWayTrip (mem_tripSet.1 hi) (mem_tripSet.1 hj)

/-- A dart whose trip contains no leg, such as a dart of a roundtrip, has an empty trip set. -/
theorem IsPlabicGraph.tripSet_eq_empty_of_forall_not_isLeg {d : H}
    (h : ∀ n, ¬G.IsLeg (G.tripMap^[n] d)) :
    G.tripSet d = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  obtain ⟨k, -, hkd⟩ := mem_oneWayTrip.1 (mem_tripSet.1 hi)
  have hsc : hG.tripEquiv.SameCycle (G.leg i) d :=
    ⟨k, by rw [zpow_natCast, hG.tripEquiv_pow_apply, hkd]⟩
  obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq
  exact h n ⟨i, by rw [← hG.tripEquiv_pow_apply, hn]⟩

/-- **The trip set of a leg**: `tr(g_i) = {i}`. -/
@[cluster_algebras "lem_dart_trip_set_leg"]
theorem IsPlabicGraph.tripSet_leg (i : Fin b) : G.tripSet (G.leg i) = {i} := by
  have hi : G.leg i ∈ G.oneWayTrip i := mem_oneWayTrip.2 ⟨0, hG.tripLength_pos i, rfl⟩
  ext j
  simp only [mem_tripSet, Finset.mem_singleton]
  exact ⟨fun hj => hG.eq_of_mem_oneWayTrip hj hi, fun h => h ▸ hi⟩

/-- **Trip sets along a trip**: if `T(d)` is not a leg, then `tr(T(d)) = tr(d)`. -/
@[cluster_algebras "lem_dart_trip_set_step"]
theorem IsPlabicGraph.tripSet_tripMap {d : H} (hd : ¬G.IsLeg (G.tripMap d)) :
    G.tripSet (G.tripMap d) = G.tripSet d := by
  ext i
  simp only [mem_tripSet, mem_oneWayTrip]
  constructor
  · rintro ⟨k, hk, hkd⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact (hd ⟨i, hkd⟩).elim
    · obtain ⟨u, rfl⟩ : ∃ u, k = u + 1 := ⟨k - 1, by omega⟩
      exact ⟨u, by omega, (tripMap_bijective hG).injective
        ((iterate_succ_apply' _ _ _).symm.trans hkd)⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k + 1, ?_, iterate_succ_apply' _ _ _⟩
    by_contra hcon
    have hkm : k + 1 = G.tripLength i := by omega
    exact hd ⟨G.tripPerm i, by rw [hG.leg_tripPerm, ← hkm, iterate_succ_apply']⟩

/-- **Labels from corners**: for a dart `e` at an internal vertex, `λ(e) = cr(e) ∪ cr(σ(e))`. -/
@[cluster_algebras "lem_label_corner_sets"]
theorem IsPlabicGraph.edgeLabel_edgeOf_eq_cornerTripSet_union {e : H}
    (he : ¬G.IsBoundaryVertex (G.vertexOf e)) :
    G.edgeLabel (G.edgeOf e) = G.cornerTripSet e ∪ G.cornerTripSet (G.rot e) := by
  have he' : ¬G.IsBoundaryVertex (G.vertexOf (G.rot e)) := by rwa [G.vertexOf_rot]
  rw [edgeLabel_edgeOf]
  cases hc : G.colour e
  · have hc' : G.colour (G.rot e) = .white := by rw [hG.colour_rot _ he, hc]
    rw [cornerTripSet_of_white hc, cornerTripSet_of_white hc']
    have hT : G.tripMap (G.inv (G.rot e)) = e := by
      rw [tripMap_apply, hG.inv_involutive, turn_of_white he' hc', Equiv.symm_apply_apply]
    have h := hG.tripSet_tripMap (d := G.inv (G.rot e))
      (hT.symm ▸ hG.not_isLeg_of_not_isBoundaryVertex he)
    rw [hT] at h
    rw [h, Finset.union_comm]
  · have hc' : G.colour (G.rot e) = .black := by rw [hG.colour_rot _ he, hc]
    rw [cornerTripSet_of_black hc, cornerTripSet_of_black hc']
    have hT : G.tripMap (G.inv e) = G.rot e := by
      rw [tripMap_apply, hG.inv_involutive, turn_of_black he hc]
    have h := hG.tripSet_tripMap (d := G.inv e)
      (hT.symm ▸ hG.not_isLeg_of_not_isBoundaryVertex he')
    rw [hT] at h
    rw [h]

/-! ### One-way trips through a first-return map -/

/-- The darts of the one-way trip from `i`: `d = T^k(g_i)` with none of `T(g_i), …, T^k(g_i)` a
leg. -/
theorem IsPlabicGraph.mem_oneWayTrip_iff_exists {d : H} {i : Fin b} :
    d ∈ G.oneWayTrip i ↔ ∃ k, G.tripMap^[k] (G.leg i) = d ∧
      ∀ t, 0 < t → t ≤ k → ¬G.IsLeg (G.tripMap^[t] (G.leg i)) := by
  rw [mem_oneWayTrip]
  constructor
  · rintro ⟨k, hk, hkd⟩
    exact ⟨k, hkd, fun t ht htk => not_isLeg_of_lt_tripLength ht (by omega)⟩
  · rintro ⟨k, hkd, hrun⟩
    refine ⟨k, ?_, hkd⟩
    by_contra hcon
    exact hrun _ (hG.tripLength_pos i) (by omega)
      (tripLength_spec (hG.exists_isLeg_iterate_tripMap i)).2

/-- `π_G(i) = j` exactly when `T^k(g_i) = g_j` for some `k ≥ 1` with none of
`T(g_i), …, T^{k-1}(g_i)` a leg. -/
theorem IsPlabicGraph.tripPerm_eq_iff_exists {i j : Fin b} :
    G.tripPerm i = j ↔ ∃ k, 0 < k ∧ G.tripMap^[k] (G.leg i) = G.leg j ∧
      ∀ t, 0 < t → t < k → ¬G.IsLeg (G.tripMap^[t] (G.leg i)) := by
  rw [hG.tripPerm_eq_iff]
  constructor
  · intro h
    exact ⟨_, hG.tripLength_pos i, h, fun t ht htk => not_isLeg_of_lt_tripLength ht htk⟩
  · rintro ⟨k, hk, hkj, hrun⟩
    have hle : G.tripLength i ≤ k := tripLength_le hk ⟨j, hkj.symm⟩
    rcases hle.lt_or_eq with hlt | rfl
    · exact ((hrun _ (hG.tripLength_pos i) hlt)
        (tripLength_spec (hG.exists_isLeg_iterate_tripMap i)).2).elim
    · exact hkj

variable {Y : Set H} (hY : ∀ i, G.leg i ∈ Y)

include hY

/-- The darts in `Y` of the one-way trip from `i` are the `T_Y^s(g_i)` such that none of
`T_Y(g_i), …, T_Y^s(g_i)` is a leg, for `Y` containing the legs. -/
theorem IsPlabicGraph.mem_oneWayTrip_iff_firstReturn (y : Y) (i : Fin b) :
    (y : H) ∈ G.oneWayTrip i ↔
      ∃ s, ((firstReturn hG.tripEquiv Y)^[s] ⟨G.leg i, hY i⟩ : H) = y ∧
        ∀ t, 0 < t → t ≤ s → ¬G.IsLeg ((firstReturn hG.tripEquiv Y)^[t] ⟨G.leg i, hY i⟩) := by
  have hP : ∀ x, G.IsLeg x → x ∈ Y := fun _ ⟨j, hj⟩ => hj ▸ hY j
  rw [hG.mem_oneWayTrip_iff_exists]
  constructor
  · rintro ⟨k, hky, hrun⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨0, hky, fun t ht htk => by omega⟩
    · obtain ⟨s, hs, hsy, hsrun⟩ := exists_iterate_firstReturn_of_pow_avoiding k
        ⟨G.leg i, hY i⟩ y.2 hk (by rwa [hG.tripEquiv_pow_apply])
        (fun t ht htk => by simpa only [hG.tripEquiv_pow_apply] using hrun t ht htk.le)
      refine ⟨s, hsy, fun t ht hts => ?_⟩
      rcases hts.lt_or_eq with hlt | heq
      · exact hsrun t ht hlt
      · rw [heq, hsy]
        exact hky ▸ hrun k hk le_rfl
  · rintro ⟨s, hsy, hrun⟩
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact ⟨0, hsy, fun t ht htk => by omega⟩
    · obtain ⟨k, hk, hky, hkrun⟩ := exists_pow_of_iterate_firstReturn_avoiding hP s
        ⟨G.leg i, hY i⟩ hs (fun t ht hts => hrun t ht hts.le)
      rw [hG.tripEquiv_pow_apply, hsy] at hky
      refine ⟨k, hky, fun t ht htk => ?_⟩
      rcases htk.lt_or_eq with hlt | heq
      · simpa only [hG.tripEquiv_pow_apply] using hkrun t ht hlt
      · rw [heq, hky, ← hsy]
        exact hrun s hs le_rfl

/-- `π_G(i) = j` exactly when `T_Y^s(g_i) = g_j` for some `s ≥ 1` with none of
`T_Y(g_i), …, T_Y^{s-1}(g_i)` a leg, for `Y` containing the legs. -/
theorem IsPlabicGraph.tripPerm_eq_iff_firstReturn (i j : Fin b) :
    G.tripPerm i = j ↔
      ∃ s, 0 < s ∧ ((firstReturn hG.tripEquiv Y)^[s] ⟨G.leg i, hY i⟩ : H) = G.leg j ∧
        ∀ t, 0 < t → t < s → ¬G.IsLeg ((firstReturn hG.tripEquiv Y)^[t] ⟨G.leg i, hY i⟩) := by
  have hP : ∀ x, G.IsLeg x → x ∈ Y := fun _ ⟨j, hj⟩ => hj ▸ hY j
  rw [hG.tripPerm_eq_iff_exists]
  constructor
  · rintro ⟨k, hk, hkj, hrun⟩
    exact exists_iterate_firstReturn_of_pow_avoiding k ⟨G.leg i, hY i⟩ (hY j) hk
      (by rwa [hG.tripEquiv_pow_apply])
      (fun t ht htk => by simpa only [hG.tripEquiv_pow_apply] using hrun t ht htk)
  · rintro ⟨s, hs, hsj, hrun⟩
    obtain ⟨k, hk, hkj, hkrun⟩ := exists_pow_of_iterate_firstReturn_avoiding hP s
      ⟨G.leg i, hY i⟩ hs hrun
    rw [hG.tripEquiv_pow_apply, hsj] at hkj
    exact ⟨k, hk, hkj, fun t ht htk => by
      simpa only [hG.tripEquiv_pow_apply] using hkrun t ht htk⟩

end IsPlabicGraph

/-! ### Comparing two plabic graphs through a first-return map -/

section Compare

variable {H' : Type*} [Fintype H'] [DecidableEq H'] {G' : PlabicData H' b}
  {Y : Set H} {Y' : Set H'}

omit [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] in
private theorem leg_mem_of_equiv (e : Y ≃ Y')
    (hleg : ∀ i, ∃ h : G.leg i ∈ Y, (e ⟨G.leg i, h⟩ : H') = G'.leg i) (i : Fin b) :
    G'.leg i ∈ Y' := by
  obtain ⟨h, he⟩ := hleg i
  rw [← he]
  exact (e _).2

omit [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] in
private theorem isLeg_iff_of_equiv (e : Y ≃ Y')
    (hleg : ∀ i, ∃ h : G.leg i ∈ Y, (e ⟨G.leg i, h⟩ : H') = G'.leg i) (y : Y) :
    G.IsLeg (y : H) ↔ G'.IsLeg (e y : H') := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨h, he⟩ := hleg j
    obtain rfl : y = ⟨G.leg j, h⟩ := Subtype.ext hj.symm
    exact ⟨j, he.symm⟩
  · rintro ⟨j, hj⟩
    obtain ⟨h, he⟩ := hleg j
    have : e y = e ⟨G.leg j, h⟩ := Subtype.ext (hj.symm.trans he.symm)
    rw [e.injective this]
    exact ⟨j, rfl⟩

variable (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (e : Y ≃ Y')
  (hleg : ∀ i, ∃ h : G.leg i ∈ Y, (e ⟨G.leg i, h⟩ : H') = G'.leg i)
  (hfr : ∀ y, e (firstReturn hG.tripEquiv Y y) = firstReturn hG'.tripEquiv Y' (e y))

include hleg hfr

/-- **Trip sets are determined by a first-return map**. Let `G` and `G'` be plabic graphs, let `Y`
be a set of darts of `G` and `Y'` a set of darts of `G'`, identified by a bijection `e : Y ≃ Y'`
which maps the leg `g_i` of `G` to the leg `g'_i` of `G'` for every `i` and intertwines the
first-return maps `T_Y` and `T'_{Y'}` of the trip maps. Then `tr_G(y) = tr_{G'}(e(y))` for every
`y ∈ Y`. -/
@[cluster_algebras "lem_dart_trip_set_first_return"]
theorem IsPlabicGraph.tripSet_eq_of_firstReturn (y : Y) : G.tripSet y = G'.tripSet (e y) := by
  have hY : ∀ i, G.leg i ∈ Y := fun i => (hleg i).1
  have hY' := leg_mem_of_equiv e hleg
  have he_leg : ∀ i, e ⟨G.leg i, hY i⟩ = ⟨G'.leg i, hY' i⟩ := fun i => Subtype.ext (hleg i).2
  have hiter : ∀ (s : ℕ) (y : Y),
      e ((firstReturn hG.tripEquiv Y)^[s] y) = (firstReturn hG'.tripEquiv Y')^[s] (e y) :=
    fun s y => Semiconj.iterate_right (f := e) hfr s y
  have hlegiff := isLeg_iff_of_equiv e hleg
  ext i
  rw [mem_tripSet, mem_tripSet, hG.mem_oneWayTrip_iff_firstReturn hY,
    hG'.mem_oneWayTrip_iff_firstReturn hY']
  constructor
  · rintro ⟨s, hs, hrun⟩
    refine ⟨s, ?_, fun t ht hts => ?_⟩
    · rw [← he_leg, ← hiter, Subtype.ext hs]
    · rw [← he_leg, ← hiter, ← hlegiff]
      exact hrun t ht hts
  · rintro ⟨s, hs, hrun⟩
    refine ⟨s, ?_, fun t ht hts => ?_⟩
    · rw [← he_leg, ← hiter] at hs
      rw [e.injective (Subtype.ext hs)]
    · rw [hlegiff, hiter, he_leg]
      exact hrun t ht hts

/-- **Trip permutations through a common first return**. Let `G` and `G'` be plabic graphs with
`b` boundary vertices, let `Y` be a set of darts of `G` and `Y'` a set of darts of `G'`, identified
by a bijection `e : Y ≃ Y'` which maps the leg `g_i` of `G` to the leg `g'_i` of `G'` for every
`i` and intertwines the first-return maps `T_Y` and `T'_{Y'}` of the trip maps. Then
`π_G = π_{G'}`. -/
@[cluster_algebras "lem_trip_first_return"]
theorem IsPlabicGraph.tripPerm_eq_of_firstReturn : G.tripPerm = G'.tripPerm := by
  have hY : ∀ i, G.leg i ∈ Y := fun i => (hleg i).1
  have hY' := leg_mem_of_equiv e hleg
  have he_leg : ∀ i, e ⟨G.leg i, hY i⟩ = ⟨G'.leg i, hY' i⟩ := fun i => Subtype.ext (hleg i).2
  have hiter : ∀ (s : ℕ) (y : Y),
      e ((firstReturn hG.tripEquiv Y)^[s] y) = (firstReturn hG'.tripEquiv Y')^[s] (e y) :=
    fun s y => Semiconj.iterate_right (f := e) hfr s y
  funext i
  obtain ⟨s, hs, hsj, hrun⟩ := (hG.tripPerm_eq_iff_firstReturn hY i (G.tripPerm i)).1 rfl
  symm
  rw [hG'.tripPerm_eq_iff_firstReturn hY']
  refine ⟨s, hs, ?_, fun t ht hts => ?_⟩
  · rw [← he_leg, ← hiter, (Subtype.ext hsj : _ = (⟨G.leg (G.tripPerm i), hY _⟩ : Y)), he_leg]
  · rw [← he_leg, ← hiter, ← isLeg_iff_of_equiv e hleg]
    exact hrun t ht hts

end Compare

/-- If two plabic graphs `G` and `G'` on the same darts have the same legs, and their trip maps
have the same first-return map to a set `Y` of darts containing the legs, then `π_G = π_{G'}`. -/
theorem IsPlabicGraph.tripPerm_eq_of_firstReturn_eq {G G' : PlabicData H b} (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) {Y : Set H} (hY : ∀ i, G.leg i ∈ Y) (hleg : G.leg = G'.leg)
    (hfr : firstReturn hG.tripEquiv Y = firstReturn hG'.tripEquiv Y) : G.tripPerm = G'.tripPerm :=
  hG.tripPerm_eq_of_firstReturn hG' (Equiv.refl Y) (fun i => ⟨hY i, by simp [hleg]⟩)
    (fun y => by simp [hfr])

/-- If two plabic graphs `G` and `G'` on the same darts have the same legs, and their trip maps
have the same first-return map to a set `Y` of darts containing the legs, then
`tr_G(y) = tr_{G'}(y)` for every `y ∈ Y`. -/
theorem IsPlabicGraph.tripSet_eq_of_firstReturn_eq {G G' : PlabicData H b} (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) {Y : Set H} (hY : ∀ i, G.leg i ∈ Y) (hleg : G.leg = G'.leg)
    (hfr : firstReturn hG.tripEquiv Y = firstReturn hG'.tripEquiv Y) {y : H} (hy : y ∈ Y) :
    G.tripSet y = G'.tripSet y :=
  hG.tripSet_eq_of_firstReturn hG' (Equiv.refl Y) (fun i => ⟨hY i, by simp [hleg]⟩)
    (fun y => by simp [hfr]) ⟨y, hy⟩

end PlabicData

end ClusterAlgebras
