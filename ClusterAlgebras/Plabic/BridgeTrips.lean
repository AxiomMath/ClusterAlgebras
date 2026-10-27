/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BridgePlabic
public import ClusterAlgebras.Plabic.CornerTriangulation
public import ClusterAlgebras.Plabic.TripRuns

/-!
# Trips of the bridge graph

Let `s = ((i₁, j₁), …, (i_r, j_r))` be a nested sequence of pairs with `1 ≤ i_t < j_t ≤ b` and
`γ : [1, b] → {white, black}`, and let `G(s, γ)` be the bridge graph. This file collects the facts
about the vertices and the trips of `G(s, γ)` used to show that bridge decompositions are reduced.

The only white internal vertices of `G(s, γ)` with at least three darts are the white ends
`{up_{i_t,t}, dn_{i_t,t}, c_t}` of the bridges that are not the lowest one on their line, so these
are the crossings. The keys of the darts strictly increase along the trip map until a leg is
reached; as keys are bounded, every trip reaches a leg, and `G(s, γ)` has no roundtrip.

Finally the one-way trips are *wires*: the trip from `ρ_τ⁻¹(y)` runs down the line of `y` through
the darts `dn_{y,u}` at the heights `u ≤ τ` (where `ρ_τ = τ_τ ∘ ⋯ ∘ τ₁` is the position map), it
arrives at the black end of the `t`-th bridge along `c̄_t` when it is on the line of `j_t` just
before height `t`, and the trip ending at `z` climbs the line of `z` through all the darts
`up_{z,u}`.

## Main results

* `ClusterAlgebras.exists_eq_of_isCrossing_bridgeGraph`: the crossings of the bridge graph.
* `ClusterAlgebras.BridgeDart.key_lt_key_tripMap`: keys increase along trips.
* `ClusterAlgebras.not_hasRoundtrip_bridgeGraph`: the bridge graph has no roundtrip.
* `ClusterAlgebras.dn_mem_oneWayTrip_bridgeGraph`: the down darts of a trip.
* `ClusterAlgebras.bridgeRev_mem_oneWayTrip_bridgeGraph`: the bridge dart arriving at a black
  end.
* `ClusterAlgebras.up_mem_oneWayTrip_bridgeGraph`: the up darts of a trip.

## Implementation notes

* **Labels.** As in the construction of the bridge graph, `x : Fin b` is FWZ's label
  `x + 1`, while the entries of the pairs are FWZ's integers; the position map
  `positionMap s τ` is a permutation of `ℤ`, so FWZ's `ρ_τ⁻¹(y)` is the label `x` with
  `x + 1 = (positionMap s τ).symm (y + 1)`.
* **Hypotheses.** FWZ assume throughout that `b ≥ 1`, that `s` is nested and that
  `1 ≤ i_t < j_t ≤ b`. The crossings are determined without any of these hypotheses; the
  statements about keys and roundtrips use only `1 ≤ i_t < j_t ≤ b`. The statements about one-way
  trips use that `G(s, γ)` is a plabic graph, hence all three.
* **No roundtrip.** FWZ argue that `T^p(z) = z` for the size `p` of an orbit; here the
  keys of the darts are bounded by `4r + 4`, so a trip that met no leg would have unbounded keys.
  This does not need the trip map to be a permutation.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset BridgeGraph BridgeSymbol

/-! ### Generalities -/

/-- The vertex of a dart fixed by the `n`-th power of the rotation, `n ≥ 1`, has at most `n`
darts. -/
private theorem card_vertexOf_le_of_pow_apply_eq {α : Type*} [Fintype α] [DecidableEq α]
    (R : RotationSystem α) {d : α} {n : ℕ} (hn : 0 < n) (h : (R.rot ^ n) d = d) :
    (R.vertexOf d).card ≤ n := by
  calc (R.vertexOf d).card ≤ ((range n).image fun k => (R.rot ^ k) d).card := by
        apply card_le_card
        intro e he
        obtain ⟨m, rfl⟩ := (R.mem_vertexOf.1 he).exists_nat_pow_eq
        refine mem_image.2 ⟨m % n, mem_range.2 (Nat.mod_lt _ hn), ?_⟩
        conv_rhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, Equiv.Perm.mul_apply,
          Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h]
    _ ≤ (range n).card := card_image_le
    _ = n := card_range n

/-- The vertex of a dart fixed by the cube of the rotation consists of the dart and its first two
images. -/
private theorem vertexOf_eq_of_rot_rot_rot' {α : Type*} [Fintype α] [DecidableEq α]
    (R : RotationSystem α) {d : α} (h : R.rot (R.rot (R.rot d)) = d) :
    R.vertexOf d = {d, R.rot d, R.rot (R.rot d)} := by
  ext e
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro he
    obtain ⟨n, rfl⟩ := he.exists_nat_pow_eq
    clear he
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      simp only [mem_insert, mem_singleton] at ih ⊢
      rcases ih with h' | h' | h' <;> rw [h'] <;> simp [h]
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact .refl _ _
    · exact Equiv.Perm.sameCycle_apply_right.2 (.refl _ _)
    · exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.sameCycle_apply_right.2 (.refl _ _))

/-- A stretch of a trip following a dart of a one-way trip and meeting no leg stays on that
one-way trip. -/
private theorem iterate_mem_oneWayTrip_of_not_isLeg {H : Type*} [Fintype H] [DecidableEq H]
    {b : ℕ} {G : PlabicData H b} (hG : G.IsPlabicGraph) {i : Fin b} {d : H} {n : ℕ}
    (hd : d ∈ G.oneWayTrip i) (hleg : ∀ l, 0 < l → l ≤ n → ¬G.IsLeg (G.tripMap^[l] d)) :
    G.tripMap^[n] d ∈ G.oneWayTrip i := by
  obtain ⟨p, hp, hpn⟩ := hG.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip (x := d) hleg
    (Nat.zero_le n) (by simpa only [Function.iterate_zero, id_eq] using hd)
  refine PlabicData.mem_oneWayTrip.2 ⟨p + n, hpn, ?_⟩
  rw [add_comm, Function.iterate_add_apply, hp]

variable {b : ℕ} {s : List (ℤ × ℤ)}

/-- A dart that is not some `dn_{y,0}` is not a leg of the bridge graph. -/
private theorem not_isLeg_bridgeGraph (γ : Fin b → Shade) {d : BridgeDart b s}
    (h : ∀ y, d.1 ≠ .dn y 0) : ¬(bridgeGraph b s γ).IsLeg d := by
  rintro ⟨y, rfl⟩
  exact h y rfl

/-! ### The crossings -/

/-- The vertex of a dart `dn_{x,t}`, `t ≠ 0`, at the left end of the `t`-th bridge is a crossing
`{up_{x,t}, dn_{x,t}, c_t}`. -/
private theorem exists_eq_of_vertexOf_dn_bridgeGraph (γ : Fin b → Shade) {x : Fin b} {t : ℕ}
    (hd : IsDart s (.dn x t)) (ht0 : t ≠ 0) (hx : (x : ℤ) + 1 = (pair s t).1) :
    ∃ (t' : ℕ) (x' : Fin b), (1 ≤ t' ∧ t' ≤ s.length) ∧ (x' : ℤ) + 1 = (pair s t').1 ∧
      t' ≠ top s x' ∧
      ((bridgeGraph b s γ).vertexOf ⟨.dn x t, hd⟩).image Subtype.val =
        {.up x' t', .dn x' t', .bridge t'} ∧
      ((bridgeGraph b s γ).vertexOf ⟨.dn x t, hd⟩).card = 3 := by
  have hd' : t ∈ heights s x ∧ t < top s x := hd.resolve_left ht0
  have hbr : IsDart (b := b) s (.bridge t) :=
    ⟨pos_of_mem_heights hd'.1, le_length_of_mem_heights hd'.1⟩
  have hr1 : (bridgeGraph b s γ).rot ⟨.dn x t, hd⟩ = ⟨.bridge t, hbr⟩ :=
    Subtype.ext (by rw [bridgeGraph.rot_val, rotate_dn_of_ne_zero ht0, if_pos hx])
  have hr2 : (bridgeGraph b s γ).rot ⟨.bridge t, hbr⟩ = ⟨.up x t, hd'.1⟩ :=
    Subtype.ext (by rw [bridgeGraph.rot_val, rotate_bridge_of_eq hx])
  have hr3 : (bridgeGraph b s γ).rot ⟨.up x t, hd'.1⟩ = ⟨.dn x t, hd⟩ :=
    Subtype.ext (by rw [bridgeGraph.rot_val, rotate_up, if_pos hx, if_pos hd'.2])
  have hV := vertexOf_eq_of_rot_rot_rot' (bridgeGraph b s γ).toRotationSystem
    (d := ⟨.dn x t, hd⟩) (by rw [hr1, hr2, hr3])
  refine ⟨t, x, hbr, hx, hd'.2.ne, ?_, ?_⟩
  · rw [hV, hr1, hr2]
    ext e
    simp only [image_insert, image_singleton, mem_insert, mem_singleton]
    tauto
  · rw [hV, hr1, hr2, card_eq_three]
    exact ⟨_, _, _, by simp, by simp, by simp, rfl⟩

/-- A white vertex of the bridge graph containing a dart `up_{x,u}` and at least three darts is a
crossing `{up_{x',t'}, dn_{x',t'}, c_{t'}}`. -/
private theorem exists_eq_of_vertexOf_up_bridgeGraph (γ : Fin b → Shade) {x : Fin b} {u : ℕ}
    (hd : IsDart s (.up x u))
    (hc : ∀ e ∈ (bridgeGraph b s γ).vertexOf ⟨.up x u, hd⟩,
      (bridgeGraph b s γ).colour e = .white)
    (h3 : 3 ≤ ((bridgeGraph b s γ).vertexOf ⟨.up x u, hd⟩).card) :
    ∃ (t' : ℕ) (x' : Fin b), (1 ≤ t' ∧ t' ≤ s.length) ∧ (x' : ℤ) + 1 = (pair s t').1 ∧
      t' ≠ top s x' ∧
      ((bridgeGraph b s γ).vertexOf ⟨.up x u, hd⟩).image Subtype.val =
        {.up x' t', .dn x' t', .bridge t'} ∧
      ((bridgeGraph b s γ).vertexOf ⟨.up x u, hd⟩).card = 3 := by
  have hself := (bridgeGraph b s γ).self_mem_vertexOf ⟨.up x u, hd⟩
  by_cases hx : (x : ℤ) + 1 = (pair s u).1
  · by_cases hut : u < top s x
    · have hdn : IsDart s (.dn x u) := Or.inr ⟨hd, hut⟩
      have hr : (bridgeGraph b s γ).rot ⟨.up x u, hd⟩ = ⟨.dn x u, hdn⟩ :=
        Subtype.ext (by rw [bridgeGraph.rot_val, rotate_up, if_pos hx, if_pos hut])
      rw [← (bridgeGraph b s γ).vertexOf_rot ⟨.up x u, hd⟩, hr]
      exact exists_eq_of_vertexOf_dn_bridgeGraph γ hdn (pos_of_mem_heights hd).ne' hx
    · have hbr : IsDart (b := b) s (.bridge u) :=
        ⟨pos_of_mem_heights hd, le_length_of_mem_heights hd⟩
      have hr1 : (bridgeGraph b s γ).rot ⟨.up x u, hd⟩ = ⟨.bridge u, hbr⟩ :=
        Subtype.ext (by rw [bridgeGraph.rot_val, rotate_up, if_pos hx, if_neg hut])
      have hr2 : (bridgeGraph b s γ).rot ⟨.bridge u, hbr⟩ = ⟨.up x u, hd⟩ :=
        Subtype.ext (by rw [bridgeGraph.rot_val, rotate_bridge_of_eq hx])
      have : ((bridgeGraph b s γ).vertexOf ⟨.up x u, hd⟩).card ≤ 2 :=
        card_vertexOf_le_of_pow_apply_eq (bridgeGraph b s γ).toRotationSystem (n := 2) two_pos
          (by rw [pow_two, Equiv.Perm.mul_apply, hr1, hr2])
      omega
  · have hc' := hc _ hself
    simp [colour_up, hx] at hc'

/-- Every crossing of `G(s, γ)` is the set `{up_{i_t,t}, dn_{i_t,t}, c_t}` of three distinct darts
for some `t ∈ [1, r]` with `t ≠ m_{i_t}`; here `x` is the label with `x + 1 = i_t`. -/
@[cluster_algebras "lem_bridge_graph_crossings"]
theorem exists_eq_of_isCrossing_bridgeGraph (γ : Fin b → Shade) {w : Finset (BridgeDart b s)}
    (hw : (bridgeGraph b s γ).IsCrossing w) :
    ∃ (t : ℕ) (x : Fin b), (1 ≤ t ∧ t ≤ s.length) ∧ (x : ℤ) + 1 = (pair s t).1 ∧
      t ≠ top s x ∧ w.image Subtype.val = {.up x t, .dn x t, .bridge t} ∧ w.card = 3 := by
  obtain ⟨hwi, hwc, hw3⟩ := hw
  obtain ⟨hwv, hwb⟩ := (bridgeGraph b s γ).mem_internalVertices.1 hwi
  obtain ⟨d, rfl⟩ := (bridgeGraph b s γ).mem_vertices.1 hwv
  obtain ⟨d, hd⟩ := d
  have hself := (bridgeGraph b s γ).self_mem_vertexOf ⟨d, hd⟩
  cases d with
  | bdry x => exact (hwb ⟨_, hself, bridgeGraph.mem_bdry.2 (isBoundaryArc_bdry x)⟩).elim
  | bdryRev x => exact (hwb ⟨_, hself, bridgeGraph.mem_bdry.2 (isBoundaryArc_bdryRev x)⟩).elim
  | lam x =>
    have : ((bridgeGraph b s γ).vertexOf ⟨.lam x, hd⟩).card ≤ 1 :=
      card_vertexOf_le_of_pow_apply_eq (bridgeGraph b s γ).toRotationSystem one_pos
        (by rw [pow_one]; rfl)
    omega
  | dn x u =>
    rcases eq_or_ne u 0 with rfl | hu0
    · exact (hwb (bridgeGraph.isBoundaryVertex_leg x)).elim
    · by_cases hx : (x : ℤ) + 1 = (pair s u).1
      · exact exists_eq_of_vertexOf_dn_bridgeGraph γ hd hu0 hx
      · have hc' := hwc _ hself
        simp [colour_dn_of_ne_zero γ hu0, hx] at hc'
  | up x u => exact exists_eq_of_vertexOf_up_bridgeGraph γ hd hwc hw3
  | bridge t =>
    rcases hl : leftEnd s b t with _ | x
    · have : ((bridgeGraph b s γ).vertexOf ⟨.bridge t, hd⟩).card ≤ 1 :=
        card_vertexOf_le_of_pow_apply_eq (bridgeGraph b s γ).toRotationSystem one_pos (by
          rw [pow_one]
          exact Subtype.ext (by
            change BridgeSymbol.rotate s (.bridge t) = _
            simp only [rotate, hl]))
      omega
    · have hx := leftEnd_eq_some.1 hl
      have hm : t ∈ heights s x := mem_heights.2 ⟨hd.1, hd.2, Or.inl hx⟩
      have hr : (bridgeGraph b s γ).rot ⟨.bridge t, hd⟩ = ⟨.up x t, hm⟩ :=
        Subtype.ext (by rw [bridgeGraph.rot_val, rotate_bridge_of_eq hx])
      rw [← (bridgeGraph b s γ).vertexOf_rot ⟨.bridge t, hd⟩, hr] at hwc hw3 ⊢
      exact exists_eq_of_vertexOf_up_bridgeGraph γ hm hwc hw3
  | bridgeRev t =>
    have hc' := hwc _ hself
    simp at hc'

/-! ### Keys along trips -/

/-- The keys of the darts of the bridge graph lie in `[0, 4r + 4]`. -/
private theorem BridgeDart.key_bounds (d : BridgeDart b s) :
    0 ≤ d.key ∧ d.key ≤ 4 * s.length + 4 := by
  obtain ⟨d, hd⟩ := d
  simp only [BridgeDart.key]
  cases d with
  | dn x u =>
    have hd' : u = 0 ∨ (u ∈ heights s x ∧ u < top s x) := hd
    have : u ≤ s.length := by
      rcases hd' with rfl | ⟨h, -⟩
      · omega
      · exact le_length_of_mem_heights h
    simp only [BridgeSymbol.key]
    omega
  | up x u =>
    have := le_length_of_mem_heights (s := s) hd
    have := pos_of_mem_heights (s := s) hd
    simp only [BridgeSymbol.key]
    omega
  | bridge t | bridgeRev t =>
    have := hd.2
    simp only [BridgeSymbol.key]
    omega
  | lam x | bdry x | bdryRev x =>
    simp only [BridgeSymbol.key]
    omega

/-- In the bridge graph the trip map sends a dart outside `B` to a dart outside `B`. -/
private theorem tripMap_notMem_bdry_bridgeGraph (γ : Fin b → Shade) {z : BridgeDart b s}
    (hz : z ∉ (bridgeGraph b s γ).bdry) :
    (bridgeGraph b s γ).tripMap z ∉ (bridgeGraph b s γ).bdry := by
  have hiz : (bridgeGraph b s γ).inv z ∉ (bridgeGraph b s γ).bdry := by
    rw [bridgeGraph.mem_bdry] at hz ⊢
    change ¬(z.1.reverse s).IsBoundaryArc
    obtain ⟨d, hd⟩ := z
    cases d with
    | bdry x => exact (hz (isBoundaryArc_bdry x)).elim
    | bdryRev x => exact (hz (isBoundaryArc_bdryRev x)).elim
    | dn x u =>
      change ¬(BridgeSymbol.reverse s (.dn x u)).IsBoundaryArc
      rw [reverse_dn]
      split_ifs <;> simp
    | _ => simp
  rw [PlabicData.tripMap_apply]
  by_cases hv : (bridgeGraph b s γ).IsBoundaryVertex
      ((bridgeGraph b s γ).vertexOf ((bridgeGraph b s γ).inv z))
  · rw [PlabicData.turn_of_isBoundaryVertex hv]
    exact hiz
  · exact PlabicData.notMem_bdry_of_mem_vertexOf hv (PlabicData.turn_mem_vertexOf _)

/-- Let `1 ≤ i_t < j_t ≤ b` for every pair of `s`, let `T` be the trip map of `G(s, γ)`, and let
`z ∉ B` be a dart such that `T(z)` is not a leg. Then `key(T(z)) > key(z)`. -/
@[cluster_algebras "lem_bridge_dart_key_increasing"]
theorem BridgeDart.key_lt_key_tripMap (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {z : BridgeDart b s} (hz : z ∉ (bridgeGraph b s γ).bdry)
    (hT : ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap z)) :
    z.key < ((bridgeGraph b s γ).tripMap z).key := by
  obtain ⟨d, hd⟩ := z
  simp only [BridgeDart.key]
  cases d with
  | bdry x => exact (hz (bridgeGraph.mem_bdry.2 (isBoundaryArc_bdry x))).elim
  | bdryRev x => exact (hz (bridgeGraph.mem_bdry.2 (isBoundaryArc_bdryRev x))).elim
  | lam x =>
    exact (hT ⟨x, Subtype.ext ((bridgeGraph.leg_val x).trans
      (tripMap_bridgeGraph_lollipop γ hd).2.symm)⟩).elim
  | dn x u =>
    by_cases hut : u < top s x
    · have hm := next_mem hut
      have hlt := lt_next hut
      obtain ⟨h1, h2⟩ := tripMap_bridgeGraph_dn hs γ hut rfl hd
      rcases (mem_heights.1 hm).2.2 with hl | hr <;> [rw [h1 hl]; rw [h2 hr]] <;>
        simp only [BridgeSymbol.key] <;> omega
    · have hd' : u = 0 ∨ (u ∈ heights s x ∧ u < top s x) := hd
      obtain rfl : u = 0 := hd'.resolve_right fun h => hut h.2
      have hx : heights s x = ∅ := top_eq_zero_iff.1 (by omega)
      rw [(tripMap_bridgeGraph_lollipop (s := s) γ hx).1]
      simp only [BridgeSymbol.key]
      omega
  | up x u' =>
    have hv := prev_eq_zero_or_mem (s := s) x u'
    obtain ⟨d1, d2⟩ := tripMap_bridgeGraph_up γ hv (prev_lt_top hd) (next_prev hd) hd
    rcases eq_or_ne (prev s x u') 0 with h0 | h0
    · exact (hT ⟨x, Subtype.ext ((bridgeGraph.leg_val x).trans (d2 h0).symm)⟩).elim
    · rw [d1 h0]
      have := prev_lt (s := s) (x := x) (pos_of_mem_heights hd)
      simp only [BridgeSymbol.key]
      omega
  | bridge t =>
    obtain ⟨-, xr, -, hxr, -, -, -⟩ := exists_ends hs hd.1 hd.2
    obtain ⟨b1, b2⟩ := tripMap_bridgeGraph_bridge hs γ hd hxr
    have := hd.2
    rcases eq_or_ne t (top s xr) with h | h <;> [rw [b2 h]; rw [b1 h]] <;>
      simp only [BridgeSymbol.key] <;> omega
  | bridgeRev t =>
    obtain ⟨xl, -, hxl, -, -, -, -⟩ := exists_ends hs hd.1 hd.2
    obtain ⟨b1, b2⟩ := tripMap_bridgeGraph_bridgeRev γ hd hxl
    have := hd.2
    rcases eq_or_ne t (top s xl) with h | h <;> [rw [b2 h]; rw [b1 h]] <;>
      simp only [BridgeSymbol.key] <;> omega

/-- Along a stretch of a trip of the bridge graph that meets no leg, the key grows by at least one
at each step, and the darts stay outside `B`. -/
private theorem key_add_le_key_iterate (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {d : BridgeDart b s} (hd : d ∉ (bridgeGraph b s γ).bdry) {n : ℕ}
    (h : ∀ k, 0 < k → k ≤ n → ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[k] d)) :
    d.key + n ≤ ((bridgeGraph b s γ).tripMap^[n] d).key ∧
      (bridgeGraph b s γ).tripMap^[n] d ∉ (bridgeGraph b s γ).bdry := by
  induction n with
  | zero => exact ⟨by simp, hd⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k h0 hk => h k h0 (by omega)
    have hT : ¬(bridgeGraph b s γ).IsLeg
        ((bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).tripMap^[n] d)) := by
      rw [← Function.iterate_succ_apply' (bridgeGraph b s γ).tripMap n d]
      exact h (n + 1) (by omega) le_rfl
    have := BridgeDart.key_lt_key_tripMap hs γ ih2 hT
    rw [Function.iterate_succ_apply']
    exact ⟨by push_cast; omega, tripMap_notMem_bdry_bridgeGraph γ ih2⟩

/-- Every trip of the bridge graph through a dart outside `B` reaches a leg. -/
private theorem exists_isLeg_iterate_bridgeGraph (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {d : BridgeDart b s} (hd : d ∉ (bridgeGraph b s γ).bdry) :
    ∃ n, 0 < n ∧ (bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[n] d) := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have h := (key_add_le_key_iterate hs γ hd (n := 4 * s.length + 5)
    fun k hk _ => hcon k hk).1
  have h1 := (BridgeDart.key_bounds d).1
  have h2 := (BridgeDart.key_bounds ((bridgeGraph b s γ).tripMap^[4 * s.length + 5] d)).2
  push_cast at h
  omega

/-- If `1 ≤ i_t < j_t ≤ b` for every pair of `s`, then `G(s, γ)` has no roundtrip. -/
@[cluster_algebras "lem_bridge_graph_no_roundtrip"]
theorem not_hasRoundtrip_bridgeGraph (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) : ¬(bridgeGraph b s γ).HasRoundtrip := by
  rw [PlabicData.hasRoundtrip_iff]
  rintro ⟨d, hd, h⟩
  obtain ⟨n, -, hn⟩ := exists_isLeg_iterate_bridgeGraph hs γ hd
  exact h n hn

/-! ### Trips are wires -/

/-- Two steps of a trip running down the line of `y` from the vertex at height `u`: it crosses
the bridge of height `t = nx_y(u)` to the other end `z` of the `t`-th pair, and then continues
downwards from height `t` on the line of `z`, or turns up if `t = m_z`. -/
private theorem tripMap_tripMap_dn' (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {y : Fin b} {u : ℕ} (hut : u < top s y) (hd : IsDart s (.dn y u)) :
    ∃ z : Fin b, (z : ℤ) + 1 = Equiv.swap (pair s (next s y u)).1 (pair s (next s y u)).2
        ((y : ℤ) + 1) ∧ next s y u ∈ heights s z ∧
      (∀ w, ((bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩).1 ≠ .dn w 0) ∧
      ((bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩)).1 =
        if next s y u < top s z then .dn z (next s y u) else .up z (next s y u) := by
  have hm := next_mem hut
  have h1 := pos_of_mem_heights hm
  have h2 := le_length_of_mem_heights hm
  obtain ⟨xl, xr, hxl, hxr, -, hml, hmr⟩ := exists_ends hs h1 h2
  obtain ⟨ha1, ha2⟩ := tripMap_bridgeGraph_dn hs γ hut rfl hd
  rcases (mem_heights.1 hm).2.2 with hl | hr
  · have e1 : (bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩ = ⟨.bridge (next s y u), h1, h2⟩ :=
      Subtype.ext (ha1 hl)
    refine ⟨xr, by rw [← hl, Equiv.swap_apply_left, hxr], hmr, by simp [e1], ?_⟩
    rw [e1]
    obtain ⟨hb1, hb2⟩ := tripMap_bridgeGraph_bridge hs γ ⟨h1, h2⟩ hxr
    split_ifs with htop
    · exact hb1 htop.ne
    · exact hb2 (le_antisymm (le_top hmr) (not_lt.1 htop))
  · have e1 : (bridgeGraph b s γ).tripMap ⟨.dn y u, hd⟩ = ⟨.bridgeRev (next s y u), h1, h2⟩ :=
      Subtype.ext (ha2 hr)
    refine ⟨xl, by rw [← hr, Equiv.swap_apply_right, hxl], hml, by simp [e1], ?_⟩
    rw [e1]
    obtain ⟨hb1, hb2⟩ := tripMap_bridgeGraph_bridgeRev γ ⟨h1, h2⟩ hxl
    split_ifs with htop
    · exact hb1 htop.ne
    · exact hb2 (le_antisymm (le_top hml) (not_lt.1 htop))

/-- `ρ_{τ+1}⁻¹ = ρ_τ⁻¹ ∘ τ_{τ+1}`. -/
private theorem positionMap_succ_symm_apply {τ : ℕ} (hτ : τ < s.length) (v : ℤ) :
    (positionMap s (τ + 1)).symm v =
      (positionMap s τ).symm (Equiv.swap (pair s (τ + 1)).1 (pair s (τ + 1)).2 v) := by
  rw [Equiv.symm_apply_eq, positionMap_succ hτ, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
    pair_succ hτ, Equiv.swap_apply_self]

/-- Two steps of a trip of the bridge graph that meet no leg stay on the same one-way trip. -/
private theorem tripMap_tripMap_mem_oneWayTrip_bridgeGraph (γ : Fin b → Shade)
    (hG : (bridgeGraph b s γ).IsPlabicGraph) {i : Fin b} {d e : BridgeDart b s}
    (hd : d ∈ (bridgeGraph b s γ).oneWayTrip i)
    (h1 : ∀ w, ((bridgeGraph b s γ).tripMap d).1 ≠ .dn w 0) (h2 : ∀ w, e.1 ≠ .dn w 0)
    (he : (bridgeGraph b s γ).tripMap ((bridgeGraph b s γ).tripMap d) = e) :
    e ∈ (bridgeGraph b s γ).oneWayTrip i := by
  have := iterate_mem_oneWayTrip_of_not_isLeg (n := 2) hG hd fun l hl hl2 => by
    interval_cases l
    · rw [Function.iterate_one]
      exact not_isLeg_bridgeGraph γ h1
    · rw [Function.iterate_succ_apply', Function.iterate_one, he]
      exact not_isLeg_bridgeGraph γ h2
  rwa [Function.iterate_succ_apply', Function.iterate_one, he] at this

/-- Let `b ≥ 1`, let `s` be a nested sequence of `r` pairs with `1 ≤ i_t < j_t ≤ b`,
`γ : [1, b] → Shade`, `y` a line position, `τ ∈ [0, m_y - 1]`, and `u ∈ {0} ∪ P_y` with `u ≤ τ`
such that no element of `P_y` lies in `[u + 1, τ]`. Then `dn_{y,u}` is a dart of `G(s, γ)` lying
on the one-way trip from `ρ_τ⁻¹(y)`; in `0`-indexed labels, from the label `x` with
`x + 1 = ρ_τ⁻¹(y + 1)`. -/
@[cluster_algebras "lem_bridge_trip_down_darts"]
theorem dn_mem_oneWayTrip_bridgeGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) {y : Fin b} {τ u : ℕ}
    (hτ : τ < top s y) (hu : u = 0 ∨ u ∈ heights s y) (huτ : u ≤ τ)
    (hgap : ∀ v ∈ heights s y, v ∉ Icc (u + 1) τ) {x : Fin b}
    (hx : (x : ℤ) + 1 = (positionMap s τ).symm ((y : ℤ) + 1)) :
    ∃ h : IsDart s (.dn y u),
      (⟨.dn y u, h⟩ : BridgeDart b s) ∈ (bridgeGraph b s γ).oneWayTrip x := by
  have hG := isPlabicGraph_bridgeGraph hb hs hn γ
  induction τ generalizing y u x with
  | zero =>
    obtain rfl : u = 0 := by omega
    obtain rfl : x = y := by
      rw [positionMap_zero] at hx
      change (x : ℤ) + 1 = (y : ℤ) + 1 at hx
      exact Fin.ext (by omega)
    exact ⟨Or.inl rfl, PlabicData.mem_oneWayTrip.2 ⟨0, hG.tripLength_pos x, rfl⟩⟩
  | succ τ ih =>
    have hlt : τ < s.length := (Nat.lt_succ_self τ).trans (hτ.trans_le (top_le_length y))
    by_cases hmem : τ + 1 ∈ heights s y
    · obtain rfl : u = τ + 1 := by
        by_contra hne
        exact hgap _ hmem (mem_Icc.2 ⟨by omega, le_rfl⟩)
      obtain ⟨xl, xr, hxl, hxr, -, hml, hmr⟩ := exists_ends hs (t := τ + 1) (by omega) (by omega)
      obtain ⟨y', hy'sw, hy'm⟩ : ∃ y' : Fin b, (y' : ℤ) + 1 =
          Equiv.swap (pair s (τ + 1)).1 (pair s (τ + 1)).2 ((y : ℤ) + 1) ∧
            τ + 1 ∈ heights s y' := by
        by_cases hl : (y : ℤ) + 1 = (pair s (τ + 1)).1
        · exact ⟨xr, by rw [hl, Equiv.swap_apply_left, hxr], hmr⟩
        · exact ⟨xl, by rw [eq_snd_of_mem_heights hmem hl, Equiv.swap_apply_right, hxl], hml⟩
      have hp0 := prev_eq_zero_or_mem (s := s) y' (τ + 1)
      have hpl : prev s y' (τ + 1) < τ + 1 := prev_lt (by omega)
      have hτ' : τ < top s y' := Nat.lt_of_succ_le (le_top hy'm)
      obtain ⟨hd', hmem'⟩ := ih (y := y') (u := prev s y' (τ + 1)) (x := x) hτ' hp0 (by omega)
        (fun v hv hvI => by
          rw [mem_Icc] at hvI
          have := le_prev hv (show v < τ + 1 by omega)
          omega)
        (by rw [hx, positionMap_succ_symm_apply hlt, hy'sw])
      obtain ⟨z, hz, -, hnl, hT2⟩ := tripMap_tripMap_dn' hs γ (by omega) hd'
      rw [next_prev hy'm] at hz hT2
      have hzy : z = y := by
        rw [hy'sw, Equiv.swap_apply_self] at hz
        exact Fin.ext (by omega)
      rw [hzy, if_pos hτ] at hT2
      exact ⟨Or.inr ⟨hmem, hτ⟩,
        tripMap_tripMap_mem_oneWayTrip_bridgeGraph γ hG hmem' hnl (by simp) (Subtype.ext hT2)⟩
    · obtain ⟨e1, e2⟩ := ne_of_notMem_heights hmem (by omega) (by omega)
      have hu' : u ≤ τ := by
        rcases hu with rfl | h
        · omega
        · exact Nat.le_of_lt_succ (huτ.lt_of_ne fun he => hmem (he ▸ h))
      exact ih (by omega) hu hu' (fun v hv hvI => hgap v hv (by
          rw [mem_Icc] at hvI ⊢
          omega))
        (by rw [hx, positionMap_succ_symm_apply hlt, Equiv.swap_apply_of_ne_of_ne e1 e2])

/-- Let `b ≥ 1`, let `s` be a nested sequence of `r` pairs with `1 ≤ i_t < j_t ≤ b`,
`γ : [1, b] → Shade` and `t ∈ [1, r]`. Then `c̄_t` is a dart of the one-way trip from
`ρ_{t-1}⁻¹(j_t)` in `G(s, γ)`; in `0`-indexed labels, with `y + 1 = j_t`, from the label `x` with
`x + 1 = ρ_{t-1}⁻¹(y + 1)`. -/
@[cluster_algebras "lem_bridge_trip_bridge_dart"]
theorem bridgeRev_mem_oneWayTrip_bridgeGraph (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    (γ : Fin b → Shade) {t : ℕ} (ht : 1 ≤ t ∧ t ≤ s.length) {y : Fin b}
    (hy : (y : ℤ) + 1 = (pair s t).2) {x : Fin b}
    (hx : (x : ℤ) + 1 = (positionMap s (t - 1)).symm ((y : ℤ) + 1)) :
    (⟨.bridgeRev t, ht⟩ : BridgeDart b s) ∈ (bridgeGraph b s γ).oneWayTrip x := by
  have hty : t ∈ heights s y := mem_heights.2 ⟨ht.1, ht.2, Or.inr hy⟩
  have hpl : prev s y t < t := prev_lt (by omega)
  have htop := le_top hty
  obtain ⟨hd, hmem⟩ := dn_mem_oneWayTrip_bridgeGraph hb hs hn γ (τ := t - 1) (u := prev s y t)
    (by omega) (prev_eq_zero_or_mem (s := s) y t) (by omega) (fun v hv hvI => by
      rw [mem_Icc] at hvI
      have := le_prev hv (show v < t by omega)
      omega) hx
  have e : (bridgeGraph b s γ).tripMap ⟨.dn y (prev s y t), hd⟩ = ⟨.bridgeRev t, ht⟩ :=
    Subtype.ext ((tripMap_bridgeGraph_dn hs γ (prev_lt_top hty) (next_prev hty) hd).2 hy)
  have := iterate_mem_oneWayTrip_of_not_isLeg (n := 1)
    (isPlabicGraph_bridgeGraph hb hs hn γ) hmem fun l hl hl1 => by
    obtain rfl : l = 1 := by omega
    rw [Function.iterate_one, e]
    exact not_isLeg_bridgeGraph γ (by simp)
  rwa [Function.iterate_one, e] at this

/-- Let `b ≥ 1`, let `s` be a nested sequence of pairs with `1 ≤ i_t < j_t ≤ b`,
`γ : [1, b] → Shade`, `z` a line position, `u ∈ P_z`, and `x` a label with `π_{G(s, γ)}(x) = z`.
Then `up_{z,u}` is a dart of the one-way trip from `x`. -/
@[cluster_algebras "lem_bridge_trip_up_darts"]
theorem up_mem_oneWayTrip_bridgeGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) {z : Fin b} {u : ℕ}
    (hu : u ∈ heights s z) {x : Fin b} (hx : (bridgeGraph b s γ).tripPerm x = z) :
    (⟨.up z u, hu⟩ : BridgeDart b s) ∈ (bridgeGraph b s γ).oneWayTrip x := by
  have hG := isPlabicGraph_bridgeGraph hb hs hn γ
  have desc : ∀ u (hu : u ∈ heights s z), ∃ k, 0 < k ∧
      (bridgeGraph b s γ).tripMap^[k] ⟨.up z u, hu⟩ = (bridgeGraph b s γ).leg z ∧
      ∀ l, 0 < l → l < k →
        ¬(bridgeGraph b s γ).IsLeg ((bridgeGraph b s γ).tripMap^[l] ⟨.up z u, hu⟩) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      have hv := prev_eq_zero_or_mem (s := s) z u
      obtain ⟨d1, d2⟩ := tripMap_bridgeGraph_up γ hv (prev_lt_top hu) (next_prev hu) hu
      rcases eq_or_ne (prev s z u) 0 with h0 | h0
      · exact ⟨1, one_pos, Subtype.ext (d2 h0), fun l h1 h2 => by omega⟩
      · have hm := hv.resolve_left h0
        have e : (bridgeGraph b s γ).tripMap ⟨.up z u, hu⟩ = ⟨.up z (prev s z u), hm⟩ :=
          Subtype.ext (d1 h0)
        obtain ⟨k, hk, hkl, hkn⟩ := ih _ (prev_lt (pos_of_mem_heights hu)) hm
        refine ⟨k + 1, by omega, by rw [Function.iterate_succ_apply, e, hkl], fun l h1 h2 => ?_⟩
        obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        rw [Function.iterate_succ_apply, e]
        rcases Nat.eq_zero_or_pos l with rfl | hl
        · exact not_isLeg_bridgeGraph γ (by simp)
        · exact hkn l hl (by omega)
  obtain ⟨k, hk, hkl, hkn⟩ := desc u hu
  obtain ⟨x', hx', -⟩ := hG.existsUnique_mem_oneWayTrip
    (d := ⟨.up z u, hu⟩) ⟨z, k, hkl⟩
  obtain ⟨p, hp, hpk⟩ := hG.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip (n := k - 1) (j := 0)
    (x := ⟨.up z u, hu⟩) (fun l h1 h2 => hkn l h1 (by omega)) (Nat.zero_le _) hx'
  have hend : (bridgeGraph b s γ).tripMap^[p + k] ((bridgeGraph b s γ).leg x') =
      (bridgeGraph b s γ).leg z := by
    rw [add_comm, Function.iterate_add_apply, hp, hkl]
  have hlen : (bridgeGraph b s γ).tripLength x' = p + k :=
    le_antisymm (PlabicData.tripLength_le (by omega) ⟨z, hend.symm⟩) (by omega)
  have hperm : (bridgeGraph b s γ).tripPerm x' = z := by
    rw [hG.tripPerm_eq_iff, hlen, hend]
  have hxx : x' = x := by
    have h1 := tripPerm_bridgeGraph hs γ x
    have h2 := tripPerm_bridgeGraph hs γ x'
    rw [hx] at h1
    rw [hperm] at h2
    have := (positionMap s s.length).injective (h2.symm.trans h1)
    exact Fin.ext (by omega)
  exact hxx ▸ hx'

end ClusterAlgebras
