/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BadFeatures
public import ClusterAlgebras.Plabic.GeneralizedMoves
public import ClusterAlgebras.Plabic.NormalOfTriple
public import ClusterAlgebras.Plabic.ClosedStrands

/-!
# Bad features and badgons

Let `G` be a normal plabic graph with trip map `T`. Its crossings are its white vertices, each with
three darts, so `∅` is its only white datum, and its triple diagram `X(G)` is isomorphic to the
strand diagram `X° = X°(G, ∅)`. A strand path of `X°` between triple points is a stretch
`T(y), …, Tⁿ(y)` of a trip of `G` running from an arrival at a white vertex `w` to an arrival at a
white vertex `w'` and passing no leg, and conversely. Reading badgons of `X°` through this
dictionary gives FWZ's criterion: `G` has a bad feature (a roundtrip, an essential
self-intersection or a bad double crossing) if and only if `X(G)` has a badgon.

* A monogon of `X°` is a trip arriving twice at a white vertex, which in a normal graph gives an
  essential self-intersection. Conversely an essential self-intersection along the edge
  `{a, ā}`, with `a` at the white vertex `w`, gives the two distinct arrivals `ā` and
  `T⁻¹(a) = \overline{σ a}` at `w` on one trip, hence a monogon.
* A parallel digon of `X°` with corners `x_w ≠ x_{w'}` gives two stretches of trips from `w` to
  `w'`. If they lie on one trip, it arrives twice at `w'`; otherwise the two trips cross the same
  edge at `w` and then the same edge at `w'`, a bad double crossing. Conversely a bad double
  crossing along edges with white ends `w₁ ≠ w₂` gives a parallel digon, and if `w₁ = w₂` one of
  its two trips arrives twice at `w₁`.
* A roundtrip of `G` gives a closed strand of `X(G)`, hence a badgon.

## Main results

* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.hasBadFeature_iff_hasBadgon`: a normal plabic
  graph has a bad feature if and only if its triple diagram has a badgon.

## Implementation notes

* The triple diagram `X(G)` is `G.tripleOfNormal hG.isNormalPlabicPregraph`. It is a generalized
  triple diagram of `G`, isomorphic to `X°(G, D)` for some white datum `D`; as `D` vanishes on
  the crossings, `X°(G, D)` is isomorphic to `X°(G, ∅)`, whose badgons are those of `X(G)`.
* "`z` comes after `y` on its trip, passing no leg" is recorded as `z = Tⁿ(y)` with `n ≥ 1` and
  none of `T(y), …, Tⁿ(y)` a leg. For a dart `s` of an edge joining two internal vertices, the
  arrival at the white end of the edge is `s` itself if `s` lies at the black end, and
  `T⁻¹(s) = \overline{σ s}` if `s` lies at the white end.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset StrandSymbol

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Strand diagrams of white data agreeing on the crossings -/

section StrandIso

/-- A bijection intertwining two rotations maps each vertex onto a vertex. -/
private theorem map_vertexOf_of_semiconj {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {R : RotationSystem α} {R' : RotationSystem β} (θ : α ≃ β)
    (h : ∀ x, θ (R.rot x) = R'.rot (θ x)) (d : α) :
    (R.vertexOf d).map θ.toEmbedding = R'.vertexOf (θ d) := by
  have hp : ∀ (n : ℕ) (x : α), θ ((R.rot ^ n) x) = (R'.rot ^ n) (θ x) := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rw [h, ih]
  ext y
  rw [mem_map_equiv, RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
  refine ⟨fun hs => ?_, fun hs => ?_⟩ <;> obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  · exact ⟨n, by rw [zpow_natCast, ← hp, hn, Equiv.apply_symm_apply]⟩
  · exact ⟨n, θ.injective (by rw [zpow_natCast, hp, hn, Equiv.apply_symm_apply])⟩

variable (hG : G.IsPlabicGraph) {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)
  {H' : Type*} [Fintype H'] [DecidableEq H']

/-- An isomorphism out of a strand diagram: a bijection of darts commuting with the involutions
and the rotations, matching the boundaries, the orientations and the darts of the endpoints. -/
private theorem strandDiagram_isomorphic_of (Y : TripleData H' b) (θ : G.StrandDart D ≃ H')
    (hinv : ∀ a, θ ((G.strandDiagram hG hD).inv a) = Y.inv (θ a))
    (hrot : ∀ a, θ ((G.strandDiagram hG hD).rot a) = Y.rot (θ a))
    (hbdry : ∀ a, θ a ∈ Y.bdry ↔ a.1.IsBoundary)
    (hout : ∀ a, ¬a.1.IsBoundary → Y.isOut (θ a) = a.1.isOut)
    (hend : ∀ r, θ ((G.strandDiagram hG hD).endDart r) = Y.endDart r) :
    (G.strandDiagram hG hD).Isomorphic Y :=
  ⟨{ toEquiv := θ
     map_inv := hinv
     map_rot := hrot
     mem_bdry_iff := fun a => by rw [hbdry, mem_strandDiagram_bdry]
     map_isOut := fun a ha => by
       rw [hout a ((mem_strandDiagram_bdry hG hD).not.1 ha), strandDiagram_isOut]
     map_endpoint := fun r => by
       rw [TripleData.endpoint, TripleData.endpoint, map_vertexOf_of_semiconj θ hrot, hend] }⟩

omit [Fintype H'] [DecidableEq H'] in
/-- To check that a map out of a strand diagram commutes with the involutions, it suffices to
check it on the symbols `x⁺_d`, `y⁺_{s,τ}` and `∂_r`. -/
private theorem strandDiagram_map_inv_of {Y : TripleData H' b} (hY : Function.Involutive Y.inv)
    (θ : G.StrandDart D → H')
    (h : ∀ a : G.StrandDart D, ((∃ d, a.1 = xPlus d) ∨ (∃ s τ, a.1 = yPlus s τ) ∨
      ∃ r, a.1 = bd r) → θ ((G.strandDiagram hG hD).inv a) = Y.inv (θ a))
    (a : G.StrandDart D) : θ ((G.strandDiagram hG hD).inv a) = Y.inv (θ a) := by
  set X := G.strandDiagram hG hD
  have hX : Function.Involutive X.inv := (isPreTripleDiagram_strandDiagram hG hD).inv_involutive
  have hrev : ∀ c : G.StrandDart D, ((∃ d, c.1 = xPlus d) ∨ (∃ s τ, c.1 = yPlus s τ) ∨
      ∃ r, c.1 = bd r) → θ (X.inv (X.inv c)) = Y.inv (θ (X.inv c)) := by
    intro c hc
    rw [hX c, h c hc, hY]
  obtain ⟨a, ha⟩ := a
  cases a with
  | xPlus d => exact h _ (Or.inl ⟨d, rfl⟩)
  | yPlus s τ => exact h _ (Or.inr (Or.inl ⟨s, τ, rfl⟩))
  | bd r => exact h _ (Or.inr (Or.inr ⟨r, rfl⟩))
  | xMinus t =>
    rw [← hX ⟨xMinus t, ha⟩]
    exact hrev _ (Or.inl ⟨_, rfl⟩)
  | yMinus s τ =>
    rw [← hX ⟨yMinus s τ, ha⟩]
    exact hrev _ (Or.inr (Or.inl ⟨_, _, rfl⟩))
  | bd' r =>
    rw [← hX ⟨bd' r, ha⟩]
    exact hrev _ (Or.inr (Or.inr ⟨_, rfl⟩))

end StrandIso

/-- White data agreeing at every crossing have isomorphic strand diagrams. -/
private theorem strandDiagram_isomorphic_of_agree (hG : G.IsPlabicGraph)
    {D D' : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) (hD' : G.IsWhiteDatum D')
    (h : ∀ x, G.IsCrossing x → D' x = D x) :
    (G.strandDiagram hG hD').Isomorphic (G.strandDiagram hG hD) := by
  have hT : ∀ τ, G.IsDatumTriangle D' τ ↔ G.IsDatumTriangle D τ := fun τ =>
    ⟨fun ⟨w, hw, ht⟩ => ⟨w, hw, h w hw ▸ ht⟩, fun ⟨w, hw, ht⟩ => ⟨w, hw, (h w hw).symm ▸ ht⟩⟩
  have hS : ∀ e τ, G.IsDatumSegment D' e τ ↔ G.IsDatumSegment D e τ := fun e τ =>
    ⟨fun ⟨w, hw, he, ht, hm⟩ => ⟨w, hw, h w hw ▸ he, h w hw ▸ ht, hm⟩,
      fun ⟨w, hw, he, ht, hm⟩ => ⟨w, hw, (h w hw).symm ▸ he, (h w hw).symm ▸ ht, hm⟩⟩
  have hI : ∀ a, G.IsStrandSymbol D' a ↔ G.IsStrandSymbol D a := by
    intro a
    cases a with
    | yPlus e τ => exact hS e τ
    | yMinus e τ => exact hS e τ
    | _ => exact Iff.rfl
  set θ : G.StrandDart D' ≃ G.StrandDart D := Equiv.subtypeEquivRight hI
  have θval : ∀ a, (θ a).1 = a.1 := fun _ => rfl
  refine strandDiagram_isomorphic_of hG hD' _ θ ?_ ?_ ?_ ?_ ?_
  · refine strandDiagram_map_inv_of hG hD'
      (isPreTripleDiagram_strandDiagram hG hD).inv_involutive _ ?_
    rintro ⟨a, ha⟩ (⟨d, rfl⟩ | ⟨e, τ, rfl⟩ | ⟨r, rfl⟩)
    · rfl
    · apply Subtype.ext
      have ha' : G.IsDatumSegment D e τ := (hS e τ).1 ha
      obtain ⟨o1, o2, -⟩ := hD'.otherTriangle_spec (ha : G.IsDatumSegment D' e τ)
      have ho : G.otherTriangle D' e τ = G.otherTriangle D e τ := by
        obtain ⟨-, -, -, -, hm⟩ := id o1
        exact hD.eq_otherTriangle ha' ((hT _).1 (.of_isDatumSegment o1)) hm o2
      change yMinus e (G.otherTriangle D' e τ) = yMinus e (G.otherTriangle D e τ)
      rw [ho]
    · rfl
  · intro a
    apply Subtype.ext
    rw [θval, strandDiagram_rot_apply, strandDiagram_rot_apply, θval]
    rcases IsStrandSymbol.cases hG hD' a.2 with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ |
      ⟨τ, p, hτ, hp, hr⟩ | ⟨τ, p, hτ, hp, hr⟩ <;> rw [hr]
    · rfl
    · rfl
    · rw [strandRotSym_endSymbol hG, strandRotSym_endSymbol hG]
    · rw [strandRotSym_pairOut hG hτ hp, strandRotSym_pairOut hG ((hT τ).1 hτ) hp]
    · rw [strandRotSym_pairIn hG hD' hτ hp, strandRotSym_pairIn hG hD ((hT τ).1 hτ) hp]
  · intro a
    rw [mem_strandDiagram_bdry, θval]
  · intro a _
    rw [strandDiagram_isOut, θval]
  · intro r
    rfl

/-! ### Trips -/

section Trips

variable (hG : G.IsPlabicGraph)

include hG

/-- In a plabic graph, a dart lies on at most one trip. -/
private theorem Trip.eq_of_mem_darts {τ τ' : G.Trip} {d : H} (h : d ∈ τ.darts)
    (h' : d ∈ τ'.darts) : τ = τ' := by
  have key : ∀ (i : Fin b) (O : Set H), G.IsRoundtrip O →
      d ∈ (Trip.oneWay i : G.Trip).darts → d ∉ O := by
    rintro i O ⟨d₀, -, rfl, hl⟩ hi hO
    obtain ⟨k, -, rfl⟩ := Trip.mem_darts_oneWay.1 hi
    apply hl i
    simp only [hG.trip_eq_setOf_sameCycle, Set.mem_setOf_eq] at hO ⊢
    have hk : hG.tripEquiv.SameCycle (G.leg i) (G.tripMap^[k] (G.leg i)) :=
      ⟨k, by rw [zpow_natCast, hG.tripEquiv_pow_apply]⟩
    exact hO.trans hk.symm
  cases τ with
  | oneWay i =>
    cases τ' with
    | oneWay j => rw [hG.eq_of_mem_oneWayTrip h h']
    | round O hO => exact (key i O hO h h').elim
  | round O hO =>
    cases τ' with
    | oneWay j => exact (key j O hO h' h).elim
    | round O' hO' =>
      rw [Trip.darts_round] at h h'
      obtain rfl : O = O' := by
        obtain ⟨d₀, -, rfl, -⟩ := hO
        obtain ⟨d₁, -, rfl, -⟩ := hO'
        simp only [hG.trip_eq_setOf_sameCycle, Set.mem_setOf_eq] at h h' ⊢
        ext e
        exact ⟨fun he => (h.trans h'.symm).symm.trans he, fun he => (h.trans h'.symm).trans he⟩
      rfl

/-- If `T(y)` is a dart of a trip `τ` and not a leg, then `y` is a dart of `τ`. -/
private theorem Trip.mem_darts_of_tripMap {τ : G.Trip} {y : H} (h : G.tripMap y ∈ τ.darts)
    (hT : ¬G.IsLeg (G.tripMap y)) : y ∈ τ.darts := by
  cases τ with
  | oneWay i =>
    obtain ⟨p, hp, hpn⟩ := hG.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip (x := y) (n := 1)
      (j := 1) (fun l hl0 hl1 => by
        obtain rfl : l = 1 := by omega
        exact hT) le_rfl h
    exact Trip.mem_darts_oneWay.2 ⟨p, by omega, hp⟩
  | round O hO =>
    rw [Trip.darts_round] at h ⊢
    obtain ⟨d, -, rfl, -⟩ := hO
    simp only [hG.trip_eq_setOf_sameCycle, Set.mem_setOf_eq] at h ⊢
    exact (Equiv.Perm.sameCycle_apply_right (f := hG.tripEquiv)).1 h

end Trips

/-! ### Stretches of trips passing no leg -/

variable (G) in
/-- `z` **follows** `y` on its trip, passing no leg: `z = Tⁿ(y)` for some `n ≥ 1`, and none of
`T(y), …, Tⁿ(y)` is a leg. -/
private def Follows (y z : H) : Prop :=
  ∃ n, 1 ≤ n ∧ G.tripMap^[n] y = z ∧ ∀ k, 1 ≤ k → k ≤ n → ¬G.IsLeg (G.tripMap^[k] y)

private theorem follows_tripMap {y : H} (h : ¬G.IsLeg (G.tripMap y)) :
    G.Follows y (G.tripMap y) :=
  ⟨1, le_rfl, rfl, fun k hk1 hk2 => by
    obtain rfl : k = 1 := by omega
    exact h⟩

private theorem Follows.trans {x y z : H} (h₁ : G.Follows x y) (h₂ : G.Follows y z) :
    G.Follows x z := by
  obtain ⟨m, hm, rfl, hl⟩ := h₁
  obtain ⟨n, hn, rfl, hl'⟩ := h₂
  refine ⟨n + m, by omega, Function.iterate_add_apply _ _ _ _, fun k hk1 hk2 => ?_⟩
  rcases le_or_gt k m with hkm | hkm
  · exact hl k hk1 hkm
  · have := hl' (k - m) (by omega) (by omega)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hkm.le] at this

private theorem Follows.of_tripMap (hG : G.IsPlabicGraph) {y z : H}
    (h : G.Follows y (G.tripMap z)) (hne : y ≠ z) : G.Follows y z := by
  obtain ⟨n, hn, hyz, hl⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply'] at hyz
  have hmz := (tripMap_bijective hG).injective hyz
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact (hne hmz).elim
  · exact ⟨m, hm, hmz, fun k hk1 hk2 => hl k hk1 (by omega)⟩

/-- If `t` follows `s ∉ B`, then `v(s̄)` is an internal vertex. -/
private theorem Follows.not_isBoundaryVertex_inv (hG : G.IsPlabicGraph) {s t : H}
    (h : G.Follows s t) (hs : s ∉ G.bdry) : ¬G.IsBoundaryVertex (G.vertexOf (G.inv s)) := by
  intro hb
  obtain ⟨n, hn, -, hl⟩ := h
  apply hl 1 le_rfl hn
  rw [Function.iterate_one, tripMap_apply, turn_of_isBoundaryVertex hb]
  exact hG.isLeg_of_isBoundaryVertex (fun h' => hs (hG.inv_mem_bdry_iff.1 h')) hb

/-- If `t ∉ B` follows `s`, then `v(t)` is an internal vertex. -/
private theorem Follows.not_isBoundaryVertex (hG : G.IsPlabicGraph) {s t : H}
    (h : G.Follows s t) (ht : t ∉ G.bdry) : ¬G.IsBoundaryVertex (G.vertexOf t) := by
  intro hb
  obtain ⟨n, hn, rfl, hl⟩ := h
  exact hl n hn le_rfl (hG.isLeg_of_isBoundaryVertex ht hb)

/-- A trip traversing `e₁` and later the disjoint `e₂` has darts `u₁ ∈ e₁` and `u₂ ∈ e₂` with
`u₂` following `u₁`. -/
private theorem Trip.exists_follows (hG : G.IsPlabicGraph) {τ : G.Trip} {e₁ e₂ : Finset H}
    (hd : Disjoint e₁ e₂) (h : τ.TraversesThen e₁ e₂) :
    ∃ u₁ ∈ τ.darts, u₁ ∈ e₁ ∧ ∃ u₂ ∈ τ.darts, u₂ ∈ e₂ ∧ G.Follows u₁ u₂ := by
  cases τ with
  | oneWay i =>
    obtain ⟨p₁, p₂, h12, h2, h₁, h₂⟩ := h
    refine ⟨_, Trip.mem_darts_oneWay.2 ⟨p₁, by omega, rfl⟩, h₁, _,
      Trip.mem_darts_oneWay.2 ⟨p₂, h2, rfl⟩, h₂, p₂ - p₁, by omega, ?_, fun k hk1 hk2 => ?_⟩
    · rw [← Function.iterate_add_apply, Nat.sub_add_cancel h12.le]
    · rw [← Function.iterate_add_apply]
      exact not_isLeg_of_lt_tripLength (by omega) (by omega)
  | round O hO =>
    obtain ⟨⟨u₁, hu₁, he₁⟩, ⟨u₂, hu₂, he₂⟩⟩ := h
    refine ⟨u₁, hu₁, he₁, u₂, hu₂, he₂, ?_⟩
    obtain ⟨d, -, rfl, hl⟩ := hO
    have hsc : hG.tripEquiv.SameCycle u₁ u₂ := by
      simp only [hG.trip_eq_setOf_sameCycle, Set.mem_setOf_eq] at hu₁ hu₂
      exact (Equiv.Perm.SameCycle.symm hu₁).trans hu₂
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    rw [hG.tripEquiv_pow_apply] at hn
    refine ⟨n, ?_, hn, fun k _ _ ⟨j, hj⟩ => ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | h
      · rw [Function.iterate_zero_apply] at hn
        subst hn
        exact (disjoint_left.1 hd he₁ he₂).elim
      · exact h
    · obtain ⟨m, rfl⟩ := hu₁
      exact hl j ⟨k + m, by
        change G.tripMap^[k + m] d = _
        rw [Function.iterate_add_apply, hj]⟩

/-- A stretch `y, …, Tⁿ(y), T^{n+1}(y)` of a trip, `n ≥ 2`, passing no leg after `y`, lies on one
trip `τ`, which traverses an edge containing `y` or `T(y)` and later an edge containing `Tⁿ(y)` or
`T^{n+1}(y)`. -/
private theorem exists_trip_traversesThen (hG : G.IsPlabicGraph) {y : H} (hyB : y ∉ G.bdry)
    {n : ℕ} (hn : 2 ≤ n) (hl : ∀ k, 1 ≤ k → k ≤ n + 1 → ¬G.IsLeg (G.tripMap^[k] y)) :
    ∃ τ : G.Trip, y ∈ τ.darts ∧ G.tripMap^[n] y ∈ τ.darts ∧
      ∀ e₁ e₂ : Finset H, (y ∈ e₁ ∨ G.tripMap y ∈ e₁) →
        (G.tripMap^[n] y ∈ e₂ ∨ G.tripMap (G.tripMap^[n] y) ∈ e₂) → τ.TraversesThen e₁ e₂ := by
  by_cases hleg : ∃ k, G.IsLeg (G.tripMap^[k] y)
  · obtain ⟨k, j, hj⟩ := hleg
    obtain ⟨i, hi, -⟩ := hG.existsUnique_mem_oneWayTrip ⟨j, k, hj.symm⟩
    obtain ⟨p, hp, hpn⟩ := hG.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip
      (fun l hl0 hln => hl l hl0 hln) (Nat.zero_le (n + 1)) hi
    have hit : ∀ q, G.tripMap^[q + p] (G.leg i) = G.tripMap^[q] y := fun q => by
      rw [Function.iterate_add_apply, hp]
    refine ⟨.oneWay i, Trip.mem_darts_oneWay.2 ⟨p, by omega, hp⟩,
      Trip.mem_darts_oneWay.2 ⟨n + p, by omega, hit n⟩, fun e₁ e₂ h₁ h₂ => ?_⟩
    have h₁' : ∃ p₁, p ≤ p₁ ∧ p₁ ≤ p + 1 ∧ G.tripMap^[p₁] (G.leg i) ∈ e₁ := by
      rcases h₁ with h | h
      · exact ⟨p, le_rfl, by omega, by rwa [hp]⟩
      · exact ⟨1 + p, by omega, by omega, by rwa [hit 1, Function.iterate_one]⟩
    have h₂' : ∃ p₂, n + p ≤ p₂ ∧ p₂ ≤ n + 1 + p ∧ G.tripMap^[p₂] (G.leg i) ∈ e₂ := by
      rcases h₂ with h | h
      · exact ⟨n + p, le_rfl, by omega, by rwa [hit n]⟩
      · exact ⟨n + 1 + p, by omega, le_rfl, by rwa [hit (n + 1), Function.iterate_succ_apply']⟩
    obtain ⟨p₁, hp₁, hp₁', hm₁⟩ := h₁'
    obtain ⟨p₂, hp₂, hp₂', hm₂⟩ := h₂'
    change ∃ p₁ p₂, p₁ < p₂ ∧ p₂ < G.tripLength i ∧
      G.tripMap^[p₁] (G.leg i) ∈ e₁ ∧ G.tripMap^[p₂] (G.leg i) ∈ e₂
    exact ⟨p₁, p₂, by omega, by omega, hm₁, hm₂⟩
  · simp only [not_exists] at hleg
    have hO : G.IsRoundtrip (G.trip y) :=
      ⟨y, hyB, rfl, fun j ⟨k, hk⟩ => hleg k ⟨j, hk.symm⟩⟩
    refine ⟨.round _ hO, mem_trip_self y, iterate_mem_trip y n, fun e₁ e₂ h₁ h₂ => ?_⟩
    change (∃ d ∈ G.trip y, d ∈ e₁) ∧ ∃ d ∈ G.trip y, d ∈ e₂
    refine ⟨?_, ?_⟩
    · rcases h₁ with h | h
      · exact ⟨y, mem_trip_self y, h⟩
      · exact ⟨_, iterate_mem_trip y 1, h⟩
    · rcases h₂ with h | h
      · exact ⟨_, iterate_mem_trip y n, h⟩
      · exact ⟨_, iterate_mem_trip y (n + 1), by rwa [Function.iterate_succ_apply']⟩

/-! ### Darts of vertices with three darts -/

/-- Two distinct darts of a vertex with three darts are adjacent in the rotation. -/
private theorem eq_rot_or_eq_rot_of_card_eq_three {a a' : H} (h3 : (G.vertexOf a).card = 3)
    (ha' : a' ∈ G.vertexOf a) (hne : a' ≠ a) : a' = G.rot a ∨ a = G.rot a' := by
  obtain ⟨i, rfl⟩ :=
    (RotationSystem.isCornerLabelling_rot_symm_pow (R := G.toRotationSystem) a h3).exists_eq ha'
  have hc := RotationSystem.rot_symm_pow_card_vertexOf (R := G.toRotationSystem) a
  rw [h3] at hc
  have hk : i.val < 3 := ZMod.val_lt i
  generalize i.val = k at hne hk ⊢
  interval_cases k
  · exact (hne (by simp)).elim
  · right
    simp
  · left
    calc (G.rot.symm ^ 2) a = G.rot ((G.rot.symm ^ 3) a) := by
          simp [pow_succ, Equiv.Perm.mul_apply]
      _ = G.rot a := by rw [hc]

/-- At a vertex with three darts, `σ a ≠ a` and `σ (σ a) ≠ a`. -/
private theorem rot_ne_self_of_card_eq_three {a : H} (h3 : (G.vertexOf a).card = 3) :
    G.rot a ≠ a ∧ G.rot (G.rot a) ≠ a := by
  have hinj :=
    (RotationSystem.isCornerLabelling_rot_symm_pow (R := G.toRotationSystem) a h3).1.injOn
  have h01 : (G.rot.symm ^ (1 : ZMod 3).val) a ≠ (G.rot.symm ^ (0 : ZMod 3).val) a :=
    fun h => absurd (@hinj 1 (Set.mem_univ _) 0 (Set.mem_univ _) h) (by decide)
  have h02 : (G.rot.symm ^ (2 : ZMod 3).val) a ≠ (G.rot.symm ^ (0 : ZMod 3).val) a :=
    fun h => absurd (@hinj 2 (Set.mem_univ _) 0 (Set.mem_univ _) h) (by decide)
  have e0 : (0 : ZMod 3).val = 0 := rfl
  have e1 : (1 : ZMod 3).val = 1 := rfl
  have e2 : (2 : ZMod 3).val = 2 := rfl
  rw [e1, e0, pow_one, pow_zero, Equiv.Perm.one_apply] at h01
  rw [e2, e0, pow_zero, Equiv.Perm.one_apply] at h02
  refine ⟨fun h => h01 ((Equiv.symm_apply_eq _).2 h.symm), fun h => h02 ?_⟩
  rw [pow_two, Equiv.Perm.mul_apply, Equiv.symm_apply_eq, Equiv.symm_apply_eq, h]

/-! ### Edges -/

section Edges

variable (hG : G.IsPlabicGraph)

include hG

/-- The edge of a dart of an edge is that edge. -/
private theorem edgeOf_eq_of_mem {d x : H} (hx : x ∈ G.edgeOf d) : G.edgeOf x = G.edgeOf d := by
  have hi : ∀ z, G.inv (G.inv z) = z := hG.inv_involutive
  ext z
  rcases G.mem_edgeOf.1 hx with rfl | rfl
  · rfl
  · simp only [RotationSystem.mem_edgeOf, hi]
    tauto

/-- Distinct edges are disjoint. -/
private theorem disjoint_edgeOf_of_ne {d₁ d₂ : H} (h : G.edgeOf d₁ ≠ G.edgeOf d₂) :
    Disjoint (G.edgeOf d₁) (G.edgeOf d₂) :=
  disjoint_left.2 fun x h₁ h₂ => h (by rw [← edgeOf_eq_of_mem hG h₁, edgeOf_eq_of_mem hG h₂])

/-- Two distinct darts of an edge are each other's reverse. -/
private theorem eq_inv_of_mem_edgeOf {d x y : H} (hx : x ∈ G.edgeOf d) (hy : y ∈ G.edgeOf d)
    (hne : x ≠ y) : y = G.inv x := by
  rcases G.mem_edgeOf.1 hx with rfl | rfl <;> rcases G.mem_edgeOf.1 hy with rfl | rfl
  · exact (hne rfl).elim
  · rfl
  · exact (hG.inv_involutive _).symm
  · exact (hne rfl).elim

/-- The edge of a dart at a crossing is disjoint from `B`. -/
private theorem disjoint_edgeOf_bdry {w : Finset H} (hw : G.IsCrossing w) {c : H} (hc : c ∈ w) :
    Disjoint (G.edgeOf c) G.bdry := by
  have hv : ¬G.IsBoundaryVertex (G.vertexOf c) := by
    rw [← hw.eq_vertexOf hc]
    exact hw.not_isBoundaryVertex
  have hcB : c ∉ G.bdry := notMem_bdry_of_mem_vertexOf hv (G.self_mem_vertexOf c)
  refine disjoint_left.2 fun x hx hxB => ?_
  rcases G.mem_edgeOf.1 hx with rfl | rfl
  · exact hcB hxB
  · exact hcB (hG.inv_mem_bdry_iff.1 hxB)

end Edges

/-- `T(t) = σ⁻¹(t̄)` when `t̄` lies at a crossing. -/
private theorem tripMap_of_isCrossing {t : H} (hc : G.IsCrossing (G.vertexOf (G.inv t))) :
    G.tripMap t = G.rot.symm (G.inv t) :=
  turn_of_white hc.not_isBoundaryVertex (hc.2.1 _ (G.self_mem_vertexOf _))

/-! ### Badgons of `X°(G, ∅)` and trips -/

section Badgons

variable (hG : G.IsPlabicGraph) (htri : ∀ w, G.IsCrossing w → w.card = 3)

include hG htri

/-- Two distinct darts `y, y'` of a trip arriving at a crossing `w` give a monogon of
`X°(G, ∅)`. -/
private theorem hasMonogon_of_mem_darts {w : Finset H} (hw : G.IsCrossing w) {τ : G.Trip}
    {y y' : H} (hy : y ∈ τ.darts) (hy' : y' ∈ τ.darts) (hne : y ≠ y')
    (hyw : G.vertexOf (G.inv y) = w) (hy'w : G.vertexOf (G.inv y') = w) :
    (G.strandDiagram hG (isWhiteDatum_empty htri)).HasMonogon := by
  obtain ⟨P, hP, -⟩ := (exists_isMonogon_iff hG htri hw).2 ⟨y, y', hne, hyw, hy'w, τ, hy, hy'⟩
  exact ⟨P, hP⟩

/-- Darts `y, y'` arriving at a crossing `w`, and darts `z, z'` following them and arriving at a
crossing `w' ≠ w`, with `y ≠ y'` and `z ≠ z'`, give a parallel digon of `X°(G, ∅)`. -/
private theorem hasParallelDigon_of_follows {y₁ y₂ z₁ z₂ : H} (h₁ : G.Follows y₁ z₁)
    (h₂ : G.Follows y₂ z₂) (hy : y₁ ≠ y₂) (hz : z₁ ≠ z₂) {w w' : Finset H} (hw : G.IsCrossing w)
    (hw' : G.IsCrossing w') (hww' : w ≠ w') (hy₁ : G.vertexOf (G.inv y₁) = w)
    (hy₂ : G.vertexOf (G.inv y₂) = w) (hz₁ : G.vertexOf (G.inv z₁) = w')
    (hz₂ : G.vertexOf (G.inv z₂) = w') :
    (G.strandDiagram hG (isWhiteDatum_empty htri)).HasParallelDigon := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  obtain ⟨n₁, hn₁, rfl, hl₁⟩ := h₁
  obtain ⟨n₂, hn₂, rfl, hl₂⟩ := h₂
  obtain ⟨P, hP, hPh, hPl⟩ :=
    exists_isStrandPath_of_tripMap hG htri hn₁ (hy₁ ▸ hw) (hz₁ ▸ hw') hl₁
  obtain ⟨Q, hQ, hQh, hQl⟩ :=
    exists_isStrandPath_of_tripMap hG htri hn₂ (hy₂ ▸ hw) (hz₂ ▸ hw') hl₂
  obtain ⟨e, P', rfl⟩ := List.exists_cons_of_ne_nil hP.ne_nil
  obtain ⟨f, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ.ne_nil
  have hPm := List.getLast?_eq_some_getLast (l := e :: P') (List.cons_ne_nil _ _)
  have hQm := List.getLast?_eq_some_getLast (l := f :: Q') (List.cons_ne_nil _ _)
  have he : e.1 = xPlus (G.tripMap y₁) := hPh e rfl
  have hf : f.1 = xPlus (G.tripMap y₂) := hQh f rfl
  have hel := hPl _ hPm
  have hfl := hQl _ hQm
  have hT₁ : G.tripMap y₁ ∈ w := hy₁ ▸ turn_mem_vertexOf _
  have hT₂ : G.tripMap y₂ ∈ w := hy₂ ▸ turn_mem_vertexOf _
  have hZ₁ : G.inv (G.tripMap^[n₁] y₁) ∈ w' := hz₁ ▸ G.self_mem_vertexOf _
  have hZ₂ : G.inv (G.tripMap^[n₂] y₂) ∈ w' := hz₂ ▸ G.self_mem_vertexOf _
  refine ⟨e :: P', f :: Q', G.crossingTriplePoint (fun _ => ∅) w,
    G.crossingTriplePoint (fun _ => ∅) w',
    { ne := (bijOn_crossingTriplePoint htri hG).injOn.ne hw hw' hww'
      mem_left := crossingTriplePoint_mem_internalVertices htri hG hw
      mem_right := crossingTriplePoint_mem_internalVertices htri hG hw'
      isStrandPath_fst := hP
      isStrandPath_snd := hQ
      pathStart_fst := strandDiagram_vertexOf_of_eq_xPlus htri hG hw hT₁ he
      pathEnd_fst := by
        rw [X.pathEnd_of_getLast? hPm]
        exact strandDiagram_vertexOf_of_eq_xMinus htri hG hw' hZ₁
          (by rw [hel, hG.inv_involutive])
      pathStart_snd := strandDiagram_vertexOf_of_eq_xPlus htri hG hw hT₂ hf
      pathEnd_snd := by
        rw [X.pathEnd_of_getLast? hQm]
        exact strandDiagram_vertexOf_of_eq_xMinus htri hG hw' hZ₂
          (by rw [hfl, hG.inv_involutive])
      head?_ne := by
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        refine fun hef => hy ((tripMap_bijective hG).injective (xPlus.inj (he.symm.trans ?_)))
        rw [hef, hf]
      getLast?_ne := by
        rw [hPm, hQm]
        refine fun h => hz (xMinus.inj (hel.symm.trans ?_))
        rw [Option.some.inj h, hfl] }⟩

/-- A strand path of `X°(G, ∅)` from `x_w` to `x_{w'}` is a stretch `T(y), …, Tⁿ(y)` of a trip
from an arrival `y` at `w` to an arrival `Tⁿ(y)` at `w'`. -/
private theorem exists_tripMap_of_isStrandPath_crossing
    {P : List (G.StrandDart fun _ => ∅)}
    (hPP : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath P) {w w' : Finset H}
    (hw : G.IsCrossing w) (hw' : G.IsCrossing w')
    (hs : (G.strandDiagram hG (isWhiteDatum_empty htri)).pathStart P =
      G.crossingTriplePoint (fun _ => ∅) w)
    (he : (G.strandDiagram hG (isWhiteDatum_empty htri)).pathEnd P =
      G.crossingTriplePoint (fun _ => ∅) w') :
    ∃ y ∉ G.bdry, ∃ n, 1 ≤ n ∧ G.vertexOf (G.inv y) = w ∧
      G.vertexOf (G.inv (G.tripMap^[n] y)) = w' ∧
      (∀ k, 1 ≤ k → k ≤ n → ¬G.IsLeg (G.tripMap^[k] y)) ∧
      (∀ e₁ ∈ P.head?, e₁.1 = xPlus (G.tripMap y)) ∧
      ∀ eₘ ∈ P.getLast?,
        ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv eₘ).1 =
          xMinus (G.tripMap^[n] y) := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  obtain ⟨y, hyB, n, hn, -, -, hleg, hhead, hlast⟩ := exists_tripMap_of_isStrandPath hG htri hPP
    (hs ▸ crossingTriplePoint_mem_internalVertices htri hG hw)
    (he ▸ crossingTriplePoint_mem_internalVertices htri hG hw')
  obtain ⟨e₁, P', rfl⟩ := List.exists_cons_of_ne_nil hPP.ne_nil
  have hm := List.getLast?_eq_some_getLast (l := e₁ :: P') (List.cons_ne_nil _ _)
  have h1 : e₁.1 = xPlus (G.tripMap y) := hhead e₁ rfl
  have hTyw : G.tripMap y ∈ w := by
    have : e₁ ∈ X.pathStart (e₁ :: P') := X.self_mem_vertexOf e₁
    rw [hs] at this
    exact (mem_crossingTriplePoint_of_eq_xPlus h1).1 this
  have hyw : G.vertexOf (G.inv y) = w :=
    (vertexOf_turn (G.inv y)).symm.trans (hw.eq_vertexOf hTyw).symm
  have hy'w : G.inv (G.tripMap^[n] y) ∈ w' := by
    have : X.inv ((e₁ :: P').getLast (List.cons_ne_nil _ _)) ∈ X.pathEnd (e₁ :: P') := by
      rw [X.pathEnd_of_getLast? hm]
      exact X.self_mem_vertexOf _
    rw [he] at this
    exact (mem_crossingTriplePoint_of_eq_xMinus hG (hlast _ hm)).1 this
  exact ⟨y, hyB, n, hn, hyw, (hw'.eq_vertexOf hy'w).symm, hleg, hhead, hlast⟩

/-- Distinct first darts `x⁺_{T(y)} ≠ x⁺_{T(y')}` of strand paths come from distinct darts. -/
private theorem ne_of_head?_ne {P Q : List (G.StrandDart fun _ => ∅)}
    (hPP : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath P)
    (hQQ : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath Q) {y y' : H}
    (hP : ∀ e ∈ P.head?, e.1 = xPlus (G.tripMap y))
    (hQ : ∀ e ∈ Q.head?, e.1 = xPlus (G.tripMap y')) (h : P.head? ≠ Q.head?) : y ≠ y' := by
  rintro rfl
  apply h
  obtain ⟨e, P', rfl⟩ := List.exists_cons_of_ne_nil hPP.ne_nil
  obtain ⟨f, Q', rfl⟩ := List.exists_cons_of_ne_nil hQQ.ne_nil
  simp only [List.head?_cons, Option.some.injEq]
  exact Subtype.ext ((hP e rfl).trans (hQ f rfl).symm)

/-- Distinct last darts of strand paths, with `ē_m = x⁻_z` and `f̄_n = x⁻_{z'}`, come from distinct
darts `z ≠ z'`. -/
private theorem ne_of_getLast?_ne {P Q : List (G.StrandDart fun _ => ∅)}
    (hPP : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath P)
    (hQQ : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath Q) {z z' : H}
    (hP : ∀ e ∈ P.getLast?, ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv e).1 = xMinus z)
    (hQ : ∀ e ∈ Q.getLast?,
      ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv e).1 = xMinus z')
    (h : P.getLast? ≠ Q.getLast?) : z ≠ z' := by
  rintro rfl
  apply h
  obtain ⟨e, P', rfl⟩ := List.exists_cons_of_ne_nil hPP.ne_nil
  obtain ⟨f, Q', rfl⟩ := List.exists_cons_of_ne_nil hQQ.ne_nil
  have hPm := List.getLast?_eq_some_getLast (l := e :: P') (List.cons_ne_nil _ _)
  have hQm := List.getLast?_eq_some_getLast (l := f :: Q') (List.cons_ne_nil _ _)
  rw [hPm, hQm]
  congr 1
  apply (isPreTripleDiagram_strandDiagram hG (isWhiteDatum_empty htri)).inv_involutive.injective
  exact Subtype.ext ((hP _ hPm).trans (hQ _ hQm).symm)

/-- Two distinct darts `y, y'` arriving at a crossing `w` with three darts: some edge `{c, c̄}`,
`c ∈ w`, contains `y` or `T(y)` and contains `y'` or `T(y')`. -/
private theorem exists_mem_edgeOf {w : Finset H} (hw : G.IsCrossing w) {y y' : H}
    (hy : G.vertexOf (G.inv y) = w) (hy' : G.vertexOf (G.inv y') = w) (hne : y ≠ y') :
    ∃ c ∈ w, (y ∈ G.edgeOf c ∨ G.tripMap y ∈ G.edgeOf c) ∧
      (y' ∈ G.edgeOf c ∨ G.tripMap y' ∈ G.edgeOf c) := by
  have hi : ∀ z, G.inv (G.inv z) = z := hG.inv_involutive
  have h3 : (G.vertexOf (G.inv y)).card = 3 := by
    rw [hy]
    exact htri w hw
  have hmem : G.inv y' ∈ G.vertexOf (G.inv y) := by
    rw [hy, ← hy']
    exact G.self_mem_vertexOf _
  have hne' : G.inv y' ≠ G.inv y := fun h => hne (hG.inv_involutive.injective h).symm
  have hcy : G.IsCrossing (G.vertexOf (G.inv y)) := hy ▸ hw
  have hcy' : G.IsCrossing (G.vertexOf (G.inv y')) := hy' ▸ hw
  have hyw : G.inv y ∈ w := by
    rw [← hy]
    exact G.self_mem_vertexOf _
  have hy'w : G.inv y' ∈ w := by
    rw [← hy']
    exact G.self_mem_vertexOf _
  rcases eq_rot_or_eq_rot_of_card_eq_three h3 hmem hne' with h | h
  · refine ⟨G.inv y, hyw, Or.inl (G.mem_edgeOf.2 (Or.inr (hi y).symm)), Or.inr ?_⟩
    rw [tripMap_of_isCrossing hcy', h, Equiv.symm_apply_apply]
    exact G.mem_edgeOf.2 (Or.inl rfl)
  · refine ⟨G.inv y', hy'w, Or.inr ?_, Or.inl (G.mem_edgeOf.2 (Or.inr (hi y').symm))⟩
    rw [tripMap_of_isCrossing hcy, h, Equiv.symm_apply_apply]
    exact G.mem_edgeOf.2 (Or.inl rfl)

end Badgons

/-! ### Arrivals at white vertices -/

variable (G) in
/-- The **arrival** at the white end of the edge of `s`: `s` itself if `s` is black, and
`\overline{σ s}`, the dart with `T(\overline{σ s}) = s`, if `s` is white. -/
private def arrival (s : H) : H :=
  match G.colour s with
  | .white => G.inv (G.rot s)
  | .black => s

omit [Fintype H] [DecidableEq H] in
private theorem arrival_of_white {s : H} (h : G.colour s = .white) :
    G.arrival s = G.inv (G.rot s) := by
  unfold arrival
  rw [h]

omit [Fintype H] [DecidableEq H] in
private theorem arrival_of_black {s : H} (h : G.colour s = .black) : G.arrival s = s := by
  unfold arrival
  rw [h]

namespace IsNormalPlabicGraph

variable (hG : G.IsNormalPlabicGraph)

include hG

/-- Every crossing of a normal plabic graph consists of exactly three darts. -/
theorem card_eq_three_of_isCrossing {w : Finset H} (hw : G.IsCrossing w) : w.card = 3 := by
  obtain ⟨a, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw.1).1
  exact hG.card_vertexOf_of_white a hw.not_isBoundaryVertex (hw.2.1 a (G.self_mem_vertexOf a))

/-- In a normal plabic graph, the far end of an edge joining internal vertices from a black dart
is white. -/
private theorem colour_inv_of_black {s : H} (hs : ¬G.IsBoundaryVertex (G.vertexOf s))
    (hs' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv s))) (hc : G.colour s = .black) :
    G.colour (G.inv s) = .white := by
  have := hG.colour_inv_ne s hs hs'
  rw [hc] at this
  cases h : G.colour (G.inv s)
  · rfl
  · exact absurd h this

/-- The arrival `ā` at the white end `w` of an edge joining internal vertices: `v(ā) = w` is a
crossing. -/
private theorem isCrossing_vertexOf_inv_arrival {s : H}
    (hs : ¬G.IsBoundaryVertex (G.vertexOf s))
    (hs' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv s))) :
    G.IsCrossing (G.vertexOf (G.inv (G.arrival s))) := by
  cases hc : G.colour s
  · rw [arrival_of_white hc, hG.inv_involutive, G.vertexOf_rot]
    exact hG.isCrossing_vertexOf hs hc
  · rw [arrival_of_black hc]
    exact hG.isCrossing_vertexOf hs' (colour_inv_of_black hG hs hs' hc)

/-- The two darts of an edge joining internal vertices have the same white end. -/
private theorem vertexOf_inv_arrival_inv {s : H} (hs : ¬G.IsBoundaryVertex (G.vertexOf s))
    (hs' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv s))) :
    G.vertexOf (G.inv (G.arrival (G.inv s))) = G.vertexOf (G.inv (G.arrival s)) := by
  cases hc : G.colour s
  · have hc' := (hG.inv_internal_black_of_white hs hc).2
    rw [arrival_of_black hc', arrival_of_white hc, hG.inv_involutive, hG.inv_involutive,
      G.vertexOf_rot]
  · have hc' := colour_inv_of_black hG hs hs' hc
    rw [arrival_of_white hc', arrival_of_black hc, hG.inv_involutive, G.vertexOf_rot]

/-- The two darts of an edge joining internal vertices give distinct arrivals at its white end. -/
private theorem arrival_inv_ne {s : H} (hs : ¬G.IsBoundaryVertex (G.vertexOf s))
    (hs' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv s))) :
    G.arrival (G.inv s) ≠ G.arrival s := by
  cases hc : G.colour s
  · have hc' := (hG.inv_internal_black_of_white hs hc).2
    rw [arrival_of_black hc', arrival_of_white hc]
    intro h
    exact (rot_ne_self_of_card_eq_three (hG.card_vertexOf_of_white s hs hc)).1
      (hG.inv_involutive.injective h).symm
  · have hc' := colour_inv_of_black hG hs hs' hc
    rw [arrival_of_white hc', arrival_of_black hc]
    intro h
    apply (rot_ne_self_of_card_eq_three (hG.card_vertexOf_of_white _ hs' hc')).1
    simpa only [hG.inv_involutive _] using congrArg G.inv h

/-- The arrival of `s` is `s`, or `T` maps it to `s`. -/
private theorem tripMap_arrival {s : H} (hs : ¬G.IsBoundaryVertex (G.vertexOf s)) :
    G.arrival s = s ∨ G.tripMap (G.arrival s) = s := by
  cases hc : G.colour s
  · right
    have hr : ¬G.IsBoundaryVertex (G.vertexOf (G.rot s)) := by rwa [G.vertexOf_rot]
    rw [arrival_of_white hc, tripMap_apply, hG.inv_involutive,
      turn_of_white hr (by rw [hG.colour_rot _ hs, hc]), Equiv.symm_apply_apply]
  · exact Or.inl (arrival_of_black hc)

/-- A dart at an internal vertex is not a leg. -/
private theorem not_isLeg {x : H} (hx : ¬G.IsBoundaryVertex (G.vertexOf x)) : ¬G.IsLeg x :=
  fun h => hx (hG.toIsPlabicGraph.isBoundaryVertex_of_isLeg h)

/-- A trip containing `s` contains its arrival. -/
private theorem arrival_mem_darts {τ : G.Trip} {s : H} (hτ : s ∈ τ.darts)
    (hs : ¬G.IsBoundaryVertex (G.vertexOf s)) : G.arrival s ∈ τ.darts := by
  rcases tripMap_arrival hG hs with h | h
  · rwa [h]
  · refine Trip.mem_darts_of_tripMap hG.toIsPlabicGraph (by rwa [h]) ?_
    rw [h]
    exact not_isLeg hG hs

/-- If `u₂` follows `u₁`, then the arrival of `u₂` follows the arrival of `u₁`, when they
differ. -/
private theorem follows_arrival {u₁ u₂ : H} (h₁ : ¬G.IsBoundaryVertex (G.vertexOf u₁))
    (h₂ : ¬G.IsBoundaryVertex (G.vertexOf u₂)) (h : G.Follows u₁ u₂)
    (hne : G.arrival u₁ ≠ G.arrival u₂) : G.Follows (G.arrival u₁) (G.arrival u₂) := by
  have h' : G.Follows (G.arrival u₁) u₂ := by
    rcases tripMap_arrival hG h₁ with e | e
    · rwa [e]
    · have : G.Follows (G.arrival u₁) u₁ := by
        have := follows_tripMap (G := G) (y := G.arrival u₁) (by rw [e]; exact not_isLeg hG h₁)
        rwa [e] at this
      exact this.trans h
  rcases tripMap_arrival hG h₂ with e | e
  · rwa [e]
  · rw [← e] at h'
    exact h'.of_tripMap hG.toIsPlabicGraph hne

/-- If two edges joining internal vertices give the same arrivals, they are equal. -/
private theorem eq_or_eq_inv_of_arrival_eq {u₁ u₂ : H}
    (h₁ : ¬G.IsBoundaryVertex (G.vertexOf u₁)) (h₁' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv u₁)))
    (h₂ : ¬G.IsBoundaryVertex (G.vertexOf u₂)) (h₂' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv u₂)))
    (hA : G.arrival u₁ = G.arrival u₂) (hA' : G.arrival (G.inv u₁) = G.arrival (G.inv u₂)) :
    u₂ = u₁ ∨ u₂ = G.inv u₁ := by
  have hinj := hG.inv_involutive.injective
  cases hc₁ : G.colour u₁ <;> cases hc₂ : G.colour u₂
  · rw [arrival_of_white hc₁, arrival_of_white hc₂] at hA
    exact Or.inl (G.rot.injective (hinj hA)).symm
  · exfalso
    have hc₁' := (hG.inv_internal_black_of_white h₁ hc₁).2
    have hc₂' := colour_inv_of_black hG h₂ h₂' hc₂
    rw [arrival_of_white hc₁, arrival_of_black hc₂] at hA
    rw [arrival_of_black hc₁', arrival_of_white hc₂'] at hA'
    have e := hinj hA'
    rw [← hA, hG.inv_involutive] at e
    exact (rot_ne_self_of_card_eq_three (hG.card_vertexOf_of_white u₁ h₁ hc₁)).2 e.symm
  · exfalso
    have hc₁' := colour_inv_of_black hG h₁ h₁' hc₁
    have hc₂' := (hG.inv_internal_black_of_white h₂ hc₂).2
    rw [arrival_of_black hc₁, arrival_of_white hc₂] at hA
    rw [arrival_of_white hc₁', arrival_of_black hc₂'] at hA'
    have e := hinj hA'
    rw [hA, hG.inv_involutive] at e
    exact (rot_ne_self_of_card_eq_three (hG.card_vertexOf_of_white u₂ h₂ hc₂)).2 e
  · rw [arrival_of_black hc₁, arrival_of_black hc₂] at hA
    exact Or.inl hA.symm

/-- In a normal plabic graph, the edges of darts at distinct crossings are distinct: the far end of
an edge at a white vertex is black. -/
private theorem edgeOf_ne {w w' : Finset H} (hw : G.IsCrossing w) (hw' : G.IsCrossing w')
    (hww' : w ≠ w') {c c' : H} (hc : c ∈ w) (hc' : c' ∈ w') : G.edgeOf c ≠ G.edgeOf c' := by
  intro h
  have hmem : c ∈ G.edgeOf c' := h ▸ G.mem_edgeOf.2 (Or.inl rfl)
  have hv' : ¬G.IsBoundaryVertex (G.vertexOf c') := by
    rw [← hw'.eq_vertexOf hc']
    exact hw'.not_isBoundaryVertex
  rcases G.mem_edgeOf.1 hmem with rfl | rfl
  · exact hww' ((hw.eq_vertexOf hc).trans (hw'.eq_vertexOf hc').symm)
  · have hb := (hG.inv_internal_black_of_white hv' (hw'.2.1 _ hc')).2
    rw [hw.2.1 _ hc] at hb
    exact Shade.noConfusion hb

/-! ### Bad features and badgons -/

/-- A stretch `T(y), …, Tⁿ(y)` of a trip from an arrival at a crossing `w` to an arrival at a
crossing `w'` has length at least two, the far end of `T(y)` being black. -/
private theorem two_le_of_iterate_tripMap {w w' : Finset H} (hw : G.IsCrossing w)
    (hw' : G.IsCrossing w') {y : H} {n : ℕ} (hn : 1 ≤ n) (hy : G.vertexOf (G.inv y) = w)
    (hz : G.vertexOf (G.inv (G.tripMap^[n] y)) = w') : 2 ≤ n := by
  by_contra hlt
  obtain rfl : n = 1 := by omega
  rw [Function.iterate_one] at hz
  have hTy : G.tripMap y ∈ w := hy ▸ turn_mem_vertexOf _
  have hv : ¬G.IsBoundaryVertex (G.vertexOf (G.tripMap y)) := by
    rw [← hw.eq_vertexOf hTy]
    exact hw.not_isBoundaryVertex
  have hb := (hG.inv_internal_black_of_white hv (hw.2.1 _ hTy)).2
  rw [hw'.2.1 _ (hz ▸ G.self_mem_vertexOf _)] at hb
  exact Shade.noConfusion hb

/-- The dart after an arrival at an internal vertex is not a leg. -/
private theorem not_isLeg_iterate_succ {y : H} {n : ℕ}
    (hz : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.tripMap^[n] y))))
    (hl : ∀ k, 1 ≤ k → k ≤ n → ¬G.IsLeg (G.tripMap^[k] y)) :
    ∀ k, 1 ≤ k → k ≤ n + 1 → ¬G.IsLeg (G.tripMap^[k] y) := by
  intro k hk1 hk2
  rcases Nat.lt_or_ge n k with h | h
  · obtain rfl : k = n + 1 := by omega
    rw [Function.iterate_succ_apply']
    intro hleg
    have := hG.toIsPlabicGraph.isBoundaryVertex_of_isLeg hleg
    rw [tripMap_apply, vertexOf_turn] at this
    exact hz this
  · exact hl k hk1 h

/-- A badgon of `X°(G, ∅)` gives a bad feature. -/
private theorem hasBadFeature_of_hasBadgon
    (h : (G.strandDiagram hG.toIsPlabicGraph hG.isWhiteDatum_empty).HasBadgon) :
    G.HasBadFeature := by
  have hP := hG.toIsPlabicGraph
  have htri : ∀ w, G.IsCrossing w → w.card = 3 := fun _ hw => hG.card_eq_three_of_isCrossing hw
  have hbij := bijOn_crossingTriplePoint htri hP
  rcases h with ⟨P, hPm⟩ | ⟨P, Q, x, y, hD⟩
  · obtain ⟨w, hw, hxw⟩ := hbij.surjOn (Finset.mem_coe.2 hPm.pathStart_mem)
    obtain ⟨y, y', hne, hy, hy', τ, hyτ, hy'τ⟩ :=
      (exists_isMonogon_iff hP htri hw).1 ⟨P, hPm, hxw.symm⟩
    exact Or.inr (Or.inl (hG.exists_isEssentialSelfIntersection hw.1 hw.2.1 hyτ hy'τ hne hy hy'))
  · obtain ⟨w, hw, rfl⟩ := hbij.surjOn (Finset.mem_coe.2 hD.mem_left)
    obtain ⟨w', hw', rfl⟩ := hbij.surjOn (Finset.mem_coe.2 hD.mem_right)
    have hww' : w ≠ w' := fun h => hD.ne (by rw [h])
    obtain ⟨yP, hyPB, nP, hnP, hyP, hzP, hlP, hP1, hP2⟩ :=
      exists_tripMap_of_isStrandPath_crossing hP htri hD.isStrandPath_fst hw hw'
        hD.pathStart_fst hD.pathEnd_fst
    obtain ⟨yQ, hyQB, nQ, hnQ, hyQ, hzQ, hlQ, hQ1, hQ2⟩ :=
      exists_tripMap_of_isStrandPath_crossing hP htri hD.isStrandPath_snd hw hw'
        hD.pathStart_snd hD.pathEnd_snd
    have hyne : yP ≠ yQ :=
      ne_of_head?_ne hP htri hD.isStrandPath_fst hD.isStrandPath_snd hP1 hQ1 hD.head?_ne
    have hzne : G.tripMap^[nP] yP ≠ G.tripMap^[nQ] yQ :=
      ne_of_getLast?_ne hP htri hD.isStrandPath_fst hD.isStrandPath_snd hP2 hQ2 hD.getLast?_ne
    obtain ⟨τP, -, hzPτ, htP⟩ :=
      exists_trip_traversesThen hP hyPB (hG.two_le_of_iterate_tripMap hw hw' hnP hyP hzP)
        (hG.not_isLeg_iterate_succ (hzP ▸ hw'.not_isBoundaryVertex) hlP)
    obtain ⟨τQ, -, hzQτ, htQ⟩ :=
      exists_trip_traversesThen hP hyQB (hG.two_le_of_iterate_tripMap hw hw' hnQ hyQ hzQ)
        (hG.not_isLeg_iterate_succ (hzQ ▸ hw'.not_isBoundaryVertex) hlQ)
    by_cases hτ : τP = τQ
    · subst hτ
      exact Or.inr (Or.inl
        (hG.exists_isEssentialSelfIntersection hw'.1 hw'.2.1 hzPτ hzQτ hzne hzP hzQ))
    · obtain ⟨c, hcw, hc₁, hc₂⟩ := exists_mem_edgeOf hP htri hw hyP hyQ hyne
      obtain ⟨c', hc'w, hc'₁, hc'₂⟩ := exists_mem_edgeOf hP htri hw' hzP hzQ hzne
      exact Or.inr (Or.inr ⟨τP, τQ, G.edgeOf c, G.edgeOf c', hτ, G.mem_edges.2 ⟨c, rfl⟩,
        disjoint_edgeOf_bdry hP hw hcw, G.mem_edges.2 ⟨c', rfl⟩, disjoint_edgeOf_bdry hP hw' hc'w,
        edgeOf_ne hG hw hw' hww' hcw hc'w, htP _ _ hc₁ hc'₁, htQ _ _ hc₂ hc'₂⟩)

/-- An essential self-intersection gives a monogon of `X°(G, ∅)`. -/
private theorem hasMonogon_of_isEssentialSelfIntersection {d : H}
    (h : G.IsEssentialSelfIntersection d) :
    (G.strandDiagram hG.toIsPlabicGraph hG.isWhiteDatum_empty).HasMonogon := by
  have htri : ∀ w, G.IsCrossing w → w.card = 3 := fun _ hw => hG.card_eq_three_of_isCrossing hw
  obtain ⟨-, hd, hd', τ, hdτ, hd'τ⟩ := h
  exact hasMonogon_of_mem_darts hG.toIsPlabicGraph htri
    (hG.isCrossing_vertexOf_inv_arrival hd hd') (hG.arrival_mem_darts hdτ hd)
    (hG.arrival_mem_darts hd'τ hd') (hG.arrival_inv_ne hd hd').symm rfl
    (hG.vertexOf_inv_arrival_inv hd hd')

/-- A bad double crossing gives a badgon of `X°(G, ∅)`. -/
private theorem hasBadgon_of_isBadDoubleCrossing {τ τ' : G.Trip} {e₁ e₂ : Finset H}
    (h : G.IsBadDoubleCrossing τ τ' e₁ e₂) :
    (G.strandDiagram hG.toIsPlabicGraph hG.isWhiteDatum_empty).HasBadgon := by
  have hP := hG.toIsPlabicGraph
  have htri : ∀ w, G.IsCrossing w → w.card = 3 := fun _ hw => hG.card_eq_three_of_isCrossing hw
  obtain ⟨hne, he₁, hB₁, he₂, hB₂, h12, ht, ht'⟩ := h
  obtain ⟨d₁, rfl⟩ := G.mem_edges.1 he₁
  obtain ⟨d₂, rfl⟩ := G.mem_edges.1 he₂
  have hd := disjoint_edgeOf_of_ne hP h12
  -- each trip traverses the two edges along darts `u₁ ∈ e₁`, `u₂ ∈ e₂` with `u₂` after `u₁`
  obtain ⟨u₁, hu₁τ, hu₁e, u₂, hu₂τ, hu₂e, hr⟩ := Trip.exists_follows hP hd ht
  obtain ⟨v₁, hv₁τ, hv₁e, v₂, hv₂τ, hv₂e, hr'⟩ := Trip.exists_follows hP hd ht'
  -- a dart lies on one trip, so the second trip traverses the edges along `ū₁` and `ū₂`
  obtain rfl : v₁ = G.inv u₁ := eq_inv_of_mem_edgeOf hP hu₁e hv₁e fun h =>
    hne (Trip.eq_of_mem_darts hP hu₁τ (by rwa [h]))
  obtain rfl : v₂ = G.inv u₂ := eq_inv_of_mem_edgeOf hP hu₂e hv₂e fun h =>
    hne (Trip.eq_of_mem_darts hP hu₂τ (by rwa [h]))
  -- no leg: the edges join internal vertices
  have h₁' := hr.not_isBoundaryVertex_inv hP (disjoint_left.1 hB₁ hu₁e)
  have h₁'' := hr'.not_isBoundaryVertex_inv hP (disjoint_left.1 hB₁ hv₁e)
  have h₁ : ¬G.IsBoundaryVertex (G.vertexOf u₁) := by rwa [hP.inv_involutive] at h₁''
  have h₂ := hr.not_isBoundaryVertex hP (disjoint_left.1 hB₂ hu₂e)
  have h₂' := hr'.not_isBoundaryVertex hP (disjoint_left.1 hB₂ hv₂e)
  have hW₁ := hG.isCrossing_vertexOf_inv_arrival h₁ h₁'
  have hW₂ := hG.isCrossing_vertexOf_inv_arrival h₂ h₂'
  have hV₁ := hG.vertexOf_inv_arrival_inv h₁ h₁'
  have hV₂ := hG.vertexOf_inv_arrival_inv h₂ h₂'
  by_cases hW : G.vertexOf (G.inv (G.arrival u₁)) = G.vertexOf (G.inv (G.arrival u₂))
  · -- both edges end at the same white vertex: one of the trips arrives there twice
    have ha₁ := hG.arrival_mem_darts hu₁τ h₁
    have ha₂ := hG.arrival_mem_darts hu₂τ h₂
    have hb₁ := hG.arrival_mem_darts hv₁τ h₁'
    have hb₂ := hG.arrival_mem_darts hv₂τ h₂'
    by_cases hA : G.arrival u₁ = G.arrival u₂
    · by_cases hA' : G.arrival (G.inv u₁) = G.arrival (G.inv u₂)
      · exfalso
        rcases hG.eq_or_eq_inv_of_arrival_eq h₁ h₁' h₂ h₂' hA hA' with h | h
        · exact disjoint_left.1 hd hu₁e (by rwa [← h])
        · exact disjoint_left.1 hd hv₁e (by rwa [← h])
      · exact Or.inl (hasMonogon_of_mem_darts hP htri hW₁ hb₁ hb₂ hA' hV₁ (hV₂.trans hW.symm))
    · exact Or.inl (hasMonogon_of_mem_darts hP htri hW₁ ha₁ ha₂ hA rfl hW.symm)
  · -- distinct white ends: a parallel digon
    refine Or.inr (hasParallelDigon_of_follows hP htri
      (hG.follows_arrival h₁ h₂ hr fun h => hW (by rw [h]))
      (hG.follows_arrival h₁' h₂' hr' fun h => hW (by rw [← hV₁, ← hV₂, h]))
      (hG.arrival_inv_ne h₁ h₁').symm (hG.arrival_inv_ne h₂ h₂').symm hW₁ hW₂ hW rfl hV₁ rfl hV₂)

/-- A roundtrip gives a badgon of `X(G)`. -/
private theorem hasBadgon_of_hasRoundtrip (h : G.HasRoundtrip) :
    (G.tripleOfNormal hG.isNormalPlabicPregraph).HasBadgon := by
  obtain ⟨C, hC⟩ := hG.hasRoundtrip_iff_exists_isClosedStrand.1 h
  by_contra hb
  exact TripleData.not_isClosedStrand_of_not_hasBadgon hG.isTripleDiagram_tripleOfNormal hb C hC

/-- `X(G)` is isomorphic to `X°(G, ∅)`. -/
private theorem isomorphic_strandDiagram :
    (G.tripleOfNormal hG.isNormalPlabicPregraph).Isomorphic
      (G.strandDiagram hG.toIsPlabicGraph hG.isWhiteDatum_empty) := by
  obtain ⟨-, -, D, hD, hiso⟩ := hG.isGeneralizedTripleDiagram_tripleOfNormal
  exact TripleData.Isomorphic.trans _ hiso
    (strandDiagram_isomorphic_of_agree hG.toIsPlabicGraph _ hD
      fun x hx => hD.eq_empty hx (hG.card_eq_three_of_isCrossing hx))

/-- A normal plabic graph `G` has a bad feature if and only if its triple diagram `X(G)` has a
badgon. -/
@[cluster_algebras "lem_bad_feature_iff_badgon"]
theorem hasBadFeature_iff_hasBadgon :
    G.HasBadFeature ↔ (G.tripleOfNormal hG.isNormalPlabicPregraph).HasBadgon := by
  obtain ⟨θ⟩ := hG.isomorphic_strandDiagram
  constructor
  · rintro (h | ⟨d, hd⟩ | ⟨τ, τ', e₁, e₂, h⟩)
    · exact hG.hasBadgon_of_hasRoundtrip h
    · exact θ.symm.hasBadgon (Or.inl (hG.hasMonogon_of_isEssentialSelfIntersection hd))
    · exact θ.symm.hasBadgon (hG.hasBadgon_of_isBadDoubleCrossing h)
  · exact fun h => hG.hasBadFeature_of_hasBadgon (θ.hasBadgon h)

end IsNormalPlabicGraph

end PlabicData

end ClusterAlgebras
