/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.GeneralizedMoves
public import ClusterAlgebras.Plabic.BridgeTrips
public import ClusterAlgebras.Plabic.BadFeatures
public import ClusterAlgebras.Plabic.NearlyLeafless
public import ClusterAlgebras.Plabic.RoundtripMoves
public import ClusterAlgebras.Plabic.Excision

/-!
# A normalization of the bridge graph

Let `b ≥ 1`, let `s` be a nested sequence of pairs `(i_t, j_t)` with `1 ≤ i_t < j_t ≤ b`, and let
`γ : [1, b] → {white, black}`. Every crossing of the bridge graph `G = G(s, γ)` consists of three
darts, so its strand diagram `X° = X°(G, ∅)` for the empty white datum is defined. This file
makes precise the statement of [FWZ] that `X(N(G))` is isotopic to `X(G)`: `G` has a normalization
`N` whose triple diagram `X(N)` is isomorphic to `X°`; consequently `X°` is a triple diagram.

The normalization is built in four stages. Recolouring the white lollipops of `G` (Stage A) gives
the bridge graph `G♭` all of whose lollipops are black; the recolourings change neither the trip
map nor the crossings, so `X°` is a generalized triple diagram of `G♭`. As `G♭` has no roundtrip,
the remaining stages are local moves that keep generalized triple diagrams: removing the white
vertices with two darts (Stage B), contracting the edges between two distinct black internal
vertices (Stage C), and inserting a black vertex on every edge without a black internal end
(Stage D). The result `N` is normal: a monochromatic edge between internal vertices would be a
loop, and a loop gives a roundtrip. Then `X°` and `X(N)` are generalized triple diagrams of `N`,
and since the crossings of `N` have three darts, both are isomorphic to `X°(N, ∅)`.

## Main definitions

* `ClusterAlgebras.bridgePlabicGraph`: the bridge graph `G(s, γ)` as a bundled plabic graph.

## Main results

* `ClusterAlgebras.PlabicData.strandDiagram_isomorphic_of_eq_toDiskMap`: graphs differing only in
  colours away from the crossings, with the same trip map, have isomorphic strand diagrams.
* `ClusterAlgebras.PlabicData.strandDiagram_isomorphic_of_eqOn_crossings`: white data agreeing at
  the crossings give isomorphic strand diagrams.
* `ClusterAlgebras.PlabicGraph.exists_moveEquivalent_isNormal_of_not_hasRoundtrip`: Stages B, C
  and D, for any plabic graph without roundtrips whose white internal vertices have two or three
  darts.
* `ClusterAlgebras.recolourLollipop_bridgeGraph`, `ClusterAlgebras.isNearlyLeafless_bridgeGraph`:
  Stage A.
* `ClusterAlgebras.exists_isNormalization_bridgeGraph`: a normalization `N` of `G(s, γ)` with
  `X(N) ≅ X°(G(s, γ), ∅)`.
* `ClusterAlgebras.isTripleDiagram_strandDiagram_bridgeGraph`: `X°(G(s, γ), ∅)` is a triple
  diagram.

## Implementation notes

* **Labels.** As for the bridge graph, `x : Fin b` is FWZ's label `x + 1`.
* **The colouring `γ₀`.** The graph `G♭` at the end of Stage A is `G(s, γ₀)` for the colouring
  `γ₀` black everywhere: the colouring matters only at the lollipop positions.
* **Stages B to D** are stated for an arbitrary plabic graph `K` without roundtrips whose white
  internal vertices have two or three darts; the hypothesis replaces FWZ's appeal to the
  shape of `G♭`. The stages terminate since each removal and contraction removes two darts and
  each insertion lowers the number of darts `d ∉ B` of which neither `v(d)` nor `v(d̄)` is a black
  internal vertex.
* **Normality.** Instead of FWZ's final appeal to `G♭ ∼ N`, the absence of roundtrips is
  carried along the stages one step at a time, by
  `ClusterAlgebras.PlabicGraph.MoveEquivalent.hasRoundtrip_iff`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

open StrandSymbol

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### Isomorphisms out of a strand diagram -/

/-- A bijection intertwining two rotations maps each vertex onto a vertex. -/
private theorem map_vertexOf_of_semiconj {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {R : RotationSystem α} {R' : RotationSystem β} (θ : α ≃ β)
    (h : ∀ x, θ (R.rot x) = R'.rot (θ x)) (d : α) :
    (R.vertexOf d).map θ.toEmbedding = R'.vertexOf (θ d) := by
  have hp : ∀ (n : ℕ) (x : α), θ ((R.rot ^ n) x) = (R'.rot ^ n) (θ x) := by
    intro n
    induction n with
    | zero => exact fun _ => rfl
    | succ n ih =>
      intro x
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rw [h, ih]
  ext y
  rw [mem_map_equiv, RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
  constructor
  · intro hs
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← hp, hn, Equiv.apply_symm_apply]⟩
  · intro hs
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    exact ⟨n, θ.injective (by rw [zpow_natCast, hp, hn, Equiv.apply_symm_apply])⟩

/-- An isomorphism out of a strand diagram: a bijection of darts commuting with the involutions
and the rotations, matching the boundaries, the orientations and the darts of the endpoints. -/
private theorem strandDiagram_isomorphic_of' {G : PlabicData H b} (hG : G.IsPlabicGraph)
    {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) {H' : Type*} [Fintype H']
    [DecidableEq H'] (Y : TripleData H' b) (θ : G.StrandDart D ≃ H')
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

/-- To check that a map out of a strand diagram commutes with the involutions, it suffices to
check it on the symbols `x⁺_d`, `y⁺_{s,τ}` and `∂_r`. -/
private theorem strandDiagram_map_inv_of' {G : PlabicData H b} (hG : G.IsPlabicGraph)
    {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D) {H' : Type*}
    {Y : TripleData H' b} (hY : Function.Involutive Y.inv)
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

/-- White data agreeing at every crossing have isomorphic strand diagrams. -/
theorem strandDiagram_isomorphic_of_eqOn_crossings {G : PlabicData H b} (hG : G.IsPlabicGraph)
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
  refine strandDiagram_isomorphic_of' hG hD' _ θ ?_ ?_ ?_ ?_ ?_
  · refine strandDiagram_map_inv_of' hG hD'
      (isPreTripleDiagram_strandDiagram hG hD).inv_involutive _ ?_
    rintro ⟨a, ha⟩ (⟨d, rfl⟩ | ⟨e, τ, rfl⟩ | ⟨r, rfl⟩)
    · rfl
    · apply Subtype.ext
      have ha' : G.IsDatumSegment D e τ := (hS e τ).1 ha
      obtain ⟨o1, o2, -⟩ := hD'.otherTriangle_spec (ha : G.IsDatumSegment D' e τ)
      have ho : G.otherTriangle D' e τ = G.otherTriangle D e τ := by
        obtain ⟨-, -, -, -, hm⟩ := id o1
        exact hD.eq_otherTriangle ha' ((hT _).1 (.of_isDatumSegment o1)) hm o2
      exact congrArg (yMinus e) ho
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
  · exact fun _ => rfl

/-! ### Changing colours away from the crossings -/

/-- A vertex containing a dart fixed by the rotation has at most one dart. -/
private theorem card_vertexOf_le_one_of_rot_eq {R : RotationSystem H} {e : H} (he : R.rot e = e) :
    (R.vertexOf e).card ≤ 1 := by
  refine card_le_one.2 fun x hx y hy => ?_
  obtain ⟨i, rfl⟩ := (R.mem_vertexOf).1 hx
  obtain ⟨j, rfl⟩ := (R.mem_vertexOf).1 hy
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self he,
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self he]

/-- The turn at a dart fixed by the rotation is that dart. -/
private theorem turn_eq_self_of_rot_eq {G : PlabicData H b} {z : H} (hz : G.rot z = z) :
    G.turn z = z := by
  have hz' : G.rot.symm z = z := (Equiv.symm_apply_eq _).2 hz.symm
  unfold turn
  split_ifs
  · rfl
  · cases G.colour z <;> simp [hz, hz']

/-- Data with the same disk map and the same colour at `z` turn the same way at `z`. -/
private theorem turn_congr {G G' : PlabicData H b} (hM : G'.toDiskMap = G.toDiskMap) {z : H}
    (hz : G'.colour z = G.colour z) : G'.turn z = G.turn z := by
  obtain ⟨M, c, l⟩ := G
  obtain ⟨M', c', l'⟩ := G'
  obtain rfl : M = M' := hM.symm
  unfold turn
  rw [hz]

/-- Data with the same disk map, whose colours agree at every dart not fixed by the rotation,
have the same trip map. -/
theorem tripMap_eq_of_colour_eq {G G' : PlabicData H b} (hM : G'.toDiskMap = G.toDiskMap)
    (hc : ∀ d, G.rot d ≠ d → G'.colour d = G.colour d) : G'.tripMap = G.tripMap := by
  obtain ⟨M, c, l⟩ := G
  obtain ⟨M', c', l'⟩ := G'
  obtain rfl : M = M' := hM.symm
  funext d
  by_cases hf : M.rot (M.inv d) = M.inv d
  · exact (turn_eq_self_of_rot_eq (G := ⟨M, c', l'⟩) hf).trans
      (turn_eq_self_of_rot_eq (G := ⟨M, c, l⟩) hf).symm
  · exact turn_congr (G := ⟨M, c, l⟩) (G' := ⟨M, c', l'⟩) rfl (hc (M.inv d) hf)

/-- Data with the same disk map, whose colours agree at every dart not fixed by the rotation,
have the same crossings: a vertex containing a dart fixed by the rotation has one dart. -/
theorem isCrossing_iff_of_colour_eq {G G' : PlabicData H b} (hM : G'.toDiskMap = G.toDiskMap)
    (hc : ∀ d, G.rot d ≠ d → G'.colour d = G.colour d) (w : Finset H) :
    G'.IsCrossing w ↔ G.IsCrossing w := by
  obtain ⟨M, c, l⟩ := G
  obtain ⟨M', c', l'⟩ := G'
  obtain rfl : M = M' := hM.symm
  have key : ∀ v ∈ M.internalVertices, 3 ≤ v.card → ∀ e ∈ v, M.rot e ≠ e := by
    intro v hv h3 e he hf
    obtain ⟨a, rfl⟩ := M.mem_vertices.1 (M.mem_internalVertices.1 hv).1
    have := card_vertexOf_le_one_of_rot_eq hf
    rw [M.vertexOf_eq_of_mem he] at this
    omega
  unfold IsCrossing
  constructor
  · rintro ⟨hw, hcol, h3⟩
    refine ⟨hw, fun e he => ?_, h3⟩
    rw [← hc e (key w hw h3 e he)]
    exact hcol e he
  · rintro ⟨hw, hcol, h3⟩
    refine ⟨hw, fun e he => ?_, h3⟩
    rw [hc e (key w hw h3 e he)]
    exact hcol e he

/-- **Recolouring keeps the strand diagram.** Let `G` and `G'` be plabic graphs with the same
disk map and the same labelling, the same crossings and the same trip map; so they differ at most
in the colours of vertices that are not crossings. Then for a white datum `D` of both, the strand
diagrams `X°(G', D)` and `X°(G, D)` are isomorphic. -/
theorem strandDiagram_isomorphic_of_eq_toDiskMap {G G' : PlabicData H b}
    (hM : G'.toDiskMap = G.toDiskMap) (hl : G'.leg = G.leg)
    (hc : ∀ w, G'.IsCrossing w ↔ G.IsCrossing w) (ht : G'.tripMap = G.tripMap)
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D) (hD' : G'.IsWhiteDatum D) :
    (G'.strandDiagram hG' hD').Isomorphic (G.strandDiagram hG hD) := by
  obtain ⟨M, c, l⟩ := G
  obtain ⟨M', c', l'⟩ := G'
  obtain rfl : M = M' := hM.symm
  obtain rfl : l = l' := hl.symm
  have hcF : PlabicData.IsCrossing ⟨M, c', l⟩ =
      PlabicData.IsCrossing (⟨M, c, l⟩ : PlabicData H b) :=
    funext fun w => propext (hc w)
  have hIn : PlabicData.IsInitial ⟨M, c', l⟩ = PlabicData.IsInitial (⟨M, c, l⟩ : PlabicData H b) :=
    by funext d; unfold IsInitial; rw [hcF]; rfl
  have hTe : PlabicData.IsTerminal ⟨M, c', l⟩ =
      PlabicData.IsTerminal (⟨M, c, l⟩ : PlabicData H b) := by
    funext d; unfold IsTerminal; rw [hcF]
  have hCL : PlabicData.chainLength ⟨M, c', l⟩ =
      PlabicData.chainLength (⟨M, c, l⟩ : PlabicData H b) := by
    funext d
    have hn : ∀ n, PlabicData.IsTerminal ⟨M, c', l⟩
        ((PlabicData.tripMap ⟨M, c', l⟩)^[n] d) ↔ PlabicData.IsTerminal
          (⟨M, c, l⟩ : PlabicData H b) ((PlabicData.tripMap ⟨M, c, l⟩)^[n] d) := by
      intro n; rw [hTe, ht]
    unfold chainLength
    split_ifs with h1 h2 h2
    · exact Nat.find_congr' (hn _)
    · exact absurd (h1.imp fun n => (hn n).1) h2
    · exact absurd (h2.imp fun n => (hn n).2) h1
    · rfl
  have hCE : PlabicData.chainEnd ⟨M, c', l⟩ =
      PlabicData.chainEnd (⟨M, c, l⟩ : PlabicData H b) := by
    funext d; unfold chainEnd; rw [hCL, ht]
  have hCS : PlabicData.chainStart ⟨M, c', l⟩ =
      PlabicData.chainStart (⟨M, c, l⟩ : PlabicData H b) := by
    funext d; unfold chainStart; simp only [hIn, hCE]
  have hDT : PlabicData.IsDatumTriangle ⟨M, c', l⟩ D =
      PlabicData.IsDatumTriangle (⟨M, c, l⟩ : PlabicData H b) D := by
    funext τ; unfold IsDatumTriangle; rw [hcF]
  have hDS : PlabicData.IsDatumSegment ⟨M, c', l⟩ D =
      PlabicData.IsDatumSegment (⟨M, c, l⟩ : PlabicData H b) D := by
    funext e τ; unfold IsDatumSegment; rw [hcF]
  have hST : PlabicData.sideTriangle ⟨M, c', l⟩ D =
      PlabicData.sideTriangle (⟨M, c, l⟩ : PlabicData H b) D := by
    funext p; unfold sideTriangle; simp only [hDT]
  have hOT : PlabicData.otherTriangle ⟨M, c', l⟩ D =
      PlabicData.otherTriangle (⟨M, c, l⟩ : PlabicData H b) D := by
    funext e τ; unfold otherTriangle; simp only [hDT]
  have hIS : PlabicData.IsStrandSymbol ⟨M, c', l⟩ D =
      PlabicData.IsStrandSymbol (⟨M, c, l⟩ : PlabicData H b) D := by
    funext a
    cases a <;> simp only [IsStrandSymbol, hIn, hTe, hDS]
  have hInv : PlabicData.strandInvSym ⟨M, c', l⟩ D =
      PlabicData.strandInvSym (⟨M, c, l⟩ : PlabicData H b) D := by
    funext a
    cases a <;> simp only [strandInvSym, hCE, hCS, hOT]
  have hRot : PlabicData.strandRotSym ⟨M, c', l⟩ D =
      PlabicData.strandRotSym (⟨M, c, l⟩ : PlabicData H b) D := by
    funext a
    cases a <;> simp only [strandRotSym, hST] <;> rfl
  set θ := Equiv.subtypeEquivRight (fun a => (congrFun hIS a).to_iff)
  refine strandDiagram_isomorphic_of' hG' hD' _ θ ?_ ?_ ?_ ?_ ?_
  · intro a
    apply Subtype.ext
    change PlabicData.strandInvSym ⟨M, c', l⟩ D a.1 = _
    rw [hInv]
    rfl
  · intro a
    apply Subtype.ext
    change PlabicData.strandRotSym ⟨M, c', l⟩ D a.1 = _
    rw [hRot]
    rfl
  · intro a
    rw [mem_strandDiagram_bdry]
    rfl
  · exact fun _ _ => rfl
  · exact fun _ => rfl

end PlabicData

/-! ### Normalizing a graph without roundtrips -/

namespace PlabicGraph

open PlabicData

variable {b : ℕ}

/-- A subtype of a finite type missing some element has fewer elements. -/
private theorem card_subtype_lt' {α : Type} [Fintype α] {p : α → Prop} [Fintype (Subtype p)]
    {x : α} (hx : ¬p x) : Fintype.card (Subtype p) < Fintype.card α :=
  Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective fun h => by
    obtain ⟨y, hy⟩ := h x
    exact hx (hy ▸ y.2)

/-- In a plabic graph without roundtrips, an internal vertex with two darts `d`, `σ d` can be
removed: `d̄ ≠ σ d`, since otherwise `{d, d̄}` would be a loop. -/
private theorem isBivalentRemovable_of_not_hasRoundtrip (K : PlabicGraph b)
    (hr : ¬K.data.HasRoundtrip) {d : K.Dart}
    (hdb : ¬K.data.IsBoundaryVertex (K.data.vertexOf d)) (hd2 : (K.data.vertexOf d).card = 2) :
    K.data.IsBivalentRemovable d where
  not_isBoundaryVertex := hdb
  card_vertexOf := hd2
  inv_ne_rot h := hr <| K.isPlabicGraph.hasRoundtrip_of_loop
    (notMem_bdry_of_mem_vertexOf hdb (K.data.self_mem_vertexOf d))
    (by rw [h, K.data.vertexOf_rot])

/-- **Stage B**: removing the white vertices with two darts. -/
private theorem exists_moveEquivalent_card_vertexOf_eq_three_of_white
    {H'' : Type*} [Fintype H''] [DecidableEq H''] (X : TripleData H'' b) :
    ∀ (n : ℕ) (K : PlabicGraph b), Fintype.card K.Dart ≤ n → ¬K.data.HasRoundtrip →
    (∀ d, ¬K.data.IsBoundaryVertex (K.data.vertexOf d) → K.data.colour d = .white →
      (K.data.vertexOf d).card = 2 ∨ (K.data.vertexOf d).card = 3) →
    K.data.IsGeneralizedTripleDiagram K.isPlabicGraph X →
    ∃ K' : PlabicGraph b, MoveEquivalent Set.univ K K' ∧ ¬K'.data.HasRoundtrip ∧
      (∀ d, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf d) → K'.data.colour d = .white →
        (K'.data.vertexOf d).card = 3) ∧
      K'.data.IsGeneralizedTripleDiagram K'.isPlabicGraph X := by
  intro n
  induction n with
  | zero =>
    intro K hn hr hw hX
    refine ⟨K, MoveEquivalent.refl _ _, hr, fun d _ _ => ?_, hX⟩
    have := Fintype.card_pos_iff.2 ⟨d⟩
    omega
  | succ n ih =>
    intro K hn hr hw hX
    by_cases hex : ∃ d, ¬K.data.IsBoundaryVertex (K.data.vertexOf d) ∧
        K.data.colour d = .white ∧ (K.data.vertexOf d).card = 2
    · obtain ⟨d, hdb, -, hd2⟩ := hex
      have hG := K.isPlabicGraph
      have hd := isBivalentRemovable_of_not_hasRoundtrip K hr hdb hd2
      let K' : PlabicGraph b :=
        ⟨_, K.data.bivalentRemoval hG hd, isPlabicGraph_bivalentRemoval hG hd⟩
      have hstep : MoveStep Set.univ K K' :=
        Or.inr ⟨.m2, trivial, Or.inl ⟨d, hd, Isomorphic.refl _⟩⟩
      have hcard : Fintype.card K'.Dart ≤ n := by
        have : Fintype.card K'.Dart < Fintype.card K.Dart :=
          card_subtype_lt' (p := (· ∈ ({d, K.data.rot d}ᶜ : Set K.Dart))) (x := d) (by simp)
        omega
      have hr' : ¬K'.data.HasRoundtrip := fun h => hr (hstep.hasRoundtrip_iff.2 h)
      have hw' : ∀ y, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf y) →
          K'.data.colour y = .white →
          (K'.data.vertexOf y).card = 2 ∨ (K'.data.vertexOf y).card = 3 := by
        intro y hy hc
        have hcy : (K'.data.vertexOf y).card = (K.data.vertexOf y).card := by
          rw [← map_bivalentRemoval_vertexOf hG hd y, card_map]
        rw [hcy]
        exact hw y ((isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd y).not.1 hy) hc
      have hX' : K'.data.IsGeneralizedTripleDiagram K'.isPlabicGraph X :=
        (isGeneralizedTripleDiagram_bivalentRemoval_iff hG hd X).1 hX
      obtain ⟨K'', h1, h2, h3, h4⟩ := ih K' hcard hr' hw' hX'
      exact ⟨K'', (MoveEquivalent.of_moveStep hstep).trans h1, h2, h3, h4⟩
    · push Not at hex
      exact ⟨K, MoveEquivalent.refl _ _, hr,
        fun d hd hc => (hw d hd hc).resolve_left (hex d hd hc), hX⟩

/-- **Stage C**: contracting the edges between two distinct black internal vertices. -/
private theorem exists_moveEquivalent_vertexOf_eq_vertexOf_inv_of_black
    {H'' : Type*} [Fintype H''] [DecidableEq H''] (X : TripleData H'' b) :
    ∀ (n : ℕ) (K : PlabicGraph b), Fintype.card K.Dart ≤ n → ¬K.data.HasRoundtrip →
    (∀ d, ¬K.data.IsBoundaryVertex (K.data.vertexOf d) → K.data.colour d = .white →
      (K.data.vertexOf d).card = 3) →
    K.data.IsGeneralizedTripleDiagram K.isPlabicGraph X →
    ∃ K' : PlabicGraph b, MoveEquivalent Set.univ K K' ∧ ¬K'.data.HasRoundtrip ∧
      (∀ d, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf d) → K'.data.colour d = .white →
        (K'.data.vertexOf d).card = 3) ∧
      (∀ d, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf d) →
        ¬K'.data.IsBoundaryVertex (K'.data.vertexOf (K'.data.inv d)) →
        K'.data.colour d = .black → K'.data.colour (K'.data.inv d) = .black →
        K'.data.vertexOf d = K'.data.vertexOf (K'.data.inv d)) ∧
      K'.data.IsGeneralizedTripleDiagram K'.isPlabicGraph X := by
  intro n
  induction n with
  | zero =>
    intro K hn hr hw hX
    refine ⟨K, MoveEquivalent.refl _ _, hr, hw, fun d _ _ _ _ => ?_, hX⟩
    have := Fintype.card_pos_iff.2 ⟨d⟩
    omega
  | succ n ih =>
    intro K hn hr hw hX
    by_cases hex : ∃ d, ¬K.data.IsBoundaryVertex (K.data.vertexOf d) ∧
        ¬K.data.IsBoundaryVertex (K.data.vertexOf (K.data.inv d)) ∧
        K.data.colour d = .black ∧ K.data.colour (K.data.inv d) = .black ∧
        K.data.vertexOf d ≠ K.data.vertexOf (K.data.inv d)
    · obtain ⟨d, hdb, hdb', hdc, hdc', hne⟩ := hex
      have hG := K.isPlabicGraph
      have he : K.data.IsContractibleEdge d :=
        ⟨hne, K.data.vertexOf_mem_internalVertices.2 hdb,
          K.data.vertexOf_mem_internalVertices.2 hdb', hdc'.trans hdc.symm⟩
      let K' : PlabicGraph b :=
        ⟨_, K.data.contractEdge d (he.leg_mem hG), hG.contractEdge he⟩
      have hstep : MoveStep Set.univ K K' :=
        Or.inr ⟨.m3, trivial, Or.inl ⟨d, he, Isomorphic.refl _⟩⟩
      have hcard : Fintype.card K'.Dart ≤ n := by
        have : Fintype.card K'.Dart < Fintype.card K.Dart :=
          card_subtype_lt' (p := (· ∈ (({d, K.data.inv d} : Set K.Dart)ᶜ : Set K.Dart)))
            (x := d) (by simp)
        omega
      have hr' : ¬K'.data.HasRoundtrip := fun h => hr (hstep.hasRoundtrip_iff.2 h)
      have hw' : ∀ y, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf y) →
          K'.data.colour y = .white → (K'.data.vertexOf y).card = 3 := by
        intro y hy hc
        have hc' : K.data.colour y = .white := hc
        have hyn : (y : K.Dart) ∉ K.data.vertexOf d ∪ K.data.vertexOf (K.data.inv d) := by
          intro hm
          rw [colour_eq_of_mem_union hG he hm, hdc] at hc'
          exact Shade.noConfusion hc'
        have hcy : (K'.data.vertexOf y).card = (K.data.vertexOf y).card := by
          rw [← map_vertexOf_contractEdge_of_notMem he.not_sameCycle hyn, card_map]
        rw [hcy]
        exact hw y ((isBoundaryVertex_vertexOf_contractEdge_iff he).not.1 hy) hc'
      have hX' : K'.data.IsGeneralizedTripleDiagram K'.isPlabicGraph X :=
        (isGeneralizedTripleDiagram_contractEdge_iff hG he hdc X).1 hX
      obtain ⟨K'', h1, h2, h3, h4, h5⟩ := ih K' hcard hr' hw' hX'
      exact ⟨K'', (MoveEquivalent.of_moveStep hstep).trans h1, h2, h3, h4, h5⟩
    · push Not at hex
      exact ⟨K, MoveEquivalent.refl _ _, hr, hw, hex, hX⟩

/-- `v(d)` is a black internal vertex. -/
private def IsBlackEnd {H : Type} [Fintype H] [DecidableEq H] (G : PlabicData H b) (d : H) :
    Prop :=
  ¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = .black

open scoped Classical in
/-- **Stage D**: inserting a black vertex on every edge without a black internal end. -/
private theorem exists_moveEquivalent_isBlackEnd_or_isBlackEnd_inv
    {H'' : Type*} [Fintype H''] [DecidableEq H''] (X : TripleData H'' b) :
    ∀ (n : ℕ) (K : PlabicGraph b),
    (univ.filter fun d => d ∉ K.data.bdry ∧ ¬IsBlackEnd K.data d ∧
      ¬IsBlackEnd K.data (K.data.inv d)).card ≤ n → ¬K.data.HasRoundtrip →
    (∀ d, ¬K.data.IsBoundaryVertex (K.data.vertexOf d) → K.data.colour d = .white →
      (K.data.vertexOf d).card = 3) →
    (∀ d, ¬K.data.IsBoundaryVertex (K.data.vertexOf d) →
      ¬K.data.IsBoundaryVertex (K.data.vertexOf (K.data.inv d)) →
      K.data.colour d = .black → K.data.colour (K.data.inv d) = .black →
      K.data.vertexOf d = K.data.vertexOf (K.data.inv d)) →
    K.data.IsGeneralizedTripleDiagram K.isPlabicGraph X →
    ∃ K' : PlabicGraph b, MoveEquivalent Set.univ K K' ∧ ¬K'.data.HasRoundtrip ∧
      (∀ d, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf d) → K'.data.colour d = .white →
        (K'.data.vertexOf d).card = 3) ∧
      (∀ d, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf d) →
        ¬K'.data.IsBoundaryVertex (K'.data.vertexOf (K'.data.inv d)) →
        K'.data.colour d = .black → K'.data.colour (K'.data.inv d) = .black →
        K'.data.vertexOf d = K'.data.vertexOf (K'.data.inv d)) ∧
      (∀ d, d ∉ K'.data.bdry → IsBlackEnd K'.data d ∨ IsBlackEnd K'.data (K'.data.inv d)) ∧
      K'.data.IsGeneralizedTripleDiagram K'.isPlabicGraph X := by
  intro n
  induction n with
  | zero =>
    intro K hn hr hw hbb hX
    refine ⟨K, MoveEquivalent.refl _ _, hr, hw, hbb, fun d hd => ?_, hX⟩
    by_contra! h
    have hmem : d ∈ univ.filter fun d => d ∉ K.data.bdry ∧ ¬IsBlackEnd K.data d ∧
        ¬IsBlackEnd K.data (K.data.inv d) := mem_filter.2 ⟨mem_univ _, hd, h⟩
    have := card_pos.2 ⟨d, hmem⟩
    omega
  | succ n ih =>
    intro K hn hr hw hbb hX
    by_cases hex : ∃ d, d ∉ K.data.bdry ∧ ¬IsBlackEnd K.data d ∧
        ¬IsBlackEnd K.data (K.data.inv d)
    · obtain ⟨d, hdB, hd1, hd2⟩ := hex
      have hG := K.isPlabicGraph
      have hinv := hG.inv_involutive
      have hfix := hG.inv_ne d
      let K' : PlabicGraph b :=
        ⟨K.Dart ⊕ Fin 2, K.data.bivalentInsertion d .black,
          isPlabicGraph_bivalentInsertion .black hG hdB⟩
      have hG' : K'.data.IsPlabicGraph := K'.isPlabicGraph
      have hd' : K'.data.IsBivalentRemovable (Sum.inr 0) :=
        isBivalentRemovable_bivalentInsertion d .black
      have hstep : MoveStep Set.univ K K' :=
        Or.inr ⟨.m2, trivial, Or.inr ⟨Sum.inr 0, hd', ⟨bivalentInsertionRemovalIso .black hG hdB⟩⟩⟩
      -- the vertices, colours and involution of the insertion
      have hvl : ∀ e,
          K'.data.vertexOf (Sum.inl e) = (K.data.vertexOf e).map Function.Embedding.inl :=
        bivalentInsertion_vertexOf_inl d .black
      have hbl : ∀ e, K'.data.IsBoundaryVertex (K'.data.vertexOf (Sum.inl e)) ↔
          K.data.IsBoundaryVertex (K.data.vertexOf e) :=
        isBoundaryVertex_bivalentInsertion_vertexOf_inl d .black
      have hbr : ∀ j, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf (Sum.inr j)) :=
        not_isBoundaryVertex_bivalentInsertion_vertexOf_inr d .black
      have hcl : ∀ e, K'.data.colour (Sum.inl e) = K.data.colour e := fun _ => rfl
      have hcr : ∀ j, K'.data.colour (Sum.inr j) = .black := fun _ => rfl
      have hBl : ∀ e, IsBlackEnd K'.data (Sum.inl e) ↔ IsBlackEnd K.data e := by
        intro e
        unfold IsBlackEnd
        rw [hbl, hcl]
      have hBr : ∀ j, IsBlackEnd K'.data (Sum.inr j) := fun j => ⟨hbr j, hcr j⟩
      have hi0 : K'.data.inv (Sum.inl d) = Sum.inr 0 :=
        bivalentInsertion_inv_inl_self .black hfix
      have hi1 : K'.data.inv (Sum.inl (K.data.inv d)) = Sum.inr 1 :=
        bivalentInsertion_inv_inl_inv .black hinv
      have hr0 : K'.data.inv (Sum.inr 0) = Sum.inl d := bivalentInsertion_inv_inr_zero d .black
      have hr1 : K'.data.inv (Sum.inr 1) = Sum.inl (K.data.inv d) :=
        bivalentInsertion_inv_inr_one .black hfix
      have hie : ∀ e, e ≠ d → e ≠ K.data.inv d →
          K'.data.inv (Sum.inl e) = Sum.inl (K.data.inv e) :=
        fun e h₁ h₂ => bivalentInsertion_inv_inl_of_ne .black hinv h₁ h₂
      -- the measure drops
      have hcard : (univ.filter fun y => y ∉ K'.data.bdry ∧ ¬IsBlackEnd K'.data y ∧
          ¬IsBlackEnd K'.data (K'.data.inv y)).card ≤ n := by
        set F := univ.filter fun d => d ∉ K.data.bdry ∧ ¬IsBlackEnd K.data d ∧
          ¬IsBlackEnd K.data (K.data.inv d)
        have hsub : (univ.filter fun y => y ∉ K'.data.bdry ∧ ¬IsBlackEnd K'.data y ∧
            ¬IsBlackEnd K'.data (K'.data.inv y)) ⊆ (F.erase d).map Function.Embedding.inl := by
          intro y hy
          obtain ⟨-, hyB, hy1, hy2⟩ := mem_filter.1 hy
          rcases y with e | j
          · have he1 : e ≠ d := by
              rintro rfl
              rw [hi0] at hy2
              exact hy2 (hBr 0)
            have he2 : e ≠ K.data.inv d := by
              rintro rfl
              rw [hi1] at hy2
              exact hy2 (hBr 1)
            rw [hie e he1 he2, hBl] at hy2
            rw [hBl] at hy1
            refine mem_map_of_mem _ (mem_erase.2 ⟨he1, mem_filter.2 ⟨mem_univ _, ?_, hy1, hy2⟩⟩)
            exact fun h => hyB ((inl_mem_bivalentInsertion_bdry d .black).2 h)
          · exact absurd (hBr j) hy1
        have hdF : d ∈ F := mem_filter.2 ⟨mem_univ _, hdB, hd1, hd2⟩
        have h1 := card_le_card hsub
        rw [card_map, card_erase_of_mem hdF] at h1
        have h2 := card_pos.2 ⟨d, hdF⟩
        omega
      have hr' : ¬K'.data.HasRoundtrip := fun h => hr (hstep.hasRoundtrip_iff.2 h)
      have hw' : ∀ y, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf y) →
          K'.data.colour y = .white → (K'.data.vertexOf y).card = 3 := by
        rintro (e | j) hy hc
        · rw [hvl, card_map]
          exact hw e ((hbl e).not.1 hy) hc
        · rw [hcr] at hc
          exact Shade.noConfusion hc
      have hbb' : ∀ y, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf y) →
          ¬K'.data.IsBoundaryVertex (K'.data.vertexOf (K'.data.inv y)) →
          K'.data.colour y = .black → K'.data.colour (K'.data.inv y) = .black →
          K'.data.vertexOf y = K'.data.vertexOf (K'.data.inv y) := by
        rintro (e | j) hy hy' hc hc'
        · by_cases he1 : e = d
          · subst he1
            exact absurd ((hBl e).1 ⟨hy, hc⟩) hd1
          by_cases he2 : e = K.data.inv d
          · subst he2
            exact absurd ((hBl _).1 ⟨hy, hc⟩) hd2
          rw [hie e he1 he2] at hy' hc' ⊢
          rw [hvl, hvl, hbb e ((hbl e).not.1 hy) ((hbl _).not.1 hy') hc hc']
        · fin_cases j
          · exfalso
            change ¬K'.data.IsBoundaryVertex (K'.data.vertexOf (K'.data.inv (Sum.inr 0))) at hy'
            change K'.data.colour (K'.data.inv (Sum.inr 0)) = .black at hc'
            rw [hr0] at hy' hc'
            exact hd1 ((hBl d).1 ⟨hy', hc'⟩)
          · exfalso
            change ¬K'.data.IsBoundaryVertex (K'.data.vertexOf (K'.data.inv (Sum.inr 1))) at hy'
            change K'.data.colour (K'.data.inv (Sum.inr 1)) = .black at hc'
            rw [hr1] at hy' hc'
            exact hd2 ((hBl _).1 ⟨hy', hc'⟩)
      have hX' : K'.data.IsGeneralizedTripleDiagram hG' X := by
        refine (isGeneralizedTripleDiagram_bivalentRemoval_iff hG' hd' X).2 ?_
        exact ((bivalentInsertionRemovalIso .black hG hdB).isGeneralizedTripleDiagram_iff hG
          (isPlabicGraph_bivalentRemoval hG' hd') X).1 hX
      obtain ⟨K'', h1, h2, h3, h4, h5, h6⟩ := ih K' hcard hr' hw' hbb' hX'
      exact ⟨K'', (MoveEquivalent.of_moveStep hstep).trans h1, h2, h3, h4, h5, h6⟩
    · push Not at hex
      refine ⟨K, MoveEquivalent.refl _ _, hr, hw, hbb, fun d hd => ?_, hX⟩
      by_contra! h
      exact h.2 (hex d hd h.1)

/-- **Normalizing a plabic graph without roundtrips.** Let `K` be a plabic graph without
roundtrips each of whose white internal vertices consists of two or three darts, and let `X` be a
generalized triple diagram of `K`. Then removing the white vertices with two darts, contracting the
edges between two distinct black internal vertices, and inserting a black vertex on every
remaining edge without a black internal end gives a normal plabic graph `N ∼ K` of which `X` is
still a generalized triple diagram. -/
theorem exists_moveEquivalent_isNormal_of_not_hasRoundtrip (K : PlabicGraph b)
    (hr : ¬K.data.HasRoundtrip)
    (hw : ∀ d, ¬K.data.IsBoundaryVertex (K.data.vertexOf d) → K.data.colour d = .white →
      (K.data.vertexOf d).card = 2 ∨ (K.data.vertexOf d).card = 3)
    {H'' : Type*} [Fintype H''] [DecidableEq H''] (X : TripleData H'' b)
    (hX : K.data.IsGeneralizedTripleDiagram K.isPlabicGraph X) :
    ∃ N : PlabicGraph b, MoveEquivalent Set.univ K N ∧ N.data.IsNormal ∧
      N.data.IsGeneralizedTripleDiagram N.isPlabicGraph X := by
  classical
  obtain ⟨K₁, h₁, hr₁, hw₁, hX₁⟩ :=
    exists_moveEquivalent_card_vertexOf_eq_three_of_white X _ K le_rfl hr hw hX
  obtain ⟨K₂, h₂, hr₂, hw₂, hb₂, hX₂⟩ :=
    exists_moveEquivalent_vertexOf_eq_vertexOf_inv_of_black X _ K₁ le_rfl hr₁ hw₁ hX₁
  obtain ⟨N, h₃, hrN, hwN, hbN, heN, hXN⟩ :=
    exists_moveEquivalent_isBlackEnd_or_isBlackEnd_inv X _ K₂ le_rfl hr₂ hw₂ hb₂ hX₂
  refine ⟨N, h₁.trans (h₂.trans h₃), ?_, hXN⟩
  have hG := N.isPlabicGraph
  have hleg : ∀ i, IsBlackEnd N.data (N.data.inv (N.data.leg i)) := fun i =>
    (heN _ (hG.leg_notMem_bdry i)).resolve_left fun h =>
      h.1 (N.data.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))
  refine
    { colour_inv_ne := fun d hd hd' h => ?_
      card_vertexOf_of_white := hwN
      not_isBoundaryVertex_inv_leg := fun i => (hleg i).1
      colour_inv_leg := fun i => (hleg i).2 }
  have hdB : d ∉ N.data.bdry := notMem_bdry_of_mem_vertexOf hd (N.data.self_mem_vertexOf d)
  cases hc : N.data.colour d with
  | black =>
    rw [hc] at h
    exact hrN (hG.hasRoundtrip_of_loop hdB (hbN d hd hd' hc h).symm)
  | white =>
    rw [hc] at h
    rcases heN d hdB with ⟨-, h'⟩ | ⟨-, h'⟩
    · rw [hc] at h'
      exact Shade.noConfusion h'
    · rw [h] at h'
      exact Shade.noConfusion h'

end PlabicGraph

/-! ### The bridge graph -/

section Bridge

open BridgeGraph BridgeSymbol PlabicData

variable {b : ℕ} {s : List (ℤ × ℤ)}

/-- Data of plabic graphs with the same disk map, colours and labelling are equal. -/
private theorem plabicData_ext {H : Type} {G G' : PlabicData H b}
    (h₁ : G.toDiskMap = G'.toDiskMap) (h₂ : G.colour = G'.colour) (h₃ : G.leg = G'.leg) :
    G = G' := by
  cases G
  cases G'
  simp_all

/-- Under `1 ≤ i_t < j_t ≤ b`, the only darts of `G(s, γ)` fixed by the rotation are the lollipop
darts `λ_x`. -/
theorem exists_eq_lam_of_rot_eq_bridgeGraph (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) {d : BridgeDart b s} (h : (bridgeGraph b s γ).rot d = d) :
    ∃ x, d.1 = .lam x := by
  obtain ⟨d, hd⟩ := d
  have h' : d.rotate s = d := congrArg Subtype.val h
  cases d with
  | bdry x => simp at h'
  | bdryRev y => simp at h'
  | lam x => exact ⟨x, rfl⟩
  | dn x u =>
    cases u with
    | zero => simp at h'
    | succ u =>
      simp only [rotate] at h'
      split_ifs at h'
  | up x u =>
    simp only [rotate] at h'
    split_ifs at h'
  | bridge t =>
    obtain ⟨h1, h2, h3⟩ := pair_bounds hs hd.1 hd.2
    have hx : leftEnd s b t = some ⟨((pair s t).1 - 1).toNat, by omega⟩ :=
      leftEnd_eq_some.2 (by simp; omega)
    simp [rotate, hx] at h'
  | bridgeRev t =>
    obtain ⟨h1, h2, h3⟩ := pair_bounds hs hd.1 hd.2
    have hy : rightEnd s b t = some ⟨((pair s t).2 - 1).toNat, by omega⟩ :=
      rightEnd_eq_some.2 ⟨by simp; omega, by simp; omega⟩
    simp only [rotate, hy] at h'
    split_ifs at h'

/-- The colour of a dart of `G(s, γ)` depends on `γ` only at a lollipop dart. -/
private theorem bridgeGraph_colour_congr {γ γ' : Fin b → Shade} (d : BridgeDart b s)
    (h : ∀ x, d.1 = .lam x → γ x = γ' x) :
    (bridgeGraph b s γ).colour d = (bridgeGraph b s γ').colour d := by
  obtain ⟨d, hd⟩ := d
  cases d with
  | lam x => exact h x rfl
  | _ => rfl

/-- The colour of a dart of `G(s, γ)` not fixed by the rotation does not depend on `γ`. -/
private theorem bridgeGraph_colour_of_rot_ne (γ γ' : Fin b → Shade) {d : BridgeDart b s}
    (h : (bridgeGraph b s γ).rot d ≠ d) :
    (bridgeGraph b s γ').colour d = (bridgeGraph b s γ).colour d := by
  refine bridgeGraph_colour_congr d fun x hx => absurd (Subtype.ext ?_) h
  rw [bridgeGraph.rot_val, hx]
  rfl

/-- `G(s, γ)` depends on `γ` only at the lollipop positions. -/
theorem bridgeGraph_eq_of_eqOn_lollipops {γ γ' : Fin b → Shade}
    (h : ∀ x, heights s x = ∅ → γ x = γ' x) : bridgeGraph b s γ = bridgeGraph b s γ' :=
  plabicData_ext rfl (funext fun d => bridgeGraph_colour_congr d fun x hx => h x (by
    have := d.2
    rwa [hx] at this)) rfl

/-- The dart `λ_x` of the lollipop at a lollipop position `x`, as a dart of `G(s, γ)`. -/
private theorem bridgeGraph_inv_leg_of_heights_eq_empty (γ : Fin b → Shade) {x : Fin b}
    (hx : heights s x = ∅) :
    (bridgeGraph b s γ).inv ((bridgeGraph b s γ).leg x) = ⟨.lam x, hx⟩ := by
  apply Subtype.ext
  rw [bridgeGraph.inv_val, bridgeGraph.leg_val, reverse_dn, top_eq_zero_iff.2 hx]
  rfl

/-- The vertex `{λ_x}` of the lollipop at a lollipop position `x`. -/
private theorem bridgeGraph_vertexOf_lam (γ : Fin b → Shade) {x : Fin b}
    (hx : heights s x = ∅) :
    (bridgeGraph b s γ).vertexOf ⟨.lam x, hx⟩ = {⟨.lam x, hx⟩} := by
  refine (eq_singleton_iff_unique_mem.2 ⟨(bridgeGraph b s γ).self_mem_vertexOf _, ?_⟩)
  intro e he
  exact card_le_one.1 (card_vertexOf_le_one_of_rot_eq
    (R := (bridgeGraph b s γ).toRotationSystem) (e := ⟨.lam x, hx⟩) rfl) _ he _
    ((bridgeGraph b s γ).self_mem_vertexOf _)

/-- At a lollipop position `x`, the vertex `v(ḡ_x) = {λ_x}` of `G(s, γ)` is an internal leaf. -/
private theorem isInternalLeaf_bridgeGraph (γ : Fin b → Shade) {x : Fin b}
    (hx : heights s x = ∅) :
    (bridgeGraph b s γ).IsInternalLeaf
      ((bridgeGraph b s γ).vertexOf ((bridgeGraph b s γ).inv ((bridgeGraph b s γ).leg x))) := by
  rw [bridgeGraph_inv_leg_of_heights_eq_empty γ hx]
  refine ⟨(bridgeGraph b s γ).vertexOf_mem_internalVertices.2 ?_, ?_⟩
  · rw [bridgeGraph_vertexOf_lam γ hx]
    rintro ⟨e, he, heB⟩
    rw [mem_singleton.1 he, bridgeGraph.mem_bdry] at heB
    exact heB
  · rw [bridgeGraph_vertexOf_lam γ hx, card_singleton]

/-- **Recolouring a white lollipop of the bridge graph.** At a lollipop position `x` with
`γ(x)` white, `R_x(G(s, γ)) = G(s, γ')` for the colouring `γ'` that is black at `x` and agrees
with `γ` elsewhere. -/
theorem recolourLollipop_bridgeGraph {γ : Fin b → Shade} {x : Fin b} (hx : heights s x = ∅)
    (hγ : γ x = .white) :
    (bridgeGraph b s γ).recolourLollipop x = bridgeGraph b s (Function.update γ x .black) := by
  have hleaf := isInternalLeaf_bridgeGraph γ hx
  have hv : (bridgeGraph b s γ).vertexOf ((bridgeGraph b s γ).inv ((bridgeGraph b s γ).leg x)) =
      {⟨.lam x, hx⟩} := by
    rw [bridgeGraph_inv_leg_of_heights_eq_empty γ hx, bridgeGraph_vertexOf_lam γ hx]
  refine plabicData_ext rfl (funext fun e => ?_) rfl
  by_cases he : e = ⟨.lam x, hx⟩
  · subst he
    rw [colour_recolourLollipop_of_mem hleaf (by rw [hv]; exact mem_singleton_self _)]
    simp [BridgeSymbol.colour, hγ]
  · rw [colour_recolourLollipop_of_notMem fun h => he (by rw [hv] at h; exact mem_singleton.1 h.2)]
    refine bridgeGraph_colour_congr e fun y hy => ?_
    have hyx : y ≠ x := by
      rintro rfl
      exact he (Subtype.ext hy)
    rw [Function.update_of_ne hyx]

/-- **The bridge graph is nearly leafless.** Under `1 ≤ i_t < j_t ≤ b`, every internal leaf of
`G(s, γ)` is a lollipop `{λ_x}`. -/
theorem isNearlyLeafless_bridgeGraph (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (γ : Fin b → Shade) : (bridgeGraph b s γ).IsNearlyLeafless := by
  rintro v ⟨hv, h1⟩
  obtain ⟨d, rfl⟩ :=
    (bridgeGraph b s γ).mem_vertices.1 ((bridgeGraph b s γ).mem_internalVertices.1 hv).1
  have hrot : (bridgeGraph b s γ).rot d = d :=
    card_le_one.1 h1.le _ ((bridgeGraph b s γ).rot_mem_vertexOf d) _
      ((bridgeGraph b s γ).self_mem_vertexOf d)
  obtain ⟨x, hx⟩ := exists_eq_lam_of_rot_eq_bridgeGraph hs γ hrot
  refine ⟨x, ⟨hv, h1⟩, d, (bridgeGraph b s γ).self_mem_vertexOf d, ?_⟩
  have : (bridgeGraph b s γ).inv d = (bridgeGraph b s γ).leg x := by
    apply Subtype.ext
    rw [bridgeGraph.inv_val, hx, bridgeGraph.leg_val]
    rfl
  rw [this]
  exact (bridgeGraph b s γ).self_mem_vertexOf _

/-- The empty white datum `∅` is a white datum of `G(s, γ)`, so the strand diagram
`X°(G(s, γ), ∅)` is defined. -/
theorem isWhiteDatum_empty_bridgeGraph (γ : Fin b → Shade) :
    (bridgeGraph b s γ).IsWhiteDatum fun _ => ∅ :=
  isWhiteDatum_empty fun _ hw =>
    (exists_eq_of_isCrossing_bridgeGraph γ hw).choose_spec.choose_spec.2.2.2.2

/-- The bridge graph `G(s, γ)` as a bundled plabic graph. -/
def bridgePlabicGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) : PlabicGraph b :=
  ⟨BridgeDart b s, bridgeGraph b s γ, isPlabicGraph_bridgeGraph hb hs hn γ⟩

/-- The underlying plabic data of `bridgePlabicGraph hb hs hn γ` is the bridge graph `G(s, γ)`. -/
@[simp]
theorem data_bridgePlabicGraph (hb : 1 ≤ b) (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b)
    (hn : IsNestedPairSequence s) (γ : Fin b → Shade) :
    (bridgePlabicGraph hb hs hn γ).data = bridgeGraph b s γ :=
  rfl

/-- Bridge graphs with equal data are equal as bundled plabic graphs. -/
private theorem bridgePlabicGraph_congr (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    {γ γ' : Fin b → Shade} (h : bridgeGraph b s γ = bridgeGraph b s γ') :
    bridgePlabicGraph hb hs hn γ = bridgePlabicGraph hb hs hn γ' := by
  unfold bridgePlabicGraph
  congr 1

/-- **Stage A**: recolouring the white lollipops of `G(s, γ)` one at a time gives `G(s, γ₀)` for
the colouring `γ₀` that is black everywhere. -/
private theorem reflTransGen_bridgePlabicGraph (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    (γ : Fin b → Shade) :
    Relation.ReflTransGen PlabicGraph.NormalizationStep (bridgePlabicGraph hb hs hn γ)
      (bridgePlabicGraph hb hs hn fun _ => .black) := by
  classical
  have key : ∀ S : Finset (Fin b), Relation.ReflTransGen PlabicGraph.NormalizationStep
      (bridgePlabicGraph hb hs hn γ)
      (bridgePlabicGraph hb hs hn fun x => if x ∈ S then .black else γ x) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [notMem_empty, if_false]
      exact .refl
    | insert i S hi ih =>
      refine ih.trans ?_
      set γS : Fin b → Shade := fun x => if x ∈ S then .black else γ x
      have hupd : (fun x => if x ∈ insert i S then Shade.black else γ x) =
          Function.update γS i .black := by
        funext x
        by_cases hxi : x = i
        · subst hxi
          simp
        · simp [γS, hxi]
      rw [hupd]
      by_cases hc : heights s i = ∅ ∧ γ i = .white
      · have hγi : γS i = .white := by simp [γS, hi, hc.2]
        refine .single (Or.inr ⟨isNearlyLeafless_bridgeGraph hs γS, i, ?_⟩)
        change _ = (⟨BridgeDart b s, (bridgeGraph b s γS).recolourLollipop i, _⟩ : PlabicGraph b)
        unfold bridgePlabicGraph
        congr 1
        exact (recolourLollipop_bridgeGraph (s := s) hc.1 hγi).symm
      · rw [bridgePlabicGraph_congr hb hs hn (bridgeGraph_eq_of_eqOn_lollipops (γ := γS)
          (γ' := Function.update γS i .black) fun x hx => ?_)]
        by_cases hxi : x = i
        · subst hxi
          have : γ x = .black := by
            cases h : γ x
            · exact absurd ⟨hx, h⟩ hc
            · rfl
          simp [γS, hi, this]
        · rw [Function.update_of_ne hxi]
  simpa only [mem_univ, if_true] using key univ

/-- Every white internal vertex of `G(s, γ₀)`, for the colouring `γ₀` black everywhere, consists
of two or three darts. -/
private theorem card_vertexOf_bridgeGraph_black (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    (d : BridgeDart b s)
    (hd : ¬(bridgeGraph b s fun _ => .black).IsBoundaryVertex
      ((bridgeGraph b s fun _ => .black).vertexOf d))
    (hc : (bridgeGraph b s fun _ => .black).colour d = .white) :
    ((bridgeGraph b s fun _ => .black).vertexOf d).card = 2 ∨
      ((bridgeGraph b s fun _ => .black).vertexOf d).card = 3 := by
  set G := bridgeGraph b s fun _ => .black
  have hG : G.IsPlabicGraph := isPlabicGraph_bridgeGraph hb hs hn _
  have hpos : 0 < (G.vertexOf d).card := card_pos.2 ⟨d, G.self_mem_vertexOf d⟩
  by_cases h1 : (G.vertexOf d).card = 1
  · exfalso
    have hrot : G.rot d = d :=
      card_le_one.1 h1.le _ (G.rot_mem_vertexOf d) _ (G.self_mem_vertexOf d)
    obtain ⟨x, hx⟩ := exists_eq_lam_of_rot_eq_bridgeGraph hs _ hrot
    have : G.colour d = .black := by
      rw [bridgeGraph.colour_apply, hx]
      rfl
    rw [this] at hc
    exact Shade.noConfusion hc
  by_cases h3 : 3 ≤ (G.vertexOf d).card
  · have hcr : G.IsCrossing (G.vertexOf d) :=
      ⟨G.vertexOf_mem_internalVertices.2 hd, fun e he =>
        (colour_eq_of_sameCycle hG hd ((G.mem_vertexOf).1 he)).trans hc, h3⟩
    exact Or.inr (exists_eq_of_isCrossing_bridgeGraph _ hcr).choose_spec.choose_spec.2.2.2.2
  · omega

/-- Every trip of a plabic graph without roundtrips contains a leg, an initial dart. -/
private theorem exists_isInitial_mem_trip_of_not_hasRoundtrip {H : Type} [Fintype H]
    [DecidableEq H] {G : PlabicData H b} (hG : G.IsPlabicGraph) (hr : ¬G.HasRoundtrip) {d : H}
    (hd : d ∉ G.bdry) : ∃ e ∈ G.trip d, G.IsInitial e := by
  rw [hasRoundtrip_iff] at hr
  push Not at hr
  obtain ⟨n, i, hi⟩ := hr d hd
  refine ⟨_, G.iterate_mem_trip d n, ?_, Or.inr ⟨i, hi⟩⟩
  rw [← hi]
  exact hG.leg_notMem_bdry i

/-- Let `b ≥ 1`, let `s` be a nested sequence of pairs with `1 ≤ i_t < j_t ≤ b`, and
`γ : [1, b] → Shade`. Then `G(s, γ)` has a normalization `N` such that the triple diagram `X(N)`
is isomorphic to the strand diagram `X°(G(s, γ), ∅)`. -/
@[cluster_algebras "lem_bridge_normalization"]
theorem exists_isNormalization_bridgeGraph (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    (γ : Fin b → Shade) :
    ∃ (N : PlabicGraph b) (hN : (bridgePlabicGraph hb hs hn γ).IsNormalization N),
      (N.data.tripleOfNormal
        (IsNormalPlabicGraph.mk N.isPlabicGraph hN.1).isNormalPlabicPregraph).Isomorphic
        ((bridgeGraph b s γ).strandDiagram (isPlabicGraph_bridgeGraph hb hs hn γ)
          (isWhiteDatum_empty_bridgeGraph γ)) := by
  set γ₀ : Fin b → Shade := fun _ => .black
  have hG := isPlabicGraph_bridgeGraph hb hs hn γ
  have hG₀ := isPlabicGraph_bridgeGraph hb hs hn γ₀
  have hD := isWhiteDatum_empty_bridgeGraph (s := s) γ
  have hD₀ := isWhiteDatum_empty_bridgeGraph (s := s) γ₀
  set X := (bridgeGraph b s γ).strandDiagram hG hD
  -- Stage A: the recolourings keep `X°`
  have hcol : ∀ d, (bridgeGraph b s γ₀).rot d ≠ d →
      (bridgeGraph b s γ).colour d = (bridgeGraph b s γ₀).colour d :=
    fun d h => bridgeGraph_colour_of_rot_ne γ₀ γ h
  have hXG₀ : (bridgeGraph b s γ₀).IsGeneralizedTripleDiagram hG₀ X :=
    ⟨isPreTripleDiagram_strandDiagram hG hD,
      fun d hd => exists_isInitial_mem_trip_of_not_hasRoundtrip hG₀
        (not_hasRoundtrip_bridgeGraph hs γ₀) hd,
      fun _ => ∅, hD₀,
      strandDiagram_isomorphic_of_eq_toDiskMap (G := bridgeGraph b s γ₀)
        (G' := bridgeGraph b s γ) rfl rfl (isCrossing_iff_of_colour_eq rfl hcol)
        (tripMap_eq_of_colour_eq rfl hcol) hG₀ hG hD₀ hD⟩
  -- Stages B, C and D
  obtain ⟨N, hKN, hNn, hXN⟩ :=
    PlabicGraph.exists_moveEquivalent_isNormal_of_not_hasRoundtrip
      (bridgePlabicGraph hb hs hn γ₀) (not_hasRoundtrip_bridgeGraph hs γ₀)
      (card_vertexOf_bridgeGraph_black hb hs hn) X hXG₀
  have hNorm : (bridgePlabicGraph hb hs hn γ).IsNormalization N :=
    ⟨hNn, (reflTransGen_bridgePlabicGraph hb hs hn γ).trans
      (Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) hKN)⟩
  refine ⟨N, hNorm, ?_⟩
  -- `X(N)` and `X°` are generalized triple diagrams of `N`
  have hNP : N.data.IsNormalPlabicGraph := ⟨N.isPlabicGraph, hNn⟩
  obtain ⟨-, -, D₁, hD₁, θ₁⟩ := hNP.isGeneralizedTripleDiagram_tripleOfNormal
  obtain ⟨-, -, D₂, hD₂, θ₂⟩ := hXN
  have h3 : ∀ w, N.data.IsCrossing w → w.card = 3 := by
    intro w hw
    obtain ⟨a, rfl⟩ := N.data.mem_vertices.1 (N.data.mem_internalVertices.1 hw.1).1
    exact hNn.card_vertexOf_of_white a (N.data.mem_internalVertices.1 hw.1).2
      (hw.2.1 a (N.data.self_mem_vertexOf a))
  have hagree : ∀ w, N.data.IsCrossing w → D₁ w = D₂ w := fun w hw => by
    rw [hD₁.eq_empty hw (h3 w hw), hD₂.eq_empty hw (h3 w hw)]
  exact TripleData.Isomorphic.trans _ θ₁ (TripleData.Isomorphic.trans _
    (strandDiagram_isomorphic_of_eqOn_crossings N.isPlabicGraph hD₂ hD₁ hagree)
    (TripleData.Isomorphic.symm _ θ₂))

/-- An equivalence carrying a family of finsets to another carries the set of its members to the
other's, so the two have the same number of distinct members. -/
theorem card_image_univ_eq_of_map_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (F : α → Finset α) (F' : β → Finset β)
    (h : ∀ d, (F d).map e.toEmbedding = F' (e d)) :
    (univ.image F).card = (univ.image F').card := by
  have : (univ.image F').image (Finset.map e.symm.toEmbedding) = univ.image F := by
    ext s
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨e.symm y, ?_⟩
      rw [← Finset.map_injective e.toEmbedding |>.eq_iff, h, Finset.map_map]
      simp
    · rintro ⟨x, rfl⟩
      refine ⟨F' (e x), ⟨_, rfl⟩, ?_⟩
      rw [← h, Finset.map_map]
      simp
  rw [← this, card_image_of_injective _ (Finset.map_injective _)]

/-- A pre-triple diagram isomorphic to a triple diagram is a triple diagram. -/
private theorem isTripleDiagram_of_iso {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {Y : TripleData α b} {X' : TripleData β b} (θ : Y.Iso X')
    (hY : Y.IsPreTripleDiagram) (hX' : X'.IsTripleDiagram) : Y.IsTripleDiagram := by
  have hv : ∀ d, (Y.vertexOf d).map θ.toEquiv.toEmbedding = X'.vertexOf (θ.toEquiv d) :=
    PlabicData.map_vertexOf_of_semiconj θ.toEquiv θ.map_rot
  have hf : ∀ d, (Y.faceOf d).map θ.toEquiv.toEmbedding = X'.faceOf (θ.toEquiv d) :=
    PlabicData.map_vertexOf_of_semiconj (R := ⟨Y.inv, Y.facePerm⟩)
      (R' := ⟨X'.inv, X'.facePerm⟩) θ.toEquiv θ.map_facePerm
  have he : ∀ d, (Y.edgeOf d).map θ.toEquiv.toEmbedding = X'.edgeOf (θ.toEquiv d) := by
    intro d
    simp [RotationSystem.edgeOf, θ.map_inv]
  refine hY.isTripleDiagram (fun d e => ?_) ?_
  · refine (RotationSystem.reach_iff_exists_mem_closure _).1 ?_
    have key : ∀ a c, X'.Reach a c → Y.Reach (θ.toEquiv.symm a) (θ.toEquiv.symm c) := by
      intro a c h
      induction h with
      | refl => exact .refl _
      | rot _ ih =>
        rw [θ.symm_map_rot]
        exact ih.rot
      | inv _ ih =>
        rw [θ.symm_map_inv]
        exact ih.inv
    simpa using key _ _ (hX'.toIsDiskMap.toIsConnected.reach (θ.toEquiv d) (θ.toEquiv e))
  · have h1 : Y.vertices.card = X'.vertices.card :=
      card_image_univ_eq_of_map_equiv θ.toEquiv _ _ hv
    have h2 : Y.edges.card = X'.edges.card :=
      card_image_univ_eq_of_map_equiv θ.toEquiv _ _ he
    have h3 : Y.faceOrbits.card = X'.faceOrbits.card :=
      card_image_univ_eq_of_map_equiv θ.toEquiv _ _ hf
    rw [h1, h2, h3]
    exact hX'.euler

/-- Let `b ≥ 1`, let `s` be a nested sequence of pairs with `1 ≤ i_t < j_t ≤ b`, and
`γ : [1, b] → Shade`. Then `X°(G(s, γ), ∅)` is a triple diagram. -/
@[cluster_algebras "lem_bridge_strand_diagram_triple"]
theorem isTripleDiagram_strandDiagram_bridgeGraph (hb : 1 ≤ b)
    (hs : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b) (hn : IsNestedPairSequence s)
    (γ : Fin b → Shade) :
    ((bridgeGraph b s γ).strandDiagram (isPlabicGraph_bridgeGraph hb hs hn γ)
      (isWhiteDatum_empty_bridgeGraph γ)).IsTripleDiagram := by
  obtain ⟨N, hN, hθ⟩ := exists_isNormalization_bridgeGraph hb hs hn γ
  obtain ⟨θ⟩ := TripleData.Isomorphic.symm _ hθ
  exact isTripleDiagram_of_iso θ (isPreTripleDiagram_strandDiagram _ _)
    (IsNormalPlabicGraph.mk N.isPlabicGraph hN.1).isTripleDiagram_tripleOfNormal

end Bridge

end ClusterAlgebras
