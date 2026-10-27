/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.StrandDiagram
public import ClusterAlgebras.Plabic.CornerMaps
public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.NormalPlabic
public import ClusterAlgebras.Plabic.TripRuns
public import ClusterAlgebras.Plabic.TripleMoves

/-!
# Strands follow trips

Let `G` be a plabic graph each of whose crossings (white internal vertices with at least three
darts) consists of exactly three darts. The polygon of corners of such a crossing is a triangle,
which has no diagonal; so the empty family `∅` is the only white datum of `G`, and the only
triangle of `∅` at a crossing `w` is `w` itself. The triple point of `w` in the strand diagram
`X°(G, ∅)` is the set `x_w` of the six symbols `x⁺_a`, `x⁻_{ā}`, `a ∈ w`, with the rotation
`x⁺_a ↦ x⁻_{ā} ↦ x⁺_{σ a}`, and `w ↦ x_w` is a bijection from the crossings onto the triple
points.

Reading these cycles, a strand path of `X°(G, ∅)` between triple points is a stretch
`T(y), …, Tⁿ(y)` of a trip of `G` between two arrivals at crossings, passing no leg, and
conversely. So `X°(G, ∅)` has a monogon at `x_w` exactly when a trip of `G` arrives twice at `w`.
In a normal plabic graph, a trip arriving twice at a white vertex has an essential
self-intersection. Finally, badgons are carried along isomorphisms of triple diagrams.

## Main definitions

* `ClusterAlgebras.PlabicData.crossingTriplePoint`: the triple point `x_w` of a crossing.

## Main results

* `ClusterAlgebras.PlabicData.isWhiteDatum_empty`,
  `ClusterAlgebras.PlabicData.IsWhiteDatum.eq_empty`: `∅` is the only white datum of a graph with
  trivalent crossings.
* `ClusterAlgebras.PlabicData.strandRotSym_xPlus`,
  `ClusterAlgebras.PlabicData.strandRotSym_xMinus_inv`,
  `ClusterAlgebras.PlabicData.strandDiagram_vertexOf_of_eq_xPlus`: the triple point of a trivalent
  crossing is the cycle `(x⁺_a, x⁻_{ā}, x⁺_{σ a}, …)`.
* `ClusterAlgebras.PlabicData.bijOn_crossingTriplePoint`: the triple points of `X°(G, ∅)` are the
  `x_w`.
* `ClusterAlgebras.PlabicData.exists_tripMap_of_isStrandPath`: a strand path follows a trip.
* `ClusterAlgebras.PlabicData.exists_isStrandPath_of_tripMap`: a stretch of a trip is a strand
  path.
* `ClusterAlgebras.PlabicData.exists_isMonogon_iff`: monogons are trips passing a crossing twice.
* `ClusterAlgebras.TripleData.Iso.hasBadgon`: badgons are invariant under isomorphism.
* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.exists_isEssentialSelfIntersection`: a trip
  visiting a white vertex twice in a normal graph gives an essential self-intersection.

## Implementation notes

* The hypothesis that every crossing consists of exactly three darts is
  `∀ w, G.IsCrossing w → w.card = 3`, and the white datum `∅` is the constant family
  `fun _ => ∅`.
* The triple point `x_w` is defined for every white datum `D` as a set of darts of `X°(G, D)`:
  the symbols `x⁺_a` (`a ∈ w`) and `x⁻_{ā}` are darts of every `X°(G, D)`.
* The cycle `(x⁺_a, x⁻_{ā}, x⁺_{σ a}, x⁻_{\overline{σ a}}, x⁺_{σ² a}, x⁻_{\overline{σ² a}})` is
  recorded by the two steps `σ°(x⁺_a) = x⁻_{ā}` and `σ°(x⁻_{ā}) = x⁺_{σ a}` for every `a ∈ w`, on
  symbols, together with the fact that the cycle of `x⁺_a` is `x_w`.
* A strand path `(e₁, …, e_m)` is a list; `e₁ = x⁺_{T(y)}` and `ē_m = x⁻_{Tⁿ(y)}` are read on its
  head and last entry. A monogon with vertex `x_w` is a monogon `P` with `pathStart P = x_w`.
* The hypotheses that `X°(G, ∅)` be a triple diagram in `exists_tripMap_of_isStrandPath`,
  `exists_isStrandPath_of_tripMap` and `exists_isMonogon_iff`, and that `y ∉ B` in
  `exists_isStrandPath_of_tripMap`, are not used by the proofs and are not assumed.
* A white vertex `w` is an internal vertex all of whose darts are white.
* `TripleData.Iso.hasBadgon` is stated for isomorphisms of the data of (pre-)triple diagrams, which
  include the isomorphisms of triple diagrams.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset StrandSymbol

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-- Dropping the first dart of a strand path of length at least two leaves a strand path. -/
theorem IsStrandPath.of_cons_cons {e e' : H} {P : List H}
    (hP : X.IsStrandPath (e :: e' :: P)) : X.IsStrandPath (e' :: P) where
  ne_nil := List.cons_ne_nil _ _
  notMem_bdry x hx := hP.notMem_bdry x (List.mem_cons_of_mem _ hx)
  isOut_eq_true x hx := hP.isOut_eq_true x (List.mem_cons_of_mem _ hx)
  isChain := (List.isChain_cons_cons.1 hP.isChain).2

/-- Prepending an `out` dart outside `B` with a strand step to a strand path gives a strand
path. -/
theorem IsStrandPath.cons_cons {e e' : H} {P : List H} (hP : X.IsStrandPath (e' :: P))
    (hB : e ∉ X.bdry) (ho : X.isOut e = true) (hstep : X.StrandStep e e') :
    X.IsStrandPath (e :: e' :: P) where
  ne_nil := List.cons_ne_nil _ _
  notMem_bdry := List.forall_mem_cons.2 ⟨hB, hP.notMem_bdry⟩
  isOut_eq_true := List.forall_mem_cons.2 ⟨ho, hP.isOut_eq_true⟩
  isChain := List.IsChain.cons_cons hstep hP.isChain

end TripleData

/-! ### The triangle -/

/-- The triangle has no diagonal. -/
private theorem not_isDiagonal_three (e : Sym2 (ZMod 3)) : ¬IsDiagonal e := by
  revert e
  unfold IsDiagonal IsSegment IsSide
  decide

/-- The empty set of diagonals is a triangulation of the triangle. -/
private theorem isTriangulation_empty_three : IsTriangulation (∅ : Finset (Sym2 (ZMod 3))) where
  isDiagonal := by simp
  noncrossing := by simp
  maximal e he _ := absurd he (not_isDiagonal_three e)

/-- The whole triangle is a triangle of the empty triangulation. -/
private theorem isTriangle_empty_three :
    IsTriangle (∅ : Finset (Sym2 (ZMod 3))) (univ : Finset (ZMod 3)) := by
  unfold IsTriangle
  simp only [mem_segments, notMem_empty, false_or]
  unfold IsSide
  decide

namespace RotationSystem

variable {H : Type*} [DecidableEq H]

private theorem cornerPullback_empty {m : ℕ} [NeZero m] (l : ZMod m → H) :
    cornerPullback l (∅ : Finset (Sym2 H)) = ∅ := by
  ext e
  simp [mem_cornerPullback]

end RotationSystem

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### The white datum of a graph with trivalent crossings -/

/-- The labelling `i ↦ σ^{-i}(a)` of a vertex with three darts. -/
private theorem isCornerLabelling_three {a : H} (ha : (G.vertexOf a).card = 3) :
    G.IsCornerLabelling (G.vertexOf a) fun i : ZMod 3 => (G.rot.symm ^ i.val) a :=
  RotationSystem.isCornerLabelling_rot_symm_pow a ha

/-- **The white datum of a graph with trivalent crossings**, first part: if every crossing of `G`
consists of exactly three darts, the family `∅` is a white datum. -/
@[cluster_algebras "lem_trivalent_white_datum"]
theorem isWhiteDatum_empty (htri : ∀ w, G.IsCrossing w → w.card = 3) :
    G.IsWhiteDatum fun _ => ∅ := by
  intro w hw
  obtain ⟨a, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw.1).1
  refine ⟨by simp, 3, inferInstance, _, isCornerLabelling_three (htri _ hw), ?_⟩
  rw [RotationSystem.cornerPullback_empty]
  exact isTriangulation_empty_three

/-- **The white datum of a graph with trivalent crossings**, second part: a white datum assigns `∅`
to every crossing consisting of three darts. So if every crossing of `G` consists of exactly three
darts, `∅` is the only white datum. -/
@[cluster_algebras "lem_trivalent_white_datum"]
theorem IsWhiteDatum.eq_empty {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)
    {w : Finset H} (hw : G.IsCrossing w) (h3 : w.card = 3) : D w = ∅ := by
  obtain ⟨hDw, m, _, l, hl, hT⟩ := hD w hw
  obtain rfl : m = 3 := hl.card_eq.symm.trans h3
  refine eq_empty_of_forall_notMem fun e he => ?_
  induction e using Sym2.ind with | _ x y => ?_
  obtain ⟨-, hxw⟩ := hDw _ he
  obtain ⟨i, rfl⟩ := hl.exists_eq (hxw _ (Sym2.mem_mk_left _ _))
  obtain ⟨j, rfl⟩ := hl.exists_eq (hxw _ (Sym2.mem_mk_right _ _))
  have hij : s(i, j) ∈ RotationSystem.cornerPullback l (D w) :=
    RotationSystem.mem_cornerPullback.2 (by simpa using he)
  exact not_isDiagonal_three _ (hT.isDiagonal _ hij)

/-! ### The triple point of a crossing -/

variable (G) in
/-- **The triple point of a crossing** `w`: the set `x_w` of the symbols `x⁺_a` and `x⁻_{ā}`,
`a ∈ w`, as darts of the strand diagram `X°(G, D)`. -/
@[cluster_algebras "def_crossing_triple_point"]
noncomputable def crossingTriplePoint (D : Finset H → Finset (Sym2 H)) (w : Finset H) :
    Finset (G.StrandDart D) :=
  univ.filter fun a => ∃ p ∈ w, a.1 = xPlus p ∨ a.1 = xMinus (G.inv p)

/-- A dart of `X°(G, D)` lies in `crossingTriplePoint G D w` if and only if it is `xPlus p` or
`xMinus (G.inv p)` for some `p ∈ w`. -/
theorem mem_crossingTriplePoint {D : Finset H → Finset (Sym2 H)} {w : Finset H}
    {a : G.StrandDart D} :
    a ∈ G.crossingTriplePoint D w ↔ ∃ p ∈ w, a.1 = xPlus p ∨ a.1 = xMinus (G.inv p) := by
  simp [crossingTriplePoint]

/-- The dart `xPlus p` lies in `crossingTriplePoint G D w` if and only if `p ∈ w`. -/
theorem mem_crossingTriplePoint_of_eq_xPlus {D : Finset H → Finset (Sym2 H)} {w : Finset H}
    {e : G.StrandDart D} {p : H} (he : e.1 = xPlus p) : e ∈ G.crossingTriplePoint D w ↔ p ∈ w := by
  rw [mem_crossingTriplePoint, he]
  refine ⟨fun ⟨q, hq, h⟩ => ?_, fun hp => ⟨p, hp, Or.inl rfl⟩⟩
  rcases h with h | h
  · rwa [xPlus.inj h]
  · cases h

/-- In a plabic graph, the dart `xMinus t` lies in `crossingTriplePoint G D w` if and only if
`G.inv t ∈ w`. -/
theorem mem_crossingTriplePoint_of_eq_xMinus (hG : G.IsPlabicGraph)
    {D : Finset H → Finset (Sym2 H)} {w : Finset H} {e : G.StrandDart D} {t : H}
    (he : e.1 = xMinus t) : e ∈ G.crossingTriplePoint D w ↔ G.inv t ∈ w := by
  rw [mem_crossingTriplePoint, he]
  refine ⟨fun ⟨q, hq, h⟩ => ?_, fun ht => ⟨G.inv t, ht, Or.inr (by rw [hG.inv_involutive])⟩⟩
  rcases h with h | h
  · cases h
  · rwa [xMinus.inj h, hG.inv_involutive]

private theorem isCrossing_vertexOf {w : Finset H} (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) :
    G.IsCrossing (G.vertexOf a) := by
  rwa [← hw.eq_vertexOf ha]

/-! ### The triple point of a trivalent crossing -/

section Trivalent

variable (htri : ∀ w, G.IsCrossing w → w.card = 3)

include htri

/-- The darts of a trivalent crossing: `σ³ = 1`. -/
private theorem rot_symm_rot_symm_rot_symm {w : Finset H} (hw : G.IsCrossing w) {a : H}
    (ha : a ∈ w) : G.rot.symm (G.rot.symm (G.rot.symm a)) = a := by
  have h := RotationSystem.rot_symm_pow_card_vertexOf (R := G.toRotationSystem) a
  rw [← hw.eq_vertexOf ha, htri w hw] at h
  simpa [pow_succ, Equiv.Perm.mul_apply] using h

/-- At a trivalent crossing, `σ a = σ⁻²(a)`. -/
private theorem rot_eq_rot_symm_rot_symm {w : Finset H} (hw : G.IsCrossing w) {a : H}
    (ha : a ∈ w) : G.rot a = G.rot.symm (G.rot.symm a) := by
  conv_lhs => rw [← rot_symm_rot_symm_rot_symm htri hw ha]
  simp

/-- A trivalent crossing is a triangle of the white datum `∅`. -/
theorem isDatumTriangle_empty {w : Finset H} (hw : G.IsCrossing w) :
    G.IsDatumTriangle (fun _ => ∅) w := by
  refine ⟨w, hw, ?_⟩
  change G.IsCornerTriangle w ∅ w
  obtain ⟨a, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw.1).1
  have hl := isCornerLabelling_three (htri _ hw)
  have himage : (univ : Finset (ZMod 3)).image (fun i : ZMod 3 => (G.rot.symm ^ i.val) a) =
      G.vertexOf a := by
    ext x
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ hl.mem i, hl.exists_eq⟩
  have h := (hl.isCornerTriangle_image_iff (D := ∅) univ).2
    (by simpa only [RotationSystem.cornerPullback_empty] using isTriangle_empty_three)
  rwa [himage] at h

/-- A triangle of the white datum `∅` is a crossing. -/
theorem IsDatumTriangle.isCrossing_of_empty {τ : Finset H}
    (hτ : G.IsDatumTriangle (fun _ => ∅) τ) : G.IsCrossing τ := by
  obtain ⟨w, hw, ht⟩ := hτ
  obtain rfl : τ = w := eq_of_subset_of_card_le ht.1 (by rw [ht.2.1, htri w hw])
  exact hw

omit htri in
private theorem rot_symm_mem {w : Finset H} (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) :
    G.rot.symm a ∈ w := by
  rw [hw.eq_vertexOf ha]
  exact G.rot_symm_mem_vertexOf a

omit htri in
private theorem rot_mem {w : Finset H} (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) :
    G.rot a ∈ w := by
  rw [hw.eq_vertexOf ha]
  exact G.rot_mem_vertexOf a

/-- At a trivalent crossing, `σ (σ a) = σ⁻¹ a`. -/
private theorem rot_rot_eq_rot_symm {w : Finset H} (hw : G.IsCrossing w) {a : H}
    (ha : a ∈ w) : G.rot (G.rot a) = G.rot.symm a := by
  conv_lhs => rw [← rot_symm_rot_symm_rot_symm htri hw ha]
  simp

/-- At a trivalent crossing `w`, the clockwise successor of `a` in the triangle `w` of `∅` is
`σ⁻¹ a`. -/
private theorem cornerNext_eq {w : Finset H} (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) :
    G.cornerNext w a = G.rot.symm a :=
  (isWhiteDatum_empty htri).cornerNext_eq_rot_symm (isDatumTriangle_empty htri hw) ha
    (rot_symm_mem hw ha)

/-- At a trivalent crossing `w`, the first symbol of the pair at `a` is `x⁺_a`. -/
theorem pairOut_eq_xPlus {w : Finset H} (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) :
    G.pairOut w a = xPlus a := by
  rw [pairOut, if_pos (cornerNext_eq htri hw ha)]

/-- At a trivalent crossing `w`, the second symbol of the pair at `a` is `x⁻_{ā}`. -/
theorem pairIn_eq_xMinus {w : Finset H} (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) :
    G.pairIn w a = xMinus (G.inv a) := by
  rw [pairIn, if_pos (cornerNext_eq htri hw ha)]

/-- At a trivalent crossing, `x_w` is the triple point of the triangle `w` of `∅`. -/
theorem crossingTriplePoint_eq_strandTriplePoint {w : Finset H} (hw : G.IsCrossing w) :
    G.crossingTriplePoint (fun _ => ∅) w = G.strandTriplePoint (fun _ => ∅) w := by
  ext x
  rw [mem_crossingTriplePoint]
  simp only [strandTriplePoint, mem_filter, mem_univ, true_and]
  refine ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, ?_⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, ?_⟩⟩
  · rwa [pairOut_eq_xPlus htri hw hp, pairIn_eq_xMinus htri hw hp]
  · rwa [pairOut_eq_xPlus htri hw hp, pairIn_eq_xMinus htri hw hp] at h

omit htri in
/-- **The triple point of a trivalent crossing**: for a dart `a` at a crossing,
`σ°(x⁺_a) = x⁻_{ā}`. -/
@[cluster_algebras "lem_trivalent_crossing_cycle"]
theorem strandRotSym_xPlus (hG : G.IsPlabicGraph) (D : Finset H → Finset (Sym2 H)) {a : H}
    (ha : G.IsCrossing (G.vertexOf a)) : G.strandRotSym D (xPlus a) = xMinus (G.inv a) := by
  rw [strandRotSym, dif_neg (hG.not_isLeg_of_isCrossing ha)]

/-- **The triple point of a trivalent crossing**: for a dart `a` at a crossing `w` with three
darts, `σ°(x⁻_{ā}) = x⁺_{σ a}` in `X°(G, ∅)`. -/
@[cluster_algebras "lem_trivalent_crossing_cycle"]
theorem strandRotSym_xMinus_inv (hG : G.IsPlabicGraph) {w : Finset H} (hw : G.IsCrossing w)
    {a : H} (ha : a ∈ w) :
    G.strandRotSym (fun _ => ∅) (xMinus (G.inv a)) = xPlus (G.rot a) := by
  have h := strandRotSym_pairIn hG (isWhiteDatum_empty htri) (isDatumTriangle_empty htri hw) ha
  have ha' := rot_symm_mem hw ha
  rwa [pairIn_eq_xMinus htri hw ha, cornerNext_eq htri hw ha, cornerNext_eq htri hw ha',
    pairOut_eq_xPlus htri hw (rot_symm_mem hw ha'), ← rot_eq_rot_symm_rot_symm htri hw ha] at h

/-- The dart `x⁺_a`, `a ∈ w`, of `X°(G, ∅)` lies at the triple point `x_w` of the trivalent
crossing `w`. -/
@[cluster_algebras "lem_trivalent_crossing_cycle"]
theorem strandDiagram_vertexOf_of_eq_xPlus (hG : G.IsPlabicGraph) {w : Finset H}
    (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) {e : G.StrandDart fun _ => ∅}
    (he : e.1 = xPlus a) :
    (G.strandDiagram hG (isWhiteDatum_empty htri)).vertexOf e =
      G.crossingTriplePoint (fun _ => ∅) w := by
  have hτ := isDatumTriangle_empty htri hw
  have e' : e = ⟨G.pairOut w a, isStrandSymbol_pairOut (isWhiteDatum_empty htri) hτ ha⟩ :=
    Subtype.ext (he.trans (pairOut_eq_xPlus htri hw ha).symm)
  rw [e', strandDiagram_vertexOf_pairOut hG _ hτ ha,
    crossingTriplePoint_eq_strandTriplePoint htri hw]

/-- The dart `x⁻_{ā}`, `a ∈ w`, of `X°(G, ∅)` lies at `x_w`. -/
theorem strandDiagram_vertexOf_of_eq_xMinus (hG : G.IsPlabicGraph) {w : Finset H}
    (hw : G.IsCrossing w) {a : H} (ha : a ∈ w) {e : G.StrandDart fun _ => ∅}
    (he : e.1 = xMinus (G.inv a)) :
    (G.strandDiagram hG (isWhiteDatum_empty htri)).vertexOf e =
      G.crossingTriplePoint (fun _ => ∅) w := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  have hτ := isDatumTriangle_empty htri hw
  have ha0 : G.IsStrandSymbol (fun _ => ∅) (xPlus a) :=
    (⟨hτ.notMem_bdry ha, Or.inl (isCrossing_vertexOf hw ha)⟩ : G.IsInitial a)
  have e' : e = X.rot ⟨xPlus a, ha0⟩ := by
    refine Subtype.ext ?_
    rw [he, strandDiagram_rot_apply,
      strandRotSym_xPlus hG _ (isCrossing_vertexOf hw ha)]
  rw [e', X.vertexOf_rot, strandDiagram_vertexOf_of_eq_xPlus htri hG hw ha rfl]

/-- The triple point `x_w` of a trivalent crossing is a triple point of `X°(G, ∅)`. -/
theorem crossingTriplePoint_mem_internalVertices (hG : G.IsPlabicGraph) {w : Finset H}
    (hw : G.IsCrossing w) :
    G.crossingTriplePoint (fun _ => ∅) w ∈
      (G.strandDiagram hG (isWhiteDatum_empty htri)).internalVertices :=
  (mem_strandDiagram_internalVertices hG _).2
    ⟨w, isDatumTriangle_empty htri hw, crossingTriplePoint_eq_strandTriplePoint htri hw⟩

/-- **Triple points of a graph with trivalent crossings**: if every crossing of `G` consists of
exactly three darts, `w ↦ x_w` is a bijection from the crossings of `G` onto the triple points of
`X°(G, ∅)`. -/
@[cluster_algebras "lem_trivalent_triple_points"]
theorem bijOn_crossingTriplePoint (hG : G.IsPlabicGraph) :
    Set.BijOn (G.crossingTriplePoint fun _ => ∅) {w | G.IsCrossing w}
      ((G.strandDiagram hG (isWhiteDatum_empty htri)).internalVertices :
        Set (Finset (G.StrandDart fun _ => ∅))) := by
  have hs : {τ | G.IsDatumTriangle (fun _ => ∅) τ} = {w | G.IsCrossing w} :=
    Set.ext fun _ => ⟨fun h => h.isCrossing_of_empty htri, isDatumTriangle_empty htri⟩
  have h := bijOn_strandTriplePoint hG (isWhiteDatum_empty htri)
  rw [hs] at h
  exact h.congr fun w hw => (crossingTriplePoint_eq_strandTriplePoint htri hw).symm

end Trivalent

/-! ### Strands follow trips -/

section StrandPath

variable (hG : G.IsPlabicGraph)

include hG

/-- A leg is an initial dart. -/
private theorem isInitial_of_isLeg {d : H} (h : G.IsLeg d) : G.IsInitial d := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨hG.leg_notMem_bdry i, Or.inr ⟨i, rfl⟩⟩

omit hG in
/-- The trip map at a dart arriving at a crossing. -/
private theorem tripMap_of_isCrossing {t : H} (hc : G.IsCrossing (G.vertexOf (G.inv t))) :
    G.tripMap t = G.rot.symm (G.inv t) :=
  turn_of_white hc.not_isBoundaryVertex (hc.2.1 _ (G.self_mem_vertexOf _))

/-- Along the chain from a dart at a crossing no dart is a leg. -/
private theorem not_isLeg_iterate_of_le_chainLength {d : H} (hd : G.IsCrossing (G.vertexOf d))
    {j : ℕ} (hj : j ≤ G.chainLength d) : ¬G.IsLeg (G.tripMap^[j] d) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact hG.not_isLeg_of_isCrossing hd
  · exact fun h => not_isInitial_of_le_chainLength hG hj0 hj (isInitial_of_isLeg hG h)

/-- The rotation of a strand diagram, three times, on symbols. -/
private theorem strandDiagram_rot_pow_three_val {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D) (e : G.StrandDart D) :
    (((G.strandDiagram hG hD).rot ^ 3) e).1 =
      G.strandRotSym D (G.strandRotSym D (G.strandRotSym D e.1)) := by
  simp [pow_succ, Equiv.Perm.mul_apply]

/-- The cycle of an endpoint symbol is an endpoint. -/
private theorem isBoundaryVertex_of_eq_endSymbol {D : Finset H → Finset (Sym2 H)}
    (hD : G.IsWhiteDatum D) {e : G.StrandDart D} {r : Fin (2 * b)} (he : e.1 = G.endSymbol r) :
    (G.strandDiagram hG hD).IsBoundaryVertex ((G.strandDiagram hG hD).vertexOf e) := by
  refine ⟨(G.strandDiagram hG hD).rot e, (G.strandDiagram hG hD).rot_mem_vertexOf e, ?_⟩
  rw [mem_strandDiagram_bdry, strandDiagram_rot_apply, he, strandRotSym_endSymbol hG]
  trivial

/-- A dart `x⁺_d` at a triple point has `v(d)` a crossing. -/
private theorem isCrossing_of_eq_xPlus {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)
    {e : G.StrandDart D} {d : H} (he : e.1 = xPlus d)
    (hv : ¬(G.strandDiagram hG hD).IsBoundaryVertex ((G.strandDiagram hG hD).vertexOf e)) :
    G.IsCrossing (G.vertexOf d) := by
  have hd : G.IsInitial d := by
    have := e.2
    rwa [he] at this
  rcases hd.2 with h | ⟨i, rfl⟩
  · exact h
  · exact (hv (isBoundaryVertex_of_eq_endSymbol hG hD (r := sourceIndex i)
      (he.trans (endSymbol_sourceIndex i).symm))).elim

/-- A dart `x⁻_t` at a triple point has `v(t̄)` a crossing. -/
private theorem isCrossing_of_eq_xMinus {D : Finset H → Finset (Sym2 H)} (hD : G.IsWhiteDatum D)
    {e : G.StrandDart D} {t : H} (he : e.1 = xMinus t)
    (hv : ¬(G.strandDiagram hG hD).IsBoundaryVertex ((G.strandDiagram hG hD).vertexOf e)) :
    G.IsCrossing (G.vertexOf (G.inv t)) := by
  have ht : G.IsTerminal t := by
    have := e.2
    rwa [he] at this
  rcases ht.2 with h | h
  · exact h
  · obtain ⟨i, hi⟩ :=
      hG.isLeg_of_isBoundaryVertex (fun hB => ht.1 (hG.inv_mem_bdry_iff.1 hB)) h
    refine (hv (isBoundaryVertex_of_eq_endSymbol hG hD (r := targetIndex i) ?_)).elim
    rw [he, endSymbol_targetIndex, hi, hG.inv_involutive]

/-- The `out` darts of `X°(G, ∅)` outside `B°` are the symbols `x⁺_d`. -/
private theorem exists_eq_xPlus_of_isOut (hD : G.IsWhiteDatum fun _ => ∅)
    {e : G.StrandDart fun _ => ∅} (hB : e ∉ (G.strandDiagram hG hD).bdry)
    (ho : (G.strandDiagram hG hD).isOut e = true) : ∃ d, e.1 = xPlus d := by
  obtain ⟨e, he⟩ := e
  rw [mem_strandDiagram_bdry] at hB
  rw [strandDiagram_isOut] at ho
  cases e with
  | xPlus d => exact ⟨d, rfl⟩
  | xMinus _ => simp [StrandSymbol.isOut] at ho
  | yPlus s τ =>
    obtain ⟨w, -, hs, -⟩ := (he : G.IsDatumSegment _ s τ)
    simp at hs
  | yMinus _ _ => simp [StrandSymbol.isOut] at ho
  | bd _ => exact (hB trivial).elim
  | bd' _ => exact (hB trivial).elim

/-- The inverse of the dart `x⁺_d` of `X°(G, ∅)` is `x⁻` of the end of the chain from `d`. -/
private theorem inv_val_of_eq_xPlus (hD : G.IsWhiteDatum fun _ => ∅)
    {e : G.StrandDart fun _ => ∅} {d : H} (he : e.1 = xPlus d) :
    ((G.strandDiagram hG hD).inv e).1 = xMinus (G.chainEnd d) := by
  rw [strandDiagram_inv_apply, he]
  rfl

variable (htri : ∀ w, G.IsCrossing w → w.card = 3)

include htri

/-- `σ°³(x⁻_{ā}) = x⁺_{σ⁻¹ a}` for `a` at a trivalent crossing. -/
private theorem rot_pow_three_of_eq_xMinus {w : Finset H} (hw : G.IsCrossing w) {a : H}
    (ha : a ∈ w) {e : G.StrandDart fun _ => ∅} (he : e.1 = xMinus (G.inv a)) :
    (((G.strandDiagram hG (isWhiteDatum_empty htri)).rot ^ 3) e).1 = xPlus (G.rot.symm a) := by
  have h1 := rot_mem hw ha
  rw [strandDiagram_rot_pow_three_val, he, strandRotSym_xMinus_inv htri hG hw ha,
    strandRotSym_xPlus hG _ (isCrossing_vertexOf hw h1), strandRotSym_xMinus_inv htri hG hw h1,
    rot_rot_eq_rot_symm htri hw ha]

/-- `σ°³(x⁺_a) = x⁻_{\overline{σ a}}` for `a` at a trivalent crossing. -/
private theorem rot_pow_three_of_eq_xPlus {w : Finset H} (hw : G.IsCrossing w) {a : H}
    (ha : a ∈ w) {e : G.StrandDart fun _ => ∅} (he : e.1 = xPlus a) :
    (((G.strandDiagram hG (isWhiteDatum_empty htri)).rot ^ 3) e).1 =
      xMinus (G.inv (G.rot a)) := by
  rw [strandDiagram_rot_pow_three_val, he, strandRotSym_xPlus hG _ (isCrossing_vertexOf hw ha),
    strandRotSym_xMinus_inv htri hG hw ha,
    strandRotSym_xPlus hG _ (isCrossing_vertexOf hw (rot_mem hw ha))]

/-- A strand path of `X°(G, ∅)` from `x⁺_d`, `v(d)` a crossing, to a triple point follows the trip
of `d`. -/
private theorem exists_iterate_of_isStrandPath_cons (P : List (G.StrandDart fun _ => ∅)) :
    ∀ (e : G.StrandDart fun _ => ∅) (d : H),
      (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath (e :: P) → e.1 = xPlus d →
      G.IsCrossing (G.vertexOf d) →
      (G.strandDiagram hG (isWhiteDatum_empty htri)).pathEnd (e :: P) ∈
        (G.strandDiagram hG (isWhiteDatum_empty htri)).internalVertices →
      ∃ N, (∀ j ≤ N, ¬G.IsLeg (G.tripMap^[j] d)) ∧
        G.IsCrossing (G.vertexOf (G.inv (G.tripMap^[N] d))) ∧
        ∀ eₘ ∈ (e :: P).getLast?,
          ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv eₘ).1 =
            xMinus (G.tripMap^[N] d) := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  induction P with
  | nil =>
    intro e d _ he hd hend
    have hinv : (X.inv e).1 = xMinus (G.chainEnd d) := inv_val_of_eq_xPlus hG _ he
    refine ⟨G.chainLength d, fun j hj => not_isLeg_iterate_of_le_chainLength hG hd hj, ?_, ?_⟩
    · exact isCrossing_of_eq_xMinus hG _ hinv (X.mem_internalVertices.1 hend).2
    · intro eₘ hm
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hm
      subst hm
      exact hinv
  | cons e' P ih =>
    intro e d hP he hd hend
    have hstep := (List.isChain_cons_cons.1 hP.isChain).1
    have hinv : (X.inv e).1 = xMinus (G.chainEnd d) := inv_val_of_eq_xPlus hG _ he
    have hw' := isCrossing_of_eq_xMinus hG _ hinv hstep.1
    have hmem : G.inv (G.chainEnd d) ∈ G.vertexOf (G.inv (G.chainEnd d)) := G.self_mem_vertexOf _
    have he' : e'.1 = xPlus (G.tripMap (G.chainEnd d)) := by
      rw [hstep.2, rot_pow_three_of_eq_xMinus hG htri hw' hmem (by rw [hinv, hG.inv_involutive]),
        tripMap_of_isCrossing hw']
    have hd' : G.IsCrossing (G.vertexOf (G.tripMap (G.chainEnd d))) := by
      rwa [tripMap_apply, vertexOf_turn]
    obtain ⟨N, hleg, hcr, hlast⟩ := ih e' _ hP.of_cons_cons he' hd' <| by
      simpa only [TripleData.pathEnd, List.getLast?_cons_cons] using hend
    have hT : G.tripMap (G.chainEnd d) = G.tripMap^[G.chainLength d + 1] d := by
      rw [Function.iterate_succ_apply', chainEnd_def]
    refine ⟨N + (G.chainLength d + 1), fun j hj => ?_, ?_, ?_⟩
    · by_cases hjL : j ≤ G.chainLength d
      · exact not_isLeg_iterate_of_le_chainLength hG hd hjL
      · obtain ⟨k, rfl⟩ : ∃ k, j = k + (G.chainLength d + 1) :=
          ⟨j - (G.chainLength d + 1), by omega⟩
        rw [Function.iterate_add_apply, ← hT]
        exact hleg k (by omega)
    · rwa [Function.iterate_add_apply, ← hT]
    · intro eₘ hm
      rw [List.getLast?_cons_cons] at hm
      rw [Function.iterate_add_apply, ← hT]
      exact hlast eₘ hm

/-- **A strand path follows a trip**. Let `G` be a plabic graph each of whose crossings consists of
exactly three darts, and `(e₁, …, e_m)` a strand path of `X°(G, ∅)` running from a triple point to
a triple point. Then there are a dart `y ∉ B` and `n ≥ 1` such that `v(ȳ)` and
`v(\overline{Tⁿ(y)})` are crossings, none of `T(y), …, Tⁿ(y)` is a leg, `e₁ = x⁺_{T(y)}` and
`ē_m = x⁻_{Tⁿ(y)}`. -/
@[cluster_algebras "lem_strand_path_trip"]
theorem exists_tripMap_of_isStrandPath {P : List (G.StrandDart fun _ => ∅)}
    (hP : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath P)
    (hs : (G.strandDiagram hG (isWhiteDatum_empty htri)).pathStart P ∈
      (G.strandDiagram hG (isWhiteDatum_empty htri)).internalVertices)
    (he : (G.strandDiagram hG (isWhiteDatum_empty htri)).pathEnd P ∈
      (G.strandDiagram hG (isWhiteDatum_empty htri)).internalVertices) :
    ∃ y ∉ G.bdry, ∃ n, 1 ≤ n ∧ G.IsCrossing (G.vertexOf (G.inv y)) ∧
      G.IsCrossing (G.vertexOf (G.inv (G.tripMap^[n] y))) ∧
      (∀ k, 1 ≤ k → k ≤ n → ¬G.IsLeg (G.tripMap^[k] y)) ∧
      (∀ e₁ ∈ P.head?, e₁.1 = xPlus (G.tripMap y)) ∧
      ∀ eₘ ∈ P.getLast?,
        ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv eₘ).1 =
          xMinus (G.tripMap^[n] y) := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  obtain ⟨e, P', rfl⟩ := List.exists_cons_of_ne_nil hP.ne_nil
  obtain ⟨d, hd⟩ := exists_eq_xPlus_of_isOut hG _ (hP.notMem_bdry e (by simp))
    (hP.isOut_eq_true e (by simp))
  have hdc : G.IsCrossing (G.vertexOf d) :=
    isCrossing_of_eq_xPlus hG _ hd (X.mem_internalVertices.1 hs).2
  obtain ⟨N, hleg, hcr, hlast⟩ := exists_iterate_of_isStrandPath_cons hG htri P' e d hP hd hdc he
  have hrot : ¬G.IsBoundaryVertex (G.vertexOf (G.rot d)) := by
    rw [G.vertexOf_rot]
    exact hdc.not_isBoundaryVertex
  have hTy : G.tripMap (G.inv (G.rot d)) = d := by
    rw [tripMap_apply, hG.inv_involutive, turn_of_white hrot (hdc.2.1 _ (G.rot_mem_vertexOf d)),
      Equiv.symm_apply_apply]
  refine ⟨G.inv (G.rot d), fun h => notMem_bdry_of_mem_vertexOf hdc.not_isBoundaryVertex
    (G.rot_mem_vertexOf d) (hG.inv_mem_bdry_iff.1 h), N + 1, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hG.inv_involutive, G.vertexOf_rot]
  · rwa [Function.iterate_succ_apply, hTy]
  · intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply, hTy]
    exact hleg j (by omega)
  · intro e₁ he₁
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he₁
    subst he₁
    rwa [hTy]
  · intro eₘ hm
    rw [Function.iterate_succ_apply, hTy]
    exact hlast eₘ hm

omit htri in
/-- If `z` is terminal and `T(z)` is not a leg, then `v(z̄)` is a crossing. -/
private theorem isCrossing_of_isTerminal {z : H} (hz : G.IsTerminal z)
    (hT : ¬G.IsLeg (G.tripMap z)) : G.IsCrossing (G.vertexOf (G.inv z)) := by
  rcases hz.2 with h | h
  · exact h
  · have hl : G.IsLeg (G.inv z) :=
      hG.isLeg_of_isBoundaryVertex (fun hB => hz.1 (hG.inv_mem_bdry_iff.1 hB)) h
    exact absurd (by rwa [tripMap_apply, turn_of_isBoundaryVertex h]) hT

/-- If `ē₁ = x⁻_z` and `e' = x⁺_{T(z)}` with `v(z̄)` a trivalent crossing, then `e₁ → e'` is a
strand step of `X°(G, ∅)`. -/
private theorem strandStep_of_inv_eq_xMinus {z : H} (hz : G.IsCrossing (G.vertexOf (G.inv z)))
    {e₁ e' : G.StrandDart fun _ => ∅}
    (h₁ : ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv e₁).1 = xMinus z)
    (h' : e'.1 = xPlus (G.tripMap z)) :
    (G.strandDiagram hG (isWhiteDatum_empty htri)).StrandStep e₁ e' := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  have hmem := G.self_mem_vertexOf (G.inv z)
  have h₁' : (X.inv e₁).1 = xMinus (G.inv (G.inv z)) := by rw [h₁, hG.inv_involutive]
  refine ⟨?_, ?_⟩
  · change ¬X.IsBoundaryVertex (X.vertexOf (X.inv e₁))
    rw [strandDiagram_vertexOf_of_eq_xMinus htri hG hz hmem h₁']
    exact (X.mem_internalVertices.1 (crossingTriplePoint_mem_internalVertices htri hG hz)).2
  · apply Subtype.ext
    rw [h', rot_pow_three_of_eq_xMinus hG htri hz hmem h₁', tripMap_of_isCrossing hz]

/-- **A stretch of a trip is a strand path**. Let `G` be a plabic graph each of whose crossings
consists of exactly three darts, and let `y` be a dart and `n ≥ 1` such that `v(ȳ)` and
`v(\overline{Tⁿ(y)})` are crossings and none of `T(y), …, Tⁿ(y)` is a leg. Then `X°(G, ∅)` has a
strand path `(e₁, …, e_m)` with `e₁ = x⁺_{T(y)}` and `ē_m = x⁻_{Tⁿ(y)}`. -/
@[cluster_algebras "lem_trip_strand_path"]
theorem exists_isStrandPath_of_tripMap {y : H} {n : ℕ} (hn : 1 ≤ n)
    (hy : G.IsCrossing (G.vertexOf (G.inv y)))
    (hyn : G.IsCrossing (G.vertexOf (G.inv (G.tripMap^[n] y))))
    (hleg : ∀ k, 1 ≤ k → k ≤ n → ¬G.IsLeg (G.tripMap^[k] y)) :
    ∃ P, (G.strandDiagram hG (isWhiteDatum_empty htri)).IsStrandPath P ∧
      (∀ e₁ ∈ P.head?, e₁.1 = xPlus (G.tripMap y)) ∧
      ∀ eₘ ∈ P.getLast?,
        ((G.strandDiagram hG (isWhiteDatum_empty htri)).inv eₘ).1 =
          xMinus (G.tripMap^[n] y) := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  induction n using Nat.strong_induction_on generalizing y with
  | _ n ih =>
  have hd₁ : G.IsCrossing (G.vertexOf (G.tripMap y)) := by
    rwa [tripMap_apply, vertexOf_turn]
  have hinit : G.IsInitial (G.tripMap y) :=
    ⟨notMem_bdry_of_mem_vertexOf hd₁.not_isBoundaryVertex (G.self_mem_vertexOf _), Or.inl hd₁⟩
  have hL : G.chainLength (G.tripMap y) ≤ n - 1 := chainLength_le <| by
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    exact ⟨fun h => hyn.not_isBoundaryVertex ⟨_, G.self_mem_vertexOf _, hG.inv_mem_bdry _ h⟩,
      Or.inl hyn⟩
  have hEnd : G.chainEnd (G.tripMap y) = G.tripMap^[G.chainLength (G.tripMap y) + 1] y := by
    rw [chainEnd_def, Function.iterate_succ_apply]
  let e₁ : G.StrandDart fun _ => ∅ := ⟨xPlus (G.tripMap y), hinit⟩
  have hinv₁ : (X.inv e₁).1 = xMinus (G.tripMap^[G.chainLength (G.tripMap y) + 1] y) := by
    rw [← hEnd]
    exact inv_val_of_eq_xPlus hG _ rfl
  have hB₁ : e₁ ∉ X.bdry := fun h => (mem_strandDiagram_bdry hG _).1 h
  rcases Nat.lt_or_ge (G.chainLength (G.tripMap y) + 1) n with hlt | hge
  · set L := G.chainLength (G.tripMap y)
    have hy'term : G.IsTerminal (G.tripMap^[L + 1] y) := hEnd ▸ hinit.isTerminal_chainEnd hG
    have hy' := isCrossing_of_isTerminal hG hy'term <| by
      simpa only [Function.iterate_succ_apply'] using hleg (L + 2) (by omega) (by omega)
    have hyn' : G.tripMap^[n - (L + 1)] (G.tripMap^[L + 1] y) = G.tripMap^[n] y := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    obtain ⟨P, hP, hhead, hlast⟩ := ih (n - (L + 1)) (by omega) (by omega) hy' (hyn'.symm ▸ hyn)
      fun k hk1 hk2 => by
        rw [← Function.iterate_add_apply]
        exact hleg _ (by omega) (by omega)
    obtain ⟨e', P', rfl⟩ := List.exists_cons_of_ne_nil hP.ne_nil
    refine ⟨e₁ :: e' :: P', ?_, fun x hx => by obtain rfl := Option.mem_some_iff.1 hx; rfl,
      fun x hx => ?_⟩
    · exact hP.cons_cons hB₁ rfl (strandStep_of_inv_eq_xMinus hG htri hy' hinv₁ (hhead e' rfl))
    · rw [List.getLast?_cons_cons] at hx
      rw [← hyn']
      exact hlast x hx
  · have hLn : G.chainLength (G.tripMap y) + 1 = n := by omega
    refine ⟨[e₁], X.isStrandPath_iff.2 ⟨List.cons_ne_nil _ _, List.forall_mem_singleton.2 hB₁,
      List.forall_mem_singleton.2 rfl, List.IsChain.singleton _⟩,
      fun x hx => by obtain rfl := Option.mem_some_iff.1 hx; rfl, fun x hx => ?_⟩
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
    subst hx
    rw [hinv₁, hLn]

omit htri in
/-- If `τ` is a trip containing `z` and `T(z)` is not a leg, then `τ` contains `T(z)`. -/
theorem Trip.tripMap_mem_darts {τ : G.Trip} {z : H} (hz : z ∈ τ.darts)
    (hT : ¬G.IsLeg (G.tripMap z)) : G.tripMap z ∈ τ.darts := by
  cases τ with
  | oneWay i =>
    rw [Trip.mem_darts_oneWay] at hz ⊢
    obtain ⟨p, hp, hpn⟩ := hG.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip (x := z) (n := 1)
      (j := 0) (fun l hl0 hl1 => by
        obtain rfl : l = 1 := by omega
        exact hT) (Nat.zero_le 1) (mem_oneWayTrip.2 hz)
    exact ⟨p + 1, hpn, by rw [Function.iterate_succ_apply', hp]⟩
  | round O hO =>
    rw [Trip.darts_round] at hz ⊢
    obtain ⟨d, -, rfl, -⟩ := hO
    obtain ⟨k, rfl⟩ := hz
    exact ⟨k + 1, Function.iterate_succ_apply' _ _ _⟩

/-- A stretch `y, T(y), …, Tⁿ(y) = y'` of a trip, passing no leg, from a dart arriving at a
trivalent crossing `w` to another dart arriving at `w`, gives a monogon with vertex `x_w`. -/
private theorem exists_isMonogon_of_iterate {w : Finset H} (hw : G.IsCrossing w) {y y' : H}
    {n : ℕ} (hn : 1 ≤ n) (hyn : G.tripMap^[n] y = y') (hne : y ≠ y')
    (hy : G.vertexOf (G.inv y) = w) (hy' : G.vertexOf (G.inv y') = w)
    (hleg : ∀ k, 1 ≤ k → k ≤ n → ¬G.IsLeg (G.tripMap^[k] y)) :
    ∃ P, (G.strandDiagram hG (isWhiteDatum_empty htri)).IsMonogon P ∧
      (G.strandDiagram hG (isWhiteDatum_empty htri)).pathStart P =
        G.crossingTriplePoint (fun _ => ∅) w := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  have hyc : G.IsCrossing (G.vertexOf (G.inv y)) := hy ▸ hw
  obtain ⟨P, hP, hhead, hlast⟩ :=
    exists_isStrandPath_of_tripMap hG htri hn hyc (by rw [hyn, hy']; exact hw) hleg
  obtain ⟨e₁, P', rfl⟩ := List.exists_cons_of_ne_nil hP.ne_nil
  have hm := List.getLast?_eq_some_getLast (l := e₁ :: P') (List.cons_ne_nil _ _)
  set eₘ := (e₁ :: P').getLast (List.cons_ne_nil _ _)
  have h1 : e₁.1 = xPlus (G.tripMap y) := hhead e₁ rfl
  have hTyw : G.tripMap y ∈ w := by
    rw [← hy]
    exact turn_mem_vertexOf _
  have hstart : X.pathStart (e₁ :: P') = G.crossingTriplePoint (fun _ => ∅) w :=
    strandDiagram_vertexOf_of_eq_xPlus htri hG hw hTyw h1
  have hlastv : (X.inv eₘ).1 = xMinus y' := hyn ▸ hlast eₘ hm
  have hy'w : G.inv y' ∈ w := hy' ▸ G.self_mem_vertexOf _
  have hrT : G.rot (G.tripMap y) = G.inv y := by
    rw [tripMap_of_isCrossing hyc, Equiv.apply_symm_apply]
  refine ⟨_, ⟨hP, hstart ▸ crossingTriplePoint_mem_internalVertices htri hG hw, ?_, ?_⟩, hstart⟩
  · rw [X.pathEnd_of_getLast? hm, hstart]
    exact strandDiagram_vertexOf_of_eq_xMinus htri hG hw hy'w (by rw [hlastv, hG.inv_involutive])
  · intro a ha c hc heq
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    subst ha
    rw [Option.mem_def, hm, Option.some.injEq] at hc
    subst hc
    have h := congrArg Subtype.val heq
    rw [hlastv, rot_pow_three_of_eq_xPlus hG htri hw hTyw h1, hrT, hG.inv_involutive] at h
    exact hne (xMinus.inj h).symm

private theorem exists_trip_of_isMonogon {w : Finset H} (hw : G.IsCrossing w) {P : List _}
    (hP : (G.strandDiagram hG (isWhiteDatum_empty htri)).IsMonogon P)
    (hstart : (G.strandDiagram hG (isWhiteDatum_empty htri)).pathStart P =
      G.crossingTriplePoint (fun _ => ∅) w) :
    ∃ y y', y ≠ y' ∧ G.vertexOf (G.inv y) = w ∧ G.vertexOf (G.inv y') = w ∧
      ∃ τ : G.Trip, y ∈ τ.darts ∧ y' ∈ τ.darts := by
  set X := G.strandDiagram hG (isWhiteDatum_empty htri)
  have hs := hP.pathStart_mem
  obtain ⟨y, hyB, n, hn, hyc, -, hleg, hhead, hlast⟩ :=
    exists_tripMap_of_isStrandPath hG htri hP.isStrandPath hs (hP.pathEnd_eq ▸ hs)
  obtain ⟨e₁, P', rfl⟩ := List.exists_cons_of_ne_nil hP.isStrandPath.ne_nil
  have hm := List.getLast?_eq_some_getLast (l := e₁ :: P') (List.cons_ne_nil _ _)
  set eₘ := (e₁ :: P').getLast (List.cons_ne_nil _ _)
  have h1 : e₁.1 = xPlus (G.tripMap y) := hhead e₁ rfl
  have hTyw : G.tripMap y ∈ w := by
    have : e₁ ∈ X.pathStart (e₁ :: P') := X.self_mem_vertexOf e₁
    rw [hstart] at this
    exact (mem_crossingTriplePoint_of_eq_xPlus h1).1 this
  have hyw : G.vertexOf (G.inv y) = w :=
    (vertexOf_turn (G.inv y)).symm.trans (hw.eq_vertexOf hTyw).symm
  have hlastv := hlast eₘ hm
  have hy'w : G.inv (G.tripMap^[n] y) ∈ w := by
    have : X.inv eₘ ∈ X.pathEnd (e₁ :: P') := by
      rw [X.pathEnd_of_getLast? hm]
      exact X.self_mem_vertexOf _
    rw [hP.pathEnd_eq, hstart] at this
    exact (mem_crossingTriplePoint_of_eq_xMinus hG hlastv).1 this
  have hrT : G.rot (G.tripMap y) = G.inv y := by
    rw [tripMap_of_isCrossing hyc, Equiv.apply_symm_apply]
  refine ⟨y, G.tripMap^[n] y, fun hyy => ?_, hyw, (hw.eq_vertexOf hy'w).symm, ?_⟩
  · refine hP.inv_ne e₁ rfl eₘ hm (Subtype.ext ?_)
    rw [hlastv, rot_pow_three_of_eq_xPlus hG htri hw hTyw h1, hrT, hG.inv_involutive, ← hyy]
  · by_cases hl : ∃ k, G.IsLeg (G.tripMap^[k] y)
    · obtain ⟨k, j, hj⟩ := hl
      obtain ⟨i, hi, -⟩ := hG.existsUnique_mem_oneWayTrip ⟨j, k, hj.symm⟩
      obtain ⟨p, hp, hpn⟩ := hG.exists_iterate_leg_eq_of_iterate_mem_oneWayTrip
        hleg (Nat.zero_le n) hi
      exact ⟨.oneWay i, Trip.mem_darts_oneWay.2 ⟨p, by omega, hp⟩,
        Trip.mem_darts_oneWay.2 ⟨n + p, by omega, by rw [Function.iterate_add_apply, hp]⟩⟩
    · push Not at hl
      refine ⟨.round (G.trip y) ⟨y, hyB, rfl, fun j hj => ?_⟩, mem_trip_self y,
        iterate_mem_trip y n⟩
      obtain ⟨k, hk⟩ := hj
      exact hl k ⟨j, hk.symm⟩

private theorem exists_isMonogon_of_mem_trip_darts {w : Finset H} (hw : G.IsCrossing w)
    {y y' : H} (hne : y ≠ y') (hy : G.vertexOf (G.inv y) = w) (hy' : G.vertexOf (G.inv y') = w)
    {τ : G.Trip} (hyτ : y ∈ τ.darts) (hy'τ : y' ∈ τ.darts) :
    ∃ P, (G.strandDiagram hG (isWhiteDatum_empty htri)).IsMonogon P ∧
      (G.strandDiagram hG (isWhiteDatum_empty htri)).pathStart P =
        G.crossingTriplePoint (fun _ => ∅) w := by
  cases τ with
  | oneWay i =>
    obtain ⟨p, hp, rfl⟩ := Trip.mem_darts_oneWay.1 hyτ
    obtain ⟨p', hp', rfl⟩ := Trip.mem_darts_oneWay.1 hy'τ
    have hpp : p ≠ p' := fun h => hne (h ▸ rfl)
    rcases lt_or_gt_of_ne hpp with h | h
    · refine exists_isMonogon_of_iterate hG htri hw (n := p' - p) (by omega) ?_ hne hy hy'
        fun k hk1 hk2 => ?_
      · rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      · rw [← Function.iterate_add_apply]
        exact not_isLeg_of_lt_tripLength (by omega) (by omega)
    · refine exists_isMonogon_of_iterate hG htri hw (n := p - p') (by omega) ?_ hne.symm hy' hy
        fun k hk1 hk2 => ?_
      · rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
      · rw [← Function.iterate_add_apply]
        exact not_isLeg_of_lt_tripLength (by omega) (by omega)
  | round O hO =>
    rw [Trip.darts_round] at hyτ hy'τ
    obtain ⟨d, -, rfl, hl⟩ := hO
    have hsc : hG.tripEquiv.SameCycle y y' := by
      rw [hG.trip_eq_setOf_sameCycle] at hyτ hy'τ
      exact (Equiv.Perm.SameCycle.symm hyτ).trans hy'τ
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    rw [hG.tripEquiv_pow_apply] at hn
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h => hne (by subst h; exact hn)
    refine exists_isMonogon_of_iterate hG htri hw hn1 hn hne hy hy' fun k _ _ ⟨j, hj⟩ => ?_
    obtain ⟨m, rfl⟩ := hyτ
    exact hl j ⟨k + m, by
      change G.tripMap^[k + m] d = _
      rw [Function.iterate_add_apply, hj]⟩

/-- **Monogons are trips passing a crossing twice**. Let `G` be a plabic graph each of whose
crossings consists of exactly three darts, and `w` a crossing. Then `X°(G, ∅)` has a monogon with
vertex `x_w` if and only if there are two distinct darts `y, y'` with `v(ȳ) = v(ȳ') = w` that are
darts of one trip (a roundtrip, or the one-way trip from some label). -/
@[cluster_algebras "lem_monogon_trip"]
theorem exists_isMonogon_iff {w : Finset H} (hw : G.IsCrossing w) :
    (∃ P, (G.strandDiagram hG (isWhiteDatum_empty htri)).IsMonogon P ∧
        (G.strandDiagram hG (isWhiteDatum_empty htri)).pathStart P =
          G.crossingTriplePoint (fun _ => ∅) w) ↔
      ∃ y y', y ≠ y' ∧ G.vertexOf (G.inv y) = w ∧ G.vertexOf (G.inv y') = w ∧
        ∃ τ : G.Trip, y ∈ τ.darts ∧ y' ∈ τ.darts :=
  ⟨fun ⟨_, hP, hstart⟩ => exists_trip_of_isMonogon hG htri hw hP hstart,
    fun ⟨_, _, hne, hy, hy', _, hyτ, hy'τ⟩ =>
      exists_isMonogon_of_mem_trip_darts hG htri hw hne hy hy' hyτ hy'τ⟩

end StrandPath

/-! ### A trip visiting a white vertex twice in a normal graph -/

/-- Two distinct darts of a vertex with three darts are adjacent in the rotation. -/
private theorem eq_rot_or_eq_rot_of_card_eq_three {a a' : H} (h3 : (G.vertexOf a).card = 3)
    (ha' : a' ∈ G.vertexOf a) (hne : a' ≠ a) : a' = G.rot a ∨ a = G.rot a' := by
  obtain ⟨i, rfl⟩ := (isCornerLabelling_three h3).exists_eq ha'
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

/-- In a normal plabic graph, if a trip contains darts `y`, `y'` arriving at a white vertex with
`ȳ' = σ(ȳ)`, then `ȳ` is an essential self-intersection. -/
private theorem exists_isEssentialSelfIntersection_of_inv_eq_rot (hG : G.IsNormalPlabicGraph)
    {τ : G.Trip} {y y' : H} (hy : y ∈ τ.darts) (hy' : y' ∈ τ.darts)
    (hint : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y))) (hwhite : G.colour (G.inv y) = .white)
    (hrot : G.inv y' = G.rot (G.inv y)) : ∃ d, G.IsEssentialSelfIntersection d := by
  have hint' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y')) := by
    rwa [hrot, G.vertexOf_rot]
  have hwhite' : G.colour (G.inv y') = .white := by
    rwa [hrot, hG.colour_rot _ hint]
  have hT : G.tripMap y' = G.inv y := by
    rw [tripMap_apply, turn_of_white hint' hwhite', hrot, Equiv.symm_apply_apply]
  have hnl : ¬G.IsLeg (G.inv y) := fun h =>
    hint (hG.toIsPlabicGraph.isBoundaryVertex_of_isLeg h)
  refine ⟨G.inv y, notMem_bdry_of_mem_vertexOf hint (G.self_mem_vertexOf _), hint,
    (hG.inv_internal_black_of_white hint hwhite).1, τ, ?_, ?_⟩
  · rw [← hT]
    exact Trip.tripMap_mem_darts hG.toIsPlabicGraph hy' (hT ▸ hnl)
  · rwa [hG.inv_involutive]

/-- **A trip visiting a white vertex twice in a normal graph**: if `G` is a normal plabic graph,
`w` a white vertex and `τ` a trip of `G` containing two distinct darts `y, y'` with
`v(ȳ) = v(ȳ') = w`, then `G` has an essential self-intersection. -/
@[cluster_algebras "lem_normal_two_arrivals"]
theorem IsNormalPlabicGraph.exists_isEssentialSelfIntersection (hG : G.IsNormalPlabicGraph)
    {w : Finset H} (hw : w ∈ G.internalVertices) (hwhite : ∀ d ∈ w, G.colour d = .white)
    {τ : G.Trip} {y y' : H} (hy : y ∈ τ.darts) (hy' : y' ∈ τ.darts) (hne : y ≠ y')
    (hyw : G.vertexOf (G.inv y) = w) (hy'w : G.vertexOf (G.inv y') = w) :
    ∃ d, G.IsEssentialSelfIntersection d := by
  have hwint := (G.mem_internalVertices.1 hw).2
  have hint : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y)) := hyw ▸ hwint
  have hint' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv y')) := hy'w ▸ hwint
  have hwh : G.colour (G.inv y) = .white := hwhite _ (hyw ▸ G.self_mem_vertexOf _)
  have hwh' : G.colour (G.inv y') = .white := hwhite _ (hy'w ▸ G.self_mem_vertexOf _)
  have h3 := hG.card_vertexOf_of_white _ hint hwh
  have hmem : G.inv y' ∈ G.vertexOf (G.inv y) := by
    rw [hyw, ← hy'w]
    exact G.self_mem_vertexOf _
  have hne' : G.inv y' ≠ G.inv y := fun h => hne (hG.inv_involutive.injective h).symm
  rcases eq_rot_or_eq_rot_of_card_eq_three h3 hmem hne' with h | h
  · exact exists_isEssentialSelfIntersection_of_inv_eq_rot hG hy hy' hint hwh h
  · exact exists_isEssentialSelfIntersection_of_inv_eq_rot hG hy' hy hint' hwh' h

end PlabicData

/-! ### Badgons are invariant under isomorphism -/

namespace TripleData

namespace Iso

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {X : TripleData H b} {X' : TripleData H' b}

/-- An isomorphism intertwines `σ³`. -/
theorem map_rot_pow_three (θ : X.Iso X') (d : H) :
    θ.toEquiv ((X.rot ^ 3) d) = (X'.rot ^ 3) (θ.toEquiv d) := by
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, θ.map_rot]

/-- An isomorphism maps a step of a strand path to a step of a strand path. -/
theorem strandStep_map (θ : X.Iso X') {e e' : H} (h : X.StrandStep e e') :
    X'.StrandStep (θ.toEquiv e) (θ.toEquiv e') :=
  ⟨mt (θ.runsToEndpoint_iff e).1 h.1, by rw [h.2, θ.map_rot_pow_three, θ.map_inv]⟩

/-- An isomorphism maps a strand path onto a strand path. -/
theorem isStrandPath_map (θ : X.Iso X') {P : List H} (hP : X.IsStrandPath P) :
    X'.IsStrandPath (P.map θ.toEquiv) where
  ne_nil := by simpa using hP.ne_nil
  notMem_bdry e he := by
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    rw [θ.mem_bdry_iff]
    exact hP.notMem_bdry e₀ he₀
  isOut_eq_true e he := by
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    rw [θ.map_isOut _ (hP.notMem_bdry e₀ he₀)]
    exact hP.isOut_eq_true e₀ he₀
  isChain := List.isChain_map_of_isChain _ (fun _ _ h => θ.strandStep_map h) hP.isChain

/-- An isomorphism maps the vertex a strand path runs from onto the vertex its image runs
from. -/
theorem pathStart_map (θ : X.Iso X') (P : List H) :
    X'.pathStart (P.map θ.toEquiv) = (X.pathStart P).map θ.toEquiv.toEmbedding := by
  cases P with
  | nil => simp [pathStart]
  | cons e P => rw [List.map_cons, pathStart_cons, pathStart_cons, θ.map_vertexOf]

/-- An isomorphism maps the vertex a strand path runs to onto the vertex its image runs to. -/
theorem pathEnd_map (θ : X.Iso X') (P : List H) :
    X'.pathEnd (P.map θ.toEquiv) = (X.pathEnd P).map θ.toEquiv.toEmbedding := by
  cases h : P.getLast? with
  | none =>
    obtain rfl : P = [] := List.getLast?_eq_none_iff.1 h
    simp [pathEnd]
  | some e =>
    rw [X.pathEnd_of_getLast? h, X'.pathEnd_of_getLast? (e := θ.toEquiv e)
      (by rw [List.getLast?_map, h]; rfl), θ.map_vertexOf, θ.map_inv]

/-- An isomorphism maps triple points onto triple points. -/
theorem map_mem_internalVertices (θ : X.Iso X') {v : Finset H} (hv : v ∈ X.internalVertices) :
    v.map θ.toEquiv.toEmbedding ∈ X'.internalVertices := by
  obtain ⟨hvV, hb⟩ := X.mem_internalVertices.1 hv
  obtain ⟨d, rfl⟩ := X.mem_vertices.1 hvV
  rw [θ.map_vertexOf]
  exact X'.vertexOf_mem_internalVertices.2 (by rwa [θ.isBoundaryVertex_vertexOf_iff])

/-- **Badgons are invariant under isomorphism**: if `θ : X → X'` is an isomorphism and `X` has a
badgon, then `X'` has a badgon. -/
@[cluster_algebras "lem_badgon_isomorphism"]
theorem hasBadgon (θ : X.Iso X') (h : X.HasBadgon) : X'.HasBadgon := by
  rcases h with ⟨P, hP⟩ | ⟨P, Q, x, y, hPQ⟩
  · refine Or.inl ⟨P.map θ.toEquiv, θ.isStrandPath_map hP.isStrandPath, ?_, ?_, ?_⟩
    · rw [θ.pathStart_map]
      exact θ.map_mem_internalVertices hP.pathStart_mem
    · rw [θ.pathStart_map, θ.pathEnd_map, hP.pathEnd_eq]
    · intro e₁ he₁ eₘ heₘ
      rw [List.head?_map, Option.mem_map] at he₁
      rw [List.getLast?_map, Option.mem_map] at heₘ
      obtain ⟨a, ha, rfl⟩ := he₁
      obtain ⟨c, hc, rfl⟩ := heₘ
      rw [← θ.map_inv, ← θ.map_rot_pow_three]
      exact θ.toEquiv.injective.ne (hP.inv_ne a ha c hc)
  · refine Or.inr ⟨P.map θ.toEquiv, Q.map θ.toEquiv, x.map θ.toEquiv.toEmbedding,
      y.map θ.toEquiv.toEmbedding,
      { ne := (map_injective _).ne hPQ.ne
        mem_left := θ.map_mem_internalVertices hPQ.mem_left
        mem_right := θ.map_mem_internalVertices hPQ.mem_right
        isStrandPath_fst := θ.isStrandPath_map hPQ.isStrandPath_fst
        isStrandPath_snd := θ.isStrandPath_map hPQ.isStrandPath_snd
        pathStart_fst := by rw [θ.pathStart_map, hPQ.pathStart_fst]
        pathEnd_fst := by rw [θ.pathEnd_map, hPQ.pathEnd_fst]
        pathStart_snd := by rw [θ.pathStart_map, hPQ.pathStart_snd]
        pathEnd_snd := by rw [θ.pathEnd_map, hPQ.pathEnd_snd]
        head?_ne := by
          rw [List.head?_map, List.head?_map]
          exact (Option.map_injective θ.toEquiv.injective).ne hPQ.head?_ne
        getLast?_ne := by
          rw [List.getLast?_map, List.getLast?_map]
          exact (Option.map_injective θ.toEquiv.injective).ne hPQ.getLast?_ne }⟩

end Iso

end TripleData

end ClusterAlgebras
