/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.StrandDiagram
public import ClusterAlgebras.Plabic.Excision
public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.NormalTriple
public import ClusterAlgebras.Plabic.Reduced
public import ClusterAlgebras.Plabic.ExcisionLemmas

/-!
# Ears, stray leaves and hollow digons in the strand diagram

Let `G` be a plabic graph with a white datum `D`, `w` a crossing of `G` and `a ∈ w` such that
`{σ(a), a, σ⁻¹(a)}` is a triangle of `D_w` (an *ear* of the corner triangulation). The cycle of the
rotation `σ°` of the strand diagram `X°(G, D)` through `x⁺_a` is then
`(x⁺_a, x⁻_{ā}, x⁺_{σ(a)}, x⁻_{\overline{σ(a)}}, q₁, q₂)`. From this one reads off how the
forbidden configurations of `G` show up in `X°(G, D)`:

* an internal leaf whose dart `k` runs to a crossing gives the hollow monogon `{x⁻_k}`;
* a hollow digon with no crossing is a trip of `G` without initial dart;
* a hollow digon from a black vertex to a crossing gives a hollow monogon;
* a hollow digon from a crossing to a white vertex gives a closed strand.

For a normal plabic graph `G`, a hollow monogon of the triple diagram `X(G)` comes from a hollow
digon of `G` or from an internal leaf of `G` that is not a lollipop. Finally, a plabic tree in
which every internal leaf is black is not `{M2, M3}`-equivalent to the lollipop graph `L_white`,
nor to `L_black` if moreover every white vertex has at least three darts and there is a white
vertex.

## Main results

* `ClusterAlgebras.PlabicData.IsWhiteDatum.map_val_toList_strandRot_ear`: the strand diagram at an
  ear.
* `ClusterAlgebras.PlabicData.IsWhiteDatum.strandDiagram_facePerm_xMinus_of_isInternalLeaf`: a
  stray leaf at a crossing gives a hollow monogon.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.trip_eq_of_isHollowDigon`: a hollow digon without
  crossings is a trip without initial dart.
* `ClusterAlgebras.PlabicData.IsWhiteDatum.strandDiagram_facePerm_xPlus_of_isHollowDigon`: a
  bicoloured hollow digon at a crossing gives a hollow monogon.
* `ClusterAlgebras.PlabicData.IsWhiteDatum.exists_isClosedStrand_of_isHollowDigon`: a white hollow
  digon at a crossing gives a closed strand.
* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.exists_isHollowDigon_or_isInternalLeaf`:
  a hollow monogon of `X(G)` is a forbidden configuration of `G`.
* `ClusterAlgebras.PlabicGraph.not_moveEquivalent_lollipopPlabicGraph`: a colour obstruction for
  collapsing plabic trees.

## Implementation notes

* The cycle of `σ°` through a dart `x` is `Equiv.Perm.toList σ° x`, the list
  `(x, σ° x, (σ°)² x, …)` up to the length of the cycle. The darts of `X°(G, D)` are symbols
  cut out by a predicate, and the cycle is stated through their symbols.
* A plabic graph with one boundary vertex is an element of `PlabicGraph 1`, as is the lollipop
  graph `L_c`; `{M2, M3}`-equivalence is a relation on this type.
* The colour obstruction runs a maximal sequence of `0`-reduction steps, by strong induction on the
  number of darts, carrying the invariant "every internal leaf is black", together with "every
  white internal vertex has at least three darts, and there is one" when `c` is black.
* In `exists_isHollowDigon_or_isInternalLeaf`, the case `c = x⁺_k` excludes `k = ḡ_i` directly,
  without first showing that the hollow monogon is a monogon: from `σ(\overline{σ(k)}) = k̄ = g_i`
  the dart `σ(k)` would run to `β(i)`, while `σ_X(x⁻_{σ(k)}) = x⁺_k` forces `σ(k)` to run to an
  internal vertex.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset StrandSymbol

/-! ### Cycles of permutations -/

/-- The cycle of a permutation through a point whose cycle has six elements. -/
private theorem Equiv.Perm.toList_eq_of_six {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) {x₀ x₁ x₂ x₃ x₄ x₅ : α} (h₀ : p x₀ = x₁) (h₁ : p x₁ = x₂)
    (h₂ : p x₂ = x₃) (h₃ : p x₃ = x₄) (h₄ : p x₄ = x₅)
    (hcard : (p.cycleOf x₀).support.card = 6) :
    p.toList x₀ = [x₀, x₁, x₂, x₃, x₄, x₅] := by
  apply List.ext_getElem
  · rw [Equiv.Perm.length_toList, hcard]
    rfl
  · intro n h₁' h₂'
    rw [Equiv.Perm.getElem_toList]
    have hn : n < 6 := by simpa using h₂'
    interval_cases n <;>
      simp [pow_succ', Equiv.Perm.mul_apply, h₀, h₁, h₂, h₃, h₄]

/-- The iterates of `x` under a map swapping `x` and `y` are `x` or `y`. -/
private theorem iterate_eq_or_eq_of_swap {α : Type*} {f : α → α} {x y : α}
    (h₁ : f x = y) (h₂ : f y = x) : ∀ n, f^[n] x = x ∨ f^[n] x = y
  | 0 => Or.inl rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    rcases iterate_eq_or_eq_of_swap h₁ h₂ n with h | h <;> rw [h]
    exacts [Or.inr h₁, Or.inl h₂]

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)

/-- A dart `d ∉ B` at a triple point whose orbit under the strand map is `{d, e}`, with `e` at a
triple point as well, gives a closed strand. -/
private theorem exists_isClosedStrand_of_strandMap {d e : H} (hd : d ∉ X.bdry)
    (h₁ : X.strandMap d = e) (h₂ : X.strandMap e = d)
    (hdv : ¬X.IsBoundaryVertex (X.vertexOf d)) (hev : ¬X.IsBoundaryVertex (X.vertexOf e)) :
    ∃ C, X.IsClosedStrand C := by
  refine ⟨X.strandOrbit d, d, hd, rfl, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := X.mem_strandOrbit.1 hx
  rcases iterate_eq_or_eq_of_swap h₁ h₂ k with h | h <;> rw [h]
  exacts [hdv, hev]

end TripleData

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  {D : Finset H → Finset (Sym2 H)}

/-! ### Chains of length zero and one -/

/-- The chain from a terminal dart ends at once. -/
private theorem chainEnd_eq_self {t : H} (ht : G.IsTerminal t) : G.chainEnd t = t := by
  rw [chainEnd_def, Nat.le_zero.1 (chainLength_le (j := 0) ht)]
  rfl

/-- The chain from a dart that is not terminal, but whose image under the trip map is, ends at
that image. -/
private theorem chainEnd_eq_tripMap {d : H} (hd : ¬G.IsTerminal d)
    (ht : G.IsTerminal (G.tripMap d)) : G.chainEnd d = G.tripMap d := by
  have h1 : G.chainLength d ≤ 1 := chainLength_le (j := 1) ht
  have h0 : G.chainLength d ≠ 0 := by
    intro h
    have := chainLength_spec (d := d) ⟨1, ht⟩
    rw [h] at this
    exact hd this
  have h : G.chainLength d = 1 := by omega
  rw [chainEnd_def, h]
  rfl

/-! ### Vertices of a plabic graph -/

/-- The colour of a dart at an internal vertex is that of every dart of the vertex. -/
private theorem colour_eq_of_mem_vertexOf (hG : G.IsPlabicGraph) {x y : H}
    (hx : ¬G.IsBoundaryVertex (G.vertexOf x)) (hy : y ∈ G.vertexOf x) :
    G.colour y = G.colour x :=
  colour_eq_of_sameCycle hG hx ((RotationSystem.mem_vertexOf _).1 hy)

/-- A dart equal to `σ⁻¹ x` lies at the vertex of `x`. -/
private theorem vertexOf_eq_of_rot_symm_eq {x y : H} (h : G.rot.symm x = y) :
    G.vertexOf y = G.vertexOf x := by
  subst h
  exact G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf x)

/-- At an internal vertex that is not a crossing, the turn sends `σ⁻¹ x` back to `x`, provided
`σ⁻¹ x ≠ x`: at a black vertex this is `σ(σ⁻¹ x) = x`, and a white vertex that is not a crossing
has exactly the two darts `x` and `σ⁻¹ x`. -/
private theorem turn_rot_symm_of_not_isCrossing (hG : G.IsPlabicGraph) {x : H}
    (hint : ¬G.IsBoundaryVertex (G.vertexOf x)) (hnc : ¬G.IsCrossing (G.vertexOf x))
    (hne : G.rot.symm x ≠ x) : G.turn (G.rot.symm x) = x := by
  have hv : G.vertexOf (G.rot.symm x) = G.vertexOf x :=
    G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf x)
  have hint' : ¬G.IsBoundaryVertex (G.vertexOf (G.rot.symm x)) := hv ▸ hint
  have hc : G.colour (G.rot.symm x) = G.colour x :=
    colour_eq_of_mem_vertexOf hG hint (G.rot_symm_mem_vertexOf x)
  cases hcol : G.colour x with
  | black =>
    rw [turn_of_black hint' (hc.trans hcol), Equiv.apply_symm_apply]
  | white =>
    rw [turn_of_white hint' (hc.trans hcol)]
    have hcard : (G.vertexOf x).card < 3 := by
      by_contra h3
      refine hnc ⟨G.vertexOf_mem_internalVertices.2 hint, fun y hy => ?_, not_lt.1 h3⟩
      rw [colour_eq_of_mem_vertexOf hG hint hy, hcol]
    have hsub : {x, G.rot.symm x} ⊆ G.vertexOf x :=
      insert_subset_iff.2
        ⟨G.self_mem_vertexOf _, singleton_subset_iff.2 (G.rot_symm_mem_vertexOf _)⟩
    have h2 : ({x, G.rot.symm x} : Finset H).card = 2 := card_pair hne.symm
    have heq : ({x, G.rot.symm x} : Finset H) = G.vertexOf x :=
      eq_of_subset_of_card_le hsub (by omega)
    have hmem : G.rot.symm (G.rot.symm x) ∈ G.vertexOf x :=
      hv ▸ G.rot_symm_mem_vertexOf _
    rw [← heq] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    exact hmem.resolve_right fun h => hne (G.rot.symm.injective h)

/-! ### The strand diagram at an ear -/

section Ear

variable (hG : G.IsPlabicGraph) (hD : G.IsWhiteDatum D) {w : Finset H} (hw : G.IsCrossing w)
  {a : H} (hτ : G.IsCornerTriangle w (D w) {G.rot a, a, G.rot.symm a})

include hG hD hw hτ

/-- **The rotation of the strand diagram at an ear.** If `{σ(a), a, σ⁻¹(a)}` is a triangle of
`D_w`, the rotation `σ°` runs
`x⁺_a ↦ x⁻_{ā} ↦ x⁺_{σ(a)} ↦ x⁻_{\overline{σ(a)}} ↦ q₁ ↦ q₂ ↦ x⁺_a`, where `(q₁, q₂)` is the pair
`P_τ(σ⁻¹(a), σ(a))` of the triangle `τ = {σ(a), a, σ⁻¹(a)}`. -/
theorem IsWhiteDatum.strandRotSym_ear :
    G.strandRotSym D (xPlus a) = xMinus (G.inv a) ∧
      G.strandRotSym D (xMinus (G.inv a)) = xPlus (G.rot a) ∧
      G.strandRotSym D (xPlus (G.rot a)) = xMinus (G.inv (G.rot a)) ∧
      G.strandRotSym D (xMinus (G.inv (G.rot a))) =
        G.pairOut {G.rot a, a, G.rot.symm a} (G.rot.symm a) ∧
      G.strandRotSym D (G.pairOut {G.rot a, a, G.rot.symm a} (G.rot.symm a)) =
        G.pairIn {G.rot a, a, G.rot.symm a} (G.rot.symm a) ∧
      G.strandRotSym D (G.pairIn {G.rot a, a, G.rot.symm a} (G.rot.symm a)) = xPlus a := by
  set τ : Finset H := {G.rot a, a, G.rot.symm a} with hτdef
  have hT : G.IsDatumTriangle D τ := ⟨w, hw, hτ⟩
  have m0 : G.rot a ∈ τ := by simp [hτdef]
  have m1 : a ∈ τ := by simp [hτdef]
  have m2 : G.rot.symm a ∈ τ := by simp [hτdef]
  have c1 : G.cornerNext τ a = G.rot.symm a := hD.cornerNext_eq_rot_symm hT m1 m2
  have c0 : G.cornerNext τ (G.rot a) = a := by
    have := hD.cornerNext_eq_rot_symm hT m0 (by rw [Equiv.symm_apply_apply]; exact m1)
    rwa [Equiv.symm_apply_apply] at this
  have c2 : G.cornerNext τ (G.rot.symm a) = G.rot a := by
    have := hD.cornerNext_three hT m0
    rwa [c0, c1] at this
  have po1 : G.pairOut τ a = xPlus a := by rw [pairOut, if_pos c1]
  have pi1 : G.pairIn τ a = xMinus (G.inv a) := by rw [pairIn, if_pos c1]
  have po0 : G.pairOut τ (G.rot a) = xPlus (G.rot a) := by
    rw [pairOut, if_pos (c0.trans (Equiv.symm_apply_apply _ _).symm)]
  have pi0 : G.pairIn τ (G.rot a) = xMinus (G.inv (G.rot a)) := by
    rw [pairIn, if_pos (c0.trans (Equiv.symm_apply_apply _ _).symm)]
  refine ⟨?_, ?_, ?_, ?_, strandRotSym_pairOut hG hT m2, ?_⟩
  · rw [← po1, strandRotSym_pairOut hG hT m1, pi1]
  · rw [← pi1, strandRotSym_pairIn hG hD hT m1, c1, c2, po0]
  · rw [← po0, strandRotSym_pairOut hG hT m0, pi0]
  · rw [← pi0, strandRotSym_pairIn hG hD hT m0, c0, c1]
  · rw [strandRotSym_pairIn hG hD hT m2, c2, c0, po1]

/-- Three steps of the rotation at an ear: `(σ°)³(x⁻_{\overline{σ(a)}}) = x⁺_a`. -/
theorem IsWhiteDatum.strandRotSym_three_ear :
    G.strandRotSym D (G.strandRotSym D (G.strandRotSym D (xMinus (G.inv (G.rot a))))) =
      xPlus a := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := hD.strandRotSym_ear hG hw hτ
  rw [h4, h5, h6]

/-- **The strand diagram at an ear**. Let `G` be a plabic graph, `D` a white datum, `w` a crossing
and `a ∈ w` such that `{σ(a), a, σ⁻¹(a)}` is a triangle of `D_w` (which forces `a ∈ w`). Then the
cycle of the rotation `σ°` of `X°(G, D)` through the dart `x⁺_a` is
`(x⁺_a, x⁻_{ā}, x⁺_{σ(a)}, x⁻_{\overline{σ(a)}}, q₁, q₂)` for some darts `q₁, q₂`. -/
@[cluster_algebras "lem_ear_cycle"]
theorem IsWhiteDatum.map_val_toList_strandRot_ear :
    ∃ x q₁ q₂ : G.StrandDart D, x.1 = xPlus a ∧
      ((G.strandDiagram hG hD).rot.toList x).map Subtype.val =
        [xPlus a, xMinus (G.inv a), xPlus (G.rot a), xMinus (G.inv (G.rot a)), q₁.1, q₂.1] := by
  set τ : Finset H := {G.rot a, a, G.rot.symm a} with hτdef
  have hT : G.IsDatumTriangle D τ := ⟨w, hw, hτ⟩
  have m1 : a ∈ τ := by simp [hτdef]
  have m2 : G.rot.symm a ∈ τ := by simp [hτdef]
  have c1 : G.cornerNext τ a = G.rot.symm a := hD.cornerNext_eq_rot_symm hT m1 m2
  have po1 : G.pairOut τ a = xPlus a := by rw [pairOut, if_pos c1]
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hD.strandRotSym_ear hG hw hτ
  set X := G.strandDiagram hG hD
  have hx := isStrandSymbol_pairOut hD hT m1
  rw [po1] at hx
  have hy₂ := isStrandSymbol_strandRotSym hG hD hx
  rw [h1] at hy₂
  have hy₃ := isStrandSymbol_strandRotSym hG hD hy₂
  rw [h2] at hy₃
  have hy₄ := isStrandSymbol_strandRotSym hG hD hy₃
  rw [h3] at hy₄
  have hq₁ := isStrandSymbol_pairOut hD hT m2
  have hq₂ := isStrandSymbol_pairIn hG hD hT m2
  refine ⟨⟨_, hx⟩, ⟨_, hq₁⟩, ⟨_, hq₂⟩, rfl, ?_⟩
  have hcard : (X.rot.cycleOf ⟨_, hx⟩).support.card = 6 := by
    have hsupp : (X.rot.cycleOf ⟨_, hx⟩).support = X.vertexOf ⟨_, hx⟩ := by
      have hmem : (⟨_, hx⟩ : G.StrandDart D) ∈ X.rot.support := by
        rw [Equiv.Perm.mem_support]
        intro h
        have := congrArg Subtype.val h
        rw [strandDiagram_rot_apply, h1] at this
        simp at this
      ext y
      rw [Equiv.Perm.mem_support_cycleOf_iff, RotationSystem.mem_vertexOf]
      exact ⟨fun h => h.1, fun h => ⟨h, hmem⟩⟩
    have hx' : (⟨_, hx⟩ : G.StrandDart D) = ⟨G.pairOut τ a, isStrandSymbol_pairOut hD hT m1⟩ :=
      Subtype.ext po1.symm
    rw [hsupp, hx', strandDiagram_vertexOf_pairOut hG hD hT m1, card_strandTriplePoint hG hD hT]
  rw [Equiv.Perm.toList_eq_of_six X.rot (x₀ := ⟨_, hx⟩) (x₁ := ⟨_, hy₂⟩) (x₂ := ⟨_, hy₃⟩)
    (x₃ := ⟨_, hy₄⟩) (x₄ := ⟨_, hq₁⟩) (x₅ := ⟨_, hq₂⟩) (Subtype.ext h1) (Subtype.ext h2)
    (Subtype.ext h3) (Subtype.ext h4) (Subtype.ext h5) hcard]
  rfl

end Ear

/-! ### Darts of the strand diagram at triple points -/

section TriplePoints

variable (hG : G.IsPlabicGraph) (hD : G.IsWhiteDatum D)

include hG hD

/-- A dart `x⁺_p`, with `p` at a crossing, lies at a triple point of the strand diagram. -/
private theorem not_isBoundaryVertex_strandDiagram_xPlus {p : H}
    (hp : G.IsCrossing (G.vertexOf p)) (hx : G.IsStrandSymbol D (xPlus p)) :
    ¬(G.strandDiagram hG hD).IsBoundaryVertex
      ((G.strandDiagram hG hD).vertexOf ⟨xPlus p, hx⟩) := by
  obtain ⟨hT, hs⟩ := hD.sideTriangle_spec hp
  have hp₁ : p ∈ G.sideTriangle D p := mem_sym2_iff.1 hs p (Sym2.mem_mk_left _ _)
  have hp₂ : G.rot.symm p ∈ G.sideTriangle D p := mem_sym2_iff.1 hs _ (Sym2.mem_mk_right _ _)
  have he : (⟨xPlus p, hx⟩ : G.StrandDart D) =
      ⟨G.pairOut (G.sideTriangle D p) p, isStrandSymbol_pairOut hD hT hp₁⟩ :=
    Subtype.ext (by
      change xPlus p = G.pairOut (G.sideTriangle D p) p
      rw [pairOut, if_pos (hD.cornerNext_eq_rot_symm hT hp₁ hp₂)])
  rw [he, strandDiagram_vertexOf_pairOut hG hD hT hp₁]
  exact ((G.strandDiagram hG hD).mem_internalVertices.1
    ((mem_strandDiagram_internalVertices hG hD).2 ⟨_, hT, rfl⟩)).2

/-- A dart `x⁻_t`, with `t̄` at a crossing, lies at a triple point of the strand diagram. -/
private theorem not_isBoundaryVertex_strandDiagram_xMinus {t : H}
    (ht : G.IsCrossing (G.vertexOf (G.inv t))) (hx : G.IsStrandSymbol D (xMinus t)) :
    ¬(G.strandDiagram hG hD).IsBoundaryVertex
      ((G.strandDiagram hG hD).vertexOf ⟨xMinus t, hx⟩) := by
  have hinit : G.IsInitial (G.inv t) :=
    ⟨fun h => (hx : G.IsTerminal t).1 (hG.inv_mem_bdry_iff.1 h), Or.inl ht⟩
  have hrot : (G.strandDiagram hG hD).rot ⟨xPlus (G.inv t), hinit⟩ = ⟨xMinus t, hx⟩ := by
    refine Subtype.ext ?_
    change G.strandRotSym D (xPlus (G.inv t)) = xMinus t
    rw [strandRotSym, dif_neg (hG.not_isLeg_of_isCrossing ht), hG.inv_involutive]
  rw [← hrot, RotationSystem.vertexOf_rot]
  exact not_isBoundaryVertex_strandDiagram_xPlus hG hD ht hinit

/-- A dart `x⁺_p` of the strand diagram is not a boundary dart. -/
private theorem xPlus_notMem_strandDiagram_bdry {p : H} (hp : G.IsStrandSymbol D (xPlus p)) :
    (⟨xPlus p, hp⟩ : G.StrandDart D) ∉ (G.strandDiagram hG hD).bdry := by
  rw [mem_strandDiagram_bdry]
  simp [StrandSymbol.IsBoundary]

/-- A dart `x⁻_t` of the strand diagram is not a boundary dart. -/
private theorem xMinus_notMem_strandDiagram_bdry {t : H} (ht : G.IsStrandSymbol D (xMinus t)) :
    (⟨xMinus t, ht⟩ : G.StrandDart D) ∉ (G.strandDiagram hG hD).bdry := by
  rw [mem_strandDiagram_bdry]
  simp [StrandSymbol.IsBoundary]

/-- The strand map at `x⁺_p`, when the chain from `p` ends at a dart `t` with `t̄` at a crossing:
`S(x⁺_p) = (σ°)³(x⁻_t)`. -/
private theorem coe_strandMap_xPlus {p t : H} (hx : G.IsStrandSymbol D (xPlus p))
    (hend : G.chainEnd p = t) (ht : G.IsCrossing (G.vertexOf (G.inv t))) :
    ((G.strandDiagram hG hD).strandMap ⟨xPlus p, hx⟩).1 =
      G.strandRotSym D (G.strandRotSym D (G.strandRotSym D (xMinus t))) := by
  have hxt : G.IsStrandSymbol D (xMinus t) := hend ▸ (hx : G.IsInitial p).isTerminal_chainEnd hG
  have hinv : (G.strandDiagram hG hD).inv ⟨xPlus p, hx⟩ = ⟨xMinus t, hxt⟩ :=
    Subtype.ext (by
      change xMinus (G.chainEnd p) = xMinus t
      rw [hend])
  have hnr : ¬(G.strandDiagram hG hD).RunsToEndpoint ⟨xPlus p, hx⟩ := by
    unfold TripleData.RunsToEndpoint
    rw [hinv]
    exact not_isBoundaryVertex_strandDiagram_xMinus hG hD ht hxt
  rw [(G.strandDiagram hG hD).strandMap_of_not_runsToEndpoint hnr, hinv]
  rfl

end TriplePoints

/-! ### Stray leaves and hollow digons -/

section Forbidden

variable (hG : G.IsPlabicGraph)

include hG

/-- **A stray leaf at a crossing gives a hollow monogon**. Let `G` be a plabic graph, `D` a white
datum, and `u` an internal leaf of `G` whose dart `k` runs to a crossing. Then `x⁻_k` is a dart of
`X°(G, D)` outside `B°`, and the face permutation `φ°` of `X°(G, D)` fixes it. -/
@[cluster_algebras "lem_leaf_strand_monogon"]
theorem IsWhiteDatum.strandDiagram_facePerm_xMinus_of_isInternalLeaf (hD : G.IsWhiteDatum D)
    {u : Finset H} (hu : G.IsInternalLeaf u) {k : H} (hk : k ∈ u)
    (hc : G.IsCrossing (G.vertexOf (G.inv k))) :
    ∃ hx : G.IsStrandSymbol D (xMinus k),
      (⟨xMinus k, hx⟩ : G.StrandDart D) ∉ (G.strandDiagram hG hD).bdry ∧
        (G.strandDiagram hG hD).facePerm ⟨xMinus k, hx⟩ = ⟨xMinus k, hx⟩ := by
  obtain ⟨hui, hu1⟩ := hu
  obtain ⟨huV, hub⟩ := G.mem_internalVertices.1 hui
  obtain ⟨e, rfl⟩ := G.mem_vertices.1 huV
  have hvk : G.vertexOf k = G.vertexOf e := G.vertexOf_eq_of_mem hk
  rw [← hvk] at hub hu1
  have hrot : G.rot k = k := by
    obtain ⟨z, hz⟩ := card_eq_one.1 hu1
    have h1 := G.rot_mem_vertexOf k
    have h2 := G.self_mem_vertexOf k
    rw [hz, mem_singleton] at h1 h2
    rw [h1, h2]
  have hrot' : G.rot.symm k = k := G.rot.symm_apply_eq.2 hrot.symm
  have hkB : k ∉ G.bdry := notMem_bdry_of_mem_vertexOf hub (G.self_mem_vertexOf k)
  have hikB : G.inv k ∉ G.bdry := fun h => hkB (hG.inv_mem_bdry_iff.1 h)
  have hkT : G.IsTerminal k := ⟨hkB, Or.inl hc⟩
  have hinit : G.IsInitial (G.inv k) := ⟨hikB, Or.inl hc⟩
  have hT : G.tripMap (G.inv k) = k := by
    rw [tripMap_apply, hG.inv_involutive]
    cases hcol : G.colour k
    · rw [turn_of_white hub hcol, hrot']
    · rw [turn_of_black hub hcol, hrot]
  have hnT : ¬G.IsTerminal (G.inv k) := by
    rintro ⟨-, h | h⟩ <;> rw [hG.inv_involutive] at h
    · have := h.three_le_card
      omega
    · exact hub h
  have hend : G.chainEnd (G.inv k) = k := by
    rw [chainEnd_eq_tripMap hnT (by rwa [hT]), hT]
  have hs := hinit.chainStart_chainEnd hG
  rw [hend] at hs
  refine ⟨hkT, xMinus_notMem_strandDiagram_bdry hG hD hkT, Subtype.ext ?_⟩
  rw [RotationSystem.facePerm_apply]
  change G.strandRotSym D (xPlus (G.chainStart k)) = xMinus k
  rw [hs, strandRotSym, dif_neg (hG.not_isLeg_of_isCrossing hc), hG.inv_involutive]

/-- **A hollow digon without crossings gives a trip without initial dart**. Let `G` be a plabic
graph with a hollow digon `{d₁, d₂}` such that neither `v(d₁)` nor `v(d₂)` is a crossing. Then
`{d₁, d₂}` is an orbit of the trip map of `G` containing no initial dart. -/
@[cluster_algebras "lem_digon_no_crossing"]
theorem IsPlabicGraph.trip_eq_of_isHollowDigon {d₁ d₂ : H} (h : G.IsHollowDigon {d₁, d₂})
    (h₁ : ¬G.IsCrossing (G.vertexOf d₁)) (h₂ : ¬G.IsCrossing (G.vertexOf d₂)) :
    G.trip d₁ = {d₁, d₂} ∧ ∀ d ∈ G.trip d₁, ¬G.IsInitial d := by
  obtain ⟨hb₁, hb₂, ⟨-, -, hne₁, hr₁⟩, ⟨-, -, hne₂, hr₂⟩⟩ := hG.toIsDiskMap.hollowDigon_shape h
  have hT₂ : G.tripMap d₂ = d₁ := by
    rw [tripMap_apply, ← hr₁]
    exact turn_rot_symm_of_not_isCrossing hG hb₁ h₁ (by rw [hr₁]; exact hne₁.symm)
  have hT₁ : G.tripMap d₁ = d₂ := by
    rw [tripMap_apply, ← hr₂]
    exact turn_rot_symm_of_not_isCrossing hG hb₂ h₂ (by rw [hr₂]; exact hne₂.symm)
  have htrip : G.trip d₁ = {d₁, d₂} := by
    ext x
    simp only [trip, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact iterate_eq_or_eq_of_swap hT₁ hT₂ n
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, hT₁⟩
  refine ⟨htrip, ?_⟩
  rw [htrip]
  intro d hd hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  obtain ⟨-, hc | hl⟩ := hi
  · rcases hd with rfl | rfl
    exacts [h₁ hc, h₂ hc]
  · have := hG.isBoundaryVertex_of_isLeg hl
    rcases hd with rfl | rfl
    exacts [hb₁ this, hb₂ this]

/-- **A bicoloured hollow digon at a crossing gives a hollow monogon**. Let `G` be a plabic graph
with a hollow digon `{d₁, d₂}` such that `v(d₁)` is black and `v(d₂)` is a crossing, and let `D` be
a white datum of `G` such that `{d₂, d̄₁, σ⁻¹(d̄₁)}` is a triangle of `D_{v(d₂)}`. Then `x⁺_{d₂}`
is a dart of `X°(G, D)` outside `B°`, and the face permutation `φ°` fixes it. -/
@[cluster_algebras "lem_digon_strand_monogon"]
theorem IsWhiteDatum.strandDiagram_facePerm_xPlus_of_isHollowDigon (hD : G.IsWhiteDatum D)
    {d₁ d₂ : H} (h : G.IsHollowDigon {d₁, d₂}) (hb : G.colour d₁ = .black)
    (hc : G.IsCrossing (G.vertexOf d₂))
    (hτ : G.IsCornerTriangle (G.vertexOf d₂) (D (G.vertexOf d₂))
      {d₂, G.inv d₁, G.rot.symm (G.inv d₁)}) :
    ∃ hx : G.IsStrandSymbol D (xPlus d₂),
      (⟨xPlus d₂, hx⟩ : G.StrandDart D) ∉ (G.strandDiagram hG hD).bdry ∧
        (G.strandDiagram hG hD).facePerm ⟨xPlus d₂, hx⟩ = ⟨xPlus d₂, hx⟩ := by
  obtain ⟨hb₁, hb₂, ⟨-, -, -, hr₁⟩, ⟨-, -, -, hr₂⟩⟩ := hG.toIsDiskMap.hollowDigon_shape h
  have hd₁B : d₁ ∉ G.bdry := notMem_bdry_of_mem_vertexOf hb₁ (G.self_mem_vertexOf d₁)
  have hd₂B : d₂ ∉ G.bdry := notMem_bdry_of_mem_vertexOf hb₂ (G.self_mem_vertexOf d₂)
  have hv₁ : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := vertexOf_eq_of_rot_symm_eq hr₁
  have hv₂ : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := vertexOf_eq_of_rot_symm_eq hr₂
  have hinit : G.IsInitial d₂ := ⟨hd₂B, Or.inl hc⟩
  have hT : G.tripMap d₂ = d₁ := by
    rw [tripMap_apply, ← hr₁]
    have hint' : ¬G.IsBoundaryVertex (G.vertexOf (G.rot.symm d₁)) := by
      rw [G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf d₁)]
      exact hb₁
    rw [turn_of_black hint'
      ((colour_eq_of_mem_vertexOf hG hb₁ (G.rot_symm_mem_vertexOf d₁)).trans hb),
      Equiv.apply_symm_apply]
  have hnT : ¬G.IsTerminal d₂ := by
    rintro ⟨-, h' | h'⟩ <;> rw [hv₁] at h'
    · have := h'.2.1 d₁ (G.self_mem_vertexOf d₁)
      rw [hb] at this
      exact absurd this (by decide)
    · exact hb₁ h'
  have hT₁ : G.IsTerminal d₁ := ⟨hd₁B, Or.inl (hv₂ ▸ hc)⟩
  have hend : G.chainEnd d₂ = d₁ := by
    rw [chainEnd_eq_tripMap hnT (by rwa [hT]), hT]
  have hra : G.rot (G.inv d₁) = d₂ := (G.rot.symm_apply_eq.1 hr₂).symm
  have hτ' : G.IsCornerTriangle (G.vertexOf d₂) (D (G.vertexOf d₂))
      {G.rot (G.inv d₁), G.inv d₁, G.rot.symm (G.inv d₁)} := by
    rwa [hra]
  obtain ⟨-, h2, -⟩ := hD.strandRotSym_ear hG hc hτ'
  rw [hG.inv_involutive, hra] at h2
  refine ⟨hinit, xPlus_notMem_strandDiagram_bdry hG hD hinit, Subtype.ext ?_⟩
  rw [RotationSystem.facePerm_apply]
  change G.strandRotSym D (xMinus (G.chainEnd d₂)) = xPlus d₂
  rw [hend, h2]

/-- **A white hollow digon at a crossing gives a closed strand**. Let `G` be a plabic graph with a
hollow digon `{d₁, d₂}` such that `v(d₁)` is a crossing and `v(d₂)` is white, and let `D` be a
white datum of `G` such that `{d₁, d̄₂, σ⁻¹(d̄₂)}` is a triangle of `D_{v(d₁)}` and, if `v(d₂)` is
a crossing, `{d₂, d̄₁, σ⁻¹(d̄₁)}` is a triangle of `D_{v(d₂)}`. Then `X°(G, D)` has a closed
strand. -/
@[cluster_algebras "lem_digon_closed_strand"]
theorem IsWhiteDatum.exists_isClosedStrand_of_isHollowDigon (hD : G.IsWhiteDatum D)
    {d₁ d₂ : H} (h : G.IsHollowDigon {d₁, d₂}) (hc : G.IsCrossing (G.vertexOf d₁))
    (hw : G.colour d₂ = .white)
    (hτ₁ : G.IsCornerTriangle (G.vertexOf d₁) (D (G.vertexOf d₁))
      {d₁, G.inv d₂, G.rot.symm (G.inv d₂)})
    (hτ₂ : G.IsCrossing (G.vertexOf d₂) → G.IsCornerTriangle (G.vertexOf d₂) (D (G.vertexOf d₂))
      {d₂, G.inv d₁, G.rot.symm (G.inv d₁)}) :
    ∃ C, (G.strandDiagram hG hD).IsClosedStrand C := by
  obtain ⟨hb₁, hb₂, ⟨-, -, -, hr₁⟩, ⟨-, -, -, hr₂⟩⟩ := hG.toIsDiskMap.hollowDigon_shape h
  have hd₁B : d₁ ∉ G.bdry := notMem_bdry_of_mem_vertexOf hb₁ (G.self_mem_vertexOf d₁)
  have hd₂B : d₂ ∉ G.bdry := notMem_bdry_of_mem_vertexOf hb₂ (G.self_mem_vertexOf d₂)
  have hi₁B : G.inv d₁ ∉ G.bdry := fun h => hd₁B (hG.inv_mem_bdry_iff.1 h)
  have hi₂B : G.inv d₂ ∉ G.bdry := fun h => hd₂B (hG.inv_mem_bdry_iff.1 h)
  have hv₁ : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := vertexOf_eq_of_rot_symm_eq hr₁
  have hv₂ : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := vertexOf_eq_of_rot_symm_eq hr₂
  have hra₂ : G.rot (G.inv d₂) = d₁ := (G.rot.symm_apply_eq.1 hr₁).symm
  have hra₁ : G.rot (G.inv d₁) = d₂ := (G.rot.symm_apply_eq.1 hr₂).symm
  have hτ₁' : G.IsCornerTriangle (G.vertexOf d₁) (D (G.vertexOf d₁))
      {G.rot (G.inv d₂), G.inv d₂, G.rot.symm (G.inv d₂)} := by
    rwa [hra₂]
  have e₁ := hD.strandRotSym_three_ear hG hc hτ₁'
  rw [hra₂] at e₁
  have hc₁ : G.IsCrossing (G.vertexOf (G.inv (G.inv d₁))) := by
    rwa [hG.inv_involutive]
  have hx₂ : G.IsStrandSymbol D (xPlus (G.inv d₂)) :=
    (⟨hi₂B, Or.inl (hv₁ ▸ hc)⟩ : G.IsInitial (G.inv d₂))
  have hnb₂ := not_isBoundaryVertex_strandDiagram_xPlus hG hD (hv₁ ▸ hc) hx₂
  by_cases hy : G.IsCrossing (G.vertexOf d₂)
  · have hτ₂' : G.IsCornerTriangle (G.vertexOf d₂) (D (G.vertexOf d₂))
        {G.rot (G.inv d₁), G.inv d₁, G.rot.symm (G.inv d₁)} := by
      rw [hra₁]
      exact hτ₂ hy
    have e₂ := hD.strandRotSym_three_ear hG hy hτ₂'
    rw [hra₁] at e₂
    have hc₂ : G.IsCrossing (G.vertexOf (G.inv (G.inv d₂))) := by
      rwa [hG.inv_involutive]
    have hx₁ : G.IsStrandSymbol D (xPlus (G.inv d₁)) :=
      (⟨hi₁B, Or.inl (hv₂ ▸ hy)⟩ : G.IsInitial (G.inv d₁))
    have hend₂ : G.chainEnd (G.inv d₂) = G.inv d₂ := chainEnd_eq_self ⟨hi₂B, Or.inl hc₂⟩
    have hend₁ : G.chainEnd (G.inv d₁) = G.inv d₁ := chainEnd_eq_self ⟨hi₁B, Or.inl hc₁⟩
    exact (G.strandDiagram hG hD).exists_isClosedStrand_of_strandMap
      (xPlus_notMem_strandDiagram_bdry hG hD hx₂)
      (e := ⟨xPlus (G.inv d₁), hx₁⟩)
      (Subtype.ext ((coe_strandMap_xPlus hG hD hx₂ hend₂ hc₂).trans e₂))
      (Subtype.ext ((coe_strandMap_xPlus hG hD hx₁ hend₁ hc₁).trans e₁)) hnb₂
      (not_isBoundaryVertex_strandDiagram_xPlus hG hD (hv₂ ▸ hy) hx₁)
  · have hT : G.tripMap (G.inv d₂) = G.inv d₁ := by
      rw [tripMap_apply, hG.inv_involutive, turn_of_white hb₂ hw, hr₂]
    have hnT : ¬G.IsTerminal (G.inv d₂) := by
      rintro ⟨-, h' | h'⟩ <;> rw [hG.inv_involutive] at h'
      exacts [hy h', hb₂ h']
    have hend : G.chainEnd (G.inv d₂) = G.inv d₁ := by
      rw [chainEnd_eq_tripMap hnT (hT ▸ ⟨hi₁B, Or.inl hc₁⟩), hT]
    have hS : (G.strandDiagram hG hD).strandMap ⟨xPlus (G.inv d₂), hx₂⟩ =
        ⟨xPlus (G.inv d₂), hx₂⟩ :=
      Subtype.ext ((coe_strandMap_xPlus hG hD hx₂ hend hc₁).trans e₁)
    exact (G.strandDiagram hG hD).exists_isClosedStrand_of_strandMap
      (xPlus_notMem_strandDiagram_bdry hG hD hx₂) hS hS hnb₂ hnb₂

end Forbidden

end PlabicData

/-! ### Hollow monogons of the triple diagram of a normal plabic graph -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] (M : DiskMap H)

/-- An orbit `{x, y}` of the face permutation, with `φ x = y` and `φ y = x`. -/
private theorem faceOf_eq_pair {x y : H} (h₁ : M.facePerm x = y) (h₂ : M.facePerm y = x) :
    M.faceOf x = {x, y} := by
  ext z
  rw [RotationSystem.mem_faceOf, mem_insert, mem_singleton]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    simpa only [← Equiv.Perm.iterate_eq_pow] using iterate_eq_or_eq_of_swap h₁ h₂ n
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← h₁]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)

end DiskMap

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- If `ι σ ι σ k = k` for a black dart `k` with `σ k` not a leg, then the face through `σ k` is a
hollow digon. -/
private theorem exists_isHollowDigon_of_inv_rot_inv_rot (hG : G.IsNormalPlabicGraph) {k : H}
    (hk : k ∈ G.blackDarts) (hl' : G.legIndex (G.rot k) = none)
    (hψ : G.inv (G.rot (G.inv (G.rot k))) = k) : ∃ g, G.IsHollowDigon g := by
  have hP := hG.isNormalPlabicPregraph
  have hrkm : G.rot k ∈ G.blackDarts := hP.rot_mem_blackDarts hk
  have hrk : G.rot (G.inv (G.rot k)) = G.inv k := by
    have := congrArg G.inv hψ
    rwa [hP.inv_inv] at this
  have hk' := hP.not_isBoundaryVertex_inv hrkm hl'
  have hl : G.legIndex k = none := by
    rcases hl : G.legIndex k with _ | i
    · rfl
    · exfalso
      have h1 : G.inv k = G.leg i := by
        rw [← inv_leg_of_legIndex_eq_some hl, hP.inv_inv]
      have h2 : G.inv (G.rot k) ∈ G.vertexOf (G.leg i) := by
        rw [← h1, ← hrk, RotationSystem.vertexOf_rot]
        exact G.self_mem_vertexOf _
      exact hk' (G.vertexOf_eq_of_mem h2 ▸ hP.isBoundaryVertex_leg i)
  have hcol := hP.colour_inv hk hl
  have hrkb := mem_blackDarts.1 hrkm
  have hrkB : G.rot k ∉ G.bdry := notMem_bdry_of_mem_blackDarts hrkm
  have hikB : G.inv k ∉ G.bdry :=
    notMem_bdry_of_mem_vertexOf (hP.not_isBoundaryVertex_inv hk hl) (G.self_mem_vertexOf _)
  have hface : G.faceOf (G.rot k) = {G.rot k, G.inv k} :=
    G.toDiskMap.faceOf_eq_pair (by rw [RotationSystem.facePerm_apply, hrk])
      (by rw [RotationSystem.facePerm_apply, hP.inv_inv])
  refine ⟨{G.rot k, G.inv k}, G.mem_internalFaces.2 ⟨?_, ?_⟩, G.rot k, G.inv k, rfl, ?_⟩
  · rw [← hface]
    exact G.faceOf_mem_faces hrkB
  · rw [disjoint_left]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [hrkB, hikB]
  · intro he
    have hmem : G.inv k ∈ G.vertexOf (G.rot k) := he ▸ G.self_mem_vertexOf _
    have := colour_eq_of_mem_vertexOf hG.toIsPlabicGraph hrkb.1 hmem
    rw [hcol, hrkb.2] at this
    exact absurd this (by decide)

/-- A black dart `m` fixed by `σ` with `σ⁻¹ m` not a leg forms an internal leaf `{m}` that is not a
lollipop. -/
private theorem exists_isInternalLeaf_of_rot_symm_eq_self (hG : G.IsNormalPlabicGraph) {m : H}
    (hm : m ∈ G.blackDarts) (hkm : G.rot.symm m = m) (hl : G.legIndex (G.rot.symm m) = none) :
    ∃ v, G.IsInternalLeaf v ∧ ∀ i, ¬G.IsLollipop i v := by
  have hP := hG.isNormalPlabicPregraph
  have hfix : G.rot m = m := (G.rot.symm_apply_eq.1 hkm).symm
  have hmb := mem_blackDarts.1 hm
  have hv : G.vertexOf m = {m} := by
    ext z
    rw [RotationSystem.mem_vertexOf, mem_singleton]
    exact ⟨fun h => (h.eq_of_left hfix).symm, fun h => h ▸ Equiv.Perm.SameCycle.refl _ _⟩
  refine ⟨G.vertexOf m, ⟨G.vertexOf_mem_internalVertices.2 hmb.1, by rw [hv]; rfl⟩, ?_⟩
  rintro i ⟨-, d, hd, hdi⟩
  rw [hv, mem_singleton] at hd
  rw [hd] at hdi
  have hb : G.IsBoundaryVertex (G.vertexOf (G.inv m)) := by
    rw [G.vertexOf_eq_of_mem hdi]
    exact G.vertexOf_mem_boundaryVertices.1 (hP.bvertex_mem i)
  have := hP.not_isBoundaryVertex_inv (hP.rot_symm_mem_blackDarts hm) hl
  rw [hkm] at this
  exact this hb

/-- **A hollow monogon of `X(G)` is a forbidden configuration of `G`**. Let `G` be a normal plabic
graph such that the triple diagram `X(G)` has a hollow monogon. Then `G` contains a hollow digon or
an internal leaf that is not a lollipop. -/
@[cluster_algebras "lem_normal_hollow_monogon"]
theorem IsNormalPlabicGraph.exists_isHollowDigon_or_isInternalLeaf
    (hG : G.IsNormalPlabicGraph) {f : Finset G.TripleDart}
    (hf : (G.tripleOfNormal hG.isNormalPlabicPregraph).IsHollowMonogon f) :
    (∃ g, G.IsHollowDigon g) ∨ ∃ v, G.IsInternalLeaf v ∧ ∀ i, ¬G.IsLollipop i v := by
  have hP := hG.isNormalPlabicPregraph
  obtain ⟨c, rfl⟩ := card_eq_one.1 hf.2
  obtain ⟨hcB, hφ⟩ := hf.facePerm_eq
  rcases c with k | m | r | r
  · left
    rw [hP.facePerm_tripleOfNormal_plus] at hφ
    set k' : G.BlackDart := ⟨G.rot k, hP.rot_mem_blackDarts k.2⟩
    rcases hl' : G.legIndex k' with _ | i
    · rw [hP.tripleRot_minus_of_none hl', TripleOfNormalDart.plus.injEq] at hφ
      exact exists_isHollowDigon_of_inv_rot_inv_rot hG k.2 hl' (congrArg Subtype.val hφ)
    · rw [hP.tripleRot_minus_of_some hl'] at hφ
      exact absurd hφ (by simp)
  · right
    rw [hP.facePerm_tripleOfNormal_minus] at hφ
    set k : G.BlackDart := ⟨G.rot.symm m, hP.rot_symm_mem_blackDarts m.2⟩
    rcases hl : G.legIndex k with _ | i
    · rw [hP.tripleRot_plus_of_none hl, TripleOfNormalDart.minus.injEq] at hφ
      exact exists_isInternalLeaf_of_rot_symm_eq_self hG m.2 (congrArg Subtype.val hφ) hl
    · rw [hP.tripleRot_plus_of_some hl] at hφ
      exact absurd hφ (by simp)
  · exact absurd (hP.mem_tripleOfNormal_bdry.2 rfl) hcB
  · exact absurd (hP.mem_tripleOfNormal_bdry.2 rfl) hcB

end PlabicData

/-! ### A colour obstruction for collapsing plabic trees -/

namespace PlabicData

open Function

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

/-- Every internal leaf of `X` is black (in terms of darts). -/
private def LeavesBlack (X : PlabicData H b) : Prop :=
  ∀ d, X.IsInternalLeaf (X.vertexOf d) → X.colour d = .black

/-- Every white internal vertex of `X` has at least three darts, and `X` has a white internal
vertex (in terms of darts). -/
private def WhiteFat (X : PlabicData H b) : Prop :=
  (∀ d, ¬X.IsBoundaryVertex (X.vertexOf d) → X.colour d = .white → 3 ≤ (X.vertexOf d).card) ∧
    ∃ d, ¬X.IsBoundaryVertex (X.vertexOf d) ∧ X.colour d = .white

/-- The invariant of the reduction: `(I1)`, and `(I2)` when `c` is black. -/
private def TreeInvariant (c : Shade) (X : PlabicData H b) : Prop :=
  LeavesBlack X ∧ (c = .black → WhiteFat X)

private theorem isInternalLeaf_vertexOf_iff {X : PlabicData H b} {d : H} :
    X.IsInternalLeaf (X.vertexOf d) ↔
      ¬X.IsBoundaryVertex (X.vertexOf d) ∧ (X.vertexOf d).card = 1 := by
  rw [DiskMap.IsInternalLeaf, X.vertexOf_mem_internalVertices]

private theorem leavesBlack_iff {X : PlabicData H b} :
    LeavesBlack X ↔ ∀ v, X.IsInternalLeaf v → ∀ d ∈ v, X.colour d = .black := by
  refine ⟨fun h v hv d hd => ?_, fun h d hd => h _ hd d (X.self_mem_vertexOf d)⟩
  obtain ⟨e, rfl⟩ := X.mem_vertices.1 (X.mem_internalVertices.1 hv.1).1
  rw [← X.vertexOf_eq_of_mem hd] at hv
  exact h d hv

/-- An internal white vertex of a graph satisfying `(I1)` has at least two darts. -/
private theorem two_le_card_of_leavesBlack {X : PlabicData H b} (h : LeavesBlack X) {d : H}
    (hd : ¬X.IsBoundaryVertex (X.vertexOf d)) (hc : X.colour d = .white) :
    2 ≤ (X.vertexOf d).card := by
  have h0 : 0 < (X.vertexOf d).card := card_pos.2 ⟨d, X.self_mem_vertexOf d⟩
  have h1 : (X.vertexOf d).card ≠ 1 := fun h1 => by
    have := h d (isInternalLeaf_vertexOf_iff.2 ⟨hd, h1⟩)
    rw [hc] at this
    exact absurd this (by decide)
  omega

/-! #### Isomorphisms -/

private theorem Iso.leavesBlack {X : PlabicData H b} {Y : PlabicData H' b} (θ : X.Iso Y)
    (h : LeavesBlack X) : LeavesBlack Y := by
  intro d' hd'
  obtain ⟨d, rfl⟩ := θ.toEquiv.surjective d'
  rw [isInternalLeaf_vertexOf_iff, θ.isBoundaryVertex_vertexOf_iff, ← θ.map_vertexOf,
    card_map] at hd'
  rw [θ.map_colour d hd'.1]
  exact h d (isInternalLeaf_vertexOf_iff.2 hd')

private theorem Iso.whiteFat {X : PlabicData H b} {Y : PlabicData H' b} (θ : X.Iso Y)
    (h : WhiteFat X) : WhiteFat Y := by
  obtain ⟨h1, e, he, hec⟩ := h
  refine ⟨fun d' hd' hc' => ?_, θ.toEquiv e, (θ.isBoundaryVertex_vertexOf_iff e).not.2 he,
    (θ.map_colour e he).trans hec⟩
  obtain ⟨d, rfl⟩ := θ.toEquiv.surjective d'
  rw [θ.isBoundaryVertex_vertexOf_iff] at hd'
  rw [θ.map_colour d hd'] at hc'
  rw [← θ.map_vertexOf, card_map]
  exact h1 d hd' hc'

private theorem Iso.treeInvariant {c : Shade} {X : PlabicData H b} {Y : PlabicData H' b}
    (θ : X.Iso Y) (h : TreeInvariant c X) : TreeInvariant c Y :=
  ⟨θ.leavesBlack h.1, fun hc => θ.whiteFat (h.2 hc)⟩

/-! #### Removal of a bivalent vertex -/

section Removal

variable {X : PlabicData H b} (hX : X.IsPlabicGraph) {d : H} (hd : X.IsBivalentRemovable d)

include hX hd

private theorem card_bivalentRemoval_vertexOf (y : ({d, X.rot d}ᶜ : Set H)) :
    ((X.bivalentRemoval hX hd).vertexOf y).card = (X.vertexOf y).card := by
  rw [← map_bivalentRemoval_vertexOf hX hd y, card_map]

private theorem leavesBlack_bivalentRemoval (h : LeavesBlack X) :
    LeavesBlack (X.bivalentRemoval hX hd) := by
  intro y hy
  rw [isInternalLeaf_vertexOf_iff, isBoundaryVertex_bivalentRemoval_vertexOf_iff hX hd,
    card_bivalentRemoval_vertexOf hX hd] at hy
  exact h y (isInternalLeaf_vertexOf_iff.2 hy)

private theorem whiteFat_bivalentRemoval (h : WhiteFat X) :
    WhiteFat (X.bivalentRemoval hX hd) := by
  obtain ⟨h1, e, he, hec⟩ := h
  refine ⟨fun y hy hyc => ?_, ?_⟩
  · rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff hX hd] at hy
    rw [card_bivalentRemoval_vertexOf hX hd]
    exact h1 y hy hyc
  · have heS : e ∈ ({d, X.rot d}ᶜ : Set H) := by
      rw [Set.mem_compl_iff]
      intro hmem
      have hev : X.vertexOf e = X.vertexOf d := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl
        · rfl
        · exact X.vertexOf_rot d
      have := h1 e he hec
      rw [hev, hd.card_vertexOf] at this
      omega
    exact ⟨⟨e, heS⟩, (isBoundaryVertex_bivalentRemoval_vertexOf_iff hX hd _).not.2 he, hec⟩

end Removal

/-! #### Contraction of an edge -/

section Contraction

variable {X : PlabicData H b} (hX : X.IsPlabicGraph) {d : H} (he : X.IsContractibleEdge d)

include hX he

private theorem card_mergedVertex_add_two :
    (X.mergedVertex d).card + 2 = (X.vertexOf d).card + (X.vertexOf (X.inv d)).card := by
  have hdisj : Disjoint (X.vertexOf d) (X.vertexOf (X.inv d)) := by
    rw [disjoint_left]
    intro z hz hz'
    exact he.vertexOf_ne ((X.vertexOf_eq_of_mem hz).symm.trans (X.vertexOf_eq_of_mem hz'))
  have hsub : ({d, X.inv d} : Finset H) ⊆ X.vertexOf d ∪ X.vertexOf (X.inv d) :=
    insert_subset_iff.2 ⟨mem_union_left _ (X.self_mem_vertexOf _),
      singleton_subset_iff.2 (mem_union_right _ (X.self_mem_vertexOf _))⟩
  have hpair : ({d, X.inv d} : Finset H).card = 2 := card_pair (hX.inv_ne d).symm
  have := card_sdiff_add_card_eq_card hsub
  rw [hpair, card_union_of_disjoint hdisj] at this
  rw [mergedVertex]
  omega

private theorem card_contractEdge_vertexOf_of_mem {x : (({d, X.inv d} : Set H)ᶜ : Set H)}
    (hx : (x : H) ∈ X.vertexOf d ∪ X.vertexOf (X.inv d)) :
    ((X.contractEdge d (he.leg_mem hX)).vertexOf x).card = (X.mergedVertex d).card := by
  rw [← map_vertexOf_contractEdge_of_mem he.not_sameCycle hx, card_map]

private theorem card_contractEdge_vertexOf_of_notMem {x : (({d, X.inv d} : Set H)ᶜ : Set H)}
    (hx : (x : H) ∉ X.vertexOf d ∪ X.vertexOf (X.inv d)) :
    ((X.contractEdge d (he.leg_mem hX)).vertexOf x).card = (X.vertexOf x).card := by
  rw [← map_vertexOf_contractEdge_of_notMem he.not_sameCycle hx, card_map]

private theorem leavesBlack_contractEdge (h : LeavesBlack X) :
    LeavesBlack (X.contractEdge d (he.leg_mem hX)) := by
  intro x hx
  rw [isInternalLeaf_vertexOf_iff, isBoundaryVertex_vertexOf_contractEdge_iff he] at hx
  change X.colour x = .black
  by_cases hxu : (x : H) ∈ X.vertexOf d ∪ X.vertexOf (X.inv d)
  · rw [card_contractEdge_vertexOf_of_mem hX he hxu] at hx
    rw [colour_eq_of_mem_union hX he hxu]
    cases hcd : X.colour d with
    | black => rfl
    | white =>
      have h₁ := two_le_card_of_leavesBlack h he.not_isBoundaryVertex hcd
      have h₂ := two_le_card_of_leavesBlack h he.not_isBoundaryVertex_inv
        (he.colour_inv.trans hcd)
      have := card_mergedVertex_add_two hX he
      omega
  · rw [card_contractEdge_vertexOf_of_notMem hX he hxu] at hx
    exact h x (isInternalLeaf_vertexOf_iff.2 hx)

private theorem whiteFat_contractEdge (h : WhiteFat X) :
    WhiteFat (X.contractEdge d (he.leg_mem hX)) := by
  obtain ⟨h1, e, hei, hec⟩ := h
  have hbig : X.colour d = .white → 4 ≤ (X.mergedVertex d).card := by
    intro hcd
    have h₁ := h1 d he.not_isBoundaryVertex hcd
    have h₂ := h1 _ he.not_isBoundaryVertex_inv (he.colour_inv.trans hcd)
    have := card_mergedVertex_add_two hX he
    omega
  refine ⟨fun x hx hxc => ?_, ?_⟩
  · rw [isBoundaryVertex_vertexOf_contractEdge_iff he] at hx
    change X.colour x = .white at hxc
    by_cases hxu : (x : H) ∈ X.vertexOf d ∪ X.vertexOf (X.inv d)
    · rw [card_contractEdge_vertexOf_of_mem hX he hxu]
      have := hbig ((colour_eq_of_mem_union hX he hxu).symm.trans hxc)
      omega
    · rw [card_contractEdge_vertexOf_of_notMem hX he hxu]
      exact h1 x hx hxc
  · by_cases heu : e ∈ X.vertexOf d ∪ X.vertexOf (X.inv d)
    · have hcd : X.colour d = .white := (colour_eq_of_mem_union hX he heu).symm.trans hec
      obtain ⟨z, hz⟩ : (X.mergedVertex d).Nonempty := card_pos.1 (by have := hbig hcd; omega)
      obtain ⟨hzu, hzd, hzi⟩ := mem_mergedVertex.1 hz
      have hzu' : z ∈ X.vertexOf d ∪ X.vertexOf (X.inv d) := mem_union.2 hzu
      refine ⟨⟨z, mem_compl_pair_iff.2 ⟨hzd, hzi⟩⟩, ?_, ?_⟩
      · rw [isBoundaryVertex_vertexOf_contractEdge_iff he]
        exact fun hb => he.notMem_of_isBoundaryVertex hb hzu'
      · exact (colour_eq_of_mem_union hX he hzu').trans hcd
    · refine ⟨⟨e, mem_compl_pair_of_notMem heu⟩, ?_, hec⟩
      rw [isBoundaryVertex_vertexOf_contractEdge_iff he]
      exact hei

end Contraction

end PlabicData

namespace PlabicGraph

open PlabicData

variable {b : ℕ}

private theorem card_lt_of_isReductionStep {ε : Fin 2} {Q Q' : PlabicGraph b}
    (h : IsReductionStep ε Q Q') : Fintype.card Q'.Dart < Fintype.card Q.Dart := by
  rcases h with ⟨d, hd, -, ⟨θ⟩⟩ | ⟨d, he, ⟨θ⟩⟩ <;>
  · rw [Fintype.card_congr θ.toEquiv]
    exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
      (b := d) (by simp)

private theorem treeInvariant_of_isReductionStep {c : Shade} {Q Q' : PlabicGraph b}
    (h : IsReductionStep 0 Q Q') (hQ : TreeInvariant c Q.data) : TreeInvariant c Q'.data := by
  rcases h with ⟨d, hd, -, ⟨θ⟩⟩ | ⟨d, he, ⟨θ⟩⟩
  · exact θ.symm.treeInvariant ⟨leavesBlack_bivalentRemoval Q.isPlabicGraph hd hQ.1,
      fun hc => whiteFat_bivalentRemoval Q.isPlabicGraph hd (hQ.2 hc)⟩
  · exact θ.symm.treeInvariant ⟨leavesBlack_contractEdge Q.isPlabicGraph he hQ.1,
      fun hc => whiteFat_contractEdge Q.isPlabicGraph he (hQ.2 hc)⟩

/-- A maximal sequence of `0`-reduction steps preserving the invariant. -/
private theorem exists_isIrreducible_treeInvariant (c : Shade) (n : ℕ) :
    ∀ Q : PlabicGraph b, Fintype.card Q.Dart = n → TreeInvariant c Q.data →
      ∃ R, Relation.ReflTransGen (IsReductionStep 0) Q R ∧ IsIrreducible 0 R ∧
        TreeInvariant c R.data := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q hn hQ
    by_cases hirr : IsIrreducible 0 Q
    · exact ⟨Q, .refl, hirr, hQ⟩
    · simp only [IsIrreducible, not_forall, not_not] at hirr
      obtain ⟨Q', hs⟩ := hirr
      obtain ⟨R, hR, hRi, hRinv⟩ :=
        ih _ (hn ▸ card_lt_of_isReductionStep hs) Q' rfl (treeInvariant_of_isReductionStep hs hQ)
      exact ⟨R, .head hs hR, hRi, hRinv⟩

/-- The lollipop graph is `0`-irreducible. -/
private theorem isIrreducible_zero_lollipopPlabicGraph (c : Shade) :
    IsIrreducible 0 (lollipopPlabicGraph c) := by
  intro Q' hs
  have k₁ : ∀ x : LollipopDart, ((lollipopGraph c).vertexOf x).card ≠ 2 := by
    cases c <;> decide
  have k₂ : ∀ x : LollipopDart, (lollipopGraph c).vertexOf x ∈ (lollipopGraph c).internalVertices →
      (lollipopGraph c).vertexOf ((lollipopGraph c).inv x) ∈ (lollipopGraph c).internalVertices →
      False := by
    cases c <;> decide
  rcases hs with ⟨x, hx, -, -⟩ | ⟨x, hx, -⟩
  · exact k₁ x hx.card_vertexOf
  · exact k₂ x hx.mem_internalVertices hx.inv_mem_internalVertices

/-- **A colour obstruction for collapsing plabic trees**. Let `Q` be a plabic graph with one
boundary vertex and exactly one face in which every internal leaf is black, and let `c` be a
colour. If `c` is black, assume moreover that every white internal vertex of `Q` has at least three
darts and that `Q` has a white internal vertex. Then `Q` is not `{M2, M3}`-equivalent to the
lollipop graph `L_c`. -/
@[cluster_algebras "lem_plabic_tree_colour_obstruction"]
theorem not_moveEquivalent_lollipopPlabicGraph {Q : PlabicGraph 1} (hf : Q.data.faces.card = 1)
    {c : Shade} (hleaf : ∀ v, Q.data.IsInternalLeaf v → ∀ d ∈ v, Q.data.colour d = .black)
    (hwhite : c = .black →
      (∀ v ∈ Q.data.internalVertices, (∀ d ∈ v, Q.data.colour d = .white) → 3 ≤ v.card) ∧
        ∃ v ∈ Q.data.internalVertices, ∀ d ∈ v, Q.data.colour d = .white) :
    ¬MoveEquivalent {.m2, .m3} Q (lollipopPlabicGraph c) := by
  intro hQL
  have hQ : TreeInvariant c Q.data := by
    refine ⟨leavesBlack_iff.2 hleaf, fun hc => ?_⟩
    obtain ⟨h1, v, hv, hvc⟩ := hwhite hc
    obtain ⟨hvV, hvb⟩ := Q.data.mem_internalVertices.1 hv
    obtain ⟨e, rfl⟩ := Q.data.mem_vertices.1 hvV
    refine ⟨fun d hd hdc => h1 _ (Q.data.vertexOf_mem_internalVertices.2 hd) fun x hx => ?_,
      e, hvb, hvc e (Q.data.self_mem_vertexOf e)⟩
    rw [colour_eq_of_mem_vertexOf Q.isPlabicGraph hd hx, hdc]
  obtain ⟨R, hR, hRirr, hRinv⟩ := exists_isIrreducible_treeInvariant c _ Q rfl hQ
  have hQR : MoveEquivalent {.m2, .m3} Q R := by
    clear hRirr hRinv
    induction hR with
    | refl => exact MoveEquivalent.refl _ _
    | tail _ hs ih => exact ih.trans (MoveEquivalent.of_moveStep hs.moveStep)
  have hRf : R.data.faces.card = 1 := hQR.card_eq.2.1.symm.trans hf
  obtain ⟨θ⟩ := isomorphic_of_moveEquivalent_of_isIrreducible
    R.isPlabicGraph.card_boundaryVertices hRf
    (lollipopPlabicGraph c).isPlabicGraph.card_boundaryVertices (card_faces_lollipopGraph c)
    (hQR.symm.trans hQL) hRirr (isIrreducible_zero_lollipopPlabicGraph c)
  have hL := θ.treeInvariant hRinv
  cases c with
  | white =>
    obtain ⟨⟨hleafL, -⟩, -⟩ := isLollipopOfColour_lollipopGraph .white
    have := leavesBlack_iff.1 hL.1 _ hleafL .gBar (mem_singleton_self _)
    exact absurd this (by decide)
  | black =>
    obtain ⟨-, d, -, hd⟩ := hL.2 rfl
    change Shade.black = Shade.white at hd
    exact absurd hd (by decide)

end PlabicGraph

end ClusterAlgebras
