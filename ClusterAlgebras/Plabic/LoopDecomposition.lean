/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.NearlyLeafless
public import ClusterAlgebras.Plabic.EarStrands
public import ClusterAlgebras.Plabic.TrivalentMoves

/-!
# Normal plabic graphs, collapsible trees and loops

A normal plabic graph has no collapsible tree: the plabic graph `P_T` of a rooted tree `T` of a
normal graph has only black internal leaves, its white vertices have three darts, and it has a
white vertex whenever the colour of the collapse is black, so the colour obstruction for
collapsing plabic trees applies.

## Main results

* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.not_isCollapsible`: a normal plabic graph has
  no collapsible tree.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

private theorem shade_eq_white_of_ne {s : Shade} (h : s ≠ .black) : s = .white := by
  cases s <;> simp_all

namespace RootedTree

variable (T : G.RootedTree)

/-- A dart of `P_T` whose vertex is internal and has one dart is fixed by the rotation. -/
private theorem rot_eq_of_card_eq_one {x : T.Dart} (h : (T.plabicData.vertexOf x).card = 1) :
    T.plabicData.rot x = x :=
  card_le_one.1 h.le _ (T.plabicData.rot_mem_vertexOf x) _ (T.plabicData.self_mem_vertexOf x)

/-- A dart `ⓘd` of `P_T` with `v(d) ∈ W`: the vertex of `ⓘd` in `P_T` has at least as many darts
as `v(d)` in `G`. -/
private theorem card_vertexOf_le (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts)
    (hW : G.vertexOf d ∈ T.nonRoot) :
    (G.vertexOf d).card ≤ (T.plabicData.vertexOf ⟨.inl d, hd⟩).card := by
  have hmem : ∀ y ∈ G.vertexOf d, y ∈ T.darts := fun y hy =>
    T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_eq_of_mem hy])
  refine card_le_card_of_injOn (fun y => if hy : y ∈ T.darts then ⟨.inl y, hy⟩ else
    ⟨.inl d, hd⟩) (fun y hy => ?_) (fun y₁ hy₁ y₂ hy₂ h => ?_)
  · obtain ⟨n, rfl⟩ := ((RotationSystem.mem_vertexOf _).1 hy).exists_nat_pow_eq
    dsimp only
    rw [dif_pos (hmem _ hy)]
    refine (RotationSystem.mem_vertexOf _).2 ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext (T.coe_rot_pow_inl hG hd hW n)
  · simpa only [dif_pos (hmem _ hy₁), dif_pos (hmem _ hy₂), Subtype.mk.injEq, Sum.inl.injEq]
      using h

/-- A dart `ⓘd` of `P_T` with `v(d) ∈ W` lies at an internal vertex of `P_T`. -/
private theorem not_isBoundaryVertex_inl (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts)
    (hW : G.vertexOf d ∈ T.nonRoot) :
    ¬T.plabicData.IsBoundaryVertex (T.plabicData.vertexOf ⟨.inl d, hd⟩) := by
  rw [T.isBoundaryVertex_vertexOf_iff hG, T.vertexOf_dartE hG]
  simp only [mem_insert, mem_singleton]
  rintro (h | h | h)
  · simp [dartE] at h
  · have hroot : G.vertexOf d = T.root := by
      unfold legDart at h
      split_ifs at h with hb
      · simp only [Subtype.mk.injEq, Sum.inl.injEq] at h
        rw [h, T.root_eq_vertexOf_intervalStart]
      · simp at h
    exact T.root_notMem_nonRoot (hroot ▸ hW)
  · simp [dartEBar] at h

/-- If `d ∈ D_T` lies at a vertex of `W` and `d` is white in `G`, then the vertex of `ⓘd` is a
white internal vertex of `P_T`. -/
private theorem exists_white (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts)
    (hW : G.vertexOf d ∈ T.nonRoot) (hc : G.colour d = .white) :
    ∃ v ∈ T.plabicData.internalVertices, ∀ x ∈ v, T.plabicData.colour x = .white := by
  refine ⟨_, T.plabicData.vertexOf_mem_internalVertices.2 (T.not_isBoundaryVertex_inl hG hd hW),
    fun x hx => ?_⟩
  obtain ⟨d', h1, h2⟩ := T.exists_of_mem_vertexOf_inl hG hd hW hx
  have hint : ¬G.IsBoundaryVertex (G.vertexOf d) :=
    (G.mem_internalVertices.1 (T.nonRoot_subset hW)).2
  change T.colourAux x.1 = _
  rw [h1]
  change G.colour d' = _
  rw [hG.colour_eq_of_mem_vertexOf hint (h2 ▸ G.self_mem_vertexOf d'), hc]

/-- In `P_T` for a normal plabic graph, every internal leaf is black. -/
private theorem colour_eq_black_of_isInternalLeaf (hG : G.IsNormalPlabicGraph) :
    ∀ v, T.plabicData.IsInternalLeaf v → ∀ x ∈ v, T.plabicData.colour x = .black := by
  have hP : G.IsPlabicGraph := hG.toIsPlabicGraph
  rintro v ⟨hv, hv1⟩ x hx
  obtain ⟨hvV, hvb⟩ := T.plabicData.mem_internalVertices.1 hv
  have hvx : T.plabicData.vertexOf x = v := by
    obtain ⟨y, rfl⟩ := T.plabicData.mem_vertices.1 hvV
    exact T.plabicData.vertexOf_eq_of_mem hx
  have hfix := T.rot_eq_of_card_eq_one (x := x) (hvx ▸ hv1)
  have hxb' : ¬T.plabicData.IsBoundaryVertex (T.plabicData.vertexOf x) := hvx ▸ hvb
  rw [T.isBoundaryVertex_vertexOf_iff hP, T.vertexOf_dartE hP] at hxb'
  simp only [mem_insert, mem_singleton, not_or] at hxb'
  have hrot := congrArg Subtype.val hfix
  rw [T.coe_rot_plabicData hP] at hrot
  rcases x with ⟨d | (_ | _ | _ | _), hd⟩
  · rcases T.vertexOf_mem_or_eq_root hP hd with hW | hR
    · have h1 : G.rot d ∈ T.darts := T.rot_mem_darts_of_vertexOf_mem hW
      simp only [RootedTree.rotAux, h1, if_true, Sum.inl.injEq] at hrot
      have hint : ¬G.IsBoundaryVertex (G.vertexOf d) :=
        (G.mem_internalVertices.1 (T.nonRoot_subset hW)).2
      change G.colour d = _
      by_contra hcol
      have hw := shade_eq_white_of_ne hcol
      have h3 := hG.card_vertexOf_of_white d hint hw
      have h3' := T.card_vertexOf_le hP hd hW
      rw [h3, hvx, hv1] at h3'
      omega
    · by_cases h1 : G.rot d ∈ T.darts
      · simp only [RootedTree.rotAux, h1, if_true, Sum.inl.injEq] at hrot
        exfalso
        have hcard : T.root.card ≤ 1 := by
          rw [← hR]
          refine card_le_one.2 fun y hy z hz => ?_
          have key : ∀ y ∈ G.vertexOf d, y = d := fun y hy => by
            obtain ⟨n, rfl⟩ := ((RotationSystem.mem_vertexOf _).1 hy).exists_nat_pow_eq
            exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hrot n
          rw [key y hy, key z hz]
        have := T.intervalLength_lt_card
        have := T.one_le_intervalLength
        omega
      · simp only [RootedTree.rotAux, h1, if_false] at hrot
        split_ifs at hrot
  · exact absurd rfl hxb'.1
  · exact absurd rfl hxb'.2.2
  · exfalso
    apply hxb'.2.1
    apply Subtype.ext
    simp [RootedTree.legDart, show ¬G.IsBoundaryVertex T.root from hd]
  · simp [RootedTree.rotAux] at hrot

/-- For a collapsible tree of black colour of a normal plabic graph, white internal vertices of
`P_T` have at least three darts. -/
private theorem three_le_card_of_forall_white (hG : G.IsNormalPlabicGraph) {c : Shade}
    (hT : T.IsCollapsibleOfColour c) (hc : c = .black) :
    ∀ v ∈ T.plabicData.internalVertices, (∀ x ∈ v, T.plabicData.colour x = .white) →
      3 ≤ v.card := by
  have hP : G.IsPlabicGraph := hG.toIsPlabicGraph
  intro v hv hvw
  obtain ⟨hvV, hxb'⟩ := T.plabicData.mem_internalVertices.1 hv
  obtain ⟨x, rfl⟩ := T.plabicData.mem_vertices.1 hvV
  have hxw := hvw x (T.plabicData.self_mem_vertexOf x)
  rw [T.isBoundaryVertex_vertexOf_iff hP, T.vertexOf_dartE hP] at hxb'
  simp only [mem_insert, mem_singleton, not_or] at hxb'
  rcases x with ⟨d | (_ | _ | _ | _), hd⟩
  · change G.colour d = .white at hxw
    rcases T.vertexOf_mem_or_eq_root hP hd with hW | hR
    · have hint : ¬G.IsBoundaryVertex (G.vertexOf d) :=
        (G.mem_internalVertices.1 (T.nonRoot_subset hW)).2
      have h3 := hG.card_vertexOf_of_white d hint hxw
      have h3' := T.card_vertexOf_le hP hd hW
      omega
    · by_cases hb : G.IsBoundaryVertex T.root
      · exfalso
        apply hxb'.2.1
        apply Subtype.ext
        simp [RootedTree.legDart, hb, T.eq_intervalStart_of_isBoundaryVertex hP hb hd hR]
      · rcases hT.root_cases with ⟨-, hcol⟩ | ⟨hb', -⟩
        · rw [hcol d (T.mem_root_iff.2 hR), hc] at hxw
          exact absurd hxw (by decide)
        · exact absurd hb' hb
  · exact absurd rfl hxb'.1
  · exact absurd rfl hxb'.2.2
  · exfalso
    apply hxb'.2.1
    apply Subtype.ext
    simp [RootedTree.legDart, show ¬G.IsBoundaryVertex T.root from hd]
  · change G.colour T.intervalStart = .white at hxw
    rcases hT.root_cases with ⟨-, hcol⟩ | ⟨hb', -⟩
    · rw [hcol _ T.intervalStart_mem_root, hc] at hxw
      exact absurd hxw (by decide)
    · exact absurd hb' hd

/-- If the root of `T` is a boundary vertex and `|W| ≥ 2`, the vertex of `ā₁` has a second dart. -/
private theorem rot_inv_intervalStart_ne (hP : G.IsPlabicGraph) (hb : G.IsBoundaryVertex T.root)
    (h2 : 2 ≤ T.nonRoot.card) : G.rot (G.inv T.intervalStart) ≠ G.inv T.intervalStart := by
  set a := T.intervalStart with ha_def
  intro hfix
  have hx1 : ∀ e, G.vertexOf e = G.vertexOf (G.inv a) → e = G.inv a := fun e he => by
    have : e ∈ G.vertexOf (G.inv a) := he ▸ G.self_mem_vertexOf e
    obtain ⟨n, rfl⟩ := ((RotationSystem.mem_vertexOf _).1 this).exists_nat_pow_eq
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix n
  have hreach : ∀ u, Relation.ReflTransGen (G.TreeAdj T.nonRoot) T.root u →
      u = T.root ∨ u = G.vertexOf (G.inv a) := by
    intro u hu
    induction hu with
    | refl => exact Or.inl rfl
    | @tail u u' _ hstep ih =>
      obtain ⟨e, heD, heu, heu'⟩ := hstep
      rcases ih with rfl | rfl
      · rw [← heu', T.eq_intervalStart_of_isBoundaryVertex hP hb heD heu]
        exact Or.inr rfl
      · rw [← heu', hx1 e heu, hP.inv_involutive, ha_def,
          ← T.root_eq_vertexOf_intervalStart]
        exact Or.inl rfl
  have hsub : T.nonRoot ⊆ {G.vertexOf (G.inv a)} := by
    intro u hu
    rcases hreach u (T.reflTransGen_treeAdj u (mem_insert_of_mem hu)) with rfl | rfl
    · exact absurd hu T.root_notMem_nonRoot
    · exact mem_singleton_self _
  have := card_le_card hsub
  rw [card_singleton] at this
  omega

/-- For a collapsible tree of black colour of a normal plabic graph, `P_T` has a white internal
vertex. -/
private theorem exists_white_of_isCollapsibleOfColour (hG : G.IsNormalPlabicGraph) {c : Shade}
    (hT : T.IsCollapsibleOfColour c) (hc : c = .black) :
    ∃ v ∈ T.plabicData.internalVertices, ∀ x ∈ v, T.plabicData.colour x = .white := by
  have hP : G.IsPlabicGraph := hG.toIsPlabicGraph
  have ha := T.intervalStart_mem_darts
  have haW : G.vertexOf (G.inv T.intervalStart) ∈ T.nonRoot := by
    rcases (G.mem_treeDarts.1 ha).2 with h | h
    · rw [← T.root_eq_vertexOf_intervalStart] at h
      exact absurd h T.root_notMem_nonRoot
    · exact h
  rcases hT.root_cases with ⟨hint, hcol⟩ | ⟨hb, h2⟩
  · have hacol : G.colour T.intervalStart = .black := hc ▸ hcol _ T.intervalStart_mem_root
    have hne := hG.colour_inv_ne T.intervalStart
      (by rwa [← T.root_eq_vertexOf_intervalStart])
      (G.mem_internalVertices.1 (T.nonRoot_subset haW)).2
    exact T.exists_white hP (T.inv_mem_darts hP ha) haW
      (shade_eq_white_of_ne (hacol ▸ hne))
  · -- the root is `β(i)` and `a₁ = g_i`
    obtain ⟨i, hi⟩ := hP.exists_bvertex_eq _
      (G.mem_boundaryVertices.2 ⟨T.root_mem_vertices, hb⟩)
    have haleg : T.intervalStart = G.leg i := by
      have : T.intervalStart ∈ (G.bvertex i).filter (· ∉ G.bdry) :=
        mem_filter.2 ⟨hi ▸ T.intervalStart_mem_root, (G.mem_treeDarts.1 ha).1⟩
      rwa [hP.filter_bvertex_notMem_bdry, mem_singleton] at this
    have hxcol : G.colour (G.inv T.intervalStart) = .black := haleg ▸ hG.colour_inv_leg i
    have hxint : ¬G.IsBoundaryVertex (G.vertexOf (G.inv T.intervalStart)) :=
      (G.mem_internalVertices.1 (T.nonRoot_subset haW)).2
    set a := T.intervalStart with ha_def
    have hrot : G.rot (G.inv a) ≠ G.inv a := T.rot_inv_intervalStart_ne hP hb h2
    set d' := G.rot (G.inv a) with hd'
    have hd'W : G.vertexOf d' ∈ T.nonRoot := by rwa [hd', G.vertexOf_rot]
    have hd'D := T.mem_darts_of_vertexOf_mem hd'W
    have hid'D := T.inv_mem_darts hP hd'D
    have hid'W : G.vertexOf (G.inv d') ∈ T.nonRoot := by
      rcases T.vertexOf_mem_or_eq_root hP hid'D with h | h
      · exact h
      · exfalso
        have := T.eq_intervalStart_of_isBoundaryVertex hP hb hid'D h
        apply hrot
        rw [← ha_def] at this
        rw [← this, hP.inv_involutive]
    have hd'int : ¬G.IsBoundaryVertex (G.vertexOf d') :=
      (G.mem_internalVertices.1 (T.nonRoot_subset hd'W)).2
    have hd'col : G.colour d' = .black := by
      rw [hd', hP.colour_rot _ hxint, hxcol]
    have hne := hG.colour_inv_ne d' hd'int
      (G.mem_internalVertices.1 (T.nonRoot_subset hid'W)).2
    exact T.exists_white hP hid'D hid'W (shade_eq_white_of_ne (hd'col ▸ hne))

end RootedTree

/-- A normal plabic graph has no collapsible tree. -/
@[cluster_algebras "lem_normal_no_collapse"]
theorem IsNormalPlabicGraph.not_isCollapsible (hG : G.IsNormalPlabicGraph) (T : G.RootedTree) :
    ¬T.IsCollapsible := by
  rintro ⟨c, hT⟩
  exact PlabicGraph.not_moveEquivalent_lollipopPlabicGraph
    (Q := ⟨T.Dart, T.plabicData, hT.isPlabicGraph⟩) (T.card_faces_plabicData hG.toIsPlabicGraph)
    (T.colour_eq_black_of_isInternalLeaf hG)
    (fun hc => ⟨T.three_le_card_of_forall_white hG hT hc,
      T.exists_white_of_isCollapsibleOfColour hG hT hc⟩)
    hT.moveEquivalent

end PlabicData

namespace PlabicData

/-! ### Making a graph normal, or finding a black loop -/

section Normalize

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-- White internal vertices have at least `k` darts. -/
private def WhiteGE (G : PlabicData H b) (k : ℕ) : Prop :=
  ∀ x, ¬G.IsBoundaryVertex (G.vertexOf x) → G.colour x = .white → k ≤ (G.vertexOf x).card

/-- White internal vertices have at most three darts. -/
private def WhiteLE3 (G : PlabicData H b) : Prop :=
  ∀ x, ¬G.IsBoundaryVertex (G.vertexOf x) → G.colour x = .white → (G.vertexOf x).card ≤ 3

/-- The edge `{d, d̄}` has a black end: one of `v(d)`, `v(d̄)` is a black internal vertex. -/
private def BlackEnd (G : PlabicData H b) (d : H) : Prop :=
  (¬G.IsBoundaryVertex (G.vertexOf d) ∧ G.colour d = .black) ∨
    (¬G.IsBoundaryVertex (G.vertexOf (G.inv d)) ∧ G.colour (G.inv d) = .black)

private instance (G : PlabicData H b) : DecidablePred G.BlackEnd := fun d => by
  unfold BlackEnd
  infer_instance

private theorem eq_or_eq_rot_of_card_two {G : PlabicData H b} {x y : H}
    (h : (G.vertexOf x).card = 2) (hy : y ∈ G.vertexOf x) : y = x ∨ y = G.rot x := by
  have hne : G.rot x ≠ x := by
    intro hfix
    have hsub : G.vertexOf x ⊆ {x} := fun z hz => by
      obtain ⟨n, rfl⟩ := ((RotationSystem.mem_vertexOf _).1 hz).exists_nat_pow_eq
      rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix n]
      exact mem_singleton_self _
    have := card_le_card hsub
    rw [h, card_singleton] at this
    omega
  have hsub : ({x, G.rot x} : Finset H) ⊆ G.vertexOf x := by
    intro z hz
    rcases mem_insert.1 hz with rfl | hz
    · exact G.self_mem_vertexOf _
    · rw [mem_singleton.1 hz]
      exact G.rot_mem_vertexOf _
  have heq := eq_of_subset_of_card_le hsub (by rw [h, card_pair hne.symm])
  rw [← heq] at hy
  simpa using hy

/-- An internal vertex with two darts can be removed: `d̄₁ ≠ d₂`, since otherwise the vertex
would be closed under the rotation and the involution. -/
private theorem isBivalentRemovable_of_card_two {G : PlabicData H b} (hG : G.IsPlabicGraph)
    {x : H} (hx : ¬G.IsBoundaryVertex (G.vertexOf x)) (h2 : (G.vertexOf x).card = 2) :
    G.IsBivalentRemovable x := by
  refine ⟨hx, h2, fun heq => ?_⟩
  have hS : ∀ y, G.Reach x y → y ∈ G.vertexOf x := by
    intro y hy
    induction hy with
    | refl => exact G.self_mem_vertexOf x
    | rot _ ih =>
      rw [← G.vertexOf_eq_of_mem ih]
      exact G.rot_mem_vertexOf _
    | inv _ ih =>
      rcases eq_or_eq_rot_of_card_two h2 ih with h | h
      · rw [h, heq]
        exact G.rot_mem_vertexOf _
      · rw [h, ← heq, hG.inv_involutive]
        exact G.self_mem_vertexOf _
  obtain ⟨e, he, -, -⟩ := hG.exists_exterior ⟨0, hG.one_le⟩
  exact hx ⟨e, hS e (hG.toIsConnected.reach x e), G.exterior_subset_bdry he⟩

/-! #### Transfer along a removal -/

private theorem whiteGE_bivalentRemoval {G : PlabicData H b} (hG : G.IsPlabicGraph) {d : H}
    (hd : G.IsBivalentRemovable d) {k : ℕ} (hw : WhiteGE G k) :
    WhiteGE (G.bivalentRemoval hG hd) k := by
  intro y hy hyc
  rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd] at hy
  rw [← card_map (Function.Embedding.subtype _), map_bivalentRemoval_vertexOf hG hd]
  exact hw y hy hyc

/-! #### Transfer along a contraction -/

section Contraction

variable {G : PlabicData H b} (hG : G.IsPlabicGraph) {d : H} (he : G.IsContractibleEdge d)
  (hblack : G.colour d = .black)

include hG he hblack

private theorem whiteGE_contractEdge {k : ℕ} (hw : WhiteGE G k) :
    WhiteGE (G.contractEdge d (he.leg_mem hG)) k := by
  intro y hy hyc
  rw [isBoundaryVertex_vertexOf_contractEdge_iff he] at hy
  by_cases hyU : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · have : G.colour y = .black := (colour_eq_of_mem_union hG he hyU).trans hblack
    exact absurd (this.symm.trans hyc) (by decide)
  · rw [← card_map (Function.Embedding.subtype _),
      map_vertexOf_contractEdge_of_notMem he.not_sameCycle hyU]
    exact hw y hy hyc

private theorem whiteLE3_contractEdge (hw : WhiteLE3 G) :
    WhiteLE3 (G.contractEdge d (he.leg_mem hG)) := by
  intro y hy hyc
  rw [isBoundaryVertex_vertexOf_contractEdge_iff he] at hy
  by_cases hyU : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · have : G.colour y = .black := (colour_eq_of_mem_union hG he hyU).trans hblack
    exact absurd (this.symm.trans hyc) (by decide)
  · rw [← card_map (Function.Embedding.subtype _),
      map_vertexOf_contractEdge_of_notMem he.not_sameCycle hyU]
    exact hw y hy hyc

omit hblack in
private theorem blackEnd_contractEdge (h : ∀ x, x ∉ G.bdry → BlackEnd G x) :
    ∀ y, y ∉ (G.contractEdge d (he.leg_mem hG)).bdry →
      BlackEnd (G.contractEdge d (he.leg_mem hG)) y := by
  intro y hy
  rw [mem_contractEdge_bdry] at hy
  have hinv : ((G.contractEdge d (he.leg_mem hG)).inv y : H) = G.inv y :=
    coe_contractEdge_inv hG.inv_involutive y
  unfold BlackEnd
  rw [isBoundaryVertex_vertexOf_contractEdge_iff he, isBoundaryVertex_vertexOf_contractEdge_iff he,
    contractEdge_colour, contractEdge_colour, hinv]
  exact h y hy

end Contraction

/-! #### Transfer along an insertion -/

section Insertion

variable {G : PlabicData H b} (hG : G.IsPlabicGraph) {d : H} (hd : d ∉ G.bdry)

include hG

private theorem blackEnd_bivalentInsertion_inl_iff {y : H} (h₁ : y ≠ d) (h₂ : y ≠ G.inv d) :
    BlackEnd (G.bivalentInsertion d .black) (Sum.inl y) ↔ BlackEnd G y := by
  unfold BlackEnd
  rw [bivalentInsertion_inv_inl_of_ne .black hG.inv_involutive h₁ h₂,
    isBoundaryVertex_bivalentInsertion_vertexOf_inl,
    isBoundaryVertex_bivalentInsertion_vertexOf_inl]
  exact Iff.rfl

private theorem blackEnd_bivalentInsertion_of_not_inl (e : H ⊕ Fin 2)
    (he : ∀ y, e = Sum.inl y → y ≠ d ∧ y ≠ G.inv d → False) :
    BlackEnd (G.bivalentInsertion d .black) e := by
  rcases e with y | j
  · by_cases h₁ : y = d
    · subst h₁
      refine Or.inr ⟨?_, ?_⟩
      · rw [bivalentInsertion_inv_inl_self .black (hG.inv_ne y)]
        exact not_isBoundaryVertex_bivalentInsertion_vertexOf_inr y .black 0
      · rw [bivalentInsertion_inv_inl_self .black (hG.inv_ne y)]
        exact bivalentInsertion_colour_inr _ _ _
    · by_cases h₂ : y = G.inv d
      · subst h₂
        refine Or.inr ⟨?_, ?_⟩
        · rw [bivalentInsertion_inv_inl_inv .black hG.inv_involutive]
          exact not_isBoundaryVertex_bivalentInsertion_vertexOf_inr d .black 1
        · rw [bivalentInsertion_inv_inl_inv .black hG.inv_involutive]
          exact bivalentInsertion_colour_inr _ _ _
      · exact (he y rfl ⟨h₁, h₂⟩).elim
  · exact Or.inl ⟨not_isBoundaryVertex_bivalentInsertion_vertexOf_inr d .black j, rfl⟩

omit hG in
private theorem whiteGE_bivalentInsertion {k : ℕ} (hw : WhiteGE G k) :
    WhiteGE (G.bivalentInsertion d .black) k := by
  rintro (y | j) hy hyc
  · rw [isBoundaryVertex_bivalentInsertion_vertexOf_inl] at hy
    rw [bivalentInsertion_vertexOf_inl, card_map]
    exact hw y hy hyc
  · simp at hyc

omit hG in
private theorem whiteLE3_bivalentInsertion (hw : WhiteLE3 G) :
    WhiteLE3 (G.bivalentInsertion d .black) := by
  rintro (y | j) hy hyc
  · rw [isBoundaryVertex_bivalentInsertion_vertexOf_inl] at hy
    rw [bivalentInsertion_vertexOf_inl, card_map]
    exact hw y hy hyc
  · simp at hyc

private theorem isNearlyLeafless_bivalentInsertion (hnl : G.IsNearlyLeafless)
    (hw : WhiteGE G 2) (hbad : ¬BlackEnd G d) :
    (G.bivalentInsertion d .black).IsNearlyLeafless := by
  intro v hv
  obtain ⟨e, rfl⟩ := (G.bivalentInsertion d .black).mem_vertices.1
    ((G.bivalentInsertion d .black).mem_internalVertices.1 hv.1).1
  rcases e with y | j
  · have hint : ¬G.IsBoundaryVertex (G.vertexOf y) := by
      have := ((G.bivalentInsertion d .black).mem_internalVertices.1 hv.1).2
      rwa [isBoundaryVertex_bivalentInsertion_vertexOf_inl] at this
    have hcard : (G.vertexOf y).card = 1 := by
      have := hv.2
      rwa [bivalentInsertion_vertexOf_inl, card_map] at this
    obtain ⟨i, -, z, hz, hzi⟩ := hnl _ ⟨G.vertexOf_mem_internalVertices.2 hint, hcard⟩
    have hvz : G.vertexOf z = G.vertexOf y := G.vertexOf_eq_of_mem hz
    have hzint : ¬G.IsBoundaryVertex (G.vertexOf z) := hvz ▸ hint
    have hzb : G.colour z = .black := by
      by_contra hc
      have := hw z hzint (shade_eq_white_of_ne hc)
      rw [hvz, hcard] at this
      omega
    have h₁ : z ≠ d := fun h => hbad (Or.inl ⟨h ▸ hzint, h ▸ hzb⟩)
    have h₂ : z ≠ G.inv d := fun h => hbad (Or.inr ⟨h ▸ hzint, h ▸ hzb⟩)
    refine ⟨i, hv, Sum.inl z, ?_, ?_⟩
    · rw [bivalentInsertion_vertexOf_inl]
      exact mem_map_of_mem _ hz
    · rw [bivalentInsertion_inv_inl_of_ne .black hG.inv_involutive h₁ h₂]
      change Sum.inl (G.inv z) ∈ (G.bivalentInsertion d .black).vertexOf (Sum.inl (G.leg i))
      rw [bivalentInsertion_vertexOf_inl]
      exact mem_map_of_mem _ hzi
  · have := hv.2
    rw [bivalentInsertion_vertexOf_inr, card_pair (by simp)] at this
    omega

private theorem card_bad_bivalentInsertion (hbad : d ∉ G.bdry ∧ ¬BlackEnd G d) :
    (univ.filter fun e => e ∉ (G.bivalentInsertion d .black).bdry ∧
        ¬BlackEnd (G.bivalentInsertion d .black) e).card <
      (univ.filter fun e => e ∉ G.bdry ∧ ¬BlackEnd G e).card := by
  have hmem : d ∈ univ.filter fun e => e ∉ G.bdry ∧ ¬BlackEnd G e := by simp [hbad]
  refine lt_of_le_of_lt (card_le_card_of_injOn (fun e => Sum.elim id (fun _ => d) e) ?_ ?_)
    (card_erase_lt_of_mem hmem)
  · intro e he
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at he
    obtain ⟨heB, heE⟩ := he
    by_contra hcon
    apply heE
    refine blackEnd_bivalentInsertion_of_not_inl hG e fun y hy hy' => hcon ?_
    subst hy
    simp only [coe_erase, coe_filter, mem_univ, true_and, Set.mem_sdiff, Set.mem_setOf_eq,
      Set.mem_singleton_iff, Sum.elim_inl, id]
    refine ⟨⟨fun h => heB ((inl_mem_bivalentInsertion_bdry d .black).2 h), fun h => heE
      ((blackEnd_bivalentInsertion_inl_iff hG hy'.1 hy'.2).2 h)⟩, hy'.1⟩
  · intro e₁ he₁ e₂ he₂ h
    have key : ∀ e ∈ ((univ.filter fun e => e ∉ (G.bivalentInsertion d .black).bdry ∧
        ¬BlackEnd (G.bivalentInsertion d .black) e : Finset (H ⊕ Fin 2)) : Set (H ⊕ Fin 2)),
        ∃ y, e = Sum.inl y := by
      intro e he
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at he
      by_contra hcon
      push Not at hcon
      exact he.2 (blackEnd_bivalentInsertion_of_not_inl hG e fun y hy _ => hcon y hy)
    obtain ⟨y₁, rfl⟩ := key e₁ he₁
    obtain ⟨y₂, rfl⟩ := key e₂ he₂
    simp only [Sum.elim_inl, id] at h
    rw [h]

end Insertion

/-! #### Orbits of a permutation -/

section Orbits

variable {X : Type*}

private theorem minimalPeriod_perm_pos'' [Finite X] (σ : Equiv.Perm X) (x : X) :
    0 < Function.minimalPeriod σ x := by
  refine Function.IsPeriodicPt.minimalPeriod_pos (n := orderOf σ)
    (isOfFinOrder_of_finite σ).orderOf_pos ?_
  rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one,
    Equiv.Perm.one_apply]

/-- A set mapped into itself by a permutation contains the cycles of its elements. -/
private theorem mem_of_sameCycle_of_mapsTo' [Finite X] {σ : Equiv.Perm X} {A : Set X}
    (hA : ∀ a ∈ A, σ a ∈ A) {x y : X} (hx : x ∈ A) (h : σ.SameCycle x y) : y ∈ A := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hA _ ih

variable [Fintype X] [DecidableEq X]

private theorem card_orbit_eq_minimalPeriod' (σ : Equiv.Perm X) (x : X) :
    ({y | σ.SameCycle x y} : Finset X).card = Function.minimalPeriod σ x := by
  have h : ({y | σ.SameCycle x y} : Finset X) =
      (range (Function.minimalPeriod σ x)).image fun i => (σ ^ i) x := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := hy.exists_nat_pow_eq
      refine ⟨n % Function.minimalPeriod σ x, Nat.mod_lt _ (minimalPeriod_perm_pos'' σ x), ?_⟩
      rw [← Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.iterate_eq_pow,
        Function.iterate_mod_minimalPeriod_eq]
    · rintro ⟨i, -, rfl⟩
      exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)
  rw [h, card_image_of_injOn, card_range]
  intro i hi j hj hij
  exact Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) (by simpa using hi)
    (by simpa using hj) (by simpa [Equiv.Perm.iterate_eq_pow] using hij)

/-- The elements `σ^i(x)`, `i < k`, of the orbit of `x` are distinct. -/
private theorem eq_of_pow_apply_eq_of_lt' (σ : Equiv.Perm X) (x : X) {i j : ℕ}
    (hi : i < ({y | σ.SameCycle x y} : Finset X).card)
    (hj : j < ({y | σ.SameCycle x y} : Finset X).card) (h : (σ ^ i) x = (σ ^ j) x) : i = j := by
  rw [card_orbit_eq_minimalPeriod'] at hi hj
  exact Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x) hi hj
    (by simpa [Equiv.Perm.iterate_eq_pow] using h)

/-- Every element of the orbit of `x` is `σ^i(x)` for some `i` less than the size of the orbit. -/
private theorem exists_pow_lt_card_of_sameCycle' (σ : Equiv.Perm X) {x y : X}
    (h : σ.SameCycle x y) : ∃ i < ({y | σ.SameCycle x y} : Finset X).card, (σ ^ i) x = y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  refine ⟨n % Function.minimalPeriod σ x, ?_, ?_⟩
  · rw [card_orbit_eq_minimalPeriod']
    exact Nat.mod_lt _ (minimalPeriod_perm_pos'' σ x)
  · rw [← Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.iterate_eq_pow,
      Function.iterate_mod_minimalPeriod_eq]

end Orbits

/-! #### Splitting a white vertex with at least four darts -/

section Split

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-- The darts of the vertex `z = v(s)` and the two new darts of a splitting at `z`. -/
private def splitSet' (K : PlabicData H b) (s : H) : Set (H ⊕ Fin 2) :=
  {e | Sum.elim (fun x => K.rot.SameCycle s x) (fun _ => True) e}

omit [Fintype H] [DecidableEq H] in
private theorem inl_mem_splitSet' {K : PlabicData H b} {s x : H} :
    Sum.inl x ∈ splitSet' K s ↔ K.rot.SameCycle s x :=
  Iff.rfl

omit [Fintype H] [DecidableEq H] in
private theorem inr_mem_splitSet' {K : PlabicData H b} {s : H} {i : Fin 2} :
    Sum.inr i ∈ splitSet' K s := trivial

omit [Fintype H] in
private theorem rot_vertexSplit_mem_splitSet' {K : PlabicData H b} {s : H} {p : ℕ}
    {e : H ⊕ Fin 2} (he : e ∈ splitSet' K s) : (K.vertexSplit s p).rot e ∈ splitSet' K s := by
  rcases e with x | i
  · rw [inl_mem_splitSet'] at he
    rw [rot_vertexSplit, splitRot_inl]
    split_ifs <;> simp [splitSet', he]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [rot_vertexSplit, splitRot_inr_zero]
      split_ifs <;> simp [splitSet', Equiv.Perm.SameCycle.refl]
    · rw [rot_vertexSplit, splitRot_inr_one]
      split_ifs <;> simp [splitSet', Equiv.Perm.sameCycle_pow_right, Equiv.Perm.SameCycle.refl]

/-- The excess `∑ (|v(x)| - 3)` over the darts `x` at white internal vertices. -/
private def whiteExcess (G : PlabicData H b) : ℕ :=
  ∑ x, if ¬G.IsBoundaryVertex (G.vertexOf x) ∧ G.colour x = .white then
    (G.vertexOf x).card - 3 else 0

/-- A vertex `v(s)` with at least four darts is not fixed by the rotation at `s`. -/
private theorem rot_ne_self_of_four_le {K : PlabicData H b} {s : H}
    (hk : 4 ≤ ({y | K.rot.SameCycle s y} : Finset H).card) : K.rot s ≠ s := by
  intro h
  have := eq_of_pow_apply_eq_of_lt' K.rot s (i := 1) (j := 0) (by omega) (by omega)
    (by rwa [pow_one, pow_zero, Equiv.Perm.one_apply])
  omega

omit [Fintype H] in
private theorem card_splitTriple {K : PlabicData H b} {s : H} (hs1 : K.rot s ≠ s) :
    ({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2)).card = 3 := by
  refine card_eq_three.2 ⟨_, _, _, by simp, by simp, ?_, rfl⟩
  simpa using hs1.symm

/-- After splitting `s` with size `2`, the new dart `n` lies at the vertex `{n, s, σ s}`. -/
private theorem vertexOf_inr_zero_vertexSplit_two {K : PlabicData H b} {s : H}
    (hs1 : K.rot s ≠ s) :
    (K.vertexSplit s 2).vertexOf (Sum.inr 0) = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} := by
  set S := K.vertexSplit s 2
  have hsr : ∀ e, S.rot e = splitRot K.rot s 2 e := fun _ => rfl
  have e0 : S.rot (Sum.inr 0) = Sum.inl s := by rw [hsr, splitRot_inr_zero, if_neg (by norm_num)]
  have e1 : S.rot (Sum.inl s) = Sum.inl (K.rot s) := by
    rw [hsr, splitRot_inl, if_neg, if_neg hs1]
    rintro ⟨-, h⟩
    rw [show 2 - 1 = 1 from rfl, pow_one] at h
    exact hs1 h.symm
  have e2 : S.rot (Sum.inl (K.rot s)) = Sum.inr 0 := by
    rw [hsr, splitRot_inl, if_pos]
    exact ⟨by norm_num, by rw [show 2 - 1 = 1 from rfl, pow_one]⟩
  ext e
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro h
    refine mem_of_sameCycle_of_mapsTo'
      (A := (({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2)) : Set (H ⊕ Fin 2)))
      ?_ (by simp) h
    intro a ha
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl <;> simp [e0, e1, e2]
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← e0]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
    · rw [show Sum.inl (K.rot s) = S.rot (S.rot (Sum.inr 0)) by rw [e0, e1]]
      exact Equiv.Perm.sameCycle_apply_right.2
        (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))

private theorem vertexOf_vertexSplit_two_of_mem_triple {K : PlabicData H b} {s : H}
    (hs1 : K.rot s ≠ s) {e : H ⊕ Fin 2}
    (he : e ∈ ({Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} : Finset (H ⊕ Fin 2))) :
    (K.vertexSplit s 2).vertexOf e = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} := by
  rw [← vertexOf_inr_zero_vertexSplit_two hs1] at he ⊢
  exact (K.vertexSplit s 2).vertexOf_eq_of_mem he

/-- After splitting `s` with size `2`, the other new dart `n̄` lies at the vertex of `σ ^ j s`
for `2 ≤ j < k`. -/
private theorem sameCycle_inr_one_vertexSplit_two {K : PlabicData H b} {s : H} {j : ℕ}
    (hj2 : 2 ≤ j) (hjk : j < ({y | K.rot.SameCycle s y} : Finset H).card) :
    (K.vertexSplit s 2).rot.SameCycle (Sum.inr 1) (Sum.inl ((K.rot ^ j) s)) := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hsr : ∀ e, S.rot e = splitRot K.rot s 2 e := fun _ => rfl
  induction j, hj2 using Nat.le_induction with
  | base =>
    have : S.rot (Sum.inr 1) = Sum.inl ((K.rot ^ 2) s) := by
      rw [hsr, splitRot_inr_one_of_le K.rot s 2 (by omega), if_neg (by omega)]
    rw [← this]
    exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
  | succ j hj ih =>
    have : S.rot (Sum.inl ((K.rot ^ j) s)) = Sum.inl ((K.rot ^ (j + 1)) s) := by
      rw [hsr, splitRot_inl_pow K.rot s 2 (by omega) (by omega), if_neg (by omega),
        if_neg (by omega)]
    rw [← this]
    exact Equiv.Perm.sameCycle_apply_right.2 (ih (by omega))

/-- Splitting a vertex with `k ≥ 4` darts with size `2` produces vertices with at most `k - 1`
darts. -/
private theorem card_vertexOf_vertexSplit_two_le' {K : PlabicData H b} {s : H}
    (hk : 4 ≤ ({y | K.rot.SameCycle s y} : Finset H).card) {e : H ⊕ Fin 2}
    (he : e ∈ splitSet' K s) :
    ((K.vertexSplit s 2).vertexOf e).card ≤ ({y | K.rot.SameCycle s y} : Finset H).card - 1 := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hs1 := rot_ne_self_of_four_le hk
  set A0 : Finset (H ⊕ Fin 2) := {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)}
  have hA0 : S.vertexOf (Sum.inr 0) = A0 := vertexOf_inr_zero_vertexSplit_two hs1
  have hA0card : A0.card = 3 := card_splitTriple hs1
  let Zf : Finset (H ⊕ Fin 2) := (K.vertexOf s).map Function.Embedding.inl ∪ {Sum.inr 0, Sum.inr 1}
  have hZf : ∀ e, e ∈ splitSet' K s → e ∈ Zf := by
    rintro (x | i) he
    · rw [inl_mem_splitSet'] at he
      exact mem_union_left _ (mem_map_of_mem _ ((RotationSystem.mem_vertexOf _).2 he))
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      all_goals simp [Zf]
  have hZfcard : Zf.card = k + 2 := by
    rw [card_union_of_disjoint, card_map, card_pair (by simp)]
    · rfl
    · rw [disjoint_left]
      intro e he he'
      simp only [mem_map, Function.Embedding.inl_apply] at he
      obtain ⟨x, -, rfl⟩ := he
      simp at he'
  have hsub : ∀ e ∈ splitSet' K s, S.vertexOf e ⊆ Zf := fun e he y hy =>
    hZf _ (mem_of_sameCycle_of_mapsTo' (fun _ h => rot_vertexSplit_mem_splitSet' h) he
      ((RotationSystem.mem_vertexOf _).1 hy))
  have hA0Zf : A0 ⊆ Zf := by
    rw [← hA0]
    exact hsub _ inr_mem_splitSet'
  by_cases h : S.vertexOf e = A0
  · rw [h, hA0card]
    omega
  · have hdisj : Disjoint (S.vertexOf e) A0 := by
      rw [disjoint_left]
      intro y hy hy'
      rw [← hA0] at hy'
      exact h ((S.vertexOf_eq_of_mem hy).symm.trans ((S.vertexOf_eq_of_mem hy').trans hA0))
    have h1 : S.vertexOf e ⊆ Zf \ A0 := fun y hy =>
      mem_sdiff.2 ⟨hsub e he hy, disjoint_left.1 hdisj hy⟩
    have h2 := card_le_card h1
    have h3 := card_sdiff_add_card_eq_card hA0Zf
    omega

/-- Splitting a vertex with `k ≥ 4` darts with size `2` produces vertices with at least `3`
darts. -/
private theorem three_le_card_vertexOf_vertexSplit_two' {K : PlabicData H b} {s : H}
    (hk : 4 ≤ ({y | K.rot.SameCycle s y} : Finset H).card) {e : H ⊕ Fin 2}
    (he : e ∈ splitSet' K s) : 3 ≤ ((K.vertexSplit s 2).vertexOf e).card := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hs1 := rot_ne_self_of_four_le hk
  have hcases : S.vertexOf e = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} ∨
      S.rot.SameCycle (Sum.inr 1) e := by
    rcases e with x | i
    · rw [inl_mem_splitSet'] at he
      obtain ⟨j, hj, rfl⟩ := exists_pow_lt_card_of_sameCycle' K.rot he
      rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | h2
      · exact Or.inl (vertexOf_vertexSplit_two_of_mem_triple hs1 (by simp))
      · exact Or.inl (vertexOf_vertexSplit_two_of_mem_triple hs1 (by simp))
      · exact Or.inr (sameCycle_inr_one_vertexSplit_two h2 hj)
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · exact Or.inl (vertexOf_inr_zero_vertexSplit_two hs1)
      · exact Or.inr (Equiv.Perm.SameCycle.refl _ _)
  rcases hcases with h | h
  · rw [h, card_splitTriple hs1]
  · rw [← S.vertexOf_eq_vertexOf_iff.2 h]
    have hsub3 : ({Sum.inr 1, Sum.inl ((K.rot ^ 2) s), Sum.inl ((K.rot ^ 3) s)} :
        Finset (H ⊕ Fin 2)) ⊆ S.vertexOf (Sum.inr 1) := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rw [RotationSystem.mem_vertexOf]
      rcases hy with rfl | rfl | rfl
      · exact Equiv.Perm.SameCycle.refl _ _
      · exact sameCycle_inr_one_vertexSplit_two le_rfl (by omega)
      · exact sameCycle_inr_one_vertexSplit_two (by omega) (by omega)
    have h3card : ({Sum.inr 1, Sum.inl ((K.rot ^ 2) s), Sum.inl ((K.rot ^ 3) s)} :
        Finset (H ⊕ Fin 2)).card = 3 := by
      refine card_eq_three.2 ⟨_, _, _, by simp, by simp, ?_, rfl⟩
      have hne : (K.rot ^ 2) s ≠ (K.rot ^ 3) s := fun h =>
        absurd (eq_of_pow_apply_eq_of_lt' K.rot s (by omega) (by omega) h) (by omega)
      simpa using hne
    rw [← h3card]
    exact card_le_card hsub3

/-- Splitting a white internal vertex `z = v(s)` with `k ≥ 4` darts from `s` with size `2`: the
darts of the two new vertices lie at white internal vertices with at least three darts. -/
private theorem vertexSplit_two_splitSet'_facts {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {s : H} (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (hk : 4 ≤ (K.vertexOf s).card)
    (hs : K.colour s = .white) :
    ∀ e ∈ splitSet' K s, ¬(K.vertexSplit s 2).IsBoundaryVertex ((K.vertexSplit s 2).vertexOf e) ∧
      3 ≤ ((K.vertexSplit s 2).vertexOf e).card ∧ (K.vertexSplit s 2).colour e = .white := by
  intro e he
  refine ⟨?_, three_le_card_vertexOf_vertexSplit_two' hk he, ?_⟩
  · rintro ⟨y, hy, hyB⟩
    have hyZ := mem_of_sameCycle_of_mapsTo' (fun _ h => rot_vertexSplit_mem_splitSet' h) he
      ((RotationSystem.mem_vertexOf _).1 hy)
    rw [bdry_vertexSplit, mem_map] at hyB
    obtain ⟨x, hx, rfl⟩ := hyB
    rw [Function.Embedding.inl_apply, inl_mem_splitSet'] at hyZ
    exact hz ⟨x, (RotationSystem.mem_vertexOf _).2 hyZ, hx⟩
  · rcases e with x | i
    · rw [inl_mem_splitSet'] at he
      change K.colour x = _
      rw [hK.colour_eq_of_mem_vertexOf hz ((RotationSystem.mem_vertexOf _).2 he), hs]
    · exact hs

/-- Splitting a white internal vertex `z = v(s)` with `k ≥ 4` darts does not increase the
white-excess weight of an old dart. -/
private theorem whiteWeight_vertexSplit_two_inl_le {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {s : H} (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (hk : 4 ≤ (K.vertexOf s).card)
    (hs : K.colour s = .white) (x : H) :
    (if ¬(K.vertexSplit s 2).IsBoundaryVertex ((K.vertexSplit s 2).vertexOf (Sum.inl x)) ∧
        (K.vertexSplit s 2).colour (Sum.inl x) = .white then
      ((K.vertexSplit s 2).vertexOf (Sum.inl x)).card - 3 else 0) ≤
      if ¬K.IsBoundaryVertex (K.vertexOf x) ∧ K.colour x = .white then (K.vertexOf x).card - 3
      else 0 := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  by_cases hx : K.rot.SameCycle s x
  · have hv : K.vertexOf x = K.vertexOf s := (K.vertexOf_eq_vertexOf_iff.2 hx).symm
    have : (S.vertexOf (Sum.inl x)).card ≤ k - 1 :=
      card_vertexOf_vertexSplit_two_le' hk ((inl_mem_splitSet' (K := K)).2 hx)
    have hxc : K.colour x = .white := by
      rw [hK.colour_eq_of_mem_vertexOf hz ((RotationSystem.mem_vertexOf _).2 hx), hs]
    simp only [hv, hxc, hz, not_false_eq_true, true_and, if_true]
    split_ifs
    · change _ ≤ k - 3
      omega
    · exact Nat.zero_le _
  · have hv : S.vertexOf (Sum.inl x) = (K.vertexOf x).map Function.Embedding.inl :=
      K.vertexOf_vertexSplit_inl s 2 hx
    have hb : S.IsBoundaryVertex ((K.vertexOf x).map Function.Embedding.inl) ↔
        K.IsBoundaryVertex (K.vertexOf x) := K.isBoundaryVertex_map_inl_iff s 2 _
    simp only [hv, hb, card_map]
    exact le_rfl

/-- Splitting a white internal vertex `z = v(s)` with `k ≥ 4` darts from `s` with size `2`
decreases the white excess. -/
private theorem whiteExcess_vertexSplit_two_lt {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {s : H} (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (hk : 4 ≤ (K.vertexOf s).card)
    (hs : K.colour s = .white) : whiteExcess (K.vertexSplit s 2) < whiteExcess K := by
  set S := K.vertexSplit s 2
  set k := ({y | K.rot.SameCycle s y} : Finset H).card
  have hk' : 4 ≤ k := hk
  have hs1 := rot_ne_self_of_four_le hk'
  have hA0 : S.vertexOf (Sum.inr 0) = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} :=
    vertexOf_inr_zero_vertexSplit_two hs1
  have hA0card := card_splitTriple hs1
  have hle : ∀ e ∈ splitSet' K s, (S.vertexOf e).card ≤ k - 1 := fun e he =>
    card_vertexOf_vertexSplit_two_le' hk' he
  set wK : H → ℕ := fun x =>
    if ¬K.IsBoundaryVertex (K.vertexOf x) ∧ K.colour x = .white then (K.vertexOf x).card - 3
    else 0 with hwK
  set wS : H ⊕ Fin 2 → ℕ := fun e =>
    if ¬S.IsBoundaryVertex (S.vertexOf e) ∧ S.colour e = .white then (S.vertexOf e).card - 3
    else 0 with hwS
  have hw_le : ∀ x, wS (Sum.inl x) ≤ wK x := whiteWeight_vertexSplit_two_inl_le hK hz hk hs
  have hw_s : wS (Sum.inl s) = 0 := by
    have hv : S.vertexOf (Sum.inl s) = {Sum.inr 0, Sum.inl s, Sum.inl (K.rot s)} :=
      vertexOf_vertexSplit_two_of_mem_triple hs1 (by simp)
    simp only [hwS, hv, hA0card]
    split_ifs <;> rfl
  have hw_0 : wS (Sum.inr 0) = 0 := by
    simp only [hwS, hA0, hA0card]
    split_ifs <;> rfl
  have hw_1 : wS (Sum.inr 1) ≤ k - 4 := by
    have := hle (Sum.inr 1) inr_mem_splitSet'
    simp only [hwS]
    split_ifs <;> omega
  have hwK_s : wK s = k - 3 := by
    simp only [hwK, hz, hs, not_false_eq_true, and_self, if_true]
    rfl
  have hSsum : whiteExcess S = ∑ x, wS (Sum.inl x) + (wS (Sum.inr 0) + wS (Sum.inr 1)) := by
    rw [whiteExcess, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [hSsum, show whiteExcess K = ∑ x, wK x from rfl, ← add_sum_erase _ _ (mem_univ s),
    ← add_sum_erase _ _ (mem_univ s), hw_s, hw_0, hwK_s]
  have : ∑ x ∈ univ.erase s, wS (Sum.inl x) ≤ ∑ x ∈ univ.erase s, wK x :=
    sum_le_sum fun x _ => hw_le x
  omega

/-- Splitting a white internal vertex with at least four darts keeps the graph nearly
leafless. -/
private theorem isNearlyLeafless_vertexSplit_two {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {s : H} (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (hk : 4 ≤ (K.vertexOf s).card)
    (hs : K.colour s = .white) (hnl : K.IsNearlyLeafless) :
    (K.vertexSplit s 2).IsNearlyLeafless := by
  intro v hv
  obtain ⟨e, rfl⟩ := (K.vertexSplit s 2).mem_vertices.1
    ((K.vertexSplit s 2).mem_internalVertices.1 hv.1).1
  by_cases he : e ∈ splitSet' K s
  · have h1 := (vertexSplit_two_splitSet'_facts hK hz hk hs e he).2.1
    have h2 := hv.2
    omega
  · rcases e with x | i
    · rw [inl_mem_splitSet'] at he
      have hv' := K.vertexOf_vertexSplit_inl s 2 he
      have hint : ¬K.IsBoundaryVertex (K.vertexOf x) := by
        have := ((K.vertexSplit s 2).mem_internalVertices.1 hv.1).2
        rwa [hv', isBoundaryVertex_map_inl_iff K s 2] at this
      have hcard : (K.vertexOf x).card = 1 := by
        have := hv.2
        rwa [hv', card_map] at this
      obtain ⟨i, -, z, hz', hzi⟩ := hnl _ ⟨K.vertexOf_mem_internalVertices.2 hint, hcard⟩
      refine ⟨i, hv, Sum.inl z, ?_, ?_⟩
      · rw [hv']
        exact mem_map_of_mem _ hz'
      · change Sum.inl (K.inv z) ∈ (K.vertexSplit s 2).bvertex i
        rw [bvertex_vertexSplit K s 2 hK hz i]
        exact mem_map_of_mem _ hzi
    · exact absurd inr_mem_splitSet' he

/-- Splitting a white internal vertex with at least four darts keeps white internal vertices
with at least three darts. -/
private theorem whiteGE_vertexSplit_two {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {s : H} (hz : ¬K.IsBoundaryVertex (K.vertexOf s)) (hk : 4 ≤ (K.vertexOf s).card)
    (hs : K.colour s = .white) (hw : WhiteGE K 3) : WhiteGE (K.vertexSplit s 2) 3 := by
  intro e he hec
  by_cases hes : e ∈ splitSet' K s
  · exact (vertexSplit_two_splitSet'_facts hK hz hk hs e hes).2.1
  · rcases e with x | i
    · rw [inl_mem_splitSet'] at hes
      have hv' := K.vertexOf_vertexSplit_inl s 2 hes
      rw [hv', isBoundaryVertex_map_inl_iff K s 2] at he
      rw [hv', card_map]
      exact hw x he hec
    · exact absurd inr_mem_splitSet' hes

end Split

/-! #### The stages -/

private theorem stage1 (n : ℕ) : ∀ K : PlabicGraph b, Fintype.card K.Dart = n →
    K.data.IsNearlyLeafless → WhiteGE K.data 2 →
    ∃ K' : PlabicGraph b, PlabicGraph.MoveEquivalent Set.univ K K' ∧
      K'.data.IsNearlyLeafless ∧ WhiteGE K'.data 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn hnl hw
  by_cases h2 : ∃ x, ¬K.data.IsBoundaryVertex (K.data.vertexOf x) ∧ K.data.colour x = .white ∧
      (K.data.vertexOf x).card = 2
  · obtain ⟨x, hx, -, hx2⟩ := h2
    have hd := isBivalentRemovable_of_card_two K.isPlabicGraph hx hx2
    have hlt : Fintype.card (({x, K.data.rot x}ᶜ : Set K.Dart)) < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := x) (by simp)
    obtain ⟨K', h1, h2, h3⟩ := ih _ hlt ⟨_, K.data.bivalentRemoval K.isPlabicGraph hd,
      isPlabicGraph_bivalentRemoval K.isPlabicGraph hd⟩ rfl
      (hnl.bivalentRemoval K.isPlabicGraph hd) (whiteGE_bivalentRemoval K.isPlabicGraph hd hw)
    refine ⟨K', PlabicGraph.MoveEquivalent.trans ?_ h1, h2, h3⟩
    exact PlabicGraph.MoveEquivalent.of_isLocalMove (t := .m2) (Set.mem_univ _)
      (Or.inl ⟨x, hd, ⟨PlabicData.Iso.refl _⟩⟩)
  · refine ⟨K, PlabicGraph.MoveEquivalent.refl _ _, hnl, fun x hx hxc => ?_⟩
    have := hw x hx hxc
    have : (K.data.vertexOf x).card ≠ 2 := fun h => h2 ⟨x, hx, hxc, h⟩
    omega

private theorem stage3 (n : ℕ) : ∀ K : PlabicGraph b,
    (univ.filter fun e => e ∉ K.data.bdry ∧ ¬BlackEnd K.data e).card = n →
    K.data.IsNearlyLeafless → WhiteGE K.data 3 → WhiteLE3 K.data →
    ∃ K' : PlabicGraph b, PlabicGraph.MoveEquivalent Set.univ K K' ∧
      K'.data.IsNearlyLeafless ∧ WhiteGE K'.data 3 ∧ WhiteLE3 K'.data ∧
      ∀ e, e ∉ K'.data.bdry → BlackEnd K'.data e := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn hnl hw hw'
  by_cases hbad : ∃ d, d ∉ K.data.bdry ∧ ¬BlackEnd K.data d
  · obtain ⟨d, hd, hdE⟩ := hbad
    have hG := K.isPlabicGraph
    have hw2 : WhiteGE K.data 2 := fun x hx hxc => (Nat.le_succ 2).trans (hw x hx hxc)
    obtain ⟨K', h1, h2, h3, h4, h5⟩ := ih _ (hn ▸ card_bad_bivalentInsertion hG ⟨hd, hdE⟩)
      ⟨_, K.data.bivalentInsertion d .black, isPlabicGraph_bivalentInsertion .black hG hd⟩ rfl
      (isNearlyLeafless_bivalentInsertion hG hnl hw2 hdE) (whiteGE_bivalentInsertion hw)
      (whiteLE3_bivalentInsertion hw')
    refine ⟨K', PlabicGraph.MoveEquivalent.trans ?_ h1, h2, h3, h4, h5⟩
    refine PlabicGraph.MoveEquivalent.of_isLocalMove (t := .m2) (Set.mem_univ _)
      (Or.inr ⟨Sum.inr 0, isBivalentRemovable_bivalentInsertion d .black, ?_⟩)
    exact (bivalentRemoval_bivalentInsertion_isomorphic .black hG hd).symm
  · push Not at hbad
    exact ⟨K, PlabicGraph.MoveEquivalent.refl _ _, hnl, hw, hw', hbad⟩

private theorem stage4 (n : ℕ) : ∀ K : PlabicGraph b, Fintype.card K.Dart = n →
    K.data.IsNearlyLeafless → WhiteGE K.data 3 → WhiteLE3 K.data →
    (∀ e, e ∉ K.data.bdry → BlackEnd K.data e) →
    ∃ K' : PlabicGraph b, PlabicGraph.MoveEquivalent Set.univ K K' ∧
      K'.data.IsNearlyLeafless ∧ WhiteGE K'.data 3 ∧ WhiteLE3 K'.data ∧
      (∀ e, e ∉ K'.data.bdry → BlackEnd K'.data e) ∧
      ∀ e, ¬K'.data.IsBoundaryVertex (K'.data.vertexOf e) →
        ¬K'.data.IsBoundaryVertex (K'.data.vertexOf (K'.data.inv e)) →
        K'.data.colour e = .black → K'.data.colour (K'.data.inv e) = .black →
        K'.data.vertexOf e = K'.data.vertexOf (K'.data.inv e) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn hnl hw hw' hE
  by_cases hc : ∃ e, ¬K.data.IsBoundaryVertex (K.data.vertexOf e) ∧
      ¬K.data.IsBoundaryVertex (K.data.vertexOf (K.data.inv e)) ∧
      K.data.colour e = .black ∧ K.data.colour (K.data.inv e) = .black ∧
      K.data.vertexOf e ≠ K.data.vertexOf (K.data.inv e)
  · obtain ⟨e, h1, h2, h3, h4, h5⟩ := hc
    have hG := K.isPlabicGraph
    have he : K.data.IsContractibleEdge e := ⟨h5, K.data.vertexOf_mem_internalVertices.2 h1,
      K.data.vertexOf_mem_internalVertices.2 h2, h4.trans h3.symm⟩
    have hlt : Fintype.card (({e, K.data.inv e}ᶜ : Set K.Dart)) < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := e) (by simp)
    obtain ⟨K', k1, k2, k3, k4, k5, k6⟩ := ih _ hlt
      ⟨_, K.data.contractEdge e (he.leg_mem hG), hG.contractEdge he⟩ rfl
      (hnl.contractEdge hG he) (whiteGE_contractEdge hG he h3 hw)
      (whiteLE3_contractEdge hG he h3 hw') (blackEnd_contractEdge hG he hE)
    refine ⟨K', PlabicGraph.MoveEquivalent.trans ?_ k1, k2, k3, k4, k5, k6⟩
    exact PlabicGraph.MoveEquivalent.of_isLocalMove (t := .m3) (Set.mem_univ _)
      (Or.inl ⟨e, he, ⟨PlabicData.Iso.refl _⟩⟩)
  · push Not at hc
    exact ⟨K, PlabicGraph.MoveEquivalent.refl _ _, hnl, hw, hw', hE, hc⟩

private theorem stage2 (n : ℕ) : ∀ K : PlabicGraph b, whiteExcess K.data = n →
    K.data.IsNearlyLeafless → WhiteGE K.data 3 →
    ∃ K' : PlabicGraph b, PlabicGraph.MoveEquivalent Set.univ K K' ∧
      K'.data.IsNearlyLeafless ∧ WhiteGE K'.data 3 ∧ WhiteLE3 K'.data := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K hn hnl hw
  by_cases h4 : ∃ s, ¬K.data.IsBoundaryVertex (K.data.vertexOf s) ∧ K.data.colour s = .white ∧
      4 ≤ (K.data.vertexOf s).card
  · obtain ⟨s, hz, hs, hk⟩ := h4
    have hG := K.isPlabicGraph
    have hlt := whiteExcess_vertexSplit_two_lt hG hz hk hs
    obtain ⟨K', h1, h2, h3, h4⟩ := ih _ (hn ▸ hlt) ⟨_, K.data.vertexSplit s 2, hG.vertexSplit hz 2⟩
      rfl (isNearlyLeafless_vertexSplit_two hG hz hk hs hnl)
      (whiteGE_vertexSplit_two hG hz hk hs hw)
    refine ⟨K', PlabicGraph.MoveEquivalent.trans ?_ h1, h2, h3, h4⟩
    refine PlabicGraph.MoveEquivalent.of_isLocalMove (t := .m3) (Set.mem_univ _)
      (Or.inr ⟨Sum.inr 0, ?_⟩)
    exact ⟨K.data.isContractibleEdge_vertexSplit s 2 hz (by omega),
      K.data.isomorphic_contractEdge_vertexSplit s 2 hG.inv_involutive⟩
  · push Not at h4
    refine ⟨K, PlabicGraph.MoveEquivalent.refl _ _, hnl, hw, fun x hx hxc => ?_⟩
    have := h4 x hx hxc
    omega

end Normalize

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- Let `K` be a nearly leafless plabic graph without white lollipops. Then `K` is move-equivalent
to a nearly leafless plabic graph `K'` that is normal, or has an edge of the graph `{d, d̄}`
(so `d ∉ B`) that is a loop (`v(d̄) = v(d)`) at a black internal vertex. -/
@[cluster_algebras "lem_normalize_or_loop"]
theorem exists_moveEquivalent_isNormal_or_loop {K : PlabicGraph b}
    (hK : K.data.IsNearlyLeafless) (hw : ∀ i v, ¬K.data.IsLollipopOfColour i .white v) :
    ∃ K' : PlabicGraph b, MoveEquivalent Set.univ K K' ∧ K'.data.IsNearlyLeafless ∧
      (K'.data.IsNormal ∨ ∃ d, d ∉ K'.data.bdry ∧ K'.data.vertexOf (K'.data.inv d) =
        K'.data.vertexOf d ∧ ¬K'.data.IsBoundaryVertex (K'.data.vertexOf d) ∧
        K'.data.colour d = .black) := by
  have hw2 : WhiteGE K.data 2 := by
    intro x hx hxc
    refine two_le_card_vertexOf_of_not_isInternalLeaf hx fun hl => ?_
    obtain ⟨i, hi⟩ := hK _ hl
    refine hw i _ ⟨hi, fun y hy => ?_⟩
    rw [K.isPlabicGraph.colour_eq_of_mem_vertexOf hx hy, hxc]
  obtain ⟨K₁, e₁, n₁, w₁⟩ := stage1 _ K rfl hK hw2
  obtain ⟨K₂, e₂, n₂, w₂, w₂'⟩ := stage2 _ K₁ rfl n₁ w₁
  obtain ⟨K₃, e₃, n₃, w₃, w₃', b₃⟩ := stage3 _ K₂ rfl n₂ w₂ w₂'
  obtain ⟨K₄, e₄, n₄, w₄, w₄', b₄, c₄⟩ := stage4 _ K₃ rfl n₃ w₃ w₃' b₃
  refine ⟨K₄, e₁.trans (e₂.trans (e₃.trans e₄)), n₄, ?_⟩
  by_cases hloop : ∃ d, d ∉ K₄.data.bdry ∧ K₄.data.vertexOf (K₄.data.inv d) =
      K₄.data.vertexOf d ∧ ¬K₄.data.IsBoundaryVertex (K₄.data.vertexOf d) ∧
      K₄.data.colour d = .black
  · exact Or.inr hloop
  left
  have hG := K₄.isPlabicGraph
  -- a leg runs to a black internal vertex
  have hleg : ∀ i, ¬K₄.data.IsBoundaryVertex (K₄.data.vertexOf (K₄.data.inv (K₄.data.leg i))) ∧
      K₄.data.colour (K₄.data.inv (K₄.data.leg i)) = .black := by
    intro i
    rcases b₄ _ (hG.leg_notMem_bdry i) with ⟨h, -⟩ | h
    · exact absurd (K₄.data.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)) h
    · exact h
  refine ⟨fun d hd hd' hcol => ?_, fun d hd hdc => le_antisymm (w₄' d hd hdc) (w₄ d hd hdc),
    fun i => (hleg i).1, fun i => (hleg i).2⟩
  have hdB : d ∉ K₄.data.bdry := fun h => hd (K₄.data.isBoundaryVertex_vertexOf_of_mem h)
  have hblack : K₄.data.colour d = .black := by
    rcases b₄ d hdB with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact hcol ▸ h
  exact hloop ⟨d, hdB, (c₄ d hd hd' hblack (hcol ▸ hblack)).symm, hd, hblack⟩

end PlabicGraph

end ClusterAlgebras
