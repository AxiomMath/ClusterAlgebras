/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.External
public import ClusterAlgebras.Plabic.FlipMoves
public import ClusterAlgebras.Plabic.NearlyLeafless
public import ClusterAlgebras.Plabic.TreeCollapse
public import ClusterAlgebras.Plabic.TrivalentMoves

/-!
# Collapsing trees and reducedness

Collapsing the collapsible trees of a plabic graph removes the internal leaves that are not
lollipops but are allowed in a reduced graph. This file collects the consequences used to
characterise reduced plabic graphs.

A hollow digon of a plabic graph `K`, or an internal leaf of `K` that is neither a lollipop nor a
non-root vertex of a collapsible tree, survives the collapse `K/𝒯` of a collapsing family: if
`K/𝒯` is nearly leafless, it contains a hollow digon. A reduced plabic graph is
`{M2, M3}`-equivalent to a nearly leafless one, obtained by collapsing its collapsible trees one at
a time. Finally, a lollipop at `j`, or a collapsible tree with root `β(j)`, makes `j` a fixed point
of the trip permutation: the one-way trip from `j` goes to the lollipop and comes straight back.

## Main definitions

* `ClusterAlgebras.PlabicGraph.collapse`: the collapse `K/𝒯` of a collapsing family, as a plabic
  graph.
* `ClusterAlgebras.PlabicGraph.CollapseStep`, `ClusterAlgebras.PlabicGraph.HasCollapseSteps`: the
  conclusion and the statement that a step of a move equivalence lifts to the collapses of
  collapsing families with nearly leafless collapse.
* `ClusterAlgebras.PlabicGraph.IsLiteralMove`: the five constructions of the local moves (square
  move, removal and insertion of a bivalent vertex, contraction of an edge and splitting of a
  vertex) on the darts of the construction.
* `ClusterAlgebras.PlabicData.RootedTree.map`, `ClusterAlgebras.PlabicData.Iso.mapFamily`: the
  image of a rooted tree and of a family of trees under an isomorphism.

## Main results

* `ClusterAlgebras.PlabicData.IsCollapsingFamily.exists_isHollowDigon_collapse`: collapsing keeps
  forbidden configurations visible.
* `ClusterAlgebras.PlabicGraph.IsReduced.exists_moveEquivalent_isNearlyLeafless`: a reduced plabic
  graph is `{M2, M3}`-equivalent to a nearly leafless one.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.tripPerm_eq_self_of_isLollipop_or_isCollapsible`: a
  lollipop at `j` or a collapsible tree with root `β(j)` gives a fixed point `j` of the trip
  permutation.
* `ClusterAlgebras.PlabicData.Iso.collapse`: isomorphic graphs have isomorphic collapses, along
  the image of the family.
* `ClusterAlgebras.PlabicGraph.MoveStep.of_isomorphic`: a step of an `S`-equivalence between two
  graphs is a step between any graphs isomorphic to them.
* `ClusterAlgebras.PlabicGraph.hasCollapseSteps_of_isLiteralMove`: `HasCollapseSteps b` reduces
  to the literal local moves.
* `ClusterAlgebras.PlabicGraph.collapseStep_squareMove`: the case of a square move.
* `ClusterAlgebras.PlabicGraph.not_isReduced_iff_of_hasCollapseSteps`: given
  `HasCollapseSteps b`, a nearly leafless plabic graph is not reduced if and only if it is nearly
  leafless equivalent to a graph containing a hollow digon.
* `ClusterAlgebras.PlabicGraph.reflTransGen_leaflessStep_of_hasCollapseSteps`: given
  `HasCollapseSteps b`, move-equivalent reduced graphs without internal leaves are joined by a
  sequence of steps through graphs without internal leaves.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is the label `i + 1` of [FWZ].
* The darts of the collapse `K/𝒯` are a subset of the darts of `K`, so a dart of the collapse is
  compared with the dart of `K` it is.
* Isomorphisms carry collapsing families and their collapses (`Iso.collapse`), so to prove
  `HasCollapseSteps b` it suffices to treat the five literal local moves; the square move is
  treated here. The results `not_isReduced_iff_of_hasCollapseSteps` and
  `reflTransGen_leaflessStep_of_hasCollapseSteps` are derived from `HasCollapseSteps b`, following
  the induction of [FWZ] along a sequence of moves.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-- A permutation exchanging `a` and `b` has the orbit `{a, b}` through `a`. -/
private theorem sameCycle_iff_of_apply_eq' {α : Type*} {f : Equiv.Perm α} {a b : α}
    (hab : f a = b) (hba : f b = a) (z : α) : f.SameCycle a z ↔ z = a ∨ z = b := by
  constructor
  · rintro ⟨n, rfl⟩
    have key : ∀ n : ℤ, (f ^ n) a = a ∨ (f ^ n) a = b := by
      intro n
      induction n using Int.induction_on with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
        rcases ih with h | h <;> rw [h]
        · exact Or.inr hab
        · exact Or.inl hba
      | pred n ih =>
        rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg, zpow_one, Equiv.Perm.mul_apply]
        rcases ih with h | h <;> rw [h]
        · exact Or.inr (by rw [Equiv.Perm.inv_eq_iff_eq, hba])
        · exact Or.inl (by rw [Equiv.Perm.inv_eq_iff_eq, hab])
    exact key n
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← hab]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)

namespace PlabicData

/-! ### Lollipops and fixed points of the trip permutation -/

section Lollipop

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- A vertex that is an internal vertex is the vertex of each of its darts. -/
private theorem vertexOf_eq_of_mem_internalVertices {v : Finset H} (hv : v ∈ G.internalVertices)
    {x : H} (hx : x ∈ v) : G.vertexOf x = v := by
  obtain ⟨y, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hv).1
  exact G.vertexOf_eq_of_mem hx

/-- A lollipop at `j` is the vertex `{ḡ_j}`. -/
theorem IsLollipop.eq_singleton_inv_leg (hG : G.IsPlabicGraph) {j : Fin b} {v : Finset H}
    (hv : G.IsLollipop j v) : v = {G.inv (G.leg j)} := by
  obtain ⟨⟨hvI, hcard⟩, x, hx, hxj⟩ := hv
  have hxB : x ∉ G.bdry := fun h => (G.mem_internalVertices.1 hvI).2 ⟨x, hx, h⟩
  have hinvB : G.inv x ∉ G.bdry := fun h => hxB (hG.inv_mem_bdry_iff.1 h)
  have hleg : G.inv x = G.leg j := by
    have : G.inv x ∈ (G.bvertex j).filter (· ∉ G.bdry) := mem_filter.2 ⟨hxj, hinvB⟩
    rwa [hG.filter_bvertex_notMem_bdry, mem_singleton] at this
  rw [← hleg, hG.inv_involutive]
  obtain ⟨a, rfl⟩ := card_eq_one.1 hcard
  rw [mem_singleton.1 hx]

/-- A lollipop at `j` gives a fixed point `j` of the trip permutation: `T(g_j) = ḡ_j` and
`T(ḡ_j) = g_j`. -/
theorem IsPlabicGraph.tripPerm_eq_self_of_isLollipop (hG : G.IsPlabicGraph) {j : Fin b}
    {v : Finset H} (hv : G.IsLollipop j v) : G.tripPerm j = j := by
  have hv' := hv.eq_singleton_inv_leg hG
  obtain ⟨⟨hvI, -⟩, -⟩ := hv
  set x := G.inv (G.leg j) with hxdef
  have hxv : G.vertexOf x = v :=
    vertexOf_eq_of_mem_internalVertices hvI (hv' ▸ mem_singleton_self x)
  have hint : ¬G.IsBoundaryVertex (G.vertexOf x) := hxv ▸ (G.mem_internalVertices.1 hvI).2
  have hrot : G.rot x = x := by
    have : G.rot x ∈ v := hxv ▸ G.rot_mem_vertexOf x
    rw [hv'] at this
    exact mem_singleton.1 this
  have hrot' : G.rot.symm x = x := by
    rw [Equiv.symm_apply_eq, hrot]
  have h1 : G.tripMap (G.leg j) = x := by
    rw [tripMap_apply]
    cases hc : G.colour x with
    | white => rw [turn_of_white hint hc, hrot']
    | black => rw [turn_of_black hint hc, hrot]
  have h2 : G.tripMap x = G.leg j := by
    rw [tripMap_apply, hxdef, hG.inv_involutive,
      turn_of_isBoundaryVertex (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j))]
  have hxleg : ¬G.IsLeg x := by
    rintro ⟨i, hi⟩
    exact hint (hi ▸ G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))
  have h21 : G.tripMap^[2] (G.leg j) = G.leg j := by
    change G.tripMap (G.tripMap (G.leg j)) = G.leg j
    rw [h1, h2]
  have hlen : G.tripLength j = 2 := by
    have hle : G.tripLength j ≤ 2 := tripLength_le two_pos ⟨j, h21.symm⟩
    have hpos := hG.tripLength_pos j
    have hne : G.tripLength j ≠ 1 := by
      intro h1'
      have := (tripLength_spec (hG.exists_isLeg_iterate_tripMap j)).2
      rw [h1'] at this
      exact hxleg (h1 ▸ this)
    omega
  rw [hG.tripPerm_eq_iff, hlen, h21]

end Lollipop

section CollapsibleTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- Collapsing a collapsible tree with root `β(j)` produces a lollipop at `j`. -/
theorem RootedTree.exists_isLollipop_collapse (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (c : Shade) {j : Fin b} (hroot : T.root = G.bvertex j) :
    ∃ v, (G.collapse {(T, c)}).IsLollipop j v := by
  have hlegD : G.leg j ∈ G.familyDarts {(T, c)} :=
    mem_familyDarts.2 ⟨(T, c), mem_singleton_self _, by
      rw [← T.intervalStart_eq_leg hG hroot]; exact T.intervalStart_mem_darts⟩
  set x : G.collapseDarts {(T, c)} := ⟨G.inv (G.leg j), Or.inr ⟨j, hlegD, rfl⟩⟩ with hxdef
  have hvx : (G.collapse {(T, c)}).vertexOf x = {x} := collapse_vertexOf_inv_leg hG hlegD rfl
  have hxB : x ∉ (G.collapse {(T, c)}).bdry := fun h =>
    hG.leg_notMem_bdry j (hG.inv_mem_bdry_iff.1 (mem_collapse_bdry.1 h))
  refine ⟨{x}, ⟨?_, card_singleton x⟩, x, mem_singleton_self x, ?_⟩
  · rw [← hvx, DiskMap.vertexOf_mem_internalVertices, hvx]
    rintro ⟨y, hy, hyB⟩
    rw [mem_singleton.1 hy] at hyB
    exact hxB hyB
  · have hinv : (G.collapse {(T, c)}).inv x = (G.collapse {(T, c)}).leg j := by
      apply Subtype.ext
      rw [coe_collapse_inv hG, hxdef, hG.inv_involutive]
      rfl
    rw [hinv]
    exact (G.collapse {(T, c)}).leg_mem_bvertex j

/-- **A lollipop or a collapsible tree gives a fixed point**. Let `G` be a plabic graph with `b`
boundary vertices and `j` a label such that `G` has a lollipop at `j` or a collapsible tree with
root `β(j)`. Then `π_G(j) = j`. Labels are `0`-indexed: `j : Fin b` stands for the boundary
label `j + 1`. -/
@[cluster_algebras "lem_lollipop_fixed_point"]
theorem IsPlabicGraph.tripPerm_eq_self_of_isLollipop_or_isCollapsible (hG : G.IsPlabicGraph)
    {j : Fin b}
    (h : (∃ v, G.IsLollipop j v) ∨ ∃ T : G.RootedTree, T.root = G.bvertex j ∧ T.IsCollapsible) :
    G.tripPerm j = j := by
  rcases h with ⟨v, hv⟩ | ⟨T, hroot, c, hT⟩
  · exact hG.tripPerm_eq_self_of_isLollipop hv
  obtain ⟨h1, hmove⟩ := hT.moveEquivalent_collapse hG
  have hπ := PlabicGraph.MoveEquivalent.tripPerm_eq (hmove.mono (Set.subset_univ _))
  obtain ⟨v, hv⟩ := T.exists_isLollipop_collapse hG c hroot
  exact (congrFun hπ j).trans (h1.tripPerm_eq_self_of_isLollipop hv)

end CollapsibleTree

/-! ### Collapsing keeps forbidden configurations visible -/

section Digon

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- In a rooted tree, the two ends of an edge `{d, d̄}` of the tree are not joined by a path of
other edges of the tree. -/
private theorem RootedTree.not_reflTransGen_of_mem_darts (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {d : H} (hd : d ∈ T.darts)
    (h : Relation.ReflTransGen (fun u u' => ∃ e ∈ T.darts, e ≠ d ∧ e ≠ G.inv d ∧
      G.vertexOf e = u ∧ G.vertexOf (G.inv e) = u') (G.vertexOf d) (G.vertexOf (G.inv d))) :
    False := by
  have hinv := hG.inv_involutive
  set D' := T.darts.filter fun e => e ≠ d ∧ e ≠ G.inv d with hD'
  have hD'mem : ∀ e, e ∈ D' ↔ e ∈ T.darts ∧ e ≠ d ∧ e ≠ G.inv d := fun e => mem_filter
  set R : Finset H → Finset H → Prop :=
    fun u u' => ∃ e ∈ D', G.vertexOf e = u ∧ G.vertexOf (G.inv e) = u' with hR
  have hRsymm : ∀ u u', R u u' → R u' u := by
    rintro u u' ⟨e, he, rfl, rfl⟩
    obtain ⟨heD, h1, h2⟩ := (hD'mem e).1 he
    refine ⟨G.inv e, (hD'mem _).2 ⟨T.inv_mem_darts hG heD, fun h' => h2 ?_, fun h' => h1 ?_⟩,
      rfl, by rw [hinv]⟩
    · rw [← h', hinv]
    · exact hinv.injective h'
  have hpath : Relation.ReflTransGen R (G.vertexOf d) (G.vertexOf (G.inv d)) := by
    refine Relation.ReflTransGen.mono (fun u u' ⟨e, he, h1, h2, h3, h4⟩ => ?_) h
    exact ⟨e, (hD'mem e).2 ⟨he, h1, h2⟩, h3, h4⟩
  have hconn : ∀ u ∈ insert T.root T.nonRoot, Relation.ReflTransGen R T.root u := by
    intro u hu
    have h0 := T.reflTransGen_treeAdj u hu
    induction h0 with
    | refl => exact .refl
    | @tail u₁ u₂ _ hstep ih =>
      obtain ⟨e, heD, rfl, rfl⟩ := hstep
      have ih' := ih (by
        rcases T.vertexOf_mem_or_eq_root hG heD with h' | h'
        · exact mem_insert_of_mem h'
        · rw [h']; exact mem_insert_self _ _)
      by_cases h1 : e = d
      · subst h1
        exact ih'.trans hpath
      by_cases h2 : e = G.inv d
      · subst h2
        rw [hinv]
        have : Std.Symm R := ⟨fun _ _ h => hRsymm _ _ h⟩
        exact ih'.trans (Relation.ReflTransGen.stdSymm.symm _ _ hpath)
      · exact ih'.tail ⟨e, (hD'mem e).2 ⟨heD, h1, h2⟩, rfl, rfl⟩
  have hbound := card_le_card_image_pair_add_one G.vertexOf G.inv hinv D'
    (fun e he => by
      obtain ⟨heD, h1, h2⟩ := (hD'mem e).1 he
      refine (hD'mem _).2 ⟨T.inv_mem_darts hG heD, fun h' => h2 (by rw [← h', hinv]),
        fun h' => h1 (hinv.injective h')⟩)
    (insert T.root T.nonRoot) T.root (mem_insert_self _ _)
    (fun e he => by
      rcases T.vertexOf_mem_or_eq_root hG ((hD'mem e).1 he).1 with h' | h'
      · exact mem_insert_of_mem h'
      · rw [h']; exact mem_insert_self _ _) hconn
  rw [card_insert_of_notMem T.root_notMem_nonRoot] at hbound
  have hsub : (D'.image fun e => ({e, G.inv e} : Finset H)) ⊆
      (T.darts.image G.edgeOf).erase (G.edgeOf d) := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := mem_image.1 hs
    obtain ⟨heD, h1, h2⟩ := (hD'mem e).1 he
    refine mem_erase.2 ⟨fun h' => ?_, mem_image.2 ⟨e, heD, rfl⟩⟩
    rcases (G.edgeOf_eq_edgeOf_iff hinv).1 h' with h' | h'
    · exact h1 h'
    · exact h2 h'
  have hcard := card_le_card hsub
  rw [card_erase_of_mem (mem_image.2 ⟨d, hd, rfl⟩), T.card_image_edgeOf] at hcard
  have := T.nonRoot_nonempty.card_pos
  omega

/-- A rooted tree has no two distinct edges with the same ends. -/
private theorem RootedTree.false_of_parallel (hG : G.IsPlabicGraph) (T : G.RootedTree) {d e : H}
    (hd : d ∈ T.darts) (he : e ∈ T.darts) (h1 : e ≠ d) (h2 : e ≠ G.inv d)
    (hv : G.vertexOf e = G.vertexOf d) (hv' : G.vertexOf (G.inv e) = G.vertexOf (G.inv d)) :
    False :=
  T.not_reflTransGen_of_mem_darts hG hd (Relation.ReflTransGen.single ⟨e, he, h1, h2, hv, hv'⟩)

/-- In a plabic graph, two darts exchanged by the face permutation are not the two darts of an
edge. -/
private theorem ne_inv_of_facePerm (hG : G.IsPlabicGraph) {d₁ d₂ : H}
    (h₁ : G.facePerm d₁ = d₂) (h₂ : G.facePerm d₂ = d₁) (hB₁ : d₁ ∉ G.bdry) (hB₂ : d₂ ∉ G.bdry) :
    d₂ ≠ G.inv d₁ := by
  intro h
  have hinv := hG.inv_involutive
  have hr₁ : G.rot (G.inv d₁) = G.inv d₁ := by
    have := h₁
    rw [RotationSystem.facePerm_apply] at this
    rw [this, h]
  have hr₂ : G.rot d₁ = d₁ := by
    rwa [RotationSystem.facePerm_apply, h, hinv] at h₂
  have hreach : ∀ e, G.Reach d₁ e → e = d₁ ∨ e = G.inv d₁ := by
    intro e he
    induction he with
    | refl => exact Or.inl rfl
    | rot _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inl hr₂
      · exact Or.inr hr₁
    | inv _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (hinv _)
  obtain ⟨y, -, hyB⟩ := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem ⟨0, hG.one_le⟩)
  rcases hreach y (hG.reach d₁ y) with rfl | rfl
  · exact hB₁ hyB
  · exact hB₂ (h ▸ hyB)

/-- A vertex of a hollow digon does not lie in the set `W` of a rooted tree. -/
private theorem RootedTree.vertexOf_notMem_nonRoot_of_facePerm (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {d₁ d₂ : H} (h₁ : G.facePerm d₁ = d₂) (h₂ : G.facePerm d₂ = d₁)
    (hne : d₁ ≠ d₂) (hB₁ : d₁ ∉ G.bdry) (hB₂ : d₂ ∉ G.bdry) : G.vertexOf d₁ ∉ T.nonRoot := by
  intro hW
  have hinv := hG.inv_involutive
  have hn := ne_inv_of_facePerm hG h₁ h₂ hB₁ hB₂
  have hv₁ : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := by
    rw [← h₁, RotationSystem.facePerm_apply, G.vertexOf_rot]
  have hv₂ : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := by
    rw [← h₂, RotationSystem.facePerm_apply, G.vertexOf_rot]
  have hd₁ : d₁ ∈ T.darts := T.mem_darts_of_vertexOf_mem hW
  have he : G.inv d₂ ∈ T.darts := T.mem_darts_of_vertexOf_mem (hv₂ ▸ hW)
  refine T.false_of_parallel hG hd₁ he (fun h => hn ?_) (fun h => hne (hinv.injective h).symm)
    hv₂ (by rw [hinv, hv₁])
  rw [← h, hinv]

/-- A dart of a hollow digon is not a dart of a rooted tree. -/
private theorem RootedTree.notMem_darts_of_facePerm (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {d₁ d₂ : H} (h₁ : G.facePerm d₁ = d₂) (h₂ : G.facePerm d₂ = d₁)
    (hne : d₁ ≠ d₂) (hB₁ : d₁ ∉ G.bdry) (hB₂ : d₂ ∉ G.bdry) : d₁ ∉ T.darts := by
  intro hd
  have hv₁ : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := by
    rw [← h₁, RotationSystem.facePerm_apply, G.vertexOf_rot]
  rcases T.vertexOf_mem_or_eq_root hG hd with h | h
  · exact T.vertexOf_notMem_nonRoot_of_facePerm hG h₁ h₂ hne hB₁ hB₂ h
  · have := T.vertexOf_inv_mem_nonRoot_of_mem_root hd (T.mem_root_iff.2 h)
    rw [hv₁] at this
    exact T.vertexOf_notMem_nonRoot_of_facePerm hG h₂ h₁ hne.symm hB₂ hB₁ this

/-- The darts of a hollow digon and their partners are kept by a collapse. -/
private theorem mem_collapseCore_of_facePerm (hG : G.IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)} {d₁ d₂ : H} (h₁ : G.facePerm d₁ = d₂)
    (h₂ : G.facePerm d₂ = d₁) (hne : d₁ ≠ d₂) (hB₁ : d₁ ∉ G.bdry) (hB₂ : d₂ ∉ G.bdry) :
    d₁ ∈ G.collapseCore 𝒯 ∧ G.inv d₁ ∈ G.collapseCore 𝒯 := by
  have hinv := hG.inv_involutive
  have hnot : d₁ ∉ G.familyDarts 𝒯 := fun h => by
    obtain ⟨p, -, hp⟩ := mem_familyDarts.1 h
    exact p.1.notMem_darts_of_facePerm hG h₁ h₂ hne hB₁ hB₂ hp
  refine ⟨Or.inl hnot, Or.inl fun h => hnot ?_⟩
  have := inv_mem_familyDarts hG h
  rwa [hinv] at this

/-- In a hollow digon `{d₁, d₂}`, the face permutation exchanges `d₁` and `d₂`. -/
private theorem facePerm_eq_of_faceOf_eq_pair {M : DiskMap H} {d₁ d₂ : H}
    (hf : M.faceOf d₁ = {d₁, d₂}) (hne : d₁ ≠ d₂) :
    M.facePerm d₁ = d₂ ∧ M.facePerm d₂ = d₁ := by
  have hmem : M.facePerm d₁ ∈ ({d₁, d₂} : Finset H) := hf ▸ M.facePerm_mem_faceOf d₁
  have h₁ : M.facePerm d₁ = d₂ := by
    rcases mem_insert.1 hmem with h | h
    · have := M.faceOf_eq_singleton h
      rw [hf] at this
      have h2 : d₂ ∈ ({d₁} : Finset H) := this ▸ mem_insert_of_mem (mem_singleton_self d₂)
      exact absurd (mem_singleton.1 h2).symm hne
    · exact mem_singleton.1 h
  refine ⟨h₁, ?_⟩
  have hf₂ : M.faceOf d₂ = {d₁, d₂} := by
    rw [M.faceOf_eq_of_mem (hf ▸ mem_insert_of_mem (mem_singleton_self d₂)), hf]
  have hmem₂ : M.facePerm d₂ ∈ ({d₁, d₂} : Finset H) := hf₂ ▸ M.facePerm_mem_faceOf d₂
  rcases mem_insert.1 hmem₂ with h | h
  · exact h
  · exact absurd (M.facePerm.injective (h₁.trans (mem_singleton.1 h).symm)) hne

/-- A hollow digon of `K` survives in the collapse `K/𝒯`. -/
private theorem isHollowDigon_collapse_of_isHollowDigon {K : PlabicData H b}
    (hK : K.IsPlabicGraph) (𝒯 : Finset (K.RootedTree × Shade)) {f : Finset H}
    (hf : K.IsHollowDigon f) : ∃ f, (K.collapse 𝒯).IsHollowDigon f := by
  obtain ⟨hf, d₁, d₂, rfl, hv⟩ := hf
  obtain ⟨hfF, hfB⟩ := K.mem_internalFaces.1 hf
  have hne : d₁ ≠ d₂ := fun h => hv (h ▸ rfl)
  have hB₁ : d₁ ∉ K.bdry := fun h => disjoint_left.1 hfB (mem_insert_self _ _) h
  have hB₂ : d₂ ∉ K.bdry := fun h =>
    disjoint_left.1 hfB (mem_insert_of_mem (mem_singleton_self _)) h
  have hface : K.faceOf d₁ = {d₁, d₂} := by
    obtain ⟨e, he⟩ := K.mem_faceOrbits.1 (K.mem_faces.1 hfF).2
    rw [← he] at hfF ⊢
    exact K.faceOf_eq_of_mem (he ▸ mem_insert_self _ _)
  obtain ⟨h₁, h₂⟩ := facePerm_eq_of_faceOf_eq_pair hface hne
  obtain ⟨hc₁, hci₁⟩ := mem_collapseCore_of_facePerm (𝒯 := 𝒯) hK h₁ h₂ hne hB₁ hB₂
  obtain ⟨hc₂, hci₂⟩ := mem_collapseCore_of_facePerm (𝒯 := 𝒯) hK h₂ h₁ hne.symm hB₂ hB₁
  set K' := K.collapse 𝒯
  set x₁ : K.collapseDarts 𝒯 := ⟨d₁, K.collapseCore_subset 𝒯 hc₁⟩
  set x₂ : K.collapseDarts 𝒯 := ⟨d₂, K.collapseCore_subset 𝒯 hc₂⟩
  have hφ : ∀ {y z : K.collapseDarts 𝒯}, K.facePerm y = z → (z : H) ∈ K.collapseCore 𝒯 →
      K.inv y ∈ K.collapseCore 𝒯 → K'.facePerm y = z := by
    intro y z hyz hz hy
    apply Subtype.ext
    have hiy : ((K'.inv y : K.collapseDarts 𝒯) : H) = K.inv y := coe_collapse_inv hK y
    rw [RotationSystem.facePerm_apply, coe_collapse_rot_of_mem (hiy ▸ hy)]
    simp only [hiy]
    rw [coe_firstReturn_of_apply_mem]
    · exact hyz
    · rw [← RotationSystem.facePerm_apply, hyz]
      exact hz
  have hφ₁ : K'.facePerm x₁ = x₂ := hφ h₁ hc₂ hci₁
  have hφ₂ : K'.facePerm x₂ = x₁ := hφ h₂ hc₁ hci₂
  have hne' : x₁ ≠ x₂ := fun h => hne (congrArg Subtype.val h)
  have hface' : K'.faceOf x₁ = {x₁, x₂} := by
    ext z
    rw [RotationSystem.mem_faceOf, sameCycle_iff_of_apply_eq' hφ₁ hφ₂, mem_insert,
      mem_singleton]
  have hxB : ∀ x : K.collapseDarts 𝒯, (x : H) ∉ K.bdry → x ∉ K'.bdry := fun x hx h =>
    hx (mem_collapse_bdry.1 h)
  refine ⟨K'.faceOf x₁, K'.mem_internalFaces.2 ⟨K'.mem_faces.2 ⟨fun h => ?_,
    K'.faceOf_mem_faceOrbits x₁⟩, ?_⟩, x₁, x₂, hface', fun h => ?_⟩
  · have : x₁ ∈ K'.exterior := h ▸ K'.self_mem_faceOf x₁
    exact hxB x₁ hB₁ (K'.exterior_subset_bdry this)
  · rw [hface', disjoint_insert_left, disjoint_singleton_left]
    exact ⟨hxB x₁ hB₁, hxB x₂ hB₂⟩
  · have hx₂ : x₂ ∈ K'.vertexOf x₁ := h ▸ K'.self_mem_vertexOf x₂
    have hmap := map_collapse_vertexOf_of_mem (x := x₁) hc₁
    have : (x₂ : H) ∈ (K'.vertexOf x₁).map (Function.Embedding.subtype _) :=
      mem_map_of_mem _ hx₂
    rw [hmap, mem_filter] at this
    exact hv (K.vertexOf_eq_of_mem this.1).symm
/-- If `K/𝒯` is nearly leafless, then `K` has no internal leaf that is neither a lollipop nor a
vertex, other than the root, of a collapsible tree. -/
private theorem IsCollapsingFamily.false_of_isInternalLeaf {K : PlabicData H b}
    (hK : K.IsPlabicGraph) {𝒯 : Finset (K.RootedTree × Shade)} (h𝒯 : K.IsCollapsingFamily 𝒯)
    (hnl : (K.collapse 𝒯).IsNearlyLeafless) {v : Finset H} (hv : K.IsInternalLeaf v)
    (hlol : ¬∃ i, K.IsLollipop i v)
    (hcol : ¬∃ T : K.RootedTree, T.IsCollapsible ∧ v ∈ T.nonRoot) : False := by
  obtain ⟨hvI, hcard⟩ := hv
  obtain ⟨x, hxv⟩ := K.mem_vertices.1 (K.mem_internalVertices.1 hvI).1
  have hxB : ∀ y ∈ v, y ∉ K.bdry := fun y hy hyB => (K.mem_internalVertices.1 hvI).2 ⟨y, hy, hyB⟩
  have hxK : x ∈ K.collapseCore 𝒯 := by
    refine Or.inl fun hxD => ?_
    obtain ⟨p, hp, hxp⟩ := mem_familyDarts.1 hxD
    rcases p.1.vertexOf_mem_or_eq_root hK hxp with h | h
    · exact hcol ⟨p.1, (h𝒯.isCollapsibleOfColour p hp).isCollapsible, hxv ▸ h⟩
    · have := p.1.one_lt_card_root
      rw [← h, hxv, hcard] at this
      exact lt_irrefl _ this
  set K' := K.collapse 𝒯
  set x' : K.collapseDarts 𝒯 := ⟨x, K.collapseCore_subset 𝒯 hxK⟩
  have hmap := map_collapse_vertexOf_of_mem (x := x') hxK
  have hsub : ∀ y ∈ K'.vertexOf x', (y : H) ∈ v := fun y hy => by
    have : (y : H) ∈ (K'.vertexOf x').map (Function.Embedding.subtype _) := mem_map_of_mem _ hy
    rw [hmap, mem_filter] at this
    exact hxv ▸ this.1
  have hleaf : K'.IsInternalLeaf (K'.vertexOf x') := by
    refine ⟨K'.vertexOf_mem_internalVertices.2 fun ⟨y, hy, hyB⟩ =>
      hxB y (hsub y hy) (mem_collapse_bdry.1 hyB), ?_⟩
    have hc1 : (K.vertexOf x).card = 1 := by rwa [hxv]
    have hall : ∀ y ∈ K.vertexOf x, y ∈ K.collapseCore 𝒯 := fun y hy => by
      have : y = x := card_le_one.1 hc1.le _ hy _ (K.self_mem_vertexOf x)
      exact this ▸ hxK
    have := congrArg card hmap
    rw [card_map, filter_true_of_mem hall] at this
    rw [this, hc1]
  obtain ⟨i, -, y, hy, hyi⟩ := hnl _ hleaf
  apply hlol
  refine ⟨i, ⟨hvI, hcard⟩, y, hsub y hy, ?_⟩
  have hlegK : K.leg i ∈ K.collapseCore 𝒯 := K.leg_mem_collapseCore 𝒯 i
  have hmap' := map_collapse_vertexOf_of_mem (x := K'.leg i) hlegK
  have : ((K'.inv y : K.collapseDarts 𝒯) : H) ∈
      (K'.vertexOf (K'.leg i)).map (Function.Embedding.subtype _) := mem_map_of_mem _ hyi
  rw [hmap', mem_filter, coe_collapse_inv hK] at this
  exact this.1

/-- **Collapsing keeps forbidden configurations visible**. Let `K` be a plabic graph containing a
hollow digon or an internal leaf that is not a lollipop and is not a vertex, other than the root,
of a collapsible tree of `K`. Let `𝒯` be a collapsing family of `K` such that `K/𝒯` is nearly
leafless. Then `K/𝒯` contains a hollow digon. -/
@[cluster_algebras "lem_family_collapse_digon"]
theorem IsCollapsingFamily.exists_isHollowDigon_collapse {K : PlabicData H b}
    (hK : K.IsPlabicGraph) {𝒯 : Finset (K.RootedTree × Shade)} (h𝒯 : K.IsCollapsingFamily 𝒯)
    (hnl : (K.collapse 𝒯).IsNearlyLeafless)
    (h : (∃ f, K.IsHollowDigon f) ∨ ∃ v, K.IsInternalLeaf v ∧ (¬∃ i, K.IsLollipop i v) ∧
      ¬∃ T : K.RootedTree, T.IsCollapsible ∧ v ∈ T.nonRoot) :
    ∃ f, (K.collapse 𝒯).IsHollowDigon f := by
  rcases h with ⟨f, hf⟩ | ⟨v, hv, hlol, hcol⟩
  · exact isHollowDigon_collapse_of_isHollowDigon hK 𝒯 hf
  · exact (h𝒯.false_of_isInternalLeaf hK hnl hv hlol hcol).elim

end Digon

end PlabicData

/-! ### Reduced graphs and nearly leafless graphs -/

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- The collapse of a collapsible tree deletes a dart. -/
theorem RootedTree.IsCollapsibleOfColour.exists_notMem_collapseDarts (hG : G.IsPlabicGraph)
    {T : G.RootedTree} {c : Shade} (hT : T.IsCollapsibleOfColour c) :
    ∃ x, x ∉ G.collapseDarts {(T, c)} := by
  have key : ∀ x, G.vertexOf x ∈ T.nonRoot → (∀ i, G.leg i ∈ T.darts → x ≠ G.inv (G.leg i)) →
      x ∉ G.collapseDarts {(T, c)} := by
    intro x hx hne
    rintro ((hxD | ⟨i, rfl⟩) | ⟨i, hi, rfl⟩)
    · exact hxD (mem_familyDarts.2 ⟨(T, c), mem_singleton_self _, T.mem_darts_of_vertexOf_mem hx⟩)
    · exact T.ne_leg_of_vertexOf_mem hG hx i rfl
    · obtain ⟨p, hp, hip⟩ := mem_familyDarts.1 hi
      rw [mem_singleton.1 hp] at hip
      exact hne i hip rfl
  have hvert : ∀ w ∈ T.nonRoot, ∃ x, G.vertexOf x = w := fun w hw =>
    G.mem_vertices.1 (G.mem_internalVertices.1 (T.nonRoot_subset hw)).1
  rcases hT.root_cases with ⟨hb, -⟩ | ⟨-, h2⟩
  · obtain ⟨w, hw⟩ := T.nonRoot_nonempty
    obtain ⟨x, rfl⟩ := hvert w hw
    refine ⟨x, key x hw fun i hi => absurd ?_ hb⟩
    rw [T.root_eq_bvertex_of_leg_mem hG hi]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  · obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := one_lt_card.1 h2
    obtain ⟨x₁, rfl⟩ := hvert w₁ hw₁
    obtain ⟨x₂, rfl⟩ := hvert w₂ hw₂
    by_cases h₁ : ∀ i, G.leg i ∈ T.darts → x₁ ≠ G.inv (G.leg i)
    · exact ⟨x₁, key x₁ hw₁ h₁⟩
    push Not at h₁
    obtain ⟨i, hi, rfl⟩ := h₁
    refine ⟨x₂, key x₂ hw₂ fun i' hi' hx₂ => hne ?_⟩
    have : i = i' := hG.bvertex_injective
      ((T.root_eq_bvertex_of_leg_mem hG hi).symm.trans (T.root_eq_bvertex_of_leg_mem hG hi'))
    rw [hx₂, this]

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- **A reduced graph is equivalent to one without stray leaves**. Let `G` be a reduced plabic
graph. Then `G` is `{M2, M3}`-equivalent to a nearly leafless plabic graph. -/
@[cluster_algebras "lem_reduced_nearly_leafless"]
theorem IsReduced.exists_moveEquivalent_isNearlyLeafless {G : PlabicGraph b} (hG : G.IsReduced) :
    ∃ G' : PlabicGraph b, G'.data.IsNearlyLeafless ∧ MoveEquivalent {.m2, .m3} G G' := by
  induction hn : Fintype.card G.Dart using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hnl : G.data.IsNearlyLeafless
  · exact ⟨G, hnl, .refl _ _⟩
  unfold IsNearlyLeafless at hnl
  push Not at hnl
  obtain ⟨v, hv, hvl⟩ := hnl
  rcases (hG G (.refl _ _)).2 v hv with ⟨i, hi⟩ | ⟨T, ⟨c, hT⟩, -⟩
  · exact absurd hi (hvl i)
  obtain ⟨h1, hmove⟩ := hT.moveEquivalent_collapse G.isPlabicGraph
  have hred : IsReduced ⟨_, G.data.collapse {(T, c)}, h1⟩ :=
    hG.of_moveEquivalent (hmove.mono (Set.subset_univ _))
  obtain ⟨x, hx⟩ := hT.exists_notMem_collapseDarts G.isPlabicGraph
  have hlt : Fintype.card (G.data.collapseDarts {(T, c)}) < n := by
    rw [← hn]
    exact Fintype.card_subtype_lt hx
  obtain ⟨G', hG', h'⟩ := ih _ hlt hred rfl
  exact ⟨G', hG', hmove.trans h'⟩

end PlabicGraph

/-! ### The collapse as a plabic graph -/

namespace PlabicData

section IsoLeafless

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {G : PlabicData H b} {G' : PlabicData H' b}

/-- An isomorphism of plabic graphs maps a nearly leafless graph to a nearly leafless graph. -/
theorem Iso.isNearlyLeafless (θ : G.Iso G') (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (h : G.IsNearlyLeafless) : G'.IsNearlyLeafless := by
  intro v hv
  obtain ⟨x, rfl⟩ := G'.mem_vertices.1 (G'.mem_internalVertices.1 hv.1).1
  have hx : G.IsInternalLeaf (G.vertexOf (θ.toEquiv.symm x)) := by
    rw [← θ.isInternalLeaf_vertexOf_iff, Equiv.apply_symm_apply]
    exact hv
  obtain ⟨i, -, d, hd, hdi⟩ := h _ hx
  refine ⟨i, hv, θ.toEquiv d, ?_, ?_⟩
  · have := θ.map_vertexOf (θ.toEquiv.symm x)
    rw [Equiv.apply_symm_apply] at this
    rw [← this]
    exact mem_map_equiv.2 (by rwa [Equiv.symm_apply_apply])
  · rw [← θ.map_inv, bvertex, ← θ.map_leg hG hG', ← θ.map_vertexOf]
    exact mem_map_of_mem _ hdi

end IsoLeafless

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- The empty family is a collapsing family. -/
theorem isCollapsingFamily_empty : G.IsCollapsingFamily ∅ :=
  ⟨by simp, by simp, by simp, by simp⟩

/-- Every dart lies in the core of the collapse along the empty family. -/
theorem mem_collapseCore_empty (x : H) : x ∈ G.collapseCore ∅ :=
  Or.inl (by simp [familyDarts])

/-- Every dart is a dart of the collapse along the empty family. -/
theorem mem_collapseDarts_empty (x : H) : x ∈ G.collapseDarts ∅ :=
  G.collapseCore_subset ∅ (mem_collapseCore_empty x)

/-- The collapse `G/∅` of the empty family is isomorphic to `G`: no dart is deleted, the first
return of `σ` to all of `H` is `σ`, and no colour changes. -/
noncomputable def collapseEmptyIso (hG : G.IsPlabicGraph) : (G.collapse ∅).Iso G :=
  Iso.ofEquivOfMapLeg (Equiv.subtypeUnivEquiv mem_collapseDarts_empty)
    (fun x => coe_collapse_inv hG x)
    (fun x => by
      change ((G.collapse ∅).rot x : H) = G.rot x
      rw [coe_collapse_rot_of_mem (mem_collapseCore_empty _),
        coe_firstReturn_of_apply_mem (mem_collapseCore_empty _)])
    (fun x => mem_collapse_bdry.symm)
    (fun x _ => by
      change G.colour x = G.collapseColour ∅ x
      simp [collapseColour])
    (fun i => rfl)

end PlabicData

/-! ### Local moves and isomorphisms -/

/-- A bijection intertwining two permutations intertwines their powers. -/
private theorem pow_apply_of_semiconj'' {X Y : Type*} {π : Equiv.Perm X} {π' : Equiv.Perm Y}
    (θ : X ≃ Y) (h : ∀ x, θ (π x) = π' (θ x)) (n : ℕ) (x : X) :
    θ ((π ^ n) x) = (π' ^ n) (θ x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, ih]

/-- A bijection intertwining two permutations carries first returns to first returns. -/
private theorem coe_firstReturn_of_semiconj'' {X Y : Type*} [Finite X] [Finite Y]
    {π : Equiv.Perm X} {π' : Equiv.Perm Y} (θ : X ≃ Y) (h : ∀ x, θ (π x) = π' (θ x))
    {S : Set X} {S' : Set Y} (hS : ∀ x, θ x ∈ S' ↔ x ∈ S) (y : S) :
    θ (firstReturn π S y) = firstReturn π' S' ⟨θ y, (hS y).2 y.2⟩ := by
  rw [coe_firstReturn π S y, pow_apply_of_semiconj'' θ h]
  symm
  refine coe_firstReturn_of_pow (y := ⟨θ y, (hS y).2 y.2⟩) (firstReturnTime_pos y) ?_ ?_
  · change (π' ^ _) (θ y) ∈ S'
    rw [← pow_apply_of_semiconj'' θ h, hS]
    exact pow_firstReturnTime_apply_mem y
  · intro j hj hjm
    change (π' ^ j) (θ y) ∉ S'
    rw [← pow_apply_of_semiconj'' θ h, hS]
    exact pow_apply_notMem_of_lt_firstReturnTime hj hjm

namespace PlabicData

section IsoMoves

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {G : PlabicData H b} {G' : PlabicData H' b}

/-- An isomorphism maps a removable bivalent vertex to a removable bivalent vertex. -/
theorem Iso.isBivalentRemovable (θ : G.Iso G') {d : H} (hd : G.IsBivalentRemovable d) :
    G'.IsBivalentRemovable (θ.toEquiv d) where
  not_isBoundaryVertex := by
    rw [θ.isBoundaryVertex_vertexOf_iff]
    exact hd.not_isBoundaryVertex
  card_vertexOf := by
    rw [θ.card_vertexOf]
    exact hd.card_vertexOf
  inv_ne_rot := by
    rw [← θ.map_inv, ← θ.map_rot]
    exact θ.toEquiv.injective.ne hd.inv_ne_rot

/-- An isomorphism maps a contractible edge to a contractible edge. -/
theorem Iso.isContractibleEdge (θ : G.Iso G') {d : H} (he : G.IsContractibleEdge d) :
    G'.IsContractibleEdge (θ.toEquiv d) where
  vertexOf_ne := by
    rw [← θ.map_inv, Ne, θ.vertexOf_eq_vertexOf_iff]
    exact he.vertexOf_ne
  mem_internalVertices := by
    rw [θ.vertexOf_mem_internalVertices_iff]
    exact he.mem_internalVertices
  inv_mem_internalVertices := by
    rw [← θ.map_inv, θ.vertexOf_mem_internalVertices_iff]
    exact he.inv_mem_internalVertices
  colour_inv := by
    rw [← θ.map_inv, θ.map_colour _ he.not_isBoundaryVertex_inv,
      θ.map_colour _ he.not_isBoundaryVertex]
    exact he.colour_inv

/-- An isomorphism `θ : G → G'` restricts to an isomorphism from the removal of a bivalent vertex
`{d, σ d}` of `G` to the removal of `{θ d, σ' (θ d)}` from `G'`. -/
noncomputable def Iso.bivalentRemoval (θ : G.Iso G') (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d) :
    (G.bivalentRemoval hG hd).Iso (G'.bivalentRemoval hG' (θ.isBivalentRemovable hd)) :=
  have hmem : ∀ x, x ∈ ({d, G.rot d}ᶜ : Set H) ↔
      θ.toEquiv x ∈ ({θ.toEquiv d, G'.rot (θ.toEquiv d)}ᶜ : Set H') := fun x => by
    rw [← θ.map_rot]
    simp [θ.toEquiv.injective.eq_iff]
  Iso.ofEquivOfMapLeg (θ.toEquiv.subtypeEquiv hmem)
    (fun x => by
      apply Subtype.ext
      change θ.toEquiv ((Equiv.swap d (G.inv (G.rot d)) * Equiv.swap (G.rot d) (G.inv d) *
          G.inv) x) = (Equiv.swap (θ.toEquiv d) (G'.inv (G'.rot (θ.toEquiv d))) *
          Equiv.swap (G'.rot (θ.toEquiv d)) (G'.inv (θ.toEquiv d)) * G'.inv) (θ.toEquiv x)
      simp only [Equiv.Perm.mul_apply, θ.toEquiv.injective.map_swap, θ.map_inv, θ.map_rot])
    (fun x => Subtype.ext (θ.map_rot x))
    (fun x => by
      simp only [mem_bivalentRemoval_bdry, Equiv.subtypeEquiv_apply]
      exact θ.mem_bdry_iff x)
    (fun x hx => by
      have hx' : ¬G.IsBoundaryVertex (G.vertexOf x) :=
        (not_congr (isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd x)).1 hx
      exact θ.map_colour _ hx')
    (fun i => Subtype.ext (θ.map_leg hG hG' i))

/-- An isomorphism `θ : G → G'` restricts to an isomorphism from the contraction of `G` along
`{d, d̄}` to the contraction of `G'` along `{θ d, θ d̄}`. -/
noncomputable def Iso.contractEdge (θ : G.Iso G') (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) {d : H} (he : G.IsContractibleEdge d) :
    (G.contractEdge d (he.leg_mem hG)).Iso
      (G'.contractEdge (θ.toEquiv d) ((θ.isContractibleEdge he).leg_mem hG')) :=
  have hmem : ∀ x, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) ↔
      θ.toEquiv x ∈ (({θ.toEquiv d, G'.inv (θ.toEquiv d)} : Set H')ᶜ : Set H') := fun x => by
    rw [← θ.map_inv]
    simp [θ.toEquiv.injective.eq_iff]
  Iso.ofEquivOfMapLeg (θ.toEquiv.subtypeEquiv hmem)
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.subtypeEquiv_apply]
      rw [coe_contractEdge_inv hG.inv_involutive, coe_contractEdge_inv hG'.inv_involutive]
      exact θ.map_inv x)
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.subtypeEquiv_apply, contractEdge_rot, coe_inducedRotationPerm,
        inducedRotation]
      refine (coe_firstReturn_of_semiconj'' θ.toEquiv (fun y => ?_) (fun y => (hmem y).symm)
        x).trans rfl
      simp only [Equiv.Perm.mul_apply, θ.toEquiv.injective.map_swap, θ.map_inv, θ.map_rot])
    (fun x => by
      simp only [mem_contractEdge_bdry, Equiv.subtypeEquiv_apply]
      exact θ.mem_bdry_iff x)
    (fun x hx => by
      have hx' : ¬G.IsBoundaryVertex (G.vertexOf x) :=
        (not_congr (isBoundaryVertex_vertexOf_contractEdge_iff he)).1 hx
      exact θ.map_colour _ hx')
    (fun i => Subtype.ext (θ.map_leg hG hG' i))

end IsoMoves

end PlabicData

/-! ### Transporting collapsing families along isomorphisms -/

namespace PlabicData

section TransportIso

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {G : PlabicData H b} {G' : PlabicData H' b}

namespace Iso

variable (θ : G.Iso G')

/-- The map of sets of darts induced by an isomorphism. -/
abbrev mapFinset : Finset H ↪ Finset H' := θ.toEquiv.finsetCongr.toEmbedding

/-- `θ.mapFinset s` is the image of `s` under `θ`. -/
theorem mapFinset_apply (s : Finset H) : θ.mapFinset s = s.map θ.toEquiv.toEmbedding := rfl

/-- An isomorphism maps the vertex of a dart `d` to the vertex of `θ d`. -/
theorem mapFinset_vertexOf (d : H) : θ.mapFinset (G.vertexOf d) = G'.vertexOf (θ.toEquiv d) :=
  θ.map_vertexOf d

/-- The image of a set of darts under an isomorphism is a boundary vertex if and only if the set
is. -/
theorem isBoundaryVertex_mapFinset_iff (s : Finset H) :
    G'.IsBoundaryVertex (θ.mapFinset s) ↔ G.IsBoundaryVertex s := by
  simp only [mapFinset_apply, DiskMap.IsBoundaryVertex, mem_map_equiv]
  constructor
  · rintro ⟨e, he, heB⟩
    exact ⟨_, he, by rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply]⟩
  · rintro ⟨e, he, heB⟩
    exact ⟨θ.toEquiv e, by rwa [Equiv.symm_apply_apply], (θ.mem_bdry_iff e).2 heB⟩

/-- `θ x` is a tree dart of the image of a set `W` of vertices if and only if `x` is a tree dart
of `W`. -/
theorem mem_treeDarts_iff (W : Finset (Finset H)) (x : H) :
    θ.toEquiv x ∈ G'.treeDarts (W.map θ.mapFinset) ↔ x ∈ G.treeDarts W := by
  rw [mem_treeDarts, mem_treeDarts, ← θ.map_inv, ← θ.mapFinset_vertexOf, ← θ.mapFinset_vertexOf,
    mem_map', mem_map', θ.mem_bdry_iff]

/-- An isomorphism maps the tree darts of a set `W` of vertices to the tree darts of the image
of `W`. -/
theorem map_treeDarts (W : Finset (Finset H)) :
    (G.treeDarts W).map θ.toEquiv.toEmbedding = G'.treeDarts (W.map θ.mapFinset) := by
  ext y
  obtain ⟨x, rfl⟩ := θ.toEquiv.surjective y
  rw [mem_map_equiv, Equiv.symm_apply_apply, θ.mem_treeDarts_iff]

/-- An isomorphism maps the edge of a dart `d` to the edge of `θ d`. -/
theorem mapFinset_edgeOf (d : H) : θ.mapFinset (G.edgeOf d) = G'.edgeOf (θ.toEquiv d) := by
  simp [mapFinset_apply, RotationSystem.edgeOf, θ.map_inv]

/-- An isomorphism commutes with every power of the rotation. -/
theorem map_rot_pow (n : ℕ) (d : H) :
    θ.toEquiv ((G.rot ^ n) d) = (G'.rot ^ n) (θ.toEquiv d) :=
  pow_apply_of_semiconj'' θ.toEquiv θ.map_rot n d

/-- An isomorphism commutes with the inverse of the rotation. -/
theorem rot_symm_apply (d : H) : G'.rot.symm (θ.toEquiv d) = θ.toEquiv (G.rot.symm d) := by
  apply G'.rot.injective
  rw [Equiv.apply_symm_apply, ← θ.map_rot, Equiv.apply_symm_apply]

end Iso

/-- The image `θ(T)` of a rooted tree `T` under an isomorphism `θ`. -/
noncomputable def RootedTree.map (θ : G.Iso G') (T : G.RootedTree) : G'.RootedTree where
  root := θ.mapFinset T.root
  nonRoot := T.nonRoot.map θ.mapFinset
  root_mem_vertices := by
    rw [T.root_eq_vertexOf_intervalStart, θ.mapFinset_vertexOf]
    exact G'.vertexOf_mem_vertices _
  nonRoot_nonempty := T.nonRoot_nonempty.map
  nonRoot_subset := by
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := mem_map.1 hw'
    obtain ⟨a, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 (T.nonRoot_subset hw)).1
    rw [θ.mapFinset_vertexOf, θ.vertexOf_mem_internalVertices_iff]
    exact T.nonRoot_subset hw
  root_notMem_nonRoot := by
    rw [mem_map']
    exact T.root_notMem_nonRoot
  vertexOf_inv_mem := by
    intro d' hd'
    obtain ⟨d, rfl⟩ := θ.toEquiv.surjective d'
    rw [← θ.mapFinset_vertexOf, mem_map'] at hd'
    rw [← θ.map_inv, ← θ.mapFinset_vertexOf, ← map_insert, mem_map']
    exact T.vertexOf_inv_mem d hd'
  exists_interval := by
    refine ⟨θ.toEquiv T.intervalStart, ?_, T.intervalLength, T.one_le_intervalLength, ?_, ?_, ?_⟩
    · exact mem_map_of_mem _ T.intervalStart_mem_root
    · rw [Iso.mapFinset_apply, card_map]
      exact T.intervalLength_lt_card
    · intro d' hd'
      obtain ⟨d, rfl⟩ := θ.toEquiv.surjective d'
      have hd : d ∈ T.root := by
        rw [Iso.mapFinset_apply] at hd'
        exact (mem_map' _).1 hd'
      rw [θ.mem_treeDarts_iff, T.mem_darts_iff_of_mem_root hd]
      simp only [← θ.map_rot_pow, θ.toEquiv.injective.eq_iff]
    · rw [θ.rot_symm_apply, θ.mem_treeDarts_iff]
      exact T.rot_symm_intervalStart_notMem
  card_image_edgeOf := by
    rw [← θ.map_treeDarts, map_eq_image, image_image]
    have : G'.edgeOf ∘ θ.toEquiv.toEmbedding = θ.mapFinset ∘ G.edgeOf :=
      funext fun d => (θ.mapFinset_edgeOf d).symm
    rw [this, ← image_image, card_image_of_injective _ θ.mapFinset.injective,
      T.card_image_edgeOf, card_map]
  reflTransGen_treeAdj := by
    intro u' hu'
    rw [← map_insert] at hu'
    obtain ⟨u, hu, rfl⟩ := mem_map.1 hu'
    refine Relation.ReflTransGen.lift θ.mapFinset (fun u₁ u₂ h => ?_) (T.reflTransGen_treeAdj u hu)
    obtain ⟨d, hd, h1, h2⟩ := h
    exact ⟨θ.toEquiv d, (θ.mem_treeDarts_iff _ d).2 hd, by rw [← θ.mapFinset_vertexOf, h1],
      by rw [← θ.map_inv, ← θ.mapFinset_vertexOf, h2]⟩

namespace RootedTree

variable (θ : G.Iso G') (T : G.RootedTree)

/-- The root of `θ(T)` is the image of the root of `T`. -/
theorem map_root : (T.map θ).root = θ.mapFinset T.root := rfl

/-- The non-root vertices of `θ(T)` are the images of the non-root vertices of `T`. -/
theorem map_nonRoot : (T.map θ).nonRoot = T.nonRoot.map θ.mapFinset := rfl

/-- `θ x` is a dart of `θ(T)` if and only if `x` is a dart of `T`. -/
theorem mem_map_darts_iff (x : H) : θ.toEquiv x ∈ (T.map θ).darts ↔ x ∈ T.darts :=
  θ.mem_treeDarts_iff _ x

/-- The darts of `θ(T)` are the images of the darts of `T`. -/
theorem map_darts : (T.map θ).darts = T.darts.map θ.toEquiv.toEmbedding :=
  (θ.map_treeDarts _).symm

/-- The root of `θ(T)` is a boundary vertex if and only if the root of `T` is. -/
theorem isBoundaryVertex_map_root_iff :
    G'.IsBoundaryVertex (T.map θ).root ↔ G.IsBoundaryVertex T.root :=
  θ.isBoundaryVertex_mapFinset_iff _

/-- The start of the interval of `θ(T)` is the image of the start of the interval of `T`. -/
theorem map_intervalStart : (T.map θ).intervalStart = θ.toEquiv T.intervalStart := by
  refine ((T.map θ).eq_intervalStart_of_rot_symm_notMem ?_ ?_ ?_).symm
  · exact (T.mem_map_darts_iff θ _).2 T.intervalStart_mem_darts
  · exact mem_map_of_mem _ T.intervalStart_mem_root
  · rw [θ.rot_symm_apply, T.mem_map_darts_iff θ]
    exact T.rot_symm_intervalStart_notMem

/-- The plabic graph of a rooted tree is isomorphic to the plabic graph of its image under an
isomorphism. -/
noncomputable def plabicDataIsoMap (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    T.plabicData.Iso (T.map θ).plabicData :=
  have hb := T.isBoundaryVertex_map_root_iff θ
  have hmem : ∀ x, T.IsDart x ↔ (T.map θ).IsDart (Equiv.sumCongr θ.toEquiv (Equiv.refl _) x) := by
    rintro (d | (_ | _ | _ | _))
    · exact (T.mem_map_darts_iff θ d).symm
    · exact Iff.rfl
    · exact Iff.rfl
    · exact not_congr hb.symm
    · exact not_congr hb.symm
  have hstart := T.map_intervalStart θ
  Iso.ofEquivOfMapLeg ((Equiv.sumCongr θ.toEquiv (Equiv.refl _)).subtypeEquiv hmem)
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.subtypeEquiv_apply]
      rw [T.coe_inv_plabicData hG, (T.map θ).coe_inv_plabicData hG']
      rcases x with ⟨d | l, hx⟩
      · simp [θ.map_inv]
      · rfl)
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.subtypeEquiv_apply]
      rw [T.coe_rot_plabicData hG, (T.map θ).coe_rot_plabicData hG']
      rcases x with ⟨d | (_ | _ | _ | _), hx⟩
      · have e1 : G'.rot (θ.toEquiv d) ∈ (T.map θ).darts ↔ G.rot d ∈ T.darts := by
          rw [← θ.map_rot, T.mem_map_darts_iff θ]
        by_cases h1 : G.rot d ∈ T.darts
        · have h1' := e1.2 h1
          simp [rotAux, h1, h1', θ.map_rot]
        · have h1' := mt e1.1 h1
          by_cases h2 : G.IsBoundaryVertex T.root
          · have h2' := hb.2 h2
            simp [rotAux, h1, h1', h2, h2']
          · have h2' := mt hb.1 h2
            simp [rotAux, h1, h1', h2, h2']
      · simp only [rotAux, Equiv.sumCongr_apply, Sum.map_inr, Equiv.coe_refl, hb,
          hstart]
        split_ifs <;> rfl
      · rfl
      · rfl
      · simp only [rotAux, Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, Equiv.coe_refl, hstart,
          id])
    (fun x => by
      rw [mem_bdry_plabicData, mem_bdry_plabicData]
      rcases x with ⟨d | (_ | _ | _ | _), hx⟩ <;>
        simp [dartE, dartEBar, Subtype.ext_iff])
    (fun x hx => by
      have hroot : ¬G.IsBoundaryVertex T.root → G'.colour (θ.toEquiv T.intervalStart) =
          G.colour T.intervalStart := fun h =>
        θ.map_colour _ (by rwa [← T.root_eq_vertexOf_intervalStart])
      rw [T.isBoundaryVertex_vertexOf_iff hG, T.vertexOf_dartE hG] at hx
      change (T.map θ).colourAux _ = T.colourAux x.1
      rcases x with ⟨d | (_ | _ | _ | _), hxd⟩
      · simp only [colourAux, Equiv.subtypeEquiv_apply, Equiv.sumCongr_apply, Sum.map_inl]
        refine θ.map_colour d fun hd => hx ?_
        have hdr : G.vertexOf d = T.root := by
          rcases T.vertexOf_mem_or_eq_root hG hxd with h | h
          · exact absurd hd (G.mem_internalVertices.1 (T.nonRoot_subset h)).2
          · exact h
        have hdb : G.IsBoundaryVertex T.root := hdr ▸ hd
        have := T.eq_intervalStart_of_isBoundaryVertex hG hdb hxd hdr
        subst this
        simp [legDart, hdb]
      · exact absurd (by simp [dartE]) hx
      · exact absurd (by simp [dartEBar]) hx
      · simp only [colourAux, Equiv.subtypeEquiv_apply, Equiv.sumCongr_apply, Sum.map_inr,
          hstart]
        exact hroot hxd
      · simp only [colourAux, Equiv.subtypeEquiv_apply, Equiv.sumCongr_apply, Sum.map_inr,
          hstart]
        exact hroot hxd)
    (fun i => by
      apply Subtype.ext
      simp only [Equiv.subtypeEquiv_apply]
      change Equiv.sumCongr θ.toEquiv (Equiv.refl _) (T.legDart : H ⊕ LollipopDart) =
        ((T.map θ).legDart : H' ⊕ LollipopDart)
      by_cases h : G.IsBoundaryVertex T.root
      · have h' := hb.2 h
        simp [legDart, h, h', hstart]
      · have h' := mt hb.1 h
        simp [legDart, h, h'])

/-- The image of a collapsible tree of colour `c` under an isomorphism is a collapsible tree of
colour `c`. -/
theorem IsCollapsibleOfColour.map (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) {c : Shade}
    (h : T.IsCollapsibleOfColour c) : (T.map θ).IsCollapsibleOfColour c where
  isPlabicGraph := (T.map θ).isPlabicGraph_plabicData hG'
  moveEquivalent :=
    (PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
      (G := ⟨_, (T.map θ).plabicData, (T.map θ).isPlabicGraph_plabicData hG'⟩)
      (G' := ⟨_, T.plabicData, h.isPlabicGraph⟩) ⟨T.plabicDataIsoMap θ hG hG'⟩).trans
      h.moveEquivalent
  root_cases := by
    rcases h.root_cases with ⟨hb, hc⟩ | ⟨hb, h2⟩
    · refine Or.inl ⟨mt (T.isBoundaryVertex_map_root_iff θ).1 hb, fun d' hd' => ?_⟩
      obtain ⟨d, hd, rfl⟩ := mem_map.1 hd'
      have hdr : G.vertexOf d = T.root := T.mem_root_iff.1 hd
      rw [Equiv.coe_toEmbedding, θ.map_colour d (hdr ▸ hb)]
      exact hc d hd
    · refine Or.inr ⟨(T.isBoundaryVertex_map_root_iff θ).2 hb, ?_⟩
      rw [map_nonRoot, card_map]
      exact h2

end RootedTree

open scoped Classical in
/-- The image of a family of trees under an isomorphism. -/
noncomputable def Iso.mapFamily (θ : G.Iso G') (𝒯 : Finset (G.RootedTree × Shade)) :
    Finset (G'.RootedTree × Shade) :=
  𝒯.image fun p => (p.1.map θ, p.2)

/-- A pair lies in the image of `𝒯` if and only if it is the image of a pair of `𝒯`. -/
theorem Iso.mem_mapFamily {θ : G.Iso G'} {𝒯 : Finset (G.RootedTree × Shade)}
    {p' : G'.RootedTree × Shade} : p' ∈ θ.mapFamily 𝒯 ↔ ∃ p ∈ 𝒯, (p.1.map θ, p.2) = p' := by
  classical
  unfold mapFamily
  convert mem_image

variable {𝒯 : Finset (G.RootedTree × Shade)}

/-- The image of a collapsing family under an isomorphism is a collapsing family. -/
theorem IsCollapsingFamily.mapFamily (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (θ : G.Iso G') (h𝒯 : G.IsCollapsingFamily 𝒯) : G'.IsCollapsingFamily (θ.mapFamily 𝒯) where
  isCollapsibleOfColour p' hp' := by
    obtain ⟨p, hp, rfl⟩ := Iso.mem_mapFamily.1 hp'
    exact (h𝒯.isCollapsibleOfColour p hp).map θ p.1 hG hG'
  disjoint_nonRoot p' hp' q' hq' hne := by
    obtain ⟨p, hp, rfl⟩ := Iso.mem_mapFamily.1 hp'
    obtain ⟨q, hq, rfl⟩ := Iso.mem_mapFamily.1 hq'
    have hpq : p ≠ q := fun h => hne (h ▸ rfl)
    rw [RootedTree.map_nonRoot, RootedTree.map_nonRoot, disjoint_map]
    exact h𝒯.disjoint_nonRoot p hp q hq hpq
  root_notMem_nonRoot p' hp' q' hq' hne := by
    obtain ⟨p, hp, rfl⟩ := Iso.mem_mapFamily.1 hp'
    obtain ⟨q, hq, rfl⟩ := Iso.mem_mapFamily.1 hq'
    have hpq : p ≠ q := fun h => hne (h ▸ rfl)
    rw [RootedTree.map_nonRoot, RootedTree.map_root, mem_map']
    exact h𝒯.root_notMem_nonRoot p hp q hq hpq
  exists_mem_root p' hp' := by
    obtain ⟨p, hp, rfl⟩ := Iso.mem_mapFamily.1 hp'
    obtain ⟨d, hd, hdq⟩ := h𝒯.exists_mem_root p hp
    refine ⟨θ.toEquiv d, mem_map_of_mem _ hd, fun q' hq' => ?_⟩
    obtain ⟨q, hq, rfl⟩ := Iso.mem_mapFamily.1 hq'
    rw [RootedTree.mem_map_darts_iff]
    exact hdq q hq

/-- `θ x` is a dart of a tree of the image of `𝒯` if and only if `x` is a dart of a tree of
`𝒯`. -/
theorem Iso.mem_familyDarts_mapFamily_iff (θ : G.Iso G') (x : H) :
    θ.toEquiv x ∈ G'.familyDarts (θ.mapFamily 𝒯) ↔ x ∈ G.familyDarts 𝒯 := by
  rw [mem_familyDarts, mem_familyDarts]
  constructor
  · rintro ⟨p', hp', hx⟩
    obtain ⟨p, hp, rfl⟩ := Iso.mem_mapFamily.1 hp'
    exact ⟨p, hp, (p.1.mem_map_darts_iff θ x).1 hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨_, Iso.mem_mapFamily.2 ⟨p, hp, rfl⟩, (p.1.mem_map_darts_iff θ x).2 hx⟩

/-- `θ x` lies in the core of the collapse along the image of `𝒯` if and only if `x` lies in the
core of the collapse along `𝒯`. -/
theorem Iso.mem_collapseCore_mapFamily_iff (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (θ : G.Iso G') (x : H) :
    θ.toEquiv x ∈ G'.collapseCore (θ.mapFamily 𝒯) ↔ x ∈ G.collapseCore 𝒯 := by
  simp only [collapseCore, Set.mem_setOf_eq, θ.mem_familyDarts_mapFamily_iff, ← θ.map_leg hG hG',
    θ.toEquiv.injective.eq_iff]

/-- `θ x` is a dart of the collapse along the image of `𝒯` if and only if `x` is a dart of the
collapse along `𝒯`. -/
theorem Iso.mem_collapseDarts_mapFamily_iff (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (θ : G.Iso G') (x : H) :
    θ.toEquiv x ∈ G'.collapseDarts (θ.mapFamily 𝒯) ↔ x ∈ G.collapseDarts 𝒯 := by
  unfold collapseDarts
  simp only [Set.mem_setOf_eq, θ.mem_collapseCore_mapFamily_iff hG hG', ← θ.map_leg hG hG',
    θ.mem_familyDarts_mapFamily_iff, ← θ.map_inv, θ.toEquiv.injective.eq_iff]

/-- The colour of `ḡ_i` in a collapse is the colour of the member whose tree contains `g_i`. -/
theorem IsCollapsingFamily.collapseColour_inv_leg (hG : G.IsPlabicGraph)
    (h𝒯 : G.IsCollapsingFamily 𝒯) {p : G.RootedTree × Shade} (hp : p ∈ 𝒯) {i : Fin b}
    (hi : G.leg i ∈ p.1.darts) : G.collapseColour 𝒯 (G.inv (G.leg i)) = p.2 := by
  have hex : ∃ q ∈ 𝒯, ∃ j, G.leg j ∈ q.1.darts ∧ G.inv (G.leg i) = G.inv (G.leg j) :=
    ⟨p, hp, i, hi, rfl⟩
  classical
  rw [collapseColour, dif_pos hex]
  obtain ⟨hq, j, hj, hij⟩ := hex.choose_spec
  have hij' : i = j := hG.leg_injective (G.inv.injective hij)
  subst hij'
  by_contra hne
  have hne' : hex.choose ≠ p := fun h => hne (h ▸ rfl)
  exact disjoint_left.1 (hex.choose.1.disjoint_darts hG (h𝒯.disjoint_nonRoot _ hq _ hp hne')
    (h𝒯.root_notMem_nonRoot _ hp _ hq hne'.symm)) hj hi

/-- The colour in the collapse `G/𝒯` of a dart of the collapse core is its colour in `G`. -/
theorem collapseColour_of_mem_collapseCore (hG : G.IsPlabicGraph) {x : H}
    (hx : x ∈ G.collapseCore 𝒯) : G.collapseColour 𝒯 x = G.colour x := by
  classical
  rw [collapseColour, dif_neg]
  rintro ⟨p, hp, i, hi, rfl⟩
  exact inv_leg_notMem_collapseCore hG (mem_familyDarts.2 ⟨p, hp, hi⟩) hx

/-- **Collapses of isomorphic graphs.** An isomorphism `θ : G → G'` is an isomorphism from the
collapse `G/𝒯` to the collapse `G'/θ(𝒯)`. -/
noncomputable def Iso.collapse (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (θ : G.Iso G')
    (h𝒯 : G.IsCollapsingFamily 𝒯) : (G.collapse 𝒯).Iso (G'.collapse (θ.mapFamily 𝒯)) :=
  have hC := θ.mem_collapseDarts_mapFamily_iff (𝒯 := 𝒯) hG hG'
  have hK := θ.mem_collapseCore_mapFamily_iff (𝒯 := 𝒯) hG hG'
  have h𝒯' := h𝒯.mapFamily hG hG' θ
  Iso.ofEquivOfMapLeg (θ.toEquiv.subtypeEquiv fun x => (hC x).symm)
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.subtypeEquiv_apply]
      rw [coe_collapse_inv hG, coe_collapse_inv hG', θ.map_inv])
    (fun x => by
      apply Subtype.ext
      simp only [Equiv.subtypeEquiv_apply]
      by_cases hx : (x : H) ∈ G.collapseCore 𝒯
      · rw [coe_collapse_rot_of_mem hx, coe_collapse_rot_of_mem (x := ⟨θ.toEquiv x, _⟩)
          ((hK x).2 hx)]
        exact coe_firstReturn_of_semiconj'' θ.toEquiv θ.map_rot hK ⟨x, hx⟩
      · rw [coe_collapse_rot_of_notMem hx, coe_collapse_rot_of_notMem (x := ⟨θ.toEquiv x, _⟩)
          (mt (hK x).1 hx)])
    (fun x => by
      simp only [mem_collapse_bdry, Equiv.subtypeEquiv_apply]
      exact θ.mem_bdry_iff x)
    (fun x hx => by
      change G'.collapseColour (θ.mapFamily 𝒯) (θ.toEquiv x) = G.collapseColour 𝒯 x
      by_cases hxK : (x : H) ∈ G.collapseCore 𝒯
      · rw [collapseColour_of_mem_collapseCore hG' ((hK x).2 hxK),
          collapseColour_of_mem_collapseCore hG hxK]
        refine θ.map_colour _ fun ⟨y, hy, hyB⟩ => hx ?_
        have hyK : y ∈ G.collapseCore 𝒯 := mem_collapseCore_of_mem_bdry hyB
        have : y ∈ ((G.collapse 𝒯).vertexOf x).map (Function.Embedding.subtype _) := by
          rw [map_collapse_vertexOf_of_mem hxK, mem_filter]
          exact ⟨hy, hyK⟩
        obtain ⟨y', hy', rfl⟩ := mem_map.1 this
        exact ⟨y', hy', mem_collapse_bdry.2 hyB⟩
      · rcases x.2 with hx' | ⟨i, hi, hxi⟩
        · exact absurd hx' hxK
        obtain ⟨p, hp, hip⟩ := mem_familyDarts.1 hi
        rw [hxi, h𝒯.collapseColour_inv_leg hG hp hip, θ.map_inv, θ.map_leg hG hG',
          h𝒯'.collapseColour_inv_leg hG' (Iso.mem_mapFamily.2 ⟨p, hp, rfl⟩)
            (by rwa [← θ.map_leg hG hG', RootedTree.mem_map_darts_iff])])
    (fun i => Subtype.ext (θ.map_leg hG hG' i))

end TransportIso

end PlabicData

/-! ### Square moves and collapsing families -/

namespace PlabicData

section SquareCollapse

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

private theorem squareCorner_notMem_bdry {c : H} (hq : G.IsSquareMoveFace c) (k : Fin 4) :
    G.squareCorner c k ∉ G.bdry := by
  have hmem : G.squareCorner c k ∈ G.faceOf c :=
    G.mem_faceOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
  exact disjoint_left.1 (G.mem_internalFaces.1 hq.faceOf_mem_internalFaces).2 hmem

private theorem vertexOf_inv_squareCorner {c : H} (hq : G.IsSquareMoveFace c) (k : Fin 4) :
    G.vertexOf (G.inv (G.squareCorner c k)) = G.vertexOf (G.squareCorner c (k + 1)) := by
  rw [← hq.facePerm_squareCorner, RotationSystem.facePerm_apply,
    G.vertexOf_rot]

/-- The vertices of a square face lie in no set `W` of a rooted tree: the four edges of the face
would form a cycle in the tree. -/
private theorem RootedTree.vertexOf_squareCorner_notMem_nonRoot (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {c : H} (hq : G.IsSquareMoveFace c) (k : Fin 4) :
    G.vertexOf (G.squareCorner c k) ∉ T.nonRoot := by
  intro hk
  have hinv := hG.inv_involutive
  set v : Fin 4 → Finset H := fun j => G.vertexOf (G.squareCorner c j) with hvdef
  have hv' := vertexOf_inv_squareCorner hq
  have hinj : Function.Injective v := hq.injective
  have hS1 : ∀ j, v j ∈ T.nonRoot → v (j + 1) ∈ insert T.root T.nonRoot := fun j h => by
    have := T.vertexOf_inv_mem _ h
    rwa [hv'] at this
  have hS2 : ∀ j, v j ∈ T.nonRoot → v (j - 1) ∈ insert T.root T.nonRoot := fun j h => by
    have h' : G.vertexOf (G.inv (G.squareCorner c (j - 1))) ∈ T.nonRoot := by
      rwa [hv', sub_add_cancel]
    have := T.vertexOf_inv_mem _ h'
    rwa [hinv] at this
  have hroot : ∀ j l, v j = T.root → v l = T.root → j = l := fun j l h1 h2 =>
    hinj (h1.trans h2.symm)
  have hall : ∀ j, v j ∈ insert T.root T.nonRoot := by
    have h1 := hS1 k hk
    have h2 := hS2 k hk
    have h3 : v (k + 2) ∈ insert T.root T.nonRoot := by
      rcases mem_insert.1 h1 with h1 | h1
      · rcases mem_insert.1 h2 with h2 | h2
        · exact absurd (hroot _ _ h1 h2) (by fin_cases k <;> decide)
        · have := hS2 _ h2
          rwa [show k - 1 - 1 = k + 2 by fin_cases k <;> decide] at this
      · have := hS1 _ h1
        rwa [show k + 1 + 1 = k + 2 by fin_cases k <;> decide] at this
    intro j
    have : j = k ∨ j = k + 1 ∨ j = k + 2 ∨ j = k - 1 := by
      fin_cases j <;> fin_cases k <;> decide
    rcases this with rfl | rfl | rfl | rfl
    · exact mem_insert_of_mem hk
    · exact h1
    · exact h3
    · exact h2
  have hdarts : ∀ j, G.squareCorner c j ∈ T.darts := by
    intro j
    refine G.mem_treeDarts.2 ⟨squareCorner_notMem_bdry hq j, ?_⟩
    rw [hv']
    rcases mem_insert.1 (hall j) with h | h
    · rcases mem_insert.1 (hall (j + 1)) with h' | h'
      · exact absurd (hroot _ _ h h') (by fin_cases j <;> decide)
      · exact Or.inr h'
    · exact Or.inl h
  have hcard : ∀ j, G.rot (G.squareCorner c j) ≠ G.squareCorner c j := fun j h => by
    have := G.card_vertexOf_le_two (d := G.squareCorner c j) (by rw [h, h])
    rw [hq.card_vertexOf j] at this
    omega
  have hne : ∀ j l, j ≠ l → G.squareCorner c j ≠ G.squareCorner c l := fun j l h h' =>
    h (hinj (by simp only [hvdef, h']))
  refine T.not_reflTransGen_of_mem_darts hG (hdarts 0) ?_
  have hstep : ∀ j : Fin 4, j ≠ 0 → (fun u u' => ∃ e ∈ T.darts, e ≠ G.squareCorner c 0 ∧
      e ≠ G.inv (G.squareCorner c 0) ∧ G.vertexOf e = u ∧ G.vertexOf (G.inv e) = u')
        (v (j + 1)) (v j) := by
    intro j hj
    refine ⟨G.inv (G.squareCorner c j), T.inv_mem_darts hG (hdarts j), fun h => ?_,
      fun h => hne j 0 hj (hinv.injective h), hv' j, by rw [hinv]⟩
    by_cases hj3 : j = 3
    · subst hj3
      have h1 := hq.facePerm_squareCorner 3
      rw [RotationSystem.facePerm_apply, h, show (3 : Fin 4) + 1 = 0 from rfl] at h1
      exact hcard 0 h1
    · have := congrArg G.vertexOf h
      rw [hv'] at this
      have h01 : ∀ j : Fin 4, j ≠ 0 → j ≠ 3 → j + 1 ≠ 0 := by decide
      exact h01 j hj hj3 (hinj this)
  rw [hv' 0]
  exact ((Relation.ReflTransGen.single (hstep 3 (by decide))).tail (hstep 2 (by decide))).tail
    (hstep 1 (by decide))

/-- The darts of a square face, and the darts across them, lie in no tree of a family. -/
private theorem squareCorner_mem_collapseCore (hG : G.IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)} {c : H} (hq : G.IsSquareMoveFace c) (k : Fin 4) :
    G.squareCorner c k ∈ G.collapseCore 𝒯 ∧ G.inv (G.squareCorner c k) ∈ G.collapseCore 𝒯 := by
  have hinv := hG.inv_involutive
  have hnot : G.squareCorner c k ∉ G.familyDarts 𝒯 := fun h => by
    obtain ⟨p, -, hp⟩ := mem_familyDarts.1 h
    rcases p.1.vertexOf_mem_or_eq_root hG hp with h' | h'
    · exact p.1.vertexOf_squareCorner_notMem_nonRoot hG hq k h'
    · have := p.1.vertexOf_inv_mem_nonRoot_of_mem_root hp (p.1.mem_root_iff.2 h')
      rw [vertexOf_inv_squareCorner hq] at this
      exact p.1.vertexOf_squareCorner_notMem_nonRoot hG hq _ this
  refine ⟨Or.inl hnot, Or.inl fun h => hnot ?_⟩
  have := inv_mem_familyDarts hG h
  rwa [hinv] at this

end SquareCollapse

section SquareCollapseFace

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  {𝒯 : Finset (G.RootedTree × Shade)} (hG : G.IsPlabicGraph) {c : H} (hq : G.IsSquareMoveFace c)

/-- The corner `c_{k+1}` of a square face, as a dart of a collapse. -/
private def collapseCorner (k : Fin 4) : G.collapseDarts 𝒯 :=
  ⟨G.squareCorner c k, G.collapseCore_subset 𝒯 (squareCorner_mem_collapseCore hG hq k).1⟩

include hG hq

private theorem facePerm_collapseCorner (k : Fin 4) :
    (G.collapse 𝒯).facePerm (collapseCorner (𝒯 := 𝒯) hG hq k) = collapseCorner hG hq (k + 1) := by
  apply Subtype.ext
  obtain ⟨-, hik⟩ := squareCorner_mem_collapseCore (𝒯 := 𝒯) hG hq k
  obtain ⟨hk1, -⟩ := squareCorner_mem_collapseCore (𝒯 := 𝒯) hG hq (k + 1)
  have hiy : (((G.collapse 𝒯).inv (collapseCorner hG hq k) : G.collapseDarts 𝒯) : H) =
      G.inv (G.squareCorner c k) := coe_collapse_inv hG _
  rw [RotationSystem.facePerm_apply, coe_collapse_rot_of_mem (hiy ▸ hik)]
  simp only [hiy]
  have hrot : G.rot (G.inv (G.squareCorner c k)) = G.squareCorner c (k + 1) := by
    rw [← RotationSystem.facePerm_apply, hq.facePerm_squareCorner]
  rw [coe_firstReturn_of_apply_mem (by rwa [hrot]), hrot]
  rfl

private theorem facePerm_pow_collapseCorner (n : ℕ) :
    ((G.collapse 𝒯).facePerm ^ n) (collapseCorner (𝒯 := 𝒯) hG hq 0) =
      collapseCorner hG hq ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, facePerm_collapseCorner]
    congr 1
    ext
    simp only [Fin.val_add]
    omega

private theorem squareCorner_collapse (k : Fin 4) :
    (G.collapse 𝒯).squareCorner (collapseCorner (𝒯 := 𝒯) hG hq 0) k =
      collapseCorner hG hq k := by
  rw [squareCorner, facePerm_pow_collapseCorner]
  congr 1
  ext
  simp only
  omega

private theorem map_vertexOf_collapseCorner (k : Fin 4) :
    ((G.collapse 𝒯).vertexOf (collapseCorner (𝒯 := 𝒯) hG hq k)).map
      (Function.Embedding.subtype _) =
      (G.vertexOf (G.squareCorner c k)).filter (· ∈ G.collapseCore 𝒯) :=
  map_collapse_vertexOf_of_mem (squareCorner_mem_collapseCore hG hq k).1

private theorem mem_vertexOf_collapseCorner_iff (k : Fin 4) {y : G.collapseDarts 𝒯} :
    y ∈ (G.collapse 𝒯).vertexOf (collapseCorner (𝒯 := 𝒯) hG hq k) ↔
      (y : H) ∈ G.vertexOf (G.squareCorner c k) ∧ (y : H) ∈ G.collapseCore 𝒯 := by
  rw [← mem_filter, ← map_vertexOf_collapseCorner hG hq k]
  exact (mem_map' (Function.Embedding.subtype _)).symm

private theorem collapse_vertexOf_collapseCorner_injective :
    Function.Injective fun k => (G.collapse 𝒯).vertexOf (collapseCorner (𝒯 := 𝒯) hG hq k) := by
  intro k l h
  have hk : collapseCorner (𝒯 := 𝒯) hG hq k ∈
      (G.collapse 𝒯).vertexOf (collapseCorner (𝒯 := 𝒯) hG hq l) := by
    simp only at h
    rw [← h]
    exact (G.collapse 𝒯).self_mem_vertexOf _
  have := ((mem_vertexOf_collapseCorner_iff hG hq l).1 hk).1
  exact hq.injective (G.vertexOf_eq_of_mem this)

private theorem not_isBoundaryVertex_collapse_collapseCorner (k : Fin 4) :
    ¬(G.collapse 𝒯).IsBoundaryVertex
      ((G.collapse 𝒯).vertexOf (collapseCorner (𝒯 := 𝒯) hG hq k)) := by
  rintro ⟨y, hy, hyB⟩
  have hint := G.mem_internalVertices.1 (hq.vertexOf_mem_internalVertices k)
  exact hint.2 ⟨y, ((mem_vertexOf_collapseCorner_iff hG hq k).1 hy).1, mem_collapse_bdry.1 hyB⟩

omit hG in
private theorem rot_squareCorner_ne (k : Fin 4) : G.rot (G.squareCorner c k) ≠ G.squareCorner c k :=
  fun h => by
    have := G.card_vertexOf_le_two (d := G.squareCorner c k) (by rw [h, h])
    rw [hq.card_vertexOf k] at this
    omega

private theorem two_le_card_collapse_collapseCorner (k : Fin 4) :
    2 ≤ ((G.collapse 𝒯).vertexOf (collapseCorner (𝒯 := 𝒯) hG hq k)).card := by
  rw [← card_map (Function.Embedding.subtype _), map_vertexOf_collapseCorner hG hq k]
  obtain ⟨-, hi⟩ := squareCorner_mem_collapseCore (𝒯 := 𝒯) hG hq (k - 1)
  obtain ⟨hk, -⟩ := squareCorner_mem_collapseCore (𝒯 := 𝒯) hG hq k
  have hrot : G.rot (G.inv (G.squareCorner c (k - 1))) = G.squareCorner c k := by
    rw [← RotationSystem.facePerm_apply, hq.facePerm_squareCorner,
      sub_add_cancel]
  have hne : G.inv (G.squareCorner c (k - 1)) ≠ G.squareCorner c k := fun h => by
    rw [h] at hrot
    exact rot_squareCorner_ne hq k hrot
  have hmem : G.inv (G.squareCorner c (k - 1)) ∈ G.vertexOf (G.squareCorner c k) := by
    rw [← hrot, G.vertexOf_rot]
    exact G.self_mem_vertexOf _
  refine one_lt_card.2 ⟨_, mem_filter.2 ⟨G.self_mem_vertexOf _, hk⟩, _,
    mem_filter.2 ⟨hmem, hi⟩, hne.symm⟩

private theorem collapse_faceOf_collapseCorner_mem_internalFaces :
    (G.collapse 𝒯).faceOf (collapseCorner (𝒯 := 𝒯) hG hq 0) ∈ (G.collapse 𝒯).internalFaces := by
  have hB : ∀ k, collapseCorner (𝒯 := 𝒯) hG hq k ∉ (G.collapse 𝒯).bdry := fun k h =>
    squareCorner_notMem_bdry hq k (mem_collapse_bdry.1 h)
  refine (G.collapse 𝒯).mem_internalFaces.2 ⟨(G.collapse 𝒯).mem_faces.2 ⟨fun h => ?_,
    (G.collapse 𝒯).faceOf_mem_faceOrbits _⟩, disjoint_left.2 fun y hy hyB => ?_⟩
  · have := h ▸ (G.collapse 𝒯).self_mem_faceOf (collapseCorner (𝒯 := 𝒯) hG hq 0)
    exact hB 0 ((G.collapse 𝒯).exterior_subset_bdry this)
  · obtain ⟨n, rfl⟩ := ((G.collapse 𝒯).mem_faceOf.1 hy).exists_nat_pow_eq
    rw [facePerm_pow_collapseCorner] at hyB
    exact hB _ hyB

private theorem collapse_colour_collapseCorner (k : Fin 4) :
    (G.collapse 𝒯).colour (collapseCorner (𝒯 := 𝒯) hG hq k) = G.colour (G.squareCorner c k) :=
  collapseColour_of_mem_collapseCore hG (squareCorner_mem_collapseCore hG hq k).1

/-- If the root of a tree of `𝒯` is the vertex of the corner `c_{k+1}`, that corner is at most
bivalent in the collapse. -/
private theorem card_vertexOf_collapseCorner_le_two_of_root {p : G.RootedTree × Shade}
    (hp : p ∈ 𝒯) {k : Fin 4} (hpk : p.1.root = G.vertexOf (G.squareCorner c k)) :
    ((G.collapse 𝒯).vertexOf (collapseCorner (𝒯 := 𝒯) hG hq k)).card ≤ 2 := by
  rw [← card_map (Function.Embedding.subtype _), map_vertexOf_collapseCorner hG hq k]
  have hlt : ((G.vertexOf (G.squareCorner c k)).filter (· ∈ G.collapseCore 𝒯)).card <
      (G.vertexOf (G.squareCorner c k)).card := by
    refine card_lt_card (filter_ssubset.2 ⟨p.1.intervalStart, ?_, ?_⟩)
    · rw [← hpk]
      exact p.1.intervalStart_mem_root
    · rintro (h | ⟨i, hi⟩)
      · exact h (mem_familyDarts.2 ⟨p, hp, p.1.intervalStart_mem_darts⟩)
      · have : G.IsBoundaryVertex (G.vertexOf (G.squareCorner c k)) := by
          rw [← hpk, p.1.root_eq_vertexOf_intervalStart, hi]
          exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
        exact (G.mem_internalVertices.1 (hq.vertexOf_mem_internalVertices k)).2 this
  rw [hq.card_vertexOf k] at hlt
  omega

/-- A dart of the core lies at a vertex of the square in the collapse if and only if it does
so in `G`. -/
private theorem mem_squareVertices_collapse_iff {y : G.collapseDarts 𝒯}
    (hy : (y : H) ∈ G.collapseCore 𝒯) :
    (G.collapse 𝒯).vertexOf y ∈
        (G.collapse 𝒯).squareVertices (collapseCorner (𝒯 := 𝒯) hG hq 0) ↔
      G.vertexOf y ∈ G.squareVertices c := by
  rw [mem_squareVertices, mem_squareVertices]
  refine exists_congr fun k => ?_
  rw [squareCorner_collapse hG hq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : y ∈ (G.collapse 𝒯).vertexOf (collapseCorner hG hq k) :=
      h ▸ (G.collapse 𝒯).self_mem_vertexOf y
    exact (G.vertexOf_eq_of_mem ((mem_vertexOf_collapseCorner_iff hG hq k).1 this).1).symm
  · exact ((G.collapse 𝒯).vertexOf_eq_of_mem
      ((mem_vertexOf_collapseCorner_iff hG hq k).2 ⟨h ▸ G.self_mem_vertexOf _, hy⟩)).symm

end SquareCollapseFace

section SquareTransport

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- A rooted tree of `G` is a rooted tree of the square move of `G` at the face through `c`: the
square move does not change the rotation system. -/
def RootedTree.toSquareMove (T : G.RootedTree) (c : H) : (G.squareMove c).RootedTree where
  root := T.root
  nonRoot := T.nonRoot
  root_mem_vertices := T.root_mem_vertices
  nonRoot_nonempty := T.nonRoot_nonempty
  nonRoot_subset := T.nonRoot_subset
  root_notMem_nonRoot := T.root_notMem_nonRoot
  vertexOf_inv_mem := T.vertexOf_inv_mem
  exists_interval := T.exists_interval
  card_image_edgeOf := T.card_image_edgeOf
  reflTransGen_treeAdj := T.reflTransGen_treeAdj

namespace RootedTree

variable (T : G.RootedTree) (c : H)

/-- The darts of `T`, read in the square move, are the darts of `T`. -/
@[simp]
theorem toSquareMove_darts : (T.toSquareMove c).darts = T.darts := rfl

/-- The start of the interval of `T`, read in the square move, is that of `T`. -/
@[simp]
theorem toSquareMove_intervalStart : (T.toSquareMove c).intervalStart = T.intervalStart := rfl

/-- If the square move recolours no dart of `T`, then `P_T` is unchanged. -/
noncomputable def plabicDataIsoToSquareMove
    (hc : ∀ d ∈ T.darts, (G.squareMove c).colour d = G.colour d) :
    T.plabicData.Iso (T.toSquareMove c).plabicData :=
  Iso.ofEquivOfMapLeg (Equiv.subtypeEquivRight fun _ => Iff.rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => Iff.rfl)
    (fun x _ => by
      change (T.toSquareMove c).colourAux x.1 = T.colourAux x.1
      rcases x with ⟨d | _, hx⟩
      · exact hc d hx
      · exact hc _ T.intervalStart_mem_darts)
    (fun _ => rfl)

/-- A collapsible tree none of whose darts or root is recoloured by the square move is a
collapsible tree of the square move. -/
theorem IsCollapsibleOfColour.toSquareMove (hG : G.IsPlabicGraph) {T : G.RootedTree} {c' : H}
    {s : Shade} (h : T.IsCollapsibleOfColour s)
    (hroot : T.root ∉ G.squareVertices c') (hW : ∀ w ∈ T.nonRoot, w ∉ G.squareVertices c') :
    (T.toSquareMove c').IsCollapsibleOfColour s where
  isPlabicGraph := (T.toSquareMove c').isPlabicGraph_plabicData (hG.squareMove c')
  moveEquivalent :=
    (PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
      (G := ⟨_, (T.toSquareMove c').plabicData,
        (T.toSquareMove c').isPlabicGraph_plabicData (hG.squareMove c')⟩)
      (G' := ⟨_, T.plabicData, h.isPlabicGraph⟩) ⟨T.plabicDataIsoToSquareMove c' fun d hd =>
        colour_squareMove_of_notMem _ (by
          rcases T.vertexOf_mem_or_eq_root hG hd with h' | h'
          · exact hW _ h'
          · rwa [h'])⟩).trans h.moveEquivalent
  root_cases := by
    rcases h.root_cases with ⟨hb, hcol⟩ | ⟨hb, h2⟩
    · refine Or.inl ⟨hb, fun d hd => ?_⟩
      rw [colour_squareMove_of_notMem _ (by rwa [T.mem_root_iff.1 hd])]
      exact hcol d hd
    · exact Or.inr ⟨hb, h2⟩

end RootedTree

end SquareTransport

section SquareFamily

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  {𝒯 : Finset (G.RootedTree × Shade)}

open scoped Classical in
/-- The family `𝒯`, read in the square move of `G` at the face through `c`. -/
noncomputable def toSquareMoveFamily (𝒯 : Finset (G.RootedTree × Shade)) (c : H) :
    Finset ((G.squareMove c).RootedTree × Shade) :=
  𝒯.image fun p => (p.1.toSquareMove c, p.2)

/-- A pair lies in `toSquareMoveFamily 𝒯 c` if and only if it is a pair of `𝒯` read in the
square move. -/
theorem mem_toSquareMoveFamily {c : H} {p' : (G.squareMove c).RootedTree × Shade} :
    p' ∈ toSquareMoveFamily 𝒯 c ↔ ∃ p ∈ 𝒯, (p.1.toSquareMove c, p.2) = p' := by
  classical
  unfold toSquareMoveFamily
  convert mem_image

/-- A collapsing family none of whose roots or non-root vertices is a vertex of the square at `c`
is a collapsing family of the square move at `c`. -/
theorem IsCollapsingFamily.toSquareMove (hG : G.IsPlabicGraph) (h𝒯 : G.IsCollapsingFamily 𝒯)
    {c : H} (hroot : ∀ p ∈ 𝒯, p.1.root ∉ G.squareVertices c)
    (hW : ∀ p ∈ 𝒯, ∀ w ∈ p.1.nonRoot, w ∉ G.squareVertices c) :
    (G.squareMove c).IsCollapsingFamily (toSquareMoveFamily 𝒯 c) where
  isCollapsibleOfColour p' hp' := by
    obtain ⟨p, hp, rfl⟩ := mem_toSquareMoveFamily.1 hp'
    exact (h𝒯.isCollapsibleOfColour p hp).toSquareMove hG (hroot p hp) (hW p hp)
  disjoint_nonRoot p' hp' q' hq' hne := by
    obtain ⟨p, hp, rfl⟩ := mem_toSquareMoveFamily.1 hp'
    obtain ⟨q, hq, rfl⟩ := mem_toSquareMoveFamily.1 hq'
    exact h𝒯.disjoint_nonRoot p hp q hq fun h => hne (h ▸ rfl)
  root_notMem_nonRoot p' hp' q' hq' hne := by
    obtain ⟨p, hp, rfl⟩ := mem_toSquareMoveFamily.1 hp'
    obtain ⟨q, hq, rfl⟩ := mem_toSquareMoveFamily.1 hq'
    exact h𝒯.root_notMem_nonRoot p hp q hq fun h => hne (h ▸ rfl)
  exists_mem_root p' hp' := by
    obtain ⟨p, hp, rfl⟩ := mem_toSquareMoveFamily.1 hp'
    obtain ⟨d, hd, hdq⟩ := h𝒯.exists_mem_root p hp
    refine ⟨d, hd, fun q' hq' => ?_⟩
    obtain ⟨q, hq, rfl⟩ := mem_toSquareMoveFamily.1 hq'
    exact hdq q hq

/-- A dart lies in the family darts of `toSquareMoveFamily 𝒯 c` iff it lies in those of `𝒯`. -/
theorem mem_familyDarts_toSquareMoveFamily_iff {c x : H} :
    x ∈ (G.squareMove c).familyDarts (toSquareMoveFamily 𝒯 c) ↔ x ∈ G.familyDarts 𝒯 := by
  rw [mem_familyDarts, mem_familyDarts]
  constructor
  · rintro ⟨p', hp', hx⟩
    obtain ⟨p, hp, rfl⟩ := mem_toSquareMoveFamily.1 hp'
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨_, mem_toSquareMoveFamily.2 ⟨p, hp, rfl⟩, hx⟩

/-- A dart lies in the collapse core of the square move along `toSquareMoveFamily 𝒯 c` iff it lies
in the collapse core along `𝒯`. -/
theorem mem_collapseCore_toSquareMoveFamily_iff {c x : H} :
    x ∈ (G.squareMove c).collapseCore (toSquareMoveFamily 𝒯 c) ↔ x ∈ G.collapseCore 𝒯 := by
  simp only [collapseCore, Set.mem_setOf_eq, mem_familyDarts_toSquareMoveFamily_iff,
    leg_squareMove]

/-- A dart lies in the collapse of the square move along `toSquareMoveFamily 𝒯 c` iff it lies in
the collapse along `𝒯`. -/
theorem mem_collapseDarts_toSquareMoveFamily_iff {c x : H} :
    x ∈ (G.squareMove c).collapseDarts (toSquareMoveFamily 𝒯 c) ↔ x ∈ G.collapseDarts 𝒯 := by
  unfold collapseDarts
  simp only [Set.mem_setOf_eq, mem_collapseCore_toSquareMoveFamily_iff,
    mem_familyDarts_toSquareMoveFamily_iff, leg_squareMove, inv_squareMove]

end SquareFamily

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- A local move from `A` to `B` is a local move from any graph isomorphic to `A`. -/
theorem IsLocalMove.of_isomorphic_left {t : LocalMoveType} {A A' B : PlabicGraph b}
    (h : IsLocalMove t A B) (hA : A'.Isomorphic A) : IsLocalMove t A' B := by
  obtain ⟨θ⟩ := hA
  cases t with
  | m1 =>
    obtain ⟨c, hq, hB⟩ := h
    exact ⟨θ.symm.toEquiv c, θ.symm.isSquareMoveFace hq,
      PlabicData.Isomorphic.trans _ hB ⟨θ.symm.squareMove c⟩⟩
  | m2 =>
    rcases h with ⟨d, hd, hB⟩ | ⟨d, hd, hA⟩
    · exact Or.inl ⟨θ.symm.toEquiv d, θ.symm.isBivalentRemovable hd,
        PlabicData.Isomorphic.trans _ hB
          ⟨θ.symm.bivalentRemoval A.isPlabicGraph A'.isPlabicGraph hd⟩⟩
    · exact Or.inr ⟨d, hd, PlabicData.Isomorphic.trans _ ⟨θ⟩ hA⟩
  | m3 =>
    rcases h with ⟨d, he, hB⟩ | ⟨d, he, hA⟩
    · exact Or.inl ⟨θ.symm.toEquiv d, θ.symm.isContractibleEdge he,
        PlabicData.Isomorphic.trans _ hB ⟨θ.symm.contractEdge A.isPlabicGraph A'.isPlabicGraph he⟩⟩
    · exact Or.inr ⟨d, he, PlabicData.Isomorphic.trans _ ⟨θ⟩ hA⟩

/-- A local move from `A` to `B` is a local move to any graph isomorphic to `B`. -/
theorem IsLocalMove.of_isomorphic_right {t : LocalMoveType} {A B B' : PlabicGraph b}
    (h : IsLocalMove t A B) (hB : B'.Isomorphic B) : IsLocalMove t A B' := by
  obtain ⟨θ⟩ := hB
  cases t with
  | m1 =>
    obtain ⟨c, hq, hB⟩ := h
    exact ⟨c, hq, PlabicData.Isomorphic.trans _ ⟨θ⟩ hB⟩
  | m2 =>
    rcases h with ⟨d, hd, hB⟩ | ⟨d, hd, hA⟩
    · exact Or.inl ⟨d, hd, PlabicData.Isomorphic.trans _ ⟨θ⟩ hB⟩
    · exact Or.inr ⟨θ.symm.toEquiv d, θ.symm.isBivalentRemovable hd,
        PlabicData.Isomorphic.trans _ hA
          ⟨θ.symm.bivalentRemoval B.isPlabicGraph B'.isPlabicGraph hd⟩⟩
  | m3 =>
    rcases h with ⟨d, he, hB⟩ | ⟨d, he, hA⟩
    · exact Or.inl ⟨d, he, PlabicData.Isomorphic.trans _ ⟨θ⟩ hB⟩
    · exact Or.inr ⟨θ.symm.toEquiv d, θ.symm.isContractibleEdge he,
        PlabicData.Isomorphic.trans _ hA ⟨θ.symm.contractEdge B.isPlabicGraph B'.isPlabicGraph he⟩⟩

/-- A step of an `S`-equivalence between `A` and `B` is a step between any graphs isomorphic to
`A` and `B`. -/
theorem MoveStep.of_isomorphic {S : Set LocalMoveType} {A A' B B' : PlabicGraph b}
    (h : MoveStep S A B) (hA : A'.Isomorphic A) (hB : B'.Isomorphic B) : MoveStep S A' B' := by
  rcases h with h | ⟨t, ht, h⟩
  · exact Or.inl (PlabicData.Isomorphic.trans _ hB (PlabicData.Isomorphic.trans _ h hA.symm))
  · exact Or.inr ⟨t, ht, (h.of_isomorphic_left hA).of_isomorphic_right hB⟩

end PlabicGraph

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- The collapse `K/𝒯` of a collapsing family `𝒯` of a plabic graph `K`, as a plabic graph. -/
noncomputable def collapse (K : PlabicGraph b) {𝒯 : Finset (K.data.RootedTree × Shade)}
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) : PlabicGraph b :=
  ⟨K.data.collapseDarts 𝒯, K.data.collapse 𝒯, (h𝒯.moveEquivalent_collapse K.isPlabicGraph).1⟩

/-- The underlying data of the collapse `K/𝒯` is the collapse of the data of `K`. -/
@[simp]
theorem collapse_data (K : PlabicGraph b) {𝒯 : Finset (K.data.RootedTree × Shade)}
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) : (K.collapse h𝒯).data = K.data.collapse 𝒯 :=
  rfl

/-- A plabic graph is `{M2, M3}`-equivalent to its collapse. -/
theorem moveEquivalent_collapse (K : PlabicGraph b) {𝒯 : Finset (K.data.RootedTree × Shade)}
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) : MoveEquivalent {.m2, .m3} K (K.collapse h𝒯) :=
  (h𝒯.moveEquivalent_collapse K.isPlabicGraph).2

/-- The collapse of the empty family is isomorphic to the graph. -/
theorem collapse_empty_isomorphic (K : PlabicGraph b) :
    (K.collapse (isCollapsingFamily_empty (G := K.data))).Isomorphic K :=
  ⟨collapseEmptyIso K.isPlabicGraph⟩

/-- For a collapsing family `𝒯` of `K` and a plabic graph `K'`: `K'` has a collapsing family `𝒯'`
such that `K'/𝒯'` is nearly leafless and is isomorphic to `K/𝒯` or obtained from `K/𝒯` by a local
move, or `K/𝒯` is nearly leafless equivalent to a plabic graph containing a hollow digon. -/
def CollapseStep (K K' : PlabicGraph b) {𝒯 : Finset (K.data.RootedTree × Shade)}
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) : Prop :=
  (∃ (𝒯' : Finset (K'.data.RootedTree × Shade)) (h𝒯' : K'.data.IsCollapsingFamily 𝒯'),
      (K'.data.collapse 𝒯').IsNearlyLeafless ∧
        MoveStep Set.univ (K.collapse h𝒯) (K'.collapse h𝒯')) ∨
    ∃ X : PlabicGraph b, NearlyLeaflessEquivalent (K.collapse h𝒯) X ∧ ∃ f, X.data.IsHollowDigon f

/-- For plabic graphs with `b` boundary vertices: every collapsing family `𝒯` of a plabic graph
`K` with `K/𝒯` nearly leafless, and every plabic graph `K'` isomorphic to `K` or obtained from `K`
by a local move, satisfy `CollapseStep`. -/
def HasCollapseSteps (b : ℕ) : Prop :=
  ∀ (K K' : PlabicGraph b) (𝒯 : Finset (K.data.RootedTree × Shade))
    (h𝒯 : K.data.IsCollapsingFamily 𝒯), (K.data.collapse 𝒯).IsNearlyLeafless →
      MoveStep Set.univ K K' → CollapseStep K K' h𝒯

/-! ### Reducing `HasCollapseSteps` to the constructions of the local moves -/

/-- The removal of a bivalent vertex `{d, σ d}` of a plabic graph, as a plabic graph. -/
def bivalentRemoval (K : PlabicGraph b) {d : K.Dart} (hd : K.data.IsBivalentRemovable d) :
    PlabicGraph b :=
  ⟨_, K.data.bivalentRemoval K.isPlabicGraph hd, isPlabicGraph_bivalentRemoval K.isPlabicGraph hd⟩

/-- `K'` is obtained from `K` by one of the five constructions of the local moves, on the darts of
the construction: `K'` is the square move, the removal of a bivalent vertex or the contraction of
an edge of `K`, or `K` is the removal of a bivalent vertex or the contraction of an edge of `K'`.
Every local move is one of these up to isomorphisms on both sides. -/
inductive IsLiteralMove : PlabicGraph b → PlabicGraph b → Prop
  /-- A square move. -/
  | squareMove (K : PlabicGraph b) {c : K.Dart} (hq : K.data.IsSquareMoveFace c) :
      IsLiteralMove K (K.squareMove c)
  /-- The removal of a bivalent vertex. -/
  | bivalentRemoval (K : PlabicGraph b) {d : K.Dart} (hd : K.data.IsBivalentRemovable d) :
      IsLiteralMove K (K.bivalentRemoval hd)
  /-- The insertion of a bivalent vertex. -/
  | bivalentInsertion (K : PlabicGraph b) {d : K.Dart} (hd : K.data.IsBivalentRemovable d) :
      IsLiteralMove (K.bivalentRemoval hd) K
  /-- The contraction of an edge. -/
  | contractEdge (K : PlabicGraph b) {d : K.Dart} (he : K.data.IsContractibleEdge d) :
      IsLiteralMove K (K.contractEdge he)
  /-- The splitting of a vertex. -/
  | splitVertex (K : PlabicGraph b) {d : K.Dart} (he : K.data.IsContractibleEdge d) :
      IsLiteralMove (K.contractEdge he) K

/-- A collapsing family of a plabic graph is carried by an isomorphism to a collapsing family with
an isomorphic collapse. -/
theorem exists_collapse_isomorphic {K K₁ : PlabicGraph b} (θ : K.data.Iso K₁.data)
    {𝒯 : Finset (K.data.RootedTree × Shade)} (h𝒯 : K.data.IsCollapsingFamily 𝒯) :
    ∃ (𝒯₁ : Finset (K₁.data.RootedTree × Shade)) (h𝒯₁ : K₁.data.IsCollapsingFamily 𝒯₁),
      (K.collapse h𝒯).Isomorphic (K₁.collapse h𝒯₁) :=
  ⟨θ.mapFamily 𝒯, h𝒯.mapFamily K.isPlabicGraph K₁.isPlabicGraph θ,
    ⟨θ.collapse K.isPlabicGraph K₁.isPlabicGraph h𝒯⟩⟩

/-- `CollapseStep` passes to a graph isomorphic to the target. -/
theorem CollapseStep.of_isomorphic_right {K K₁ K' : PlabicGraph b}
    {𝒯 : Finset (K.data.RootedTree × Shade)} {h𝒯 : K.data.IsCollapsingFamily 𝒯}
    (h : CollapseStep K K₁ h𝒯) (hK' : K'.Isomorphic K₁) : CollapseStep K K' h𝒯 := by
  rcases h with ⟨𝒯₁, h𝒯₁, hnl, hst⟩ | h
  · obtain ⟨θ⟩ := hK'
    obtain ⟨𝒯', h𝒯', ⟨θc⟩⟩ := exists_collapse_isomorphic θ.symm h𝒯₁
    exact Or.inl ⟨𝒯', h𝒯', θc.isNearlyLeafless (K₁.collapse h𝒯₁).isPlabicGraph
      (K'.collapse h𝒯').isPlabicGraph hnl,
      hst.of_isomorphic (PlabicData.Isomorphic.refl _) ⟨θc.symm⟩⟩
  · exact Or.inr h

/-- `CollapseStep` passes from a graph isomorphic to the source. -/
theorem CollapseStep.of_isomorphic_left {K K₀ K' : PlabicGraph b} (θ : K.data.Iso K₀.data)
    {𝒯 : Finset (K.data.RootedTree × Shade)} (h𝒯 : K.data.IsCollapsingFamily 𝒯)
    (hnl : (K.data.collapse 𝒯).IsNearlyLeafless)
    (h : ∀ (𝒯₀ : Finset (K₀.data.RootedTree × Shade)) (h𝒯₀ : K₀.data.IsCollapsingFamily 𝒯₀),
      (K₀.data.collapse 𝒯₀).IsNearlyLeafless → CollapseStep K₀ K' h𝒯₀) :
    CollapseStep K K' h𝒯 := by
  obtain ⟨𝒯₀, h𝒯₀, ⟨θc⟩⟩ := exists_collapse_isomorphic θ h𝒯
  have hnl₀ := θc.isNearlyLeafless (K.collapse h𝒯).isPlabicGraph (K₀.collapse h𝒯₀).isPlabicGraph
    hnl
  rcases h 𝒯₀ h𝒯₀ hnl₀ with ⟨𝒯', h𝒯', hnl', hst⟩ | ⟨X, hX, hXd⟩
  · exact Or.inl ⟨𝒯', h𝒯', hnl', hst.of_isomorphic ⟨θc⟩ (PlabicData.Isomorphic.refl _)⟩
  · exact Or.inr ⟨X, ⟨hnl, Relation.ReflTransGen.head ⟨hnl₀, Or.inl ⟨θc.symm⟩⟩ hX.2⟩, hXd⟩

/-- **Reduction of `HasCollapseSteps` to the constructions.** If `CollapseStep` holds for
every collapsing family with a nearly leafless collapse and every literal local move
(`IsLiteralMove`), then it holds for every step of a move equivalence: isomorphisms carry
collapsing families and their collapses, and a local move is a literal one up to isomorphisms. -/
theorem hasCollapseSteps_of_isLiteralMove
    (h : ∀ (K K' : PlabicGraph b) (𝒯 : Finset (K.data.RootedTree × Shade))
      (h𝒯 : K.data.IsCollapsingFamily 𝒯), (K.data.collapse 𝒯).IsNearlyLeafless →
        IsLiteralMove K K' → CollapseStep K K' h𝒯) :
    HasCollapseSteps b := by
  intro K K' 𝒯 h𝒯 hnl hst
  rcases hst with hiso | ⟨t, -, ht⟩
  · obtain ⟨θ⟩ : K'.data.Isomorphic K.data := hiso
    obtain ⟨𝒯', h𝒯', ⟨θc⟩⟩ := exists_collapse_isomorphic θ.symm h𝒯
    exact Or.inl ⟨𝒯', h𝒯', θc.isNearlyLeafless (K.collapse h𝒯).isPlabicGraph
      (K'.collapse h𝒯').isPlabicGraph hnl, Or.inl ⟨θc.symm⟩⟩
  cases t with
  | m1 =>
    obtain ⟨c, hq, hB⟩ := ht
    exact (h K (K.squareMove c) 𝒯 h𝒯 hnl (.squareMove K hq)).of_isomorphic_right hB
  | m2 =>
    rcases ht with ⟨d, hd, hB⟩ | ⟨d, hd, hA⟩
    · exact (h K _ 𝒯 h𝒯 hnl (.bivalentRemoval K hd)).of_isomorphic_right hB
    · obtain ⟨θ⟩ := hA
      exact CollapseStep.of_isomorphic_left (K₀ := K'.bivalentRemoval hd) θ h𝒯 hnl
        fun 𝒯₀ h𝒯₀ hnl₀ => h _ K' 𝒯₀ h𝒯₀ hnl₀ (.bivalentInsertion K' hd)
  | m3 =>
    rcases ht with ⟨d, he, hB⟩ | ⟨d, he, hA⟩
    · exact (h K _ 𝒯 h𝒯 hnl (.contractEdge K he)).of_isomorphic_right hB
    · obtain ⟨θ⟩ := hA
      exact CollapseStep.of_isomorphic_left (K₀ := K'.contractEdge he) θ h𝒯 hnl
        fun 𝒯₀ h𝒯₀ hnl₀ => h _ K' 𝒯₀ h𝒯₀ hnl₀ (.splitVertex K' he)

private noncomputable def collapseSquareMoveIso (K : PlabicGraph b)
    {𝒯 : Finset (K.data.RootedTree × Shade)} (h𝒯 : K.data.IsCollapsingFamily 𝒯) {c : K.Dart}
    (hq : K.data.IsSquareMoveFace c)
    (h𝒯' : (K.data.squareMove c).IsCollapsingFamily (toSquareMoveFamily 𝒯 c)) :
    ((K.data.squareMove c).collapse (toSquareMoveFamily 𝒯 c)).Iso
      ((K.data.collapse 𝒯).squareMove (collapseCorner (𝒯 := 𝒯) K.isPlabicGraph hq 0)) := by
  have hG := K.isPlabicGraph
  set x : Fin 4 → K.data.collapseDarts 𝒯 := fun k => collapseCorner hG hq k with hxdef
  have hcorner : ∀ k, (K.data.collapse 𝒯).squareCorner (x 0) k = x k := squareCorner_collapse hG hq
  have hmemSV : ∀ y : K.data.collapseDarts 𝒯, (y : K.Dart) ∈ K.data.collapseCore 𝒯 →
      ((K.data.collapse 𝒯).vertexOf y ∈ (K.data.collapse 𝒯).squareVertices (x 0) ↔
        K.data.vertexOf y ∈ K.data.squareVertices c) :=
    fun _ hy => mem_squareVertices_collapse_iff hG hq hy
  have hC : ∀ z : K.Dart, z ∈ (K.data.squareMove c).collapseDarts (toSquareMoveFamily 𝒯 c) ↔
      z ∈ K.data.collapseDarts 𝒯 := fun z => mem_collapseDarts_toSquareMoveFamily_iff
  have hK : ∀ z : K.Dart, z ∈ (K.data.squareMove c).collapseCore (toSquareMoveFamily 𝒯 c) ↔
      z ∈ K.data.collapseCore 𝒯 := fun z => mem_collapseCore_toSquareMoveFamily_iff
  have hGs : (K.data.squareMove c).IsPlabicGraph := hG.squareMove c
  exact Iso.ofEquivOfMapLeg (Equiv.subtypeEquivRight hC)
    (fun y => by
      apply Subtype.ext
      change (((K.data.squareMove c).collapse (toSquareMoveFamily 𝒯 c)).inv y : K.Dart) =
        ((K.data.collapse 𝒯).inv ⟨y, (hC y).1 y.2⟩ : K.Dart)
      rw [coe_collapse_inv hGs, coe_collapse_inv hG]
      rfl)
    (fun y => by
      apply Subtype.ext
      change (((K.data.squareMove c).collapse (toSquareMoveFamily 𝒯 c)).rot y : K.Dart) =
        ((K.data.collapse 𝒯).rot ⟨y, (hC y).1 y.2⟩ : K.Dart)
      by_cases hy : (y : K.Dart) ∈ K.data.collapseCore 𝒯
      · rw [coe_collapse_rot_of_mem ((hK y).2 hy), coe_collapse_rot_of_mem (G := K.data) (𝒯 := 𝒯)
          (x := ⟨(y : K.Dart), (hC y).1 y.2⟩) hy]
        exact coe_firstReturn_of_semiconj'' (π := (K.data.squareMove c).rot) (π' := K.data.rot)
          (Equiv.refl K.Dart) (fun _ => rfl) (fun z => (hK z).symm) ⟨y, (hK y).2 hy⟩
      · rw [coe_collapse_rot_of_notMem (mt (hK y).1 hy),
          coe_collapse_rot_of_notMem (G := K.data) (𝒯 := 𝒯)
            (x := ⟨(y : K.Dart), (hC y).1 y.2⟩) hy])
    (fun y => by
      change (⟨y, (hC y).1 y.2⟩ : K.data.collapseDarts 𝒯) ∈ (K.data.collapse 𝒯).bdry ↔
        y ∈ ((K.data.squareMove c).collapse (toSquareMoveFamily 𝒯 c)).bdry
      rw [mem_collapse_bdry, mem_collapse_bdry]
      rfl)
    (fun y _ => by
      set y' : K.data.collapseDarts 𝒯 := ⟨y, (hC y).1 y.2⟩ with hy'
      change ((K.data.collapse 𝒯).squareMove (x 0)).colour y' =
        (K.data.squareMove c).collapseColour (toSquareMoveFamily 𝒯 c) y
      by_cases hyK : (y : K.Dart) ∈ K.data.collapseCore 𝒯
      · rw [collapseColour_of_mem_collapseCore hGs ((hK y).2 hyK), colour_squareMove,
          colour_squareMove]
        change (if _ then (K.data.collapseColour 𝒯 y).swap else K.data.collapseColour 𝒯 y) = _
        rw [collapseColour_of_mem_collapseCore hG hyK]
        simp only [hmemSV y' hyK]
        rfl
      · rcases ((hC y).1 y.2) with hy0 | ⟨i, hi, hyi⟩
        · exact absurd hy0 hyK
        obtain ⟨p, hp, hip⟩ := mem_familyDarts.1 hi
        rw [show (y : K.Dart) = (K.data.squareMove c).inv ((K.data.squareMove c).leg i) from hyi,
          h𝒯'.collapseColour_inv_leg hGs (mem_toSquareMoveFamily.2 ⟨p, hp, rfl⟩) hip,
          colour_squareMove_of_notMem]
        · change K.data.collapseColour 𝒯 y = p.2
          rw [hyi]
          exact h𝒯.collapseColour_inv_leg hG hp hip
        · rw [collapse_vertexOf_inv_leg hG hi hyi]
          intro h
          obtain ⟨k, hk⟩ := mem_squareVertices.1 h
          rw [hcorner] at hk
          have : x k ∈ ({y'} : Finset _) := hk ▸ (K.data.collapse 𝒯).self_mem_vertexOf (x k)
          have hxk : (x k : K.Dart) = y := congrArg Subtype.val (mem_singleton.1 this)
          exact hyK (hxk ▸ (squareCorner_mem_collapseCore hG hq k).1))
    (fun i => rfl)

/-- **`CollapseStep` for square moves**. Let `𝒯` be a collapsing family of `K` with `K/𝒯` nearly
leafless and `q` a face of `K` satisfying the conditions of a square move. If no vertex of `q` is a
root, `𝒯` is a collapsing family of the square move `K'` of `K` at `q`, and `K'/𝒯` is the square
move of `K/𝒯` at `q`; otherwise `q` is a square of `K/𝒯` with a bivalent corner, and `K/𝒯` is
nearly leafless equivalent to a graph with a hollow digon. -/
theorem collapseStep_squareMove (K : PlabicGraph b) {𝒯 : Finset (K.data.RootedTree × Shade)}
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) (hnl : (K.data.collapse 𝒯).IsNearlyLeafless)
    {c : K.Dart} (hq : K.data.IsSquareMoveFace c) : CollapseStep K (K.squareMove c) h𝒯 := by
  have hG := K.isPlabicGraph
  set x : Fin 4 → K.data.collapseDarts 𝒯 := fun k => collapseCorner hG hq k with hxdef
  have hcorner : ∀ k, (K.data.collapse 𝒯).squareCorner (x 0) k = x k := squareCorner_collapse hG hq
  have hφ4 : ((K.data.collapse 𝒯).facePerm ^ 4) (x 0) = x 0 :=
    facePerm_pow_collapseCorner (𝒯 := 𝒯) hG hq 4
  have hint : ∀ k, (K.data.collapse 𝒯).vertexOf ((K.data.collapse 𝒯).squareCorner (x 0) k) ∈
      (K.data.collapse 𝒯).internalVertices :=
    fun k => by
      rw [hcorner]
      exact (K.data.collapse 𝒯).vertexOf_mem_internalVertices.2
        (not_isBoundaryVertex_collapse_collapseCorner hG hq k)
  have hinj : Function.Injective fun k =>
      (K.data.collapse 𝒯).vertexOf ((K.data.collapse 𝒯).squareCorner (x 0) k) := by
    intro k l h
    simp only [hcorner] at h
    exact collapse_vertexOf_collapseCorner_injective hG hq h
  have hcol : ∀ k, (K.data.collapse 𝒯).colour ((K.data.collapse 𝒯).squareCorner (x 0) k) ≠
      (K.data.collapse 𝒯).colour ((K.data.collapse 𝒯).squareCorner (x 0) (k + 1)) := by
    intro k
    rw [hcorner, hcorner]
    erw [collapse_colour_collapseCorner hG hq, collapse_colour_collapseCorner hG hq]
    exact hq.colour_ne k
  have hface : (K.data.collapse 𝒯).faceOf (x 0) ∈ (K.data.collapse 𝒯).internalFaces :=
    collapse_faceOf_collapseCorner_mem_internalFaces (𝒯 := 𝒯) hG hq
  by_cases hroot : ∃ p ∈ 𝒯, ∃ k, p.1.root = K.data.vertexOf (K.data.squareCorner c k)
  · -- a corner of `q` is a root: `q` has a bivalent corner in `K/𝒯`
    obtain ⟨p, hp, k, hpk⟩ := hroot
    refine Or.inr (exists_nearlyLeaflessEquivalent_isHollowDigon (K := K.collapse h𝒯) hnl hface
      hφ4 hint hinj
      (fun j => by erw [hcorner]; exact two_le_card_collapse_collapseCorner hG hq j) hcol
      (k := k) ?_)
    erw [hcorner]
    exact le_antisymm (card_vertexOf_collapseCorner_le_two_of_root hG hq hp hpk)
      (two_le_card_collapse_collapseCorner hG hq k)
  push Not at hroot
  have hrootq : ∀ p ∈ 𝒯, p.1.root ∉ K.data.squareVertices c := fun p hp h => by
    obtain ⟨k, hk⟩ := mem_squareVertices.1 h
    exact hroot p hp k hk.symm
  have hWq : ∀ p ∈ 𝒯, ∀ w ∈ p.1.nonRoot, w ∉ K.data.squareVertices c := fun p hp w hw h => by
    obtain ⟨k, rfl⟩ := mem_squareVertices.1 h
    exact p.1.vertexOf_squareCorner_notMem_nonRoot hG hq k hw
  have h𝒯' := h𝒯.toSquareMove hG hrootq hWq
  have hfull : ∀ k, (K.data.vertexOf (K.data.squareCorner c k)).filter (· ∈ K.data.collapseCore 𝒯) =
      K.data.vertexOf (K.data.squareCorner c k) := fun k =>
    filter_vertexOf_mem_collapseCore_of_not hG
      (fun p _ => p.1.vertexOf_squareCorner_notMem_nonRoot hG hq k)
      (Or.inr fun p hp => hroot p hp k)
  have hqL : (K.data.collapse 𝒯).IsSquareMoveFace (x 0) :=
    { faceOf_mem_internalFaces := hface
      facePerm_pow_four := hφ4
      vertexOf_mem_internalVertices := hint
      injective := hinj
      card_vertexOf := fun k => by
        rw [hcorner, ← card_map (Function.Embedding.subtype _),
          map_vertexOf_collapseCorner hG hq k, hfull, hq.card_vertexOf k]
      colour_ne := hcol }
  have θ := collapseSquareMoveIso K h𝒯 hq h𝒯'
  refine Or.inl ⟨toSquareMoveFamily 𝒯 c, h𝒯', ?_, Or.inr ⟨.m1, trivial, x 0, hqL, ⟨θ⟩⟩⟩
  exact θ.symm.isNearlyLeafless ((K.collapse h𝒯).isPlabicGraph.squareMove (x 0))
    ((K.squareMove c).collapse h𝒯').isPlabicGraph hnl

/-- A nearly leafless graph `G` has nearly leafless collapse `G/∅` along the empty family, and
`G` is nearly leafless equivalent to `G/∅`. -/
private theorem nearlyLeaflessEquivalent_collapse_empty {G : PlabicGraph b}
    (hG : G.data.IsNearlyLeafless) :
    (G.data.collapse ∅).IsNearlyLeafless ∧
      NearlyLeaflessEquivalent G (G.collapse (isCollapsingFamily_empty (G := G.data))) := by
  have hθ := collapse_empty_isomorphic G
  have hnl : (G.data.collapse ∅).IsNearlyLeafless :=
    hθ.symm.elim fun θ => θ.isNearlyLeafless G.isPlabicGraph
      (G.collapse (isCollapsingFamily_empty (G := G.data))).isPlabicGraph hG
  exact ⟨hnl, ⟨hG, Relation.ReflTransGen.single ⟨hnl, Or.inl hθ⟩⟩⟩

/-- Given `HasCollapseSteps b`, a nearly leafless plabic graph `G` is not reduced if and only if
`G` is nearly leafless equivalent to a plabic graph containing a hollow digon. -/
theorem not_isReduced_iff_of_hasCollapseSteps (hstep : HasCollapseSteps b) {G : PlabicGraph b}
    (hG : G.data.IsNearlyLeafless) :
    ¬G.IsReduced ↔ ∃ X : PlabicGraph b, NearlyLeaflessEquivalent G X ∧
      ∃ f, X.data.IsHollowDigon f := by
  constructor
  · intro hred
    unfold IsReduced at hred
    push Not at hred
    obtain ⟨G', hG'G, hbad⟩ := hred
    have hbad' : (∃ f, G'.data.IsHollowDigon f) ∨ ∃ v, G'.data.IsInternalLeaf v ∧
        (¬∃ i, G'.data.IsLollipop i v) ∧
          ¬∃ T : G'.data.RootedTree, T.IsCollapsible ∧ v ∈ T.nonRoot := by
      by_cases h : ∀ f, ¬G'.data.IsHollowDigon f
      · obtain ⟨v, hv, h1, h2⟩ := hbad h
        exact Or.inr ⟨v, hv, fun ⟨i, hi⟩ => h1 i hi, fun ⟨T, hT, hvT⟩ => h2 T hT hvT⟩
      · push Not at h
        exact Or.inl h
    have key : ∀ K, MoveEquivalent Set.univ G K →
        (∃ X : PlabicGraph b, NearlyLeaflessEquivalent G X ∧ ∃ f, X.data.IsHollowDigon f) ∨
          ∃ (𝒯 : Finset (K.data.RootedTree × Shade)) (h𝒯 : K.data.IsCollapsingFamily 𝒯),
            (K.data.collapse 𝒯).IsNearlyLeafless ∧ NearlyLeaflessEquivalent G (K.collapse h𝒯) := by
      intro K hK
      induction hK with
      | refl =>
        obtain ⟨hnl, h⟩ := nearlyLeaflessEquivalent_collapse_empty hG
        exact Or.inr ⟨∅, isCollapsingFamily_empty, hnl, h⟩
      | @tail A B _ hAB ih =>
        rcases ih with h | ⟨𝒯, h𝒯, hnl, hGA⟩
        · exact Or.inl h
        rcases hstep A B 𝒯 h𝒯 hnl hAB with ⟨𝒯', h𝒯', hnl', hst⟩ | ⟨X, hX, hXd⟩
        · exact Or.inr ⟨𝒯', h𝒯', hnl', hGA.trans ⟨hGA.isNearlyLeafless_right, .single ⟨hnl', hst⟩⟩⟩
        · exact Or.inl ⟨X, hGA.trans hX, hXd⟩
    rcases key G' hG'G.symm with h | ⟨𝒯, h𝒯, hnl, hGK⟩
    · exact h
    obtain ⟨f, hf⟩ := h𝒯.exists_isHollowDigon_collapse G'.isPlabicGraph hnl hbad'
    exact ⟨_, hGK, f, hf⟩
  · rintro ⟨X, hX, f, hf⟩ hred
    exact (hred X hX.moveEquivalent.symm).1 f hf

/-- A **step without internal leaves**: `G'` has no internal leaf and is isomorphic to `G` or
obtained from `G` by a local move. -/
def LeaflessStep (G G' : PlabicGraph b) : Prop :=
  (∀ v, ¬G'.data.IsInternalLeaf v) ∧ MoveStep Set.univ G G'

/-- Given `HasCollapseSteps b`: if `G` and `G'` have no internal leaves, `G` is reduced and
`G ∼ G'`, then `G` and `G'` are joined by a sequence of steps through plabic graphs without
internal leaves. -/
theorem reflTransGen_leaflessStep_of_hasCollapseSteps (hstep : HasCollapseSteps b)
    {G G' : PlabicGraph b} (hG : ∀ v, ¬G.data.IsInternalLeaf v)
    (hG' : ∀ v, ¬G'.data.IsInternalLeaf v) (hred : G.IsReduced)
    (h : MoveEquivalent Set.univ G G') : Relation.ReflTransGen LeaflessStep G G' := by
  have hGnl : G.data.IsNearlyLeafless := fun v hv => absurd hv (hG v)
  have key : ∀ K, MoveEquivalent Set.univ G K →
      ∃ (𝒯 : Finset (K.data.RootedTree × Shade)) (h𝒯 : K.data.IsCollapsingFamily 𝒯),
        (K.data.collapse 𝒯).IsNearlyLeafless ∧ (∀ v, ¬(K.data.collapse 𝒯).IsInternalLeaf v) ∧
          Relation.ReflTransGen LeaflessStep G (K.collapse h𝒯) := by
    intro K hK
    induction hK with
    | refl =>
      obtain ⟨hnl, -⟩ := nearlyLeaflessEquivalent_collapse_empty hGnl
      have hθ := collapse_empty_isomorphic G
      have hL : ∀ v, ¬(G.data.collapse ∅).IsInternalLeaf v :=
        hθ.symm.elim fun θ => θ.forall_not_isInternalLeaf hG
      exact ⟨∅, isCollapsingFamily_empty, hnl, hL, .single ⟨hL, Or.inl hθ⟩⟩
    | @tail A B hGA hAB ih =>
      obtain ⟨𝒯, h𝒯, hnl, hL, hseq⟩ := ih
      rcases hstep A B 𝒯 h𝒯 hnl hAB with ⟨𝒯', h𝒯', hnl', hst⟩ | ⟨X, hX, f, hf⟩
      · have hL' := MoveStep.forall_not_isInternalLeaf (L := A.collapse h𝒯) (L' := B.collapse h𝒯')
          hL hnl' hst
        exact ⟨𝒯', h𝒯', hnl', hL', hseq.tail ⟨hL', hst⟩⟩
      · exfalso
        have hXG : MoveEquivalent Set.univ X G :=
          hX.moveEquivalent.symm.trans (((A.moveEquivalent_collapse h𝒯).mono
            (Set.subset_univ _)).symm.trans (MoveEquivalent.symm hGA))
        exact (hred X hXG).1 f hf
  obtain ⟨𝒯, h𝒯, -, -, hseq⟩ := key G' h
  have h𝒯e : 𝒯 = ∅ := by
    by_contra hne
    obtain ⟨p, -⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨w, -, hw⟩ := p.1.exists_isInternalLeaf G'.isPlabicGraph
    exact hG' w hw
  subst h𝒯e
  exact hseq.tail ⟨hG', Or.inl (collapse_empty_isomorphic G').symm⟩

end PlabicGraph

end ClusterAlgebras
