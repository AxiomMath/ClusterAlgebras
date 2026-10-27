/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TreeBranches
public import ClusterAlgebras.Plabic.TreeSubstitution

/-!
# Collapsing trees in plabic graphs

A *collapsing family* of a plabic graph `G` is a finite set of triples `(v, W, c)`, each `(v, W)` a
collapsible tree of colour `c`, whose sets `W` are pairwise disjoint, whose roots lie in no other
`W`, and whose roots keep a dart outside all the trees. The *collapse* `G/𝒯` deletes the darts of
the trees: an internal root loses its intervals, and a tree with a boundary root `β(i)` is replaced
by a lollipop of its colour at `i`. Its rotation is the first return of `σ` to the kept darts.

A rooted tree with an internal root is collapsible if and only if each of its branches is. The main
result of this development is that collapsing is a sequence of moves (M2) and (M3). To prove it,
the plabic graph `P_T` of a tree is replaced inside `G` by any plabic graph `R` with one boundary
vertex, a *`T`-filling*: the *substitution* `G[R]` splices the rotation of `R` around the dart `ḡ`
across its leg (or around its leg, for a boundary root) into the rotation of `G` at the root, in
place of the interval of `T`. A reduction step of `R` (the removal of a bivalent vertex or the
contraction of an edge between internal vertices of the same colour) is then a local move of
`G[R]`. Substituting `P_T` gives back `G`; reducing `P_T` as far as possible gives `L_c`, and
substituting `L_c` gives the collapse.

This file proves the characterization of collapsible trees by their branches, and re-exports the
collapse (`ClusterAlgebras.Plabic.FamilyCollapse`), the branches
(`ClusterAlgebras.Plabic.TreeBranches`) and the substitution
(`ClusterAlgebras.Plabic.TreeSubstitution`).

## Main results

* `ClusterAlgebras.PlabicData.RootedTree.isCollapsible_iff_forall_isCollapsible_branchTree`: a tree
  with an internal root is collapsible iff its branches are.

## Implementation notes

* For `RootedTree.isCollapsible_iff_forall_isCollapsible_branchTree`, each branch `T_j` of `T` is
  transported into `P_T` along the inclusion `D_T → H_T` (`RootedTree.IsEmbedding.tree`,
  `RootedTree.branchTreeIn`), where it is a rooted tree with root `{ḡ, a₁, …, a_k}` and the same
  plabic graph `P_{T_j}`. Then `P_T` is the substitution of the `P_{T_j}` into these trees, and the
  tuple `C(R_1, …, R_k)` of FWZ is the substitution of the reductions `R_j`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Orbits of the glued rotation -/

section GluedOrbits

variable {ι : Type} [Fintype ι] {T : ι → G.RootedTree}
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts) {R : ι → PlabicGraph 1}

include hdisj

/-- The orbit of the glued rotation through the last dart `a_k` of `T j` contains the whole cycle
of `R j` through its attaching dart. -/
theorem sameCycle_substRot_inl_intervalEnd_inr {j : ι} {w : (R j).Dart}
    (hw : (R j).data.rot.SameCycle ((T j).attachDart (R j)) w) :
    (substRot T R).SameCycle (.inl (T j).intervalEnd) (.inr ⟨j, w⟩) := by
  have hinj := intervalEnd_injective hdisj
  set a := (T j).attachDart (R j)
  set σ := (R j).data.rot
  have h1 : (substRot T R).SameCycle (.inl (T j).intervalEnd) (.inr ⟨j, σ a⟩) :=
    ⟨1, by rw [zpow_one, substRot_inl_intervalEnd hinj]⟩
  refine h1.trans ?_
  have hex : ∃ n : ℕ, (σ ^ n) (σ a) = w := (Perm.sameCycle_apply_left.2 hw).exists_nat_pow_eq
  classical
  set n := Nat.find hex with hn
  have hnw : (σ ^ n) (σ a) = w := Nat.find_spec hex
  have hmin : ∀ m < n, (σ ^ m) (σ a) ≠ a := by
    intro m hm h
    have hm' : (σ ^ (n - (m + 1))) (σ a) = w := by
      rw [← hnw, show n = n - (m + 1) + (m + 1) by omega, pow_add, Perm.mul_apply,
        pow_succ', Perm.mul_apply, h, Nat.add_sub_cancel]
    exact Nat.find_min hex (by omega) hm'
  have key : ∀ i ≤ n, ((substRot T R) ^ i) (.inr ⟨j, σ a⟩) = .inr ⟨j, (σ ^ i) (σ a)⟩ := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ', Perm.mul_apply, ih (by omega),
        substRot_inr_of_ne hinj (hmin i (by omega)), pow_succ', Perm.mul_apply]
  exact ⟨n, by rw [zpow_natCast, key n le_rfl, hnw]⟩

/-- Consecutive darts of `G` lie in one orbit of the glued rotation. -/
theorem sameCycle_substRot_inl_rot (d : H) :
    (substRot T R).SameCycle (.inl d) (.inl (G.rot d)) := by
  have hinj := intervalEnd_injective hdisj
  by_cases h : ∃ j, (T j).intervalEnd = d
  · obtain ⟨j, rfl⟩ := h
    exact (sameCycle_substRot_inl_intervalEnd_inr hdisj (Perm.SameCycle.refl _ _)).trans
      ⟨1, by rw [zpow_one, substRot_inr_attachDart hinj]⟩
  · push Not at h
    exact ⟨1, by rw [zpow_one, substRot_inl_of_forall_ne hinj h]⟩

/-- Darts at one vertex of `G` lie in one orbit of the glued rotation. -/
theorem sameCycle_substRot_inl_of_sameCycle {d d' : H} (h : G.rot.SameCycle d d') :
    (substRot T R).SameCycle (.inl d) (.inl d') := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Perm.SameCycle.refl _ _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (sameCycle_substRot_inl_rot hdisj _)

/-- Darts at one vertex of a filling lie in one orbit of the glued rotation. -/
theorem sameCycle_substRot_inr_of_sameCycle {j : ι} {w w' : (R j).Dart}
    (h : (R j).data.rot.SameCycle w w') :
    (substRot T R).SameCycle (.inr ⟨j, w⟩) (.inr ⟨j, w'⟩) := by
  have hinj := intervalEnd_injective hdisj
  by_cases ha : (R j).data.rot.SameCycle ((T j).attachDart (R j)) w
  · exact (sameCycle_substRot_inl_intervalEnd_inr hdisj ha).symm.trans
      (sameCycle_substRot_inl_intervalEnd_inr hdisj (ha.trans h))
  · obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    have key : ∀ i, ((substRot T R) ^ i) (.inr ⟨j, w⟩) = .inr ⟨j, ((R j).data.rot ^ i) w⟩ := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        have hne : ((R j).data.rot ^ i) w ≠ (T j).attachDart (R j) := fun h' =>
          ha (h' ▸ (sameCycle_pow_apply_self _ w i).symm)
        rw [pow_succ', Perm.mul_apply, ih, substRot_inr_of_ne hinj hne, pow_succ', Perm.mul_apply]
    exact ⟨n, by rw [zpow_natCast, key]⟩

end GluedOrbits

/-! ### The branches inside the plabic graph of a tree -/

section BranchesInside

open PlabicGraph

namespace RootedTree

variable (T : G.RootedTree)

/-- The inclusion of the darts `D_T` into the darts of `P_T` (any other dart goes to `e`). -/
noncomputable def toDart (d : H) : T.Dart :=
  if h : d ∈ T.darts then ⟨.inl d, h⟩ else T.dartE

/-- The inclusion `toDart` sends a dart of `D_T` to itself. -/
theorem toDart_of_mem {d : H} (h : d ∈ T.darts) : T.toDart d = ⟨.inl d, h⟩ :=
  dif_pos h

/-- The inclusion `toDart` sends a dart outside `D_T` to `e`. -/
theorem toDart_of_notMem {d : H} (h : d ∉ T.darts) : T.toDart d = T.dartE :=
  dif_neg h

/-- The inclusion `toDart` is injective on the darts of `D_T`. -/
theorem toDart_injOn : Set.InjOn T.toDart T.darts := fun d hd d' hd' h => by
  rw [T.toDart_of_mem hd, T.toDart_of_mem hd'] at h
  exact Sum.inl.inj (congrArg Subtype.val h)

/-- If the rotation of `P_T` takes the dart `d` of `D_T` to the dart `y` of `D_T`, then
`σ d = y`. -/
theorem rot_eq_of_rot_toDart_eq (hG : G.IsPlabicGraph) {d y : H} (hd : d ∈ T.darts)
    (hy : y ∈ T.darts) (h : T.plabicData.rot (T.toDart d) = T.toDart y) : G.rot d = y := by
  have h' := congrArg Subtype.val h
  rw [T.coe_rot_plabicData hG, T.toDart_of_mem hd, T.toDart_of_mem hy] at h'
  change T.rotAux (.inl d) = .inl y at h'
  by_cases h₁ : G.rot d ∈ T.darts
  · simp only [rotAux, h₁, if_true] at h'
    exact Sum.inl.inj h'
  · simp [rotAux, h₁] at h'

/-- The interval of the branch at `a_i` is `(a_i)`. -/
theorem branchTree_intervalLength (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    (T.branchTree hG hi).intervalLength = 1 := by
  rw [intervalLength_eq_card, card_eq_one]
  refine ⟨(G.rot ^ i) T.intervalStart, ?_⟩
  ext d
  simp only [mem_filter, mem_singleton, branchTree_root, branchTree_darts]
  constructor
  · rintro ⟨hr, hd⟩
    exact T.eq_of_mem_branchDarts_of_mem_root hG hi hd hr
  · rintro rfl
    exact ⟨T.pow_intervalStart_mem_root i, T.pow_intervalStart_mem_branchDarts hi⟩

/-- The interval of the branch tree at `a_i` ends at `a_i`. -/
theorem branchTree_intervalEnd (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    (T.branchTree hG hi).intervalEnd = (G.rot ^ i) T.intervalStart := by
  rw [intervalEnd, T.branchTree_intervalLength hG hi, Nat.sub_self, pow_zero, Perm.one_apply,
    T.branchTree_intervalStart hG hi]

/-- The branch at `a_i` embeds into `P_T`. -/
theorem branchTree_isEmbedding (hG : G.IsPlabicGraph) {i : ℕ} (hi : i < T.intervalLength) :
    (T.branchTree hG hi).IsEmbedding T.plabicData T.toDart where
  injOn := fun x hx y hy h => T.toDart_injOn (T.branchDarts_subset i hx)
    (T.branchDarts_subset i hy) h
  map_inv := fun d hd => by
    have hd' := T.branchDarts_subset i hd
    rw [T.toDart_of_mem (T.inv_mem_darts hG hd'), T.toDart_of_mem hd', T.inv_inl hG hd']
  map_rot := fun d hd hrd => by
    rw [T.toDart_of_mem (T.branchDarts_subset i hrd), T.toDart_of_mem (T.branchDarts_subset i hd),
      T.rot_inl_of_mem hG _ (T.branchDarts_subset i hrd)]
  notMem_bdry := fun d hd => by
    rw [T.toDart_of_mem (T.branchDarts_subset i hd), T.mem_bdry_plabicData]
    rintro (h | h) <;> simp [dartE, dartEBar, Subtype.ext_iff] at h
  rot_intervalEnd_notMem := by
    intro hx
    obtain ⟨y, hy, hxy⟩ := mem_image.1 hx
    have ha := (T.branchTree hG hi).intervalEnd_mem_darts
    have := T.rot_eq_of_rot_toDart_eq hG (T.branchDarts_subset i ha)
      (T.branchDarts_subset i hy) hxy.symm
    exact (T.branchTree hG hi).rot_intervalEnd_notMem hG (this ▸ hy)
  rot_symm_intervalStart_notMem := by
    intro hx
    obtain ⟨y, hy, hxy⟩ := mem_image.1 hx
    have ha := (T.branchTree hG hi).intervalStart_mem_darts
    have h' : T.plabicData.rot (T.toDart y) = T.toDart (T.branchTree hG hi).intervalStart := by
      rw [hxy, Equiv.apply_symm_apply]
    have := T.rot_eq_of_rot_toDart_eq hG (T.branchDarts_subset i hy)
      (T.branchDarts_subset i ha) h'
    refine (T.branchTree hG hi).rot_symm_intervalStart_notMem ?_
    rwa [← this, Equiv.symm_apply_apply]
  intervalLength_lt_card := by
    rw [T.branchTree_intervalLength hG hi, Finset.one_lt_card]
    set s := (T.branchTree hG hi).intervalStart
    have hs : s ∈ T.darts := T.branchDarts_subset i (T.branchTree hG hi).intervalStart_mem_darts
    refine ⟨_, T.plabicData.self_mem_vertexOf _, _, T.plabicData.rot_mem_vertexOf _,
      fun h => ?_⟩
    have hfix := T.rot_eq_of_rot_toDart_eq hG hs hs h.symm
    have h1 : (G.rot ^ 1) s = s := by rwa [pow_one]
    have := card_vertexOf_le_of_pow_apply_eq one_pos h1
    rw [← (T.branchTree hG hi).root_eq_vertexOf_intervalStart] at this
    have := (T.branchTree hG hi).one_lt_card_root
    omega
  colour := fun d hd => by
    rw [T.toDart_of_mem (T.branchDarts_subset i hd)]
    rfl

/-- The dart `ḡ` of `P_T` lies at the vertex of every dart of the interval. -/
theorem sameCycle_gBar_toDart (hG : G.IsPlabicGraph) (hb : ¬G.IsBoundaryVertex T.root) {j : ℕ}
    (hj : j < T.intervalLength) :
    T.plabicData.rot.SameCycle ⟨.inr .gBar, hb⟩ (T.toDart ((G.rot ^ j) T.intervalStart)) := by
  induction j with
  | zero =>
    refine ⟨1, ?_⟩
    rw [zpow_one, pow_zero, Perm.one_apply, T.rot_gBar hG hb,
      T.toDart_of_mem T.intervalStart_mem_darts]
  | succ j ih =>
    refine (ih (by omega)).trans ⟨1, ?_⟩
    have h₁ := T.pow_intervalStart_mem_darts (j := j) (by omega)
    have h₂ := T.pow_intervalStart_mem_darts hj
    rw [pow_succ', Perm.mul_apply] at h₂ ⊢
    rw [zpow_one, T.toDart_of_mem h₁, T.toDart_of_mem h₂, T.rot_inl_of_mem hG h₁ h₂]

/-- The darts at the vertex of `ḡ` in `P_T` are `ḡ` and the darts of the interval. -/
theorem eq_gBar_or_of_sameCycle (hG : G.IsPlabicGraph) (hb : ¬G.IsBoundaryVertex T.root)
    {x : T.Dart} (h : T.plabicData.rot.SameCycle ⟨.inr .gBar, hb⟩ x) :
    x = ⟨.inr .gBar, hb⟩ ∨ ∃ d ∈ T.darts, d ∈ T.root ∧ x = T.toDart d := by
  refine SameCycle.of_invariant (π := T.plabicData.rot)
    (fun x => x = ⟨.inr .gBar, hb⟩ ∨ ∃ d ∈ T.darts, d ∈ T.root ∧ x = T.toDart d) ?_
    (Or.inl rfl) h
  rintro _ (rfl | ⟨d, hd, hr, rfl⟩)
  · rw [T.rot_gBar hG hb]
    exact Or.inr ⟨_, T.intervalStart_mem_darts, T.intervalStart_mem_root,
      (T.toDart_of_mem _).symm⟩
  · by_cases h : G.rot d ∈ T.darts
    · rw [T.toDart_of_mem hd, T.rot_inl_of_mem hG hd h]
      refine Or.inr ⟨_, h, ?_, (T.toDart_of_mem _).symm⟩
      rwa [T.mem_root_iff, G.vertexOf_rot, ← T.mem_root_iff]
    · left
      apply Subtype.ext
      rw [T.coe_rot_plabicData hG, T.toDart_of_mem hd]
      change T.rotAux (.inl d) = _
      simp [rotAux, h, hb]

/-- **The branch at `a_i` as a rooted tree of `P_T`**, with root the vertex `{ḡ, a₁, …, a_k}` of
`P_T` and interval `(a_i)`. -/
noncomputable def branchTreeIn (hG : G.IsPlabicGraph) (i : Fin T.intervalLength) :
    T.plabicData.RootedTree :=
  (T.branchTree_isEmbedding hG i.isLt).tree hG (T.isPlabicGraph_plabicData hG)

/-- The darts of the branch at `a_i` inside `P_T` are the images of the darts of the branch. -/
theorem branchTreeIn_darts (hG : G.IsPlabicGraph) (i : Fin T.intervalLength) :
    (T.branchTreeIn hG i).darts = (T.branchDarts i).image T.toDart :=
  IsEmbedding.tree_darts _ hG _

/-- The interval of the branch at `a_i` inside `P_T` ends at the image of `a_i`. -/
theorem branchTreeIn_intervalEnd (hG : G.IsPlabicGraph) (i : Fin T.intervalLength) :
    (T.branchTreeIn hG i).intervalEnd = T.toDart ((G.rot ^ (i : ℕ)) T.intervalStart) := by
  have h₁ := IsEmbedding.tree_intervalLength (T.branchTree_isEmbedding hG i.isLt) hG
    (T.isPlabicGraph_plabicData hG)
  have h₂ := IsEmbedding.tree_intervalStart (T.branchTree_isEmbedding hG i.isLt) hG
    (T.isPlabicGraph_plabicData hG)
  rw [T.branchTree_intervalLength hG i.isLt] at h₁
  change (T.branchTreeIn hG i).intervalLength = 1 at h₁
  change (T.branchTreeIn hG i).intervalStart = _ at h₂
  rw [intervalEnd, h₁, Nat.sub_self, pow_zero, Perm.one_apply, h₂,
    T.branchTree_intervalStart hG i.isLt]

/-- For an internal root, the root of the branch at `a_i` inside `P_T` is the vertex of `ḡ`. -/
theorem branchTreeIn_root (hG : G.IsPlabicGraph) (hb : ¬G.IsBoundaryVertex T.root)
    (i : Fin T.intervalLength) :
    (T.branchTreeIn hG i).root = T.plabicData.vertexOf ⟨.inr .gBar, hb⟩ := by
  rw [← (T.branchTreeIn hG i).mem_root_iff.1 (T.branchTreeIn hG i).intervalEnd_mem_root,
    branchTreeIn_intervalEnd]
  exact (T.plabicData.vertexOf_eq_vertexOf_iff.2 (T.sameCycle_gBar_toDart hG hb i.isLt)).symm

/-- For an internal root, the root of the branch at `a_i` inside `P_T` is internal. -/
theorem not_isBoundaryVertex_branchTreeIn_root (hG : G.IsPlabicGraph)
    (hb : ¬G.IsBoundaryVertex T.root) (i : Fin T.intervalLength) :
    ¬T.plabicData.IsBoundaryVertex (T.branchTreeIn hG i).root := by
  rw [T.branchTreeIn_root hG hb, ← T.inv_legDart_of_not_isBoundaryVertex hG hb]
  exact not_isBoundaryVertex_inv_leg' (T.isPlabicGraph_plabicData hG)

/-- The branches of `T` inside `P_T` at distinct darts of the interval have disjoint darts. -/
theorem pairwise_disjoint_branchTreeIn_darts (hG : G.IsPlabicGraph) :
    Pairwise fun i i' => Disjoint (T.branchTreeIn hG i).darts (T.branchTreeIn hG i').darts := by
  intro i i' hne
  rw [branchTreeIn_darts, branchTreeIn_darts, Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  obtain ⟨d', hd', h⟩ := mem_image.1 hx'
  obtain rfl := T.toDart_injOn (T.branchDarts_subset _ hd') (T.branchDarts_subset _ hd) h
  exact Finset.disjoint_left.1 (T.disjoint_branchDarts hG i.isLt i'.isLt
    (fun h => hne (Fin.ext h))) hd hd'

/-- The plabic graph of the branch at `a_i` inside `P_T` is isomorphic to that of the branch
inside `G`. -/
theorem branchTreeIn_plabicData_isomorphic (hG : G.IsPlabicGraph)
    (hb : ¬G.IsBoundaryVertex T.root) (i : Fin T.intervalLength) :
    (T.branchTree hG i.isLt).plabicData.Isomorphic (T.branchTreeIn hG i).plabicData :=
  IsEmbedding.tree_plabicData_isomorphic _ hG _ hb
    (T.not_isBoundaryVertex_branchTreeIn_root hG hb i)

end RootedTree

end BranchesInside

/-! ### Substituting fillings into the branches inside `P_T` -/

section BranchSubstitution

open PlabicGraph

/-- A dart of a plabic graph with one boundary vertex that is neither in `B` nor the leg lies at an
internal vertex. -/
private theorem not_isBoundaryVertex_of_ne_leg {Q : PlabicGraph 1} {y : Q.Dart}
    (hB : y ∉ Q.data.bdry) (hl : y ≠ Q.data.leg 0) :
    ¬Q.data.IsBoundaryVertex (Q.data.vertexOf y) := fun h => by
  obtain ⟨j, rfl⟩ := Q.isPlabicGraph.exists_eq_leg_of_isBoundaryVertex h hB
  exact hl (by rw [Subsingleton.elim j 0])

/-- For an internal root, a dart of a plabic graph with one boundary vertex is not cut iff it is
neither in `B` nor the leg `g` nor `ḡ`. -/
theorem RootedTree.not_isCutDart_iff (T₀ : G.RootedTree) (hb : ¬G.IsBoundaryVertex T₀.root)
    {Q : PlabicGraph 1} {y : Q.Dart} :
    ¬T₀.IsCutDart Q y ↔
      y ∉ Q.data.bdry ∧ y ≠ Q.data.leg 0 ∧ y ≠ Q.data.inv (Q.data.leg 0) := by
  simp only [RootedTree.IsCutDart, hb, not_false_eq_true, true_and, not_or]

/-- A dart at an internal vertex of a filling, at a vertex other than that of `ḡ`, is not cut. -/
private theorem not_isCutDart_of_not_sameCycle (T₀ : G.RootedTree)
    (hb : ¬G.IsBoundaryVertex T₀.root) {Q : PlabicGraph 1} {y : Q.Dart}
    (hy : ¬Q.data.IsBoundaryVertex (Q.data.vertexOf y))
    (hs : ¬Q.data.rot.SameCycle (Q.data.inv (Q.data.leg 0)) y) : ¬T₀.IsCutDart Q y := by
  refine (T₀.not_isCutDart_iff hb).2 ⟨fun h => hy (Q.data.isBoundaryVertex_vertexOf_of_mem h),
    ?_, ?_⟩
  · rintro rfl
    exact hy (Q.data.vertexOf_mem_boundaryVertices.1 (Q.isPlabicGraph.bvertex_mem 0))
  · rintro rfl
    exact hs (Perm.SameCycle.refl _ _)

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {T : ι → G.RootedTree} (hG : G.IsPlabicGraph)
  (hdisj : Pairwise fun j j' => Disjoint (T j).darts (T j').darts) {R : ι → PlabicGraph 1}

include hdisj

/-- A vertex of the substitution through a surviving dart `y` of a filling, away from the
attaching dart, has as many darts as the vertex of `y` in the filling. -/
theorem card_vertexOf_familySubstitution_of_not_sameCycle {x : substDarts T R} {j : ι}
    {y : (R j).Dart} (hx : (x : H ⊕ Σ j, (R j).Dart) = .inr ⟨j, y⟩)
    (hy : ¬(R j).data.rot.SameCycle y ((T j).attachDart (R j)))
    (hnc : ∀ w ∈ (R j).data.vertexOf y, ¬(T j).IsCutDart (R j) w) :
    ((G.familySubstitution T R hG).vertexOf x).card = ((R j).data.vertexOf y).card := by
  symm
  refine Finset.card_bij (fun w hw => (⟨.inr ⟨j, w⟩, hnc w hw⟩ : substDarts T R)) ?_ ?_ ?_
  · intro w hw
    rw [RotationSystem.mem_vertexOf]
    change (firstReturnPerm (substRot T R) (substDarts T R)).SameCycle _ _
    rw [sameCycle_firstReturnPerm_iff, hx]
    exact sameCycle_substRot_inr_of_sameCycle hdisj ((RotationSystem.mem_vertexOf _).1 hw)
  · intro w hw w' hw' h
    simpa using congrArg Subtype.val h
  · intro z hz
    have hs := sameCycle_substRot_of_mem_vertexOf hG hz
    rw [hx] at hs
    obtain ⟨w, hw, hyw⟩ := substRot_orbit_of_not_sameCycle hdisj hy hs
    exact ⟨w, (RotationSystem.mem_vertexOf _).2 hyw, Subtype.ext hw.symm⟩

end Generic

variable {T : G.RootedTree} (hG : G.IsPlabicGraph) (hb : ¬G.IsBoundaryVertex T.root)
  {R : Fin T.intervalLength → PlabicGraph 1}

include hb

/-- For an internal root, the dart of a filling glued to the branch at `a_j` inside `P_T` is
`ḡ`. -/
theorem attachDart_branchTreeIn (j : Fin T.intervalLength) (Q : PlabicGraph 1) :
    (T.branchTreeIn hG j).attachDart Q = Q.data.inv (Q.data.leg 0) := by
  rw [RootedTree.attachDart, if_neg (T.not_isBoundaryVertex_branchTreeIn_root hG hb j)]

/-- The leg of the substitution of the fillings `R_j` into the branches of `T` inside `P_T` is the
leg of `P_T`. -/
theorem coe_familySubstitution_branchTreeIn_leg :
    ((T.plabicData.familySubstitution (T.branchTreeIn hG) R (T.isPlabicGraph_plabicData hG)).leg 0 :
      T.Dart ⊕ Σ j, (R j).Dart) = .inl T.legDart := by
  rw [coe_familySubstitution_leg_of_notMem]
  · rfl
  · intro j hj
    rw [RootedTree.branchTreeIn_darts] at hj
    obtain ⟨d, hd, h⟩ := mem_image.1 hj
    rw [T.toDart_of_mem (T.branchDarts_subset _ hd)] at h
    have h' := congrArg Subtype.val h
    change Sum.inl d = (T.legDart : H ⊕ LollipopDart) at h'
    rw [RootedTree.legDart, dif_neg hb] at h'
    simp at h'

/-- The involution of the substitution of the fillings `R_j` into the branches of `T` inside `P_T`
sends its leg to `ḡ`. -/
theorem coe_familySubstitution_branchTreeIn_inv_leg :
    ((T.plabicData.familySubstitution (T.branchTreeIn hG) R (T.isPlabicGraph_plabicData hG)).inv
      ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).leg 0) : T.Dart ⊕ Σ j, (R j).Dart) =
      .inl ⟨.inr .gBar, hb⟩ := by
  rw [coe_familySubstitution_inv, coe_familySubstitution_branchTreeIn_leg hG hb, substInv_inl,
    T.inv_legDart_of_not_isBoundaryVertex hG hb]

/-- The darts of the cycle of `ḡ` in a filling lie in the orbit of `ḡ` of the glued rotation. -/
theorem sameCycle_substRot_gBar_inr {j : Fin T.intervalLength} {w : (R j).Dart}
    (hw : (R j).data.rot.SameCycle ((R j).data.inv ((R j).data.leg 0)) w) :
    (substRot (T.branchTreeIn hG) R).SameCycle (.inl ⟨.inr .gBar, hb⟩) (.inr ⟨j, w⟩) := by
  have hdisj := T.pairwise_disjoint_branchTreeIn_darts hG
  have h₁ : T.plabicData.rot.SameCycle ⟨.inr .gBar, hb⟩ (T.branchTreeIn hG j).intervalEnd := by
    rw [RootedTree.branchTreeIn_intervalEnd]
    exact T.sameCycle_gBar_toDart hG hb j.isLt
  refine (sameCycle_substRot_inl_of_sameCycle hdisj h₁).trans
    (sameCycle_substRot_inl_intervalEnd_inr hdisj ?_)
  rwa [attachDart_branchTreeIn hG hb]

/-- The darts of the substitution coming from `P_T` are `e`, `ē`, the leg `g` and `ḡ`. -/
theorem familySubstitution_branchTreeIn_inl_cases
    {z : substDarts (T.branchTreeIn hG) R} {e : T.Dart}
    (hz : (z : T.Dart ⊕ Σ j, (R j).Dart) = .inl e) :
    z ∈ (T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).bdry ∨
      z = (T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).leg 0 ∨
      z = (T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).inv ((T.plabicData.familySubstitution
          (T.branchTreeIn hG) R (T.isPlabicGraph_plabicData hG)).leg 0) := by
  have hz2 := z.2
  rw [hz] at hz2
  have hout := (inl_mem_substDarts _ _).1 hz2
  obtain ⟨x, hx⟩ := e
  rcases x with d | (_ | _ | _ | _)
  · exfalso
    obtain ⟨i, hi, hdi⟩ := T.exists_mem_branchDarts (d := d) hx
    refine hout ⟨i, hi⟩ ?_
    rw [RootedTree.branchTreeIn_darts]
    exact mem_image.2 ⟨d, hdi, T.toDart_of_mem hx⟩
  · left
    exact (mem_familySubstitution_bdry _).2 ⟨T.dartE, T.mem_bdry_plabicData.2 (Or.inl rfl), hz⟩
  · left
    exact (mem_familySubstitution_bdry _).2
      ⟨T.dartEBar, T.mem_bdry_plabicData.2 (Or.inr rfl), hz⟩
  · right
    left
    apply Subtype.ext
    rw [hz, coe_familySubstitution_branchTreeIn_leg hG hb, RootedTree.legDart, dif_neg hb]
  · right
    right
    apply Subtype.ext
    rw [hz, coe_familySubstitution_branchTreeIn_inv_leg hG hb]

/-- A dart of the substitution of the fillings `R_j` into the branches of `T` inside `P_T` lies at
the vertex of `ḡ` iff it lies in the orbit of `ḡ` of the glued rotation. -/
theorem mem_vertexOf_familySubstitution_branchTreeIn_inv_leg_iff
    (z : substDarts (T.branchTreeIn hG) R) :
    z ∈ (T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).vertexOf
      ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).inv ((T.plabicData.familySubstitution
          (T.branchTreeIn hG) R (T.isPlabicGraph_plabicData hG)).leg 0)) ↔
      (substRot (T.branchTreeIn hG) R).SameCycle (.inl ⟨.inr .gBar, hb⟩) z := by
  rw [RotationSystem.mem_vertexOf, ← coe_familySubstitution_branchTreeIn_inv_leg hG hb (R := R)]
  exact sameCycle_firstReturnPerm_iff _ _

/-- If the vertex of `ḡ` in the substitution of the fillings `R_j` into the branches of `T` inside
`P_T` is `{ḡ}`, then so is the vertex of `ḡ` in each `R_j`. -/
theorem card_vertexOf_inv_leg_eq_one_of_card_familySubstitution_branchTreeIn
    (h1 : ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).vertexOf
      ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).inv ((T.plabicData.familySubstitution
          (T.branchTreeIn hG) R (T.isPlabicGraph_plabicData hG)).leg 0))).card = 1)
    (j : Fin T.intervalLength) :
    ((R j).data.vertexOf ((R j).data.inv ((R j).data.leg 0))).card = 1 := by
  classical
  set S := T.plabicData.familySubstitution (T.branchTreeIn hG) R
    (T.isPlabicGraph_plabicData hG)
  have hx₀ : ((S.inv (S.leg 0) : substDarts _ _) : T.Dart ⊕ Σ j, (R j).Dart) =
      .inl ⟨.inr .gBar, hb⟩ := coe_familySubstitution_branchTreeIn_inv_leg hG hb
  have hmem : ∀ z : substDarts (T.branchTreeIn hG) R, z ∈ S.vertexOf (S.inv (S.leg 0)) ↔
      (substRot (T.branchTreeIn hG) R).SameCycle (.inl ⟨.inr .gBar, hb⟩) z :=
    mem_vertexOf_familySubstitution_branchTreeIn_inv_leg_iff hG hb
  by_contra hne
  obtain ⟨w, hw, hwne⟩ : ∃ w ∈ (R j).data.vertexOf ((R j).data.inv ((R j).data.leg 0)),
      w ≠ (R j).data.inv ((R j).data.leg 0) := by
    by_contra hcon
    push Not at hcon
    exact hne (card_eq_one.2 ⟨_, eq_singleton_iff_unique_mem.2
      ⟨(R j).data.self_mem_vertexOf _, hcon⟩⟩)
  have hint := not_isBoundaryVertex_inv_leg' (R j).isPlabicGraph
  have hwv := (R j).data.vertexOf_eq_of_mem hw
  have hsw : (R j).data.rot.SameCycle ((R j).data.inv ((R j).data.leg 0)) w :=
    (RotationSystem.mem_vertexOf _).1 hw
  have hnc : ¬(T.branchTreeIn hG j).IsCutDart (R j) w := by
    refine ((T.branchTreeIn hG j).not_isCutDart_iff
      (T.not_isBoundaryVertex_branchTreeIn_root hG hb j)).2 ⟨fun h => ?_, ?_, hwne⟩
    · exact hint (hwv ▸ (R j).data.isBoundaryVertex_vertexOf_of_mem h)
    · rintro rfl
      exact hint (hwv ▸ (R j).data.vertexOf_mem_boundaryVertices.1
        ((R j).isPlabicGraph.bvertex_mem 0))
  have hz := (hmem ⟨.inr ⟨j, w⟩, hnc⟩).2 (sameCycle_substRot_gBar_inr hG hb hsw)
  obtain ⟨a, ha⟩ := card_eq_one.1 h1
  have e₁ := mem_singleton.1 (ha ▸ S.self_mem_vertexOf (S.inv (S.leg 0)))
  have e₂ := mem_singleton.1 (ha ▸ hz)
  have := congrArg Subtype.val (e₂.trans e₁.symm)
  rw [hx₀] at this
  simp at this

/-- If the vertex of `ḡ` in each `R_j` is `{ḡ}`, then so is the vertex of `ḡ` in the substitution
of the fillings `R_j` into the branches of `T` inside `P_T`. -/
theorem card_vertexOf_familySubstitution_branchTreeIn_eq_one_of_forall
    (h1 : ∀ j, ((R j).data.vertexOf ((R j).data.inv ((R j).data.leg 0))).card = 1) :
    ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).vertexOf
      ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).inv ((T.plabicData.familySubstitution
          (T.branchTreeIn hG) R (T.isPlabicGraph_plabicData hG)).leg 0))).card = 1 := by
  classical
  have hdisj := T.pairwise_disjoint_branchTreeIn_darts hG
  set S := T.plabicData.familySubstitution (T.branchTreeIn hG) R
    (T.isPlabicGraph_plabicData hG)
  have hx₀ : ((S.inv (S.leg 0) : substDarts _ _) : T.Dart ⊕ Σ j, (R j).Dart) =
      .inl ⟨.inr .gBar, hb⟩ := coe_familySubstitution_branchTreeIn_inv_leg hG hb
  have hmem : ∀ z : substDarts (T.branchTreeIn hG) R, z ∈ S.vertexOf (S.inv (S.leg 0)) ↔
      (substRot (T.branchTreeIn hG) R).SameCycle (.inl ⟨.inr .gBar, hb⟩) z :=
    mem_vertexOf_familySubstitution_branchTreeIn_inv_leg_iff hG hb
  rw [card_eq_one]
  refine ⟨_, eq_singleton_iff_unique_mem.2 ⟨S.self_mem_vertexOf _, fun z hz => ?_⟩⟩
  have hsc := (hmem z).1 hz
  set j₀ : Fin T.intervalLength := ⟨0, T.one_le_intervalLength⟩
  have hK := sameCycle_substRot_gBar_inr hG hb (R := R) (j := j₀) (Perm.SameCycle.refl _ _)
  rw [← attachDart_branchTreeIn hG hb j₀] at hK
  have horb := substRot_orbit_of_sameCycle hdisj (Perm.SameCycle.refl _ _) (hK.symm.trans hsc)
  have hz2 := z.2
  rcases hzc : (z : T.Dart ⊕ Σ j, (R j).Dart) with e | ⟨j, w⟩
  · rw [hzc] at horb hz2
    simp only [Sum.elim_inl] at horb
    have he : T.plabicData.rot.SameCycle ⟨.inr .gBar, hb⟩ e :=
      (T.plabicData.vertexOf_eq_vertexOf_iff).1
        (horb.trans (T.branchTreeIn_root hG hb j₀)).symm
    rcases T.eq_gBar_or_of_sameCycle hG hb he with rfl | ⟨d, hd, -, rfl⟩
    · exact Subtype.ext (hzc.trans hx₀.symm)
    · exfalso
      obtain ⟨i, hi, hdi⟩ := T.exists_mem_branchDarts hd
      refine (inl_mem_substDarts _ _).1 hz2 ⟨i, hi⟩ ?_
      rw [RootedTree.branchTreeIn_darts]
      exact mem_image_of_mem _ hdi
  · exfalso
    rw [hzc] at horb hz2
    simp only [Sum.elim_inr] at horb
    obtain ⟨-, hw⟩ := horb
    rw [attachDart_branchTreeIn hG hb] at hw
    have hwm := (RotationSystem.mem_vertexOf _).2 hw
    obtain ⟨a, ha⟩ := card_eq_one.1 (h1 j)
    have e₁ := mem_singleton.1 (ha ▸ hwm)
    have e₂ := mem_singleton.1 (ha ▸ (R j).data.self_mem_vertexOf
      ((R j).data.inv ((R j).data.leg 0)))
    have hc := (inr_mem_substDarts _ _).1 hz2
    exact ((T.branchTreeIn hG j).not_isCutDart_iff
      (T.not_isBoundaryVertex_branchTreeIn_root hG hb j)).1 hc |>.2.2 (e₁.trans e₂.symm)

/-- The vertex of `ḡ` in the substitution of the fillings `R_j` into the branches of `T` inside
`P_T` is `{ḡ}` if and only if the vertex of `ḡ` in each `R_j` is `{ḡ}`. -/
theorem card_vertexOf_familySubstitution_branchTreeIn_eq_one_iff :
    ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).vertexOf
      ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).inv ((T.plabicData.familySubstitution
          (T.branchTreeIn hG) R (T.isPlabicGraph_plabicData hG)).leg 0))).card = 1 ↔
      ∀ j, ((R j).data.vertexOf ((R j).data.inv ((R j).data.leg 0))).card = 1 :=
  ⟨card_vertexOf_inv_leg_eq_one_of_card_familySubstitution_branchTreeIn hG hb,
    card_vertexOf_familySubstitution_branchTreeIn_eq_one_of_forall hG hb⟩

end BranchSubstitution

/-! ### A tree is collapsible iff its branches are -/

section CollapsibleBranches

open PlabicGraph

/-- Irreducibility is invariant under isomorphism. -/
private theorem isIrreducible_of_isomorphic {b' : ℕ} {ε : Fin 2} {A B : PlabicGraph b'}
    (hAB : A.Isomorphic B) (hB : IsIrreducible ε B) : IsIrreducible ε A :=
  fun Q h => hB Q (IsReductionStep.of_isomorphic (PlabicData.Isomorphic.symm _ hAB) h)

/-- A sequence of reduction steps from a graph can be started at an isomorphic graph. -/
private theorem exists_reflTransGen_of_isomorphic {b' : ℕ} {ε : Fin 2} {A B C : PlabicGraph b'}
    (hAB : A.Isomorphic B) (h : Relation.ReflTransGen (IsReductionStep ε) B C) :
    ∃ C', Relation.ReflTransGen (IsReductionStep ε) A C' ∧ C'.Isomorphic C := by
  rcases h.cases_head with rfl | ⟨D, hBD, hDC⟩
  · exact ⟨A, .refl, hAB⟩
  · exact ⟨C, .head (IsReductionStep.of_isomorphic hAB hBD) hDC, PlabicData.Isomorphic.refl _⟩

/-- Isomorphic plabic graphs with one boundary vertex have vertices of `ḡ` of the same size. -/
private theorem card_vertexOf_inv_leg_eq_of_isomorphic {A B : PlabicGraph 1}
    (h : A.Isomorphic B) :
    (A.data.vertexOf (A.data.inv (A.data.leg 0))).card =
      (B.data.vertexOf (B.data.inv (B.data.leg 0))).card := by
  obtain ⟨θ⟩ := h
  rw [← θ.card_vertexOf, θ.map_inv, Iso.map_leg A.isPlabicGraph B.isPlabicGraph θ]

variable {T : G.RootedTree} (hG : G.IsPlabicGraph) (hb : ¬G.IsBoundaryVertex T.root)

include hb

omit hb in
/-- The involution of the substitution of the fillings `R_j` into the branches of `T` inside `P_T`
acts on the darts of a filling `R_j` as the involution of `R_j`. -/
theorem coe_familySubstitution_branchTreeIn_inv_inr {R : Fin T.intervalLength → PlabicGraph 1}
    {z : substDarts (T.branchTreeIn hG) R} {j : Fin T.intervalLength} {y : (R j).Dart}
    (h : (z : T.Dart ⊕ Σ j, (R j).Dart) = .inr ⟨j, y⟩) :
    (((T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).inv z : substDarts _ _) : T.Dart ⊕ Σ j, (R j).Dart) =
      .inr ⟨j, (R j).data.inv y⟩ := by
  rw [coe_familySubstitution_inv, h]
  rfl

/-- For an internal root, a dart at an internal vertex of the substitution of the fillings `R_j`
into the branches of `T` inside `P_T`, other than `ḡ`, comes from a filling. -/
theorem exists_coe_eq_inr_of_not_isBoundaryVertex_familySubstitution_branchTreeIn
    {R : Fin T.intervalLength → PlabicGraph 1}
    (hS : (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).IsPlabicGraph)
    {z : substDarts (T.branchTreeIn hG) R}
    (hz : ¬(T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).IsBoundaryVertex
        ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
          (T.isPlabicGraph_plabicData hG)).vertexOf z))
    (hne : z ≠ (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).inv ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).leg 0)) :
    ∃ j y, (z : T.Dart ⊕ Σ j, (R j).Dart) = .inr ⟨j, y⟩ := by
  set S := T.plabicData.familySubstitution (T.branchTreeIn hG) R
    (T.isPlabicGraph_plabicData hG)
  rcases hzc : (z : T.Dart ⊕ Σ j, (R j).Dart) with e | ⟨j, y⟩
  · exfalso
    rcases familySubstitution_branchTreeIn_inl_cases hG hb hzc with h | h | h
    · exact hz (S.isBoundaryVertex_vertexOf_of_mem h)
    · exact hz (h ▸ S.vertexOf_mem_boundaryVertices.1 (hS.bvertex_mem 0))
    · exact hne h
  · exact ⟨j, y, rfl⟩

/-- For an internal root, a removable bivalent vertex of the substitution of the fillings `R_j`
into the branches of `T` inside `P_T`, away from `ḡ`, gives a reduction step of one `R_j`. -/
theorem exists_isReductionStep_of_isBivalentRemovable_familySubstitution_branchTreeIn
    {R : Fin T.intervalLength → PlabicGraph 1}
    (hS : (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).IsPlabicGraph)
    {d : substDarts (T.branchTreeIn hG) R}
    (hd : (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).IsBivalentRemovable d)
    (hside : (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).inv ((T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).leg 0) ∉
      (T.plabicData.familySubstitution (T.branchTreeIn hG) R
        (T.isPlabicGraph_plabicData hG)).vertexOf d) :
    ∃ j Q, IsReductionStep 1 (R j) Q := by
  classical
  have hdisj := T.pairwise_disjoint_branchTreeIn_darts hG
  have hinj := intervalEnd_injective hdisj
  set S := T.plabicData.familySubstitution (T.branchTreeIn hG) R
    (T.isPlabicGraph_plabicData hG) with hSdef
  have hbj := T.not_isBoundaryVertex_branchTreeIn_root hG hb
  obtain ⟨j, y, hdy⟩ := exists_coe_eq_inr_of_not_isBoundaryVertex_familySubstitution_branchTreeIn
    hG hb hS hd.not_isBoundaryVertex (fun h => hside (h ▸ S.self_mem_vertexOf d))
  have hdc : ¬(T.branchTreeIn hG j).IsCutDart (R j) y := by
    have := d.2
    rwa [hdy] at this
  obtain ⟨hyB, hyl, -⟩ := ((T.branchTreeIn hG j).not_isCutDart_iff (hbj j)).1 hdc
  have hyint := not_isBoundaryVertex_of_ne_leg hyB hyl
  by_cases hsc : (R j).data.rot.SameCycle ((R j).data.inv ((R j).data.leg 0)) y
  · refine (hside ((RotationSystem.mem_vertexOf _).2 ?_)).elim
    change (firstReturnPerm (substRot _ R) (substDarts _ R)).SameCycle _ _
    rw [sameCycle_firstReturnPerm_iff, hdy, coe_familySubstitution_branchTreeIn_inv_leg hG hb]
    exact (sameCycle_substRot_gBar_inr hG hb hsc).symm
  have hya : ¬(R j).data.rot.SameCycle y ((T.branchTreeIn hG j).attachDart (R j)) := by
    rw [attachDart_branchTreeIn hG hb]
    exact fun h => hsc h.symm
  have hnc : ∀ w ∈ (R j).data.vertexOf y, ¬(T.branchTreeIn hG j).IsCutDart (R j) w := by
    intro w hw
    have hwv := (R j).data.vertexOf_eq_of_mem hw
    refine not_isCutDart_of_not_sameCycle _ (hbj j) (hwv ▸ hyint) fun h => hsc ?_
    exact h.trans ((RotationSystem.mem_vertexOf _).1 hw).symm
  have hcard := card_vertexOf_familySubstitution_of_not_sameCycle
    (T.isPlabicGraph_plabicData hG) hdisj hdy hya hnc
  have hdinv : ((S.inv d : substDarts _ _) : T.Dart ⊕ Σ j, (R j).Dart) =
      .inr ⟨j, (R j).data.inv y⟩ := coe_familySubstitution_branchTreeIn_inv_inr hG hdy
  have hrot : ((S.rot d : substDarts _ _) : T.Dart ⊕ Σ j, (R j).Dart) =
      .inr ⟨j, (R j).data.rot y⟩ := by
    have hne : y ≠ (T.branchTreeIn hG j).attachDart (R j) := by
      rintro rfl
      exact hya (Perm.SameCycle.refl _ _)
    rw [hSdef, coe_familySubstitution_rot,
      coe_firstReturn_of_apply_mem (by
        rw [hdy, substRot_inr_of_ne hinj hne]
        exact hnc _ ((R j).data.rot_mem_vertexOf y)),
      hdy, substRot_inr_of_ne hinj hne]
  have hy : (R j).data.IsBivalentRemovable y :=
    ⟨hyint, hcard ▸ hd.card_vertexOf, fun h => hd.inv_ne_rot (Subtype.ext (by
      rw [hdinv, hrot, h]))⟩
  refine ⟨j, ⟨_, _, isPlabicGraph_bivalentRemoval (R j).isPlabicGraph hy⟩,
    Or.inl ⟨y, hy, fun _ i hi => hsc ?_, PlabicData.Isomorphic.refl _⟩⟩
  rw [Subsingleton.elim i 0] at hi
  exact ((RotationSystem.mem_vertexOf _).1 hi).symm

/-- For an internal root, a contractible edge of the substitution of the fillings `R_j` into the
branches of `T` inside `P_T` gives a reduction step of one `R_j`. -/
theorem exists_isReductionStep_of_isContractibleEdge_familySubstitution_branchTreeIn
    {R : Fin T.intervalLength → PlabicGraph 1}
    (hS : (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).IsPlabicGraph)
    {d : substDarts (T.branchTreeIn hG) R}
    (he : (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).IsContractibleEdge d) :
    ∃ j Q, IsReductionStep 1 (R j) Q := by
  classical
  have hdisj := T.pairwise_disjoint_branchTreeIn_darts hG
  set S := T.plabicData.familySubstitution (T.branchTreeIn hG) R
    (T.isPlabicGraph_plabicData hG) with hSdef
  have hbj := T.not_isBoundaryVertex_branchTreeIn_root hG hb
  have hnotcut : ∀ (z : substDarts (T.branchTreeIn hG) R) j y,
      (z : T.Dart ⊕ Σ j, (R j).Dart) = .inr ⟨j, y⟩ → ¬(T.branchTreeIn hG j).IsCutDart (R j) y := by
    intro z j y h
    have := z.2
    rwa [h] at this
  have hdne : d ≠ S.inv (S.leg 0) := by
    rintro rfl
    refine (S.vertexOf_mem_internalVertices.1 he.inv_mem_internalVertices) ?_
    rw [hS.inv_involutive]
    exact S.vertexOf_mem_boundaryVertices.1 (hS.bvertex_mem 0)
  obtain ⟨j, y, hdy⟩ := exists_coe_eq_inr_of_not_isBoundaryVertex_familySubstitution_branchTreeIn
    hG hb hS (S.vertexOf_mem_internalVertices.1 he.mem_internalVertices) hdne
  have hdinv : ((S.inv d : substDarts _ _) : T.Dart ⊕ Σ j, (R j).Dart) =
      .inr ⟨j, (R j).data.inv y⟩ := coe_familySubstitution_branchTreeIn_inv_inr hG hdy
  obtain ⟨hyB, hyl, -⟩ := ((T.branchTreeIn hG j).not_isCutDart_iff (hbj j)).1
    (hnotcut d j y hdy)
  obtain ⟨hyB', hyl', -⟩ := ((T.branchTreeIn hG j).not_isCutDart_iff (hbj j)).1
    (hnotcut (S.inv d) j _ hdinv)
  have he' : (R j).data.IsContractibleEdge y := by
    refine ⟨fun h => he.vertexOf_ne ((S.vertexOf_eq_vertexOf_iff).2 ?_),
      (R j).data.vertexOf_mem_internalVertices.2 (not_isBoundaryVertex_of_ne_leg hyB hyl),
      (R j).data.vertexOf_mem_internalVertices.2 (not_isBoundaryVertex_of_ne_leg hyB' hyl'),
      ?_⟩
    · change (firstReturnPerm (substRot _ R) (substDarts _ R)).SameCycle _ _
      rw [sameCycle_firstReturnPerm_iff, hdy, hdinv]
      exact sameCycle_substRot_inr_of_sameCycle hdisj
        ((R j).data.vertexOf_eq_vertexOf_iff.1 h)
    · have : S.colour (S.inv d) = S.colour d := he.colour_inv
      rwa [hSdef, familySubstitution_colour, familySubstitution_colour, ← hSdef, hdinv, hdy]
        at this
  exact ⟨j, ⟨_, _, (R j).isPlabicGraph.contractEdge he'⟩,
    Or.inr ⟨y, he', PlabicData.Isomorphic.refl _⟩⟩

/-- If every filling `R_j` is `1`-irreducible, so is their substitution into the branches of `T`
inside `P_T`. -/
theorem isIrreducible_familySubstitution_branchTreeIn {R : Fin T.intervalLength → PlabicGraph 1}
    (hirr : ∀ j, IsIrreducible 1 (R j))
    (hS : (T.plabicData.familySubstitution (T.branchTreeIn hG) R
      (T.isPlabicGraph_plabicData hG)).IsPlabicGraph) :
    IsIrreducible 1 ⟨_, _, hS⟩ := by
  intro Q' hstep
  rcases hstep with ⟨d, hd, hside, -⟩ | ⟨d, he, -⟩
  · obtain ⟨j, Q, hQ⟩ :=
      exists_isReductionStep_of_isBivalentRemovable_familySubstitution_branchTreeIn hG hb hS hd
        (hside rfl 0)
    exact hirr j Q hQ
  · obtain ⟨j, Q, hQ⟩ :=
      exists_isReductionStep_of_isContractibleEdge_familySubstitution_branchTreeIn hG hb hS he
    exact hirr j Q hQ

/-- A rooted tree with an internal root of colour `c` is collapsible iff `P_T` is
`{M2, M3}`-equivalent to `L_c`. -/
theorem RootedTree.isCollapsible_iff_moveEquivalent {c : Shade}
    (hc : ∀ d ∈ T.root, G.colour d = c) :
    T.IsCollapsible ↔ MoveEquivalent {.m2, .m3} (T.toPlabicGraph hG) (lollipopPlabicGraph c) := by
  constructor
  · rintro ⟨c', h⟩
    rcases h.root_cases with ⟨-, hc'⟩ | ⟨hb', -⟩
    · obtain rfl : c' = c :=
        (hc' _ T.intervalStart_mem_root).symm.trans (hc _ T.intervalStart_mem_root)
      exact h.moveEquivalent
    · exact absurd hb' hb
  · exact fun h => ⟨c, T.isPlabicGraph_plabicData hG, h, Or.inl ⟨hb, hc⟩⟩

omit hb in
/-- **A tree is collapsible iff its branches are.** Let `T = (v, W)` be a rooted tree of a plabic
graph `G` with `v` internal and interval `(a₁, …, a_k)`. Then `T` is a collapsible tree if and only
if, for every `j ∈ [1, k]`, the branch of `T` at `a_j` is a collapsible tree. Here the branch at
`a_j = σ^i a₁` is `T.branchTree hG hi` with `i = j - 1`. -/
@[cluster_algebras "lem_collapsible_branches"]
theorem RootedTree.isCollapsible_iff_forall_isCollapsible_branchTree (T : G.RootedTree)
    (hb : ¬G.IsBoundaryVertex T.root) :
    T.IsCollapsible ↔ ∀ i (hi : i < T.intervalLength), (T.branchTree hG hi).IsCollapsible := by
  classical
  set c := G.colour T.intervalStart
  have hc : ∀ d ∈ T.root, G.colour d = c := fun d hd =>
    hG.colour_eq_of_mem_vertexOf (by rwa [← T.root_eq_vertexOf_intervalStart])
      (by rwa [← T.root_eq_vertexOf_intervalStart])
  have hQ := T.isPlabicGraph_plabicData hG
  have hdisj := T.pairwise_disjoint_branchTreeIn_darts hG
  choose R hR hirr using fun i : Fin T.intervalLength =>
    exists_reflTransGen_isIrreducible 1 ((T.branchTree hG i.isLt).toPlabicGraph hG)
  have hfrozen : ∀ i : Fin T.intervalLength,
      MoveEquivalent {.m2, .m3} ((T.branchTree hG i.isLt).toPlabicGraph hG)
        (lollipopPlabicGraph c) ↔
      ((R i).data.vertexOf ((R i).data.inv ((R i).data.leg 0))).card = 1 :=
    fun i => (T.branchTree hG i.isLt).moveEquivalent_lollipopPlabicGraph_iff hG hb hc (hR i)
      (hirr i)
  have θ : ∀ i, ((T.branchTreeIn hG i).toPlabicGraph hQ).data.Iso
      ((T.branchTree hG i.isLt).toPlabicGraph hG).data := fun i =>
    Classical.choice (PlabicData.Isomorphic.symm _ (T.branchTreeIn_plabicData_isomorphic hG hb i))
  obtain ⟨θ₁⟩ := familySubstitution_isomorphic hQ hdisj θ
  have hP₀ := isPlabicGraph_familySubstitution_toPlabicGraph (T := T.branchTreeIn hG) hQ hdisj
  have hP := θ₁.isPlabicGraph hP₀ (familySubstitution_legs_notMem hQ hdisj _)
  obtain ⟨hS, C, hC, hCS⟩ := familySubstitution_reflTransGen_isReductionStep hQ hdisj
    (T.not_isBoundaryVertex_branchTreeIn_root hG hb)
    (P := fun i => (T.branchTree hG i.isLt).toPlabicGraph hG) hR hP
  obtain ⟨θ₀⟩ := isomorphic_familySubstitution_toPlabicGraph (T := T.branchTreeIn hG) hQ hdisj
  have hiso : (T.toPlabicGraph hG).Isomorphic ⟨_, _, hP⟩ := ⟨θ₀.trans θ₁⟩
  obtain ⟨C', hC', hC'C⟩ := exists_reflTransGen_of_isomorphic hiso hC
  have hC'S : C'.Isomorphic ⟨_, _, hS⟩ := PlabicData.Isomorphic.trans _ hC'C hCS
  have hirrC' := isIrreducible_of_isomorphic hC'S
    (isIrreducible_familySubstitution_branchTreeIn hG hb hirr hS)
  rw [T.isCollapsible_iff_moveEquivalent hG hb hc]
  refine (T.moveEquivalent_lollipopPlabicGraph_iff hG hb hc hC' hirrC').trans ?_
  rw [card_vertexOf_inv_leg_eq_of_isomorphic hC'S]
  refine (card_vertexOf_familySubstitution_branchTreeIn_eq_one_iff hG hb).trans ?_
  exact ⟨fun h i hi => ((T.branchTree hG hi).isCollapsible_iff_moveEquivalent hG hb hc).2
      ((hfrozen ⟨i, hi⟩).2 (h ⟨i, hi⟩)),
    fun h i => (hfrozen i).1
      (((T.branchTree hG i.isLt).isCollapsible_iff_moveEquivalent hG hb hc).1 (h i i.isLt))⟩

end CollapsibleBranches

end PlabicData

end ClusterAlgebras
