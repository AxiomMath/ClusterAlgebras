/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.ReducedCollapse

/-!
# Lollipops and boundary trees persist under local moves

Let `G` and `G'` be plabic graphs with `b` boundary vertices and `G ∼ G'`, and let `i` be a label.
If `G` has a lollipop at `i` or a collapsible tree with root `β(i)`, then so does `G'`. This
replaces FWZ's argument "local moves preserve the number of internal faces, so no (M1) move
appears, and the component of `i` is a tree".

The proof follows the sequence of moves. Both alternatives are captured by one condition: `G` has a
rooted tree `T` with root `β(i)` whose plabic graph `P_T` is `{M2, M3}`-equivalent to a lollipop
graph `L_c`. A rooted tree with `|W| = 1` and boundary root is a lollipop, and a collapsible tree
with root `β(i)` has `|W| ≥ 2`. Isomorphisms and square moves carry such a tree to such a tree. A
removal of a bivalent vertex or a contraction of an edge that touches the tree acts on `P_T` by the
same move; one that avoids the tree leaves it unchanged. In the reverse direction, the tree of the
smaller graph lifts to the larger one: a bivalent vertex inserted on an edge of the tree, or a
vertex of the tree split in two, is inserted or split in `P_T` as well.

## Main results

* `ClusterAlgebras.PlabicGraph.MoveEquivalent.exists_isLollipop_or_isCollapsible`: lollipops and
  boundary trees persist under local moves.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.
* A plabic graph `R` with one boundary vertex and one face is the plabic graph of its *full tree*,
  the rooted tree with root `β(1)` and all internal vertices. A tree of a plabic graph `K` with
  root `β(i)` is then produced from such an `R` and a map from the darts of `R` outside `B` to the
  darts of `K` that respects the involutions, the rotations and the colours, and sends the leg to
  `g_i` (`RootedTree.IsEmbedding`). For the moves inside a tree, `R` is the move applied to `P_T`.
* The colour of a dart at a boundary vertex carries no information. The embedding asks for equal
  colours on all the darts of the tree, the leg included; the colour of `g_i` is therefore first
  changed in an isomorphic copy of `K`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

/-! ### The full tree of a plabic graph with one boundary vertex and one face -/

section FullTree

variable {Y : Type} [Fintype Y] [DecidableEq Y] {R : PlabicData Y 1}

namespace IsPlabicGraph

variable (hR : R.IsPlabicGraph)

include hR

/-- A boundary vertex of a plabic graph with one boundary vertex is `β(1)`. -/
private theorem eq_bvertex_zero_of_isBoundaryVertex' {v : Finset Y} (hv : v ∈ R.vertices)
    (hb : R.IsBoundaryVertex v) : v = R.bvertex 0 := by
  obtain ⟨j, hj⟩ := hR.exists_bvertex_eq v (R.mem_boundaryVertices.2 ⟨hv, hb⟩)
  rw [← hj, Subsingleton.elim j 0]

private theorem isBoundaryVertex_bvertex_zero' : R.IsBoundaryVertex (R.bvertex 0) :=
  R.vertexOf_mem_boundaryVertices.1 (hR.bvertex_mem 0)

/-- A dart outside `B` at a boundary vertex is the leg. -/
private theorem eq_leg_zero_of_notMem_bdry' {d : Y} (hd : d ∉ R.bdry)
    (hb : R.IsBoundaryVertex (R.vertexOf d)) : d = R.leg 0 := by
  have h := hR.eq_bvertex_zero_of_isBoundaryVertex' (R.vertexOf_mem_vertices d) hb
  exact DiskMap.eq_of_notMem_bdry hR.boundaryVertex_card hR.isBoundaryVertex_bvertex_zero'
    (by rw [bvertex] at h; rw [← h]; exact R.self_mem_vertexOf d) (R.self_mem_vertexOf _) hd
    (hR.leg_notMem_bdry 0)

private theorem not_isBoundaryVertex_vertexOf_inv_leg_zero' :
    ¬R.IsBoundaryVertex (R.vertexOf (R.inv (R.leg 0))) := fun hb =>
  hR.inv_ne _ (hR.eq_leg_zero_of_notMem_bdry'
    (fun h => hR.leg_notMem_bdry 0 (hR.inv_mem_bdry_iff.1 h)) hb)

private theorem mem_treeDarts_internalVertices' {d : Y} :
    d ∈ R.treeDarts R.internalVertices ↔ d ∉ R.bdry := by
  rw [mem_treeDarts]
  refine ⟨fun h => h.1, fun hd => ⟨hd, ?_⟩⟩
  by_cases hb : R.IsBoundaryVertex (R.vertexOf d)
  · obtain rfl := hR.eq_leg_zero_of_notMem_bdry' hd hb
    exact Or.inr (R.vertexOf_mem_internalVertices.2 hR.not_isBoundaryVertex_vertexOf_inv_leg_zero')
  · exact Or.inl (R.vertexOf_mem_internalVertices.2 hb)

private theorem rot_leg_zero_mem_bdry' : R.rot (R.leg 0) ∈ R.bdry := by
  by_contra h
  have := hR.eq_leg_zero_of_notMem_bdry' h
    (by rw [R.vertexOf_rot]; exact hR.isBoundaryVertex_bvertex_zero')
  exact DiskMap.rot_ne_of_isBoundaryVertex hR.boundaryVertex_card
    hR.isBoundaryVertex_bvertex_zero' this

private theorem rot_symm_leg_zero_mem_bdry' : R.rot.symm (R.leg 0) ∈ R.bdry := by
  by_contra h
  have hb : R.IsBoundaryVertex (R.vertexOf (R.rot.symm (R.leg 0))) := by
    rw [R.vertexOf_eq_of_mem (R.rot_symm_mem_vertexOf _)]; exact hR.isBoundaryVertex_bvertex_zero'
  have := hR.eq_leg_zero_of_notMem_bdry' h hb
  apply DiskMap.rot_ne_of_isBoundaryVertex hR.boundaryVertex_card
    hR.isBoundaryVertex_bvertex_zero'
  conv_lhs => rw [← this]
  exact Equiv.apply_symm_apply _ _

private theorem bvertex_zero_eq_rot_rot' :
    R.bvertex 0 = {R.leg 0, R.rot (R.leg 0), R.rot (R.rot (R.leg 0))} := by
  have hb := hR.isBoundaryVertex_bvertex_zero'
  have hne1 := DiskMap.rot_ne_of_isBoundaryVertex hR.boundaryVertex_card hb
  have hne2 := DiskMap.rot_rot_ne_of_isBoundaryVertex hR.boundaryVertex_card hb
  symm
  refine eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact R.self_mem_vertexOf _
    · exact R.rot_mem_vertexOf _
    · rw [bvertex, ← R.vertexOf_rot]
      exact R.rot_mem_vertexOf _
  · rw [(hR.boundaryVertex_card _ (hR.bvertex_mem 0)).1, card_insert_of_notMem, card_pair]
    · exact fun h => hne1 (R.rot.injective h).symm
    · simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hne1.symm, hne2.symm⟩

/-- At `β(1)`, `σ² g₁ = σ⁻¹ g₁`. -/
private theorem rot_rot_leg_zero' : R.rot (R.rot (R.leg 0)) = R.rot.symm (R.leg 0) := by
  have hb := hR.isBoundaryVertex_bvertex_zero'
  have hne1 := DiskMap.rot_ne_of_isBoundaryVertex hR.boundaryVertex_card hb
  have hne2 := DiskMap.rot_rot_ne_of_isBoundaryVertex hR.boundaryVertex_card hb
  have hmem : R.rot.symm (R.leg 0) ∈ R.bvertex 0 := R.rot_symm_mem_vertexOf _
  rw [hR.bvertex_zero_eq_rot_rot'] at hmem
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with h | h | h
  · exact (hne1 (by simpa using (congrArg R.rot h).symm)).elim
  · exfalso
    apply hne2
    conv_rhs => rw [← Equiv.apply_symm_apply R.rot (R.leg 0)]
    rw [← h]
  · exact h.symm

/-- `β(1) = {g₁, σ g₁, σ⁻¹ g₁}`. -/
private theorem bvertex_zero_eq' :
    R.bvertex 0 = {R.leg 0, R.rot (R.leg 0), R.rot.symm (R.leg 0)} := by
  rw [← hR.rot_rot_leg_zero']
  exact hR.bvertex_zero_eq_rot_rot'

/-- The darts of `B` are `σ g₁` and `σ⁻¹ g₁`. -/
private theorem mem_bdry_iff_eq' {y : Y} :
    y ∈ R.bdry ↔ y = R.rot (R.leg 0) ∨ y = R.rot.symm (R.leg 0) := by
  constructor
  · intro hy
    have hb := R.isBoundaryVertex_vertexOf_of_mem hy
    have hv := hR.eq_bvertex_zero_of_isBoundaryVertex' (R.vertexOf_mem_vertices y) hb
    have hmem : y ∈ R.bvertex 0 := hv ▸ R.self_mem_vertexOf y
    rw [hR.bvertex_zero_eq'] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact absurd (h ▸ hy) (hR.leg_notMem_bdry 0)
    exacts [.inl h, .inr h]
  · rintro (rfl | rfl)
    · exact hR.rot_leg_zero_mem_bdry'
    · exact hR.rot_symm_leg_zero_mem_bdry'

private theorem rot_leg_zero_ne_rot_symm_leg_zero' :
    R.rot (R.leg 0) ≠ R.rot.symm (R.leg 0) := fun h =>
  DiskMap.rot_rot_ne_of_isBoundaryVertex hR.boundaryVertex_card hR.isBoundaryVertex_bvertex_zero'
    (by rw [h, Equiv.apply_symm_apply])

private theorem bdry_eq' : R.bdry = {R.rot (R.leg 0), R.rot.symm (R.leg 0)} := by
  ext y
  rw [hR.mem_bdry_iff_eq', mem_insert, mem_singleton]

private theorem card_bdry' : R.bdry.card = 2 := by
  rw [hR.bdry_eq', card_pair hR.rot_leg_zero_ne_rot_symm_leg_zero']

/-- The involution exchanges the two darts of `B`. -/
private theorem inv_rot_symm_leg_zero' : R.inv (R.rot.symm (R.leg 0)) = R.rot (R.leg 0) := by
  have hB := hR.inv_mem_bdry _ hR.rot_symm_leg_zero_mem_bdry'
  rcases hR.mem_bdry_iff_eq'.1 hB with h | h
  · exact h
  · exact absurd h (hR.inv_ne _)

private theorem inv_rot_leg_zero' : R.inv (R.rot (R.leg 0)) = R.rot.symm (R.leg 0) := by
  rw [← hR.inv_rot_symm_leg_zero', hR.inv_involutive]

private theorem card_vertices_eq' : R.vertices.card = R.internalVertices.card + 1 := by
  have hu : R.vertices = R.boundaryVertices ∪ R.internalVertices := by
    ext v
    simp only [mem_union, R.mem_boundaryVertices, R.mem_internalVertices]
    tauto
  have hd : Disjoint R.boundaryVertices R.internalVertices := disjoint_left.2 fun v h1 h2 =>
    (R.mem_internalVertices.1 h2).2 (R.mem_boundaryVertices.1 h1).2
  rw [hu, card_union_of_disjoint hd, hR.card_boundaryVertices]
  omega

variable (hf : R.faces.card = 1)

include hf

private theorem card_image_edgeOf_internalVertices' :
    ((R.treeDarts R.internalVertices).image R.edgeOf).card = R.internalVertices.card := by
  have hF : R.faceOrbits.card = 2 := by
    have := card_erase_of_mem hR.toIsDiskMap.exterior_mem_faceOrbits
    rw [← DiskMap.faces, hf] at this
    have h1 := card_pos.2 ⟨_, hR.toIsDiskMap.exterior_mem_faceOrbits⟩
    omega
  have heuler := hR.euler
  have hV := hR.card_vertices_eq'
  have hE := R.card_eq_two_mul_card_edges hR.inv_involutive hR.inv_ne
  have hS : R.treeDarts R.internalVertices = univ.filter (· ∉ R.bdry) := by
    ext d; rw [hR.mem_treeDarts_internalVertices', mem_filter]; simp
  have hS2 := R.card_eq_two_mul_card_image_edgeOf hR.inv_involutive hR.inv_ne
    (S := R.treeDarts R.internalVertices) fun d hd => by
      rw [hR.mem_treeDarts_internalVertices'] at hd ⊢
      exact fun h => hd (hR.inv_mem_bdry_iff.1 h)
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset Y)) (· ∉ R.bdry)
  have hB : (univ.filter fun d => ¬(d ∉ R.bdry)).card = 2 := by
    rw [← hR.card_bdry']; congr 1; ext d; simp
  rw [← hS, hB, card_univ] at hsplit
  rw [hF, hV] at heuler
  omega

/-- The **full tree** of a plabic graph `R` with one boundary vertex and one face: the rooted tree
with root `β(1)` whose non-root vertices are all the internal vertices of `R`. -/
private noncomputable def fullTree : R.RootedTree where
  root := R.bvertex 0
  nonRoot := R.internalVertices
  root_mem_vertices := R.vertexOf_mem_vertices _
  nonRoot_nonempty :=
    ⟨_, R.vertexOf_mem_internalVertices.2 hR.not_isBoundaryVertex_vertexOf_inv_leg_zero'⟩
  nonRoot_subset := Subset.rfl
  root_notMem_nonRoot h := (R.mem_internalVertices.1 h).2 hR.isBoundaryVertex_bvertex_zero'
  vertexOf_inv_mem d _ := by
    by_cases hb : R.IsBoundaryVertex (R.vertexOf (R.inv d))
    · rw [hR.eq_bvertex_zero_of_isBoundaryVertex' (R.vertexOf_mem_vertices _) hb]
      exact mem_insert_self _ _
    · exact mem_insert_of_mem (R.vertexOf_mem_internalVertices.2 hb)
  exists_interval := by
    refine ⟨R.leg 0, R.self_mem_vertexOf _, 1, le_rfl, ?_, fun d hd => ?_, ?_⟩
    · rw [(hR.boundaryVertex_card _ (hR.bvertex_mem 0)).1]; norm_num
    · rw [hR.mem_treeDarts_internalVertices']
      constructor
      · intro hdB
        refine ⟨0, one_pos, ?_⟩
        rw [pow_zero, Equiv.Perm.one_apply]
        refine (hR.eq_leg_zero_of_notMem_bdry' hdB ?_).symm
        rw [R.vertexOf_eq_of_mem hd]
        exact hR.isBoundaryVertex_bvertex_zero'
      · rintro ⟨j, hj, rfl⟩
        obtain rfl : j = 0 := by omega
        exact hR.leg_notMem_bdry 0
    · rw [hR.mem_treeDarts_internalVertices', not_not]
      exact hR.rot_symm_leg_zero_mem_bdry'
  card_image_edgeOf := hR.card_image_edgeOf_internalVertices' hf
  reflTransGen_treeAdj u hu := by
    have key : ∀ e, R.Reach (R.leg 0) e → Relation.ReflTransGen
        (R.TreeAdj R.internalVertices) (R.bvertex 0) (R.vertexOf e) := by
      intro e he
      induction he with
      | refl => exact .refl
      | rot _ ih => rwa [R.vertexOf_rot]
      | @inv e' _ ih =>
        by_cases heB : e' ∈ R.bdry
        · rw [hR.eq_bvertex_zero_of_isBoundaryVertex' (R.vertexOf_mem_vertices _)
            (R.isBoundaryVertex_vertexOf_of_mem (hR.inv_mem_bdry _ heB))]
        · exact ih.tail ⟨e', hR.mem_treeDarts_internalVertices'.2 heB, rfl, rfl⟩
    rcases mem_insert.1 hu with rfl | hu
    · exact .refl
    · obtain ⟨e, rfl⟩ := R.mem_vertices.1 (R.mem_internalVertices.1 hu).1
      exact key e (hR.reach _ _)

private theorem mem_fullTree_darts {d : Y} : d ∈ (hR.fullTree hf).darts ↔ d ∉ R.bdry :=
  hR.mem_treeDarts_internalVertices'

private theorem isBoundaryVertex_fullTree_root : R.IsBoundaryVertex (hR.fullTree hf).root :=
  hR.isBoundaryVertex_bvertex_zero'

private theorem fullTree_intervalStart : (hR.fullTree hf).intervalStart = R.leg 0 :=
  (hR.fullTree hf).intervalStart_eq_leg hR rfl

end IsPlabicGraph

/-- The dart of `R` corresponding to a dart of `P_T`, for the full tree `T` of `R`. -/
private def fullTreeDartFun (R : PlabicData Y 1) : Y ⊕ LollipopDart → Y
  | .inl d => d
  | .inr .e => R.rot.symm (R.leg 0)
  | .inr .eBar => R.rot (R.leg 0)
  | .inr _ => R.leg 0

namespace IsPlabicGraph

variable (hR : R.IsPlabicGraph) (hf : R.faces.card = 1)

include hR

private theorem fullTreeDartFun_bijective :
    Function.Bijective fun x : (hR.fullTree hf).Dart => fullTreeDartFun R x.1 := by
  have hb := hR.isBoundaryVertex_fullTree_root hf
  constructor
  · rintro ⟨d | (_ | _ | _ | _), hx⟩ ⟨d' | (_ | _ | _ | _), hy⟩ h <;>
      simp only [fullTreeDartFun] at h <;>
      first
        | exact absurd hb hx
        | exact absurd hb hy
        | rfl
        | skip
    · subst h; rfl
    · exact absurd hR.rot_symm_leg_zero_mem_bdry' (h ▸ (hR.mem_fullTree_darts hf).1 hx)
    · exact absurd hR.rot_leg_zero_mem_bdry' (h ▸ (hR.mem_fullTree_darts hf).1 hx)
    · exact absurd hR.rot_symm_leg_zero_mem_bdry' (h.symm ▸ (hR.mem_fullTree_darts hf).1 hy)
    · exact absurd h.symm hR.rot_leg_zero_ne_rot_symm_leg_zero'
    · exact absurd hR.rot_leg_zero_mem_bdry' (h.symm ▸ (hR.mem_fullTree_darts hf).1 hy)
    · exact absurd h hR.rot_leg_zero_ne_rot_symm_leg_zero'
  · intro y
    by_cases hy : y ∈ R.bdry
    · rcases hR.mem_bdry_iff_eq'.1 hy with rfl | rfl
      · exact ⟨⟨.inr .eBar, trivial⟩, rfl⟩
      · exact ⟨⟨.inr .e, trivial⟩, rfl⟩
    · exact ⟨⟨.inl y, (hR.mem_fullTree_darts hf).2 hy⟩, rfl⟩

/-- A plabic graph with one boundary vertex and one face is isomorphic to the plabic graph of its
full tree. -/
private noncomputable def fullTreeIso : (hR.fullTree hf).plabicData.Iso R :=
  have hb := hR.isBoundaryVertex_fullTree_root hf
  have hstart := hR.fullTree_intervalStart hf
  Iso.ofEquivOfMapLeg (Equiv.ofBijective _ (hR.fullTreeDartFun_bijective hf))
    (fun x => by
      simp only [Equiv.ofBijective_apply]
      rw [(hR.fullTree hf).coe_inv_plabicData hR]
      rcases x with ⟨d | (_ | _ | _ | _), hx⟩
      · rfl
      · exact hR.inv_rot_symm_leg_zero'.symm
      · exact hR.inv_rot_leg_zero'.symm
      · exact absurd hb hx
      · exact absurd hb hx)
    (fun x => by
      simp only [Equiv.ofBijective_apply]
      rw [(hR.fullTree hf).coe_rot_plabicData hR]
      rcases x with ⟨d | (_ | _ | _ | _), hx⟩
      · have hdB : d ∉ R.bdry := (hR.mem_fullTree_darts hf).1 hx
        simp only [RootedTree.rotAux, if_pos hb]
        split_ifs with h
        · rfl
        · have hrB : R.rot d ∈ R.bdry := by
            by_contra h'
            exact h ((hR.mem_fullTree_darts hf).2 h')
          have hvb : R.IsBoundaryVertex (R.vertexOf d) := by
            rw [← R.vertexOf_rot]; exact R.isBoundaryVertex_vertexOf_of_mem hrB
          rw [hR.eq_leg_zero_of_notMem_bdry' hdB hvb]
          rfl
      · simp only [RootedTree.rotAux, if_pos hb, hstart, fullTreeDartFun]
        exact (Equiv.apply_symm_apply _ _).symm
      · simp only [RootedTree.rotAux, fullTreeDartFun]
        exact hR.rot_rot_leg_zero'.symm
      · exact absurd hb hx
      · exact absurd hb hx)
    (fun x => by
      simp only [Equiv.ofBijective_apply]
      rw [RootedTree.mem_bdry_plabicData]
      rcases x with ⟨d | (_ | _ | _ | _), hx⟩
      · simp only [fullTreeDartFun, RootedTree.dartE, RootedTree.dartEBar, Subtype.mk.injEq,
          reduceCtorEq, or_self, iff_false]
        exact (hR.mem_fullTree_darts hf).1 hx
      · simp only [fullTreeDartFun, RootedTree.dartE, true_or, iff_true]
        exact hR.rot_symm_leg_zero_mem_bdry'
      · simp only [fullTreeDartFun, RootedTree.dartEBar, or_true, iff_true]
        exact hR.rot_leg_zero_mem_bdry'
      · exact absurd hb hx
      · exact absurd hb hx)
    (fun x hx => by
      rcases x with ⟨d | (_ | _ | _ | _), hxd⟩
      · rfl
      · exact absurd ⟨_, (hR.fullTree hf).plabicData.self_mem_vertexOf _,
          (RootedTree.mem_bdry_plabicData _).2 (Or.inl rfl)⟩ hx
      · exact absurd ⟨_, (hR.fullTree hf).plabicData.self_mem_vertexOf _,
          (RootedTree.mem_bdry_plabicData _).2 (Or.inr rfl)⟩ hx
      · exact absurd hb hxd
      · exact absurd hb hxd)
    (fun i => by
      rw [Subsingleton.elim i 0]
      simp only [Equiv.ofBijective_apply]
      change fullTreeDartFun R ((hR.fullTree hf).legDart : Y ⊕ LollipopDart) = R.leg 0
      rw [RootedTree.legDart, dif_pos hb]
      exact hstart)

end IsPlabicGraph

end FullTree

/-! ### Producing a boundary tree from a map of darts -/

section Transport

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b b' : ℕ}

/-- In a plabic graph, `σ(g_i) ∈ B`. -/
private theorem IsPlabicGraph.rot_leg_mem_bdry' {G : PlabicData H b} (hG : G.IsPlabicGraph)
    (i : Fin b) : G.rot (G.leg i) ∈ G.bdry := by
  have hb : G.IsBoundaryVertex (G.vertexOf (G.leg i)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  by_contra h
  exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hb
    (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hb (G.rot_mem_vertexOf _)
      (G.self_mem_vertexOf _) h (hG.leg_notMem_bdry i))

/-- In a plabic graph, `σ⁻¹(g_i) ∈ B`. -/
private theorem IsPlabicGraph.rot_symm_leg_mem_bdry' {G : PlabicData H b} (hG : G.IsPlabicGraph)
    (i : Fin b) : G.rot.symm (G.leg i) ∈ G.bdry := by
  have hb : G.IsBoundaryVertex (G.vertexOf (G.leg i)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  by_contra h
  have := DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hb (G.rot_symm_mem_vertexOf _)
    (G.self_mem_vertexOf _) h (hG.leg_notMem_bdry i)
  apply DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hb
  conv_lhs => rw [← this]
  exact Equiv.apply_symm_apply _ _

/-- The boundary vertex `β(i)` of a plabic graph is a boundary vertex. -/
private theorem IsPlabicGraph.isBoundaryVertex_bvertex' {G : PlabicData H b}
    (hG : G.IsPlabicGraph) (i : Fin b) : G.IsBoundaryVertex (G.bvertex i) :=
  G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

/-- A dart at an internal vertex is not a leg. -/
private theorem IsPlabicGraph.ne_leg_of_not_isBoundaryVertex' {G : PlabicData H b}
    (hG : G.IsPlabicGraph) {d : H} (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) (i : Fin b) :
    d ≠ G.leg i := by
  rintro rfl
  exact hd (hG.isBoundaryVertex_bvertex' i)

namespace RootedTree.IsEmbedding

variable {G : PlabicData H b} {G' : PlabicData H' b'} {T : G.RootedTree} {f : H → H'}

/-- The plabic graph of a transported tree is isomorphic to `P_T`, for boundary roots. -/
private theorem tree_plabicData_isomorphic_of_isBoundaryVertex (hf : T.IsEmbedding G' f)
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (hv : G.IsBoundaryVertex T.root)
    (hv' : G'.IsBoundaryVertex (G'.vertexOf (f T.intervalStart))) :
    T.plabicData.Isomorphic (hf.tree hG hG').plabicData := by
  set T' := hf.tree hG hG' with hT'
  have hv'' : G'.IsBoundaryVertex T'.root := hv'
  have hD' : T'.darts = T.darts.image f := tree_darts hf hG hG'
  have hmap : ∀ x : T.Dart, T'.IsDart (Sum.map f id x.1) := by
    rintro ⟨d | (_ | _ | _ | _), hx⟩
    · change f d ∈ T'.darts
      rw [hD']
      exact mem_image_of_mem f hx
    · trivial
    · trivial
    · exact absurd hv hx
    · exact absurd hv hx
  let e : T.Dart ≃ T'.Dart := Equiv.ofBijective (fun x => ⟨Sum.map f id x.1, hmap x⟩) ⟨by
      rintro ⟨d | l, hx⟩ ⟨d' | l', hy⟩ h <;> simp only [Subtype.mk.injEq, Sum.map_inl,
        Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, id] at h
      · exact Subtype.ext (congrArg Sum.inl (hf.injOn hx hy h))
      · exact Subtype.ext (congrArg Sum.inr h), by
      rintro ⟨d' | l, hx⟩
      · have : d' ∈ T.darts.image f := by rw [← hD']; exact hx
        obtain ⟨d, hd, rfl⟩ := mem_image.1 this
        exact ⟨⟨.inl d, hd⟩, rfl⟩
      · refine ⟨⟨.inr l, ?_⟩, rfl⟩
        rcases l with _ | _ | _ | _
        · trivial
        · trivial
        · exact absurd hv'' hx
        · exact absurd hv'' hx⟩
  have he : ∀ x, ((e x : T'.Dart) : H' ⊕ LollipopDart) = Sum.map f id x.1 := fun _ => rfl
  have hstart : T'.intervalStart = f T.intervalStart := tree_intervalStart hf hG hG'
  refine ⟨Iso.ofEquivOfMapLeg e (fun x => Subtype.ext ?_) (fun x => Subtype.ext ?_) (fun x => ?_)
    (fun x _ => ?_) (fun i => Subtype.ext ?_)⟩
  · rw [he, T'.coe_inv_plabicData hG', he, T.coe_inv_plabicData hG]
    rcases x with ⟨d | l, hx⟩
    · simp only [Sum.map_inl]
      rw [hf.map_inv d hx]
    · rfl
  · rw [he, T'.coe_rot_plabicData hG', he, T.coe_rot_plabicData hG]
    rcases x with ⟨d | (_ | _ | _ | _), hx⟩
    · change Sum.map f id (T.rotAux (.inl d)) = T'.rotAux (.inl (f d))
      simp only [RootedTree.rotAux, if_pos hv, if_pos hv'']
      by_cases h : G.rot d ∈ T.darts
      · rw [if_pos h, if_pos (by rw [hD', ← hf.map_rot d hx h]; exact mem_image_of_mem f h),
          Sum.map_inl, hf.map_rot d hx h]
      · have hend := T.eq_intervalEnd hG hx h
        rw [if_neg h, if_neg (by rw [hD', hend]; exact hf.rot_intervalEnd_notMem)]
        rfl
    · change Sum.map f id (T.rotAux (.inr .e)) = T'.rotAux (.inr .e)
      simp only [RootedTree.rotAux, if_pos hv, if_pos hv'', hstart]
      rfl
    · rfl
    · exact absurd hv hx
    · exact absurd hv hx
  · rw [T'.mem_bdry_plabicData, T.mem_bdry_plabicData]
    rcases x with ⟨d | (_ | _ | _ | _), hx⟩ <;>
      simp [RootedTree.dartE, RootedTree.dartEBar, e]
  · change T'.colourAux (e x : H' ⊕ LollipopDart) = T.colourAux x.1
    rw [he]
    rcases x with ⟨d | l, hx⟩
    · exact hf.colour d hx
    · change G'.colour T'.intervalStart = G.colour T.intervalStart
      rw [hstart]
      exact hf.colour _ T.intervalStart_mem_darts
  · change ((e T.legDart : T'.Dart) : H' ⊕ LollipopDart) = (T'.legDart : H' ⊕ LollipopDart)
    rw [he, RootedTree.legDart, RootedTree.legDart, dif_pos hv, dif_pos hv'']
    change Sum.inl (f T.intervalStart) = Sum.inl T'.intervalStart
    rw [hstart]

end RootedTree.IsEmbedding

/-- `K` with the colour of the leg `g_i` replaced by `s`. The colour of a dart at a boundary
vertex carries no information, so this is isomorphic to `K`. -/
private def recolourLeg (K : PlabicData H' b') (i : Fin b') (s : Shade) : PlabicData H' b' :=
  { K with colour := Function.update K.colour (K.leg i) s }

private theorem isPlabicGraph_recolourLeg {K : PlabicData H' b'} (hK : K.IsPlabicGraph)
    (i : Fin b') (s : Shade) : (recolourLeg K i s).IsPlabicGraph :=
  { hK with
    colour_rot := fun d hd => by
      have hd' : ¬K.IsBoundaryVertex (K.vertexOf d) := hd
      have hrd : ¬K.IsBoundaryVertex (K.vertexOf (K.rot d)) := by rwa [K.vertexOf_rot]
      change Function.update K.colour (K.leg i) s (K.rot d) =
        Function.update K.colour (K.leg i) s d
      rw [Function.update_of_ne (hK.ne_leg_of_not_isBoundaryVertex' hrd i),
        Function.update_of_ne (hK.ne_leg_of_not_isBoundaryVertex' hd' i)]
      exact hK.colour_rot d hd' }

/-- The isomorphism from `K` with a recoloured leg to `K`. -/
private def recolourLegIso {K : PlabicData H' b'} (hK : K.IsPlabicGraph) (i : Fin b')
    (s : Shade) : (recolourLeg K i s).Iso K :=
  Iso.ofEquivOfMapLeg (Equiv.refl H') (fun _ => rfl) (fun _ => rfl) (fun _ => Iff.rfl)
    (fun d hd => by
      change K.colour d = Function.update K.colour (K.leg i) s d
      rw [Function.update_of_ne (hK.ne_leg_of_not_isBoundaryVertex' hd i)])
    (fun _ => rfl)

/-- **Transport of a boundary tree.** Let `T` be a rooted tree of a plabic graph `G` with root
`β(j)`, and let `g` map the darts of `T` to darts of a plabic graph `K` outside `B`, injectively,
respecting the involutions, the rotations along `T` and the colours (except at the leg), and
sending `g_j` to `g_i`. Then `K` has a rooted tree with root `β(i)` whose plabic graph is
isomorphic to `P_T`. -/
private theorem RootedTree.exists_isomorphic_of_map {G : PlabicData H b} (hG : G.IsPlabicGraph)
    {K : PlabicData H' b'} (hK : K.IsPlabicGraph) (T : G.RootedTree) {j : Fin b} {i : Fin b'}
    (hT : T.root = G.bvertex j) (g : H → H') (hinj : Set.InjOn g T.darts)
    (hinv : ∀ e ∈ T.darts, g (G.inv e) = K.inv (g e))
    (hrot : ∀ e ∈ T.darts, G.rot e ∈ T.darts → g (G.rot e) = K.rot (g e))
    (hbdry : ∀ e ∈ T.darts, g e ∉ K.bdry)
    (hcol : ∀ e ∈ T.darts, e ≠ G.leg j → K.colour (g e) = G.colour e)
    (hleg : g (G.leg j) = K.leg i) :
    ∃ T' : K.RootedTree, T'.root = K.bvertex i ∧ T'.plabicData.Isomorphic T.plabicData := by
  set K' := recolourLeg K i (G.colour (G.leg j))
  have hK' : K'.IsPlabicGraph := isPlabicGraph_recolourLeg hK i _
  have hstart : T.intervalStart = G.leg j := T.intervalStart_eq_leg hG hT
  have hb : G.IsBoundaryVertex T.root := hT ▸ hG.isBoundaryVertex_bvertex' j
  have hlegD : G.leg j ∈ T.darts := hstart ▸ T.intervalStart_mem_darts
  have hend : T.intervalEnd = G.leg j := (T.intervalEnd_eq_intervalStart hG hb).trans hstart
  have himg : ∀ y ∈ T.darts.image g, y ∉ K.bdry := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_image.1 hy
    exact hbdry e he
  have hemb : T.IsEmbedding K' g :=
    { injOn := hinj
      map_inv := hinv
      map_rot := hrot
      notMem_bdry := hbdry
      rot_intervalEnd_notMem := by
        rw [hend, hleg]
        exact fun h => himg _ h (hK.rot_leg_mem_bdry' i)
      rot_symm_intervalStart_notMem := by
        rw [hstart, hleg]
        exact fun h => himg _ h (hK.rot_symm_leg_mem_bdry' i)
      intervalLength_lt_card := by
        have h1 := T.intervalLength_lt_card
        rw [hT, (hG.boundaryVertex_card _ (hG.bvertex_mem j)).1] at h1
        rw [hstart, hleg]
        change T.intervalLength < (K.bvertex i).card
        rw [(hK.boundaryVertex_card _ (hK.bvertex_mem i)).1]
        exact h1
      colour := by
        intro e he
        change Function.update K.colour (K.leg i) (G.colour (G.leg j)) (g e) = G.colour e
        by_cases hej : e = G.leg j
        · subst hej
          rw [hleg, Function.update_self]
        · have hne : g e ≠ K.leg i := fun h => hej (hinj he hlegD (h.trans hleg.symm))
          rw [Function.update_of_ne hne]
          exact hcol e he hej }
  set T'' := hemb.tree hG hK' with hT''
  have hroot'' : T''.root = K.bvertex i := by
    change K.vertexOf (g T.intervalStart) = K.vertexOf (K.leg i)
    rw [hstart, hleg]
  have hv' : K'.IsBoundaryVertex (K'.vertexOf (g T.intervalStart)) := by
    change K.IsBoundaryVertex (K.vertexOf (g T.intervalStart))
    rw [hstart, hleg]
    exact hK.isBoundaryVertex_bvertex' i
  obtain ⟨θ⟩ := hemb.tree_plabicData_isomorphic_of_isBoundaryVertex hG hK' hb hv'
  set ι := recolourLegIso hK i (G.colour (G.leg j))
  refine ⟨T''.map ι, ?_, ⟨((T''.plabicDataIsoMap ι hK' hK).symm.trans θ.symm)⟩⟩
  rw [RootedTree.map_root, hroot'', Iso.mapFinset_apply]
  ext y
  simp [ι, recolourLegIso, Iso.ofEquivOfMapLeg]

/-- **A boundary tree from a plabic tree.** Let `R` be a plabic graph with one boundary vertex and
one face, and let `φ` map the darts of `R` outside `B` to darts of a plabic graph `K` outside `B`,
injectively, respecting the involutions, the rotations and the colours (except at the leg), and
sending the leg of `R` to `g_i`. Then `K` has a rooted tree with root `β(i)` whose plabic graph is
isomorphic to `R`. -/
private theorem exists_rootedTree_isomorphic_of_map {Y : Type} [Fintype Y] [DecidableEq Y]
    {R : PlabicData Y 1} (hR : R.IsPlabicGraph) (hf : R.faces.card = 1) {K : PlabicData H' b'}
    (hK : K.IsPlabicGraph) (i : Fin b') (φ : Y → H')
    (hinj : ∀ x y, x ∉ R.bdry → y ∉ R.bdry → φ x = φ y → x = y)
    (hinv : ∀ x, x ∉ R.bdry → φ (R.inv x) = K.inv (φ x))
    (hrot : ∀ x, x ∉ R.bdry → R.rot x ∉ R.bdry → φ (R.rot x) = K.rot (φ x))
    (hbdry : ∀ x, x ∉ R.bdry → φ x ∉ K.bdry)
    (hcol : ∀ x, x ∉ R.bdry → x ≠ R.leg 0 → K.colour (φ x) = R.colour x)
    (hleg : φ (R.leg 0) = K.leg i) :
    ∃ T : K.RootedTree, T.root = K.bvertex i ∧ T.plabicData.Isomorphic R := by
  have hD : ∀ x, x ∈ (hR.fullTree hf).darts ↔ x ∉ R.bdry := fun x => hR.mem_fullTree_darts hf
  obtain ⟨T, hT, ⟨θ⟩⟩ := (hR.fullTree hf).exists_isomorphic_of_map hR hK (j := 0) rfl φ
    (fun x hx y hy h => hinj x y ((hD x).1 hx) ((hD y).1 hy) h)
    (fun e he => hinv e ((hD e).1 he))
    (fun e he hre => hrot e ((hD e).1 he) ((hD _).1 hre))
    (fun e he => hbdry e ((hD e).1 he))
    (fun e he hne => hcol e ((hD e).1 he) hne) hleg
  exact ⟨T, hT, ⟨θ.trans (hR.fullTreeIso hf)⟩⟩

end Transport

/-! ### Rooted trees avoid square faces -/

section Square

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- In a rooted tree, the two ends of an edge `{d, d̄}` of the tree are not joined by a path of
other edges of the tree. -/
private theorem RootedTree.not_reflTransGen_of_mem_darts' (hG : G.IsPlabicGraph)
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
        have hrev : ∀ {u u'}, Relation.ReflTransGen R u u' → Relation.ReflTransGen R u' u := by
          intro u u' hp
          induction hp with
          | refl => exact .refl
          | tail _ hs ih => exact Relation.ReflTransGen.head (hRsymm _ _ hs) ih
        exact ih'.trans (hrev hpath)
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


private theorem squareCorner_notMem_bdry'' {c : H} (hq : G.IsSquareMoveFace c) (k : Fin 4) :
    G.squareCorner c k ∉ G.bdry := by
  have hmem : G.squareCorner c k ∈ G.faceOf c :=
    G.mem_faceOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
  exact disjoint_left.1 (G.mem_internalFaces.1 hq.faceOf_mem_internalFaces).2 hmem

/-- The vertices of a square face lie in no set `W` of a rooted tree: the four edges of the face
would form a cycle in the tree. -/
private theorem RootedTree.vertexOf_squareCorner_notMem_nonRoot' (hG : G.IsPlabicGraph)
    (T : G.RootedTree) {c : H} (hq : G.IsSquareMoveFace c) (k : Fin 4) :
    G.vertexOf (G.squareCorner c k) ∉ T.nonRoot := by
  intro hk
  have hinv := hG.inv_involutive
  set v : Fin 4 → Finset H := fun j => G.vertexOf (G.squareCorner c j) with hvdef
  have hv' := hq.vertexOf_inv_squareCorner
  have hinj : Function.Injective v := hq.injective
  have hS1 : ∀ j, v j ∈ T.nonRoot → v (j + 1) ∈ insert T.root T.nonRoot := fun j h => by
    have := T.vertexOf_inv_mem _ h
    rwa [hv'] at this
  have hS2 : ∀ j, v j ∈ T.nonRoot → v (j - 1) ∈ insert T.root T.nonRoot := fun j h => by
    have h' : G.vertexOf (G.inv (G.squareCorner c (j - 1))) ∈ T.nonRoot := by
      rw [hv', sub_add_cancel]; exact h
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
  -- every edge of the face is an edge of the tree
  have hdarts : ∀ j, G.squareCorner c j ∈ T.darts := by
    intro j
    refine G.mem_treeDarts.2 ⟨squareCorner_notMem_bdry'' hq j, ?_⟩
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
  -- the path `v₀ → v₃ → v₂ → v₁` avoids the edge `{c₀, c̄₀}`
  refine T.not_reflTransGen_of_mem_darts' hG (hdarts 0) ?_
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


end Square

/-! ### Boundary trees whose plabic graph reduces to a lollipop -/

section LollipopTree

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

/-- `K` has a rooted tree with root `β(i)` whose plabic graph is `{M2, M3}`-equivalent to a
lollipop graph. -/
private def HasLollipopTree (K : PlabicData H b) (hK : K.IsPlabicGraph) (i : Fin b) : Prop :=
  ∃ T : K.RootedTree, T.root = K.bvertex i ∧
    ∃ c, PlabicGraph.MoveEquivalent {.m2, .m3} (T.toPlabicGraph hK) (lollipopPlabicGraph c)

private theorem hasLollipopTree_of_isomorphic {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {i : Fin b} {T : K.RootedTree} (hT : T.root = K.bvertex i) {R : PlabicGraph 1}
    (h : T.plabicData.Isomorphic R.data) {c : Shade}
    (hR : PlabicGraph.MoveEquivalent {.m2, .m3} R (lollipopPlabicGraph c)) :
    HasLollipopTree K hK i :=
  ⟨T, hT, c, (PlabicGraph.MoveEquivalent.of_isomorphic (G := T.toPlabicGraph hK) (G' := R)
    h.symm).trans hR⟩

private theorem lollipopGraph_eq_of_notMem_bdry {c : Shade} {y : LollipopDart}
    (hy : y ∉ (lollipopGraph c).bdry) : y = .g ∨ y = .gBar := by
  cases y <;> simp_all [lollipopGraph]

/-- A lollipop at `i` is a boundary tree whose plabic graph is a lollipop graph. -/
private theorem IsLollipop.hasLollipopTree {K : PlabicData H b} (hK : K.IsPlabicGraph)
    {i : Fin b} {v : Finset H} (hv : K.IsLollipop i v) : HasLollipopTree K hK i := by
  have hv' := hv.eq_singleton_inv_leg hK
  set x := K.inv (K.leg i)
  have hxv : x ∈ v := hv' ▸ mem_singleton_self x
  have hvI := hv.1.1
  have hvx : K.vertexOf x = v := by
    obtain ⟨y, rfl⟩ := K.mem_vertices.1 (K.mem_internalVertices.1 hvI).1
    exact K.vertexOf_eq_of_mem hxv
  have hrot : K.rot x = x := by
    have := K.rot_mem_vertexOf x
    rw [hvx, hv'] at this
    exact mem_singleton.1 this
  have hxB : x ∉ K.bdry := fun h => (K.mem_internalVertices.1 hvI).2 ⟨x, hxv, h⟩
  have hlegB := hK.leg_notMem_bdry i
  have hne : K.leg i ≠ x := fun h => hK.inv_ne (K.leg i) h.symm
  set c := K.colour x
  have hf : (lollipopGraph c).faces.card = 1 := by rw [faces_lollipopGraph]; rfl
  let φ : LollipopDart → H := fun y => match y with
    | .gBar => x
    | _ => K.leg i
  have h1 : ∀ y y', y ∉ (lollipopGraph c).bdry → y' ∉ (lollipopGraph c).bdry → φ y = φ y' →
      y = y' := by
    intro y y' hy hy' h
    rcases lollipopGraph_eq_of_notMem_bdry hy with rfl | rfl <;>
      rcases lollipopGraph_eq_of_notMem_bdry hy' with rfl | rfl <;>
      first | rfl | exact absurd h hne | exact absurd h.symm hne
  have h2 : ∀ y, y ∉ (lollipopGraph c).bdry → φ ((lollipopGraph c).inv y) = K.inv (φ y) := by
    intro y hy
    rcases lollipopGraph_eq_of_notMem_bdry hy with rfl | rfl
    · rfl
    · exact (hK.inv_involutive _).symm
  have h3 : ∀ y, y ∉ (lollipopGraph c).bdry → (lollipopGraph c).rot y ∉ (lollipopGraph c).bdry →
      φ ((lollipopGraph c).rot y) = K.rot (φ y) := by
    intro y hy hry
    rcases lollipopGraph_eq_of_notMem_bdry hy with rfl | rfl
    · rw [lollipopGraph_rot_g] at hry
      exact absurd (by simp [lollipopGraph]) hry
    · rw [lollipopGraph_rot_gBar]
      exact hrot.symm
  have h4 : ∀ y, y ∉ (lollipopGraph c).bdry → φ y ∉ K.bdry := by
    intro y hy
    rcases lollipopGraph_eq_of_notMem_bdry hy with rfl | rfl
    · exact hlegB
    · exact hxB
  have h5 : ∀ y, y ∉ (lollipopGraph c).bdry → y ≠ (lollipopGraph c).leg 0 →
      K.colour (φ y) = (lollipopGraph c).colour y := by
    intro y hy hy0
    rcases lollipopGraph_eq_of_notMem_bdry hy with rfl | rfl
    · exact absurd rfl hy0
    · rfl
  obtain ⟨T, hT, hiso⟩ := exists_rootedTree_isomorphic_of_map (isPlabicGraph_lollipopGraph c) hf
    hK i φ h1 h2 h3 h4 h5 rfl
  exact hasLollipopTree_of_isomorphic hK hT (R := lollipopPlabicGraph c) hiso
    (PlabicGraph.MoveEquivalent.refl _ _)

/-- A boundary tree whose plabic graph reduces to a lollipop graph is a lollipop (one non-root
vertex) or a collapsible tree (at least two). -/
private theorem HasLollipopTree.isLollipop_or_isCollapsible {K : PlabicData H b}
    {hK : K.IsPlabicGraph} {i : Fin b} (h : HasLollipopTree K hK i) :
    (∃ v, K.IsLollipop i v) ∨ ∃ T : K.RootedTree, T.root = K.bvertex i ∧ T.IsCollapsible := by
  obtain ⟨T, hT, c, hc⟩ := h
  by_cases h2 : 2 ≤ T.nonRoot.card
  · exact Or.inr ⟨T, hT, c, ⟨T.isPlabicGraph_plabicData hK, hc,
      Or.inr ⟨hT ▸ hK.isBoundaryVertex_bvertex' i, h2⟩⟩⟩
  left
  have hW1 : T.nonRoot.card = 1 := by
    have := T.nonRoot_nonempty.card_pos
    omega
  obtain ⟨w, hw⟩ := card_eq_one.1 hW1
  have hstart := T.intervalStart_eq_leg hK hT
  have hlegD : K.leg i ∈ T.darts := hstart ▸ T.intervalStart_mem_darts
  have hu : K.vertexOf (K.inv (K.leg i)) ∈ T.nonRoot := T.vertexOf_inv_leg_mem hK hlegD
  rw [hw, mem_singleton] at hu
  have hwI : w ∈ K.internalVertices := T.nonRoot_subset (hw ▸ mem_singleton_self w)
  have hcard := T.card_darts hK
  rw [hW1] at hcard
  have hlegw : K.leg i ∉ w := by
    intro h
    have : K.vertexOf (K.leg i) = w := by rw [← hu]; exact K.vertexOf_eq_of_mem (hu ▸ h)
    exact (K.mem_internalVertices.1 hwI).2 (this ▸ hK.isBoundaryVertex_bvertex' i)
  have hsub : insert (K.leg i) w ⊆ T.darts := by
    intro y hy
    rcases mem_insert.1 hy with rfl | hy
    · exact hlegD
    · refine T.mem_darts_of_vertexOf_mem ?_
      rw [hw, mem_singleton, ← hu]
      exact K.vertexOf_eq_of_mem (hu ▸ hy)
  have h1 := card_le_card hsub
  rw [card_insert_of_notMem hlegw] at h1
  have hwne : w.Nonempty := ⟨_, hu ▸ K.self_mem_vertexOf _⟩
  refine ⟨w, ⟨hwI, by have := hwne.card_pos; omega⟩, K.inv (K.leg i),
    hu ▸ K.self_mem_vertexOf _, ?_⟩
  rw [hK.inv_involutive]
  exact K.leg_mem_bvertex i

/-- An isomorphism carries a boundary tree to a boundary tree. -/
private theorem HasLollipopTree.of_iso {K : PlabicData H b} {K' : PlabicData H' b}
    (hK : K.IsPlabicGraph) (hK' : K'.IsPlabicGraph) (θ : K.Iso K') {i : Fin b}
    (h : HasLollipopTree K hK i) : HasLollipopTree K' hK' i := by
  obtain ⟨T, hT, c, hc⟩ := h
  refine hasLollipopTree_of_isomorphic hK' (T := T.map θ) ?_ (R := T.toPlabicGraph hK)
    ⟨(T.plabicDataIsoMap θ hK hK').symm⟩ hc
  rw [RootedTree.map_root, hT, bvertex, θ.mapFinset_vertexOf, θ.map_leg hK hK']
  rfl

/-- **Case (A)**: a square move carries a boundary tree to a boundary tree. -/
private theorem HasLollipopTree.squareMove {K : PlabicData H b} (hK : K.IsPlabicGraph) {c : H}
    (hq : K.IsSquareMoveFace c) {i : Fin b} (h : HasLollipopTree K hK i) :
    HasLollipopTree (K.squareMove c) (hK.squareMove c) i := by
  obtain ⟨T, hT, s, hs⟩ := h
  refine hasLollipopTree_of_isomorphic _ (T := T.toSquareMove c) hT (R := T.toPlabicGraph hK)
    ⟨(T.plabicDataIsoToSquareMove c fun d hd => ?_).symm⟩ hs
  apply colour_squareMove_of_notMem
  intro hm
  obtain ⟨k, hk⟩ := mem_squareVertices.1 hm
  rcases T.vertexOf_mem_or_eq_root hK hd with h' | h'
  · exact T.vertexOf_squareCorner_notMem_nonRoot' hK hq k (by rw [hk]; exact h')
  · have hint := hq.vertexOf_mem_internalVertices k
    rw [hk, h', hT] at hint
    exact (K.mem_internalVertices.1 hint).2 (hK.isBoundaryVertex_bvertex' i)

end LollipopTree

/-! ### Darts of the plabic graph of a tree -/

open scoped Classical in
/-- The element `e` of `S` if `e ∈ S`, and `a` otherwise. -/
private noncomputable def inclOr {α : Type*} (S : Set α) (a : S) (e : α) : S :=
  if h : e ∈ S then ⟨e, h⟩ else a

private theorem coe_inclOr {α : Type*} {S : Set α} {a : S} {e : α} (h : e ∈ S) :
    (inclOr S a e : α) = e := by
  classical
  simp [inclOr, h]

section TreeDarts

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

namespace RootedTree

variable (T : G.RootedTree)

/-- The dart of `G` underlying a dart of `P_T`; the new darts go to `a₁`. -/
private noncomputable def baseDart (x : H ⊕ LollipopDart) : H :=
  Sum.elim id (fun _ => T.intervalStart) x

/-- A dart of `P_T` outside `B` is a dart of `T`, for a boundary root. -/
private theorem exists_eq_inl_of_notMem_bdry (hb : G.IsBoundaryVertex T.root) {x : T.Dart}
    (hx : x ∉ T.plabicData.bdry) : ∃ e, ∃ he : e ∈ T.darts, x = ⟨.inl e, he⟩ := by
  rcases x with ⟨e | (_ | _ | _ | _), h⟩
  · exact ⟨e, h, rfl⟩
  · exact absurd (T.mem_bdry_plabicData.2 (Or.inl rfl)) hx
  · exact absurd (T.mem_bdry_plabicData.2 (Or.inr rfl)) hx
  · exact absurd hb h
  · exact absurd hb h

private theorem inl_notMem_bdry {e : H} (he : e ∈ T.darts) :
    (⟨.inl e, he⟩ : T.Dart) ∉ T.plabicData.bdry := by
  rw [T.mem_bdry_plabicData]
  rintro (h | h) <;> simp [dartE, dartEBar] at h

private theorem rot_inl_of_notMem (hG : G.IsPlabicGraph) (hb : G.IsBoundaryVertex T.root)
    {e : H} (he : e ∈ T.darts) (h : G.rot e ∉ T.darts) :
    T.plabicData.rot ⟨.inl e, he⟩ = T.dartEBar :=
  Subtype.ext (by rw [T.coe_rot_plabicData hG]; simp [rotAux, h, hb, dartEBar])

/-- The darts of `P_T` at the vertex of a dart `d` of a non-root vertex are those of `v(d)`. -/
private theorem map_vertexOf_inl (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts)
    (hW : G.vertexOf d ∈ T.nonRoot) :
    (T.plabicData.vertexOf ⟨.inl d, hd⟩).map (Function.Embedding.subtype _) =
      (G.vertexOf d).map Function.Embedding.inl := by
  ext z
  simp only [mem_map, Function.Embedding.coe_subtype, Function.Embedding.inl_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨d', h1, h2⟩ := T.exists_of_mem_vertexOf_inl hG hd hW hy
    exact ⟨d', h2 ▸ G.self_mem_vertexOf d', h1.symm⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨n, rfl⟩ := ((G.mem_vertexOf).1 he).exists_nat_pow_eq
    exact ⟨(T.plabicData.rot ^ n) ⟨.inl d, hd⟩,
      (T.plabicData.mem_vertexOf).2 (sameCycle_pow_apply_self _ _ n),
      T.coe_rot_pow_inl hG hd hW n⟩

private theorem card_vertexOf_inl (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts)
    (hW : G.vertexOf d ∈ T.nonRoot) :
    (T.plabicData.vertexOf ⟨.inl d, hd⟩).card = (G.vertexOf d).card := by
  rw [← card_map (Function.Embedding.subtype _), T.map_vertexOf_inl hG hd hW, card_map]

private theorem not_isBoundaryVertex_vertexOf_inl (hG : G.IsPlabicGraph) {d : H}
    (hd : d ∈ T.darts) (hW : G.vertexOf d ∈ T.nonRoot) :
    ¬T.plabicData.IsBoundaryVertex (T.plabicData.vertexOf ⟨.inl d, hd⟩) := by
  rintro ⟨y, hy, hyB⟩
  obtain ⟨d', h1, -⟩ := T.exists_of_mem_vertexOf_inl hG hd hW hy
  rcases T.mem_bdry_plabicData.1 hyB with rfl | rfl <;> simp [dartE, dartEBar] at h1

private theorem leg_mem_darts (hG : G.IsPlabicGraph) {i : Fin b} (hT : T.root = G.bvertex i) :
    G.leg i ∈ T.darts :=
  T.intervalStart_eq_leg hG hT ▸ T.intervalStart_mem_darts

private theorem coe_legDart (hG : G.IsPlabicGraph) {i : Fin b} (hT : T.root = G.bvertex i) :
    (T.legDart : H ⊕ LollipopDart) = .inl (G.leg i) := by
  have hb : G.IsBoundaryVertex T.root := hT ▸ hG.isBoundaryVertex_bvertex' i
  rw [T.legDart_of_isBoundaryVertex hb]
  exact congrArg Sum.inl (T.intervalStart_eq_leg hG hT)

end RootedTree

end TreeDarts

/-! ### Removing and inserting a bivalent vertex -/

private theorem fin_two_cases' (j : Fin 2) : j = 0 ∨ j = 1 := by
  fin_cases j <;> simp

section Bivalent

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {K : PlabicData H b}
  (hK : K.IsPlabicGraph) {d : H} (hd : K.IsBivalentRemovable d)

include hK hd

/-- **Case (B)**: removing a bivalent vertex keeps a boundary tree. If the vertex is in the tree,
it is removed from `P_T` as well; otherwise the tree is unchanged. -/
private theorem hasLollipopTree_bivalentRemoval {i : Fin b} (h : HasLollipopTree K hK i) :
    HasLollipopTree (K.bivalentRemoval hK hd) (isPlabicGraph_bivalentRemoval hK hd) i := by
  obtain ⟨T, hT, c, hc⟩ := h
  have hb : K.IsBoundaryVertex T.root := hT ▸ hK.isBoundaryVertex_bvertex' i
  set S : Set H := ({d, K.rot d}ᶜ : Set H) with hS
  set K'' := K.bivalentRemoval hK hd
  have hK'' : K''.IsPlabicGraph := isPlabicGraph_bivalentRemoval hK hd
  set a : S := ⟨K.leg i, hd.leg_mem hK i⟩
  set g : H → S := inclOr S a
  have hvd : K.vertexOf (K.rot d) = K.vertexOf d := K.vertexOf_rot d
  have hdroot : K.vertexOf d ≠ T.root := fun h => hd.not_isBoundaryVertex (h ▸ hb)
  have hinvd : K.inv (K.inv d) = d := hK.inv_involutive d
  have hinvrd : K.inv (K.inv (K.rot d)) = K.rot d := hK.inv_involutive _
  have hmemS : ∀ e, e ∈ S ↔ e ≠ d ∧ e ≠ K.rot d := fun e => by
    simp only [hS, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  have hlegD := T.leg_mem_darts hK hT
  have hlegS : K.leg i ∈ S := hd.leg_mem hK i
  have hgleg : g (K.leg i) = K''.leg i := Subtype.ext (coe_inclOr hlegS)
  by_cases hW : K.vertexOf d ∈ T.nonRoot
  · -- the removed vertex lies in the tree: remove it from `P_T`
    have hdD : d ∈ T.darts := T.mem_darts_of_vertexOf_mem hW
    have hrdD : K.rot d ∈ T.darts := T.rot_mem_darts_of_vertexOf_mem hW
    set P := T.plabicData
    have hP : P.IsPlabicGraph := T.isPlabicGraph_plabicData hK
    set dP : T.Dart := ⟨.inl d, hdD⟩
    have hProt : P.rot dP = ⟨.inl (K.rot d), hrdD⟩ := T.rot_inl_of_mem hK hdD hrdD
    have hPinv : P.inv dP = ⟨.inl (K.inv d), T.inv_mem_darts hK hdD⟩ := T.inv_inl hK hdD
    have hPinvrot : P.inv (P.rot dP) = ⟨.inl (K.inv (K.rot d)), T.inv_mem_darts hK hrdD⟩ := by
      rw [hProt]; exact T.inv_inl hK hrdD
    have hdP : P.IsBivalentRemovable dP :=
      { not_isBoundaryVertex := T.not_isBoundaryVertex_vertexOf_inl hK hdD hW
        card_vertexOf := (T.card_vertexOf_inl hK hdD hW).trans hd.card_vertexOf
        inv_ne_rot := by
          rw [hPinv, hProt]
          intro h
          exact hd.inv_ne_rot (Sum.inl_injective (congrArg Subtype.val h)) }
    set R := P.bivalentRemoval hP hdP
    have hR : R.IsPlabicGraph := isPlabicGraph_bivalentRemoval hP hdP
    have hRf : R.faces.card = 1 :=
      (card_bivalentRemoval_faces hP hdP).trans (T.card_faces_plabicData hK)
    have hRc : PlabicGraph.MoveEquivalent {.m2, .m3} ⟨_, R, hR⟩ (lollipopPlabicGraph c) :=
      (PlabicGraph.MoveEquivalent.of_isLocalMove (S := {.m2, .m3}) (t := .m2) (by simp)
        (G := T.toPlabicGraph hK) (G' := ⟨_, R, hR⟩)
        (Or.inl ⟨dP, hdP, PlabicData.Isomorphic.refl _⟩)).symm.trans hc
    let φ : ({dP, P.rot dP}ᶜ : Set T.Dart) → S := fun y => g (T.baseDart (y : T.Dart).1)
    have hy : ∀ y : ({dP, P.rot dP}ᶜ : Set T.Dart), y ∉ R.bdry → ∃ e, ∃ he : e ∈ T.darts,
        (y : T.Dart) = ⟨.inl e, he⟩ ∧ ∃ hS : e ∈ S, φ y = ⟨e, hS⟩ := by
      intro y hyB
      rw [mem_bivalentRemoval_bdry] at hyB
      obtain ⟨e, he, hye⟩ := T.exists_eq_inl_of_notMem_bdry hb hyB
      have hy2 := y.2
      rw [hye] at hy2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
        hProt] at hy2
      have heS : e ∈ S := (hmemS e).2 ⟨fun h => hy2.1 (Subtype.ext (congrArg Sum.inl h)),
        fun h => hy2.2 (Subtype.ext (congrArg Sum.inl h))⟩
      refine ⟨e, he, hye, heS, Subtype.ext ?_⟩
      change (g (T.baseDart (y : T.Dart).1) : H) = e
      rw [hye]
      exact coe_inclOr heS
    obtain ⟨T', hT', hiso⟩ := exists_rootedTree_isomorphic_of_map hR hRf hK'' i φ
      (fun y y' hy1 hy1' h => by
        obtain ⟨e, he, hye, heS, hφ⟩ := hy y hy1
        obtain ⟨e', he', hye', heS', hφ'⟩ := hy y' hy1'
        rw [hφ, hφ'] at h
        obtain rfl : e = e' := congrArg Subtype.val h
        exact Subtype.ext (hye.trans hye'.symm))
      (fun y hy1 => by
        obtain ⟨e, he, hye, heS, hφ⟩ := hy y hy1
        rw [hφ]
        by_cases h1 : e = K.inv d
        · have hyP : (y : T.Dart) = P.inv dP := by
            rw [hye, hPinv]; exact Subtype.ext (congrArg Sum.inl h1)
          have hRy : (R.inv y : T.Dart) = ⟨.inl (K.inv (K.rot d)), T.inv_mem_darts hK hrdD⟩ := by
            rw [coe_bivalentRemoval_inv_of_eq_inv hP hdP hyP, hPinvrot]
          apply Subtype.ext
          change (g (T.baseDart (R.inv y : T.Dart).1) : H) = _
          rw [hRy, coe_bivalentRemoval_inv_of_eq_inv hK hd h1]
          exact coe_inclOr (hd.inv_rot_mem hK)
        by_cases h2 : e = K.inv (K.rot d)
        · have hyP : (y : T.Dart) = P.inv (P.rot dP) := by
            rw [hye, hPinvrot]; exact Subtype.ext (congrArg Sum.inl h2)
          have hRy : (R.inv y : T.Dart) = ⟨.inl (K.inv d), T.inv_mem_darts hK hdD⟩ := by
            rw [coe_bivalentRemoval_inv_of_eq_inv_rot hP hdP hyP, hPinv]
          apply Subtype.ext
          change (g (T.baseDart (R.inv y : T.Dart).1) : H) = _
          rw [hRy, coe_bivalentRemoval_inv_of_eq_inv_rot hK hd h2]
          exact coe_inclOr (hd.inv_mem hK)
        · have n1 : (y : T.Dart) ≠ P.inv dP := by
            rw [hye, hPinv]; intro h; exact h1 (Sum.inl_injective (congrArg Subtype.val h))
          have n2 : (y : T.Dart) ≠ P.inv (P.rot dP) := by
            rw [hye, hPinvrot]; intro h; exact h2 (Sum.inl_injective (congrArg Subtype.val h))
          have hie := T.inv_mem_darts hK he
          have hieS : K.inv e ∈ S := (hmemS _).2 ⟨fun h => h1 (by rw [← h, hK.inv_involutive]),
            fun h => h2 (by rw [← h, hK.inv_involutive])⟩
          apply Subtype.ext
          change (g (T.baseDart (R.inv y : T.Dart).1) : H) = _
          rw [coe_bivalentRemoval_inv_of_ne hP hdP n1 n2, hye, T.inv_inl hK he,
            coe_bivalentRemoval_inv_of_ne hK hd h1 h2]
          exact coe_inclOr hieS)
      (fun y hy1 hry => by
        obtain ⟨e, he, hye, heS, hφ⟩ := hy y hy1
        rw [hφ]
        have hRy : (R.rot y : T.Dart) = P.rot ⟨.inl e, he⟩ := by
          rw [coe_bivalentRemoval_rot, hye]
        by_cases hre : K.rot e ∈ T.darts
        · rw [T.rot_inl_of_mem hK he hre] at hRy
          apply Subtype.ext
          change (g (T.baseDart (R.rot y : T.Dart).1) : H) = K.rot e
          rw [hRy]
          exact coe_inclOr ((hd.rot_mem_iff e).2 heS)
        · rw [T.rot_inl_of_notMem hK hb he hre] at hRy
          exact absurd ((mem_bivalentRemoval_bdry hP hdP).2
            (by rw [hRy]; exact T.mem_bdry_plabicData.2 (Or.inr rfl))) hry)
      (fun y hy1 => by
        obtain ⟨e, he, hye, heS, hφ⟩ := hy y hy1
        rw [hφ, mem_bivalentRemoval_bdry]
        exact T.notMem_bdry_of_mem_darts he)
      (fun y hy1 _ => by
        obtain ⟨e, he, hye, heS, hφ⟩ := hy y hy1
        rw [hφ, bivalentRemoval_colour, bivalentRemoval_colour]
        change K.colour e = T.colourAux (y : T.Dart).1
        rw [hye]
        rfl)
      (by
        apply Subtype.ext
        change (g (T.baseDart (T.legDart : H ⊕ LollipopDart)) : H) = K.leg i
        rw [T.coe_legDart hK hT]
        exact coe_inclOr hlegS)
    exact hasLollipopTree_of_isomorphic hK'' hT' (R := ⟨_, R, hR⟩) hiso hRc
  · -- the removed vertex is not in the tree: the tree is unchanged
    have hmem : ∀ e ∈ T.darts, e ∈ S := by
      intro e he
      have hve : K.vertexOf e ≠ K.vertexOf d := by
        rcases T.vertexOf_mem_or_eq_root hK he with h | h
        · exact fun h' => hW (h' ▸ h)
        · exact fun h' => hdroot (h' ▸ h)
      exact (hmemS e).2 ⟨fun h => hve (by rw [h]), fun h => hve (by rw [h, hvd])⟩
    have hg : ∀ e ∈ T.darts, (g e : H) = e := fun e he => coe_inclOr (hmem e he)
    obtain ⟨T', hT', hiso⟩ := T.exists_isomorphic_of_map hK hK'' hT g
      (fun x hx y hy h => by
        have := congrArg Subtype.val h
        rwa [hg x hx, hg y hy] at this)
      (fun e he => by
        apply Subtype.ext
        have hie := T.inv_mem_darts hK he
        have h1 : (g e : H) ≠ K.inv d := by
          rw [hg e he]
          intro h
          have := (hmemS _).1 (hmem _ hie)
          rw [h, hinvd] at this
          exact this.1 rfl
        have h2 : (g e : H) ≠ K.inv (K.rot d) := by
          rw [hg e he]
          intro h
          have := (hmemS _).1 (hmem _ hie)
          rw [h, hinvrd] at this
          exact this.2 rfl
        rw [hg _ hie, coe_bivalentRemoval_inv_of_ne hK hd h1 h2, hg e he])
      (fun e he hre => by
        apply Subtype.ext
        rw [hg _ hre, coe_bivalentRemoval_rot, hg e he])
      (fun e he => by
        rw [mem_bivalentRemoval_bdry, hg e he]
        exact T.notMem_bdry_of_mem_darts he)
      (fun e he _ => by rw [bivalentRemoval_colour, hg e he])
      hgleg
    exact hasLollipopTree_of_isomorphic hK'' hT' (R := T.toPlabicGraph hK) hiso hc

/-- **Case (C)**: a boundary tree of the removal of a bivalent vertex lifts. If the edge of the
removal replacing the two edges at the vertex is an edge of the tree, the vertex is inserted on it
in `P_T`; otherwise the tree is a tree of the graph itself. -/
private theorem hasLollipopTree_of_bivalentRemoval {i : Fin b}
    (h : HasLollipopTree (K.bivalentRemoval hK hd) (isPlabicGraph_bivalentRemoval hK hd) i) :
    HasLollipopTree K hK i := by
  set S : Set H := ({d, K.rot d}ᶜ : Set H) with hS
  set K'' := K.bivalentRemoval hK hd
  have hK'' : K''.IsPlabicGraph := isPlabicGraph_bivalentRemoval hK hd
  obtain ⟨T, hT, c, hc⟩ := h
  have hb : K''.IsBoundaryVertex T.root := hT ▸ hK''.isBoundaryVertex_bvertex' i
  have hmemS : ∀ e, e ∈ S ↔ e ≠ d ∧ e ≠ K.rot d := fun e => by
    simp only [hS, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  set u : S := ⟨K.inv d, hd.inv_mem hK⟩
  set u' : S := ⟨K.inv (K.rot d), hd.inv_rot_mem hK⟩
  have hinvu : K''.inv u = u' := Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv hK hd rfl)
  have hinvu' : K''.inv u' = u :=
    Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hK hd rfl)
  have hinv'' : ∀ e : S, (e : H) ≠ K.inv d → (e : H) ≠ K.inv (K.rot d) →
      ((K''.inv e : S) : H) = K.inv e := fun e h1 h2 => coe_bivalentRemoval_inv_of_ne hK hd h1 h2
  by_cases hu : u ∈ T.darts
  · -- the merged edge is an edge of the tree: insert the vertex on it in `P_T`
    set P := T.plabicData
    have hP : P.IsPlabicGraph := T.isPlabicGraph_plabicData hK''
    set uP : T.Dart := ⟨.inl u, hu⟩
    have huPB : uP ∉ P.bdry := T.inl_notMem_bdry hu
    have hu'D : u' ∈ T.darts := hinvu ▸ T.inv_mem_darts hK'' hu
    have hPinvu : P.inv uP = ⟨.inl u', hu'D⟩ := by
      rw [T.inv_inl hK'' hu]
      exact Subtype.ext (congrArg Sum.inl hinvu)
    have hfix : P.inv uP ≠ uP := hP.inv_ne uP
    set c' := K.colour d
    set R := P.bivalentInsertion uP c'
    have hR : R.IsPlabicGraph := isPlabicGraph_bivalentInsertion c' hP huPB
    have hRP : PlabicGraph.MoveEquivalent {.m2, .m3} ⟨_, R, hR⟩ (T.toPlabicGraph hK'') :=
      PlabicGraph.MoveEquivalent.of_isLocalMove (t := .m2) (by simp)
        (Or.inl ⟨Sum.inr 0, isBivalentRemovable_bivalentInsertion (d := uP) (c := c'),
          (bivalentRemoval_bivalentInsertion_isomorphic c' hP huPB).symm⟩)
    have hRf : R.faces.card = 1 := hRP.card_eq.2.1.trans (T.card_faces_plabicData hK'')
    have hRc := hRP.trans hc
    let φ : T.Dart ⊕ Fin 2 → H := fun z => match z with
      | .inl y => ((T.baseDart y.1 : S) : H)
      | .inr j => if j = 0 then d else K.rot d
    have hφ0 : φ (.inr 0) = d := rfl
    have hφ1 : φ (.inr 1) = K.rot d := rfl
    have hz : ∀ y : T.Dart, Sum.inl y ∉ R.bdry → ∃ e, ∃ he : e ∈ T.darts,
        y = ⟨.inl e, he⟩ := fun y hy =>
      T.exists_eq_inl_of_notMem_bdry hb (by rwa [inl_mem_bivalentInsertion_bdry] at hy)
    have hφinl : ∀ (e : S) (he : e ∈ T.darts), φ (.inl ⟨.inl e, he⟩) = e := fun _ _ => rfl
    have heS : ∀ e : S, (e : H) ≠ d ∧ (e : H) ≠ K.rot d := fun e => (hmemS e).1 e.2
    obtain ⟨T', hT', hiso⟩ := exists_rootedTree_isomorphic_of_map hR hRf hK i φ
      (by
        rintro (y | j) (y' | j') hy hy' h
        · obtain ⟨e, he, rfl⟩ := hz y hy
          obtain ⟨e', he', rfl⟩ := hz y' hy'
          rw [hφinl, hφinl] at h
          obtain rfl : e = e' := Subtype.ext h
          rfl
        · obtain ⟨e, he, rfl⟩ := hz y hy
          rw [hφinl] at h
          rcases fin_two_cases' j' with rfl | rfl
          · exact absurd h (heS e).1
          · exact absurd h (heS e).2
        · obtain ⟨e', he', rfl⟩ := hz y' hy'
          rw [hφinl] at h
          rcases fin_two_cases' j with rfl | rfl
          · exact absurd h.symm (heS e').1
          · exact absurd h.symm (heS e').2
        · rcases fin_two_cases' j with rfl | rfl <;> rcases fin_two_cases' j' with rfl | rfl
          · rfl
          · exact absurd h hd.rot_ne.symm
          · exact absurd h hd.rot_ne
          · rfl)
      (by
        rintro (y | j) hy
        · obtain ⟨e, he, rfl⟩ := hz y hy
          by_cases h1 : e = u
          · subst h1
            rw [bivalentInsertion_inv_inl_self c' hfix, hφ0, hφinl]
            exact (hK.inv_involutive d).symm
          by_cases h2 : e = u'
          · subst h2
            have : (⟨.inl u', he⟩ : T.Dart) = P.inv uP := hPinvu.symm
            have hRi : R.inv (Sum.inl ⟨.inl u', he⟩) = Sum.inr 1 := by
              rw [this]
              exact bivalentInsertion_inv_inl_inv c' hP.inv_involutive
            rw [hRi, hφ1, hφinl]
            exact (hK.inv_involutive _).symm
          · have n1 : (⟨.inl e, he⟩ : T.Dart) ≠ uP := fun h =>
              h1 (Sum.inl_injective (congrArg Subtype.val h))
            have n2 : (⟨.inl e, he⟩ : T.Dart) ≠ P.inv uP := by
              rw [hPinvu]
              exact fun h => h2 (Sum.inl_injective (congrArg Subtype.val h))
            rw [bivalentInsertion_inv_inl_of_ne c' hP.inv_involutive n1 n2, T.inv_inl hK'' he,
              hφinl, hφinl]
            exact hinv'' e (fun h => h1 (Subtype.ext h)) (fun h => h2 (Subtype.ext h))
        · rcases fin_two_cases' j with rfl | rfl
          · rw [bivalentInsertion_inv_inr_zero, hφ0]
            rfl
          · rw [bivalentInsertion_inv_inr_one c' hfix, hPinvu, hφ1]
            rfl)
      (by
        rintro (y | j) hy hry
        · obtain ⟨e, he, rfl⟩ := hz y hy
          rw [bivalentInsertion_rot_inl] at hry ⊢
          by_cases hre : K''.rot e ∈ T.darts
          · rw [T.rot_inl_of_mem hK'' he hre, hφinl, hφinl]
            rfl
          · rw [T.rot_inl_of_notMem hK'' hb he hre] at hry
            exact absurd ((inl_mem_bivalentInsertion_bdry _ _).2
              (T.mem_bdry_plabicData.2 (Or.inr rfl))) hry
        · rcases fin_two_cases' j with rfl | rfl
          · rw [bivalentInsertion_rot_inr_zero, hφ0, hφ1]
          · rw [bivalentInsertion_rot_inr_one, hφ0, hφ1]
            exact hd.rot_rot.symm)
      (by
        rintro (y | j) hy
        · obtain ⟨e, he, rfl⟩ := hz y hy
          rw [hφinl, ← mem_bivalentRemoval_bdry hK hd]
          exact T.notMem_bdry_of_mem_darts he
        · rcases fin_two_cases' j with rfl | rfl
          · exact hd.notMem_bdry
          · exact hd.rot_notMem_bdry)
      (by
        rintro (y | j) hy _
        · obtain ⟨e, he, rfl⟩ := hz y hy
          rfl
        · rcases fin_two_cases' j with rfl | rfl
          · rfl
          · rw [hφ1, bivalentInsertion_colour_inr]
            exact hK.colour_rot d hd.not_isBoundaryVertex)
      (by
        change ((T.baseDart (T.legDart : _ ⊕ LollipopDart) : S) : H) = K.leg i
        rw [T.coe_legDart hK'' hT]
        rfl)
    exact hasLollipopTree_of_isomorphic hK hT' (R := ⟨_, R, hR⟩) hiso hRc
  · -- the merged edge is not an edge of the tree: the tree is a tree of `K`
    have hu' : u' ∉ T.darts := fun h => hu (hinvu' ▸ T.inv_mem_darts hK'' h)
    obtain ⟨T', hT', hiso⟩ := T.exists_isomorphic_of_map hK'' hK hT Subtype.val
      Subtype.val_injective.injOn
      (fun e he => hinv'' e (fun h => hu (by rwa [show e = u from Subtype.ext h] at he))
        (fun h => hu' (by rwa [show e = u' from Subtype.ext h] at he)))
      (fun _ _ _ => rfl)
      (fun e he => by
        rw [← mem_bivalentRemoval_bdry hK hd]
        exact T.notMem_bdry_of_mem_darts he)
      (fun _ _ _ => rfl)
      rfl
    exact hasLollipopTree_of_isomorphic hK hT' (R := T.toPlabicGraph hK'') hiso hc

end Bivalent

/-! ### Contracting an edge and splitting a vertex -/

/-- A map intertwining two permutations on an invariant set carries first returns to first
returns. -/
private theorem map_firstReturn_of_semiconjOn {X X' : Type*} [Finite X] [Finite X']
    {τ : Equiv.Perm X} {τ' : Equiv.Perm X'} (ι : X → X') {A : Set X} (hA : ∀ x ∈ A, τ x ∈ A)
    (hι : ∀ x ∈ A, ι (τ x) = τ' (ι x)) {Y : Set X} {Y' : Set X'}
    (hY : ∀ x ∈ A, ι x ∈ Y' ↔ x ∈ Y) (y : Y) (hyA : (y : X) ∈ A) :
    (firstReturn τ Y y : X) ∈ A ∧
      ι (firstReturn τ Y y) = firstReturn τ' Y' ⟨ι y, (hY y hyA).2 y.2⟩ := by
  have hpow : ∀ n : ℕ, (τ ^ n) y ∈ A ∧ ι ((τ ^ n) y) = (τ' ^ n) (ι y) := by
    intro n
    induction n with
    | zero => exact ⟨hyA, rfl⟩
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply]
      exact ⟨hA _ ih.1, by rw [hι _ ih.1, ih.2]⟩
  rw [coe_firstReturn]
  refine ⟨(hpow _).1, ?_⟩
  rw [(hpow _).2]
  symm
  refine coe_firstReturn_of_pow (y := ⟨ι y, (hY y hyA).2 y.2⟩) (firstReturnTime_pos y) ?_ ?_
  · change (τ' ^ _) (ι y) ∈ Y'
    rw [← (hpow _).2, hY _ (hpow _).1]
    exact pow_firstReturnTime_apply_mem y
  · intro j hj hjm
    change (τ' ^ j) (ι y) ∉ Y'
    rw [← (hpow _).2, hY _ (hpow _).1]
    exact pow_apply_notMem_of_lt_firstReturnTime hj hjm

section Contraction

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {K : PlabicData H b}
  (hK : K.IsPlabicGraph) {d : H} (he : K.IsContractibleEdge d)

include hK he

private theorem IsContractibleEdge.inv'' : K.IsContractibleEdge (K.inv d) where
  vertexOf_ne := by rw [hK.inv_involutive d]; exact he.vertexOf_ne.symm
  mem_internalVertices := he.inv_mem_internalVertices
  inv_mem_internalVertices := by rw [hK.inv_involutive d]; exact he.mem_internalVertices
  colour_inv := by rw [hK.inv_involutive d]; exact he.colour_inv.symm

/-- The contractions along `d` and along `d̄` are isomorphic. -/
private noncomputable def contractEdgeInvIso' :
    (K.contractEdge d (he.leg_mem hK)).Iso
      (K.contractEdge (K.inv d) ((IsContractibleEdge.inv'' hK he).leg_mem hK)) :=
  have hinv := hK.inv_involutive
  have hmem : ∀ x : H, x ∈ (({d, K.inv d} : Set H)ᶜ : Set H) ↔
      x ∈ (({K.inv d, K.inv (K.inv d)} : Set H)ᶜ : Set H) := fun x => by
    rw [mem_compl_pair_iff, mem_compl_pair_iff, hinv]
    exact And.comm
  have hτ : K.rot * Equiv.swap (K.inv d) (K.inv (K.inv d)) = K.rot * Equiv.swap d (K.inv d) := by
    rw [hinv, Equiv.swap_comm]
  Iso.ofEquivOfMapLeg (Equiv.subtypeEquivRight hmem)
    (fun x => Subtype.ext (by
      change ((K.contractEdge d (he.leg_mem hK)).inv x : H) =
        ((K.contractEdge (K.inv d) _).inv _ : H)
      rw [coe_contractEdge_inv hinv, coe_contractEdge_inv hinv]
      rfl))
    (fun x => Subtype.ext (by
      change (firstReturn (K.rot * Equiv.swap d (K.inv d)) _ x : H) =
        (firstReturn (K.rot * Equiv.swap (K.inv d) (K.inv (K.inv d))) _ _ : H)
      rw [hτ]
      exact (map_firstReturn_of_semiconjOn id (A := Set.univ) (fun _ _ => trivial)
        (fun _ _ => rfl) (fun x _ => (hmem x).symm) x trivial).2))
    (fun x => by
      rw [mem_contractEdge_bdry, mem_contractEdge_bdry]
      rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)

/-- **Case (D)**: contracting an edge keeps a boundary tree. If the edge is an edge of the tree,
it is contracted in `P_T` as well; otherwise the tree is unchanged. -/
private theorem hasLollipopTree_contractEdge {i : Fin b} (h : HasLollipopTree K hK i) :
    HasLollipopTree (K.contractEdge d (he.leg_mem hK)) (hK.contractEdge he) i := by
  obtain ⟨T, hT, c, hc⟩ := h
  have hb : K.IsBoundaryVertex T.root := hT ▸ hK.isBoundaryVertex_bvertex' i
  set S : Set H := (({d, K.inv d} : Set H)ᶜ : Set H) with hS
  set K'' := K.contractEdge d (he.leg_mem hK)
  have hK'' : K''.IsPlabicGraph := hK.contractEdge he
  have hinv := hK.inv_involutive
  have hmemS : ∀ e, e ∈ S ↔ e ≠ d ∧ e ≠ K.inv d := fun e => mem_compl_pair_iff
  have hlegS : K.leg i ∈ S := he.leg_mem hK i
  set a : S := ⟨K.leg i, hlegS⟩
  set g : H → S := inclOr S a
  have hgleg : g (K.leg i) = K''.leg i := Subtype.ext (coe_inclOr hlegS)
  have hdroot : K.vertexOf d ≠ T.root := fun h => he.not_isBoundaryVertex (h ▸ hb)
  have hidroot : K.vertexOf (K.inv d) ≠ T.root := fun h => he.not_isBoundaryVertex_inv (h ▸ hb)
  have hinvS : ∀ e, e ∈ S → K.inv e ∈ S := fun e h => (apply_mem_compl_pair_iff hinv d e).2 h
  by_cases hW : K.vertexOf d ∈ T.nonRoot
  · -- the edge lies in the tree: contract it in `P_T`
    have hW' : K.vertexOf (K.inv d) ∈ T.nonRoot := by
      rcases mem_insert.1 (T.vertexOf_inv_mem d hW) with h | h
      · exact absurd h hidroot
      · exact h
    have hdD := T.mem_darts_of_vertexOf_mem hW
    have hidD := T.mem_darts_of_vertexOf_mem hW'
    set P := T.plabicData
    have hP : P.IsPlabicGraph := T.isPlabicGraph_plabicData hK
    set dP : T.Dart := ⟨.inl d, hdD⟩
    have hPinv : P.inv dP = ⟨.inl (K.inv d), hidD⟩ := T.inv_inl hK hdD
    have heP : P.IsContractibleEdge dP :=
      { vertexOf_ne := by
          rw [hPinv]
          intro h
          apply he.vertexOf_ne
          have := congrArg (Finset.map (Function.Embedding.subtype _)) h
          rw [T.map_vertexOf_inl hK hdD hW, T.map_vertexOf_inl hK hidD hW'] at this
          exact Finset.map_injective _ this
        mem_internalVertices :=
          P.vertexOf_mem_internalVertices.2 (T.not_isBoundaryVertex_vertexOf_inl hK hdD hW)
        inv_mem_internalVertices := by
          rw [hPinv]
          exact P.vertexOf_mem_internalVertices.2 (T.not_isBoundaryVertex_vertexOf_inl hK hidD hW')
        colour_inv := by
          rw [hPinv]
          exact he.colour_inv }
    set R := P.contractEdge dP (heP.leg_mem hP)
    have hR : R.IsPlabicGraph := hP.contractEdge heP
    have hRf : R.faces.card = 1 :=
      (card_faces_contractEdge hP heP).trans (T.card_faces_plabicData hK)
    have hRc : PlabicGraph.MoveEquivalent {.m2, .m3} ⟨_, R, hR⟩ (lollipopPlabicGraph c) :=
      (PlabicGraph.MoveEquivalent.of_isLocalMove (S := {.m2, .m3}) (t := .m3) (by simp)
        (G := T.toPlabicGraph hK) (G' := ⟨_, R, hR⟩)
        (Or.inl ⟨dP, heP, PlabicData.Isomorphic.refl _⟩)).symm.trans hc
    let ι : T.Dart → H := fun x => T.baseDart x.1
    let φ : (({dP, P.inv dP} : Set T.Dart)ᶜ : Set T.Dart) → S := fun y => g (ι y)
    have hy : ∀ y : (({dP, P.inv dP} : Set T.Dart)ᶜ : Set T.Dart), y ∉ R.bdry →
        ∃ e, ∃ he : e ∈ T.darts,
        (y : T.Dart) = ⟨.inl e, he⟩ ∧ ∃ hS : e ∈ S, φ y = ⟨e, hS⟩ := by
      intro y hyB
      rw [mem_contractEdge_bdry] at hyB
      obtain ⟨e, he', hye⟩ := T.exists_eq_inl_of_notMem_bdry hb hyB
      have hy2 := mem_compl_pair_iff.1 y.2
      rw [hye, hPinv] at hy2
      have heS : e ∈ S := (hmemS e).2 ⟨fun h => hy2.1 (Subtype.ext (congrArg Sum.inl h)),
        fun h => hy2.2 (Subtype.ext (congrArg Sum.inl h))⟩
      refine ⟨e, he', hye, heS, Subtype.ext ?_⟩
      change (g (T.baseDart (y : T.Dart).1) : H) = e
      rw [hye]
      exact coe_inclOr heS
    -- the darts of `P_T` at the non-root vertices
    set A : Set T.Dart := {x | ∃ e, ∃ he : e ∈ T.darts, x = ⟨.inl e, he⟩ ∧
      K.vertexOf e ∈ T.nonRoot} with hA
    have hswap : ∀ x ∈ A, Equiv.swap dP (P.inv dP) x ∈ A ∧
        ι (Equiv.swap dP (P.inv dP) x) = Equiv.swap d (K.inv d) (ι x) := by
      rintro x ⟨e, he', rfl, heW⟩
      by_cases h1 : e = d
      · subst h1
        rw [show (⟨.inl e, he'⟩ : T.Dart) = dP from rfl, Equiv.swap_apply_left, hPinv]
        exact ⟨⟨_, hidD, rfl, hW'⟩, by
          change K.inv e = Equiv.swap e (K.inv e) e
          rw [Equiv.swap_apply_left]⟩
      by_cases h2 : e = K.inv d
      · subst h2
        have : (⟨.inl (K.inv d), he'⟩ : T.Dart) = P.inv dP := hPinv.symm
        rw [this, Equiv.swap_apply_right]
        refine ⟨⟨_, hdD, rfl, hW⟩, ?_⟩
        change d = Equiv.swap d (K.inv d) (T.baseDart (P.inv dP).1)
        rw [hPinv]
        exact (Equiv.swap_apply_right _ _).symm
      · have n1 : (⟨.inl e, he'⟩ : T.Dart) ≠ dP := fun h =>
          h1 (Sum.inl_injective (congrArg Subtype.val h))
        have n2 : (⟨.inl e, he'⟩ : T.Dart) ≠ P.inv dP := by
          rw [hPinv]
          exact fun h => h2 (Sum.inl_injective (congrArg Subtype.val h))
        rw [Equiv.swap_apply_of_ne_of_ne n1 n2]
        exact ⟨⟨e, he', rfl, heW⟩, (Equiv.swap_apply_of_ne_of_ne h1 h2).symm⟩
    have hrotA : ∀ x ∈ A, P.rot x ∈ A ∧ ι (P.rot x) = K.rot (ι x) := by
      rintro x ⟨e, he', rfl, heW⟩
      have hre : K.rot e ∈ T.darts := T.rot_mem_darts_of_vertexOf_mem heW
      rw [T.rot_inl_of_mem hK he' hre]
      exact ⟨⟨_, hre, rfl, by rwa [K.vertexOf_rot]⟩, rfl⟩
    have hτA : ∀ x ∈ A, (P.rot * Equiv.swap dP (P.inv dP)) x ∈ A := fun x hx =>
      (hrotA _ (hswap x hx).1).1
    have hτι : ∀ x ∈ A, ι ((P.rot * Equiv.swap dP (P.inv dP)) x) =
        (K.rot * Equiv.swap d (K.inv d)) (ι x) := fun x hx => by
      rw [Equiv.Perm.mul_apply, (hrotA _ (hswap x hx).1).2, (hswap x hx).2]
      rfl
    have hYA : ∀ x ∈ A, ι x ∈ S ↔ x ∈ (({dP, P.inv dP} : Set T.Dart)ᶜ : Set T.Dart) := by
      rintro x ⟨e, he', rfl, -⟩
      rw [hmemS, mem_compl_pair_iff, hPinv]
      change e ≠ d ∧ e ≠ K.inv d ↔ _
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (Sum.inl_injective (congrArg Subtype.val h)),
          fun h => h2 (Sum.inl_injective (congrArg Subtype.val h))⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h1 (Subtype.ext (congrArg Sum.inl h)),
          fun h => h2 (Subtype.ext (congrArg Sum.inl h))⟩
    obtain ⟨T', hT', hiso⟩ := exists_rootedTree_isomorphic_of_map hR hRf hK'' i φ
      (fun y y' hy1 hy1' h => by
        obtain ⟨e, he', hye, heS, hφ⟩ := hy y hy1
        obtain ⟨e', he'', hye', heS', hφ'⟩ := hy y' hy1'
        rw [hφ, hφ'] at h
        obtain rfl : e = e' := congrArg Subtype.val h
        exact Subtype.ext (hye.trans hye'.symm))
      (fun y hy1 => by
        obtain ⟨e, he', hye, heS, hφ⟩ := hy y hy1
        rw [hφ]
        apply Subtype.ext
        change (g (T.baseDart (R.inv y : T.Dart).1) : H) = _
        rw [coe_contractEdge_inv hP.inv_involutive, hye, T.inv_inl hK he',
          coe_contractEdge_inv hinv]
        exact coe_inclOr (hinvS e heS))
      (fun y hy1 hry => by
        obtain ⟨e, he', hye, heS, hφ⟩ := hy y hy1
        rcases T.vertexOf_mem_or_eq_root hK he' with heW | heR
        · have hyA : (y : T.Dart) ∈ A := ⟨e, he', hye, heW⟩
          obtain ⟨hmA, hmap⟩ := map_firstReturn_of_semiconjOn ι hτA hτι hYA y hyA
          have hRrot : (R.rot y : T.Dart) =
              (firstReturn (P.rot * Equiv.swap dP (P.inv dP))
                (({dP, P.inv dP} : Set T.Dart)ᶜ : Set T.Dart) y : T.Dart) := rfl
          have hKrot : ∀ z : S, (K''.rot z : H) =
              (firstReturn (K.rot * Equiv.swap d (K.inv d)) S z : H) := fun _ => rfl
          apply Subtype.ext
          change (g (ι (R.rot y : T.Dart)) : H) = _
          have hmS : ι (R.rot y : T.Dart) ∈ S := (hYA _ (hRrot ▸ hmA)).2 (R.rot y).2
          have hφy : φ y = ⟨ι (y : T.Dart), (hYA _ hyA).2 y.2⟩ := by
            rw [hφ]
            apply Subtype.ext
            change e = T.baseDart (y : T.Dart).1
            rw [hye]
            rfl
          rw [coe_inclOr hmS, hRrot, hmap, hφy, hKrot]
        · exfalso
          apply hry
          rw [mem_contractEdge_bdry]
          have hst : e = T.intervalStart := T.eq_intervalStart_of_isBoundaryVertex hK hb he' heR
          have hre : K.rot e ∉ T.darts := hst ▸ T.rot_intervalStart_notMem_of_isBoundaryVertex hK hb
          have hPr : P.rot (y : T.Dart) = T.dartEBar := by
            rw [hye]; exact T.rot_inl_of_notMem hK hb he' hre
          have hsw : Equiv.swap dP (P.inv dP) (y : T.Dart) = y :=
            Equiv.swap_apply_of_ne_of_ne (mem_compl_pair_iff.1 y.2).1 (mem_compl_pair_iff.1 y.2).2
          have hEB : T.dartEBar ∈ (({dP, P.inv dP} : Set T.Dart)ᶜ : Set T.Dart) := by
            rw [mem_compl_pair_iff, hPinv]
            exact ⟨fun h => by simp [RootedTree.dartEBar, dP] at h,
              fun h => by simp [RootedTree.dartEBar] at h⟩
          have : (R.rot y : T.Dart) = T.dartEBar := by
            change (firstReturn (P.rot * Equiv.swap dP (P.inv dP))
              (({dP, P.inv dP} : Set T.Dart)ᶜ : Set T.Dart) y : T.Dart) = _
            rw [coe_firstReturn_of_apply_mem (by rw [Equiv.Perm.mul_apply, hsw, hPr]; exact hEB),
              Equiv.Perm.mul_apply, hsw, hPr]
          rw [this]
          exact T.mem_bdry_plabicData.2 (Or.inr rfl))
      (fun y hy1 => by
        obtain ⟨e, he', hye, heS, hφ⟩ := hy y hy1
        rw [hφ, mem_contractEdge_bdry]
        exact T.notMem_bdry_of_mem_darts he')
      (fun y hy1 _ => by
        obtain ⟨e, he', hye, heS, hφ⟩ := hy y hy1
        rw [hφ, contractEdge_colour, contractEdge_colour]
        change K.colour e = T.colourAux (y : T.Dart).1
        rw [hye]
        rfl)
      (by
        apply Subtype.ext
        change (g (T.baseDart (T.legDart : H ⊕ LollipopDart)) : H) = K.leg i
        rw [T.coe_legDart hK hT]
        exact coe_inclOr hlegS)
    exact hasLollipopTree_of_isomorphic hK'' hT' (R := ⟨_, R, hR⟩) hiso hRc
  · -- the edge is not in the tree: the tree is unchanged
    have hW' : K.vertexOf (K.inv d) ∉ T.nonRoot := fun h => by
      rcases mem_insert.1 (T.vertexOf_inv_mem _ h) with h' | h' <;> rw [hinv] at h'
      · exact hdroot h'
      · exact hW h'
    have hmem : ∀ e ∈ T.darts, e ∈ S := by
      intro e he'
      refine (hmemS e).2 ⟨?_, ?_⟩ <;> rintro rfl
      · rcases T.vertexOf_mem_or_eq_root hK he' with h | h
        · exact hW h
        · exact hdroot h
      · rcases T.vertexOf_mem_or_eq_root hK he' with h | h
        · exact hW' h
        · exact hidroot h
    have hg : ∀ e ∈ T.darts, (g e : H) = e := fun e he' => coe_inclOr (hmem e he')
    obtain ⟨T', hT', hiso⟩ := T.exists_isomorphic_of_map hK hK'' hT g
      (fun x hx y hy h => by
        have := congrArg Subtype.val h
        rwa [hg x hx, hg y hy] at this)
      (fun e he' => by
        apply Subtype.ext
        rw [hg _ (T.inv_mem_darts hK he'), coe_contractEdge_inv hinv, hg e he'])
      (fun e he' hre => by
        apply Subtype.ext
        have hgr := hg e he'
        rw [hg _ hre, coe_contractEdge_rot_of_mem (by rw [hgr]; exact hmem _ hre), hgr])
      (fun e he' => by
        rw [mem_contractEdge_bdry, hg e he']
        exact T.notMem_bdry_of_mem_darts he')
      (fun e he' _ => by rw [contractEdge_colour, hg e he'])
      hgleg
    exact hasLollipopTree_of_isomorphic hK'' hT' (R := T.toPlabicGraph hK) hiso hc

/-- **Case (E)**, for an edge `{d, d̄}` with `σ d ≠ d`: a boundary tree of the contraction lifts.
If the merged vertex is a vertex of the tree, it is split in `P_T` as `G` is the splitting of its
contraction; otherwise the tree is a tree of the graph itself. -/
private theorem hasLollipopTree_of_contractEdge_of_rot_ne (hσ : K.rot d ≠ d) {i : Fin b}
    (h : HasLollipopTree (K.contractEdge d (he.leg_mem hK)) (hK.contractEdge he) i) :
    HasLollipopTree K hK i := by
  set S : Set H := (({d, K.inv d} : Set H)ᶜ : Set H) with hS
  set K'' := K.contractEdge d (he.leg_mem hK)
  have hK'' : K''.IsPlabicGraph := hK.contractEdge he
  have hinv := hK.inv_involutive
  obtain ⟨T, hT, c, hc⟩ := h
  have hb : K''.IsBoundaryVertex T.root := hT ▸ hK''.isBoundaryVertex_bvertex' i
  by_cases hM : ∃ x ∈ T.darts, (x : H) ∈ K.vertexOf d ∪ K.vertexOf (K.inv d)
  · -- the merged vertex is a vertex of the tree: split it in `P_T`
    obtain ⟨x, hxD, hxM⟩ := hM
    have ha : K.rot d ∈ S := mem_compl_pair_iff.2 ⟨hσ, fun h => he.vertexOf_ne (by
      rw [← h, K.vertexOf_rot])⟩
    set s : S := ⟨K.rot d, ha⟩
    have hsM : (s : H) ∈ K.vertexOf d ∪ K.vertexOf (K.inv d) :=
      mem_union_left _ (K.rot_mem_vertexOf d)
    have hvs : K''.vertexOf s = K''.vertexOf x :=
      Finset.map_injective (Function.Embedding.subtype _) (by
        rw [map_vertexOf_contractEdge_of_mem he.not_sameCycle hsM,
          map_vertexOf_contractEdge_of_mem he.not_sameCycle hxM])
    have hxint : ¬K''.IsBoundaryVertex (K''.vertexOf x) := by
      rw [isBoundaryVertex_vertexOf_contractEdge_iff he]
      exact fun h => he.notMem_of_isBoundaryVertex h hxM
    have hsW : K''.vertexOf s ∈ T.nonRoot := by
      rw [hvs]
      rcases T.vertexOf_mem_or_eq_root hK'' hxD with h | h
      · exact h
      · exact absurd (h ▸ hb) hxint
    have hsD : s ∈ T.darts := T.mem_darts_of_vertexOf_mem hsW
    have hzK : ¬K''.IsBoundaryVertex (K''.vertexOf s) := hvs ▸ hxint
    set p := (K.vertexOf d).card - 1
    have hcard : (K.vertexOf d).card = p + 1 := by
      have := card_pos.2 ⟨d, K.self_mem_vertexOf d⟩
      omega
    have θ : K.Iso (K''.vertexSplit s p) := contractEdgeSplitIso hK he hcard ha
    set KS := K''.vertexSplit s p with hKSdef
    have hKS : KS.IsPlabicGraph := hK''.vertexSplit hzK p
    set P := T.plabicData
    have hP : P.IsPlabicGraph := T.isPlabicGraph_plabicData hK''
    set sP : T.Dart := ⟨.inl s, hsD⟩ with hsPdef
    have hzP : ¬P.IsBoundaryVertex (P.vertexOf sP) :=
      T.not_isBoundaryVertex_vertexOf_inl hK'' hsD hsW
    have hp : p ≤ (P.vertexOf sP).card := by
      rw [T.card_vertexOf_inl hK'' hsD hsW, ← card_map (Function.Embedding.subtype _),
        map_vertexOf_contractEdge_of_mem he.not_sameCycle hsM]
      have hsub : (K.vertexOf d).erase d ⊆ K.mergedVertex d := by
        intro y hy
        obtain ⟨hyd, hy⟩ := mem_erase.1 hy
        refine mem_mergedVertex.2 ⟨Or.inl hy, hyd, fun h => he.vertexOf_ne ?_⟩
        rw [← h]
        exact (K.vertexOf_eq_of_mem hy).symm
      have := card_le_card hsub
      rw [card_erase_of_mem (K.self_mem_vertexOf d)] at this
      omega
    set R := P.vertexSplit sP p with hRdef
    have hR : R.IsPlabicGraph := hP.vertexSplit hzP p
    have heR : R.IsContractibleEdge (Sum.inr 0) := P.isContractibleEdge_vertexSplit sP p hzP hp
    have hRP : PlabicGraph.MoveEquivalent {.m2, .m3} ⟨_, R, hR⟩ (T.toPlabicGraph hK'') :=
      PlabicGraph.MoveEquivalent.of_isLocalMove (t := .m3) (by simp)
        (Or.inl ⟨Sum.inr 0, heR, P.isomorphic_contractEdge_vertexSplit sP p hP.inv_involutive⟩)
    have hRf : R.faces.card = 1 := hRP.card_eq.2.1.trans (T.card_faces_plabicData hK'')
    have hRc := hRP.trans hc
    let φ : T.Dart ⊕ Fin 2 → S ⊕ Fin 2 := Sum.map (fun y => T.baseDart y.1) id
    have hφl : ∀ (e : S) (he : e ∈ T.darts), φ (.inl ⟨.inl e, he⟩) = .inl e := fun _ _ => rfl
    have hφr : ∀ j, φ (.inr j) = .inr j := fun _ => rfl
    have hz : ∀ y : T.Dart, Sum.inl y ∉ R.bdry → ∃ e, ∃ he : e ∈ T.darts,
        y = ⟨.inl e, he⟩ := fun y hy =>
      T.exists_eq_inl_of_notMem_bdry hb (fun h => hy (by
        rw [hRdef, bdry_vertexSplit]
        exact mem_map_of_mem _ h))
    have hpow : ∀ n : ℕ, ((P.rot ^ n) sP : _ ⊕ LollipopDart) = .inl ((K''.rot ^ n) s) :=
      fun n => T.coe_rot_pow_inl hK'' hsD hsW n
    have hpowφ : ∀ n : ℕ, φ (.inl ((P.rot ^ n) sP)) = .inl ((K''.rot ^ n) s) := fun n => by
      change Sum.inl (T.baseDart ((P.rot ^ n) sP : _ ⊕ LollipopDart)) = _
      rw [hpow]
      rfl
    have hpowiff : ∀ (n : ℕ) (e : S) (he : e ∈ T.darts),
        (⟨.inl e, he⟩ : T.Dart) = (P.rot ^ n) sP ↔ e = (K''.rot ^ n) s := fun n e he => by
      rw [Subtype.ext_iff, hpow]
      exact Sum.inl_injective.eq_iff
    obtain ⟨T', hT', hiso⟩ := exists_rootedTree_isomorphic_of_map hR hRf hKS i φ
      (by
        rintro (y | j) (y' | j') hy hy' h
        · obtain ⟨e, he, rfl⟩ := hz y hy
          obtain ⟨e', he', rfl⟩ := hz y' hy'
          rw [hφl, hφl] at h
          obtain rfl : e = e' := Sum.inl_injective h
          rfl
        · obtain ⟨e, he, rfl⟩ := hz y hy
          rw [hφl, hφr] at h
          exact absurd h Sum.inl_ne_inr
        · obtain ⟨e', he', rfl⟩ := hz y' hy'
          rw [hφl, hφr] at h
          exact absurd h Sum.inr_ne_inl
        · rw [hφr, hφr] at h
          exact congrArg Sum.inr (Sum.inr_injective h))
      (by
        rintro (y | j) hy
        · obtain ⟨e, he, rfl⟩ := hz y hy
          change φ (Sum.inl (P.inv ⟨.inl e, he⟩)) = Sum.inl (K''.inv e)
          rw [T.inv_inl hK'' he]
          rfl
        · rcases fin_two_cases' j with rfl | rfl <;> rfl)
      (by
        rintro (y | j) hy hry
        · obtain ⟨e, he, rfl⟩ := hz y hy
          have hR1 : R.rot (Sum.inl ⟨.inl e, he⟩) =
              if p ≠ 0 ∧ (⟨.inl e, he⟩ : T.Dart) = (P.rot ^ (p - 1)) sP then Sum.inr 0
              else if P.rot ⟨.inl e, he⟩ = sP then Sum.inr 1
              else Sum.inl (P.rot ⟨.inl e, he⟩) := splitRot_inl _ _ _ _
          have hK1 : KS.rot (φ (Sum.inl ⟨.inl e, he⟩)) =
              if p ≠ 0 ∧ e = (K''.rot ^ (p - 1)) s then Sum.inr 0
              else if K''.rot e = s then Sum.inr 1
              else Sum.inl (K''.rot e) := splitRot_inl _ _ _ _
          rw [hK1]
          rw [hR1] at hry ⊢
          by_cases heW : K''.vertexOf e ∈ T.nonRoot
          · have hre : K''.rot e ∈ T.darts := T.rot_mem_darts_of_vertexOf_mem heW
            have hPr : P.rot ⟨.inl e, he⟩ = ⟨.inl (K''.rot e), hre⟩ := T.rot_inl_of_mem hK'' he hre
            have c2 : P.rot ⟨.inl e, he⟩ = sP ↔ K''.rot e = s := by
              rw [hPr, Subtype.ext_iff]
              exact Sum.inl_injective.eq_iff
            by_cases h1 : p ≠ 0 ∧ e = (K''.rot ^ (p - 1)) s
            · rw [if_pos h1, if_pos ⟨h1.1, (hpowiff _ e he).2 h1.2⟩]
              rfl
            · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, (hpowiff _ e he).1 h.2⟩)]
              by_cases h2 : K''.rot e = s
              · rw [if_pos h2, if_pos (c2.2 h2)]
                rfl
              · rw [if_neg h2, if_neg (fun h => h2 (c2.1 h)), hPr]
                rfl
          · exfalso
            have heR : K''.vertexOf e = T.root :=
              (T.vertexOf_mem_or_eq_root hK'' he).resolve_left heW
            have hst : e = T.intervalStart := T.eq_intervalStart_of_isBoundaryVertex hK'' hb he heR
            have hre : K''.rot e ∉ T.darts :=
              hst ▸ T.rot_intervalStart_notMem_of_isBoundaryVertex hK'' hb
            have hPr : P.rot ⟨.inl e, he⟩ = T.dartEBar := T.rot_inl_of_notMem hK'' hb he hre
            have n1 : ¬(p ≠ 0 ∧ (⟨.inl e, he⟩ : T.Dart) = (P.rot ^ (p - 1)) sP) := by
              rintro ⟨-, h⟩
              rw [hpowiff] at h
              apply heW
              rw [h, K''.vertexOf_pow_apply]
              exact hsW
            have n2 : P.rot ⟨.inl e, he⟩ ≠ sP := by
              rw [hPr]
              intro h
              have := congrArg Subtype.val h
              simp [RootedTree.dartEBar, hsPdef] at this
            rw [if_neg n1, if_neg n2, hPr] at hry
            apply hry
            rw [hRdef, bdry_vertexSplit]
            exact mem_map_of_mem _ (T.mem_bdry_plabicData.2 (Or.inr rfl))
        · rcases fin_two_cases' j with rfl | rfl
          · change φ (splitRot P.rot sP p (Sum.inr 0)) = splitRot K''.rot s p (Sum.inr 0)
            rw [splitRot_inr_zero, splitRot_inr_zero]
            split_ifs <;> rfl
          · change φ (splitRot P.rot sP p (Sum.inr 1)) = splitRot K''.rot s p (Sum.inr 1)
            rw [splitRot_inr_one, splitRot_inr_one]
            have hiff : (P.rot ^ p) sP = sP ↔ (K''.rot ^ p) s = s := by
              rw [Subtype.ext_iff, hpow]
              exact Sum.inl_injective.eq_iff
            by_cases h1 : p ≠ 0 ∧ (K''.rot ^ p) s = s
            · rw [if_pos h1, if_pos ⟨h1.1, hiff.2 h1.2⟩]
              rfl
            · rw [if_neg h1, if_neg (fun h => h1 ⟨h.1, hiff.1 h.2⟩)]
              exact hpowφ p)
      (by
        rintro (y | j) hy
        · obtain ⟨e, he, rfl⟩ := hz y hy
          rw [hφl, hKSdef, bdry_vertexSplit]
          intro h
          obtain ⟨e', he', hee⟩ := mem_map.1 h
          have := Sum.inl_injective hee
          subst this
          exact T.notMem_bdry_of_mem_darts he he'
        · rw [hφr, hKSdef, bdry_vertexSplit]
          intro h
          obtain ⟨e', -, hee⟩ := mem_map.1 h
          exact Sum.inl_ne_inr hee)
      (by
        rintro (y | j) hy _
        · obtain ⟨e, he, rfl⟩ := hz y hy
          rfl
        · rfl)
      (by
        change Sum.inl (T.baseDart (T.legDart : _ ⊕ LollipopDart)) = Sum.inl (K''.leg i)
        rw [T.coe_legDart hK'' hT]
        rfl)
    exact HasLollipopTree.of_iso hKS hK θ.symm
      (hasLollipopTree_of_isomorphic hKS hT' (R := ⟨_, R, hR⟩) hiso hRc)
  · -- the merged vertex is not a vertex of the tree: the tree is a tree of `K`
    push Not at hM
    have hnotM : ∀ e ∈ T.darts, K.rot (e : H) ∈ S := by
      intro e he'
      have h' : K.vertexOf (K.rot (e : H)) = K.vertexOf (e : H) := K.vertexOf_rot _
      refine mem_compl_pair_iff.2 ⟨fun h => hM e he' (mem_union_left _ ?_),
        fun h => hM e he' (mem_union_right _ ?_)⟩
      · rw [h] at h'
        rw [h']
        exact K.self_mem_vertexOf _
      · rw [h] at h'
        rw [h']
        exact K.self_mem_vertexOf _
    obtain ⟨T', hT', hiso⟩ := T.exists_isomorphic_of_map hK'' hK hT Subtype.val
      Subtype.val_injective.injOn
      (fun e _ => coe_contractEdge_inv hinv e)
      (fun e he' _ => coe_contractEdge_rot_of_mem (hnotM e he'))
      (fun e he' => by
        rw [← mem_contractEdge_bdry]
        exact T.notMem_bdry_of_mem_darts he')
      (fun _ _ _ => rfl)
      rfl
    exact hasLollipopTree_of_isomorphic hK hT' (R := T.toPlabicGraph hK'') hiso hc

/-- **Case (E)**: a boundary tree of the contraction of an edge lifts. -/
private theorem hasLollipopTree_of_contractEdge {i : Fin b}
    (h : HasLollipopTree (K.contractEdge d (he.leg_mem hK)) (hK.contractEdge he) i) :
    HasLollipopTree K hK i := by
  rcases rot_ne_or_rot_inv_ne hK he with hσ | hσ
  · exact hasLollipopTree_of_contractEdge_of_rot_ne hK he hσ h
  · have he' := IsContractibleEdge.inv'' hK he
    exact hasLollipopTree_of_contractEdge_of_rot_ne hK he' hσ
      (HasLollipopTree.of_iso _ _ (contractEdgeInvIso' hK he) h)

end Contraction

end PlabicData

/-! ### Lollipops and boundary trees along a move equivalence -/

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- One step of a move equivalence keeps a boundary tree whose plabic graph reduces to a lollipop
graph. -/
private theorem hasLollipopTree_of_moveStep {G G' : PlabicGraph b} (h : MoveStep Set.univ G G')
    {i : Fin b} (hG : HasLollipopTree G.data G.isPlabicGraph i) :
    HasLollipopTree G'.data G'.isPlabicGraph i := by
  rcases h with hiso | ⟨t, -, ht⟩
  · obtain ⟨θ⟩ : G'.data.Isomorphic G.data := hiso
    exact HasLollipopTree.of_iso _ _ θ.symm hG
  cases t with
  | m1 =>
    obtain ⟨c, hq, ⟨θ⟩⟩ := ht
    exact HasLollipopTree.of_iso _ _ θ.symm (HasLollipopTree.squareMove G.isPlabicGraph hq hG)
  | m2 =>
    rcases ht with ⟨d, hd, ⟨θ⟩⟩ | ⟨d, hd, ⟨θ⟩⟩
    · exact HasLollipopTree.of_iso _ _ θ.symm
        (hasLollipopTree_bivalentRemoval G.isPlabicGraph hd hG)
    · exact hasLollipopTree_of_bivalentRemoval G'.isPlabicGraph hd
        (HasLollipopTree.of_iso _ _ θ hG)
  | m3 =>
    rcases ht with ⟨d, he, ⟨θ⟩⟩ | ⟨d, he, ⟨θ⟩⟩
    · exact HasLollipopTree.of_iso _ _ θ.symm (hasLollipopTree_contractEdge G.isPlabicGraph he hG)
    · exact hasLollipopTree_of_contractEdge G'.isPlabicGraph he (HasLollipopTree.of_iso _ _ θ hG)

/-- **Lollipops and boundary trees persist under local moves**.
Let `G` and `G'` be plabic graphs with `b` boundary vertices and `G ∼ G'`, and let `i` be a label.
If `G` has a lollipop at `i` or a collapsible tree with root `β(i)`, then so does `G'`. Labels are
`0`-indexed, so `i : Fin b` is the boundary label `i + 1` in `1`-indexed notation. -/
@[cluster_algebras "lem_fixed_lollipop_invariant"]
theorem MoveEquivalent.exists_isLollipop_or_isCollapsible {G G' : PlabicGraph b}
    (h : MoveEquivalent Set.univ G G') (i : Fin b)
    (hG : (∃ v, G.data.IsLollipop i v) ∨
      ∃ T : G.data.RootedTree, T.root = G.data.bvertex i ∧ T.IsCollapsible) :
    (∃ v, G'.data.IsLollipop i v) ∨
      ∃ T : G'.data.RootedTree, T.root = G'.data.bvertex i ∧ T.IsCollapsible := by
  have h0 : HasLollipopTree G.data G.isPlabicGraph i := by
    rcases hG with ⟨v, hv⟩ | ⟨T, hT, c, hc⟩
    · exact IsLollipop.hasLollipopTree G.isPlabicGraph hv
    · exact ⟨T, hT, c, hc.moveEquivalent⟩
  refine HasLollipopTree.isLollipop_or_isCollapsible (hK := G'.isPlabicGraph) ?_
  induction h with
  | refl => exact h0
  | tail _ hst ih => exact hasLollipopTree_of_moveStep hst ih

end PlabicGraph

end ClusterAlgebras
