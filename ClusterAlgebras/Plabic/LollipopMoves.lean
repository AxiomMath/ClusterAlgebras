/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.LeafGluing
public import ClusterAlgebras.Plabic.LollipopInsertion
public import ClusterAlgebras.Plabic.Reduced

/-!
# Lollipops, leaf gluings and local moves

This file collects facts about lollipops and gluings used in the classification of reduced plabic
graphs by their decorated trip permutations.

A loop around an empty face is forbidden in a reduced plabic graph: inserting a bivalent vertex on
the loop produces a hollow digon.

Inserting a lollipop does not disturb a plabic graph `A`: the trips of `A` are trips of
`I_i(A, c)`, with the labels `j` shifted to `j⁺`, and the collapsible trees of `A` are those of
`I_i(A, c)`. The local moves of `A` are local moves of `I_i(A, c)`: a square move, the removal of
a bivalent vertex or the contraction of an edge of `A` involves only internal vertices of `A`,
which are internal vertices of `I_i(A, c)` with the same darts, rotation and colours, so the same
move applies to `I_i(A, c)` and inserting the lollipop into the result gives the same plabic graph
up to isomorphism. Hence move-equivalent plabic graphs have move-equivalent insertions. In the
same way, the local moves of a plabic graph `R` with one boundary vertex are local moves of the
gluing `Y⟨f ← R⟩` of `R` into a leaf `{f}` of a plabic graph `Y`, and move-equivalent plabic
graphs `R ∼ R'` have move-equivalent gluings.

## Main definitions

* `ClusterAlgebras.PlabicGraph.lollipopInsertion`, `ClusterAlgebras.PlabicGraph.leafGluing`: the
  insertion of a lollipop and the gluing into a leaf, as bundled plabic graphs.
* `ClusterAlgebras.PlabicData.RootedTree.lollipopInsertion`: a rooted tree of `A` as a rooted tree
  of `I_i(A, c)`.

## Main results

* `ClusterAlgebras.PlabicGraph.not_isReduced_of_card_eq_one`: a plabic graph with an internal
  face consisting of one dart is not reduced.
* `ClusterAlgebras.PlabicData.tripPerm_lollipopInsertion_succAbove`:
  `π_{I_i(A, c)}(j⁺) = π_A(j)⁺`.
* `ClusterAlgebras.PlabicData.exists_isCollapsibleOfColour_lollipopInsertion_iff`: the collapsible
  trees of `A` are those of `I_i(A, c)`.
* `ClusterAlgebras.PlabicGraph.MoveEquivalent.map_of_commute`: a construction on plabic graphs
  that commutes with isomorphisms, square moves, removals and contractions preserves
  `S`-equivalence.
* `ClusterAlgebras.PlabicGraph.MoveEquivalent.lollipopInsertion`: if `A ∼ A'`, then
  `I_i(A, c) ∼ I_i(A', c)`.
* `ClusterAlgebras.PlabicGraph.MoveEquivalent.leafGluing`: if `R ∼ R'`, then
  `Y⟨f ← R⟩ ∼ Y⟨f ← R'⟩`.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`, and the relabelling
  `j ↦ j⁺` of the insertion of a lollipop is `Fin.succAbove i`.
* The darts of `I_i(A, c)` are `H ⊕ Fin 4` and those of `Y⟨f ← R⟩` form a subset of `H_Y ⊕ H_R`,
  so the new darts are disjoint from the old ones by construction, and the choice of fresh darts
  made in FWZ is not needed. A set of darts `s` and a set of vertices `W` of `A` are read in
  `I_i(A, c)` as `s.map Sum.inl` and `W.image (Finset.map Sum.inl)`.
* The two results on move equivalence are stated for `S`-equivalence for any set `S` of types of
  local moves; move equivalence `∼` is the case `S = Set.univ`. Both are instances of
  `MoveEquivalent.map_of_commute`: FWZ's case analysis on the steps of a sequence of moves
  is carried out once there.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset _root_.Equiv _root_.Equiv.Perm

/-- Every element of `Fin 4` is one of `0, 1, 2, 3`. -/
private theorem fin_cases_four (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  revert k; decide

/-! ### A loop around an empty face -/

/-- The orbit of a point exchanged with another one by a permutation is the pair of them. -/
private theorem RotationSystem.faceOf_eq_pair {X : Type*} [Fintype X] [DecidableEq X]
    (R : RotationSystem X) {x y : X} (hxy : R.facePerm x = y) (hyx : R.facePerm y = x) :
    R.faceOf x = {x, y} := by
  ext z
  rw [RotationSystem.mem_faceOf]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have := ih ⟨(n : ℤ), by rw [zpow_natCast]⟩
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with h | h <;> rw [h] <;> simp [hxy, hyx]
  · simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← hxy]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- **A loop around an empty face is forbidden**: a plabic graph with an internal face consisting
of exactly one dart is not reduced. -/
@[cluster_algebras "lem_empty_loop_not_reduced"]
theorem not_isReduced_of_card_eq_one (K : PlabicGraph b) {f : Finset K.Dart}
    (hf : f ∈ K.data.internalFaces) (hcard : f.card = 1) : ¬K.IsReduced := by
  intro hK
  have hG := K.isPlabicGraph
  obtain ⟨d, rfl⟩ := card_eq_one.1 hcard
  obtain ⟨hfaces, hdisj⟩ := K.data.mem_internalFaces.1 hf
  have hd : d ∉ K.data.bdry := disjoint_singleton_left.1 hdisj
  obtain ⟨e, he⟩ := K.data.mem_faceOrbits.1 (K.data.mem_faces.1 hfaces).2
  have hde : K.data.faceOf d = {d} := by
    rw [← he, K.data.faceOf_eq_of_mem (he ▸ mem_singleton_self d)]
  have hφ : K.data.facePerm d = d := by
    have := K.data.facePerm_mem_faceOf d
    rwa [hde, mem_singleton] at this
  have hinv := hG.inv_involutive
  have hfix := hG.inv_ne d
  set c := K.data.colour d
  let K₁ : PlabicGraph b :=
    ⟨K.Dart ⊕ Fin 2, K.data.bivalentInsertion d c, isPlabicGraph_bivalentInsertion c hG hd⟩
  have hstep : MoveEquivalent Set.univ K₁ K :=
    MoveEquivalent.of_isLocalMove (t := .m2) trivial
      (Or.inl ⟨Sum.inr 0, isBivalentRemovable_bivalentInsertion d c,
        (bivalentRemoval_bivalentInsertion_isomorphic c hG hd).symm⟩)
  refine (hK K₁ hstep).1 {Sum.inl d, Sum.inr 1} ⟨?_, Sum.inl d, Sum.inr 1, rfl, ?_⟩
  · have h1 : K₁.data.facePerm (Sum.inl d) = Sum.inr 1 :=
      bivalentInsertion_facePerm_inl_self c hfix
    have h2 : K₁.data.facePerm (Sum.inr 1) = Sum.inl d := by
      rw [show K₁.data.facePerm (Sum.inr 1) = Sum.inl (K.data.facePerm d) from
        bivalentInsertion_facePerm_inr_one c hfix, hφ]
    rw [← RotationSystem.faceOf_eq_pair _ h1 h2]
    refine K₁.data.mem_internalFaces.2 ⟨DiskMap.faceOf_mem_faces _ ?_, ?_⟩
    · exact (inl_mem_bivalentInsertion_bdry d c).not.2 hd
    · rw [RotationSystem.faceOf_eq_pair _ h1 h2, disjoint_insert_left, disjoint_singleton_left]
      exact ⟨(inl_mem_bivalentInsertion_bdry d c).not.2 hd,
        inr_notMem_bivalentInsertion_bdry d c 1⟩
  · intro h
    have hmem : (Sum.inr 1 : K.Dart ⊕ Fin 2) ∈ K₁.data.vertexOf (Sum.inl d) := by
      rw [h]
      exact K₁.data.self_mem_vertexOf _
    rw [show K₁.data.vertexOf (Sum.inl d) = (K.data.vertexOf d).map Function.Embedding.inl from
      bivalentInsertion_vertexOf_inl d c d] at hmem
    simp at hmem

end PlabicGraph

/-! ### Trips of an insertion -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} [NeZero b] {A : PlabicData H b}
  {i : Fin (b + 1)} {c : Shade}

/-- Away from `B`, the trip map of `I_i(A, c)` is that of `A`. -/
theorem tripMap_lollipopInsertion_inl (hA : A.IsPlabicGraph) {z : H} (hz : z ∉ A.bdry) :
    (A.lollipopInsertion i c).tripMap (Sum.inl z) = Sum.inl (A.tripMap z) := by
  have hh : z ≠ A.lollipopArc i := fun h =>
    hz (h ▸ A.exterior_subset_bdry hA.lollipopArc_mem_exterior)
  have hh' : z ≠ A.inv (A.lollipopArc i) := fun h =>
    hz (h ▸ hA.inv_mem_bdry _ (A.exterior_subset_bdry hA.lollipopArc_mem_exterior))
  rw [tripMap_apply, tripMap_apply, lollipopInsertion_inv_inl_of_ne A i c hh hh']
  have hiff := isBoundaryVertex_lollipopInsertion_vertexOf_inl (A := A) (i := i) c (A.inv z)
  by_cases hb : A.IsBoundaryVertex (A.vertexOf (A.inv z))
  · rw [turn_of_isBoundaryVertex (hiff.2 hb), turn_of_isBoundaryVertex hb]
  · cases hc : A.colour (A.inv z)
    · rw [turn_of_white (hiff.not.2 hb) (by rwa [lollipopInsertion_colour_inl]),
        turn_of_white hb hc]
      rfl
    · rw [turn_of_black (hiff.not.2 hb) (by rwa [lollipopInsertion_colour_inl]),
        turn_of_black hb hc]
      rfl

omit [Fintype H] in
/-- The legs of `I_i(A, c)` lying in `H` are the legs of `A`. -/
theorem isLeg_lollipopInsertion_inl {x : H} :
    (A.lollipopInsertion i c).IsLeg (Sum.inl x) ↔ A.IsLeg x := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · simp at hk
    · rw [lollipopInsertion_leg_succAbove] at hk
      exact ⟨j, Sum.inl_injective hk⟩
  · rintro ⟨j, rfl⟩
    exact ⟨i.succAbove j, lollipopInsertion_leg_succAbove A i c j⟩

/-- Starting from a dart `z` of `A` not in `B`, the iterates of the trip map of `I_i(A, c)` are
those of `A`. -/
theorem iterate_tripMap_lollipopInsertion_inl (hA : A.IsPlabicGraph) {z : H} (hz : z ∉ A.bdry)
    (n : ℕ) :
    (A.lollipopInsertion i c).tripMap^[n] (Sum.inl z) = Sum.inl (A.tripMap^[n] z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      tripMap_lollipopInsertion_inl hA hz, ih ((not_congr (tripMap_mem_bdry_iff hA z)).2 hz)]

/-- **Trips of an insertion**: for a plabic graph `A`, `π_{I_i(A, c)}(j⁺) = π_A(j)⁺` for every
label `j` of `A`. -/
@[cluster_algebras "lem_lollipop_insertion_trips"]
theorem tripPerm_lollipopInsertion_succAbove (hA : A.IsPlabicGraph) (j : Fin b) :
    (A.lollipopInsertion i c).tripPerm (i.succAbove j) = i.succAbove (A.tripPerm j) := by
  have hI := hA.lollipopInsertion i c
  have hlen : (A.lollipopInsertion i c).tripLength (i.succAbove j) = A.tripLength j := by
    unfold tripLength
    congr 1
    ext m
    simp only [Set.mem_setOf_eq, lollipopInsertion_leg_succAbove,
      iterate_tripMap_lollipopInsertion_inl hA (hA.leg_notMem_bdry j), isLeg_lollipopInsertion_inl]
  apply hI.leg_injective
  rw [hI.leg_tripPerm, hlen, lollipopInsertion_leg_succAbove,
    iterate_tripMap_lollipopInsertion_inl hA (hA.leg_notMem_bdry j), ← hA.leg_tripPerm,
    lollipopInsertion_leg_succAbove]

end PlabicData

/-! ### Collapsible trees of an insertion -/

namespace PlabicData

section Transport

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} [NeZero b] {A : PlabicData H b}
  {i : Fin (b + 1)} {c : Shade}

omit [Fintype H] [DecidableEq H] in
private theorem inr_notMem_map_inl {s : Finset H} (k : Fin 4) :
    (Sum.inr k : H ⊕ Fin 4) ∉ s.map Function.Embedding.inl := by
  simp

omit [Fintype H] in
/-- A set of darts `s` of `A`, read in `H ⊕ Fin 4`, lies in the image of `W` if and only if
`s ∈ W`. -/
theorem map_inl_mem_image_map_inl {W : Finset (Finset H)} {s : Finset H} :
    s.map Function.Embedding.inl ∈ W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4)) ↔
      s ∈ W := by
  rw [mem_image]
  exact ⟨fun ⟨t, ht, h⟩ => Finset.map_injective _ h ▸ ht, fun h => ⟨s, h, rfl⟩⟩

omit [Fintype H] in
/-- An element of the image of `W` in `Finset (H ⊕ Fin 4)` is the image of an element of `W`. -/
theorem exists_eq_map_inl_of_mem_image {W : Finset (Finset H)} {w : Finset (H ⊕ Fin 4)}
    (hw : w ∈ W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4))) :
    ∃ s ∈ W, w = s.map Function.Embedding.inl := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hw
  exact ⟨s, hs, rfl⟩

/-- Away from `B`, the involution of `I_i(A, c)` is that of `A`. -/
theorem lollipopInsertion_inv_inl_of_notMem_bdry (hA : A.IsPlabicGraph) {x : H}
    (hx : x ∉ A.bdry) :
    (A.lollipopInsertion i c).inv (Sum.inl x) = Sum.inl (A.inv x) := by
  refine lollipopInsertion_inv_inl_of_ne A i c (fun h => hx ?_) (fun h => hx ?_)
  · exact h ▸ A.exterior_subset_bdry hA.lollipopArc_mem_exterior
  · exact h ▸ hA.inv_mem_bdry _ (A.exterior_subset_bdry hA.lollipopArc_mem_exterior)

omit [Fintype H] in
/-- On the darts of `A`, the powers of the rotation of `I_i(A, c)` are those of `A`. -/
theorem lollipopInsertion_rot_pow_inl (n : ℕ) (x : H) :
    ((A.lollipopInsertion i c).rot ^ n) (Sum.inl x) = Sum.inl ((A.rot ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]; rfl

omit [Fintype H] in
/-- On the darts of `A`, the inverse rotation of `I_i(A, c)` is that of `A`. -/
theorem lollipopInsertion_rot_symm_inl (x : H) :
    (A.lollipopInsertion i c).rot.symm (Sum.inl x) = Sum.inl (A.rot.symm x) := by
  rw [Equiv.symm_apply_eq, lollipopInsertion_rot_inl, Equiv.apply_symm_apply]

omit [Fintype H] in
/-- A set of darts of `A` is a boundary vertex of `I_i(A, c)` if and only if it is one of `A`. -/
theorem isBoundaryVertex_lollipopInsertion_map_inl {s : Finset H} :
    (A.lollipopInsertion i c).IsBoundaryVertex (s.map Function.Embedding.inl) ↔
      A.IsBoundaryVertex s := by
  simp [DiskMap.IsBoundaryVertex]

/-- A set of darts of `A` is a vertex of `I_i(A, c)` if and only if it is a vertex of `A`. -/
theorem map_inl_mem_lollipopInsertion_vertices {s : Finset H} :
    s.map Function.Embedding.inl ∈ (A.lollipopInsertion i c).vertices ↔ s ∈ A.vertices := by
  rw [RotationSystem.mem_vertices, RotationSystem.mem_vertices]
  constructor
  · rintro ⟨x | k, hx⟩
    · rw [lollipopInsertion_vertexOf_inl] at hx
      exact ⟨x, Finset.map_injective _ hx⟩
    · have := hx ▸ (A.lollipopInsertion i c).self_mem_vertexOf (Sum.inr k)
      exact absurd this (inr_notMem_map_inl k)
  · rintro ⟨x, rfl⟩
    exact ⟨Sum.inl x, lollipopInsertion_vertexOf_inl c x⟩

/-- A set of darts of `A` is an internal vertex of `I_i(A, c)` if and only if it is an internal
vertex of `A`. -/
theorem map_inl_mem_lollipopInsertion_internalVertices {s : Finset H} :
    s.map Function.Embedding.inl ∈ (A.lollipopInsertion i c).internalVertices ↔
      s ∈ A.internalVertices := by
  rw [DiskMap.mem_internalVertices, DiskMap.mem_internalVertices,
    map_inl_mem_lollipopInsertion_vertices, isBoundaryVertex_lollipopInsertion_map_inl]

/-- A new dart of `I_i(A, c)` does not lie at a vertex of `A`. -/
theorem lollipopInsertion_vertexOf_inr_notMem {W : Finset (Finset H)} (k : Fin 4) :
    (A.lollipopInsertion i c).vertexOf (Sum.inr k) ∉
      W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4)) := fun h => by
  obtain ⟨s, -, hs⟩ := exists_eq_map_inl_of_mem_image h
  have := hs ▸ (A.lollipopInsertion i c).self_mem_vertexOf (Sum.inr k)
  exact inr_notMem_map_inl k this

/-- The darts of the edges of a set `W` of vertices of `A` are the same in `I_i(A, c)`. -/
theorem treeDarts_lollipopInsertion (hA : A.IsPlabicGraph) (W : Finset (Finset H)) :
    (A.lollipopInsertion i c).treeDarts
      (W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4))) =
      (A.treeDarts W).map Function.Embedding.inl := by
  ext y
  rw [mem_treeDarts]
  rcases y with x | k
  · rw [show (Sum.inl x : H ⊕ Fin 4) ∈ (A.treeDarts W).map Function.Embedding.inl ↔
        x ∈ A.treeDarts W from Finset.mem_map' _, mem_treeDarts, mem_lollipopInsertion_bdry_inl]
    by_cases hx : x ∈ A.bdry
    · simp [hx]
    · rw [lollipopInsertion_inv_inl_of_notMem_bdry hA hx, lollipopInsertion_vertexOf_inl,
        lollipopInsertion_vertexOf_inl, map_inl_mem_image_map_inl, map_inl_mem_image_map_inl]
  · simp only [mem_lollipopInsertion_bdry_inr, mem_map, Function.Embedding.inl_apply,
      reduceCtorEq, and_false, exists_false, iff_false, not_and, not_or]
    intro hk
    refine ⟨lollipopInsertion_vertexOf_inr_notMem k, ?_⟩
    rcases fin_cases_four k with rfl | rfl | rfl | rfl
    · exact absurd rfl hk.1
    · exact absurd rfl hk.2
    · rw [lollipopInsertion_inv_inr_two]
      exact lollipopInsertion_vertexOf_inr_notMem 3
    · rw [lollipopInsertion_inv_inr_three]
      exact lollipopInsertion_vertexOf_inr_notMem 2

end Transport

section Trees

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} [NeZero b] {A : PlabicData H b}
  {i : Fin (b + 1)} {c : Shade}

omit [Fintype H] in
/-- `Sum.inl x` lies in the image of `s` under `Sum.inl` if and only if `x ∈ s`. -/
theorem inl_mem_map_inl_iff {α β : Type*} {s : Finset α} {x : α} :
    (Sum.inl x : α ⊕ β) ∈ s.map Function.Embedding.inl ↔ x ∈ s :=
  Finset.mem_map' _

omit [NeZero b] in
/-- A rooted tree is determined by its root and its non-root vertices. -/
private theorem RootedTree.ext' {G : PlabicData H b} {T T' : G.RootedTree}
    (h₁ : T.root = T'.root) (h₂ : T.nonRoot = T'.nonRoot) : T = T' := by
  obtain ⟨r, W, _, _, _, _, _, _, _, _⟩ := T
  obtain ⟨r', W', _, _, _, _, _, _, _, _⟩ := T'
  dsimp only at h₁ h₂
  subst h₁ h₂
  rfl

omit [NeZero b] in
/-- The first dart `a₁` of the interval of a rooted tree is the only dart of `D_T` at the root
whose predecessor `σ⁻¹ a₁` is not in `D_T`. -/
private theorem RootedTree.eq_intervalStart {G : PlabicData H b} (T : G.RootedTree) {a : H}
    (ha : a ∈ T.root) (had : a ∈ T.darts) (hnot : G.rot.symm a ∉ T.darts) :
    a = T.intervalStart := by
  obtain ⟨j, hj, rfl⟩ := (T.mem_darts_iff_of_mem_root ha).1 had
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rfl
  · exfalso
    apply hnot
    have hmem : G.rot.symm ((G.rot ^ j) T.intervalStart) ∈ T.root := by
      rw [T.mem_root_iff, G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf _)]
      exact T.mem_root_iff.1 ha
    refine (T.mem_darts_iff_of_mem_root hmem).2 ⟨j - 1, by omega, ?_⟩
    rw [Equiv.eq_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hj0]

/-- Two vertices of `A` adjacent along an edge of `W` are adjacent along an edge of the image of
`W` in `I_i(A, c)`. -/
theorem treeAdj_lollipopInsertion_map (hA : A.IsPlabicGraph) {W : Finset (Finset H)}
    {u u' : Finset H} (h : A.TreeAdj W u u') :
    (A.lollipopInsertion i c).TreeAdj
      (W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4)))
      (u.map Function.Embedding.inl) (u'.map Function.Embedding.inl) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  refine ⟨Sum.inl d, ?_, lollipopInsertion_vertexOf_inl c d, ?_⟩
  · rw [treeDarts_lollipopInsertion hA]
    exact inl_mem_map_inl_iff.2 hd
  · rw [lollipopInsertion_inv_inl_of_notMem_bdry hA (mem_treeDarts.1 hd).1,
      lollipopInsertion_vertexOf_inl]

/-- In `I_i(A, c)`, a vertex adjacent to a vertex `u` of `A` along an edge of the image of `W` is
a vertex of `A` adjacent to `u` along an edge of `W`. -/
theorem exists_of_treeAdj_lollipopInsertion (hA : A.IsPlabicGraph)
    {W : Finset (Finset H)} {u : Finset H} {w : Finset (H ⊕ Fin 4)}
    (h : (A.lollipopInsertion i c).TreeAdj
      (W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4)))
      (u.map Function.Embedding.inl) w) :
    ∃ u', w = u'.map Function.Embedding.inl ∧ A.TreeAdj W u u' := by
  obtain ⟨d, hd, hdu, rfl⟩ := h
  rw [treeDarts_lollipopInsertion hA] at hd
  obtain ⟨x, hx, hxd⟩ := mem_map.1 hd
  rw [Function.Embedding.inl_apply] at hxd
  subst hxd
  refine ⟨A.vertexOf (A.inv x), ?_, x, hx, ?_, rfl⟩
  · rw [lollipopInsertion_inv_inl_of_notMem_bdry hA (mem_treeDarts.1 hx).1,
      lollipopInsertion_vertexOf_inl]
  · rw [lollipopInsertion_vertexOf_inl] at hdu
    exact Finset.map_injective _ hdu

/-- In `I_i(A, c)`, a vertex joined to a vertex `u` of `A` by a path of edges of the image of `W`
is a vertex of `A` joined to `u` by a path of edges of `W`. -/
theorem exists_of_reflTransGen_treeAdj_lollipopInsertion (hA : A.IsPlabicGraph)
    {W : Finset (Finset H)} {u : Finset H} {w : Finset (H ⊕ Fin 4)}
    (h : Relation.ReflTransGen ((A.lollipopInsertion i c).TreeAdj
      (W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4))))
      (u.map Function.Embedding.inl) w) :
    ∃ u', w = u'.map Function.Embedding.inl ∧ Relation.ReflTransGen (A.TreeAdj W) u u' := by
  induction h with
  | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
    obtain ⟨u', rfl, hu'⟩ := ih
    obtain ⟨u'', rfl, h''⟩ := exists_of_treeAdj_lollipopInsertion hA hbc
    exact ⟨u'', rfl, hu'.tail h''⟩

/-- The edges of a set `W` of vertices of `A` are the same in `I_i(A, c)`. -/
theorem card_image_edgeOf_lollipopInsertion (hA : A.IsPlabicGraph)
    (W : Finset (Finset H)) :
    (((A.lollipopInsertion i c).treeDarts
      (W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4)))).image
        (A.lollipopInsertion i c).edgeOf).card = ((A.treeDarts W).image A.edgeOf).card := by
  rw [treeDarts_lollipopInsertion hA, map_eq_image, image_image]
  have : ((A.treeDarts W).image ((A.lollipopInsertion i c).edgeOf ∘ Function.Embedding.inl)) =
      ((A.treeDarts W).image A.edgeOf).image (Finset.map Function.Embedding.inl) := by
    rw [image_image]
    refine image_congr fun x hx => ?_
    simp only [Function.comp_apply, Function.Embedding.inl_apply, RotationSystem.edgeOf,
      lollipopInsertion_inv_inl_of_notMem_bdry hA (mem_treeDarts.1 hx).1, map_insert,
      map_singleton]
  rw [this, card_image_of_injective _ (Finset.map_injective _)]

/-- **A rooted tree of `A` is a rooted tree of `I_i(A, c)`**: the root and the non-root vertices
of a rooted tree `(v, W)` of a plabic graph `A` form a rooted tree of `I_i(A, c)`. -/
def RootedTree.lollipopInsertion (hA : A.IsPlabicGraph) (i : Fin (b + 1)) (c : Shade)
    (T : A.RootedTree) : (A.lollipopInsertion i c).RootedTree where
  root := T.root.map Function.Embedding.inl
  nonRoot := T.nonRoot.image (Finset.map Function.Embedding.inl)
  root_mem_vertices := map_inl_mem_lollipopInsertion_vertices.2 T.root_mem_vertices
  nonRoot_nonempty := T.nonRoot_nonempty.image _
  nonRoot_subset w hw := by
    obtain ⟨s, hs, rfl⟩ := exists_eq_map_inl_of_mem_image hw
    exact map_inl_mem_lollipopInsertion_internalVertices.2 (T.nonRoot_subset hs)
  root_notMem_nonRoot h := T.root_notMem_nonRoot (map_inl_mem_image_map_inl.1 h)
  vertexOf_inv_mem d hd := by
    rcases d with x | k
    · rw [lollipopInsertion_vertexOf_inl, map_inl_mem_image_map_inl] at hd
      rw [lollipopInsertion_inv_inl_of_notMem_bdry hA (T.notMem_bdry_of_vertexOf_mem hd),
        lollipopInsertion_vertexOf_inl, mem_insert, map_inl_mem_image_map_inl]
      rcases mem_insert.1 (T.vertexOf_inv_mem x hd) with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
    · exact absurd hd (lollipopInsertion_vertexOf_inr_notMem k)
  exists_interval := by
    obtain ⟨a, ha, k, hk1, hk2, hiff, hnot⟩ := T.exists_interval
    refine ⟨Sum.inl a, inl_mem_map_inl_iff.2 ha, k, hk1, by rwa [card_map], fun d hd => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := mem_map.1 hd
      rw [Function.Embedding.inl_apply, treeDarts_lollipopInsertion hA, inl_mem_map_inl_iff,
        hiff x hx]
      simp only [lollipopInsertion_rot_pow_inl, Sum.inl.injEq]
    · rw [lollipopInsertion_rot_symm_inl, treeDarts_lollipopInsertion hA, inl_mem_map_inl_iff]
      exact hnot
  card_image_edgeOf := by
    rw [card_image_edgeOf_lollipopInsertion hA, T.card_image_edgeOf,
      card_image_of_injective _ (Finset.map_injective _)]
  reflTransGen_treeAdj u hu := by
    have key : ∀ s ∈ insert T.root T.nonRoot, Relation.ReflTransGen
        ((A.lollipopInsertion i c).TreeAdj
          (T.nonRoot.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4))))
        (T.root.map Function.Embedding.inl) (s.map Function.Embedding.inl) := fun s hs =>
      (T.reflTransGen_treeAdj s hs).lift _ fun _ _ h => treeAdj_lollipopInsertion_map hA h
    rcases mem_insert.1 hu with rfl | hu
    · exact key _ (mem_insert_self _ _)
    · obtain ⟨s, hs, rfl⟩ := exists_eq_map_inl_of_mem_image hu
      exact key s (mem_insert_of_mem hs)

namespace RootedTree

variable (hA : A.IsPlabicGraph) (T : A.RootedTree)

include hA

/-- The root of `T` as a rooted tree of `I_i(A, c)` is the root of `T`. -/
@[simp]
theorem root_lollipopInsertion :
    (T.lollipopInsertion hA i c).root = T.root.map Function.Embedding.inl := rfl

/-- The non-root vertices of `T` as a rooted tree of `I_i(A, c)` are those of `T`. -/
@[simp]
theorem nonRoot_lollipopInsertion :
    (T.lollipopInsertion hA i c).nonRoot =
      T.nonRoot.image (Finset.map Function.Embedding.inl) := rfl

/-- The darts `D_T` of `T` as a rooted tree of `I_i(A, c)` are those of `T`. -/
theorem darts_lollipopInsertion :
    (T.lollipopInsertion hA i c).darts = T.darts.map Function.Embedding.inl :=
  treeDarts_lollipopInsertion hA _

/-- The root of `T` is a boundary vertex of `I_i(A, c)` if and only if it is one of `A`. -/
theorem isBoundaryVertex_root_lollipopInsertion :
    (A.lollipopInsertion i c).IsBoundaryVertex (T.lollipopInsertion hA i c).root ↔
      A.IsBoundaryVertex T.root :=
  isBoundaryVertex_lollipopInsertion_map_inl

/-- The first dart of the interval of `T` as a rooted tree of `I_i(A, c)` is that of `T`. -/
theorem intervalStart_lollipopInsertion :
    (T.lollipopInsertion hA i c).intervalStart = Sum.inl T.intervalStart := by
  refine (RootedTree.eq_intervalStart _ (inl_mem_map_inl_iff.2 T.intervalStart_mem_root) ?_ ?_).symm
  · rw [darts_lollipopInsertion]
    exact inl_mem_map_inl_iff.2 T.intervalStart_mem_darts
  · rw [darts_lollipopInsertion, lollipopInsertion_rot_symm_inl, inl_mem_map_inl_iff]
    exact T.rot_symm_intervalStart_notMem

/-- A dart of `P_T` is a dart of the plabic graph of `T` as a rooted tree of `I_i(A, c)` if and
only if it is a dart of `P_T`. -/
theorem isDart_lollipopInsertion_map {x : H ⊕ LollipopDart} :
    (T.lollipopInsertion hA i c).IsDart (Sum.map Sum.inl id x) ↔ T.IsDart x := by
  rcases x with d | (_ | _ | _ | _)
  · change Sum.inl d ∈ (T.lollipopInsertion hA i c).darts ↔ d ∈ T.darts
    rw [darts_lollipopInsertion, inl_mem_map_inl_iff]
  · exact Iff.rfl
  · exact Iff.rfl
  · exact not_congr (isBoundaryVertex_root_lollipopInsertion hA T)
  · exact not_congr (isBoundaryVertex_root_lollipopInsertion hA T)

/-- The darts of `P_T` are those of the plabic graph of `T` as a rooted tree of `I_i(A, c)`. -/
noncomputable def lollipopInsertionDartEquiv : T.Dart ≃ (T.lollipopInsertion hA i c).Dart :=
  Equiv.ofBijective
    (fun x => ⟨Sum.map Sum.inl id x.1, (isDart_lollipopInsertion_map hA T).2 x.2⟩)
    ⟨fun x y h => Subtype.ext (Sum.map_injective.2 ⟨Sum.inl_injective, Function.injective_id⟩
      (congrArg Subtype.val h)), by
      rintro ⟨(x | k) | l, hy⟩
      · exact ⟨⟨Sum.inl x, (isDart_lollipopInsertion_map hA T (x := Sum.inl x)).1 hy⟩, rfl⟩
      · exfalso
        change Sum.inr k ∈ (T.lollipopInsertion hA i c).darts at hy
        rw [darts_lollipopInsertion] at hy
        simp at hy
      · exact ⟨⟨Sum.inr l, (isDart_lollipopInsertion_map hA T (x := Sum.inr l)).1 hy⟩, rfl⟩⟩

/-- The equivalence `lollipopInsertionDartEquiv` sends a dart `x` of `P_T` to the image of `x`
under `Sum.map Sum.inl id`. -/
@[simp]
theorem coe_lollipopInsertionDartEquiv (x : T.Dart) :
    ((T.lollipopInsertionDartEquiv hA (i := i) (c := c) x : (H ⊕ Fin 4) ⊕ LollipopDart)) =
      Sum.map Sum.inl id x.1 := rfl

/-- The plabic graph `P_T` of a rooted tree `T` of `A` is isomorphic to that of `T` as a rooted
tree of `I_i(A, c)`. -/
noncomputable def lollipopInsertionIso :
    T.plabicData.Iso (T.lollipopInsertion hA i c).plabicData where
  toEquiv := T.lollipopInsertionDartEquiv hA
  map_inv x := by
    have hI := hA.lollipopInsertion i c
    apply Subtype.ext
    rw [coe_lollipopInsertionDartEquiv, coe_inv_plabicData _ hI, coe_inv_plabicData _ hA,
      coe_lollipopInsertionDartEquiv]
    obtain ⟨d | l, hx⟩ := x
    · simp only [Sum.map_inl]
      rw [lollipopInsertion_inv_inl_of_notMem_bdry hA (mem_treeDarts.1 hx).1]
    · rfl
  map_rot x := by
    have hI := hA.lollipopInsertion i c
    apply Subtype.ext
    rw [coe_lollipopInsertionDartEquiv, coe_rot_plabicData _ hI, coe_rot_plabicData _ hA,
      coe_lollipopInsertionDartEquiv]
    have hb := isBoundaryVertex_root_lollipopInsertion hA T (i := i) (c := c)
    obtain ⟨d | (_ | _ | _ | _), hx⟩ := x
    · simp only [Sum.map_inl, rotAux, lollipopInsertion_rot_inl, darts_lollipopInsertion hA T,
        inl_mem_map_inl_iff, hb]
      split_ifs <;> rfl
    · simp only [Sum.map_inr, id, rotAux, hb, intervalStart_lollipopInsertion hA T]
      split_ifs <;> rfl
    · rfl
    · rfl
    · simp only [Sum.map_inr, id, rotAux, intervalStart_lollipopInsertion hA T]
      rfl
  mem_bdry_iff x := by
    rw [mem_bdry_plabicData, mem_bdry_plabicData]
    obtain ⟨d | (_ | _ | _ | _), hx⟩ := x <;>
      simp [Subtype.ext_iff, dartE, dartEBar]
  map_colour x _ := by
    obtain ⟨d | l, hx⟩ := x
    · rfl
    · change (A.lollipopInsertion i c).colour (T.lollipopInsertion hA i c).intervalStart =
        A.colour T.intervalStart
      rw [intervalStart_lollipopInsertion hA T]
      rfl
  map_bvertex j := by
    have hI := hA.lollipopInsertion i c
    rw [(isPlabicGraph_plabicData _ hA).filter_bvertex_notMem_bdry,
      (isPlabicGraph_plabicData _ hI).filter_bvertex_notMem_bdry, map_singleton]
    congr 1
    apply Subtype.ext
    change ((T.lollipopInsertionDartEquiv hA T.legDart : (H ⊕ Fin 4) ⊕ LollipopDart)) =
      ((T.lollipopInsertion hA i c).legDart : (H ⊕ Fin 4) ⊕ LollipopDart)
    rw [coe_lollipopInsertionDartEquiv]
    by_cases hb : A.IsBoundaryVertex T.root
    · have hb' := (isBoundaryVertex_root_lollipopInsertion hA T (i := i) (c := c)).2 hb
      simp only [legDart, dif_pos hb, dif_pos hb', intervalStart_lollipopInsertion hA T]
      rfl
    · have hb' := (isBoundaryVertex_root_lollipopInsertion hA T (i := i) (c := c)).not.2 hb
      simp only [legDart, dif_neg hb, dif_neg hb']
      rfl

/-- `T` is collapsible of colour `c'` in `A` iff it is so in `I_i(A, c)`. -/
theorem isCollapsibleOfColour_lollipopInsertion_iff {c' : Shade} :
    (T.lollipopInsertion hA i c).IsCollapsibleOfColour c' ↔ T.IsCollapsibleOfColour c' := by
  have hI := hA.lollipopInsertion i c
  have hP := isPlabicGraph_plabicData T hA
  have hP' := isPlabicGraph_plabicData (T.lollipopInsertion hA i c) hI
  have θ := T.lollipopInsertionIso hA (i := i) (c := c)
  have hroot : ((¬(A.lollipopInsertion i c).IsBoundaryVertex (T.lollipopInsertion hA i c).root ∧
        ∀ d ∈ (T.lollipopInsertion hA i c).root, (A.lollipopInsertion i c).colour d = c') ∨
      ((A.lollipopInsertion i c).IsBoundaryVertex (T.lollipopInsertion hA i c).root ∧
        2 ≤ (T.lollipopInsertion hA i c).nonRoot.card)) ↔
      ((¬A.IsBoundaryVertex T.root ∧ ∀ d ∈ T.root, A.colour d = c') ∨
        (A.IsBoundaryVertex T.root ∧ 2 ≤ T.nonRoot.card)) := by
    rw [isBoundaryVertex_root_lollipopInsertion hA T, nonRoot_lollipopInsertion,
      card_image_of_injective _ (Finset.map_injective _), root_lollipopInsertion,
      Finset.forall_mem_map]
    rfl
  constructor
  · intro h
    refine ⟨hP, ?_, hroot.1 h.root_cases⟩
    exact (PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
      (G := ⟨T.Dart, T.plabicData, hP⟩) (G' := ⟨_, _, h.isPlabicGraph⟩) ⟨θ.symm⟩).trans
      h.moveEquivalent
  · intro h
    refine ⟨hP', ?_, hroot.2 h.root_cases⟩
    exact (PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
      (G := ⟨_, _, hP'⟩) (G' := ⟨T.Dart, T.plabicData, h.isPlabicGraph⟩) ⟨θ⟩).trans
      h.moveEquivalent

end RootedTree

/-- A rooted tree of `I_i(A, c)` whose root and non-root vertices are vertices of `A` comes from
a rooted tree of `A`. -/
theorem exists_rootedTree_of_lollipopInsertion (hA : A.IsPlabicGraph)
    (T : (A.lollipopInsertion i c).RootedTree) {v : Finset H} {W : Finset (Finset H)}
    (hv : T.root = v.map Function.Embedding.inl)
    (hW : T.nonRoot = W.image (Finset.map Function.Embedding.inl)) :
    ∃ T₀ : A.RootedTree, T₀.lollipopInsertion hA i c = T := by
  have hWsub : W ⊆ A.internalVertices := fun w hw =>
    map_inl_mem_lollipopInsertion_internalVertices.1
      (T.nonRoot_subset (hW ▸ mem_image_of_mem _ hw))
  have hdarts : T.darts = (A.treeDarts W).map Function.Embedding.inl := by
    rw [RootedTree.darts, hW, treeDarts_lollipopInsertion hA]
  let T₀ : A.RootedTree :=
    { root := v
      nonRoot := W
      root_mem_vertices := map_inl_mem_lollipopInsertion_vertices.1 (hv ▸ T.root_mem_vertices)
      nonRoot_nonempty := by
        have := T.nonRoot_nonempty
        rw [hW] at this
        exact this.of_image
      nonRoot_subset := hWsub
      root_notMem_nonRoot := fun h => T.root_notMem_nonRoot (by
        rw [hv, hW]; exact map_inl_mem_image_map_inl.2 h)
      vertexOf_inv_mem := fun x hx => by
        have hxB : x ∉ A.bdry := fun h =>
          (A.mem_internalVertices.1 (hWsub hx)).2 (A.isBoundaryVertex_vertexOf_of_mem h)
        have hx' : (A.lollipopInsertion i c).vertexOf (Sum.inl x) ∈ T.nonRoot := by
          rw [hW, lollipopInsertion_vertexOf_inl]; exact map_inl_mem_image_map_inl.2 hx
        have := T.vertexOf_inv_mem _ hx'
        rw [hv, hW, lollipopInsertion_inv_inl_of_notMem_bdry hA hxB,
          lollipopInsertion_vertexOf_inl, mem_insert, map_inl_mem_image_map_inl] at this
        rcases this with h | h
        · exact mem_insert.2 (Or.inl (Finset.map_injective _ h))
        · exact mem_insert_of_mem h
      exists_interval := by
        obtain ⟨a', ha', k, hk1, hk2, hiff, hnot⟩ := T.exists_interval
        rw [hv] at ha' hk2
        obtain ⟨a, ha, rfl⟩ := mem_map.1 ha'
        refine ⟨a, ha, k, hk1, by rwa [card_map] at hk2, fun d hd => ?_, ?_⟩
        · have := hiff (Sum.inl d) (by rw [hv]; exact inl_mem_map_inl_iff.2 hd)
          rw [← RootedTree.darts, hdarts, inl_mem_map_inl_iff] at this
          rw [this]
          simp only [Function.Embedding.inl_apply, lollipopInsertion_rot_pow_inl, Sum.inl.injEq]
        · rwa [← RootedTree.darts, hdarts, Function.Embedding.inl_apply,
            lollipopInsertion_rot_symm_inl, inl_mem_map_inl_iff] at hnot
      card_image_edgeOf := by
        have := T.card_image_edgeOf
        rwa [hW, card_image_edgeOf_lollipopInsertion hA,
          card_image_of_injective _ (Finset.map_injective _)] at this
      reflTransGen_treeAdj := fun s hs => by
        have h := T.reflTransGen_treeAdj (s.map Function.Embedding.inl) (by
          rw [hv, hW, mem_insert]
          rcases mem_insert.1 hs with rfl | hs
          · exact Or.inl rfl
          · exact Or.inr (map_inl_mem_image_map_inl.2 hs))
        rw [hv, hW] at h
        obtain ⟨u', hu', h'⟩ := exists_of_reflTransGen_treeAdj_lollipopInsertion hA h
        rwa [Finset.map_injective _ hu'] }
  exact ⟨T₀, RootedTree.ext' hv.symm hW.symm⟩

/-- **Collapsible trees of an insertion**: for a plabic graph `A`, a vertex `v` and a set `W` of
vertices of `A`, `(v, W)` is a collapsible tree of colour `c'` of `A` iff it is a collapsible tree
of colour `c'` of `I_i(A, c)`, the darts of `A` being darts of `I_i(A, c)` through `Sum.inl`. -/
@[cluster_algebras "lem_lollipop_insertion_trees"]
theorem exists_isCollapsibleOfColour_lollipopInsertion_iff (hA : A.IsPlabicGraph)
    (v : Finset H) (W : Finset (Finset H)) (c' : Shade) :
    (∃ T : A.RootedTree, T.root = v ∧ T.nonRoot = W ∧ T.IsCollapsibleOfColour c') ↔
      ∃ T : (A.lollipopInsertion i c).RootedTree, T.root = v.map Function.Embedding.inl ∧
        T.nonRoot = W.image (Finset.map Function.Embedding.inl) ∧
          T.IsCollapsibleOfColour c' := by
  constructor
  · rintro ⟨T, rfl, rfl, h⟩
    exact ⟨T.lollipopInsertion hA i c, rfl, rfl,
      (T.isCollapsibleOfColour_lollipopInsertion_iff hA).2 h⟩
  · rintro ⟨T, hv, hW, h⟩
    obtain ⟨T₀, rfl⟩ := exists_rootedTree_of_lollipopInsertion hA T hv hW
    refine ⟨T₀, ?_, ?_, (T₀.isCollapsibleOfColour_lollipopInsertion_iff hA).1 h⟩
    · exact Finset.map_injective _ hv
    · rw [RootedTree.nonRoot_lollipopInsertion] at hW
      exact image_injective (Finset.map_injective _) hW

end Trees

end PlabicData

/-! ### Constructions commuting with local moves -/

namespace PlabicGraph

open PlabicData

variable {b b' : ℕ}

/-- The square move of a plabic graph at the face through `c`, as a bundled plabic graph. -/
def squareMoveGraph (Q : PlabicGraph b) (c : Q.Dart) : PlabicGraph b :=
  ⟨Q.Dart, Q.data.squareMove c, Q.isPlabicGraph.squareMove c⟩

/-- The removal of a bivalent vertex, as a bundled plabic graph. -/
def bivalentRemovalGraph (Q : PlabicGraph b) {d : Q.Dart}
    (hd : Q.data.IsBivalentRemovable d) : PlabicGraph b :=
  ⟨_, Q.data.bivalentRemoval Q.isPlabicGraph hd, isPlabicGraph_bivalentRemoval _ _⟩

/-- The contraction along an edge, as a bundled plabic graph. -/
noncomputable def contractEdgeGraph (Q : PlabicGraph b) {d : Q.Dart}
    (he : Q.data.IsContractibleEdge d) : PlabicGraph b :=
  ⟨_, Q.data.contractEdge d (he.leg_mem Q.isPlabicGraph), Q.isPlabicGraph.contractEdge he⟩

/-- A construction `F` on plabic graphs that is compatible with isomorphisms, square moves,
removals of bivalent vertices and contractions of edges carries `S`-equivalent plabic graphs to
`S`-equivalent plabic graphs. -/
theorem MoveEquivalent.map_of_commute (F : PlabicGraph b → PlabicGraph b')
    (hiso : ∀ Q Q' : PlabicGraph b, Q.Isomorphic Q' → (F Q).Isomorphic (F Q'))
    (hsq : ∀ (Q : PlabicGraph b) (c : Q.Dart), Q.data.IsSquareMoveFace c →
      (F Q).IsSquareMove (F (Q.squareMoveGraph c)))
    (hrem : ∀ (Q : PlabicGraph b) (d : Q.Dart) (hd : Q.data.IsBivalentRemovable d),
      (F Q).IsBivalentRemoval (F (Q.bivalentRemovalGraph hd)))
    (hcon : ∀ (Q : PlabicGraph b) (d : Q.Dart) (he : Q.data.IsContractibleEdge d),
      ∃ d', (F Q).IsEdgeContraction (F (Q.contractEdgeGraph he)) d')
    {S : Set LocalMoveType} {Q Q' : PlabicGraph b} (h : MoveEquivalent S Q Q') :
    MoveEquivalent S (F Q) (F Q') := by
  -- isomorphic targets of local moves of `F Q`
  have hsq' : ∀ {P P' : PlabicGraph b'} {P'' : PlabicGraph b'}, P.IsSquareMove P'' →
      P'.Isomorphic P'' → P.IsSquareMove P' := fun ⟨c, hc, h⟩ h' => ⟨c, hc, h'.trans _ h⟩
  have hrem' : ∀ {P P' : PlabicGraph b'} {P'' : PlabicGraph b'}, P.IsBivalentRemoval P'' →
      P'.Isomorphic P'' → P.IsBivalentRemoval P' := fun ⟨d, hd, h⟩ h' => ⟨d, hd, h'.trans _ h⟩
  have hcon' : ∀ {P P' : PlabicGraph b'} {P'' : PlabicGraph b'} {d}, P.IsEdgeContraction P'' d →
      P'.Isomorphic P'' → P.IsEdgeContraction P' d := fun ⟨he, h⟩ h' => ⟨he, h'.trans _ h⟩
  induction h with
  | refl => exact MoveEquivalent.refl _ _
  | tail _ hst ih =>
    refine ih.trans (MoveEquivalent.of_moveStep ?_)
    rename_i Q₁ Q₂ _
    rcases hst with hiso₁ | ⟨t, ht, hmove⟩
    · exact Or.inl (hiso _ _ hiso₁)
    refine Or.inr ⟨t, ht, ?_⟩
    cases t with
    | m1 =>
      obtain ⟨c, hc, h₂⟩ := hmove
      exact hsq' (hsq Q₁ c hc) (hiso Q₂ (Q₁.squareMoveGraph c) h₂)
    | m2 =>
      rcases hmove with ⟨d, hd, h₂⟩ | ⟨d, hd, h₁⟩
      · exact Or.inl (hrem' (hrem Q₁ d hd) (hiso Q₂ (Q₁.bivalentRemovalGraph hd) h₂))
      · exact Or.inr (hrem' (hrem Q₂ d hd) (hiso Q₁ (Q₂.bivalentRemovalGraph hd) h₁))
    | m3 =>
      rcases hmove with ⟨d, he, h₂⟩ | ⟨d, he, h₁⟩
      · obtain ⟨d', hd'⟩ := hcon Q₁ d he
        exact Or.inl ⟨d', hcon' hd' (hiso Q₂ (Q₁.contractEdgeGraph he) h₂)⟩
      · obtain ⟨d', hd'⟩ := hcon Q₂ d he
        exact Or.inr ⟨d', hcon' hd' (hiso Q₁ (Q₂.contractEdgeGraph he) h₁)⟩

end PlabicGraph

/-! ### Moves commute with inserting a lollipop -/

namespace PlabicData

section Helpers

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

/-- An isomorphism of plabic graphs, built from a bijection of darts commuting with the
involutions and the rotations, preserving `B` and the colours of internal vertices, and mapping
legs to legs. -/
private def isoOfLeg {G : PlabicData H b} {G' : PlabicData H' b} (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) (e : H ≃ H') (map_inv : ∀ d, e (G.inv d) = G'.inv (e d))
    (map_rot : ∀ d, e (G.rot d) = G'.rot (e d)) (mem_bdry_iff : ∀ d, e d ∈ G'.bdry ↔ d ∈ G.bdry)
    (map_colour : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G'.colour (e d) = G.colour d)
    (map_leg : ∀ i, e (G.leg i) = G'.leg i) : G.Iso G' where
  toEquiv := e
  map_inv := map_inv
  map_rot := map_rot
  mem_bdry_iff := mem_bdry_iff
  map_colour := map_colour
  map_bvertex i := by
    rw [hG.filter_bvertex_notMem_bdry, hG'.filter_bvertex_notMem_bdry, map_singleton,
      Equiv.coe_toEmbedding, map_leg]

private theorem sumCongr_zpow' {α β : Type*} (a : Perm α) (b : Perm β) (n : ℤ) :
    Perm.sumCongr a b ^ n = Perm.sumCongr (a ^ n) (b ^ n) := by
  simpa using (map_zpow (Perm.sumCongrHom α β) (a, b) n).symm

private theorem sameCycle_sumCongr_inr_inr' {α β : Type*} {a : Perm α} {b : Perm β} {x y : β} :
    (Perm.sumCongr a b).SameCycle (Sum.inr x) (Sum.inr y) ↔ b.SameCycle x y := by
  simp [Perm.SameCycle, sumCongr_zpow']

private theorem not_sameCycle_sumCongr_inr_inl' {α β : Type*} {a : Perm α} {b : Perm β} {x : β}
    {y : α} : ¬(Perm.sumCongr a b).SameCycle (Sum.inr x) (Sum.inl y) := by
  simp [Perm.SameCycle, sumCongr_zpow']

/-- The first return of a permutation is carried along a map intertwining it with another one on
an invariant set of points. -/
private theorem coe_firstReturn_map_of_invariant {X X' : Type*} [Finite X] [Finite X']
    (ε : X → X') {π : Perm X} {π' : Perm X'} {P : X → Prop} (hP : ∀ x, P x → P (π x))
    (hπ : ∀ x, P x → π' (ε x) = ε (π x)) {S : Set X} {S' : Set X'}
    (hS : ∀ x, P x → (ε x ∈ S' ↔ x ∈ S)) (y : S) (hy : P y) (y' : S')
    (hy' : (y' : X') = ε y) : (firstReturn π' S' y' : X') = ε (firstReturn π S y) := by
  have hpow : ∀ (n : ℕ) (x : X), P x → (π' ^ n) (ε x) = ε ((π ^ n) x) ∧ P ((π ^ n) x) := by
    intro n
    induction n with
    | zero => intro x hx; exact ⟨rfl, hx⟩
    | succ n ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      refine ⟨?_, ?_⟩
      · rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, h1, hπ _ h2]
      · rw [pow_succ', Perm.mul_apply]
        exact hP _ h2
  rw [coe_firstReturn π S y, ← (hpow _ _ hy).1, ← hy']
  refine coe_firstReturn_of_pow (y := y') (firstReturnTime_pos y) ?_ ?_
  · rw [hy', (hpow _ _ hy).1, hS _ (hpow _ _ hy).2]
    exact pow_firstReturnTime_apply_mem y
  · intro j hj hjm
    rw [hy', (hpow _ _ hy).1, hS _ (hpow _ _ hy).2]
    exact pow_apply_notMem_of_lt_firstReturnTime hj hjm

end Helpers

section LollipopMoves

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  [NeZero b] {A : PlabicData H b} {i : Fin (b + 1)} {c : Shade}

/-- An isomorphism of plabic graphs `A ≅ A'` sends `A.lollipopArc i` to `A'.lollipopArc i`. -/
theorem IsPlabicGraph.map_lollipopArc {A' : PlabicData H' b} (hA : A.IsPlabicGraph)
    (hA' : A'.IsPlabicGraph) (θ : A.Iso A') : θ.toEquiv (A.lollipopArc i) = A'.lollipopArc i := by
  rw [lollipopArc, lollipopArc, ← Iso.map_leg hA hA' θ, Equiv.eq_symm_apply, ← θ.map_rot,
    Equiv.apply_symm_apply]

/-- **An isomorphism of plabic graphs extends to their insertions**: if `A ≅ A'`, then
`I_i(A, c) ≅ I_i(A', c)`. -/
theorem Isomorphic.lollipopInsertion {A' : PlabicData H' b} (hA : A.IsPlabicGraph)
    (hA' : A'.IsPlabicGraph) (h : A.Isomorphic A') (i : Fin (b + 1)) (c : Shade) :
    (A.lollipopInsertion i c).Isomorphic (A'.lollipopInsertion i c) := by
  obtain ⟨θ⟩ := h
  have harc := hA.map_lollipopArc hA' θ (i := i)
  let e : H ⊕ Fin 4 ≃ H' ⊕ Fin 4 := Equiv.sumCongr θ.toEquiv (Equiv.refl _)
  have he : ∀ x, e (Sum.inl x) = Sum.inl (θ.toEquiv x) := fun _ => rfl
  have he' : ∀ k, e (Sum.inr k) = Sum.inr k := fun _ => rfl
  refine ⟨isoOfLeg (hA.lollipopInsertion i c) (hA'.lollipopInsertion i c) e (fun x => ?_)
    (fun x => ?_) (fun x => ?_) (fun x hx => ?_) (fun k => ?_)⟩
  · change e ((Perm.sumCongr A.inv (swap 2 3)) (swap (Sum.inl (A.lollipopArc i))
      (Sum.inl (A.inv (A.lollipopArc i))) (swap (Sum.inl (A.lollipopArc i)) (Sum.inr 0)
        (swap (Sum.inl (A.inv (A.lollipopArc i))) (Sum.inr 1) x)))) =
      (Perm.sumCongr A'.inv (swap 2 3)) (swap (Sum.inl (A'.lollipopArc i))
      (Sum.inl (A'.inv (A'.lollipopArc i))) (swap (Sum.inl (A'.lollipopArc i)) (Sum.inr 0)
        (swap (Sum.inl (A'.inv (A'.lollipopArc i))) (Sum.inr 1) (e x))))
    have hsum : ∀ y, e (Perm.sumCongr A.inv (swap 2 3) y) =
        Perm.sumCongr A'.inv (swap 2 3) (e y) := by
      rintro (y | k)
      · simp [e, θ.map_inv]
      · rfl
    rw [hsum, e.injective.map_swap, e.injective.map_swap, e.injective.map_swap, he, he, he', he',
      θ.map_inv, harc]
  · rcases x with y | k
    · simp [e, θ.map_rot]
    · rfl
  · rcases x with y | k
    · rw [he, mem_lollipopInsertion_bdry_inl, mem_lollipopInsertion_bdry_inl, θ.mem_bdry_iff]
    · rw [he']
      simp
  · rcases x with y | k
    · rw [he, lollipopInsertion_colour_inl, lollipopInsertion_colour_inl]
      rw [isBoundaryVertex_lollipopInsertion_vertexOf_inl] at hx
      exact θ.map_colour y hx
    · rfl
  · rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · simp [he']
    · rw [lollipopInsertion_leg_succAbove, lollipopInsertion_leg_succAbove, he,
        Iso.map_leg hA hA' θ]

/-- Away from `B`, the face permutation of `I_i(A, c)` is that of `A`. -/
theorem lollipopInsertion_facePerm_inl (hA : A.IsPlabicGraph) {x : H} (hx : x ∉ A.bdry) :
    (A.lollipopInsertion i c).facePerm (Sum.inl x) = Sum.inl (A.facePerm x) := by
  rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inl_of_notMem_bdry hA hx]
  rfl

/-- On a face of `A` disjoint from `B`, the powers of the face permutation of `I_i(A, c)` are
those of `A`. -/
theorem lollipopInsertion_facePerm_pow_inl (hA : A.IsPlabicGraph) {x : H}
    (hx : Disjoint (A.faceOf x) A.bdry) (n : ℕ) :
    ((A.lollipopInsertion i c).facePerm ^ n) (Sum.inl x) = Sum.inl ((A.facePerm ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, lollipopInsertion_facePerm_inl hA, ← Perm.mul_apply,
      ← pow_succ']
    exact disjoint_left.1 hx ((RotationSystem.mem_faceOf _).2 ⟨n, by rw [zpow_natCast]⟩)

namespace IsSquareMoveFace

variable (hA : A.IsPlabicGraph) {c₀ : H} (hq : A.IsSquareMoveFace c₀)

include hA hq

omit [NeZero b] hA in
/-- The face of a square move is disjoint from `B`. -/
theorem disjoint_faceOf_bdry : Disjoint (A.faceOf c₀) A.bdry :=
  (A.mem_internalFaces.1 hq.faceOf_mem_internalFaces).2

/-- The corners of the square face through `c₀` in `I_i(A, c)` are those in `A`. -/
theorem lollipopInsertion_squareCorner (k : Fin 4) :
    (A.lollipopInsertion i c).squareCorner (Sum.inl c₀) k = Sum.inl (A.squareCorner c₀ k) :=
  lollipopInsertion_facePerm_pow_inl hA hq.disjoint_faceOf_bdry _

/-- A vertex of `A` is a vertex of the square face through `c₀` in `I_i(A, c)` if and only if it
is one in `A`. -/
theorem vertexOf_inl_mem_lollipopInsertion_squareVertices_iff (y : H) :
    (A.lollipopInsertion i c).vertexOf (Sum.inl y) ∈
        (A.lollipopInsertion i c).squareVertices (Sum.inl c₀) ↔
      A.vertexOf y ∈ A.squareVertices c₀ := by
  simp only [mem_squareVertices, hq.lollipopInsertion_squareCorner hA,
    lollipopInsertion_vertexOf_inl, Finset.map_inj]

/-- A vertex at a new dart of `I_i(A, c)` is not a vertex of the square face through `c₀`. -/
theorem vertexOf_inr_notMem_lollipopInsertion_squareVertices (k : Fin 4) :
    (A.lollipopInsertion i c).vertexOf (Sum.inr k) ∉
      (A.lollipopInsertion i c).squareVertices (Sum.inl c₀) := by
  rw [mem_squareVertices]
  rintro ⟨l, hl⟩
  rw [hq.lollipopInsertion_squareCorner hA, lollipopInsertion_vertexOf_inl] at hl
  have := hl ▸ (A.lollipopInsertion i c).self_mem_vertexOf (Sum.inr k)
  exact inr_notMem_map_inl k this

/-- A square move of `A` is a square move of `I_i(A, c)`. -/
theorem lollipopInsertion : (A.lollipopInsertion i c).IsSquareMoveFace (Sum.inl c₀) where
  faceOf_mem_internalFaces := by
    have hd := hq.disjoint_faceOf_bdry
    refine (A.lollipopInsertion i c).mem_internalFaces.2 ⟨DiskMap.faceOf_mem_faces _ ?_, ?_⟩
    · rw [mem_lollipopInsertion_bdry_inl]
      exact disjoint_left.1 hd (A.self_mem_faceOf c₀)
    · rw [disjoint_left]
      intro z hz
      obtain ⟨n, rfl⟩ := ((RotationSystem.mem_faceOf _).1 hz).exists_nat_pow_eq
      rw [lollipopInsertion_facePerm_pow_inl hA hd, mem_lollipopInsertion_bdry_inl]
      exact disjoint_left.1 hd ((RotationSystem.mem_faceOf _).2 ⟨n, by rw [zpow_natCast]⟩)
  facePerm_pow_four := by
    rw [lollipopInsertion_facePerm_pow_inl hA hq.disjoint_faceOf_bdry, hq.facePerm_pow_four]
  vertexOf_mem_internalVertices k := by
    rw [hq.lollipopInsertion_squareCorner hA, lollipopInsertion_vertexOf_inl]
    exact map_inl_mem_lollipopInsertion_internalVertices.2 (hq.vertexOf_mem_internalVertices k)
  injective k l h := hq.injective (by
    simpa only [hq.lollipopInsertion_squareCorner hA, lollipopInsertion_vertexOf_inl,
      Finset.map_inj] using h)
  card_vertexOf k := by
    rw [hq.lollipopInsertion_squareCorner hA, lollipopInsertion_vertexOf_inl, card_map]
    exact hq.card_vertexOf k
  colour_ne k := by
    rw [hq.lollipopInsertion_squareCorner hA, hq.lollipopInsertion_squareCorner hA]
    exact hq.colour_ne k

/-- The insertion into a square move is the square move of the insertion. -/
theorem squareMove_lollipopInsertion_isomorphic :
    ((A.squareMove c₀).lollipopInsertion i c).Isomorphic
      ((A.lollipopInsertion i c).squareMove (Sum.inl c₀)) := by
  refine ⟨isoOfLeg ((hA.squareMove c₀).lollipopInsertion i c)
    ((hA.lollipopInsertion i c).squareMove _) (Equiv.refl _) (fun _ => rfl) (fun _ => rfl)
    (fun _ => Iff.rfl) (fun x _ => ?_) (fun _ => rfl)⟩
  rcases x with y | k
  · change (if (A.lollipopInsertion i c).vertexOf (Sum.inl y) ∈
        (A.lollipopInsertion i c).squareVertices (Sum.inl c₀) then (A.colour y).swap
        else A.colour y) = (A.squareMove c₀).colour y
    rw [colour_squareMove]
    by_cases h : A.vertexOf y ∈ A.squareVertices c₀
    · rw [if_pos ((hq.vertexOf_inl_mem_lollipopInsertion_squareVertices_iff hA y).2 h), if_pos h]
    · rw [if_neg ((hq.vertexOf_inl_mem_lollipopInsertion_squareVertices_iff hA y).not.2 h),
        if_neg h]
  · change (if (A.lollipopInsertion i c).vertexOf (Sum.inr k) ∈
        (A.lollipopInsertion i c).squareVertices (Sum.inl c₀) then c.swap else c) = c
    rw [if_neg (hq.vertexOf_inr_notMem_lollipopInsertion_squareVertices hA k)]

end IsSquareMoveFace

/-- The involution of `I_i(A, c)` on the darts of `A`. -/
theorem lollipopInsertion_inv_inl_eq (hA : A.IsPlabicGraph) (x : H) :
    (A.lollipopInsertion i c).inv (Sum.inl x) =
      if x = A.lollipopArc i then Sum.inr 0
      else if x = A.inv (A.lollipopArc i) then Sum.inr 1 else Sum.inl (A.inv x) := by
  have hh := hA.inv_ne (A.lollipopArc i)
  split_ifs with h1 h2
  · subst h1; exact lollipopInsertion_inv_inl_self c hh
  · subst h2; exact lollipopInsertion_inv_inl_inv A i c
  · exact lollipopInsertion_inv_inl_of_ne A i c h1 h2

/-- The involution of `I_i(A, c)` sends the new dart `0` to `A.lollipopArc i`. -/
theorem lollipopInsertion_inv_inr_zero_eq (hA : A.IsPlabicGraph) :
    (A.lollipopInsertion i c).inv (Sum.inr 0) = Sum.inl (A.lollipopArc i) :=
  lollipopInsertion_inv_inr_zero' c hA.inv_involutive

/-- The involution of `I_i(A, c)` sends the new dart `1` to the involute of `A.lollipopArc i`. -/
theorem lollipopInsertion_inv_inr_one_eq (hA : A.IsPlabicGraph) :
    (A.lollipopInsertion i c).inv (Sum.inr 1) = Sum.inl (A.inv (A.lollipopArc i)) :=
  lollipopInsertion_inv_inr_one c (hA.inv_ne _)

/-- The dart `A.lollipopArc i` lies in `B`. -/
theorem IsPlabicGraph.lollipopArc_mem_bdry (hA : A.IsPlabicGraph) : A.lollipopArc i ∈ A.bdry :=
  A.exterior_subset_bdry hA.lollipopArc_mem_exterior

/-- The involute of the dart `A.lollipopArc i` lies in `B`. -/
theorem IsPlabicGraph.inv_lollipopArc_mem_bdry (hA : A.IsPlabicGraph) :
    A.inv (A.lollipopArc i) ∈ A.bdry :=
  hA.inv_mem_bdry _ hA.lollipopArc_mem_bdry

namespace IsBivalentRemovable

variable (hA : A.IsPlabicGraph) {d : H} (hd : A.IsBivalentRemovable d)

include hA hd

/-- A removable bivalent vertex of `A` is a removable bivalent vertex of `I_i(A, c)`. -/
theorem lollipopInsertion : (A.lollipopInsertion i c).IsBivalentRemovable (Sum.inl d) where
  not_isBoundaryVertex :=
    (isBoundaryVertex_lollipopInsertion_vertexOf_inl c d).not.2 hd.not_isBoundaryVertex
  card_vertexOf := by
    rw [lollipopInsertion_vertexOf_inl, card_map]
    exact hd.card_vertexOf
  inv_ne_rot := by
    rw [lollipopInsertion_inv_inl_of_notMem_bdry hA hd.notMem_bdry, lollipopInsertion_rot_inl]
    exact fun h => hd.inv_ne_rot (Sum.inl_injective h)

omit [NeZero b] in
private theorem coe_bivalentRemoval_rot_symm (y : ({d, A.rot d}ᶜ : Set H)) :
    ((A.bivalentRemoval hA hd).rot.symm y : H) = A.rot.symm y := by
  rw [Equiv.eq_symm_apply, ← coe_bivalentRemoval_rot hA hd, Equiv.apply_symm_apply]

/-- The dart `lollipopArc i` of the removal of a bivalent vertex is that of `A`. -/
theorem coe_bivalentRemoval_lollipopArc :
    ((A.bivalentRemoval hA hd).lollipopArc i : H) = A.lollipopArc i := by
  rw [lollipopArc, coe_bivalentRemoval_rot_symm hA hd, coe_bivalentRemoval_leg]
  rfl

/-- The involute of the dart `lollipopArc i` of the removal of a bivalent vertex is that of
`A`. -/
theorem coe_bivalentRemoval_inv_lollipopArc :
    ((A.bivalentRemoval hA hd).inv ((A.bivalentRemoval hA hd).lollipopArc i) : H) =
      A.inv (A.lollipopArc i) := by
  rw [coe_bivalentRemoval_inv_of_mem_bdry hA hd
    (by rw [coe_bivalentRemoval_lollipopArc hA hd]; exact hA.lollipopArc_mem_bdry),
    coe_bivalentRemoval_lollipopArc hA hd]

/-- **Removing a bivalent vertex commutes with inserting a lollipop.** -/
theorem bivalentRemoval_lollipopInsertion_isomorphic :
    ((A.bivalentRemoval hA hd).lollipopInsertion i c).Isomorphic
      ((A.lollipopInsertion i c).bivalentRemoval (hA.lollipopInsertion i c)
        (hd.lollipopInsertion hA (i := i) (c := c))) := by
  have hJ := hA.lollipopInsertion i c
  have hd' := hd.lollipopInsertion hA (i := i) (c := c)
  have hM := isPlabicGraph_bivalentRemoval hA hd
  set S : Set H := ({d, A.rot d}ᶜ : Set H)
  set S' : Set (H ⊕ Fin 4) :=
    ({Sum.inl d, (A.lollipopInsertion i c).rot (Sum.inl d)}ᶜ : Set (H ⊕ Fin 4))
  have hinl : ∀ y : H, (Sum.inl y : H ⊕ Fin 4) ∈ S' ↔ y ∈ S := fun y => by
    simp [S, S', lollipopInsertion_rot_inl]
  have hinr : ∀ k : Fin 4, (Sum.inr k : H ⊕ Fin 4) ∈ S' := fun k => by
    simp [S', lollipopInsertion_rot_inl]
  let ψ : S ⊕ Fin 4 ≃ S' := Equiv.ofBijective
    (Sum.elim (fun y => ⟨Sum.inl y.1, (hinl y).2 y.2⟩) (fun k => ⟨Sum.inr k, hinr k⟩))
    ⟨by
      rintro (y | k) (y' | k') h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq,
        Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact congrArg Sum.inr h, by
      rintro ⟨y | k, hy⟩
      · exact ⟨Sum.inl ⟨y, (hinl y).1 hy⟩, rfl⟩
      · exact ⟨Sum.inr k, rfl⟩⟩
  have hψ : ∀ w, (ψ w : H ⊕ Fin 4) = Sum.map Subtype.val id w := by
    rintro (y | k) <;> rfl
  have harc := coe_bivalentRemoval_lollipopArc hA hd (i := i)
  have harc' := coe_bivalentRemoval_inv_lollipopArc hA hd (i := i)
  have hb := hA.lollipopArc_mem_bdry (i := i)
  have hb' := hA.inv_lollipopArc_mem_bdry (i := i)
  have hJd : (A.lollipopInsertion i c).inv (Sum.inl d) = Sum.inl (A.inv d) :=
    lollipopInsertion_inv_inl_of_notMem_bdry hA hd.notMem_bdry
  have hJrd : (A.lollipopInsertion i c).inv ((A.lollipopInsertion i c).rot (Sum.inl d)) =
      Sum.inl (A.inv (A.rot d)) :=
    lollipopInsertion_inv_inl_of_notMem_bdry hA hd.rot_notMem_bdry
  have hne : ∀ x : H, x ∈ A.bdry → x ≠ A.inv d ∧ x ≠ A.inv (A.rot d) := fun x hx =>
    ⟨fun h => hd.inv_notMem_bdry hA (h ▸ hx), fun h => hd.inv_rot_notMem_bdry hA (h ▸ hx)⟩
  refine ⟨isoOfLeg (hM.lollipopInsertion i c) (isPlabicGraph_bivalentRemoval hJ hd') ψ
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z _ => ?_) (fun k => ?_)⟩
  · apply Subtype.ext
    rw [hψ]
    rcases z with y | k
    · rw [lollipopInsertion_inv_inl_eq hM]
      by_cases h1 : (y : H) = A.lollipopArc i
      · rw [if_pos (Subtype.ext (h1.trans harc.symm)), coe_bivalentRemoval_inv_of_ne _ _
          (by rw [hψ, hJd]; simpa [h1] using (hne _ hb).1)
          (by rw [hψ, hJrd]; simpa [h1] using (hne _ hb).2), hψ]
        simp [lollipopInsertion_inv_inl_eq hA, h1]
      rw [if_neg (fun h => h1 (by rw [h, harc]))]
      by_cases h2 : (y : H) = A.inv (A.lollipopArc i)
      · rw [if_pos (Subtype.ext (h2.trans harc'.symm)), coe_bivalentRemoval_inv_of_ne _ _
          (by rw [hψ, hJd]; simpa [h2] using (hne _ hb').1)
          (by rw [hψ, hJrd]; simpa [h2] using (hne _ hb').2), hψ]
        simp [lollipopInsertion_inv_inl_eq hA, h2, (hA.inv_ne (A.lollipopArc i))]
      rw [if_neg (fun h => h2 (by rw [h, harc']))]
      simp only [Sum.map_inl]
      by_cases h3 : (y : H) = A.inv d
      · rw [coe_bivalentRemoval_inv_of_eq_inv hA hd h3, coe_bivalentRemoval_inv_of_eq_inv _ _
          (by rw [hψ, hJd]; simp [h3]), hJrd]
      by_cases h4 : (y : H) = A.inv (A.rot d)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hA hd h4,
          coe_bivalentRemoval_inv_of_eq_inv_rot _ _ (by rw [hψ, hJrd]; simp [h4]), hJd]
      rw [coe_bivalentRemoval_inv_of_ne hA hd h3 h4, coe_bivalentRemoval_inv_of_ne _ _
        (by rw [hψ, hJd]; simpa using h3) (by rw [hψ, hJrd]; simpa using h4), hψ]
      simp [lollipopInsertion_inv_inl_eq hA, h1, h2]
    · have hk0 : ∀ x : H, (ψ (Sum.inr k) : H ⊕ Fin 4) ≠ Sum.inl x := fun x => by
        rw [hψ]; simp
      rw [coe_bivalentRemoval_inv_of_ne _ _ (by rw [hJd]; exact hk0 _)
        (by rw [hJrd]; exact hk0 _), hψ]
      simp only [Sum.map_inr, id]
      rcases fin_cases_four k with rfl | rfl | rfl | rfl
      · rw [lollipopInsertion_inv_inr_zero_eq hM, lollipopInsertion_inv_inr_zero_eq hA,
          Sum.map_inl, harc]
      · rw [lollipopInsertion_inv_inr_one_eq hM, lollipopInsertion_inv_inr_one_eq hA,
          Sum.map_inl, harc']
      · rw [lollipopInsertion_inv_inr_two, lollipopInsertion_inv_inr_two]; rfl
      · rw [lollipopInsertion_inv_inr_three, lollipopInsertion_inv_inr_three]; rfl
  · apply Subtype.ext
    rw [hψ, coe_bivalentRemoval_rot, hψ]
    rcases z with y | k
    · rfl
    · rfl
  · rcases z with y | k
    · rw [mem_bivalentRemoval_bdry, hψ, Sum.map_inl, mem_lollipopInsertion_bdry_inl,
        mem_lollipopInsertion_bdry_inl, mem_bivalentRemoval_bdry]
    · rw [mem_bivalentRemoval_bdry, hψ, Sum.map_inr, mem_lollipopInsertion_bdry_inr,
        mem_lollipopInsertion_bdry_inr]
      rfl
  · rcases z with y | k <;> rfl
  · apply Subtype.ext
    rw [hψ, coe_bivalentRemoval_leg]
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · rw [lollipopInsertion_leg_self, lollipopInsertion_leg_self]
      rfl
    · rw [lollipopInsertion_leg_succAbove, lollipopInsertion_leg_succAbove]
      rfl

end IsBivalentRemovable

/-- The darts `S ⊕ Fin 4` of an insertion into a restriction of `A` to `S`, matched with the
corresponding darts of `H ⊕ Fin 4`. -/
private noncomputable def sumSubtypeEquiv {S : Set H} {S' : Set (H ⊕ Fin 4)}
    (hinl : ∀ y : H, (Sum.inl y : H ⊕ Fin 4) ∈ S' ↔ y ∈ S)
    (hinr : ∀ k : Fin 4, (Sum.inr k : H ⊕ Fin 4) ∈ S') : S ⊕ Fin 4 ≃ S' :=
  Equiv.ofBijective
    (Sum.elim (fun y => ⟨Sum.inl y.1, (hinl y).2 y.2⟩) (fun k => ⟨Sum.inr k, hinr k⟩))
    ⟨by
      rintro (y | k) (y' | k') h <;> simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq,
        Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
      · exact congrArg Sum.inl (Subtype.ext h)
      · exact congrArg Sum.inr h, by
      rintro ⟨y | k, hy⟩
      · exact ⟨Sum.inl ⟨y, (hinl y).1 hy⟩, rfl⟩
      · exact ⟨Sum.inr k, rfl⟩⟩

omit [Fintype H] [DecidableEq H] in
private theorem coe_sumSubtypeEquiv {S : Set H} {S' : Set (H ⊕ Fin 4)}
    (hinl : ∀ y : H, (Sum.inl y : H ⊕ Fin 4) ∈ S' ↔ y ∈ S)
    (hinr : ∀ k : Fin 4, (Sum.inr k : H ⊕ Fin 4) ∈ S') (w : S ⊕ Fin 4) :
    (sumSubtypeEquiv hinl hinr w : H ⊕ Fin 4) = Sum.map Subtype.val id w := by
  rcases w with y | k <;> rfl

namespace IsContractibleEdge

variable (hA : A.IsPlabicGraph) {d : H} (he : A.IsContractibleEdge d)

include hA he

omit [NeZero b] hA in
/-- The darts of a contractible edge are not in `B`. -/
theorem notMem_bdry : d ∉ A.bdry := fun h =>
  he.not_isBoundaryVertex (A.isBoundaryVertex_vertexOf_of_mem h)

/-- At a dart of a contractible edge, the involution of `I_i(A, c)` is that of `A`. -/
theorem lollipopInsertion_inv_inl_self :
    (A.lollipopInsertion i c).inv (Sum.inl d) = Sum.inl (A.inv d) :=
  lollipopInsertion_inv_inl_of_notMem_bdry hA (he.notMem_bdry)

/-- An edge of `A` that can be contracted can be contracted in `I_i(A, c)`. -/
theorem lollipopInsertion : (A.lollipopInsertion i c).IsContractibleEdge (Sum.inl d) where
  vertexOf_ne := by
    rw [he.lollipopInsertion_inv_inl_self hA, lollipopInsertion_vertexOf_inl,
      lollipopInsertion_vertexOf_inl]
    exact fun h => he.vertexOf_ne (Finset.map_injective _ h)
  mem_internalVertices := by
    rw [lollipopInsertion_vertexOf_inl]
    exact map_inl_mem_lollipopInsertion_internalVertices.2 he.mem_internalVertices
  inv_mem_internalVertices := by
    rw [he.lollipopInsertion_inv_inl_self hA, lollipopInsertion_vertexOf_inl]
    exact map_inl_mem_lollipopInsertion_internalVertices.2 he.inv_mem_internalVertices
  colour_inv := by
    rw [he.lollipopInsertion_inv_inl_self hA]
    exact he.colour_inv

/-- The dart `lollipopArc i` of the contraction of an edge is that of `A`. -/
theorem coe_contractEdge_lollipopArc :
    ((A.contractEdge d (he.leg_mem hA)).lollipopArc i : H) = A.lollipopArc i := by
  have hx : A.lollipopArc i ∈ (({d, A.inv d} : Set H)ᶜ : Set H) :=
    he.mem_of_mem_bdry hA.lollipopArc_mem_bdry
  have hx' : A.rot (A.lollipopArc i) = A.leg (insertionNext i) := Equiv.apply_symm_apply _ _
  have hrot : (A.contractEdge d (he.leg_mem hA)).rot ⟨A.lollipopArc i, hx⟩ =
      (A.contractEdge d (he.leg_mem hA)).leg (insertionNext i) := by
    apply Subtype.ext
    rw [coe_contractEdge_rot_of_mem (by rw [hx']; exact he.leg_mem hA _), coe_contractEdge_leg,
      hx']
  change ((A.contractEdge d (he.leg_mem hA)).rot.symm
    ((A.contractEdge d (he.leg_mem hA)).leg (insertionNext i)) : H) = _
  rw [← hrot, Equiv.symm_apply_apply]

/-- The involute of the dart `lollipopArc i` of the contraction of an edge is that of `A`. -/
theorem coe_contractEdge_inv_lollipopArc :
    ((A.contractEdge d (he.leg_mem hA)).inv ((A.contractEdge d (he.leg_mem hA)).lollipopArc i) :
      H) = A.inv (A.lollipopArc i) := by
  rw [coe_contractEdge_inv hA.inv_involutive, coe_contractEdge_lollipopArc hA he]

/-- **Contracting an edge commutes with inserting a lollipop.** -/
theorem contractEdge_lollipopInsertion_isomorphic :
    ((A.contractEdge d (he.leg_mem hA)).lollipopInsertion i c).Isomorphic
      ((A.lollipopInsertion i c).contractEdge (Sum.inl d)
        ((he.lollipopInsertion hA (i := i) (c := c)).leg_mem (hA.lollipopInsertion i c))) := by
  have hJ := hA.lollipopInsertion i c
  have he' := he.lollipopInsertion hA (i := i) (c := c)
  have hM := hA.contractEdge he (hleg := he.leg_mem hA)
  have hJd := he.lollipopInsertion_inv_inl_self hA (i := i) (c := c)
  set S : Set H := (({d, A.inv d} : Set H)ᶜ : Set H)
  set S' : Set (H ⊕ Fin 4) :=
    (({Sum.inl d, (A.lollipopInsertion i c).inv (Sum.inl d)} : Set (H ⊕ Fin 4))ᶜ :
      Set (H ⊕ Fin 4))
  have hinl : ∀ y : H, (Sum.inl y : H ⊕ Fin 4) ∈ S' ↔ y ∈ S := fun y => by
    simp [S, S', hJd]
  have hinr : ∀ k : Fin 4, (Sum.inr k : H ⊕ Fin 4) ∈ S' := fun k => by
    simp [S', hJd]
  have hψ := coe_sumSubtypeEquiv hinl hinr
  have harc := coe_contractEdge_lollipopArc hA he (i := i)
  have harc' := coe_contractEdge_inv_lollipopArc hA he (i := i)
  refine ⟨isoOfLeg (hM.lollipopInsertion i c) (hJ.contractEdge he') (sumSubtypeEquiv hinl hinr)
    (fun z => ?_) (fun z => ?_) (fun z => ?_) (fun z _ => ?_) (fun k => ?_)⟩
  · apply Subtype.ext
    rw [hψ, coe_contractEdge_inv hJ.inv_involutive, hψ]
    rcases z with y | k
    · rw [lollipopInsertion_inv_inl_eq hM, Sum.map_inl, lollipopInsertion_inv_inl_eq hA]
      by_cases h1 : (y : H) = A.lollipopArc i
      · rw [if_pos (Subtype.ext (h1.trans harc.symm)), if_pos h1]
        rfl
      rw [if_neg (fun h => h1 (by rw [h, harc])), if_neg h1]
      by_cases h2 : (y : H) = A.inv (A.lollipopArc i)
      · rw [if_pos (Subtype.ext (h2.trans harc'.symm)), if_pos h2]
        rfl
      rw [if_neg (fun h => h2 (by rw [h, harc'])), if_neg h2, Sum.map_inl,
        coe_contractEdge_inv hA.inv_involutive]
    · simp only [Sum.map_inr, id]
      rcases fin_cases_four k with rfl | rfl | rfl | rfl
      · rw [lollipopInsertion_inv_inr_zero_eq hM, lollipopInsertion_inv_inr_zero_eq hA,
          Sum.map_inl, harc]
      · rw [lollipopInsertion_inv_inr_one_eq hM, lollipopInsertion_inv_inr_one_eq hA,
          Sum.map_inl, harc']
      · rw [lollipopInsertion_inv_inr_two, lollipopInsertion_inv_inr_two]; rfl
      · rw [lollipopInsertion_inv_inr_three, lollipopInsertion_inv_inr_three]; rfl
  · apply Subtype.ext
    rw [hψ, contractEdge_rot, coe_inducedRotationPerm, inducedRotation]
    have hπ : ∀ x : H, ((A.lollipopInsertion i c).rot *
        swap (Sum.inl d) ((A.lollipopInsertion i c).inv (Sum.inl d))) (Sum.inl x) =
        Sum.inl ((A.rot * swap d (A.inv d)) x) := fun x => by
      rw [hJd, Perm.mul_apply, Perm.mul_apply, Sum.inl_injective.swap_apply]
      rfl
    rcases z with y | k
    · rw [show sumSubtypeEquiv hinl hinr (Sum.inl y) = ⟨Sum.inl (y : H), (hinl y).2 y.2⟩ from
        rfl, coe_firstReturn_map_of_invariant Sum.inl (P := fun _ => True) (fun _ _ => trivial)
        (fun x _ => hπ x) (fun x _ => hinl x) y trivial ⟨_, (hinl y).2 y.2⟩ rfl]
      rfl
    · rw [show sumSubtypeEquiv hinl hinr (Sum.inr k) = ⟨Sum.inr k, hinr k⟩ from rfl]
      have h : ((A.lollipopInsertion i c).rot *
          swap (Sum.inl d) ((A.lollipopInsertion i c).inv (Sum.inl d))) (Sum.inr k) =
          (A.lollipopInsertion i c).rot (Sum.inr k) := by
        rw [Perm.mul_apply, hJd, swap_apply_of_ne_of_ne (by simp) (by simp)]
      rw [coe_firstReturn_of_apply_mem (by rw [h]; exact hinr _), h]
      rfl
  · rcases z with y | k
    · rw [mem_contractEdge_bdry, hψ, Sum.map_inl, mem_lollipopInsertion_bdry_inl,
        mem_lollipopInsertion_bdry_inl, mem_contractEdge_bdry]
    · rw [mem_contractEdge_bdry, hψ, Sum.map_inr, mem_lollipopInsertion_bdry_inr,
        mem_lollipopInsertion_bdry_inr]
      rfl
  · rcases z with y | k <;> rfl
  · apply Subtype.ext
    rw [hψ, coe_contractEdge_leg]
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · rw [lollipopInsertion_leg_self, lollipopInsertion_leg_self]
      rfl
    · rw [lollipopInsertion_leg_succAbove, lollipopInsertion_leg_succAbove]
      rfl

end IsContractibleEdge

end LollipopMoves

end PlabicData

namespace PlabicGraph

variable {b : ℕ} [NeZero b]

/-- The insertion `I_i(A, c)` of a lollipop, as a bundled plabic graph. -/
def lollipopInsertion (A : PlabicGraph b) (i : Fin (b + 1)) (c : Shade) : PlabicGraph (b + 1) :=
  ⟨A.Dart ⊕ Fin 4, A.data.lollipopInsertion i c, A.isPlabicGraph.lollipopInsertion i c⟩

/-- **Moves commute with inserting a lollipop**: if `A` and `A'` are `S`-equivalent plabic graphs
with `b` boundary vertices, in particular if `A ∼ A'`, then `I_i(A, c)` and `I_i(A', c)` are
`S`-equivalent. -/
@[cluster_algebras "lem_lollipop_insertion_moves"]
theorem MoveEquivalent.lollipopInsertion {S : Set LocalMoveType} {A A' : PlabicGraph b}
    (h : MoveEquivalent S A A') (i : Fin (b + 1)) (c : Shade) :
    MoveEquivalent S (A.lollipopInsertion i c) (A'.lollipopInsertion i c) := by
  refine MoveEquivalent.map_of_commute (fun Q => Q.lollipopInsertion i c) (fun Q Q' hQ => ?_)
    (fun Q c₀ hq => ?_) (fun Q d hd => ?_) (fun Q d he => ?_) h
  · exact PlabicData.Isomorphic.lollipopInsertion Q.isPlabicGraph Q'.isPlabicGraph hQ i c
  · exact ⟨Sum.inl c₀, hq.lollipopInsertion Q.isPlabicGraph,
      hq.squareMove_lollipopInsertion_isomorphic Q.isPlabicGraph⟩
  · exact ⟨Sum.inl d, hd.lollipopInsertion Q.isPlabicGraph,
      hd.bivalentRemoval_lollipopInsertion_isomorphic Q.isPlabicGraph⟩
  · exact ⟨Sum.inl d, he.lollipopInsertion Q.isPlabicGraph,
      he.contractEdge_lollipopInsertion_isomorphic Q.isPlabicGraph⟩

end PlabicGraph

/-! ### Moves of a glued graph lift -/

namespace PlabicData

section GluingMoves

variable {HY HR HR' : Type*} [Fintype HY] [DecidableEq HY] [Fintype HR] [DecidableEq HR]
  [Fintype HR'] [DecidableEq HR'] {b : ℕ} {Y : PlabicData HY b} {f : HY} {R : PlabicData HR 1}

namespace IsLeafGluingSite

variable {p g : HR} (h : Y.IsLeafGluingSite f R p g)

include h

omit [Fintype HY] [DecidableEq HY] in
/-- A dart at an internal vertex of `R` is none of `p̄, p, g`. -/
theorem mem_leafGluingDarts_of_not_isBoundaryVertex {r : HR}
    (hr : ¬R.IsBoundaryVertex (R.vertexOf r)) : Sum.inr r ∈ leafGluingDarts f R p g := by
  simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    reduceCtorEq, Sum.inr.injEq, false_or, not_or]
  refine ⟨fun e => hr ⟨r, R.self_mem_vertexOf r, e ▸ h.mem_bdry_inv_p⟩,
    fun e => hr ⟨r, R.self_mem_vertexOf r, e ▸ h.mem_bdry_p⟩, fun e => hr ?_⟩
  refine ⟨R.inv p, ?_, h.mem_bdry_inv_p⟩
  rw [e, ← h.rot_rot_right]
  exact R.rot_mem_vertexOf g

omit [Fintype HY] [DecidableEq HY] in
/-- A dart of `R` other than `p̄, p, g` lies at an internal vertex of `R`. -/
theorem not_isBoundaryVertex_of_mem_leafGluingDarts {r : HR}
    (hr : Sum.inr r ∈ leafGluingDarts f R p g) : ¬R.IsBoundaryVertex (R.vertexOf r) := by
  rintro ⟨z, hz, hzB⟩
  rw [h.bdry_right, mem_insert, mem_singleton] at hzB
  have := h.mem_triple_of_sameCycle (z := z) (r := r) (by tauto)
    ((RotationSystem.mem_vertexOf _).1 hz).symm
  simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    reduceCtorEq, Sum.inr.injEq, false_or] at hr
  exact hr this

omit [Fintype HY] [Fintype HR] in
/-- At a dart `r` of `R` other than `ḡ`, the involution of `Y⟨f ← R⟩` is that of `R`. -/
theorem coe_leafGluing_inv_inr {x : leafGluingDarts f R p g} {r : HR}
    (hx : (x : HY ⊕ HR) = Sum.inr r) (hr : r ≠ R.inv g) :
    ((Y.leafGluing h).inv x : HY ⊕ HR) = Sum.inr (R.inv r) := by
  rw [h.coe_leafGluing_inv_of_ne (by rw [hx]; simp) (by rw [hx]; simpa using hr), hx]
  rfl

omit [Fintype HY] [Fintype HR] in
/-- At a dart `y` of `Y` other than `f̄`, the involution of `Y⟨f ← R⟩` is that of `Y`. -/
theorem coe_leafGluing_inv_inl {x : leafGluingDarts f R p g} {y : HY}
    (hx : (x : HY ⊕ HR) = Sum.inl y) (hy : y ≠ Y.inv f) :
    ((Y.leafGluing h).inv x : HY ⊕ HR) = Sum.inl (Y.inv y) := by
  rw [h.coe_leafGluing_inv_of_ne (by rw [hx]; simpa using hy) (by rw [hx]; simp), hx]
  rfl

/-- Two darts of `Y⟨f ← R⟩` lie at the same vertex if and only if they lie in the same cycle of
the rotation `Perm.sumCongr Y.rot R.rot`. -/
theorem leafGluing_vertexOf_eq_iff {x z : leafGluingDarts f R p g} :
    (Y.leafGluing h).vertexOf x = (Y.leafGluing h).vertexOf z ↔
      (Perm.sumCongr Y.rot R.rot).SameCycle x z := by
  rw [RotationSystem.vertexOf_eq_vertexOf_iff, h.sameCycle_leafGluing_rot_iff]

/-- The vertex of `Y⟨f ← R⟩` at a dart of `R` is not a boundary vertex. -/
theorem not_isBoundaryVertex_leafGluing_vertexOf_inr {x : leafGluingDarts f R p g} {r : HR}
    (hx : (x : HY ⊕ HR) = Sum.inr r) :
    ¬(Y.leafGluing h).IsBoundaryVertex ((Y.leafGluing h).vertexOf x) := by
  rw [h.isBoundaryVertex_leafGluing_vertexOf_iff]
  rintro ⟨a, ha, -⟩
  rw [hx] at ha
  exact Sum.inr_ne_inl ha

/-- The vertex of the gluing at a dart of an internal vertex of `R` is that vertex of `R`. -/
theorem map_leafGluing_vertexOf_inr {x : leafGluingDarts f R p g} {r : HR}
    (hx : (x : HY ⊕ HR) = Sum.inr r) :
    ((Y.leafGluing h).vertexOf x).map (Function.Embedding.subtype _) =
      (R.vertexOf r).map Function.Embedding.inr := by
  have hint := h.not_isBoundaryVertex_of_mem_leafGluingDarts (hx ▸ x.2)
  ext z
  simp only [mem_map, Function.Embedding.coe_subtype, Function.Embedding.inr_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [RotationSystem.mem_vertexOf, h.sameCycle_leafGluing_rot_iff, hx] at hw
    obtain ⟨v, hv⟩ := w
    rcases v with a | r'
    · exact absurd hw not_sameCycle_sumCongr_inr_inl'
    · exact ⟨r', (RotationSystem.mem_vertexOf _).2 (sameCycle_sumCongr_inr_inr'.1 hw), rfl⟩
  · rintro ⟨r', hr', rfl⟩
    have hr'v : R.vertexOf r' = R.vertexOf r := R.vertexOf_eq_of_mem hr'
    have hmem := h.mem_leafGluingDarts_of_not_isBoundaryVertex (r := r') (hr'v ▸ hint)
    refine ⟨⟨_, hmem⟩, ?_, rfl⟩
    rw [RotationSystem.mem_vertexOf, h.sameCycle_leafGluing_rot_iff, hx]
    exact sameCycle_sumCongr_inr_inr'.2 ((RotationSystem.mem_vertexOf _).1 hr')

/-- The vertex of `Y⟨f ← R⟩` at a dart `r` of `R` has as many darts as the vertex of `R` at
`r`. -/
theorem card_leafGluing_vertexOf_inr {x : leafGluingDarts f R p g} {r : HR}
    (hx : (x : HY ⊕ HR) = Sum.inr r) :
    ((Y.leafGluing h).vertexOf x).card = (R.vertexOf r).card := by
  rw [← card_map (Function.Embedding.subtype _), h.map_leafGluing_vertexOf_inr hx, card_map]

end IsLeafGluingSite

variable (hY : Y.IsPlabicGraph) (hf : f ∉ Y.bdry) (hff : Y.rot f = f)

include hY hf hff in
/-- **An isomorphism of plabic graphs extends to their gluings**: if `R ≅ R'`, then the gluings
of `R` and `R'` into `Y` are isomorphic. -/
theorem Isomorphic.leafGluing {R' : PlabicData HR' 1} (hR : R.IsPlabicGraph)
    (hR' : R'.IsPlabicGraph) (hRR : R.Isomorphic R') :
    (Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY hR hf hff)).Isomorphic
      (Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY hR' hf hff)) := by
  obtain ⟨θ⟩ := hRR
  have h := isLeafGluingSite_of_isPlabicGraph hY hR hf hff
  have h' := isLeafGluingSite_of_isPlabicGraph hY hR' hf hff
  have hg : θ.toEquiv (R.leg 0) = R'.leg 0 := Iso.map_leg hR hR' θ 0
  have hp : θ.toEquiv (R.rot.symm (R.leg 0)) = R'.rot.symm (R'.leg 0) := by
    rw [← hg, Equiv.eq_symm_apply, ← θ.map_rot, Equiv.apply_symm_apply]
  set E : HY ⊕ HR ≃ HY ⊕ HR' := Equiv.sumCongr (Equiv.refl HY) θ.toEquiv with hE
  have hEl : ∀ y, E (Sum.inl y) = Sum.inl y := fun _ => rfl
  have hEr : ∀ r, E (Sum.inr r) = Sum.inr (θ.toEquiv r) := fun _ => rfl
  have hmem : ∀ x, x ∈ leafGluingDarts f R (R.rot.symm (R.leg 0)) (R.leg 0) ↔
      E x ∈ leafGluingDarts f R' (R'.rot.symm (R'.leg 0)) (R'.leg 0) := by
    rintro (y | r)
    · simp [hEl]
    · simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        reduceCtorEq, Sum.inr.injEq, false_or, hEr]
      rw [← hp, ← hg, ← θ.map_inv]
      simp only [θ.toEquiv.injective.eq_iff]
  refine ⟨isoOfLeg (h.isPlabicGraph_leafGluing hY hR) (h'.isPlabicGraph_leafGluing hY hR')
    (E.subtypeEquiv hmem) (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x hx => ?_)
    (fun i => rfl)⟩
  · apply Subtype.ext
    simp only [Equiv.subtypeEquiv_apply, coe_leafGluing_inv, leafGluingInv_apply]
    have hsum : ∀ z, E (Perm.sumCongr Y.inv R.inv z) = Perm.sumCongr Y.inv R'.inv (E z) := by
      rintro (y | r)
      · rfl
      · simp [hE, θ.map_inv]
    rw [E.injective.map_swap, hsum, E.injective.map_swap, hEl, hEr, θ.map_inv, hg]
  · apply Subtype.ext
    simp only [Equiv.subtypeEquiv_apply, coe_leafGluing_rot]
    obtain ⟨y | r, _⟩ := x
    · rfl
    · simp [hE, θ.map_rot]
  · rw [h.mem_leafGluing_bdry_iff, h'.mem_leafGluing_bdry_iff]
    obtain ⟨y | r, _⟩ := x
    · simp [hEl]
    · simp [hEr]
  · obtain ⟨y | r, hxm⟩ := x
    · rfl
    · exact θ.map_colour r (h.not_isBoundaryVertex_of_mem_leafGluingDarts hxm)

private theorem pow_mul_four_apply {α : Type*} (π : Perm α) {x : α} (hx : (π ^ 4) x = x)
    (m : ℕ) : (π ^ (4 * m)) x = x := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Nat.mul_succ, pow_add, Perm.mul_apply, hx, ih]

private theorem pow_apply_eq_pow_mod_four {α : Type*} (π : Perm α) {x : α}
    (hx : (π ^ 4) x = x) (n : ℕ) : (π ^ n) x = (π ^ (n % 4)) x := by
  conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, Perm.mul_apply, pow_mul_four_apply π hx]

namespace IsSquareMoveFace

variable {c₀ : HR} (hq : R.IsSquareMoveFace c₀)

include hq

/-- The vertices of the square face through `c₀` are not boundary vertices. -/
theorem not_isBoundaryVertex_facePerm_pow (n : ℕ) :
    ¬R.IsBoundaryVertex (R.vertexOf ((R.facePerm ^ n) c₀)) := by
  rw [pow_apply_eq_pow_mod_four _ hq.facePerm_pow_four]
  exact R.vertexOf_mem_internalVertices.1
    (hq.vertexOf_mem_internalVertices ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩)

/-- The darts of the square face through `c₀` are not in `B`. -/
theorem facePerm_pow_notMem_bdry (n : ℕ) : (R.facePerm ^ n) c₀ ∉ R.bdry := fun h =>
  hq.not_isBoundaryVertex_facePerm_pow n (R.isBoundaryVertex_vertexOf_of_mem h)

omit [Fintype HY] [DecidableEq HY] in
/-- No dart of the square face through `c₀` is the involute `ḡ` of the leg `g` of `R`. -/
theorem facePerm_pow_ne_inv_leg {p g : HR} (h : Y.IsLeafGluingSite f R p g) (n : ℕ) :
    (R.facePerm ^ n) c₀ ≠ R.inv g := fun e => by
  have := hq.facePerm_pow_notMem_bdry (n + 1)
  rw [pow_succ', Perm.mul_apply, e, RotationSystem.facePerm_apply, h.inv_inv_right,
    h.rot_rot_right] at this
  exact this h.mem_bdry_inv_p

variable {p g : HR} (h : Y.IsLeafGluingSite f R p g)

include h

omit [Fintype HY] [DecidableEq HY] in
/-- The darts of the square face through `c₀` are darts of `Y⟨f ← R⟩`. -/
theorem inr_mem_leafGluingDarts (n : ℕ) :
    Sum.inr ((R.facePerm ^ n) c₀) ∈ leafGluingDarts f R p g :=
  h.mem_leafGluingDarts_of_not_isBoundaryVertex (hq.not_isBoundaryVertex_facePerm_pow n)

omit [Fintype HY] in
/-- On the square face through `c₀`, the powers of the face permutation of `Y⟨f ← R⟩` are those
of `R`. -/
theorem coe_leafGluing_facePerm_pow (n : ℕ) :
    (((Y.leafGluing h).facePerm ^ n) ⟨Sum.inr c₀, hq.inr_mem_leafGluingDarts h 0⟩ :
      HY ⊕ HR) = Sum.inr ((R.facePerm ^ n) c₀) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    have hx : ((((Y.leafGluing h).facePerm ^ n) ⟨Sum.inr c₀, hq.inr_mem_leafGluingDarts h 0⟩ :
        leafGluingDarts f R p g) : HY ⊕ HR) = Sum.inr ((R.facePerm ^ n) c₀) := ih
    rw [h.coe_leafGluing_facePerm_of_ne (by rw [hx]; simp)
      (by rw [hx]; simpa using hq.facePerm_pow_ne_inv_leg h n), hx, pow_succ', Perm.mul_apply]
    rfl

omit [Fintype HY] in
/-- The corners of the square face through `c₀` in `Y⟨f ← R⟩` are those in `R`. -/
theorem coe_leafGluing_squareCorner (k : Fin 4) :
    ((Y.leafGluing h).squareCorner ⟨Sum.inr c₀, hq.inr_mem_leafGluingDarts h 0⟩ k :
      HY ⊕ HR) = Sum.inr (R.squareCorner c₀ k) :=
  hq.coe_leafGluing_facePerm_pow h k

/-- A vertex of `Y⟨f ← R⟩` is a vertex of the square face through `c₀` if and only if it lies at
a dart `r` of `R` whose vertex is a vertex of the square face through `c₀` in `R`. -/
theorem leafGluing_vertexOf_mem_squareVertices_iff (x : leafGluingDarts f R p g) :
    (Y.leafGluing h).vertexOf x ∈
        (Y.leafGluing h).squareVertices ⟨Sum.inr c₀, hq.inr_mem_leafGluingDarts h 0⟩ ↔
      ∃ r, (x : HY ⊕ HR) = Sum.inr r ∧ R.vertexOf r ∈ R.squareVertices c₀ := by
  rw [mem_squareVertices]
  simp only [h.leafGluing_vertexOf_eq_iff, mem_squareVertices]
  obtain ⟨y | r, hx⟩ := x
  · simp only [reduceCtorEq, false_and, exists_false, iff_false, not_exists]
    intro k hk
    rw [hq.coe_leafGluing_squareCorner h k] at hk
    exact not_sameCycle_sumCongr_inr_inl' hk
  · simp only [Sum.inr.injEq, exists_eq_left', hq.coe_leafGluing_squareCorner h,
      sameCycle_sumCongr_inr_inr', RotationSystem.vertexOf_eq_vertexOf_iff]

/-- A square move of `R` is a square move of the gluing `Y⟨f ← R⟩`. -/
theorem leafGluing :
    (Y.leafGluing h).IsSquareMoveFace ⟨Sum.inr c₀, hq.inr_mem_leafGluingDarts h 0⟩ where
  faceOf_mem_internalFaces := by
    refine (Y.leafGluing h).mem_internalFaces.2 ⟨DiskMap.faceOf_mem_faces _ ?_, ?_⟩
    · rw [h.mem_leafGluing_bdry_iff]
      rintro ⟨a, -, ha⟩
      exact Sum.inr_ne_inl ha
    · rw [disjoint_left]
      intro z hz hzB
      obtain ⟨n, rfl⟩ := ((RotationSystem.mem_faceOf _).1 hz).exists_nat_pow_eq
      obtain ⟨a, -, ha⟩ := h.mem_leafGluing_bdry_iff.1 hzB
      rw [hq.coe_leafGluing_facePerm_pow h] at ha
      exact Sum.inr_ne_inl ha
  facePerm_pow_four := Subtype.ext (by
    rw [hq.coe_leafGluing_facePerm_pow h, hq.facePerm_pow_four])
  vertexOf_mem_internalVertices k :=
    (Y.leafGluing h).vertexOf_mem_internalVertices.2
      (h.not_isBoundaryVertex_leafGluing_vertexOf_inr (hq.coe_leafGluing_squareCorner h k))
  injective k l hkl := hq.injective (by
    have := (h.leafGluing_vertexOf_eq_iff).1 hkl
    rw [hq.coe_leafGluing_squareCorner h, hq.coe_leafGluing_squareCorner h,
      sameCycle_sumCongr_inr_inr'] at this
    exact R.vertexOf_eq_vertexOf_iff.2 this)
  card_vertexOf k := by
    rw [h.card_leafGluing_vertexOf_inr (hq.coe_leafGluing_squareCorner h k)]
    exact hq.card_vertexOf k
  colour_ne k := by
    rw [leafGluing_colour, leafGluing_colour, hq.coe_leafGluing_squareCorner h,
      hq.coe_leafGluing_squareCorner h]
    exact hq.colour_ne k

end IsSquareMoveFace

include hY hf hff in
/-- **Square moves commute with gluing.** -/
theorem IsSquareMoveFace.squareMove_leafGluing_isomorphic (hR : R.IsPlabicGraph) {c₀ : HR}
    (hq : R.IsSquareMoveFace c₀) :
    (Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY (hR.squareMove c₀) hf hff)).Isomorphic
      ((Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY hR hf hff)).squareMove
        ⟨Sum.inr c₀, hq.inr_mem_leafGluingDarts (isLeafGluingSite_of_isPlabicGraph hY hR hf hff)
          0⟩) := by
  have h := isLeafGluingSite_of_isPlabicGraph hY hR hf hff
  have hsq := isLeafGluingSite_of_isPlabicGraph hY (hR.squareMove c₀) hf hff
  refine ⟨isoOfLeg (hsq.isPlabicGraph_leafGluing hY (hR.squareMove c₀))
    ((h.isPlabicGraph_leafGluing hY hR).squareMove _) (Equiv.refl _) (fun _ => rfl)
    (fun _ => rfl) (fun _ => Iff.rfl) (fun x _ => ?_) (fun _ => rfl)⟩
  rw [colour_squareMove]
  obtain ⟨y | r, hx⟩ := x
  · rw [if_neg]
    · rfl
    · rw [hq.leafGluing_vertexOf_mem_squareVertices_iff h]
      rintro ⟨r, hr, -⟩
      exact Sum.inl_ne_inr hr
  · change _ = (R.squareMove c₀).colour r
    rw [colour_squareMove R c₀ r]
    by_cases hr : R.vertexOf r ∈ R.squareVertices c₀
    · rw [if_pos ((hq.leafGluing_vertexOf_mem_squareVertices_iff h _).2 ⟨r, rfl, hr⟩), if_pos hr]
      rfl
    · rw [if_neg hr, if_neg (fun h' => by
        obtain ⟨r', hr', hr'm⟩ := (hq.leafGluing_vertexOf_mem_squareVertices_iff h _).1 h'
        exact hr (Sum.inr_injective hr' ▸ hr'm))]
      rfl

namespace IsBivalentRemovable

variable (hR : R.IsPlabicGraph) {d : HR} (hd : R.IsBivalentRemovable d)

omit [Fintype HY] [DecidableEq HY] in
include hd in
/-- A dart at a removable bivalent vertex of `R` is a dart of `Y⟨f ← R⟩`. -/
theorem inr_mem_leafGluingDarts {p g : HR} (h : Y.IsLeafGluingSite f R p g) :
    Sum.inr d ∈ leafGluingDarts f R p g :=
  h.mem_leafGluingDarts_of_not_isBoundaryVertex hd.not_isBoundaryVertex

include hd in
/-- A removable bivalent vertex of `R` is a removable bivalent vertex of the gluing. -/
theorem leafGluing {p g : HR} (h : Y.IsLeafGluingSite f R p g) :
    (Y.leafGluing h).IsBivalentRemovable ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩ where
  not_isBoundaryVertex := h.not_isBoundaryVertex_leafGluing_vertexOf_inr rfl
  card_vertexOf := by
    rw [h.card_leafGluing_vertexOf_inr rfl]
    exact hd.card_vertexOf
  inv_ne_rot := by
    intro e
    have e' : leafGluingInv Y f R g (Sum.inr d) = Sum.inr (R.rot d) := congrArg Subtype.val e
    by_cases hdg : d = R.inv g
    · rw [hdg, h.leafGluingInv_inr_inv_g] at e'
      exact Sum.inl_ne_inr e'
    · have e'' := (h.coe_leafGluing_inv_inr (x := ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩)
        rfl hdg).symm.trans e'
      exact hd.inv_ne_rot (Sum.inr_injective e'')

include hR hd in
/-- **Removing a bivalent vertex commutes with gluing**, for any data `p, g` of the gluing. -/
theorem bivalentRemoval_leafGluing_isomorphic' (hY : Y.IsPlabicGraph) {p g : HR}
    (h : Y.IsLeafGluingSite f R p g) {p' g' : ({d, R.rot d}ᶜ : Set HR)}
    (hm : Y.IsLeafGluingSite f (R.bivalentRemoval hR hd) p' g') (hp' : (p' : HR) = p)
    (hg' : (g' : HR) = g) :
    (Y.leafGluing hm).Isomorphic
      ((Y.leafGluing h).bivalentRemoval (h.isPlabicGraph_leafGluing hY hR)
        (hd.leafGluing h)) := by
  have hM := isPlabicGraph_bivalentRemoval hR hd
  have hZ := h.isPlabicGraph_leafGluing hY hR
  have hd' := hd.leafGluing h
  have hinv := hR.inv_involutive
  have hrd : R.rot d ≠ d := hd.rot_ne
  -- the darts `p̄'` and `ḡ'` of the removal
  have hpi' : (((R.bivalentRemoval hR hd).inv p' : ({d, R.rot d}ᶜ : Set HR)) : HR) =
      R.inv p := by
    rw [coe_bivalentRemoval_inv_of_mem_bdry hR hd (by rw [hp']; exact h.mem_bdry_p), hp']
  have hgbar : (((R.bivalentRemoval hR hd).inv g' : ({d, R.rot d}ᶜ : Set HR)) : HR) =
      if d = R.inv g then R.inv (R.rot d) else if R.rot d = R.inv g then R.inv d
      else R.inv g := by
    by_cases h1 : d = R.inv g
    · rw [if_pos h1]
      exact coe_bivalentRemoval_inv_of_eq_inv hR hd (by rw [hg', h1, hinv])
    rw [if_neg h1]
    by_cases h2 : R.rot d = R.inv g
    · rw [if_pos h2]
      exact coe_bivalentRemoval_inv_of_eq_inv_rot hR hd (by rw [hg', h2, hinv])
    rw [if_neg h2, coe_bivalentRemoval_inv_of_ne hR hd (y := g')
      (fun e => h1 (by rw [← hg', e, hinv])) (fun e => h2 (by rw [← hg', e, hinv])), hg']
  have hdg : d ≠ g := fun e => hd.not_isBoundaryVertex ⟨R.inv p, by
    rw [e, ← h.rot_rot_right]; exact R.rot_mem_vertexOf g, h.mem_bdry_inv_p⟩
  have hrdg : R.rot d ≠ g := fun e => hd.not_isBoundaryVertex ⟨R.inv p, by
    rw [← R.vertexOf_rot, e, ← h.rot_rot_right]; exact R.rot_mem_vertexOf g, h.mem_bdry_inv_p⟩
  have hrotx₀ : (((Y.leafGluing h).rot ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩ :
      leafGluingDarts f R p g) : HY ⊕ HR) = Sum.inr (R.rot d) := rfl
  -- the inclusion of the darts
  have hmemr : ∀ r : ({d, R.rot d}ᶜ : Set HR),
      Sum.inr r ∈ leafGluingDarts f (R.bivalentRemoval hR hd) p' g' ↔
        Sum.inr (r : HR) ∈ leafGluingDarts f R p g := fun r => by
    simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      reduceCtorEq, Sum.inr.injEq, false_or, Subtype.ext_iff, hp', hpi', hg']
  have hmem1 : ∀ x : HY ⊕ ({d, R.rot d}ᶜ : Set HR),
      x ∈ leafGluingDarts f (R.bivalentRemoval hR hd) p' g' →
        Sum.map id Subtype.val x ∈ leafGluingDarts f R p g := by
    rintro (y | r) hx
    · simpa using hx
    · exact (hmemr r).1 hx
  have hmem2 : ∀ x (hx : x ∈ leafGluingDarts f (R.bivalentRemoval hR hd) p' g'),
      (⟨Sum.map id Subtype.val x, hmem1 x hx⟩ : leafGluingDarts f R p g) ∈
        ({⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩,
          (Y.leafGluing h).rot ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩}ᶜ :
            Set (leafGluingDarts f R p g)) := by
    rintro (y | r) hx
    · simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
        Subtype.ext_iff, hrotx₀, Sum.map_inl]
      simp
    · have hr := r.2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
        Subtype.ext_iff, hrotx₀, Sum.map_inr, Sum.inr.injEq]
      exact hr
  let ψ : leafGluingDarts f (R.bivalentRemoval hR hd) p' g' ≃
      ({⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩,
          (Y.leafGluing h).rot ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩}ᶜ :
            Set (leafGluingDarts f R p g)) :=
    Equiv.ofBijective (fun x => ⟨⟨Sum.map id Subtype.val x.1, hmem1 x.1 x.2⟩, hmem2 x.1 x.2⟩)
      ⟨fun x x' e => by
        simp only [Subtype.mk.injEq] at e
        exact Subtype.ext (Sum.map_injective.2 ⟨Function.injective_id, Subtype.val_injective⟩ e),
      by
        rintro ⟨⟨y | r, hw⟩, hw'⟩
        · exact ⟨⟨Sum.inl y, by simpa using hw⟩, rfl⟩
        · have hrS : r ∈ ({d, R.rot d}ᶜ : Set HR) := by
            simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
              Subtype.ext_iff, hrotx₀, Sum.inr.injEq] at hw' ⊢
            exact hw'
          exact ⟨⟨Sum.inr ⟨r, hrS⟩, (hmemr ⟨r, hrS⟩).2 hw⟩, rfl⟩⟩
  have hψ : ∀ x, (((ψ x : leafGluingDarts f R p g)) : HY ⊕ HR) = Sum.map id Subtype.val x.1 :=
    fun _ => rfl
  -- values of the involution of the gluing at `x₀` and `σ x₀`
  have hZx₀ : (((Y.leafGluing h).inv ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩ :
      leafGluingDarts f R p g) : HY ⊕ HR) =
      if d = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv d) := by
    by_cases h1 : d = R.inv g
    · rw [if_pos h1]
      change leafGluingInv Y f R g (Sum.inr d) = _
      rw [h1, h.leafGluingInv_inr_inv_g]
    · rw [if_neg h1]
      exact h.coe_leafGluing_inv_inr rfl h1
  have hZrx₀ : (((Y.leafGluing h).inv
      ((Y.leafGluing h).rot ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩) :
      leafGluingDarts f R p g) : HY ⊕ HR) =
      if R.rot d = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv (R.rot d)) := by
    by_cases h1 : R.rot d = R.inv g
    · rw [if_pos h1]
      change leafGluingInv Y f R g (Sum.inr (R.rot d)) = _
      rw [h1, h.leafGluingInv_inr_inv_g]
    · rw [if_neg h1]
      exact h.coe_leafGluing_inv_inr hrotx₀ h1
  refine ⟨isoOfLeg (hm.isPlabicGraph_leafGluing hY hM) (isPlabicGraph_bivalentRemoval hZ hd') ψ
    (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x _ => ?_) (fun i => rfl)⟩
  · -- the involutions
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨y | r, hx⟩ := x
    · by_cases hy : y = Y.inv f
      · subst hy
        rw [hψ, coe_leafGluing_inv]
        change Sum.map id Subtype.val (leafGluingInv Y f (R.bivalentRemoval hR hd) g'
          (Sum.inl (Y.inv f))) = _
        rw [hm.leafGluingInv_inl_inv_f, Sum.map_inr, hgbar]
        by_cases h1 : d = R.inv g
        · rw [if_pos h1, coe_bivalentRemoval_inv_of_eq_inv hZ hd' (by
            apply Subtype.ext; rw [hZx₀, if_pos h1]; rfl), hZrx₀,
            if_neg (fun e => hrd (e.trans h1.symm))]
        rw [if_neg h1]
        by_cases h2 : R.rot d = R.inv g
        · rw [if_pos h2, coe_bivalentRemoval_inv_of_eq_inv_rot hZ hd' (by
            apply Subtype.ext; rw [hZrx₀, if_pos h2]; rfl), hZx₀, if_neg h1]
        rw [if_neg h2, coe_bivalentRemoval_inv_of_ne hZ hd' (by
            intro e; have := congrArg Subtype.val e; rw [hZx₀, if_neg h1] at this
            exact Sum.inl_ne_inr this) (by
            intro e; have := congrArg Subtype.val e; rw [hZrx₀, if_neg h2] at this
            exact Sum.inl_ne_inr this), coe_leafGluing_inv]
        exact h.leafGluingInv_inl_inv_f.symm
      · have hy' : ((⟨Sum.inl y, hx⟩ : leafGluingDarts f (R.bivalentRemoval hR hd) p' g') :
            HY ⊕ ({d, R.rot d}ᶜ : Set HR)) = Sum.inl y := rfl
        rw [hψ, hm.coe_leafGluing_inv_inl hy' hy, Sum.map_inl,
          coe_bivalentRemoval_inv_of_ne hZ hd' (by
            intro e; have := congrArg Subtype.val e; rw [hZx₀] at this
            split_ifs at this
            · exact hy (Sum.inl_injective this)
            · exact Sum.inl_ne_inr this) (by
            intro e; have := congrArg Subtype.val e; rw [hZrx₀] at this
            split_ifs at this
            · exact hy (Sum.inl_injective this)
            · exact Sum.inl_ne_inr this)]
        have hxy : (((ψ ⟨Sum.inl y, hx⟩ : _) : leafGluingDarts f R p g) : HY ⊕ HR) =
            Sum.inl y := rfl
        exact (h.coe_leafGluing_inv_inl hxy hy).symm
    · have hr := r.2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
      obtain ⟨hrd1, hrd2⟩ := hr
      have hrx : ((⟨Sum.inr r, hx⟩ : leafGluingDarts f (R.bivalentRemoval hR hd) p' g') :
          HY ⊕ _) = Sum.inr r := rfl
      have hrg : (r : HR) ≠ g := fun e => by
        simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, reduceCtorEq, Sum.inr.injEq, false_or, not_or,
          Subtype.ext_iff, hg'] at hx
        exact hx.2.2 e
      have hMr : (((R.bivalentRemoval hR hd).inv r : ({d, R.rot d}ᶜ : Set HR)) : HR) =
          if (r : HR) = R.inv d then R.inv (R.rot d)
          else if (r : HR) = R.inv (R.rot d) then R.inv d else R.inv r := by
        by_cases e1 : (r : HR) = R.inv d
        · rw [if_pos e1]; exact coe_bivalentRemoval_inv_of_eq_inv hR hd e1
        rw [if_neg e1]
        by_cases e2 : (r : HR) = R.inv (R.rot d)
        · rw [if_pos e2]; exact coe_bivalentRemoval_inv_of_eq_inv_rot hR hd e2
        rw [if_neg e2]; exact coe_bivalentRemoval_inv_of_ne hR hd e1 e2
      have hL : (((ψ ((Y.leafGluing hm).inv ⟨Sum.inr r, hx⟩) : leafGluingDarts f R p g)) :
          HY ⊕ HR) =
          if (r : HR) = (if d = R.inv g then R.inv (R.rot d)
            else if R.rot d = R.inv g then R.inv d else R.inv g) then Sum.inl (Y.inv f)
          else Sum.inr (if (r : HR) = R.inv d then R.inv (R.rot d)
            else if (r : HR) = R.inv (R.rot d) then R.inv d else R.inv r) := by
        rw [hψ, ← hgbar, ← hMr]
        by_cases e : (r : HR) =
            (((R.bivalentRemoval hR hd).inv g' : ({d, R.rot d}ᶜ : Set HR)) : HR)
        · rw [if_pos e, coe_leafGluing_inv, hrx,
            show r = (R.bivalentRemoval hR hd).inv g' from Subtype.ext e,
            hm.leafGluingInv_inr_inv_g]
          rfl
        · rw [if_neg e, hm.coe_leafGluing_inv_inr hrx (fun e' => e (by rw [e']))]
          rfl
      have hZr : ∀ w : leafGluingDarts f R p g, (w : HY ⊕ HR) = Sum.inr (r : HR) →
          (((Y.leafGluing h).inv w : leafGluingDarts f R p g) : HY ⊕ HR) =
            if (r : HR) = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv r) := by
        intro w hw
        by_cases e : (r : HR) = R.inv g
        · rw [if_pos e, coe_leafGluing_inv, hw, e, h.leafGluingInv_inr_inv_g]
        · rw [if_neg e]; exact h.coe_leafGluing_inv_inr hw e
      have hR' : ((((Y.leafGluing h).bivalentRemoval hZ hd').inv (ψ ⟨Sum.inr r, hx⟩) :
          leafGluingDarts f R p g) : HY ⊕ HR) =
          if Sum.inr (r : HR) = (if d = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv d))
          then (if R.rot d = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv (R.rot d)))
          else if Sum.inr (r : HR) =
            (if R.rot d = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv (R.rot d)))
          then (if d = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv d))
          else (if (r : HR) = R.inv g then Sum.inl (Y.inv f) else Sum.inr (R.inv r)) := by
        rw [← hZx₀, ← hZrx₀]
        by_cases e1 : Sum.inr (r : HR) = (((Y.leafGluing h).inv
            ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩ : leafGluingDarts f R p g) : HY ⊕ HR)
        · rw [if_pos e1]
          exact congrArg Subtype.val (coe_bivalentRemoval_inv_of_eq_inv hZ hd' (Subtype.ext e1))
        rw [if_neg e1]
        by_cases e2 : Sum.inr (r : HR) = (((Y.leafGluing h).inv ((Y.leafGluing h).rot
            ⟨Sum.inr d, hd.inr_mem_leafGluingDarts h⟩) : leafGluingDarts f R p g) : HY ⊕ HR)
        · rw [if_pos e2]
          exact congrArg Subtype.val
            (coe_bivalentRemoval_inv_of_eq_inv_rot hZ hd' (Subtype.ext e2))
        rw [if_neg e2, coe_bivalentRemoval_inv_of_ne hZ hd' (fun e => e1 (congrArg Subtype.val e))
          (fun e => e2 (congrArg Subtype.val e))]
        exact hZr _ rfl
      rw [hL, hR']
      have hgd : R.inv d ≠ R.inv g := fun e => hdg (R.inv.injective e)
      have hgrd : R.inv (R.rot d) ≠ R.inv g := fun e => hrdg (R.inv.injective e)
      by_cases h1 : d = R.inv g
      · have h2 : R.rot d ≠ R.inv g := fun e => hrd (e.trans h1.symm)
        have h3 : (r : HR) ≠ R.inv d := fun e => hrg (by rw [e, h1, hinv])
        have h5 : (r : HR) ≠ R.inv g := fun e => hrd1 (e.trans h1.symm)
        by_cases h4 : (r : HR) = R.inv (R.rot d)
        · simp only [if_pos h1, if_neg h2, if_neg h3, if_neg h5, if_pos h4, reduceCtorEq,
            Sum.inr.injEq, ↓reduceIte]
        · simp only [if_pos h1, if_neg h2, if_neg h3, if_neg h5, if_neg h4, reduceCtorEq,
            Sum.inr.injEq, ↓reduceIte]
      by_cases h2 : R.rot d = R.inv g
      · have h4 : (r : HR) ≠ R.inv (R.rot d) := fun e => hrg (by rw [e, h2, hinv])
        have h5 : (r : HR) ≠ R.inv g := fun e => hrd2 (e.trans h2.symm)
        by_cases h3 : (r : HR) = R.inv d
        · simp only [if_neg h1, if_pos h2, if_pos h3, if_neg h4, if_neg h5, reduceCtorEq,
            Sum.inr.injEq, ↓reduceIte]
        · simp only [if_neg h1, if_pos h2, if_neg h3, if_neg h4, if_neg h5, reduceCtorEq,
            Sum.inr.injEq, ↓reduceIte]
      by_cases h3 : (r : HR) = R.inv d
      · have h5 : (r : HR) ≠ R.inv g := fun e => hgd (h3.symm.trans e)
        simp only [if_neg h1, if_neg h2, if_pos h3, if_neg h5, Sum.inr.injEq]
      by_cases h4 : (r : HR) = R.inv (R.rot d)
      · have h5 : (r : HR) ≠ R.inv g := fun e => hgrd (h4.symm.trans e)
        simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg h5, Sum.inr.injEq]
      simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, Sum.inr.injEq]
  · apply Subtype.ext
    apply Subtype.ext
    obtain ⟨y | r, hx⟩ := x <;> rfl
  · rw [mem_bivalentRemoval_bdry, h.mem_leafGluing_bdry_iff, hm.mem_leafGluing_bdry_iff, hψ]
    obtain ⟨y | r, hx⟩ := x
    · simp
    · simp
  · obtain ⟨y | r, hx⟩ := x <;> rfl

include hY hf hff hR hd in
/-- **Removing a bivalent vertex commutes with gluing.** -/
theorem bivalentRemoval_leafGluing_isomorphic :
    (Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY (isPlabicGraph_bivalentRemoval hR hd)
      hf hff)).Isomorphic
      ((Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY hR hf hff)).bivalentRemoval
        ((isLeafGluingSite_of_isPlabicGraph hY hR hf hff).isPlabicGraph_leafGluing hY hR)
        (hd.leafGluing (isLeafGluingSite_of_isPlabicGraph hY hR hf hff))) :=
  hd.bivalentRemoval_leafGluing_isomorphic' hR hY _ _ (coe_bivalentRemoval_rot_symm hR hd _) rfl

end IsBivalentRemovable

namespace IsContractibleEdge

variable (hR : R.IsPlabicGraph) {d : HR} (he : R.IsContractibleEdge d)

omit [Fintype HY] [DecidableEq HY] in
/-- The contraction keeps the darts `σ⁻¹(g_k)` and the rotation there. -/
theorem coe_contractEdge_rot_symm_leg {c : ℕ} {A : PlabicData HR c} (hA : A.IsPlabicGraph)
    {d : HR} (he : A.IsContractibleEdge d) (k : Fin c) :
    ((A.contractEdge d (he.leg_mem hA)).rot.symm ((A.contractEdge d (he.leg_mem hA)).leg k) :
      HR) = A.rot.symm (A.leg k) := by
  have hx : A.rot.symm (A.leg k) ∈ (({d, A.inv d} : Set HR)ᶜ : Set HR) :=
    he.mem_of_mem_bdry (A.exterior_subset_bdry (hA.rot_symm_leg_mem_exterior k))
  have hx' : A.rot (A.rot.symm (A.leg k)) = A.leg k := Equiv.apply_symm_apply _ _
  have hrot : (A.contractEdge d (he.leg_mem hA)).rot ⟨A.rot.symm (A.leg k), hx⟩ =
      (A.contractEdge d (he.leg_mem hA)).leg k := by
    apply Subtype.ext
    rw [coe_contractEdge_rot_of_mem (by rw [hx']; exact he.leg_mem hA _), coe_contractEdge_leg,
      hx']
  rw [← hrot, Equiv.symm_apply_apply]

omit [Fintype HY] [DecidableEq HY] in
include he in
/-- A dart of a contractible edge of `R` is a dart of `Y⟨f ← R⟩`. -/
theorem inr_mem_leafGluingDarts {p g : HR} (h : Y.IsLeafGluingSite f R p g) :
    Sum.inr d ∈ leafGluingDarts f R p g :=
  h.mem_leafGluingDarts_of_not_isBoundaryVertex he.not_isBoundaryVertex

omit [Fintype HY] [DecidableEq HY] in
include he in
/-- The involute of a dart of a contractible edge of `R` is a dart of `Y⟨f ← R⟩`. -/
theorem inr_inv_mem_leafGluingDarts {p g : HR} (h : Y.IsLeafGluingSite f R p g) :
    Sum.inr (R.inv d) ∈ leafGluingDarts f R p g :=
  h.mem_leafGluingDarts_of_not_isBoundaryVertex he.not_isBoundaryVertex_inv

omit [Fintype HY] [DecidableEq HY] in
include he in
/-- An edge that can be contracted is not the edge `{g, ḡ}` of the leg of `R`. -/
theorem ne_inv_leg {p g : HR} (h : Y.IsLeafGluingSite f R p g) : d ≠ R.inv g := fun e => by
  have := he.inr_inv_mem_leafGluingDarts h
  rw [e, h.inv_inv_right] at this
  simp at this

omit [Fintype HY] in
include he in
/-- At a dart of a contractible edge of `R`, the involution of `Y⟨f ← R⟩` is that of `R`. -/
theorem coe_leafGluing_inv_self {p g : HR} (h : Y.IsLeafGluingSite f R p g) :
    (((Y.leafGluing h).inv ⟨Sum.inr d, he.inr_mem_leafGluingDarts h⟩ :
      leafGluingDarts f R p g) : HY ⊕ HR) = Sum.inr (R.inv d) :=
  h.coe_leafGluing_inv_inr rfl (he.ne_inv_leg h)

include he in
/-- An edge of `R` that can be contracted can be contracted in the gluing. -/
theorem leafGluing {p g : HR} (h : Y.IsLeafGluingSite f R p g) :
    (Y.leafGluing h).IsContractibleEdge ⟨Sum.inr d, he.inr_mem_leafGluingDarts h⟩ where
  vertexOf_ne := by
    rw [Ne, h.leafGluing_vertexOf_eq_iff, show (((Y.leafGluing h).inv
      ⟨Sum.inr d, he.inr_mem_leafGluingDarts h⟩ : leafGluingDarts f R p g) : HY ⊕ HR) =
        Sum.inr (R.inv d) from he.coe_leafGluing_inv_self h]
    exact fun hs => he.not_sameCycle (sameCycle_sumCongr_inr_inr'.1 hs)
  mem_internalVertices := (Y.leafGluing h).vertexOf_mem_internalVertices.2
    (h.not_isBoundaryVertex_leafGluing_vertexOf_inr rfl)
  inv_mem_internalVertices := (Y.leafGluing h).vertexOf_mem_internalVertices.2
    (h.not_isBoundaryVertex_leafGluing_vertexOf_inr (he.coe_leafGluing_inv_self h))
  colour_inv := by
    rw [leafGluing_colour, leafGluing_colour, he.coe_leafGluing_inv_self h]
    exact he.colour_inv

include hR he in
/-- **Contracting an edge commutes with gluing**, for any data `p, g` of the gluing. -/
theorem contractEdge_leafGluing_isomorphic' (hY : Y.IsPlabicGraph) {p g : HR}
    (h : Y.IsLeafGluingSite f R p g) {p' g' : (({d, R.inv d} : Set HR)ᶜ : Set HR)}
    (hm : Y.IsLeafGluingSite f (R.contractEdge d (he.leg_mem hR)) p' g') (hp' : (p' : HR) = p)
    (hg' : (g' : HR) = g) :
    (Y.leafGluing hm).Isomorphic
      ((Y.leafGluing h).contractEdge ⟨Sum.inr d, he.inr_mem_leafGluingDarts h⟩
        ((he.leafGluing h).leg_mem (h.isPlabicGraph_leafGluing hY hR))) := by
  have hM := hR.contractEdge he (hleg := he.leg_mem hR)
  have hZ := h.isPlabicGraph_leafGluing hY hR
  have he' := he.leafGluing h
  have hinv := hR.inv_involutive
  have hZinv := h.leafGluing_inv_involutive
  have hx₀ := he.coe_leafGluing_inv_self h
  have hpi' : (((R.contractEdge d (he.leg_mem hR)).inv p' : (({d, R.inv d} : Set HR)ᶜ :
      Set HR)) : HR) = R.inv p := by
    rw [coe_contractEdge_inv hinv, hp']
  have hgbar : (((R.contractEdge d (he.leg_mem hR)).inv g' : (({d, R.inv d} : Set HR)ᶜ :
      Set HR)) : HR) = R.inv g := by
    rw [coe_contractEdge_inv hinv, hg']
  set D := leafGluingDarts f R p g
  set x₀ : D := ⟨Sum.inr d, he.inr_mem_leafGluingDarts h⟩
  have hmemr : ∀ r : (({d, R.inv d} : Set HR)ᶜ : Set HR),
      Sum.inr r ∈ leafGluingDarts f (R.contractEdge d (he.leg_mem hR)) p' g' ↔
        Sum.inr (r : HR) ∈ D := fun r => by
    simp only [D, leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, reduceCtorEq, Sum.inr.injEq, false_or, Subtype.ext_iff, hp', hpi',
      hg']
  have hmem1 : ∀ x : HY ⊕ (({d, R.inv d} : Set HR)ᶜ : Set HR),
      x ∈ leafGluingDarts f (R.contractEdge d (he.leg_mem hR)) p' g' →
        Sum.map id Subtype.val x ∈ D := by
    rintro (y | r) hx
    · simpa [D] using hx
    · exact (hmemr r).1 hx
  have hS' : ∀ w : D, w ∈ (({x₀, (Y.leafGluing h).inv x₀} : Set D)ᶜ : Set D) ↔
      (w : HY ⊕ HR) ≠ Sum.inr d ∧ (w : HY ⊕ HR) ≠ Sum.inr (R.inv d) := fun w => by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
      Subtype.ext_iff, x₀, hx₀]
  have hmem2 : ∀ x (hx : x ∈ leafGluingDarts f (R.contractEdge d (he.leg_mem hR)) p' g'),
      (⟨Sum.map id Subtype.val x, hmem1 x hx⟩ : D) ∈
        (({x₀, (Y.leafGluing h).inv x₀} : Set D)ᶜ : Set D) := by
    rintro (y | r) hx
    · rw [hS']
      simp
    · have hr := r.2
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
      rw [hS']
      simpa using hr
  let ψ : leafGluingDarts f (R.contractEdge d (he.leg_mem hR)) p' g' ≃
      (({x₀, (Y.leafGluing h).inv x₀} : Set D)ᶜ : Set D) :=
    Equiv.ofBijective (fun x => ⟨⟨Sum.map id Subtype.val x.1, hmem1 x.1 x.2⟩, hmem2 x.1 x.2⟩)
      ⟨fun x x' e => by
        simp only [Subtype.mk.injEq] at e
        exact Subtype.ext (Sum.map_injective.2 ⟨Function.injective_id, Subtype.val_injective⟩ e),
      by
        rintro ⟨⟨y | r, hw⟩, hw'⟩
        · exact ⟨⟨Sum.inl y, by simpa [D] using hw⟩, rfl⟩
        · have hrS : r ∈ (({d, R.inv d} : Set HR)ᶜ : Set HR) := by
            rw [hS'] at hw'
            simpa using hw'
          exact ⟨⟨Sum.inr ⟨r, hrS⟩, (hmemr ⟨r, hrS⟩).2 hw⟩, rfl⟩⟩
  have hψ : ∀ x, (((ψ x : D)) : HY ⊕ HR) = Sum.map id Subtype.val x.1 := fun _ => rfl
  refine ⟨isoOfLeg (hm.isPlabicGraph_leafGluing hY hM) (hZ.contractEdge he') ψ
    (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x _ => ?_) (fun i => rfl)⟩
  · -- the involutions
    apply Subtype.ext
    rw [coe_contractEdge_inv hZinv]
    apply Subtype.ext
    rw [hψ]
    obtain ⟨y | r, hx⟩ := x
    · by_cases hy : y = Y.inv f
      · subst hy
        rw [coe_leafGluing_inv]
        change Sum.map id Subtype.val (leafGluingInv Y f (R.contractEdge d (he.leg_mem hR)) g'
          (Sum.inl (Y.inv f))) = leafGluingInv Y f R g (Sum.inl (Y.inv f))
        rw [hm.leafGluingInv_inl_inv_f, h.leafGluingInv_inl_inv_f, Sum.map_inr, hgbar]
      · have hy' : ((⟨Sum.inl y, hx⟩ : leafGluingDarts f (R.contractEdge d (he.leg_mem hR)) p'
            g') : HY ⊕ (({d, R.inv d} : Set HR)ᶜ : Set HR)) = Sum.inl y := rfl
        have hxy : (((ψ ⟨Sum.inl y, hx⟩ : _) : D) : HY ⊕ HR) = Sum.inl y := rfl
        rw [hm.coe_leafGluing_inv_inl hy' hy, h.coe_leafGluing_inv_inl hxy hy, Sum.map_inl]
        rfl
    · have hrx : ((⟨Sum.inr r, hx⟩ : leafGluingDarts f (R.contractEdge d (he.leg_mem hR)) p'
          g') : HY ⊕ (({d, R.inv d} : Set HR)ᶜ : Set HR)) = Sum.inr r := rfl
      have hxr : (((ψ ⟨Sum.inr r, hx⟩ : _) : D) : HY ⊕ HR) = Sum.inr (r : HR) := rfl
      by_cases hrg : (r : HR) = R.inv g
      · have hr : r = (R.contractEdge d (he.leg_mem hR)).inv g' :=
          Subtype.ext (hrg.trans hgbar.symm)
        have e1 : leafGluingInv Y f (R.contractEdge d (he.leg_mem hR)) g' (Sum.inr r) =
            Sum.inl (Y.inv f) := by
          rw [hr, hm.leafGluingInv_inr_inv_g]
        rw [coe_leafGluing_inv, hrx, e1, coe_leafGluing_inv, hxr, hrg, h.leafGluingInv_inr_inv_g]
        rfl
      · rw [hm.coe_leafGluing_inv_inr hrx (fun e => hrg (by rw [e, hgbar])),
          h.coe_leafGluing_inv_inr hxr hrg, Sum.map_inr, coe_contractEdge_inv hinv]
  · -- the rotations
    apply Subtype.ext
    apply Subtype.ext
    rw [hψ, contractEdge_rot, coe_inducedRotationPerm, inducedRotation]
    obtain ⟨y | r, hx⟩ := x
    · have hmemy : (Y.leafGluing h).rot (ψ ⟨Sum.inl y, hx⟩ : D) ∈
          (({x₀, (Y.leafGluing h).inv x₀} : Set D)ᶜ : Set D) := by
        rw [hS']; simp [hψ]
      have hτ : ((Y.leafGluing h).rot * swap x₀ ((Y.leafGluing h).inv x₀))
          (ψ ⟨Sum.inl y, hx⟩ : D) = (Y.leafGluing h).rot (ψ ⟨Sum.inl y, hx⟩ : D) := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne]
        · intro e; have := congrArg Subtype.val e; simp [hψ, x₀] at this
        · intro e; have := congrArg Subtype.val e; rw [hx₀] at this; simp [hψ] at this
      rw [coe_firstReturn_of_apply_mem (hτ ▸ hmemy), hτ]
      rfl
    · -- the first returns
      have hdS : ∀ z : HR, Sum.inr z ∈ D → Sum.inr (swap d (R.inv d) z) ∈ D := fun z hz => by
        rw [swap_apply_def]
        split_ifs
        · exact he.inr_inv_mem_leafGluingDarts h
        · exact he.inr_mem_leafGluingDarts h
        · exact hz
      let ε : HR → D := fun z => if hz : Sum.inr z ∈ D then ⟨Sum.inr z, hz⟩ else x₀
      have hε : ∀ z (hz : Sum.inr z ∈ D), ε z = ⟨Sum.inr z, hz⟩ := fun z hz => dif_pos hz
      have key := coe_firstReturn_map_of_invariant ε (π := R.rot * swap d (R.inv d))
        (π' := (Y.leafGluing h).rot * swap x₀ ((Y.leafGluing h).inv x₀))
        (P := fun z => Sum.inr z ∈ D)
        (fun z hz => (h.rot_mem_iff (Sum.inr _)).2 (hdS z hz))
        (fun z hz => by
          rw [hε z hz, hε ((R.rot * swap d (R.inv d)) z) ((h.rot_mem_iff (Sum.inr _)).2 (hdS z hz))]
          apply Subtype.ext
          rw [Perm.mul_apply, coe_leafGluing_rot, ← Subtype.val_injective.swap_apply, hx₀]
          change Perm.sumCongr Y.rot R.rot (swap (Sum.inr d) (Sum.inr (R.inv d)) (Sum.inr z)) = _
          rw [Sum.inr_injective.swap_apply]
          rfl)
        (S := (({d, R.inv d} : Set HR)ᶜ : Set HR))
        (S' := (({x₀, (Y.leafGluing h).inv x₀} : Set D)ᶜ : Set D))
        (fun z hz => by
          rw [hε z hz, hS']
          simp [not_or])
        r ((hmemr r).1 hx) (ψ ⟨Sum.inr r, hx⟩) (by rw [hε _ ((hmemr r).1 hx)]; rfl)
      rw [key, hε ((firstReturn (R.rot * swap d (R.inv d)) (({d, R.inv d} : Set HR)ᶜ : Set HR)
        r : (({d, R.inv d} : Set HR)ᶜ : Set HR)) : HR)
        ((hmemr _).1 ((hm.rot_mem_iff (Sum.inr r)).2 hx))]
      rfl
  · rw [mem_contractEdge_bdry, h.mem_leafGluing_bdry_iff, hm.mem_leafGluing_bdry_iff, hψ]
    obtain ⟨y | r, hx⟩ := x
    · simp
    · simp
  · obtain ⟨y | r, hx⟩ := x <;> rfl

include hY hf hff hR he in
/-- **Contracting an edge commutes with gluing.** -/
theorem contractEdge_leafGluing_isomorphic :
    (Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY (hR.contractEdge he
      (hleg := he.leg_mem hR)) hf hff)).Isomorphic
      ((Y.leafGluing (isLeafGluingSite_of_isPlabicGraph hY hR hf hff)).contractEdge
        ⟨Sum.inr d, he.inr_mem_leafGluingDarts (isLeafGluingSite_of_isPlabicGraph hY hR hf hff)⟩
        ((he.leafGluing (isLeafGluingSite_of_isPlabicGraph hY hR hf hff)).leg_mem
          ((isLeafGluingSite_of_isPlabicGraph hY hR hf hff).isPlabicGraph_leafGluing hY hR))) :=
  he.contractEdge_leafGluing_isomorphic' hR hY _ _ (coe_contractEdge_rot_symm_leg hR he 0) rfl

end IsContractibleEdge

end GluingMoves

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

/-- The gluing `Y⟨f ← R⟩` of a plabic graph `R` with one boundary vertex into the leaf `{f}` of a
plabic graph `Y`, as a bundled plabic graph. -/
def leafGluing (Y : PlabicGraph b) {f : Y.Dart} (hf : f ∉ Y.data.bdry)
    (hff : Y.data.rot f = f) (R : PlabicGraph 1) : PlabicGraph b :=
  ⟨_, Y.data.leafGluing
      (PlabicData.isLeafGluingSite_of_isPlabicGraph Y.isPlabicGraph R.isPlabicGraph hf hff),
    (PlabicData.isLeafGluingSite_of_isPlabicGraph Y.isPlabicGraph R.isPlabicGraph hf
      hff).isPlabicGraph_leafGluing Y.isPlabicGraph R.isPlabicGraph⟩

/-- **Moves of the glued graph lift**: if `R` and `R'` are `S`-equivalent plabic graphs with one
boundary vertex, in particular if `R ∼ R'`, then the gluings `Y⟨f ← R⟩` and `Y⟨f ← R'⟩` into the
leaf `{f}` of a plabic graph `Y` are `S`-equivalent. -/
@[cluster_algebras "lem_leaf_gluing_moves"]
theorem MoveEquivalent.leafGluing (Y : PlabicGraph b) {f : Y.Dart} (hf : f ∉ Y.data.bdry)
    (hff : Y.data.rot f = f) {S : Set LocalMoveType} {R R' : PlabicGraph 1}
    (h : MoveEquivalent S R R') :
    MoveEquivalent S (Y.leafGluing hf hff R) (Y.leafGluing hf hff R') := by
  have hY := Y.isPlabicGraph
  refine MoveEquivalent.map_of_commute (fun Q => Y.leafGluing hf hff Q) (fun Q Q' hQ => ?_)
    (fun Q c₀ hq => ?_) (fun Q d hd => ?_) (fun Q d he => ?_) h
  · exact PlabicData.Isomorphic.leafGluing hY hf hff Q.isPlabicGraph Q'.isPlabicGraph hQ
  · exact ⟨_, hq.leafGluing (PlabicData.isLeafGluingSite_of_isPlabicGraph hY Q.isPlabicGraph hf
      hff), hq.squareMove_leafGluing_isomorphic hY hf hff Q.isPlabicGraph⟩
  · exact ⟨_, hd.leafGluing
      (PlabicData.isLeafGluingSite_of_isPlabicGraph hY Q.isPlabicGraph hf hff),
      hd.bivalentRemoval_leafGluing_isomorphic hY hf hff Q.isPlabicGraph⟩
  · exact ⟨_, he.leafGluing
      (PlabicData.isLeafGluingSite_of_isPlabicGraph hY Q.isPlabicGraph hf hff),
      he.contractEdge_leafGluing_isomorphic hY hf hff Q.isPlabicGraph⟩

end PlabicGraph

end ClusterAlgebras
