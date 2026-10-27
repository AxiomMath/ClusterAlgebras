/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap
public import ClusterAlgebras.Plabic.FirstReturn

/-!
# Contracting an edge

Let `G = (H, d ↦ d̄, σ, B, κ, β)` be a plabic graph and `{d, d̄}` an edge whose endpoints
`u = v(d)` and `w = v(d̄)` are distinct internal vertices of the same colour. The *contraction*
(M3) of `G` along `{d, d̄}` removes the two darts of the edge: its darts are `H' = H \ {d, d̄}`,
its involution is the restriction of `d ↦ d̄`, and its rotation `σ'` is the first-return map to
`H'` of `τ = σ ∘ (d d̄)`. The vertices `u` and `w` are replaced by the *merged vertex*
`U = (u ∪ w) \ {d, d̄}`, which receives the common colour of `u` and `w`; everything else is
unchanged.

The vertices of the contraction are the vertices of `G` other than `u` and `w`, together with the
nonempty set `U`; its faces are the traces `f ∩ H'` of the orbits `f` of the face permutation of
`G`; and it is again a plabic graph, with the same boundary vertices, legs, and numbers of faces
and of internal faces. If the rotations at `u` and `w` are the cycles `(d a₁ … a_p)` and
`(d̄ b₁ … b_q)`, the rotation at the merged vertex is the cycle `(a₁ … a_p b₁ … b_q)`.

## Main definitions

* `ClusterAlgebras.PlabicData.IsContractibleEdge`: the conditions on the edge.
* `ClusterAlgebras.PlabicData.contractEdge`: the contraction of an edge.
* `ClusterAlgebras.PlabicData.mergedVertex`: the merged vertex `(v(d) ∪ v(d̄)) \ {d, d̄}`.

## Main results

* `ClusterAlgebras.PlabicData.image_vertices_contractEdge`,
  `ClusterAlgebras.PlabicData.mergedVertex_nonempty`: the vertices of the contraction.
* `ClusterAlgebras.PlabicData.bijOn_faceOrbits_contractEdge`: the faces of the contraction.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.contractEdge`,
  `ClusterAlgebras.PlabicData.image_boundaryVertices_contractEdge`,
  `ClusterAlgebras.PlabicData.coe_contractEdge_leg`,
  `ClusterAlgebras.PlabicData.map_bvertex_contractEdge`,
  `ClusterAlgebras.PlabicData.card_faces_contractEdge`,
  `ClusterAlgebras.PlabicData.card_internalFaces_contractEdge`: the contraction is a plabic graph
  with the same boundary vertices and legs, and the same numbers of faces and of internal faces.
* `ClusterAlgebras.PlabicData.contractEdge_mergedVertex_rotation`: the rotation at the merged
  vertex.

## Implementation notes

* The darts of the contraction form the subtype `({d, d̄} : Set H)ᶜ` of `H`, so that the rotation
  is the induced rotation `ClusterAlgebras.inducedRotationPerm`. Sets of darts of the contraction
  are compared with sets of darts of `G` through their images under the inclusion
  `Function.Embedding.subtype`, and `f ∩ H'` is `Finset.subtype`.
* The construction is defined for raw data. Its involution is the first-return map of `d ↦ d̄` to
  `H'`, which is the restriction of `d ↦ d̄` as soon as `d ↦ d̄` is an involution
  (`coe_contractEdge_inv`); this keeps the construction total. The legs of `G` must avoid `d` and
  `d̄`, which holds when `v(d)` and `v(d̄)` are internal (`IsContractibleEdge.leg_mem`).
* The colouring is on darts, so the colour of a dart of `H'` is its colour in `G`. When the two
  endpoints have the same colour, this gives the merged vertex their common colour.
* The rotation at a vertex, written as a cycle `(d a₁ … a_p)`, is encoded by a duplicate-free list
  `d :: [a₁, …, a_p]` on which `σ` acts as `List.formPerm`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- The conditions of the **contraction** (M3) of the edge `{d, d̄}`: the endpoints `v(d)` and
`v(d̄)` are distinct internal vertices of the same colour. -/
@[cluster_algebras "def_edge_contraction"]
structure IsContractibleEdge (d : H) : Prop where
  /-- The endpoints are distinct. -/
  vertexOf_ne : G.vertexOf d ≠ G.vertexOf (G.inv d)
  /-- `v(d)` is internal. -/
  mem_internalVertices : G.vertexOf d ∈ G.internalVertices
  /-- `v(d̄)` is internal. -/
  inv_mem_internalVertices : G.vertexOf (G.inv d) ∈ G.internalVertices
  /-- The endpoints have the same colour. -/
  colour_inv : G.colour (G.inv d) = G.colour d

/-- The **contraction** of `G` along the edge `{d, d̄}`: the tuple `(H', d ↦ d̄, σ', B, κ', β)` on
the darts `H' = H \ {d, d̄}`, where `σ'` is the first-return map to `H'` of `τ = σ ∘ (d d̄)`, and
`κ'` and `β` are those of `G`. The legs of `G` are required to lie in `H'`. -/
@[cluster_algebras "def_edge_contraction"]
noncomputable def contractEdge (d : H) (hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    PlabicData (({d, G.inv d} : Set H)ᶜ : Set H) b where
  inv := firstReturnPerm G.inv _
  rot := inducedRotationPerm G.inv G.rot d
  bdry := G.bdry.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
  colour x := G.colour x
  leg i := ⟨G.leg i, hleg i⟩

/-- The **merged vertex** `(v(d) ∪ v(d̄)) \ {d, d̄}` of the contraction along `{d, d̄}`. -/
def mergedVertex (d : H) : Finset H := (G.vertexOf d ∪ G.vertexOf (G.inv d)) \ {d, G.inv d}

variable {G}

/-- A dart lies in the merged vertex iff it lies at `v(d)` or `v(d̄)` and is neither `d` nor
`d̄`. -/
theorem mem_mergedVertex {d x : H} : x ∈ G.mergedVertex d ↔
    (x ∈ G.vertexOf d ∨ x ∈ G.vertexOf (G.inv d)) ∧ x ≠ d ∧ x ≠ G.inv d := by
  simp [mergedVertex, not_or]

omit [Fintype H] [DecidableEq H] in
/-- A dart lies in `H \ {d, d̄}` iff it is neither `d` nor `d̄`. -/
theorem mem_compl_pair_iff {d x : H} :
    x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) ↔ x ≠ d ∧ x ≠ G.inv d := by
  simp [not_or]

/-- A dart outside `v(d) ∪ v(d̄)` is neither `d` nor `d̄`. -/
theorem mem_compl_pair_of_notMem {d x : H} (hx : x ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
  rw [mem_compl_pair_iff]
  refine ⟨fun h' => hx (mem_union_left _ (h' ▸ G.self_mem_vertexOf _)), fun h' => ?_⟩
  exact hx (mem_union_right _ (h' ▸ G.self_mem_vertexOf _))

namespace IsContractibleEdge

variable {d : H} (he : G.IsContractibleEdge d)

include he

/-- The endpoint `v(d)` is not a boundary vertex. -/
theorem not_isBoundaryVertex : ¬G.IsBoundaryVertex (G.vertexOf d) :=
  G.vertexOf_mem_internalVertices.1 he.mem_internalVertices

/-- The endpoint `v(d̄)` is not a boundary vertex. -/
theorem not_isBoundaryVertex_inv : ¬G.IsBoundaryVertex (G.vertexOf (G.inv d)) :=
  G.vertexOf_mem_internalVertices.1 he.inv_mem_internalVertices

/-- The darts `d` and `d̄` lie in different cycles of the rotation `σ`. -/
theorem not_sameCycle : ¬G.rot.SameCycle d (G.inv d) := fun h =>
  he.vertexOf_ne (G.vertexOf_eq_vertexOf_iff.2 h)

/-- A dart at a boundary vertex is not at either endpoint of the edge. -/
theorem notMem_of_isBoundaryVertex {x : H} (hx : G.IsBoundaryVertex (G.vertexOf x)) :
    x ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  intro h
  rcases mem_union.1 h with h | h
  · exact he.not_isBoundaryVertex (G.vertexOf_eq_of_mem h ▸ hx)
  · exact he.not_isBoundaryVertex_inv (G.vertexOf_eq_of_mem h ▸ hx)

/-- A dart of `B` is neither `d` nor `d̄`. -/
theorem mem_of_mem_bdry {x : H} (hx : x ∈ G.bdry) :
    x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
  mem_compl_pair_of_notMem (he.notMem_of_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem hx))

/-- In a plabic graph the legs avoid `d` and `d̄`. -/
theorem leg_mem (hG : G.IsPlabicGraph) (i : Fin b) :
    G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
  mem_compl_pair_of_notMem
    (he.notMem_of_isBoundaryVertex (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)))

end IsContractibleEdge

/-- The rotation keeps a dart outside `v(d) ∪ v(d̄)` outside. -/
theorem rot_notMem_of_notMem {d x : H} (hx : x ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    G.rot x ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  intro h
  have hx' : x ∈ G.vertexOf (G.rot x) := by
    rw [G.vertexOf_rot]
    exact G.self_mem_vertexOf x
  rcases mem_union.1 h with h | h
  · exact hx (mem_union_left _ (G.vertexOf_eq_of_mem h ▸ hx'))
  · exact hx (mem_union_right _ (G.vertexOf_eq_of_mem h ▸ hx'))

/-! ### Basic API -/

section API

variable {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- The rotation of the contraction is the first-return map to `H \ {d, d̄}` of `σ ∘ (d d̄)`. -/
theorem contractEdge_rot : (G.contractEdge d hleg).rot = inducedRotationPerm G.inv G.rot d := rfl

/-- The involution of the contraction is the first-return map of `d ↦ d̄` to `H \ {d, d̄}`. -/
theorem contractEdge_inv : (G.contractEdge d hleg).inv = firstReturnPerm G.inv _ := rfl

/-- A dart of the contraction lies in its boundary arcs iff it lies in `B`. -/
@[simp]
theorem mem_contractEdge_bdry {x : (({d, G.inv d} : Set H)ᶜ : Set H)} :
    x ∈ (G.contractEdge d hleg).bdry ↔ (x : H) ∈ G.bdry :=
  mem_subtype

/-- The colour of a dart of the contraction is its colour in `G`. -/
@[simp]
theorem contractEdge_colour (x : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).colour x = G.colour x := rfl

/-- The contraction keeps the legs. -/
@[cluster_algebras "lem_edge_contraction_plabic", simp]
theorem coe_contractEdge_leg (i : Fin b) : ((G.contractEdge d hleg).leg i : H) = G.leg i := rfl

/-- The involution of the contraction is the restriction of `d ↦ d̄`. -/
theorem coe_contractEdge_inv (hinv : Involutive G.inv) (x : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).inv x : H) = G.inv x := by
  rw [contractEdge_inv, coe_firstReturnPerm]
  exact coe_firstReturn_of_apply_mem ((apply_mem_compl_pair_iff hinv d x).2 x.2)

/-- The involution of the contraction is the restriction of `d ↦ d̄`, as a permutation. -/
theorem contractEdge_inv_eq_subtypePerm (hinv : Involutive G.inv) :
    (G.contractEdge d hleg).inv = G.inv.subtypePerm (apply_mem_compl_pair_iff hinv d) := by
  ext x
  rw [coe_contractEdge_inv hinv, Perm.subtypePerm_apply]

/-- The boundary arcs of the contraction, read in `H`, are `B`. -/
theorem map_contractEdge_bdry (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).bdry.map (Embedding.subtype _) = G.bdry :=
  subtype_map_of_mem fun _ hx => he.mem_of_mem_bdry hx

omit [Fintype H] [DecidableEq H] in
private theorem pow_succ_apply' (τ : Perm H) (n : ℕ) (x : H) : (τ ^ (n + 1)) x = τ ((τ ^ n) x) := by
  rw [pow_succ', Perm.mul_apply]

/-- The rotation of the contraction is `σ` at a dart `x` with `σ x ∉ {d, d̄}`. -/
theorem coe_contractEdge_rot_of_mem {x : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (h : G.rot x ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).rot x : H) = G.rot x := by
  have hx := mem_compl_pair_iff.1 x.2
  have hτ : (G.rot * swap d (G.inv d)) x = G.rot x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2]
  rw [contractEdge_rot, coe_inducedRotationPerm, inducedRotation,
    coe_firstReturn_of_apply_mem (hτ ▸ h), hτ]

/-- If `σ x = d`, the rotation of the contraction sends `x` to `σ d̄` when `σ d̄ ∉ {d, d̄}`. -/
theorem coe_contractEdge_rot_of_eq {x : (({d, G.inv d} : Set H)ᶜ : Set H)} (hxd : G.rot x = d)
    (h : G.rot (G.inv d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).rot x : H) = G.rot (G.inv d) := by
  have hx := mem_compl_pair_iff.1 x.2
  set τ := G.rot * swap d (G.inv d)
  have h1 : (τ ^ 1) x = d := by
    rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2, hxd]
  have h2 : (τ ^ 2) x = G.rot (G.inv d) := by
    rw [pow_succ_apply', h1, Perm.mul_apply, swap_apply_left]
  rw [contractEdge_rot, coe_inducedRotationPerm, inducedRotation,
    coe_firstReturn_of_pow (m := 2) (by norm_num) (h2 ▸ h), h2]
  intro j hj hj2
  obtain rfl : j = 1 := by omega
  rw [h1]
  simp

/-- If `σ x = d` and `σ d̄ = d̄`, the rotation of the contraction sends `x` to `σ d` when
`σ d ∉ {d, d̄}`. -/
theorem coe_contractEdge_rot_of_eq_of_eq {x : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hxd : G.rot x = d) (hd' : G.rot (G.inv d) = G.inv d)
    (h : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).rot x : H) = G.rot d := by
  have hx := mem_compl_pair_iff.1 x.2
  set τ := G.rot * swap d (G.inv d)
  have h1 : (τ ^ 1) x = d := by
    rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2, hxd]
  have h2 : (τ ^ 2) x = G.inv d := by
    rw [pow_succ_apply', h1, Perm.mul_apply, swap_apply_left, hd']
  have h3 : (τ ^ 3) x = G.rot d := by
    rw [pow_succ_apply', h2, Perm.mul_apply, swap_apply_right]
  rw [contractEdge_rot, coe_inducedRotationPerm, inducedRotation,
    coe_firstReturn_of_pow (m := 3) (by norm_num) (h3 ▸ h), h3]
  intro j hj hj3
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
  · rw [h1]; simp
  · rw [h2]; simp

/-- If `σ x = d̄`, the rotation of the contraction sends `x` to `σ d` when `σ d ∉ {d, d̄}`. -/
theorem coe_contractEdge_rot_of_eq_inv {x : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hxd : G.rot x = G.inv d) (h : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).rot x : H) = G.rot d := by
  have hx := mem_compl_pair_iff.1 x.2
  set τ := G.rot * swap d (G.inv d)
  have h1 : (τ ^ 1) x = G.inv d := by
    rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2, hxd]
  have h2 : (τ ^ 2) x = G.rot d := by
    rw [pow_succ_apply', h1, Perm.mul_apply, swap_apply_right]
  rw [contractEdge_rot, coe_inducedRotationPerm, inducedRotation,
    coe_firstReturn_of_pow (m := 2) (by norm_num) (h2 ▸ h), h2]
  intro j hj hj2
  obtain rfl : j = 1 := by omega
  rw [h1]
  simp

/-- If `σ x = d̄` and `σ d = d`, the rotation of the contraction sends `x` to `σ d̄` when
`σ d̄ ∉ {d, d̄}`. -/
theorem coe_contractEdge_rot_of_eq_inv_of_eq {x : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hxd : G.rot x = G.inv d) (hd : G.rot d = d)
    (h : G.rot (G.inv d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).rot x : H) = G.rot (G.inv d) := by
  have hx := mem_compl_pair_iff.1 x.2
  set τ := G.rot * swap d (G.inv d)
  have h1 : (τ ^ 1) x = G.inv d := by
    rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2, hxd]
  have h2 : (τ ^ 2) x = d := by
    rw [pow_succ_apply', h1, Perm.mul_apply, swap_apply_right, hd]
  have h3 : (τ ^ 3) x = G.rot (G.inv d) := by
    rw [pow_succ_apply', h2, Perm.mul_apply, swap_apply_left]
  rw [contractEdge_rot, coe_inducedRotationPerm, inducedRotation,
    coe_firstReturn_of_pow (m := 3) (by norm_num) (h3 ▸ h), h3]
  intro j hj hj3
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
  · rw [h1]; simp
  · rw [h2]; simp

end API

/-! ### Vertices -/

section Vertices

variable {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- Two darts of the contraction lie at one vertex exactly when they lie at one vertex of `G`, or
one lies at `v(d)` and the other at `v(d̄)`. -/
theorem sameCycle_contractEdge_rot_iff (hne : ¬G.rot.SameCycle d (G.inv d))
    {x y : (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).rot.SameCycle x y ↔ G.rot.SameCycle x y ∨
      (G.rot.SameCycle x d ∧ G.rot.SameCycle y (G.inv d)) ∨
      (G.rot.SameCycle x (G.inv d) ∧ G.rot.SameCycle y d) := by
  rw [contractEdge_rot, inducedRotationPerm, sameCycle_firstReturnPerm_iff]
  exact sameCycle_mul_swap_iff G.rot hne

/-- The vertex of the contraction at a dart of `v(d) ∪ v(d̄)` is the merged vertex. -/
theorem map_vertexOf_contractEdge_of_mem (hne : ¬G.rot.SameCycle d (G.inv d))
    {x : (({d, G.inv d} : Set H)ᶜ : Set H)} (hx : (x : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).vertexOf x).map (Embedding.subtype _) = G.mergedVertex d := by
  have key : ∀ a : (({d, G.inv d} : Set H)ᶜ : Set H), (G.contractEdge d hleg).rot.SameCycle x a ↔
      G.rot.SameCycle d a ∨ G.rot.SameCycle (G.inv d) a := by
    intro a
    rw [sameCycle_contractEdge_rot_iff hne]
    rcases mem_union.1 hx with hx | hx <;> rw [RotationSystem.mem_vertexOf] at hx
    · constructor
      · rintro (h | ⟨-, h⟩ | ⟨h, -⟩)
        · exact Or.inl (hx.trans h)
        · exact Or.inr h.symm
        · exact absurd (hx.trans h) hne
      · rintro (h | h)
        · exact Or.inl (hx.symm.trans h)
        · exact Or.inr (Or.inl ⟨hx.symm, h.symm⟩)
    · constructor
      · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
        · exact Or.inr (hx.trans h)
        · exact absurd (hx.trans h).symm hne
        · exact Or.inl h.symm
      · rintro (h | h)
        · exact Or.inr (Or.inr ⟨hx.symm, h.symm⟩)
        · exact Or.inl (hx.symm.trans h)
  ext y
  simp only [mem_map, Embedding.coe_subtype, RotationSystem.mem_vertexOf, mem_mergedVertex]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(key a).1 ha, mem_compl_pair_iff.1 a.2⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨y, mem_compl_pair_iff.2 hy⟩, (key _).2 h, rfl⟩

/-- The vertex of the contraction at a dart outside `v(d) ∪ v(d̄)` is its vertex in `G`. -/
theorem map_vertexOf_contractEdge_of_notMem (hne : ¬G.rot.SameCycle d (G.inv d))
    {x : (({d, G.inv d} : Set H)ᶜ : Set H)} (hx : (x : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).vertexOf x).map (Embedding.subtype _) = G.vertexOf x := by
  have hxd : ¬G.rot.SameCycle x d := fun h =>
    hx (mem_union_left _ ((RotationSystem.mem_vertexOf _).2 h.symm))
  have hxd' : ¬G.rot.SameCycle x (G.inv d) := fun h =>
    hx (mem_union_right _ ((RotationSystem.mem_vertexOf _).2 h.symm))
  have key : ∀ a : (({d, G.inv d} : Set H)ᶜ : Set H),
      (G.contractEdge d hleg).rot.SameCycle x a ↔ G.rot.SameCycle x a := by
    intro a
    rw [sameCycle_contractEdge_rot_iff hne]
    refine ⟨?_, Or.inl⟩
    rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
    exacts [h, absurd h hxd, absurd h hxd']
  ext y
  simp only [mem_map, Embedding.coe_subtype, RotationSystem.mem_vertexOf]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (key a).1 ha
  · intro h
    exact ⟨⟨y, mem_compl_pair_iff.2 ⟨fun h' => hxd (h' ▸ h), fun h' => hxd' (h' ▸ h)⟩⟩,
      (key _).2 h, rfl⟩

/-- **The merged vertex is nonempty.** -/
@[cluster_algebras "lem_edge_contraction_vertices"]
theorem mergedVertex_nonempty (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    (G.mergedVertex d).Nonempty := by
  by_contra hU
  have hS : ∀ z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d), z = d ∨ z = G.inv d := by
    intro z hz
    by_contra h
    exact hU ⟨z, mem_mergedVertex.2 ⟨mem_union.1 hz, not_or.1 h⟩⟩
  have hreach : ∀ z, G.Reach d z → z = d ∨ z = G.inv d := by
    intro z h
    induction h with
    | refl => exact Or.inl rfl
    | @rot e _ ih =>
      apply hS
      rcases ih with rfl | rfl
      · exact mem_union_left _ (G.rot_mem_vertexOf _)
      · exact mem_union_right _ (G.rot_mem_vertexOf _)
    | @inv e _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (hG.inv_involutive _)
  obtain ⟨z, -, hzB⟩ := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem ⟨0, hG.one_le⟩)
  have := mem_compl_pair_iff.1 (he.mem_of_mem_bdry hzB)
  exact (hreach z (hG.reach d z)).elim this.1 this.2

/-- **Vertices under the contraction of an edge**: read in `H`, the vertices of the contraction
are the vertices of `G` other than `v(d)` and `v(d̄)`, together with the merged vertex
`(v(d) ∪ v(d̄)) \ {d, d̄}` (which is nonempty, `mergedVertex_nonempty`). -/
@[cluster_algebras "lem_edge_contraction_vertices"]
theorem image_vertices_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).vertices.image (Finset.map (Embedding.subtype _)) =
      insert (G.mergedVertex d)
        ((G.vertices.erase (G.vertexOf d)).erase (G.vertexOf (G.inv d))) := by
  have hne := he.not_sameCycle
  ext v
  simp only [mem_image, mem_insert, mem_erase]
  constructor
  · rintro ⟨_, hv', rfl⟩
    obtain ⟨x, rfl⟩ := (RotationSystem.mem_vertices _).1 hv'
    by_cases hx : (x : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · exact Or.inl (map_vertexOf_contractEdge_of_mem hne hx)
    · right
      rw [map_vertexOf_contractEdge_of_notMem hne hx]
      refine ⟨fun h => hx (mem_union_right _ (h ▸ G.self_mem_vertexOf _)),
        fun h => hx (mem_union_left _ (h ▸ G.self_mem_vertexOf _)), G.vertexOf_mem_vertices _⟩
  · rintro (rfl | ⟨hw, hu, hv⟩)
    · obtain ⟨y, hy⟩ := mergedVertex_nonempty hG he
      have hy' := mem_mergedVertex.1 hy
      refine ⟨_, RotationSystem.vertexOf_mem_vertices _ ⟨y, mem_compl_pair_iff.2 hy'.2⟩, ?_⟩
      exact map_vertexOf_contractEdge_of_mem hne (mem_union.2 hy'.1)
    · obtain ⟨z, rfl⟩ := (RotationSystem.mem_vertices _).1 hv
      have hz : z ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := fun h =>
        (mem_union.1 h).elim (fun h => hu (G.vertexOf_eq_of_mem h))
          fun h => hw (G.vertexOf_eq_of_mem h)
      refine ⟨_, RotationSystem.vertexOf_mem_vertices _ ⟨z, mem_compl_pair_of_notMem hz⟩, ?_⟩
      exact map_vertexOf_contractEdge_of_notMem hne hz

end Vertices

/-! ### Faces -/

section Faces

variable {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- The face permutation of the contraction is the first-return map of `φ` to `H \ {d, d̄}`. -/
theorem contractEdge_facePerm (hinv : Involutive G.inv) :
    (G.contractEdge d hleg).facePerm = firstReturnPerm G.facePerm (({d, G.inv d} : Set H)ᶜ) := by
  rw [RotationSystem.facePerm, contractEdge_rot, contractEdge_inv_eq_subtypePerm hinv]
  exact inducedRotationPerm_mul_subtypePerm hinv G.rot d

/-- Two darts of `H \ {d, d̄}` lie in one orbit of the contraction's face permutation iff they lie
in one orbit of `φ`. -/
theorem sameCycle_contractEdge_facePerm_iff (hinv : Involutive G.inv)
    {x y : (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).facePerm.SameCycle x y ↔ G.facePerm.SameCycle x y := by
  rw [contractEdge_facePerm hinv]
  exact sameCycle_firstReturnPerm_iff _ _

/-- At least one endpoint of the edge has a dart other than `d`, `d̄`. -/
theorem rot_ne_or_rot_inv_ne (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    G.rot d ≠ d ∨ G.rot (G.inv d) ≠ G.inv d := by
  obtain ⟨y, hy⟩ := mergedVertex_nonempty hG he
  obtain ⟨hy | hy, hyd, hyd'⟩ := mem_mergedVertex.1 hy
  · left
    intro h
    obtain ⟨n, hn⟩ := ((RotationSystem.mem_vertexOf _).1 hy).exists_nat_pow_eq
    exact hyd (hn ▸ pow_apply_eq_self_of_apply_eq_self h n)
  · right
    intro h
    obtain ⟨n, hn⟩ := ((RotationSystem.mem_vertexOf _).1 hy).exists_nat_pow_eq
    exact hyd' (hn ▸ pow_apply_eq_self_of_apply_eq_self h n)

private theorem exists_mem_sameCycle_facePerm_aux (hG : G.IsPlabicGraph)
    (he : G.IsContractibleEdge d) {e : H} (hde : e = d ∨ e = G.inv d) (hfix : G.rot e ≠ e) :
    ∃ y ∈ (({d, G.inv d} : Set H)ᶜ : Set H), G.facePerm.SameCycle e y := by
  refine ⟨G.inv (G.rot.symm e), ?_, ?_⟩
  · rw [apply_mem_compl_pair_iff hG.inv_involutive, mem_compl_pair_iff]
    have hmem : G.rot.symm e ∈ G.vertexOf e := G.rot_symm_mem_vertexOf e
    have hne : G.rot.symm e ≠ e := fun h => hfix (by rw [← h, Equiv.apply_symm_apply, h])
    have hsc := (RotationSystem.mem_vertexOf _).1 hmem
    rcases hde with rfl | rfl
    · refine ⟨hne, fun h => he.not_sameCycle ?_⟩
      rwa [h] at hsc
    · refine ⟨fun h => he.not_sameCycle ?_, hne⟩
      rw [h] at hsc
      exact hsc.symm
  · have : G.facePerm (G.inv (G.rot.symm e)) = e := by
      rw [RotationSystem.facePerm_apply, hG.inv_involutive, Equiv.apply_symm_apply]
    have hs : G.facePerm.SameCycle (G.inv (G.rot.symm e)) (G.facePerm (G.inv (G.rot.symm e))) :=
      Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
    rw [this] at hs
    exact hs.symm

/-- Every orbit of `φ` meets `H \ {d, d̄}`. -/
theorem exists_mem_sameCycle_facePerm (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    (z : H) : ∃ y ∈ (({d, G.inv d} : Set H)ᶜ : Set H), G.facePerm.SameCycle z y := by
  by_cases hz : z ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
  · exact ⟨z, hz, Equiv.Perm.SameCycle.refl _ _⟩
  rw [mem_compl_pair_iff, not_and_or, not_not, not_not] at hz
  have hinv := hG.inv_involutive
  have hstep : ∀ x, G.facePerm.SameCycle x (G.facePerm x) := fun x =>
    Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
  have h1 : G.rot d = d → G.facePerm.SameCycle (G.inv d) d := fun h => by
    have := hstep (G.inv d)
    rwa [RotationSystem.facePerm_apply, hinv, h] at this
  have h2 : G.rot (G.inv d) = G.inv d → G.facePerm.SameCycle d (G.inv d) := fun h => by
    have := hstep d
    rwa [RotationSystem.facePerm_apply, h] at this
  rcases hz with rfl | rfl
  · by_cases hd : G.rot z = z
    · obtain ⟨y, hy, hzy⟩ := exists_mem_sameCycle_facePerm_aux hG he (Or.inr rfl)
        ((rot_ne_or_rot_inv_ne hG he).resolve_left (not_not.2 hd))
      exact ⟨y, hy, (h1 hd).symm.trans hzy⟩
    · exact exists_mem_sameCycle_facePerm_aux hG he (Or.inl rfl) hd
  · by_cases hd : G.rot (G.inv d) = G.inv d
    · obtain ⟨y, hy, hzy⟩ := exists_mem_sameCycle_facePerm_aux hG he (Or.inl rfl)
        ((rot_ne_or_rot_inv_ne hG he).resolve_right (not_not.2 hd))
      exact ⟨y, hy, (h2 hd).symm.trans hzy⟩
    · exact exists_mem_sameCycle_facePerm_aux hG he (Or.inr rfl) hd

/-- The trace on `H \ {d, d̄}` of the orbit of `φ` through `z` is the orbit of the contraction's
face permutation through any dart `y ∉ {d, d̄}` of that orbit. -/
theorem subtype_faceOf_eq_faceOf (hinv : Involutive G.inv) {z y : H}
    (hy : y ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) (hzy : G.facePerm.SameCycle z y) :
    (G.faceOf z).subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) =
      (G.contractEdge d hleg).faceOf ⟨y, hy⟩ := by
  ext a
  rw [mem_subtype, RotationSystem.mem_faceOf, RotationSystem.mem_faceOf,
    sameCycle_contractEdge_facePerm_iff hinv]
  exact ⟨hzy.symm.trans, hzy.trans⟩

/-- **Faces under the contraction of an edge**: `f ↦ f ∩ H'` is a bijection from the orbits of
`φ` onto the orbits of the face permutation `σ' ∘ (d ↦ d̄)|_{H'}` of the contraction, where
`H' = H \ {d, d̄}`. -/
@[cluster_algebras "lem_edge_contraction_faces"]
theorem bijOn_faceOrbits_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    Set.BijOn (fun f : Finset H => f.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))
      G.faceOrbits (G.contractEdge d hleg).faceOrbits := by
  have hinv := hG.inv_involutive
  refine ⟨fun f hf => ?_, fun f hf f' hf' hff' => ?_, fun g hg => ?_⟩
  · obtain ⟨z, rfl⟩ := (RotationSystem.mem_faceOrbits _).1 (mem_coe.1 hf)
    obtain ⟨y, hy, hzy⟩ := exists_mem_sameCycle_facePerm hG he z
    simp only [mem_coe]
    rw [subtype_faceOf_eq_faceOf hinv hy hzy]
    exact RotationSystem.faceOf_mem_faceOrbits _ _
  · obtain ⟨z, rfl⟩ := (RotationSystem.mem_faceOrbits _).1 (mem_coe.1 hf)
    obtain ⟨z', rfl⟩ := (RotationSystem.mem_faceOrbits _).1 (mem_coe.1 hf')
    obtain ⟨y, hy, hzy⟩ := exists_mem_sameCycle_facePerm hG he z
    obtain ⟨y', hy', hzy'⟩ := exists_mem_sameCycle_facePerm hG he z'
    simp only at hff'
    rw [subtype_faceOf_eq_faceOf (hleg := hleg) hinv hy hzy,
      subtype_faceOf_eq_faceOf (hleg := hleg) hinv hy' hzy',
      RotationSystem.faceOf_eq_faceOf_iff, sameCycle_contractEdge_facePerm_iff hinv] at hff'
    exact (RotationSystem.faceOf_eq_faceOf_iff _).2 (hzy.trans (hff'.trans hzy'.symm))
  · obtain ⟨x, rfl⟩ := (RotationSystem.mem_faceOrbits _).1 (mem_coe.1 hg)
    exact ⟨G.faceOf x, mem_coe.2 (RotationSystem.faceOf_mem_faceOrbits _ _),
      subtype_faceOf_eq_faceOf hinv x.2 (Equiv.Perm.SameCycle.refl _ _)⟩

end Faces

/-! ### The contraction is a plabic graph -/

section Plabic

variable {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- A set of darts of the contraction contains a dart of `B` iff its image in `H` does. -/
theorem isBoundaryVertex_contractEdge_iff {v : Finset (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).IsBoundaryVertex v ↔
      G.IsBoundaryVertex (v.map (Embedding.subtype _)) := by
  simp only [DiskMap.IsBoundaryVertex, mem_map, Embedding.coe_subtype, mem_contractEdge_bdry]
  exact ⟨fun ⟨a, ha, haB⟩ => ⟨a, ⟨a, ha, rfl⟩, haB⟩, fun ⟨_, ⟨a, ha, rfl⟩, haB⟩ => ⟨a, ha, haB⟩⟩

/-- The merged vertex contains no dart of `B`. -/
theorem IsContractibleEdge.not_isBoundaryVertex_mergedVertex (he : G.IsContractibleEdge d) :
    ¬G.IsBoundaryVertex (G.mergedVertex d) := by
  rintro ⟨a, ha, haB⟩
  exact he.notMem_of_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem haB)
    (mem_union.2 (mem_mergedVertex.1 ha).1)

/-- A vertex of the contraction is a boundary vertex iff the corresponding vertex of `G` is. -/
theorem isBoundaryVertex_vertexOf_contractEdge_iff (he : G.IsContractibleEdge d)
    {x : (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).IsBoundaryVertex ((G.contractEdge d hleg).vertexOf x) ↔
      G.IsBoundaryVertex (G.vertexOf x) := by
  rw [isBoundaryVertex_contractEdge_iff]
  by_cases hx : (x : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · rw [map_vertexOf_contractEdge_of_mem he.not_sameCycle hx]
    exact iff_of_false he.not_isBoundaryVertex_mergedVertex
      fun h => he.notMem_of_isBoundaryVertex h hx
  · rw [map_vertexOf_contractEdge_of_notMem he.not_sameCycle hx]

/-- The exterior of the contraction, read in `H`, is the exterior of `G`. -/
theorem map_exterior_contractEdge (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).exterior.map (Embedding.subtype _) = G.exterior := by
  ext y
  simp only [mem_map, Embedding.coe_subtype, DiskMap.mem_exterior, mem_contractEdge_bdry]
  constructor
  · rintro ⟨a, ⟨haB, hra⟩, rfl⟩
    have hna := he.notMem_of_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem haB)
    rw [coe_contractEdge_rot_of_mem (mem_compl_pair_of_notMem (rot_notMem_of_notMem hna))] at hra
    exact ⟨haB, hra⟩
  · rintro ⟨hyB, hry⟩
    refine ⟨⟨y, he.mem_of_mem_bdry hyB⟩, ⟨hyB, ?_⟩, rfl⟩
    have hna := he.notMem_of_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem hyB)
    rwa [coe_contractEdge_rot_of_mem (mem_compl_pair_of_notMem (rot_notMem_of_notMem hna))]

/-- The trace on `H \ {d, d̄}` of the exterior of `G` is the exterior of the contraction. -/
theorem subtype_exterior (he : G.IsContractibleEdge d) :
    G.exterior.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) =
      (G.contractEdge d hleg).exterior := by
  apply map_injective (Embedding.subtype _)
  rw [map_exterior_contractEdge he,
    subtype_map_of_mem fun x hx => he.mem_of_mem_bdry (G.exterior_subset_bdry hx)]

/-- The involution of the contraction, read in `H`, is `d ↦ d̄`. -/
theorem map_map_contractEdge_inv (hinv : Involutive G.inv)
    (s : Finset (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (s.map (G.contractEdge d hleg).inv.toEmbedding).map (Embedding.subtype _) =
      (s.map (Embedding.subtype _)).map G.inv.toEmbedding := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [coe_contractEdge_inv hinv]

/-- The contraction has the same labelled boundary vertices as `G`: its vertex `β(i)`, read in
`H`, is the vertex `β(i)` of `G`. -/
@[cluster_algebras "lem_edge_contraction_plabic"]
theorem map_bvertex_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    (i : Fin b) :
    ((G.contractEdge d hleg).bvertex i).map (Embedding.subtype _) = G.bvertex i :=
  map_vertexOf_contractEdge_of_notMem he.not_sameCycle
    (he.notMem_of_isBoundaryVertex (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)))

/-- The edges of the contraction, read in `H`, are edges of `G`. -/
theorem map_edgeOf_contractEdge (hinv : Involutive G.inv)
    (x : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    ((G.contractEdge d hleg).edgeOf x).map (Embedding.subtype _) = G.edgeOf x := by
  simp only [RotationSystem.edgeOf, map_insert, map_singleton, Embedding.coe_subtype,
    coe_contractEdge_inv hinv]

/-- The edges of the contraction are the edges of `G` other than `{d, d̄}`. -/
theorem image_edges_contractEdge (hinv : Involutive G.inv) :
    (G.contractEdge d hleg).edges.image (Finset.map (Embedding.subtype _)) =
      G.edges.erase (G.edgeOf d) := by
  ext e
  simp only [mem_image, mem_erase, RotationSystem.mem_edges]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [map_edgeOf_contractEdge hinv]
    refine ⟨fun h => ?_, x, rfl⟩
    have hd : d ∈ G.edgeOf x := h ▸ by simp [RotationSystem.edgeOf]
    have hx := mem_compl_pair_iff.1 x.2
    rcases (RotationSystem.mem_edgeOf _).1 hd with h' | h'
    · exact hx.1 h'.symm
    · have h'' := congrArg G.inv h'
      rw [hinv] at h''
      exact hx.2 h''.symm
  · rintro ⟨hne, z, rfl⟩
    have hz : z ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
      rw [mem_compl_pair_iff]
      refine ⟨fun h => hne (h ▸ rfl), fun h => hne ?_⟩
      rw [h]
      ext y
      simp only [RotationSystem.mem_edgeOf, hinv d]
      tauto
    exact ⟨_, ⟨⟨z, hz⟩, rfl⟩, map_edgeOf_contractEdge hinv _⟩

/-- The contraction has one vertex fewer than `G`. -/
theorem card_vertices_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    ((G.contractEdge d hleg).vertices.card : ℤ) = G.vertices.card - 1 := by
  have h := congrArg Finset.card (image_vertices_contractEdge (hleg := hleg) hG he)
  rw [card_image_of_injective _ (map_injective _)] at h
  have hU : G.mergedVertex d ∉ (G.vertices.erase (G.vertexOf d)).erase (G.vertexOf (G.inv d)) := by
    intro hU
    obtain ⟨hw, hu, hV⟩ := by simpa only [mem_erase] using hU
    obtain ⟨z, hz⟩ := (RotationSystem.mem_vertices _).1 hV
    obtain ⟨y, hy⟩ := mergedVertex_nonempty hG he
    have hyz : G.vertexOf y = G.mergedVertex d := by
      rw [← hz]
      exact G.vertexOf_eq_of_mem (hz ▸ hy)
    rcases (mem_mergedVertex.1 hy).1 with h' | h'
    · exact hu (hyz ▸ G.vertexOf_eq_of_mem h')
    · exact hw (hyz ▸ G.vertexOf_eq_of_mem h')
  rw [card_insert_of_notMem hU, card_erase_of_mem,
    card_erase_of_mem (G.vertexOf_mem_vertices d)] at h
  · have h2 : 2 ≤ G.vertices.card := by
      have := card_le_card (insert_subset (G.vertexOf_mem_vertices d)
        (singleton_subset_iff.2 (G.vertexOf_mem_vertices (G.inv d))))
      rwa [card_insert_of_notMem (by simpa using he.vertexOf_ne), card_singleton] at this
    omega
  · exact mem_erase.2 ⟨he.vertexOf_ne.symm, G.vertexOf_mem_vertices _⟩

/-- The contraction has one edge fewer than `G`. -/
theorem card_edges_contractEdge (hinv : Involutive G.inv) :
    ((G.contractEdge d hleg).edges.card : ℤ) = G.edges.card - 1 := by
  have h := congrArg Finset.card (image_edges_contractEdge (hleg := hleg) hinv)
  rw [card_image_of_injective _ (map_injective _),
    card_erase_of_mem ((RotationSystem.mem_edges _).2 ⟨d, rfl⟩)] at h
  have : 1 ≤ G.edges.card := card_pos.2 ⟨_, (RotationSystem.mem_edges _).2 ⟨d, rfl⟩⟩
  omega

/-- The face permutations of the contraction and of `G` have equally many orbits. -/
theorem card_faceOrbits_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).faceOrbits.card = G.faceOrbits.card := by
  have h := bijOn_faceOrbits_contractEdge (hleg := hleg) hG he
  exact (card_nbij _ h.mapsTo h.injOn h.surjOn).symm

/-- The colour is constant along the rotation at an internal vertex of a plabic graph. -/
theorem colour_eq_of_sameCycle (hG : G.IsPlabicGraph) {a z : H}
    (ha : ¬G.IsBoundaryVertex (G.vertexOf a)) (h : G.rot.SameCycle a z) :
    G.colour z = G.colour a := by
  have key : ∀ n : ℕ, G.colour ((G.rot ^ n) a) = G.colour a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hv : ¬G.IsBoundaryVertex (G.vertexOf ((G.rot ^ n) a)) := by
        rwa [G.vertexOf_eq_of_mem
          ((RotationSystem.mem_vertexOf _).2 (sameCycle_pow_apply_self _ a n))]
      rw [pow_succ_apply', hG.colour_rot _ hv, ih]
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact key n

/-- All darts at the two endpoints of the edge have the colour of `d`. -/
theorem colour_eq_of_mem_union (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) {z : H}
    (hz : z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) : G.colour z = G.colour d := by
  rcases mem_union.1 hz with h | h
  · exact colour_eq_of_sameCycle hG he.not_isBoundaryVertex ((RotationSystem.mem_vertexOf _).1 h)
  · exact (colour_eq_of_sameCycle hG he.not_isBoundaryVertex_inv
      ((RotationSystem.mem_vertexOf _).1 h)).trans he.colour_inv

/-- In the contraction, every dart reaches every other. -/
theorem reach_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    (x y : (({d, G.inv d} : Set H)ᶜ : Set H)) : (G.contractEdge d hleg).Reach x y := by
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  have hτ : ∀ a b : (({d, G.inv d} : Set H)ᶜ : Set H),
      (G.rot * swap d (G.inv d)).SameCycle a b → (G.contractEdge d hleg).Reach a b := by
    intro a b h
    have h' : (G.contractEdge d hleg).rot.SameCycle a b := by
      rwa [contractEdge_rot, inducedRotationPerm, sameCycle_firstReturnPerm_iff]
    obtain ⟨n, rfl⟩ := h'.exists_nat_pow_eq
    exact RotationSystem.reach_pow_apply _ (fun z => (RotationSystem.Reach.refl z).rot) n a
  have hτσ : ∀ a b : H, G.rot.SameCycle a b → (G.rot * swap d (G.inv d)).SameCycle a b :=
    fun a b h => (sameCycle_mul_swap_iff G.rot hne).2 (Or.inl h)
  have hτd : (G.rot * swap d (G.inv d)).SameCycle d (G.inv d) :=
    (sameCycle_mul_swap_iff G.rot hne).2
      (Or.inr (Or.inl ⟨SameCycle.refl _ _, SameCycle.refl _ _⟩))
  have P : ∀ z, G.Reach x z → ∃ y' : (({d, G.inv d} : Set H)ᶜ : Set H),
      (G.contractEdge d hleg).Reach x y' ∧ (G.rot * swap d (G.inv d)).SameCycle z y' := by
    intro z h
    induction h with
    | refl => exact ⟨x, RotationSystem.Reach.refl _, SameCycle.refl _ _⟩
    | @rot e _ ih =>
      obtain ⟨y', hy', he'⟩ := ih
      exact ⟨y', hy', (hτσ _ _ (sameCycle_apply_right.2 (SameCycle.refl _ _))).symm.trans he'⟩
    | @inv e _ ih =>
      obtain ⟨y', hy', he'⟩ := ih
      by_cases heY : e ∈ (({d, G.inv d} : Set H)ᶜ : Set H)
      · have hre : (G.contractEdge d hleg).Reach x ⟨e, heY⟩ := hy'.trans (hτ _ _ he'.symm)
        refine ⟨(G.contractEdge d hleg).inv ⟨e, heY⟩, hre.inv, ?_⟩
        rw [coe_contractEdge_inv hinv]
      · rw [mem_compl_pair_iff, not_and_or, not_not, not_not] at heY
        refine ⟨y', hy', ?_⟩
        rcases heY with rfl | rfl
        · exact hτd.symm.trans he'
        · rw [hinv]
          exact hτd.trans he'
  obtain ⟨y', hy', hyy'⟩ := P y (hG.reach x y)
  exact hy'.trans (hτ _ _ hyy'.symm)

/-- The exterior of the contraction is an orbit of its face permutation. -/
theorem exterior_mem_faceOrbits_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).exterior ∈ (G.contractEdge d hleg).faceOrbits := by
  have := (bijOn_faceOrbits_contractEdge (hleg := hleg) hG he).mapsTo
    (mem_coe.2 hG.exterior_mem_faceOrbits)
  simp only [mem_coe] at this
  rwa [subtype_exterior he] at this

/-- **Contracting an edge gives a plabic graph.** -/
@[cluster_algebras "lem_edge_contraction_plabic"]
theorem IsPlabicGraph.contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).IsPlabicGraph := by
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  refine
    { nonempty := ⟨(G.contractEdge d hleg).leg ⟨0, hG.one_le⟩⟩
      inv_involutive := fun x => Subtype.ext (by
        rw [coe_contractEdge_inv hinv, coe_contractEdge_inv hinv, hinv])
      inv_ne := fun x h => hG.inv_ne x (by
        rw [← coe_contractEdge_inv (hleg := hleg) hinv]
        exact congrArg Subtype.val h)
      transitive := fun x y =>
        (RotationSystem.reach_iff_exists_mem_closure _).1 (reach_contractEdge hG he x y)
      inv_mem_bdry := fun x hx => by
        rw [mem_contractEdge_bdry] at hx ⊢
        rw [coe_contractEdge_inv hinv]
        exact hG.inv_mem_bdry _ hx
      euler := by
        rw [card_vertices_contractEdge (hleg := hleg) hG he,
          card_edges_contractEdge (hleg := hleg) hinv,
          card_faceOrbits_contractEdge (hleg := hleg) hG he]
        linarith [hG.euler]
      boundaryVertex_card := fun v hv => by
        obtain ⟨hvV, hvB⟩ := (DiskMap.mem_boundaryVertices _).1 hv
        obtain ⟨x, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
        rw [isBoundaryVertex_vertexOf_contractEdge_iff he] at hvB
        have hx := he.notMem_of_isBoundaryVertex hvB
        have hmap := map_vertexOf_contractEdge_of_notMem (hleg := hleg) hne hx
        obtain ⟨h3, h2⟩ := hG.boundaryVertex_card _ (G.vertexOf_mem_boundaryVertices.2 hvB)
        refine ⟨by rw [← h3, ← hmap, card_map], ?_⟩
        rw [← h2, ← hmap, filter_map, card_map]
        congr 1
        ext a
        simp
      exists_orbit := by
        refine ⟨_, exterior_mem_faceOrbits_contractEdge hG he, DiskMap.exterior_subset_bdry _,
          ?_, ?_⟩
        · apply map_injective (Embedding.subtype _)
          rw [map_union, map_map_contractEdge_inv hinv, map_exterior_contractEdge he,
            map_contractEdge_bdry he]
          exact hG.exterior_union_map_inv
        · rw [← disjoint_map (Embedding.subtype _), map_map_contractEdge_inv hinv,
            map_exterior_contractEdge he]
          exact hG.disjoint_exterior_map_inv
      one_le := hG.one_le
      colour_rot := fun x hx => by
        simp only [contractEdge_colour]
        by_cases hxu : (x : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
        · have hr : ((G.contractEdge d hleg).rot x : H) ∈ G.mergedVertex d := by
            rw [← map_vertexOf_contractEdge_of_mem (hleg := hleg) hne hxu]
            exact mem_map_of_mem _ (RotationSystem.rot_mem_vertexOf _ _)
          rw [colour_eq_of_mem_union hG he (mem_union.2 (mem_mergedVertex.1 hr).1),
            colour_eq_of_mem_union hG he hxu]
        · rw [isBoundaryVertex_vertexOf_contractEdge_iff he] at hx
          rw [coe_contractEdge_rot_of_mem (mem_compl_pair_of_notMem (rot_notMem_of_notMem hxu))]
          exact hG.colour_rot _ hx
      leg_notMem_bdry := fun i => by
        rw [mem_contractEdge_bdry, coe_contractEdge_leg]
        exact hG.leg_notMem_bdry i
      bvertex_mem := fun i => (DiskMap.mem_boundaryVertices _).2
        ⟨RotationSystem.vertexOf_mem_vertices _ _, by
          rw [PlabicData.bvertex, isBoundaryVertex_vertexOf_contractEdge_iff he]
          exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)⟩
      bvertex_injective := fun i j h => hG.bvertex_injective (by
        rw [← map_bvertex_contractEdge (hleg := hleg) hG he i,
          ← map_bvertex_contractEdge (hleg := hleg) hG he j, h])
      exists_bvertex_eq := fun v hv => by
        obtain ⟨hvV, hvB⟩ := (DiskMap.mem_boundaryVertices _).1 hv
        obtain ⟨x, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
        rw [isBoundaryVertex_vertexOf_contractEdge_iff he] at hvB
        have hx := he.notMem_of_isBoundaryVertex hvB
        obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hvB)
        refine ⟨i, map_injective (Embedding.subtype _) ?_⟩
        rw [map_bvertex_contractEdge hG he, map_vertexOf_contractEdge_of_notMem hne hx, hi]
      exists_exterior := fun i => by
        obtain ⟨e, heE, he1, he2⟩ := hG.exists_exterior i
        refine ⟨⟨e, he.mem_of_mem_bdry (G.exterior_subset_bdry heE)⟩, ?_, ?_, ?_⟩
        · rwa [← mem_map' (Embedding.subtype _), map_exterior_contractEdge he]
        · rwa [← mem_map' (Embedding.subtype _), map_bvertex_contractEdge hG he]
        · rwa [← mem_map' (Embedding.subtype _), map_bvertex_contractEdge hG he,
            Embedding.coe_subtype, coe_contractEdge_inv hinv] }

/-- The contraction has the same boundary vertices as `G`. -/
@[cluster_algebras "lem_edge_contraction_plabic"]
theorem image_boundaryVertices_contractEdge (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).boundaryVertices.image (Finset.map (Embedding.subtype _)) =
      G.boundaryVertices := by
  have hne := he.not_sameCycle
  ext v
  simp only [mem_image, DiskMap.mem_boundaryVertices]
  constructor
  · rintro ⟨_, ⟨hvV, hvB⟩, rfl⟩
    obtain ⟨x, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
    rw [isBoundaryVertex_vertexOf_contractEdge_iff he] at hvB
    rw [map_vertexOf_contractEdge_of_notMem hne (he.notMem_of_isBoundaryVertex hvB)]
    exact ⟨G.vertexOf_mem_vertices _, hvB⟩
  · rintro ⟨hvV, hvB⟩
    obtain ⟨z, rfl⟩ := (RotationSystem.mem_vertices _).1 hvV
    have hz := he.notMem_of_isBoundaryVertex hvB
    refine ⟨(G.contractEdge d hleg).vertexOf ⟨z, mem_compl_pair_of_notMem hz⟩,
      ⟨RotationSystem.vertexOf_mem_vertices _ _, ?_⟩, map_vertexOf_contractEdge_of_notMem hne hz⟩
    rwa [isBoundaryVertex_vertexOf_contractEdge_iff he]

/-- The contraction has as many faces as `G`. -/
@[cluster_algebras "lem_edge_contraction_plabic"]
theorem card_faces_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).faces.card = G.faces.card := by
  rw [DiskMap.faces, DiskMap.faces, card_erase_of_mem (exterior_mem_faceOrbits_contractEdge hG he),
    card_erase_of_mem hG.exterior_mem_faceOrbits, card_faceOrbits_contractEdge hG he]

/-- The contraction has as many internal faces as `G`. -/
@[cluster_algebras "lem_edge_contraction_plabic"]
theorem card_internalFaces_contractEdge (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d) :
    (G.contractEdge d hleg).internalFaces.card = G.internalFaces.card := by
  have hb := bijOn_faceOrbits_contractEdge (hleg := hleg) hG he
  have hext := subtype_exterior (hleg := hleg) he
  symm
  refine card_nbij (fun f : Finset H => f.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H)))
    (fun f hf => ?_) (fun f hf f' hf' h => ?_) (fun g hg => ?_)
  · obtain ⟨⟨hfe, hfΦ⟩, hfB⟩ := by simpa only [mem_coe, DiskMap.mem_internalFaces,
      DiskMap.mem_faces] using hf
    simp only [mem_coe, DiskMap.mem_internalFaces, DiskMap.mem_faces]
    refine ⟨⟨fun h => hfe ?_, mem_coe.1 (hb.mapsTo (mem_coe.2 hfΦ))⟩, ?_⟩
    · rw [← hext] at h
      exact hb.injOn (mem_coe.2 hfΦ) (mem_coe.2 hG.exterior_mem_faceOrbits) h
    · exact disjoint_left.2 fun a ha haB =>
        disjoint_left.1 hfB (mem_subtype.1 ha) (mem_contractEdge_bdry.1 haB)
  · have hfΦ : f ∈ G.faceOrbits :=
      (DiskMap.mem_faces _).1 ((DiskMap.mem_internalFaces _).1 hf).1 |>.2
    have hfΦ' : f' ∈ G.faceOrbits :=
      (DiskMap.mem_faces _).1 ((DiskMap.mem_internalFaces _).1 hf').1 |>.2
    exact hb.injOn (mem_coe.2 hfΦ) (mem_coe.2 hfΦ') h
  · obtain ⟨⟨hge, hgΦ⟩, hgB⟩ := by simpa only [mem_coe, DiskMap.mem_internalFaces,
      DiskMap.mem_faces] using hg
    obtain ⟨f, hf, rfl⟩ := hb.surjOn (mem_coe.2 hgΦ)
    beta_reduce at hge hgB
    refine ⟨f, ?_, rfl⟩
    simp only [mem_coe, DiskMap.mem_internalFaces, DiskMap.mem_faces]
    refine ⟨⟨fun h => hge (by rw [h, hext]), mem_coe.1 hf⟩, ?_⟩
    rw [disjoint_left]
    intro x hx hxB
    exact disjoint_left.1 hgB
      (show (⟨x, he.mem_of_mem_bdry hxB⟩ : (({d, G.inv d} : Set H)ᶜ : Set H)) ∈ _ from
        mem_subtype.2 hx) (mem_contractEdge_bdry.2 hxB)

end Plabic

/-! ### The rotation at the merged vertex -/

section MergedRotation

omit [Fintype H] in
/-- If a permutation acts on a duplicate-free list `d :: l` as `List.formPerm`, it moves each entry
of `l` to the next, the last entry of `l` to `d`, and `d` to the first entry of `l`. -/
private theorem cycle_facts {σ : Perm H} {d : H} {l : List H} (hl : (d :: l).Nodup)
    (hσ : ∀ x ∈ d :: l, σ x = (d :: l).formPerm x) :
    (∀ j (hj : j + 1 < l.length), σ l[j] = l[j + 1]) ∧
    (∀ h : 0 < l.length, σ l[l.length - 1] = d) ∧
    (∀ h : 0 < l.length, σ d = l[0]) ∧ (l = [] → σ d = d) := by
  refine ⟨fun j hj => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hσ _ (List.mem_cons_of_mem _ (List.getElem_mem _))]
    have := List.formPerm_apply_lt_getElem (d :: l) hl (j + 1) (by simp; omega)
    simpa using this
  · rw [hσ _ (List.mem_cons_of_mem _ (List.getElem_mem _))]
    have := List.formPerm_apply_getLast d l
    have hne : l ≠ [] := List.ne_nil_of_length_pos h
    rwa [List.getLast_cons hne, List.getLast_eq_getElem] at this
  · rw [hσ _ List.mem_cons_self]
    obtain ⟨y, l', rfl⟩ := List.exists_cons_of_length_pos h
    simpa using List.formPerm_apply_head d y l' hl
  · subst h
    rw [hσ _ List.mem_cons_self]
    simp

omit [Fintype H] in
private theorem formPerm_getElem_last {L : List H} (hL : L.Nodup) (h : 0 < L.length) :
    L.formPerm L[L.length - 1] = L[0] := by
  rw [List.formPerm_apply_getElem _ hL]
  congr 1
  rw [Nat.sub_add_cancel h, Nat.mod_self]

omit [Fintype H] in
/-- The cycle `(a₁ … a_p b₁ … b_q)` of a duplicate-free list `la ++ lb`. -/
private theorem formPerm_append_facts {la lb : List H} (hL : (la ++ lb).Nodup) :
    (∀ k (hk : k + 1 < la.length), (la ++ lb).formPerm la[k] = la[k + 1]) ∧
    (∀ (ha : 0 < la.length) (hb : 0 < lb.length),
      (la ++ lb).formPerm la[la.length - 1] = lb[0]) ∧
    (∀ (ha : 0 < la.length), lb = [] → (la ++ lb).formPerm la[la.length - 1] = la[0]) ∧
    (∀ k (hk : k + 1 < lb.length), (la ++ lb).formPerm lb[k] = lb[k + 1]) ∧
    (∀ (hb : 0 < lb.length) (ha : 0 < la.length),
      (la ++ lb).formPerm lb[lb.length - 1] = la[0]) ∧
    (∀ (hb : 0 < lb.length), la = [] → (la ++ lb).formPerm lb[lb.length - 1] = lb[0]) := by
  refine ⟨fun k hk => ?_, fun ha hb => ?_, fun ha hlb => ?_, fun k hk => ?_, fun hb ha => ?_,
    fun hb hla => ?_⟩
  · have := List.formPerm_apply_lt_getElem (la ++ lb) hL k (by simp; omega)
    rwa [List.getElem_append_left (by omega), List.getElem_append_left (by omega)] at this
  · have := List.formPerm_apply_lt_getElem (la ++ lb) hL (la.length - 1) (by simp; omega)
    rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)] at this
    simpa [Nat.sub_add_cancel ha] using this
  · subst hlb
    simp only [List.append_nil] at hL ⊢
    exact formPerm_getElem_last hL ha
  · have := List.formPerm_apply_lt_getElem (la ++ lb) hL (la.length + k) (by simp; omega)
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)] at this
    have e1 : la.length + k + 1 - la.length = k + 1 := by omega
    simpa [e1] using this
  · have := formPerm_getElem_last hL (by simp; omega)
    rw [List.getElem_append_left ha, List.getElem_append_right (by simp; omega)] at this
    have e1 : la.length + lb.length - 1 - la.length = lb.length - 1 := by omega
    simpa [e1] using this
  · subst hla
    simp only [List.nil_append] at hL ⊢
    exact formPerm_getElem_last hL hb

/-- If the rotation at `v(e)` is the cycle `(e l₀ l₁ …)` of a duplicate-free list `e :: l`, the
vertex `v(e)` is the set of entries of the list. -/
theorem vertexOf_eq_toFinset_of_formPerm {e : H} {l : List H} (hl : (e :: l).Nodup)
    (h : ∀ x ∈ e :: l, G.rot x = (e :: l).formPerm x) : G.vertexOf e = (e :: l).toFinset := by
  have hpow : ∀ n : ℕ, (G.rot ^ n) e = ((e :: l).formPerm ^ n) e ∧ (G.rot ^ n) e ∈ e :: l := by
    intro n
    induction n with
    | zero => exact ⟨rfl, List.mem_cons_self⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [h1] at h2
      rw [pow_succ_apply', pow_succ_apply', h1, h _ h2]
      exact ⟨rfl, List.formPerm_apply_mem_of_mem h2⟩
  ext x
  rw [RotationSystem.mem_vertexOf, List.mem_toFinset]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨n, rfl⟩ := hx.exists_nat_pow_eq
    exact (hpow n).2
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have h' := List.formPerm_pow_apply_getElem (e :: l) hl i 0 (by simp)
    simp only [zero_add, Nat.mod_eq_of_lt hi] at h'
    rw [← h', List.getElem_cons_zero, ← (hpow i).1]
    exact sameCycle_pow_apply_self _ _ _

variable {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- For rotation cycles `d :: la` at `v(d)` and `d̄ :: lb` at `v(d̄)` along a contractible edge,
`la ++ lb` is duplicate-free and avoids `{d, d̄}`. -/
theorem nodup_append_and_mem_compl_pair (he : G.IsContractibleEdge d) {la lb : List H}
    (ha : (d :: la).Nodup) (hσa : ∀ x ∈ d :: la, G.rot x = (d :: la).formPerm x)
    (hb : (G.inv d :: lb).Nodup)
    (hσb : ∀ x ∈ G.inv d :: lb, G.rot x = (G.inv d :: lb).formPerm x) :
    (la ++ lb).Nodup ∧ ∀ y ∈ la ++ lb, y ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
  have hu := G.vertexOf_eq_toFinset_of_formPerm ha hσa
  have hw := G.vertexOf_eq_toFinset_of_formPerm hb hσb
  obtain ⟨hdla, hla⟩ := List.nodup_cons.1 ha
  obtain ⟨hdlb, hlb⟩ := List.nodup_cons.1 hb
  have hmu : ∀ x ∈ la, x ∈ G.vertexOf d := fun x hx => by
    rw [hu, List.mem_toFinset]
    exact List.mem_cons_of_mem _ hx
  have hmw : ∀ x ∈ lb, x ∈ G.vertexOf (G.inv d) := fun x hx => by
    rw [hw, List.mem_toFinset]
    exact List.mem_cons_of_mem _ hx
  have hdisj : ∀ x ∈ G.vertexOf d, x ∉ G.vertexOf (G.inv d) := fun x h1 h2 =>
    he.vertexOf_ne ((G.vertexOf_eq_of_mem h1).symm.trans (G.vertexOf_eq_of_mem h2))
  have hd'la : G.inv d ∉ la := fun h => hdisj _ (hmu _ h) (G.self_mem_vertexOf _)
  have hdlb' : d ∉ lb := fun h => hdisj _ (G.self_mem_vertexOf _) (hmw _ h)
  refine ⟨List.nodup_append.2
    ⟨hla, hlb, fun a ha' b hb' hab => hdisj _ (hmu _ ha') (hab ▸ hmw _ hb')⟩, fun y hy => ?_⟩
  rcases List.mem_append.1 hy with hy | hy
  · exact mem_compl_pair_iff.2 ⟨fun h => hdla (h ▸ hy), fun h => hd'la (h ▸ hy)⟩
  · exact mem_compl_pair_iff.2 ⟨fun h => hdlb' (h ▸ hy), fun h => hdlb (h ▸ hy)⟩

/-- For rotation cycles `d :: la` at `v(d)` and `d̄ :: lb` at `v(d̄)` along a contractible edge,
the merged vertex consists of the darts of `la ++ lb`. -/
theorem mergedVertex_eq_toFinset_append (he : G.IsContractibleEdge d) {la lb : List H}
    (ha : (d :: la).Nodup) (hσa : ∀ x ∈ d :: la, G.rot x = (d :: la).formPerm x)
    (hb : (G.inv d :: lb).Nodup)
    (hσb : ∀ x ∈ G.inv d :: lb, G.rot x = (G.inv d :: lb).formPerm x) :
    G.mergedVertex d = (la ++ lb).toFinset := by
  have hY := (nodup_append_and_mem_compl_pair he ha hσa hb hσb).2
  ext y
  rw [mem_mergedVertex, G.vertexOf_eq_toFinset_of_formPerm ha hσa,
    G.vertexOf_eq_toFinset_of_formPerm hb hσb]
  simp only [List.toFinset_cons, mem_insert, List.mem_toFinset, List.mem_append]
  constructor
  · rintro ⟨(h | h) | (h | h), h1, h2⟩
    exacts [absurd h h1, Or.inl h, absurd h h2, Or.inr h]
  · rintro (h | h)
    · exact ⟨Or.inl (Or.inr h), mem_compl_pair_iff.1 (hY _ (List.mem_append_left _ h))⟩
    · exact ⟨Or.inr (Or.inr h), mem_compl_pair_iff.1 (hY _ (List.mem_append_right _ h))⟩

/-- For rotation cycles `d :: la` at `v(d)` and `d̄ :: lb` at `v(d̄)` along a contractible edge,
the rotation of the contraction acts on `la ++ lb` as its `List.formPerm`. -/
theorem coe_contractEdge_rot_eq_formPerm_append (he : G.IsContractibleEdge d) {la lb : List H}
    (ha : (d :: la).Nodup) (hσa : ∀ x ∈ d :: la, G.rot x = (d :: la).formPerm x)
    (hb : (G.inv d :: lb).Nodup)
    (hσb : ∀ x ∈ G.inv d :: lb, G.rot x = (G.inv d :: lb).formPerm x)
    {x : (({d, G.inv d} : Set H)ᶜ : Set H)} (hx : (x : H) ∈ la ++ lb) :
    ((G.contractEdge d hleg).rot x : H) = (la ++ lb).formPerm x := by
  obtain ⟨hnd, hY⟩ := nodup_append_and_mem_compl_pair he ha hσa hb hσb
  have hYa : ∀ y ∈ la, y ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := fun y hy =>
    hY y (List.mem_append_left _ hy)
  have hYb : ∀ y ∈ lb, y ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := fun y hy =>
    hY y (List.mem_append_right _ hy)
  obtain ⟨hA1, hA2, hA3, hA4⟩ := cycle_facts ha hσa
  obtain ⟨hB1, hB2, hB3, hB4⟩ := cycle_facts hb hσb
  obtain ⟨F1, F2, F3, F4, F5, F6⟩ := formPerm_append_facts hnd
  rcases List.mem_append.1 hx with hxa | hxb
  · obtain ⟨k, hk, hxk⟩ := List.mem_iff_getElem.1 hxa
    rcases Nat.lt_or_ge (k + 1) la.length with hk1 | hk1
    · have hσx : G.rot x = la[k + 1] := by rw [← hxk, hA1 k hk1]
      rw [coe_contractEdge_rot_of_mem (by rw [hσx]; exact hYa _ (List.getElem_mem _)), hσx,
        ← hxk, F1 k hk1]
    · obtain rfl : k = la.length - 1 := by omega
      have hσx : G.rot x = d := by rw [← hxk, hA2 (by omega)]
      rcases Nat.eq_zero_or_pos lb.length with hq0 | hq0
      · have hσd := hA3 (by omega)
        rw [coe_contractEdge_rot_of_eq_of_eq hσx (hB4 (List.eq_nil_of_length_eq_zero hq0))
          (by rw [hσd]; exact hYa _ (List.getElem_mem _)), hσd, ← hxk,
          F3 (by omega) (List.eq_nil_of_length_eq_zero hq0)]
      · have hσd' := hB3 hq0
        rw [coe_contractEdge_rot_of_eq hσx (by rw [hσd']; exact hYb _ (List.getElem_mem _)),
          hσd', ← hxk, F2 (by omega) hq0]
  · obtain ⟨k, hk, hxk⟩ := List.mem_iff_getElem.1 hxb
    rcases Nat.lt_or_ge (k + 1) lb.length with hk1 | hk1
    · have hσx : G.rot x = lb[k + 1] := by rw [← hxk, hB1 k hk1]
      rw [coe_contractEdge_rot_of_mem (by rw [hσx]; exact hYb _ (List.getElem_mem _)), hσx,
        ← hxk, F4 k hk1]
    · obtain rfl : k = lb.length - 1 := by omega
      have hσx : G.rot x = G.inv d := by rw [← hxk, hB2 (by omega)]
      rcases Nat.eq_zero_or_pos la.length with hp0 | hp0
      · have hσd' := hB3 (by omega)
        rw [coe_contractEdge_rot_of_eq_inv_of_eq hσx (hA4 (List.eq_nil_of_length_eq_zero hp0))
          (by rw [hσd']; exact hYb _ (List.getElem_mem _)), hσd', ← hxk,
          F6 (by omega) (List.eq_nil_of_length_eq_zero hp0)]
      · have hσd := hA3 hp0
        rw [coe_contractEdge_rot_of_eq_inv hσx (by rw [hσd]; exact hYa _ (List.getElem_mem _)),
          hσd, ← hxk, F5 (by omega) hp0]

/-- **The rotation at a merged vertex.** Let the rotations at `v(d)` and `v(d̄)` be the cycles
`(d a₁ … a_p)` and `(d̄ b₁ … b_q)`, given as duplicate-free lists `d :: la` and `d̄ :: lb` on which
`σ` acts as `List.formPerm`. Then `p + q ≥ 1`, and in the contraction along `{d, d̄}` the darts
`a₁, …, a_p, b₁, …, b_q` are distinct and form one vertex, on which the rotation is the cycle
`(a₁ … a_p b₁ … b_q)`. -/
@[cluster_algebras "lem_contraction_merged_rotation"]
theorem contractEdge_mergedVertex_rotation (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
    {la lb : List H} (ha : (d :: la).Nodup) (hσa : ∀ x ∈ d :: la, G.rot x = (d :: la).formPerm x)
    (hb : (G.inv d :: lb).Nodup)
    (hσb : ∀ x ∈ G.inv d :: lb, G.rot x = (G.inv d :: lb).formPerm x) :
    1 ≤ la.length + lb.length ∧ (la ++ lb).Nodup ∧
      ∀ x : (({d, G.inv d} : Set H)ᶜ : Set H), (x : H) ∈ la ++ lb →
        ((G.contractEdge d hleg).vertexOf x).map (Embedding.subtype _) = (la ++ lb).toFinset ∧
        ((G.contractEdge d hleg).rot x : H) = (la ++ lb).formPerm x := by
  have hU := mergedVertex_eq_toFinset_append he ha hσa hb hσb
  refine ⟨?_, (nodup_append_and_mem_compl_pair he ha hσa hb hσb).1, fun x hx =>
    ⟨?_, coe_contractEdge_rot_eq_formPerm_append he ha hσa hb hσb hx⟩⟩
  · obtain ⟨y, hy⟩ := mergedVertex_nonempty hG he
    rw [hU, List.mem_toFinset, List.mem_append] at hy
    rcases hy with hy | hy <;> (have := List.length_pos_of_mem hy; omega)
  · rw [← hU]
    refine map_vertexOf_contractEdge_of_mem he.not_sameCycle ?_
    rw [G.vertexOf_eq_toFinset_of_formPerm ha hσa, G.vertexOf_eq_toFinset_of_formPerm hb hσb]
    rcases List.mem_append.1 hx with h | h
    · exact mem_union_left _ (List.mem_toFinset.2 (List.mem_cons_of_mem _ h))
    · exact mem_union_right _ (List.mem_toFinset.2 (List.mem_cons_of_mem _ h))

end MergedRotation

end PlabicData

end ClusterAlgebras
