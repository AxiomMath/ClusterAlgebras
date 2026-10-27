/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap
public import ClusterAlgebras.Plabic.FirstReturn

/-!
# The core and the skeleton of a plabic graph

The local moves (M2) and (M3) may create internal leaves and bivalent vertices. The *core* of a
plabic graph discards the trees hanging off the rest of the graph: a set `S` of darts is
*core-like* if it contains the boundary arcs `B`, is closed under `d ↦ d̄`, and meets every vertex
in no dart or in at least two darts; the core `K(G)` is the union of all core-like sets, and is
itself core-like. A plabic graph is *anchored* if all of its legs lie in the core.

An internal leaf `u = {ℓ}` whose neighbour `v(ℓ̄)` is internal can be deleted: the darts `ℓ, ℓ̄`
are removed and the rotation is the rotation induced off the edge `{ℓ, ℓ̄}`. The result is again a
plabic graph, with the vertices of `G` other than `u` and `v(ℓ̄)` together with `v(ℓ̄) \ {ℓ̄}`.

The *skeleton* `Γ(G)` keeps, of the core, the darts at boundary vertices and at vertices with at
least three core darts, and walks through the vertices with exactly two core darts. A plabic
graph whose internal vertices all have at least three darts is its own skeleton.

## Main definitions

* `ClusterAlgebras.DiskMap.IsCoreLike`, `ClusterAlgebras.DiskMap.core`: core-like sets and the
  core.
* `ClusterAlgebras.PlabicData.IsAnchored`: anchored plabic graphs.
* `ClusterAlgebras.PlabicData.leafDeletion`: the deletion of an internal leaf.
* `ClusterAlgebras.PlabicData.skeleton`: the skeleton of a plabic graph.

## Main results

* `ClusterAlgebras.DiskMap.IsDiskMap.isCoreLike_core`: the core is core-like.
* `ClusterAlgebras.PlabicData.isPlabicGraph_leafDeletion`,
  `ClusterAlgebras.PlabicData.vertices_leafDeletion`,
  `ClusterAlgebras.PlabicData.bvertex_leafDeletion`: deleting an internal leaf gives a plabic
  graph with the same boundary vertices and legs.
* `ClusterAlgebras.PlabicData.involutive_skeletonInvFun`: the walk through the vertices with two
  core darts defines an involution `d ↦ d̄^Γ` of `R`.
* `ClusterAlgebras.PlabicData.map_skeleton_vertexOf`,
  `ClusterAlgebras.PlabicData.map_skeleton_bvertex`: the vertices of `Γ(G)` are the sets `v ∩ R`,
  and `β_Γ(i) = β(i) ∩ R`.
* `ClusterAlgebras.PlabicData.skeleton_of_thick`: a plabic graph without small internal vertices
  is its own skeleton; `PlabicData.skeletonIsoOfThick` is the corresponding isomorphism
  `Γ(G) → G`.

## Implementation notes

* Sets of darts are `Finset`s of the dart type; when a set of darts becomes the dart type of a new
  graph (the deletion of a leaf, the skeleton), it is the subtype of the corresponding `Set`, the
  form taken by first-return maps.
* The deletion of a leaf and the skeleton are defined for a plabic graph, as in FWZ: the
  deletion needs the legs to avoid `ℓ, ℓ̄`, and the skeleton needs `d ↦ d̄` to be an involution,
  so that `d ↦ d̄^Γ` is a permutation, and a dart of `β(i) ∩ R` to record `β_Γ(i)`. The core,
  `R`, `σ_K` and the walks are defined for arbitrary data.
* The colouring is a function on darts (see `ClusterAlgebras.PlabicData`). The colour `κ'` of the
  deletion of a leaf gives the darts of `v(ℓ̄) \ {ℓ̄}` the colour of `ℓ̄` and keeps the colour of
  every other dart; the colour of the skeleton is the restriction of the colour of `G`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

/-! ### The core -/

namespace DiskMap

variable {H : Type*} [Fintype H] [DecidableEq H] (M : DiskMap H)

/-- A set `S` of darts is **core-like** if it contains `B`, is closed under `d ↦ d̄`, and every
vertex containing a dart of `S` contains at least two darts of `S`. -/
@[cluster_algebras "def_plabic_core"]
structure IsCoreLike (S : Finset H) : Prop where
  /-- `B ⊆ S`. -/
  bdry_subset : M.bdry ⊆ S
  /-- `S` is closed under `d ↦ d̄`. -/
  inv_mem : ∀ d ∈ S, M.inv d ∈ S
  /-- A vertex meeting `S` contains at least two darts of `S`. -/
  two_le_card : ∀ v ∈ M.vertices, (∃ d ∈ v, d ∈ S) → 2 ≤ #(v ∩ S)

/-- Core-likeness of a set of darts is decidable. -/
instance : DecidablePred M.IsCoreLike := fun S =>
  decidable_of_iff (M.bdry ⊆ S ∧ (∀ d ∈ S, M.inv d ∈ S) ∧
      ∀ v ∈ M.vertices, (∃ d ∈ v, d ∈ S) → 2 ≤ #(v ∩ S))
    ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- The **core** `K(G)`: the union of all core-like sets of darts. -/
@[cluster_algebras "def_plabic_core"]
def core : Finset H := (univ.filter M.IsCoreLike).sup id

variable {M}

/-- A dart lies in the core iff it lies in some core-like set. -/
theorem mem_core {d : H} : d ∈ M.core ↔ ∃ S, M.IsCoreLike S ∧ d ∈ S := by
  simp [core, mem_sup]

/-- A core-like set lies in the core. -/
theorem IsCoreLike.subset_core {S : Finset H} (h : M.IsCoreLike S) : S ⊆ M.core :=
  fun _ hd => mem_core.2 ⟨S, h, hd⟩

/-- The vertex of a dart of a core-like set `S` contains at least two darts of `S`. -/
theorem IsCoreLike.two_le_card_vertexOf {S : Finset H} (h : M.IsCoreLike S) {d : H}
    (hd : d ∈ S) : 2 ≤ #(M.vertexOf d ∩ S) :=
  h.two_le_card _ (M.vertexOf_mem_vertices d) ⟨d, M.self_mem_vertexOf d, hd⟩

/-- The core is closed under `d ↦ d̄`; this needs no hypothesis on `M`. -/
theorem inv_mem_core {d : H} (hd : d ∈ M.core) : M.inv d ∈ M.core := by
  obtain ⟨S, hS, hdS⟩ := mem_core.1 hd
  exact hS.subset_core (hS.inv_mem d hdS)

/-- The vertex of a dart of the core contains at least two darts of the core; this needs no
hypothesis on `M`. -/
theorem two_le_card_vertexOf_inter_core {d : H} (hd : d ∈ M.core) :
    2 ≤ #(M.vertexOf d ∩ M.core) := by
  obtain ⟨S, hS, hdS⟩ := mem_core.1 hd
  exact (hS.two_le_card_vertexOf hdS).trans
    (card_le_card (inter_subset_inter_left hS.subset_core))

namespace IsDiskMap

variable (hM : M.IsDiskMap)

include hM

/-- In a disk map, `B` is core-like. -/
theorem isCoreLike_bdry : M.IsCoreLike M.bdry where
  bdry_subset := Subset.refl _
  inv_mem := hM.inv_mem_bdry
  two_le_card v hv hvB := by
    rw [← filter_mem_eq_inter, (hM.boundaryVertex_card v (M.mem_boundaryVertices.2 ⟨hv, hvB⟩)).2]

/-- In a disk map, `B` lies in the core. -/
theorem bdry_subset_core : M.bdry ⊆ M.core :=
  hM.isCoreLike_bdry.subset_core

/-- **The core is core-like**: in a disk map (in particular in a plabic graph), `B ⊆ K(G)`, `K(G)`
is closed under `d ↦ d̄`, and every vertex containing a dart of `K(G)` contains at least two darts
of `K(G)`. -/
@[cluster_algebras "lem_plabic_core_closed"]
theorem isCoreLike_core : M.IsCoreLike M.core where
  bdry_subset := hM.bdry_subset_core
  inv_mem _ := inv_mem_core
  two_le_card v hv := by
    rintro ⟨d, hdv, hd⟩
    obtain ⟨e, rfl⟩ := M.mem_vertices.1 hv
    rw [← M.vertexOf_eq_of_mem hdv]
    exact two_le_card_vertexOf_inter_core hd

/-- If every internal vertex of a disk map has at least two darts, every dart lies in the core. -/
theorem core_eq_univ (h : ∀ v ∈ M.internalVertices, 2 ≤ #v) : M.core = univ := by
  refine eq_univ_of_forall fun d => (?_ : M.IsCoreLike univ).subset_core (mem_univ d)
  refine ⟨subset_univ _, fun _ _ => mem_univ _, fun v hv _ => ?_⟩
  rw [inter_univ]
  by_cases hb : M.IsBoundaryVertex v
  · rw [(hM.boundaryVertex_card v (M.mem_boundaryVertices.2 ⟨hv, hb⟩)).1]
    omega
  · exact h v (M.mem_internalVertices.2 ⟨hv, hb⟩)

end IsDiskMap

end DiskMap

/-! ### Anchored plabic graphs -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- A plabic graph is **anchored** if every leg `g_i` lies in the core `K(G)`. -/
@[cluster_algebras "def_anchored"]
def IsAnchored : Prop := ∀ i, G.leg i ∈ G.core

variable {G}

/-- A plabic graph whose internal vertices all have at least two darts is anchored. -/
theorem IsPlabicGraph.isAnchored (hG : G.IsPlabicGraph)
    (h : ∀ v ∈ G.internalVertices, 2 ≤ #v) : G.IsAnchored := fun i => by
  rw [hG.core_eq_univ h]
  exact mem_univ _

/-! ### Deleting an internal leaf -/

section LeafDeletion

variable {ℓ : H}

/-- A leg of a plabic graph is neither the dart `ℓ` of an internal leaf nor its reverse `ℓ̄`, when
`v(ℓ̄)` is internal. -/
theorem leg_mem_compl_pair (hG : G.IsPlabicGraph) (hu : G.IsInternalLeaf (G.vertexOf ℓ))
    (hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices) (i : Fin b) :
    G.leg i ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) := by
  have hb := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact G.vertexOf_mem_internalVertices.1 hu.1 (h ▸ hb)
  · exact G.vertexOf_mem_internalVertices.1 hv (h ▸ hb)

variable (G) in
/-- The **deletion of an internal leaf**. Let `u = v(ℓ)` be an internal leaf of the plabic graph
`G` with dart `ℓ`, such that `v(ℓ̄)` is internal. The deletion of `u` has the darts
`H' = H \ {ℓ, ℓ̄}`, the restriction of `d ↦ d̄`, the rotation `σ'` induced on `H'` by `d ↦ d̄`, `σ`
and `ℓ` (`ClusterAlgebras.inducedRotationPerm`), the same `B` and the same legs; the darts of
`v(ℓ̄) \ {ℓ̄}` get the colour of `v(ℓ̄)` and every other dart keeps its colour. -/
@[cluster_algebras "def_leaf_deletion"]
noncomputable def leafDeletion (hG : G.IsPlabicGraph) (hu : G.IsInternalLeaf (G.vertexOf ℓ))
    (hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices) :
    PlabicData (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) b where
  inv := G.inv.subtypePerm (apply_mem_compl_pair_iff hG.inv_involutive ℓ)
  rot := inducedRotationPerm G.inv G.rot ℓ
  bdry := univ.filter fun x => (x : H) ∈ G.bdry
  colour x := if (x : H) ∈ G.vertexOf (G.inv ℓ) then G.colour (G.inv ℓ) else G.colour x
  leg i := ⟨G.leg i, leg_mem_compl_pair hG hu hv i⟩

variable (hG : G.IsPlabicGraph) (hu : G.IsInternalLeaf (G.vertexOf ℓ))
  (hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices)

omit [Fintype H] [DecidableEq H] in
private theorem mem_compl_pair_iff {x : H} :
    x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) ↔ x ≠ ℓ ∧ x ≠ G.inv ℓ := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

include hu in
/-- The leaf `u = v(ℓ)` consists of `ℓ` alone. -/
theorem mem_vertexOf_iff_of_isInternalLeaf {x : H} : x ∈ G.vertexOf ℓ ↔ x = ℓ := by
  obtain ⟨a, ha⟩ := card_eq_one.1 hu.2
  have hℓ := G.self_mem_vertexOf ℓ
  rw [ha, mem_singleton] at hℓ ⊢
  rw [hℓ]

include hu in
/-- The rotation fixes the dart of an internal leaf. -/
theorem rot_eq_self_of_isInternalLeaf : G.rot ℓ = ℓ :=
  (mem_vertexOf_iff_of_isInternalLeaf hu).1 (G.rot_mem_vertexOf ℓ)

include hG hu hv in
/-- The vertex `v(ℓ̄)` has at least two darts: `σ(ℓ̄) ≠ ℓ̄`. -/
theorem rot_inv_ne_of_isInternalLeaf : G.rot (G.inv ℓ) ≠ G.inv ℓ := by
  intro h
  have key : ∀ z, G.Reach ℓ z → z = ℓ ∨ z = G.inv ℓ := by
    intro z hz
    induction hz with
    | refl => exact Or.inl rfl
    | rot _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inl (rot_eq_self_of_isInternalLeaf hu)
      · exact Or.inr h
    | inv _ ih =>
      rcases ih with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (hG.inv_involutive _)
  obtain ⟨z, hz, hzB⟩ := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem ⟨0, hG.one_le⟩)
  rcases key z (hG.reach ℓ z) with rfl | rfl
  · exact G.vertexOf_mem_internalVertices.1 hu.1 (G.isBoundaryVertex_vertexOf_of_mem hzB)
  · exact G.vertexOf_mem_internalVertices.1 hv (G.isBoundaryVertex_vertexOf_of_mem hzB)

include hG hu hv in
/-- `σ(ℓ̄)` is a dart of the deletion. -/
theorem rot_inv_mem_compl_pair : G.rot (G.inv ℓ) ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) := by
  refine mem_compl_pair_iff.2 ⟨fun h => ?_, rot_inv_ne_of_isInternalLeaf hG hu hv⟩
  exact hG.inv_ne ℓ (G.rot.injective (h.trans (rot_eq_self_of_isInternalLeaf hu).symm))

include hu hv in
/-- The darts of `B` are darts of the deletion. -/
theorem mem_compl_pair_of_mem_bdry {x : H} (hx : x ∈ G.bdry) :
    x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) := by
  refine mem_compl_pair_iff.2 ⟨fun h => ?_, fun h => ?_⟩
  · exact G.vertexOf_mem_internalVertices.1 hu.1 (h ▸ G.isBoundaryVertex_vertexOf_of_mem hx)
  · exact G.vertexOf_mem_internalVertices.1 hv (h ▸ G.isBoundaryVertex_vertexOf_of_mem hx)

/-- The involution of the deletion is the restriction of `d ↦ d̄`. -/
@[simp]
theorem coe_leafDeletion_inv (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ((G.leafDeletion hG hu hv).inv x : H) = G.inv x :=
  rfl

/-- The legs of the deletion are the legs of `G`. -/
@[simp]
theorem coe_leafDeletion_leg (i : Fin b) : ((G.leafDeletion hG hu hv).leg i : H) = G.leg i :=
  rfl

/-- The boundary arcs of the deletion are the darts of `B`. -/
@[simp]
theorem mem_leafDeletion_bdry {x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)} :
    x ∈ (G.leafDeletion hG hu hv).bdry ↔ (x : H) ∈ G.bdry := by
  simp [leafDeletion]

/-- The colour of a dart of the deletion: the colour of `ℓ̄` on `v(ℓ̄)`, and the colour in `G`
elsewhere. -/
theorem leafDeletion_colour (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    (G.leafDeletion hG hu hv).colour x =
      if (x : H) ∈ G.vertexOf (G.inv ℓ) then G.colour (G.inv ℓ) else G.colour x :=
  rfl

include hu in
private theorem rot_ne_self_of_mem {x : H} (hx : x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    G.rot x ≠ ℓ := by
  intro h
  rw [← rot_eq_self_of_isInternalLeaf hu] at h
  exact (mem_compl_pair_iff.1 hx).1 (G.rot.injective h)

/-- The rotation of the deletion agrees with `σ`, except that it sends `σ⁻¹(ℓ̄)` to `σ(ℓ̄)`. -/
theorem coe_leafDeletion_rot (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ((G.leafDeletion hG hu hv).rot x : H) =
      if G.rot x = G.inv ℓ then G.rot (G.inv ℓ) else G.rot x := by
  have hx := mem_compl_pair_iff.1 x.2
  have hτx : (G.rot * swap ℓ (G.inv ℓ)) x = G.rot x := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 hx.2]
  change (inducedRotation G.inv G.rot ℓ x : H) = _
  unfold inducedRotation
  split_ifs with h
  · set τ := G.rot * swap ℓ (G.inv ℓ) with hτ
    have e1 : (τ ^ 1) x = G.inv ℓ := by rw [pow_one, hτx, h]
    have e2 : (τ ^ 2) x = ℓ := by
      rw [pow_succ', Perm.mul_apply, e1, hτ, Perm.mul_apply, swap_apply_right,
        rot_eq_self_of_isInternalLeaf hu]
    have e3 : (τ ^ 3) x = G.rot (G.inv ℓ) := by
      rw [pow_succ', Perm.mul_apply, e2, hτ, Perm.mul_apply, swap_apply_left]
    refine (coe_firstReturn_of_pow (m := 3) (by norm_num) (e3 ▸ rot_inv_mem_compl_pair hG hu hv)
      fun j hj hj3 => ?_).trans e3
    interval_cases j
    · rw [e1]
      simp
    · rw [e2]
      simp
  · exact (coe_firstReturn_of_apply_mem
      (hτx ▸ mem_compl_pair_iff.2 ⟨rot_ne_self_of_mem hu x.2, h⟩)).trans hτx

include hG hu hv in
/-- The rotation of the deletion is the first-return map of `σ` to `H \ {ℓ, ℓ̄}`. -/
theorem leafDeletion_rot_eq_firstReturnPerm :
    (G.leafDeletion hG hu hv).rot = firstReturnPerm G.rot (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) := by
  refine Equiv.ext fun x => Subtype.ext ?_
  rw [coe_leafDeletion_rot, coe_firstReturnPerm]
  split_ifs with h
  · rw [coe_firstReturn_of_pow (m := 2) (by norm_num)
      (by rw [pow_two, Perm.mul_apply, h]; exact rot_inv_mem_compl_pair hG hu hv)
      (fun j hj hj2 => by interval_cases j; rw [pow_one, h]; simp), pow_two, Perm.mul_apply, h]
  · exact (coe_firstReturn_of_apply_mem
      (mem_compl_pair_iff.2 ⟨rot_ne_self_of_mem hu x.2, h⟩)).symm

include hG hu hv in
/-- Two darts of the deletion lie in one vertex of the deletion iff they lie in one vertex of
`G`. -/
theorem sameCycle_leafDeletion_rot_iff {x y : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)} :
    (G.leafDeletion hG hu hv).rot.SameCycle x y ↔ G.rot.SameCycle x y := by
  rw [leafDeletion_rot_eq_firstReturnPerm hG hu hv, sameCycle_firstReturnPerm_iff]

include hu in
/-- The leaf dart `ℓ` does not lie in the vertex of a dart of the deletion. -/
theorem notMem_vertexOf_of_mem_compl_pair {x : H} (hx : x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ℓ ∉ G.vertexOf x := by
  intro h
  exact (mem_compl_pair_iff.1 hx).1
    ((mem_vertexOf_iff_of_isInternalLeaf hu).1 (G.vertexOf_eq_of_mem h ▸ G.self_mem_vertexOf x))

include hG hu hv in
/-- Each vertex `v'(x)` of the deletion is the vertex `v(x)` of `G` with `ℓ̄` removed. -/
theorem map_vertexOf_leafDeletion (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ((G.leafDeletion hG hu hv).vertexOf x).map (Embedding.subtype _) =
      (G.vertexOf x).erase (G.inv ℓ) := by
  ext z
  simp only [mem_map, Embedding.coe_subtype, mem_erase, RotationSystem.mem_vertexOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(mem_compl_pair_iff.1 y.2).2, (sameCycle_leafDeletion_rot_iff hG hu hv).1 hy⟩
  · rintro ⟨hz, hxz⟩
    have hzℓ : z ≠ ℓ := by
      rintro rfl
      exact notMem_vertexOf_of_mem_compl_pair hu x.2 (G.mem_vertexOf.2 hxz)
    exact ⟨⟨z, mem_compl_pair_iff.2 ⟨hzℓ, hz⟩⟩,
      (sameCycle_leafDeletion_rot_iff hG hu hv).2 hxz, rfl⟩

include hG hu hv in
/-- A dart of the deletion lies in the vertex `v'(x)` of the deletion iff it lies in the vertex
`v(x)` of `G`. -/
theorem mem_leafDeletion_vertexOf_iff {x y : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)} :
    y ∈ (G.leafDeletion hG hu hv).vertexOf x ↔ (y : H) ∈ G.vertexOf x := by
  rw [← Finset.mem_map' (Embedding.subtype _), map_vertexOf_leafDeletion hG hu hv]
  simp only [Embedding.coe_subtype, mem_erase, and_iff_right_iff_imp]
  exact fun _ => (mem_compl_pair_iff.1 y.2).2

include hG hu hv in
/-- A vertex of the deletion is a boundary vertex iff the corresponding vertex of `G` is. -/
theorem isBoundaryVertex_vertexOf_leafDeletion_iff (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    (G.leafDeletion hG hu hv).IsBoundaryVertex ((G.leafDeletion hG hu hv).vertexOf x) ↔
      G.IsBoundaryVertex (G.vertexOf x) := by
  constructor
  · rintro ⟨y, hy, hyB⟩
    exact ⟨y, (mem_leafDeletion_vertexOf_iff hG hu hv).1 hy,
      (mem_leafDeletion_bdry hG hu hv).1 hyB⟩
  · rintro ⟨z, hz, hzB⟩
    exact ⟨⟨z, mem_compl_pair_of_mem_bdry hu hv hzB⟩, (mem_leafDeletion_vertexOf_iff hG hu hv).2 hz,
      (mem_leafDeletion_bdry hG hu hv).2 hzB⟩

include hG hu hv in
/-- A boundary vertex of the deletion is the corresponding boundary vertex of `G`. -/
theorem map_vertexOf_leafDeletion_of_isBoundaryVertex {x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)}
    (hx : G.IsBoundaryVertex (G.vertexOf x)) :
    ((G.leafDeletion hG hu hv).vertexOf x).map (Embedding.subtype _) = G.vertexOf x := by
  rw [map_vertexOf_leafDeletion, erase_eq_of_notMem]
  intro h
  rw [← G.vertexOf_eq_of_mem h] at hx
  exact G.vertexOf_mem_internalVertices.1 hv hx

include hG hu hv in
/-- **Deleting an internal leaf**, the vertices: the vertices of the deletion of `u = v(ℓ)` are
those of `G` other than `u` and `v(ℓ̄)`, together with `v(ℓ̄) \ {ℓ̄}`. -/
@[cluster_algebras "lem_leaf_deletion_plabic"]
theorem vertices_leafDeletion :
    (G.leafDeletion hG hu hv).vertices.image (Finset.map (Embedding.subtype _)) =
      insert ((G.vertexOf (G.inv ℓ)).erase (G.inv ℓ))
        ((G.vertices.erase (G.vertexOf ℓ)).erase (G.vertexOf (G.inv ℓ))) := by
  ext s
  simp only [mem_image, RotationSystem.mem_vertices, mem_insert, mem_erase]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [map_vertexOf_leafDeletion hG hu hv]
    by_cases hx : (x : H) ∈ G.vertexOf (G.inv ℓ)
    · left
      rw [G.vertexOf_eq_of_mem hx]
    · right
      have hℓx : G.inv ℓ ∉ G.vertexOf x := fun h =>
        hx (G.vertexOf_eq_of_mem h ▸ G.self_mem_vertexOf _)
      rw [erase_eq_of_notMem hℓx]
      refine ⟨fun h => hℓx (by rw [h]; exact G.self_mem_vertexOf _), fun h =>
        notMem_vertexOf_of_mem_compl_pair hu x.2 (by rw [h]; exact G.self_mem_vertexOf _), x, rfl⟩
  · rintro (rfl | ⟨hs1, hs2, z, rfl⟩)
    · refine ⟨_, ⟨⟨G.rot (G.inv ℓ), rot_inv_mem_compl_pair hG hu hv⟩, rfl⟩, ?_⟩
      rw [map_vertexOf_leafDeletion hG hu hv]
      simp only [G.vertexOf_rot]
    · have hz : z ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) :=
        mem_compl_pair_iff.2 ⟨fun h => hs2 (by rw [h]), fun h => hs1 (by rw [h])⟩
      refine ⟨_, ⟨⟨z, hz⟩, rfl⟩, ?_⟩
      rw [map_vertexOf_leafDeletion hG hu hv, erase_eq_of_notMem]
      intro h
      exact hs1 (G.vertexOf_eq_of_mem h).symm

include hG hu hv in
/-- The deletion has one vertex fewer than `G`. -/
theorem card_vertices_leafDeletion : #(G.leafDeletion hG hu hv).vertices + 1 = #G.vertices := by
  have hw : G.vertexOf (G.inv ℓ) ∈ G.vertices.erase (G.vertexOf ℓ) := by
    refine mem_erase.2 ⟨fun h => hG.inv_ne ℓ ?_, G.vertexOf_mem_vertices _⟩
    exact (mem_vertexOf_iff_of_isInternalLeaf hu).1 (h ▸ G.self_mem_vertexOf _)
  have hA : (G.vertexOf (G.inv ℓ)).erase (G.inv ℓ) ∉
      (G.vertices.erase (G.vertexOf ℓ)).erase (G.vertexOf (G.inv ℓ)) := by
    intro h
    obtain ⟨z, hz⟩ := G.mem_vertices.1 (mem_of_mem_erase (mem_of_mem_erase h))
    have hzA : z ∈ (G.vertexOf (G.inv ℓ)).erase (G.inv ℓ) := hz ▸ G.self_mem_vertexOf z
    have hz' := G.vertexOf_eq_of_mem (mem_of_mem_erase hzA)
    have : G.inv ℓ ∈ (G.vertexOf (G.inv ℓ)).erase (G.inv ℓ) := by
      rw [← hz, hz']
      exact G.self_mem_vertexOf _
    simp at this
  rw [← card_image_of_injective _ (map_injective (Embedding.subtype _)),
    vertices_leafDeletion hG hu hv, card_insert_of_notMem hA, card_erase_add_one hw,
    card_erase_add_one (G.vertexOf_mem_vertices ℓ)]

include hG hu hv in
/-- Each edge of the deletion is the corresponding edge of `G`. -/
theorem map_edgeOf_leafDeletion (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ((G.leafDeletion hG hu hv).edgeOf x).map (Embedding.subtype _) = G.edgeOf x := by
  simp [RotationSystem.edgeOf, map_insert]

include hG hu hv in
/-- The edges of the deletion are those of `G` other than `{ℓ, ℓ̄}`. -/
theorem edges_leafDeletion :
    (G.leafDeletion hG hu hv).edges.image (Finset.map (Embedding.subtype _)) =
      G.edges.erase (G.edgeOf ℓ) := by
  ext s
  simp only [mem_image, RotationSystem.mem_edges, mem_erase]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [map_edgeOf_leafDeletion]
    refine ⟨fun h => ?_, x, rfl⟩
    have hx := mem_compl_pair_iff.1 x.2
    have : (x : H) ∈ G.edgeOf ℓ := by
      rw [← h]
      exact G.mem_edgeOf.2 (Or.inl rfl)
    rcases G.mem_edgeOf.1 this with h' | h'
    exacts [hx.1 h', hx.2 h']
  · rintro ⟨hs, z, rfl⟩
    have hz : z ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) := by
      refine mem_compl_pair_iff.2 ⟨fun h => hs (by rw [h]), fun h => hs ?_⟩
      rw [h]
      ext y
      simp only [RotationSystem.mem_edgeOf, hG.inv_involutive ℓ]
      tauto
    exact ⟨_, ⟨⟨z, hz⟩, rfl⟩, map_edgeOf_leafDeletion hG hu hv _⟩

include hG hu hv in
/-- The deletion has one edge fewer than `G`. -/
theorem card_edges_leafDeletion : #(G.leafDeletion hG hu hv).edges + 1 = #G.edges := by
  rw [← card_image_of_injective _ (map_injective (Embedding.subtype _)),
    edges_leafDeletion hG hu hv, card_erase_add_one (G.mem_edges.2 ⟨ℓ, rfl⟩)]

omit [DecidableEq H] in
private theorem card_faceOrbits_eq_numOrbits [DecidableEq H] (R : RotationSystem H) :
    #R.faceOrbits = numOrbits R.facePerm := by
  rw [numOrbits_eq_card_image]
  rfl

include hG hu hv in
/-- The deletion has as many orbits of the face permutation as `G`. -/
theorem card_faceOrbits_leafDeletion :
    #(G.leafDeletion hG hu hv).faceOrbits = #G.faceOrbits := by
  rw [card_faceOrbits_eq_numOrbits, card_faceOrbits_eq_numOrbits]
  refine numOrbits_inducedRotationPerm_mul hG.inv_involutive G.rot ℓ fun x => ?_
  have h0 : (G.rot * G.inv).SameCycle ℓ (G.rot (G.inv ℓ)) :=
    sameCycle_apply_right.2 (SameCycle.refl _ _)
  by_cases hx : x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)
  · exact ⟨x, hx, SameCycle.refl _ _⟩
  · refine ⟨_, rot_inv_mem_compl_pair hG hu hv, ?_⟩
    rcases not_and_or.1 (mt mem_compl_pair_iff.2 hx) with h | h <;> rw [not_ne_iff] at h <;> subst h
    · exact h0
    · have h1 : (G.rot * G.inv) (G.inv ℓ) = ℓ := by
        rw [Perm.mul_apply, hG.inv_involutive ℓ, rot_eq_self_of_isInternalLeaf hu]
      have : (G.rot * G.inv).SameCycle (G.inv ℓ) ((G.rot * G.inv) (G.inv ℓ)) :=
        sameCycle_apply_right.2 (SameCycle.refl _ _)
      rw [h1] at this
      exact this.trans h0

include hG hu hv in
/-- Two darts of the deletion lie in one orbit of its face permutation iff they lie in one orbit
of the face permutation of `G`. -/
theorem sameCycle_leafDeletion_facePerm_iff {x y : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)} :
    (G.leafDeletion hG hu hv).facePerm.SameCycle x y ↔ G.facePerm.SameCycle x y := by
  have : (G.leafDeletion hG hu hv).facePerm =
      firstReturnPerm G.facePerm (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) :=
    inducedRotationPerm_mul_subtypePerm hG.inv_involutive G.rot ℓ
  rw [this, sameCycle_firstReturnPerm_iff]

include hG hu hv in
/-- The group generated by the rotation and the involution of the deletion is transitive. -/
theorem isConnected_leafDeletion : (G.leafDeletion hG hu hv).IsConnected := by
  have hinv := hG.inv_involutive
  have hmem := rot_inv_mem_compl_pair hG hu hv
  let proj : H → (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) := fun z =>
    if h : z ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) then ⟨z, h⟩ else ⟨G.rot (G.inv ℓ), hmem⟩
  have hpos : ∀ z (h : z ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)), proj z = ⟨z, h⟩ :=
    fun z h => dif_pos h
  have hneg : ∀ z, z ∉ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) → proj z = ⟨G.rot (G.inv ℓ), hmem⟩ :=
    fun z h => dif_neg h
  have key : ∀ d e : H, G.Reach d e → ∀ x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H), (x : H) = d →
      (G.leafDeletion hG hu hv).Reach x (proj e) := by
    intro d e he x hx
    induction he with
    | refl =>
      rw [← hx, hpos _ x.2]
      exact .refl _
    | @rot e _ ih =>
      by_cases he : e ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)
      · rw [hpos e he] at ih
        have : proj (G.rot e) = (G.leafDeletion hG hu hv).rot ⟨e, he⟩ := by
          apply Subtype.ext
          rw [coe_leafDeletion_rot]
          by_cases h : G.rot e = G.inv ℓ
          · have hn : G.rot e ∉ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) :=
              fun hh => (mem_compl_pair_iff.1 hh).2 h
            rw [hneg _ hn, if_pos h]
          · have hy : G.rot e ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) :=
              mem_compl_pair_iff.2 ⟨rot_ne_self_of_mem hu he, h⟩
            rw [hpos _ hy, if_neg h]
        rw [this]
        exact ih.rot
      · rw [hneg e he] at ih
        rcases not_and_or.1 (mt mem_compl_pair_iff.2 he) with h | h <;>
          rw [not_ne_iff] at h <;> subst h
        · rwa [rot_eq_self_of_isInternalLeaf hu, hneg _ he]
        · rwa [hpos _ hmem]
    | @inv e _ ih =>
      by_cases he : e ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)
      · rw [hpos e he] at ih
        rw [hpos _ ((apply_mem_compl_pair_iff hinv ℓ e).2 he)]
        exact ih.inv
      · rw [hneg e he] at ih
        rwa [hneg _ (mt (apply_mem_compl_pair_iff hinv ℓ e).1 he)]
  refine RotationSystem.IsConnected.of_reach ⟨⟨_, hmem⟩⟩ (fun x => Subtype.ext ?_)
    (fun x h => hG.inv_ne x (congrArg Subtype.val h)) fun x y => ?_
  · simpa only [coe_leafDeletion_inv] using hinv _
  · simpa only [hpos _ y.2] using key x y (hG.reach x y) x rfl

include hG in
private theorem exists_mem_exterior : ∃ w, w ∈ G.exterior := by
  obtain ⟨z, _, hzB⟩ := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem ⟨0, hG.one_le⟩)
  rw [← hG.exterior_union_map_inv, mem_union, mem_map] at hzB
  rcases hzB with hz | ⟨w, hw, -⟩
  exacts [⟨z, hz⟩, ⟨w, hw⟩]

include hG hu hv in
/-- **Deleting an internal leaf**, the boundary vertices: the vertex of the deletion labelled `i`
is the vertex `β(i)` of `G`. -/
@[cluster_algebras "lem_leaf_deletion_plabic"]
theorem bvertex_leafDeletion (i : Fin b) :
    ((G.leafDeletion hG hu hv).bvertex i).map (Embedding.subtype _) = G.bvertex i :=
  map_vertexOf_leafDeletion_of_isBoundaryVertex hG hu hv
    (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))

include hG hu hv in
/-- **Deleting an internal leaf**, the legs: the leg of the deletion labelled `i` is the leg `g_i`
of `G`. -/
@[cluster_algebras "lem_leaf_deletion_plabic"]
theorem leg_leafDeletion (i : Fin b) : ((G.leafDeletion hG hu hv).leg i : H) = G.leg i :=
  coe_leafDeletion_leg hG hu hv i

include hG hu hv in
private theorem exists_orbit_leafDeletion :
    ∃ f ∈ (G.leafDeletion hG hu hv).faceOrbits, f ⊆ (G.leafDeletion hG hu hv).bdry ∧
      f ∪ f.map (G.leafDeletion hG hu hv).inv.toEmbedding = (G.leafDeletion hG hu hv).bdry ∧
      Disjoint f (f.map (G.leafDeletion hG hu hv).inv.toEmbedding) := by
  obtain ⟨w, hw⟩ := exists_mem_exterior hG
  have hwY := mem_compl_pair_of_mem_bdry hu hv (G.exterior_subset_bdry hw)
  have hfw : G.faceOf w = G.exterior := by
    obtain ⟨z, hz⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
    rw [← hz] at hw ⊢
    exact G.faceOf_eq_of_mem hw
  have hext : ∀ y, y ∈ (G.leafDeletion hG hu hv).faceOf ⟨w, hwY⟩ ↔ (y : H) ∈ G.exterior := by
    intro y
    rw [RotationSystem.mem_faceOf, sameCycle_leafDeletion_facePerm_iff hG hu hv, ← hfw,
      RotationSystem.mem_faceOf]
  refine ⟨(G.leafDeletion hG hu hv).faceOf ⟨w, hwY⟩, RotationSystem.faceOf_mem_faceOrbits _ _,
    fun y hy => (mem_leafDeletion_bdry hG hu hv).2 (G.exterior_subset_bdry ((hext y).1 hy)),
    ?_, ?_⟩
  · ext y
    rw [mem_union, hext, mem_leafDeletion_bdry, ← hG.exterior_union_map_inv, mem_union]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · simp only [mem_map, Equiv.coe_toEmbedding]
      rintro ⟨a, ha, rfl⟩
      exact ⟨a, (hext a).1 ha, rfl⟩
    · simp only [mem_map, Equiv.coe_toEmbedding]
      rintro ⟨a, ha, hay⟩
      exact ⟨⟨a, mem_compl_pair_of_mem_bdry hu hv (G.exterior_subset_bdry ha)⟩, (hext _).2 ha,
        Subtype.ext hay⟩
  · rw [disjoint_left]
    intro y hy hy'
    refine disjoint_left.1 hG.disjoint_exterior_map_inv ((hext y).1 hy) ?_
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hy'
    exact mem_map.2 ⟨a, (hext a).1 ha, rfl⟩

include hG hu hv in
private theorem colour_rot_leafDeletion (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H))
    (hx : ¬(G.leafDeletion hG hu hv).IsBoundaryVertex ((G.leafDeletion hG hu hv).vertexOf x)) :
    (G.leafDeletion hG hu hv).colour ((G.leafDeletion hG hu hv).rot x) =
      (G.leafDeletion hG hu hv).colour x := by
  rw [isBoundaryVertex_vertexOf_leafDeletion_iff] at hx
  rw [leafDeletion_colour, leafDeletion_colour]
  have hrx : (((G.leafDeletion hG hu hv).rot x : _) : H) ∈ G.vertexOf x :=
    (mem_leafDeletion_vertexOf_iff hG hu hv).1 (RotationSystem.rot_mem_vertexOf _ x)
  by_cases h : (x : H) ∈ G.vertexOf (G.inv ℓ)
  · rw [G.vertexOf_eq_of_mem h] at hrx
    rw [if_pos hrx, if_pos h]
  · have h' : (((G.leafDeletion hG hu hv).rot x : _) : H) ∉ G.vertexOf (G.inv ℓ) := by
      intro h'
      apply h
      rw [← G.vertexOf_eq_of_mem h', G.vertexOf_eq_of_mem hrx]
      exact G.self_mem_vertexOf _
    have hσ : G.rot x ≠ G.inv ℓ := by
      intro hσ
      apply h
      rw [G.vertexOf_eq_of_mem (hσ ▸ G.rot_mem_vertexOf (x : H))]
      exact G.self_mem_vertexOf _
    rw [if_neg h', if_neg h, coe_leafDeletion_rot, if_neg hσ]
    exact hG.colour_rot x hx

include hG hu hv in
private theorem exists_exterior_leafDeletion (i : Fin b) :
    ∃ d ∈ (G.leafDeletion hG hu hv).exterior,
      d ∈ (G.leafDeletion hG hu hv).bvertex (finRotate b i) ∧
      (G.leafDeletion hG hu hv).inv d ∈ (G.leafDeletion hG hu hv).bvertex i := by
  obtain ⟨d, hd, h1, h2⟩ := hG.exists_exterior i
  have hdB := G.exterior_subset_bdry hd
  have hσ : G.rot d ≠ G.inv ℓ := by
    intro hσ
    have := G.vertexOf_eq_of_mem (hσ ▸ G.rot_mem_vertexOf d)
    exact G.vertexOf_mem_internalVertices.1 hv
      (this ▸ G.isBoundaryVertex_vertexOf_of_mem hdB)
  refine ⟨⟨d, mem_compl_pair_of_mem_bdry hu hv hdB⟩, ?_, ?_, ?_⟩
  · rw [DiskMap.mem_exterior, mem_leafDeletion_bdry, mem_leafDeletion_bdry,
      coe_leafDeletion_rot, if_neg hσ]
    exact G.mem_exterior.1 hd
  · rwa [← mem_map' (Embedding.subtype _), bvertex_leafDeletion]
  · rwa [← mem_map' (Embedding.subtype _), bvertex_leafDeletion]

include hG hu hv in
/-- **Deleting an internal leaf gives a plabic graph**: if `u = v(ℓ)` is an internal leaf of the
plabic graph `G` and `v(ℓ̄)` is internal, the deletion of `u` is a plabic graph. Its boundary
vertices and legs are those of `G` (`bvertex_leafDeletion`, `leg_leafDeletion`) and its vertices
are described by `vertices_leafDeletion`. -/
@[cluster_algebras "lem_leaf_deletion_plabic"]
theorem isPlabicGraph_leafDeletion : (G.leafDeletion hG hu hv).IsPlabicGraph where
  toIsConnected := isConnected_leafDeletion hG hu hv
  inv_mem_bdry x hx := by
    rw [mem_leafDeletion_bdry] at hx ⊢
    exact hG.inv_mem_bdry _ hx
  euler := by
    have := hG.euler
    have h1 := card_vertices_leafDeletion hG hu hv
    have h2 := card_edges_leafDeletion hG hu hv
    have h3 := card_faceOrbits_leafDeletion hG hu hv
    omega
  boundaryVertex_card v hv' := by
    obtain ⟨hvV, hvB⟩ := (G.leafDeletion hG hu hv).mem_boundaryVertices.1 hv'
    obtain ⟨x, rfl⟩ := (G.leafDeletion hG hu hv).mem_vertices.1 hvV
    have hb := (isBoundaryVertex_vertexOf_leafDeletion_iff hG hu hv x).1 hvB
    have hm := map_vertexOf_leafDeletion_of_isBoundaryVertex hG hu hv hb
    obtain ⟨h3, h2⟩ := hG.boundaryVertex_card _ (G.vertexOf_mem_boundaryVertices.2 hb)
    constructor
    · rw [← card_map (Embedding.subtype _), hm]
      exact h3
    · rw [← card_map (Embedding.subtype _), ← h2, ← hm, filter_map]
      congr 2
      exact filter_congr fun y _ => mem_leafDeletion_bdry hG hu hv
  exists_orbit := exists_orbit_leafDeletion hG hu hv
  one_le := hG.one_le
  colour_rot := colour_rot_leafDeletion hG hu hv
  leg_notMem_bdry i := by
    rw [mem_leafDeletion_bdry]
    exact hG.leg_notMem_bdry i
  bvertex_mem i := (G.leafDeletion hG hu hv).vertexOf_mem_boundaryVertices.2
    ((isBoundaryVertex_vertexOf_leafDeletion_iff hG hu hv _).2
      (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)))
  bvertex_injective i j h := hG.bvertex_injective (by
    rw [← bvertex_leafDeletion hG hu hv i, h, bvertex_leafDeletion])
  exists_bvertex_eq v hv' := by
    obtain ⟨hvV, hvB⟩ := (G.leafDeletion hG hu hv).mem_boundaryVertices.1 hv'
    obtain ⟨x, rfl⟩ := (G.leafDeletion hG hu hv).mem_vertices.1 hvV
    have hb := (isBoundaryVertex_vertexOf_leafDeletion_iff hG hu hv x).1 hvB
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hb)
    exact ⟨i, map_injective (Embedding.subtype _) (by
      rw [bvertex_leafDeletion, map_vertexOf_leafDeletion_of_isBoundaryVertex hG hu hv hb, hi])⟩
  exists_exterior := exists_exterior_leafDeletion hG hu hv

end LeafDeletion

/-! ### The skeleton -/

section Skeleton

variable (G)

/-- The **rotation of the core** `σ_K : K → K`: it sends `x` to `σ^m(x)` for the least `m ≥ 1`
with `σ^m(x) ∈ K`, the first-return map of `σ` to the core. -/
noncomputable def coreRot : Perm (G.core : Set H) :=
  firstReturnPerm G.rot G.core

/-- The darts `R` of the skeleton: the darts `x` of the core `K` such that `v(x)` is a boundary
vertex or contains at least three darts of `K`. -/
def skeletonDarts : Finset H :=
  {x ∈ G.core | G.IsBoundaryVertex (G.vertexOf x) ∨ 3 ≤ #(G.vertexOf x ∩ G.core)}

/-- One step `e ↦ \overline{σ_K(e)}` of the walk through the core. -/
noncomputable def coreWalk (e : (G.core : Set H)) : (G.core : Set H) :=
  ⟨G.inv (G.coreRot e), mem_coe.2 (DiskMap.inv_mem_core (G.coreRot e).2)⟩

variable {G}

/-- A dart `x` lies in `R` if and only if it lies in the core and `v(x)` is a boundary vertex or
contains at least three darts of the core. -/
theorem mem_skeletonDarts {x : H} :
    x ∈ G.skeletonDarts ↔
      x ∈ G.core ∧ (G.IsBoundaryVertex (G.vertexOf x) ∨ 3 ≤ #(G.vertexOf x ∩ G.core)) :=
  mem_filter

/-- A dart of `R` lies in the core. -/
theorem mem_core_of_mem_skeletonDarts {x : H} (hx : x ∈ G.skeletonDarts) : x ∈ G.core :=
  (mem_skeletonDarts.1 hx).1

variable (G)

/-- The walk `e_0 = d̄`, `e_{j+1} = \overline{σ_K(e_j)}` through the core, from a dart `d` of the
skeleton. -/
noncomputable def skeletonWalk (d : (G.skeletonDarts : Set H)) (j : ℕ) : (G.core : Set H) :=
  G.coreWalk^[j] ⟨G.inv d, mem_coe.2 (DiskMap.inv_mem_core (mem_core_of_mem_skeletonDarts d.2))⟩

open scoped Classical in
/-- The involution `d ↦ d̄^Γ` of the skeleton, as a function: `d̄^Γ` is the first term `e_j` of the
walk `G.skeletonWalk d` lying in `R`, and `d` if there is none. For a plabic graph there always is
one, and `d ↦ d̄^Γ` is an involution (`PlabicData.involutive_skeletonInvFun`). -/
noncomputable def skeletonInvFun (d : (G.skeletonDarts : Set H)) : (G.skeletonDarts : Set H) :=
  if h : ∃ j, (G.skeletonWalk d j : H) ∈ G.skeletonDarts then
    ⟨G.skeletonWalk d (Nat.find h), mem_coe.2 (Nat.find_spec h)⟩
  else d

variable {G}

/-- One step of the walk through the core sends `e` to `\overline{σ_K(e)}`. -/
@[simp]
theorem coe_coreWalk (e : (G.core : Set H)) : (G.coreWalk e : H) = G.inv (G.coreRot e) :=
  rfl

/-- The walk from a dart `d` of the skeleton starts at `d̄`. -/
theorem skeletonWalk_zero (d : (G.skeletonDarts : Set H)) :
    (G.skeletonWalk d 0 : H) = G.inv d :=
  rfl

/-- The walk from a dart `d` of the skeleton satisfies `e_{j+1} = \overline{σ_K(e_j)}`. -/
theorem skeletonWalk_succ (d : (G.skeletonDarts : Set H)) (j : ℕ) :
    G.skeletonWalk d (j + 1) = G.coreWalk (G.skeletonWalk d j) :=
  iterate_succ_apply' _ _ _

/-- Two darts of the core lie in one orbit of `σ_K` iff they lie in one vertex. -/
theorem sameCycle_coreRot_iff {x y : (G.core : Set H)} :
    G.coreRot.SameCycle x y ↔ G.rot.SameCycle x y :=
  sameCycle_firstReturnPerm_iff _ _

/-- A dart `e` of the core and its image `σ_K(e)` lie in one vertex. -/
theorem sameCycle_coreRot_apply (e : (G.core : Set H)) : G.rot.SameCycle e (G.coreRot e) :=
  sameCycle_coreRot_iff.1 (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-- `R` consists of whole intersections `v ∩ K`. -/
theorem mem_skeletonDarts_of_sameCycle {x y : H} (hx : x ∈ G.skeletonDarts) (hy : y ∈ G.core)
    (hxy : G.rot.SameCycle x y) : y ∈ G.skeletonDarts := by
  simp only [mem_skeletonDarts] at hx ⊢
  rw [← G.vertexOf_eq_vertexOf_iff.2 hxy]
  exact ⟨hy, hx.2⟩

/-- At a dart `e` of the core outside `R`, the vertex has exactly two darts of the core, so `σ_K`
exchanges them. -/
theorem coreRot_coreRot_of_notMem {e : (G.core : Set H)} (he : (e : H) ∉ G.skeletonDarts) :
    G.coreRot (G.coreRot e) = e := by
  by_contra hne
  have hc2 : #(G.vertexOf e ∩ G.core) < 3 := by
    by_contra h3
    exact he (mem_skeletonDarts.2 ⟨e.2, Or.inr (not_lt.1 h3)⟩)
  have h1 : G.coreRot e ≠ e := fun h => hne (by rw [h, h])
  have h2 : G.coreRot (G.coreRot e) ≠ G.coreRot e := fun h => h1 (G.coreRot.injective h)
  have hs1 := sameCycle_coreRot_apply e
  have h3 : 2 < #(G.vertexOf e ∩ G.core) := two_lt_card_iff.2 ⟨(e : H), (G.coreRot e : H),
    (G.coreRot (G.coreRot e) : H), ?_, ?_, ?_, fun h => h1 (Subtype.ext h).symm,
    fun h => hne (Subtype.ext h).symm, fun h => h2 (Subtype.ext h).symm⟩
  · omega
  · exact mem_inter.2 ⟨G.self_mem_vertexOf _, e.2⟩
  · exact mem_inter.2 ⟨G.mem_vertexOf.2 hs1, (G.coreRot e).2⟩
  · exact mem_inter.2 ⟨G.mem_vertexOf.2 (hs1.trans (sameCycle_coreRot_apply _)),
      (G.coreRot (G.coreRot e)).2⟩

/-- If a dart `e` of the core is not in `R`, neither is `σ_K(e)`. -/
theorem coreRot_notMem_of_notMem {e : (G.core : Set H)} (he : (e : H) ∉ G.skeletonDarts) :
    (G.coreRot e : H) ∉ G.skeletonDarts := fun h =>
  he (mem_skeletonDarts_of_sameCycle h e.2 (sameCycle_coreRot_apply e).symm)

/-- The walk from a dart of the skeleton reaches `R`. -/
theorem exists_skeletonWalk_mem (d : (G.skeletonDarts : Set H)) :
    ∃ j, (G.skeletonWalk d j : H) ∈ G.skeletonDarts := by
  have hinj : Injective G.coreWalk := fun x y h =>
    G.coreRot.injective (Subtype.ext (G.inv.injective (congrArg Subtype.val h)))
  let P : Perm (G.core : Set H) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
  have hP : 0 < orderOf P := (isOfFinOrder_of_finite P).orderOf_pos
  obtain ⟨m, hm⟩ : ∃ m, orderOf P = m + 1 := ⟨orderOf P - 1, by omega⟩
  refine ⟨m, ?_⟩
  have key : (P ^ (m + 1)) (G.skeletonWalk d 0) = G.skeletonWalk d 0 := by
    rw [← hm, pow_orderOf_eq_one, Perm.one_apply]
  rw [pow_succ', Perm.mul_apply, Perm.coe_pow] at key
  change G.coreWalk (G.skeletonWalk d m) = G.skeletonWalk d 0 at key
  have h1 : (G.coreRot (G.skeletonWalk d m) : H) = d :=
    G.inv.injective (congrArg Subtype.val key)
  exact mem_skeletonDarts_of_sameCycle (mem_coe.1 d.2) (G.skeletonWalk d m).2
    (h1 ▸ sameCycle_coreRot_apply (G.skeletonWalk d m)).symm

/-- `d̄^Γ` is the first term of the walk from `d` lying in `R`. -/
theorem exists_coe_skeletonInvFun (d : (G.skeletonDarts : Set H)) :
    ∃ n, (G.skeletonWalk d n : H) ∈ G.skeletonDarts ∧
      (∀ j < n, (G.skeletonWalk d j : H) ∉ G.skeletonDarts) ∧
      (G.skeletonInvFun d : H) = G.skeletonWalk d n := by
  have h := exists_skeletonWalk_mem d
  unfold skeletonInvFun
  rw [dif_pos h]
  exact ⟨_, Nat.find_spec h, fun j hj => Nat.find_min h hj, rfl⟩

/-- If `e_n` is the first term of the walk from `d` lying in `R`, then `d̄^Γ = e_n`. -/
theorem coe_skeletonInvFun_of_isLeast (d : (G.skeletonDarts : Set H)) {n : ℕ}
    (hn : (G.skeletonWalk d n : H) ∈ G.skeletonDarts)
    (hmin : ∀ j < n, (G.skeletonWalk d j : H) ∉ G.skeletonDarts) :
    (G.skeletonInvFun d : H) = G.skeletonWalk d n := by
  obtain ⟨n', hn', hmin', h⟩ := exists_coe_skeletonInvFun d
  obtain rfl : n' = n := le_antisymm (not_lt.1 fun hlt => hmin' _ hlt hn)
    (not_lt.1 fun hlt => hmin _ hlt hn')
  exact h

/-- Reversing a walk: if `e_n` is the first term of the walk from `d` in `R` and `t = e_n`, then
the walk from `t` first meets `R` at its `n`-th term, which is `d`. -/
theorem skeletonWalk_reverse (hinv : Involutive G.inv) (d : (G.skeletonDarts : Set H)) (n : ℕ)
    (hn : (G.skeletonWalk d n : H) ∈ G.skeletonDarts)
    (hmin : ∀ j < n, (G.skeletonWalk d j : H) ∉ G.skeletonDarts) :
    (G.skeletonWalk ⟨G.skeletonWalk d n, mem_coe.2 hn⟩ n : H) = d ∧
      ∀ j < n, (G.skeletonWalk ⟨G.skeletonWalk d n, mem_coe.2 hn⟩ j : H) ∉ G.skeletonDarts := by
  rcases n with _ | m
  · exact ⟨hinv _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  set t : (G.skeletonDarts : Set H) := ⟨G.skeletonWalk d (m + 1), mem_coe.2 hn⟩ with ht
  have claim : ∀ k ≤ m, G.skeletonWalk t k = G.coreRot (G.skeletonWalk d (m - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      apply Subtype.ext
      rw [skeletonWalk_zero]
      change G.inv (G.skeletonWalk d (m + 1) : H) = _
      rw [skeletonWalk_succ, coe_coreWalk, hinv, Nat.sub_zero]
    | succ k ih =>
      intro hk
      rw [skeletonWalk_succ, ih (by omega)]
      apply Subtype.ext
      rw [coe_coreWalk, coreRot_coreRot_of_notMem (hmin _ (by omega))]
      obtain ⟨r, hr⟩ : ∃ r, m - k = r + 1 := ⟨m - k - 1, by omega⟩
      rw [hr, skeletonWalk_succ, coe_coreWalk, hinv, show m - (k + 1) = r by omega]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [skeletonWalk_succ, claim m le_rfl, Nat.sub_self, coe_coreWalk,
      coreRot_coreRot_of_notMem (hmin 0 (Nat.succ_pos _)), skeletonWalk_zero, hinv]
  · rw [claim j (by omega)]
    exact coreRot_notMem_of_notMem (hmin _ (by omega))

/-- If `d ↦ d̄` is an involution (for instance in a plabic graph), then so is `d ↦ d̄^Γ` on `R`. -/
theorem involutive_skeletonInvFun (hinv : Involutive G.inv) : Involutive G.skeletonInvFun := by
  intro d
  obtain ⟨n, hn, hmin, hd⟩ := exists_coe_skeletonInvFun d
  rw [show G.skeletonInvFun d = ⟨G.skeletonWalk d n, mem_coe.2 hn⟩ from Subtype.ext hd]
  obtain ⟨h1, h2⟩ := skeletonWalk_reverse hinv d n hn hmin
  exact Subtype.ext ((coe_skeletonInvFun_of_isLeast _ (h1 ▸ mem_coe.1 d.2) h2).trans h1)

/-- At a boundary vertex the dart after the leg lies in `R`. -/
theorem rot_leg_mem_skeletonDarts (hG : G.IsPlabicGraph) (i : Fin b) :
    G.rot (G.leg i) ∈ G.skeletonDarts := by
  have hb := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hB : G.rot (G.leg i) ∈ G.bdry := by
    by_contra h
    exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hb
      (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hb (G.rot_mem_vertexOf _)
        (G.self_mem_vertexOf _) h (hG.leg_notMem_bdry i))
  exact mem_skeletonDarts.2 ⟨hG.bdry_subset_core hB, Or.inl (by rw [G.vertexOf_rot]; exact hb)⟩

variable (G) in
/-- The **skeleton** `Γ(G)` of a plabic graph: its darts are `R`, its involution is `d ↦ d̄^Γ`
(`PlabicData.skeletonInvFun`), its rotation is the first-return map `σ_R` of `σ` to `R`, its
boundary arcs are `B`, its colouring is that of `G`, and the vertex labelled `i` is `β(i) ∩ R`.
The latter is recorded by the dart `leg i` of `Γ(G)`: the leg `g_i` of `G` when it lies in `R`
(always, when `G` is anchored), and otherwise the dart `σ(g_i)` of `β(i) ∩ B`. -/
@[cluster_algebras "def_skeleton"]
noncomputable def skeleton (hG : G.IsPlabicGraph) : PlabicData (G.skeletonDarts : Set H) b where
  inv := Involutive.toPerm G.skeletonInvFun (involutive_skeletonInvFun hG.inv_involutive)
  rot := firstReturnPerm G.rot G.skeletonDarts
  bdry := univ.filter fun x => (x : H) ∈ G.bdry
  colour x := G.colour x
  leg i := if h : G.leg i ∈ G.skeletonDarts then ⟨G.leg i, mem_coe.2 h⟩
    else ⟨G.rot (G.leg i), mem_coe.2 (rot_leg_mem_skeletonDarts hG i)⟩

variable (hG : G.IsPlabicGraph)

/-- The involution of the skeleton is `d ↦ d̄^Γ`. -/
@[simp]
theorem coe_skeleton_inv (x : (G.skeletonDarts : Set H)) :
    ((G.skeleton hG).inv x : H) = G.skeletonInvFun x :=
  rfl

/-- The rotation of the skeleton is the first-return map of `σ` to `R`. -/
theorem skeleton_rot : (G.skeleton hG).rot = firstReturnPerm G.rot G.skeletonDarts :=
  rfl

/-- The boundary arcs of the skeleton are the darts of `B`. -/
@[simp]
theorem mem_skeleton_bdry {x : (G.skeletonDarts : Set H)} :
    x ∈ (G.skeleton hG).bdry ↔ (x : H) ∈ G.bdry := by
  simp [skeleton]

/-- The colouring of the skeleton is the restriction of the colouring of `G`. -/
@[simp]
theorem skeleton_colour (x : (G.skeletonDarts : Set H)) :
    (G.skeleton hG).colour x = G.colour x :=
  rfl

/-- If the leg `g_i` lies in `R`, it is the leg of the skeleton labelled `i`. -/
theorem coe_skeleton_leg_of_mem {i : Fin b} (h : G.leg i ∈ G.skeletonDarts) :
    ((G.skeleton hG).leg i : H) = G.leg i := by
  simp [skeleton, h]

include hG in
/-- In an anchored plabic graph every leg is a dart of the skeleton. -/
theorem IsAnchored.leg_mem_skeletonDarts (hA : G.IsAnchored) (i : Fin b) :
    G.leg i ∈ G.skeletonDarts :=
  mem_skeletonDarts.2 ⟨hA i, Or.inl (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))⟩

/-- The vertices of the skeleton are the sets `v ∩ R`. -/
theorem map_skeleton_vertexOf (x : (G.skeletonDarts : Set H)) :
    ((G.skeleton hG).vertexOf x).map (Embedding.subtype _) = G.vertexOf x ∩ G.skeletonDarts := by
  ext z
  simp only [mem_map, Embedding.coe_subtype, mem_inter, RotationSystem.mem_vertexOf,
    skeleton_rot]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(sameCycle_firstReturnPerm_iff _ _).1 hy, mem_coe.1 y.2⟩
  · rintro ⟨hxz, hz⟩
    exact ⟨⟨z, mem_coe.2 hz⟩, (sameCycle_firstReturnPerm_iff _ _).2 hxz, rfl⟩

/-- The vertex of the skeleton labelled `i` is `β_Γ(i) = β(i) ∩ R`. -/
theorem map_skeleton_bvertex (i : Fin b) :
    ((G.skeleton hG).bvertex i).map (Embedding.subtype _) = G.bvertex i ∩ G.skeletonDarts := by
  rw [PlabicData.bvertex, map_skeleton_vertexOf]
  congr 1
  by_cases h : G.leg i ∈ G.skeletonDarts
  · rw [coe_skeleton_leg_of_mem hG h]
    rfl
  · have : ((G.skeleton hG).leg i : H) = G.rot (G.leg i) := by
      simp [skeleton, h]
    rw [this, G.vertexOf_rot]
    rfl

/-- **A graph without small vertices is its own skeleton**: if every internal vertex of the plabic
graph `G` has at least three darts, then `R = H`, and the involution, the rotation, the boundary
arcs, the colours and the legs of `Γ(G)` are those of `G`. -/
@[cluster_algebras "lem_skeleton_of_thick"]
theorem skeleton_of_thick (h3 : ∀ v ∈ G.internalVertices, 3 ≤ #v) :
    G.skeletonDarts = univ ∧
      (∀ x, ((G.skeleton hG).inv x : H) = G.inv x) ∧
      (∀ x, ((G.skeleton hG).rot x : H) = G.rot x) ∧
      (∀ x, x ∈ (G.skeleton hG).bdry ↔ (x : H) ∈ G.bdry) ∧
      (∀ x, (G.skeleton hG).colour x = G.colour x) ∧
      ∀ i, ((G.skeleton hG).leg i : H) = G.leg i := by
  have hK : G.core = univ := hG.core_eq_univ fun v hv => Nat.le_of_succ_le (h3 v hv)
  have hR : ∀ x, x ∈ G.skeletonDarts := by
    intro x
    refine mem_skeletonDarts.2 ⟨hK ▸ mem_univ x, ?_⟩
    rw [hK, inter_univ]
    exact or_iff_not_imp_left.2 fun hb => h3 _ (G.vertexOf_mem_internalVertices.2 hb)
  refine ⟨eq_univ_of_forall hR, fun x => ?_, fun x => ?_, fun x => mem_skeleton_bdry hG,
    fun x => rfl, fun i => coe_skeleton_leg_of_mem hG (hR _)⟩
  · rw [coe_skeleton_inv]
    exact (coe_skeletonInvFun_of_isLeast x (n := 0) (hR _)
      fun j hj => absurd hj (Nat.not_lt_zero _)).trans (skeletonWalk_zero x)
  · rw [skeleton_rot, coe_firstReturnPerm]
    exact coe_firstReturn_of_apply_mem (mem_coe.2 (hR _))

/-- If every internal vertex of the plabic graph `G` has at least three darts, the inclusion of
the darts of `Γ(G)` is an isomorphism `Γ(G) → G`. -/
noncomputable def skeletonIsoOfThick (h3 : ∀ v ∈ G.internalVertices, 3 ≤ #v) :
    (G.skeleton hG).Iso G where
  toEquiv := Equiv.subtypeUnivEquiv fun x =>
    mem_coe.2 ((skeleton_of_thick hG h3).1 ▸ mem_univ x)
  map_inv x := (skeleton_of_thick hG h3).2.1 x
  map_rot x := (skeleton_of_thick hG h3).2.2.1 x
  mem_bdry_iff _ := (mem_skeleton_bdry hG).symm
  map_colour _ _ := rfl
  map_bvertex i := by
    have he : (Equiv.subtypeUnivEquiv fun x =>
        mem_coe.2 ((skeleton_of_thick hG h3).1 ▸ mem_univ x)).toEmbedding =
        Embedding.subtype (· ∈ (G.skeletonDarts : Set H)) := by
      ext
      rfl
    have hb : G.bvertex i = ((G.skeleton hG).bvertex i).map (Embedding.subtype _) := by
      rw [map_skeleton_bvertex, (skeleton_of_thick hG h3).1, inter_univ]
    rw [he, hb, filter_map]
    congr 1
    exact filter_congr fun y _ => (mem_skeleton_bdry hG).not

end Skeleton

end PlabicData

end ClusterAlgebras
