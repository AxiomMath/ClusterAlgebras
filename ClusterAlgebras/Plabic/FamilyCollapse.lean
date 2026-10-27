/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Reduced
public import ClusterAlgebras.Plabic.LollipopInsertion
public import ClusterAlgebras.Plabic.TripSides

/-!
# Collapsing families of trees in plabic graphs

A *collapsing family* of a plabic graph `G` is a finite set of triples `(v, W, c)`, each `(v, W)` a
collapsible tree of colour `c`, whose sets `W` are pairwise disjoint, whose roots lie in no other
`W`, and whose roots keep a dart outside all the trees. The *collapse* `G/𝒯` deletes the darts of
the trees: an internal root loses its intervals, and a tree with a boundary root `β(i)` is replaced
by a lollipop of its colour at `i`. Its rotation is the first return of `σ` to the kept darts.

This file also builds isomorphisms of plabic data from bijections of darts (`isoOfMapLeg`) and the
API of the rotation orbits and of the interval of a rooted tree on which the collapse rests.

## Main definitions

* `ClusterAlgebras.PlabicData.IsCollapsingFamily`: collapsing families.
* `ClusterAlgebras.PlabicData.collapse`: the collapse `G/𝒯` of a family of trees, with its kept
  darts `collapseCore` and its darts `collapseDarts`.

## Main results

* `ClusterAlgebras.PlabicData.image_collapse_vertices` and its companions
  `filter_vertexOf_mem_collapseCore_nonempty`, `exists_mem_bdry_filter_vertexOf_iff`,
  `filter_vertexOf_mem_collapseCore_of_not`, `filter_vertexOf_mem_collapseCore_of_internal`: the
  vertices of a collapse.

## Implementation notes

* A member `(v, W, c)` of a family is a pair of a rooted tree and a colour, and a family is a
  `Finset` of such pairs.
* The labels `I` of the collapse are those `i` whose leg `g_i` lies in a tree; for a family of
  rooted trees of a plabic graph this is the case exactly when `β(i)` is a root. Since the other
  legs lie outside the trees, the set `K` is written as the darts outside the trees together with
  all the legs. The colour `c_i` at `ḡ_i` is that of the member whose tree contains `g_i`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

/-! ### Isomorphisms from bijections of darts -/

section Iso

variable {X Y : Type*}

private theorem pow_apply_of_semiconj' {π : Perm X} {π' : Perm Y} (θ : X ≃ Y)
    (h : ∀ x, θ (π x) = π' (θ x)) (n : ℕ) (x : X) : θ ((π ^ n) x) = (π' ^ n) (θ x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, h, ih]

private theorem sameCycle_apply_iff_of_semiconj' [Finite X] {π : Perm X} {π' : Perm Y}
    (θ : X ≃ Y) (h : ∀ x, θ (π x) = π' (θ x)) {x y : X} :
    π'.SameCycle (θ x) (θ y) ↔ π.SameCycle x y := by
  have h' : ∀ y, θ.symm (π' y) = π (θ.symm y) := fun y => by
    apply θ.injective
    rw [h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  constructor
  · intro hxy
    have : Finite Y := Finite.of_equiv X θ
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    have := pow_apply_of_semiconj' θ.symm h' n (θ x)
    rw [hn, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
    exact this.symm
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← pow_apply_of_semiconj' θ h, hn]⟩

end Iso

namespace PlabicData

section Iso

variable {H₁ H₂ : Type*} [Fintype H₁] [DecidableEq H₁] [Fintype H₂] [DecidableEq H₂] {b : ℕ}

/-- A bijection of darts intertwining the rotations maps each vertex onto a vertex. -/
private theorem map_vertexOf_of_semiconj' {G : PlabicData H₁ b} {G' : PlabicData H₂ b}
    (e : H₁ ≃ H₂) (map_rot : ∀ d, e (G.rot d) = G'.rot (e d)) (d : H₁) :
    (G.vertexOf d).map e.toEmbedding = G'.vertexOf (e d) := by
  ext y
  rw [mem_map_equiv, RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf,
    ← sameCycle_apply_iff_of_semiconj' e map_rot, Equiv.apply_symm_apply]

/-- An isomorphism of tuples, built from a bijection of darts commuting with the involutions and
the rotations, preserving `B`, the colours of internal vertices and the legs. -/
def isoOfMapLeg {G : PlabicData H₁ b} {G' : PlabicData H₂ b} (e : H₁ ≃ H₂)
    (map_inv : ∀ d, e (G.inv d) = G'.inv (e d)) (map_rot : ∀ d, e (G.rot d) = G'.rot (e d))
    (mem_bdry_iff : ∀ d, e d ∈ G'.bdry ↔ d ∈ G.bdry)
    (map_colour : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G'.colour (e d) = G.colour d)
    (map_leg : ∀ i, e (G.leg i) = G'.leg i) : G.Iso G' where
  toEquiv := e
  map_inv := map_inv
  map_rot := map_rot
  mem_bdry_iff := mem_bdry_iff
  map_colour := map_colour
  map_bvertex i := by
    simp only [bvertex]
    rw [← map_leg, ← map_vertexOf_of_semiconj' e map_rot, filter_map]
    congr 1
    refine filter_congr fun x _ => ?_
    simp [mem_bdry_iff]

end Iso

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Orbits of the rotation -/

/-- If `σ^n d = d` with `0 < n`, the vertex of `d` has at most `n` darts. -/
theorem card_vertexOf_le_of_pow_apply_eq {d : H} {n : ℕ} (hn : 0 < n)
    (h : (G.rot ^ n) d = d) : (G.vertexOf d).card ≤ n := by
  have hsub : G.vertexOf d ⊆ (range n).image fun i => (G.rot ^ i) d := by
    intro e he
    obtain ⟨m, rfl⟩ := ((RotationSystem.mem_vertexOf _).1 he).exists_nat_pow_eq
    have hm : (G.rot ^ m) d = (G.rot ^ (m % n)) d := by
      conv_lhs => rw [← Nat.mod_add_div m n]
      rw [pow_add, Perm.mul_apply, pow_mul]
      congr 1
      exact Perm.pow_apply_eq_self_of_apply_eq_self h _
    rw [hm]
    exact mem_image_of_mem _ (mem_range.2 (Nat.mod_lt _ hn))
  exact (card_le_card hsub).trans (card_image_le.trans (card_range n).le)

/-- The darts `σ^i d`, `i < |v(d)|`, are distinct. -/
private theorem pow_apply_injective {d : H} {i j : ℕ} (hi : i < (G.vertexOf d).card)
    (hj : j < (G.vertexOf d).card) (h : (G.rot ^ i) d = (G.rot ^ j) d) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi h.symm (by omega)).symm
  by_contra hne
  have hpos : 0 < j - i := by omega
  have : (G.rot ^ (j - i)) d = d := by
    apply (G.rot ^ i).injective
    rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij, h]
  have := card_vertexOf_le_of_pow_apply_eq hpos this
  omega

namespace RootedTree

variable (T : G.RootedTree)

/-- The root of a tree has as many darts as the vertex of `G` at its first interval dart. -/
theorem card_root_eq : T.root.card = (G.vertexOf T.intervalStart).card := by
  rw [T.root_eq_vertexOf_intervalStart]

/-- The darts `σ^j a₁`, `j < |v|`, are distinct. -/
theorem pow_intervalStart_injective {i j : ℕ} (hi : i < T.root.card) (hj : j < T.root.card)
    (h : (G.rot ^ i) T.intervalStart = (G.rot ^ j) T.intervalStart) : i = j := by
  rw [card_root_eq] at hi hj
  exact pow_apply_injective hi hj h

/-- A dart of `D_T` at the root is a dart of the interval. -/
theorem exists_eq_pow_of_mem_root {d : H} (hd : d ∈ T.darts) (hr : d ∈ T.root) :
    ∃ j < T.intervalLength, (G.rot ^ j) T.intervalStart = d :=
  (T.mem_darts_iff_of_mem_root hr).1 hd

/-- If `x ∉ D_T` and `σ x ∈ D_T`, then `x` lies at the root. -/
theorem vertexOf_eq_root_of_rot_mem (hG : G.IsPlabicGraph) {x : H} (hx : x ∉ T.darts)
    (hrx : G.rot x ∈ T.darts) : G.vertexOf x = T.root := by
  rcases T.vertexOf_mem_or_eq_root hG hrx with h | h
  · rw [G.vertexOf_rot] at h
    exact absurd (T.mem_darts_of_vertexOf_mem h) hx
  · rwa [G.vertexOf_rot] at h

/-- If `x ∉ D_T` and `σ x ∈ D_T`, then `σ x = a₁`. -/
theorem rot_eq_intervalStart (hG : G.IsPlabicGraph) {x : H} (hx : x ∉ T.darts)
    (hrx : G.rot x ∈ T.darts) : G.rot x = T.intervalStart := by
  have hroot : G.vertexOf (G.rot x) = T.root := by
    rw [G.vertexOf_rot]
    exact T.vertexOf_eq_root_of_rot_mem hG hx hrx
  obtain ⟨j, hj, hj'⟩ := T.exists_eq_pow_of_mem_root hrx (T.mem_root_iff.2 hroot)
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact hj'.symm
  · refine absurd ?_ hx
    have : x = (G.rot ^ (j - 1)) T.intervalStart := by
      apply G.rot.injective
      rw [← hj', ← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hj0]
    rw [this]
    exact T.pow_intervalStart_mem_darts (by omega)

/-- A dart `d` of `D_T` with `σ d ∉ D_T` is `a_k`. -/
theorem eq_intervalEnd (hG : G.IsPlabicGraph) {d : H} (hd : d ∈ T.darts)
    (h : G.rot d ∉ T.darts) : d = T.intervalEnd :=
  T.eq_of_rot_notMem hG hd T.intervalEnd_mem_darts h (T.rot_intervalEnd_notMem hG)

/-- A leg in `D_T` lies at the root. -/
theorem root_eq_bvertex_of_leg_mem (hG : G.IsPlabicGraph) {i : Fin b}
    (h : G.leg i ∈ T.darts) : T.root = G.bvertex i := by
  rcases T.vertexOf_mem_or_eq_root hG h with h' | h'
  · exact absurd (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))
      (G.mem_internalVertices.1 (T.nonRoot_subset h')).2
  · exact h'.symm

/-- A leg in `D_T` is `a₁`. -/
theorem leg_eq_intervalStart (hG : G.IsPlabicGraph) {i : Fin b} (h : G.leg i ∈ T.darts) :
    G.leg i = T.intervalStart := by
  have hr := T.root_eq_bvertex_of_leg_mem hG h
  have hb : G.IsBoundaryVertex T.root := by
    rw [hr]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  refine T.eq_intervalStart_of_isBoundaryVertex hG hb h ?_
  rw [hr]
  rfl

/-- For a boundary root, the interval is the single dart `a₁ = a_k`. -/
theorem intervalEnd_eq_intervalStart (hG : G.IsPlabicGraph) (hb : G.IsBoundaryVertex T.root) :
    T.intervalEnd = T.intervalStart :=
  (T.eq_intervalEnd hG T.intervalStart_mem_darts
    (T.rot_intervalStart_notMem_of_isBoundaryVertex hG hb)).symm

/-- For a boundary root `β(i)`, `a₁` is the leg `g_i`. -/
theorem intervalStart_eq_leg (hG : G.IsPlabicGraph) {i : Fin b} (h : T.root = G.bvertex i) :
    T.intervalStart = G.leg i := by
  have hb : G.IsBoundaryVertex T.root := by
    rw [h]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hrA := T.intervalStart_mem_root
  rw [h] at hrA
  exact DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card
    (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)) hrA (G.self_mem_vertexOf _)
    (G.mem_treeDarts.1 T.intervalStart_mem_darts).1 (hG.leg_notMem_bdry i)

/-- A dart of a rooted tree is not a boundary arc. -/
theorem notMem_bdry_of_mem_darts {d : H} (hd : d ∈ T.darts) : d ∉ G.bdry :=
  (G.mem_treeDarts.1 hd).1

/-- The darts of two rooted trees are disjoint when their non-root vertices are disjoint and the
root of the second tree is not a non-root vertex of the first. -/
theorem disjoint_darts (hG : G.IsPlabicGraph) {T' : G.RootedTree}
    (hW : Disjoint T.nonRoot T'.nonRoot) (h₂ : T'.root ∉ T.nonRoot) :
    Disjoint T.darts T'.darts := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  rcases (G.mem_treeDarts.1 hd).2 with h | h <;> rcases (G.mem_treeDarts.1 hd').2 with h' | h'
  · exact Finset.disjoint_left.1 hW h h'
  · have := T'.vertexOf_inv_mem (G.inv d) h'
    rw [hG.inv_involutive, mem_insert] at this
    rcases this with h'' | h''
    · exact h₂ (h'' ▸ h)
    · exact Finset.disjoint_left.1 hW h h''
  · have := T'.vertexOf_inv_mem d h'
    rw [mem_insert] at this
    rcases this with h'' | h''
    · exact h₂ (h'' ▸ h)
    · exact Finset.disjoint_left.1 hW h h''
  · exact Finset.disjoint_left.1 hW h h'

end RootedTree

/-! ### Collapsing families -/

variable (G) in
/-- A **collapsing family** of `G`: a finite set `𝒯` of triples `(v, W, c)`, here pairs of a rooted
tree `(v, W)` and a colour `c`, such that each `(v, W)` is a collapsible tree of colour `c`; for
distinct members `(v, W, c)` and `(v', W', c')`, `W ∩ W' = ∅` and `v ∉ W'`; and every root `v` has
a dart lying in `D_{(v', W')}` for no member. -/
@[cluster_algebras "def_collapsing_family"]
structure IsCollapsingFamily (𝒯 : Finset (G.RootedTree × Shade)) : Prop where
  /-- Each member is a collapsible tree of its colour. -/
  isCollapsibleOfColour : ∀ p ∈ 𝒯, p.1.IsCollapsibleOfColour p.2
  /-- Distinct members have disjoint sets of non-root vertices. -/
  disjoint_nonRoot : ∀ p ∈ 𝒯, ∀ q ∈ 𝒯, p ≠ q → Disjoint p.1.nonRoot q.1.nonRoot
  /-- The root of a member is not a non-root vertex of another member. -/
  root_notMem_nonRoot : ∀ p ∈ 𝒯, ∀ q ∈ 𝒯, p ≠ q → p.1.root ∉ q.1.nonRoot
  /-- The root of each member has a dart lying in the tree of no member. -/
  exists_mem_root : ∀ p ∈ 𝒯, ∃ d ∈ p.1.root, ∀ q ∈ 𝒯, d ∉ q.1.darts

variable (G) in
/-- The set `D` of darts of the trees of a family: the union of the sets `D_{(v, W)}`. -/
def familyDarts (𝒯 : Finset (G.RootedTree × Shade)) : Finset H :=
  𝒯.biUnion fun p => p.1.darts

variable (G) in
/-- The set `K = (H \ D) ∪ {g_i : i ∈ I}` of darts kept by the collapse of a family, on which the
rotation of the collapse is the first return of `σ`. Here it is written `(H \ D) ∪ {legs}`. -/
def collapseCore (𝒯 : Finset (G.RootedTree × Shade)) : Set H :=
  {x | x ∉ G.familyDarts 𝒯 ∨ ∃ i, x = G.leg i}

variable (G) in
/-- The darts `H' = K ∪ {ḡ_i : i ∈ I}` of the collapse of a family, where `I` is the set of labels
whose leg lies in `D`. -/
def collapseDarts (𝒯 : Finset (G.RootedTree × Shade)) : Set H :=
  {x | x ∈ G.collapseCore 𝒯 ∨ ∃ i, G.leg i ∈ G.familyDarts 𝒯 ∧ x = G.inv (G.leg i)}

/-- Membership in `K` is decidable. -/
instance (𝒯 : Finset (G.RootedTree × Shade)) : DecidablePred (· ∈ G.collapseCore 𝒯) :=
  fun x => by unfold collapseCore; infer_instance

/-- Membership in the darts `H'` of the collapse is decidable. -/
instance (𝒯 : Finset (G.RootedTree × Shade)) : DecidablePred (· ∈ G.collapseDarts 𝒯) :=
  fun x => by unfold collapseDarts; infer_instance

/-- `K ⊆ H'`. -/
theorem collapseCore_subset (𝒯 : Finset (G.RootedTree × Shade)) :
    G.collapseCore 𝒯 ⊆ G.collapseDarts 𝒯 :=
  fun _ hx => Or.inl hx

/-- Every leg `g_i` lies in `K`. -/
theorem leg_mem_collapseCore (𝒯 : Finset (G.RootedTree × Shade)) (i : Fin b) :
    G.leg i ∈ G.collapseCore 𝒯 :=
  Or.inr ⟨i, rfl⟩

/-- The rotation `σ'` of the collapse, on all of `H`: the first return of `σ` to `K` on `K`, and
the identity elsewhere. -/
noncomputable def collapseRotAux (𝒯 : Finset (G.RootedTree × Shade)) : Perm H :=
  Perm.ofSubtype (firstReturnPerm G.rot (G.collapseCore 𝒯))

/-- On `K`, the rotation `σ'` is the first return of `σ` to `K`. -/
theorem collapseRotAux_apply_of_mem (𝒯 : Finset (G.RootedTree × Shade)) {x : H}
    (hx : x ∈ G.collapseCore 𝒯) :
    G.collapseRotAux 𝒯 x = firstReturn G.rot (G.collapseCore 𝒯) ⟨x, hx⟩ := by
  rw [collapseRotAux, Perm.ofSubtype_apply_of_mem _ hx, coe_firstReturnPerm]

/-- Outside `K`, the rotation `σ'` is the identity. -/
theorem collapseRotAux_apply_of_notMem (𝒯 : Finset (G.RootedTree × Shade)) {x : H}
    (hx : x ∉ G.collapseCore 𝒯) : G.collapseRotAux 𝒯 x = x :=
  Perm.ofSubtype_apply_of_not_mem _ hx

/-- The rotation `σ'` preserves the darts `H'` of the collapse. -/
theorem collapseRotAux_mem_iff (𝒯 : Finset (G.RootedTree × Shade)) (x : H) :
    G.collapseRotAux 𝒯 x ∈ G.collapseDarts 𝒯 ↔ x ∈ G.collapseDarts 𝒯 := by
  by_cases hx : x ∈ G.collapseCore 𝒯
  · rw [G.collapseRotAux_apply_of_mem 𝒯 hx]
    exact ⟨fun _ => G.collapseCore_subset 𝒯 hx,
      fun _ => G.collapseCore_subset 𝒯 (firstReturn _ _ _).2⟩
  · rw [G.collapseRotAux_apply_of_notMem 𝒯 hx]

open scoped Classical in
/-- The colouring `κ'` of the collapse, on darts: the colour `c_i` of the member whose tree
contains the leg `g_i` at the dart `ḡ_i`, and the colour of `G` elsewhere. -/
noncomputable def collapseColour (𝒯 : Finset (G.RootedTree × Shade)) (x : H) : Shade :=
  if h : ∃ p ∈ 𝒯, ∃ i, G.leg i ∈ p.1.darts ∧ x = G.inv (G.leg i) then h.choose.2
  else G.colour x

variable (G) in
/-- **The collapse `G/𝒯` of a family of trees**. With `D` the union of the sets `D_{(v, W)}` of the
members and `I` the set of labels `i` whose leg `g_i` lies in `D` (that is, such that `β(i)` is the
root of a member), the collapse has the darts `H' = (H \ D) ∪ {g_i, ḡ_i : i ∈ I}`; the restriction
of the involution; the rotation `σ'` which is the first return of `σ` to
`K = (H \ D) ∪ {g_i : i ∈ I}` on `K` and fixes each `ḡ_i`; the boundary arcs `B`; the colour `c_i`
of the member with root `β(i)` at `ḡ_i` and the colour of `G` elsewhere; and the labelling of
`G`. -/
@[cluster_algebras "def_family_collapse"]
noncomputable def collapse (𝒯 : Finset (G.RootedTree × Shade)) :
    PlabicData (G.collapseDarts 𝒯) b where
  inv := firstReturnPerm G.inv (G.collapseDarts 𝒯)
  rot := (G.collapseRotAux 𝒯).subtypePerm (G.collapseRotAux_mem_iff 𝒯)
  bdry := G.bdry.subtype (· ∈ G.collapseDarts 𝒯)
  colour x := G.collapseColour 𝒯 x
  leg i := ⟨G.leg i, G.collapseCore_subset 𝒯 (G.leg_mem_collapseCore 𝒯 i)⟩

/-! ### The vertices of a collapse -/

section CollapseVertices

variable {𝒯 : Finset (G.RootedTree × Shade)}

/-- A dart lies in `D` if and only if it is a dart of the tree of some member. -/
theorem mem_familyDarts {x : H} : x ∈ G.familyDarts 𝒯 ↔ ∃ p ∈ 𝒯, x ∈ p.1.darts :=
  mem_biUnion

/-- At a boundary vertex, the only dart outside `B` is a leg. -/
theorem IsPlabicGraph.exists_eq_leg_of_isBoundaryVertex (hG : G.IsPlabicGraph) {d : H}
    (hd : G.IsBoundaryVertex (G.vertexOf d)) (hdB : d ∉ G.bdry) : ∃ j, d = G.leg j := by
  obtain ⟨j, hj⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hd)
  have hmem : d ∈ (G.bvertex j).filter (· ∉ G.bdry) := by
    rw [mem_filter, hj]
    exact ⟨G.self_mem_vertexOf d, hdB⟩
  rw [hG.filter_bvertex_notMem_bdry, mem_singleton] at hmem
  exact ⟨j, hmem⟩

/-- In a plabic graph, `D` is closed under `d ↦ d̄`. -/
theorem inv_mem_familyDarts (hG : G.IsPlabicGraph) {x : H} (hx : x ∈ G.familyDarts 𝒯) :
    G.inv x ∈ G.familyDarts 𝒯 := by
  obtain ⟨p, hp, hxp⟩ := mem_familyDarts.1 hx
  exact mem_familyDarts.2 ⟨p, hp, p.1.inv_mem_darts hG hxp⟩

/-- A boundary arc does not lie in `D`. -/
theorem notMem_familyDarts_of_mem_bdry {x : H} (hx : x ∈ G.bdry) : x ∉ G.familyDarts 𝒯 :=
  fun h => by
    obtain ⟨p, -, hxp⟩ := mem_familyDarts.1 h
    exact p.1.notMem_bdry_of_mem_darts hxp hx

/-- Every boundary arc lies in `K`. -/
theorem mem_collapseCore_of_mem_bdry {x : H} (hx : x ∈ G.bdry) : x ∈ G.collapseCore 𝒯 :=
  Or.inl (notMem_familyDarts_of_mem_bdry hx)

/-- The dart `ḡ_i` across a leg `g_i ∈ D_T` lies at a non-root vertex of `T`. -/
theorem RootedTree.vertexOf_inv_leg_mem (hG : G.IsPlabicGraph) (T : G.RootedTree) {i : Fin b}
    (h : G.leg i ∈ T.darts) : G.vertexOf (G.inv (G.leg i)) ∈ T.nonRoot := by
  rcases (G.mem_treeDarts.1 h).2 with h' | h'
  · exact absurd (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))
      (G.mem_internalVertices.1 (T.nonRoot_subset h')).2
  · exact h'

/-- A dart at a non-root vertex of a tree is not a leg. -/
theorem RootedTree.ne_leg_of_vertexOf_mem (hG : G.IsPlabicGraph) (T : G.RootedTree) {x : H}
    (hx : G.vertexOf x ∈ T.nonRoot) (j : Fin b) : x ≠ G.leg j := by
  rintro rfl
  exact (G.mem_internalVertices.1 (T.nonRoot_subset hx)).2
    (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j))

/-- `ḡ_i ∉ K` when `g_i ∈ D`. -/
theorem inv_leg_notMem_collapseCore (hG : G.IsPlabicGraph) {i : Fin b}
    (h : G.leg i ∈ G.familyDarts 𝒯) : G.inv (G.leg i) ∉ G.collapseCore 𝒯 := by
  obtain ⟨p, hp, hip⟩ := mem_familyDarts.1 h
  rintro (h' | ⟨j, hj⟩)
  · exact h' (inv_mem_familyDarts hG h)
  · exact p.1.ne_leg_of_vertexOf_mem hG (p.1.vertexOf_inv_leg_mem hG hip) j hj

/-- In a plabic graph, the darts `H'` of the collapse are closed under `d ↦ d̄`. -/
theorem inv_mem_collapseDarts (hG : G.IsPlabicGraph) {x : H} (hx : x ∈ G.collapseDarts 𝒯) :
    G.inv x ∈ G.collapseDarts 𝒯 := by
  have hinv := hG.inv_involutive
  rcases hx with (hx | ⟨i, rfl⟩) | ⟨i, hi, rfl⟩
  · exact Or.inl (Or.inl fun h => hx (by simpa [hinv x] using inv_mem_familyDarts hG h))
  · by_cases hi : G.leg i ∈ G.familyDarts 𝒯
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl (Or.inl fun h => hi (by simpa [hinv _] using inv_mem_familyDarts hG h))
  · rw [hinv]
    exact Or.inl (G.leg_mem_collapseCore 𝒯 i)

/-- The involution of the collapse is the restriction of `d ↦ d̄`. -/
theorem coe_collapse_inv (hG : G.IsPlabicGraph) (x : G.collapseDarts 𝒯) :
    ((G.collapse 𝒯).inv x : H) = G.inv x :=
  coe_firstReturn_of_apply_mem (inv_mem_collapseDarts hG x.2)

/-- On `K`, the rotation of the collapse is the first return of `σ` to `K`. -/
theorem coe_collapse_rot_of_mem {x : G.collapseDarts 𝒯} (hx : (x : H) ∈ G.collapseCore 𝒯) :
    ((G.collapse 𝒯).rot x : H) = firstReturn G.rot (G.collapseCore 𝒯) ⟨x, hx⟩ :=
  G.collapseRotAux_apply_of_mem 𝒯 hx

/-- The rotation of the collapse fixes each dart outside `K`. -/
theorem coe_collapse_rot_of_notMem {x : G.collapseDarts 𝒯} (hx : (x : H) ∉ G.collapseCore 𝒯) :
    ((G.collapse 𝒯).rot x : H) = x :=
  G.collapseRotAux_apply_of_notMem 𝒯 hx

/-- The boundary arcs of the collapse are those of `G`. -/
theorem mem_collapse_bdry {x : G.collapseDarts 𝒯} :
    x ∈ (G.collapse 𝒯).bdry ↔ (x : H) ∈ G.bdry :=
  mem_subtype

private theorem coe_collapse_rot_pow_of_mem {x : G.collapseDarts 𝒯}
    (hx : (x : H) ∈ G.collapseCore 𝒯) (n : ℕ) :
    (((G.collapse 𝒯).rot ^ n) x : H) =
      ((firstReturnPerm G.rot (G.collapseCore 𝒯) ^ n) ⟨x, hx⟩ : H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmem : (((G.collapse 𝒯).rot ^ n) x : H) ∈ G.collapseCore 𝒯 := by
      rw [ih]
      exact Subtype.property _
    rw [pow_succ', Perm.mul_apply, coe_collapse_rot_of_mem hmem, pow_succ', Perm.mul_apply,
      coe_firstReturnPerm]
    congr 2
    exact Subtype.ext ih

/-- For `x ∈ K`, the vertex of `G/𝒯` containing `x` is `v(x) ∩ K`. -/
theorem map_collapse_vertexOf_of_mem {x : G.collapseDarts 𝒯} (hx : (x : H) ∈ G.collapseCore 𝒯) :
    ((G.collapse 𝒯).vertexOf x).map (Embedding.subtype _) =
      (G.vertexOf x).filter (· ∈ G.collapseCore 𝒯) := by
  ext z
  simp only [mem_map, RotationSystem.mem_vertexOf, Embedding.coe_subtype, mem_filter]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨n, rfl⟩ := hw.exists_nat_pow_eq
    rw [coe_collapse_rot_pow_of_mem hx]
    exact ⟨(sameCycle_firstReturnPerm_iff G.rot (G.collapseCore 𝒯)
      (y := ⟨x, hx⟩) (y' := (firstReturnPerm G.rot (G.collapseCore 𝒯) ^ n) ⟨x, hx⟩)).1
      ⟨n, by rw [zpow_natCast]⟩, Subtype.property _⟩
  · rintro ⟨hz, hzK⟩
    obtain ⟨n, hn⟩ := ((sameCycle_firstReturnPerm_iff G.rot (G.collapseCore 𝒯)
      (y := ⟨x, hx⟩) (y' := ⟨z, hzK⟩)).2 hz).exists_nat_pow_eq
    refine ⟨((G.collapse 𝒯).rot ^ n) x, ⟨n, by rw [zpow_natCast]⟩, ?_⟩
    rw [coe_collapse_rot_pow_of_mem hx, hn]

/-- For `i ∈ I`, the vertex of `G/𝒯` containing `ḡ_i` is `{ḡ_i}`. -/
theorem collapse_vertexOf_inv_leg (hG : G.IsPlabicGraph) {x : G.collapseDarts 𝒯} {i : Fin b}
    (hi : G.leg i ∈ G.familyDarts 𝒯) (hx : (x : H) = G.inv (G.leg i)) :
    (G.collapse 𝒯).vertexOf x = {x} := by
  have hfix : (G.collapse 𝒯).rot x = x :=
    Subtype.ext (coe_collapse_rot_of_notMem (hx ▸ inv_leg_notMem_collapseCore hG hi))
  ext z
  rw [RotationSystem.mem_vertexOf, mem_singleton]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    exact Perm.pow_apply_eq_self_of_apply_eq_self hfix n
  · rintro rfl
    exact Perm.SameCycle.refl _ _

variable (hG : G.IsPlabicGraph) (h𝒯 : G.IsCollapsingFamily 𝒯)

include hG h𝒯

omit h𝒯 in
/-- A dart of `D` at a vertex `u` lying in no `W` is a dart of the interval of a member with root
`u`. -/
theorem exists_root_eq_of_mem_familyDarts {d : H} (hd : d ∈ G.familyDarts 𝒯)
    (hU : ∀ p ∈ 𝒯, G.vertexOf d ∉ p.1.nonRoot) :
    ∃ p ∈ 𝒯, p.1.root = G.vertexOf d ∧ d ∈ p.1.darts := by
  obtain ⟨p, hp, hdp⟩ := mem_familyDarts.1 hd
  rcases p.1.vertexOf_mem_or_eq_root hG hdp with h | h
  · exact absurd h (hU p hp)
  · exact ⟨p, hp, h.symm, hdp⟩

omit h𝒯 in
/-- A vertex `u ∉ U` that is a boundary vertex, or is the root of no member, satisfies
`u ∩ K = u`. -/
@[cluster_algebras "lem_family_collapse_vertices"]
theorem filter_vertexOf_mem_collapseCore_of_not {d : H}
    (hU : ∀ p ∈ 𝒯, G.vertexOf d ∉ p.1.nonRoot)
    (h : G.IsBoundaryVertex (G.vertexOf d) ∨ ∀ p ∈ 𝒯, p.1.root ≠ G.vertexOf d) :
    (G.vertexOf d).filter (· ∈ G.collapseCore 𝒯) = G.vertexOf d := by
  refine filter_true_of_mem fun y hy => ?_
  have hvy := G.vertexOf_eq_of_mem hy
  by_cases hyD : y ∈ G.familyDarts 𝒯
  · obtain ⟨p, hp, hroot, hyp⟩ := exists_root_eq_of_mem_familyDarts hG hyD (hvy ▸ hU)
    rcases h with h | h
    · rw [← hvy] at h
      obtain ⟨j, rfl⟩ := hG.exists_eq_leg_of_isBoundaryVertex h (p.1.notMem_bdry_of_mem_darts hyp)
      exact G.leg_mem_collapseCore 𝒯 j
    · exact absurd (hroot.trans hvy) (h p hp)
  · exact Or.inl hyD

omit h𝒯 in
/-- For an internal vertex `u ∉ U`, `u ∩ K` is `u` minus the darts of the intervals of the members
with root `u`. -/
@[cluster_algebras "lem_family_collapse_vertices"]
theorem filter_vertexOf_mem_collapseCore_of_internal {d : H}
    (hU : ∀ p ∈ 𝒯, G.vertexOf d ∉ p.1.nonRoot) (h : ¬G.IsBoundaryVertex (G.vertexOf d)) :
    (G.vertexOf d).filter (· ∈ G.collapseCore 𝒯) =
      (G.vertexOf d).filter fun y => ∀ p ∈ 𝒯, p.1.root = G.vertexOf d → y ∉ p.1.darts := by
  refine filter_congr fun y hy => ?_
  have hvy := G.vertexOf_eq_of_mem hy
  constructor
  · rintro (hyD | ⟨j, rfl⟩) p hp _ hyp
    · exact hyD (mem_familyDarts.2 ⟨p, hp, hyp⟩)
    · rw [← hvy] at h
      exact h (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j))
  · intro hy'
    refine Or.inl fun hyD => ?_
    obtain ⟨p, hp, hroot, hyp⟩ := exists_root_eq_of_mem_familyDarts hG hyD (hvy ▸ hU)
    exact hy' p hp (hroot.trans hvy) hyp

/-- For a vertex `u ∉ U`, `u ∩ K` is nonempty. -/
@[cluster_algebras "lem_family_collapse_vertices"]
theorem filter_vertexOf_mem_collapseCore_nonempty {d : H}
    (hU : ∀ p ∈ 𝒯, G.vertexOf d ∉ p.1.nonRoot) :
    ((G.vertexOf d).filter (· ∈ G.collapseCore 𝒯)).Nonempty := by
  by_cases h : G.IsBoundaryVertex (G.vertexOf d) ∨ ∀ p ∈ 𝒯, p.1.root ≠ G.vertexOf d
  · rw [filter_vertexOf_mem_collapseCore_of_not hG hU h]
    exact ⟨d, G.self_mem_vertexOf d⟩
  · push Not at h
    obtain ⟨-, p, hp, hroot⟩ := h
    obtain ⟨y, hy, hy'⟩ := h𝒯.exists_mem_root p hp
    refine ⟨y, mem_filter.2 ⟨hroot ▸ hy, Or.inl fun hyD => ?_⟩⟩
    obtain ⟨q, hq, hyq⟩ := mem_familyDarts.1 hyD
    exact hy' q hq hyq

omit hG h𝒯 in
/-- For every vertex `u`, `u ∩ K` contains a dart of `B` if and only if `u` does. -/
@[cluster_algebras "lem_family_collapse_vertices"]
theorem exists_mem_bdry_filter_vertexOf_iff {d : H} :
    (∃ y ∈ (G.vertexOf d).filter (· ∈ G.collapseCore 𝒯), y ∈ G.bdry) ↔
      ∃ y ∈ G.vertexOf d, y ∈ G.bdry :=
  ⟨fun ⟨y, hy, hyB⟩ => ⟨y, (mem_filter.1 hy).1, hyB⟩,
    fun ⟨y, hy, hyB⟩ => ⟨y, mem_filter.2 ⟨hy, mem_collapseCore_of_mem_bdry hyB⟩, hyB⟩⟩

omit h𝒯 in
/-- A dart of `K` does not lie at a vertex of `U`. -/
theorem vertexOf_notMem_nonRoot_of_mem_collapseCore {x : H} (hx : x ∈ G.collapseCore 𝒯) :
    ∀ p ∈ 𝒯, G.vertexOf x ∉ p.1.nonRoot := by
  intro p hp hxp
  rcases hx with hx | ⟨j, rfl⟩
  · exact hx (mem_familyDarts.2 ⟨p, hp, p.1.mem_darts_of_vertexOf_mem hxp⟩)
  · exact p.1.ne_leg_of_vertexOf_mem hG hxp j rfl

/-- **The vertices of a collapse**: the orbits of the rotation `σ'` of `G/𝒯`, read as sets of darts
of `G`, are the sets `u ∩ K` for the vertices `u` of `G` lying in no set `W` of a member, and the
sets `{ḡ_i}` for `i ∈ I`. -/
@[cluster_algebras "lem_family_collapse_vertices"]
theorem image_collapse_vertices :
    (G.collapse 𝒯).vertices.image (Finset.map (Embedding.subtype _)) =
      (G.vertices.filter fun u => ∀ p ∈ 𝒯, u ∉ p.1.nonRoot).image
          (Finset.filter (· ∈ G.collapseCore 𝒯)) ∪
        (univ.filter fun i => G.leg i ∈ G.familyDarts 𝒯).image fun i => {G.inv (G.leg i)} := by
  ext s
  simp only [mem_image, RotationSystem.mem_vertices, mem_union, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    by_cases hx : (x : H) ∈ G.collapseCore 𝒯
    · exact Or.inl ⟨G.vertexOf x, ⟨⟨x, rfl⟩, vertexOf_notMem_nonRoot_of_mem_collapseCore hG hx⟩,
        (map_collapse_vertexOf_of_mem hx).symm⟩
    · rcases x.2 with hx' | ⟨i, hi, hxi⟩
      · exact absurd hx' hx
      · refine Or.inr ⟨i, hi, ?_⟩
        rw [collapse_vertexOf_inv_leg hG hi hxi, map_singleton, Embedding.coe_subtype, hxi]
  · rintro (⟨u, ⟨⟨d, rfl⟩, hU⟩, rfl⟩ | ⟨i, hi, rfl⟩)
    · obtain ⟨y, hy⟩ := filter_vertexOf_mem_collapseCore_nonempty hG h𝒯 hU
      obtain ⟨hyd, hyK⟩ := mem_filter.1 hy
      refine ⟨_, ⟨⟨y, G.collapseCore_subset 𝒯 hyK⟩, rfl⟩, ?_⟩
      rw [map_collapse_vertexOf_of_mem (x := ⟨y, _⟩) hyK]
      simp only
      rw [G.vertexOf_eq_of_mem hyd]
    · refine ⟨_, ⟨⟨G.inv (G.leg i), Or.inr ⟨i, hi, rfl⟩⟩, rfl⟩, ?_⟩
      rw [collapse_vertexOf_inv_leg hG hi rfl, map_singleton]
      rfl

end CollapseVertices

end PlabicData

end ClusterAlgebras
