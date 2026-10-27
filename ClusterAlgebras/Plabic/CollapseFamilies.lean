/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CollapseCuts

/-!
# Transporting and merging collapsing families

Constructions on collapsing families of rooted trees: transporting trees and families along
embeddings of plabic tuples, replacing the trees of a family by their branches, and merging the
trees at a thin root into one tree.

## Main definitions

* `ClusterAlgebras.PlabicData.transportFamily`: the transport of a family along an embedding.
* `ClusterAlgebras.PlabicData.branchFamily`: the family of the branches of the trees of a family.
* `ClusterAlgebras.PlabicData.mergeTree`: the tree obtained by merging the trees at a root.

## Main results

* `ClusterAlgebras.PlabicData.isCollapsingFamily_transportFamily`: a transported family is
  collapsing.
* `ClusterAlgebras.PlabicData.isCollapsingFamily_branchFamily`,
  `ClusterAlgebras.PlabicData.collapseMatch_branchFamily`: the branch family is collapsing and has
  the same collapse.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

namespace PlabicData

/-! ### Transporting trees and families -/

section Transport

variable {H H' : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {G : PlabicData H b} {G' : PlabicData H' b}

/-- The plabic graph of a transported tree is isomorphic to `P_T`, for boundary roots. -/
private theorem RootedTree.IsEmbedding.tree_plabicData_isomorphic_of_isBoundaryVertex
    {T : G.RootedTree} {f : H → H'} (hf : T.IsEmbedding G' f)
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (hv : G.IsBoundaryVertex T.root)
    (hv' : G'.IsBoundaryVertex (G'.vertexOf (f T.intervalStart))) :
    T.plabicData.Isomorphic (hf.tree hG hG').plabicData := by
  set T' := hf.tree hG hG' with hT'
  have hv'' : G'.IsBoundaryVertex T'.root := hv'
  have hD' : T'.darts = T.darts.image f := hf.tree_darts hG hG'
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
      · have : d' ∈ T.darts.image f := by rwa [← hD']
        obtain ⟨d, hd, rfl⟩ := mem_image.1 this
        exact ⟨⟨.inl d, hd⟩, rfl⟩
      · refine ⟨⟨.inr l, ?_⟩, rfl⟩
        rcases l with _ | _ | _ | _
        · trivial
        · trivial
        · exact absurd hv'' hx
        · exact absurd hv'' hx⟩
  have he : ∀ x, ((e x : T'.Dart) : H' ⊕ LollipopDart) = Sum.map f id x.1 := fun _ => rfl
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
      simp only [RootedTree.rotAux, if_pos hv, if_pos hv'']
      rw [show T'.intervalStart = f T.intervalStart from hf.tree_intervalStart hG hG']
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
      rw [hf.tree_intervalStart hG hG']
      exact hf.colour _ T.intervalStart_mem_darts
  · change ((e T.legDart : T'.Dart) : H' ⊕ LollipopDart) = (T'.legDart : H' ⊕ LollipopDart)
    rw [he, RootedTree.legDart, RootedTree.legDart, dif_pos hv, dif_pos hv'']
    change Sum.inl (f T.intervalStart) = Sum.inl T'.intervalStart
    rw [hf.tree_intervalStart hG hG']

/-- The plabic graph of a transported tree is isomorphic to `P_T`. -/
private theorem RootedTree.IsEmbedding.tree_plabicData_isomorphic'
    {T : G.RootedTree} {f : H → H'} (hf : T.IsEmbedding G' f)
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (hv : G'.IsBoundaryVertex (G'.vertexOf (f T.intervalStart)) ↔ G.IsBoundaryVertex T.root) :
    T.plabicData.Isomorphic (hf.tree hG hG').plabicData := by
  by_cases hb : G.IsBoundaryVertex T.root
  · exact hf.tree_plabicData_isomorphic_of_isBoundaryVertex hG hG' hb (hv.2 hb)
  · exact hf.tree_plabicData_isomorphic hG hG' hb (mt hv.1 hb)

/-- The images of the non-root vertices of `T` are as many as the non-root vertices. -/
private theorem RootedTree.IsEmbedding.card_tree_nonRoot
    {T : G.RootedTree} {f : H → H'} (hf : T.IsEmbedding G' f)
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    (hf.tree hG hG').nonRoot.card = T.nonRoot.card := by
  change (T.nonRoot.image (Finset.image f)).card = _
  refine card_image_of_injOn fun w hw w' hw' heq => ?_
  have hw₀ := T.nonRoot_subset hw
  obtain ⟨d, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw₀).1
  have hd : f d ∈ w'.image f := heq ▸ mem_image_of_mem f (G.self_mem_vertexOf d)
  obtain ⟨d', hd', hfd⟩ := mem_image.1 hd
  have h1 : d ∈ T.darts := T.mem_darts_of_vertexOf_mem hw
  have hw'₀ := T.nonRoot_subset hw'
  obtain ⟨d'', rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hw'₀).1
  have h2 : d' ∈ T.darts := T.mem_darts_of_vertexOf_mem (by
    rwa [G.vertexOf_eq_of_mem hd'])
  have := hf.injOn h2 h1 hfd
  subst this
  exact G.vertexOf_eq_of_mem hd'

/-- A transported collapsible tree is collapsible of the same colour, when the root stays internal
or boundary, and an internal root keeps its colour. -/
theorem RootedTree.IsEmbedding.isCollapsibleOfColour
    {T : G.RootedTree} {f : H → H'} (hf : T.IsEmbedding G' f)
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) {c : Shade} (hT : T.IsCollapsibleOfColour c)
    (hv : G'.IsBoundaryVertex (G'.vertexOf (f T.intervalStart)) ↔ G.IsBoundaryVertex T.root) :
    (hf.tree hG hG').IsCollapsibleOfColour c := by
  obtain ⟨θ⟩ := hf.tree_plabicData_isomorphic' hG hG' hv
  refine ⟨(hf.tree hG hG').isPlabicGraph_plabicData hG', ?_, ?_⟩
  · exact (PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
      (G := ⟨_, _, (hf.tree hG hG').isPlabicGraph_plabicData hG'⟩)
      (G' := ⟨_, _, hT.isPlabicGraph⟩) ⟨θ⟩).trans hT.moveEquivalent
  · rcases hT.root_cases with ⟨hb, hc⟩ | ⟨hb, h2⟩
    · refine Or.inl ⟨mt hv.1 hb, fun d hd => ?_⟩
      have hb' : ¬G'.IsBoundaryVertex (G'.vertexOf (f T.intervalStart)) := mt hv.1 hb
      rw [hG'.colour_eq_of_mem_vertexOf hb' hd, hf.colour _ T.intervalStart_mem_darts]
      exact hc _ T.intervalStart_mem_root
    · exact Or.inr ⟨hv.2 hb, by rwa [hf.card_tree_nonRoot hG hG']⟩

/-- Two members of a collapsing family whose trees share a dart are equal. -/
theorem IsCollapsingFamily.eq_of_mem_darts (hG : G.IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯) {p q : G.RootedTree × Shade}
    (hp : p ∈ 𝒯) (hq : q ∈ 𝒯) {x : H} (hxp : x ∈ p.1.darts) (hxq : x ∈ q.1.darts) : p = q := by
  by_contra hne
  exact disjoint_left.1 (p.1.disjoint_darts hG (h𝒯.disjoint_nonRoot _ hp _ hq hne)
    (h𝒯.root_notMem_nonRoot _ hq _ hp (Ne.symm hne))) hxp hxq

/-- A subfamily of a collapsing family is a collapsing family. -/
theorem IsCollapsingFamily.subset {𝒯 𝒯' : Finset (G.RootedTree × Shade)}
    (h𝒯 : G.IsCollapsingFamily 𝒯) (h : 𝒯' ⊆ 𝒯) : G.IsCollapsingFamily 𝒯' where
  isCollapsibleOfColour p hp := h𝒯.isCollapsibleOfColour p (h hp)
  disjoint_nonRoot p hp q hq hne := h𝒯.disjoint_nonRoot p (h hp) q (h hq) hne
  root_notMem_nonRoot p hp q hq hne := h𝒯.root_notMem_nonRoot p (h hp) q (h hq) hne
  exists_mem_root p hp := by
    obtain ⟨d, hd, hdq⟩ := h𝒯.exists_mem_root p (h hp)
    exact ⟨d, hd, fun q hq => hdq q (h hq)⟩

/-- A vertex in `W` has a dart. -/
private theorem RootedTree.exists_mem_of_mem_nonRoot {T : G.RootedTree} {w : Finset H}
    (hw : w ∈ T.nonRoot) : ∃ y, y ∈ w :=
  (RootedTree.IsEmbedding.exists_vertexOf_eq hw).imp fun d (hd : G.vertexOf d = w) =>
    hd ▸ G.self_mem_vertexOf d

open scoped Classical in
/-- The image of a family along embeddings of its trees into `G'`. -/
noncomputable def transportFamily (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    {𝒯 : Finset (G.RootedTree × Shade)} {f : H → H'} (hemb : ∀ p ∈ 𝒯, p.1.IsEmbedding G' f) :
    Finset (G'.RootedTree × Shade) :=
  𝒯.attach.image fun p => ((hemb p.1 p.2).tree hG hG', p.1.2)

section TransportFamily

variable (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)}
  {f : H → H'} (hemb : ∀ p ∈ 𝒯, p.1.IsEmbedding G' f)

/-- A pair lies in the transported family iff it is the transport of a member of `𝒯`. -/
theorem mem_transportFamily {p' : G'.RootedTree × Shade} :
    p' ∈ transportFamily hG hG' hemb ↔ ∃ p, ∃ hp : p ∈ 𝒯, ((hemb p hp).tree hG hG', p.2) = p' := by
  classical
  unfold transportFamily
  rw [mem_image]
  constructor
  · rintro ⟨⟨p, hp⟩, -, h⟩
    exact ⟨p, hp, h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨⟨p, hp⟩, mem_attach _ _, h⟩

/-- The darts of the transported family are the images under `f` of the darts of `𝒯`. -/
theorem mem_familyDarts_transportFamily {x : H'} :
    x ∈ G'.familyDarts (transportFamily hG hG' hemb) ↔ ∃ d ∈ G.familyDarts 𝒯, f d = x := by
  rw [mem_familyDarts]
  constructor
  · rintro ⟨p', hp', hx⟩
    obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hp'
    change x ∈ ((hemb p hp).tree hG hG').darts at hx
    rw [(hemb p hp).tree_darts hG hG'] at hx
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
    exact ⟨d, mem_familyDarts.2 ⟨p, hp, hd⟩, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨p, hp, hdp⟩ := mem_familyDarts.1 hd
    refine ⟨_, (mem_transportFamily hG hG' hemb).2 ⟨p, hp, rfl⟩, ?_⟩
    change f d ∈ ((hemb p hp).tree hG hG').darts
    rw [(hemb p hp).tree_darts hG hG']
    exact mem_image_of_mem f hdp

/-- The members of the transported family whose trees contain the image of a dart `x` of a set `A`
on which `f` is injective are the images of the members whose trees contain `x`. -/
theorem transportFamily_colour {A : Set H} (hA : Set.InjOn f A)
    (hDA : ∀ x ∈ G.familyDarts 𝒯, x ∈ A) {x : H} (hx : x ∈ A) {p' : G'.RootedTree × Shade}
    (hp' : p' ∈ transportFamily hG hG' hemb) (hxp' : f x ∈ p'.1.darts) :
    ∃ p ∈ 𝒯, x ∈ p.1.darts ∧ p.2 = p'.2 := by
  obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hp'
  change f x ∈ ((hemb p hp).tree hG hG').darts at hxp'
  rw [(hemb p hp).tree_darts hG hG'] at hxp'
  obtain ⟨d, hd, hdx⟩ := mem_image.1 hxp'
  have := hA (hDA d (mem_familyDarts.2 ⟨p, hp, hd⟩)) hx hdx
  subst this
  exact ⟨p, hp, hd, rfl⟩

/-- **Transporting a collapsing family**, with the free darts of the roots given in `G'`. -/
theorem isCollapsingFamily_transportFamily_of_free (h𝒯 : G.IsCollapsingFamily 𝒯)
    {A : Set H} (hA : Set.InjOn f A) (hDA : ∀ x ∈ G.familyDarts 𝒯, x ∈ A)
    (hroot : ∀ p ∈ 𝒯, G'.IsBoundaryVertex (G'.vertexOf (f p.1.intervalStart)) ↔
      G.IsBoundaryVertex p.1.root)
    (hfree : ∀ p ∈ 𝒯, ∃ a ∈ G'.vertexOf (f p.1.intervalStart),
      a ∉ G'.familyDarts (transportFamily hG hG' hemb)) :
    G'.IsCollapsingFamily (transportFamily hG hG' hemb) := by
  have hnr : ∀ p (hp : p ∈ 𝒯) {w'}, w' ∈ ((hemb p hp).tree hG hG').nonRoot →
      ∃ w ∈ p.1.nonRoot, w' = w.image f := by
    intro p hp w' hw'
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hw'
    exact ⟨w, hw, rfl⟩
  have hdw : ∀ p ∈ 𝒯, ∀ w ∈ p.1.nonRoot, ∀ d ∈ w, d ∈ G.familyDarts 𝒯 := by
    intro p hp w hw d hd
    refine mem_familyDarts.2 ⟨p, hp, p.1.mem_darts_of_vertexOf_mem ?_⟩
    obtain ⟨e, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 (p.1.nonRoot_subset hw)).1
    rw [G.vertexOf_eq_of_mem hd]
    exact hw
  have hvw : ∀ p ∈ 𝒯, ∀ w ∈ p.1.nonRoot, ∀ d ∈ w, G.vertexOf d = w := by
    intro p hp w hw d hd
    obtain ⟨e, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 (p.1.nonRoot_subset hw)).1
    exact G.vertexOf_eq_of_mem hd
  have hne : ∀ p (hp : p ∈ 𝒯) q (hq : q ∈ 𝒯),
      (((hemb p hp).tree hG hG', p.2) : G'.RootedTree × Shade) ≠ ((hemb q hq).tree hG hG', q.2) →
      p ≠ q := by
    rintro p hp q hq h rfl
    exact h rfl
  refine ⟨fun p' hp' => ?_, fun p' hp' q' hq' hpq => ?_, fun p' hp' q' hq' hpq => ?_,
    fun p' hp' => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hp'
    exact (hemb p hp).isCollapsibleOfColour hG hG' (h𝒯.isCollapsibleOfColour p hp) (hroot p hp)
  · obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hp'
    obtain ⟨q, hq, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hq'
    have hpq' := hne p hp q hq hpq
    rw [Finset.disjoint_left]
    intro w' hw₁' hw₂'
    obtain ⟨w₁, hw₁, hw₁e⟩ := hnr p hp hw₁'
    obtain ⟨w₂, hw₂, heq⟩ := hnr q hq hw₂'
    obtain ⟨d, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 (p.1.nonRoot_subset hw₁)).1
    have : f d ∈ w₂.image f := heq ▸ hw₁e ▸ mem_image_of_mem f (G.self_mem_vertexOf d)
    obtain ⟨d', hd', hfd⟩ := mem_image.1 this
    have := hA (hDA _ (hdw q hq w₂ hw₂ d' hd'))
      (hDA _ (hdw p hp _ hw₁ d (G.self_mem_vertexOf d))) hfd
    subst this
    exact disjoint_left.1 (h𝒯.disjoint_nonRoot p hp q hq hpq') hw₁
      ((hvw q hq w₂ hw₂ d' hd') ▸ hw₂)
  · obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hp'
    obtain ⟨q, hq, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hq'
    have hpq' := hne p hp q hq hpq
    intro h
    obtain ⟨w₂, hw₂, heq⟩ := hnr q hq h
    change G'.vertexOf (f p.1.intervalStart) = w₂.image f at heq
    have : f p.1.intervalStart ∈ w₂.image f := heq ▸ G'.self_mem_vertexOf _
    obtain ⟨d', hd', hfd⟩ := mem_image.1 this
    have := hA (hDA _ (hdw q hq w₂ hw₂ d' hd'))
      (hDA _ (mem_familyDarts.2 ⟨p, hp, p.1.intervalStart_mem_darts⟩)) hfd
    subst this
    refine h𝒯.root_notMem_nonRoot p hp q hq hpq' ?_
    rw [p.1.root_eq_vertexOf_intervalStart, hvw q hq w₂ hw₂ _ hd']
    exact hw₂
  · obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hG hG' hemb).1 hp'
    obtain ⟨a, hav, haD⟩ := hfree p hp
    exact ⟨a, hav, fun q' hq' haq => haD (mem_familyDarts.2 ⟨q', hq', haq⟩)⟩

/-- **Transporting a collapsing family** along embeddings of its trees, injective on a set `A`
containing the darts of the trees, when the roots stay internal or boundary and keep a dart of `A`
outside the trees. -/
theorem isCollapsingFamily_transportFamily (h𝒯 : G.IsCollapsingFamily 𝒯) {A : Set H}
    (hA : Set.InjOn f A) (hDA : ∀ x ∈ G.familyDarts 𝒯, x ∈ A)
    (hroot : ∀ p ∈ 𝒯, G'.IsBoundaryVertex (G'.vertexOf (f p.1.intervalStart)) ↔
      G.IsBoundaryVertex p.1.root)
    (hfree : ∀ p ∈ 𝒯, ∃ a ∈ A, a ∉ G.familyDarts 𝒯 ∧ f a ∈ G'.vertexOf (f p.1.intervalStart)) :
    G'.IsCollapsingFamily (transportFamily hG hG' hemb) :=
  isCollapsingFamily_transportFamily_of_free hG hG' hemb h𝒯 hA hDA hroot fun p hp => by
    obtain ⟨a, haA, haD, hav⟩ := hfree p hp
    refine ⟨f a, hav, fun h => ?_⟩
    obtain ⟨d, hd, hdx⟩ := (mem_familyDarts_transportFamily hG hG' hemb).1 h
    have := hA (hDA d hd) haA hdx
    subst this
    exact haD hd

open scoped Classical in
/-- **Adding a tree to a transported collapsing family.** The trees of the collapsing family `𝒯o`
are transported into `G'`, and the tree `T'` of `G'` is added: its darts come from the darts of a
tree `T₀` of `G` whose darts are disjoint from those of `𝒯o`, or lie outside the image of `f`, and
its root has a dart coming from a dart outside the trees. -/
theorem isCollapsingFamily_insert_transportFamily' {𝒯o : Finset (G.RootedTree × Shade)}
    (h𝒯o : G.IsCollapsingFamily 𝒯o) {T₀ : G.RootedTree}
    (hdisj : ∀ q ∈ 𝒯o, Disjoint T₀.darts q.1.darts) (hemb' : ∀ p ∈ 𝒯o, p.1.IsEmbedding G' f)
    {A : Set H} (hA : Set.InjOn f A) (hDA' : ∀ x ∈ G.familyDarts 𝒯o, x ∈ A)
    (hroot : ∀ p ∈ 𝒯o, G'.IsBoundaryVertex (G'.vertexOf (f p.1.intervalStart)) ↔
      G.IsBoundaryVertex p.1.root)
    (hfree : ∀ p ∈ 𝒯o, ∃ a ∈ A, a ∉ G.familyDarts 𝒯o ∧ a ∉ T₀.darts ∧
      f a ∈ G'.vertexOf (f p.1.intervalStart))
    {T' : G'.RootedTree} {c : Shade} (hT' : T'.IsCollapsibleOfColour c)
    (hT'D : ∀ y ∈ T'.darts, (∃ e ∈ T₀.darts, e ∈ A ∧ f e = y) ∨ y ∉ Set.range f)
    (hT'free : ∃ a ∈ A, a ∉ G.familyDarts 𝒯o ∧ a ∉ T₀.darts ∧ f a ∈ T'.root) :
    G'.IsCollapsingFamily (insert (T', c) (transportFamily hG hG' hemb')) := by
  have hDq : ∀ q ∈ 𝒯o, ∀ e ∈ q.1.darts, e ∈ A := fun q hq e he =>
    hDA' e (mem_familyDarts.2 ⟨q, hq, he⟩)
  have h𝒯' := isCollapsingFamily_transportFamily hG hG' hemb' h𝒯o hA hDA' hroot
    (fun p hp => by
      obtain ⟨a, haA, haD, -, hav⟩ := hfree p hp
      exact ⟨a, haA, haD, hav⟩)
  have hT'q : ∀ y ∈ T'.darts, ∀ q' ∈ transportFamily hG hG' hemb', y ∉ q'.1.darts := by
    intro y hy q' hq' hyq
    obtain ⟨q, hq, rfl⟩ := (mem_transportFamily hG hG' hemb').1 hq'
    change y ∈ ((hemb' q hq).tree hG hG').darts at hyq
    rw [(hemb' q hq).tree_darts hG hG'] at hyq
    obtain ⟨e', he', rfl⟩ := mem_image.1 hyq
    rcases hT'D _ hy with ⟨e, he, heA, hfe⟩ | h
    · have := hA (hDq q hq e' he') heA hfe.symm
      subst this
      exact disjoint_left.1 (hdisj q hq) he he'
    · exact h ⟨e', rfl⟩
  have hfD : ∀ a ∈ A, a ∉ G.familyDarts 𝒯o → a ∉ T₀.darts →
      ∀ q' ∈ insert (T', c) (transportFamily hG hG' hemb'), f a ∉ q'.1.darts := by
    intro a haA haD haT q' hq' haq
    rcases mem_insert.1 hq' with rfl | hq'
    · rcases hT'D _ haq with ⟨e, he, heA, hfe⟩ | h
      · have := hA heA haA hfe
        subst this
        exact haT he
      · exact h ⟨a, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := (mem_transportFamily hG hG' hemb').1 hq'
      change f a ∈ ((hemb' q hq).tree hG hG').darts at haq
      rw [(hemb' q hq).tree_darts hG hG'] at haq
      obtain ⟨e, he, hfe⟩ := mem_image.1 haq
      have := hA (hDq q hq e he) haA hfe
      subst this
      exact haD (mem_familyDarts.2 ⟨q, hq, he⟩)
  refine ⟨fun q' hq' => ?_, fun q₁ hq₁ q₂ hq₂ hne => ?_, fun q₁ hq₁ q₂ hq₂ hne => ?_,
    fun q' hq' => ?_⟩
  · rcases mem_insert.1 hq' with rfl | hq'
    · exact hT'
    · exact h𝒯'.isCollapsibleOfColour q' hq'
  · rcases mem_insert.1 hq₁ with rfl | hq₁ <;> rcases mem_insert.1 hq₂ with rfl | hq₂
    · exact absurd rfl hne
    · rw [Finset.disjoint_left]
      intro w hw₁ hw₂
      obtain ⟨y, hy⟩ := RootedTree.exists_mem_of_mem_nonRoot hw₁
      exact hT'q y (RootedTree.IsEmbedding.mem_darts_of_mem_nonRoot hw₁ hy) q₂ hq₂
        (RootedTree.IsEmbedding.mem_darts_of_mem_nonRoot hw₂ hy)
    · rw [Finset.disjoint_left]
      intro w hw₁ hw₂
      obtain ⟨y, hy⟩ := RootedTree.exists_mem_of_mem_nonRoot hw₂
      exact hT'q y (RootedTree.IsEmbedding.mem_darts_of_mem_nonRoot hw₂ hy) q₁ hq₁
        (RootedTree.IsEmbedding.mem_darts_of_mem_nonRoot hw₁ hy)
    · exact h𝒯'.disjoint_nonRoot q₁ hq₁ q₂ hq₂ hne
  · rcases mem_insert.1 hq₁ with rfl | hq₁ <;> rcases mem_insert.1 hq₂ with rfl | hq₂
    · exact absurd rfl hne
    · intro h
      obtain ⟨a, haA, haD, haT, har⟩ := hT'free
      exact hfD a haA haD haT q₂ (mem_insert_of_mem hq₂)
        (RootedTree.IsEmbedding.mem_darts_of_mem_nonRoot h har)
    · intro h
      obtain ⟨q, hq, rfl⟩ := (mem_transportFamily hG hG' hemb').1 hq₁
      have hy : f q.1.intervalStart ∈ T'.darts :=
        RootedTree.IsEmbedding.mem_darts_of_mem_nonRoot h (G'.self_mem_vertexOf _)
      exact hT'q _ hy _ hq₁ (by
        change f q.1.intervalStart ∈ ((hemb' q hq).tree hG hG').darts
        rw [(hemb' q hq).tree_darts hG hG']
        exact mem_image_of_mem f q.1.intervalStart_mem_darts)
    · exact h𝒯'.root_notMem_nonRoot q₁ hq₁ q₂ hq₂ hne
  · rcases mem_insert.1 hq' with rfl | hq'
    · obtain ⟨a, haA, haD, haT, har⟩ := hT'free
      exact ⟨f a, har, hfD a haA haD haT⟩
    · obtain ⟨q, hq, rfl⟩ := (mem_transportFamily hG hG' hemb').1 hq'
      obtain ⟨a, haA, haD, haT, hav⟩ := hfree q hq
      exact ⟨f a, hav, hfD a haA haD haT⟩

open scoped Classical in
/-- **Replacing one tree of a collapsing family.** The other trees are transported into `G'`, and
the tree `T'` of `G'` replaces the member `p₀`: its darts come from the darts of `p₀`, and its root
has a dart coming from a dart outside the trees. -/
theorem isCollapsingFamily_insert_transportFamily (h𝒯 : G.IsCollapsingFamily 𝒯)
    {p₀ : G.RootedTree × Shade} (hp₀ : p₀ ∈ 𝒯) (hemb' : ∀ p ∈ 𝒯.erase p₀, p.1.IsEmbedding G' f)
    {A : Set H} (hA : Set.InjOn f A) (hDA' : ∀ x ∈ G.familyDarts (𝒯.erase p₀), x ∈ A)
    (hroot : ∀ p ∈ 𝒯.erase p₀, G'.IsBoundaryVertex (G'.vertexOf (f p.1.intervalStart)) ↔
      G.IsBoundaryVertex p.1.root)
    (hfree : ∀ p ∈ 𝒯.erase p₀, ∃ a ∈ A, a ∉ G.familyDarts 𝒯 ∧
      f a ∈ G'.vertexOf (f p.1.intervalStart))
    {T' : G'.RootedTree} {c : Shade} (hT' : T'.IsCollapsibleOfColour c)
    (hT'D : ∀ y ∈ T'.darts, ∃ e ∈ p₀.1.darts, e ∈ A ∧ f e = y)
    (hT'free : ∃ a ∈ A, a ∉ G.familyDarts 𝒯 ∧ f a ∈ T'.root) :
    G'.IsCollapsingFamily (insert (T', c) (transportFamily hG hG' hemb')) := by
  have hnot : ∀ {a}, a ∉ G.familyDarts 𝒯 → a ∉ G.familyDarts (𝒯.erase p₀) ∧ a ∉ p₀.1.darts :=
    fun {a} ha => ⟨fun h => ha (by
      obtain ⟨q, hq, haq⟩ := mem_familyDarts.1 h
      exact mem_familyDarts.2 ⟨q, mem_of_mem_erase hq, haq⟩),
      fun h => ha (mem_familyDarts.2 ⟨p₀, hp₀, h⟩)⟩
  refine isCollapsingFamily_insert_transportFamily' hG hG' (h𝒯.subset (erase_subset p₀ 𝒯))
    (fun q hq => p₀.1.disjoint_darts hG
      (h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq) (ne_of_mem_erase hq).symm)
      (h𝒯.root_notMem_nonRoot q (mem_of_mem_erase hq) p₀ hp₀ (ne_of_mem_erase hq)))
    hemb' hA hDA' hroot (fun p hp => ?_) hT' (fun y hy => Or.inl (hT'D y hy)) ?_
  · obtain ⟨a, haA, haD, hav⟩ := hfree p hp
    exact ⟨a, haA, (hnot haD).1, (hnot haD).2, hav⟩
  · obtain ⟨a, haA, haD, har⟩ := hT'free
    exact ⟨a, haA, (hnot haD).1, (hnot haD).2, har⟩

open scoped Classical in
/-- The darts of the family with a replaced tree. -/
theorem mem_familyDarts_insert_transportFamily {𝒯o : Finset (G.RootedTree × Shade)}
    (hemb' : ∀ p ∈ 𝒯o, p.1.IsEmbedding G' f) {T' : G'.RootedTree} {c : Shade} {y : H'} :
    y ∈ G'.familyDarts (insert (T', c) (transportFamily hG hG' hemb')) ↔
      y ∈ T'.darts ∨ ∃ e ∈ G.familyDarts 𝒯o, f e = y := by
  rw [← mem_familyDarts_transportFamily hG hG' hemb', mem_familyDarts, mem_familyDarts]
  constructor
  · rintro ⟨q, hq, hyq⟩
    rcases mem_insert.1 hq with rfl | hq
    · exact Or.inl hyq
    · exact Or.inr ⟨q, hq, hyq⟩
  · rintro (h | ⟨q, hq, hyq⟩)
    · exact ⟨_, mem_insert_self _ _, h⟩
    · exact ⟨q, mem_insert_of_mem hq, hyq⟩

end TransportFamily

end Transport

/-! ### Families of branches -/

section Branches

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- The interval of a rooted tree with a boundary root is one dart, the leg. -/
private theorem RootedTree.intervalLength_eq_one_of_isBoundaryVertex (hG : G.IsPlabicGraph)
    (T : G.RootedTree) (hb : G.IsBoundaryVertex T.root) : T.intervalLength = 1 := by
  by_contra h
  have h2 : 1 < T.intervalLength := by have := T.one_le_intervalLength; omega
  have hmem : G.rot T.intervalStart ∈ T.root := by
    rw [T.mem_root_iff, G.vertexOf_rot, ← T.root_eq_vertexOf_intervalStart]
  exact T.rot_intervalStart_notMem_of_isBoundaryVertex hG hb
    ((T.mem_darts_iff_of_mem_root hmem).2 ⟨1, h2, by rw [pow_one]⟩)

/-- For a tree whose interval is one dart, the darts of the tree at the root are `a₁` alone. -/
theorem RootedTree.eq_intervalStart_of_intervalLength_eq_one (T : G.RootedTree)
    (h1 : T.intervalLength = 1) {d : H} (hd : d ∈ T.darts) (hr : d ∈ T.root) :
    d = T.intervalStart := by
  obtain ⟨j, hj, rfl⟩ := T.exists_eq_pow_of_mem_root hd hr
  obtain rfl : j = 0 := by omega
  rfl

open scoped Classical in
/-- The **family of branches** of a family: each tree with an internal root is replaced by its
branches, with the same colour. -/
noncomputable def branchFamily (hG : G.IsPlabicGraph) (𝒯 : Finset (G.RootedTree × Shade)) :
    Finset (G.RootedTree × Shade) :=
  𝒯.biUnion fun p => if G.IsBoundaryVertex p.1.root then {p} else
    (univ : Finset (Fin p.1.intervalLength)).image fun i => (p.1.branchTree hG i.isLt, p.2)

private theorem mem_branchFamily (hG : G.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)}
    {q : G.RootedTree × Shade} :
    q ∈ branchFamily hG 𝒯 ↔ ∃ p ∈ 𝒯, (G.IsBoundaryVertex p.1.root ∧ q = p) ∨
      (¬G.IsBoundaryVertex p.1.root ∧ ∃ i, ∃ hi : i < p.1.intervalLength,
        q = (p.1.branchTree hG hi, p.2)) := by
  classical
  unfold branchFamily
  rw [mem_biUnion]
  refine exists_congr fun p => and_congr Iff.rfl ?_
  split_ifs with hb
  · simp [hb]
  · simp only [hb, false_and, false_or, not_false_eq_true, true_and, mem_image, mem_univ]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩

variable (hG : G.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)}
  (h𝒯 : G.IsCollapsingFamily 𝒯)

include hG

omit hG in
/-- Every tree of the family of branches has an interval of length one. -/
theorem branchFamily_intervalLength (hG : G.IsPlabicGraph) {q : G.RootedTree × Shade}
    (hq : q ∈ branchFamily hG 𝒯) : q.1.intervalLength = 1 := by
  obtain ⟨p, -, ⟨hb, hqp⟩ | ⟨-, i, hi, hqp⟩⟩ := (mem_branchFamily hG).1 hq
  · rw [hqp]
    exact p.1.intervalLength_eq_one_of_isBoundaryVertex hG hb
  · rw [hqp]
    exact p.1.branchTree_intervalLength hG hi

private theorem mem_familyDarts_branchFamily {x : H} :
    x ∈ G.familyDarts (branchFamily hG 𝒯) ↔ x ∈ G.familyDarts 𝒯 := by
  rw [mem_familyDarts, mem_familyDarts]
  constructor
  · rintro ⟨q, hq, hx⟩
    obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨-, i, hi, rfl⟩⟩ := (mem_branchFamily hG).1 hq
    · exact ⟨q, hp, hx⟩
    · exact ⟨p, hp, p.1.branchDarts_subset i hx⟩
  · rintro ⟨p, hp, hx⟩
    by_cases hb : G.IsBoundaryVertex p.1.root
    · exact ⟨p, (mem_branchFamily hG).2 ⟨p, hp, Or.inl ⟨hb, rfl⟩⟩, hx⟩
    · obtain ⟨i, hi, hxi⟩ := p.1.exists_mem_branchDarts hx
      exact ⟨_, (mem_branchFamily hG).2 ⟨p, hp, Or.inr ⟨hb, i, hi, rfl⟩⟩, hxi⟩

/-- The members of the family of branches whose trees contain a leg are members of the family. -/
private theorem branchFamily_leg {i : Fin b} {q : G.RootedTree × Shade}
    (hq : q ∈ branchFamily hG 𝒯) (hiq : G.leg i ∈ q.1.darts) : q ∈ 𝒯 := by
  obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨hb, j, hj, rfl⟩⟩ := (mem_branchFamily hG).1 hq
  · exact hp
  · refine absurd ?_ hb
    rw [p.1.root_eq_bvertex_of_leg_mem hG (p.1.branchDarts_subset j hiq)]
    exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

include h𝒯 in
/-- The family of branches of a collapsing family is a collapsing family. -/
theorem isCollapsingFamily_branchFamily : G.IsCollapsingFamily (branchFamily hG 𝒯) := by
  refine ⟨fun q hq => ?_, fun q hq q' hq' hne => ?_, fun q hq q' hq' hne => ?_, fun q hq => ?_⟩
  · obtain ⟨p, hp, ⟨-, rfl⟩ | ⟨hb, i, hi, rfl⟩⟩ := (mem_branchFamily hG).1 hq
    · exact h𝒯.isCollapsibleOfColour q hp
    · have hc := h𝒯.isCollapsibleOfColour p hp
      obtain ⟨c', hc'⟩ := (p.1.isCollapsible_iff_forall_isCollapsible_branchTree hG hb).1
        hc.isCollapsible i hi
      have hcol : ∀ d ∈ p.1.root, G.colour d = p.2 := by
        rcases hc.root_cases with h | h
        · exact h.2
        · exact absurd h.1 hb
      rcases hc'.root_cases with h | h
      · obtain rfl : c' = p.2 := (h.2 _ p.1.intervalStart_mem_root).symm.trans
          (hcol _ p.1.intervalStart_mem_root)
        exact hc'
      · exact absurd h.1 hb
  · obtain ⟨p, hp, hq₁⟩ := (mem_branchFamily hG).1 hq
    obtain ⟨p', hp', hq₂⟩ := (mem_branchFamily hG).1 hq'
    have hsub : ∀ {p r : G.RootedTree × Shade}, ((G.IsBoundaryVertex p.1.root ∧ r = p) ∨
        (¬G.IsBoundaryVertex p.1.root ∧ ∃ i, ∃ hi : i < p.1.intervalLength,
          r = (p.1.branchTree hG hi, p.2))) → r.1.nonRoot ⊆ p.1.nonRoot := by
      rintro p r (⟨-, rfl⟩ | ⟨-, i, hi, rfl⟩)
      · exact Subset.rfl
      · exact p.1.branch_subset i
    by_cases hpp : p = p'
    · subst hpp
      rcases hq₁ with ⟨hb₀, rfl⟩ | ⟨hb, i, hi, rfl⟩
      · rcases hq₂ with ⟨-, rfl⟩ | ⟨hb', -⟩
        · exact absurd rfl hne
        · exact absurd hb₀ hb'
      · rcases hq₂ with ⟨hb', -⟩ | ⟨-, i', hi', rfl⟩
        · exact absurd hb' hb
        · have hii : i ≠ i' := by rintro rfl; exact hne rfl
          exact p.1.disjoint_branch hG hi hi' hii
    · exact (h𝒯.disjoint_nonRoot p hp p' hp' hpp).mono (hsub hq₁) (hsub hq₂)
  · obtain ⟨p, hp, hq₁⟩ := (mem_branchFamily hG).1 hq
    obtain ⟨p', hp', hq₂⟩ := (mem_branchFamily hG).1 hq'
    have hroot : q.1.root = p.1.root := by
      rcases hq₁ with ⟨-, rfl⟩ | ⟨-, i, hi, rfl⟩
      · rfl
      · rfl
    have hsub : q'.1.nonRoot ⊆ p'.1.nonRoot := by
      rcases hq₂ with ⟨-, rfl⟩ | ⟨-, i, hi, rfl⟩
      · exact Subset.rfl
      · exact p'.1.branch_subset i
    rw [hroot]
    intro h
    by_cases hpp : p = p'
    · subst hpp
      exact p.1.root_notMem_nonRoot (hsub h)
    · exact h𝒯.root_notMem_nonRoot p hp p' hp' hpp (hsub h)
  · obtain ⟨p, hp, hq₁⟩ := (mem_branchFamily hG).1 hq
    obtain ⟨d, hd, hdq⟩ := h𝒯.exists_mem_root p hp
    have hroot : q.1.root = p.1.root := by
      rcases hq₁ with ⟨-, rfl⟩ | ⟨-, i, hi, rfl⟩
      · rfl
      · rfl
    refine ⟨d, hroot ▸ hd, fun q' hq' hdq' => ?_⟩
    have : d ∈ G.familyDarts (branchFamily hG 𝒯) := mem_familyDarts.2 ⟨q', hq', hdq'⟩
    obtain ⟨r, hr, hdr⟩ := mem_familyDarts.1 ((mem_familyDarts_branchFamily hG).1 this)
    exact hdq r hr hdr

include h𝒯 in
/-- Replacing the trees of a collapsing family by their branches does not change the collapse. -/
theorem collapseMatch_branchFamily :
    CollapseMatch G G (branchFamily hG 𝒯) 𝒯 id := by
  have hK : ∀ x, x ∈ G.collapseCore (branchFamily hG 𝒯) ↔ x ∈ G.collapseCore 𝒯 := by
    intro x
    change (x ∉ G.familyDarts _ ∨ _) ↔ (x ∉ G.familyDarts _ ∨ _)
    rw [mem_familyDarts_branchFamily hG]
  have h𝒯b := isCollapsingFamily_branchFamily hG h𝒯
  refine
    { injective := injective_id
      mem_core_iff := hK
      exists_eq := fun y _ => ⟨y, rfl⟩
      map_leg := fun i => rfl
      leg_mem_iff := fun i => (mem_familyDarts_branchFamily hG).symm
      map_inv := fun x _ _ => rfl
      map_rot := fun x hx => ?_
      mem_bdry_iff := fun x _ => Iff.rfl
      colour := fun x _ => rfl
      colour_leg := fun i q hq p hp hiq hip => ?_
      colour_leg₁ := fun i q hq q' hq' hiq hiq' => ?_ }
  · exact coe_firstReturn_congr G.rot (Set.ext hK).symm x hx _
  · rw [h𝒯.eq_of_mem_darts hG (branchFamily_leg hG hq hiq) hp hiq hip]
  · rw [h𝒯b.eq_of_mem_darts hG hq hq' hiq hiq']

end Branches

/-- The darts of a set of vertices are closed under the involution. -/
theorem inv_mem_treeDarts' {X : Type*} [Fintype X] [DecidableEq X] {b : ℕ}
    {Q : PlabicData X b}
    (hQ : Q.IsPlabicGraph) {W : Finset (Finset X)} {y : X} (hy : y ∈ Q.treeDarts W) :
    Q.inv y ∈ Q.treeDarts W := by
  obtain ⟨hB, h⟩ := Q.mem_treeDarts.1 hy
  refine Q.mem_treeDarts.2 ⟨fun h' => hB (hQ.inv_mem_bdry_iff.1 h'), ?_⟩
  rw [hQ.inv_involutive]
  exact h.symm

/-- A dart `δ` with `σ² δ = δ ≠ σ δ`, outside `B` together with `σ δ`, and with `δ̄ ≠ σ δ`, spans a
removable bivalent vertex. -/
theorem isBivalentRemovable_of_rot_rot {X : Type*} [Fintype X] [DecidableEq X] {b : ℕ}
    {Q : PlabicData X b} {δ : X} (h2 : Q.rot (Q.rot δ) = δ) (h1 : Q.rot δ ≠ δ)
    (hB : δ ∉ Q.bdry) (hB' : Q.rot δ ∉ Q.bdry) (hinv : Q.inv δ ≠ Q.rot δ) :
    Q.IsBivalentRemovable δ := by
  have hsub : ∀ e ∈ Q.vertexOf δ, e = δ ∨ e = Q.rot δ := by
    intro e he
    obtain ⟨n, rfl⟩ := ((Q.mem_vertexOf).1 he).exists_nat_pow_eq
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih (by rw [Q.mem_vertexOf]; exact sameCycle_pow_apply_self _ _ _) with h | h
      · rw [h]; exact Or.inr rfl
      · rw [h, h2]; exact Or.inl rfl
  refine ⟨?_, ?_, hinv⟩
  · rintro ⟨e, he, heB⟩
    rcases hsub e he with rfl | rfl
    · exact hB heB
    · exact hB' heB
  · refine le_antisymm (Q.card_vertexOf_le_two h2) ?_
    exact (card_pair h1.symm).symm.le.trans
      (card_le_card fun e he => by
        rcases mem_insert.1 he with rfl | he
        · exact Q.self_mem_vertexOf _
        · rw [mem_singleton.1 he]; exact Q.rot_mem_vertexOf _)

/-! ### Merging the trees at a root -/

section MergeTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- Two rooted trees with the same root and the same non-root vertices are equal. -/
theorem RootedTree.ext' {Q : PlabicData H b} {T T' : Q.RootedTree} (h1 : T.root = T'.root)
    (h2 : T.nonRoot = T'.nonRoot) : T = T' := by
  cases T; cases T'
  simp only at h1 h2
  subst h1 h2
  rfl

/-- Every dart of `v(d)` is `σ^m d` for some `m < |v(d)|`. -/
theorem exists_pow_lt_card {d e : H} (he : e ∈ G.vertexOf d) :
    ∃ m < (G.vertexOf d).card, (G.rot ^ m) d = e := by
  obtain ⟨m, rfl⟩ := ((G.mem_vertexOf).1 he).exists_nat_pow_eq
  have hpos : 0 < (G.vertexOf d).card := card_pos.2 ⟨d, G.self_mem_vertexOf d⟩
  have hper : (G.rot ^ (G.vertexOf d).card) d = d := by
    by_contra hne
    have hinj : ∀ i j, i ≤ (G.vertexOf d).card → j ≤ (G.vertexOf d).card → i < j →
        (G.rot ^ i) d ≠ (G.rot ^ j) d := by
      intro i j hi hj hij h
      have h' : (G.rot ^ (j - i)) d = d := by
        apply (G.rot ^ i).injective
        rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le, h]
      have := card_vertexOf_le_of_pow_apply_eq (G := G) (by omega) h'
      by_cases hi0 : i = 0
      · subst hi0
        rw [Nat.sub_zero] at h'
        exact hne (by
          have hj' : j = (G.vertexOf d).card := by omega
          rwa [← hj'])
      · omega
    have hsub : (range ((G.vertexOf d).card + 1)).image (fun i => (G.rot ^ i) d) ⊆
        G.vertexOf d := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      exact (G.mem_vertexOf).2 (sameCycle_pow_apply_self _ _ _)
    have := card_le_card hsub
    rw [card_image_of_injOn, card_range] at this
    · omega
    · intro i hi j hj h
      simp only [coe_range, Set.mem_Iio] at hi hj
      by_contra hij
      rcases lt_or_gt_of_ne hij with h' | h'
      · exact hinj i j (by omega) (by omega) h' h
      · exact hinj j i (by omega) (by omega) h' h.symm
  set n := (G.vertexOf d).card with hn
  have hpow : ∀ k : ℕ, (G.rot ^ (n * k)) d = d := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Nat.mul_succ, pow_add, Perm.mul_apply, hper, ih]
  refine ⟨m % n, Nat.mod_lt _ hpos, ?_⟩
  conv_rhs => rw [← Nat.mod_add_div m n]
  rw [pow_add, Perm.mul_apply, hpow]

variable (hG : G.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)}
  (h𝒯 : G.IsCollapsingFamily 𝒯) {z : H} (hzD : z ∉ G.familyDarts 𝒯)
  (hthin : ∀ e ∈ G.vertexOf z, e ≠ z → ∃ p ∈ 𝒯, p.1.root = G.vertexOf z ∧ e ∈ p.1.darts)
  (hne : ∃ p ∈ 𝒯, p.1.root = G.vertexOf z)

include hG h𝒯 hzD hthin hne

namespace MergeTree

omit hG h𝒯 hzD hthin hne in
private theorem mem_treeDarts_biUnion {W : Finset (G.RootedTree × Shade)} {e : H} :
    e ∈ G.treeDarts (W.biUnion fun p => p.1.nonRoot) ↔ ∃ p ∈ W, e ∈ p.1.darts := by
  constructor
  · intro h
    obtain ⟨hB, h⟩ := G.mem_treeDarts.1 h
    rcases h with h | h
    · obtain ⟨p, hp, h⟩ := mem_biUnion.1 h
      exact ⟨p, hp, G.mem_treeDarts.2 ⟨hB, Or.inl h⟩⟩
    · obtain ⟨p, hp, h⟩ := mem_biUnion.1 h
      exact ⟨p, hp, G.mem_treeDarts.2 ⟨hB, Or.inr h⟩⟩
  · rintro ⟨p, hp, he⟩
    obtain ⟨hB, h⟩ := G.mem_treeDarts.1 he
    exact G.mem_treeDarts.2 ⟨hB, h.imp (fun h => mem_biUnion.2 ⟨p, hp, h⟩)
      (fun h => mem_biUnion.2 ⟨p, hp, h⟩)⟩

omit hzD hthin hne in
private theorem disjoint_darts_of_ne {p q : G.RootedTree × Shade} (hp : p ∈ 𝒯) (hq : q ∈ 𝒯)
    (hpq : p ≠ q) : Disjoint p.1.darts q.1.darts :=
  p.1.disjoint_darts hG (h𝒯.disjoint_nonRoot p hp q hq hpq)
    (h𝒯.root_notMem_nonRoot q hq p hp hpq.symm)

end MergeTree

/-- **The trees at a root merged into one tree**: if every dart of `v = v(z)` other than `z` is a
dart of a tree of `𝒯` with root `v`, these trees form one rooted tree with root `v`, whose interval
is `v` without `z`. -/
noncomputable def mergeTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hM : ∀ e, e ∈ G.treeDarts ((𝒯.filter fun p => p.1.root = G.vertexOf z).biUnion
      fun p => p.1.nonRoot) ↔ ∃ p ∈ 𝒯, p.1.root = G.vertexOf z ∧ e ∈ p.1.darts := fun e => by
    rw [MergeTree.mem_treeDarts_biUnion]
    simp only [mem_filter, and_assoc]
  have hzDv : z ∉ G.treeDarts ((𝒯.filter fun p => p.1.root = G.vertexOf z).biUnion
      fun p => p.1.nonRoot) := fun h => by
    obtain ⟨p, hp, -, hzp⟩ := (hM z).1 h
    exact hzD (mem_familyDarts.2 ⟨p, hp, hzp⟩)
  have hcard2 : 2 ≤ (G.vertexOf z).card := by
    obtain ⟨p, hp, hpr⟩ := hne
    have ha : p.1.intervalStart ∈ G.vertexOf z := hpr ▸ p.1.intervalStart_mem_root
    have hne' : p.1.intervalStart ≠ z := fun h =>
      hzD (mem_familyDarts.2 ⟨p, hp, h ▸ p.1.intervalStart_mem_darts⟩)
    exact (card_pair hne').symm.le.trans (card_le_card fun e he => by
      rcases mem_insert.1 he with rfl | he
      · exact ha
      · rw [mem_singleton.1 he]; exact G.self_mem_vertexOf z)
  { root := G.vertexOf z
    nonRoot := (𝒯.filter fun p => p.1.root = G.vertexOf z).biUnion fun p => p.1.nonRoot
    root_mem_vertices := G.vertexOf_mem_vertices z
    nonRoot_nonempty := by
      obtain ⟨p, hp, hpr⟩ := hne
      obtain ⟨w, hw⟩ := p.1.nonRoot_nonempty
      exact ⟨w, mem_biUnion.2 ⟨p, mem_filter.2 ⟨hp, hpr⟩, hw⟩⟩
    nonRoot_subset := by
      intro w hw
      obtain ⟨p, -, hw⟩ := mem_biUnion.1 hw
      exact p.1.nonRoot_subset hw
    root_notMem_nonRoot := by
      intro h
      obtain ⟨p, hp, hw⟩ := mem_biUnion.1 h
      rw [← (mem_filter.1 hp).2] at hw
      exact p.1.root_notMem_nonRoot hw
    vertexOf_inv_mem := by
      intro e he
      obtain ⟨p, hp, hw⟩ := mem_biUnion.1 he
      rcases mem_insert.1 (p.1.vertexOf_inv_mem e hw) with h | h
      · rw [h, (mem_filter.1 hp).2]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_biUnion.2 ⟨p, hp, h⟩)
    exists_interval := by
      refine ⟨G.rot z, G.rot_mem_vertexOf z, (G.vertexOf z).card - 1, by omega, by omega,
        fun e he => ?_, ?_⟩
      · constructor
        · intro h
          have hez : e ≠ z := fun h' => hzDv (h' ▸ h)
          obtain ⟨m, hm, rfl⟩ := exists_pow_lt_card he
          have hm0 : m ≠ 0 := by rintro rfl; exact hez rfl
          refine ⟨m - 1, by omega, ?_⟩
          rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]
        · rintro ⟨j, hj, rfl⟩
          have hez : (G.rot ^ j) (G.rot z) ≠ z := by
            intro h
            rw [← Perm.mul_apply, ← pow_succ] at h
            have := card_vertexOf_le_of_pow_apply_eq (G := G) (Nat.succ_pos j) h
            omega
          obtain ⟨p, hp, hpr, hep⟩ := hthin _ he hez
          exact (hM _).2 ⟨p, hp, hpr, hep⟩
      · rw [Equiv.symm_apply_apply]
        exact hzDv
    card_image_edgeOf := by
      set M := 𝒯.filter fun p => p.1.root = G.vertexOf z
      have hD : G.treeDarts (M.biUnion fun p => p.1.nonRoot) = M.biUnion fun p => p.1.darts := by
        ext e
        rw [MergeTree.mem_treeDarts_biUnion, mem_biUnion]
      have h1 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
        (S := G.treeDarts (M.biUnion fun p => p.1.nonRoot)) fun e he => inv_mem_treeDarts' hG he
      have h2 : (M.biUnion fun p => p.1.darts).card =
          2 * (M.biUnion fun p => p.1.nonRoot).card := by
        rw [card_biUnion, card_biUnion, mul_sum]
        · exact sum_congr rfl fun p _ => p.1.card_darts hG
        · intro p hp q hq hpq
          exact h𝒯.disjoint_nonRoot p (mem_filter.1 hp).1 q (mem_filter.1 hq).1 hpq
        · intro p hp q hq hpq
          exact MergeTree.disjoint_darts_of_ne hG h𝒯 (mem_filter.1 hp).1 (mem_filter.1 hq).1 hpq
      rw [hD] at h1
      rw [hD]
      omega
    reflTransGen_treeAdj := by
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact .refl
      obtain ⟨p, hp, hw⟩ := mem_biUnion.1 hu
      have := p.1.reflTransGen_treeAdj u (mem_insert_of_mem hw)
      rw [(mem_filter.1 hp).2] at this
      refine this.mono fun u u' ⟨e, he, h1, h2⟩ => ⟨e, (hM e).2 ⟨p, (mem_filter.1 hp).1,
        (mem_filter.1 hp).2, he⟩, h1, h2⟩ }

namespace MergeTree

/-- The root of the merged tree is `v(z)`. -/
theorem root_eq : (mergeTree hG h𝒯 hzD hthin hne).root = G.vertexOf z := rfl

/-- The non-root vertices of the merged tree are those of the trees of `𝒯` with root `v(z)`. -/
theorem nonRoot_eq : (mergeTree hG h𝒯 hzD hthin hne).nonRoot =
    (𝒯.filter fun p => p.1.root = G.vertexOf z).biUnion fun p => p.1.nonRoot := rfl

/-- The darts of the merged tree are the darts of the trees of `𝒯` with root `v(z)`. -/
theorem darts_iff {e : H} : e ∈ (mergeTree hG h𝒯 hzD hthin hne).darts ↔
    ∃ p ∈ 𝒯, p.1.root = G.vertexOf z ∧ e ∈ p.1.darts := by
  rw [RootedTree.darts, nonRoot_eq, mem_treeDarts_biUnion]
  simp only [mem_filter, and_assoc]

/-- The interval of the merged tree starts at `σ z`. -/
theorem intervalStart_eq : (mergeTree hG h𝒯 hzD hthin hne).intervalStart = G.rot z := by
  refine ((mergeTree hG h𝒯 hzD hthin hne).eq_intervalStart_of_rot_symm_notMem ?_
    (G.rot_mem_vertexOf z) ?_).symm
  · obtain ⟨p, hp, hpr⟩ := id hne
    have hne' : G.rot z ≠ z := by
      intro h
      have ha : p.1.intervalStart ∈ G.vertexOf z := hpr ▸ p.1.intervalStart_mem_root
      obtain ⟨n, hn⟩ := ((G.mem_vertexOf).1 ha).exists_nat_pow_eq
      have hpow : ∀ n : ℕ, (G.rot ^ n) z = z := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ', Perm.mul_apply, ih, h]
      rw [hpow] at hn
      exact hzD (mem_familyDarts.2 ⟨p, hp, hn ▸ p.1.intervalStart_mem_darts⟩)
    obtain ⟨q, hq, hqr, hq'⟩ := hthin _ (G.rot_mem_vertexOf z) hne'
    exact (darts_iff hG h𝒯 hzD hthin hne).2 ⟨q, hq, hqr, hq'⟩
  · rw [Equiv.symm_apply_apply]
    intro h
    obtain ⟨p, hp, -, hzp⟩ := (darts_iff hG h𝒯 hzD hthin hne).1 h
    exact hzD (mem_familyDarts.2 ⟨p, hp, hzp⟩)

/-- **The merged tree is collapsible**: its branches are the trees of the family with root `v`. -/
theorem isCollapsibleOfColour (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1)
    (hint : ¬G.IsBoundaryVertex (G.vertexOf z)) :
    (mergeTree hG h𝒯 hzD hthin hne).IsCollapsibleOfColour (G.colour z) := by
  set Tv := mergeTree hG h𝒯 hzD hthin hne with hTv
  have hD := fun e => darts_iff hG h𝒯 hzD hthin hne (e := e)
  have hb : ¬G.IsBoundaryVertex Tv.root := hint
  have hcoll : Tv.IsCollapsible := by
    refine (Tv.isCollapsible_iff_forall_isCollapsible_branchTree hG hb).2 fun i hi => ?_
    set a := (G.rot ^ i) Tv.intervalStart with ha
    obtain ⟨p, hp, hpr, hap⟩ := (hD a).1 (Tv.pow_intervalStart_mem_darts hi)
    have har : a ∈ p.1.root := by
      rw [hpr]
      exact Tv.pow_intervalStart_mem_root i
    have hpa : p.1.intervalStart = a :=
      (p.1.eq_intervalStart_of_intervalLength_eq_one (hbr p hp) hap har).symm
    have hmono : ∀ u u', p.1.NonRootAdj u u' → Tv.NonRootAdj u u' := by
      rintro u u' ⟨hu, hu', e, he, h1, h2⟩
      have hpM : p ∈ 𝒯.filter fun p => p.1.root = G.vertexOf z := mem_filter.2 ⟨hp, hpr⟩
      exact ⟨mem_biUnion.2 ⟨p, hpM, hu⟩, mem_biUnion.2 ⟨p, hpM, hu'⟩, e,
        (hD e).2 ⟨p, hp, hpr, he⟩, h1, h2⟩
    have hbranch : Tv.branchTree hG hi = p.1 := by
      refine RootedTree.ext' (by rw [RootedTree.branchTree_root, root_eq, hpr]) ?_
      rw [RootedTree.branchTree_nonRoot]
      ext w
      rw [Tv.mem_branch]
      constructor
      · rintro ⟨-, hpath⟩
        induction hpath with
        | refl => exact p.1.vertexOf_inv_mem_nonRoot_of_mem_root hap har
        | @tail u₁ u₂ _ hstep ih =>
          obtain ⟨-, hu₂, e, -, rfl, rfl⟩ := hstep
          rcases mem_insert.1 (p.1.vertexOf_inv_mem e ih) with h | h
          · exact absurd hu₂ (by rw [h, hpr]; exact Tv.root_notMem_nonRoot)
          · exact h
      · intro hw
        obtain ⟨j, hj, hwj⟩ := p.1.exists_mem_branch hw
        obtain rfl : j = 0 := by rw [hbr p hp] at hj; omega
        rw [pow_zero, Perm.one_apply, hpa] at hwj
        obtain ⟨-, hpath⟩ := (p.1.mem_branch).1 hwj
        exact ⟨mem_biUnion.2 ⟨p, mem_filter.2 ⟨hp, hpr⟩, hw⟩, hpath.mono hmono⟩
    rw [hbranch]
    exact (h𝒯.isCollapsibleOfColour p hp).isCollapsible
  obtain ⟨c', hc'⟩ := hcoll
  rcases hc'.root_cases with ⟨-, hcol⟩ | ⟨hb', -⟩
  · rw [hcol z (G.self_mem_vertexOf z)]
    exact hc'
  · exact absurd hb' hb

end MergeTree

end MergeTree

end PlabicData

end ClusterAlgebras
