/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CollapseFamilies

/-!
# Collapse steps for bivalent vertices

Let `𝒯` be a collapsing family of a plabic graph `G`. If a bivalent vertex is removed from `G`, or
inserted into an edge of `G`, there is a collapsing family of the new graph whose collapse is
isomorphic to `G/𝒯` or obtained from it by the same move. These are cases (III) and (IV) of the
source: the move lies outside the trees of the family, at a root, or inside a tree.

## Main results

* `ClusterAlgebras.PlabicData.exists_isomorphic_bivalentRemoval_collapse`,
  `ClusterAlgebras.PlabicData.exists_collapse_removal_inside`,
  `ClusterAlgebras.PlabicData.exists_collapse_removal_root`: removing a bivalent vertex.
* `ClusterAlgebras.PlabicData.exists_collapse_insertion_inside`,
  `ClusterAlgebras.PlabicData.exists_collapse_insertion_outside`,
  `ClusterAlgebras.PlabicData.exists_collapse_insertion_lollipopEdge`: inserting a bivalent
  vertex.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

namespace PlabicData

/-! ### Removing a bivalent vertex outside the trees -/

section RemovalOutside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

private theorem coe_bivalentRemoval_rot_symm (hG : G.IsPlabicGraph) {d : H}
    (hd : G.IsBivalentRemovable d) (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).rot.symm y : H) = G.rot.symm y := rfl

/-- A dart of the trees lies at a vertex of `U` or at a root. -/
private theorem notMem_familyDarts_of_forall {𝒯 : Finset (G.RootedTree × Shade)}
    (hG : G.IsPlabicGraph) {x : H}
    (hx : ∀ p ∈ 𝒯, G.vertexOf x ∉ p.1.nonRoot ∧ p.1.root ≠ G.vertexOf x) :
    x ∉ G.familyDarts 𝒯 := fun h => by
  obtain ⟨p, hp, hroot, -⟩ := exists_root_eq_of_mem_familyDarts hG h fun p hp => (hx p hp).1
  exact (hx p hp).2 hroot

variable (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d)
  {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯)
  (hx : ∀ p ∈ 𝒯, G.vertexOf d ∉ p.1.nonRoot ∧ p.1.root ≠ G.vertexOf d)

include hG hd h𝒯 hx

omit hd h𝒯 in
/-- The darts of the removed vertex are not darts of the trees. -/
private theorem removalOutside_notMem :
    d ∉ G.familyDarts 𝒯 ∧ G.rot d ∉ G.familyDarts 𝒯 := by
  refine ⟨notMem_familyDarts_of_forall hG hx, notMem_familyDarts_of_forall hG ?_⟩
  rw [G.vertexOf_rot]
  exact hx

omit hd h𝒯 in
/-- The trees of the family do not meet the removed vertex. -/
private theorem removalOutside_mem_compl {p : G.RootedTree × Shade} (hp : p ∈ 𝒯) {e : H}
    (he : e ∈ p.1.darts) : e ∈ ({d, G.rot d}ᶜ : Set H) := by
  obtain ⟨h1, h2⟩ := removalOutside_notMem hG hx
  refine mem_compl_pair.2 ⟨fun h => h1 ?_, fun h => h2 ?_⟩
  · exact mem_familyDarts.2 ⟨p, hp, h ▸ he⟩
  · exact mem_familyDarts.2 ⟨p, hp, h ▸ he⟩

omit h𝒯 in
/-- Each tree of the family embeds into the removal. -/
private theorem removalOutside_isEmbedding (x₀ : ({d, G.rot d}ᶜ : Set H))
    {p : G.RootedTree × Shade} (hp : p ∈ 𝒯) :
    p.1.IsEmbedding (G.bivalentRemoval hG hd) (toCompl d (G.rot d) x₀) := by
  have hinv := hG.inv_involutive
  have hc := fun {e} (he : e ∈ p.1.darts) => removalOutside_mem_compl hG hx hp he
  refine ⟨fun e he e' he' h => injOn_toCompl x₀ (hc he) (hc he') h, fun e he => ?_,
    fun e he he' => ?_, fun e he => ?_, ?_, ?_, ?_, fun e he => ?_⟩
  · apply Subtype.ext
    rw [toCompl_of_mem (hc (p.1.inv_mem_darts hG he)), toCompl_of_mem (hc he)]
    have h1 : e ≠ G.inv d := fun h => (mem_compl_pair.1 (hc (p.1.inv_mem_darts hG he))).1
      (by rw [h, hinv])
    have h2 : e ≠ G.inv (G.rot d) := fun h => (mem_compl_pair.1
      (hc (p.1.inv_mem_darts hG he))).2 (by rw [h, hinv])
    exact (coe_bivalentRemoval_inv_of_ne hG hd (y := ⟨e, hc he⟩) h1 h2).symm
  · apply Subtype.ext
    rw [toCompl_of_mem (hc he'), toCompl_of_mem (hc he), coe_bivalentRemoval_rot]
  · rw [toCompl_of_mem (hc he), mem_bivalentRemoval_bdry]
    exact p.1.notMem_bdry_of_mem_darts he
  · intro h
    obtain ⟨e, he, hfe⟩ := mem_image.1 h
    have := congrArg Subtype.val hfe
    rw [coe_toCompl_of_mem (hc he), toCompl_of_mem (hc p.1.intervalEnd_mem_darts),
      coe_bivalentRemoval_rot] at this
    exact p.1.rot_intervalEnd_notMem hG (this ▸ he)
  · intro h
    obtain ⟨e, he, hfe⟩ := mem_image.1 h
    have := congrArg Subtype.val hfe
    rw [coe_toCompl_of_mem (hc he), toCompl_of_mem (hc p.1.intervalStart_mem_darts),
      coe_bivalentRemoval_rot_symm] at this
    exact p.1.rot_symm_intervalStart_notMem (this ▸ he)
  · rw [toCompl_of_mem (hc p.1.intervalStart_mem_darts), ← card_map (Embedding.subtype _),
      map_bivalentRemoval_vertexOf]
    change p.1.intervalLength < (G.vertexOf p.1.intervalStart).card
    rw [← p.1.root_eq_vertexOf_intervalStart]
    exact p.1.intervalLength_lt_card
  · rw [toCompl_of_mem (hc he)]
    rfl

omit hd h𝒯 hx in
/-- The vertex of the collapse at a dart lying at a vertex outside `U` that is no root is the
vertex of `G`. -/
private theorem map_collapse_vertexOf_of_forall' {y : G.collapseDarts 𝒯}
    (hy : ∀ p ∈ 𝒯, G.vertexOf y ∉ p.1.nonRoot ∧ p.1.root ≠ G.vertexOf y) :
    ((G.collapse 𝒯).vertexOf y).map (Embedding.subtype _) = G.vertexOf y := by
  have hyK : (y : H) ∈ G.collapseCore 𝒯 := Or.inl (notMem_familyDarts_of_forall hG hy)
  rw [map_collapse_vertexOf_of_mem hyK,
    filter_vertexOf_mem_collapseCore_of_not hG (fun p hp => (hy p hp).1)
      (Or.inr fun p hp => (hy p hp).2)]


omit h𝒯 in
/-- The vertex `v(d)`, lying neither in a tree nor at a root, is a removable bivalent vertex of the
collapse, with the same rotation. -/
private theorem collapse_isBivalentRemovable :
    ∃ hdK : d ∈ G.collapseCore 𝒯, ((G.collapse 𝒯).rot ⟨d, Or.inl hdK⟩ : H) = G.rot d ∧
      (G.collapse 𝒯).IsBivalentRemovable ⟨d, Or.inl hdK⟩ := by
  obtain ⟨hdD, hσdD⟩ := removalOutside_notMem hG hx
  set X := G.collapse 𝒯 with hXdef
  set d' : G.collapseDarts 𝒯 := ⟨d, Or.inl (Or.inl hdD)⟩ with hd'def
  have hrot : (X.rot d' : H) = G.rot d := by
    rw [coe_collapse_rot_of_mem (show (d : H) ∈ G.collapseCore 𝒯 from Or.inl hdD),
      coe_firstReturn_of_apply_mem (show G.rot d ∈ G.collapseCore 𝒯 from Or.inl hσdD)]
  have hmap := map_collapse_vertexOf_of_forall' hG (y := d') hx
  refine ⟨Or.inl hdD, hrot, ?_, ?_, ?_⟩
  · rintro ⟨z, hz, hzB⟩
    apply hd.not_isBoundaryVertex
    refine ⟨z, ?_, mem_collapse_bdry.1 hzB⟩
    rw [← hmap]
    exact mem_map_of_mem _ hz
  · rw [← card_map (Embedding.subtype _), hmap]
    exact hd.card_vertexOf
  · intro h
    have := congrArg Subtype.val h
    rw [coe_collapse_inv hG, hrot] at this
    exact hd.inv_ne_rot this

/-- **Removing a bivalent vertex outside the trees**: the family is a collapsing family of the
removal, whose collapse is the removal of the vertex from the collapse. -/
theorem exists_isomorphic_bivalentRemoval_collapse :
    ∃ 𝒯' : Finset ((G.bivalentRemoval hG hd).RootedTree × Shade),
      (G.bivalentRemoval hG hd).IsCollapsingFamily 𝒯' ∧
      ∃ (d' : G.collapseDarts 𝒯) (hd' : (G.collapse 𝒯).IsBivalentRemovable d'),
        ((G.bivalentRemoval hG hd).collapse 𝒯').Isomorphic
          ((G.collapse 𝒯).bivalentRemoval (h𝒯.moveEquivalent_collapse hG).1 hd') := by
  obtain ⟨hdD, hσdD⟩ := removalOutside_notMem hG hx
  set x₀ : ({d, G.rot d}ᶜ : Set H) := ⟨G.leg ⟨0, hG.one_le⟩, hd.leg_mem hG _⟩
  have hemb := fun p (hp : p ∈ 𝒯) => removalOutside_isEmbedding hG hd hx x₀ hp
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  have hA := injOn_toCompl x₀
  have hDA : ∀ e ∈ G.familyDarts 𝒯, e ∈ ({d, G.rot d}ᶜ : Set H) := fun e he => by
    obtain ⟨p, hp, hep⟩ := mem_familyDarts.1 he
    exact removalOutside_mem_compl hG hx hp hep
  have hroot : ∀ p ∈ 𝒯, (G.bivalentRemoval hG hd).IsBoundaryVertex
      ((G.bivalentRemoval hG hd).vertexOf (toCompl d (G.rot d) x₀ p.1.intervalStart)) ↔
      G.IsBoundaryVertex p.1.root := fun p hp => by
    rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff,
      coe_toCompl_of_mem (hDA _ (mem_familyDarts.2 ⟨p, hp, p.1.intervalStart_mem_darts⟩)),
      ← p.1.root_eq_vertexOf_intervalStart]
  have hfree : ∀ p ∈ 𝒯, ∃ a ∈ ({d, G.rot d}ᶜ : Set H), a ∉ G.familyDarts 𝒯 ∧
      toCompl d (G.rot d) x₀ a ∈ (G.bivalentRemoval hG hd).vertexOf
        (toCompl d (G.rot d) x₀ p.1.intervalStart) := fun p hp => by
    obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root p hp
    have haD : a ∉ G.familyDarts 𝒯 := fun h => by
      obtain ⟨q, hq, haq'⟩ := mem_familyDarts.1 h
      exact haq q hq haq'
    have hav : G.vertexOf a = G.vertexOf d → False := fun h =>
      (hx p hp).2 (by rwa [p.1.mem_root_iff.1 ha] at h)
    have haC : a ∈ ({d, G.rot d}ᶜ : Set H) := mem_compl_pair.2
      ⟨fun h => hav (by rw [h]), fun h => hav (by rw [h, G.vertexOf_rot])⟩
    refine ⟨a, haC, haD, ?_⟩
    rw [mem_bivalentRemoval_vertexOf, coe_toCompl_of_mem haC,
      coe_toCompl_of_mem (hDA _ (mem_familyDarts.2 ⟨p, hp, p.1.intervalStart_mem_darts⟩)),
      ← p.1.root_eq_vertexOf_intervalStart]
    exact ha
  have h𝒯c := isCollapsingFamily_transportFamily hG hGr hemb h𝒯 hA hDA hroot hfree
  refine ⟨_, h𝒯c, ?_⟩
  set X := G.collapse 𝒯 with hXdef
  have hX : X.IsPlabicGraph := (h𝒯.moveEquivalent_collapse hG).1
  set d' : G.collapseDarts 𝒯 := ⟨d, Or.inl (Or.inl hdD)⟩ with hd'def
  have hrot : (X.rot d' : H) = G.rot d := by
    rw [coe_collapse_rot_of_mem (show (d : H) ∈ G.collapseCore 𝒯 from Or.inl hdD),
      coe_firstReturn_of_apply_mem (show G.rot d ∈ G.collapseCore 𝒯 from Or.inl hσdD)]
  have hmap := map_collapse_vertexOf_of_forall' hG (y := d') hx
  have hd' : X.IsBivalentRemovable d' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨z, hz, hzB⟩
      apply hd.not_isBoundaryVertex
      refine ⟨z, ?_, mem_collapse_bdry.1 hzB⟩
      rw [← hmap]
      exact mem_map_of_mem _ hz
    · rw [← card_map (Embedding.subtype _), hmap]
      exact hd.card_vertexOf
    · intro h
      have := congrArg Subtype.val h
      rw [coe_collapse_inv hG, hrot] at this
      exact hd.inv_ne_rot this
  refine ⟨d', hd', ?_⟩
  have hD : ∀ x : ({d, G.rot d}ᶜ : Set H), x ∈ (G.bivalentRemoval hG hd).familyDarts
      (transportFamily hG hGr hemb) ↔ (x : H) ∈ G.familyDarts 𝒯 := by
    intro x
    rw [mem_familyDarts_transportFamily]
    constructor
    · rintro ⟨e, he, rfl⟩
      rwa [coe_toCompl_of_mem (hDA e he)]
    · intro h
      exact ⟨x, h, toCompl_val x⟩
  have hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ transportFamily hG hGr hemb, G.leg i ∈ p₁.1.darts →
      (G.bivalentRemoval hG hd).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ hi₁ hi₂
    have hf : toCompl d (G.rot d) x₀ (G.leg i) = (G.bivalentRemoval hG hd).leg i :=
      toCompl_of_mem (hd.leg_mem hG i)
    obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hG hGr hemb hA hDA (hd.leg_mem hG i) hp₂
      (hf ▸ hi₂)
    rw [h𝒯.eq_of_mem_darts hG hp₁ hr hi₁ hir, hrc]
  have hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  have := isomorphic_collapse_cut_of_eq hG (bivalentRemoval_eq_cutData hG hd) hGr hD hdD hσdD
    hcol hcol₁ d' (X.rot d') rfl hrot (hd'.leg_mem hX)
  rw [bivalentRemoval_eq_cutData hX hd']
  exact this

end RemovalOutside

/-! ### Removing a bivalent vertex inside a tree -/

section RemovalVertices

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d)

/-- The vertex of the removal of `v(d)` corresponding to a vertex of `G`: its darts outside
`v(d)`. -/
private def restrictV (d : H) (G : PlabicData H b) (w : Finset H) :
    Finset ({d, G.rot d}ᶜ : Set H) :=
  w.subtype (· ∈ ({d, G.rot d}ᶜ : Set H))

omit [Fintype H] in
private theorem mem_restrictV {w : Finset H} {y : ({d, G.rot d}ᶜ : Set H)} :
    y ∈ restrictV d G w ↔ (y : H) ∈ w :=
  mem_subtype

include hd in
/-- A dart lies outside `v(d) = {d, σ d}` iff its vertex is not `v(d)`. -/
private theorem mem_compl_iff_vertexOf_ne {e : H} :
    e ∈ ({d, G.rot d}ᶜ : Set H) ↔ G.vertexOf e ≠ G.vertexOf d := by
  rw [mem_compl_pair]
  constructor
  · rintro ⟨h1, h2⟩ h
    rcases hd.mem_vertexOf_iff.1 (h ▸ G.self_mem_vertexOf e) with h' | h'
    · exact h1 h'
    · exact h2 h'
  · intro h
    exact ⟨fun h' => h (by rw [h']), fun h' => h (by rw [h', G.vertexOf_rot])⟩

include hG hd in
/-- The vertices of the removal are the restrictions of the vertices of `G`. -/
private theorem bivalentRemoval_vertexOf_eq (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).vertexOf y = restrictV d G (G.vertexOf y) := by
  ext z
  rw [mem_restrictV, mem_bivalentRemoval_vertexOf]

include hd in
/-- The restriction is injective on the vertices other than `v(d)`. -/
private theorem restrictV_injOn {w w' : Finset H} (hw : w ∈ G.vertices) (hw' : w' ∈ G.vertices)
    (hwx : w ≠ G.vertexOf d) (hw'x : w' ≠ G.vertexOf d) (h : restrictV d G w = restrictV d G w') :
    w = w' := by
  obtain ⟨e, rfl⟩ := G.mem_vertices.1 hw
  obtain ⟨e', rfl⟩ := G.mem_vertices.1 hw'
  have he : e ∈ ({d, G.rot d}ᶜ : Set H) := (mem_compl_iff_vertexOf_ne hd).2 hwx
  have : (⟨e, he⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ restrictV d G (G.vertexOf e') := by
    rw [← h, mem_restrictV]
    exact G.self_mem_vertexOf e
  rw [mem_restrictV] at this
  exact G.vertexOf_eq_of_mem this

omit [Fintype H] in
private theorem card_restrictV {w : Finset H} (hw : ∀ e ∈ w, e ∈ ({d, G.rot d}ᶜ : Set H)) :
    (restrictV d G w).card = w.card := by
  rw [restrictV, card_subtype, filter_true_of_mem hw]

private theorem coe_bivalentRemoval_rot_pow (y : ({d, G.rot d}ᶜ : Set H)) (n : ℕ) :
    (((G.bivalentRemoval hG hd).rot ^ n) y : H) = (G.rot ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, coe_bivalentRemoval_rot, ih, pow_succ',
      Perm.mul_apply]

end RemovalVertices

section RemovalTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d) (T : G.RootedTree)
  (hxW : G.vertexOf d ∈ T.nonRoot)

include hG hd hxW

/-- The darts `d̄` and `\overline{σ d}` at the neighbours of `v(d)` are not both at the root. -/
private theorem removalTree_inv_cases :
    G.vertexOf (G.inv d) ∈ T.nonRoot ∨ G.vertexOf (G.inv (G.rot d)) ∈ T.nonRoot := by
  have hinv := hG.inv_involutive
  have h1 := T.vertexOf_inv_mem d hxW
  have h2 := T.vertexOf_inv_mem (G.rot d) (by rwa [G.vertexOf_rot])
  rcases mem_insert.1 h1 with h1 | h1
  · rcases mem_insert.1 h2 with h2 | h2
    · exfalso
      refine T.false_of_parallel hG (T.mem_darts_of_vertexOf_mem hxW)
        (T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_rot])) hd.rot_ne
        (fun h => hd.inv_ne_rot h.symm) (G.vertexOf_rot d) (h2.trans h1.symm)
    · exact Or.inr h2
  · exact Or.inl h1

omit hxW in
/-- A vertex of the removal lies in the restricted non-root set iff its vertex in `G` is
non-root. -/
private theorem mem_image_restrictV_iff (z : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).vertexOf z ∈ (T.nonRoot.erase (G.vertexOf d)).image
      (restrictV d G) ↔ G.vertexOf z ∈ T.nonRoot := by
  rw [bivalentRemoval_vertexOf_eq hG hd, mem_image]
  constructor
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨hwx, hwW⟩ := mem_erase.1 hw
    rwa [← restrictV_injOn hd (G.mem_internalVertices.1 (T.nonRoot_subset hwW)).1
      (G.vertexOf_mem_vertices _) hwx ((mem_compl_iff_vertexOf_ne hd).1 z.2) hwz]
  · intro h
    exact ⟨_, mem_erase.2 ⟨(mem_compl_iff_vertexOf_ne hd).1 z.2, h⟩, rfl⟩

/-- The darts of the tree outside `v(d)`. -/
private theorem removalTree_mem_treeDarts_iff (y : ({d, G.rot d}ᶜ : Set H)) :
    y ∈ (G.bivalentRemoval hG hd).treeDarts ((T.nonRoot.erase (G.vertexOf d)).image
      (restrictV d G)) ↔ (y : H) ∈ T.darts := by
  have hinv := hG.inv_involutive
  rw [mem_treeDarts, mem_treeDarts, mem_image_restrictV_iff hG hd T,
    mem_image_restrictV_iff hG hd T, mem_bivalentRemoval_bdry]
  refine and_congr Iff.rfl ?_
  by_cases h₁ : (y : H) = G.inv d
  · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁, h₁, hinv]
    refine iff_of_true ?_ (Or.inr hxW)
    exact removalTree_inv_cases hG hd T hxW
  by_cases h₂ : (y : H) = G.inv (G.rot d)
  · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂, h₂, hinv]
    refine iff_of_true ?_ (Or.inr (by rwa [G.vertexOf_rot]))
    exact (removalTree_inv_cases hG hd T hxW).symm
  · rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]

/-- **The tree with `v(d)` removed**, a rooted tree of the removal of `v(d)`, for `v(d)` a non-root
vertex of `T`. -/
private noncomputable def removalTree : (G.bivalentRemoval hG hd).RootedTree :=
  have hinv := hG.inv_involutive
  have hrx : T.root ≠ G.vertexOf d := fun h => T.root_notMem_nonRoot (h ▸ hxW)
  have hroot : ∀ e ∈ T.root, e ∈ ({d, G.rot d}ᶜ : Set H) := fun e he =>
    (mem_compl_iff_vertexOf_ne hd).2 (by rwa [T.mem_root_iff.1 he])
  have ha1 : T.intervalStart ∈ ({d, G.rot d}ᶜ : Set H) := hroot _ T.intervalStart_mem_root
  have hroot' : restrictV d G T.root =
      (G.bivalentRemoval hG hd).vertexOf ⟨T.intervalStart, ha1⟩ := by
    rw [bivalentRemoval_vertexOf_eq hG hd, ← T.root_eq_vertexOf_intervalStart]
  have hD := removalTree_mem_treeDarts_iff hG hd T hxW
  have hmem := mem_image_restrictV_iff hG hd T
  have hvW : ∀ w ∈ T.nonRoot, ∃ e, G.vertexOf e = w := fun w hw =>
    G.mem_vertices.1 (G.mem_internalVertices.1 (T.nonRoot_subset hw)).1
  { root := restrictV d G T.root
    nonRoot := (T.nonRoot.erase (G.vertexOf d)).image (restrictV d G)
    root_mem_vertices := by rw [hroot']; exact (G.bivalentRemoval hG hd).vertexOf_mem_vertices _
    nonRoot_nonempty := by
      refine Nonempty.image ?_ _
      rcases removalTree_inv_cases hG hd T hxW with h | h
      · refine ⟨_, mem_erase.2 ⟨fun h' => ?_, h⟩⟩
        rcases hd.mem_vertexOf_iff.1 (h' ▸ G.self_mem_vertexOf (G.inv d)) with h'' | h''
        · exact hG.inv_ne d h''
        · exact hd.inv_ne_rot h''
      · refine ⟨_, mem_erase.2 ⟨fun h' => ?_, h⟩⟩
        rcases hd.mem_vertexOf_iff.1 (h' ▸ G.self_mem_vertexOf (G.inv (G.rot d))) with h'' | h''
        · exact hd.inv_rot_ne hG h''
        · exact hG.inv_ne _ h''
    nonRoot_subset := by
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hw'
      obtain ⟨hwx, hwW⟩ := mem_erase.1 hw
      obtain ⟨e, rfl⟩ := hvW w hwW
      have he : e ∈ ({d, G.rot d}ᶜ : Set H) := (mem_compl_iff_vertexOf_ne hd).2 hwx
      rw [← bivalentRemoval_vertexOf_eq hG hd ⟨e, he⟩]
      refine (G.bivalentRemoval hG hd).vertexOf_mem_internalVertices.2 ?_
      rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff]
      exact (G.vertexOf_mem_internalVertices).1 (T.nonRoot_subset hwW)
    root_notMem_nonRoot := by
      intro h
      obtain ⟨w, hw, hwr⟩ := mem_image.1 h
      obtain ⟨hwx, hwW⟩ := mem_erase.1 hw
      rw [restrictV_injOn hd (G.mem_internalVertices.1 (T.nonRoot_subset hwW)).1
        T.root_mem_vertices hwx hrx hwr] at hwW
      exact T.root_notMem_nonRoot hwW
    vertexOf_inv_mem := by
      intro y hy
      have hyW := (hmem y).1 hy
      have hyD : (y : H) ∈ T.darts := T.mem_darts_of_vertexOf_mem hyW
      have hiD : ((G.bivalentRemoval hG hd).inv y : H) ∈ T.darts :=
        (hD _).1 (inv_mem_treeDarts' (isPlabicGraph_bivalentRemoval hG hd) ((hD y).2 hyD))
      rcases T.vertexOf_mem_or_eq_root hG hiD with h | h
      · exact mem_insert_of_mem ((hmem _).2 h)
      · rw [bivalentRemoval_vertexOf_eq hG hd, h]
        exact mem_insert_self _ _
    exists_interval := by
      refine ⟨⟨T.intervalStart, ha1⟩, (mem_restrictV).2 T.intervalStart_mem_root,
        T.intervalLength, T.one_le_intervalLength, ?_, fun e he => ?_, ?_⟩
      · rw [card_restrictV hroot]
        exact T.intervalLength_lt_card
      · rw [hD, T.mem_darts_iff_of_mem_root ((mem_restrictV).1 he)]
        refine exists_congr fun j => and_congr Iff.rfl ?_
        rw [Subtype.ext_iff, coe_bivalentRemoval_rot_pow]
      · rw [hD, coe_bivalentRemoval_rot_symm]
        exact T.rot_symm_intervalStart_notMem
    card_image_edgeOf := by
      set D' := (G.bivalentRemoval hG hd).treeDarts
        ((T.nonRoot.erase (G.vertexOf d)).image (restrictV d G))
      have hGr := isPlabicGraph_bivalentRemoval hG hd
      have h1 := (G.bivalentRemoval hG hd).card_eq_two_mul_card_image_edgeOf
        (bivalentRemoval_inv_involutive hG hd) (bivalentRemoval_inv_ne hG hd)
        (S := D') fun y hy => inv_mem_treeDarts' hGr hy
      have h2 : D'.map (Embedding.subtype _) = (T.darts.erase d).erase (G.rot d) := by
        ext z
        simp only [mem_map, Embedding.coe_subtype, mem_erase]
        constructor
        · rintro ⟨y, hy, rfl⟩
          have := mem_compl_pair.1 y.2
          exact ⟨this.2, this.1, (hD y).1 hy⟩
        · rintro ⟨h2, h1, hz⟩
          exact ⟨⟨z, mem_compl_pair.2 ⟨h1, h2⟩⟩, (hD _).2 hz, rfl⟩
      have h3 : D'.card = T.darts.card - 2 := by
        rw [← card_map (Embedding.subtype _), h2, card_erase_of_mem, card_erase_of_mem]
        · rfl
        · exact T.mem_darts_of_vertexOf_mem hxW
        · exact mem_erase.2 ⟨hd.rot_ne, T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_rot])⟩
      have h4 : ((T.nonRoot.erase (G.vertexOf d)).image (restrictV d G)).card =
          T.nonRoot.card - 1 := by
        rw [card_image_of_injOn, card_erase_of_mem hxW]
        intro w hw w' hw' h
        exact restrictV_injOn hd (G.mem_internalVertices.1 (T.nonRoot_subset (mem_erase.1 hw).2)).1
          (G.mem_internalVertices.1 (T.nonRoot_subset (mem_erase.1 hw').2)).1 (mem_erase.1 hw).1
          (mem_erase.1 hw').1 h
      have h5 := T.card_darts hG
      have h6 : 1 ≤ T.nonRoot.card := card_pos.2 ⟨_, hxW⟩
      rw [h4]
      omega
    reflTransGen_treeAdj := by
      set W' := (T.nonRoot.erase (G.vertexOf d)).image (restrictV d G)
      let φ : Finset H → Finset ({d, G.rot d}ᶜ : Set H) := fun w =>
        if w = G.vertexOf d then restrictV d G (G.vertexOf (G.inv d)) else restrictV d G w
      have hφ : ∀ w, w ≠ G.vertexOf d → φ w = restrictV d G w := fun w hw => if_neg hw
      have hφx : φ (G.vertexOf d) = restrictV d G (G.vertexOf (G.inv d)) := if_pos rfl
      have hid : G.inv d ∈ ({d, G.rot d}ᶜ : Set H) := hd.inv_mem hG
      have hird : G.inv (G.rot d) ∈ ({d, G.rot d}ᶜ : Set H) := hd.inv_rot_mem hG
      have hadj : ∀ y : ({d, G.rot d}ᶜ : Set H), (y : H) ∈ T.darts →
          (G.bivalentRemoval hG hd).TreeAdj W' (restrictV d G (G.vertexOf y))
            (restrictV d G (G.vertexOf ((G.bivalentRemoval hG hd).inv y))) := fun y hy =>
        ⟨y, (hD y).2 hy, bivalentRemoval_vertexOf_eq hG hd y,
          bivalentRemoval_vertexOf_eq hG hd _⟩
      have hstep : ∀ u u₂, G.TreeAdj T.nonRoot u u₂ →
          Relation.ReflTransGen ((G.bivalentRemoval hG hd).TreeAdj W') (φ u) (φ u₂) := by
        rintro _ _ ⟨e, he, rfl, rfl⟩
        by_cases h1 : e = d
        · subst h1
          rw [hφx, hφ _ ((mem_compl_iff_vertexOf_ne hd).1 hid)]
        by_cases h2 : e = G.rot d
        · subst h2
          rw [G.vertexOf_rot, hφx, hφ _ ((mem_compl_iff_vertexOf_ne hd).1 hird)]
          refine Relation.ReflTransGen.single ?_
          have := hadj ⟨G.inv d, hid⟩ (T.inv_mem_darts hG (T.mem_darts_of_vertexOf_mem hxW))
          rwa [coe_bivalentRemoval_inv_of_eq_inv hG hd rfl] at this
        by_cases h3 : e = G.inv d
        · subst h3
          rw [hinv, hφx, hφ _ ((mem_compl_iff_vertexOf_ne hd).1 hid)]
        by_cases h4 : e = G.inv (G.rot d)
        · subst h4
          rw [hinv, G.vertexOf_rot, hφx, hφ _ ((mem_compl_iff_vertexOf_ne hd).1 hird)]
          refine Relation.ReflTransGen.single ?_
          have := hadj ⟨G.inv (G.rot d), hird⟩ he
          rwa [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd rfl] at this
        have heS : e ∈ ({d, G.rot d}ᶜ : Set H) := mem_compl_pair.2 ⟨h1, h2⟩
        have hieS : G.inv e ∈ ({d, G.rot d}ᶜ : Set H) := mem_compl_pair.2
          ⟨fun h => h3 (by rw [← h, hinv]), fun h => h4 (by rw [← h, hinv])⟩
        rw [hφ _ ((mem_compl_iff_vertexOf_ne hd).1 heS),
          hφ _ ((mem_compl_iff_vertexOf_ne hd).1 hieS)]
        refine Relation.ReflTransGen.single ?_
        have := hadj ⟨e, heS⟩ he
        rwa [coe_bivalentRemoval_inv_of_ne hG hd (y := ⟨e, heS⟩) h3 h4] at this
      intro u' hu'
      have hlift : ∀ w, Relation.ReflTransGen (G.TreeAdj T.nonRoot) T.root w →
          Relation.ReflTransGen ((G.bivalentRemoval hG hd).TreeAdj W') (φ T.root) (φ w) :=
        fun w h => Relation.ReflTransGen.lift' φ hstep h
      rcases mem_insert.1 hu' with rfl | hu'
      · exact .refl
      · obtain ⟨w, hw, rfl⟩ := mem_image.1 hu'
        obtain ⟨hwx, hwW⟩ := mem_erase.1 hw
        have := hlift w (T.reflTransGen_treeAdj w (mem_insert_of_mem hwW))
        rwa [hφ _ hrx, hφ _ hwx] at this }

namespace RemovalTree

omit hG hd in
private theorem root_ne : T.root ≠ G.vertexOf d := fun h' =>
  T.root_notMem_nonRoot (h' ▸ hxW)

omit hG in
private theorem intervalStart_mem_compl : T.intervalStart ∈ ({d, G.rot d}ᶜ : Set H) :=
  (mem_compl_iff_vertexOf_ne hd).2 (by
    rw [← T.root_eq_vertexOf_intervalStart]; exact root_ne T hxW)

private theorem mem_darts_iff (y : ({d, G.rot d}ᶜ : Set H)) :
    y ∈ (removalTree hG hd T hxW).darts ↔ (y : H) ∈ T.darts :=
  removalTree_mem_treeDarts_iff hG hd T hxW y

private theorem root_eq : (removalTree hG hd T hxW).root =
    (G.bivalentRemoval hG hd).vertexOf ⟨T.intervalStart, intervalStart_mem_compl hd T hxW⟩ := by
  change restrictV d G T.root = _
  rw [bivalentRemoval_vertexOf_eq hG hd, ← T.root_eq_vertexOf_intervalStart]

private theorem isBoundaryVertex_root_iff :
    (G.bivalentRemoval hG hd).IsBoundaryVertex (removalTree hG hd T hxW).root ↔
      G.IsBoundaryVertex T.root := by
  rw [root_eq, isBoundaryVertex_bivalentRemoval_vertexOf_iff, ← T.root_eq_vertexOf_intervalStart]

private theorem intervalStart_eq : (removalTree hG hd T hxW).intervalStart =
    ⟨T.intervalStart, intervalStart_mem_compl hd T hxW⟩ := by
  refine ((removalTree hG hd T hxW).eq_intervalStart_of_rot_symm_notMem ?_ ?_ ?_).symm
  · rw [mem_darts_iff]; exact T.intervalStart_mem_darts
  · rw [root_eq]; exact (G.bivalentRemoval hG hd).self_mem_vertexOf _
  · rw [mem_darts_iff, coe_bivalentRemoval_rot_symm]
    exact T.rot_symm_intervalStart_notMem

/-- The dart `d` of `P_T`. -/
private def dartD : T.Dart := ⟨.inl d, T.mem_darts_of_vertexOf_mem hxW⟩

omit hd in
private theorem rot_dartD : T.plabicData.rot (dartD T hxW) =
    ⟨.inl (G.rot d), T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_rot])⟩ :=
  T.rot_inl_of_mem hG _ _

/-- `v(d)` is a removable bivalent vertex of `P_T`. -/
private theorem isBivalentRemovable_dartD :
    T.plabicData.IsBivalentRemovable (dartD T hxW) := by
  have hσσ : G.rot (G.rot d) ∈ T.darts := by
    rw [hd.rot_rot]; exact T.mem_darts_of_vertexOf_mem hxW
  have hrr : T.plabicData.rot (T.plabicData.rot (dartD T hxW)) = dartD T hxW := by
    rw [rot_dartD hG T hxW, T.rot_inl_of_mem hG _ hσσ]
    exact Subtype.ext (by simp [dartD, hd.rot_rot])
  refine isBivalentRemovable_of_rot_rot hrr ?_ ?_ ?_ ?_
  · rw [rot_dartD hG T hxW]
    intro h
    exact hd.rot_ne (by simpa [dartD] using h)
  · rw [T.mem_bdry_plabicData]
    rintro (h | h) <;> simp [dartD, RootedTree.dartE, RootedTree.dartEBar] at h
  · rw [rot_dartD hG T hxW, T.mem_bdry_plabicData]
    rintro (h | h) <;> simp [RootedTree.dartE, RootedTree.dartEBar] at h
  · rw [rot_dartD hG T hxW, dartD, T.inv_inl hG]
    intro h
    exact hd.inv_ne_rot (by simpa using h)


/-- **The plabic graph of the tree with `v(d)` removed** is the removal of the bivalent vertex
`v(d)` from `P_T`. -/
private theorem plabicData_isomorphic :
    (T.plabicData.bivalentRemoval (T.isPlabicGraph_plabicData hG)
      (isBivalentRemovable_dartD hG hd T hxW)).Isomorphic
      (removalTree hG hd T hxW).plabicData := by
  have hinv := hG.inv_involutive
  set T' := removalTree hG hd T hxW with hT'
  set P := T.plabicData with hPdef
  have hP := T.isPlabicGraph_plabicData hG
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  set δ := dartD T hxW with hδdef
  have hδ := isBivalentRemovable_dartD hG hd T hxW
  set R := P.bivalentRemoval hP hδ with hRdef
  set x₀ : ({d, G.rot d}ᶜ : Set H) := ⟨T.intervalStart, intervalStart_mem_compl hd T hxW⟩
  set F : H ⊕ LollipopDart → ({d, G.rot d}ᶜ : Set H) ⊕ LollipopDart :=
    Sum.map (toCompl d (G.rot d) x₀) id with hF
  have hbv := isBoundaryVertex_root_iff hG hd T hxW
  have hrδ : P.rot δ = ⟨.inl (G.rot d), T.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_rot])⟩ :=
    rot_dartD hG T hxW
  -- a dart `inl a` of the removal is not `d` or `σ d`
  have hmemS : ∀ s : ({δ, P.rot δ}ᶜ : Set T.Dart), ∀ a, (s : T.Dart).1 = .inl a →
      a ∈ ({d, G.rot d}ᶜ : Set H) := by
    intro s a hs
    have := mem_compl_pair.1 s.2
    refine mem_compl_pair.2 ⟨fun h => this.1 (Subtype.ext ?_), fun h => this.2 (Subtype.ext ?_)⟩
    · rw [hs, h]; rfl
    · rw [hs, h, hrδ]
  have hmap : ∀ s : ({δ, P.rot δ}ᶜ : Set T.Dart), T'.IsDart (F (s : T.Dart).1) := by
    rintro ⟨⟨a | l, ha⟩, hs⟩
    · change toCompl d (G.rot d) x₀ a ∈ T'.darts
      rw [mem_darts_iff, coe_toCompl_of_mem (hmemS ⟨⟨_, ha⟩, hs⟩ a rfl)]
      exact ha
    · rcases l with _ | _ | _ | _
      · trivial
      · trivial
      · exact mt hbv.1 ha
      · exact mt hbv.1 ha
  let e : ({δ, P.rot δ}ᶜ : Set T.Dart) ≃ T'.Dart :=
    Equiv.ofBijective (fun s => ⟨F (s : T.Dart).1, hmap s⟩) ⟨by
      rintro ⟨⟨a | l, ha⟩, hs⟩ ⟨⟨a' | l', ha'⟩, hs'⟩ h <;>
        simp only [Subtype.mk.injEq, hF, Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq, id] at h
      · have := injOn_toCompl x₀ (hmemS ⟨⟨_, ha⟩, hs⟩ a rfl) (hmemS ⟨⟨_, ha'⟩, hs'⟩ a' rfl) h
        subst this
        rfl
      · subst h; rfl, by
      rintro ⟨y | l, hy⟩
      · have hyD : (y : H) ∈ T.darts := (mem_darts_iff hG hd T hxW y).1 hy
        have hs : (⟨.inl (y : H), hyD⟩ : T.Dart) ∈ ({δ, P.rot δ}ᶜ : Set T.Dart) := by
          refine mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩
          · have := congrArg Subtype.val h
            simp only [hδdef, dartD, Sum.inl.injEq] at this
            exact (mem_compl_pair.1 y.2).1 this
          · rw [hrδ] at h
            have := congrArg Subtype.val h
            simp only [Sum.inl.injEq] at this
            exact (mem_compl_pair.1 y.2).2 this
        refine ⟨⟨_, hs⟩, Subtype.ext ?_⟩
        change Sum.inl (toCompl d (G.rot d) x₀ y) = Sum.inl y
        rw [toCompl_val]
      · have hl : T.IsDart (.inr l) := by
          rcases l with _ | _ | _ | _
          · trivial
          · trivial
          · exact mt hbv.2 hy
          · exact mt hbv.2 hy
        refine ⟨⟨⟨.inr l, hl⟩, mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩⟩, rfl⟩
        · have := congrArg Subtype.val h
          simp [hδdef, dartD] at this
        · rw [hrδ] at h
          have := congrArg Subtype.val h
          simp at this⟩
  have he : ∀ s, ((e s : T'.Dart) : _ ⊕ LollipopDart) = F (s : T.Dart).1 := fun _ => rfl
  have hstart := intervalStart_eq hG hd T hxW
  have hfa1 : toCompl d (G.rot d) x₀ T.intervalStart = T'.intervalStart := by
    rw [hstart, toCompl_of_mem]
  refine ⟨Iso.ofEquivOfMapLeg e (fun s => Subtype.ext ?_) (fun s => Subtype.ext ?_) (fun s => ?_)
    (fun s _ => ?_) (fun i => Subtype.ext ?_)⟩
  · -- the involutions
    have hviδ : ((P.inv δ : T.Dart) : H ⊕ LollipopDart) = .inl (G.inv d) := by
      rw [T.coe_inv_plabicData hG]; rfl
    have hvirδ : ((P.inv (P.rot δ) : T.Dart) : H ⊕ LollipopDart) = .inl (G.inv (G.rot d)) := by
      rw [T.coe_inv_plabicData hG, hrδ]; rfl
    rw [he, T'.coe_inv_plabicData hGr, he]
    by_cases h₁ : (s : T.Dart) = P.inv δ
    · rw [coe_bivalentRemoval_inv_of_eq_inv hP hδ h₁, hvirδ]
      have hs1 : (s : T.Dart).1 = .inl (G.inv d) := by rw [h₁, hviδ]
      rw [hs1]
      simp only [hF, Sum.map_inl]
      congr 1
      apply Subtype.ext
      rw [coe_toCompl_of_mem (hd.inv_rot_mem hG),
        coe_bivalentRemoval_inv_of_eq_inv hG hd (coe_toCompl_of_mem (hd.inv_mem hG))]
    by_cases h₂ : (s : T.Dart) = P.inv (P.rot δ)
    · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hP hδ h₂, hviδ]
      have hs1 : (s : T.Dart).1 = .inl (G.inv (G.rot d)) := by rw [h₂, hvirδ]
      rw [hs1]
      simp only [hF, Sum.map_inl]
      congr 1
      apply Subtype.ext
      rw [coe_toCompl_of_mem (hd.inv_mem hG),
        coe_bivalentRemoval_inv_of_eq_inv_rot hG hd (coe_toCompl_of_mem (hd.inv_rot_mem hG))]
    rw [coe_bivalentRemoval_inv_of_ne hP hδ h₁ h₂, T.coe_inv_plabicData hG]
    rcases s with ⟨⟨a | l, ha⟩, hs⟩
    · have haS := hmemS ⟨⟨_, ha⟩, hs⟩ a rfl
      have h₁' : a ≠ G.inv d := fun h => h₁ (Subtype.ext (by rw [hviδ, ← h]))
      have h₂' : a ≠ G.inv (G.rot d) := fun h => h₂ (Subtype.ext (by rw [hvirδ, ← h]))
      have hiaS : G.inv a ∈ ({d, G.rot d}ᶜ : Set H) := mem_compl_pair.2
        ⟨fun h => h₁' (by rw [← h, hinv]), fun h => h₂' (by rw [← h, hinv])⟩
      simp only [hF, Sum.map_inl]
      congr 1
      apply Subtype.ext
      rw [coe_toCompl_of_mem hiaS, coe_bivalentRemoval_inv_of_ne hG hd
        (y := toCompl d (G.rot d) x₀ a) (by rwa [coe_toCompl_of_mem haS])
        (by rwa [coe_toCompl_of_mem haS]), coe_toCompl_of_mem haS]
    · rfl
  · -- the rotations
    rw [he, coe_bivalentRemoval_rot, T.coe_rot_plabicData hG, T'.coe_rot_plabicData hGr, he]
    rcases s with ⟨⟨a | (_ | _ | _ | _), ha⟩, hs⟩
    · have haS := hmemS ⟨⟨_, ha⟩, hs⟩ a rfl
      have hraS : G.rot a ∈ ({d, G.rot d}ᶜ : Set H) := (hd.rot_mem_iff a).2 haS
      have hrot : (G.bivalentRemoval hG hd).rot (toCompl d (G.rot d) x₀ a) =
          toCompl d (G.rot d) x₀ (G.rot a) := by
        apply Subtype.ext
        rw [coe_bivalentRemoval_rot, coe_toCompl_of_mem haS, coe_toCompl_of_mem hraS]
      change F (T.rotAux (.inl a)) = T'.rotAux (.inl (toCompl d (G.rot d) x₀ a))
      simp only [RootedTree.rotAux, hrot]
      have hiff : toCompl d (G.rot d) x₀ (G.rot a) ∈ T'.darts ↔ G.rot a ∈ T.darts := by
        rw [mem_darts_iff, coe_toCompl_of_mem hraS]
      by_cases h : G.rot a ∈ T.darts
      · rw [if_pos h, if_pos (hiff.2 h)]
        rfl
      · rw [if_neg h, if_neg (mt hiff.1 h)]
        by_cases hb : G.IsBoundaryVertex T.root
        · rw [if_pos hb, if_pos (hbv.2 hb)]; rfl
        · rw [if_neg hb, if_neg (mt hbv.1 hb)]; rfl
    · change F (T.rotAux (.inr .e)) = T'.rotAux (.inr .e)
      simp only [RootedTree.rotAux]
      by_cases hb : G.IsBoundaryVertex T.root
      · rw [if_pos hb, if_pos (hbv.2 hb), ← hfa1]; rfl
      · rw [if_neg hb, if_neg (mt hbv.1 hb)]; rfl
    · rfl
    · rfl
    · change F (T.rotAux (.inr .gBar)) = T'.rotAux (.inr .gBar)
      simp only [RootedTree.rotAux, ← hfa1]
      rfl
  · -- the boundaries
    rw [mem_bivalentRemoval_bdry, T'.mem_bdry_plabicData, T.mem_bdry_plabicData]
    rcases s with ⟨⟨a | (_ | _ | _ | _), ha⟩, hs⟩ <;>
      simp [RootedTree.dartE, RootedTree.dartEBar, e, hF]
  · -- the colours
    change T'.colourAux (F (s : T.Dart).1) = T.colourAux (s : T.Dart).1
    rcases s with ⟨⟨a | l, ha⟩, hs⟩
    · change (G.bivalentRemoval hG hd).colour (toCompl d (G.rot d) x₀ a) = G.colour a
      rw [bivalentRemoval_colour, coe_toCompl_of_mem (hmemS ⟨⟨_, ha⟩, hs⟩ a rfl)]
    · change (G.bivalentRemoval hG hd).colour T'.intervalStart = G.colour T.intervalStart
      rw [bivalentRemoval_colour, hstart]
  · -- the legs
    change F ((P.leg i : T.Dart) : H ⊕ LollipopDart) = (T'.legDart : _ ⊕ LollipopDart)
    change F (T.legDart : H ⊕ LollipopDart) = _
    rw [RootedTree.legDart, RootedTree.legDart]
    by_cases hb : G.IsBoundaryVertex T.root
    · rw [dif_pos hb, dif_pos (hbv.2 hb)]
      change Sum.inl (toCompl d (G.rot d) x₀ T.intervalStart) = Sum.inl T'.intervalStart
      rw [hfa1]
    · rw [dif_neg hb, dif_neg (mt hbv.1 hb)]
      rfl

end RemovalTree

end RemovalTree

/-! ### Moving the root of a tree to a boundary vertex -/

section RootCardTwo

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- A root with two darts consists of `a₁` and `σ a₁`. -/
private theorem RootedTree.mem_root_iff_of_card_eq_two (T : G.RootedTree)
    (hcard : T.root.card = 2) {e : H} :
    e ∈ T.root ↔ e = T.intervalStart ∨ e = G.rot T.intervalStart := by
  have hsub : ({T.intervalStart, G.rot T.intervalStart} : Finset H) ⊆ T.root := by
    intro e he
    rcases mem_insert.1 he with rfl | he
    · exact T.intervalStart_mem_root
    · rw [mem_singleton.1 he, T.mem_root_iff, G.vertexOf_rot, ← T.root_eq_vertexOf_intervalStart]
  have hne : G.rot T.intervalStart ≠ T.intervalStart := by
    intro h
    have hpow : ∀ n : ℕ, (G.rot ^ n) T.intervalStart = T.intervalStart := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ', Perm.mul_apply, ih, h]
    have : T.root ⊆ {T.intervalStart} := by
      intro e he
      rw [T.mem_root_iff, T.root_eq_vertexOf_intervalStart] at he
      have := (G.vertexOf_eq_vertexOf_iff).1 he.symm
      obtain ⟨n, rfl⟩ := this.exists_nat_pow_eq
      rw [mem_singleton, hpow]
    have := card_le_card this
    rw [hcard, card_singleton] at this
    omega
  have heq : ({T.intervalStart, G.rot T.intervalStart} : Finset H) = T.root :=
    eq_of_subset_of_card_le hsub (by rw [hcard, card_pair hne.symm])
  rw [← heq, mem_insert, mem_singleton]

end RootCardTwo

section ExtendTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) (T : G.RootedTree) {i : Fin b} (hx : ¬G.IsBoundaryVertex T.root)
  (hthin : ∀ e ∈ T.root, e ∉ T.darts → e = G.rot.symm T.intervalStart)
  (hσ : G.inv (G.rot.symm T.intervalStart) = G.leg i)

include hG hx hthin hσ

namespace ExtendTree

omit hx hσ in
private theorem rot_intervalEnd : G.rot T.intervalEnd = G.rot.symm T.intervalStart := by
  refine hthin _ ?_ (T.rot_intervalEnd_notMem hG)
  have := T.intervalEnd_mem_darts
  rcases T.vertexOf_mem_or_eq_root hG this with h | h
  · exact absurd (T.rot_mem_darts_of_vertexOf_mem h) (T.rot_intervalEnd_notMem hG)
  · rw [T.mem_root_iff, G.vertexOf_rot, h]

omit hG hx hthin hσ in
private theorem rot_symm_mem_root : G.rot.symm T.intervalStart ∈ T.root := by
  rw [T.mem_root_iff, ← G.vertexOf_rot, Equiv.apply_symm_apply, ← T.root_eq_vertexOf_intervalStart]

private theorem mem_treeDarts_iff {e : H} :
    e ∈ G.treeDarts (insert T.root T.nonRoot) ↔
      e ∈ T.darts ∨ e = G.rot.symm T.intervalStart ∨ e = G.leg i := by
  have hinv := hG.inv_involutive
  have hz := rot_symm_mem_root T
  rw [mem_treeDarts, mem_insert, mem_insert]
  constructor
  · rintro ⟨hB, (h | h) | (h | h)⟩
    · by_cases heD : e ∈ T.darts
      · exact Or.inl heD
      · exact Or.inr (Or.inl (hthin e (T.mem_root_iff.2 h) heD))
    · exact Or.inl (G.mem_treeDarts.2 ⟨hB, Or.inl h⟩)
    · by_cases heD : G.inv e ∈ T.darts
      · left
        have := T.inv_mem_darts hG heD
        rwa [hinv] at this
      · right; right
        rw [← hσ, ← hthin _ (T.mem_root_iff.2 h) heD, hinv]
    · exact Or.inl (G.mem_treeDarts.2 ⟨hB, Or.inr h⟩)
  · rintro (h | rfl | rfl)
    · obtain ⟨hB, h⟩ := G.mem_treeDarts.1 h
      exact ⟨hB, h.imp Or.inr Or.inr⟩
    · refine ⟨fun hB => hx ?_, Or.inl (Or.inl (T.mem_root_iff.1 hz))⟩
      rw [← T.mem_root_iff.1 hz]
      exact G.isBoundaryVertex_vertexOf_of_mem hB
    · refine ⟨hG.leg_notMem_bdry i, Or.inr (Or.inl ?_)⟩
      rw [← hσ, hinv]
      exact T.mem_root_iff.1 hz

end ExtendTree

/-- **The tree moved to a boundary root**: if all the darts of the root `v` of `T` except one, `z`,
lie in the interval, and `z` is joined to the leg `g_i`, then `(β(i), W ∪ {v})` is a rooted
tree. -/
private noncomputable def extendTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hD := fun e => ExtendTree.mem_treeDarts_iff hG T hx hthin hσ (e := e)
  have hz := ExtendTree.rot_symm_mem_root T
  have hbv : G.IsBoundaryVertex (G.bvertex i) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hxne : T.root ≠ G.bvertex i := fun h => hx (h ▸ hbv)
  have hWb : G.bvertex i ∉ T.nonRoot := fun h =>
    (G.mem_internalVertices.1 (T.nonRoot_subset h)).2 hbv
  have hgx : G.vertexOf (G.inv (G.leg i)) = T.root := by
    rw [← hσ, hinv]; exact T.mem_root_iff.1 hz
  { root := G.bvertex i
    nonRoot := insert T.root T.nonRoot
    root_mem_vertices := G.vertexOf_mem_vertices _
    nonRoot_nonempty := ⟨_, mem_insert_self _ _⟩
    nonRoot_subset := insert_subset (G.mem_internalVertices.2 ⟨T.root_mem_vertices, hx⟩)
      T.nonRoot_subset
    root_notMem_nonRoot := by
      rw [mem_insert, not_or]
      exact ⟨fun h => hxne h.symm, hWb⟩
    vertexOf_inv_mem := by
      intro e he
      rcases mem_insert.1 he with h | h
      · by_cases heD : e ∈ T.darts
        · exact mem_insert_of_mem (mem_insert_of_mem
            (T.vertexOf_inv_mem_nonRoot_of_mem_root heD (T.mem_root_iff.2 h)))
        · rw [hthin e (T.mem_root_iff.2 h) heD, hσ]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (T.vertexOf_inv_mem e h)
    exists_interval := by
      refine ⟨G.leg i, G.leg_mem_bvertex i, 1, le_rfl, ?_, fun e he => ?_, ?_⟩
      · rw [(hG.boundaryVertex_card _ (hG.bvertex_mem i)).1]; norm_num
      · have hnB : ∀ e ∈ G.bvertex i, e ∉ G.bdry → e = G.leg i := fun e he hB => by
          have : e ∈ (G.bvertex i).filter (· ∉ G.bdry) := mem_filter.2 ⟨he, hB⟩
          rwa [hG.filter_bvertex_notMem_bdry, mem_singleton] at this
        constructor
        · intro h
          exact ⟨0, one_pos, (hnB e he (G.mem_treeDarts.1 h).1).symm⟩
        · rintro ⟨j, hj, rfl⟩
          obtain rfl : j = 0 := by omega
          exact (hD _).2 (Or.inr (Or.inr rfl))
      · intro h
        have hmem : G.rot.symm (G.leg i) ∈ G.bvertex i := G.rot_symm_mem_vertexOf _
        have hne : G.rot.symm (G.leg i) ≠ G.leg i := fun h' => by
          have := G.rot.apply_symm_apply (G.leg i)
          rw [h'] at this
          exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hbv this
        refine (G.mem_treeDarts.1 h).1 (by_contra fun hB => hne ?_)
        have : G.rot.symm (G.leg i) ∈ (G.bvertex i).filter (· ∉ G.bdry) := mem_filter.2 ⟨hmem, hB⟩
        rwa [hG.filter_bvertex_notMem_bdry, mem_singleton] at this
    card_image_edgeOf := by
      have hD' : G.treeDarts (insert T.root T.nonRoot) =
          insert (G.rot.symm T.intervalStart) (insert (G.leg i) T.darts) := by
        ext e
        rw [hD, mem_insert, mem_insert]
        tauto
      have hlegD : G.leg i ∉ T.darts := fun h => by
        rcases T.vertexOf_mem_or_eq_root hG h with h' | h'
        · exact hWb h'
        · exact hxne h'.symm
      have hσD := T.rot_symm_intervalStart_notMem
      have hne : G.rot.symm T.intervalStart ≠ G.leg i := fun h => hx (by
        rwa [← T.mem_root_iff.1 hz, h])
      have h2 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
        (S := G.treeDarts (insert T.root T.nonRoot)) fun e he => by
          obtain ⟨hB, h⟩ := G.mem_treeDarts.1 he
          refine G.mem_treeDarts.2 ⟨fun h' => hB (hG.inv_mem_bdry_iff.1 h'), ?_⟩
          rw [hinv]; exact h.symm
      rw [hD', card_insert_of_notMem (by rw [mem_insert, not_or]; exact ⟨hne, hσD⟩),
        card_insert_of_notMem hlegD, T.card_darts hG] at h2
      rw [card_insert_of_notMem T.root_notMem_nonRoot, hD']
      omega
    reflTransGen_treeAdj := by
      have hmono : ∀ u u', G.TreeAdj T.nonRoot u u' → G.TreeAdj (insert T.root T.nonRoot) u u' := by
        rintro _ _ ⟨e, he, rfl, rfl⟩
        exact ⟨e, (hD e).2 (Or.inl he), rfl, rfl⟩
      have hstep : G.TreeAdj (insert T.root T.nonRoot) (G.bvertex i) T.root :=
        ⟨G.leg i, (hD _).2 (Or.inr (Or.inr rfl)), rfl, hgx⟩
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact .refl
      · exact Relation.ReflTransGen.head hstep
          ((T.reflTransGen_treeAdj u hu).mono hmono) }

namespace ExtendTree

private theorem darts_iff {e : H} : e ∈ (extendTree hG T hx hthin hσ).darts ↔
    e ∈ T.darts ∨ e = G.rot.symm T.intervalStart ∨ e = G.leg i :=
  mem_treeDarts_iff hG T hx hthin hσ

private theorem nonRoot_eq :
    (extendTree hG T hx hthin hσ).nonRoot = insert T.root T.nonRoot := rfl

private theorem isBoundaryVertex_root :
    G.IsBoundaryVertex (extendTree hG T hx hthin hσ).root :=
  G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

private theorem intervalStart_eq : (extendTree hG T hx hthin hσ).intervalStart = G.leg i :=
  (extendTree hG T hx hthin hσ).intervalStart_eq_leg hG rfl

/-- **The plabic graph of the moved tree** is the plabic graph of `T`: the leg `g_i` and the dart
`z` across it play the roles of `g` and `ḡ`. -/
private theorem plabicData_isomorphic :
    T.plabicData.Isomorphic (extendTree hG T hx hthin hσ).plabicData := by
  have hinv := hG.inv_involutive
  set T' := extendTree hG T hx hthin hσ with hT'
  have hb' : G.IsBoundaryVertex T'.root := isBoundaryVertex_root hG T hx hthin hσ
  have hstart : T'.intervalStart = G.leg i := intervalStart_eq hG T hx hthin hσ
  have hD := fun e => darts_iff hG T hx hthin hσ (e := e)
  set a := T.intervalStart with ha
  set z := G.rot.symm a with hzdef
  have hσg : G.inv (G.leg i) = z := by rw [← hσ, hinv]
  have hrz : G.rot z = a := Equiv.apply_symm_apply _ _
  have hend : G.rot T.intervalEnd = z := rot_intervalEnd hG T hthin
  have hzD : z ∉ T.darts := T.rot_symm_intervalStart_notMem
  have hz : z ∈ T.root := rot_symm_mem_root T
  have hbv : G.IsBoundaryVertex (G.bvertex i) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hσleg : G.rot (G.leg i) ∉ T'.darts := by
    intro h
    have hB : G.rot (G.leg i) ∈ G.bdry := by
      by_contra hB
      have : G.rot (G.leg i) ∈ (G.bvertex i).filter (· ∉ G.bdry) :=
        mem_filter.2 ⟨G.rot_mem_vertexOf _, hB⟩
      rw [hG.filter_bvertex_notMem_bdry, mem_singleton] at this
      exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hbv this
    exact (G.mem_treeDarts.1 h).1 hB
  -- the map of darts
  let ψ : H ⊕ LollipopDart → H ⊕ LollipopDart
    | .inl e => .inl e
    | .inr .e => .inr .e
    | .inr .eBar => .inr .eBar
    | .inr .g => .inl (G.leg i)
    | .inr .gBar => .inl z
  have hmap : ∀ s : T.Dart, T'.IsDart (ψ s.1) := by
    rintro ⟨e | (_ | _ | _ | _), he⟩
    · exact (hD e).2 (Or.inl he)
    · trivial
    · trivial
    · exact (hD _).2 (Or.inr (Or.inr rfl))
    · exact (hD _).2 (Or.inr (Or.inl rfl))
  have hlegD : G.leg i ∉ T.darts := fun h => by
    rcases T.vertexOf_mem_or_eq_root hG h with h' | h'
    · exact (G.mem_internalVertices.1 (T.nonRoot_subset h')).2 hbv
    · exact hx (h' ▸ hbv)
  have hne : z ≠ G.leg i := fun h => hx (by
    rwa [← T.mem_root_iff.1 hz, h])
  let χ : H ⊕ LollipopDart → H ⊕ LollipopDart
    | .inl e => if e = G.leg i then .inr .g else if e = z then .inr .gBar else .inl e
    | .inr l => .inr l
  have hχ : ∀ s : T.Dart, χ (ψ s.1) = s.1 := by
    rintro ⟨x | (_ | _ | _ | _), hx'⟩
    · change (if x = G.leg i then _ else _) = _
      rw [if_neg (by rintro rfl; exact hlegD hx'), if_neg (by rintro rfl; exact hzD hx')]
    · rfl
    · rfl
    · change (if G.leg i = G.leg i then _ else _) = _
      rw [if_pos rfl]
    · change (if z = G.leg i then _ else _) = _
      rw [if_neg hne, if_pos rfl]
  let e : T.Dart ≃ T'.Dart := Equiv.ofBijective (fun s => ⟨ψ s.1, hmap s⟩) ⟨by
      intro s s' h
      have := congrArg (fun t : T'.Dart => χ t.1) h
      simp only [hχ] at this
      exact Subtype.ext this, by
      rintro ⟨y | l, hy⟩
      · rcases (hD y).1 hy with h | rfl | rfl
        · exact ⟨⟨.inl y, h⟩, rfl⟩
        · exact ⟨⟨.inr .gBar, hx⟩, rfl⟩
        · exact ⟨⟨.inr .g, hx⟩, rfl⟩
      · rcases l with _ | _ | _ | _
        · exact ⟨⟨.inr .e, trivial⟩, rfl⟩
        · exact ⟨⟨.inr .eBar, trivial⟩, rfl⟩
        · exact absurd hb' hy
        · exact absurd hb' hy⟩
  have he : ∀ s, ((e s : T'.Dart) : H ⊕ LollipopDart) = ψ s.1 := fun _ => rfl
  -- the boundary darts of `P_T` lie at its boundary vertex
  have hbdryv : ∀ s : T.Dart, (s.1 = .inr .e ∨ s.1 = .inr .eBar ∨ s.1 = .inr .g) →
      T.plabicData.IsBoundaryVertex (T.plabicData.vertexOf s) := by
    rintro s hs
    refine ⟨T.dartE, ?_, (T.mem_bdry_plabicData).2 (Or.inl rfl)⟩
    rw [RotationSystem.mem_vertexOf]
    rcases hs with hs | hs | hs
    · rw [show s = T.dartE from Subtype.ext hs]
    · have : T.plabicData.rot s = T.dartE := Subtype.ext (by
        rw [T.coe_rot_plabicData hG, hs]; rfl)
      rw [← this]
      exact sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
    · have : T.plabicData.rot T.dartE = s := Subtype.ext (by
        rw [T.coe_rot_plabicData hG, hs]
        change T.rotAux (.inr .e) = _
        simp [RootedTree.rotAux, hx])
      rw [← this]
      exact (sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)).symm
  refine ⟨Iso.ofEquivOfMapLeg e (fun s => Subtype.ext ?_) (fun s => Subtype.ext ?_)
    (fun s => ?_) (fun s hs => ?_) (fun j => Subtype.ext ?_)⟩
  · rw [he, T'.coe_inv_plabicData hG, he, T.coe_inv_plabicData hG]
    rcases s with ⟨x | (_ | _ | _ | _), hx'⟩
    · rfl
    · rfl
    · rfl
    · change Sum.inl z = Sum.inl (G.inv (G.leg i))
      rw [hσg]
    · change Sum.inl (G.leg i) = Sum.inl (G.inv z)
      rw [← hσ]
  · rw [he, T'.coe_rot_plabicData hG, he, T.coe_rot_plabicData hG]
    rcases s with ⟨x | (_ | _ | _ | _), hx'⟩
    · change ψ (T.rotAux (.inl x)) = T'.rotAux (.inl x)
      simp only [RootedTree.rotAux, if_neg hx, if_pos hb']
      by_cases h : G.rot x ∈ T.darts
      · rw [if_pos h, if_pos ((hD _).2 (Or.inl h))]
      · rw [if_neg h, T.eq_intervalEnd hG hx' h, hend, if_pos ((hD _).2 (Or.inr (Or.inl rfl)))]
    · change ψ (T.rotAux (.inr .e)) = T'.rotAux (.inr .e)
      simp only [RootedTree.rotAux, if_neg hx, if_pos hb', hstart]
      rfl
    · rfl
    · change ψ (T.rotAux (.inr .g)) = T'.rotAux (.inl (G.leg i))
      simp only [RootedTree.rotAux, if_neg hσleg, if_pos hb']
      rfl
    · change ψ (T.rotAux (.inr .gBar)) = T'.rotAux (.inl z)
      have ha' : G.rot z ∈ T'.darts := by
        rw [hrz]; exact (hD a).2 (Or.inl T.intervalStart_mem_darts)
      simp only [RootedTree.rotAux]
      rw [if_pos ha', hrz]
  · rw [T'.mem_bdry_plabicData, T.mem_bdry_plabicData]
    rcases s with ⟨x | (_ | _ | _ | _), hx'⟩ <;>
      simp [RootedTree.dartE, RootedTree.dartEBar, e, ψ]
  · change T'.colourAux (ψ s.1) = T.colourAux s.1
    rcases s with ⟨x | (_ | _ | _ | _), hx'⟩
    · rfl
    · exact absurd (hbdryv _ (Or.inl rfl)) hs
    · exact absurd (hbdryv _ (Or.inr (Or.inl rfl))) hs
    · exact absurd (hbdryv _ (Or.inr (Or.inr rfl))) hs
    · change G.colour z = G.colour a
      rw [← hrz]
      exact (hG.colour_rot _ (by rwa [T.mem_root_iff.1 hz])).symm
  · change ψ (T.legDart : H ⊕ LollipopDart) = (T'.legDart : H ⊕ LollipopDart)
    rw [RootedTree.legDart, RootedTree.legDart, dif_neg hx, dif_pos hb']
    change Sum.inl (G.leg i) = Sum.inl T'.intervalStart
    rw [hstart]

end ExtendTree

end ExtendTree

/-! ### Removing a bivalent vertex of a tree -/

section RemovalInside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d)
  {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯)
  {p₀ : G.RootedTree × Shade} (hp₀ : p₀ ∈ 𝒯) (hxW : G.vertexOf d ∈ p₀.1.nonRoot)

include hG hd h𝒯 hp₀ hxW

open scoped Classical in
/-- **Removing a bivalent vertex of a tree**: the tree loses the vertex, or is dropped when it
becomes the edge of a lollipop, and the collapse does not change. -/
theorem exists_collapse_removal_inside :
    ∃ 𝒯' : Finset ((G.bivalentRemoval hG hd).RootedTree × Shade),
      (G.bivalentRemoval hG hd).IsCollapsingFamily 𝒯' ∧
      ((G.bivalentRemoval hG hd).collapse 𝒯').Isomorphic (G.collapse 𝒯) := by
  have hinv := hG.inv_involutive
  set S := ({d, G.rot d}ᶜ : Set H) with hS
  set T₀ := p₀.1 with hT₀
  set T' := removalTree hG hd T₀ hxW with hT'
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  set x₀ : S := ⟨T₀.intervalStart, RemovalTree.intervalStart_mem_compl hd T₀ hxW⟩
  set f := toCompl d (G.rot d) x₀ with hf
  have hA := injOn_toCompl x₀
  have hothers : ∀ q ∈ 𝒯.erase p₀, G.vertexOf d ∉ q.1.nonRoot ∧ q.1.root ≠ G.vertexOf d := by
    intro q hq
    have hqp := ne_of_mem_erase hq
    have hq' := mem_of_mem_erase hq
    refine ⟨fun h => disjoint_left.1 (h𝒯.disjoint_nonRoot p₀ hp₀ q hq' (Ne.symm hqp)) hxW h,
      fun h => h𝒯.root_notMem_nonRoot q hq' p₀ hp₀ hqp (h ▸ hxW)⟩
  have h𝒯e := h𝒯.subset (erase_subset p₀ 𝒯)
  have hemb' := fun q (hq : q ∈ 𝒯.erase p₀) => removalOutside_isEmbedding hG hd hothers x₀ hq
  have hDA' : ∀ e ∈ G.familyDarts (𝒯.erase p₀), e ∈ S := fun e he => by
    obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he
    exact removalOutside_mem_compl hG hothers hq heq
  have hroot : ∀ q ∈ 𝒯.erase p₀, (G.bivalentRemoval hG hd).IsBoundaryVertex
      ((G.bivalentRemoval hG hd).vertexOf (f q.1.intervalStart)) ↔ G.IsBoundaryVertex q.1.root :=
    fun q hq => by
      rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff,
        coe_toCompl_of_mem (hDA' _ (mem_familyDarts.2 ⟨q, hq, q.1.intervalStart_mem_darts⟩)),
        ← q.1.root_eq_vertexOf_intervalStart]
  -- a dart at a root other than `v(d)` lies outside `v(d)`
  have hrootS : ∀ q ∈ 𝒯, q.1.root ≠ G.vertexOf d → ∀ a ∈ q.1.root, a ∈ S := fun q _ hq a ha =>
    (mem_compl_iff_vertexOf_ne hd).2 (by rwa [q.1.mem_root_iff.1 ha])
  have hfreeD : ∀ q ∈ 𝒯, ∃ a ∈ q.1.root, a ∉ G.familyDarts 𝒯 := fun q hq => by
    obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root q hq
    exact ⟨a, ha, fun h => by
      obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
      exact haq r hr har⟩
  have hfree : ∀ q ∈ 𝒯.erase p₀, ∃ a ∈ S, a ∉ G.familyDarts 𝒯 ∧
      f a ∈ (G.bivalentRemoval hG hd).vertexOf (f q.1.intervalStart) := fun q hq => by
    obtain ⟨a, ha, haD⟩ := hfreeD q (mem_of_mem_erase hq)
    have haS := hrootS q (mem_of_mem_erase hq) (hothers q hq).2 a ha
    refine ⟨a, haS, haD, ?_⟩
    rw [mem_bivalentRemoval_vertexOf, coe_toCompl_of_mem haS,
      coe_toCompl_of_mem (hrootS q (mem_of_mem_erase hq) (hothers q hq).2 _
        q.1.intervalStart_mem_root), ← q.1.root_eq_vertexOf_intervalStart]
    exact ha
  have hT'D : ∀ y ∈ T'.darts, ∃ e ∈ T₀.darts, e ∈ S ∧ f e = y := fun y hy =>
    ⟨y, (RemovalTree.mem_darts_iff hG hd T₀ hxW y).1 hy, y.2, toCompl_val y⟩
  have hT'free : ∃ a ∈ S, a ∉ G.familyDarts 𝒯 ∧ f a ∈ T'.root := by
    obtain ⟨a, ha, haD⟩ := hfreeD p₀ hp₀
    have haS := hrootS p₀ hp₀ (RemovalTree.root_ne T₀ hxW) a ha
    refine ⟨a, haS, haD, ?_⟩
    change f a ∈ restrictV d G T₀.root
    rw [mem_restrictV, coe_toCompl_of_mem haS]
    exact ha
  -- the darts of the new family
  set 𝒯p := insert (T', p₀.2) (transportFamily hG hGr hemb') with h𝒯p
  have hD : ∀ y : S, y ∈ (G.bivalentRemoval hG hd).familyDarts 𝒯p ↔ (y : H) ∈ G.familyDarts 𝒯 := by
    intro y
    rw [mem_familyDarts_insert_transportFamily, RemovalTree.mem_darts_iff]
    constructor
    · rintro (h | ⟨e, he, hfe⟩)
      · exact mem_familyDarts.2 ⟨p₀, hp₀, h⟩
      · rw [← hfe, coe_toCompl_of_mem (hDA' e he)]
        obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he
        exact mem_familyDarts.2 ⟨q, mem_of_mem_erase hq, heq⟩
    · intro h
      obtain ⟨q, hq, hyq⟩ := mem_familyDarts.1 h
      by_cases hqp : q = p₀
      · subst hqp
        exact Or.inl hyq
      · exact Or.inr ⟨y, mem_familyDarts.2 ⟨q, mem_erase.2 ⟨hqp, hq⟩, hyq⟩, toCompl_val y⟩
  have hdD : d ∈ G.familyDarts 𝒯 := mem_familyDarts.2 ⟨p₀, hp₀, T₀.mem_darts_of_vertexOf_mem hxW⟩
  have hσdD : G.rot d ∈ G.familyDarts 𝒯 := mem_familyDarts.2 ⟨p₀, hp₀,
    T₀.mem_darts_of_vertexOf_mem (by rwa [G.vertexOf_rot])⟩
  have hQ : ∀ x, G.rot x ∈ (G.vertexOf d : Set H) ↔ x ∈ (G.vertexOf d : Set H) := fun x => by
    simp only [mem_coe, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hQK : ∀ x ∈ (G.vertexOf d : Set H), x ∉ G.collapseCore 𝒯 := by
    intro x hx
    have hvx : G.vertexOf x = G.vertexOf d := G.vertexOf_eq_of_mem (mem_coe.1 hx)
    rintro (h | ⟨i, rfl⟩)
    · exact h (mem_familyDarts.2 ⟨p₀, hp₀, T₀.mem_darts_of_vertexOf_mem (hvx ▸ hxW)⟩)
    · exact T₀.ne_leg_of_vertexOf_mem hG (hvx ▸ hxW) i rfl
  have hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  have hleg : ∀ i, f (G.leg i) = (G.bivalentRemoval hG hd).leg i := fun i =>
    toCompl_of_mem (hd.leg_mem hG i)
  have hcolT : ∀ i, ∀ p₁ ∈ 𝒯, ∀ q' ∈ transportFamily hG hGr hemb', G.leg i ∈ p₁.1.darts →
      (G.bivalentRemoval hG hd).leg i ∈ q'.1.darts → p₁.2 = q'.2 := by
    intro i p₁ hp₁ q' hq' h₁ h₂
    obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hG hGr hemb' hA hDA' (hd.leg_mem hG i) hq'
      (by rwa [toCompl_of_mem (hd.leg_mem hG i)])
    rw [h𝒯.eq_of_mem_darts hG hp₁ (mem_of_mem_erase hr) h₁ hir, hrc]
  have hcol : ∀ i, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯p, G.leg i ∈ p₁.1.darts →
      (G.bivalentRemoval hG hd).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    rcases mem_insert.1 hp₂ with rfl | hp₂
    · have : G.leg i ∈ T₀.darts := (RemovalTree.mem_darts_iff hG hd T₀ hxW _).1 h₂
      rw [h𝒯.eq_of_mem_darts hG hp₁ hp₀ h₁ this]
    · exact hcolT i p₁ hp₁ p₂ hp₂ h₁ h₂
  have hisoP := isomorphic_collapse_of_cut hG (bivalentRemoval_eq_cutData hG hd) hGr hD hdD hσdD
    _ hQ hQK (Or.inl (G.self_mem_vertexOf d)) hcol hcol₁
  -- `P_{T'}` is `{M2, M3}`-equivalent to `L_c`
  have hc := h𝒯.isCollapsibleOfColour p₀ hp₀
  have hPT' : PlabicGraph.MoveEquivalent {.m2, .m3}
      ⟨_, T'.plabicData, T'.isPlabicGraph_plabicData hGr⟩ (lollipopPlabicGraph p₀.2) := by
    have hloc : PlabicGraph.IsLocalMove .m2 ⟨_, T₀.plabicData, hc.isPlabicGraph⟩
        ⟨_, T'.plabicData, T'.isPlabicGraph_plabicData hGr⟩ :=
      Or.inl ⟨RemovalTree.dartD T₀ hxW, RemovalTree.isBivalentRemovable_dartD hG hd T₀ hxW,
        (RemovalTree.plabicData_isomorphic hG hd T₀ hxW).symm⟩
    exact (PlabicGraph.MoveEquivalent.of_isLocalMove (by simp) hloc).symm.trans hc.moveEquivalent
  by_cases hdrop : G.IsBoundaryVertex T₀.root ∧ T'.nonRoot.card = 1
  · -- the tree becomes the edge of a lollipop and is dropped
    obtain ⟨hb, h1⟩ := hdrop
    have hb' : (G.bivalentRemoval hG hd).IsBoundaryVertex T'.root :=
      (RemovalTree.isBoundaryVertex_root_iff hG hd T₀ hxW).2 hb
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.mem_boundaryVertices.2 ⟨T₀.root_mem_vertices, hb⟩)
    have hi' : T'.root = (G.bivalentRemoval hG hd).bvertex i := by
      rw [RemovalTree.root_eq, bvertex]
      congr 1
      apply Subtype.ext
      change T₀.intervalStart = G.leg i
      exact T₀.intervalStart_eq_leg hG hi.symm
    have hstart := T'.intervalStart_eq_leg hGr hi'
    obtain ⟨hD', hu⟩ := T'.darts_eq_of_card_nonRoot_eq_one hGr hb' h1
    -- the colour of the lollipop
    have hcol' : (G.bivalentRemoval hG hd).colour
        ((G.bivalentRemoval hG hd).inv T'.intervalStart) = p₀.2 := by
      obtain ⟨θ⟩ := T'.lollipop_isomorphic_of_card_nonRoot_eq_one hGr hb' h1
      exact eq_of_moveEquivalent_lollipopPlabicGraph
        ((PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
          (G := lollipopPlabicGraph _) (G' := ⟨_, T'.plabicData, T'.isPlabicGraph_plabicData hGr⟩)
          ⟨θ.symm⟩).trans hPT')
    have hemb'' := isCollapsingFamily_transportFamily hG hGr hemb' h𝒯e hA hDA' hroot
      (fun q hq => by
        obtain ⟨a, haS, haD, hav⟩ := hfree q hq
        exact ⟨a, haS, fun h => haD (by
          obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
          exact mem_familyDarts.2 ⟨r, mem_of_mem_erase hr, har⟩), hav⟩)
    refine ⟨_, hemb'', ?_⟩
    refine PlabicData.Isomorphic.trans _ ⟨collapseIsoAbsorb hGr (𝒯₂ := 𝒯p) (i := i) ?_ ?_ ?_ ?_ ?_
      ?_⟩ hisoP
    · intro y
      rw [mem_familyDarts_insert_transportFamily, hD', mem_insert, mem_singleton, ← hstart,
        ← mem_familyDarts_transportFamily hG hGr hemb']
      tauto
    · intro h
      obtain ⟨e, he, hfe⟩ := (mem_familyDarts_transportFamily hG hGr hemb').1 h
      have := congrArg Subtype.val hfe
      rw [coe_toCompl_of_mem (hDA' e he)] at this
      obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he
      have hlegT₀ : G.leg i ∈ T₀.darts := by
        rw [← T₀.intervalStart_eq_leg hG hi.symm]; exact T₀.intervalStart_mem_darts
      have he' : e = G.leg i := this
      subst he'
      exact ne_of_mem_erase hq (h𝒯.eq_of_mem_darts hG (mem_of_mem_erase hq) hp₀ heq hlegT₀)
    · intro y hy hne
      rw [← hstart] at hy hne
      rw [hu, mem_singleton] at hy
      exact absurd hy hne
    · intro p hp hip
      rcases mem_insert.1 hp with rfl | hp
      · rw [← hstart]
        exact hcol'.symm
      · exfalso
        obtain ⟨r, hr, hir, -⟩ := transportFamily_colour hG hGr hemb' hA hDA' (hd.leg_mem hG i) hp
          (by rwa [toCompl_of_mem (hd.leg_mem hG i)])
        have hlegT₀ : G.leg i ∈ T₀.darts := by
          rw [← T₀.intervalStart_eq_leg hG hi.symm]; exact T₀.intervalStart_mem_darts
        exact ne_of_mem_erase hr (h𝒯.eq_of_mem_darts hG (mem_of_mem_erase hr) hp₀ hir hlegT₀)
    · intro j p₁ hp₁ p₂ hp₂ h₁ h₂
      rcases mem_insert.1 hp₂ with rfl | hp₂
      · exfalso
        obtain ⟨r, hr, hjr, -⟩ := transportFamily_colour hG hGr hemb' hA hDA' (hd.leg_mem hG j)
          hp₁ (by rwa [toCompl_of_mem (hd.leg_mem hG j)])
        have : G.leg j ∈ T₀.darts := (RemovalTree.mem_darts_iff hG hd T₀ hxW _).1 h₂
        exact ne_of_mem_erase hr (h𝒯.eq_of_mem_darts hG (mem_of_mem_erase hr) hp₀ hjr this)
      · rw [hemb''.eq_of_mem_darts hGr hp₁ hp₂ h₁ h₂]
    · intro j p₁ hp₁ p₂ hp₂ h₁ h₂
      rw [hemb''.eq_of_mem_darts hGr hp₁ hp₂ h₁ h₂]
  · -- the tree stays collapsible
    have hT' : T'.IsCollapsibleOfColour p₀.2 := by
      refine ⟨T'.isPlabicGraph_plabicData hGr, hPT', ?_⟩
      rcases hc.root_cases with ⟨hb, hcol'⟩ | ⟨hb, h2⟩
      · refine Or.inl ⟨mt (RemovalTree.isBoundaryVertex_root_iff hG hd T₀ hxW).1 hb, ?_⟩
        intro y hy
        rw [bivalentRemoval_colour]
        exact hcol' _ ((mem_restrictV).1 hy)
      · refine Or.inr ⟨(RemovalTree.isBoundaryVertex_root_iff hG hd T₀ hxW).2 hb, ?_⟩
        have hpos : 0 < T'.nonRoot.card := T'.nonRoot_nonempty.card_pos
        have : T'.nonRoot.card ≠ 1 := fun h => hdrop ⟨hb, h⟩
        omega
    refine ⟨𝒯p, ?_, hisoP⟩
    exact isCollapsingFamily_insert_transportFamily hG hGr h𝒯 hp₀ hemb' hA hDA' hroot hfree hT'
      hT'D hT'free

end RemovalInside

/-! ### Removing a bivalent root -/

section RemovalRoot

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d)
  {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯)
  (hnl : (G.collapse 𝒯).IsNearlyLeafless) (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1)
  {p₀ : G.RootedTree × Shade} (hp₀ : p₀ ∈ 𝒯) (hroot : p₀.1.root = G.vertexOf d)
  (hU : ∀ p ∈ 𝒯, G.vertexOf d ∉ p.1.nonRoot)

include hG hd h𝒯 hnl hbr hp₀ hroot hU

open scoped Classical in
/-- **Removing a bivalent root**: the root `v(d)` of a tree keeps one dart in the collapse, which
is a lollipop since the collapse is nearly leafless; the tree is then moved to the boundary vertex
of the lollipop, and `v(d)` becomes a non-root vertex of a tree. -/
theorem exists_collapse_removal_root :
    ∃ 𝒯' : Finset ((G.bivalentRemoval hG hd).RootedTree × Shade),
      (G.bivalentRemoval hG hd).IsCollapsingFamily 𝒯' ∧
      ((G.bivalentRemoval hG hd).collapse 𝒯').Isomorphic (G.collapse 𝒯) := by
  have hinv := hG.inv_involutive
  set T₀ := p₀.1 with hT₀
  set a := T₀.intervalStart with ha
  have h1 := hbr p₀ hp₀
  have hx : ¬G.IsBoundaryVertex T₀.root := by rw [hroot]; exact hd.not_isBoundaryVertex
  have hcard : T₀.root.card = 2 := by rw [hroot]; exact hd.card_vertexOf
  have hmemx := fun e => T₀.mem_root_iff_of_card_eq_two hcard (e := e)
  have haD : a ∈ T₀.darts := T₀.intervalStart_mem_darts
  -- the second dart of the root lies outside the trees
  have hσaD : G.rot a ∉ G.familyDarts 𝒯 := by
    obtain ⟨y, hy, hyq⟩ := h𝒯.exists_mem_root p₀ hp₀
    rcases (hmemx y).1 hy with rfl | rfl
    · exact absurd haD (hyq p₀ hp₀)
    · intro h
      obtain ⟨q, hq, hyq'⟩ := mem_familyDarts.1 h
      exact hyq q hq hyq'
  have hσaK : G.rot a ∈ G.collapseCore 𝒯 := Or.inl hσaD
  have hvσa : G.vertexOf (G.rot a) = T₀.root := by
    rw [G.vertexOf_rot, ← T₀.root_eq_vertexOf_intervalStart]
  -- in the collapse, the vertex of `σ a` is `{σ a}`
  set y : G.collapseDarts 𝒯 := ⟨G.rot a, Or.inl hσaK⟩ with hy
  have hmapy : ((G.collapse 𝒯).vertexOf y).map (Embedding.subtype _) = {G.rot a} := by
    rw [map_collapse_vertexOf_of_mem hσaK]
    ext z
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hz, hzK⟩
      rw [G.mem_vertexOf, ← G.vertexOf_eq_vertexOf_iff, hvσa] at hz
      rcases (hmemx z).1 (T₀.mem_root_iff.2 hz.symm) with rfl | rfl
      · exfalso
        rcases hzK with h | ⟨j, hj⟩
        · exact h (mem_familyDarts.2 ⟨p₀, hp₀, haD⟩)
        · exact hx (by rw [T₀.root_eq_vertexOf_intervalStart, hj]
                       exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j))
      · rfl
    · rintro rfl
      exact ⟨G.self_mem_vertexOf _, hσaK⟩
  have hleaf : (G.collapse 𝒯).IsInternalLeaf ((G.collapse 𝒯).vertexOf y) := by
    refine ⟨(G.collapse 𝒯).vertexOf_mem_internalVertices.2 ?_, ?_⟩
    · rintro ⟨z, hz, hzB⟩
      have : (z : H) ∈ ({G.rot a} : Finset H) := by
        rw [← hmapy]; exact mem_map_of_mem _ hz
      rw [mem_singleton] at this
      apply hx
      rw [← hvσa, ← this]
      exact G.isBoundaryVertex_vertexOf_of_mem (mem_collapse_bdry.1 hzB)
    · rw [← card_map (Embedding.subtype _), hmapy, card_singleton]
  -- it is a lollipop: `σ a` is joined to a leg
  obtain ⟨i, -, z, hz, hzi⟩ := hnl _ hleaf
  have hzy : (z : H) = G.rot a := by
    have : (z : H) ∈ ({G.rot a} : Finset H) := by rw [← hmapy]; exact mem_map_of_mem _ hz
    exact mem_singleton.1 this
  have hσ : ∃ j, G.inv (G.rot a) = G.leg j := by
    have hzi' : ((G.collapse 𝒯).inv z : H) ∈ G.bvertex i := by
      have := map_collapse_vertexOf_of_mem (𝒯 := 𝒯) (x := (G.collapse 𝒯).leg i)
        (G.leg_mem_collapseCore 𝒯 i)
      have hmem : ((G.collapse 𝒯).inv z : H) ∈
          ((G.collapse 𝒯).vertexOf ((G.collapse 𝒯).leg i)).map (Embedding.subtype _) :=
        mem_map_of_mem _ hzi
      rw [this] at hmem
      exact (mem_filter.1 hmem).1
    rw [coe_collapse_inv hG, hzy] at hzi'
    refine hG.exists_eq_leg_of_isBoundaryVertex ?_ ?_
    · rw [G.vertexOf_eq_of_mem hzi']
      exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
    · intro hB
      exact hx (by rw [← hvσa]; exact G.isBoundaryVertex_vertexOf_of_mem (hG.inv_mem_bdry_iff.1 hB))
  obtain ⟨j, hσ⟩ := hσ
  -- the moved tree
  have hrr : G.rot (G.rot a) = a := by
    rcases hd.mem_vertexOf_iff.1 (show a ∈ G.vertexOf d by
      rw [← hroot]; exact T₀.intervalStart_mem_root) with h | h <;> rw [h, hd.rot_rot]
  have hsym : G.rot.symm a = G.rot a := by rw [Equiv.symm_apply_eq, hrr]
  have hσ' : G.inv (G.rot.symm a) = G.leg j := by rwa [hsym]
  have hthin : ∀ e ∈ T₀.root, e ∉ T₀.darts → e = G.rot.symm a := by
    intro e he heD
    rcases (hmemx e).1 he with rfl | rfl
    · exact absurd haD heD
    · exact hsym.symm
  set Tp := extendTree hG T₀ hx hthin hσ' with hTp
  have hDp : ∀ e, e ∈ Tp.darts ↔ e ∈ T₀.darts ∨ e = G.rot a ∨ e = G.leg j := fun e => by
    rw [ExtendTree.darts_iff, hsym]
  have hc := h𝒯.isCollapsibleOfColour p₀ hp₀
  have hcolx : ∀ e ∈ T₀.root, G.colour e = p₀.2 := by
    rcases hc.root_cases with h | h
    · exact h.2
    · exact absurd h.1 hx
  have hbv : G.IsBoundaryVertex (G.bvertex j) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem j)
  have hlegD : G.leg j ∉ G.familyDarts 𝒯 := fun h => hσaD (by
    have := inv_mem_familyDarts hG h
    rwa [← hσ, hinv] at this)
  have hTp : Tp.IsCollapsibleOfColour p₀.2 := by
    obtain ⟨θ⟩ := ExtendTree.plabicData_isomorphic hG T₀ hx hthin hσ'
    refine ⟨Tp.isPlabicGraph_plabicData hG, ?_, Or.inr ⟨ExtendTree.isBoundaryVertex_root hG T₀ hx
      hthin hσ', ?_⟩⟩
    · exact (PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
        (G := ⟨_, Tp.plabicData, Tp.isPlabicGraph_plabicData hG⟩)
        (G' := ⟨_, T₀.plabicData, hc.isPlabicGraph⟩) ⟨θ⟩).trans hc.moveEquivalent
    · rw [ExtendTree.nonRoot_eq, card_insert_of_notMem T₀.root_notMem_nonRoot]
      have := T₀.nonRoot_nonempty.card_pos
      omega
  -- no other tree has its root at `v(d)` or at `β(j)`
  have hother : ∀ q ∈ 𝒯, q ≠ p₀ → q.1.root ≠ T₀.root ∧ q.1.root ≠ G.bvertex j := by
    intro q hq hqp
    constructor
    · intro hqr
      have hq1 := q.1.intervalStart_mem_darts
      rcases (hmemx _).1 (hqr ▸ q.1.intervalStart_mem_root) with h | h
      · exact hqp (h𝒯.eq_of_mem_darts hG hq hp₀ hq1 (h ▸ haD))
      · exact hσaD (mem_familyDarts.2 ⟨q, hq, h ▸ hq1⟩)
    · intro hqr
      apply hlegD
      rw [← q.1.intervalStart_eq_leg hG hqr]
      exact mem_familyDarts.2 ⟨q, hq, q.1.intervalStart_mem_darts⟩
  set 𝒯p := insert (Tp, p₀.2) (𝒯.erase p₀) with h𝒯p
  have hDp' : ∀ e, e ∈ G.familyDarts 𝒯p ↔
      e ∈ G.familyDarts 𝒯 ∨ e = G.leg j ∨ e = G.inv (G.leg j) := by
    intro e
    rw [mem_familyDarts, mem_familyDarts]
    constructor
    · rintro ⟨q, hq, heq⟩
      rcases mem_insert.1 hq with rfl | hq
      · rcases (hDp e).1 heq with h | h | h
        · exact Or.inl ⟨p₀, hp₀, h⟩
        · exact Or.inr (Or.inr (by rw [h, ← hσ, hinv]))
        · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨q, mem_of_mem_erase hq, heq⟩
    · rintro (⟨q, hq, heq⟩ | h | h)
      · by_cases hqp : q = p₀
        · subst hqp
          exact ⟨_, mem_insert_self _ _, (hDp e).2 (Or.inl heq)⟩
        · exact ⟨q, mem_insert_of_mem (mem_erase.2 ⟨hqp, hq⟩), heq⟩
      · exact ⟨_, mem_insert_self _ _, (hDp e).2 (Or.inr (Or.inr h))⟩
      · refine ⟨_, mem_insert_self _ _, (hDp e).2 (Or.inr (Or.inl ?_))⟩
        rw [h, ← hσ, hinv]
  have h𝒯p : G.IsCollapsingFamily 𝒯p := by
    refine ⟨fun q hq => ?_, fun q₁ hq₁ q₂ hq₂ hne => ?_, fun q₁ hq₁ q₂ hq₂ hne => ?_,
      fun q hq => ?_⟩
    · rcases mem_insert.1 hq with rfl | hq
      · exact hTp
      · exact h𝒯.isCollapsibleOfColour q (mem_of_mem_erase hq)
    · have key : ∀ q ∈ 𝒯.erase p₀, Disjoint Tp.nonRoot q.1.nonRoot := fun q hq => by
        rw [ExtendTree.nonRoot_eq, disjoint_insert_left]
        exact ⟨by rw [hroot]; exact hU q (mem_of_mem_erase hq),
          h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq) (ne_of_mem_erase hq).symm⟩
      rcases mem_insert.1 hq₁ with rfl | hq₁ <;> rcases mem_insert.1 hq₂ with rfl | hq₂
      · exact absurd rfl hne
      · exact key q₂ hq₂
      · exact (key q₁ hq₁).symm
      · exact h𝒯.disjoint_nonRoot q₁ (mem_of_mem_erase hq₁) q₂ (mem_of_mem_erase hq₂) hne
    · rcases mem_insert.1 hq₁ with rfl | hq₁ <;> rcases mem_insert.1 hq₂ with rfl | hq₂
      · exact absurd rfl hne
      · intro h
        exact (G.mem_internalVertices.1 (q₂.1.nonRoot_subset h)).2 hbv
      · rw [ExtendTree.nonRoot_eq, mem_insert, not_or]
        exact ⟨(hother q₁ (mem_of_mem_erase hq₁) (ne_of_mem_erase hq₁)).1,
          h𝒯.root_notMem_nonRoot q₁ (mem_of_mem_erase hq₁) p₀ hp₀ (ne_of_mem_erase hq₁)⟩
      · exact h𝒯.root_notMem_nonRoot q₁ (mem_of_mem_erase hq₁) q₂ (mem_of_mem_erase hq₂) hne
    · rcases mem_insert.1 hq with rfl | hq
      · obtain ⟨e, he, heB⟩ := hbv
        refine ⟨e, he, fun q' _ heq => (G.mem_treeDarts.1 heq).1 heB⟩
      · obtain ⟨e, he, heq⟩ := h𝒯.exists_mem_root q (mem_of_mem_erase hq)
        refine ⟨e, he, fun q' hq' heq' => ?_⟩
        rcases mem_insert.1 hq' with rfl | hq'
        · rcases (hDp e).1 heq' with h | h | h
          · exact heq p₀ hp₀ h
          · apply (hother q (mem_of_mem_erase hq) (ne_of_mem_erase hq)).1
            rw [← q.1.mem_root_iff.1 he, h, hvσa]
          · apply (hother q (mem_of_mem_erase hq) (ne_of_mem_erase hq)).2
            rw [← q.1.mem_root_iff.1 he, h]
            rfl
        · exact heq q' (mem_of_mem_erase hq') heq'
  -- the collapses of `𝒯` and of `𝒯p` agree
  have hcolj : ∀ k, ∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯p, G.leg k ∈ p₁.1.darts → G.leg k ∈ p₂.1.darts →
      p₁.2 = p₂.2 := by
    intro k p₁ hp₁ p₂ hp₂ h₁ h₂
    rcases mem_insert.1 hp₂ with rfl | hp₂
    · rcases (hDp _).1 h₂ with h | h | h
      · rw [h𝒯.eq_of_mem_darts hG hp₁ hp₀ h₁ h]
      · exfalso
        exact hx (by rw [← hvσa, ← h]
                     exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem k))
      · exfalso
        rw [hG.leg_injective h] at h₁
        exact hlegD (mem_familyDarts.2 ⟨p₁, hp₁, h₁⟩)
    · rw [h𝒯.eq_of_mem_darts hG hp₁ (mem_of_mem_erase hp₂) h₁ h₂]
  have hiso₁ := collapseIsoAbsorb hG (𝒯₁ := 𝒯) (𝒯₂ := 𝒯p) (i := j) hDp' hlegD
    (fun e he hne => by
      rw [← hσ, hinv, G.mem_vertexOf, ← G.vertexOf_eq_vertexOf_iff, hvσa] at he
      rw [← hσ, hinv] at hne
      rcases (hmemx e).1 (T₀.mem_root_iff.2 he.symm) with rfl | rfl
      · exact mem_familyDarts.2 ⟨p₀, hp₀, haD⟩
      · exact absurd rfl hne)
    (fun q hq hjq => by
      rcases mem_insert.1 hq with rfl | hq
      · rw [← hσ, hinv]
        exact (hcolx _ ((hmemx _).2 (Or.inr rfl))).symm
      · exact absurd (mem_familyDarts.2 ⟨q, mem_of_mem_erase hq, hjq⟩) hlegD)
    hcolj (fun k q hq q' hq' h₁ h₂ => by rw [h𝒯.eq_of_mem_darts hG hq hq' h₁ h₂])
  have hnlp := hiso₁.isNearlyLeafless (h𝒯.moveEquivalent_collapse hG).1
    (h𝒯p.moveEquivalent_collapse hG).1 hnl
  have hxW : G.vertexOf d ∈ (Tp, p₀.2).1.nonRoot := by
    rw [ExtendTree.nonRoot_eq, ← hroot]
    exact mem_insert_self _ _
  obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_removal_inside hG hd h𝒯p (mem_insert_self _ _) hxW
  exact ⟨𝒯', h𝒯', PlabicData.Isomorphic.trans _ θ ⟨hiso₁.symm⟩⟩

end RemovalRoot

/-! ### Inserting a bivalent vertex into a tree -/

section InsertTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d)

/-- The vertex of `G` corresponding to a vertex of the removal of `v(d)`. -/
private def liftV (d : H) (G : PlabicData H b) (w : Finset ({d, G.rot d}ᶜ : Set H)) : Finset H :=
  w.map (Embedding.subtype _)

omit [Fintype H] [DecidableEq H] in
private theorem mem_liftV {w : Finset ({d, G.rot d}ᶜ : Set H)} {e : H} :
    e ∈ liftV d G w ↔
      ∃ h : e ∈ ({d, G.rot d}ᶜ : Set H), (⟨e, h⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ w := by
  simp [liftV]

include hG hd in
private theorem liftV_vertexOf (y : ({d, G.rot d}ᶜ : Set H)) :
    liftV d G ((G.bivalentRemoval hG hd).vertexOf y) = G.vertexOf y :=
  map_bivalentRemoval_vertexOf hG hd y

omit [Fintype H] [DecidableEq H] in
private theorem liftV_injective : Injective (liftV d G) := map_injective _

omit [Fintype H] in
private theorem restrictV_liftV (w : Finset ({d, G.rot d}ᶜ : Set H)) :
    restrictV d G (liftV d G w) = w := by
  ext y
  rw [mem_restrictV, mem_liftV]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨y.2, h⟩⟩

variable (T : (G.bivalentRemoval hG hd).RootedTree)
  (hy : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ T.darts)

include hy

namespace InsertTree

omit hy in
private theorem vertexOf_mem_iff (z : ({d, G.rot d}ᶜ : Set H)) :
    G.vertexOf z ∈ insert (G.vertexOf d) (T.nonRoot.image (liftV d G)) ↔
      (G.bivalentRemoval hG hd).vertexOf z ∈ T.nonRoot := by
  rw [mem_insert, ← liftV_vertexOf hG hd, mem_image]
  constructor
  · rintro (h | ⟨w, hw, h⟩)
    · exact absurd (by rw [← h, liftV_vertexOf hG hd]) ((mem_compl_iff_vertexOf_ne hd).1 z.2)
    · exact liftV_injective h ▸ hw
  · intro h
    exact Or.inr ⟨_, h, rfl⟩

private theorem inv_rot_mem_darts :
    (⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ T.darts := by
  have := T.inv_mem_darts (isPlabicGraph_bivalentRemoval hG hd) hy
  rwa [show (G.bivalentRemoval hG hd).inv ⟨G.inv d, hd.inv_mem hG⟩ =
    ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ from
    Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv hG hd rfl)] at this

/-- The darts of the tree with `v(d)` inserted. -/
private theorem mem_treeDarts_iff {e : H} :
    e ∈ G.treeDarts (insert (G.vertexOf d) (T.nonRoot.image (liftV d G))) ↔
      (∃ h : e ∈ ({d, G.rot d}ᶜ : Set H), (⟨e, h⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ T.darts) ∨
        e = d ∨ e = G.rot d := by
  have hinv := hG.inv_involutive
  rw [mem_treeDarts]
  by_cases he : e ∈ ({d, G.rot d}ᶜ : Set H)
  · have hne : e ≠ d ∧ e ≠ G.rot d := mem_compl_pair.1 he
    simp only [hne.1, hne.2, or_false, exists_prop_of_true he]
    by_cases h₁ : e = G.inv d
    · subst h₁
      refine iff_of_true ⟨hd.inv_notMem_bdry hG, Or.inr (by rw [hinv]; exact mem_insert_self _ _)⟩
        hy
    by_cases h₂ : e = G.inv (G.rot d)
    · subst h₂
      refine iff_of_true ⟨hd.inv_rot_notMem_bdry hG, Or.inr (by
        rw [hinv, G.vertexOf_rot]; exact mem_insert_self _ _)⟩ (inv_rot_mem_darts hG hd T hy)
    have hie : G.inv e ∈ ({d, G.rot d}ᶜ : Set H) := mem_compl_pair.2
      ⟨fun h => h₁ (by rw [← h, hinv]), fun h => h₂ (by rw [← h, hinv])⟩
    have hinv' : (G.bivalentRemoval hG hd).inv ⟨e, he⟩ = ⟨G.inv e, hie⟩ :=
      Subtype.ext (coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂)
    rw [(G.bivalentRemoval hG hd).mem_treeDarts, hinv', mem_bivalentRemoval_bdry,
      ← vertexOf_mem_iff hG hd T ⟨e, he⟩, ← vertexOf_mem_iff hG hd T ⟨G.inv e, hie⟩]
  · have hx : e = d ∨ e = G.rot d := by
      by_contra h
      exact he (mem_compl_pair.2 (not_or.1 h))
    refine iff_of_true ⟨fun hB => hd.not_isBoundaryVertex ?_, Or.inl ?_⟩ (Or.inr hx)
    · rcases hx with rfl | rfl
      · exact G.isBoundaryVertex_vertexOf_of_mem hB
      · rw [← G.vertexOf_rot]; exact G.isBoundaryVertex_vertexOf_of_mem hB
    · rcases hx with rfl | rfl
      · exact mem_insert_self _ _
      · rw [G.vertexOf_rot]; exact mem_insert_self _ _


/-- A dart of the tree with `v(d)` inserted lies at `v(d)`, at a lifted non-root vertex or at the
lifted root. -/
private theorem vertexOf_mem_or_eq_root {e : H}
    (he : e ∈ G.treeDarts (insert (G.vertexOf d) (T.nonRoot.image (liftV d G)))) :
    G.vertexOf e ∈ insert (G.vertexOf d) (T.nonRoot.image (liftV d G)) ∨
      G.vertexOf e = liftV d G T.root := by
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  rcases (mem_treeDarts_iff hG hd T hy).1 he with ⟨h, hT⟩ | rfl | rfl
  · rcases T.vertexOf_mem_or_eq_root hGr hT with h' | h'
    · exact Or.inl ((vertexOf_mem_iff hG hd T ⟨e, h⟩).2 h')
    · right
      rw [← h', liftV_vertexOf]
  · exact Or.inl (mem_insert_self _ _)
  · left; rw [G.vertexOf_rot]; exact mem_insert_self _ _

end InsertTree

/-- **The tree with `v(d)` inserted**: if the edge `{d̄, \overline{σ d}}` of the removal of a
bivalent vertex `v(d)` is an edge of a rooted tree `T` of the removal, inserting `v(d)` into it
gives a rooted tree of `G`. -/
private noncomputable def insertTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  have hD := fun e => InsertTree.mem_treeDarts_iff hG hd T hy (e := e)
  have ha1 : (T.intervalStart : H) ∈ ({d, G.rot d}ᶜ : Set H) := T.intervalStart.2
  have hroot' : liftV d G T.root = G.vertexOf T.intervalStart := by
    rw [T.root_eq_vertexOf_intervalStart, liftV_vertexOf]
  have hrx : liftV d G T.root ≠ G.vertexOf d := by
    rw [hroot']; exact (mem_compl_iff_vertexOf_ne hd).1 ha1
  have hvW : ∀ w ∈ T.nonRoot, ∃ e, (G.bivalentRemoval hG hd).vertexOf e = w := fun w hw =>
    (G.bivalentRemoval hG hd).mem_vertices.1
      ((G.bivalentRemoval hG hd).mem_internalVertices.1 (T.nonRoot_subset hw)).1
  { root := liftV d G T.root
    nonRoot := insert (G.vertexOf d) (T.nonRoot.image (liftV d G))
    root_mem_vertices := by rw [hroot']; exact G.vertexOf_mem_vertices _
    nonRoot_nonempty := ⟨_, mem_insert_self _ _⟩
    nonRoot_subset := by
      refine insert_subset (G.mem_internalVertices.2 ⟨G.vertexOf_mem_vertices _,
        hd.not_isBoundaryVertex⟩) fun w' hw' => ?_
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hw'
      obtain ⟨e, rfl⟩ := hvW w hw
      rw [liftV_vertexOf]
      refine G.vertexOf_mem_internalVertices.2 fun h => ?_
      have := (G.bivalentRemoval hG hd).vertexOf_mem_internalVertices.1 (T.nonRoot_subset hw)
      rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff] at this
      exact this h
    root_notMem_nonRoot := by
      rw [mem_insert, not_or]
      refine ⟨hrx, fun h => ?_⟩
      obtain ⟨w, hw, hwr⟩ := mem_image.1 h
      exact T.root_notMem_nonRoot (liftV_injective hwr ▸ hw)
    vertexOf_inv_mem := by
      intro e he
      have heD : e ∈ G.treeDarts (insert (G.vertexOf d) (T.nonRoot.image (liftV d G))) :=
        G.mem_treeDarts.2 ⟨fun hB => (G.mem_internalVertices.1 (insert_subset
          (G.mem_internalVertices.2 ⟨G.vertexOf_mem_vertices _, hd.not_isBoundaryVertex⟩)
          (fun w' hw' => by
            obtain ⟨w, hw, rfl⟩ := mem_image.1 hw'
            obtain ⟨e', rfl⟩ := hvW w hw
            rw [liftV_vertexOf]
            refine G.vertexOf_mem_internalVertices.2 fun h => ?_
            have := (G.bivalentRemoval hG hd).vertexOf_mem_internalVertices.1 (T.nonRoot_subset hw)
            rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff] at this
            exact this h) he)).2 (G.isBoundaryVertex_vertexOf_of_mem hB), Or.inl he⟩
      rcases InsertTree.vertexOf_mem_or_eq_root hG hd T hy (inv_mem_treeDarts' hG heD) with h | h
      · exact mem_insert_of_mem h
      · rw [h]; exact mem_insert_self _ _
    exists_interval := by
      refine ⟨T.intervalStart, (mem_liftV).2 ⟨ha1, T.intervalStart_mem_root⟩, T.intervalLength,
        T.one_le_intervalLength, ?_, fun e he => ?_, ?_⟩
      · rw [liftV, card_map]; exact T.intervalLength_lt_card
      · obtain ⟨heS, heR⟩ := (mem_liftV).1 he
        have hne := mem_compl_pair.1 heS
        rw [hD]
        simp only [hne.1, hne.2, or_false, exists_prop_of_true heS]
        rw [T.mem_darts_iff_of_mem_root heR]
        refine exists_congr fun j => and_congr Iff.rfl ?_
        rw [Subtype.ext_iff, coe_bivalentRemoval_rot_pow]
      · have hmem : G.rot.symm T.intervalStart ∈ ({d, G.rot d}ᶜ : Set H) := by
          rw [← coe_bivalentRemoval_rot_symm hG hd]; exact Subtype.property _
        rw [hD]
        have hne := mem_compl_pair.1 hmem
        simp only [hne.1, hne.2, or_false, exists_prop_of_true hmem]
        rw [show (⟨G.rot.symm T.intervalStart, hmem⟩ : ({d, G.rot d}ᶜ : Set H)) =
          (G.bivalentRemoval hG hd).rot.symm T.intervalStart from
          Subtype.ext (coe_bivalentRemoval_rot_symm hG hd _).symm]
        exact T.rot_symm_intervalStart_notMem
    card_image_edgeOf := by
      set D' := G.treeDarts (insert (G.vertexOf d) (T.nonRoot.image (liftV d G)))
      have h1 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne (S := D')
        fun e he => inv_mem_treeDarts' hG he
      have hD' : D' = insert d (insert (G.rot d) (T.darts.map (Embedding.subtype _))) := by
        ext e
        rw [hD, mem_insert, mem_insert, mem_map]
        constructor
        · rintro (⟨h, hT⟩ | rfl | rfl)
          · exact Or.inr (Or.inr ⟨_, hT, rfl⟩)
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · rintro (rfl | rfl | ⟨y, hyT, rfl⟩)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl ⟨y.2, hyT⟩
      have hdD : d ∉ insert (G.rot d) (T.darts.map (Embedding.subtype _)) := by
        rw [mem_insert, mem_map, not_or]
        refine ⟨hd.rot_ne.symm, fun ⟨y, _, hy'⟩ => (mem_compl_pair.1 y.2).1 hy'⟩
      have hσD : G.rot d ∉ T.darts.map (Embedding.subtype _) := by
        rw [mem_map]
        exact fun ⟨y, _, hy'⟩ => (mem_compl_pair.1 y.2).2 hy'
      have h2 : D'.card = 2 * T.nonRoot.card + 2 := by
        rw [hD', card_insert_of_notMem hdD, card_insert_of_notMem hσD, card_map, T.card_darts hGr]
      have hx : G.vertexOf d ∉ T.nonRoot.image (liftV d G) := fun h => by
        obtain ⟨w, hw, hwx⟩ := mem_image.1 h
        obtain ⟨e, rfl⟩ := hvW w hw
        rw [liftV_vertexOf] at hwx
        exact (mem_compl_iff_vertexOf_ne hd).1 e.2 hwx
      rw [card_insert_of_notMem hx, card_image_of_injective _ liftV_injective]
      omega
    reflTransGen_treeAdj := by
      set W' := insert (G.vertexOf d) (T.nonRoot.image (liftV d G))
      have hid := hd.inv_mem hG
      have hird := hd.inv_rot_mem hG
      have hyT' := InsertTree.inv_rot_mem_darts hG hd T hy
      have hadjx₁ : G.TreeAdj W' (G.vertexOf (G.inv d)) (G.vertexOf d) :=
        ⟨G.inv d, (hD _).2 (Or.inl ⟨hid, hy⟩), rfl, by rw [hinv]⟩
      have hadjx₂ : G.TreeAdj W' (G.vertexOf d) (G.vertexOf (G.inv (G.rot d))) :=
        ⟨G.rot d, (hD _).2 (Or.inr (Or.inr rfl)), G.vertexOf_rot d, rfl⟩
      have hadjx₃ : G.TreeAdj W' (G.vertexOf (G.inv (G.rot d))) (G.vertexOf d) :=
        ⟨G.inv (G.rot d), (hD _).2 (Or.inl ⟨hird, hyT'⟩), rfl, by rw [hinv, G.vertexOf_rot]⟩
      have hadjx₄ : G.TreeAdj W' (G.vertexOf d) (G.vertexOf (G.inv d)) :=
        ⟨d, (hD _).2 (Or.inr (Or.inl rfl)), rfl, rfl⟩
      have hstep : ∀ u u₂, (G.bivalentRemoval hG hd).TreeAdj T.nonRoot u u₂ →
          Relation.ReflTransGen (G.TreeAdj W') (liftV d G u) (liftV d G u₂) := by
        rintro _ _ ⟨e, he, rfl, rfl⟩
        rw [liftV_vertexOf, liftV_vertexOf]
        by_cases h₁ : (e : H) = G.inv d
        · rw [Subtype.ext_iff.1 (show (G.bivalentRemoval hG hd).inv e = ⟨_, hird⟩ from
            Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv hG hd h₁)), h₁]
          exact .tail (.single hadjx₁) hadjx₂
        by_cases h₂ : (e : H) = G.inv (G.rot d)
        · rw [Subtype.ext_iff.1 (show (G.bivalentRemoval hG hd).inv e = ⟨_, hid⟩ from
            Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂)), h₂]
          exact .tail (.single hadjx₃) hadjx₄
        · refine .single ⟨e, (hD _).2 (Or.inl ⟨e.2, he⟩), rfl, ?_⟩
          rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]
      have hlift : ∀ w, Relation.ReflTransGen ((G.bivalentRemoval hG hd).TreeAdj T.nonRoot)
          T.root w → Relation.ReflTransGen (G.TreeAdj W') (liftV d G T.root) (liftV d G w) :=
        fun w h => Relation.ReflTransGen.lift' (liftV d G) hstep h
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact .refl
      rcases mem_insert.1 hu with rfl | hu
      · have hY : (G.bivalentRemoval hG hd).vertexOf ⟨G.inv d, hid⟩ ∈
            insert T.root T.nonRoot := by
          rcases T.vertexOf_mem_or_eq_root hGr hy with h | h
          · exact mem_insert_of_mem h
          · rw [h]; exact mem_insert_self _ _
        have := hlift _ (T.reflTransGen_treeAdj _ hY)
        rw [liftV_vertexOf] at this
        exact this.tail hadjx₁
      · obtain ⟨w, hw, rfl⟩ := mem_image.1 hu
        exact hlift w (T.reflTransGen_treeAdj w (mem_insert_of_mem hw)) }


namespace InsertTree

private theorem mem_darts_iff {e : H} : e ∈ (insertTree hG hd T hy).darts ↔
    (∃ h : e ∈ ({d, G.rot d}ᶜ : Set H), (⟨e, h⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ T.darts) ∨
      e = d ∨ e = G.rot d :=
  mem_treeDarts_iff hG hd T hy

private theorem vertexOf_mem_nonRoot : G.vertexOf d ∈ (insertTree hG hd T hy).nonRoot :=
  mem_insert_self _ _

private theorem root_eq : (insertTree hG hd T hy).root = liftV d G T.root := rfl

/-- Removing `v(d)` from the tree with `v(d)` inserted gives back the tree. -/
private theorem removalTree_eq :
    removalTree hG hd (insertTree hG hd T hy) (vertexOf_mem_nonRoot hG hd T hy) = T := by
  refine RootedTree.ext' (restrictV_liftV T.root) ?_
  change ((insert (G.vertexOf d) (T.nonRoot.image (liftV d G))).erase (G.vertexOf d)).image
    (restrictV d G) = T.nonRoot
  have hx : G.vertexOf d ∉ T.nonRoot.image (liftV d G) := fun h => by
    obtain ⟨w, hw, hwx⟩ := mem_image.1 h
    obtain ⟨e, rfl⟩ := (G.bivalentRemoval hG hd).mem_vertices.1
      ((G.bivalentRemoval hG hd).mem_internalVertices.1 (T.nonRoot_subset hw)).1
    rw [liftV_vertexOf] at hwx
    exact (mem_compl_iff_vertexOf_ne hd).1 e.2 hwx
  rw [erase_insert hx, image_image]
  conv_rhs => rw [← image_id (s := T.nonRoot)]
  exact image_congr fun w _ => restrictV_liftV w

private theorem isBoundaryVertex_root_iff :
    G.IsBoundaryVertex (insertTree hG hd T hy).root ↔
      (G.bivalentRemoval hG hd).IsBoundaryVertex T.root := by
  rw [root_eq, T.root_eq_vertexOf_intervalStart, liftV_vertexOf,
    isBoundaryVertex_bivalentRemoval_vertexOf_iff]

end InsertTree

omit hy in
/-- A tree of the removal whose darts avoid `d̄` and `\overline{σ d}` embeds into `G`. -/
private theorem isEmbedding_val {q : (G.bivalentRemoval hG hd).RootedTree}
    (hq₁ : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∉ q.darts)
    (hq₂ : (⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∉ q.darts) :
    q.IsEmbedding G Subtype.val := by
  refine ⟨Subtype.val_injective.injOn, fun e he => ?_, fun e he _ => rfl, fun e he => ?_, ?_, ?_,
    ?_, fun e _ => rfl⟩
  · refine coe_bivalentRemoval_inv_of_ne hG hd (fun h => hq₁ ?_) (fun h => hq₂ ?_)
    · rwa [show e = ⟨G.inv d, hd.inv_mem hG⟩ from Subtype.ext h] at he
    · rwa [show e = ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ from Subtype.ext h] at he
  · rw [← mem_bivalentRemoval_bdry hG hd]
    exact q.notMem_bdry_of_mem_darts he
  · intro h
    obtain ⟨e, he, hfe⟩ := mem_image.1 h
    have : e = (G.bivalentRemoval hG hd).rot q.intervalEnd := Subtype.ext hfe
    exact q.rot_intervalEnd_notMem (isPlabicGraph_bivalentRemoval hG hd) (this ▸ he)
  · intro h
    obtain ⟨e, he, hfe⟩ := mem_image.1 h
    have : e = (G.bivalentRemoval hG hd).rot.symm q.intervalStart := Subtype.ext (by
      rw [hfe, coe_bivalentRemoval_rot_symm])
    exact q.rot_symm_intervalStart_notMem (this ▸ he)
  · rw [← liftV_vertexOf hG hd, liftV, card_map, ← q.root_eq_vertexOf_intervalStart]
    exact q.intervalLength_lt_card

end InsertTree

section LollipopTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) (i : Fin b)
  (hℓ : G.vertexOf (G.inv (G.leg i)) = {G.inv (G.leg i)})

include hG hℓ

namespace LollipopTree

private theorem not_isBoundaryVertex : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.leg i))) := by
  rw [hℓ]
  rintro ⟨e, he, heB⟩
  rw [mem_singleton] at he
  subst he
  exact hG.leg_notMem_bdry i (hG.inv_mem_bdry_iff.1 heB)

private theorem mem_treeDarts_iff {e : H} :
    e ∈ G.treeDarts {G.vertexOf (G.inv (G.leg i))} ↔ e = G.leg i ∨ e = G.inv (G.leg i) := by
  have hinv := hG.inv_involutive
  have hv : ∀ y, G.vertexOf y = G.vertexOf (G.inv (G.leg i)) ↔ y = G.inv (G.leg i) := fun y =>
    ⟨fun h => by
      have := G.self_mem_vertexOf y
      rwa [h, hℓ, mem_singleton] at this, fun h => by rw [h]⟩
  rw [mem_treeDarts, mem_singleton, mem_singleton, hv, hv]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inr h
    · left; rw [← hinv e, h, hinv]
  · rintro (rfl | rfl)
    · exact ⟨hG.leg_notMem_bdry i, Or.inr rfl⟩
    · refine ⟨fun hB => hG.leg_notMem_bdry i (hG.inv_mem_bdry_iff.1 hB), Or.inl rfl⟩

end LollipopTree

/-- **The tree of a lollipop**: if the dart `ḡ_i` across a leg forms a vertex by itself, then
`(β(i), {ḡ_i})` is a rooted tree. -/
private noncomputable def lollipopTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hD := fun e => LollipopTree.mem_treeDarts_iff hG i hℓ (e := e)
  have hint := LollipopTree.not_isBoundaryVertex hG i hℓ
  have hbv : G.IsBoundaryVertex (G.bvertex i) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  { root := G.bvertex i
    nonRoot := {G.vertexOf (G.inv (G.leg i))}
    root_mem_vertices := G.vertexOf_mem_vertices _
    nonRoot_nonempty := singleton_nonempty _
    nonRoot_subset := singleton_subset_iff.2
      (G.mem_internalVertices.2 ⟨G.vertexOf_mem_vertices _, hint⟩)
    root_notMem_nonRoot := by
      rw [mem_singleton]
      intro h
      exact hint (h ▸ hbv)
    vertexOf_inv_mem := by
      intro e he
      rw [mem_singleton] at he
      have : e = G.inv (G.leg i) := by
        have := G.self_mem_vertexOf e
        rwa [he, hℓ, mem_singleton] at this
      rw [this, hinv]
      exact mem_insert_self _ _
    exists_interval := by
      refine ⟨G.leg i, G.leg_mem_bvertex i, 1, le_rfl, ?_, fun e he => ?_, ?_⟩
      · rw [(hG.boundaryVertex_card _ (hG.bvertex_mem i)).1]; norm_num
      · rw [hD]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨0, one_pos, rfl⟩
          · exfalso
            exact hint (by rwa [G.vertexOf_eq_of_mem he])
        · rintro ⟨j, hj, rfl⟩
          obtain rfl : j = 0 := by omega
          exact Or.inl rfl
      · rw [hD]
        rintro (h | h)
        · exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hbv (x := G.leg i)
            (by conv_lhs => rw [← h]; exact Equiv.apply_symm_apply _ _)
        · apply hint
          rw [← h]
          have : G.vertexOf (G.rot.symm (G.leg i)) = G.bvertex i := by
            rw [← G.vertexOf_rot, Equiv.apply_symm_apply]; rfl
          rwa [this]
    card_image_edgeOf := by
      have h1 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
        (S := G.treeDarts {G.vertexOf (G.inv (G.leg i))}) fun e he => inv_mem_treeDarts' hG he
      have h2 : G.treeDarts {G.vertexOf (G.inv (G.leg i))} = {G.leg i, G.inv (G.leg i)} := by
        ext e; rw [hD, mem_insert, mem_singleton]
      rw [h2, card_pair (hG.inv_ne _).symm] at h1
      rw [card_singleton, h2]
      omega
    reflTransGen_treeAdj := by
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact .refl
      · rw [mem_singleton.1 hu]
        exact .single ⟨G.leg i, (hD _).2 (Or.inl rfl), rfl, rfl⟩ }

private theorem lollipopTree_darts {e : H} :
    e ∈ (lollipopTree hG i hℓ).darts ↔ e = G.leg i ∨ e = G.inv (G.leg i) :=
  LollipopTree.mem_treeDarts_iff hG i hℓ

private theorem lollipopTree_nonRoot :
    (lollipopTree hG i hℓ).nonRoot = {G.vertexOf (G.inv (G.leg i))} := rfl

private theorem lollipopTree_intervalStart : (lollipopTree hG i hℓ).intervalStart = G.leg i :=
  (lollipopTree hG i hℓ).intervalStart_eq_leg hG rfl

/-- The plabic graph of the tree of a lollipop is the lollipop graph of its colour. -/
private theorem lollipopTree_moveEquivalent :
    PlabicGraph.MoveEquivalent {.m2, .m3}
      ⟨_, (lollipopTree hG i hℓ).plabicData, (lollipopTree hG i hℓ).isPlabicGraph_plabicData hG⟩
      (lollipopPlabicGraph (G.colour (G.inv (G.leg i)))) := by
  have hb : G.IsBoundaryVertex (lollipopTree hG i hℓ).root :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  obtain ⟨θ⟩ := (lollipopTree hG i hℓ).lollipop_isomorphic_of_card_nonRoot_eq_one hG hb
    (by rw [lollipopTree_nonRoot, card_singleton])
  rw [lollipopTree_intervalStart] at θ
  exact PlabicGraph.MoveEquivalent.of_isomorphic ⟨θ⟩

end LollipopTree


/-! ### Absorbing a thin root into a boundary tree -/

section AbsorbRoot

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {𝒯 : Finset (G.RootedTree × Shade)} (h𝒯 : G.IsCollapsingFamily 𝒯)
  (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1) {z : H} {i : Fin b} (hzD : z ∉ G.familyDarts 𝒯)
  (hthin : ∀ e ∈ G.vertexOf z, e ≠ z → ∃ p ∈ 𝒯, p.1.root = G.vertexOf z ∧ e ∈ p.1.darts)
  (hne : ∃ p ∈ 𝒯, p.1.root = G.vertexOf z) (hint : ¬G.IsBoundaryVertex (G.vertexOf z))
  (hσ : G.inv z = G.leg i)

include hG h𝒯 hbr hzD hthin hne hint hσ

open scoped Classical in
/-- **Absorbing a thin root.** If all the darts of an internal vertex `v = v(z)` other than `z` are
darts of the trees with root `v`, and `z` is joined to the leg `g_i`, these trees and `v` form one
collapsible tree with root `β(i)`, without changing the collapse. -/
private theorem exists_absorbRoot :
    ∃ (Tp : G.RootedTree) (𝒯o : Finset (G.RootedTree × Shade)), G.IsCollapsingFamily 𝒯o ∧
      Tp.IsCollapsibleOfColour (G.colour z) ∧ G.IsBoundaryVertex Tp.root ∧
      z ∈ Tp.darts ∧ G.leg i ∈ Tp.darts ∧ (∀ q ∈ 𝒯o, Disjoint Tp.darts q.1.darts) ∧
      (∀ q ∈ 𝒯o, ∃ a ∈ q.1.root, a ∉ G.familyDarts 𝒯o ∧ a ∉ Tp.darts) ∧
      (∃ a ∈ Tp.root, a ∉ G.familyDarts 𝒯o ∧ a ∉ Tp.darts) ∧
      (G.collapse 𝒯).Isomorphic (G.collapse (insert (Tp, G.colour z) 𝒯o)) := by
  have hinv := hG.inv_involutive
  set Tv := mergeTree hG h𝒯 hzD hthin hne with hTv
  have hDv := fun e => MergeTree.darts_iff hG h𝒯 hzD hthin hne (e := e)
  have hstart := MergeTree.intervalStart_eq hG h𝒯 hzD hthin hne
  have hthin' : ∀ e ∈ Tv.root, e ∉ Tv.darts → e = G.rot.symm Tv.intervalStart := by
    intro e he heD
    rw [hstart, Equiv.symm_apply_apply]
    by_contra hez
    obtain ⟨p, hp, hpr, hep⟩ := hthin e he hez
    exact heD ((hDv e).2 ⟨p, hp, hpr, hep⟩)
  have hσ' : G.inv (G.rot.symm Tv.intervalStart) = G.leg i := by
    rwa [hstart, Equiv.symm_apply_apply]
  set Tp := extendTree hG Tv hint hthin' hσ' with hTp
  have hDp : ∀ e, e ∈ Tp.darts ↔ e ∈ Tv.darts ∨ e = z ∨ e = G.leg i := fun e => by
    rw [ExtendTree.darts_iff, hstart, Equiv.symm_apply_apply]
  have hcv := MergeTree.isCollapsibleOfColour hG h𝒯 hzD hthin hne hbr hint
  have hbp : G.IsBoundaryVertex Tp.root := ExtendTree.isBoundaryVertex_root hG Tv hint hthin' hσ'
  have hTpc : Tp.IsCollapsibleOfColour (G.colour z) := by
    obtain ⟨θ⟩ := ExtendTree.plabicData_isomorphic hG Tv hint hthin' hσ'
    refine ⟨Tp.isPlabicGraph_plabicData hG, ?_, Or.inr ⟨hbp, ?_⟩⟩
    · exact (PlabicGraph.MoveEquivalent.of_isomorphic (S := {.m2, .m3})
        (G := ⟨_, Tp.plabicData, Tp.isPlabicGraph_plabicData hG⟩)
        (G' := ⟨_, Tv.plabicData, hcv.isPlabicGraph⟩) ⟨θ⟩).trans hcv.moveEquivalent
    · rw [ExtendTree.nonRoot_eq, card_insert_of_notMem Tv.root_notMem_nonRoot]
      have := Tv.nonRoot_nonempty.card_pos
      omega
  set 𝒯o := 𝒯.filter fun p => p.1.root ≠ G.vertexOf z with h𝒯odef
  have h𝒯o : G.IsCollapsingFamily 𝒯o := h𝒯.subset (filter_subset _ _)
  have hlegD : G.leg i ∉ G.familyDarts 𝒯 := fun h => hzD (by
    have := inv_mem_familyDarts hG h
    rwa [← hσ, hinv] at this)
  have hbv : G.IsBoundaryVertex (G.bvertex i) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hDo : ∀ e, e ∈ G.familyDarts 𝒯o → e ∈ G.familyDarts 𝒯 := fun e he => by
    obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he
    exact mem_familyDarts.2 ⟨q, (mem_filter.1 hq).1, heq⟩
  have hdisj : ∀ q ∈ 𝒯o, Disjoint Tp.darts q.1.darts := by
    intro q hq
    rw [Finset.disjoint_left]
    intro e he heq
    have heD : e ∈ G.familyDarts 𝒯 := mem_familyDarts.2 ⟨q, (mem_filter.1 hq).1, heq⟩
    rcases (hDp e).1 he with h | rfl | rfl
    · obtain ⟨p, hp, hpr, hep⟩ := (hDv e).1 h
      have := h𝒯.eq_of_mem_darts hG hp (mem_filter.1 hq).1 hep heq
      subst this
      exact (mem_filter.1 hq).2 hpr
    · exact hzD heD
    · exact hlegD heD
  refine ⟨Tp, 𝒯o, h𝒯o, hTpc, hbp, (hDp z).2 (Or.inr (Or.inl rfl)),
    (hDp _).2 (Or.inr (Or.inr rfl)), hdisj, fun q hq => ?_, ?_, ?_⟩
  · obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root q (mem_filter.1 hq).1
    have haD : a ∉ G.familyDarts 𝒯 := fun h => by
      obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
      exact haq r hr har
    refine ⟨a, ha, fun h => haD (hDo a h), fun h => ?_⟩
    rcases (hDp a).1 h with h | rfl | rfl
    · obtain ⟨p, hp, -, hap⟩ := (hDv a).1 h
      exact haD (mem_familyDarts.2 ⟨p, hp, hap⟩)
    · exact (mem_filter.1 hq).2 (by rw [← q.1.mem_root_iff.1 ha])
    · apply hlegD
      have hr : q.1.root = G.bvertex i := by rw [← q.1.mem_root_iff.1 ha]; rfl
      rw [← q.1.intervalStart_eq_leg hG hr]
      exact mem_familyDarts.2 ⟨q, (mem_filter.1 hq).1, q.1.intervalStart_mem_darts⟩
  · obtain ⟨a, ha, haB⟩ := hbp
    exact ⟨a, ha, notMem_familyDarts_of_mem_bdry haB, fun h => Tp.notMem_bdry_of_mem_darts h haB⟩
  · refine ⟨collapseIsoAbsorb hG (𝒯₁ := 𝒯) (𝒯₂ := insert (Tp, G.colour z) 𝒯o) (i := i) ?_ hlegD
      ?_ ?_ ?_ ?_⟩
    · intro e
      rw [mem_familyDarts, mem_familyDarts, ← hσ, hinv]
      constructor
      · rintro ⟨q, hq, heq⟩
        rcases mem_insert.1 hq with rfl | hq
        · rcases (hDp e).1 heq with h | h | h
          · obtain ⟨p, hp, -, hep⟩ := (hDv e).1 h
            exact Or.inl ⟨p, hp, hep⟩
          · exact Or.inr (Or.inr h)
          · right; left; rw [h, hσ]
        · exact Or.inl ⟨q, (mem_filter.1 hq).1, heq⟩
      · rintro (⟨q, hq, heq⟩ | h | h)
        · by_cases hqr : q.1.root = G.vertexOf z
          · exact ⟨_, mem_insert_self _ _, (hDp e).2 (Or.inl ((hDv e).2 ⟨q, hq, hqr, heq⟩))⟩
          · exact ⟨q, mem_insert_of_mem (mem_filter.2 ⟨hq, hqr⟩), heq⟩
        · exact ⟨_, mem_insert_self _ _, (hDp e).2 (Or.inr (Or.inr (by rw [h, hσ])))⟩
        · exact ⟨_, mem_insert_self _ _, (hDp e).2 (Or.inr (Or.inl h))⟩
    · intro e he hne'
      rw [← hσ, hinv] at he hne'
      obtain ⟨p, hp, -, hep⟩ := hthin e he hne'
      exact mem_familyDarts.2 ⟨p, hp, hep⟩
    · intro q hq hiq
      rcases mem_insert.1 hq with rfl | hq
      · rw [← hσ, hinv]
      · exact absurd (mem_familyDarts.2 ⟨q, (mem_filter.1 hq).1, hiq⟩) hlegD
    · intro k p₁ hp₁ p₂ hp₂ h₁ h₂
      rcases mem_insert.1 hp₂ with rfl | hp₂
      · exfalso
        rcases (hDp _).1 h₂ with h | h | h
        · obtain ⟨p, hp, hpr, hkp⟩ := (hDv _).1 h
          apply hint
          rw [← hpr, p.1.root_eq_bvertex_of_leg_mem hG hkp]
          exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem k)
        · apply hint
          rw [← h]
          exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem k)
        · rw [hG.leg_injective h] at h₁
          exact hlegD (mem_familyDarts.2 ⟨p₁, hp₁, h₁⟩)
      · rw [h𝒯.eq_of_mem_darts hG hp₁ (mem_filter.1 hp₂).1 h₁ h₂]
    · intro k p₁ hp₁ p₂ hp₂ h₁ h₂
      rw [h𝒯.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]

end AbsorbRoot

/-! ### Inserting a bivalent vertex into an edge of a tree -/

section InsertionInside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d)
  {𝒯o : Finset ((G.bivalentRemoval hG hd).RootedTree × Shade)}
  (h𝒯o : (G.bivalentRemoval hG hd).IsCollapsingFamily 𝒯o)
  (T₀ : (G.bivalentRemoval hG hd).RootedTree) (c : Shade)
  (hy : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ T₀.darts)
  (hP : PlabicGraph.MoveEquivalent {.m2, .m3}
    ⟨_, T₀.plabicData, T₀.isPlabicGraph_plabicData (isPlabicGraph_bivalentRemoval hG hd)⟩
    (lollipopPlabicGraph c))
  (hc : (¬(G.bivalentRemoval hG hd).IsBoundaryVertex T₀.root ∧
      ∀ e ∈ T₀.root, (G.bivalentRemoval hG hd).colour e = c) ∨
    (G.bivalentRemoval hG hd).IsBoundaryVertex T₀.root)
  (hdisj : ∀ q ∈ 𝒯o, Disjoint T₀.darts q.1.darts)
  (hfreeo : ∀ q ∈ 𝒯o, ∃ a ∈ q.1.root,
    a ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯o ∧ a ∉ T₀.darts)
  (hfree₀ : ∃ a ∈ T₀.root, a ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯o ∧ a ∉ T₀.darts)

include hG hd h𝒯o hy hP hc hdisj hfreeo hfree₀

open scoped Classical in
/-- **Inserting a bivalent vertex into an edge of a tree**: the tree of `G` with `v(d)` inserted,
together with the other trees, is a collapsing family of `G` with the same collapse. -/
theorem exists_collapse_insertion_inside :
    ∃ 𝒯' : Finset (G.RootedTree × Shade), G.IsCollapsingFamily 𝒯' ∧
      (G.collapse 𝒯').Isomorphic ((G.bivalentRemoval hG hd).collapse (insert (T₀, c) 𝒯o)) := by
  have hinv := hG.inv_involutive
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  set T' := insertTree hG hd T₀ hy with hT'
  have hxW := InsertTree.vertexOf_mem_nonRoot hG hd T₀ hy
  have hD' := fun e => InsertTree.mem_darts_iff hG hd T₀ hy (e := e)
  have hσy : (⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ T₀.darts :=
    InsertTree.inv_rot_mem_darts hG hd T₀ hy
  -- `T'` is collapsible
  have hT' : T'.IsCollapsibleOfColour c := by
    have hiso := RemovalTree.plabicData_isomorphic hG hd T' hxW
    rw [InsertTree.removalTree_eq] at hiso
    have hloc : PlabicGraph.IsLocalMove .m2 ⟨_, T'.plabicData, T'.isPlabicGraph_plabicData hG⟩
        ⟨_, T₀.plabicData, T₀.isPlabicGraph_plabicData hGr⟩ :=
      Or.inl ⟨RemovalTree.dartD T' hxW, RemovalTree.isBivalentRemovable_dartD hG hd T' hxW,
        hiso.symm⟩
    refine ⟨T'.isPlabicGraph_plabicData hG,
      (PlabicGraph.MoveEquivalent.of_isLocalMove (by simp) hloc).trans hP, ?_⟩
    rcases hc with ⟨hb, hcol⟩ | hb
    · refine Or.inl ⟨mt (InsertTree.isBoundaryVertex_root_iff hG hd T₀ hy).1 hb, fun e he => ?_⟩
      obtain ⟨heS, heR⟩ := (mem_liftV).1 he
      exact hcol _ heR
    · refine Or.inr ⟨(InsertTree.isBoundaryVertex_root_iff hG hd T₀ hy).2 hb, ?_⟩
      change 2 ≤ (insert (G.vertexOf d) (T₀.nonRoot.image (liftV d G))).card
      have hx : G.vertexOf d ∉ T₀.nonRoot.image (liftV d G) := fun h => by
        obtain ⟨w, hw, hwx⟩ := mem_image.1 h
        obtain ⟨e, rfl⟩ := (G.bivalentRemoval hG hd).mem_vertices.1
          ((G.bivalentRemoval hG hd).mem_internalVertices.1 (T₀.nonRoot_subset hw)).1
        rw [liftV_vertexOf] at hwx
        exact (mem_compl_iff_vertexOf_ne hd).1 e.2 hwx
      rw [card_insert_of_notMem hx, card_image_of_injective _ liftV_injective]
      have := T₀.nonRoot_nonempty.card_pos
      omega
  -- the other trees embed into `G`
  have hemb : ∀ q ∈ 𝒯o, q.1.IsEmbedding G Subtype.val := fun q hq =>
    isEmbedding_val hG hd (fun h => disjoint_left.1 (hdisj q hq) hy h)
      (fun h => disjoint_left.1 (hdisj q hq) hσy h)
  have hA : Set.InjOn (Subtype.val : ({d, G.rot d}ᶜ : Set H) → H) Set.univ :=
    Subtype.val_injective.injOn
  have h𝒯' := isCollapsingFamily_insert_transportFamily' hGr hG h𝒯o hdisj hemb hA
    (fun _ _ => trivial)
    (fun q hq => by
      rw [q.1.root_eq_vertexOf_intervalStart, isBoundaryVertex_bivalentRemoval_vertexOf_iff])
    (fun q hq => by
      obtain ⟨a, ha, haD, haT⟩ := hfreeo q hq
      refine ⟨a, trivial, haD, haT, ?_⟩
      rw [← liftV_vertexOf hG hd, ← q.1.root_eq_vertexOf_intervalStart]
      exact (mem_liftV).2 ⟨a.2, ha⟩)
    hT'
    (fun y hy' => by
      rcases (hD' y).1 hy' with ⟨h, hT⟩ | rfl | rfl
      · exact Or.inl ⟨⟨y, h⟩, hT, trivial, rfl⟩
      · exact Or.inr fun ⟨z, hz⟩ => (mem_compl_pair.1 z.2).1 hz
      · exact Or.inr fun ⟨z, hz⟩ => (mem_compl_pair.1 z.2).2 hz)
    (by
      obtain ⟨a, ha, haD, haT⟩ := hfree₀
      exact ⟨a, trivial, haD, haT, (mem_liftV).2 ⟨a.2, ha⟩⟩)
  refine ⟨_, h𝒯', ?_⟩
  have hdT' : d ∈ T'.darts := (hD' d).2 (Or.inr (Or.inl rfl))
  have hσdT' : G.rot d ∈ T'.darts := (hD' _).2 (Or.inr (Or.inr rfl))
  have hmemD : ∀ e, e ∈ G.familyDarts (insert (T', c) (transportFamily hGr hG hemb)) ↔
      e ∈ T'.darts ∨ ∃ e' ∈ (G.bivalentRemoval hG hd).familyDarts 𝒯o, (e' : H) = e :=
    fun e => mem_familyDarts_insert_transportFamily hGr hG hemb
  have hD : ∀ y : ({d, G.rot d}ᶜ : Set H),
      y ∈ (G.bivalentRemoval hG hd).familyDarts (insert (T₀, c) 𝒯o) ↔
        (y : H) ∈ G.familyDarts (insert (T', c) (transportFamily hGr hG hemb)) := by
    intro y
    rw [hmemD, hD', mem_familyDarts]
    have hne := mem_compl_pair.1 y.2
    simp only [hne.1, hne.2, or_false, exists_prop_of_true y.2]
    constructor
    · rintro ⟨q, hq, hyq⟩
      rcases mem_insert.1 hq with rfl | hq
      · exact Or.inl hyq
      · exact Or.inr ⟨y, mem_familyDarts.2 ⟨q, hq, hyq⟩, rfl⟩
    · rintro (h | ⟨e, he, hey⟩)
      · exact ⟨_, mem_insert_self _ _, h⟩
      · obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he
        rw [show e = y from Subtype.ext hey] at heq
        exact ⟨q, mem_insert_of_mem hq, heq⟩
  have hQK : ∀ x ∈ (G.vertexOf d : Set H),
      x ∉ G.collapseCore (insert (T', c) (transportFamily hGr hG hemb)) := by
    intro x hx
    have hvx : G.vertexOf x = G.vertexOf d := G.vertexOf_eq_of_mem (mem_coe.1 hx)
    rintro (h | ⟨i, rfl⟩)
    · exact h ((hmemD x).2 (Or.inl (T'.mem_darts_of_vertexOf_mem (hvx ▸ hxW))))
    · exact T'.ne_leg_of_vertexOf_mem hG (hvx ▸ hxW) i rfl
  have hcol : ∀ i, ∀ p₁ ∈ insert (T', c) (transportFamily hGr hG hemb), ∀ p₂ ∈ insert (T₀, c) 𝒯o,
      G.leg i ∈ p₁.1.darts → (G.bivalentRemoval hG hd).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    have hlegT₀ : (G.bivalentRemoval hG hd).leg i ∈ p₂.1.darts → p₂ ∈ 𝒯o →
        (G.bivalentRemoval hG hd).leg i ∉ T₀.darts := fun h hp hT =>
      disjoint_left.1 (hdisj p₂ hp) hT h
    rcases mem_insert.1 hp₁ with rfl | hp₁
    · have hT₀ : (G.bivalentRemoval hG hd).leg i ∈ T₀.darts := by
        rcases (hD' _).1 h₁ with ⟨h, hT⟩ | h | h
        · exact hT
        · exact absurd h (mem_compl_pair.1 (hd.leg_mem hG i)).1
        · exact absurd h (mem_compl_pair.1 (hd.leg_mem hG i)).2
      rcases mem_insert.1 hp₂ with rfl | hp₂
      · rfl
      · exact absurd hT₀ (hlegT₀ h₂ hp₂)
    · obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hGr hG hemb hA (fun _ _ => trivial)
        (x := (G.bivalentRemoval hG hd).leg i) trivial hp₁ h₁
      rcases mem_insert.1 hp₂ with rfl | hp₂
      · exact absurd h₂ (fun h => disjoint_left.1 (hdisj r hr) h hir)
      · rw [← hrc, h𝒯o.eq_of_mem_darts hGr hr hp₂ hir h₂]
  have hcol₁ : ∀ i, ∀ p₁ ∈ insert (T', c) (transportFamily hGr hG hemb),
      ∀ p₂ ∈ insert (T', c) (transportFamily hGr hG hemb),
      G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts → p₁.2 = p₂.2 :=
    fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯'.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  exact (isomorphic_collapse_of_cut hG (bivalentRemoval_eq_cutData hG hd) hGr hD
    ((hmemD d).2 (Or.inl hdT')) ((hmemD _).2 (Or.inl hσdT')) _
    (fun x => by simp only [mem_coe, RotationSystem.mem_vertexOf, sameCycle_apply_right])
    hQK (Or.inl (G.self_mem_vertexOf d)) hcol hcol₁).symm

end InsertionInside

/-! ### Inserting a bivalent vertex into the edge of a lollipop, or outside the trees -/

section InsertionOther

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} (hd : G.IsBivalentRemovable d)
  {𝒯 : Finset ((G.bivalentRemoval hG hd).RootedTree × Shade)}
  (h𝒯 : (G.bivalentRemoval hG hd).IsCollapsingFamily 𝒯)

include hG hd h𝒯

open scoped Classical in
/-- **Inserting a bivalent vertex into the edge of a lollipop**: the lollipop and the new vertex
form a collapsible tree with a boundary root, whose collapse is the lollipop. -/
private theorem exists_collapse_insertion_lollipop {i : Fin b}
    (hleg : G.inv d = G.leg i ∨ G.inv (G.rot d) = G.leg i)
    (hℓ : (G.bivalentRemoval hG hd).vertexOf ((G.bivalentRemoval hG hd).inv
      ((G.bivalentRemoval hG hd).leg i)) =
      {(G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i)})
    (hnot : (G.bivalentRemoval hG hd).leg i ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯) :
    ∃ 𝒯' : Finset (G.RootedTree × Shade), G.IsCollapsingFamily 𝒯' ∧
      (G.collapse 𝒯').Isomorphic ((G.bivalentRemoval hG hd).collapse 𝒯) := by
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  have hinvr := hGr.inv_involutive
  set T₀ := lollipopTree hGr i hℓ with hT₀
  set c := (G.bivalentRemoval hG hd).colour
    ((G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i)) with hc
  have hD₀ := fun e => lollipopTree_darts hGr i hℓ (e := e)
  have hy : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ T₀.darts := by
    rcases hleg with hleg | hleg
    · have hlegy : (G.bivalentRemoval hG hd).leg i = ⟨G.inv d, hd.inv_mem hG⟩ :=
        Subtype.ext hleg.symm
      rw [← hlegy]; exact (hD₀ _).2 (Or.inl rfl)
    · have hlegy : (G.bivalentRemoval hG hd).leg i = ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ :=
        Subtype.ext hleg.symm
      have : (G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i) =
          ⟨G.inv d, hd.inv_mem hG⟩ := by
        rw [hlegy]; exact Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd rfl)
      rw [← this]; exact (hD₀ _).2 (Or.inr rfl)
  have hnot' : (G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i) ∉
      (G.bivalentRemoval hG hd).familyDarts 𝒯 := fun h => hnot (by
    have := inv_mem_familyDarts hGr h
    rwa [hinvr] at this)
  have hdisj : ∀ q ∈ 𝒯, Disjoint T₀.darts q.1.darts := fun q hq => by
    rw [Finset.disjoint_left]
    intro e he heq
    rcases (hD₀ e).1 he with rfl | rfl
    · exact hnot (mem_familyDarts.2 ⟨q, hq, heq⟩)
    · exact hnot' (mem_familyDarts.2 ⟨q, hq, heq⟩)
  have hbv : (G.bivalentRemoval hG hd).IsBoundaryVertex ((G.bivalentRemoval hG hd).bvertex i) :=
    (G.bivalentRemoval hG hd).vertexOf_mem_boundaryVertices.1 (hGr.bvertex_mem i)
  have hfreeo : ∀ q ∈ 𝒯, ∃ a ∈ q.1.root,
      a ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯 ∧ a ∉ T₀.darts := by
    intro q hq
    obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root q hq
    have haD : a ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯 := fun h => by
      obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
      exact haq r hr har
    refine ⟨a, ha, haD, fun haT => ?_⟩
    have hq1 := q.1.intervalStart_mem_darts
    rcases (hD₀ a).1 haT with rfl | rfl
    · have hr : q.1.root = (G.bivalentRemoval hG hd).bvertex i := by
        rw [← q.1.mem_root_iff.1 ha]; rfl
      rw [q.1.intervalStart_eq_leg hGr hr] at hq1
      exact hnot (mem_familyDarts.2 ⟨q, hq, hq1⟩)
    · have : q.1.intervalStart ∈
        ({(G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i)} : Finset _) := by
        rw [← hℓ, q.1.mem_root_iff.1 ha]; exact q.1.intervalStart_mem_root
      rw [mem_singleton.1 this] at hq1
      exact hnot' (mem_familyDarts.2 ⟨q, hq, hq1⟩)
  have hfree₀ : ∃ a ∈ T₀.root, a ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯 ∧ a ∉ T₀.darts := by
    obtain ⟨a, ha, haB⟩ := hbv
    exact ⟨a, ha, notMem_familyDarts_of_mem_bdry haB, fun h => T₀.notMem_bdry_of_mem_darts h haB⟩
  obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_insertion_inside hG hd h𝒯 T₀ c hy
    (lollipopTree_moveEquivalent hGr i hℓ) (Or.inr hbv) hdisj hfreeo hfree₀
  refine ⟨𝒯', h𝒯', PlabicData.Isomorphic.trans _ θ ⟨(collapseIsoAbsorb hGr (𝒯₁ := 𝒯)
    (𝒯₂ := insert (T₀, c) 𝒯) (i := i) ?_ hnot ?_ ?_ ?_ ?_).symm⟩⟩
  · intro e
    rw [mem_familyDarts, mem_familyDarts]
    constructor
    · rintro ⟨q, hq, heq⟩
      rcases mem_insert.1 hq with rfl | hq
      · exact Or.inr ((hD₀ e).1 heq)
      · exact Or.inl ⟨q, hq, heq⟩
    · rintro (⟨q, hq, heq⟩ | h)
      · exact ⟨q, mem_insert_of_mem hq, heq⟩
      · exact ⟨_, mem_insert_self _ _, (hD₀ e).2 h⟩
  · intro e he hne
    rw [hℓ, mem_singleton] at he
    exact absurd he hne
  · intro q hq hiq
    rcases mem_insert.1 hq with rfl | hq
    · rfl
    · exact absurd (mem_familyDarts.2 ⟨q, hq, hiq⟩) hnot
  · intro j p₁ hp₁ p₂ hp₂ h₁ h₂
    rcases mem_insert.1 hp₂ with rfl | hp₂
    · exact absurd h₂ (fun h => disjoint_left.1 (hdisj p₁ hp₁) h h₁)
    · rw [h𝒯.eq_of_mem_darts hGr hp₁ hp₂ h₁ h₂]
  · intro j p₁ hp₁ p₂ hp₂ h₁ h₂
    rw [h𝒯.eq_of_mem_darts hGr hp₁ hp₂ h₁ h₂]

open scoped Classical in
/-- **Inserting a bivalent vertex outside the trees**: the family is a collapsing family of `G`,
the collapse of the removal is the removal from the collapse, and the collapse of `G` is nearly
leafless as long as no end of the edge is a leaf of the collapse. -/
theorem exists_collapse_insertion_outside
    (hyD : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∉
      (G.bivalentRemoval hG hd).familyDarts 𝒯)
    (hnl : ((G.bivalentRemoval hG hd).collapse 𝒯).IsNearlyLeafless)
    (hlol : ∀ y : (G.bivalentRemoval hG hd).collapseDarts 𝒯,
      ((y : ({d, G.rot d}ᶜ : Set H)) : H) = G.inv d ∨
        ((y : ({d, G.rot d}ᶜ : Set H)) : H) = G.inv (G.rot d) →
      ¬((G.bivalentRemoval hG hd).collapse 𝒯).IsInternalLeaf
        (((G.bivalentRemoval hG hd).collapse 𝒯).vertexOf y)) :
    ∃ (𝒯' : Finset (G.RootedTree × Shade)) (h𝒯' : G.IsCollapsingFamily 𝒯'),
      (G.collapse 𝒯').IsNearlyLeafless ∧
      ∃ (d' : G.collapseDarts 𝒯') (hd' : (G.collapse 𝒯').IsBivalentRemovable d'),
        ((G.bivalentRemoval hG hd).collapse 𝒯).Isomorphic
          ((G.collapse 𝒯').bivalentRemoval (h𝒯'.moveEquivalent_collapse hG).1 hd') := by
  have hinv := hG.inv_involutive
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  have hσyD : (⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∉
      (G.bivalentRemoval hG hd).familyDarts 𝒯 := fun h => hyD (by
    have := inv_mem_familyDarts hGr h
    rwa [show (G.bivalentRemoval hG hd).inv ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩ =
      ⟨G.inv d, hd.inv_mem hG⟩ from
      Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd rfl)] at this)
  have hemb : ∀ q ∈ 𝒯, q.1.IsEmbedding G Subtype.val := fun q hq =>
    isEmbedding_val hG hd (fun h => hyD (mem_familyDarts.2 ⟨q, hq, h⟩))
      (fun h => hσyD (mem_familyDarts.2 ⟨q, hq, h⟩))
  have hA : Set.InjOn (Subtype.val : ({d, G.rot d}ᶜ : Set H) → H) Set.univ :=
    Subtype.val_injective.injOn
  set 𝒯' := transportFamily hGr hG hemb with h𝒯'def
  have h𝒯' : G.IsCollapsingFamily 𝒯' := isCollapsingFamily_transportFamily hGr hG hemb h𝒯 hA
    (fun _ _ => trivial)
    (fun q hq => by
      rw [q.1.root_eq_vertexOf_intervalStart, isBoundaryVertex_bivalentRemoval_vertexOf_iff])
    (fun q hq => by
      obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root q hq
      refine ⟨a, trivial, fun h => ?_, ?_⟩
      · obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
        exact haq r hr har
      · rw [← liftV_vertexOf hG hd, ← q.1.root_eq_vertexOf_intervalStart]
        exact (mem_liftV).2 ⟨a.2, ha⟩)
  have hD' : ∀ e, e ∈ G.familyDarts 𝒯' ↔
      ∃ e' ∈ (G.bivalentRemoval hG hd).familyDarts 𝒯, (e' : H) = e :=
    fun e => mem_familyDarts_transportFamily hGr hG hemb
  have hDS : ∀ y : ({d, G.rot d}ᶜ : Set H),
      y ∈ (G.bivalentRemoval hG hd).familyDarts 𝒯 ↔ (y : H) ∈ G.familyDarts 𝒯' := by
    intro y
    rw [hD']
    exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨e, he, hey⟩ => Subtype.ext hey ▸ he⟩
  have hdD' : d ∉ G.familyDarts 𝒯' := fun h => by
    obtain ⟨e, -, he⟩ := (hD' d).1 h
    exact (mem_compl_pair.1 e.2).1 he
  have hσdD' : G.rot d ∉ G.familyDarts 𝒯' := fun h => by
    obtain ⟨e, -, he⟩ := (hD' _).1 h
    exact (mem_compl_pair.1 e.2).2 he
  -- `v(d)` lies neither in a tree nor at a root of `𝒯'`
  have hx' : ∀ p ∈ 𝒯', G.vertexOf d ∉ p.1.nonRoot ∧ p.1.root ≠ G.vertexOf d := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := (mem_transportFamily hGr hG hemb).1 hp
    constructor
    · intro h
      exact hdD' ((hD' d).2 (by
        obtain ⟨w, hw, hwx⟩ := mem_image.1 h
        have : d ∈ w.image Subtype.val := hwx ▸ G.self_mem_vertexOf d
        obtain ⟨e, -, he⟩ := mem_image.1 this
        exact absurd he (mem_compl_pair.1 e.2).1))
    · intro h
      have : d ∈ G.vertexOf (q.1.intervalStart : H) := by
        change G.vertexOf (q.1.intervalStart : H) = G.vertexOf d at h
        rw [h]; exact G.self_mem_vertexOf d
      rw [G.mem_vertexOf, ← G.vertexOf_eq_vertexOf_iff] at this
      exact (mem_compl_iff_vertexOf_ne hd).1 q.1.intervalStart.2 this
  obtain ⟨hdK, hrot, hd'⟩ := collapse_isBivalentRemovable hG hd hx'
  set Y := G.collapse 𝒯' with hYdef
  have hY : Y.IsPlabicGraph := (h𝒯'.moveEquivalent_collapse hG).1
  -- the kept darts correspond
  have hcore : ∀ z : ({d, G.rot d}ᶜ : Set H),
      z ∈ (G.bivalentRemoval hG hd).collapseCore 𝒯 ↔ (z : H) ∈ G.collapseCore 𝒯' := by
    intro z
    change (z ∉ _ ∨ ∃ j, z = (G.bivalentRemoval hG hd).leg j) ↔ ((z : H) ∉ _ ∨ ∃ j, (z : H) = _)
    rw [hDS z]
    refine or_congr Iff.rfl (exists_congr fun j => ?_)
    rw [Subtype.ext_iff]
    rfl
  -- nearly leafless
  have hnlY : Y.IsNearlyLeafless := by
    intro v hv
    obtain ⟨w, rfl⟩ := Y.mem_vertices.1 (Y.mem_internalVertices.1 hv.1).1
    by_cases hwK : (w : H) ∈ G.collapseCore 𝒯'
    · have hwS : (w : H) ∈ ({d, G.rot d}ᶜ : Set H) := by
        refine mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩
        · have := hv.2
          rw [← card_map (Embedding.subtype _), map_collapse_vertexOf_of_mem hwK,
            show (w : H) = d from h, filter_vertexOf_mem_collapseCore_of_not hG
              (fun p hp => (hx' p hp).1)
              (Or.inr fun p hp => (hx' p hp).2), hd.card_vertexOf] at this
          omega
        · have := hv.2
          rw [← card_map (Embedding.subtype _), map_collapse_vertexOf_of_mem hwK,
            show (w : H) = G.rot d from h, G.vertexOf_rot,
            filter_vertexOf_mem_collapseCore_of_not hG
              (fun p hp => (hx' p hp).1)
              (Or.inr fun p hp => (hx' p hp).2), hd.card_vertexOf] at this
          omega
      set y : ({d, G.rot d}ᶜ : Set H) := ⟨w, hwS⟩ with hydef
      have hyK : y ∈ (G.bivalentRemoval hG hd).collapseCore 𝒯 := (hcore y).2 hwK
      set y' : (G.bivalentRemoval hG hd).collapseDarts 𝒯 := ⟨y, Or.inl hyK⟩ with hy'def
      -- the vertices of `w` and `y` correspond
      have hmapv : (((G.bivalentRemoval hG hd).collapse 𝒯).vertexOf y').map
          ((Embedding.subtype _).trans (Embedding.subtype _)) =
          (Y.vertexOf w).map (Embedding.subtype _) := by
        rw [← map_map, map_collapse_vertexOf_of_mem (x := y') hyK, map_collapse_vertexOf_of_mem hwK]
        ext e
        simp only [mem_map, mem_filter, Embedding.coe_subtype]
        constructor
        · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
          refine ⟨?_, (hcore z).1 hzK⟩
          rw [show G.vertexOf (w : H) = G.vertexOf ((y : ({d, G.rot d}ᶜ : Set H)) : H) from rfl,
            ← liftV_vertexOf hG hd]
          exact (mem_liftV).2 ⟨z.2, hz⟩
        · rintro ⟨he, heK⟩
          rw [show G.vertexOf (w : H) = G.vertexOf ((y : ({d, G.rot d}ᶜ : Set H)) : H) from rfl,
            ← liftV_vertexOf hG hd] at he
          obtain ⟨heS, he'⟩ := (mem_liftV).1 he
          exact ⟨⟨e, heS⟩, ⟨he', (hcore _).2 heK⟩, rfl⟩
      have hleaf : ((G.bivalentRemoval hG hd).collapse 𝒯).IsInternalLeaf
          (((G.bivalentRemoval hG hd).collapse 𝒯).vertexOf y') := by
        refine ⟨((G.bivalentRemoval hG hd).collapse 𝒯).vertexOf_mem_internalVertices.2 ?_, ?_⟩
        · rintro ⟨z, hz, hzB⟩
          apply (Y.vertexOf_mem_internalVertices).1 hv.1
          have hz' : (((z : ({d, G.rot d}ᶜ : Set H)) : H)) ∈ (Y.vertexOf w).map
              (Embedding.subtype _) := by
            rw [← hmapv]; exact mem_map_of_mem _ hz
          obtain ⟨z', hz', hzz⟩ := mem_map.1 hz'
          refine ⟨z', hz', mem_collapse_bdry.2 ?_⟩
          rw [show ((z' : H)) = _ from hzz]
          exact (mem_bivalentRemoval_bdry hG hd).1 (mem_collapse_bdry.1 hzB)
        · rw [← card_map ((Embedding.subtype _).trans (Embedding.subtype _)), hmapv, card_map]
          exact hv.2
      obtain ⟨i, -, z, hz, hzi⟩ := hnl _ hleaf
      have hzy : z = y' := by
        have := card_le_one.1 hleaf.2.le _ hz _
          (((G.bivalentRemoval hG hd).collapse 𝒯).self_mem_vertexOf y')
        exact this
      subst hzy
      have hne₁ : (w : H) ≠ G.inv d := fun h => hlol y' (Or.inl h) hleaf
      have hne₂ : (w : H) ≠ G.inv (G.rot d) := fun h => hlol y' (Or.inr h) hleaf
      -- the partner of `w` lies at `β(i)`
      have hpart : G.inv w ∈ G.bvertex i := by
        have hm : (((((G.bivalentRemoval hG hd).collapse 𝒯).inv y' :
            (G.bivalentRemoval hG hd).collapseDarts 𝒯) : ({d, G.rot d}ᶜ : Set H)) : H) ∈
            ((((G.bivalentRemoval hG hd).collapse 𝒯).bvertex i).map
              ((Embedding.subtype _).trans (Embedding.subtype _))) := mem_map_of_mem _ hzi
        rw [bvertex, ← map_map, map_collapse_vertexOf_of_mem
          ((G.bivalentRemoval hG hd).leg_mem_collapseCore 𝒯 i)] at hm
        obtain ⟨u, hu, hu'⟩ := mem_map.1 hm
        rw [coe_collapse_inv hGr, Embedding.coe_subtype] at hu'
        have hinvw : ((G.bivalentRemoval hG hd).inv y : H) = G.inv w :=
          coe_bivalentRemoval_inv_of_ne hG hd hne₁ hne₂
        have hu2 : (u : H) = G.inv w := by rwa [hu']
        rw [← hu2, ← map_bivalentRemoval_bvertex hG hd i]
        exact mem_map_of_mem _ (mem_filter.1 hu).1
      refine ⟨i, hv, w, Y.self_mem_vertexOf w, ?_⟩
      have hiw : G.inv w = G.leg i := by
        refine DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card
          (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)) hpart (G.leg_mem_bvertex i)
          (fun hB => ?_) (hG.leg_notMem_bdry i)
        apply (Y.vertexOf_mem_internalVertices).1 hv.1
        exact ⟨w, Y.self_mem_vertexOf w, mem_collapse_bdry.2 (hG.inv_mem_bdry_iff.1 hB)⟩
      have : Y.inv w = Y.leg i := Subtype.ext (by rwa [coe_collapse_inv hG])
      rw [this]
      exact Y.leg_mem_bvertex i
    · obtain ⟨j, hj, hwj⟩ := w.2.resolve_left hwK
      refine ⟨j, hv, w, Y.self_mem_vertexOf w, ?_⟩
      have : Y.inv w = Y.leg j := Subtype.ext (by rw [coe_collapse_inv hG, hwj, hinv]; rfl)
      rw [this]
      exact Y.leg_mem_bvertex j
  refine ⟨𝒯', h𝒯', hnlY, ⟨d, Or.inl hdK⟩, hd', ?_⟩
  have hcol : ∀ i, ∀ p₁ ∈ 𝒯', ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts →
      (G.bivalentRemoval hG hd).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hGr hG hemb hA (fun _ _ => trivial)
      (x := (G.bivalentRemoval hG hd).leg i) trivial hp₁ h₁
    rw [← hrc, h𝒯.eq_of_mem_darts hGr hr hp₂ hir h₂]
  have hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯', ∀ p₂ ∈ 𝒯', G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯'.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  have := isomorphic_collapse_cut_of_eq hG (bivalentRemoval_eq_cutData hG hd) hGr hDS hdD' hσdD'
    hcol hcol₁ ⟨d, Or.inl hdK⟩ (Y.rot ⟨d, Or.inl hdK⟩) rfl hrot (hd'.leg_mem hY)
  rw [bivalentRemoval_eq_cutData hY hd']
  exact this

open scoped Classical in
/-- **Inserting a bivalent vertex into the edge of a lollipop of the collapse**, including the
case of a root keeping a single dart joined to a leg, which the collapse turns into a lollipop:
the lollipop, with the trees at its vertex, becomes a tree with a boundary root containing the new
vertex. -/
theorem exists_collapse_insertion_lollipopEdge
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1)
    (hnl : ((G.bivalentRemoval hG hd).collapse 𝒯).IsNearlyLeafless)
    {u : ({d, G.rot d}ᶜ : Set H)} (hu : (u : H) = G.inv d ∨ (u : H) = G.inv (G.rot d))
    (huD : u ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯)
    (hleaf : ((G.bivalentRemoval hG hd).collapse 𝒯).IsInternalLeaf
      (((G.bivalentRemoval hG hd).collapse 𝒯).vertexOf ⟨u, Or.inl (Or.inl huD)⟩)) :
    ∃ 𝒯' : Finset (G.RootedTree × Shade), G.IsCollapsingFamily 𝒯' ∧
      (G.collapse 𝒯').Isomorphic ((G.bivalentRemoval hG hd).collapse 𝒯) := by
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  have hinvr := hGr.inv_involutive
  set u' : (G.bivalentRemoval hG hd).collapseDarts 𝒯 := ⟨u, Or.inl (Or.inl huD)⟩ with hu'
  have huK : u ∈ (G.bivalentRemoval hG hd).collapseCore 𝒯 := Or.inl huD
  -- the vertex of `u` meets the kept darts in `u` alone
  have hmapu : ((G.bivalentRemoval hG hd).vertexOf u).filter
      (· ∈ (G.bivalentRemoval hG hd).collapseCore 𝒯) = {u} := by
    rw [← map_collapse_vertexOf_of_mem (x := u') huK]
    obtain ⟨a, ha⟩ := card_eq_one.1 hleaf.2
    rw [ha, map_singleton]
    have : u' ∈ ({a} : Finset _) := ha ▸ ((G.bivalentRemoval hG hd).collapse 𝒯).self_mem_vertexOf u'
    rw [← mem_singleton.1 this]
    rfl
  have hint : ¬(G.bivalentRemoval hG hd).IsBoundaryVertex
      ((G.bivalentRemoval hG hd).vertexOf u) := by
    rintro ⟨e, he, heB⟩
    have : e ∈ ((G.bivalentRemoval hG hd).vertexOf u).filter
        (· ∈ (G.bivalentRemoval hG hd).collapseCore 𝒯) :=
      mem_filter.2 ⟨he, mem_collapseCore_of_mem_bdry heB⟩
    rw [hmapu, mem_singleton] at this
    subst this
    apply (((G.bivalentRemoval hG hd).collapse 𝒯).vertexOf_mem_internalVertices).1 hleaf.1
    exact ⟨u', ((G.bivalentRemoval hG hd).collapse 𝒯).self_mem_vertexOf u', mem_collapse_bdry.2 heB⟩
  -- it is a lollipop at some `i`: the other end of the edge is the leg `g_i`
  obtain ⟨i, -, z, hz, hzi⟩ := hnl _ hleaf
  have hzu : z = u' := card_le_one.1 hleaf.2.le _ hz _
    (((G.bivalentRemoval hG hd).collapse 𝒯).self_mem_vertexOf u')
  subst hzu
  have hσ : (G.bivalentRemoval hG hd).inv u = (G.bivalentRemoval hG hd).leg i := by
    have hm : (((G.bivalentRemoval hG hd).collapse 𝒯).inv u' : ({d, G.rot d}ᶜ : Set H)) ∈
        ((((G.bivalentRemoval hG hd).collapse 𝒯).bvertex i).map (Embedding.subtype _)) :=
      mem_map_of_mem _ hzi
    rw [bvertex, map_collapse_vertexOf_of_mem ((G.bivalentRemoval hG hd).leg_mem_collapseCore 𝒯 i),
      coe_collapse_inv hGr] at hm
    refine DiskMap.eq_of_notMem_bdry hGr.boundaryVertex_card
      ((G.bivalentRemoval hG hd).vertexOf_mem_boundaryVertices.1 (hGr.bvertex_mem i))
      (mem_filter.1 hm).1 ((G.bivalentRemoval hG hd).leg_mem_bvertex i) (fun hB => hint ?_)
      (hGr.leg_notMem_bdry i)
    exact (G.bivalentRemoval hG hd).isBoundaryVertex_vertexOf_of_mem (hGr.inv_mem_bdry_iff.1 hB)
  have huleg : u = (G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i) := by
    rw [← hσ, hinvr]
  have hlegD : (G.bivalentRemoval hG hd).leg i ∉ (G.bivalentRemoval hG hd).familyDarts 𝒯 :=
    fun h => huD (by rw [huleg]; exact inv_mem_familyDarts hGr h)
  have hleg : G.inv d = G.leg i ∨ G.inv (G.rot d) = G.leg i := by
    rcases hu with h | h
    · right
      have := congrArg Subtype.val hσ
      rwa [coe_bivalentRemoval_inv_of_eq_inv hG hd h] at this
    · left
      have := congrArg Subtype.val hσ
      rwa [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h] at this
  have hU : ∀ p ∈ 𝒯, (G.bivalentRemoval hG hd).vertexOf u ∉ p.1.nonRoot :=
    vertexOf_notMem_nonRoot_of_mem_collapseCore hGr huK
  by_cases hroot : ∃ p ∈ 𝒯, p.1.root = (G.bivalentRemoval hG hd).vertexOf u
  · -- a root keeping the single dart `u`: absorb its trees into a boundary tree
    have hthin : ∀ e ∈ (G.bivalentRemoval hG hd).vertexOf u, e ≠ u → ∃ p ∈ 𝒯,
        p.1.root = (G.bivalentRemoval hG hd).vertexOf u ∧ e ∈ p.1.darts := by
      intro e he heu
      have heK : e ∉ (G.bivalentRemoval hG hd).collapseCore 𝒯 := fun h => by
        have : e ∈ ((G.bivalentRemoval hG hd).vertexOf u).filter
            (· ∈ (G.bivalentRemoval hG hd).collapseCore 𝒯) := mem_filter.2 ⟨he, h⟩
        rw [hmapu, mem_singleton] at this
        exact heu this
      have heD : e ∈ (G.bivalentRemoval hG hd).familyDarts 𝒯 := by
        by_contra h; exact heK (Or.inl h)
      have hve : (G.bivalentRemoval hG hd).vertexOf e = (G.bivalentRemoval hG hd).vertexOf u :=
        (G.bivalentRemoval hG hd).vertexOf_eq_of_mem he
      obtain ⟨p, hp, hpr, hep⟩ := exists_root_eq_of_mem_familyDarts hGr heD
        (fun p hp => hve ▸ hU p hp)
      exact ⟨p, hp, hpr.trans hve, hep⟩
    obtain ⟨Tp, 𝒯o, h𝒯o, hTpc, hbp, huT, hlegT, hdisj, hfreeo, hfree₀, θ⟩ :=
      exists_absorbRoot hGr h𝒯 hbr huD hthin hroot hint hσ
    have hy : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ Tp.darts := by
      rcases hu with h | h
      · rwa [show (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) = u from Subtype.ext h.symm]
      · have : (G.bivalentRemoval hG hd).inv u = ⟨G.inv d, hd.inv_mem hG⟩ :=
          Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h)
        rwa [← this, hσ]
    obtain ⟨𝒯', h𝒯', θ'⟩ := exists_collapse_insertion_inside hG hd h𝒯o Tp _ hy hTpc.moveEquivalent
      (Or.inr hbp) hdisj hfreeo hfree₀
    exact ⟨𝒯', h𝒯', PlabicData.Isomorphic.trans _ θ' θ.symm⟩
  · -- a lollipop of the removal
    push Not at hroot
    have hvu : (G.bivalentRemoval hG hd).vertexOf u = {u} := by
      rw [← hmapu, filter_vertexOf_mem_collapseCore_of_not hGr hU (Or.inr hroot)]
    have hℓ : (G.bivalentRemoval hG hd).vertexOf ((G.bivalentRemoval hG hd).inv
        ((G.bivalentRemoval hG hd).leg i)) =
        {(G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i)} := by
      rwa [← huleg]
    exact exists_collapse_insertion_lollipop hG hd h𝒯 hleg hℓ hlegD

end InsertionOther

end PlabicData

end ClusterAlgebras
