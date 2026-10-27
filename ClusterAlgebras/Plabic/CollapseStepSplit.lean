/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CollapseStepContraction

/-!
# Collapse steps for vertex splits

Let `𝒯` be a collapsing family of a plabic graph `G`. If a vertex of `G` is split, there is a
collapsing family of the new graph whose collapse is isomorphic to `G/𝒯` or obtained from it by a
vertex split. This is case (VI) of FWZ's proof.

## Main results

* `ClusterAlgebras.PlabicData.exists_collapse_split_outside`: the vertex lies outside the trees.
* `ClusterAlgebras.PlabicData.exists_collapse_split_root`: the vertex is the root of a tree.
* `ClusterAlgebras.PlabicData.exists_collapse_split_inside`: the vertex lies inside a tree.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

namespace PlabicData

/-! ### Splitting a vertex outside the trees -/

section SplitOutside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-- A plabic graph whose contraction along an edge is nearly leafless is nearly leafless, if both
endpoints of the edge have at least two darts. -/
private theorem isNearlyLeafless_of_contractEdge {X : PlabicData H b} (hX : X.IsPlabicGraph)
    {d : H} (he : X.IsContractibleEdge d) (h₁ : 2 ≤ (X.vertexOf d).card)
    (h₂ : 2 ≤ (X.vertexOf (X.inv d)).card)
    (hnl : (X.contractEdge d (he.leg_mem hX)).IsNearlyLeafless) : X.IsNearlyLeafless := by
  intro v hv
  obtain ⟨y, rfl⟩ := X.mem_vertices.1 (X.mem_internalVertices.1 hv.1).1
  have hy : y ∉ X.vertexOf d ∪ X.vertexOf (X.inv d) := by
    intro h
    have h1 := hv.2
    rcases mem_union.1 h with h | h
    · rw [X.vertexOf_eq_of_mem h] at h1; omega
    · rw [X.vertexOf_eq_of_mem h] at h1; omega
  have hyS := mem_compl_pair_of_notMem hy
  have hl := (isInternalLeaf_contractEdge_vertexOf_iff_of_notMem (hleg := he.leg_mem hX) he
    (y := ⟨y, hyS⟩) hy).2 hv
  obtain ⟨i, hl', e, he', hei⟩ := hnl _ hl
  have hey : e = ⟨y, hyS⟩ := card_le_one.1 hl'.2.le _ he' _
    ((X.contractEdge d (he.leg_mem hX)).self_mem_vertexOf _)
  subst hey
  refine ⟨i, hv, y, X.self_mem_vertexOf y, ?_⟩
  rw [← map_bvertex_contractEdge hX he i (hleg := he.leg_mem hX),
    show X.inv y = (((X.contractEdge d (he.leg_mem hX)).inv ⟨y, hyS⟩ :
      (({d, X.inv d} : Set H)ᶜ : Set H)) : H) from
      (coe_contractEdge_inv (hleg := he.leg_mem hX) hX.inv_involutive ⟨y, hyS⟩).symm]
  exact mem_map_of_mem _ hei

variable {G : PlabicData H b} (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)

include hG he

/-- A dart at the same vertex of the contraction as a dart at an endpoint lies at an endpoint. -/
private theorem mem_union_of_mem_contractEdge_vertexOf {x y : (({f, G.inv f} : Set H)ᶜ : Set H)}
    (hy : y ∈ (G.contractEdge f (he.leg_mem hG)).vertexOf x)
    (hx : (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)) :
    (y : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) := by
  have h := mem_map_of_mem (Embedding.subtype _) hy
  rw [map_vertexOf_contractEdge_of_mem he.not_sameCycle hx] at h
  exact mem_union.2 (mem_mergedVertex.1 h).1

/-- A tree of the contraction whose non-root vertices avoid the merged vertex, with an interval of
one dart if its root is the merged vertex, is carried into `G` by the inclusion. -/
private theorem splitOutside_isEmbedding (q : (G.contractEdge f (he.leg_mem hG)).RootedTree)
    (hW : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H), (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) →
      (G.contractEdge f (he.leg_mem hG)).vertexOf x ∉ q.nonRoot)
    (h1 : (q.intervalStart : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) → q.intervalLength = 1) :
    q.IsEmbedding G Subtype.val := by
  have hinv := hG.inv_involutive
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  refine ⟨Subtype.val_injective.injOn, fun d _ => coe_contractEdge_inv hinv d,
    fun d hd hrd => ?_, fun d hd => ?_, ?_, ?_, ?_, fun d _ => rfl⟩
  · by_cases hσ : G.rot d ∈ (({f, G.inv f} : Set H)ᶜ : Set H)
    · exact coe_contractEdge_rot_of_mem hσ
    exfalso
    -- `d` lies at the merged vertex, which is the root
    have hdM : (d : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) := by
      have : G.rot d = f ∨ G.rot d = G.inv f := by
        by_contra h
        exact hσ (mem_compl_pair_iff.2 (not_or.1 h))
      have e := G.vertexOf_rot (d : H)
      rcases this with h | h
      · rw [h] at e
        exact mem_union_left _ (by rw [e]; exact G.self_mem_vertexOf _)
      · rw [h] at e
        exact mem_union_right _ (by rw [e]; exact G.self_mem_vertexOf _)
    have hdr : (G.contractEdge f (he.leg_mem hG)).vertexOf d = q.root :=
      (q.vertexOf_mem_or_eq_root hGc hd).resolve_left (hW d hdM)
    have ha1 : (q.intervalStart : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) :=
      mem_union_of_mem_contractEdge_vertexOf hG he
        (by rw [hdr]; exact q.intervalStart_mem_root) hdM
    have hk := h1 ha1
    have e1 := q.eq_intervalStart_of_intervalLength_eq_one hk hd (q.mem_root_iff.2 hdr)
    have e2 := q.eq_intervalStart_of_intervalLength_eq_one hk hrd (q.mem_root_iff.2 (by
      rw [(G.contractEdge f (he.leg_mem hG)).vertexOf_rot, hdr]))
    have hfix : (G.contractEdge f (he.leg_mem hG)).rot d = d := e2.trans e1.symm
    have hc := card_vertexOf_le_of_pow_apply_eq (G := G.contractEdge f (he.leg_mem hG)) (n := 1)
      one_pos (by rwa [pow_one])
    have := q.intervalLength_lt_card
    rw [hk, ← hdr] at this
    omega
  · rw [← mem_contractEdge_bdry (hleg := he.leg_mem hG)]
    exact q.notMem_bdry_of_mem_darts hd
  · intro h
    obtain ⟨d', hd', hdd'⟩ := mem_image.1 h
    have hσS : G.rot q.intervalEnd ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := hdd' ▸ d'.2
    have : (G.contractEdge f (he.leg_mem hG)).rot q.intervalEnd = d' :=
      Subtype.ext ((coe_contractEdge_rot_of_mem hσS).trans hdd'.symm)
    exact q.rot_intervalEnd_notMem hGc (this ▸ hd')
  · intro h
    obtain ⟨d', hd', hdd'⟩ := mem_image.1 h
    have hσS : G.rot d' ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
      rw [hdd', Equiv.apply_symm_apply]; exact q.intervalStart.2
    have : (G.contractEdge f (he.leg_mem hG)).rot d' = q.intervalStart :=
      Subtype.ext ((coe_contractEdge_rot_of_mem hσS).trans (by
        rw [hdd', Equiv.apply_symm_apply]))
    apply q.rot_symm_intervalStart_notMem
    rw [← this, Equiv.symm_apply_apply]
    exact hd'
  · by_cases ha : (q.intervalStart : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)
    · rw [h1 ha]
      have hS := mem_compl_pair_iff.1 q.intervalStart.2
      rcases mem_union.1 ha with h | h
      · rw [G.vertexOf_eq_of_mem h]
        exact (card_pair (Ne.symm hS.1)).symm.le.trans_lt' (by norm_num) |>.trans_le
          (card_le_card fun x hx => by
            rcases mem_insert.1 hx with rfl | hx
            · exact G.self_mem_vertexOf _
            · rwa [mem_singleton.1 hx])
      · rw [G.vertexOf_eq_of_mem h]
        exact (card_pair (Ne.symm hS.2)).symm.le.trans_lt' (by norm_num) |>.trans_le
          (card_le_card fun x hx => by
            rcases mem_insert.1 hx with rfl | hx
            · exact G.self_mem_vertexOf _
            · rwa [mem_singleton.1 hx])
    · rw [← map_vertexOf_contractEdge_of_notMem he.not_sameCycle ha (hleg := he.leg_mem hG),
        card_map, ← q.root_eq_vertexOf_intervalStart]
      exact q.intervalLength_lt_card

open scoped Classical in
/-- **Splitting a vertex outside the trees** (when both sides keep a free dart): the family carried
into `G` is a collapsing family whose collapse is nearly leafless, and the collapse of the
contraction is its contraction along `{f, f̄}`. -/
theorem exists_collapse_split_outside
    {𝒯 : Finset ((G.contractEdge f (he.leg_mem hG)).RootedTree × Shade)}
    (h𝒯 : (G.contractEdge f (he.leg_mem hG)).IsCollapsingFamily 𝒯)
    (hnl : ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯).IsNearlyLeafless)
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1)
    (hW : ∀ p ∈ 𝒯, ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) →
        (G.contractEdge f (he.leg_mem hG)).vertexOf x ∉ p.1.nonRoot)
    (hA₁ : ∃ a : (({f, G.inv f} : Set H)ᶜ : Set H), (a : H) ∈ G.vertexOf f ∧
      a ∉ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯)
    (hA₂ : ∃ a : (({f, G.inv f} : Set H)ᶜ : Set H), (a : H) ∈ G.vertexOf (G.inv f) ∧
      a ∉ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯) :
    ∃ (𝒯' : Finset (G.RootedTree × Shade)) (h𝒯' : G.IsCollapsingFamily 𝒯'),
      (G.collapse 𝒯').IsNearlyLeafless ∧ ∃ (f' : G.collapseDarts 𝒯')
        (he' : (G.collapse 𝒯').IsContractibleEdge f'),
        ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯).Isomorphic
          ((G.collapse 𝒯').contractEdge f' (he'.leg_mem (h𝒯'.moveEquivalent_collapse hG).1)) := by
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  have hemb : ∀ p ∈ 𝒯, p.1.IsEmbedding G Subtype.val := fun p hp =>
    splitOutside_isEmbedding hG he p.1 (hW p hp) fun _ => hbr p hp
  have hA : Set.InjOn (Subtype.val : (({f, G.inv f} : Set H)ᶜ : Set H) → H) Set.univ :=
    Subtype.val_injective.injOn
  have hroot : ∀ p ∈ 𝒯, G.IsBoundaryVertex (G.vertexOf (p.1.intervalStart : H)) ↔
      (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex p.1.root := fun p _ => by
    rw [p.1.root_eq_vertexOf_intervalStart, isBoundaryVertex_vertexOf_contractEdge_iff he]
  have hfree : ∀ p ∈ 𝒯, ∃ a ∈ (Set.univ : Set (({f, G.inv f} : Set H)ᶜ : Set H)),
      a ∉ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 ∧
      (a : H) ∈ G.vertexOf (p.1.intervalStart : H) := by
    intro p hp
    by_cases ha1 : (p.1.intervalStart : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)
    · rcases mem_union.1 ha1 with h | h
      · obtain ⟨a, ha, haD⟩ := hA₁
        exact ⟨a, trivial, haD, by rwa [G.vertexOf_eq_of_mem h]⟩
      · obtain ⟨a, ha, haD⟩ := hA₂
        exact ⟨a, trivial, haD, by rwa [G.vertexOf_eq_of_mem h]⟩
    · obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root p hp
      refine ⟨a, trivial, fun h => ?_, ?_⟩
      · obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
        exact haq r hr har
      · rw [p.1.root_eq_vertexOf_intervalStart] at ha
        have := mem_map_of_mem (Embedding.subtype _) ha
        rwa [map_vertexOf_contractEdge_of_notMem hne ha1] at this
  have h𝒯' := isCollapsingFamily_transportFamily hGc hG hemb h𝒯 hA (fun _ _ => trivial) hroot hfree
  set 𝒯' := transportFamily hGc hG hemb with h𝒯'def
  have hDt : ∀ x : H, x ∈ G.familyDarts 𝒯' ↔
      ∃ d ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯, (d : H) = x :=
    fun x => mem_familyDarts_transportFamily hGc hG hemb
  have hfD : f ∉ G.familyDarts 𝒯' := fun h => by
    obtain ⟨d, -, hd⟩ := (hDt f).1 h
    exact (mem_compl_pair_iff.1 d.2).1 hd
  have hifD : G.inv f ∉ G.familyDarts 𝒯' := fun h => by
    obtain ⟨d, -, hd⟩ := (hDt _).1 h
    exact (mem_compl_pair_iff.1 d.2).2 hd
  have hD : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      x ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 ↔ (x : H) ∈ G.familyDarts 𝒯' := by
    intro x
    rw [hDt]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨d, hd, hdx⟩
      rwa [← Subtype.ext hdx]
  set X := G.collapse 𝒯' with hXdef
  have hX : X.IsPlabicGraph := (h𝒯'.moveEquivalent_collapse hG).1
  have hinvX := hX.inv_involutive
  have hfK : f ∈ G.collapseCore 𝒯' := Or.inl hfD
  have hfK' : G.inv f ∈ G.collapseCore 𝒯' := Or.inl hifD
  set f' : G.collapseDarts 𝒯' := ⟨f, Or.inl hfK⟩ with hf'def
  have hif' : ((X.inv f' : G.collapseDarts 𝒯') : H) = G.inv f := coe_collapse_inv hG f'
  have hmap₁ : (X.vertexOf f').map (Embedding.subtype _) =
      (G.vertexOf f).filter (· ∈ G.collapseCore 𝒯') := map_collapse_vertexOf_of_mem hfK
  have hmap₂ : (X.vertexOf (X.inv f')).map (Embedding.subtype _) =
      (G.vertexOf (G.inv f)).filter (· ∈ G.collapseCore 𝒯') := by
    rw [map_collapse_vertexOf_of_mem (x := X.inv f') (by rwa [hif']), hif']
  have hint₁ : ¬X.IsBoundaryVertex (X.vertexOf f') := by
    rintro ⟨z, hz, hzB⟩
    apply he.not_isBoundaryVertex
    have : (z : H) ∈ (X.vertexOf f').map (Embedding.subtype _) := mem_map_of_mem _ hz
    rw [hmap₁] at this
    exact ⟨z, (mem_filter.1 this).1, mem_collapse_bdry.1 hzB⟩
  have hint₂ : ¬X.IsBoundaryVertex (X.vertexOf (X.inv f')) := by
    rintro ⟨z, hz, hzB⟩
    apply he.not_isBoundaryVertex_inv
    have : (z : H) ∈ (X.vertexOf (X.inv f')).map (Embedding.subtype _) := mem_map_of_mem _ hz
    rw [hmap₂] at this
    exact ⟨z, (mem_filter.1 this).1, mem_collapse_bdry.1 hzB⟩
  have he' : X.IsContractibleEdge f' := by
    refine ⟨fun h => ?_, X.vertexOf_mem_internalVertices.2 hint₁,
      X.vertexOf_mem_internalVertices.2 hint₂, ?_⟩
    · have : f ∈ (G.vertexOf (G.inv f)).filter (· ∈ G.collapseCore 𝒯') := by
        rw [← hmap₂, ← h, hmap₁]; exact mem_filter.2 ⟨G.self_mem_vertexOf f, hfK⟩
      exact he.vertexOf_ne (G.vertexOf_eq_of_mem (mem_filter.1 this).1)
    · change G.collapseColour 𝒯' (X.inv f') = G.collapseColour 𝒯' f'
      rw [collapseColour_of_mem_collapseCore hG (by rwa [hif']),
        collapseColour_of_mem_collapseCore hG hfK, hif']
      exact he.colour_inv
  -- each endpoint keeps a free dart
  have hcard : ∀ {g : H} (hg : g ∈ G.collapseCore 𝒯') {a : (({f, G.inv f} : Set H)ᶜ : Set H)},
      (a : H) ∈ G.vertexOf g → a ∉ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 →
      (a : H) ≠ g → 2 ≤ ((G.vertexOf g).filter (· ∈ G.collapseCore 𝒯')).card := by
    intro g hg a ha haD hag
    refine (card_pair hag).symm.le.trans (card_le_card fun x hx => ?_)
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_filter.2 ⟨ha, Or.inl (fun h => haD ((hD a).2 h))⟩
    · rw [mem_singleton.1 hx]; exact mem_filter.2 ⟨G.self_mem_vertexOf _, hg⟩
  have h₁ : 2 ≤ (X.vertexOf f').card := by
    obtain ⟨a, ha, haD⟩ := hA₁
    rw [← card_map (Embedding.subtype _), hmap₁]
    exact hcard hfK ha haD (mem_compl_pair_iff.1 a.2).1
  have h₂ : 2 ≤ (X.vertexOf (X.inv f')).card := by
    obtain ⟨a, ha, haD⟩ := hA₂
    rw [← card_map (Embedding.subtype _), hmap₂]
    exact hcard hfK' ha haD (mem_compl_pair_iff.1 a.2).2
  have hcol : ∀ i, ∀ p₁ ∈ 𝒯', ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts →
      (G.contractEdge f (he.leg_mem hG)).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hGc hG hemb hA (fun _ _ => trivial)
      (x := (G.contractEdge f (he.leg_mem hG)).leg i) trivial hp₁ h₁
    rw [← hrc, h𝒯.eq_of_mem_darts hGc hr hp₂ hir h₂]
  have hcol₁ : ∀ i, ∀ p₁ ∈ 𝒯', ∀ p₂ ∈ 𝒯', G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯'.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  have hiso := isomorphic_collapse_cut_of_eq hG (contractEdge_eq_cutData hinv (he.leg_mem hG)) hGc
    hD hfD hifD hcol hcol₁ f' (X.inv f') rfl hif' (he'.leg_mem hX)
  have hiso' : ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯).Isomorphic
      (X.contractEdge f' (he'.leg_mem hX)) := by
    rwa [contractEdge_eq_cutData hinvX]
  obtain ⟨θ⟩ := hiso'
  exact ⟨𝒯', h𝒯', isNearlyLeafless_of_contractEdge hX he' h₁ h₂
    (θ.isNearlyLeafless (h𝒯.moveEquivalent_collapse hGc).1 (hX.contractEdge he') hnl),
    f', he', ⟨θ⟩⟩

end SplitOutside

/-- The dart preceding the interval start lies at the root. -/
theorem RootedTree.vertexOf_rot_symm_intervalStart {H : Type} [Fintype H] [DecidableEq H]
    {b : ℕ} {G : PlabicData H b} (T : G.RootedTree) :
    G.vertexOf (G.rot.symm T.intervalStart) = T.root := by
  rw [← G.vertexOf_rot, Equiv.apply_symm_apply, ← T.root_eq_vertexOf_intervalStart]

/-! ### Extending a tree with a thin internal root by one edge -/

section ExtendInternal

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) (T : G.RootedTree) (hx : ¬G.IsBoundaryVertex T.root)
  (hthin : ∀ e ∈ T.root, e ∉ T.darts → e = G.rot.symm T.intervalStart)
  (hw : G.vertexOf (G.inv (G.rot.symm T.intervalStart)) ∉ insert T.root T.nonRoot)
  (hwi : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.rot.symm T.intervalStart))))
  (hw2 : 2 ≤ (G.vertexOf (G.inv (G.rot.symm T.intervalStart))).card)

include hG hx hthin hw hwi hw2

namespace ExtendInternal

omit hw hw2 in
private theorem mem_treeDarts_iff {e : H} :
    e ∈ G.treeDarts (insert T.root T.nonRoot) ↔
      e ∈ T.darts ∨ e = G.rot.symm T.intervalStart ∨ e = G.inv (G.rot.symm T.intervalStart) := by
  have hinv := hG.inv_involutive
  have hz : G.rot.symm T.intervalStart ∈ T.root :=
    T.mem_root_iff.2 T.vertexOf_rot_symm_intervalStart
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
        rw [← hthin _ (T.mem_root_iff.2 h) heD, hinv]
    · exact Or.inl (G.mem_treeDarts.2 ⟨hB, Or.inr h⟩)
  · rintro (h | rfl | rfl)
    · obtain ⟨hB, h⟩ := G.mem_treeDarts.1 h
      exact ⟨hB, h.imp Or.inr Or.inr⟩
    · refine ⟨fun hB => hx ?_, Or.inl (Or.inl (T.mem_root_iff.1 hz))⟩
      rw [← T.mem_root_iff.1 hz]
      exact G.isBoundaryVertex_vertexOf_of_mem hB
    · refine ⟨fun hB => hwi (G.isBoundaryVertex_vertexOf_of_mem hB), Or.inr (Or.inl ?_)⟩
      rw [hinv]; exact T.mem_root_iff.1 hz

end ExtendInternal

/-- **A tree extended by an edge at its root**: if all the darts of the internal root `v` of `T`
except one, `z`, lie in the interval, and the other end `w` of `z` is an internal vertex outside
`T` with at least two darts, then `(w, W ∪ {v})` is a rooted tree whose interval is `z̄`. -/
private noncomputable def extendInternalTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hD := fun e => ExtendInternal.mem_treeDarts_iff hG T hx hthin hwi (e := e)
  have hzr : G.vertexOf (G.rot.symm T.intervalStart) = T.root :=
    T.vertexOf_rot_symm_intervalStart
  have hz : G.rot.symm T.intervalStart ∈ T.root := T.mem_root_iff.2 hzr
  have hwr : G.vertexOf (G.inv (G.rot.symm T.intervalStart)) ≠ T.root := fun h =>
    hw (h ▸ mem_insert_self _ _)
  have hwW : G.vertexOf (G.inv (G.rot.symm T.intervalStart)) ∉ T.nonRoot := fun h =>
    hw (mem_insert_of_mem h)
  have hwD : ∀ e, G.vertexOf e = G.vertexOf (G.inv (G.rot.symm T.intervalStart)) →
      e ∉ T.darts := fun e he heD => by
    rcases T.vertexOf_mem_or_eq_root hG heD with h | h
    · exact hwW (he ▸ h)
    · exact hwr (he ▸ h)
  { root := G.vertexOf (G.inv (G.rot.symm T.intervalStart))
    nonRoot := insert T.root T.nonRoot
    root_mem_vertices := G.vertexOf_mem_vertices _
    nonRoot_nonempty := ⟨_, mem_insert_self _ _⟩
    nonRoot_subset := insert_subset (G.mem_internalVertices.2 ⟨T.root_mem_vertices, hx⟩)
      T.nonRoot_subset
    root_notMem_nonRoot := hw
    vertexOf_inv_mem := by
      intro e he
      rcases mem_insert.1 he with h | h
      · by_cases heD : e ∈ T.darts
        · exact mem_insert_of_mem (mem_insert_of_mem
            (T.vertexOf_inv_mem_nonRoot_of_mem_root heD (T.mem_root_iff.2 h)))
        · rw [hthin e (T.mem_root_iff.2 h) heD]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (T.vertexOf_inv_mem e h)
    exists_interval := by
      refine ⟨G.inv (G.rot.symm T.intervalStart), G.self_mem_vertexOf _, 1, le_rfl, by omega,
        fun e he => ?_, ?_⟩
      · rw [hD]
        constructor
        · rintro (h | h | h)
          · exact absurd h (hwD e (G.vertexOf_eq_of_mem he))
          · exfalso
            apply hwr
            rw [← G.vertexOf_eq_of_mem he, h, hzr]
          · exact ⟨0, one_pos, h.symm⟩
        · rintro ⟨j, hj, rfl⟩
          obtain rfl : j = 0 := by omega
          exact Or.inr (Or.inr rfl)
      · rw [hD]
        rintro (h | h | h)
        · exact hwD _ (by rw [← G.vertexOf_rot, Equiv.apply_symm_apply]) h
        · have h' : G.vertexOf (G.rot.symm (G.inv (G.rot.symm T.intervalStart))) =
              G.vertexOf (G.inv (G.rot.symm T.intervalStart)) := by
            rw [← G.vertexOf_rot, Equiv.apply_symm_apply]
          rw [h, hzr] at h'
          exact hwr h'.symm
        · have hfix : G.rot (G.inv (G.rot.symm T.intervalStart)) =
              G.inv (G.rot.symm T.intervalStart) := by
            conv_lhs => rw [← h]
            exact Equiv.apply_symm_apply _ _
          have := card_vertexOf_le_of_pow_apply_eq (G := G) (n := 1) one_pos
            (by rwa [pow_one])
          omega
    card_image_edgeOf := by
      have hD' : G.treeDarts (insert T.root T.nonRoot) =
          insert (G.rot.symm T.intervalStart)
            (insert (G.inv (G.rot.symm T.intervalStart)) T.darts) := by
        ext e
        rw [hD, mem_insert, mem_insert]
        tauto
      have hzD := T.rot_symm_intervalStart_notMem
      have hizD := hwD _ rfl
      have hne : G.rot.symm T.intervalStart ≠ G.inv (G.rot.symm T.intervalStart) :=
        (hG.inv_ne _).symm
      have h2 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
        (S := G.treeDarts (insert T.root T.nonRoot)) fun e he => inv_mem_treeDarts' hG he
      rw [hD', card_insert_of_notMem (by rw [mem_insert, not_or]; exact ⟨hne, hzD⟩),
        card_insert_of_notMem hizD, T.card_darts hG] at h2
      rw [card_insert_of_notMem T.root_notMem_nonRoot, hD']
      omega
    reflTransGen_treeAdj := by
      have hmono : ∀ u u', G.TreeAdj T.nonRoot u u' →
          G.TreeAdj (insert T.root T.nonRoot) u u' := by
        rintro _ _ ⟨e, he, rfl, rfl⟩
        exact ⟨e, (hD e).2 (Or.inl he), rfl, rfl⟩
      have hstep : G.TreeAdj (insert T.root T.nonRoot)
          (G.vertexOf (G.inv (G.rot.symm T.intervalStart))) T.root :=
        ⟨G.inv (G.rot.symm T.intervalStart), (hD _).2 (Or.inr (Or.inr rfl)), rfl,
          by rwa [hinv]⟩
      intro u hu
      rcases mem_insert.1 hu with rfl | hu
      · exact .refl
      · exact Relation.ReflTransGen.head hstep ((T.reflTransGen_treeAdj u hu).mono hmono) }

namespace ExtendInternal

private theorem darts_iff {e : H} : e ∈ (extendInternalTree hG T hx hthin hw hwi hw2).darts ↔
    e ∈ T.darts ∨ e = G.rot.symm T.intervalStart ∨ e = G.inv (G.rot.symm T.intervalStart) :=
  mem_treeDarts_iff hG T hx hthin hwi

private theorem root_eq : (extendInternalTree hG T hx hthin hw hwi hw2).root =
    G.vertexOf (G.inv (G.rot.symm T.intervalStart)) := rfl

private theorem nonRoot_eq :
    (extendInternalTree hG T hx hthin hw hwi hw2).nonRoot = insert T.root T.nonRoot := rfl

private theorem intervalStart_eq : (extendInternalTree hG T hx hthin hw hwi hw2).intervalStart =
    G.inv (G.rot.symm T.intervalStart) := by
  set T' := extendInternalTree hG T hx hthin hw hwi hw2
  have hD := fun e => darts_iff hG T hx hthin hw hwi hw2 (e := e)
  refine (T'.eq_intervalStart_of_rot_symm_notMem ((hD _).2 (Or.inr (Or.inr rfl)))
    (G.self_mem_vertexOf _) ?_).symm
  have hzr : G.vertexOf (G.rot.symm T.intervalStart) = T.root :=
    T.vertexOf_rot_symm_intervalStart
  have hv : G.vertexOf (G.rot.symm (G.inv (G.rot.symm T.intervalStart))) =
      G.vertexOf (G.inv (G.rot.symm T.intervalStart)) := by
    rw [← G.vertexOf_rot, Equiv.apply_symm_apply]
  rw [hD]
  rintro (h | h | h)
  · rcases T.vertexOf_mem_or_eq_root hG h with h' | h'
    · rw [hv] at h'; exact hw (mem_insert_of_mem h')
    · rw [hv] at h'; exact hw (by rw [h']; exact mem_insert_self _ _)
  · rw [h, hzr] at hv
    exact hw (by rw [← hv]; exact mem_insert_self _ _)
  · have hfix : G.rot (G.inv (G.rot.symm T.intervalStart)) =
        G.inv (G.rot.symm T.intervalStart) := by
      conv_lhs => rw [← h]
      exact Equiv.apply_symm_apply _ _
    have := card_vertexOf_le_of_pow_apply_eq (G := G) (n := 1) one_pos
      (by rwa [pow_one])
    omega

private theorem intervalLength_eq_one :
    (extendInternalTree hG T hx hthin hw hwi hw2).intervalLength = 1 := by
  set T' := extendInternalTree hG T hx hthin hw hwi hw2
  rw [T'.intervalLength_eq_card, card_eq_one]
  refine ⟨T'.intervalStart, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2
    ⟨T'.intervalStart_mem_root, T'.intervalStart_mem_darts⟩, fun e he => ?_⟩⟩
  obtain ⟨hr, hd⟩ := mem_filter.1 he
  obtain ⟨j, hj, rfl⟩ := T'.exists_eq_pow_of_mem_root hd hr
  have hk : T'.intervalLength ≤ 1 := by
    rw [T'.intervalLength_eq_card]
    refine card_le_one.2 fun a ha c hc => ?_
    have key : ∀ a ∈ T'.root.filter (· ∈ T'.darts), a = G.inv (G.rot.symm T.intervalStart) := by
      intro a ha
      obtain ⟨har, had⟩ := mem_filter.1 ha
      have hvr : G.vertexOf a = G.vertexOf (G.inv (G.rot.symm T.intervalStart)) :=
        T'.mem_root_iff.1 har
      rcases (darts_iff hG T hx hthin hw hwi hw2).1 had with h | h | h
      · exfalso
        rcases T.vertexOf_mem_or_eq_root hG h with h' | h'
        · exact hw (mem_insert_of_mem (by rwa [hvr] at h'))
        · exact hw (by rw [← hvr, h']; exact mem_insert_self _ _)
      · exfalso
        apply hw
        rw [← hvr, h, T.vertexOf_rot_symm_intervalStart]
        exact mem_insert_self _ _
      · exact h
    rw [key a ha, key c hc]
  obtain rfl : j = 0 := by omega
  rfl

private theorem not_isBoundaryVertex_root :
    ¬G.IsBoundaryVertex (extendInternalTree hG T hx hthin hw hwi hw2).root := hwi

/-- Removing the root of the extended tree gives back `T`. -/
private theorem rootRemovalTree_eq :
    rootRemovalTree hG (extendInternalTree hG T hx hthin hw hwi hw2)
      (intervalLength_eq_one hG T hx hthin hw hwi hw2) (by
        rw [intervalStart_eq, nonRoot_eq, hG.inv_involutive, T.vertexOf_rot_symm_intervalStart,
          erase_insert T.root_notMem_nonRoot]
        exact T.nonRoot_nonempty) = T := by
  have hzr : G.vertexOf (G.rot.symm T.intervalStart) = T.root :=
    T.vertexOf_rot_symm_intervalStart
  refine RootedTree.ext' ?_ ?_
  · rw [RootRemoval.root_eq, intervalStart_eq, hG.inv_involutive, hzr]
  · rw [RootRemoval.nonRoot_eq, intervalStart_eq, nonRoot_eq, hG.inv_involutive, hzr,
      erase_insert T.root_notMem_nonRoot]

/-- The extended tree is collapsible of the colour of `T`, if `w` has that colour. -/
private theorem isCollapsibleOfColour {c : Shade} (hT : T.IsCollapsibleOfColour c)
    (hcw : G.colour (G.inv (G.rot.symm T.intervalStart)) = c) :
    (extendInternalTree hG T hx hthin hw hwi hw2).IsCollapsibleOfColour c := by
  set T' := extendInternalTree hG T hx hthin hw hwi hw2
  have hx' := not_isBoundaryVertex_root hG T hx hthin hw hwi hw2
  have h1 := intervalLength_eq_one hG T hx hthin hw hwi hw2
  have hne : (T'.nonRoot.erase (G.vertexOf (G.inv T'.intervalStart))).Nonempty := by
    rw [intervalStart_eq, nonRoot_eq, hG.inv_involutive, T.vertexOf_rot_symm_intervalStart,
      erase_insert T.root_notMem_nonRoot]
    exact T.nonRoot_nonempty
  have hiso := RootRemoval.plabicData_isomorphic hG T' hx' h1 hne
  rw [rootRemovalTree_eq hG T hx hthin hw hwi hw2] at hiso
  have hloc : PlabicGraph.IsLocalMove .m2 ⟨_, T'.plabicData, T'.isPlabicGraph_plabicData hG⟩
      ⟨_, T.plabicData, hT.isPlabicGraph⟩ :=
    Or.inl ⟨RootRemoval.dartGBar T' hx', RootRemoval.isBivalentRemovable_dartGBar hG T' hx' h1,
      hiso.symm⟩
  refine ⟨T'.isPlabicGraph_plabicData hG,
    (PlabicGraph.MoveEquivalent.of_isLocalMove (by simp) hloc).trans hT.moveEquivalent,
    Or.inl ⟨hx', fun e he => ?_⟩⟩
  rw [root_eq] at he
  rw [hG.colour_eq_of_mem_vertexOf hwi he, hcw]

end ExtendInternal

end ExtendInternal

/-! ### The tree of a leaf -/

section LeafTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {z : H} (hz1 : G.rot z = z) (hu : ¬G.IsBoundaryVertex (G.vertexOf z))
  (hwi : ¬G.IsBoundaryVertex (G.vertexOf (G.inv z))) (hw2 : 2 ≤ (G.vertexOf (G.inv z)).card)

include hG hz1 hu hwi hw2

namespace LeafTree

omit hG hu hwi hw2 in
private theorem vertexOf_eq_iff {e : H} : G.vertexOf e = G.vertexOf z ↔ e = z := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hc := card_vertexOf_le_of_pow_apply_eq (G := G) (n := 1) one_pos
    (by rwa [pow_one])
  exact card_le_one.1 hc _ (by rw [← h]; exact G.self_mem_vertexOf e) _ (G.self_mem_vertexOf z)

omit hu hwi hw2 in
private theorem vertexOf_ne : G.vertexOf z ≠ G.vertexOf (G.inv z) := fun h =>
  hG.inv_ne z ((vertexOf_eq_iff hz1).1 h.symm)

omit hw2 in
private theorem mem_treeDarts_iff {e : H} :
    e ∈ G.treeDarts {G.vertexOf z} ↔ e = z ∨ e = G.inv z := by
  have hinv := hG.inv_involutive
  rw [mem_treeDarts, mem_singleton, mem_singleton, vertexOf_eq_iff hz1, vertexOf_eq_iff hz1]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl h
    · right; rw [← h, hinv]
  · rintro (rfl | rfl)
    · exact ⟨fun hB => hu (G.isBoundaryVertex_vertexOf_of_mem hB), Or.inl rfl⟩
    · exact ⟨fun hB => hwi (G.isBoundaryVertex_vertexOf_of_mem hB), Or.inr (hinv z)⟩

end LeafTree

/-- **The tree of a leaf**: an internal leaf `{z}` joined to an internal vertex `w` with at least
two darts forms the rooted tree `(w, {{z}})`, whose interval is `z̄`. -/
private noncomputable def leafTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hD := fun e => LeafTree.mem_treeDarts_iff hG hz1 hu hwi (e := e)
  have hne := LeafTree.vertexOf_ne hG hz1
  { root := G.vertexOf (G.inv z)
    nonRoot := {G.vertexOf z}
    root_mem_vertices := G.vertexOf_mem_vertices _
    nonRoot_nonempty := singleton_nonempty _
    nonRoot_subset := singleton_subset_iff.2
      (G.mem_internalVertices.2 ⟨G.vertexOf_mem_vertices _, hu⟩)
    root_notMem_nonRoot := by rw [mem_singleton]; exact Ne.symm hne
    vertexOf_inv_mem := by
      intro e he
      rw [mem_singleton, LeafTree.vertexOf_eq_iff hz1] at he
      subst he
      exact mem_insert_self _ _
    exists_interval := by
      refine ⟨G.inv z, G.self_mem_vertexOf _, 1, le_rfl, by omega, fun e he => ?_, ?_⟩
      · rw [hD]
        constructor
        · rintro (rfl | rfl)
          · exact absurd (G.vertexOf_eq_of_mem he) hne
          · exact ⟨0, one_pos, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          obtain rfl : j = 0 := by omega
          exact Or.inr rfl
      · rw [hD]
        rintro (h | h)
        · apply hne
          have h' : G.vertexOf (G.rot.symm (G.inv z)) = G.vertexOf (G.inv z) := by
            rw [← G.vertexOf_rot, Equiv.apply_symm_apply]
          rw [h] at h'
          exact h'
        · have hfix : G.rot (G.inv z) = G.inv z := by
            conv_lhs => rw [← h]
            exact Equiv.apply_symm_apply _ _
          have := card_vertexOf_le_of_pow_apply_eq (G := G) (n := 1) one_pos
            (by rwa [pow_one])
          omega
    card_image_edgeOf := by
      have hD' : G.treeDarts {G.vertexOf z} = {z, G.inv z} := by
        ext e
        rw [hD, mem_insert, mem_singleton]
      have h2 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
        (S := G.treeDarts {G.vertexOf z}) fun e he => inv_mem_treeDarts' hG he
      rw [hD', card_pair (hG.inv_ne z).symm] at h2
      rw [card_singleton, hD']
      omega
    reflTransGen_treeAdj := by
      intro u hu'
      rcases mem_insert.1 hu' with rfl | hu'
      · exact .refl
      · rw [mem_singleton.1 hu']
        exact Relation.ReflTransGen.single ⟨G.inv z, (hD _).2 (Or.inr rfl), rfl, by rw [hinv]⟩ }

namespace LeafTree

private theorem darts_iff {e : H} : e ∈ (leafTree hG hz1 hu hwi hw2).darts ↔ e = z ∨ e = G.inv z :=
  mem_treeDarts_iff hG hz1 hu hwi

private theorem root_eq : (leafTree hG hz1 hu hwi hw2).root = G.vertexOf (G.inv z) := rfl

private theorem nonRoot_eq : (leafTree hG hz1 hu hwi hw2).nonRoot = {G.vertexOf z} := rfl

private theorem intervalStart_eq : (leafTree hG hz1 hu hwi hw2).intervalStart = G.inv z := by
  set T := leafTree hG hz1 hu hwi hw2
  refine (T.eq_intervalStart_of_rot_symm_notMem ((darts_iff hG hz1 hu hwi hw2).2 (Or.inr rfl))
    (G.self_mem_vertexOf _) ?_).symm
  rw [darts_iff]
  rintro (h | h)
  · apply vertexOf_ne hG hz1
    have h' : G.vertexOf (G.rot.symm (G.inv z)) = G.vertexOf (G.inv z) := by
      rw [← G.vertexOf_rot, Equiv.apply_symm_apply]
    rw [h] at h'
    exact h'
  · have hfix : G.rot (G.inv z) = G.inv z := by
      conv_lhs => rw [← h]
      exact Equiv.apply_symm_apply _ _
    have := card_vertexOf_le_of_pow_apply_eq (G := G) (n := 1) one_pos
      (by rwa [pow_one])
    omega

private theorem intervalLength_eq_one : (leafTree hG hz1 hu hwi hw2).intervalLength = 1 := by
  set T := leafTree hG hz1 hu hwi hw2
  have := T.one_le_intervalLength
  by_contra h
  have hmem : G.rot T.intervalStart ∈ T.darts :=
    T.pow_intervalStart_mem_darts (j := 1) (by omega) |> fun h' => by rwa [pow_one] at h'
  rw [darts_iff, intervalStart_eq] at hmem
  rcases hmem with h' | h'
  · apply vertexOf_ne hG hz1
    have := G.vertexOf_rot (G.inv z)
    rw [h'] at this
    exact this
  · have := card_vertexOf_le_of_pow_apply_eq (G := G) (n := 1) one_pos
      (by rwa [pow_one])
    omega

/-- The tree of a leaf is collapsible of the colour of the leaf. -/
private theorem isCollapsibleOfColour (hcw : G.colour (G.inv z) = G.colour z) :
    (leafTree hG hz1 hu hwi hw2).IsCollapsibleOfColour (G.colour z) := by
  have hinv := hG.inv_involutive
  set T := leafTree hG hz1 hu hwi hw2
  have hx : ¬G.IsBoundaryVertex T.root := hwi
  have h1 : T.intervalLength = 1 := intervalLength_eq_one hG hz1 hu hwi hw2
  have hstart : T.intervalStart = G.inv z := intervalStart_eq hG hz1 hu hwi hw2
  set P := T.plabicData
  have hP := T.isPlabicGraph_plabicData hG
  set δ := RootRemoval.dartGBar T hx
  have hδ := RootRemoval.isBivalentRemovable_dartGBar hG T hx h1
  set R := P.bivalentRemoval hP hδ
  have hzD : z ∈ T.darts := (darts_iff hG hz1 hu hwi hw2).2 (Or.inl rfl)
  have hzS : (⟨.inl z, hzD⟩ : T.Dart) ∈ ({δ, P.rot δ}ᶜ : Set T.Dart) := by
    refine mem_compl_pair.2 ⟨fun h => ?_, fun h => ?_⟩
    · exact absurd (congrArg Subtype.val h) (fun h' => by cases h')
    · rw [RootRemoval.rot_dartGBar hG T hx] at h
      have := congrArg Subtype.val h
      simp only [Sum.inl.injEq] at this
      rw [hstart] at this
      exact hG.inv_ne z this.symm
  have hlegS : P.leg 0 = P.inv δ := Subtype.ext (by
    rw [T.coe_inv_plabicData hG]
    change T.legDart.1 = _
    rw [RootedTree.legDart, dif_neg hx]
    rfl)
  have hval : P.inv (P.rot δ) = ⟨.inl z, hzD⟩ := by
    rw [RootRemoval.rot_dartGBar hG T hx]
    apply Subtype.ext
    rw [T.coe_inv_plabicData hG]
    simp [hstart, hinv z]
  have hRinv : R.inv (R.leg 0) = ⟨⟨.inl z, hzD⟩, hzS⟩ := by
    apply Subtype.ext
    rw [coe_bivalentRemoval_inv_of_eq_inv hP hδ hlegS, hval]
  have hRrot : R.rot ⟨⟨.inl z, hzD⟩, hzS⟩ = ⟨⟨.inl z, hzD⟩, hzS⟩ := by
    apply Subtype.ext
    rw [coe_bivalentRemoval_rot, T.rot_inl_of_mem hG hzD (by rwa [hz1])]
    simp [hz1]
  have hRP : R.IsPlabicGraph := isPlabicGraph_bivalentRemoval hP hδ
  have hcard : (R.vertexOf (R.inv (R.leg 0))).card = 1 := by
    rw [hRinv]
    exact le_antisymm (card_vertexOf_le_of_pow_apply_eq (G := R) (n := 1) one_pos
      (by rwa [pow_one])) (card_pos.2 ⟨_, R.self_mem_vertexOf _⟩)
  have hcol : R.colour (R.inv (R.leg 0)) = G.colour z := by rw [hRinv]; rfl
  have hloc : PlabicGraph.IsLocalMove .m2 ⟨_, P, hP⟩ (lollipopPlabicGraph (G.colour z)) :=
    Or.inl ⟨δ, hδ, lollipopGraph_isomorphic hRP hcard hcol⟩
  refine ⟨hP, PlabicGraph.MoveEquivalent.of_isLocalMove (by simp) hloc, Or.inl ⟨hx, ?_⟩⟩
  intro e he
  rw [root_eq] at he
  rw [hG.colour_eq_of_mem_vertexOf hwi he, hcw]

end LeafTree

end LeafTree

/-! ### Splitting a vertex whose side is filled by trees -/

section SplitRoot

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

open scoped Classical in
/-- **Adding a tree to a collapsing family**, when its non-root vertices and root are disjoint from
those of the members, and the roots keep darts outside all the trees. -/
private theorem isCollapsingFamily_insert {𝒯o : Finset (G.RootedTree × Shade)}
    (h𝒯o : G.IsCollapsingFamily 𝒯o) {T : G.RootedTree} {c : Shade}
    (hT : T.IsCollapsibleOfColour c) (hnr : ∀ q ∈ 𝒯o, Disjoint T.nonRoot q.1.nonRoot)
    (hr₁ : ∀ q ∈ 𝒯o, T.root ∉ q.1.nonRoot) (hr₂ : ∀ q ∈ 𝒯o, q.1.root ∉ T.nonRoot)
    (hfreeo : ∀ q ∈ 𝒯o, ∃ a ∈ q.1.root, a ∉ G.familyDarts 𝒯o ∧ a ∉ T.darts)
    (hfree₀ : ∃ a ∈ T.root, a ∉ G.familyDarts 𝒯o ∧ a ∉ T.darts) :
    G.IsCollapsingFamily (insert (T, c) 𝒯o) := by
  have hfD : ∀ {a}, a ∉ G.familyDarts 𝒯o → a ∉ T.darts → ∀ r ∈ insert (T, c) 𝒯o,
      a ∉ r.1.darts := by
    intro a h₁ h₂ r hr har
    rcases mem_insert.1 hr with rfl | hr
    · exact h₂ har
    · exact h₁ (mem_familyDarts.2 ⟨r, hr, har⟩)
  refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_, fun p hp q hq hpq => ?_, fun p hp => ?_⟩
  · rcases mem_insert.1 hp with rfl | hp
    · exact hT
    · exact h𝒯o.isCollapsibleOfColour p hp
  · rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
    · exact absurd rfl hpq
    · exact hnr q hq
    · exact (hnr p hp).symm
    · exact h𝒯o.disjoint_nonRoot p hp q hq hpq
  · rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
    · exact absurd rfl hpq
    · exact hr₁ q hq
    · exact hr₂ p hp
    · exact h𝒯o.root_notMem_nonRoot p hp q hq hpq
  · rcases mem_insert.1 hp with rfl | hp
    · obtain ⟨a, ha, h₁, h₂⟩ := hfree₀
      exact ⟨a, ha, hfD h₁ h₂⟩
    · obtain ⟨a, ha, h₁, h₂⟩ := hfreeo p hp
      exact ⟨a, ha, hfD h₁ h₂⟩

variable (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)

include hG he

open scoped Classical in
/-- **Splitting a vertex one of whose sides is filled by trees**: if the darts of the merged vertex
on the side of `g ∈ {f, f̄}` all lie in trees, the trees rooted there, the vertex `v(g)` and the
edge `{g, ḡ}` form one collapsible tree rooted at `v(ḡ)` (a single edge to the leaf `v(g)` if that
side is empty), and the collapse does not change. -/
theorem exists_collapse_split_root
    {𝒯 : Finset ((G.contractEdge f (he.leg_mem hG)).RootedTree × Shade)}
    (h𝒯 : (G.contractEdge f (he.leg_mem hG)).IsCollapsingFamily 𝒯)
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1)
    (hW : ∀ p ∈ 𝒯, ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) →
        (G.contractEdge f (he.leg_mem hG)).vertexOf x ∉ p.1.nonRoot)
    {g : H} (hg : g = f ∨ g = G.inv f)
    (hA : ∀ a : (({f, G.inv f} : Set H)ᶜ : Set H), (a : H) ∈ G.vertexOf g →
      a ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯) :
    ∃ 𝒯' : Finset (G.RootedTree × Shade), G.IsCollapsingFamily 𝒯' ∧
      ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯).Isomorphic (G.collapse 𝒯') := by
  have hinv := hG.inv_involutive
  have hne' := he.not_sameCycle
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  -- the two sides
  have hgS : g ∉ (({f, G.inv f} : Set H)ᶜ : Set H) := by
    rcases hg with rfl | rfl <;> simp
  have higS : G.inv g ∉ (({f, G.inv f} : Set H)ᶜ : Set H) := by
    rcases hg with h | h <;> rw [h]
    · simp
    · simp [hinv f]
  have heg : G.IsContractibleEdge g := by
    rcases hg with rfl | rfl
    · exact he
    · exact isContractibleEdge_inv hG he
  have hunion : ∀ x : H, x ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) ↔
      x ∈ G.vertexOf g ∨ x ∈ G.vertexOf (G.inv g) := by
    intro x
    rw [mem_union]
    rcases hg with rfl | rfl
    · rfl
    · rw [hinv f]; exact or_comm
  have hpq : f ∈ (G.vertexOf g : Set H) ∨ G.inv f ∈ (G.vertexOf g : Set H) := by
    rcases hg with rfl | rfl
    · exact Or.inl (G.self_mem_vertexOf _)
    · exact Or.inr (G.self_mem_vertexOf _)
  have hfg : f ∈ ({g, G.inv g} : Set H) ∧ G.inv f ∈ ({g, G.inv g} : Set H) := by
    rcases hg with rfl | rfl
    · simp
    · simp [hinv f]
  -- the merged vertex keeps a free dart, on the side of `ḡ`
  obtain ⟨a₂, ha₂v, ha₂D⟩ : ∃ a : (({f, G.inv f} : Set H)ᶜ : Set H),
      (a : H) ∈ G.vertexOf (G.inv g) ∧ a ∉ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 := by
    obtain ⟨m, hm⟩ := mergedVertex_nonempty hG he
    have hmS : m ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
      mem_compl_pair_iff.2 (mem_mergedVertex.1 hm).2
    have hmU : m ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) := mem_union.2 (mem_mergedVertex.1 hm).1
    obtain ⟨a, haU, haD⟩ : ∃ a : (({f, G.inv f} : Set H)ᶜ : Set H),
        (a : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) ∧
        a ∉ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 := by
      by_cases hr : ∃ p ∈ 𝒯, p.1.root = (G.contractEdge f (he.leg_mem hG)).vertexOf ⟨m, hmS⟩
      · obtain ⟨p, hp, hpr⟩ := hr
        obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root p hp
        refine ⟨a, mem_union_of_mem_contractEdge_vertexOf hG he (hpr ▸ ha) hmU, fun h => ?_⟩
        obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
        exact haq r hr har
      · refine ⟨⟨m, hmS⟩, hmU, fun h => ?_⟩
        obtain ⟨r, hr', hmr⟩ := mem_familyDarts.1 h
        rcases r.1.vertexOf_mem_or_eq_root hGc hmr with h' | h'
        · exact hW r hr' _ hmU h'
        · exact hr ⟨r, hr', h'.symm⟩
    rcases (hunion a).1 haU with h | h
    · exact absurd (hA a h) haD
    · exact ⟨a, h, haD⟩
  -- the trees carried into `G`
  have hemb : ∀ p ∈ 𝒯, p.1.IsEmbedding G Subtype.val := fun p hp =>
    splitOutside_isEmbedding hG he p.1 (hW p hp) fun _ => hbr p hp
  have hA' : Set.InjOn (Subtype.val : (({f, G.inv f} : Set H)ᶜ : Set H) → H) Set.univ :=
    Subtype.val_injective.injOn
  have hDt : ∀ x : H, x ∈ G.familyDarts (transportFamily hGc hG hemb) ↔
      ∃ d ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯, (d : H) = x :=
    fun x => mem_familyDarts_transportFamily hGc hG hemb
  have hnotS : ∀ x : H, x ∉ (({f, G.inv f} : Set H)ᶜ : Set H) →
      x ∉ G.familyDarts (transportFamily hGc hG hemb) := fun x hx h => by
    obtain ⟨d, -, rfl⟩ := (hDt _).1 h
    exact hx d.2
  have hroot : ∀ p ∈ 𝒯, G.IsBoundaryVertex (G.vertexOf (p.1.intervalStart : H)) ↔
      (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex p.1.root := fun p _ => by
    rw [p.1.root_eq_vertexOf_intervalStart, isBoundaryVertex_vertexOf_contractEdge_iff he]
  have h𝒯t := isCollapsingFamily_transportFamily_of_free hGc hG hemb h𝒯 hA'
    (fun _ _ => trivial) hroot (fun p hp => by
      by_cases h₁ : (p.1.intervalStart : H) ∈ G.vertexOf g
      · exact ⟨g, by rw [G.vertexOf_eq_of_mem h₁]; exact G.self_mem_vertexOf g, hnotS g hgS⟩
      by_cases h₂ : (p.1.intervalStart : H) ∈ G.vertexOf (G.inv g)
      · exact ⟨G.inv g, by rw [G.vertexOf_eq_of_mem h₂]; exact G.self_mem_vertexOf _,
          hnotS _ higS⟩
      have hU : (p.1.intervalStart : H) ∉ G.vertexOf f ∪ G.vertexOf (G.inv f) := fun h =>
        ((hunion _).1 h).elim h₁ h₂
      obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root p hp
      refine ⟨a, ?_, fun h => ?_⟩
      · rw [p.1.root_eq_vertexOf_intervalStart] at ha
        have := mem_map_of_mem (Embedding.subtype _) ha
        rwa [map_vertexOf_contractEdge_of_notMem hne' hU] at this
      · obtain ⟨d, hd, hda⟩ := (hDt _).1 h
        obtain ⟨r, hr, hdr⟩ := mem_familyDarts.1 hd
        exact haq r hr (by rwa [← Subtype.ext hda]))
  set 𝒯t := transportFamily hGc hG hemb with h𝒯tdef
  have hbrt : ∀ p ∈ 𝒯t, p.1.intervalLength = 1 := by
    intro p' hp'
    obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hGc hG hemb).1 hp'
    rw [(hemb p hp).tree_intervalLength hGc hG]
    exact hbr p hp
  -- the vertices of the carried trees avoid `g` and `ḡ`
  have hnotW : ∀ q ∈ 𝒯t, ∀ u ∈ q.1.nonRoot, ∀ x : H,
      x ∉ (({f, G.inv f} : Set H)ᶜ : Set H) → x ∉ u := by
    intro q' hq' u hu x hx hxu
    obtain ⟨p, hp, rfl⟩ := (mem_transportFamily hGc hG hemb).1 hq'
    obtain ⟨wc, -, rfl⟩ := mem_image.1 hu
    obtain ⟨y, -, rfl⟩ := mem_image.1 hxu
    exact hx y.2
  have hvgW : ∀ q ∈ 𝒯t, G.vertexOf g ∉ q.1.nonRoot := fun q hq h =>
    hnotW q hq _ h g hgS (G.self_mem_vertexOf g)
  have hwW : ∀ q ∈ 𝒯t, G.vertexOf (G.inv g) ∉ q.1.nonRoot := fun q hq h =>
    hnotW q hq _ h _ higS (G.self_mem_vertexOf _)
  -- each dart of `v(g)` other than `g` is the interval of a carried tree rooted at `v(g)`
  have hthin : ∀ e ∈ G.vertexOf g, e ≠ g → ∃ p ∈ 𝒯t, p.1.root = G.vertexOf g ∧ e ∈ p.1.darts := by
    intro e he' hne
    have he1 : e ≠ g := hne
    have he2 : e ≠ G.inv g := fun h => heg.vertexOf_ne (by
      rw [← G.vertexOf_eq_of_mem he', h])
    have heS : e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := by
      rcases hg with h | h
      · rw [h] at he1 he2; exact mem_compl_pair_iff.2 ⟨he1, he2⟩
      · rw [h, hinv f] at he2; rw [h] at he1; exact mem_compl_pair_iff.2 ⟨he2, he1⟩
    obtain ⟨p, hp, hep⟩ := mem_familyDarts.1 (hA ⟨e, heS⟩ he')
    have heU : e ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) := (hunion e).2 (Or.inl he')
    have hr : (G.contractEdge f (he.leg_mem hG)).vertexOf ⟨e, heS⟩ = p.1.root :=
      (p.1.vertexOf_mem_or_eq_root hGc hep).resolve_left (hW p hp _ heU)
    have ha : (⟨e, heS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) = p.1.intervalStart :=
      p.1.eq_intervalStart_of_intervalLength_eq_one (hbr p hp) hep (p.1.mem_root_iff.2 hr)
    refine ⟨_, (mem_transportFamily hGc hG hemb).2 ⟨p, hp, rfl⟩, ?_, ?_⟩
    · change G.vertexOf ((p.1.intervalStart : _) : H) = _
      rw [← ha]
      exact G.vertexOf_eq_of_mem he'
    · change e ∈ ((hemb p hp).tree hGc hG).darts
      rw [(hemb p hp).tree_darts hGc hG]
      exact mem_image.2 ⟨_, hep, rfl⟩
  have hzD : g ∉ G.familyDarts 𝒯t := hnotS g hgS
  have hint : ¬G.IsBoundaryVertex (G.vertexOf g) := heg.not_isBoundaryVertex
  have hwi : ¬G.IsBoundaryVertex (G.vertexOf (G.inv g)) := heg.not_isBoundaryVertex_inv
  have hw2 : 2 ≤ (G.vertexOf (G.inv g)).card := by
    have hne : (a₂ : H) ≠ G.inv g := fun h => higS (h ▸ a₂.2)
    exact (card_pair hne).symm.le.trans (card_le_card fun x hx => by
      rcases mem_insert.1 hx with rfl | hx
      · exact ha₂v
      · rw [mem_singleton.1 hx]; exact G.self_mem_vertexOf _)
  -- the new tree
  obtain ⟨Tp, hTpc, hTpr, hTpD, hTpW⟩ : ∃ Tp : G.RootedTree,
      Tp.IsCollapsibleOfColour (G.colour g) ∧ Tp.root = G.vertexOf (G.inv g) ∧
      (∀ e, e ∈ Tp.darts ↔ (∃ p ∈ 𝒯t, p.1.root = G.vertexOf g ∧ e ∈ p.1.darts) ∨ e = g ∨
        e = G.inv g) ∧
      (∀ u, u ∈ Tp.nonRoot ↔ u = G.vertexOf g ∨
        ∃ p ∈ 𝒯t, p.1.root = G.vertexOf g ∧ u ∈ p.1.nonRoot) := by
    by_cases hne : ∃ p ∈ 𝒯t, p.1.root = G.vertexOf g
    · set Tv := mergeTree hG h𝒯t hzD hthin hne with hTv
      have hDv := fun e => MergeTree.darts_iff hG h𝒯t hzD hthin hne (e := e)
      have hstart := MergeTree.intervalStart_eq hG h𝒯t hzD hthin hne
      have hz' : G.rot.symm Tv.intervalStart = g := by rw [hstart, Equiv.symm_apply_apply]
      have hthin' : ∀ e ∈ Tv.root, e ∉ Tv.darts → e = G.rot.symm Tv.intervalStart := by
        intro e he' heD
        rw [hz']
        by_contra hez
        obtain ⟨p, hp, hpr, hep⟩ := hthin e he' hez
        exact heD ((hDv e).2 ⟨p, hp, hpr, hep⟩)
      have hint' : ¬G.IsBoundaryVertex Tv.root := hint
      have hw : G.vertexOf (G.inv (G.rot.symm Tv.intervalStart)) ∉ insert Tv.root Tv.nonRoot := by
        rw [hz', mem_insert, not_or]
        refine ⟨fun h => heg.vertexOf_ne h.symm, fun h => ?_⟩
        rw [MergeTree.nonRoot_eq] at h
        obtain ⟨p, hp, hpW⟩ := mem_biUnion.1 h
        exact hwW p (mem_filter.1 hp).1 hpW
      have hwi' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.rot.symm Tv.intervalStart))) := by
        rwa [hz']
      have hw2' : 2 ≤ (G.vertexOf (G.inv (G.rot.symm Tv.intervalStart))).card := by
        rwa [hz']
      have hcv := MergeTree.isCollapsibleOfColour hG h𝒯t hzD hthin hne hbrt hint
      refine ⟨extendInternalTree hG Tv hint' hthin' hw hwi' hw2',
        ExtendInternal.isCollapsibleOfColour hG Tv hint' hthin' hw hwi' hw2' hcv
          (by rw [hz']; exact heg.colour_inv), by rw [ExtendInternal.root_eq, hz'],
        fun e => ?_, fun u => ?_⟩
      · rw [ExtendInternal.darts_iff, hz', hDv]
      · rw [ExtendInternal.nonRoot_eq, mem_insert, MergeTree.nonRoot_eq, MergeTree.root_eq,
          mem_biUnion]
        simp only [mem_filter, and_assoc]
    · push Not at hne
      -- the side of `g` is empty: `v(g)` is a leaf
      have hz1 : G.rot g = g := by
        by_contra h
        obtain ⟨p, hp, hpr, -⟩ := hthin (G.rot g) (G.rot_mem_vertexOf g) h
        exact hne p hp hpr
      refine ⟨leafTree hG hz1 hint hwi hw2, LeafTree.isCollapsibleOfColour hG hz1 hint hwi hw2
        heg.colour_inv, LeafTree.root_eq hG hz1 hint hwi hw2, fun e => ?_, fun u => ?_⟩
      · rw [LeafTree.darts_iff]
        constructor
        · rintro (h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · rintro (⟨p, hp, hpr, -⟩ | h | h)
          · exact absurd hpr (hne p hp)
          · exact Or.inl h
          · exact Or.inr h
      · rw [LeafTree.nonRoot_eq, mem_singleton]
        constructor
        · exact Or.inl
        · rintro (h | ⟨p, hp, hpr, -⟩)
          · exact h
          · exact absurd hpr (hne p hp)
  -- the new family
  set 𝒯o := 𝒯t.filter fun p => p.1.root ≠ G.vertexOf g with h𝒯odef
  have h𝒯o : G.IsCollapsingFamily 𝒯o := h𝒯t.subset (filter_subset _ _)
  have hDo : ∀ e, e ∈ G.familyDarts 𝒯o → e ∈ G.familyDarts 𝒯t := fun e he' => by
    obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 he'
    exact mem_familyDarts.2 ⟨q, (mem_filter.1 hq).1, heq⟩
  have hTpD' : ∀ e, e ∈ Tp.darts → e ∈ G.familyDarts 𝒯t ∨ e = g ∨ e = G.inv g := by
    intro e he'
    rcases (hTpD e).1 he' with ⟨p, hp, -, hep⟩ | h | h
    · exact Or.inl (mem_familyDarts.2 ⟨p, hp, hep⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  -- the free dart `a₂` at `v(ḡ)`
  have ha₂t : (a₂ : H) ∉ G.familyDarts 𝒯t := fun h => by
    obtain ⟨d, hd, hda⟩ := (hDt _).1 h
    exact ha₂D (by rwa [← Subtype.ext hda])
  have ha₂T : (a₂ : H) ∉ Tp.darts := fun h => by
    rcases hTpD' _ h with h' | h' | h'
    · exact ha₂t h'
    · exact hgS (h' ▸ a₂.2)
    · exact higS (h' ▸ a₂.2)
  have h𝒯' : G.IsCollapsingFamily (insert (Tp, G.colour g) 𝒯o) := by
    refine isCollapsingFamily_insert h𝒯o hTpc (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
      (fun q hq => ?_) ⟨a₂, by rw [hTpr]; exact ha₂v, fun h => ha₂t (hDo _ h), ha₂T⟩
    · rw [Finset.disjoint_left]
      intro u hu huq
      rcases (hTpW u).1 hu with rfl | ⟨p, hp, hpr, hup⟩
      · exact hvgW q (mem_filter.1 hq).1 huq
      · have hpq : p ≠ q := fun h => (mem_filter.1 hq).2 (h ▸ hpr)
        exact disjoint_left.1 (h𝒯t.disjoint_nonRoot p hp q (mem_filter.1 hq).1 hpq) hup huq
    · rw [hTpr]; exact hwW q (mem_filter.1 hq).1
    · intro h
      rcases (hTpW _).1 h with h' | ⟨p, hp, hpr, hup⟩
      · exact (mem_filter.1 hq).2 h'
      · have hpq : q ≠ p := fun h => (mem_filter.1 hq).2 (h ▸ hpr)
        exact h𝒯t.root_notMem_nonRoot q (mem_filter.1 hq).1 p hp hpq hup
    · by_cases hqw : q.1.root = G.vertexOf (G.inv g)
      · exact ⟨a₂, by rw [hqw]; exact ha₂v, fun h => ha₂t (hDo _ h), ha₂T⟩
      · obtain ⟨a, ha, haq⟩ := h𝒯t.exists_mem_root q (mem_filter.1 hq).1
        have haD : a ∉ G.familyDarts 𝒯t := fun h => by
          obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
          exact haq r hr har
        refine ⟨a, ha, fun h => haD (hDo _ h), fun h => ?_⟩
        rcases hTpD' _ h with h' | rfl | rfl
        · exact haD h'
        · exact (mem_filter.1 hq).2 (by rw [← q.1.mem_root_iff.1 ha])
        · exact hqw (by rw [← q.1.mem_root_iff.1 ha])
  refine ⟨_, h𝒯', ?_⟩
  -- the darts of the new family
  have hfam : ∀ e, e ∈ G.familyDarts (insert (Tp, G.colour g) 𝒯o) ↔
      e ∈ G.familyDarts 𝒯t ∨ e = g ∨ e = G.inv g := by
    intro e
    constructor
    · intro h
      obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 h
      rcases mem_insert.1 hq with rfl | hq
      · exact hTpD' e heq
      · exact Or.inl (hDo e (mem_familyDarts.2 ⟨q, hq, heq⟩))
    · rintro (h | h | h)
      · obtain ⟨q, hq, heq⟩ := mem_familyDarts.1 h
        by_cases hqr : q.1.root = G.vertexOf g
        · exact mem_familyDarts.2 ⟨_, mem_insert_self _ _, (hTpD e).2 (Or.inl ⟨q, hq, hqr, heq⟩)⟩
        · exact mem_familyDarts.2 ⟨q, mem_insert_of_mem (mem_filter.2 ⟨hq, hqr⟩), heq⟩
      · exact mem_familyDarts.2 ⟨_, mem_insert_self _ _, (hTpD e).2 (Or.inr (Or.inl h))⟩
      · exact mem_familyDarts.2 ⟨_, mem_insert_self _ _, (hTpD e).2 (Or.inr (Or.inr h))⟩
  have hD : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      x ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 ↔
        (x : H) ∈ G.familyDarts (insert (Tp, G.colour g) 𝒯o) := by
    intro x
    rw [hfam, hDt]
    constructor
    · exact fun h => Or.inl ⟨x, h, rfl⟩
    · rintro (⟨d, hd, hdx⟩ | h | h)
      · rwa [← Subtype.ext hdx]
      · exact absurd (h ▸ x.2) hgS
      · exact absurd (h ▸ x.2) higS
  have hfD : f ∈ G.familyDarts (insert (Tp, G.colour g) 𝒯o) := by
    rw [hfam]
    exact Or.inr hfg.1
  have hifD : G.inv f ∈ G.familyDarts (insert (Tp, G.colour g) 𝒯o) := by
    rw [hfam]
    exact Or.inr hfg.2
  have hQ : ∀ x, G.rot x ∈ (G.vertexOf g : Set H) ↔ x ∈ (G.vertexOf g : Set H) := fun x => by
    simp only [mem_coe, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hQK : ∀ x ∈ (G.vertexOf g : Set H), x ∉ G.collapseCore (insert (Tp, G.colour g) 𝒯o) := by
    intro x hx'
    have hxv : G.vertexOf x = G.vertexOf g := G.vertexOf_eq_of_mem (mem_coe.1 hx')
    rintro (h | ⟨i, rfl⟩)
    · apply h
      rw [hfam]
      by_cases hxg : x = g
      · exact Or.inr (Or.inl hxg)
      · obtain ⟨p, hp, -, hxp⟩ := hthin x (mem_coe.1 hx') hxg
        exact Or.inl (mem_familyDarts.2 ⟨p, hp, hxp⟩)
    · apply hint
      rw [← hxv]
      exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hcol : ∀ i, ∀ p₁ ∈ insert (Tp, G.colour g) 𝒯o, ∀ p₂ ∈ 𝒯, G.leg i ∈ p₁.1.darts →
      (G.contractEdge f (he.leg_mem hG)).leg i ∈ p₂.1.darts → p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    rcases mem_insert.1 hp₁ with rfl | hp₁
    · exfalso
      rcases (hTpD _).1 h₁ with ⟨p, hp, hpr, hip⟩ | h | h
      · apply hint
        rw [← hpr, p.1.root_eq_bvertex_of_leg_mem hG hip]
        exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
      · apply hint
        rw [← h]
        exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
      · apply hwi
        rw [← h]
        exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
    · obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hGc hG hemb hA' (fun _ _ => trivial)
        (x := (G.contractEdge f (he.leg_mem hG)).leg i) trivial (mem_filter.1 hp₁).1 h₁
      rw [← hrc, h𝒯.eq_of_mem_darts hGc hr hp₂ hir h₂]
  have hcol₁ : ∀ i, ∀ p₁ ∈ insert (Tp, G.colour g) 𝒯o, ∀ p₂ ∈ insert (Tp, G.colour g) 𝒯o,
      G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts → p₁.2 = p₂.2 :=
    fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯'.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  exact (isomorphic_collapse_of_cut hG (contractEdge_eq_cutData hinv (he.leg_mem hG)) hGc hD
    hfD hifD _ hQ hQK hpq hcol hcol₁)

end SplitRoot

/-! ### Splitting a non-root vertex of a tree -/

section SplitTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)
  (T : (G.contractEdge f (he.leg_mem hG)).RootedTree) (m₀ : (({f, G.inv f} : Set H)ᶜ : Set H))
  (hm₀ : (m₀ : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f))
  (hMW : (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ ∈ T.nonRoot)

include hG he hm₀ hMW

namespace SplitTree

omit hMW in
/-- The merged vertex is the vertex of the darts at the endpoints. -/
private theorem vertexOf_eq_iff (x : (({f, G.inv f} : Set H)ᶜ : Set H)) :
    (G.contractEdge f (he.leg_mem hG)).vertexOf x = (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ ↔
      (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) := by
  constructor
  · intro h
    exact mem_union_of_mem_contractEdge_vertexOf hG he (by
      rw [← h]; exact (G.contractEdge f (he.leg_mem hG)).self_mem_vertexOf x) hm₀
  · intro h
    apply map_injective (Embedding.subtype (· ∈ (({f, G.inv f} : Set H)ᶜ : Set H)))
    rw [map_vertexOf_contractEdge_of_mem he.not_sameCycle h,
      map_vertexOf_contractEdge_of_mem he.not_sameCycle hm₀]

omit hMW in
/-- A vertex of the contraction other than the merged vertex, read in `H`, is a vertex of `G`. -/
private theorem map_eq_vertexOf {u : Finset (({f, G.inv f} : Set H)ᶜ : Set H)}
    (hu : u ∈ (G.contractEdge f (he.leg_mem hG)).vertices)
    (huM : u ≠ (G.contractEdge f (he.leg_mem hG)).vertexOf m₀) :
    ∃ x : (({f, G.inv f} : Set H)ᶜ : Set H), (x : H) ∉ G.vertexOf f ∪ G.vertexOf (G.inv f) ∧
      u = (G.contractEdge f (he.leg_mem hG)).vertexOf x ∧
      u.map (Embedding.subtype _) = G.vertexOf x := by
  obtain ⟨x, rfl⟩ := (G.contractEdge f (he.leg_mem hG)).mem_vertices.1 hu
  have hx : (x : H) ∉ G.vertexOf f ∪ G.vertexOf (G.inv f) := fun h =>
    huM ((vertexOf_eq_iff hG he m₀ hm₀ x).2 h)
  exact ⟨x, hx, rfl, map_vertexOf_contractEdge_of_notMem he.not_sameCycle hx⟩

omit hm₀ hMW in
/-- The non-root vertices of the split tree. -/
private noncomputable abbrev nonRoot' : Finset (Finset H) :=
  insert (G.vertexOf f) (insert (G.vertexOf (G.inv f))
    ((T.nonRoot.erase ((G.contractEdge f (he.leg_mem hG)).vertexOf m₀)).image
      (Finset.map (Embedding.subtype (· ∈ (({f, G.inv f} : Set H)ᶜ : Set H))))))

private theorem mem_nonRoot'_iff (x : (({f, G.inv f} : Set H)ᶜ : Set H)) :
    G.vertexOf x ∈ nonRoot' hG he T m₀ ↔
      (G.contractEdge f (he.leg_mem hG)).vertexOf x ∈ T.nonRoot := by
  rw [nonRoot', mem_insert, mem_insert, mem_image]
  by_cases hxU : (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)
  · rw [(vertexOf_eq_iff hG he m₀ hm₀ x).2 hxU]
    refine iff_of_true ?_ hMW
    rcases mem_union.1 hxU with h | h
    · exact Or.inl (G.vertexOf_eq_of_mem h)
    · exact Or.inr (Or.inl (G.vertexOf_eq_of_mem h))
  · have hxM : (G.contractEdge f (he.leg_mem hG)).vertexOf x ≠
        (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ := fun h =>
      hxU ((vertexOf_eq_iff hG he m₀ hm₀ x).1 h)
    constructor
    · rintro (h | h | ⟨u, hu, hux⟩)
      · exact absurd (mem_union_left _ (h ▸ G.self_mem_vertexOf (x : H))) hxU
      · exact absurd (mem_union_right _ (h ▸ G.self_mem_vertexOf (x : H))) hxU
      · obtain ⟨huM, huW⟩ := mem_erase.1 hu
        obtain ⟨y, -, rfl, hmap⟩ := map_eq_vertexOf hG he m₀ hm₀
          (((G.contractEdge f (he.leg_mem hG)).mem_internalVertices.1 (T.nonRoot_subset huW)).1) huM
        rw [hmap] at hux
        have : (x : H) ∈ G.vertexOf y := by rw [hux]; exact G.self_mem_vertexOf _
        have hxy : x ∈ (G.contractEdge f (he.leg_mem hG)).vertexOf y := by
          rw [← mem_map' (Embedding.subtype _), map_vertexOf_contractEdge_of_notMem
            he.not_sameCycle (fun h => hxU (by
              rcases mem_union.1 h with h' | h'
              · exact mem_union_left _ (by
                  rw [← G.vertexOf_eq_of_mem h', ← G.vertexOf_eq_of_mem this]
                  exact G.self_mem_vertexOf _)
              · exact mem_union_right _ (by
                  rw [← G.vertexOf_eq_of_mem h', ← G.vertexOf_eq_of_mem this]
                  exact G.self_mem_vertexOf _)))]
          exact this
        rwa [(G.contractEdge f (he.leg_mem hG)).vertexOf_eq_of_mem hxy]
    · exact fun h => Or.inr (Or.inr ⟨_, mem_erase.2 ⟨hxM, h⟩,
        map_vertexOf_contractEdge_of_notMem he.not_sameCycle hxU⟩)

private theorem mem_treeDarts_iff {e : H} :
    e ∈ G.treeDarts (nonRoot' hG he T m₀) ↔
      e = f ∨ e = G.inv f ∨ ∃ h : e ∈ (({f, G.inv f} : Set H)ᶜ : Set H), ⟨e, h⟩ ∈ T.darts := by
  have hinv := hG.inv_involutive
  by_cases heS : e ∈ (({f, G.inv f} : Set H)ᶜ : Set H)
  · have hne := mem_compl_pair_iff.1 heS
    have hieS : G.inv e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
      (apply_mem_compl_pair_iff hinv f e).2 heS
    have hcinv : (G.contractEdge f (he.leg_mem hG)).inv ⟨e, heS⟩ = ⟨G.inv e, hieS⟩ :=
      Subtype.ext (coe_contractEdge_inv hinv _)
    simp only [hne.1, hne.2, false_or, exists_prop_of_true heS]
    rw [mem_treeDarts, mem_treeDarts, mem_contractEdge_bdry, hcinv]
    rw [show G.vertexOf e =
        G.vertexOf ((⟨e, heS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) : H) from rfl,
      mem_nonRoot'_iff hG he T m₀ hm₀ hMW,
      show G.vertexOf (G.inv e) =
        G.vertexOf ((⟨G.inv e, hieS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) :
        H) from rfl, mem_nonRoot'_iff hG he T m₀ hm₀ hMW]
  · have hef : e = f ∨ e = G.inv f := by
      by_contra h
      exact heS (mem_compl_pair_iff.2 (not_or.1 h))
    refine iff_of_true ?_ (hef.elim Or.inl (fun h => Or.inr (Or.inl h)))
    rw [mem_treeDarts, nonRoot', mem_insert, mem_insert]
    rcases hef with rfl | rfl
    · exact ⟨fun hB => he.not_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem hB),
        Or.inl (Or.inl rfl)⟩
    · exact ⟨fun hB => he.not_isBoundaryVertex_inv (G.isBoundaryVertex_vertexOf_of_mem hB),
        Or.inl (Or.inr (Or.inl rfl))⟩

end SplitTree

/-- **The tree with a non-root vertex split**: for a tree `T` of the contraction along `{f, f̄}`
whose non-root vertices contain the merged vertex, the rooted tree of `G` with the same root and
the merged vertex replaced by the two endpoints `v(f)` and `v(f̄)`. -/
private noncomputable def splitTree : G.RootedTree :=
  have hinv := hG.inv_involutive
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  have hD := fun e => SplitTree.mem_treeDarts_iff hG he T m₀ hm₀ hMW (e := e)
  have hW := SplitTree.mem_nonRoot'_iff hG he T m₀ hm₀ hMW
  have hM := SplitTree.vertexOf_eq_iff hG he m₀ hm₀
  have hrM : T.root ≠ (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ := fun h =>
    T.root_notMem_nonRoot (h ▸ hMW)
  have ha₁U : (T.intervalStart : H) ∉ G.vertexOf f ∪ G.vertexOf (G.inv f) := fun h =>
    hrM (by rw [T.root_eq_vertexOf_intervalStart]; exact (hM _).2 h)
  have hmap₁ : T.root.map (Embedding.subtype _) = G.vertexOf (T.intervalStart : H) := by
    rw [T.root_eq_vertexOf_intervalStart]
    exact map_vertexOf_contractEdge_of_notMem he.not_sameCycle ha₁U
  -- the darts at the root
  have hrootS : ∀ d ∈ G.vertexOf (T.intervalStart : H), d ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
    fun d hd => by
      rw [← hmap₁] at hd
      obtain ⟨x, -, rfl⟩ := mem_map.1 hd
      exact x.2
  have hroot_iff : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      (x : H) ∈ G.vertexOf (T.intervalStart : H) ↔
      x ∈ T.root := fun x => by
    rw [← hmap₁]
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := mem_map.1 h
      rwa [← Subtype.ext hyx]
    · intro h
      exact mem_map_of_mem _ h
  have hrotS : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H), x ∈ T.root →
      G.rot x ∈ (({f, G.inv f} : Set H)ᶜ : Set H) := fun x hx =>
    hrootS _ (by
      rw [G.mem_vertexOf]
      have := (hroot_iff x).2 hx
      rw [G.mem_vertexOf] at this
      exact this.trans (Perm.SameCycle.refl _ _ |>.trans ⟨1, by rw [zpow_one]⟩))
  have hrot : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H), x ∈ T.root →
      (((G.contractEdge f (he.leg_mem hG)).rot x : (({f, G.inv f} : Set H)ᶜ : Set H)) : H) =
        G.rot x := fun x hx => coe_contractEdge_rot_of_mem (hrotS x hx)
  have hpow : ∀ (n : ℕ) (x : (({f, G.inv f} : Set H)ᶜ : Set H)), x ∈ T.root →
      ((((G.contractEdge f (he.leg_mem hG)).rot ^ n) x : (({f, G.inv f} : Set H)ᶜ : Set H)) : H) =
        (G.rot ^ n) x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      have hn : ((G.contractEdge f (he.leg_mem hG)).rot ^ n) x ∈ T.root := by
        rw [T.mem_root_iff, (G.contractEdge f (he.leg_mem hG)).vertexOf_pow_apply,
          T.mem_root_iff.1 hx]
      rw [pow_succ', Perm.mul_apply, hrot _ hn, ih x hx, pow_succ', Perm.mul_apply]
  have hfD : f ∈ G.treeDarts (SplitTree.nonRoot' hG he T m₀) := (hD f).2 (Or.inl rfl)
  have hifD : G.inv f ∈ G.treeDarts (SplitTree.nonRoot' hG he T m₀) :=
    (hD _).2 (Or.inr (Or.inl rfl))
  have hadj₁ : G.TreeAdj (SplitTree.nonRoot' hG he T m₀) (G.vertexOf f) (G.vertexOf (G.inv f)) :=
    ⟨f, hfD, rfl, rfl⟩
  have hadj₂ : G.TreeAdj (SplitTree.nonRoot' hG he T m₀) (G.vertexOf (G.inv f)) (G.vertexOf f) :=
    ⟨G.inv f, hifD, rfl, by rw [hinv]⟩
  { root := G.vertexOf (T.intervalStart : H)
    nonRoot := SplitTree.nonRoot' hG he T m₀
    root_mem_vertices := G.vertexOf_mem_vertices _
    nonRoot_nonempty := ⟨_, mem_insert_self _ _⟩
    nonRoot_subset := by
      intro w hw
      rw [mem_insert, mem_insert] at hw
      rcases hw with rfl | rfl | hw
      · exact he.mem_internalVertices
      · exact he.inv_mem_internalVertices
      · obtain ⟨u, hu, rfl⟩ := mem_image.1 hw
        obtain ⟨huM, huW⟩ := mem_erase.1 hu
        have hu₀ := (G.contractEdge f (he.leg_mem hG)).mem_internalVertices.1 (T.nonRoot_subset huW)
        obtain ⟨x, -, rfl, hmap⟩ := SplitTree.map_eq_vertexOf hG he m₀ hm₀ hu₀.1 huM
        rw [hmap]
        refine G.vertexOf_mem_internalVertices.2 ?_
        rw [← isBoundaryVertex_vertexOf_contractEdge_iff he]
        exact hu₀.2
    root_notMem_nonRoot := by
      intro h
      rw [show G.vertexOf (T.intervalStart : H) =
        G.vertexOf ((T.intervalStart : (({f, G.inv f} : Set H)ᶜ : Set H)) : H) from rfl, hW,
        ← T.root_eq_vertexOf_intervalStart] at h
      exact T.root_notMem_nonRoot h
    vertexOf_inv_mem := by
      intro e he'
      have heD : e ∈ G.treeDarts (SplitTree.nonRoot' hG he T m₀) := by
        refine G.mem_treeDarts.2 ⟨fun hB => ?_, Or.inl he'⟩
        rw [mem_insert, mem_insert] at he'
        rcases he' with h | h | h
        · exact he.not_isBoundaryVertex (h ▸ G.isBoundaryVertex_vertexOf_of_mem hB)
        · exact he.not_isBoundaryVertex_inv (h ▸ G.isBoundaryVertex_vertexOf_of_mem hB)
        · obtain ⟨u, hu, hue⟩ := mem_image.1 h
          obtain ⟨huM, huW⟩ := mem_erase.1 hu
          have hu₀ := (G.contractEdge f (he.leg_mem hG)).mem_internalVertices.1
            (T.nonRoot_subset huW)
          obtain ⟨x, -, rfl, hmap⟩ := SplitTree.map_eq_vertexOf hG he m₀ hm₀ hu₀.1 huM
          apply hu₀.2
          rw [isBoundaryVertex_vertexOf_contractEdge_iff he, ← hmap, hue]
          exact G.isBoundaryVertex_vertexOf_of_mem hB
      rcases (hD e).1 heD with rfl | rfl | ⟨heS, heT⟩
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))
      · rw [hinv]; exact mem_insert_of_mem (mem_insert_self _ _)
      · have hieS : G.inv e ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
          (apply_mem_compl_pair_iff hinv f e).2 heS
        have hcinv : (G.contractEdge f (he.leg_mem hG)).inv ⟨e, heS⟩ = ⟨G.inv e, hieS⟩ :=
          Subtype.ext (coe_contractEdge_inv hinv _)
        have hiT : (⟨G.inv e, hieS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) ∈ T.darts :=
          hcinv ▸ T.inv_mem_darts hGc heT
        rcases T.vertexOf_mem_or_eq_root hGc hiT with h | h
        · exact mem_insert_of_mem ((hW ⟨G.inv e, hieS⟩).2 h)
        · rw [show G.vertexOf (G.inv e) = G.vertexOf (T.intervalStart : H) from
            G.vertexOf_eq_of_mem ((hroot_iff ⟨G.inv e, hieS⟩).2 (T.mem_root_iff.2 h))]
          exact mem_insert_self _ _
    exists_interval := by
      refine ⟨T.intervalStart, G.self_mem_vertexOf _, T.intervalLength, T.one_le_intervalLength,
        ?_, fun d hd => ?_, ?_⟩
      · rw [← hmap₁, card_map]; exact T.intervalLength_lt_card
      · have hdS := hrootS d hd
        have hdr : (⟨d, hdS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) ∈ T.root := (hroot_iff _).1 hd
        rw [hD]
        have hne := mem_compl_pair_iff.1 hdS
        simp only [hne.1, hne.2, false_or, exists_prop_of_true hdS]
        rw [T.mem_darts_iff_of_mem_root hdr]
        refine exists_congr fun j => and_congr Iff.rfl ?_
        rw [Subtype.ext_iff, hpow j _ T.intervalStart_mem_root]
      · have hσS : G.rot.symm (T.intervalStart : H) ∈ (({f, G.inv f} : Set H)ᶜ : Set H) :=
          hrootS _ (G.rot_symm_mem_vertexOf _)
        have hσr : (⟨G.rot.symm T.intervalStart, hσS⟩ : (({f, G.inv f} : Set H)ᶜ : Set H)) ∈
            T.root := (hroot_iff _).1 (G.rot_symm_mem_vertexOf _)
        have hσ : (G.contractEdge f (he.leg_mem hG)).rot ⟨G.rot.symm T.intervalStart, hσS⟩ =
            T.intervalStart := Subtype.ext (by rw [hrot _ hσr]; exact Equiv.apply_symm_apply _ _)
        rw [hD]
        have hne := mem_compl_pair_iff.1 hσS
        simp only [hne.1, hne.2, false_or, exists_prop_of_true hσS]
        rw [← Equiv.symm_apply_apply (G.contractEdge f (he.leg_mem hG)).rot
          ⟨G.rot.symm T.intervalStart, hσS⟩, hσ]
        exact T.rot_symm_intervalStart_notMem
    card_image_edgeOf := by
      have hD' : G.treeDarts (SplitTree.nonRoot' hG he T m₀) =
          insert f (insert (G.inv f) (T.darts.map (Embedding.subtype _))) := by
        ext e
        rw [hD, mem_insert, mem_insert, mem_map]
        constructor
        · rintro (h | h | ⟨heS, heT⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨_, heT, rfl⟩)
        · rintro (h | h | ⟨x, hx, rfl⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨x.2, hx⟩)
      have hfm : f ∉ T.darts.map (Embedding.subtype _) := fun h => by
        obtain ⟨x, -, hx⟩ := mem_map.1 h
        exact (mem_compl_pair_iff.1 x.2).1 hx
      have hifm : G.inv f ∉ T.darts.map (Embedding.subtype _) := fun h => by
        obtain ⟨x, -, hx⟩ := mem_map.1 h
        exact (mem_compl_pair_iff.1 x.2).2 hx
      have h2 := G.card_eq_two_mul_card_image_edgeOf hinv hG.inv_ne
        (S := G.treeDarts (SplitTree.nonRoot' hG he T m₀)) fun e he' => inv_mem_treeDarts' hG he'
      rw [hD', card_insert_of_notMem (by
          rw [mem_insert, not_or]; exact ⟨(hG.inv_ne f).symm, hfm⟩),
        card_insert_of_notMem hifm, card_map, T.card_darts hGc] at h2
      -- the vertices
      have hy1 : G.vertexOf f ∉ insert (G.vertexOf (G.inv f))
          ((T.nonRoot.erase ((G.contractEdge f (he.leg_mem hG)).vertexOf m₀)).image
            (Finset.map (Embedding.subtype (· ∈ (({f, G.inv f} : Set H)ᶜ : Set H))))) := by
        rw [mem_insert, not_or]
        refine ⟨he.vertexOf_ne, fun h => ?_⟩
        obtain ⟨u, -, hu⟩ := mem_image.1 h
        have : f ∈ u.map (Embedding.subtype _) := hu ▸ G.self_mem_vertexOf f
        obtain ⟨x, -, hx⟩ := mem_map.1 this
        exact (mem_compl_pair_iff.1 x.2).1 hx
      have hy2 : G.vertexOf (G.inv f) ∉
          ((T.nonRoot.erase ((G.contractEdge f (he.leg_mem hG)).vertexOf m₀)).image
            (Finset.map (Embedding.subtype (· ∈ (({f, G.inv f} : Set H)ᶜ : Set H))))) := by
        intro h
        obtain ⟨u, -, hu⟩ := mem_image.1 h
        have : G.inv f ∈ u.map (Embedding.subtype _) := hu ▸ G.self_mem_vertexOf _
        obtain ⟨x, -, hx⟩ := mem_map.1 this
        exact (mem_compl_pair_iff.1 x.2).2 hx
      have hcardW : (SplitTree.nonRoot' hG he T m₀).card = T.nonRoot.card + 1 := by
        rw [SplitTree.nonRoot', card_insert_of_notMem hy1, card_insert_of_notMem hy2,
          card_image_of_injective _ (map_injective _), card_erase_of_mem hMW]
        have : 1 ≤ T.nonRoot.card := card_pos.2 ⟨_, hMW⟩
        omega
      rw [hD', hcardW]
      omega
    reflTransGen_treeAdj := by
      set W' := SplitTree.nonRoot' hG he T m₀
      let φ : Finset (({f, G.inv f} : Set H)ᶜ : Set H) → Finset H := fun u =>
        if u = (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ then G.vertexOf f
        else u.map (Embedding.subtype _)
      have hφ₁ : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H), Relation.ReflTransGen (G.TreeAdj W')
          (φ ((G.contractEdge f (he.leg_mem hG)).vertexOf x)) (G.vertexOf x) := by
        intro x
        by_cases hxU : (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)
        · have : φ ((G.contractEdge f (he.leg_mem hG)).vertexOf x) = G.vertexOf f :=
            if_pos ((hM x).2 hxU)
          rw [this]
          rcases mem_union.1 hxU with h | h
          · rw [G.vertexOf_eq_of_mem h]
          · rw [G.vertexOf_eq_of_mem h]; exact .single hadj₁
        · have : φ ((G.contractEdge f (he.leg_mem hG)).vertexOf x) = G.vertexOf x := by
            change (if _ then _ else _) = _
            rw [if_neg (mt (hM x).1 hxU), map_vertexOf_contractEdge_of_notMem he.not_sameCycle hxU]
          rw [this]
      have hφ₂ : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H), Relation.ReflTransGen (G.TreeAdj W')
          (G.vertexOf x) (φ ((G.contractEdge f (he.leg_mem hG)).vertexOf x)) := by
        intro x
        by_cases hxU : (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f)
        · have : φ ((G.contractEdge f (he.leg_mem hG)).vertexOf x) = G.vertexOf f :=
            if_pos ((hM x).2 hxU)
          rw [this]
          rcases mem_union.1 hxU with h | h
          · rw [G.vertexOf_eq_of_mem h]
          · rw [G.vertexOf_eq_of_mem h]; exact .single hadj₂
        · have : φ ((G.contractEdge f (he.leg_mem hG)).vertexOf x) = G.vertexOf x := by
            change (if _ then _ else _) = _
            rw [if_neg (mt (hM x).1 hxU), map_vertexOf_contractEdge_of_notMem he.not_sameCycle hxU]
          rw [this]
      have hstep : ∀ u u₂, (G.contractEdge f (he.leg_mem hG)).TreeAdj T.nonRoot u u₂ →
          Relation.ReflTransGen (G.TreeAdj W') (φ u) (φ u₂) := by
        rintro _ _ ⟨x, hx, rfl, rfl⟩
        have hxD : (x : H) ∈ G.treeDarts W' := (hD _).2 (Or.inr (Or.inr ⟨x.2, hx⟩))
        refine (hφ₁ x).trans (Relation.ReflTransGen.head ⟨x, hxD, rfl, ?_⟩ (hφ₂ _))
        rw [coe_contractEdge_inv hinv]
      have hφr : φ T.root = G.vertexOf (T.intervalStart : H) := by
        change (if _ then _ else _) = _
        rw [if_neg hrM, hmap₁]
      intro u hu
      rw [mem_insert] at hu
      rcases hu with rfl | hu
      · exact .refl
      have hlift : ∀ w, w ∈ insert T.root T.nonRoot →
          Relation.ReflTransGen (G.TreeAdj W') (G.vertexOf (T.intervalStart : H)) (φ w) :=
        fun w hw => hφr ▸ Relation.ReflTransGen.lift' φ hstep (T.reflTransGen_treeAdj w hw)
      have hy1 : Relation.ReflTransGen (G.TreeAdj W') (G.vertexOf (T.intervalStart : H))
          (G.vertexOf f) := by
        have := hlift _ (mem_insert_of_mem hMW)
        change Relation.ReflTransGen _ _ (if _ then _ else _) at this
        rwa [if_pos rfl] at this
      rcases mem_insert.1 hu with rfl | hu
      · exact hy1
      rcases mem_insert.1 hu with rfl | hu
      · exact hy1.tail hadj₁
      · obtain ⟨w, hw, rfl⟩ := mem_image.1 hu
        obtain ⟨hwM, hwW⟩ := mem_erase.1 hw
        have := hlift w (mem_insert_of_mem hwW)
        change Relation.ReflTransGen _ _ (if _ then _ else _) at this
        rwa [if_neg hwM] at this }

namespace SplitTree

private theorem darts_iff {e : H} : e ∈ (splitTree hG he T m₀ hm₀ hMW).darts ↔
    e = f ∨ e = G.inv f ∨ ∃ h : e ∈ (({f, G.inv f} : Set H)ᶜ : Set H), ⟨e, h⟩ ∈ T.darts :=
  mem_treeDarts_iff hG he T m₀ hm₀ hMW

private theorem root_eq :
    (splitTree hG he T m₀ hm₀ hMW).root = G.vertexOf (T.intervalStart : H) := rfl

private theorem vertexOf_mem_nonRoot : G.vertexOf f ∈ (splitTree hG he T m₀ hm₀ hMW).nonRoot :=
  mem_insert_self _ _

private theorem vertexOf_inv_mem_nonRoot :
    G.vertexOf (G.inv f) ∈ (splitTree hG he T m₀ hm₀ hMW).nonRoot :=
  mem_insert_of_mem (mem_insert_self _ _)

private theorem isBoundaryVertex_root_iff :
    G.IsBoundaryVertex (splitTree hG he T m₀ hm₀ hMW).root ↔
      (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex T.root := by
  rw [root_eq, T.root_eq_vertexOf_intervalStart, isBoundaryVertex_vertexOf_contractEdge_iff he]

private theorem darts_eq : (splitTree hG he T m₀ hm₀ hMW).darts =
    insert f (insert (G.inv f) (T.darts.map (Embedding.subtype _))) := by
  ext e
  rw [darts_iff, mem_insert, mem_insert, mem_map]
  constructor
  · rintro (h | h | ⟨heS, heT⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨_, heT, rfl⟩)
  · rintro (h | h | ⟨x, hx, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x.2, hx⟩)

private theorem card_nonRoot :
    (splitTree hG he T m₀ hm₀ hMW).nonRoot.card = T.nonRoot.card + 1 := by
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  have h1 := (splitTree hG he T m₀ hm₀ hMW).card_darts hG
  have h2 := T.card_darts hGc
  have hfm : f ∉ T.darts.map (Embedding.subtype _) := fun h => by
    obtain ⟨x, -, hx⟩ := mem_map.1 h
    exact (mem_compl_pair_iff.1 x.2).1 hx
  have hifm : G.inv f ∉ T.darts.map (Embedding.subtype _) := fun h => by
    obtain ⟨x, -, hx⟩ := mem_map.1 h
    exact (mem_compl_pair_iff.1 x.2).2 hx
  rw [darts_eq, card_insert_of_notMem (by
      rw [mem_insert, not_or]; exact ⟨(hG.inv_ne f).symm, hfm⟩),
    card_insert_of_notMem hifm, card_map] at h1
  omega

/-- Contracting the split tree gives back `T`. -/
private theorem contractTree_eq :
    contractTree hG he (splitTree hG he T m₀ hm₀ hMW) (vertexOf_mem_nonRoot hG he T m₀ hm₀ hMW)
      (vertexOf_inv_mem_nonRoot hG he T m₀ hm₀ hMW) = T := by
  have hrM : T.root ≠ (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ := fun h =>
    T.root_notMem_nonRoot (h ▸ hMW)
  have hcM : ∀ w : Finset H, (f ∈ w ∨ G.inv f ∈ w) →
      contractV f G w = (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ := fun w hw => by
    rw [contractEdge_vertexOf_eq hG he, contractV, contractV, if_pos hw,
      if_pos ((contractV_cond_iff _).2 hm₀)]
  refine RootedTree.ext' ?_ ?_
  · change contractV f G (G.vertexOf (T.intervalStart : H)) = T.root
    rw [← contractEdge_vertexOf_eq hG he, ← T.root_eq_vertexOf_intervalStart]
  · change (nonRoot' hG he T m₀).image (contractV f G) = T.nonRoot
    ext u
    rw [mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases mem_insert.1 hw with rfl | hw
      · rwa [hcM _ (Or.inl (G.self_mem_vertexOf f))]
      rcases mem_insert.1 hw with rfl | hw
      · rwa [hcM _ (Or.inr (G.self_mem_vertexOf _))]
      obtain ⟨u', hu', rfl⟩ := mem_image.1 hw
      obtain ⟨huM, huW⟩ := mem_erase.1 hu'
      obtain ⟨x, -, rfl, hmap⟩ := map_eq_vertexOf hG he m₀ hm₀
        ((G.contractEdge f (he.leg_mem hG)).mem_internalVertices.1 (T.nonRoot_subset huW)).1 huM
      rw [hmap, ← contractEdge_vertexOf_eq hG he]
      exact huW
    · intro hu
      by_cases huM : u = (G.contractEdge f (he.leg_mem hG)).vertexOf m₀
      · exact ⟨G.vertexOf f, mem_insert_self _ _, by
          rw [huM]; exact hcM _ (Or.inl (G.self_mem_vertexOf f))⟩
      · obtain ⟨x, -, rfl, hmap⟩ := map_eq_vertexOf hG he m₀ hm₀
          ((G.contractEdge f (he.leg_mem hG)).mem_internalVertices.1 (T.nonRoot_subset hu)).1 huM
        exact ⟨_, mem_insert_of_mem (mem_insert_of_mem (mem_image.2
          ⟨_, mem_erase.2 ⟨huM, hu⟩, rfl⟩)), by rw [hmap, ← contractEdge_vertexOf_eq hG he]⟩

/-- The split tree is collapsible of the colour of `T`. -/
private theorem isCollapsibleOfColour {c : Shade} (hT : T.IsCollapsibleOfColour c) :
    (splitTree hG he T m₀ hm₀ hMW).IsCollapsibleOfColour c := by
  set T' := splitTree hG he T m₀ hm₀ hMW
  have hy := vertexOf_mem_nonRoot hG he T m₀ hm₀ hMW
  have hz := vertexOf_inv_mem_nonRoot hG he T m₀ hm₀ hMW
  have hiso := ContractTree.plabicData_isomorphic hG he T' hy hz
  rw [contractTree_eq] at hiso
  have hloc : PlabicGraph.IsLocalMove .m3 ⟨_, T'.plabicData, T'.isPlabicGraph_plabicData hG⟩
      ⟨_, T.plabicData, hT.isPlabicGraph⟩ :=
    Or.inl ⟨ContractTree.dartF T' hy, ContractTree.isContractibleEdge_dartF hG he T' hy hz, hiso⟩
  have hbv := isBoundaryVertex_root_iff hG he T m₀ hm₀ hMW
  refine ⟨T'.isPlabicGraph_plabicData hG,
    (PlabicGraph.MoveEquivalent.of_isLocalMove (by simp) hloc).trans hT.moveEquivalent, ?_⟩
  rcases hT.root_cases with ⟨hb, hcol⟩ | ⟨hb, h2⟩
  · refine Or.inl ⟨mt hbv.1 hb, fun e he' => ?_⟩
    have hb' : ¬G.IsBoundaryVertex (G.vertexOf (T.intervalStart : H)) := mt hbv.1 hb
    rw [root_eq] at he'
    rw [hG.colour_eq_of_mem_vertexOf hb' he']
    exact hcol _ T.intervalStart_mem_root
  · refine Or.inr ⟨hbv.2 hb, ?_⟩
    rw [card_nonRoot]
    omega

end SplitTree

end SplitTree


/-! ### Splitting a non-root vertex of a tree, in a family -/

section SplitInside

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {f : H} (he : G.IsContractibleEdge f)
  {𝒯 : Finset ((G.contractEdge f (he.leg_mem hG)).RootedTree × Shade)}
  (h𝒯 : (G.contractEdge f (he.leg_mem hG)).IsCollapsingFamily 𝒯)
  {p₀ : (G.contractEdge f (he.leg_mem hG)).RootedTree × Shade} (hp₀ : p₀ ∈ 𝒯)
  (m₀ : (({f, G.inv f} : Set H)ᶜ : Set H))
  (hm₀ : (m₀ : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f))
  (hMW : (G.contractEdge f (he.leg_mem hG)).vertexOf m₀ ∈ p₀.1.nonRoot)

include hG he h𝒯 hp₀ hm₀ hMW

open scoped Classical in
/-- **Splitting a non-root vertex of a tree**: the tree with the vertex split replaces the tree,
and the collapse does not change. -/
theorem exists_collapse_split_inside :
    ∃ 𝒯' : Finset (G.RootedTree × Shade), G.IsCollapsingFamily 𝒯' ∧
      ((G.contractEdge f (he.leg_mem hG)).collapse 𝒯).Isomorphic (G.collapse 𝒯') := by
  have hinv := hG.inv_involutive
  have hGc : (G.contractEdge f (he.leg_mem hG)).IsPlabicGraph := hG.contractEdge he
  set T₀ := p₀.1 with hT₀
  set T' := splitTree hG he T₀ m₀ hm₀ hMW with hT'
  have hD' := fun e => SplitTree.darts_iff hG he T₀ m₀ hm₀ hMW (e := e)
  have hM := SplitTree.vertexOf_eq_iff hG he m₀ hm₀
  have hothers : ∀ q ∈ 𝒯.erase p₀, ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      (x : H) ∈ G.vertexOf f ∪ G.vertexOf (G.inv f) →
        (G.contractEdge f (he.leg_mem hG)).vertexOf x ∉ q.1.nonRoot := by
    intro q hq x hx h
    rw [(hM x).2 hx] at h
    exact disjoint_left.1 (h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq)
      (ne_of_mem_erase hq).symm) hMW h
  have hrootM : ∀ q ∈ 𝒯.erase p₀, (q.1.intervalStart : H) ∉ G.vertexOf f ∪ G.vertexOf (G.inv f) :=
    fun q hq h => by
      apply h𝒯.root_notMem_nonRoot q (mem_of_mem_erase hq) p₀ hp₀ (ne_of_mem_erase hq)
      rw [q.1.root_eq_vertexOf_intervalStart, (hM _).2 h]
      exact hMW
  have hemb : ∀ q ∈ 𝒯.erase p₀, q.1.IsEmbedding G Subtype.val := fun q hq =>
    splitOutside_isEmbedding hG he q.1 (hothers q hq) fun h => absurd h (hrootM q hq)
  have hA : Set.InjOn (Subtype.val : (({f, G.inv f} : Set H)ᶜ : Set H) → H) Set.univ :=
    Subtype.val_injective.injOn
  have hdisj : ∀ q ∈ 𝒯.erase p₀, Disjoint T₀.darts q.1.darts := fun q hq =>
    T₀.disjoint_darts hGc (h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq)
      (ne_of_mem_erase hq).symm)
      (h𝒯.root_notMem_nonRoot q (mem_of_mem_erase hq) p₀ hp₀ (ne_of_mem_erase hq))
  have hroot : ∀ q ∈ 𝒯.erase p₀, G.IsBoundaryVertex (G.vertexOf (q.1.intervalStart : H)) ↔
      (G.contractEdge f (he.leg_mem hG)).IsBoundaryVertex q.1.root := fun q _ => by
    rw [q.1.root_eq_vertexOf_intervalStart, isBoundaryVertex_vertexOf_contractEdge_iff he]
  -- a free dart at a root other than the merged vertex
  have hfreeD : ∀ q ∈ 𝒯, ∃ a ∈ q.1.root, a ∉ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 :=
    fun q hq => by
      obtain ⟨a, ha, haq⟩ := h𝒯.exists_mem_root q hq
      exact ⟨a, ha, fun h => by
        obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
        exact haq r hr har⟩
  have hmapr : ∀ q ∈ 𝒯, (q.1.intervalStart : H) ∉ G.vertexOf f ∪ G.vertexOf (G.inv f) →
      ∀ a ∈ q.1.root, (a : H) ∈ G.vertexOf (q.1.intervalStart : H) := by
    intro q _ hU a ha
    rw [q.1.root_eq_vertexOf_intervalStart] at ha
    have := mem_map_of_mem (Embedding.subtype _) ha
    rwa [map_vertexOf_contractEdge_of_notMem he.not_sameCycle hU] at this
  have hfam : ∀ y, y ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 ↔
      y ∈ T₀.darts ∨ y ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts (𝒯.erase p₀) := by
    intro y
    constructor
    · intro h
      obtain ⟨q, hq, hyq⟩ := mem_familyDarts.1 h
      by_cases hqp : q = p₀
      · subst hqp
        exact Or.inl hyq
      · exact Or.inr (mem_familyDarts.2 ⟨q, mem_erase.2 ⟨hqp, hq⟩, hyq⟩)
    · rintro (h | h)
      · exact mem_familyDarts.2 ⟨p₀, hp₀, h⟩
      · obtain ⟨q, hq, hyq⟩ := mem_familyDarts.1 h
        exact mem_familyDarts.2 ⟨q, mem_of_mem_erase hq, hyq⟩
  have hT'c := SplitTree.isCollapsibleOfColour hG he T₀ m₀ hm₀ hMW (h𝒯.isCollapsibleOfColour p₀ hp₀)
  have h𝒯' := isCollapsingFamily_insert_transportFamily' hGc hG (h𝒯.subset (erase_subset p₀ 𝒯))
    hdisj hemb hA (fun _ _ => trivial) hroot
    (fun q hq => by
      obtain ⟨a, ha, haD⟩ := hfreeD q (mem_of_mem_erase hq)
      exact ⟨a, trivial, fun h => haD ((hfam a).2 (Or.inr h)),
        fun h => haD ((hfam a).2 (Or.inl h)),
        hmapr q (mem_of_mem_erase hq) (hrootM q hq) a ha⟩)
    hT'c
    (fun y hy => by
      rcases (hD' y).1 hy with rfl | rfl | ⟨hyS, hyT⟩
      · exact Or.inr fun ⟨x, hx⟩ => (mem_compl_pair_iff.1 x.2).1 hx
      · exact Or.inr fun ⟨x, hx⟩ => (mem_compl_pair_iff.1 x.2).2 hx
      · exact Or.inl ⟨⟨y, hyS⟩, hyT, trivial, rfl⟩)
    (by
      obtain ⟨a, ha, haD⟩ := hfreeD p₀ hp₀
      have hU : (T₀.intervalStart : H) ∉ G.vertexOf f ∪ G.vertexOf (G.inv f) := fun h =>
        T₀.root_notMem_nonRoot (by
          rwa [T₀.root_eq_vertexOf_intervalStart, (hM _).2 h])
      exact ⟨a, trivial, fun h => haD ((hfam a).2 (Or.inr h)),
        fun h => haD ((hfam a).2 (Or.inl h)), hmapr p₀ hp₀ hU a ha⟩)
  refine ⟨_, h𝒯', ?_⟩
  have hD : ∀ x : (({f, G.inv f} : Set H)ᶜ : Set H),
      x ∈ (G.contractEdge f (he.leg_mem hG)).familyDarts 𝒯 ↔
        (x : H) ∈ G.familyDarts (insert (T', p₀.2) (transportFamily hGc hG hemb)) := by
    intro x
    rw [mem_familyDarts_insert_transportFamily, hfam, hD']
    have hx := mem_compl_pair_iff.1 x.2
    simp only [hx.1, hx.2, false_or, exists_prop_of_true x.2]
    refine or_congr Iff.rfl ⟨fun h => ⟨x, h, rfl⟩, ?_⟩
    rintro ⟨d, hd, hdx⟩
    rwa [← Subtype.ext hdx]
  have hfD : f ∈ G.familyDarts (insert (T', p₀.2) (transportFamily hGc hG hemb)) :=
    mem_familyDarts.2 ⟨_, mem_insert_self _ _, (hD' f).2 (Or.inl rfl)⟩
  have hifD : G.inv f ∈ G.familyDarts (insert (T', p₀.2) (transportFamily hGc hG hemb)) :=
    mem_familyDarts.2 ⟨_, mem_insert_self _ _, (hD' _).2 (Or.inr (Or.inl rfl))⟩
  have hQ : ∀ x, G.rot x ∈ (G.vertexOf f : Set H) ↔ x ∈ (G.vertexOf f : Set H) := fun x => by
    simp only [mem_coe, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hQK : ∀ x ∈ (G.vertexOf f : Set H),
      x ∉ G.collapseCore (insert (T', p₀.2) (transportFamily hGc hG hemb)) := by
    intro x hx'
    have hxv : G.vertexOf x = G.vertexOf f := G.vertexOf_eq_of_mem (mem_coe.1 hx')
    rintro (h | ⟨i, rfl⟩)
    · exact h (mem_familyDarts.2 ⟨_, mem_insert_self _ _, T'.mem_darts_of_vertexOf_mem
        (by rw [hxv]; exact SplitTree.vertexOf_mem_nonRoot hG he T₀ m₀ hm₀ hMW)⟩)
    · apply he.not_isBoundaryVertex
      rw [← hxv]
      exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hcol : ∀ i, ∀ p₁ ∈ insert (T', p₀.2) (transportFamily hGc hG hemb), ∀ p₂ ∈ 𝒯,
      G.leg i ∈ p₁.1.darts → (G.contractEdge f (he.leg_mem hG)).leg i ∈ p₂.1.darts →
      p₁.2 = p₂.2 := by
    intro i p₁ hp₁ p₂ hp₂ h₁ h₂
    rcases mem_insert.1 hp₁ with rfl | hp₁
    · rcases (hD' _).1 h₁ with h | h | ⟨hS, hT⟩
      · exact absurd h (mem_compl_pair_iff.1 (he.leg_mem hG i)).1
      · exact absurd h (mem_compl_pair_iff.1 (he.leg_mem hG i)).2
      · rw [h𝒯.eq_of_mem_darts hGc hp₀ hp₂ hT h₂]
    · obtain ⟨r, hr, hir, hrc⟩ := transportFamily_colour hGc hG hemb hA (fun _ _ => trivial)
        (x := (G.contractEdge f (he.leg_mem hG)).leg i) trivial hp₁ h₁
      rw [← hrc, h𝒯.eq_of_mem_darts hGc (mem_of_mem_erase hr) hp₂ hir h₂]
  have hcol₁ : ∀ i, ∀ p₁ ∈ insert (T', p₀.2) (transportFamily hGc hG hemb),
      ∀ p₂ ∈ insert (T', p₀.2) (transportFamily hGc hG hemb),
      G.leg i ∈ p₁.1.darts → G.leg i ∈ p₂.1.darts → p₁.2 = p₂.2 :=
    fun i p₁ hp₁ p₂ hp₂ h₁ h₂ => by rw [h𝒯'.eq_of_mem_darts hG hp₁ hp₂ h₁ h₂]
  exact isomorphic_collapse_of_cut hG (contractEdge_eq_cutData hinv (he.leg_mem hG)) hGc hD
    hfD hifD _ hQ hQK (Or.inl (G.self_mem_vertexOf f)) hcol hcol₁

end SplitInside

end PlabicData

end ClusterAlgebras
