/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.CollapseStepSplit

/-!
# Local moves and collapsed graphs

Let `K` be a plabic graph, `𝒯` a collapsing family of `K` whose collapse `K/𝒯` is nearly leafless,
and `K'` a plabic graph isomorphic to `K` or obtained from `K` by a local move. Then `K'` has a
collapsing family `𝒯'` such that `K'/𝒯'` is nearly leafless and is isomorphic to `K/𝒯` or obtained
from `K/𝒯` by a local move, unless `K/𝒯` is nearly leafless equivalent to a plabic graph with a
hollow digon. Moving along a sequence of moves from a nearly leafless graph `G`, this shows that a
nearly leafless plabic graph is not reduced exactly when it is nearly leafless equivalent to a
graph with a hollow digon, and that two move-equivalent reduced graphs without internal leaves are
joined by a sequence of moves through graphs without internal leaves.

## Main results

* `ClusterAlgebras.PlabicGraph.hasCollapseSteps`: a local move of a plabic graph induces a local
  move or an isomorphism of a nearly leafless collapse, unless the collapse is nearly leafless
  equivalent to a graph with a hollow digon.
* `ClusterAlgebras.PlabicGraph.not_isReduced_iff`: a nearly leafless plabic graph is not reduced
  if and only if it is nearly leafless equivalent to a plabic graph with a hollow digon.
* `ClusterAlgebras.PlabicGraph.IsReduced.reflTransGen_leaflessStep`: two move-equivalent plabic
  graphs without internal leaves, one of them reduced, are joined by a sequence of moves through
  plabic graphs without internal leaves.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.
* The removal of a bivalent vertex `{p, σ p}` and the contraction along an edge `{p, p̄}` are both
  *cuts*: the tuple on the darts other than `p, q` whose involution and rotation are the first
  returns of `ι ∘ (p q)` and `σ ∘ (p q)`. The cases of FWZ's proof in which the move lies outside
  the trees of the family are treated together: the collapse of the cut is the cut of the collapse.
  In the cases in which the move lies inside a tree, the tree is modified and the collapses are
  isomorphic, the darts of the trees being deleted in both.
* At the start, every tree of the family with an internal root is replaced by its branches
  (`isCollapsingFamily_branchFamily`); this does not change the collapse, and each interval then
  consists of one dart, so that a vertex split never cuts an interval.
* In case (IV) of FWZ's proof, the subdivided edge may also be the edge joining a leg to a root
  which keeps a single dart outside the trees; the collapse turns that root into a lollipop. The
  trees at that root, the root and the leg are then merged into one tree with a boundary root,
  which does not change the collapse, and the edge is the edge of a tree.
* In cases (V)(b) and (VI)(b) of FWZ's proof, the tree whose root is an endpoint of the contracted
  edge is related to the modified tree by the removal of the bivalent vertex `{ḡ, a₁}` of its
  plabic graph, a move of type (M2).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function _root_.Equiv _root_.Equiv.Perm

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- `CollapseStep` passes from a family of `K` to another family of `K` with an isomorphic
collapse. -/
private theorem CollapseStep.of_collapse_iso {K K' : PlabicGraph b}
    {𝒯 𝒯₀ : Finset (K.data.RootedTree × Shade)} {h𝒯 : K.data.IsCollapsingFamily 𝒯}
    {h𝒯₀ : K.data.IsCollapsingFamily 𝒯₀} (hnl : (K.data.collapse 𝒯).IsNearlyLeafless)
    (θ : (K.data.collapse 𝒯).Iso (K.data.collapse 𝒯₀)) (h : CollapseStep K K' h𝒯₀) :
    CollapseStep K K' h𝒯 := by
  have hnl₀ := θ.isNearlyLeafless (K.collapse h𝒯).isPlabicGraph (K.collapse h𝒯₀).isPlabicGraph hnl
  rcases h with ⟨𝒯', h𝒯', hnl', hst⟩ | ⟨X, hX, hXd⟩
  · exact Or.inl ⟨𝒯', h𝒯', hnl', hst.of_isomorphic ⟨θ⟩ (PlabicData.Isomorphic.refl _)⟩
  · exact Or.inr ⟨X, ⟨hnl, Relation.ReflTransGen.head ⟨hnl₀, Or.inl ⟨θ.symm⟩⟩ hX.2⟩, hXd⟩

/-- It suffices to prove `CollapseStep` for families whose intervals are single darts: the family
of branches has the same collapse. -/
private theorem collapseStep_of_forall_intervalLength_eq_one {K K' : PlabicGraph b}
    (h : ∀ (𝒯 : Finset (K.data.RootedTree × Shade)) (h𝒯 : K.data.IsCollapsingFamily 𝒯),
      (K.data.collapse 𝒯).IsNearlyLeafless → (∀ p ∈ 𝒯, p.1.intervalLength = 1) →
        CollapseStep K K' h𝒯)
    (𝒯 : Finset (K.data.RootedTree × Shade)) (h𝒯 : K.data.IsCollapsingFamily 𝒯)
    (hnl : (K.data.collapse 𝒯).IsNearlyLeafless) : CollapseStep K K' h𝒯 := by
  have hG := K.isPlabicGraph
  have h𝒯b := isCollapsingFamily_branchFamily hG h𝒯
  have θ := (collapseMatch_branchFamily hG h𝒯).iso hG hG
  have hnlb := θ.isNearlyLeafless (K.collapse h𝒯).isPlabicGraph (K.collapse h𝒯b).isPlabicGraph hnl
  exact CollapseStep.of_collapse_iso hnl θ
    (h _ h𝒯b hnlb fun p hp => branchFamily_intervalLength hG hp)

/-! ### Removing a bivalent vertex -/

/-- **Case (III)(c)**: removing a bivalent vertex lying neither in a tree nor at a root. -/
private theorem collapseStep_bivalentRemoval_outside (K : PlabicGraph b) {d : K.Dart}
    (hd : K.data.IsBivalentRemovable d) {𝒯 : Finset (K.data.RootedTree × Shade)}
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) (hnl : (K.data.collapse 𝒯).IsNearlyLeafless)
    (hx : ∀ p ∈ 𝒯, K.data.vertexOf d ∉ p.1.nonRoot ∧ p.1.root ≠ K.data.vertexOf d) :
    CollapseStep K (K.bivalentRemoval hd) h𝒯 := by
  obtain ⟨𝒯', h𝒯', d', hd', θ⟩ :=
    exists_isomorphic_bivalentRemoval_collapse K.isPlabicGraph hd h𝒯 hx
  refine Or.inl ⟨𝒯', h𝒯', ?_, Or.inr ⟨.m2, trivial, Or.inl ⟨d', hd', θ⟩⟩⟩
  obtain ⟨θ⟩ := θ
  have hX := (K.collapse h𝒯).isPlabicGraph
  exact θ.symm.isNearlyLeafless (isPlabicGraph_bivalentRemoval hX hd')
    ((K.bivalentRemoval hd).collapse h𝒯').isPlabicGraph (hnl.bivalentRemoval hX hd')

/-- **Removing a bivalent vertex** (case (III) of `hasCollapseSteps`). -/
private theorem collapseStep_bivalentRemoval (K : PlabicGraph b) {d : K.Dart}
    (hd : K.data.IsBivalentRemovable d) (𝒯 : Finset (K.data.RootedTree × Shade))
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) (hnl : (K.data.collapse 𝒯).IsNearlyLeafless)
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1) :
    CollapseStep K (K.bivalentRemoval hd) h𝒯 := by
  have hG := K.isPlabicGraph
  have hX := (K.collapse h𝒯).isPlabicGraph
  have key : ∀ 𝒯' (h𝒯' : (K.data.bivalentRemoval hG hd).IsCollapsingFamily 𝒯'),
      ((K.data.bivalentRemoval hG hd).collapse 𝒯').Isomorphic (K.data.collapse 𝒯) →
      CollapseStep K (K.bivalentRemoval hd) h𝒯 := fun 𝒯' h𝒯' θ => by
    obtain ⟨θ'⟩ := θ
    exact Or.inl ⟨𝒯', h𝒯', θ'.symm.isNearlyLeafless hX
      ((K.bivalentRemoval hd).collapse h𝒯').isPlabicGraph hnl, Or.inl ⟨θ'⟩⟩
  by_cases hW : ∃ p ∈ 𝒯, K.data.vertexOf d ∈ p.1.nonRoot
  · obtain ⟨p₀, hp₀, hxW⟩ := hW
    obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_removal_inside hG hd h𝒯 hp₀ hxW
    exact key 𝒯' h𝒯' θ
  push Not at hW
  by_cases hR : ∃ p ∈ 𝒯, p.1.root = K.data.vertexOf d
  · obtain ⟨p₀, hp₀, hroot⟩ := hR
    obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_removal_root hG hd h𝒯 hnl hbr hp₀ hroot hW
    exact key 𝒯' h𝒯' θ
  push Not at hR
  exact collapseStep_bivalentRemoval_outside K hd h𝒯 hnl fun p hp => ⟨hW p hp, hR p hp⟩

/-- **Inserting a bivalent vertex** (case (IV) of `hasCollapseSteps`). -/
private theorem collapseStep_bivalentInsertion (K' : PlabicGraph b) {d : K'.Dart}
    (hd : K'.data.IsBivalentRemovable d)
    (𝒯 : Finset ((K'.data.bivalentRemoval K'.isPlabicGraph hd).RootedTree × Shade))
    (h𝒯 : (K'.data.bivalentRemoval K'.isPlabicGraph hd).IsCollapsingFamily 𝒯)
    (hnl : ((K'.data.bivalentRemoval K'.isPlabicGraph hd).collapse 𝒯).IsNearlyLeafless)
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1) :
    CollapseStep (K'.bivalentRemoval hd) K' h𝒯 := by
  have hG := K'.isPlabicGraph
  have hGr := isPlabicGraph_bivalentRemoval hG hd
  have hX := ((K'.bivalentRemoval hd).collapse h𝒯).isPlabicGraph
  have key : ∀ 𝒯' (h𝒯' : K'.data.IsCollapsingFamily 𝒯'),
      (K'.data.collapse 𝒯').Isomorphic ((K'.data.bivalentRemoval hG hd).collapse 𝒯) →
      CollapseStep (K'.bivalentRemoval hd) K' h𝒯 := fun 𝒯' h𝒯' θ => by
    obtain ⟨θ'⟩ := θ
    exact Or.inl ⟨𝒯', h𝒯', θ'.symm.isNearlyLeafless hX (K'.collapse h𝒯').isPlabicGraph hnl,
      Or.inl ⟨θ'⟩⟩
  have hwy : (K'.data.bivalentRemoval hG hd).inv
      (⟨K'.data.inv (K'.data.rot d), hd.inv_rot_mem hG⟩ : ({d, K'.data.rot d}ᶜ : Set K'.Dart)) =
      (⟨K'.data.inv d, hd.inv_mem hG⟩ : ({d, K'.data.rot d}ᶜ : Set K'.Dart)) :=
    Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd rfl)
  by_cases ha : (⟨K'.data.inv d, hd.inv_mem hG⟩ : ({d, K'.data.rot d}ᶜ : Set K'.Dart)) ∈
      (K'.data.bivalentRemoval hG hd).familyDarts 𝒯
  · obtain ⟨p₀, hp₀, hyp⟩ := mem_familyDarts.1 ha
    classical
    have hc := h𝒯.isCollapsibleOfColour p₀ hp₀
    have hfreeD : ∀ q ∈ 𝒯, ∃ a ∈ q.1.root, ∀ r ∈ 𝒯, a ∉ r.1.darts := h𝒯.exists_mem_root
    obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_insertion_inside (G := K'.data) hG hd
      (h𝒯.subset (erase_subset p₀ 𝒯)) p₀.1 p₀.2 hyp hc.moveEquivalent
      (hc.root_cases.imp (fun h => h) (fun h => h.1))
      (fun q hq => p₀.1.disjoint_darts hGr
        (h𝒯.disjoint_nonRoot p₀ hp₀ q (mem_of_mem_erase hq) (ne_of_mem_erase hq).symm)
        (h𝒯.root_notMem_nonRoot q (mem_of_mem_erase hq) p₀ hp₀ (ne_of_mem_erase hq)))
      (fun q hq => by
        obtain ⟨a, ha, haq⟩ := hfreeD q (mem_of_mem_erase hq)
        refine ⟨a, ha, fun h => ?_, haq p₀ hp₀⟩
        obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
        exact haq r (mem_of_mem_erase hr) har)
      (by
        obtain ⟨a, ha, haq⟩ := hfreeD p₀ hp₀
        refine ⟨a, ha, fun h => ?_, haq p₀ hp₀⟩
        obtain ⟨r, hr, har⟩ := mem_familyDarts.1 h
        exact haq r (mem_of_mem_erase hr) har)
    rw [show ((p₀.1, p₀.2) : _ × Shade) = p₀ from rfl, insert_erase hp₀] at θ
    exact key 𝒯' h𝒯' θ
  have hwD :
      (⟨K'.data.inv (K'.data.rot d), hd.inv_rot_mem hG⟩ : ({d, K'.data.rot d}ᶜ : Set K'.Dart)) ∉
      (K'.data.bivalentRemoval hG hd).familyDarts 𝒯 := fun h => ha (by
    have := inv_mem_familyDarts hGr h
    rwa [hwy] at this)
  by_cases hleaf : ((K'.data.bivalentRemoval hG hd).collapse 𝒯).IsInternalLeaf
      (((K'.data.bivalentRemoval hG hd).collapse 𝒯).vertexOf
        ⟨(⟨K'.data.inv d, hd.inv_mem hG⟩ : ({d, K'.data.rot d}ᶜ : Set K'.Dart)),
          Or.inl (Or.inl ha)⟩)
  · obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_insertion_lollipopEdge (G := K'.data) hG hd h𝒯 hbr hnl
      (u := (⟨K'.data.inv d, hd.inv_mem hG⟩ : ({d, K'.data.rot d}ᶜ : Set K'.Dart)))
      (Or.inl (show K'.data.inv d = K'.data.inv d from rfl)) ha hleaf
    exact key 𝒯' h𝒯' θ
  by_cases hleaf' : ((K'.data.bivalentRemoval hG hd).collapse 𝒯).IsInternalLeaf
      (((K'.data.bivalentRemoval hG hd).collapse 𝒯).vertexOf
        ⟨(⟨K'.data.inv (K'.data.rot d), hd.inv_rot_mem hG⟩ :
            ({d, K'.data.rot d}ᶜ : Set K'.Dart)), Or.inl (Or.inl hwD)⟩)
  · obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_insertion_lollipopEdge (G := K'.data) hG hd h𝒯 hbr hnl
      (u := (⟨K'.data.inv (K'.data.rot d), hd.inv_rot_mem hG⟩ :
        ({d, K'.data.rot d}ᶜ : Set K'.Dart)))
      (Or.inr (show K'.data.inv (K'.data.rot d) = K'.data.inv (K'.data.rot d) from rfl)) hwD hleaf'
    exact key 𝒯' h𝒯' θ
  obtain ⟨𝒯', h𝒯', hnl', d', hd', θ⟩ := exists_collapse_insertion_outside (G := K'.data) hG hd h𝒯
    ha hnl
    (fun u hu => by
      rcases hu with hu | hu
      · rwa [show u = ⟨(⟨K'.data.inv d, hd.inv_mem hG⟩ : ({d, K'.data.rot d}ᶜ : Set K'.Dart)),
          Or.inl (Or.inl ha)⟩ from Subtype.ext (Subtype.ext hu)]
      · rwa [show u =
          ⟨(⟨K'.data.inv (K'.data.rot d), hd.inv_rot_mem hG⟩ :
              ({d, K'.data.rot d}ᶜ : Set K'.Dart)), Or.inl (Or.inl hwD)⟩
            from Subtype.ext (Subtype.ext hu)])
  exact Or.inl ⟨𝒯', h𝒯', hnl', Or.inr ⟨.m2, trivial, Or.inr ⟨d', hd', θ⟩⟩⟩

/-! ### Contracting an edge -/

/-- **Contracting an edge with an end in a tree** (cases (V)(a) and (V)(b) of
`hasCollapseSteps`). -/
private theorem collapseStep_contractEdge_of_mem (K : PlabicGraph b) {f : K.Dart}
    (he : K.data.IsContractibleEdge f) (𝒯 : Finset (K.data.RootedTree × Shade))
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) (hnl : (K.data.collapse 𝒯).IsNearlyLeafless)
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1)
    (hz : ∃ p ∈ 𝒯, K.data.vertexOf (K.data.inv f) ∈ p.1.nonRoot) :
    CollapseStep K (K.contractEdge he) h𝒯 := by
  have hG := K.isPlabicGraph
  have hX := (K.collapse h𝒯).isPlabicGraph
  have key : ∀ 𝒯' (h𝒯' : (K.data.contractEdge f (he.leg_mem hG)).IsCollapsingFamily 𝒯'),
      ((K.data.contractEdge f (he.leg_mem hG)).collapse 𝒯').Isomorphic (K.data.collapse 𝒯) →
      CollapseStep K (K.contractEdge he) h𝒯 := fun 𝒯' h𝒯' θ => by
    obtain ⟨θ'⟩ := θ
    exact Or.inl ⟨𝒯', h𝒯', θ'.symm.isNearlyLeafless hX
      ((K.contractEdge he).collapse h𝒯').isPlabicGraph hnl, Or.inl ⟨θ'⟩⟩
  obtain ⟨p₀, hp₀, hz⟩ := hz
  by_cases hy : K.data.vertexOf f ∈ p₀.1.nonRoot
  · obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_contract_inside hG he h𝒯 hp₀ hy hz
    exact key 𝒯' h𝒯' θ
  · have hifD := p₀.1.mem_darts_of_vertexOf_mem hz
    have hfD : f ∈ p₀.1.darts := by
      have := p₀.1.inv_mem_darts hG hifD; rwa [hG.inv_involutive] at this
    have hroot : p₀.1.root = K.data.vertexOf f :=
      ((p₀.1.vertexOf_mem_or_eq_root hG hfD).resolve_left hy).symm
    obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_contract_root hG he h𝒯 hbr hp₀ hroot hz
    exact key 𝒯' h𝒯' θ

/-- **Contracting an edge** (case (V) of `hasCollapseSteps`). -/
private theorem collapseStep_contractEdge (K : PlabicGraph b) {f : K.Dart}
    (he : K.data.IsContractibleEdge f) (𝒯 : Finset (K.data.RootedTree × Shade))
    (h𝒯 : K.data.IsCollapsingFamily 𝒯) (hnl : (K.data.collapse 𝒯).IsNearlyLeafless)
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1) :
    CollapseStep K (K.contractEdge he) h𝒯 := by
  have hG := K.isPlabicGraph
  have hinv := hG.inv_involutive
  by_cases hz : ∃ p ∈ 𝒯, K.data.vertexOf (K.data.inv f) ∈ p.1.nonRoot
  · exact collapseStep_contractEdge_of_mem K he 𝒯 h𝒯 hnl hbr hz
  by_cases hy : ∃ p ∈ 𝒯, K.data.vertexOf f ∈ p.1.nonRoot
  · have he' := isContractibleEdge_inv hG he
    have h := collapseStep_contractEdge_of_mem K he' 𝒯 h𝒯 hnl hbr (by rwa [hinv])
    exact h.of_isomorphic_right (contractEdge_inv_isomorphic hG he)
  push Not at hz hy
  obtain ⟨𝒯', h𝒯', f', he', θ⟩ :=
    exists_isomorphic_contractEdge_collapse hG he h𝒯 hnl fun p hp => ⟨hy p hp, hz p hp⟩
  refine Or.inl ⟨𝒯', h𝒯', ?_, Or.inr ⟨.m3, trivial, Or.inl ⟨f', he', θ⟩⟩⟩
  obtain ⟨θ⟩ := θ
  have hX := (K.collapse h𝒯).isPlabicGraph
  exact θ.symm.isNearlyLeafless (hX.contractEdge he')
    ((K.contractEdge he).collapse h𝒯').isPlabicGraph (hnl.contractEdge hX he')

/-! ### Splitting a vertex -/

/-- **Splitting a vertex** (case (VI) of `hasCollapseSteps`). -/
private theorem collapseStep_splitVertex (K' : PlabicGraph b) {f : K'.Dart}
    (he : K'.data.IsContractibleEdge f)
    (𝒯 : Finset ((K'.data.contractEdge f (he.leg_mem K'.isPlabicGraph)).RootedTree × Shade))
    (h𝒯 : (K'.data.contractEdge f (he.leg_mem K'.isPlabicGraph)).IsCollapsingFamily 𝒯)
    (hnl : ((K'.data.contractEdge f (he.leg_mem K'.isPlabicGraph)).collapse 𝒯).IsNearlyLeafless)
    (hbr : ∀ p ∈ 𝒯, p.1.intervalLength = 1) :
    CollapseStep (K'.contractEdge he) K' h𝒯 := by
  have hG := K'.isPlabicGraph
  have hX := ((K'.contractEdge he).collapse h𝒯).isPlabicGraph
  have key : ∀ 𝒯' (h𝒯' : K'.data.IsCollapsingFamily 𝒯'),
      ((K'.data.contractEdge f (he.leg_mem hG)).collapse 𝒯).Isomorphic (K'.data.collapse 𝒯') →
      CollapseStep (K'.contractEdge he) K' h𝒯 := fun 𝒯' h𝒯' θ => by
    obtain ⟨θ'⟩ := θ
    exact Or.inl ⟨𝒯', h𝒯', θ'.isNearlyLeafless hX (K'.collapse h𝒯').isPlabicGraph hnl,
      Or.inl ⟨θ'.symm⟩⟩
  by_cases hin : ∃ p ∈ 𝒯, ∃ x : (({f, K'.data.inv f} : Set K'.Dart)ᶜ : Set K'.Dart),
      (x : K'.Dart) ∈ K'.data.vertexOf f ∪ K'.data.vertexOf (K'.data.inv f) ∧
      (K'.data.contractEdge f (he.leg_mem hG)).vertexOf x ∈ p.1.nonRoot
  · obtain ⟨p₀, hp₀, m₀, hm₀, hMW⟩ := hin
    obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_split_inside hG he h𝒯 hp₀ m₀ hm₀ hMW
    exact key 𝒯' h𝒯' θ
  push Not at hin
  by_cases hA₁ : ∀ a : (({f, K'.data.inv f} : Set K'.Dart)ᶜ : Set K'.Dart),
      (a : K'.Dart) ∈ K'.data.vertexOf f →
        a ∈ (K'.data.contractEdge f (he.leg_mem hG)).familyDarts 𝒯
  · obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_split_root hG he h𝒯 hbr hin (Or.inl rfl) hA₁
    exact key 𝒯' h𝒯' θ
  by_cases hA₂ : ∀ a : (({f, K'.data.inv f} : Set K'.Dart)ᶜ : Set K'.Dart),
      (a : K'.Dart) ∈ K'.data.vertexOf (K'.data.inv f) →
        a ∈ (K'.data.contractEdge f (he.leg_mem hG)).familyDarts 𝒯
  · obtain ⟨𝒯', h𝒯', θ⟩ := exists_collapse_split_root hG he h𝒯 hbr hin (Or.inr rfl) hA₂
    exact key 𝒯' h𝒯' θ
  push Not at hA₁ hA₂
  obtain ⟨𝒯', h𝒯', hnl', f', he', θ⟩ :=
    exists_collapse_split_outside hG he h𝒯 hnl hbr hin hA₁ hA₂
  exact Or.inl ⟨𝒯', h𝒯', hnl', Or.inr ⟨.m3, trivial, Or.inr ⟨f', he', θ⟩⟩⟩

/-- `CollapseStep` for every family, for the insertion of a bivalent vertex. -/
private theorem collapseStep_bivalentInsertion' (K : PlabicGraph b) {d : K.Dart}
    (hd : K.data.IsBivalentRemovable d)
    (𝒯 : Finset ((K.bivalentRemoval hd).data.RootedTree × Shade))
    (h𝒯 : (K.bivalentRemoval hd).data.IsCollapsingFamily 𝒯)
    (hnl : ((K.bivalentRemoval hd).data.collapse 𝒯).IsNearlyLeafless) :
    CollapseStep (K.bivalentRemoval hd) K h𝒯 :=
  collapseStep_of_forall_intervalLength_eq_one (K := K.bivalentRemoval hd) (K' := K)
    (fun 𝒯₀ h𝒯₀ hnl₀ hbr => collapseStep_bivalentInsertion K hd 𝒯₀ h𝒯₀ hnl₀ hbr) 𝒯 h𝒯 hnl

/-- `CollapseStep` for every family, for the splitting of a vertex. -/
private theorem collapseStep_splitVertex' (K : PlabicGraph b) {d : K.Dart}
    (he : K.data.IsContractibleEdge d)
    (𝒯 : Finset ((K.contractEdge he).data.RootedTree × Shade))
    (h𝒯 : (K.contractEdge he).data.IsCollapsingFamily 𝒯)
    (hnl : ((K.contractEdge he).data.collapse 𝒯).IsNearlyLeafless) :
    CollapseStep (K.contractEdge he) K h𝒯 :=
  collapseStep_of_forall_intervalLength_eq_one (K := K.contractEdge he) (K' := K)
    (fun 𝒯₀ h𝒯₀ hnl₀ hbr => collapseStep_splitVertex K he 𝒯₀ h𝒯₀ hnl₀ hbr) 𝒯 h𝒯 hnl

/-! ### The three statements -/

/-- **Local moves and collapsed graphs**. Let `K` be a plabic graph, `𝒯` a collapsing family of
`K` such that `K/𝒯` is nearly leafless, and `K'` a plabic graph isomorphic to `K` or obtained from
`K` by a local move. Then `K'` has a collapsing family `𝒯'` such that `K'/𝒯'` is nearly leafless
and is isomorphic to `K/𝒯` or obtained from `K/𝒯` by a local move, or `K/𝒯` is nearly leafless
equivalent to a plabic graph containing a hollow digon. -/
@[cluster_algebras "lem_nearly_leafless_step"]
theorem hasCollapseSteps : HasCollapseSteps b := by
  refine hasCollapseSteps_of_isLiteralMove fun K K' 𝒯 h𝒯 hnl hlit => ?_
  cases hlit with
  | @squareMove K₀ c hq => exact collapseStep_squareMove _ h𝒯 hnl hq
  | @bivalentRemoval K₀ d hd =>
    exact collapseStep_of_forall_intervalLength_eq_one
      (fun 𝒯₀ h𝒯₀ hnl₀ hbr => collapseStep_bivalentRemoval _ hd 𝒯₀ h𝒯₀ hnl₀ hbr) 𝒯 h𝒯 hnl
  | @bivalentInsertion K₀ d hd => exact collapseStep_bivalentInsertion' _ hd 𝒯 h𝒯 hnl
  | @contractEdge K₀ d he =>
    exact collapseStep_of_forall_intervalLength_eq_one
      (fun 𝒯₀ h𝒯₀ hnl₀ hbr => collapseStep_contractEdge _ he 𝒯₀ h𝒯₀ hnl₀ hbr) 𝒯 h𝒯 hnl
  | @splitVertex K₀ d he => exact collapseStep_splitVertex' _ he 𝒯 h𝒯 hnl

/-- **Reducedness without stray leaves**: a nearly leafless plabic graph `G` is not reduced if and
only if `G` is nearly leafless equivalent to a plabic graph containing a hollow digon. -/
@[cluster_algebras "prop_reduced_collapse"]
theorem not_isReduced_iff {G : PlabicGraph b} (hG : G.data.IsNearlyLeafless) :
    ¬G.IsReduced ↔ ∃ X : PlabicGraph b, NearlyLeaflessEquivalent G X ∧
      ∃ f, X.data.IsHollowDigon f :=
  not_isReduced_iff_of_hasCollapseSteps hasCollapseSteps hG

/-- **Moves between reduced leafless graphs avoid leaves**: if `G` and `G'` are plabic graphs
without internal leaves, `G` is reduced and `G ∼ G'`, then there is a finite sequence
`G = L₀, L₁, …, L_r = G'` of plabic graphs without internal leaves in which each `L_t` is
isomorphic to `L_{t-1}` or obtained from `L_{t-1}` by a local move. -/
@[cluster_algebras "lem_reduced_leafless_sequence"]
theorem IsReduced.reflTransGen_leaflessStep {G G' : PlabicGraph b} (hred : G.IsReduced)
    (hG : ∀ v, ¬G.data.IsInternalLeaf v) (hG' : ∀ v, ¬G'.data.IsInternalLeaf v)
    (h : MoveEquivalent Set.univ G G') : Relation.ReflTransGen LeaflessStep G G' :=
  reflTransGen_leaflessStep_of_hasCollapseSteps hasCollapseSteps hG hG' hred h

end PlabicGraph

end ClusterAlgebras
