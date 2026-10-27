/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.NormalPlabic
public import ClusterAlgebras.Plabic.Reduced

/-!
# Nearly leafless plabic graphs, recolouring and normalization

A plabic graph is *nearly leafless* if each of its internal leaves is a lollipop. This file
collects the facts about nearly leafless plabic graphs used in the proof that reduced plabic
graphs are characterised by their decorated trip permutations.

An internal vertex of a nearly leafless graph `G` at which an edge to an internal vertex starts
has at least two darts, since a leaf of `G` runs to a boundary vertex. Hence the removal of a
bivalent vertex and the contraction of an edge keep a graph nearly leafless, and the merged vertex
of a contraction has at least two darts. A rooted tree of a nearly leafless graph has a leaf,
which is a lollipop; so the tree consists of its root `β(i)` and that lollipop, and is not
collapsible.

A local move from a graph without internal leaves to a nearly leafless graph creates no internal
leaf. In a nearly leafless graph, a face `(c₁, c₂, c₃, c₄)` with alternating colours whose corner
`v(c_k)` has two darts yields a hollow digon after removing `v(c_k)` and contracting the new
edge. The recolouring `R_i` of the lollipop at `i` commutes with local moves between nearly
leafless graphs. Finally a *normalization* of `G` is a normal plabic graph reached from `G` by
isomorphisms, local moves and recolourings of lollipops of nearly leafless graphs.

## Main definitions

* `ClusterAlgebras.PlabicGraph.recolourLollipop`: the recolouring `R_i` of a bundled plabic graph.
* `ClusterAlgebras.PlabicGraph.NormalizationStep`, `ClusterAlgebras.PlabicGraph.IsNormalization`:
  normalizations.

## Main results

* `ClusterAlgebras.PlabicGraph.exists_nearlyLeaflessEquivalent_isHollowDigon`: a square with a
  bivalent corner in a nearly leafless graph yields a hollow digon.
* `ClusterAlgebras.PlabicGraph.MoveStep.forall_not_isInternalLeaf`: a nearly leafless step from a
  graph without internal leaves creates no internal leaf.
* `ClusterAlgebras.PlabicData.IsNearlyLeafless.not_isCollapsible`: a nearly leafless plabic graph
  has no collapsible tree.
* `ClusterAlgebras.PlabicGraph.MoveStep.recolourLollipop`: recolouring commutes with local moves
  between nearly leafless graphs, from `PlabicData.Iso.recolourLollipop`,
  `PlabicData.recolourLollipop_squareMove`, `PlabicData.bivalentRemoval_recolourLollipop` and
  `PlabicData.contractEdge_recolourLollipop`.
* `ClusterAlgebras.PlabicData.IsNearlyLeafless.bivalentRemoval`,
  `ClusterAlgebras.PlabicData.IsNearlyLeafless.contractEdge`: the removal of a bivalent vertex and
  the contraction of an edge keep a plabic graph nearly leafless.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.
* The recolouring `R_i` of a bundled plabic graph has the darts of the graph, so that
  "`G_t = R_i(G_{t-1})`" is an equality in `PlabicGraph b`.
* In `PlabicGraph.exists_nearlyLeaflessEquivalent_isHollowDigon` the face `(c₁, c₂, c₃, c₄)` is
  given by `c = c₁` with `φ⁴(c) = c`; its corner `c_{j+1}` is `PlabicData.squareCorner c j` for
  `j : Fin 4`, as for square moves.
* In `PlabicGraph.MoveStep.recolourLollipop` the local move of `R_i(G)` has the type of the given
  move, so the statement is made for `S`-equivalence steps, for every set `S` of types.
* A normalization `N` is required to satisfy the conditions `PlabicData.IsNormal`; it is a plabic
  graph as an element of `PlabicGraph b`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### Leaves of nearly leafless graphs -/

/-- Every internal leaf is the vertex of a dart. -/
private theorem exists_vertexOf_eq_of_isInternalLeaf {G : PlabicData H b} {v : Finset H}
    (hv : G.IsInternalLeaf v) : ∃ x, G.vertexOf x = v :=
  G.mem_vertices.1 (G.mem_internalVertices.1 hv.1).1

/-- The vertex of a dart in `β(i)` is a boundary vertex. -/
theorem IsPlabicGraph.isBoundaryVertex_vertexOf_of_mem_bvertex {G : PlabicData H b}
    (hG : G.IsPlabicGraph) {x : H} {i : Fin b} (h : x ∈ G.bvertex i) :
    G.IsBoundaryVertex (G.vertexOf x) := by
  rw [G.vertexOf_eq_of_mem h]
  exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

/-- The only dart of `β(i)` off the boundary is the leg `g_i`. -/
theorem IsPlabicGraph.eq_leg_of_mem_bvertex {G : PlabicData H b} (hG : G.IsPlabicGraph)
    {e : H} {i : Fin b} (he : e ∈ G.bvertex i) (heB : e ∉ G.bdry) : e = G.leg i := by
  have : e ∈ (G.bvertex i).filter (· ∉ G.bdry) := mem_filter.2 ⟨he, heB⟩
  rwa [hG.filter_bvertex_notMem_bdry, mem_singleton] at this

/-- An internal vertex `v(d)` that is not an internal leaf has at least two darts. -/
theorem two_le_card_vertexOf_of_not_isInternalLeaf {G : PlabicData H b} {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) (hl : ¬G.IsInternalLeaf (G.vertexOf d)) :
    2 ≤ (G.vertexOf d).card := by
  by_contra hlt
  have h1 : (G.vertexOf d).card = 1 :=
    le_antisymm (by omega) (card_pos.2 ⟨d, G.self_mem_vertexOf d⟩)
  exact hl ⟨G.vertexOf_mem_internalVertices.2 hd, h1⟩

/-- In a nearly leafless plabic graph, an internal vertex `v(d)` whose dart `d` runs to an internal
vertex has at least two darts: an internal leaf is a lollipop, whose dart runs to a boundary
vertex. -/
theorem IsNearlyLeafless.two_le_card_vertexOf {G : PlabicData H b} (hG : G.IsPlabicGraph)
    (hnl : G.IsNearlyLeafless) {d : H} (hd : ¬G.IsBoundaryVertex (G.vertexOf d))
    (hd' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv d))) : 2 ≤ (G.vertexOf d).card := by
  refine two_le_card_vertexOf_of_not_isInternalLeaf hd fun hl => ?_
  obtain ⟨i, -, e, he, hei⟩ := hnl _ hl
  obtain rfl : e = d := card_le_one.1 hl.2.le _ he _ (G.self_mem_vertexOf d)
  exact hd' (hG.isBoundaryVertex_vertexOf_of_mem_bvertex hei)

/-- In a nearly leafless plabic graph, the far end `v(d̄)` of a contractible edge `d` has at least
two darts. -/
theorem IsNearlyLeafless.two_le_card_vertexOf_inv_of_isContractibleEdge {G : PlabicData H b}
    (hG : G.IsPlabicGraph) (hnl : G.IsNearlyLeafless) {d : H} (he : G.IsContractibleEdge d) :
    2 ≤ (G.vertexOf (G.inv d)).card :=
  hnl.two_le_card_vertexOf hG he.not_isBoundaryVertex_inv
    (by rw [hG.inv_involutive]; exact he.not_isBoundaryVertex)

/-- An isomorphism matches the internal leaves. -/
theorem Iso.isInternalLeaf_vertexOf_iff {H' : Type*} [Fintype H'] [DecidableEq H']
    {G : PlabicData H b} {G' : PlabicData H' b} (θ : G.Iso G') (d : H) :
    G'.IsInternalLeaf (G'.vertexOf (θ.toEquiv d)) ↔ G.IsInternalLeaf (G.vertexOf d) := by
  unfold DiskMap.IsInternalLeaf
  rw [θ.vertexOf_mem_internalVertices_iff, θ.card_vertexOf]

/-- A graph isomorphic to a graph without internal leaves has no internal leaves. -/
theorem Iso.forall_not_isInternalLeaf {H' : Type*} [Fintype H'] [DecidableEq H']
    {G : PlabicData H b} {G' : PlabicData H' b} (θ : G.Iso G') (h : ∀ v, ¬G.IsInternalLeaf v) :
    ∀ v, ¬G'.IsInternalLeaf v := by
  intro v hv
  obtain ⟨x, rfl⟩ := exists_vertexOf_eq_of_isInternalLeaf hv
  refine h (G.vertexOf (θ.toEquiv.symm x)) ?_
  rwa [← θ.isInternalLeaf_vertexOf_iff, Equiv.apply_symm_apply]

section Bivalent

variable {G : PlabicData H b} {d : H} (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d)

/-- The internal leaves of the removal of a bivalent vertex are the internal leaves of `G`. -/
theorem isInternalLeaf_bivalentRemoval_vertexOf_iff (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).IsInternalLeaf ((G.bivalentRemoval hG hd).vertexOf y) ↔
      G.IsInternalLeaf (G.vertexOf y) := by
  unfold DiskMap.IsInternalLeaf
  rw [DiskMap.vertexOf_mem_internalVertices, DiskMap.vertexOf_mem_internalVertices,
    isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd, ← map_bivalentRemoval_vertexOf hG hd y,
    card_map]

end Bivalent

section Contraction

variable {G : PlabicData H b} {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}

/-- Away from the endpoints of the contracted edge, the internal leaves of the contraction are
those of `G`. -/
theorem isInternalLeaf_contractEdge_vertexOf_iff_of_notMem (he : G.IsContractibleEdge d)
    {y : (({d, G.inv d} : Set H)ᶜ : Set H)} (hy : (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    (G.contractEdge d hleg).IsInternalLeaf ((G.contractEdge d hleg).vertexOf y) ↔
      G.IsInternalLeaf (G.vertexOf y) := by
  unfold DiskMap.IsInternalLeaf
  rw [DiskMap.vertexOf_mem_internalVertices, DiskMap.vertexOf_mem_internalVertices,
    isBoundaryVertex_vertexOf_contractEdge_iff he,
    ← map_vertexOf_contractEdge_of_notMem he.not_sameCycle hy, card_map]

/-- If both endpoints of the contracted edge have at least two darts, so has the merged vertex. -/
theorem IsContractibleEdge.two_le_card_mergedVertex (he : G.IsContractibleEdge d)
    (h₁ : 2 ≤ (G.vertexOf d).card) (h₂ : 2 ≤ (G.vertexOf (G.inv d)).card) :
    2 ≤ (G.mergedVertex d).card := by
  have hdisj : Disjoint (G.vertexOf d) (G.vertexOf (G.inv d)) := disjoint_left.2 fun _ hx hx' =>
    he.vertexOf_ne ((G.vertexOf_eq_of_mem hx).symm.trans (G.vertexOf_eq_of_mem hx'))
  have h := le_card_sdiff ({d, G.inv d} : Finset H) (G.vertexOf d ∪ G.vertexOf (G.inv d))
  rw [card_union_of_disjoint hdisj] at h
  have h3 : ({d, G.inv d} : Finset H).card ≤ 2 := card_le_two
  unfold mergedVertex
  omega

/-- If both endpoints of the contracted edge have at least two darts, an internal leaf of the
contraction is an internal leaf of `G`. -/
theorem isInternalLeaf_of_isInternalLeaf_contractEdge (he : G.IsContractibleEdge d)
    (h₁ : 2 ≤ (G.vertexOf d).card) (h₂ : 2 ≤ (G.vertexOf (G.inv d)).card)
    {y : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hy : (G.contractEdge d hleg).IsInternalLeaf ((G.contractEdge d hleg).vertexOf y)) :
    (y : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) ∧ G.IsInternalLeaf (G.vertexOf y) := by
  by_cases hyU : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · have h := hy.2
    rw [← card_map (Function.Embedding.subtype _),
      map_vertexOf_contractEdge_of_mem he.not_sameCycle hyU] at h
    have := he.two_le_card_mergedVertex h₁ h₂
    omega
  · exact ⟨hyU, (isInternalLeaf_contractEdge_vertexOf_iff_of_notMem he hyU).1 hy⟩

end Contraction

/-! ### Local moves keep a graph nearly leafless -/

/-- The removal of a bivalent vertex of a nearly leafless plabic graph is nearly leafless. -/
theorem IsNearlyLeafless.bivalentRemoval {G : PlabicData H b} (hG : G.IsPlabicGraph)
    (hnl : G.IsNearlyLeafless) {d : H} (hd : G.IsBivalentRemovable d) :
    (G.bivalentRemoval hG hd).IsNearlyLeafless := by
  intro v hv
  obtain ⟨y, rfl⟩ := exists_vertexOf_eq_of_isInternalLeaf hv
  obtain ⟨i, hl, e, he, hei⟩ :=
    hnl _ ((isInternalLeaf_bivalentRemoval_vertexOf_iff hG hd y).1 hv)
  obtain rfl : e = y := card_le_one.1 hl.2.le _ he _ (G.self_mem_vertexOf _)
  have hb : G.IsBoundaryVertex (G.vertexOf (G.inv y)) :=
    hG.isBoundaryVertex_vertexOf_of_mem_bvertex hei
  have h₁ : (y : H) ≠ G.inv d := fun h =>
    hd.not_isBoundaryVertex (by rwa [h, hG.inv_involutive] at hb)
  have h₂ : (y : H) ≠ G.inv (G.rot d) := fun h =>
    hd.not_isBoundaryVertex (by rwa [h, hG.inv_involutive, G.vertexOf_rot] at hb)
  refine ⟨i, hv, y, (G.bivalentRemoval hG hd).self_mem_vertexOf y, ?_⟩
  rwa [← mem_map' (Function.Embedding.subtype _), map_bivalentRemoval_bvertex hG hd,
    Function.Embedding.coe_subtype, coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]

/-- The contraction of an edge of a nearly leafless plabic graph is nearly leafless. -/
theorem IsNearlyLeafless.contractEdge {G : PlabicData H b} (hG : G.IsPlabicGraph)
    (hnl : G.IsNearlyLeafless) {d : H} (he : G.IsContractibleEdge d)
    {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).IsNearlyLeafless := by
  have h₁ := hnl.two_le_card_vertexOf hG he.not_isBoundaryVertex he.not_isBoundaryVertex_inv
  have h₂ := hnl.two_le_card_vertexOf_inv_of_isContractibleEdge hG he
  intro v hv
  obtain ⟨y, rfl⟩ := exists_vertexOf_eq_of_isInternalLeaf hv
  obtain ⟨-, hl⟩ := isInternalLeaf_of_isInternalLeaf_contractEdge he h₁ h₂ hv
  obtain ⟨i, hl', e, he', hei⟩ := hnl _ hl
  obtain rfl : e = y := card_le_one.1 hl'.2.le _ he' _ (G.self_mem_vertexOf _)
  refine ⟨i, hv, y, (G.contractEdge d hleg).self_mem_vertexOf y, ?_⟩
  rwa [← mem_map' (Function.Embedding.subtype _), map_bvertex_contractEdge hG he,
    Function.Embedding.coe_subtype, coe_contractEdge_inv hG.inv_involutive]

omit [Fintype H] [DecidableEq H] in
/-- `φ(c_k) = c_{k+1}`, indices modulo `4`, as soon as `φ^4(c) = c`. -/
private theorem facePerm_squareCorner_of_pow_four {G : PlabicData H b} {c : H}
    (h4 : (G.facePerm ^ 4) c = c) (k : Fin 4) :
    G.facePerm (G.squareCorner c k) = G.squareCorner c (k + 1) := by
  rw [squareCorner, squareCorner, ← Equiv.Perm.mul_apply, ← pow_succ', Fin.val_add_one]
  split_ifs with h
  · subst h
    simpa using h4
  · rfl

end PlabicData

/-! ### A square with a bivalent corner -/

/-- A permutation exchanging `a` and `b` has the orbit `{a, b}` through `a`. -/
private theorem sameCycle_iff_of_apply_eq {α : Type*} [Finite α] {f : Equiv.Perm α} {a b : α}
    (hab : f a = b) (hba : f b = a) (z : α) : f.SameCycle a z ↔ z = a ∨ z = b := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h <;> rw [h]
      · exact Or.inr hab
      · exact Or.inl hba
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · rw [← hab]
      exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)

/-- A face `{x, y}` exchanged by `φ`, off the boundary and with two distinct vertices, is a hollow
digon. -/
theorem PlabicData.isHollowDigon_faceOf_of_facePerm {H : Type*} [Fintype H] [DecidableEq H]
    {b : ℕ} {G : PlabicData H b} {x y : H} (hxy : G.facePerm x = y) (hyx : G.facePerm y = x)
    (hx : x ∉ G.bdry) (hy : y ∉ G.bdry) (hv : G.vertexOf x ≠ G.vertexOf y) :
    G.IsHollowDigon (G.faceOf x) := by
  have hf : G.faceOf x = {x, y} := by
    ext z
    rw [RotationSystem.mem_faceOf, sameCycle_iff_of_apply_eq hxy hyx, mem_insert, mem_singleton]
  refine ⟨G.mem_internalFaces.2 ⟨G.mem_faces.2 ⟨fun h => hx (G.exterior_subset_bdry
    (h ▸ G.self_mem_faceOf x)), G.faceOf_mem_faceOrbits _⟩, ?_⟩, x, y, hf, hv⟩
  rw [hf, disjoint_left]
  intro q hq
  rcases mem_insert.1 hq with rfl | hq
  · exact hx
  · rwa [mem_singleton.1 hq]

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- `exists_nearlyLeaflessEquivalent_isHollowDigon` for the corners `p₀ = c_{k-1}`, `p₁ = c_k`,
`p₂ = c_{k+1}`, `p₃ = c_{k+2}`. -/
private theorem exists_hollowDigon_core {K : PlabicGraph b} (hK : K.data.IsNearlyLeafless)
    {p₀ p₁ p₂ p₃ : K.Dart}
    (hp₁ : K.data.facePerm p₀ = p₁) (hp₂ : K.data.facePerm p₁ = p₂)
    (hp₃ : K.data.facePerm p₂ = p₃) (hp₀ : K.data.facePerm p₃ = p₀)
    (hface : Disjoint (K.data.faceOf p₀) K.data.bdry)
    (h01 : K.data.vertexOf p₀ ≠ K.data.vertexOf p₁) (h02 : K.data.vertexOf p₀ ≠ K.data.vertexOf p₂)
    (h03 : K.data.vertexOf p₀ ≠ K.data.vertexOf p₃) (h12 : K.data.vertexOf p₁ ≠ K.data.vertexOf p₂)
    (h13 : K.data.vertexOf p₁ ≠ K.data.vertexOf p₃) (h23 : K.data.vertexOf p₂ ≠ K.data.vertexOf p₃)
    (hi₀ : ¬K.data.IsBoundaryVertex (K.data.vertexOf p₀))
    (hi₁ : ¬K.data.IsBoundaryVertex (K.data.vertexOf p₁))
    (hi₂ : ¬K.data.IsBoundaryVertex (K.data.vertexOf p₂))
    (hc₁ : (K.data.vertexOf p₁).card = 2) (hc₂ : 2 ≤ (K.data.vertexOf p₂).card)
    (hκ₀₁ : K.data.colour p₀ ≠ K.data.colour p₁) (hκ₁₂ : K.data.colour p₁ ≠ K.data.colour p₂) :
    ∃ K' : PlabicGraph b, NearlyLeaflessEquivalent K K' ∧ ∃ f, K'.data.IsHollowDigon f := by
  have hG : K.data.IsPlabicGraph := K.isPlabicGraph
  set G := K.data with hGdef
  have hinv := hG.inv_involutive
  have hvi : ∀ x, G.vertexOf (G.inv x) = G.vertexOf (G.facePerm x) := fun x =>
    (G.vertexOf_rot _).symm
  have hne : ∀ {x y : K.Dart}, G.vertexOf x ≠ G.vertexOf y → x ≠ y := fun h hxy => h (hxy ▸ rfl)
  have hp2i : p₂ ≠ G.inv p₁ := by
    intro h
    have h' : G.rot (G.inv p₁) = p₂ := hp₂
    have hfix : G.rot p₂ = p₂ := (congrArg G.rot h).trans h'
    have hsub : G.vertexOf p₂ ⊆ {p₂} := fun y hy =>
      mem_singleton.2 ((G.mem_vertexOf.1 hy).eq_of_left hfix).symm
    have := (card_le_card hsub).trans_eq (card_singleton _)
    omega
  have hp3i : p₃ ≠ G.inv p₁ := hne (by rw [hvi, hp₂]; exact h23.symm)
  set d := G.inv p₀ with hd_def
  have hrd : G.rot d = p₁ := hp₁
  have hid : G.inv d = p₀ := hinv p₀
  have hvd : G.vertexOf d = G.vertexOf p₁ := by rw [hd_def, hvi, hp₁]
  have hd : G.IsBivalentRemovable d :=
    ⟨by rw [hvd]; exact hi₁, by rw [hvd]; exact hc₁, by rw [hid, hrd]; exact hne h01⟩
  have hS₁ : ∀ x, G.vertexOf x ≠ G.vertexOf p₁ → x ∈ ({d, G.rot d}ᶜ : Set K.Dart) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hx (by rw [h, hvd]), fun h => hx (by rw [h, hrd])⟩
  set K₁ := G.bivalentRemoval hG hd with hK₁def
  have hK₁ : K₁.IsPlabicGraph := isPlabicGraph_bivalentRemoval hG hd
  have hK₁nl : K₁.IsNearlyLeafless := hK.bivalentRemoval hG hd
  have hinv₁ := hK₁.inv_involutive
  obtain ⟨e, he₀⟩ : ∃ e : ({d, G.rot d}ᶜ : Set K.Dart), (e : K.Dart) = p₀ :=
    ⟨⟨p₀, hS₁ _ h01⟩, rfl⟩
  have hie : (K₁.inv e : K.Dart) = G.inv p₁ := by
    rw [coe_bivalentRemoval_inv_of_eq_inv hG hd (he₀.trans hid.symm), hrd]
  have hK₁v : ∀ y z : ({d, G.rot d}ᶜ : Set K.Dart),
      K₁.vertexOf y = K₁.vertexOf z ↔ G.vertexOf y = G.vertexOf z := by
    intro y z
    rw [← map_bivalentRemoval_vertexOf hG hd y, ← map_bivalentRemoval_vertexOf hG hd z, map_inj]
  have hK₁i : ∀ y : ({d, G.rot d}ᶜ : Set K.Dart),
      ¬G.IsBoundaryVertex (G.vertexOf y) → K₁.vertexOf y ∈ K₁.internalVertices := fun y hy =>
    K₁.vertexOf_mem_internalVertices.2 (by rwa [isBoundaryVertex_bivalentRemoval_vertexOf_iff])
  have hcol : ∀ a b c : Shade, a ≠ b → b ≠ c → c = a := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> simp
  have he : K₁.IsContractibleEdge e := by
    refine ⟨fun h => ?_, hK₁i e (by rw [he₀]; exact hi₀),
      hK₁i _ (by rw [hie, hvi, hp₂]; exact hi₂), ?_⟩
    · exact h02 (by rwa [hK₁v, he₀, hie, hvi, hp₂] at h)
    · rw [bivalentRemoval_colour, bivalentRemoval_colour, hie, he₀]
      have hsc : G.rot.SameCycle (G.inv p₁) p₂ := by
        rw [← hp₂]
        exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
      rw [← colour_eq_of_sameCycle hG (by rw [hvi, hp₂]; exact hi₂) hsc]
      exact hcol _ _ _ hκ₀₁ hκ₁₂
  have hleg₂ := he.leg_mem hK₁
  set K₂ := K₁.contractEdge e hleg₂ with hK₂def
  have hK₂ : K₂.IsPlabicGraph := hK₁.contractEdge he
  have hK₂nl : K₂.IsNearlyLeafless := hK₁nl.contractEdge hK₁ he
  have hS₂ : ∀ y : ({d, G.rot d}ᶜ : Set K.Dart), (y : K.Dart) ≠ p₀ →
      (y : K.Dart) ≠ G.inv p₁ → y ∈ (({e, K₁.inv e} : Set _)ᶜ : Set _) := by
    intro y h₁ h₂
    rw [mem_compl_pair_iff]
    exact ⟨fun h => h₁ (by rw [h, he₀]), fun h => h₂ (by rw [h, hie])⟩
  obtain ⟨q₂, hq₂⟩ : ∃ q : (({e, K₁.inv e} : Set _)ᶜ : Set _), ((q : _) : K.Dart) = p₂ :=
    ⟨⟨⟨p₂, hS₁ _ h12.symm⟩, hS₂ ⟨p₂, _⟩ (hne h02.symm) hp2i⟩, rfl⟩
  obtain ⟨q₃, hq₃⟩ : ∃ q : (({e, K₁.inv e} : Set _)ᶜ : Set _), ((q : _) : K.Dart) = p₃ :=
    ⟨⟨⟨p₃, hS₁ _ h13.symm⟩, hS₂ ⟨p₃, _⟩ (hne h03.symm) hp3i⟩, rfl⟩
  have hx₂ : (((K₂.inv q₂ : _) : _) : K.Dart) = G.inv p₂ := by
    rw [coe_contractEdge_inv hinv₁, coe_bivalentRemoval_inv_of_ne hG hd
      (by rw [hq₂, hid]; exact hne h02.symm) (by rw [hq₂, hrd]; exact hp2i), hq₂]
  have hx₃ : (((K₂.inv q₃ : _) : _) : K.Dart) = G.inv p₃ := by
    rw [coe_contractEdge_inv hinv₁, coe_bivalentRemoval_inv_of_ne hG hd
      (by rw [hq₃, hid]; exact hne h03.symm) (by rw [hq₃, hrd]; exact hp3i), hq₃]
  have hr₂ : ((K₁.rot (K₂.inv q₂ : _) : _) : K.Dart) = p₃ := by
    rw [coe_bivalentRemoval_rot, hx₂]
    exact hp₃
  have hre : ((K₁.rot (K₁.inv e)) : K.Dart) = p₂ := by
    rw [coe_bivalentRemoval_rot, hie]
    exact hp₂
  have hφ₂ : K₂.facePerm q₂ = q₃ := by
    have hmem : K₁.rot (K₂.inv q₂ : _) ∈ (({e, K₁.inv e} : Set _)ᶜ : Set _) :=
      hS₂ _ (by rw [hr₂]; exact hne h03.symm) (by rw [hr₂]; exact hp3i)
    refine Subtype.ext (Subtype.ext ?_)
    rw [RotationSystem.facePerm_apply, coe_contractEdge_rot_of_mem hmem, hr₂, hq₃]
  have hφ₃ : K₂.facePerm q₃ = q₂ := by
    have hxe : K₁.rot (K₂.inv q₃ : _) = e := by
      apply Subtype.ext
      rw [coe_bivalentRemoval_rot, hx₃, he₀]
      exact hp₀
    have hmem : K₁.rot (K₁.inv e) ∈ (({e, K₁.inv e} : Set _)ᶜ : Set _) :=
      hS₂ _ (by rw [hre]; exact hne h02.symm) (by rw [hre]; exact hp2i)
    refine Subtype.ext (Subtype.ext ?_)
    rw [RotationSystem.facePerm_apply, coe_contractEdge_rot_of_eq hxe hmem, hre, hq₂]
  have hsc₂ : G.facePerm.SameCycle p₀ p₂ := by
    rw [← hp₂, ← hp₁]
    exact Equiv.Perm.sameCycle_apply_right.2
      (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))
  have hsc₃ : G.facePerm.SameCycle p₀ p₃ := by
    rw [← hp₃]
    exact Equiv.Perm.sameCycle_apply_right.2 hsc₂
  have hB : ∀ q : (({e, K₁.inv e} : Set _)ᶜ : Set _), q = q₂ ∨ q = q₃ → q ∉ K₂.bdry := by
    rintro q (rfl | rfl) hq
    · rw [mem_contractEdge_bdry, mem_bivalentRemoval_bdry, hq₂] at hq
      exact disjoint_left.1 hface (G.mem_faceOf.2 hsc₂) hq
    · rw [mem_contractEdge_bdry, mem_bivalentRemoval_bdry, hq₃] at hq
      exact disjoint_left.1 hface (G.mem_faceOf.2 hsc₃) hq
  have hdigon : K₂.IsHollowDigon (K₂.faceOf q₂) := by
    refine isHollowDigon_faceOf_of_facePerm hφ₂ hφ₃ (hB q₂ (Or.inl rfl)) (hB q₃ (Or.inr rfl))
      fun h => ?_
    rw [RotationSystem.vertexOf_eq_vertexOf_iff,
      sameCycle_contractEdge_rot_iff he.not_sameCycle] at h
    have key : ∀ x y : ({d, G.rot d}ᶜ : Set K.Dart), K₁.rot.SameCycle x y →
        G.vertexOf x = G.vertexOf y := fun x y hxy =>
      G.vertexOf_eq_vertexOf_iff.2 ((sameCycle_bivalentRemoval_rot_iff hG hd).1 hxy)
    rcases h with h | ⟨h, -⟩ | ⟨-, h⟩
    · exact h23 (by simpa only [hq₂, hq₃] using key _ _ h)
    · exact h02.symm (by simpa only [hq₂, he₀] using key _ _ h)
    · exact h03.symm (by simpa only [hq₃, he₀] using key _ _ h)
  let K₁b : PlabicGraph b := ⟨_, K₁, hK₁⟩
  let K₂b : PlabicGraph b := ⟨_, K₂, hK₂⟩
  refine ⟨K₂b, ⟨hK, ?_⟩, _, hdigon⟩
  have s₁ : NearlyLeaflessStep K K₁b :=
    ⟨hK₁nl, Or.inr ⟨.m2, trivial, Or.inl ⟨d, hd, PlabicData.Isomorphic.refl _⟩⟩⟩
  have s₂ : NearlyLeaflessStep K₁b K₂b :=
    ⟨hK₂nl, Or.inr ⟨.m3, trivial, Or.inl ⟨e, he, PlabicData.Isomorphic.refl _⟩⟩⟩
  exact (Relation.ReflTransGen.single s₁).tail s₂

/-- **A square with a bivalent corner yields a hollow digon**. Let `K` be a nearly leafless
plabic graph and `q = (c₁, c₂, c₃, c₄)` an internal face of `K` with `c_{j+1} = φ(c_j)` (indices
modulo `4`; here `c_{j+1}` is `squareCorner c j` for `j : Fin 4`), whose vertices `v(c_j)` are
internal, pairwise distinct, each with at least two darts, with `κ(v(c_j)) ≠ κ(v(c_{j+1}))`, and
such that some `v(c_k)` consists of exactly two darts. Then `K` is nearly leafless equivalent to a
plabic graph containing a hollow digon. -/
@[cluster_algebras "lem_square_root_digon"]
theorem exists_nearlyLeaflessEquivalent_isHollowDigon {K : PlabicGraph b}
    (hK : K.data.IsNearlyLeafless) {c : K.Dart} (hq : K.data.faceOf c ∈ K.data.internalFaces)
    (h4 : (K.data.facePerm ^ 4) c = c)
    (hint : ∀ k, K.data.vertexOf (K.data.squareCorner c k) ∈ K.data.internalVertices)
    (hinj : Function.Injective fun k => K.data.vertexOf (K.data.squareCorner c k))
    (hcard : ∀ k, 2 ≤ (K.data.vertexOf (K.data.squareCorner c k)).card)
    (hcol : ∀ k, K.data.colour (K.data.squareCorner c k) ≠
      K.data.colour (K.data.squareCorner c (k + 1)))
    {k : Fin 4} (hk : (K.data.vertexOf (K.data.squareCorner c k)).card = 2) :
    ∃ K' : PlabicGraph b, NearlyLeaflessEquivalent K K' ∧ ∃ f, K'.data.IsHollowDigon f := by
  have hs := facePerm_squareCorner_of_pow_four h4
  have hv : ∀ j l : Fin 4, j ≠ l →
      K.data.vertexOf (K.data.squareCorner c j) ≠ K.data.vertexOf (K.data.squareCorner c l) :=
    fun _ _ => hinj.ne
  have hi : ∀ j, ¬K.data.IsBoundaryVertex (K.data.vertexOf (K.data.squareCorner c j)) := fun j =>
    K.data.vertexOf_mem_internalVertices.1 (hint j)
  have hface : Disjoint (K.data.faceOf (K.data.squareCorner c (k - 1))) K.data.bdry := by
    have hmem : K.data.squareCorner c (k - 1) ∈ K.data.faceOf c :=
      K.data.mem_faceOf.2 (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
    rw [K.data.faceOf_eq_of_mem hmem]
    exact (K.data.mem_internalFaces.1 hq).2
  refine exists_hollowDigon_core hK (p₀ := K.data.squareCorner c (k - 1))
    (p₁ := K.data.squareCorner c k) (p₂ := K.data.squareCorner c (k + 1))
    (p₃ := K.data.squareCorner c (k + 2)) (by rw [hs, sub_add_cancel]) (hs k)
    (by rw [hs]; congr 1; fin_cases k <;> rfl) (by rw [hs]; congr 1; fin_cases k <;> rfl) hface
    (hv _ _ (by fin_cases k <;> decide)) (hv _ _ (by fin_cases k <;> decide))
    (hv _ _ (by fin_cases k <;> decide)) (hv _ _ (by fin_cases k <;> decide))
    (hv _ _ (by fin_cases k <;> decide)) (hv _ _ (by fin_cases k <;> decide))
    (hi _) (hi _) (hi _) hk (hcard _) ?_ (hcol k)
  simpa only [sub_add_cancel] using hcol (k - 1)

/-! ### A nearly leafless step from a leafless graph -/

/-- **A nearly leafless step from a leafless graph creates no leaf**: if `L` is a plabic graph
without internal leaves and `L'` is a nearly leafless plabic graph isomorphic to `L` or obtained
from `L` by a local move (of any type), then `L'` has no internal leaves. -/
@[cluster_algebras "lem_leafless_step"]
theorem MoveStep.forall_not_isInternalLeaf {S : Set LocalMoveType} {L L' : PlabicGraph b}
    (hL : ∀ v, ¬L.data.IsInternalLeaf v) (hL' : L'.data.IsNearlyLeafless) (h : MoveStep S L L') :
    ∀ v, ¬L'.data.IsInternalLeaf v := by
  rcases h with hθ | ⟨t, -, ht⟩
  · exact hθ.elim fun θ => θ.symm.forall_not_isInternalLeaf hL
  cases t with
  | m1 =>
    obtain ⟨c, -, ⟨θ⟩⟩ := ht
    exact θ.symm.forall_not_isInternalLeaf fun v hv => hL v hv
  | m2 =>
    rcases ht with ⟨d, hd, ⟨θ⟩⟩ | ⟨d, hd, ⟨θ⟩⟩
    · refine θ.symm.forall_not_isInternalLeaf fun v hv => ?_
      obtain ⟨y, rfl⟩ := exists_vertexOf_eq_of_isInternalLeaf hv
      exact hL _ ((isInternalLeaf_bivalentRemoval_vertexOf_iff _ hd y).1 hv)
    · intro v hv
      obtain ⟨x, rfl⟩ := exists_vertexOf_eq_of_isInternalLeaf hv
      by_cases hx : x ∈ ({d, L'.data.rot d}ᶜ : Set L'.Dart)
      · exact θ.forall_not_isInternalLeaf hL _
          ((isInternalLeaf_bivalentRemoval_vertexOf_iff L'.isPlabicGraph hd ⟨x, hx⟩).2 hv)
      · have hxv : L'.data.vertexOf x = L'.data.vertexOf d := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
            not_and_or, not_not] at hx
          rcases hx with rfl | rfl
          · rfl
          · exact L'.data.vertexOf_rot d
        have := hv.2
        rw [hxv, hd.card_vertexOf] at this
        omega
  | m3 =>
    rcases ht with ⟨d, he, ⟨θ⟩⟩ | ⟨d, he, ⟨θ⟩⟩
    · refine θ.symm.forall_not_isInternalLeaf fun v hv => ?_
      obtain ⟨y, rfl⟩ := exists_vertexOf_eq_of_isInternalLeaf hv
      have h₁ := two_le_card_vertexOf_of_not_isInternalLeaf he.not_isBoundaryVertex (hL _)
      have h₂ := two_le_card_vertexOf_of_not_isInternalLeaf he.not_isBoundaryVertex_inv (hL _)
      exact hL _ (isInternalLeaf_of_isInternalLeaf_contractEdge he h₁ h₂ hv).2
    · intro v hv
      obtain ⟨x, rfl⟩ := exists_vertexOf_eq_of_isInternalLeaf hv
      by_cases hx : x ∈ L'.data.vertexOf d ∪ L'.data.vertexOf (L'.data.inv d)
      · have hd₂ := hL'.two_le_card_vertexOf L'.isPlabicGraph he.not_isBoundaryVertex
          he.not_isBoundaryVertex_inv
        have hd₂' := hL'.two_le_card_vertexOf_inv_of_isContractibleEdge L'.isPlabicGraph he
        have := hv.2
        rcases mem_union.1 hx with h | h <;> rw [L'.data.vertexOf_eq_of_mem h] at this <;> omega
      · exact θ.forall_not_isInternalLeaf hL _
          ((isInternalLeaf_contractEdge_vertexOf_iff_of_notMem he
            (y := ⟨x, mem_compl_pair_of_notMem hx⟩) hx).2 hv)

end PlabicGraph

/-! ### Rooted trees of nearly leafless graphs -/

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-- **Nearly leafless graphs have no collapsible tree**: a rooted tree `T` of a nearly leafless
plabic graph `G` is not collapsible. -/
@[cluster_algebras "lem_nearly_leafless_no_collapsible"]
theorem IsNearlyLeafless.not_isCollapsible {G : PlabicData H b} (hG : G.IsPlabicGraph)
    (hnl : G.IsNearlyLeafless) (T : G.RootedTree) : ¬T.IsCollapsible := by
  rintro ⟨col, hT⟩
  obtain ⟨w, hwW, hw⟩ := T.exists_isInternalLeaf hG
  obtain ⟨i, -, c, hc, hci⟩ := hnl w hw
  obtain ⟨x, hxw⟩ := exists_vertexOf_eq_of_isInternalLeaf hw
  have hwc : G.vertexOf c = w := (G.vertexOf_eq_of_mem (hxw ▸ hc)).trans hxw
  have hcw : ∀ e, G.vertexOf e = w → e = c := fun e he =>
    card_le_one.1 hw.2.le _ (he ▸ G.self_mem_vertexOf e) _ hc
  have hbi : G.vertexOf (G.inv c) = G.bvertex i := G.vertexOf_eq_of_mem hci
  have hbd : G.IsBoundaryVertex (G.vertexOf (G.inv c)) :=
    hG.isBoundaryVertex_vertexOf_of_mem_bvertex hci
  have hroot : G.vertexOf (G.inv c) = T.root := by
    have := T.vertexOf_inv_mem c (hwc ▸ hwW)
    rcases mem_insert.1 this with h | h
    · exact h
    · exact absurd hbd (G.mem_internalVertices.1 (T.nonRoot_subset h)).2
  have hcB : c ∉ G.bdry := T.notMem_bdry_of_vertexOf_mem (hwc ▸ hwW)
  have hleg : ∀ e, e ∈ G.bvertex i → e ∉ G.bdry → e = G.inv c := fun e he heB => by
    rw [hG.eq_leg_of_mem_bvertex he heB,
      hG.eq_leg_of_mem_bvertex hci fun h => hcB (hG.inv_mem_bdry_iff.1 h)]
  have hreach : ∀ u, Relation.ReflTransGen (G.TreeAdj T.nonRoot) T.root u →
      u = T.root ∨ u = w := by
    intro u hu
    induction hu with
    | refl => exact Or.inl rfl
    | @tail u u' _ hstep ih =>
      obtain ⟨e, heD, heu, heu'⟩ := hstep
      have heB := (G.mem_treeDarts.1 heD).1
      rcases ih with rfl | rfl
      · have he : e ∈ G.bvertex i := by
          rw [← hbi, hroot, ← heu]
          exact G.self_mem_vertexOf e
        rw [← heu', hleg e he heB, hG.inv_involutive]
        exact Or.inr hwc
      · rw [← heu', hcw e heu]
        exact Or.inl hroot
  have hsub : T.nonRoot ⊆ {w} := by
    intro u hu
    rcases hreach u (T.reflTransGen_treeAdj u (mem_insert_of_mem hu)) with rfl | rfl
    · exact absurd hu T.root_notMem_nonRoot
    · exact mem_singleton_self _
  have hcard := (card_le_card hsub).trans_eq (card_singleton _)
  rcases hT.root_cases with ⟨hint, -⟩ | ⟨-, h2⟩
  · exact hint (hroot ▸ hbd)
  · omega

end PlabicData

/-! ### Recolouring and local moves -/

namespace PlabicData

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

omit [Fintype H] [DecidableEq H] in
/-- Data of plabic graphs with the same disk map, colours and labelling are equal. -/
private theorem ext_of_colour {G G' : PlabicData H b} (h₁ : G.toDiskMap = G'.toDiskMap)
    (h₂ : G.colour = G'.colour) (h₃ : G.leg = G'.leg) : G = G' := by
  cases G
  cases G'
  simp_all

/-- An isomorphism `θ : G → G'` of plabic graphs is also an isomorphism `R_i(G) → R_i(G')`: it
maps `ḡ_i` to `ḡ'_i` and the vertices onto the vertices with the same numbers of darts. -/
def Iso.recolourLollipop {G : PlabicData H b} {G' : PlabicData H' b} (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) (θ : G.Iso G') (i : Fin b) :
    (G.recolourLollipop i).Iso (G'.recolourLollipop i) where
  toEquiv := θ.toEquiv
  map_inv := θ.map_inv
  map_rot := θ.map_rot
  mem_bdry_iff := θ.mem_bdry_iff
  map_colour d hd := by
    have hd' : ¬G.IsBoundaryVertex (G.vertexOf d) := hd
    have hgi : θ.toEquiv (G.inv (G.leg i)) = G'.inv (G'.leg i) := by
      rw [θ.map_inv, θ.map_leg hG hG' i]
    have hleaf : G'.IsInternalLeaf (G'.vertexOf (G'.inv (G'.leg i))) ↔
        G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) := by
      rw [← hgi, θ.isInternalLeaf_vertexOf_iff]
    have hmem : θ.toEquiv d ∈ G'.vertexOf (G'.inv (G'.leg i)) ↔
        d ∈ G.vertexOf (G.inv (G.leg i)) := by
      rw [← hgi, ← θ.map_vertexOf, mem_map_equiv, Equiv.symm_apply_apply]
    by_cases h : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
        d ∈ G.vertexOf (G.inv (G.leg i))
    · rw [colour_recolourLollipop_of_mem h.1 h.2,
        colour_recolourLollipop_of_mem (hleaf.2 h.1) (hmem.2 h.2), θ.map_colour d hd']
    · rw [colour_recolourLollipop_of_notMem h,
        colour_recolourLollipop_of_notMem (by rwa [hleaf, hmem]), θ.map_colour d hd']
  map_bvertex := θ.map_bvertex

/-- Isomorphic plabic graphs have isomorphic recolourings. -/
theorem Isomorphic.recolourLollipop {G : PlabicData H b} {G' : PlabicData H' b}
    (h : G.Isomorphic G') (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (i : Fin b) :
    (G.recolourLollipop i).Isomorphic (G'.recolourLollipop i) :=
  h.elim fun θ => ⟨θ.recolourLollipop hG hG' i⟩

variable {G : PlabicData H b}

/-- If the vertex `v(ḡ_i)` is an internal leaf, the vertices of a square face are not it. -/
private theorem vertexOf_notMem_squareVertices {c : H} (hq : G.IsSquareMoveFace c) {i : Fin b}
    (hi : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i)))) {d : H}
    (hd : d ∈ G.vertexOf (G.inv (G.leg i))) : G.vertexOf d ∉ G.squareVertices c := by
  intro h
  obtain ⟨k, hk⟩ := mem_squareVertices.1 h
  have h3 := hq.card_vertexOf k
  rw [hk, G.vertexOf_eq_of_mem hd, hi.2] at h3
  omega

/-- A face satisfying the conditions of a square move still does after a recolouring. -/
theorem IsSquareMoveFace.recolourLollipop {c : H} (hq : G.IsSquareMoveFace c) (i : Fin b) :
    (G.recolourLollipop i).IsSquareMoveFace c where
  faceOf_mem_internalFaces := hq.faceOf_mem_internalFaces
  facePerm_pow_four := hq.facePerm_pow_four
  vertexOf_mem_internalVertices := hq.vertexOf_mem_internalVertices
  injective := hq.injective
  card_vertexOf := hq.card_vertexOf
  colour_ne k := by
    have key : ∀ j, (G.recolourLollipop i).colour (G.squareCorner c j) =
        G.colour (G.squareCorner c j) := fun j =>
      colour_recolourLollipop_of_notMem fun h =>
        vertexOf_notMem_squareVertices hq h.1 h.2 (vertexOf_squareCorner_mem_squareVertices c j)
    change (G.recolourLollipop i).colour (G.squareCorner c k) ≠
      (G.recolourLollipop i).colour (G.squareCorner c (k + 1))
    rw [key, key]
    exact hq.colour_ne k

/-- **(Sq)** The square move commutes with a recolouring: `R_i` of the square move of `G` at `q`
is the square move of `R_i(G)` at `q`. -/
theorem recolourLollipop_squareMove {c : H} (hq : G.IsSquareMoveFace c) (i : Fin b) :
    (G.squareMove c).recolourLollipop i = (G.recolourLollipop i).squareMove c := by
  refine ext_of_colour rfl (funext fun d => ?_) rfl
  by_cases hP : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
      d ∈ G.vertexOf (G.inv (G.leg i))
  · have hQ := vertexOf_notMem_squareVertices hq hP.1 hP.2
    rw [colour_recolourLollipop_of_mem (G := G.squareMove c) hP.1 hP.2,
      colour_squareMove_of_notMem G hQ, colour_squareMove_of_notMem (G.recolourLollipop i) hQ,
      colour_recolourLollipop_of_mem hP.1 hP.2]
  · rw [colour_recolourLollipop_of_notMem (G := G.squareMove c) hP]
    by_cases hQ : G.vertexOf d ∈ G.squareVertices c
    · rw [colour_squareMove_of_mem G hQ, colour_squareMove_of_mem (G.recolourLollipop i) hQ,
        colour_recolourLollipop_of_notMem hP]
    · rw [colour_squareMove_of_notMem G hQ, colour_squareMove_of_notMem (G.recolourLollipop i) hQ,
        colour_recolourLollipop_of_notMem hP]

/-- In a nearly leafless plabic graph, a dart joining two internal vertices does not lie at the
vertex recoloured by `R_i`. -/
private theorem not_recoloured (hG : G.IsPlabicGraph) (hnl : G.IsNearlyLeafless) {x : H}
    (hx : ¬G.IsBoundaryVertex (G.vertexOf x)) (hx' : ¬G.IsBoundaryVertex (G.vertexOf (G.inv x)))
    (i : Fin b) :
    ¬(G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧ x ∈ G.vertexOf (G.inv (G.leg i))) := by
  rintro ⟨h, hmem⟩
  have h2 := hnl.two_le_card_vertexOf hG hx hx'
  rw [G.vertexOf_eq_of_mem hmem, h.2] at h2
  omega

section Bivalent

variable {d : H}

/-- The conditions of the removal of a bivalent vertex hold after a recolouring. -/
theorem IsBivalentRemovable.recolourLollipop (hd : G.IsBivalentRemovable d) (i : Fin b) :
    (G.recolourLollipop i).IsBivalentRemovable d :=
  ⟨hd.1, hd.2, hd.3⟩

/-- The vertex recoloured in the removal of a bivalent vertex is the vertex recoloured in `G`. -/
private theorem recoloured_bivalentRemoval_iff (hG : G.IsPlabicGraph) (hnl : G.IsNearlyLeafless)
    (hd : G.IsBivalentRemovable d) (i : Fin b) (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).IsInternalLeaf ((G.bivalentRemoval hG hd).vertexOf
        ((G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i))) ∧
      y ∈ (G.bivalentRemoval hG hd).vertexOf
        ((G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i))) ↔
      (G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
        (y : H) ∈ G.vertexOf (G.inv (G.leg i))) := by
  set K := G.bivalentRemoval hG hd
  set z := K.inv (K.leg i)
  have hinv := hG.inv_involutive
  have hvd : ¬G.IsBoundaryVertex (G.vertexOf d) := hd.not_isBoundaryVertex
  have hvrd : ¬G.IsBoundaryVertex (G.vertexOf (G.rot d)) := by rwa [G.vertexOf_rot]
  have hnot : ∀ x : H, ¬G.IsBoundaryVertex (G.vertexOf (G.inv x)) →
      ¬G.IsInternalLeaf (G.vertexOf x) := fun x hx hl => by
    have h2 := hnl.two_le_card_vertexOf hG (G.vertexOf_mem_internalVertices.1 hl.1) hx
    rw [hl.2] at h2
    omega
  have hleg : (K.leg i : H) = G.leg i := coe_bivalentRemoval_leg hG hd i
  by_cases h₁ : G.leg i = G.inv d
  · have hz : (z : H) = G.inv (G.rot d) :=
      coe_bivalentRemoval_inv_of_eq_inv hG hd (hleg.trans h₁)
    have hK : ¬K.IsInternalLeaf (K.vertexOf z) := by
      rw [isInternalLeaf_bivalentRemoval_vertexOf_iff, hz]
      exact hnot _ (by rwa [hinv])
    have hG' : ¬G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) := by
      rw [h₁, hinv]
      exact fun hl => by simpa [hd.card_vertexOf] using hl.2
    exact iff_of_false (fun h => hK h.1) fun h => hG' h.1
  by_cases h₂ : G.leg i = G.inv (G.rot d)
  · have hz : (z : H) = G.inv d :=
      coe_bivalentRemoval_inv_of_eq_inv_rot hG hd (hleg.trans h₂)
    have hK : ¬K.IsInternalLeaf (K.vertexOf z) := by
      rw [isInternalLeaf_bivalentRemoval_vertexOf_iff, hz]
      exact hnot _ (by rwa [hinv])
    have hG' : ¬G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) := by
      rw [h₂, hinv, G.vertexOf_rot]
      exact fun hl => by simpa [hd.card_vertexOf] using hl.2
    exact iff_of_false (fun h => hK h.1) fun h => hG' h.1
  have hz : (z : H) = G.inv (G.leg i) := by
    rw [coe_bivalentRemoval_inv_of_ne hG hd (by rwa [hleg]) (by rwa [hleg]), hleg]
  rw [isInternalLeaf_bivalentRemoval_vertexOf_iff, mem_bivalentRemoval_vertexOf, hz]

/-- **(Rem)** In a nearly leafless plabic graph, the removal of a bivalent vertex commutes with a
recolouring. -/
theorem bivalentRemoval_recolourLollipop (hG : G.IsPlabicGraph) (hnl : G.IsNearlyLeafless)
    (hd : G.IsBivalentRemovable d) (i : Fin b) :
    (G.recolourLollipop i).bivalentRemoval (hG.recolourLollipop i) (hd.recolourLollipop i) =
      (G.bivalentRemoval hG hd).recolourLollipop i := by
  refine ext_of_colour rfl (funext fun y => ?_) rfl
  have hc := recoloured_bivalentRemoval_iff hG hnl hd i y
  rw [bivalentRemoval_colour]
  by_cases hP : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
      (y : H) ∈ G.vertexOf (G.inv (G.leg i))
  · rw [colour_recolourLollipop_of_mem hP.1 hP.2,
      colour_recolourLollipop_of_mem (hc.2 hP).1 (hc.2 hP).2, bivalentRemoval_colour]
  · rw [colour_recolourLollipop_of_notMem hP, colour_recolourLollipop_of_notMem (mt hc.1 hP),
      bivalentRemoval_colour]

end Bivalent

section Contraction

variable {d : H}

/-- In a nearly leafless plabic graph, the conditions of the contraction of an edge hold after a
recolouring. -/
theorem IsContractibleEdge.recolourLollipop (hG : G.IsPlabicGraph) (hnl : G.IsNearlyLeafless)
    (he : G.IsContractibleEdge d) (i : Fin b) : (G.recolourLollipop i).IsContractibleEdge d where
  vertexOf_ne := he.vertexOf_ne
  mem_internalVertices := he.mem_internalVertices
  inv_mem_internalVertices := he.inv_mem_internalVertices
  colour_inv := by
    have hd := not_recoloured hG hnl he.not_isBoundaryVertex he.not_isBoundaryVertex_inv i
    have hd' := not_recoloured hG hnl (x := G.inv d) he.not_isBoundaryVertex_inv
      (by rw [hG.inv_involutive]; exact he.not_isBoundaryVertex) i
    change (G.recolourLollipop i).colour (G.inv d) = (G.recolourLollipop i).colour d
    rw [colour_recolourLollipop_of_notMem hd, colour_recolourLollipop_of_notMem hd']
    exact he.colour_inv

/-- **(Con)** In a nearly leafless plabic graph, the contraction of an edge commutes with a
recolouring. -/
theorem contractEdge_recolourLollipop (hG : G.IsPlabicGraph) (hnl : G.IsNearlyLeafless)
    (he : G.IsContractibleEdge d) (i : Fin b)
    (hleg : ∀ j, G.leg j ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.recolourLollipop i).contractEdge d hleg = (G.contractEdge d hleg).recolourLollipop i := by
  set K := G.contractEdge d hleg
  have hinv := hG.inv_involutive
  have h₁ := hnl.two_le_card_vertexOf hG he.not_isBoundaryVertex he.not_isBoundaryVertex_inv
  have h₂ := hnl.two_le_card_vertexOf_inv_of_isContractibleEdge hG he
  have hz : (K.inv (K.leg i) : H) = G.inv (G.leg i) := by
    rw [coe_contractEdge_inv hinv, coe_contractEdge_leg]
  have hc : ∀ y : (({d, G.inv d} : Set H)ᶜ : Set H),
      (K.IsInternalLeaf (K.vertexOf (K.inv (K.leg i))) ∧ y ∈ K.vertexOf (K.inv (K.leg i))) ↔
        (G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
          (y : H) ∈ G.vertexOf (G.inv (G.leg i))) := by
    intro y
    by_cases hU : G.inv (G.leg i) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · refine iff_of_false (fun h => ?_) fun h => ?_
      · exact (isInternalLeaf_of_isInternalLeaf_contractEdge he h₁ h₂ h.1).1 (hz ▸ hU)
      · have := h.1.2
        rcases mem_union.1 hU with hU | hU <;> rw [G.vertexOf_eq_of_mem hU] at this <;> omega
    · rw [← hz] at hU ⊢
      rw [isInternalLeaf_contractEdge_vertexOf_iff_of_notMem he hU,
        ← map_vertexOf_contractEdge_of_notMem (hleg := hleg) he.not_sameCycle hU, mem_map,
        Function.Embedding.coe_subtype]
      refine and_congr_right fun _ => ⟨fun h => ⟨y, h, rfl⟩, ?_⟩
      rintro ⟨y', hy', hyy'⟩
      rwa [← Subtype.ext hyy']
  refine ext_of_colour rfl (funext fun y => ?_) rfl
  rw [contractEdge_colour]
  by_cases hP : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
      (y : H) ∈ G.vertexOf (G.inv (G.leg i))
  · rw [colour_recolourLollipop_of_mem hP.1 hP.2,
      colour_recolourLollipop_of_mem ((hc y).2 hP).1 ((hc y).2 hP).2, contractEdge_colour]
  · rw [colour_recolourLollipop_of_notMem hP, colour_recolourLollipop_of_notMem (mt (hc y).1 hP),
      contractEdge_colour]

end Contraction

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- The **recolouring** `R_i(G)` of a bundled plabic graph at the label `i`: the plabic graph on
the darts of `G` whose data is `PlabicData.recolourLollipop`. -/
def recolourLollipop (G : PlabicGraph b) (i : Fin b) : PlabicGraph b :=
  ⟨G.Dart, G.data.recolourLollipop i, G.isPlabicGraph.recolourLollipop i⟩

/-- The data of the recolouring `R_i(G)` is the recolouring of the data of `G` at `i`. -/
@[simp]
theorem data_recolourLollipop (G : PlabicGraph b) (i : Fin b) :
    (G.recolourLollipop i).data = G.data.recolourLollipop i :=
  rfl

/-- **Recolouring commutes with local moves between nearly leafless graphs**: if `G` and `G'` are
nearly leafless plabic graphs such that `G'` is isomorphic to `G` or obtained from `G` by a local
move of a type in `S`, then `R_i(G')` is isomorphic to `R_i(G)` or obtained from `R_i(G)` by a
local move of the same type. -/
@[cluster_algebras "lem_recolouring_step"]
theorem MoveStep.recolourLollipop {S : Set LocalMoveType} {G G' : PlabicGraph b}
    (hG : G.data.IsNearlyLeafless) (hG' : G'.data.IsNearlyLeafless) (h : MoveStep S G G')
    (i : Fin b) : MoveStep S (G.recolourLollipop i) (G'.recolourLollipop i) := by
  rcases h with hθ | ⟨t, ht, h⟩
  · exact Or.inl (hθ.recolourLollipop G'.isPlabicGraph G.isPlabicGraph i)
  refine Or.inr ⟨t, ht, ?_⟩
  cases t with
  | m1 =>
    obtain ⟨c, hq, hθ⟩ := h
    refine ⟨c, hq.recolourLollipop i, ?_⟩
    have := hθ.recolourLollipop G'.isPlabicGraph (G.isPlabicGraph.squareMove c) i
    rwa [recolourLollipop_squareMove hq] at this
  | m2 =>
    rcases h with ⟨d, hd, hθ⟩ | ⟨d, hd, hθ⟩
    · refine Or.inl ⟨d, hd.recolourLollipop i, ?_⟩
      have := hθ.recolourLollipop G'.isPlabicGraph
        (isPlabicGraph_bivalentRemoval G.isPlabicGraph hd) i
      rwa [← bivalentRemoval_recolourLollipop G.isPlabicGraph hG hd i] at this
    · refine Or.inr ⟨d, hd.recolourLollipop i, ?_⟩
      have := hθ.recolourLollipop G.isPlabicGraph
        (isPlabicGraph_bivalentRemoval G'.isPlabicGraph hd) i
      rwa [← bivalentRemoval_recolourLollipop G'.isPlabicGraph hG' hd i] at this
  | m3 =>
    rcases h with ⟨d, he, hθ⟩ | ⟨d, he, hθ⟩
    · refine Or.inl ⟨d, he.recolourLollipop G.isPlabicGraph hG i, ?_⟩
      have := hθ.recolourLollipop G'.isPlabicGraph
        (G.isPlabicGraph.contractEdge (hleg := he.leg_mem G.isPlabicGraph) he) i
      rwa [← contractEdge_recolourLollipop G.isPlabicGraph hG he i] at this
    · refine Or.inr ⟨d, he.recolourLollipop G'.isPlabicGraph hG' i, ?_⟩
      have := hθ.recolourLollipop G.isPlabicGraph
        (G'.isPlabicGraph.contractEdge (hleg := he.leg_mem G'.isPlabicGraph) he) i
      rwa [← contractEdge_recolourLollipop G'.isPlabicGraph hG' he i] at this

/-! ### Normalization -/

/-- A **step of a normalization**: `G'` is isomorphic to `G` or obtained from `G` by a local move,
or `G` is nearly leafless and `G' = R_i(G)` for some label `i`. -/
@[cluster_algebras "def_normalization"]
def NormalizationStep (G G' : PlabicGraph b) : Prop :=
  MoveStep Set.univ G G' ∨ (G.data.IsNearlyLeafless ∧ ∃ i, G' = G.recolourLollipop i)

/-- A normal plabic graph `N` is a **normalization** of `G` if there is a finite sequence
`G = G₀, G₁, …, G_r = N` of plabic graphs such that for every `t ∈ [1, r]` either `G_t` is
isomorphic to `G_{t-1}` or obtained from `G_{t-1}` by a local move, or `G_{t-1}` is nearly
leafless and `G_t = R_i(G_{t-1})` for some label `i`. -/
@[cluster_algebras "def_normalization"]
def IsNormalization (G N : PlabicGraph b) : Prop :=
  N.data.IsNormal ∧ Relation.ReflTransGen NormalizationStep G N

end PlabicGraph

end ClusterAlgebras
