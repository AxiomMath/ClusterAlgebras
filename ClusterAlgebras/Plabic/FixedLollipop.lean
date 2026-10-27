/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.LollipopMoves

/-!
# Lollipops, reducedness and decorated trip permutations

Let `A` be a plabic graph with `b ≥ 1` boundary vertices and `I_i(A, c)` the insertion of a
lollipop of colour `c` at the label `i`. The vertices of `A` are vertices of `I_i(A, c)`, with the
same darts, rotation and colours, and the involutions agree away from the boundary arcs. A hollow
digon or an internal leaf of `A` is therefore one of `I_i(A, c)`; an internal leaf of `A` that is
a lollipop or a non-root vertex of a collapsible tree in `I_i(A, c)` is already so in `A`, since a
rooted tree of `I_i(A, c)` containing a vertex of `A` cannot use the new vertices `ν` and `{ḡ°}`.
As inserting a lollipop commutes with local moves, `A` is reduced as soon as `I_i(A, c)` is.

Likewise, the lollipops and the collapsible trees at `β(j)` are the same in `A` and at `β(j⁺)` in
`I_i(A, c)`, so the decorations of `A` and of `I_i(A, c)` agree on the fixed points, and the
decorated trip permutation of `A` is determined by that of `I_i(A, c)`.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.of_lollipopInsertion`: if `I_i(A, c)` is reduced, then
  `A` is reduced.
* `ClusterAlgebras.PlabicData.decoratedTripPerm_eq_of_lollipopInsertion`: if
  `π̃_{I_i(A, c)} = π̃_{I_i(A', c)}`, then `π̃_A = π̃_{A'}`.

## Implementation notes

* Labels are `0`-indexed: `i : Fin (b + 1)` is FWZ's label `i + 1`, and the relabelling
  `j ↦ j⁺` is `Fin.succAbove i`.
* The darts of `I_i(A, c)` are `H ⊕ Fin 4`; a set of darts `s` of `A` is read in `I_i(A, c)` as
  `s.map Sum.inl`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

section Insertion

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} [NeZero b] {A : PlabicData H b}
  {i : Fin (b + 1)} {c : Shade}

omit [Fintype H] in
/-- Every element of `Fin 4` is one of `0, 1, 2, 3`. -/
private theorem fin_four_cases' (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  fin_cases k <;> simp

/-- The darts at the vertex of a new dart of `I_i(A, c)` are new darts. -/
private theorem exists_inr_of_mem_vertexOf_inr {k : Fin 4} {z : H ⊕ Fin 4}
    (hz : z ∈ (A.lollipopInsertion i c).vertexOf (Sum.inr k)) : ∃ l, z = Sum.inr l := by
  obtain rfl | hk := eq_or_ne k 3
  · rw [lollipopInsertion_vertexOf_inr_three (A := A) (i := i) (c := c), mem_singleton] at hz
    exact ⟨3, hz⟩
  · rw [lollipopInsertion_vertexOf_inr_of_ne (A := A) (i := i) c hk] at hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- An edge of `I_i(A, c)` outside `B` at a new vertex leads to a new vertex. -/
private theorem treeAdj_vertexOf_inr {W : Finset (Finset (H ⊕ Fin 4))} {u u' : Finset (H ⊕ Fin 4)}
    (h : (A.lollipopInsertion i c).TreeAdj W u u')
    (hu : ∃ k, u = (A.lollipopInsertion i c).vertexOf (Sum.inr k)) :
    ∃ k, u' = (A.lollipopInsertion i c).vertexOf (Sum.inr k) := by
  obtain ⟨d, hd, rfl, rfl⟩ := h
  obtain ⟨k, hk⟩ := hu
  obtain ⟨l, rfl⟩ :=
    exists_inr_of_mem_vertexOf_inr (hk ▸ (A.lollipopInsertion i c).self_mem_vertexOf d)
  have hdB := (mem_treeDarts.1 hd).1
  rw [mem_lollipopInsertion_bdry_inr] at hdB
  rcases fin_four_cases' l with rfl | rfl | rfl | rfl
  · exact absurd (Or.inl rfl) hdB
  · exact absurd (Or.inr rfl) hdB
  · exact ⟨3, by rw [lollipopInsertion_inv_inr_two]⟩
  · exact ⟨2, by rw [lollipopInsertion_inv_inr_three]⟩

/-- A rooted tree of `I_i(A, c)` one of whose vertices contains a dart of `A` has a vertex of `A`
as its root. -/
private theorem RootedTree.exists_root_eq_map_inl (T : (A.lollipopInsertion i c).RootedTree)
    {u : Finset (H ⊕ Fin 4)} (hu : u ∈ insert T.root T.nonRoot) {x : H} (hx : Sum.inl x ∈ u) :
    ∃ s : Finset H, T.root = s.map Function.Embedding.inl := by
  obtain ⟨z, hz⟩ := (A.lollipopInsertion i c).mem_vertices.1 T.root_mem_vertices
  rcases z with y | k
  · exact ⟨A.vertexOf y, by rw [← hz, lollipopInsertion_vertexOf_inl]⟩
  · exfalso
    have key : ∀ u', Relation.ReflTransGen ((A.lollipopInsertion i c).TreeAdj T.nonRoot) T.root u' →
        ∃ l, u' = (A.lollipopInsertion i c).vertexOf (Sum.inr l) := by
      intro u' h
      induction h with
      | refl => exact ⟨k, hz.symm⟩
      | tail _ hadj ih => exact treeAdj_vertexOf_inr hadj ih
    obtain ⟨l, rfl⟩ := key u (T.reflTransGen_treeAdj u hu)
    obtain ⟨m, hm⟩ := exists_inr_of_mem_vertexOf_inr hx
    exact Sum.inl_ne_inr hm

/-- A rooted tree of `I_i(A, c)` whose root is a vertex of `A` has vertices of `A` as its non-root
vertices. -/
private theorem RootedTree.exists_nonRoot_eq_image (T : (A.lollipopInsertion i c).RootedTree)
    {s : Finset H} (hs : T.root = s.map Function.Embedding.inl) :
    ∃ W : Finset (Finset H),
      T.nonRoot = W.image (Finset.map (Function.Embedding.inl : H ↪ H ⊕ Fin 4)) := by
  have hint : ∀ w ∈ T.nonRoot, w ∈ (A.lollipopInsertion i c).internalVertices :=
    fun w hw => T.nonRoot_subset hw
  have hw : ∀ w ∈ T.nonRoot, ∃ t ∈ A.vertices, w = t.map Function.Embedding.inl := by
    intro w hw
    obtain ⟨z, hz⟩ := (A.lollipopInsertion i c).mem_vertices.1
      ((DiskMap.mem_internalVertices _).1 (hint w hw)).1
    rcases z with y | k
    · exact ⟨A.vertexOf y, A.vertexOf_mem_vertices y, by rw [← hz, lollipopInsertion_vertexOf_inl]⟩
    · exfalso
      obtain rfl | hk := eq_or_ne k 3
      · have := T.vertexOf_inv_mem (Sum.inr 3) (hz ▸ hw)
        rw [lollipopInsertion_inv_inr_three] at this
        rcases mem_insert.1 this with h | h
        · have h2 := (A.lollipopInsertion i c).self_mem_vertexOf (Sum.inr 2)
          rw [h, hs] at h2
          simp at h2
        · exact ((DiskMap.mem_internalVertices _).1 (hint _ h)).2
            (isBoundaryVertex_lollipopInsertion_vertexOf_inr_of_ne (k := 2) c (by decide))
      · exact ((DiskMap.mem_internalVertices _).1 (hint w hw)).2
          (hz ▸ isBoundaryVertex_lollipopInsertion_vertexOf_inr_of_ne c hk)
  refine ⟨A.vertices.filter fun t => t.map Function.Embedding.inl ∈ T.nonRoot, ?_⟩
  ext w
  simp only [mem_image, mem_filter]
  refine ⟨fun h => ?_, fun ⟨t, ⟨_, ht⟩, e⟩ => e ▸ ht⟩
  obtain ⟨t, ht, rfl⟩ := hw w h
  exact ⟨t, ⟨ht, h⟩, rfl⟩

/-- A vertex of `A` is a lollipop at `j` iff it is a lollipop at `j⁺` of `I_i(A, c)`. -/
theorem isLollipop_lollipopInsertion_map_inl_iff (hA : A.IsPlabicGraph) (j : Fin b)
    {v : Finset H} :
    (A.lollipopInsertion i c).IsLollipop (i.succAbove j) (v.map Function.Embedding.inl) ↔
      A.IsLollipop j v := by
  unfold IsLollipop DiskMap.IsInternalLeaf
  rw [map_inl_mem_lollipopInsertion_internalVertices, card_map,
    lollipopInsertion_bvertex_succAbove]
  refine and_congr_right fun ⟨hv, _⟩ => ?_
  simp only [mem_map, Function.Embedding.inl_apply]
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, h⟩
    rw [lollipopInsertion_inv_inl_of_notMem_bdry hA
      (fun h => ((DiskMap.mem_internalVertices _).1 hv).2 ⟨d, hd, h⟩)] at h
    obtain ⟨y, hy, hyd⟩ := h
    exact ⟨d, hd, Sum.inl_injective hyd ▸ hy⟩
  · rintro ⟨d, hd, h⟩
    refine ⟨_, ⟨d, hd, rfl⟩, ?_⟩
    rw [lollipopInsertion_inv_inl_of_notMem_bdry hA
      (fun h => ((DiskMap.mem_internalVertices _).1 hv).2 ⟨d, hd, h⟩)]
    exact ⟨_, h, rfl⟩

/-- A vertex of `A` is not a lollipop at the new label `i` of `I_i(A, c)`. -/
theorem not_isLollipop_lollipopInsertion_self_map_inl (hA : A.IsPlabicGraph) {v : Finset H} :
    ¬(A.lollipopInsertion i c).IsLollipop i (v.map Function.Embedding.inl) := by
  rintro ⟨⟨hv, -⟩, d, hd, h⟩
  obtain ⟨x, hx, rfl⟩ := mem_map.1 hd
  rw [map_inl_mem_lollipopInsertion_internalVertices] at hv
  rw [Function.Embedding.inl_apply, lollipopInsertion_inv_inl_of_notMem_bdry hA
    (fun h => ((DiskMap.mem_internalVertices _).1 hv).2 ⟨x, hx, h⟩),
    lollipopInsertion_bvertex_self] at h
  simp at h

/-- The new leaf `{ḡ°}` of `I_i(A, c)` is not a lollipop at a label `j⁺`. -/
theorem not_isLollipop_lollipopInsertion_succAbove_singleton (j : Fin b) :
    ¬(A.lollipopInsertion i c).IsLollipop (i.succAbove j) {Sum.inr 3} := by
  rintro ⟨-, d, hd, h⟩
  obtain rfl := mem_singleton.1 hd
  rw [lollipopInsertion_inv_inr_three, lollipopInsertion_bvertex_succAbove] at h
  simp at h

/-- An internal vertex of `I_i(A, c)` is an internal vertex of `A` or the new leaf `{ḡ°}`. -/
theorem eq_map_inl_or_eq_of_mem_lollipopInsertion_internalVertices
    {v : Finset (H ⊕ Fin 4)} (hv : v ∈ (A.lollipopInsertion i c).internalVertices) :
    (∃ s ∈ A.internalVertices, v = s.map Function.Embedding.inl) ∨ v = {Sum.inr 3} := by
  have hv' := (DiskMap.mem_internalVertices _).1 hv
  have h := hv'.1
  rw [lollipopInsertion_vertices] at h
  simp only [mem_union, mem_image, mem_insert, mem_singleton] at h
  rcases h with ⟨s, hs, rfl⟩ | rfl | rfl
  · exact Or.inl ⟨s, map_inl_mem_lollipopInsertion_internalVertices.1 hv, rfl⟩
  · exact absurd ⟨Sum.inr 0, by simp, by simp⟩ hv'.2
  · exact Or.inr rfl

/-- `A` has a lollipop of colour `s` at `j` iff `I_i(A, c)` has one at `j⁺`. -/
theorem exists_isLollipopOfColour_lollipopInsertion_succAbove_iff (hA : A.IsPlabicGraph)
    (j : Fin b) (s : Shade) :
    (∃ v, (A.lollipopInsertion i c).IsLollipopOfColour (i.succAbove j) s v) ↔
      ∃ v, A.IsLollipopOfColour j s v := by
  constructor
  · rintro ⟨v, hv, hcol⟩
    rcases eq_map_inl_or_eq_of_mem_lollipopInsertion_internalVertices hv.1.1 with
      ⟨t, -, rfl⟩ | rfl
    · exact ⟨t, (isLollipop_lollipopInsertion_map_inl_iff hA j).1 hv, fun d hd =>
        hcol _ (mem_map_of_mem _ hd)⟩
    · exact absurd hv (not_isLollipop_lollipopInsertion_succAbove_singleton j)
  · rintro ⟨v, hv, hcol⟩
    refine ⟨v.map Function.Embedding.inl, (isLollipop_lollipopInsertion_map_inl_iff hA j).2 hv,
      fun d hd => ?_⟩
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hd
    exact hcol x hx

/-- `A` has a collapsible tree of colour `c'` rooted at `β(j)` iff `I_i(A, c)` has one rooted at
`β(j⁺)`. -/
theorem exists_isCollapsibleOfColour_bvertex_lollipopInsertion_iff (hA : A.IsPlabicGraph)
    (j : Fin b) (c' : Shade) :
    (∃ T : (A.lollipopInsertion i c).RootedTree,
        T.root = (A.lollipopInsertion i c).bvertex (i.succAbove j) ∧ T.IsCollapsibleOfColour c') ↔
      ∃ T : A.RootedTree, T.root = A.bvertex j ∧ T.IsCollapsibleOfColour c' := by
  constructor
  · rintro ⟨T, hT, hc⟩
    rw [lollipopInsertion_bvertex_succAbove] at hT
    obtain ⟨W, hW⟩ := RootedTree.exists_nonRoot_eq_image T hT
    obtain ⟨T₀, h₀, -, hc₀⟩ :=
      (exists_isCollapsibleOfColour_lollipopInsertion_iff hA (A.bvertex j) W c').2 ⟨T, hT, hW, hc⟩
    exact ⟨T₀, h₀, hc₀⟩
  · rintro ⟨T, hT, hc⟩
    obtain ⟨T', h', -, hc'⟩ :=
      (exists_isCollapsibleOfColour_lollipopInsertion_iff (i := i) (c := c) hA (A.bvertex j)
        T.nonRoot c').1 ⟨T, hT, rfl, hc⟩
    exact ⟨T', by rw [h', lollipopInsertion_bvertex_succAbove], hc'⟩

/-- `j⁺` is white-decorated in `I_i(A, c)` iff `j` is white-decorated in `A`. -/
theorem isWhiteDecorated_lollipopInsertion_succAbove_iff (hA : A.IsPlabicGraph) (j : Fin b) :
    (A.lollipopInsertion i c).IsWhiteDecorated (i.succAbove j) ↔ A.IsWhiteDecorated j :=
  or_congr (exists_isLollipopOfColour_lollipopInsertion_succAbove_iff hA j _)
    (exists_isCollapsibleOfColour_bvertex_lollipopInsertion_iff hA j _)

/-- The decoration of `I_i(A, c)` at `j⁺` is that of `A` at `j`. -/
theorem tripDecoration_lollipopInsertion_succAbove (hA : A.IsPlabicGraph) (j : Fin b)
    (h : (A.lollipopInsertion i c).tripPerm (i.succAbove j) = i.succAbove j)
    (h' : A.tripPerm j = j) :
    (A.lollipopInsertion i c).tripDecoration ⟨i.succAbove j, h⟩ = A.tripDecoration ⟨j, h'⟩ := by
  by_cases hw : A.IsWhiteDecorated j
  · have h₁ := (tripDecoration_eq_white_iff (G := A.lollipopInsertion i c)
      ⟨i.succAbove j, h⟩).2 ((isWhiteDecorated_lollipopInsertion_succAbove_iff hA j).2 hw)
    have h₂ := (tripDecoration_eq_white_iff (G := A) ⟨j, h'⟩).2 hw
    exact h₁.trans h₂.symm
  · have h₁ := (tripDecoration_eq_black_iff (G := A.lollipopInsertion i c)
      ⟨i.succAbove j, h⟩).2 ((isWhiteDecorated_lollipopInsertion_succAbove_iff hA j).not.2 hw)
    have h₂ := (tripDecoration_eq_black_iff (G := A) ⟨j, h'⟩).2 hw
    exact h₁.trans h₂.symm

private theorem _root_.ClusterAlgebras.DecoratedPerm.colour_congr {n : ℕ}
    {π σ : DecoratedPerm n} (h : π = σ) (k : Fin n) (hπ : π.perm k = k) (hσ : σ.perm k = k) :
    π.colour ⟨k, hπ⟩ = σ.colour ⟨k, hσ⟩ := by
  subst h
  rfl

/-- If `A` and `A'` are plabic graphs with `b` boundary vertices and the decorated trip
permutations of `I_i(A, c)` and `I_i(A', c)` agree, then so do those of `A` and `A'`. The
decorated trip permutations are formed from any proofs that the trip permutations are
bijections. -/
@[cluster_algebras "lem_lollipop_insertion_dpi"]
theorem decoratedTripPerm_eq_of_lollipopInsertion {H' : Type} [Fintype H'] [DecidableEq H']
    {A' : PlabicData H' b} (hA : A.IsPlabicGraph) (hA' : A'.IsPlabicGraph)
    (hπ : Function.Bijective A.tripPerm) (hπ' : Function.Bijective A'.tripPerm)
    (hπI : Function.Bijective (A.lollipopInsertion i c).tripPerm)
    (hπI' : Function.Bijective (A'.lollipopInsertion i c).tripPerm)
    (h : (A.lollipopInsertion i c).decoratedTripPerm hπI =
      (A'.lollipopInsertion i c).decoratedTripPerm hπI') :
    A.decoratedTripPerm hπ = A'.decoratedTripPerm hπ' := by
  have hperm : ∀ k, (A.lollipopInsertion i c).tripPerm k = (A'.lollipopInsertion i c).tripPerm k :=
    fun k => by
      rw [← decoratedTripPerm_perm_apply hπI, ← decoratedTripPerm_perm_apply hπI', h]
  have hj : ∀ j, A.tripPerm j = A'.tripPerm j := fun j =>
    Fin.succAbove_right_injective (p := i) (by
      rw [← tripPerm_lollipopInsertion_succAbove hA, ← tripPerm_lollipopInsertion_succAbove hA',
        hperm])
  refine DecoratedPerm.ext (Equiv.ext hj) fun j hj₁ hj₂ => ?_
  rw [decoratedTripPerm_perm_apply] at hj₁ hj₂
  have hI : (A.lollipopInsertion i c).tripPerm (i.succAbove j) = i.succAbove j := by
    rw [tripPerm_lollipopInsertion_succAbove hA, hj₁]
  have hI' : (A'.lollipopInsertion i c).tripPerm (i.succAbove j) = i.succAbove j := by
    rw [tripPerm_lollipopInsertion_succAbove hA', hj₂]
  rw [decoratedTripPerm_colour, decoratedTripPerm_colour,
    ← tripDecoration_lollipopInsertion_succAbove hA j hI hj₁,
    ← tripDecoration_lollipopInsertion_succAbove hA' j hI' hj₂]
  exact DecoratedPerm.colour_congr h (i.succAbove j) hI hI'

/-! ### Hollow digons and leaves of an insertion -/

/-- The face of `I_i(A, c)` through a dart of an internal face of `A` is that face. -/
theorem lollipopInsertion_faceOf_inl (hA : A.IsPlabicGraph) {x : H}
    (hx : Disjoint (A.faceOf x) A.bdry) :
    (A.lollipopInsertion i c).faceOf (Sum.inl x) = (A.faceOf x).map Function.Embedding.inl := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, rfl⟩ := ((RotationSystem.mem_faceOf _).1 hz).exists_nat_pow_eq
    rw [lollipopInsertion_facePerm_pow_inl hA hx]
    exact mem_map_of_mem _ ((RotationSystem.mem_faceOf _).2 ⟨n, by rw [zpow_natCast]⟩)
  · intro hz
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hz
    obtain ⟨n, rfl⟩ := ((RotationSystem.mem_faceOf _).1 hy).exists_nat_pow_eq
    rw [Function.Embedding.inl_apply, ← lollipopInsertion_facePerm_pow_inl hA hx]
    exact (RotationSystem.mem_faceOf _).2 ⟨n, by rw [zpow_natCast]⟩

/-- A hollow digon of `A` is a hollow digon of `I_i(A, c)`. -/
theorem isHollowDigon_lollipopInsertion_map_inl (hA : A.IsPlabicGraph) {f : Finset H}
    (hf : A.IsHollowDigon f) :
    (A.lollipopInsertion i c).IsHollowDigon (f.map Function.Embedding.inl) := by
  obtain ⟨hfI, d₁, d₂, rfl, hne⟩ := hf
  obtain ⟨hfF, hdisj⟩ := (DiskMap.mem_internalFaces _).1 hfI
  obtain ⟨d, hd⟩ := (RotationSystem.mem_faceOrbits _).1 ((DiskMap.mem_faces _).1 hfF).2
  have h₁ : A.faceOf d₁ = {d₁, d₂} := by
    rw [← hd, RotationSystem.faceOf_eq_of_mem]
    exact hd ▸ mem_insert_self _ _
  have hd₁ : d₁ ∉ A.bdry := disjoint_left.1 hdisj (mem_insert_self _ _)
  have hface := lollipopInsertion_faceOf_inl (i := i) (c := c) hA (h₁ ▸ hdisj)
  rw [h₁] at hface
  refine ⟨(DiskMap.mem_internalFaces _).2 ⟨?_, ?_⟩, Sum.inl d₁, Sum.inl d₂, by simp, ?_⟩
  · rw [← hface]
    exact DiskMap.faceOf_mem_faces _ (by rwa [mem_lollipopInsertion_bdry_inl])
  · rw [disjoint_left]
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hz
    rw [Function.Embedding.inl_apply, mem_lollipopInsertion_bdry_inl]
    exact disjoint_left.1 hdisj hy
  · rw [lollipopInsertion_vertexOf_inl, lollipopInsertion_vertexOf_inl]
    exact fun h => hne (Finset.map_injective _ h)

end Insertion

end PlabicData

namespace PlabicGraph

variable {b : ℕ} [NeZero b]

open PlabicData

/-- If `A` is a plabic graph with `b ≥ 1` boundary vertices and the insertion `I_i(A, c)` of a
lollipop is reduced, then `A` is reduced. -/
@[cluster_algebras "lem_lollipop_insertion_reduced"]
theorem IsReduced.of_lollipopInsertion {A : PlabicGraph b} {i : Fin (b + 1)} {c : Shade}
    (h : (A.lollipopInsertion i c).IsReduced) : A.IsReduced := by
  intro A'' hA''
  have hA := A''.isPlabicGraph
  obtain ⟨hdigon, hleaf⟩ := h (A''.lollipopInsertion i c) (hA''.lollipopInsertion i c)
  refine ⟨fun f hf => hdigon _
    (isHollowDigon_lollipopInsertion_map_inl (i := i) (c := c) hA hf), fun v hv => ?_⟩
  have hvI : (A''.data.lollipopInsertion i c).IsInternalLeaf (v.map Function.Embedding.inl) :=
    ⟨map_inl_mem_lollipopInsertion_internalVertices.2 hv.1, (card_map _).trans hv.2⟩
  rcases hleaf _ hvI with ⟨k, hk⟩ | ⟨T, ⟨c', hc⟩, hvT⟩
  · rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · exact absurd hk (not_isLollipop_lollipopInsertion_self_map_inl hA)
    · exact Or.inl ⟨j, (isLollipop_lollipopInsertion_map_inl_iff hA j).1 hk⟩
  · right
    obtain ⟨x, hx⟩ := card_pos.1 (hv.2 ▸ Nat.one_pos)
    obtain ⟨s, hs⟩ := RootedTree.exists_root_eq_map_inl T (mem_insert_of_mem hvT)
      (mem_map_of_mem Function.Embedding.inl hx)
    obtain ⟨W, hW⟩ := RootedTree.exists_nonRoot_eq_image T hs
    obtain ⟨T₀, -, hW₀, hc₀⟩ :=
      (exists_isCollapsibleOfColour_lollipopInsertion_iff hA s W c').2 ⟨T, hs, hW, hc⟩
    refine ⟨T₀, hc₀.isCollapsible, ?_⟩
    rwa [hW₀, ← map_inl_mem_image_map_inl, ← hW]

end PlabicGraph

end ClusterAlgebras
