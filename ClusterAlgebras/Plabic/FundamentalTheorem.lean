/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FixedLollipopProp
public import ClusterAlgebras.Plabic.ExcisionLemmas
public import ClusterAlgebras.Plabic.MinimalTheorems
public import ClusterAlgebras.Plabic.ReducedCollapse
public import ClusterAlgebras.Plabic.TreeCollapse
public import ClusterAlgebras.Plabic.External

/-!
# The fundamental theorem of reduced plabic graphs

Two reduced plabic graphs `G` and `G'` with the same number `b` of boundary vertices are
move-equivalent if and only if they have the same decorated trip permutation `π̃_G = π̃_{G'}`.

The forward implication is the invariance of the decorated trip permutation of a reduced graph
under local moves. The converse is proved by induction on `b`.

* If `π_G = π_{G'}` has a fixed point `i`, then `G` has a lollipop at `i` or a collapsible tree
  with root `β(i)`; collapsing the tree, `G` is move-equivalent to a reduced graph `G₁` with a
  lollipop at `i`, whose colour is the decoration `ε_G(i)`, since no rooted tree with root `β(i)`
  is then collapsible. The same holds for `G'`, with the same colour `ε = ε_G(i) = ε_{G'}(i)`.
  For `b = 1` both `G₁` and `G'₁` are isomorphic to the lollipop graph `L_ε`. For `b ≥ 2`, the
  graphs `G₁`, `G'₁` are isomorphic to lollipop insertions `I_i(A, ε)`, `I_i(A', ε)` of reduced
  graphs `A`, `A'` with `b - 1` boundary vertices and `π̃_A = π̃_{A'}`; by induction `A ∼ A'`, so
  `I_i(A, ε) ∼ I_i(A', ε)`.
* If `π_G` has no fixed point, then `G` and `G'` are move-equivalent to nearly leafless graphs
  without lollipops, hence to normal plabic graphs `N`, `N'`. Their triple diagrams are minimal
  with the same strand permutation `π_G = π_{G'}`, hence move-equivalent, so `N ∼ N'`.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.moveEquivalent_iff_decoratedTripPerm_eq`: the fundamental
  theorem of reduced plabic graphs.
* `ClusterAlgebras.PlabicData.IsLollipopOfColour.isWhiteDecorated_iff`: a fixed point carrying a
  lollipop is decorated by the colour of the lollipop.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is the label `i + 1` of [FWZ].
* The decorated trip permutations are formed from any proofs that the trip permutations are
  bijections; the statement does not depend on these proofs.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- If `G` has a lollipop `u` at `i`, then a rooted tree of `G` with root `β(i)` has no non-root
vertex other than `u`: the only dart of `β(i)` outside `B` is the leg `g_i`, and the only dart of
`u` is `ḡ_i`. -/
theorem RootedTree.nonRoot_subset_singleton_of_isLollipop (hG : G.IsPlabicGraph) {i : Fin b}
    {u : Finset H} (hu : G.IsLollipop i u) (T : G.RootedTree) (hT : T.root = G.bvertex i) :
    T.nonRoot ⊆ {u} := by
  have hu' := hu.eq_singleton_inv_leg hG
  have hvu : G.vertexOf (G.inv (G.leg i)) = u := by
    obtain ⟨y, hy⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hu.1.1).1
    rw [← hy]
    exact G.vertexOf_eq_of_mem (by rw [hy, hu']; exact mem_singleton_self _)
  have key : ∀ y, Relation.ReflTransGen (G.TreeAdj T.nonRoot) T.root y → y = T.root ∨ y = u := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | tail _ hxy ih =>
      obtain ⟨d, hd, hdx, rfl⟩ := hxy
      rcases ih with hx | hx
      · have hdl : d = G.leg i := by
          have hmem : d ∈ (G.bvertex i).filter (· ∉ G.bdry) :=
            mem_filter.2 ⟨by rw [← hT, ← hx, ← hdx]; exact G.self_mem_vertexOf d,
            (G.mem_treeDarts.1 hd).1⟩
          rwa [hG.filter_bvertex_notMem_bdry, mem_singleton] at hmem
        right
        rw [hdl, hvu]
      · have hdl : d = G.inv (G.leg i) := by
          have hmem : d ∈ u := by rw [← hx, ← hdx]; exact G.self_mem_vertexOf d
          rwa [hu', mem_singleton] at hmem
        left
        rw [hdl, hG.inv_involutive, hT]
        rfl
  intro w hw
  rcases key w (T.reflTransGen_treeAdj w (mem_insert_of_mem hw)) with h | h
  · exact absurd (h ▸ hw) T.root_notMem_nonRoot
  · exact h ▸ mem_singleton_self _

/-- **A lollipop decorates its fixed point by its colour**: if `G` has a lollipop of colour `c`
at `i`, then `i` is white for the decoration of `G` exactly when `c` is white. -/
theorem IsLollipopOfColour.isWhiteDecorated_iff (hG : G.IsPlabicGraph) {i : Fin b} {c : Shade}
    {u : Finset H} (hu : G.IsLollipopOfColour i c u) : G.IsWhiteDecorated i ↔ c = .white := by
  have hu' := hu.1.eq_singleton_inv_leg hG
  constructor
  · rintro (⟨v, hv⟩ | ⟨T, hT, hc⟩)
    · have hv' := hv.1.eq_singleton_inv_leg hG
      exact (hu.2 _ (by rw [hu']; exact mem_singleton_self _)).symm.trans
        (hv.2 _ (by rw [hv']; exact mem_singleton_self _))
    · exfalso
      have hbv : G.IsBoundaryVertex (G.bvertex i) :=
        G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
      rcases hc.root_cases with ⟨hb, -⟩ | ⟨-, h2⟩
      · rw [hT] at hb
        exact hb hbv
      · have := card_le_card (T.nonRoot_subset_singleton_of_isLollipop hG hu.1 hT)
        rw [card_singleton] at this
        omega
  · rintro rfl
    exact Or.inl ⟨u, hu⟩

/-- If `G` has a lollipop of colour `c` at the fixed point `i` of `π_G`, then `ε_G(i) = c`. -/
theorem IsLollipopOfColour.tripDecoration_eq (hG : G.IsPlabicGraph) {i : Fin b} {c : Shade}
    {u : Finset H} (hu : G.IsLollipopOfColour i c u) (hi : G.tripPerm i = i) :
    G.tripDecoration ⟨i, hi⟩ = c := by
  cases c
  · exact (tripDecoration_eq_white_iff (G := G) ⟨i, hi⟩).2 ((hu.isWhiteDecorated_iff hG).2 rfl)
  · exact (tripDecoration_eq_black_iff (G := G) ⟨i, hi⟩).2
      (mt (hu.isWhiteDecorated_iff hG).1 nofun)

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- Equal decorated permutations have equal colours at a common fixed point. -/
private theorem colour_congr_of_eq {π σ : DecoratedPerm b} (h : π = σ) (k : Fin b)
    (hπ : π.perm k = k) (hσ : σ.perm k = k) : π.colour ⟨k, hπ⟩ = σ.colour ⟨k, hσ⟩ := by
  subst h
  rfl

/-- Move-equivalent reduced graphs have the same decoration at a common fixed point. -/
private theorem tripDecoration_eq_of_moveEquivalent {G G' : PlabicGraph b} (hG : G.IsReduced)
    (h : MoveEquivalent Set.univ G G') (i : Fin b) (hi : G.data.tripPerm i = i)
    (hi' : G'.data.tripPerm i = i) :
    G.data.tripDecoration ⟨i, hi⟩ = G'.data.tripDecoration ⟨i, hi'⟩ :=
  colour_congr_of_eq (hG.decoratedTripPerm_eq h G.isPlabicGraph.tripPerm_bijective
    G'.isPlabicGraph.tripPerm_bijective) i hi hi'

/-- A reduced graph `G` with a fixed point `i` of `π_G` is move-equivalent to a graph with a
lollipop of colour `ε_G(i)` at `i`. -/
private theorem exists_moveEquivalent_isLollipopOfColour {G : PlabicGraph b} (hG : G.IsReduced)
    {i : Fin b} (hi : G.data.tripPerm i = i) :
    ∃ G₁ : PlabicGraph b, MoveEquivalent Set.univ G G₁ ∧
      ∃ u, G₁.data.IsLollipopOfColour i (G.data.tripDecoration ⟨i, hi⟩) u := by
  have key : ∃ G₁ : PlabicGraph b, MoveEquivalent Set.univ G G₁ ∧ ∃ u, G₁.data.IsLollipop i u := by
    rcases hG.exists_isLollipop_or_isCollapsible_of_tripPerm_eq_self hi with
      ⟨u, hu⟩ | ⟨T, hT, c, hc⟩
    · exact ⟨G, .refl _ _, u, hu⟩
    · obtain ⟨h1, hmove⟩ := hc.moveEquivalent_collapse G.isPlabicGraph
      obtain ⟨u, hu⟩ := T.exists_isLollipop_collapse G.isPlabicGraph c hT
      exact ⟨⟨_, _, h1⟩, hmove.mono (Set.subset_univ _), u, hu⟩
  obtain ⟨G₁, hGG₁, u, hu⟩ := key
  have hc : G₁.data.IsLollipopOfColour i (G₁.data.colour (G₁.data.inv (G₁.data.leg i))) u :=
    ⟨hu, fun d hd => by
      rw [hu.eq_singleton_inv_leg G₁.isPlabicGraph, mem_singleton] at hd
      rw [hd]⟩
  have hi₁ : G₁.data.tripPerm i = i := by rwa [← hGG₁.tripPerm_eq]
  rw [tripDecoration_eq_of_moveEquivalent hG hGG₁ i hi hi₁,
    hc.tripDecoration_eq G₁.isPlabicGraph hi₁]
  exact ⟨G₁, hGG₁, u, hc⟩

/-- A reduced graph `K` whose trip permutation has no fixed point is move-equivalent to a normal
plabic graph whose triple diagram is minimal with strand permutation `π_K`. -/
private theorem exists_moveEquivalent_isNormalPlabicGraph_isMinimal {K : PlabicGraph b}
    (hK : K.IsReduced) (hKfix : ∀ i, K.data.tripPerm i ≠ i) :
    ∃ N : PlabicGraph b, MoveEquivalent Set.univ K N ∧ ∃ hN : N.data.IsNormalPlabicGraph,
      hN.toTripleDiagram.IsMinimal ∧ hN.toTripleDiagram.data.strandPerm = K.data.tripPerm := by
  obtain ⟨K₁, hnl, hKK₁⟩ := hK.exists_moveEquivalent_isNearlyLeafless
  have hKK₁' : MoveEquivalent Set.univ K K₁ := hKK₁.mono (Set.subset_univ _)
  have hw : ∀ i v, ¬K₁.data.IsLollipopOfColour i .white v := fun i v hv =>
    hKfix i (by
      rw [hKK₁'.tripPerm_eq]
      exact K₁.isPlabicGraph.tripPerm_eq_self_of_isLollipop hv.1)
  obtain ⟨N, hK₁N, hN⟩ :=
    (hK.of_moveEquivalent hKK₁').exists_moveEquivalent_isNormalPlabicGraph hnl hw
  have hKN := hKK₁'.trans hK₁N
  exact ⟨N, hKN, hN, (isReduced_iff_isMinimal hN).1 (hK.of_moveEquivalent hKN),
    hN.tripPerm_eq_strandPerm.symm.trans hKN.tripPerm_eq.symm⟩

/-- Case 2 of the fundamental theorem: reduced graphs with the same trip permutation and no fixed
point are move-equivalent. -/
private theorem moveEquivalent_of_tripPerm_eq_of_forall_ne {G G' : PlabicGraph b}
    (hG : G.IsReduced) (hG' : G'.IsReduced) (hπ : G.data.tripPerm = G'.data.tripPerm)
    (hfix : ∀ i, G.data.tripPerm i ≠ i) : MoveEquivalent Set.univ G G' := by
  obtain ⟨N, hGN, hN, hmin, hπN⟩ := exists_moveEquivalent_isNormalPlabicGraph_isMinimal hG hfix
  obtain ⟨N', hGN', hN', hmin', hπN'⟩ :=
    exists_moveEquivalent_isNormalPlabicGraph_isMinimal hG' fun i => hπ ▸ hfix i
  have hXX := hmin.moveEquivalent_of_strandPerm_eq hmin' (by rw [hπN, hπN', hπ])
  exact hGN.trans ((CircMoveEquivalent.moveEquivalent
    (((tfae_circMoveEquivalent_normalMoveEquivalent_moveEquivalent hN hN').out 0 2).2 hXX)).trans
    hGN'.symm)

/-- The converse direction of the fundamental theorem, by induction on the number of boundary
vertices. -/
private theorem moveEquivalent_of_decoratedTripPerm_eq_aux :
    ∀ (b : ℕ) (G G' : PlabicGraph b), G.IsReduced → G'.IsReduced →
      G.data.decoratedTripPerm G.isPlabicGraph.tripPerm_bijective =
        G'.data.decoratedTripPerm G'.isPlabicGraph.tripPerm_bijective →
      MoveEquivalent Set.univ G G' := by
  intro b
  induction b with
  | zero =>
    intro G G' hG hG' h
    exact moveEquivalent_of_tripPerm_eq_of_forall_ne hG hG' (funext (·.elim0)) (·.elim0)
  | succ n ih =>
    intro G G' hG hG' h
    have hperm : G.data.tripPerm = G'.data.tripPerm := funext fun k => by
      rw [← decoratedTripPerm_perm_apply G.isPlabicGraph.tripPerm_bijective,
        ← decoratedTripPerm_perm_apply G'.isPlabicGraph.tripPerm_bijective, h]
    by_cases hfix : ∀ i, G.data.tripPerm i ≠ i
    · exact moveEquivalent_of_tripPerm_eq_of_forall_ne hG hG' hperm hfix
    push Not at hfix
    obtain ⟨i, hi⟩ := hfix
    have hi' : G'.data.tripPerm i = i := by rwa [← hperm]
    have hcol : G.data.tripDecoration ⟨i, hi⟩ = G'.data.tripDecoration ⟨i, hi'⟩ :=
      colour_congr_of_eq h i hi hi'
    obtain ⟨G₁, hGG₁, u, hu⟩ := exists_moveEquivalent_isLollipopOfColour hG hi
    obtain ⟨G₁', hGG₁', u', hu'⟩ := exists_moveEquivalent_isLollipopOfColour hG' hi'
    rw [← hcol] at hu'
    generalize G.data.tripDecoration ⟨i, hi⟩ = ε at hu hu'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      exact hGG₁.trans ((MoveEquivalent.of_isomorphic (S := Set.univ) (G := lollipopPlabicGraph ε)
        (G₁.isPlabicGraph.isomorphic_lollipopGraph hu)).symm.trans ((MoveEquivalent.of_isomorphic
          (G := lollipopPlabicGraph ε) (G₁'.isPlabicGraph.isomorphic_lollipopGraph hu')).trans
            hGG₁'.symm))
    have : NeZero n := ⟨hn.ne'⟩
    obtain ⟨A, hA⟩ := G₁.isPlabicGraph.exists_isomorphic_lollipopInsertion hu
    obtain ⟨A', hA'⟩ := G₁'.isPlabicGraph.exists_isomorphic_lollipopInsertion hu'
    have hGI : MoveEquivalent Set.univ G (A.lollipopInsertion i ε) :=
      hGG₁.trans (MoveEquivalent.of_isomorphic (S := Set.univ) (G := A.lollipopInsertion i ε)
        (G' := G₁) hA).symm
    have hGI' : MoveEquivalent Set.univ G' (A'.lollipopInsertion i ε) :=
      hGG₁'.trans (MoveEquivalent.of_isomorphic (S := Set.univ) (G := A'.lollipopInsertion i ε)
        (G' := G₁') hA').symm
    have hI : (A.lollipopInsertion i ε).data.decoratedTripPerm
          (A.lollipopInsertion i ε).isPlabicGraph.tripPerm_bijective =
        (A'.lollipopInsertion i ε).data.decoratedTripPerm
          (A'.lollipopInsertion i ε).isPlabicGraph.tripPerm_bijective :=
      (hG.decoratedTripPerm_eq hGI _ _).symm.trans
        (h.trans (hG'.decoratedTripPerm_eq hGI' _ _))
    exact hGI.trans (((ih A A' (.of_lollipopInsertion (hG.of_moveEquivalent hGI))
      (.of_lollipopInsertion (hG'.of_moveEquivalent hGI'))
      (decoratedTripPerm_eq_of_lollipopInsertion A.isPlabicGraph A'.isPlabicGraph _ _ _ _ hI)
      ).lollipopInsertion i ε).trans hGI'.symm)

/-- **The fundamental theorem of reduced plabic graphs**. Let `G` and `G'` be reduced plabic
graphs with the same number `b` of boundary vertices. Then `G ∼ G'` if and only if
`π̃_G = π̃_{G'}`. The decorated trip permutations are formed from any proofs `hπ`, `hπ'` that the
trip permutations are bijections. -/
@[cluster_algebras "thm_fundamental_reduced"]
theorem IsReduced.moveEquivalent_iff_decoratedTripPerm_eq {G G' : PlabicGraph b}
    (hG : G.IsReduced) (hG' : G'.IsReduced) (hπ : Function.Bijective G.data.tripPerm)
    (hπ' : Function.Bijective G'.data.tripPerm) :
    MoveEquivalent Set.univ G G' ↔ G.data.decoratedTripPerm hπ = G'.data.decoratedTripPerm hπ' :=
  ⟨fun h => hG.decoratedTripPerm_eq h hπ hπ',
    moveEquivalent_of_decoratedTripPerm_eq_aux b G G' hG hG'⟩

end PlabicGraph

end ClusterAlgebras
