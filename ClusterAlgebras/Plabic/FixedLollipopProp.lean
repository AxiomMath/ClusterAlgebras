/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FixedLollipopInvariant
public import ClusterAlgebras.Plabic.FixedLollipop
public import ClusterAlgebras.Plabic.ReducedToNormal
public import ClusterAlgebras.Plabic.ReducedIffMinimal
public import ClusterAlgebras.Plabic.Straighten
public import ClusterAlgebras.Plabic.MinimalMonogon
public import ClusterAlgebras.Plabic.NormalMovesEquivalent
public import ClusterAlgebras.Plabic.External

/-!
# A fixed point of a reduced graph comes from a lollipop

Let `G` be a reduced plabic graph with `b` boundary vertices and let `i` be a fixed point of its
trip permutation `π_G`. Then `G` has a lollipop at `i` or a collapsible tree whose root is `β(i)`.

The proof is by induction on `b`. Both alternatives persist under move equivalence, so `G` may be
replaced by a move-equivalent nearly leafless graph `G₁`, which is still reduced with
`π_{G₁} = π_G`.
If `G₁` has a white lollipop at some label `j ≠ i`, it is the insertion `I_j(A, white)` of a
lollipop into a reduced graph `A` with `b - 1` boundary vertices, `i = i₀⁺` is a fixed point of
`π_A`, and the induction hypothesis for `A` gives the conclusion for `I_j(A, white)`. Otherwise
`G₁` has no white lollipop at all (a white lollipop at `i` would already be the conclusion), so it
is move-equivalent to a normal plabic graph `N`, whose triple diagram `X(N)` is minimal and has the
straightening property. The interval `{2i - 1, 2i}` of the fixed point `i` is minimal, so some
`X' ∼ X(N)` has its arc from `s_i` boundary-parallel along it: this arc passes through no triple
point, so it is the single dart `n_{2i - 1}`, with partner `n_{2i}`. In the normal plabic graph
`G(X') ∼ N` the vertex `{c_{n_{2i}}}` is then a black lollipop at `i`.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.exists_isLollipop_or_isCollapsible_of_tripPerm_eq_self`:
  a fixed point of a reduced graph comes from a lollipop.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`; the positions `2i - 1` and
  `2i` of `s_i` and `t_i` are `sourceIndex i` and `targetIndex i`.
* FWZ's proof argues by contradiction after reducing to `G₁`; here the two cases each
  produce the conclusion for a graph move-equivalent to `G₁`, and the conclusion for `G` follows by
  the invariance of lollipops and boundary trees under local moves.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace TripleData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-- The interval `{2i - 1, 2i}` from `s_i` to `t_i` has two positions. -/
private theorem card_cyclicIcc_sourceIndex_targetIndex (i : Fin b) :
    (cyclicIcc (sourceIndex i) (targetIndex i)).card = 2 := by
  have hle : sourceIndex i ≤ targetIndex i := by
    rw [Fin.le_def, sourceIndex_val, targetIndex_val]
    omega
  rw [cyclicIcc_of_le hle, Fin.card_Icc, sourceIndex_val, targetIndex_val]
  omega

/-- For a fixed point `i` of `π`, the interval `{2i - 1, 2i}` is a minimal interval of `i`. -/
private theorem isMinimalInterval_cyclicIcc_of_eq_self {π : Fin b → Fin b} {i : Fin b}
    (hi : π i = i) : IsMinimalInterval π i (cyclicIcc (sourceIndex i) (targetIndex i)) := by
  refine ⟨Or.inl (by rw [hi]), fun j hj hs => hj ?_⟩
  replace hs := hs.1
  have hle : sourceIndex i ≤ targetIndex i := by
    rw [Fin.le_def, sourceIndex_val, targetIndex_val]
    omega
  rw [cyclicIcc_of_le hle, mem_Icc, Fin.le_def, Fin.le_def, sourceIndex_val, sourceIndex_val,
    targetIndex_val] at hs
  exact Fin.ext (by omega)

/-- If the arc from `s_i` of a triple diagram is boundary-parallel along `{2i - 1, 2i}`, it
consists of the single dart `n_{2i - 1}`. -/
private theorem arcLength_eq_one_of_isBoundaryParallel (hX : X.IsTripleDiagram) {i : Fin b}
    (h : X.IsBoundaryParallel i (cyclicIcc (sourceIndex i) (targetIndex i))) :
    X.arcLength i = 1 := by
  obtain ⟨hI, hS, hcard, -⟩ := h
  have h0 := hI.card_intervalInterior
  rw [card_cyclicIcc_sourceIndex_targetIndex] at h0
  rw [hS.ncard_passesThrough hX] at hcard
  have := hX.toIsPreTripleDiagram.arcLength_ne_zero i
  omega

/-- The vertex of a fixed point of the rotation is a singleton. -/
private theorem vertexOf_eq_singleton' {Y : Type*} [Fintype Y] [DecidableEq Y]
    {R : RotationSystem Y} {a : Y} (ha : R.rot a = a) : R.vertexOf a = {a} := by
  ext y
  rw [RotationSystem.mem_vertexOf, mem_singleton]
  exact ⟨fun h => (h.eq_of_left ha).symm, fun h => h ▸ Equiv.Perm.SameCycle.refl _ _⟩

/-- If the arc from `s_i` of a triple diagram `X` is the single dart `n_{2i - 1}` and ends at
`t_i`, then `{c_{n_{2i}}}` is a lollipop at `i` of the normal plabic graph `G(X)`. -/
private theorem isLollipop_normalOfTriple (hX : X.IsTripleDiagram) {i : Fin b}
    (hi : X.strandPerm i = i) (h1 : X.arcLength i = 1) :
    (X.normalOfTriple hX.toIsPreTripleDiagram).IsLollipop i
      {.c (hX.toIsPreTripleDiagram.targetDart i)} := by
  set hP := hX.toIsPreTripleDiagram
  have hend : X.endDart (targetIndex i) = X.inv (X.endDart (sourceIndex i)) := by
    have := endDart_arcEndIndex hX i
    simp only [arcEndIndex, hi, h1, Nat.sub_self, arcDart_zero] at this
    exact this
  have hrot : (X.normalOfTriple hP).rot (.c (hP.targetDart i)) = .c (hP.targetDart i) := by
    rw [IsPreTripleDiagram.normalOfTriple_rot, hP.normalRot_c]
    congr 1
    apply Subtype.ext
    rw [hP.coe_psi, IsPreTripleDiagram.coe_targetDart,
      psiFun_of_some (hP.targetLabel_endDart i), hend]
  have hv := vertexOf_eq_singleton' (R := (X.normalOfTriple hP).toRotationSystem) hrot
  refine ⟨⟨?_, card_singleton _⟩, .c (hP.targetDart i), mem_singleton_self _, ?_⟩
  · rw [← hv, DiskMap.vertexOf_mem_internalVertices]
    exact hP.not_isBoundaryVertex_normalOfTriple_c _
  · exact (X.normalOfTriple hP).self_mem_vertexOf _

end TripleData

namespace PlabicGraph

open PlabicData

/-- Let `G` be a reduced plabic graph with `b` boundary vertices and let `i : Fin b` be a fixed
point of its trip permutation. Then `G` has a lollipop at `i` or a collapsible rooted tree whose
root is the boundary vertex `G.data.bvertex i`. -/
@[cluster_algebras "prop_fixed_lollipop"]
theorem IsReduced.exists_isLollipop_or_isCollapsible_of_tripPerm_eq_self {b : ℕ}
    {G : PlabicGraph b} (hG : G.IsReduced) {i : Fin b} (hi : G.data.tripPerm i = i) :
    (∃ v, G.data.IsLollipop i v) ∨
      ∃ T : G.data.RootedTree, T.root = G.data.bvertex i ∧ T.IsCollapsible := by
  induction b with
  | zero => exact i.elim0
  | succ n ih =>
  obtain ⟨G₁, hnl, hGG₁⟩ := hG.exists_moveEquivalent_isNearlyLeafless
  have hGG₁' : MoveEquivalent Set.univ G G₁ := hGG₁.mono (Set.subset_univ _)
  have hred₁ : G₁.IsReduced := hG.of_moveEquivalent hGG₁'
  have hi₁ : G₁.data.tripPerm i = i := by rw [← hGG₁'.tripPerm_eq]; exact hi
  refine hGG₁'.symm.exists_isLollipop_or_isCollapsible i ?_
  by_cases hw : ∃ j v, j ≠ i ∧ G₁.data.IsLollipopOfColour j .white v
  · /- Case 1: a white lollipop at `j ≠ i`. -/
    obtain ⟨j, u, hj, hu⟩ := hw
    haveI : NeZero n := ⟨by
      rintro rfl
      exact hj (Fin.ext (by have := j.isLt; have := i.isLt; omega))⟩
    obtain ⟨A, hA⟩ := G₁.isPlabicGraph.exists_isomorphic_lollipopInsertion hu
    have hI : MoveEquivalent Set.univ G₁ (A.lollipopInsertion j .white) :=
      (MoveEquivalent.of_isomorphic (S := Set.univ) (G := A.lollipopInsertion j .white)
        (G' := G₁) hA).symm
    have hAred : A.IsReduced := IsReduced.of_lollipopInsertion (hred₁.of_moveEquivalent hI)
    obtain ⟨i₀, rfl⟩ : ∃ i₀, j.succAbove i₀ = i := by
      rcases Fin.eq_self_or_eq_succAbove j i with h | ⟨i₀, h⟩
      · exact absurd h.symm hj
      · exact ⟨i₀, h.symm⟩
    have hπA : A.data.tripPerm i₀ = i₀ := by
      have h := tripPerm_lollipopInsertion_succAbove (A := A.data) (i := j) (c := .white)
        A.isPlabicGraph i₀
      rw [show (A.data.lollipopInsertion j .white).tripPerm = G₁.data.tripPerm from
        hI.tripPerm_eq.symm, hi₁] at h
      exact (Fin.succAbove_right_injective h).symm
    have hPI : (∃ v, (A.lollipopInsertion j .white).data.IsLollipop (j.succAbove i₀) v) ∨
        ∃ T : (A.lollipopInsertion j .white).data.RootedTree,
          T.root = (A.lollipopInsertion j .white).data.bvertex (j.succAbove i₀) ∧
            T.IsCollapsible := by
      rcases ih hAred hπA with ⟨v, hv⟩ | ⟨T, hT, c', hc'⟩
      · exact Or.inl ⟨_, (isLollipop_lollipopInsertion_map_inl_iff A.isPlabicGraph i₀).2 hv⟩
      · obtain ⟨T', hT', hc⟩ :=
          (exists_isCollapsibleOfColour_bvertex_lollipopInsertion_iff A.isPlabicGraph i₀ c').2
            ⟨T, hT, hc'⟩
        exact Or.inr ⟨T', hT', hc.isCollapsible⟩
    exact hI.symm.exists_isLollipop_or_isCollapsible _ hPI
  · /- Case 2: no white lollipop at any `j ≠ i`. -/
    by_contra hP
    have hw' : ∀ j v, ¬G₁.data.IsLollipopOfColour j .white v := fun j v h => by
      by_cases hj : j = i
      · subst hj
        exact hP (Or.inl ⟨v, h.1⟩)
      · exact hw ⟨j, v, hj, h⟩
    obtain ⟨N, hG₁N, hN⟩ := hred₁.exists_moveEquivalent_isNormalPlabicGraph hnl hw'
    have hmin := (isReduced_iff_isMinimal hN).1 (hred₁.of_moveEquivalent hG₁N)
    have hπN : hN.toTripleDiagram.data.strandPerm i = i := by
      have h := congrFun hN.tripPerm_eq_strandPerm i
      rw [← hG₁N.tripPerm_eq, hi₁] at h
      exact h.symm
    obtain ⟨X', hXX', hbp⟩ := hmin.isMonogonStable.hasStraighteningProperty.2 i _
      (TripleData.isMinimalInterval_cyclicIcc_of_eq_self hπN)
    have hπX' : X'.data.strandPerm i = i := by rw [hXX'.strandPerm_eq, hπN]
    have hX' := X'.isTripleDiagram
    have h1 := TripleData.arcLength_eq_one_of_isBoundaryParallel hX' hbp
    let N' : PlabicGraph (n + 1) :=
      ⟨_, _, hX'.isNormalPlabicGraph_normalOfTriple.toIsPlabicGraph⟩
    have hN' : N'.data.IsNormalPlabicGraph := hX'.isNormalPlabicGraph_normalOfTriple
    have hiso : TripleDiagram.Isomorphic (hN'.toTripleDiagram) X' :=
      ⟨hX'.toIsPreTripleDiagram.tripleOfNormalIso⟩
    have hXN : hN.toTripleDiagram.MoveEquivalent hN'.toTripleDiagram :=
      hXX'.trans (TripleDiagram.MoveEquivalent.of_isomorphic hiso).symm
    have hNN' : MoveEquivalent Set.univ N N' :=
      CircMoveEquivalent.moveEquivalent
        (((tfae_circMoveEquivalent_normalMoveEquivalent_moveEquivalent hN hN').out 0 2).2 hXN)
    exact hP ((hG₁N.trans hNN').symm.exists_isLollipop_or_isCollapsible i
      (Or.inl ⟨_, TripleData.isLollipop_normalOfTriple hX' hπX' h1⟩))

end PlabicGraph

end ClusterAlgebras
