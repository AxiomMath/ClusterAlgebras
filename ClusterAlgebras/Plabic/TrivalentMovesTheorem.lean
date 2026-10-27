/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.NearlyLeaflessSequences
public import ClusterAlgebras.Plabic.TrivalentFlips

/-!
# Reduced trivalent plabic graphs: square moves and flips

Let `G` and `G'` be trivalent plabic graphs with `G` reduced. Then `G ∼ G'` if and only if `G` and
`G'` are joined by square moves (M1) and flips (M4) through trivalent plabic graphs.

The "if" half holds without reducedness: a flip is two moves (M3). For the "only if" half, a move
sequence between reduced graphs without internal leaves can be chosen through graphs without
internal leaves. Each graph `G_t` of such a sequence is its own core and so is anchored; its
skeleton `X_t = Γ(G_t)` has internal vertices with at least three darts, with `X_0 ≅ G` and
`X_r ≅ G'`. A move (M2) or (M3), or an isomorphism, changes the skeleton by at most a move (M3); a
square move of `G_{t-1}` is a square move of `X_{t-1}`, which lifts to `{M1}`-connected trivalent
resolutions. Between two consecutive square moves the resolutions are `{M2, M3}`-equivalent
trivalent graphs, hence `{M4}`-connected.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.moveEquivalent_iff_trivalentConnected`: reduced trivalent
  plabic graphs are move-equivalent exactly when they are `{M1, M4}`-connected.

## Implementation notes

* The proof follows the sequence `G = G_0, …, G_r = G'` through graphs without internal leaves and
  carries, for each `t`, a trivalent graph `P` that is `{M1, M4}`-connected to `G` and
  `{M2, M3}`-equivalent to the skeleton `Γ(G_t)`. A step that is not a square move extends the
  `{M2, M3}`-equivalence; at a square move `P` is replaced by a resolution `R'` of the square move
  of `Γ(G_{t-1})`, joined to `P` by flips and a resolution `R` of `Γ(G_{t-1})`, and by square moves
  from `R` to `R'`. This is FWZ's concatenation `P'_0, …, P_1, P'_1, …, P_{k+1}` built one
  step at a time.
* The theorem is stated for reduced `G`, as in FWZ's statement of it here: FWZ's
  proof of the general "only if" half assumes that a move sequence between trivalent graphs can be
  kept trivalent, which fails when a hanging leaf is the third edge of a vertex of a square.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicGraph

variable {b : ℕ}

/-- A trivalent resolution `T` of `X` is `{M3}`-equivalent to `X`: each step of a resolution
splits a vertex. -/
private theorem moveEquivalent_m3_of_isResolution {X T : PlabicGraph b} (h : X.IsResolution T) :
    MoveEquivalent {LocalMoveType.m3} X T := by
  obtain ⟨-, -, Y, hXY, hTY⟩ := h
  refine (show MoveEquivalent {LocalMoveType.m3} X Y from ?_).trans
    (MoveEquivalent.of_isomorphic hTY)
  clear hTY
  induction hXY with
  | refl => exact MoveEquivalent.refl _ _
  | tail _ hst ih =>
    obtain ⟨-, d, hd⟩ := hst
    exact ih.trans (MoveEquivalent.of_isLocalMove (t := .m3) (Set.mem_singleton _)
      (Or.inr ⟨d, hd⟩))

/-- In a plabic graph without internal leaves every internal vertex has at least two darts. -/
private theorem two_le_card_of_forall_not_isInternalLeaf {G : PlabicGraph b}
    (h : ∀ v, ¬G.data.IsInternalLeaf v) : ∀ v ∈ G.data.internalVertices, 2 ≤ #v := by
  intro v hv
  have hne : v.Nonempty := by
    obtain ⟨d, rfl⟩ := G.data.mem_vertices.1 (mem_filter.1 hv).1
    exact ⟨d, G.data.self_mem_vertexOf d⟩
  have h1 : #v ≠ 1 := fun h1 => h v ⟨hv, h1⟩
  have := hne.card_pos
  omega

private theorem m3_subset_m2_m3 :
    ({LocalMoveType.m3} : Set LocalMoveType) ⊆ {LocalMoveType.m2, LocalMoveType.m3} :=
  Set.subset_insert _ _

/-- Let `G` and `G'` be trivalent plabic graphs, and suppose that `G` is reduced. Then `G ∼ G'` if
and only if `G` and `G'` are `{M1, M4}`-connected. -/
@[cluster_algebras "thm_trivalent_moves"]
theorem IsReduced.moveEquivalent_iff_trivalentConnected {G G' : PlabicGraph b}
    (hG : G.IsTrivalent) (hG' : G'.IsTrivalent) (hred : G.IsReduced) :
    MoveEquivalent Set.univ G G' ↔
      TrivalentConnected {TrivalentMoveType.m1, TrivalentMoveType.m4} G G' := by
  refine ⟨fun h => ?_, TrivalentConnected.moveEquivalent⟩
  have h3 : ∀ v ∈ G.data.internalVertices, 3 ≤ #v := fun v hv => (hG v hv).ge
  have h3' : ∀ v ∈ G'.data.internalVertices, 3 ≤ #v := fun v hv => (hG' v hv).ge
  have hleaf : ∀ {X : PlabicGraph b}, (∀ v ∈ X.data.internalVertices, 3 ≤ #v) →
      ∀ v, ¬X.data.IsInternalLeaf v := fun hX v hv => by
    have := hX v hv.1
    have := hv.2
    omega
  have hchain := hred.reflTransGen_leaflessStep (hleaf h3) (hleaf h3') h
  have hM4 : ({TrivalentMoveType.m4} : Set TrivalentMoveType) ⊆
      {TrivalentMoveType.m1, TrivalentMoveType.m4} := Set.subset_insert _ _
  have hM1 : ({TrivalentMoveType.m1} : Set TrivalentMoveType) ⊆
      {TrivalentMoveType.m1, TrivalentMoveType.m4} :=
    Set.singleton_subset_iff.2 (Set.mem_insert _ _)
  have key : ∀ Gt, Relation.ReflTransGen LeaflessStep G Gt →
      (∀ v ∈ Gt.data.internalVertices, 2 ≤ #v) ∧ ∀ hAt : Gt.data.IsAnchored, ∃ P,
        TrivalentConnected {TrivalentMoveType.m1, TrivalentMoveType.m4} G P ∧
          MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} P (Gt.skeleton hAt) := by
    intro Gt hGt
    induction hGt with
    | refl =>
      refine ⟨fun v hv => (h3 v hv).trans' (by norm_num), fun hA => ⟨G,
        TrivalentConnected.refl hG, MoveEquivalent.of_isomorphic ?_⟩⟩
      exact ⟨PlabicData.skeletonIsoOfThick G.isPlabicGraph h3⟩
    | @tail Gs Gu _ hstep ih =>
      obtain ⟨h2s, ih⟩ := ih
      have hAs : Gs.data.IsAnchored := Gs.isPlabicGraph.isAnchored h2s
      obtain ⟨P, hGP, hPX⟩ := ih hAs
      refine ⟨two_le_card_of_forall_not_isInternalLeaf hstep.1, fun hAu => ?_⟩
      have hother : MoveStep {LocalMoveType.m2, LocalMoveType.m3} Gs Gu → ∃ P,
          TrivalentConnected {TrivalentMoveType.m1, TrivalentMoveType.m4} G P ∧
            MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} P (Gu.skeleton hAu) :=
        fun hs => ⟨P, hGP, hPX.trans ((MoveEquivalent.of_moveStep (hs.skeleton hAs)).mono
          m3_subset_m2_m3)⟩
      obtain ⟨-, hθ | ⟨t, -, ht⟩⟩ := hstep
      · exact hother (Or.inl hθ)
      cases t with
      | m2 => exact hother (Or.inr ⟨.m2, Set.mem_insert _ _, ht⟩)
      | m3 => exact hother (Or.inr ⟨.m3, Set.mem_insert_of_mem _ rfl, ht⟩)
      | m1 =>
        obtain ⟨c, hq, hθ⟩ := ht
        have hcore : Gs.data.core = univ := Gs.isPlabicGraph.core_eq_univ h2s
        obtain ⟨hc, hqX, heq⟩ := PlabicData.IsSquareMoveFace.skeleton Gs.isPlabicGraph hq
          (fun k => by rw [hcore]; exact subset_univ _)
        set X := Gs.skeleton hAs
        have hX3 : ∀ v ∈ X.data.internalVertices, 3 ≤ #v := fun v hv =>
          PlabicData.three_le_card_of_mem_skeleton_internalVertices Gs.isPlabicGraph hv
        obtain ⟨R, R', hR, hR', hRR'⟩ :=
          exists_isResolution_squareMove X hX3 (c := ⟨c, hc⟩) hqX
        have hPR : MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} P R :=
          hPX.trans ((moveEquivalent_m3_of_isResolution hR).mono m3_subset_m2_m3)
        have hPR4 := MoveEquivalent.trivalentConnected hGP.isTrivalent_right hR.2.1 hPR
        have hR'Y : MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} R'
            (X.squareMove ⟨c, hc⟩) :=
          ((moveEquivalent_m3_of_isResolution hR').mono m3_subset_m2_m3).symm
        have hYU : MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} (X.squareMove ⟨c, hc⟩)
            (Gu.skeleton hAu) := by
          refine MoveEquivalent.of_isomorphic ?_
          change (Gu.data.skeleton Gu.isPlabicGraph).Isomorphic
            ((Gs.data.skeleton Gs.isPlabicGraph).squareMove ⟨c, hc⟩)
          rw [heq]
          exact PlabicData.Isomorphic.skeleton Gu.isPlabicGraph
            (Gs.isPlabicGraph.squareMove c) hθ
        exact ⟨R', (hGP.trans (hPR4.mono hM4)).trans (hRR'.mono hM1), hR'Y.trans hYU⟩
  obtain ⟨h2', hP⟩ := key G' hchain
  obtain ⟨P, hGP, hPX⟩ := hP (G'.isPlabicGraph.isAnchored h2')
  have hPG' : MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} P G' :=
    hPX.trans (MoveEquivalent.of_isomorphic
      ⟨(PlabicData.skeletonIsoOfThick G'.isPlabicGraph h3').symm⟩)
  exact hGP.trans ((MoveEquivalent.trivalentConnected hGP.isTrivalent_right hG' hPG').mono hM4)

end PlabicGraph

end ClusterAlgebras
