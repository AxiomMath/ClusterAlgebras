/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.UrbanNormal
public import ClusterAlgebras.Plabic.NormalOfTriple
public import ClusterAlgebras.Plabic.TripleMoves
public import ClusterAlgebras.Plabic.TrivalentMoves

/-!
# Normal moves, swivel moves and local moves

Two normal plabic graphs `G` and `G'` are normal-move-equivalent exactly when their triple
diagrams are move-equivalent, `X(G) ∼ X(G')`: urban renewal and the normal flip act on `X(G)` as
swivel moves at the two kinds of digons of `X(G)`, and every digon of `X(G)` is of one of these
kinds. Conversely, a sequence of swivel moves from `X(G)` is followed by a sequence of normal
moves from `G`, and a normal plabic graph is recovered from its triple diagram up to isomorphism.

Normal moves are also sequences of local moves avoiding the contraction of an edge between a
white internal leaf and a white vertex with at least three darts, the relation `G ∘∼ G'`. For the
normal flip at a black bivalent vertex `u = {k, σk}`: remove `u`, contract the edge joining the two
white neighbours, split the merged white vertex the other way, and insert a black vertex on the new
edge. For urban renewal at a face `(c₁, c₂, c₃, c₄)`: split the black corners `v(c₁)` and `v(c₃)`
so that they become trivalent, make the square move at the face, and contract the two edges by
which the urban renewal differs from the result. The last graph of the second sequence is
compared with the urban renewal by splitting the urban renewal at `ē₂` and `ē₄` and exhibiting an
isomorphism of the two double splittings.

## Main results

* `ClusterAlgebras.PlabicGraph.normalMoveEquivalent_iff_moveEquivalent`: normal plabic graphs
  are normal-move-equivalent if and only if their triple diagrams are move-equivalent.
* `ClusterAlgebras.PlabicData.IsUrbanRenewalFace.circMoveEquivalent`: a normal plabic graph and
  its urban renewal satisfy `G ∘∼ G'`.
* `ClusterAlgebras.PlabicData.IsNormalFlipVertex.circMoveEquivalent`: a normal plabic graph and
  its normal flip satisfy `G ∘∼ G'`.
* `ClusterAlgebras.PlabicGraph.NormalMoveEquivalent.circMoveEquivalent`: normal-move-equivalent
  normal plabic graphs satisfy `G ∘∼ G'`.

## Implementation notes

* **Urban renewal.** FWZ contract the edges `{e₂, ē₂}` and `{e₄, ē₄}` of the square move
  of the double splitting and compares the result with the urban renewal `G'`. Here, instead, the
  square move of the double splitting of `G` at `c̄₄, c̄₂` is shown isomorphic to the double
  splitting of `G'` at `ē₂, ē₄`, whose contraction along the two new edges is `G'`
  (`isomorphic_contractEdge_vertexSplit`). The isomorphism is the product of the four cycles
  `(n₁ c₄ c₁ e₂)`, `(n̄₁ c̄₄ c̄₁ ē₂)`, `(n₂ c₂ c₃ e₄)`, `(n̄₂ c̄₂ c̄₃ ē₄)`, where `n₁, n̄₁` and
  `n₂, n̄₂` are the new darts of the two splittings. Every edge contracted or created along the
  way joins two black vertices, so no step joins a white leaf to a white vertex.
* **Normal flip.** FWZ end by splitting the merged white vertex and inserting a black
  vertex on the new edge. Here these two steps are read backwards from the normal flip `G'`:
  `u` is again a normal flip vertex of `G'`, and removing it and contracting the edge between its
  white neighbours gives a graph isomorphic to the one obtained in the same way from `G`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

namespace TripleData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {d₁ : H}

/-- The darts of a digon `f(d₁)` are `d₁` and `φ(d₁)`. -/
private theorem IsDigon.eq_or_eq_facePerm_of_mem (hd : X.IsDigon (X.faceOf d₁)) {e : H}
    (he : e ∈ X.faceOf d₁) : e = d₁ ∨ e = X.facePerm d₁ := by
  have hφφ := hd.facePerm_facePerm
  obtain ⟨-, d, hf, -⟩ := hd
  have hd₁ : d₁ ∈ ({d, X.facePerm d} : Finset H) := hf ▸ X.self_mem_faceOf d₁
  rw [hf] at he
  simp only [mem_insert, mem_singleton] at hd₁ he
  rcases hd₁ with rfl | rfl
  · exact he
  · have h2 : X.facePerm (X.facePerm d) = d := X.facePerm.injective hφφ
    rcases he with rfl | rfl
    · exact Or.inr h2.symm
    · exact Or.inl rfl

/-- At a digon `f(d₁)` of a pre-triple diagram, the swivel move at `φ(d₁)` is the swivel move at
`d₁`. -/
private theorem IsDigon.swivelRot_facePerm (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) : X.swivelRot (X.facePerm d₁) = X.swivelRot d₁ := by
  have hφφ := hd.facePerm_facePerm
  obtain ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, h1, h2, h3, h4, h5, g1, g2, g3, g4, g5, hnd, -⟩ :=
    hd.exists_darts hX
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := X.swivelRot_of_darts h1 h2 h3 h4 h5 g1 g2 g3 g4 g5
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]; grind)
  generalize hd₂ : X.facePerm d₁ = d₂ at *
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := X.swivelRot_of_darts (d₁ := d₂) g1 g2 g3 g4
    (by rw [hφφ]; exact g5) (by rw [hφφ]; exact h1) h2 h3 h4 h5
    (by rw [hφφ]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true]; grind)
  rw [hφφ] at t5 t6 t7
  ext z
  by_cases e1 : z = d₁
  · subst e1; rw [s1, t5]
  by_cases e2 : z = a₂
  · subst e2; rw [s2, t6]
  by_cases e3 : z = a₄
  · subst e3; rw [s4, t3]
  by_cases e4 : z = d₂
  · subst e4; rw [s5, t1]
  by_cases e5 : z = b₂
  · subst e5; rw [s6, t2]
  by_cases e6 : z = b₄
  · subst e6; rw [s3, t4]
  rw [s7 z e1 e2 e3 e4 e5 e6, t7 z e4 e5 e6 e1 e2 e3]

/-- At a digon `f(d₁)` of a pre-triple diagram, the swivel move at either dart of the digon is the
swivel move at `d₁`. -/
private theorem IsDigon.swivelMove_eq_of_mem (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) {e : H} (he : e ∈ X.faceOf d₁) :
    X.swivelMove e = X.swivelMove d₁ := by
  rcases hd.eq_or_eq_facePerm_of_mem he with rfl | rfl
  · rfl
  · unfold swivelMove
    rw [hd.swivelRot_facePerm hX]

end TripleData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- If `G'` is isomorphic to an urban renewal of `G`, then `X(G) ∼ X(G')`. -/
private theorem moveEquivalent_of_isUrbanRenewal {G G' : PlabicGraph b}
    (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph)
    (h : G.IsUrbanRenewal G') : hG.toTripleDiagram.MoveEquivalent hG'.toTripleDiagram := by
  obtain ⟨c, hc, hiso⟩ := h
  have hU := hc.isNormalPlabicGraph_urbanRenewal hG
  obtain ⟨-, -, hd, θ, -⟩ := hc.exists_iso_swivelMove hG
  exact (TripleDiagram.MoveEquivalent.of_isSwivelMove (X' := hU.toTripleDiagram)
    ⟨_, hd, ⟨θ.symm⟩⟩).trans
    (TripleDiagram.MoveEquivalent.of_isomorphic (hiso.symm.isomorphic_toTripleDiagram hU hG'))

/-- If `G'` is isomorphic to a normal flip of `G`, then `X(G) ∼ X(G')`. -/
private theorem moveEquivalent_of_isNormalFlip {G G' : PlabicGraph b}
    (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph)
    (h : G.IsNormalFlip G') : hG.toTripleDiagram.MoveEquivalent hG'.toTripleDiagram := by
  obtain ⟨k, hk, hiso⟩ := h
  have hF := hk.isNormalPlabicGraph_normalFlip hG
  obtain ⟨-, -, hd, θ, -⟩ := hk.exists_iso_swivelMove hG
  exact (TripleDiagram.MoveEquivalent.of_isSwivelMove (X' := hF.toTripleDiagram)
    ⟨_, hd, ⟨θ.symm⟩⟩).trans
    (TripleDiagram.MoveEquivalent.of_isomorphic (hiso.symm.isomorphic_toTripleDiagram hF hG'))

/-- A step of normal move equivalence is a move equivalence of triple diagrams. -/
private theorem NormalMoveStep.moveEquivalent {G G' : PlabicGraph b}
    (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph)
    (h : NormalMoveStep G G') : hG.toTripleDiagram.MoveEquivalent hG'.toTripleDiagram := by
  obtain ⟨-, -, h⟩ := h
  rcases h with h | (h | h) | (h | h)
  · exact .of_isomorphic (PlabicData.Isomorphic.isomorphic_toTripleDiagram
      (PlabicData.Isomorphic.symm _ h) hG hG')
  · exact moveEquivalent_of_isUrbanRenewal hG hG' h
  · exact moveEquivalent_of_isNormalFlip hG hG' h
  · exact (moveEquivalent_of_isUrbanRenewal hG' hG h).symm
  · exact (moveEquivalent_of_isNormalFlip hG' hG h).symm

/-- A swivel move of a pre-triple diagram isomorphic to `X(G₁)` is isomorphic to `X(G₂)` for a
normal plabic graph `G₂` obtained from `G₁` by an urban renewal or a normal flip. -/
private theorem exists_normalMoveStep_swivelMove {G₁ : PlabicGraph b}
    (h₁ : G₁.data.IsNormalPlabicGraph) {K : Type} [Fintype K] [DecidableEq K]
    {Z : TripleData K b} (hZ : Z.IsPreTripleDiagram)
    (θ : (G₁.data.tripleOfNormal h₁.isNormalPlabicPregraph).Iso Z) {d₁ : K}
    (hd : Z.IsDigon (Z.faceOf d₁)) :
    ∃ (G₂ : PlabicGraph b) (h₂ : G₂.data.IsNormalPlabicGraph), NormalMoveStep G₁ G₂ ∧
      (G₂.data.tripleOfNormal h₂.isNormalPlabicPregraph).Isomorphic (Z.swivelMove d₁) := by
  set X := G₁.data.tripleOfNormal h₁.isNormalPlabicPregraph with hXdef
  have hX : X.IsPreTripleDiagram := h₁.isNormalPlabicPregraph.isPreTripleDiagram_tripleOfNormal
  have hd' := (θ.symm.isDigon_faceOf_map hd).1
  have ψ := θ.symm.swivelMove hZ hX d₁
  set d := θ.symm.toEquiv d₁ with hddef
  rcases (h₁.isDigon_tripleOfNormal_iff _).1 hd' with
    ⟨c, hc, k₁, k₂, hk₁, -, hδ⟩ | ⟨k, hk, k₁, k₂, hk₁, -, hδ⟩
  · have hU := hc.isNormalPlabicGraph_urbanRenewal h₁
    obtain ⟨-, -, -, θ', -⟩ := hc.exists_iso_swivelMove h₁
    refine ⟨⟨G₁.Dart, G₁.data.urbanRenewal c, hU.toIsPlabicGraph⟩, hU,
      ⟨h₁, hU, Or.inr (Or.inl (Or.inl ⟨c, hc, PlabicData.Isomorphic.refl _⟩))⟩, ?_⟩
    have hmem : (TripleOfNormalDart.plus ⟨G₁.data.inv (G₁.data.squareCorner c 3),
        hc.inv_squareCorner_three_mem_blackDarts h₁⟩ : G₁.data.TripleDart) ∈ X.faceOf d := by
      rw [hδ]
      exact mem_insert.2 (Or.inl (congrArg _ (Subtype.ext hk₁.symm)))
    have he := TripleData.IsDigon.swivelMove_eq_of_mem hX hd' hmem
    rw [he] at θ'
    exact ⟨θ'.trans ψ.symm⟩
  · have hF := hk.isNormalPlabicGraph_normalFlip h₁
    obtain ⟨-, -, -, θ', -⟩ := hk.exists_iso_swivelMove h₁
    refine ⟨⟨G₁.Dart, G₁.data.normalFlip k, hF.toIsPlabicGraph⟩, hF,
      ⟨h₁, hF, Or.inr (Or.inl (Or.inr ⟨k, hk, PlabicData.Isomorphic.refl _⟩))⟩, ?_⟩
    have hmem : (TripleOfNormalDart.minus ⟨k, hk.mem_blackDarts⟩ : G₁.data.TripleDart) ∈
        X.faceOf d := by
      rw [hδ]
      exact mem_insert.2 (Or.inl (congrArg _ (Subtype.ext hk₁.symm)))
    have he := TripleData.IsDigon.swivelMove_eq_of_mem hX hd' hmem
    rw [he] at θ'
    exact ⟨θ'.trans ψ.symm⟩

/-- Normal plabic graphs `G` and `G'` are normal-move-equivalent if and only if their triple
diagrams are move-equivalent, `X(G) ∼ X(G')`. -/
@[cluster_algebras "thm_normal_moves_swivel"]
theorem normalMoveEquivalent_iff_moveEquivalent {G G' : PlabicGraph b}
    (hG : G.data.IsNormalPlabicGraph) (hG' : G'.data.IsNormalPlabicGraph) :
    NormalMoveEquivalent G G' ↔ hG.toTripleDiagram.MoveEquivalent hG'.toTripleDiagram := by
  constructor
  · rintro ⟨-, h⟩
    revert hG'
    induction h with
    | refl => exact fun _ => .refl _
    | tail _ hs ih => exact fun hG' => (ih hs.1).trans (NormalMoveStep.moveEquivalent hs.1 hG' hs)
  · intro h
    obtain ⟨Y, hY, hYX'⟩ := h.exists_swivelSteps
    have key : ∀ Y, Relation.ReflTransGen TripleData.SwivelStep hG.toTripleDiagram.data Y →
        ∃ (G₁ : PlabicGraph b) (h₁ : G₁.data.IsNormalPlabicGraph), NormalMoveEquivalent G G₁ ∧
          (G₁.data.tripleOfNormal h₁.isNormalPlabicPregraph).Isomorphic Y := by
      intro Y hY
      induction hY with
      | refl => exact ⟨G, hG, .refl hG, TripleData.Isomorphic.refl _⟩
      | tail hY' hst ih =>
        obtain ⟨G₁, h₁, hGG₁, ⟨θ⟩⟩ := ih
        obtain ⟨d₁, hd, rfl⟩ := hst
        have hYp := (TripleData.isTripleDiagram_of_reflTransGen_swivelStep hY'
          hG.isTripleDiagram_tripleOfNormal).toIsPreTripleDiagram
        obtain ⟨G₂, h₂, hs, hiso⟩ := exists_normalMoveStep_swivelMove h₁ hYp θ hd
        exact ⟨G₂, h₂, hGG₁.trans (.of_normalMoveStep hs), hiso⟩
    obtain ⟨G₁, h₁, hGG₁, ⟨θ⟩⟩ := key Y hY
    obtain ⟨θ'⟩ := hYX'
    have χ := (h₁.normalOfTripleIso.trans ((θ.trans θ').normalOfTriple
      h₁.isNormalPlabicPregraph.isPreTripleDiagram_tripleOfNormal
      hG'.isNormalPlabicPregraph.isPreTripleDiagram_tripleOfNormal)).trans
      hG'.normalOfTripleIso.symm
    exact hGG₁.trans (.of_isomorphic h₁ hG' ⟨χ.symm⟩)

end PlabicGraph

/-! ### The normal flip by local moves -/

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {N : PlabicData H b} {k : H}

/-- The vertex `u = {k, σk}` of a normal flip can be removed. -/
private theorem IsNormalFlipVertex.isBivalentRemovable (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) : N.IsBivalentRemovable k := by
  refine ⟨hk.not_isBoundaryVertex, hk.card_vertexOf, fun h => ?_⟩
  have h1 := hk.colour_inv
  rw [h, hN.colour_rot k hk.not_isBoundaryVertex, hk.colour_eq] at h1
  exact Shade.noConfusion h1

/-- The removal of the vertex `u = {k, σk}` of a normal flip. -/
private def IsNormalFlipVertex.removal (hN : N.IsNormalPlabicGraph) (hk : N.IsNormalFlipVertex k) :
    PlabicData (({k, N.rot k}ᶜ : Set H)) b :=
  N.bivalentRemoval hN.toIsPlabicGraph (hk.isBivalentRemovable hN)

private theorem IsNormalFlipVertex.isPlabicGraph_removal (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) : (hk.removal hN).IsPlabicGraph :=
  isPlabicGraph_bivalentRemoval hN.toIsPlabicGraph (hk.isBivalentRemovable hN)

/-- The dart `k̄` of the removal. -/
private def IsNormalFlipVertex.removalDart (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) : (({k, N.rot k}ᶜ : Set H)) :=
  ⟨N.inv k, (hk.isBivalentRemovable hN).inv_mem hN.toIsPlabicGraph⟩

private theorem IsNormalFlipVertex.coe_removal_inv_removalDart (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) :
    ((hk.removal hN).inv (hk.removalDart hN) : H) = N.inv (N.rot k) :=
  coe_bivalentRemoval_inv_of_eq_inv hN.toIsPlabicGraph (hk.isBivalentRemovable hN) rfl

private theorem IsNormalFlipVertex.mem_compl_iff (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) (z : (({k, N.rot k}ᶜ : Set H))) :
    z ∈ (({hk.removalDart hN, (hk.removal hN).inv (hk.removalDart hN)} : Set _)ᶜ : Set _) ↔
      (z : H) ≠ N.inv k ∧ (z : H) ≠ N.inv (N.rot k) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    Subtype.ext_iff, hk.coe_removal_inv_removalDart hN]
  rfl

private theorem IsNormalFlipVertex.card_vertexOf_inv (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) : (N.vertexOf (N.inv k)).card = 3 :=
  hN.card_vertexOf_of_white _ hk.not_isBoundaryVertex_inv hk.colour_inv

private theorem IsNormalFlipVertex.card_vertexOf_inv_rot (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) : (N.vertexOf (N.inv (N.rot k))).card = 3 :=
  hN.card_vertexOf_of_white _ hk.not_isBoundaryVertex_inv_rot hk.colour_inv_rot

/-- In the removal, the edge `{k̄, \overline{σk}}` joins two distinct white internal vertices. -/
private theorem IsNormalFlipVertex.isContractibleEdge_removal (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) : (hk.removal hN).IsContractibleEdge (hk.removalDart hN) := by
  have hG := hN.toIsPlabicGraph
  have hd := hk.isBivalentRemovable hN
  have hinv := hk.coe_removal_inv_removalDart hN
  refine ⟨fun h => ?_, ?_, ?_, ?_⟩
  · have h' := congrArg (Finset.map (Embedding.subtype _)) h
    simp only [removal, map_bivalentRemoval_vertexOf] at h'
    rw [removal] at hinv
    rw [hinv] at h'
    exact hk.vertexOf_inv_ne h'
  · rw [(hk.removal hN).vertexOf_mem_internalVertices, removal,
      isBoundaryVertex_bivalentRemoval_vertexOf_iff]
    exact hk.not_isBoundaryVertex_inv
  · rw [(hk.removal hN).vertexOf_mem_internalVertices]
    unfold removal at hinv ⊢
    rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff, hinv]
    exact hk.not_isBoundaryVertex_inv_rot
  · unfold removal at hinv ⊢
    rw [bivalentRemoval_colour, bivalentRemoval_colour, hinv, hk.colour_inv_rot]
    exact hk.colour_inv.symm

/-- The contraction of the removal along `{k̄, \overline{σk}}`: the two white vertices `v(k̄)`
and `v(\overline{σk})` merge into one white vertex with four darts. -/
private noncomputable def IsNormalFlipVertex.contracted (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) :
    PlabicData ((({hk.removalDart hN, (hk.removal hN).inv (hk.removalDart hN)} : Set _)ᶜ :
      Set (({k, N.rot k}ᶜ : Set H)))) b :=
  (hk.removal hN).contractEdge (hk.removalDart hN)
    ((hk.isContractibleEdge_removal hN).leg_mem (hk.isPlabicGraph_removal hN))

private theorem IsNormalFlipVertex.isPlabicGraph_contracted (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) : (hk.contracted hN).IsPlabicGraph :=
  (hk.isPlabicGraph_removal hN).contractEdge (hk.isContractibleEdge_removal hN)

/-- `G ∘∼` the contraction of the removal of `u` along `{k̄, \overline{σk}}`. -/
private theorem IsNormalFlipVertex.circMoveEquivalent_contracted (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) :
    PlabicGraph.CircMoveEquivalent ⟨H, N, hN.toIsPlabicGraph⟩
      ⟨_, hk.contracted hN, hk.isPlabicGraph_contracted hN⟩ := by
  have hcard : ∀ y, ((hk.removal hN).vertexOf y).card = (N.vertexOf y).card := fun y => by
    rw [← map_bivalentRemoval_vertexOf hN.toIsPlabicGraph (hk.isBivalentRemovable hN) y,
      card_map]
    rfl
  have hinv := hk.coe_removal_inv_removalDart hN
  refine Relation.ReflTransGen.head (b := ⟨_, hk.removal hN, hk.isPlabicGraph_removal hN⟩)
    (Or.inr (Or.inr (Or.inl (Or.inl ⟨k, hk.isBivalentRemovable hN,
      PlabicData.Isomorphic.refl _⟩)))) (Relation.ReflTransGen.single ?_)
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hk.removalDart hN, ?_,
    hk.isContractibleEdge_removal hN, PlabicData.Isomorphic.refl _⟩)))
  rintro (⟨⟨-, h⟩, -⟩ | ⟨⟨-, h⟩, -⟩)
  · rw [hcard] at h
    change (N.vertexOf (N.inv k)).card = 1 at h
    rw [hk.card_vertexOf_inv hN] at h
    omega
  · rw [hcard, hinv, hk.card_vertexOf_inv_rot hN] at h
    omega

private theorem IsNormalFlipVertex.coe_contracted_inv (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) (z) : ((hk.contracted hN).inv z).1.1 = N.inv z.1.1 := by
  have hz := (hk.mem_compl_iff hN z.1).1 z.2
  unfold contracted
  rw [coe_contractEdge_inv (G := hk.removal hN) (bivalentRemoval_inv_involutive hN.toIsPlabicGraph
    (hk.isBivalentRemovable hN))]
  exact coe_bivalentRemoval_inv_of_ne hN.toIsPlabicGraph _ hz.1 hz.2

private theorem IsNormalFlipVertex.mem_contracted_bdry (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) (z) : z ∈ (hk.contracted hN).bdry ↔ z.1.1 ∈ N.bdry := by
  unfold contracted
  rw [mem_contractEdge_bdry]
  exact mem_bivalentRemoval_bdry _ _

private theorem IsNormalFlipVertex.isBoundaryVertex_contracted_iff (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) (z) :
    (hk.contracted hN).IsBoundaryVertex ((hk.contracted hN).vertexOf z) ↔
      N.IsBoundaryVertex (N.vertexOf z.1.1) := by
  unfold contracted
  rw [isBoundaryVertex_vertexOf_contractEdge_iff (hk.isContractibleEdge_removal hN)]
  exact isBoundaryVertex_bivalentRemoval_vertexOf_iff _ _ _

/-- The rotation of the contraction: with `x = k̄`, `y = \overline{σk}`, the merged white vertex
is `(σx, σ²x, σy, σ²y)`, and the rotation is `σ` elsewhere. -/
private theorem IsNormalFlipVertex.coe_contracted_rot (hN : N.IsNormalPlabicGraph)
    (hk : N.IsNormalFlipVertex k) (z) :
    ((hk.contracted hN).rot z).1.1 =
      if z.1.1 = N.rot (N.rot (N.inv k)) then N.rot (N.inv (N.rot k))
      else if z.1.1 = N.rot (N.rot (N.inv (N.rot k))) then N.rot (N.inv k)
      else N.rot z.1.1 := by
  have hx3 := rot_rot_rot_of_card_vertexOf_eq_three (hk.card_vertexOf_inv hN)
  have hy3 := rot_rot_rot_of_card_vertexOf_eq_three (hk.card_vertexOf_inv_rot hN)
  have hnd := hk.nodup hN
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨m1, m2, m3, m4⟩, ⟨l1, l2, l3⟩, ⟨o1, o2⟩, p1⟩ := hnd
  have hinv := hk.coe_removal_inv_removalDart hN
  have hz := (hk.mem_compl_iff hN z.1).1 z.2
  have hmem : ∀ w : (({k, N.rot k}ᶜ : Set H)), (w : H) ≠ N.inv k → (w : H) ≠ N.inv (N.rot k) →
      w ∈ (({hk.removalDart hN, (hk.removal hN).inv (hk.removalDart hN)} : Set _)ᶜ : Set _) :=
    fun w h1 h2 => (hk.mem_compl_iff hN w).2 ⟨h1, h2⟩
  by_cases h1 : z.1.1 = N.rot (N.rot (N.inv k))
  · rw [if_pos h1]
    have hrz : (hk.removal hN).rot z.1 = hk.removalDart hN :=
      Subtype.ext (by change N.rot z.1.1 = N.inv k; rw [h1, hx3])
    have e := coe_contractEdge_rot_of_eq (G := hk.removal hN)
      (hleg := (hk.isContractibleEdge_removal hN).leg_mem (hk.isPlabicGraph_removal hN)) hrz
      (hmem _ (by change N.rot _ ≠ _; rw [hinv]; exact Ne.symm n5)
        (by change N.rot _ ≠ _; rw [hinv]; exact Ne.symm p1))
    unfold contracted
    rw [e]
    change N.rot _ = _
    rw [hinv]
  rw [if_neg h1]
  by_cases h2 : z.1.1 = N.rot (N.rot (N.inv (N.rot k)))
  · rw [if_pos h2]
    have hrz : (hk.removal hN).rot z.1 = (hk.removal hN).inv (hk.removalDart hN) :=
      Subtype.ext (by change N.rot z.1.1 = _; rw [hinv, h2, hy3])
    have e := coe_contractEdge_rot_of_eq_inv (G := hk.removal hN)
      (hleg := (hk.isContractibleEdge_removal hN).leg_mem (hk.isPlabicGraph_removal hN)) hrz
      (hmem _ (Ne.symm n1) m3)
    unfold contracted
    rw [e]
    rfl
  rw [if_neg h2]
  have e := coe_contractEdge_rot_of_mem (G := hk.removal hN) (x := z)
    (hleg := (hk.isContractibleEdge_removal hN).leg_mem (hk.isPlabicGraph_removal hN))
    (hmem _ (fun h => h1 (N.rot.injective (by rw [hx3]; exact h)))
      (fun h => h2 (N.rot.injective (by rw [hy3]; exact h))))
  unfold contracted
  rw [e]
  rfl

/-- The normal flip `G'` of `G` at `u = {k, σk}` again has a normal flip vertex at `k`, with the
same rotation at `u`. -/
private theorem IsNormalFlipVertex.rot_normalFlip_and_isNormalFlipVertex
    (hN : N.IsNormalPlabicGraph) (hk : N.IsNormalFlipVertex k) :
    (N.normalFlip k).rot k = N.rot k ∧ (N.normalFlip k).IsNormalFlipVertex k := by
  have hN' := hk.isNormalPlabicGraph_normalFlip hN
  have hcol := hk.colour_normalFlip hN
  have hvk := hk.vertexOf_normalFlip hN
    (fun h => by have := hk.card_vertexOf; rw [h, hk.card_vertexOf_inv hN] at this; omega)
    (fun h => by have := hk.card_vertexOf; rw [h, hk.card_vertexOf_inv_rot hN] at this; omega)
  have hrk : (N.normalFlip k).rot k = N.rot k := hvk.2 k (N.self_mem_vertexOf k)
  have hnd := hk.nodup hN
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨m1, m2, m3, m4⟩, ⟨l1, l2, l3⟩, ⟨o1, o2⟩, p1⟩ := hnd
  obtain ⟨r1, r2, -, -, -, -⟩ := hk.rot_normalFlip hN
  refine ⟨hrk, ⟨fun h => hk.not_isBoundaryVertex ((hcol k).1.1 h),
    ((hcol k).2 hk.not_isBoundaryVertex).trans hk.colour_eq, by rw [hvk.1]; exact hk.card_vertexOf,
    fun h => hk.not_isBoundaryVertex_inv ((hcol (N.inv k)).1.1 h),
    ((hcol (N.inv k)).2 hk.not_isBoundaryVertex_inv).trans hk.colour_inv, ?_, ?_, ?_⟩⟩
  · rw [hrk]
    exact fun h => hk.not_isBoundaryVertex_inv_rot ((hcol _).1.1 h)
  · rw [hrk]
    exact ((hcol _).2 hk.not_isBoundaryVertex_inv_rot).trans hk.colour_inv_rot
  · rw [hrk]
    intro h
    have hx : ¬(N.normalFlip k).IsBoundaryVertex ((N.normalFlip k).vertexOf (N.inv k)) :=
      fun h => hk.not_isBoundaryVertex_inv ((hcol (N.inv k)).1.1 h)
    have hc3 := hN'.card_vertexOf_of_white _ hx
      (((hcol (N.inv k)).2 hk.not_isBoundaryVertex_inv).trans hk.colour_inv)
    have hy : N.inv (N.rot k) ∈ (N.normalFlip k).vertexOf (N.inv k) := by
      change N.inv (N.rot k) ∈ (N.normalFlip k).vertexOf ((N.normalFlip k).inv k)
      rw [h]
      exact (N.normalFlip k).self_mem_vertexOf _
    rw [vertexOf_eq_of_card_vertexOf_eq_three hc3, r1, r2] at hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with hy | hy | hy
    · exact n4 hy.symm
    · exact o1 hy.symm
    · exact p1 hy

/-- If `G'` is the normal flip `normalFlip` of the normal plabic graph `G` at a normal flip
vertex `u = {k, σk}`, then `G ∘∼ G'`. -/
@[cluster_algebras "lem_normal_flip_circ"]
theorem IsNormalFlipVertex.circMoveEquivalent {G : PlabicData H b} (hG : G.IsNormalPlabicGraph)
    (hk : G.IsNormalFlipVertex k) :
    PlabicGraph.CircMoveEquivalent ⟨H, G, hG.toIsPlabicGraph⟩
      ⟨H, G.normalFlip k, (hk.isNormalPlabicGraph_normalFlip hG).toIsPlabicGraph⟩ := by
  have hG' := hk.isNormalPlabicGraph_normalFlip hG
  obtain ⟨hrk, hk'⟩ := hk.rot_normalFlip_and_isNormalFlipVertex hG
  have hnd := hk.nodup hG
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨n1, n2, n3, n4, n5⟩, ⟨m1, m2, m3, m4⟩, ⟨l1, l2, l3⟩, ⟨o1, o2⟩, p1⟩ := hnd
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hk.rot_normalFlip hG
  have hi : (G.normalFlip k).inv = G.inv := rfl
  let e₁ : (({k, G.rot k}ᶜ : Set H)) ≃ (({k, (G.normalFlip k).rot k}ᶜ : Set H)) :=
    Equiv.subtypeEquiv (Equiv.refl H) fun a => by rw [hrk]; rfl
  let e : _ ≃ _ := Equiv.subtypeEquiv (q := fun w => w ∈
      (({hk'.removalDart hG', (hk'.removal hG').inv (hk'.removalDart hG')} : Set _)ᶜ : Set _))
    (p := fun w => w ∈
      (({hk.removalDart hG, (hk.removal hG).inv (hk.removalDart hG)} : Set _)ᶜ : Set _)) e₁
    fun a => by
      have ha : ((e₁ a : H)) = a := rfl
      rw [hk.mem_compl_iff hG, hk'.mem_compl_iff hG', ha, hrk]
      rfl
  have θ : (hk.contracted hG).Iso (hk'.contracted hG') :=
    { toEquiv := e
      map_inv := fun z => by
        apply Subtype.ext; apply Subtype.ext
        change ((hk.contracted hG).inv z).1.1 = _
        rw [hk.coe_contracted_inv hG, hk'.coe_contracted_inv hG']
        rfl
      map_rot := fun z => by
        apply Subtype.ext; apply Subtype.ext
        change ((hk.contracted hG).rot z).1.1 = _
        rw [hk.coe_contracted_rot hG, hk'.coe_contracted_rot hG']
        have hez : (e z).1.1 = z.1.1 := rfl
        rw [hez, hi, hrk, r1, r2, r4, r5]
        have hz := (hk.mem_compl_iff hG z.1).1 z.2
        by_cases h1 : z.1.1 = G.rot (G.rot (G.inv k))
        · rw [if_pos h1, if_neg (by rw [h1]; exact o2), if_neg (by rw [h1]; exact Ne.symm m2),
            h1, r2]
        rw [if_neg h1]
        by_cases h2 : z.1.1 = G.rot (G.rot (G.inv (G.rot k)))
        · rw [if_pos h2, if_neg (by rw [h2]; exact l3), if_neg (by rw [h2]; exact Ne.symm m1),
            h2, r5]
        rw [if_neg h2]
        by_cases h3 : z.1.1 = G.rot (G.inv (G.rot k))
        · rw [if_pos h3, h3]
        rw [if_neg h3]
        by_cases h4 : z.1.1 = G.rot (G.inv k)
        · rw [if_pos h4, h4]
        rw [if_neg h4]
        change _ = G.rot (G.normalFlipPerm k z.1.1)
        rw [normalFlipPerm_apply_of_notMem]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hz.1, h4, h2, h1, hz.2, h3⟩
      mem_bdry_iff := fun z => by
        rw [hk'.mem_contracted_bdry hG', hk.mem_contracted_bdry hG]
        rfl
      map_colour := fun z hz => by
        rw [hk.isBoundaryVertex_contracted_iff hG] at hz
        exact (hk.colour_normalFlip hG z.1.1).2 hz
      map_bvertex := fun i => by
        rw [(hk.isPlabicGraph_contracted hG).filter_bvertex_notMem_bdry,
          (hk'.isPlabicGraph_contracted hG').filter_bvertex_notMem_bdry, map_singleton]
        rfl }
  exact (hk.circMoveEquivalent_contracted hG).trans (Relation.ReflTransGen.head
    (Or.inl ⟨θ.symm⟩) (hk'.circMoveEquivalent_contracted hG').symm)

end PlabicData

/-! ### Splitting two vertices -/

namespace PlabicData


section DoubleSplit

variable {H : Type*} [DecidableEq H] {b : ℕ} (K : PlabicData H b)

/-- The dart of a splitting of `K` at `s₁` followed by a splitting at `s₂` which stands for the old
dart `z` after `σ`: the new dart before `s₁` if `z = s₁`, the new dart before `s₂` if `z = s₂`,
and `z` itself otherwise. -/
private def dsR (s₁ s₂ z : H) : (H ⊕ Fin 2) ⊕ Fin 2 :=
  if z = s₁ then .inl (.inr 1) else if z = s₂ then .inr 1 else .inl (.inl z)

private theorem rot_vertexSplit_two_inl (s x : H) : (K.vertexSplit s 2).rot (.inl x) =
    if x = K.rot s then .inr 0 else if K.rot x = s then .inr 1 else .inl (K.rot x) := by
  rw [rot_vertexSplit, splitRot_inl]
  simp

private theorem rot_vertexSplit_two_inr_zero (s : H) :
    (K.vertexSplit s 2).rot (.inr 0) = .inl s := by
  rw [rot_vertexSplit, splitRot_inr_zero]
  simp

private theorem rot_vertexSplit_two_inr_one (s : H) : (K.vertexSplit s 2).rot (.inr 1) =
    if K.rot (K.rot s) = s then .inr 1 else .inl (K.rot (K.rot s)) := by
  rw [rot_vertexSplit, splitRot_inr_one]
  simp [sq, Perm.mul_apply]

variable {K} {s₁ s₂ : H} (h12 : s₁ ≠ s₂) (h1 : s₂ ≠ K.rot s₁) (h2 : K.rot s₂ ≠ s₁)

include h1 h2

private theorem rot_vertexSplit_two_inl_s₂ :
    (K.vertexSplit s₁ 2).rot (.inl s₂) = .inl (K.rot s₂) := by
  rw [rot_vertexSplit_two_inl, if_neg h1, if_neg h2]

include h12

/-- The rotation of a double splitting at an old dart. -/
private theorem rot_doubleSplit_inl_inl (x : H) :
    ((K.vertexSplit s₁ 2).vertexSplit (.inl s₂) 2).rot (.inl (.inl x)) =
      if x = K.rot s₂ then .inr 0 else if x = K.rot s₁ then .inl (.inr 0)
      else dsR s₁ s₂ (K.rot x) := by
  rw [rot_vertexSplit_two_inl (K := K.vertexSplit s₁ 2), rot_vertexSplit_two_inl_s₂ h1 h2,
    rot_vertexSplit_two_inl]
  have h12' : K.rot s₁ ≠ K.rot s₂ := fun h => h12 (K.rot.injective h)
  by_cases hx2 : x = K.rot s₂
  · simp [hx2]
  by_cases hx1 : x = K.rot s₁
  · simp [hx1, h12']
  by_cases hy1 : K.rot x = s₁
  · simp [hx1, hx2, hy1, dsR]
  by_cases hy2 : K.rot x = s₂
  · simp [hx1, hx2, hy2, dsR, h12.symm]
  · simp [hx1, hx2, hy1, hy2, dsR]

omit h12 in
/-- The rotation of a double splitting at the first new dart `n₁`. -/
private theorem rot_doubleSplit_inl_inr_zero (h12 : s₁ ≠ s₂) :
    ((K.vertexSplit s₁ 2).vertexSplit (.inl s₂) 2).rot (.inl (.inr 0)) = .inl (.inl s₁) := by
  rw [rot_vertexSplit_two_inl (K := K.vertexSplit s₁ 2), rot_vertexSplit_two_inl_s₂ h1 h2,
    rot_vertexSplit_two_inr_zero]
  simp [h12]

/-- The rotation of a double splitting at the first new dart `n̄₁`. -/
private theorem rot_doubleSplit_inl_inr_one :
    ((K.vertexSplit s₁ 2).vertexSplit (.inl s₂) 2).rot (.inl (.inr 1)) =
      dsR s₁ s₂ (K.rot (K.rot s₁)) := by
  rw [rot_vertexSplit_two_inl (K := K.vertexSplit s₁ 2), rot_vertexSplit_two_inl_s₂ h1 h2,
    rot_vertexSplit_two_inr_one]
  by_cases hy1 : K.rot (K.rot s₁) = s₁
  · simp [hy1, dsR]
  by_cases hy2 : K.rot (K.rot s₁) = s₂
  · simp [hy2, dsR, h12.symm]
  · simp [hy1, hy2, dsR]

omit h12 h1 h2 in
/-- The rotation of a double splitting at the second new dart `n₂`. -/
private theorem rot_doubleSplit_inr_zero :
    ((K.vertexSplit s₁ 2).vertexSplit (.inl s₂) 2).rot (.inr 0) = .inl (.inl s₂) := by
  rw [rot_vertexSplit_two_inr_zero]

/-- The rotation of a double splitting at the second new dart `n̄₂`. -/
private theorem rot_doubleSplit_inr_one :
    ((K.vertexSplit s₁ 2).vertexSplit (.inl s₂) 2).rot (.inr 1) =
      dsR s₁ s₂ (K.rot (K.rot s₂)) := by
  rw [rot_vertexSplit_two_inr_one, rot_vertexSplit_two_inl_s₂ h1 h2,
    rot_vertexSplit_two_inl]
  have h12' : K.rot s₁ ≠ K.rot s₂ := fun h => h12 (K.rot.injective h)
  by_cases hy1 : K.rot (K.rot s₂) = s₁
  · simp [hy1, h12'.symm, dsR]
  by_cases hy2 : K.rot (K.rot s₂) = s₂
  · simp [hy2, h12'.symm, dsR, h12.symm]
  · simp [hy1, hy2, h12'.symm, dsR]

end DoubleSplit

/-! ### The bijection of urban renewal -/

section UrbanTheta

variable {H : Type*} [DecidableEq H] {b : ℕ}

/-- The bijection `θ` of the darts `(H ⊔ {n₁, n̄₁}) ⊔ {n₂, n̄₂}` attached to twelve darts
`v 0, …, v 11`, standing for `c̄₁, c₂, e₄, e₂, c̄₃, c₄, c̄₄, c₁, ē₄, c̄₂, c₃, ē₂` of urban renewal:
the product of the cycles `(n₁ c₄ c₁ e₂)`, `(n̄₁ c̄₄ c̄₁ ē₂)`, `(n₂ c₂ c₃ e₄)` and
`(n̄₂ c̄₂ c̄₃ ē₄)`. -/
private def urbanTheta (v : Fin 12 → H) : Perm ((H ⊕ Fin 2) ⊕ Fin 2) :=
  [.inl (.inr 0), .inl (.inl (v 5)), .inl (.inl (v 7)), .inl (.inl (v 3))].formPerm *
    [.inl (.inr 1), .inl (.inl (v 6)), .inl (.inl (v 0)), .inl (.inl (v 11))].formPerm *
    [.inr 0, .inl (.inl (v 1)), .inl (.inl (v 10)), .inl (.inl (v 2))].formPerm *
    [.inr 1, .inl (.inl (v 9)), .inl (.inl (v 4)), .inl (.inl (v 8))].formPerm

variable {v : Fin 12 → H} (hv : Injective v)

include hv

private theorem urbanTheta_inl_inl (x : H) : urbanTheta v (.inl (.inl x)) =
    if x = v 5 then .inl (.inl (v 7)) else if x = v 7 then .inl (.inl (v 3))
    else if x = v 3 then .inl (.inr 0) else if x = v 6 then .inl (.inl (v 0))
    else if x = v 0 then .inl (.inl (v 11)) else if x = v 11 then .inl (.inr 1)
    else if x = v 1 then .inl (.inl (v 10)) else if x = v 10 then .inl (.inl (v 2))
    else if x = v 2 then .inr 0 else if x = v 9 then .inl (.inl (v 4))
    else if x = v 4 then .inl (.inl (v 8)) else if x = v 8 then .inr 1 else .inl (.inl x) := by
  by_cases h : ∃ i, x = v i
  · obtain ⟨i, rfl⟩ := h
    fin_cases i <;>
      simp [urbanTheta, Perm.mul_apply, List.formPerm_cons_cons, swap_apply_def, hv.eq_iff]
  · push Not at h
    simp [urbanTheta, Perm.mul_apply, List.formPerm_cons_cons, swap_apply_def, h]

private theorem urbanTheta_new :
    urbanTheta v (.inl (.inr 0)) = .inl (.inl (v 5)) ∧
      urbanTheta v (.inl (.inr 1)) = .inl (.inl (v 6)) ∧
      urbanTheta v (.inr 0) = .inl (.inl (v 1)) ∧
      urbanTheta v (.inr 1) = .inl (.inl (v 9)) := by
  simp [urbanTheta, Perm.mul_apply, List.formPerm_cons_cons, swap_apply_def, hv.eq_iff]

/-- `θ` carries the dart standing for `z` in the double splitting at `c̄₄, c̄₂` to the dart
standing for `z` in the double splitting at `ē₂, ē₄`, for
`z ∉ {c₄, c₁, e₂, c̄₁, c₂, c₃, e₄, c̄₃}`. -/
private theorem urbanTheta_dsR {z : H} (h5 : z ≠ v 5) (h7 : z ≠ v 7) (h3 : z ≠ v 3)
    (h0 : z ≠ v 0) (h1 : z ≠ v 1) (h10 : z ≠ v 10) (h2 : z ≠ v 2) (h4 : z ≠ v 4) :
    urbanTheta v (dsR (v 6) (v 9) z) = dsR (v 11) (v 8) z := by
  obtain ⟨u0, u1, u2, u3⟩ := urbanTheta_new hv
  by_cases h6 : z = v 6
  · subst h6
    simp [dsR, u1, hv.eq_iff]
  by_cases h9 : z = v 9
  · subst h9
    simp [dsR, u3, hv.eq_iff]
  by_cases h11 : z = v 11
  · subst h11
    simp [dsR, urbanTheta_inl_inl hv, hv.eq_iff]
  by_cases h8 : z = v 8
  · subst h8
    simp [dsR, urbanTheta_inl_inl hv, hv.eq_iff]
  simp [dsR, urbanTheta_inl_inl hv, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- `θ` intertwines the rotation of the double splitting of `K` at `c̄₄` and `c̄₂` with the
rotation of the double splitting of `K'` at `ē₂` and `ē₄`, when `K` has the rotations of the
corners of an urban renewal face and `K'` has the rotation of its urban renewal. -/
private theorem urbanTheta_map_rot {K K' : PlabicData H b}
    (s₁ : K.rot (v 6) = v 7) (s₂ : K.rot (v 0) = v 1) (s₃ : K.rot (v 1) = v 3)
    (s₄ : K.rot (v 3) = v 0) (s₅ : K.rot (v 9) = v 10) (s₆ : K.rot (v 4) = v 5)
    (s₇ : K.rot (v 5) = v 2) (s₈ : K.rot (v 2) = v 4)
    (t₀ : K'.rot (v 0) = v 3) (t₁ : K'.rot (v 1) = v 4) (t₂ : K'.rot (v 2) = v 1)
    (t₃ : K'.rot (v 3) = v 5) (t₄ : K'.rot (v 4) = v 2) (t₅ : K'.rot (v 5) = v 0)
    (t₆ : K'.rot (v 6) = K.rot (v 7)) (t₇ : K'.rot (v 7) = K.rot (v 8))
    (t₈ : K'.rot (v 8) = v 7) (t₉ : K'.rot (v 9) = K.rot (v 10))
    (t₁₀ : K'.rot (v 10) = K.rot (v 11)) (t₁₁ : K'.rot (v 11) = v 10)
    (hfix : ∀ x, (∀ i, x ≠ v i) → K'.rot x = K.rot x) (y : (H ⊕ Fin 2) ⊕ Fin 2) :
    urbanTheta v (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot y) =
      ((K'.vertexSplit (v 11) 2).vertexSplit (.inl (v 8)) 2).rot (urbanTheta v y) := by
  have hne : ∀ {i j : Fin 12}, i ≠ j → v i ≠ v j := hv.ne
  have d12 : v 6 ≠ v 9 := hne (by decide)
  have d1 : v 9 ≠ K.rot (v 6) := by rw [s₁]; exact hne (by decide)
  have d2 : K.rot (v 9) ≠ v 6 := by rw [s₅]; exact hne (by decide)
  have e12 : v 11 ≠ v 8 := hne (by decide)
  have e1 : v 8 ≠ K'.rot (v 11) := by rw [t₁₁]; exact hne (by decide)
  have e2 : K'.rot (v 8) ≠ v 11 := by rw [t₈]; exact hne (by decide)
  obtain ⟨u0, u1, u2, u3⟩ := urbanTheta_new hv
  have key : ∀ x, x ≠ v 4 → x ≠ v 6 → x ≠ v 1 → x ≠ v 3 → x ≠ v 0 → x ≠ v 9 → x ≠ v 5 →
      x ≠ v 2 → urbanTheta v (dsR (v 6) (v 9) (K.rot x)) = dsR (v 11) (v 8) (K.rot x) :=
    fun x h4 h6 h1 h3 h0 h9 h5 h2 => urbanTheta_dsR hv
      (fun h => h4 (K.rot.injective (h.trans s₆.symm)))
      (fun h => h6 (K.rot.injective (h.trans s₁.symm)))
      (fun h => h1 (K.rot.injective (h.trans s₃.symm)))
      (fun h => h3 (K.rot.injective (h.trans s₄.symm)))
      (fun h => h0 (K.rot.injective (h.trans s₂.symm)))
      (fun h => h9 (K.rot.injective (h.trans s₅.symm)))
      (fun h => h5 (K.rot.injective (h.trans s₇.symm)))
      (fun h => h2 (K.rot.injective (h.trans s₈.symm)))
  have DL := rot_doubleSplit_inl_inl d12 d1 d2
  have DL' := rot_doubleSplit_inl_inl e12 e1 e2
  rw [s₁, s₅] at DL
  rw [t₈, t₁₁] at DL'
  have R0' := rot_doubleSplit_inl_inr_zero e1 e2 e12
  have R1' := rot_doubleSplit_inl_inr_one e12 e1 e2
  have Q0' := rot_doubleSplit_inr_zero (K := K') (s₁ := v 11) (s₂ := v 8)
  have Q1' := rot_doubleSplit_inr_one e12 e1 e2
  rw [t₁₁] at R1'
  rw [t₈] at Q1'
  rcases y with (x | i) | i
  · by_cases h8 : x = v 8
    · subst h8
      rw [DL, if_neg (show v 8 ≠ v 10 from hne (by decide)),
        if_neg (show v 8 ≠ v 7 from hne (by decide)), key (v 8) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide))]
      simp [-rot_vertexSplit, hv.eq_iff, urbanTheta_inl_inl hv, Q1', t₇]
    by_cases h11 : x = v 11
    · subst h11
      rw [DL, if_neg (show v 11 ≠ v 10 from hne (by decide)),
        if_neg (show v 11 ≠ v 7 from hne (by decide)), key (v 11) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide))]
      simp [-rot_vertexSplit, hv.eq_iff, urbanTheta_inl_inl hv, R1', t₁₀]
    by_cases hx : ∃ i, x = v i
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i
      all_goals try exact (h8 rfl).elim
      all_goals try exact (h11 rfl).elim
      all_goals (rw [DL]; simp [-rot_vertexSplit, hv.eq_iff, dsR, urbanTheta_inl_inl hv, u0, u2,
        DL', R0', Q0', s₁, s₂, s₃, s₄, s₅, s₆, s₇, s₈, t₀, t₂, t₃, t₄, t₈, t₁₁])
    · push Not at hx
      rw [DL, if_neg (hx 10), if_neg (hx 7), key x (hx 4) (hx 6) (hx 1) (hx 3) (hx 0) (hx 9)
        (hx 5) (hx 2), urbanTheta_inl_inl hv]
      simp only [hx, if_false]
      rw [DL', if_neg (hx 7), if_neg (hx 10), hfix x hx]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [rot_doubleSplit_inl_inr_zero d1 d2 d12, u0, DL', urbanTheta_inl_inl hv]
      simp [hv.eq_iff, dsR, t₅]
    · rw [rot_doubleSplit_inl_inr_one d12 d1 d2, s₁, key (v 7) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide)), u1, DL',
        if_neg (hne (by decide)), if_neg (hne (by decide)), t₆]
  · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [rot_doubleSplit_inr_zero, u2, DL', urbanTheta_inl_inl hv]
      simp [hv.eq_iff, dsR, t₁]
    · rw [rot_doubleSplit_inr_one d12 d1 d2, s₅, key (v 10) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
        (hne (by decide)) (hne (by decide)) (hne (by decide)), u3, DL',
        if_neg (hne (by decide)), if_neg (hne (by decide)), t₉]

/-- `θ` commutes with the involution of the double splittings, when the involution pairs the twelve
darts as `c̄₁ ↔ c₁`, `c₂ ↔ c̄₂`, `e₄ ↔ ē₄`, `e₂ ↔ ē₂`, `c̄₃ ↔ c₃`, `c₄ ↔ c̄₄`. -/
private theorem urbanTheta_map_inv {ι : Perm H} (hι : Involutive ι)
    (i₀ : ι (v 0) = v 7) (i₁ : ι (v 1) = v 9) (i₂ : ι (v 2) = v 8) (i₃ : ι (v 3) = v 11)
    (i₄ : ι (v 4) = v 10) (i₅ : ι (v 5) = v 6) (y : (H ⊕ Fin 2) ⊕ Fin 2) :
    urbanTheta v (splitInv (splitInv ι) y) = splitInv (splitInv ι) (urbanTheta v y) := by
  have j₀ : ι (v 7) = v 0 := by rw [← i₀, hι]
  have j₁ : ι (v 9) = v 1 := by rw [← i₁, hι]
  have j₂ : ι (v 8) = v 2 := by rw [← i₂, hι]
  have j₃ : ι (v 11) = v 3 := by rw [← i₃, hι]
  have j₄ : ι (v 10) = v 4 := by rw [← i₄, hι]
  have j₅ : ι (v 6) = v 5 := by rw [← i₅, hι]
  obtain ⟨u0, u1, u2, u3⟩ := urbanTheta_new hv
  rcases y with (x | i) | i
  · by_cases hx : ∃ i, x = v i
    · obtain ⟨i, rfl⟩ := hx
      fin_cases i <;> simp [urbanTheta_inl_inl hv, hv.eq_iff, i₀, i₁, i₂, i₃, i₄, i₅, j₀, j₁, j₂,
        j₃, j₄, j₅]
    · push Not at hx
      have hx' : ∀ i, ι x ≠ v i := by
        intro i h
        have hx2 : x = ι (v i) := by rw [← h, hι]
        fin_cases i
        · exact hx 7 (by simpa [i₀] using hx2)
        · exact hx 9 (by simpa [i₁] using hx2)
        · exact hx 8 (by simpa [i₂] using hx2)
        · exact hx 11 (by simpa [i₃] using hx2)
        · exact hx 10 (by simpa [i₄] using hx2)
        · exact hx 6 (by simpa [i₅] using hx2)
        · exact hx 5 (by simpa [j₅] using hx2)
        · exact hx 0 (by simpa [j₀] using hx2)
        · exact hx 2 (by simpa [j₂] using hx2)
        · exact hx 1 (by simpa [j₁] using hx2)
        · exact hx 4 (by simpa [j₄] using hx2)
        · exact hx 3 (by simpa [j₃] using hx2)
      simp [urbanTheta_inl_inl hv, hx, hx']
  · fin_cases i <;> simp [i₅, j₅, u0, u1]
  · fin_cases i <;> simp [i₁, j₁, u2, u3]

end UrbanTheta

/-! ### Splittings at internal vertices -/

section SplitStep

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-- A set mapped into itself by a permutation of a finite set contains the cycles of its
elements. -/
private theorem mem_of_sameCycle_of_mapsTo' {X : Type*} [Finite X] {σ : Perm X} {A : Set X}
    (hA : ∀ a ∈ A, σ a ∈ A) {x y : X} (hx : x ∈ A) (h : σ.SameCycle x y) : y ∈ A := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact Set.MapsTo.perm_pow hA n hx

/-- A vertex visited by a `3`-cycle of the rotation consists of the three darts of the cycle. -/
private theorem vertexOf_eq_of_rot_three' (K : PlabicData H b) {a₁ a₂ a₃ : H}
    (h₁ : K.rot a₁ = a₂) (h₂ : K.rot a₂ = a₃) (h₃ : K.rot a₃ = a₁) :
    K.vertexOf a₁ = {a₁, a₂, a₃} := by
  ext y
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro h
    have hA : ∀ a ∈ ({a₁, a₂, a₃} : Set H), K.rot a ∈ ({a₁, a₂, a₃} : Set H) := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl
      · exact Or.inr (Or.inl h₁)
      · exact Or.inr (Or.inr h₂)
      · exact Or.inl h₃
    simpa using mem_of_sameCycle_of_mapsTo' hA (by simp) h
  · simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact SameCycle.refl _ _
    · rw [← h₁]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · rw [← h₂, ← h₁]
      exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-- In a splitting at an internal vertex, the vertex of an old dart `x` is a boundary vertex
exactly when the vertex of `x` is one. -/
private theorem isBoundaryVertex_vertexSplit_inl_iff {K : PlabicData H b} {s : H}
    (hs : ¬K.IsBoundaryVertex (K.vertexOf s)) (p : ℕ) (x : H) :
    (K.vertexSplit s p).IsBoundaryVertex ((K.vertexSplit s p).vertexOf (.inl x)) ↔
      K.IsBoundaryVertex (K.vertexOf x) := by
  by_cases hx : K.rot.SameCycle s x
  · have hvx : K.vertexOf x = K.vertexOf s := K.vertexOf_eq_of_mem (K.mem_vertexOf.2 hx)
    rw [hvx, iff_false_right hs]
    rintro ⟨e, he, heB⟩
    let A : Set (H ⊕ Fin 2) := {e | ∀ y, e = .inl y → K.rot.SameCycle s y}
    have hA : ∀ a ∈ A, (K.vertexSplit s p).rot a ∈ A := by
      rintro (z | i) hz y hy
      · rw [rot_vertexSplit, splitRot_inl] at hy
        obtain rfl : y = K.rot z := by
          split_ifs at hy
          exact (Sum.inl.inj hy).symm
        exact (hz z rfl).trans (sameCycle_apply_right.2 (SameCycle.refl _ _))
      · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
        · rw [rot_vertexSplit, splitRot_inr_zero] at hy
          obtain rfl : y = s := by
            split_ifs at hy
            exact (Sum.inl.inj hy).symm
          exact SameCycle.refl _ _
        · rw [rot_vertexSplit, splitRot_inr_one] at hy
          obtain rfl : y = (K.rot ^ p) s := by
            split_ifs at hy
            exact (Sum.inl.inj hy).symm
          exact sameCycle_pow_right.2 (SameCycle.refl _ _)
    have heA := mem_of_sameCycle_of_mapsTo' hA (x := .inl x)
      (fun y hy => by cases hy; exact hx) ((RotationSystem.mem_vertexOf _).1 he)
    rw [bdry_vertexSplit, mem_map] at heB
    obtain ⟨y, hyB, rfl⟩ := heB
    exact hs ⟨y, K.mem_vertexOf.2 (heA y rfl), hyB⟩
  · rw [vertexOf_vertexSplit_inl K s p hx, isBoundaryVertex_map_inl_iff]

end SplitStep

section SplitStepType

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}

/-- The splitting of a plabic graph at a black internal vertex `v(s)` from `s` of size `2` is a
step of `∘∼` to the graph: its contraction along the new edge, which joins two black vertices. -/
private theorem circStep_vertexSplit {K : PlabicData H b} (hK : K.IsPlabicGraph) {s : H}
    (hs : ¬K.IsBoundaryVertex (K.vertexOf s)) (hrot : K.rot s ≠ s) (hcol : K.colour s = .black) :
    PlabicGraph.CircStep ⟨_, K.vertexSplit s 2, hK.vertexSplit hs 2⟩ ⟨H, K, hK⟩ := by
  have hp : 2 ≤ (K.vertexOf s).card := by
    have hsub : ({s, K.rot s} : Finset H) ⊆ K.vertexOf s := by
      intro e he
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl
      · exact K.self_mem_vertexOf _
      · exact K.rot_mem_vertexOf _
    have h2 := Finset.card_le_card hsub
    rwa [Finset.card_pair hrot.symm] at h2
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨Sum.inr 0, ?_, isContractibleEdge_vertexSplit K s 2 hs hp,
    isomorphic_contractEdge_vertexSplit K s 2 hK.inv_involutive⟩)))
  rintro (⟨-, h, -⟩ | ⟨-, -, h, -⟩) <;> simp [hcol] at h

end SplitStepType

/-! ### The double splitting at an urban renewal face -/

section UrbanSplit

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-- Twelve pairwise distinct darts `v 0, …, v 11` at internal vertices of `K`, standing for the
darts `c̄₁, c₂, e₄, e₂, c̄₃, c₄, c̄₄, c₁, ē₄, c̄₂, c₃, ē₂` of an urban renewal face: the first six
are white and the last six black, `σ` has the cycles `(c̄₁ c₂ e₂)` and `(c̄₃ c₄ e₄)` and maps
`c̄₄ ↦ c₁`, `c̄₂ ↦ c₃`, and the involution pairs them as `c̄₁ ↔ c₁`, `c₂ ↔ c̄₂`, `e₄ ↔ ē₄`,
`e₂ ↔ ē₂`, `c̄₃ ↔ c₃`, `c₄ ↔ c̄₄`. -/
private structure UrbanDarts (K : PlabicData H b) (v : Fin 12 → H) : Prop where
  inj : Injective v
  inv_involutive : Involutive K.inv
  not_isBoundaryVertex : ∀ i, ¬K.IsBoundaryVertex (K.vertexOf (v i))
  colour_white : ∀ i : Fin 12, i < 6 → K.colour (v i) = .white
  colour_black : ∀ i : Fin 12, 6 ≤ i → K.colour (v i) = .black
  s₁ : K.rot (v 6) = v 7
  s₂ : K.rot (v 0) = v 1
  s₃ : K.rot (v 1) = v 3
  s₄ : K.rot (v 3) = v 0
  s₅ : K.rot (v 9) = v 10
  s₆ : K.rot (v 4) = v 5
  s₇ : K.rot (v 5) = v 2
  s₈ : K.rot (v 2) = v 4
  i₀ : K.inv (v 0) = v 7
  i₁ : K.inv (v 1) = v 9
  i₂ : K.inv (v 2) = v 8
  i₃ : K.inv (v 3) = v 11
  i₄ : K.inv (v 4) = v 10
  i₅ : K.inv (v 5) = v 6

namespace UrbanDarts

variable {K : PlabicData H b} {v : Fin 12 → H}

private theorem notMem_bdry (u : UrbanDarts K v) (i : Fin 12) : v i ∉ K.bdry :=
  fun h => u.not_isBoundaryVertex i ⟨v i, K.self_mem_vertexOf _, h⟩

/-- The rotation of the double splitting at `c̄₄` and `c̄₂` on the darts of the four corners: the
cycles `(c₁ n₁ c̄₄)`, `(c₂ e₂ c̄₁)`, `(c₃ n₂ c̄₂)` and `(c₄ e₄ c̄₃)`. -/
private theorem rot_split (u : UrbanDarts K v) :
    ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 7))) =
        .inl (.inr 0) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inr 0)) =
        .inl (.inl (v 6)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 6))) =
        .inl (.inl (v 7)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 1))) =
        .inl (.inl (v 3)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 3))) =
        .inl (.inl (v 0)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 0))) =
        .inl (.inl (v 1)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 10))) = .inr 0 ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inr 0) = .inl (.inl (v 9)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 9))) =
        .inl (.inl (v 10)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 5))) =
        .inl (.inl (v 2)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 2))) =
        .inl (.inl (v 4)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).rot (.inl (.inl (v 4))) =
        .inl (.inl (v 5)) := by
  have hne : ∀ {i j : Fin 12}, i ≠ j → v i ≠ v j := u.inj.ne
  have d12 : v 6 ≠ v 9 := hne (by decide)
  have d1 : v 9 ≠ K.rot (v 6) := by rw [u.s₁]; exact hne (by decide)
  have d2 : K.rot (v 9) ≠ v 6 := by rw [u.s₅]; exact hne (by decide)
  have DL := rot_doubleSplit_inl_inl d12 d1 d2
  rw [u.s₁, u.s₅] at DL
  refine ⟨?_, rot_doubleSplit_inl_inr_zero d1 d2 d12, ?_, ?_, ?_, ?_, ?_,
    rot_doubleSplit_inr_zero, ?_, ?_, ?_, ?_⟩ <;>
    rw [DL] <;> simp [-rot_vertexSplit, u.inj.eq_iff, dsR, u.s₁, u.s₂, u.s₃, u.s₄, u.s₅, u.s₆,
      u.s₇, u.s₈]

/-- The face `(c₁, c₂, c₃, c₄)` of the double splitting. -/
private theorem facePerm_split (u : UrbanDarts K v) :
    ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).facePerm (.inl (.inl (v 7))) =
        .inl (.inl (v 1)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).facePerm (.inl (.inl (v 1))) =
        .inl (.inl (v 10)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).facePerm (.inl (.inl (v 10))) =
        .inl (.inl (v 5)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).facePerm (.inl (.inl (v 5))) =
        .inl (.inl (v 7)) := by
  obtain ⟨-, -, r6, -, -, r0, -, -, r9, -, -, r4⟩ := u.rot_split
  have j₀ : K.inv (v 7) = v 0 := by rw [← u.i₀, u.inv_involutive]
  have j₄ : K.inv (v 10) = v 4 := by rw [← u.i₄, u.inv_involutive]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [RotationSystem.facePerm_apply]
  · rw [show ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).inv
      (.inl (.inl (v 7))) = .inl (.inl (v 0)) by simp [j₀], r0]
  · rw [show ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).inv
      (.inl (.inl (v 1))) = .inl (.inl (v 9)) by simp [u.i₁], r9]
  · rw [show ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).inv
      (.inl (.inl (v 10))) = .inl (.inl (v 4)) by simp [j₄], r4]
  · rw [show ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).inv
      (.inl (.inl (v 5))) = .inl (.inl (v 6)) by simp [u.i₅], r6]

/-- The corners `c₁, c₂, c₃, c₄` of the face of the double splitting. -/
private theorem squareCorner_split (u : UrbanDarts K v) :
    ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareCorner (.inl (.inl (v 7))) 0 =
        .inl (.inl (v 7)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareCorner (.inl (.inl (v 7))) 1 =
        .inl (.inl (v 1)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareCorner (.inl (.inl (v 7))) 2 =
        .inl (.inl (v 10)) ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareCorner (.inl (.inl (v 7))) 3 =
        .inl (.inl (v 5)) ∧
      (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).facePerm ^ 4) (.inl (.inl (v 7))) =
        .inl (.inl (v 7)) := by
  obtain ⟨f7, f1, f10, f5⟩ := u.facePerm_split
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [squareCorner, show ((1 : Fin 4) : ℕ) = 1 from rfl, pow_one, f7]
  · rw [squareCorner, show ((2 : Fin 4) : ℕ) = 2 from rfl, pow_succ, Perm.mul_apply, pow_one,
      f7, f1]
  · rw [squareCorner, show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_succ, Perm.mul_apply, pow_succ,
      Perm.mul_apply, pow_one, f7, f1, f10]
  · rw [pow_succ, Perm.mul_apply, pow_succ, Perm.mul_apply, pow_succ, Perm.mul_apply, pow_one,
      f7, f1, f10, f5]

end UrbanDarts

end UrbanSplit

section UrbanSplit₂

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {K : PlabicData H b} {v : Fin 12 → H}

namespace UrbanDarts

/-- The vertices of the four corners of the double splitting. -/
private theorem vertexOf_split (u : UrbanDarts K v) :
    ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf (.inl (.inl (v 7))) =
        {.inl (.inl (v 7)), .inl (.inr 0), .inl (.inl (v 6))} ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf (.inl (.inl (v 1))) =
        {.inl (.inl (v 1)), .inl (.inl (v 3)), .inl (.inl (v 0))} ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf (.inl (.inl (v 10))) =
        {.inl (.inl (v 10)), .inr 0, .inl (.inl (v 9))} ∧
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf (.inl (.inl (v 5))) =
        {.inl (.inl (v 5)), .inl (.inl (v 2)), .inl (.inl (v 4))} := by
  obtain ⟨r7, rn1, r6, r1, r3, r0, r10, rn2, r9, r5, r2, r4⟩ := u.rot_split
  exact ⟨vertexOf_eq_of_rot_three' _ r7 rn1 r6, vertexOf_eq_of_rot_three' _ r1 r3 r0,
    vertexOf_eq_of_rot_three' _ r10 rn2 r9, vertexOf_eq_of_rot_three' _ r5 r2 r4⟩

/-- A dart of the double splitting lies at one of the four corners of the face exactly when it is
one of the twelve darts `c₁, n₁, c̄₄, c₂, e₂, c̄₁, c₃, n₂, c̄₂, c₄, e₄, c̄₃`. -/
private theorem mem_squareVertices_split_iff (u : UrbanDarts K v) (d : (H ⊕ Fin 2) ⊕ Fin 2) :
    ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf d ∈
        ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareVertices
          (.inl (.inl (v 7))) ↔
      d = .inl (.inl (v 7)) ∨ d = .inl (.inr 0) ∨ d = .inl (.inl (v 6)) ∨
        d = .inl (.inl (v 1)) ∨ d = .inl (.inl (v 3)) ∨ d = .inl (.inl (v 0)) ∨
        d = .inl (.inl (v 10)) ∨ d = .inr 0 ∨ d = .inl (.inl (v 9)) ∨
        d = .inl (.inl (v 5)) ∨ d = .inl (.inl (v 2)) ∨ d = .inl (.inl (v 4)) := by
  obtain ⟨c0, c1, c2, c3, -⟩ := u.squareCorner_split
  obtain ⟨V0, V1, V2, V3⟩ := u.vertexOf_split
  rw [mem_squareVertices]
  constructor
  · rintro ⟨k, hk⟩
    have hd := hk ▸ ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).self_mem_vertexOf d
    fin_cases k <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, c0, c1, c2, c3, V0, V1,
        V2, V3, mem_insert, mem_singleton] at hd <;> tauto
  · have m : ∀ (k : Fin 4) (e : (H ⊕ Fin 2) ⊕ Fin 2),
        e ∈ ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf
          (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareCorner
            (.inl (.inl (v 7))) k) →
        ∃ k', ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf
          (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareCorner
            (.inl (.inl (v 7))) k') =
          ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf e :=
      fun k e he => ⟨k, (RotationSystem.vertexOf_eq_of_mem _ he).symm⟩
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact m 0 _ (by rw [c0, V0]; simp)
    · exact m 0 _ (by rw [c0, V0]; simp)
    · exact m 0 _ (by rw [c0, V0]; simp)
    · exact m 1 _ (by rw [c1, V1]; simp)
    · exact m 1 _ (by rw [c1, V1]; simp)
    · exact m 1 _ (by rw [c1, V1]; simp)
    · exact m 2 _ (by rw [c2, V2]; simp)
    · exact m 2 _ (by rw [c2, V2]; simp)
    · exact m 2 _ (by rw [c2, V2]; simp)
    · exact m 3 _ (by rw [c3, V3]; simp)
    · exact m 3 _ (by rw [c3, V3]; simp)
    · exact m 3 _ (by rw [c3, V3]; simp)

private theorem inl_inl_notMem_bdry_split (u : UrbanDarts K v) (i : Fin 12) :
    (.inl (.inl (v i)) : (H ⊕ Fin 2) ⊕ Fin 2) ∉
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).bdry := by
  simpa using u.notMem_bdry i

/-- The face `(c₁, c₂, c₃, c₄)` of the double splitting satisfies the conditions of a square
move. -/
private theorem isSquareMoveFace_split (u : UrbanDarts K v) :
    ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).IsSquareMoveFace (.inl (.inl (v 7))) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := u.squareCorner_split
  obtain ⟨V0, V1, V2, V3⟩ := u.vertexOf_split
  obtain ⟨f7, f1, f10, f5⟩ := u.facePerm_split
  have hB := u.inl_inl_notMem_bdry_split
  have hB₀ : (.inl (.inr 0) : (H ⊕ Fin 2) ⊕ Fin 2) ∉
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).bdry := by simp
  have hB₁ : (.inr 0 : (H ⊕ Fin 2) ⊕ Fin 2) ∉
      ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).bdry := by simp
  have hface : ∀ e ∈ ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).faceOf
      (.inl (.inl (v 7))), e ∉ ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).bdry := by
    intro e he
    let A : Set ((H ⊕ Fin 2) ⊕ Fin 2) :=
      {.inl (.inl (v 7)), .inl (.inl (v 1)), .inl (.inl (v 10)), .inl (.inl (v 5))}
    have hA : ∀ a ∈ A, ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).facePerm a ∈ A := by
      intro a ha
      simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl
      · rw [f7]; simp
      · rw [f1]; simp
      · rw [f10]; simp
      · rw [f5]; simp
    have heA := mem_of_sameCycle_of_mapsTo' hA (by simp [A])
      ((RotationSystem.mem_faceOf _).1 he)
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at heA
    rcases heA with rfl | rfl | rfl | rfl <;> exact hB _
  have hint : ∀ k : Fin 4, ¬((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).IsBoundaryVertex
      (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf
        (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareCorner
          (.inl (.inl (v 7))) k)) := by
    intro k
    rintro ⟨e, he, heB⟩
    fin_cases k <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, c0, c1, c2, c3, V0, V1,
        V2, V3, mem_insert, mem_singleton] at he <;>
      rcases he with rfl | rfl | rfl <;> simp_all
  refine ⟨?_, c4, fun k => ?_, ?_, ?_, ?_⟩
  · refine (DiskMap.mem_internalFaces _).2 ⟨(DiskMap.mem_faces _).2 ⟨fun h => ?_,
      RotationSystem.faceOf_mem_faceOrbits _ _⟩, Finset.disjoint_left.2 hface⟩
    have h7 := ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).self_mem_faceOf
      (.inl (.inl (v 7)))
    rw [h] at h7
    exact hB 7 (DiskMap.exterior_subset_bdry _ h7)
  · exact (DiskMap.vertexOf_mem_internalVertices _).2 (hint k)
  · intro k k' h
    fin_cases k <;> fin_cases k' <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, c0, c1, c2, c3, V0, V1,
        V2, V3] at h <;>
      first
      | rfl
      | (have := Finset.ext_iff.1 h (.inl (.inl (v 7))); simp [u.inj.eq_iff] at this; done)
      | (have := Finset.ext_iff.1 h (.inl (.inl (v 1))); simp [u.inj.eq_iff] at this; done)
      | (have := Finset.ext_iff.1 h (.inl (.inl (v 10))); simp [u.inj.eq_iff] at this)
  · intro k
    fin_cases k <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, c0, c1, c2, c3, V0, V1,
        V2, V3] <;> simp [u.inj.eq_iff]
  · intro k
    have w1 := u.colour_white 1 (by decide)
    have w5 := u.colour_white 5 (by decide)
    have b7 := u.colour_black 7 (by decide)
    have b10 := u.colour_black 10 (by decide)
    fin_cases k <;>
      simp [Fin.isValue, c0, c1, c2, c3, show ((0 : Fin 4) + 1) = 1 from rfl,
        show ((1 : Fin 4) + 1) = 2 from rfl, show ((2 : Fin 4) + 1) = 3 from rfl,
        show ((3 : Fin 4) + 1) = 0 from rfl, w1, w5, b7, b10]

end UrbanDarts

end UrbanSplit₂

section UrbanSplit₃

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {K K' : PlabicData H b}
  {v : Fin 12 → H}

namespace UrbanDarts

/-- The square move of the double splitting of `K` at `c̄₄, c̄₂` is isomorphic, by `θ`, to the
double splitting at `ē₂, ē₄` of a tuple `K'` with the rotation of the urban renewal. -/
private theorem isomorphic_split (u : UrbanDarts K v) (hK : K.IsPlabicGraph)
    (t₀ : K'.rot (v 0) = v 3) (t₁ : K'.rot (v 1) = v 4) (t₂ : K'.rot (v 2) = v 1)
    (t₃ : K'.rot (v 3) = v 5) (t₄ : K'.rot (v 4) = v 2) (t₅ : K'.rot (v 5) = v 0)
    (t₆ : K'.rot (v 6) = K.rot (v 7)) (t₇ : K'.rot (v 7) = K.rot (v 8))
    (t₈ : K'.rot (v 8) = v 7) (t₉ : K'.rot (v 9) = K.rot (v 10))
    (t₁₀ : K'.rot (v 10) = K.rot (v 11)) (t₁₁ : K'.rot (v 11) = v 10)
    (hfix : ∀ x, (∀ i, x ≠ v i) → K'.rot x = K.rot x) (hinv : K'.inv = K.inv)
    (hbdry : K'.bdry = K.bdry) (hleg : K'.leg = K.leg)
    (hcol : ∀ x, ¬K.IsBoundaryVertex (K.vertexOf x) → K'.colour x = K.colour x)
    (hK₂ : ((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).IsPlabicGraph)
    (hK'₂ : ((K'.vertexSplit (v 11) 2).vertexSplit (.inl (v 8)) 2).IsPlabicGraph) :
    (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).squareMove
      (.inl (.inl (v 7)))).Isomorphic ((K'.vertexSplit (v 11) 2).vertexSplit (.inl (v 8)) 2) := by
  obtain ⟨u0, u1, u2, u3⟩ := urbanTheta_new u.inj
  have h6 := u.not_isBoundaryVertex 6
  have h9 : ¬(K.vertexSplit (v 6) 2).IsBoundaryVertex
      ((K.vertexSplit (v 6) 2).vertexOf (.inl (v 9))) := by
    rw [isBoundaryVertex_vertexSplit_inl_iff h6]
    exact u.not_isBoundaryVertex 9
  have hcolv : ∀ i, K'.colour (v i) = K.colour (v i) := fun i =>
    hcol _ (u.not_isBoundaryVertex i)
  have hB := u.notMem_bdry
  have hlegv : ∀ i j, K.leg i ≠ v j := by
    intro i j h
    apply u.not_isBoundaryVertex j
    rw [← h]
    exact (K.mem_boundaryVertices.1 (hK.bvertex_mem i)).2
  have w0 := u.colour_white 0 (by decide)
  have w1 := u.colour_white 1 (by decide)
  have w2 := u.colour_white 2 (by decide)
  have w3 := u.colour_white 3 (by decide)
  have w4 := u.colour_white 4 (by decide)
  have w5 := u.colour_white 5 (by decide)
  have b6 := u.colour_black 6 (by decide)
  have b7 := u.colour_black 7 (by decide)
  have b8 := u.colour_black 8 (by decide)
  have b9 := u.colour_black 9 (by decide)
  have b10 := u.colour_black 10 (by decide)
  have b11 := u.colour_black 11 (by decide)
  refine ⟨⟨urbanTheta v, fun d => ?_, fun d => ?_, fun d => ?_, fun d hd => ?_, fun i => ?_⟩⟩
  · change urbanTheta v (splitInv (splitInv K.inv) d) =
      splitInv (splitInv K'.inv) (urbanTheta v d)
    rw [hinv]
    exact urbanTheta_map_inv u.inj u.inv_involutive u.i₀ u.i₁ u.i₂ u.i₃ u.i₄ u.i₅ d
  · exact urbanTheta_map_rot u.inj u.s₁ u.s₂ u.s₃ u.s₄ u.s₅ u.s₆ u.s₇ u.s₈ t₀ t₁ t₂ t₃ t₄ t₅ t₆
      t₇ t₈ t₉ t₁₀ t₁₁ hfix d
  · simp only [bdry_squareMove, bdry_vertexSplit, hbdry]
    rcases d with (x | i) | i
    · by_cases hx : ∃ j, x = v j
      · obtain ⟨j, rfl⟩ := hx
        fin_cases j <;> simp [urbanTheta_inl_inl u.inj, u.inj.eq_iff, hB]
      · push Not at hx
        simp [urbanTheta_inl_inl u.inj, hx]
    · fin_cases i <;> simp [u0, u1, hB]
    · fin_cases i <;> simp [u2, u3, hB]
  · change ¬((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).IsBoundaryVertex
      (((K.vertexSplit (v 6) 2).vertexSplit (.inl (v 9)) 2).vertexOf d) at hd
    simp only [colour_squareMove, u.mem_squareVertices_split_iff]
    rcases d with (x | i) | i
    · by_cases hx : ∃ j, x = v j
      · obtain ⟨j, rfl⟩ := hx
        fin_cases j <;> simp [urbanTheta_inl_inl u.inj, u.inj.eq_iff, hcolv, w0, w1, w2, w3, w4,
          w5, b6, b7, b8, b9, b10, b11]
      · push Not at hx
        rw [isBoundaryVertex_vertexSplit_inl_iff h9, isBoundaryVertex_vertexSplit_inl_iff h6] at hd
        simp [urbanTheta_inl_inl u.inj, hx, hcol x hd]
    · fin_cases i <;> simp [u0, u1, hcolv, w5, b6]
    · fin_cases i <;> simp [u2, u3, hcolv, w1, b9]
  · rw [bvertex_squareMove, bdry_squareMove, hK₂.filter_bvertex_notMem_bdry,
      hK'₂.filter_bvertex_notMem_bdry, map_singleton]
    simp [hleg, urbanTheta_inl_inl u.inj, hlegv]

end UrbanDarts

end UrbanSplit₃

section UrbanCirc

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {K K' : PlabicData H b}
  {v : Fin 12 → H}

/-- A plabic graph `K` with twelve darts as at an urban renewal face, and a plabic graph `K'` with
the rotation of its urban renewal (and otherwise the data of `K`), satisfy `K ∘∼ K'`: split `K` at
`c̄₄` and `c̄₂`, make the square move at `(c₁, c₂, c₃, c₄)`, and contract the double splitting of
`K'` at `ē₂` and `ē₄`. -/
private theorem UrbanDarts.circMoveEquivalent (u : UrbanDarts K v) (hK : K.IsPlabicGraph)
    (hK' : K'.IsPlabicGraph)
    (t₀ : K'.rot (v 0) = v 3) (t₁ : K'.rot (v 1) = v 4) (t₂ : K'.rot (v 2) = v 1)
    (t₃ : K'.rot (v 3) = v 5) (t₄ : K'.rot (v 4) = v 2) (t₅ : K'.rot (v 5) = v 0)
    (t₆ : K'.rot (v 6) = K.rot (v 7)) (t₇ : K'.rot (v 7) = K.rot (v 8))
    (t₈ : K'.rot (v 8) = v 7) (t₉ : K'.rot (v 9) = K.rot (v 10))
    (t₁₀ : K'.rot (v 10) = K.rot (v 11)) (t₁₁ : K'.rot (v 11) = v 10)
    (hfix : ∀ x, (∀ i, x ≠ v i) → K'.rot x = K.rot x) (hinv : K'.inv = K.inv)
    (hbdry : K'.bdry = K.bdry) (hleg : K'.leg = K.leg)
    (hcol : ∀ x, ¬K.IsBoundaryVertex (K.vertexOf x) → K'.colour x = K.colour x)
    (hint : ∀ x, ¬K.IsBoundaryVertex (K.vertexOf x) → ¬K'.IsBoundaryVertex (K'.vertexOf x)) :
    PlabicGraph.CircMoveEquivalent ⟨H, K, hK⟩ ⟨H, K', hK'⟩ := by
  have hne : ∀ {i j : Fin 12}, i ≠ j → v i ≠ v j := u.inj.ne
  have h6 := u.not_isBoundaryVertex 6
  have h9 : ¬(K.vertexSplit (v 6) 2).IsBoundaryVertex
      ((K.vertexSplit (v 6) 2).vertexOf (.inl (v 9))) := by
    rw [isBoundaryVertex_vertexSplit_inl_iff h6]
    exact u.not_isBoundaryVertex 9
  have h11 : ¬K'.IsBoundaryVertex (K'.vertexOf (v 11)) := hint _ (u.not_isBoundaryVertex 11)
  have h8 : ¬(K'.vertexSplit (v 11) 2).IsBoundaryVertex
      ((K'.vertexSplit (v 11) 2).vertexOf (.inl (v 8))) := by
    rw [isBoundaryVertex_vertexSplit_inl_iff h11]
    exact hint _ (u.not_isBoundaryVertex 8)
  have hK₁ := hK.vertexSplit h6 2
  have hK₂ := hK₁.vertexSplit h9 2
  have hK'₁ := hK'.vertexSplit h11 2
  have hK'₂ := hK'₁.vertexSplit h8 2
  have d1 : v 9 ≠ K.rot (v 6) := by rw [u.s₁]; exact hne (by decide)
  have d2 : K.rot (v 9) ≠ v 6 := by rw [u.s₅]; exact hne (by decide)
  have e1 : v 8 ≠ K'.rot (v 11) := by rw [t₁₁]; exact hne (by decide)
  have e2 : K'.rot (v 8) ≠ v 11 := by rw [t₈]; exact hne (by decide)
  have st1 := circStep_vertexSplit hK h6 (by rw [u.s₁]; exact hne (by decide))
    (u.colour_black 6 (by decide))
  have st2 := circStep_vertexSplit hK₁ h9
    (by rw [rot_vertexSplit_two_inl_s₂ d1 d2, u.s₅]; exact fun h => hne (by decide) (Sum.inl.inj h))
    (by simpa using u.colour_black 9 (by decide))
  have st4 := circStep_vertexSplit hK'₁ h8
    (by rw [rot_vertexSplit_two_inl_s₂ e1 e2, t₈]; exact fun h => hne (by decide) (Sum.inl.inj h))
    (by simpa [hcol _ (u.not_isBoundaryVertex 8)] using u.colour_black 8 (by decide))
  have st5 := circStep_vertexSplit hK' h11 (by rw [t₁₁]; exact hne (by decide))
    (by rw [hcol _ (u.not_isBoundaryVertex 11)]; exact u.colour_black 11 (by decide))
  have st3 : PlabicGraph.CircStep ⟨_, _, hK₂⟩ ⟨_, _, hK'₂⟩ :=
    Or.inr (Or.inl ⟨_, u.isSquareMoveFace_split, (u.isomorphic_split hK t₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇
      t₈ t₉ t₁₀ t₁₁ hfix hinv hbdry hleg hcol hK₂ hK'₂).symm⟩)
  exact .head st1.symm (.head st2.symm (.head st3 (.head st4 (.single st5))))

end UrbanCirc

/-! ### Urban renewal by local moves -/

section UrbanRenewalCirc

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- If `G'` is the urban renewal `urbanRenewal` of the normal plabic graph `G` at the face
`(c₁, c₂, c₃, c₄)`, then `G ∘∼ G'`. -/
@[cluster_algebras "lem_urban_renewal_circ"]
theorem IsUrbanRenewalFace.circMoveEquivalent (hG : G.IsNormalPlabicGraph) {c : H}
    (hc : G.IsUrbanRenewalFace c) :
    PlabicGraph.CircMoveEquivalent ⟨H, G, hG.toIsPlabicGraph⟩
      ⟨H, G.urbanRenewal c, (hc.isNormalPlabicGraph_urbanRenewal hG).toIsPlabicGraph⟩ := by
  have hnd := hc.nodup hG
  let v : Fin 12 → H := fun i => [G.inv c, G.squareCorner c 1, G.rot (G.squareCorner c 3),
      G.rot (G.squareCorner c 1), G.inv (G.squareCorner c 2), G.squareCorner c 3,
      G.inv (G.squareCorner c 3), c, G.inv (G.rot (G.squareCorner c 3)),
      G.inv (G.squareCorner c 1), G.squareCorner c 2,
      G.inv (G.rot (G.squareCorner c 1))].get (i.cast rfl)
  have hv : Injective v := (List.nodup_iff_injective_get.1 hnd).comp (Fin.cast_injective _)
  have sq1 : G.squareCorner c 1 = G.rot (G.inv c) := by
    simp [squareCorner, G.facePerm_apply]
  have sq2 : G.squareCorner c 2 = G.rot (G.inv (G.squareCorner c 1)) := by
    change (G.facePerm ^ 2) c = G.rot (G.inv ((G.facePerm ^ 1) c))
    rw [pow_succ', Perm.mul_apply, G.facePerm_apply]
  have sq3 : G.squareCorner c 3 = G.rot (G.inv (G.squareCorner c 2)) := by
    change (G.facePerm ^ 3) c = G.rot (G.inv ((G.facePerm ^ 2) c))
    rw [pow_succ', Perm.mul_apply, G.facePerm_apply]
  have sq4 : G.rot (G.inv (G.squareCorner c 3)) = c := by
    have h4 := hc.facePerm_pow_four
    rwa [pow_succ', Perm.mul_apply, G.facePerm_apply] at h4
  have int := hc.not_isBoundaryVertex
  have b7 : G.colour c = .black := hc.colour_squareCorner_zero
  have w1 := hc.colour_squareCorner_one
  have b10 := hc.colour_squareCorner_two
  have w5 := hc.colour_squareCorner_three
  have n0 : ¬G.IsBoundaryVertex (G.vertexOf (G.inv c)) := by
    rw [← G.vertexOf_rot, ← sq1]; exact int 1
  have n2 : ¬G.IsBoundaryVertex (G.vertexOf (G.rot (G.squareCorner c 3))) := by
    rw [G.vertexOf_rot]; exact int 3
  have n3 : ¬G.IsBoundaryVertex (G.vertexOf (G.rot (G.squareCorner c 1))) := by
    rw [G.vertexOf_rot]; exact int 1
  have n4 : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.squareCorner c 2))) := by
    rw [← G.vertexOf_rot, ← sq3]; exact int 3
  have n6 : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.squareCorner c 3))) := by
    rw [← G.vertexOf_rot, sq4]; exact int 0
  have n9 : ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.squareCorner c 1))) := by
    rw [← G.vertexOf_rot, ← sq2]; exact int 2
  have w0 : G.colour (G.inv c) = .white := by
    rwa [← hG.colour_rot _ n0, ← sq1]
  have w2 : G.colour (G.rot (G.squareCorner c 3)) = .white := by
    rwa [hG.colour_rot _ (int 3)]
  have w3 : G.colour (G.rot (G.squareCorner c 1)) = .white := by
    rwa [hG.colour_rot _ (int 1)]
  have w4 : G.colour (G.inv (G.squareCorner c 2)) = .white := by
    rwa [← hG.colour_rot _ n4, ← sq3]
  have b6 : G.colour (G.inv (G.squareCorner c 3)) = .black := by
    rwa [← hG.colour_rot _ n6, sq4]
  have b9 : G.colour (G.inv (G.squareCorner c 1)) = .black := by
    rwa [← hG.colour_rot _ n9, ← sq2]
  obtain ⟨n8, b8⟩ := hG.inv_internal_black_of_white n2 w2
  obtain ⟨n11, b11⟩ := hG.inv_internal_black_of_white n3 w3
  have s₄ : G.rot (G.rot (G.squareCorner c 1)) = G.inv c := by
    have h3 : (G.vertexOf (G.inv c)).card = 3 := by
      rw [← G.vertexOf_rot, ← sq1]; exact hG.card_vertexOf_of_white _ (int 1) w1
    rw [sq1]
    exact rot_rot_rot_of_card_vertexOf_eq_three h3
  have s₈ : G.rot (G.rot (G.squareCorner c 3)) = G.inv (G.squareCorner c 2) := by
    have h3 : (G.vertexOf (G.inv (G.squareCorner c 2))).card = 3 := by
      rw [← G.vertexOf_rot, ← sq3]; exact hG.card_vertexOf_of_white _ (int 3) w5
    rw [sq3]
    exact rot_rot_rot_of_card_vertexOf_eq_three h3
  have u : UrbanDarts G v :=
    { inj := hv
      inv_involutive := hG.inv_involutive
      not_isBoundaryVertex := by
        intro i
        fin_cases i
        exacts [n0, int 1, n2, n3, n4, int 3, n6, int 0, n8, n9, int 2, n11]
      colour_white := by
        intro i hi
        fin_cases i
        all_goals first
          | exact absurd hi (by decide)
          | exact w0 | exact w1 | exact w2 | exact w3 | exact w4 | exact w5
      colour_black := by
        intro i hi
        fin_cases i
        all_goals first
          | exact absurd hi (by decide)
          | exact b6 | exact b7 | exact b8 | exact b9 | exact b10 | exact b11
      s₁ := sq4
      s₂ := sq1.symm
      s₃ := rfl
      s₄ := s₄
      s₅ := sq2.symm
      s₆ := sq3.symm
      s₇ := rfl
      s₈ := s₈
      i₀ := hG.inv_involutive c
      i₁ := rfl
      i₂ := rfl
      i₃ := rfl
      i₄ := hG.inv_involutive _
      i₅ := rfl }
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := hc.urbanRenewalPerm_apply hG
  have hπ : ∀ x, (G.urbanRenewal c).rot x = G.rot (G.urbanRenewalPerm c x) := fun _ => rfl
  refine u.circMoveEquivalent hG.toIsPlabicGraph
    (hc.isNormalPlabicGraph_urbanRenewal hG).toIsPlabicGraph ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun x hx => ?_) rfl rfl rfl (fun x hx => (hc.colour_urbanRenewal hG x).2 hx)
    (fun x hx h => hx ((hc.colour_urbanRenewal hG x).1.1 h))
  · change (G.urbanRenewal c).rot (G.inv c) = G.rot (G.squareCorner c 1)
    rw [hπ, p0]
  · change (G.urbanRenewal c).rot (G.squareCorner c 1) = G.inv (G.squareCorner c 2)
    rw [hπ, p1, s₈]
  · change (G.urbanRenewal c).rot (G.rot (G.squareCorner c 3)) = G.squareCorner c 1
    rw [hπ, p2, sq1]
  · change (G.urbanRenewal c).rot (G.rot (G.squareCorner c 1)) = G.squareCorner c 3
    rw [hπ, p3, sq3]
  · change (G.urbanRenewal c).rot (G.inv (G.squareCorner c 2)) = G.rot (G.squareCorner c 3)
    rw [hπ, p4]
  · change (G.urbanRenewal c).rot (G.squareCorner c 3) = G.inv c
    rw [hπ, p5, s₄]
  · change (G.urbanRenewal c).rot (G.inv (G.squareCorner c 3)) = G.rot c
    rw [hπ, p6]
  · change (G.urbanRenewal c).rot c = G.rot (G.inv (G.rot (G.squareCorner c 3)))
    rw [hπ, p7]
  · change (G.urbanRenewal c).rot (G.inv (G.rot (G.squareCorner c 3))) = c
    rw [hπ, p8, sq4]
  · change (G.urbanRenewal c).rot (G.inv (G.squareCorner c 1)) = G.rot (G.squareCorner c 2)
    rw [hπ, p9]
  · change (G.urbanRenewal c).rot (G.squareCorner c 2) =
      G.rot (G.inv (G.rot (G.squareCorner c 1)))
    rw [hπ, p10]
  · change (G.urbanRenewal c).rot (G.inv (G.rot (G.squareCorner c 1))) = G.squareCorner c 2
    rw [hπ, p11, sq2]
  · rw [hπ, urbanRenewalPerm_apply_of_notMem]
    intro hmem
    obtain ⟨n, hn⟩ := List.get_of_mem hmem
    exact hx (n.cast rfl) hn.symm

end UrbanRenewalCirc

end PlabicData

/-! ### Normal moves by local moves -/

namespace PlabicGraph

variable {b : ℕ}

/-- If `G` and `G'` are normal-move-equivalent normal plabic graphs, then `G ∘∼ G'`. In
particular `G ∼ G'` (`CircMoveEquivalent.moveEquivalent`). -/
@[cluster_algebras "lem_normal_moves_local"]
theorem NormalMoveEquivalent.circMoveEquivalent {G G' : PlabicGraph b}
    (h : NormalMoveEquivalent G G') : CircMoveEquivalent G G' := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    refine ih.trans ?_
    obtain ⟨h₁, h₂, hs⟩ := hs
    rcases hs with hs | (⟨c, hc, hiso⟩ | ⟨k, hk, hiso⟩) | (⟨c, hc, hiso⟩ | ⟨k, hk, hiso⟩)
    · exact Relation.ReflTransGen.single (Or.inl hs)
    · exact (hc.circMoveEquivalent h₁).tail (Or.inl hiso)
    · exact (hk.circMoveEquivalent h₁).tail (Or.inl hiso)
    · exact CircMoveEquivalent.symm ((hc.circMoveEquivalent h₂).tail (Or.inl hiso))
    · exact CircMoveEquivalent.symm ((hk.circMoveEquivalent h₂).tail (Or.inl hiso))

end PlabicGraph

namespace PlabicData

end PlabicData

end ClusterAlgebras
