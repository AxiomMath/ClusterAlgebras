/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.TrivalentMoves

/-!
# Square moves and flips of trivalent plabic graphs

For a nonempty set `T ⊆ {M1, M4}` of moves, two trivalent plabic graphs are *`T`-connected* if
they are joined by a finite sequence of trivalent plabic graphs in which each graph is isomorphic
to the previous one, or (if `M1 ∈ T`) isomorphic to a square move of it, or (if `M4 ∈ T`) related
to it by a flip in either direction.

A flip is the composite of two moves (M3): the contraction of the flipped edge, followed by the
splitting of the merged vertex along the other diagonal. Hence `{M1, M4}`-connected trivalent
graphs are move-equivalent.

## Main definitions

* `ClusterAlgebras.PlabicGraph.TrivalentMoveType`: the two moves (M1) and (M4) between trivalent
  graphs.
* `ClusterAlgebras.PlabicGraph.IsFlip`, `ClusterAlgebras.PlabicGraph.TrivalentStep`,
  `ClusterAlgebras.PlabicGraph.TrivalentConnected`: `T`-connectedness of trivalent plabic graphs.

## Main results

* `ClusterAlgebras.PlabicGraph.moveEquivalent_flipMove`: a flip is two moves (M3).
* `ClusterAlgebras.PlabicGraph.TrivalentConnected.moveEquivalent`: square moves and flips are
  move equivalences.

## Implementation notes

* A set `T` of moves is a `Set TrivalentMoveType`; FWZ ask `T` to be nonempty, which no
  statement here needs. A finite sequence of graphs is `Relation.ReflTransGen` of the step
  relation, each step asking the new graph to be trivalent; the first graph is trivalent by the
  first conjunct of `TrivalentConnected`.
* The flip step asks the flip of `G_{t-1}` at an edge satisfying the conditions of the flip move to
  be isomorphic to `G_t`. That this flip is a plabic graph is
  `PlabicData.IsPlabicGraph.flipMove`, so it is not repeated in the definition.
* The bundled constructions `PlabicGraph.squareMove`, `PlabicGraph.flipMove`,
  `PlabicGraph.contractEdge` and `PlabicGraph.vertexSplit` package the constructions on tuples
  together with the proofs that they give plabic graphs.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

namespace PlabicGraph

variable {b : ℕ}

/-! ### Bundled constructions -/

/-- The square move of `G` at the face through `c`, as a bundled plabic graph. -/
def squareMove (G : PlabicGraph b) (c : G.Dart) : PlabicGraph b where
  Dart := G.Dart
  data := G.data.squareMove c
  isPlabicGraph := G.isPlabicGraph.squareMove c

/-- The flip of `G` at an edge `{d, d̄}` satisfying the conditions of the flip move, as a bundled
plabic graph. -/
def flipMove (G : PlabicGraph b) {d : G.Dart} (hf : G.data.IsFlipEdge d) : PlabicGraph b where
  Dart := G.Dart
  data := G.data.flipMove d
  isPlabicGraph := G.isPlabicGraph.flipMove hf

/-- The contraction of `G` along an edge `{d, d̄}` whose endpoints are distinct internal vertices
of the same colour, as a bundled plabic graph. -/
noncomputable def contractEdge (G : PlabicGraph b) {d : G.Dart}
    (he : G.data.IsContractibleEdge d) : PlabicGraph b where
  Dart := (({d, G.data.inv d} : Set G.Dart)ᶜ : Set G.Dart)
  data := G.data.contractEdge d (he.leg_mem G.isPlabicGraph)
  isPlabicGraph := G.isPlabicGraph.contractEdge he

/-- The splitting of `G` at an internal vertex `v(s)` from `s` of size `p`, as a bundled plabic
graph. -/
def vertexSplit (G : PlabicGraph b) {s : G.Dart}
    (hz : ¬G.data.IsBoundaryVertex (G.data.vertexOf s)) (p : ℕ) : PlabicGraph b where
  Dart := G.Dart ⊕ Fin 2
  data := G.data.vertexSplit s p
  isPlabicGraph := G.isPlabicGraph.vertexSplit hz p

/-! ### Square-move and flip connectedness -/

/-- The two moves between trivalent plabic graphs: (M1) the square move and (M4) the flip. -/
@[cluster_algebras "def_trivalent_connected"]
inductive TrivalentMoveType
  /-- (M1): the square move. -/
  | m1
  /-- (M4): the flip. -/
  | m4
  deriving DecidableEq

/-- `G'` is isomorphic to a **flip** of `G`: to the flip of `G` at an edge satisfying the
conditions of the flip move (`PlabicData.IsFlipEdge`). -/
@[cluster_algebras "def_trivalent_connected"]
def IsFlip (G G' : PlabicGraph b) : Prop :=
  ∃ d, G.data.IsFlipEdge d ∧ G'.data.Isomorphic (G.data.flipMove d)

/-- A **step** of a `T`-connection: `G'` is trivalent, and `G'` is isomorphic to `G`, or (if
`M1 ∈ T`) isomorphic to a square move of `G`, or (if `M4 ∈ T`) `G'` is isomorphic to a flip of `G`
or `G` is isomorphic to a flip of `G'`. -/
@[cluster_algebras "def_trivalent_connected"]
def TrivalentStep (T : Set TrivalentMoveType) (G G' : PlabicGraph b) : Prop :=
  G'.IsTrivalent ∧ (G'.Isomorphic G ∨ (TrivalentMoveType.m1 ∈ T ∧ G.IsSquareMove G') ∨
    (TrivalentMoveType.m4 ∈ T ∧ (G.IsFlip G' ∨ G'.IsFlip G)))

/-- **Square-move and flip connectedness**: two trivalent plabic graphs `G` and `G'` are
`T`-connected if there is a finite sequence `G = G₀, G₁, …, G_r = G'` of trivalent plabic graphs in
which each `G_t` is isomorphic to `G_{t-1}`, or (if `M1 ∈ T`) isomorphic to the square move of
`G_{t-1}` at some face, or (if `M4 ∈ T`) isomorphic to the flip of `G_{t-1}` at an edge satisfying
the conditions of the flip move, or such that `G_{t-1}` is isomorphic to the flip of `G_t` at such
an edge. -/
@[cluster_algebras "def_trivalent_connected"]
def TrivalentConnected (T : Set TrivalentMoveType) (G G' : PlabicGraph b) : Prop :=
  G.IsTrivalent ∧ Relation.ReflTransGen (TrivalentStep T) G G'

/-- A step of a `T`-connection from a trivalent graph can be reversed. -/
theorem TrivalentStep.symm {T : Set TrivalentMoveType} {G G' : PlabicGraph b}
    (hG : G.IsTrivalent) (h : TrivalentStep T G G') : TrivalentStep T G' G := by
  obtain ⟨-, h | ⟨h1, h⟩ | ⟨h4, h⟩⟩ := h
  · exact ⟨hG, Or.inl h.symm⟩
  · exact ⟨hG, Or.inr (Or.inl ⟨h1, h.symm⟩)⟩
  · exact ⟨hG, Or.inr (Or.inr ⟨h4, h.symm⟩)⟩

namespace TrivalentConnected

variable {T T' : Set TrivalentMoveType} {G G' G'' : PlabicGraph b}

/-- A trivalent graph is `T`-connected to itself. -/
theorem refl (hG : G.IsTrivalent) : TrivalentConnected T G G := ⟨hG, .refl⟩

/-- `T`-connectedness is transitive. -/
theorem trans (h : TrivalentConnected T G G') (h' : TrivalentConnected T G' G'') :
    TrivalentConnected T G G'' :=
  ⟨h.1, h.2.trans h'.2⟩

/-- The source of a `T`-connection is trivalent. -/
theorem isTrivalent_left (h : TrivalentConnected T G G') : G.IsTrivalent := h.1

/-- The target of a `T`-connection is trivalent. -/
theorem isTrivalent_right (h : TrivalentConnected T G G') : G'.IsTrivalent := by
  obtain ⟨h0, h⟩ := h
  induction h with
  | refl => exact h0
  | tail _ hst _ => exact hst.1

/-- A single step of a `T`-connection from a trivalent graph gives a `T`-connection. -/
theorem of_trivalentStep (hG : G.IsTrivalent) (h : TrivalentStep T G G') :
    TrivalentConnected T G G' :=
  ⟨hG, .single h⟩

/-- `T`-connectedness is symmetric. -/
theorem symm (h : TrivalentConnected T G G') : TrivalentConnected T G' G := by
  refine ⟨h.isTrivalent_right, ?_⟩
  obtain ⟨h0, h⟩ := h
  induction h with
  | refl => exact .refl
  | @tail B C hBC hst ih =>
    have hB : B.IsTrivalent := isTrivalent_right ⟨h0, hBC⟩
    exact Relation.ReflTransGen.head (hst.symm hB) ih

/-- Isomorphic trivalent graphs are `T`-connected. -/
theorem of_isomorphic (hG : G.IsTrivalent) (hG' : G'.IsTrivalent) (h : G'.Isomorphic G) :
    TrivalentConnected T G G' :=
  of_trivalentStep hG ⟨hG', Or.inl h⟩

/-- A trivalent graph and a trivalent square move of it are `T`-connected when `M1 ∈ T`. -/
theorem of_isSquareMove (hT : TrivalentMoveType.m1 ∈ T) (hG : G.IsTrivalent)
    (hG' : G'.IsTrivalent) (h : G.IsSquareMove G') : TrivalentConnected T G G' :=
  of_trivalentStep hG ⟨hG', Or.inr (Or.inl ⟨hT, h⟩)⟩

/-- A trivalent graph and a trivalent flip of it are `T`-connected when `M4 ∈ T`. -/
theorem of_isFlip (hT : TrivalentMoveType.m4 ∈ T) (hG : G.IsTrivalent) (hG' : G'.IsTrivalent)
    (h : G.IsFlip G') : TrivalentConnected T G G' :=
  of_trivalentStep hG ⟨hG', Or.inr (Or.inr ⟨hT, Or.inl h⟩)⟩

/-- `T`-connectedness implies `T'`-connectedness when `T ⊆ T'`. -/
theorem mono (hTT' : T ⊆ T') (h : TrivalentConnected T G G') : TrivalentConnected T' G G' :=
  ⟨h.1, Relation.ReflTransGen.mono (fun _ _ hs => ⟨hs.1, hs.2.imp_right fun h => h.imp
    (fun ⟨h1, h⟩ => ⟨hTT' h1, h⟩) fun ⟨h4, h⟩ => ⟨hTT' h4, h⟩⟩) h.2⟩

end TrivalentConnected

/-! ### A flip is two moves (M3) -/

/-- In a plabic graph, the merged vertex of the contraction along an edge satisfying the conditions
of the flip move, through `a₂ = σ²(d)`, has at least two darts. -/
private theorem two_le_card_vertexOf_contractEdge (G : PlabicGraph b) {d : G.Dart}
    (hf : G.data.IsFlipEdge d) :
    2 ≤ ((G.contractEdge hf.isContractibleEdge).data.vertexOf
      ⟨G.data.rot (G.data.rot d), hf.rot_rot_mem⟩).card := by
  have he := hf.isContractibleEdge
  have ha := PlabicData.mem_compl_pair_iff.1 hf.rot_rot_mem
  have hx : G.data.rot (G.data.rot d) ∈ G.data.vertexOf d ∪ G.data.vertexOf (G.data.inv d) := by
    refine mem_union_left _ ?_
    rw [← G.data.vertexOf_rot d]
    exact G.data.rot_mem_vertexOf _
  have hmap := PlabicData.map_vertexOf_contractEdge_of_mem (hleg := he.leg_mem G.isPlabicGraph)
    he.not_sameCycle (x := ⟨_, hf.rot_rot_mem⟩) hx
  change 2 ≤ ((G.data.contractEdge d (he.leg_mem G.isPlabicGraph)).vertexOf _).card
  rw [← card_map, hmap]
  have h1 : G.data.rot d ≠ d := fun h => ha.1 (by rw [h, h])
  have h1' : G.data.rot d ≠ G.data.inv d := fun h => by
    apply hf.vertexOf_ne
    rw [← h, G.data.vertexOf_rot]
  have h12 : G.data.rot d ≠ G.data.rot (G.data.rot d) := fun h =>
    h1 (G.data.rot.injective h).symm
  have hsub : ({G.data.rot d, G.data.rot (G.data.rot d)} : Finset G.Dart) ⊆
      G.data.mergedVertex d := by
    intro y hy
    rw [PlabicData.mem_mergedVertex]
    rcases mem_insert.1 hy with rfl | hy
    · exact ⟨Or.inl (G.data.rot_mem_vertexOf d), h1, h1'⟩
    · rw [mem_singleton.1 hy]
      exact ⟨mem_union.1 hx, ha.1, ha.2⟩
  have := card_le_card hsub
  rwa [card_pair h12] at this

/-- **A flip is two moves (M3)**: if `{d, d̄}` is an edge of the plabic graph `G` satisfying the
conditions of the flip move, then `G` and its flip at `{d, d̄}` are `{M3}`-equivalent: the
contraction `K` along `{d, d̄}` is a move (M3) from `G`, and the flip is isomorphic to a splitting
of `K` whose new edge contracts back to `K`. -/
@[cluster_algebras "lem_flip_two_contractions"]
theorem moveEquivalent_flipMove (G : PlabicGraph b) {d : G.Dart} (hf : G.data.IsFlipEdge d) :
    MoveEquivalent {LocalMoveType.m3} G (G.flipMove hf) := by
  have hG := G.isPlabicGraph
  have he := hf.isContractibleEdge
  have ha := hf.rot_rot_mem
  have hz : ¬(G.contractEdge he).data.IsBoundaryVertex
      ((G.contractEdge he).data.vertexOf ⟨G.data.rot (G.data.rot d), ha⟩) := by
    change ¬(G.data.contractEdge d (he.leg_mem hG)).IsBoundaryVertex
      ((G.data.contractEdge d (he.leg_mem hG)).vertexOf ⟨G.data.rot (G.data.rot d), ha⟩)
    rw [PlabicData.isBoundaryVertex_vertexOf_contractEdge_iff he]
    have : G.data.vertexOf (G.data.rot (G.data.rot d)) = G.data.vertexOf d := by
      rw [G.data.vertexOf_rot, G.data.vertexOf_rot]
    rw [this]
    exact hf.not_isBoundaryVertex
  have hp := two_le_card_vertexOf_contractEdge G hf
  have s1 : MoveStep {LocalMoveType.m3} G (G.contractEdge he) :=
    Or.inr ⟨.m3, Set.mem_singleton _, Or.inl ⟨d, he, PlabicData.Isomorphic.refl _⟩⟩
  have s2 :
      MoveStep {LocalMoveType.m3} (G.contractEdge he) ((G.contractEdge he).vertexSplit hz 2) :=
    Or.inr ⟨.m3, Set.mem_singleton _, Or.inr ⟨Sum.inr 0,
      PlabicData.isContractibleEdge_vertexSplit _ _ _ hz hp,
      PlabicData.isomorphic_contractEdge_vertexSplit _ _ _
        (G.contractEdge he).isPlabicGraph.inv_involutive⟩⟩
  have s3 : MoveStep {LocalMoveType.m3} ((G.contractEdge he).vertexSplit hz 2) (G.flipMove hf) :=
    Or.inl (PlabicData.isomorphic_flipMove_vertexSplit hG hf ha)
  exact ((Relation.ReflTransGen.single s1).tail s2).tail s3

/-! ### Square moves and flips are move equivalences -/

/-- **Square moves and flips are move equivalences**: trivalent plabic graphs that are
`T`-connected for some `T ⊆ {M1, M4}`, in particular `{M1, M4}`-connected, are move-equivalent. -/
@[cluster_algebras "lem_trivalent_connected_move_equivalent"]
theorem TrivalentConnected.moveEquivalent {T : Set TrivalentMoveType} {G G' : PlabicGraph b}
    (h : TrivalentConnected T G G') : MoveEquivalent Set.univ G G' := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact MoveEquivalent.refl _ _
  | @tail B C _ hst ih =>
    refine ih.trans ?_
    obtain ⟨-, h | ⟨-, h⟩ | ⟨-, ⟨d, hf, h⟩ | ⟨d, hf, h⟩⟩⟩ := hst
    · exact MoveEquivalent.of_isomorphic h
    · exact MoveEquivalent.of_isLocalMove (t := .m1) trivial h
    · exact ((moveEquivalent_flipMove B hf).mono (Set.subset_univ _)).trans
        (MoveEquivalent.of_isomorphic h)
    · exact (MoveEquivalent.of_isomorphic (G' := C.flipMove hf) h.symm).trans
        ((moveEquivalent_flipMove C hf).mono (Set.subset_univ _)).symm

end PlabicGraph

end ClusterAlgebras
