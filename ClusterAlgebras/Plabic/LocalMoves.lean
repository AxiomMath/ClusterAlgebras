/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BivalentRemoval
public import ClusterAlgebras.Plabic.EdgeContraction
public import ClusterAlgebras.Plabic.PlabicQuiver
public import ClusterAlgebras.Plabic.SquareMove

/-!
# Local moves and move equivalence of plabic graphs

A plabic graph `G'` is obtained from a plabic graph `G` by a *local move* of type

* (M1) if `G'` is isomorphic to a square move of `G`;
* (M2) if `G'` is isomorphic to the removal of a bivalent vertex of `G`, or `G` is isomorphic to
  the removal of a bivalent vertex of `G'` (the insertion of a bivalent vertex);
* (M3) if `G'` is isomorphic to the contraction of `G` along an edge, or `G` is isomorphic to the
  contraction of `G'` along an edge (the splitting of a vertex).

For a set `S` of types, two plabic graphs are *`S`-equivalent* if they are joined by a finite
sequence of plabic graphs in which each graph is isomorphic to the previous one or is obtained from
it by a local move of a type in `S`; they are *move-equivalent*, `G ∼ G'`, if they are
`{M1, M2, M3}`-equivalent. The relation `G ∘∼ G'` uses the same steps, except that it excludes the
contraction or splitting of an edge joining a white internal leaf to a white vertex with at least
three darts.

Each of the three constructions keeps the number of faces and of internal faces, and an
isomorphism matches the faces; so move-equivalent plabic graphs have the same numbers of boundary
vertices, faces and internal faces. Each step of either relation can be reversed: an isomorphism
has an inverse, the alternatives (M2) and (M3) list both directions, and a square move of `G` at
`q` is undone by the square move at `q` (transported by the isomorphism), since the square move
changes only colours and exchanges them back when repeated. Hence both relations are symmetric.

## Main definitions

* `ClusterAlgebras.PlabicGraph.LocalMoveType`: the three types (M1), (M2), (M3) of local moves.
* `ClusterAlgebras.PlabicGraph.IsSquareMove`, `ClusterAlgebras.PlabicGraph.IsBivalentRemoval`,
  `ClusterAlgebras.PlabicGraph.IsEdgeContraction`, `ClusterAlgebras.PlabicGraph.IsLocalMove`:
  local moves.
* `ClusterAlgebras.PlabicGraph.MoveStep`, `ClusterAlgebras.PlabicGraph.MoveEquivalent`:
  `S`-equivalence and move equivalence.
* `ClusterAlgebras.PlabicData.IsWhiteLeafEdge`, `ClusterAlgebras.PlabicGraph.CircStep`,
  `ClusterAlgebras.PlabicGraph.CircMoveEquivalent`: the relation `∘∼`.

## Main results

* `ClusterAlgebras.PlabicGraph.MoveEquivalent.card_eq`: move-equivalent plabic graphs have the
  same numbers of boundary vertices, faces and internal faces.
* `ClusterAlgebras.PlabicGraph.MoveEquivalent.symm`: `S`-equivalence is symmetric.
* `ClusterAlgebras.PlabicGraph.CircMoveEquivalent.symm`: the relation `∘∼` is symmetric.

## Implementation notes

* Plabic graphs on different sets of darts are compared as elements of the type
  `ClusterAlgebras.PlabicGraph b` of plabic graphs with `b` boundary vertices bundled with their
  darts; isomorphic plabic graphs have the same number `b` of boundary vertices. A set `S` of
  types is a `Set LocalMoveType`; FWZ ask `S` to be nonempty, which no statement here
  needs, and `G ∼ G'` is `MoveEquivalent Set.univ G G'`.
* A finite sequence `G = G₀, …, G_r = G'` whose steps satisfy a relation is the
  reflexive-transitive closure `Relation.ReflTransGen` of that relation.
* The edge `{d, d̄}` of a contraction is given by the dart `d`; the conditions of the contraction
  are `ClusterAlgebras.PlabicData.IsContractibleEdge`, and the legs then avoid `d` and `d̄`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

/-- A plabic graph with labels `Fin b` has exactly `b` boundary vertices. -/
theorem IsPlabicGraph.card_boundaryVertices {G : PlabicData H b} (hG : G.IsPlabicGraph) :
    G.boundaryVertices.card = b := by
  have h : G.boundaryVertices = univ.image G.bvertex := by
    ext v
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun hv => hG.exists_bvertex_eq v hv, fun ⟨i, hi⟩ => hi ▸ hG.bvertex_mem i⟩
  rw [h, card_image_of_injective _ hG.bvertex_injective, card_univ, Fintype.card_fin]

/-- The faces split into the internal faces and the boundary faces. -/
theorem card_internalFaces_add_card_boundaryFaces (G : PlabicData H b) :
    G.internalFaces.card + G.boundaryFaces.card = G.faces.card :=
  card_filter_add_card_filter_not _

namespace Iso

variable {G : PlabicData H b} {G' : PlabicData H' b} (θ : G.Iso G')

/-- Isomorphic tuples have the same number of faces. -/
theorem card_faces (θ : G.Iso G') : G.faces.card = G'.faces.card :=
  card_nbij _ (fun _ hf => θ.bijOn_faces.1.mapsTo hf) θ.bijOn_faces.1.injOn
    θ.bijOn_faces.1.surjOn

/-- Isomorphic tuples have the same number of boundary faces. -/
theorem card_boundaryFaces (θ : G.Iso G') : G.boundaryFaces.card = G'.boundaryFaces.card :=
  card_nbij _ (fun _ hf => θ.bijOn_faces.2.mapsTo hf) θ.bijOn_faces.2.injOn
    θ.bijOn_faces.2.surjOn

/-- Isomorphic tuples have the same number of internal faces. -/
theorem card_internalFaces (θ : G.Iso G') : G.internalFaces.card = G'.internalFaces.card := by
  have h₁ := G.card_internalFaces_add_card_boundaryFaces
  have h₂ := G'.card_internalFaces_add_card_boundaryFaces
  have h₃ := θ.card_faces
  have h₄ := θ.card_boundaryFaces
  omega

/-- An isomorphism intertwines the powers of the face permutations. -/
theorem map_facePerm_pow (n : ℕ) (d : H) :
    θ.toEquiv ((G.facePerm ^ n) d) = (G'.facePerm ^ n) (θ.toEquiv d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, θ.map_facePerm, ih]

/-- An isomorphism maps the corners of the face through `c` to those of the face through `θ c`. -/
theorem map_squareCorner (c : H) (k : Fin 4) :
    θ.toEquiv (G.squareCorner c k) = G'.squareCorner (θ.toEquiv c) k :=
  θ.map_facePerm_pow _ _

/-- Two darts lie at the same vertex exactly when their images do. -/
theorem vertexOf_eq_vertexOf_iff (d e : H) :
    G'.vertexOf (θ.toEquiv d) = G'.vertexOf (θ.toEquiv e) ↔ G.vertexOf d = G.vertexOf e := by
  rw [← θ.map_vertexOf, ← θ.map_vertexOf, map_inj]

/-- An isomorphism maps internal vertices to internal vertices, and only those. -/
theorem vertexOf_mem_internalVertices_iff (d : H) :
    G'.vertexOf (θ.toEquiv d) ∈ G'.internalVertices ↔ G.vertexOf d ∈ G.internalVertices := by
  rw [DiskMap.vertexOf_mem_internalVertices, DiskMap.vertexOf_mem_internalVertices,
    θ.isBoundaryVertex_vertexOf_iff]

/-- An isomorphism preserves the number of darts of a vertex. -/
theorem card_vertexOf (d : H) : (G'.vertexOf (θ.toEquiv d)).card = (G.vertexOf d).card := by
  rw [← θ.map_vertexOf, card_map]

/-- An isomorphism maps internal faces to internal faces, and only those. -/
theorem map_mem_internalFaces_iff {f : Finset H} :
    f.map θ.toEquiv.toEmbedding ∈ G'.internalFaces ↔ f ∈ G.internalFaces := by
  rw [DiskMap.mem_internalFaces, DiskMap.mem_internalFaces, θ.map_mem_faces_iff, ← θ.map_bdry,
    disjoint_map]

/-- An isomorphism matches the vertices of the face through `c` with those of the face through
`θ c`. -/
theorem vertexOf_mem_squareVertices_iff (c d : H) :
    G'.vertexOf (θ.toEquiv d) ∈ G'.squareVertices (θ.toEquiv c) ↔
      G.vertexOf d ∈ G.squareVertices c := by
  simp only [mem_squareVertices, ← θ.map_squareCorner, θ.vertexOf_eq_vertexOf_iff]

/-- The conditions of a square move are transported by an isomorphism. -/
theorem isSquareMoveFace {c : H} (hq : G.IsSquareMoveFace c) :
    G'.IsSquareMoveFace (θ.toEquiv c) where
  faceOf_mem_internalFaces := by
    rw [← θ.map_faceOf, θ.map_mem_internalFaces_iff]
    exact hq.faceOf_mem_internalFaces
  facePerm_pow_four := by rw [← θ.map_facePerm_pow, hq.facePerm_pow_four]
  vertexOf_mem_internalVertices k := by
    rw [← θ.map_squareCorner, θ.vertexOf_mem_internalVertices_iff]
    exact hq.vertexOf_mem_internalVertices k
  injective k l h := hq.injective <| by
    simpa only [← θ.map_squareCorner, θ.vertexOf_eq_vertexOf_iff] using h
  card_vertexOf k := by
    rw [← θ.map_squareCorner, θ.card_vertexOf]
    exact hq.card_vertexOf k
  colour_ne k := by
    have hint : ∀ j, ¬G.IsBoundaryVertex (G.vertexOf (G.squareCorner c j)) := fun j =>
      G.vertexOf_mem_internalVertices.1 (hq.vertexOf_mem_internalVertices j)
    rw [← θ.map_squareCorner, ← θ.map_squareCorner, θ.map_colour _ (hint k),
      θ.map_colour _ (hint (k + 1))]
    exact hq.colour_ne k

/-- An isomorphism `θ : G → G'` is also an isomorphism from the square move of `G` at the face
through `c` to the square move of `G'` at the face through `θ c`. -/
def squareMove (c : H) : (G.squareMove c).Iso (G'.squareMove (θ.toEquiv c)) where
  toEquiv := θ.toEquiv
  map_inv := θ.map_inv
  map_rot := θ.map_rot
  mem_bdry_iff := θ.mem_bdry_iff
  map_colour d hd := by
    by_cases h : G.vertexOf d ∈ G.squareVertices c
    · rw [colour_squareMove_of_mem _ h,
        colour_squareMove_of_mem _ ((θ.vertexOf_mem_squareVertices_iff c d).2 h),
        θ.map_colour d hd]
    · rw [colour_squareMove_of_notMem _ h,
        colour_squareMove_of_notMem _ (mt (θ.vertexOf_mem_squareVertices_iff c d).1 h),
        θ.map_colour d hd]
  map_bvertex := θ.map_bvertex

end Iso

/-- Isomorphic tuples have the same number of faces. -/
theorem Isomorphic.card_faces {G : PlabicData H b} {G' : PlabicData H' b} (h : G.Isomorphic G') :
    G.faces.card = G'.faces.card :=
  h.elim Iso.card_faces

/-- Isomorphic tuples have the same number of internal faces. -/
theorem Isomorphic.card_internalFaces {G : PlabicData H b} {G' : PlabicData H' b}
    (h : G.Isomorphic G') : G.internalFaces.card = G'.internalFaces.card :=
  h.elim Iso.card_internalFaces

/-- If `G'` is isomorphic to the square move of `G` at a face `q`, then `G` is isomorphic to the
square move of `G'` at a face satisfying the conditions of a square move. -/
theorem IsSquareMoveFace.exists_isomorphic_squareMove {G : PlabicData H b} {G' : PlabicData H' b}
    {c : H} (hq : G.IsSquareMoveFace c) (h : G'.Isomorphic (G.squareMove c)) :
    ∃ c', G'.IsSquareMoveFace c' ∧ G.Isomorphic (G'.squareMove c') := by
  obtain ⟨θ⟩ := h
  refine ⟨θ.symm.toEquiv c, θ.symm.isSquareMoveFace hq.squareMove, ?_⟩
  have θ' := θ.symm.squareMove c
  rw [squareMove_squareMove] at θ'
  exact ⟨θ'⟩

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

/-! ### Local moves -/

/-- The three types of **local moves**: (M1) square moves, (M2) removal and insertion of bivalent
vertices, (M3) contraction and splitting of edges. -/
@[cluster_algebras "def_local_move"]
inductive LocalMoveType
  /-- (M1): the square move. -/
  | m1
  /-- (M2): the removal or insertion of a bivalent vertex. -/
  | m2
  /-- (M3): the contraction of an edge or the splitting of a vertex. -/
  | m3
  deriving DecidableEq

/-- `G'` is isomorphic to a **square move** of `G` (M1): to the square move of `G` at an internal
face `q` satisfying `ClusterAlgebras.PlabicData.IsSquareMoveFace`. -/
@[cluster_algebras "def_local_move"]
def IsSquareMove (G G' : PlabicGraph b) : Prop :=
  ∃ c, G.data.IsSquareMoveFace c ∧ G'.data.Isomorphic (G.data.squareMove c)

/-- `G'` is isomorphic to the **removal of a bivalent vertex** of `G` (M2): to the removal of an
internal vertex `{d₁, d₂}` with `d₂ = σ d₁` and `d̄₁ ≠ d₂`. -/
@[cluster_algebras "def_local_move"]
def IsBivalentRemoval (G G' : PlabicGraph b) : Prop :=
  ∃ (d : G.Dart) (hd : G.data.IsBivalentRemovable d),
    G'.data.Isomorphic (G.data.bivalentRemoval G.isPlabicGraph hd)

/-- `G'` is isomorphic to the **contraction of `G` along the edge** `{d, d̄}` (M3), whose
endpoints are distinct internal vertices of the same colour. -/
@[cluster_algebras "def_local_move"]
def IsEdgeContraction (G G' : PlabicGraph b) (d : G.Dart) : Prop :=
  ∃ he : G.data.IsContractibleEdge d,
    G'.data.Isomorphic (G.data.contractEdge d (he.leg_mem G.isPlabicGraph))

/-- **Local moves**. `IsLocalMove t G G'` says that `G'` is obtained from `G` by a local move of
type `t`:

* (M1): `G'` is isomorphic to a square move of `G`;
* (M2): `G'` is isomorphic to the removal of a bivalent vertex of `G`, or `G` is isomorphic to the
  removal of a bivalent vertex of `G'` (the insertion of a bivalent vertex);
* (M3): `G'` is isomorphic to a contraction of `G` along an edge, or `G` is isomorphic to a
  contraction of `G'` along an edge (the splitting of a vertex). -/
@[cluster_algebras "def_local_move"]
def IsLocalMove : LocalMoveType → PlabicGraph b → PlabicGraph b → Prop
  | .m1, G, G' => G.IsSquareMove G'
  | .m2, G, G' => G.IsBivalentRemoval G' ∨ G'.IsBivalentRemoval G
  | .m3, G, G' => (∃ d, G.IsEdgeContraction G' d) ∨ ∃ d, G'.IsEdgeContraction G d

/-! ### Move equivalence -/

/-- A **step** of an `S`-equivalence: `G'` is isomorphic to `G`, or is obtained from `G` by a local
move of a type in `S`. -/
@[cluster_algebras "def_move_equivalent"]
def MoveStep (S : Set LocalMoveType) (G G' : PlabicGraph b) : Prop :=
  G'.Isomorphic G ∨ ∃ t ∈ S, IsLocalMove t G G'

/-- **`S`-equivalence**: `G` and `G'` are `S`-equivalent if there is a finite sequence
`G = G₀, G₁, …, G_r = G'` of plabic graphs in which each `G_t` is isomorphic to `G_{t-1}` or is
obtained from it by a local move of a type in `S`. Two plabic graphs are
**move-equivalent**, `G ∼ G'`, if they are `MoveEquivalent Set.univ`-related. -/
@[cluster_algebras "def_move_equivalent"]
def MoveEquivalent (S : Set LocalMoveType) : PlabicGraph b → PlabicGraph b → Prop :=
  Relation.ReflTransGen (MoveStep S)

namespace MoveEquivalent

variable {S T : Set LocalMoveType} {G G' G'' : PlabicGraph b}

/-- `S`-equivalence is reflexive. -/
@[refl]
theorem refl (S : Set LocalMoveType) (G : PlabicGraph b) : MoveEquivalent S G G :=
  Relation.ReflTransGen.refl

/-- `S`-equivalence is transitive. -/
@[trans]
theorem trans (h : MoveEquivalent S G G') (h' : MoveEquivalent S G' G'') :
    MoveEquivalent S G G'' :=
  Relation.ReflTransGen.trans h h'

/-- A single step of an `S`-equivalence is an `S`-equivalence. -/
theorem of_moveStep (h : MoveStep S G G') : MoveEquivalent S G G' :=
  Relation.ReflTransGen.single h

/-- Isomorphic plabic graphs are `S`-equivalent. -/
theorem of_isomorphic (h : G'.Isomorphic G) : MoveEquivalent S G G' :=
  of_moveStep (Or.inl h)

/-- A local move of a type in `S` is an `S`-equivalence. -/
theorem of_isLocalMove {t : LocalMoveType} (ht : t ∈ S) (h : IsLocalMove t G G') :
    MoveEquivalent S G G' :=
  of_moveStep (Or.inr ⟨t, ht, h⟩)

/-- `S`-equivalence implies `T`-equivalence when `S ⊆ T`. -/
theorem mono (hST : S ⊆ T) (h : MoveEquivalent S G G') : MoveEquivalent T G G' :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.imp_right fun ⟨t, ht, h⟩ => ⟨t, hST ht, h⟩) h

end MoveEquivalent

/-! ### Face counts -/

/-- One step of an `S`-equivalence preserves the numbers of faces and of internal faces. -/
theorem MoveStep.card_eq {S : Set LocalMoveType} {G G' : PlabicGraph b} (h : MoveStep S G G') :
    G.data.faces.card = G'.data.faces.card ∧
      G.data.internalFaces.card = G'.data.internalFaces.card := by
  rcases h with θ | ⟨t, -, h⟩
  · exact ⟨θ.card_faces.symm, θ.card_internalFaces.symm⟩
  cases t with
  | m1 =>
    obtain ⟨c, -, θ⟩ := h
    exact ⟨θ.card_faces.symm, θ.card_internalFaces.symm⟩
  | m2 =>
    rcases h with ⟨d, hd, θ⟩ | ⟨d, hd, θ⟩
    · exact ⟨(θ.card_faces.trans (PlabicData.card_bivalentRemoval_faces _ hd)).symm,
        (θ.card_internalFaces.trans (PlabicData.card_bivalentRemoval_internalFaces _ hd)).symm⟩
    · exact ⟨θ.card_faces.trans (PlabicData.card_bivalentRemoval_faces _ hd),
        θ.card_internalFaces.trans (PlabicData.card_bivalentRemoval_internalFaces _ hd)⟩
  | m3 =>
    rcases h with ⟨d, he, θ⟩ | ⟨d, he, θ⟩
    · exact ⟨(θ.card_faces.trans (PlabicData.card_faces_contractEdge G.isPlabicGraph he)).symm,
        (θ.card_internalFaces.trans
          (PlabicData.card_internalFaces_contractEdge G.isPlabicGraph he)).symm⟩
    · exact ⟨θ.card_faces.trans (PlabicData.card_faces_contractEdge G'.isPlabicGraph he),
        θ.card_internalFaces.trans (PlabicData.card_internalFaces_contractEdge G'.isPlabicGraph he)⟩

/-- **Local moves preserve the numbers of faces**: `S`-equivalent plabic graphs, in particular
move-equivalent plabic graphs `G ∼ G'` (the case `S = Set.univ`), have the same number of boundary
vertices, the same number of faces and the same number of internal faces. -/
@[cluster_algebras "lem_local_move_face_count"]
theorem MoveEquivalent.card_eq {S : Set LocalMoveType} {G G' : PlabicGraph b}
    (h : MoveEquivalent S G G') :
    G.data.boundaryVertices.card = G'.data.boundaryVertices.card ∧
      G.data.faces.card = G'.data.faces.card ∧
      G.data.internalFaces.card = G'.data.internalFaces.card := by
  refine ⟨by rw [G.isPlabicGraph.card_boundaryVertices, G'.isPlabicGraph.card_boundaryVertices],
    ?_⟩
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hst ih => exact ⟨ih.1.trans hst.card_eq.1, ih.2.trans hst.card_eq.2⟩

/-! ### Symmetry -/

/-- If `G'` is isomorphic to a square move of `G`, then `G` is isomorphic to a square move of
`G'`. -/
theorem IsSquareMove.symm {G G' : PlabicGraph b} (h : G.IsSquareMove G') : G'.IsSquareMove G :=
  let ⟨_, hq, hiso⟩ := h
  hq.exists_isomorphic_squareMove hiso

/-- A local move can be reversed by a local move of the same type. -/
theorem IsLocalMove.symm {t : LocalMoveType} {G G' : PlabicGraph b} (h : IsLocalMove t G G') :
    IsLocalMove t G' G := by
  cases t with
  | m1 => exact IsSquareMove.symm h
  | m2 => exact Or.symm h
  | m3 => exact Or.symm h

/-- A step of an `S`-equivalence can be reversed. -/
theorem MoveStep.symm {S : Set LocalMoveType} {G G' : PlabicGraph b} (h : MoveStep S G G') :
    MoveStep S G' G :=
  h.imp (fun h => h.symm) fun ⟨t, ht, h⟩ => ⟨t, ht, h.symm⟩

/-- **Move equivalence is symmetric**: if `G` and `G'` are `S`-equivalent, then `G'` and `G` are
`S`-equivalent. -/
@[cluster_algebras "lem_move_equivalence_symmetric", symm]
theorem MoveEquivalent.symm {S : Set LocalMoveType} {G G' : PlabicGraph b}
    (h : MoveEquivalent S G G') : MoveEquivalent S G' G := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.head hst.symm ih

/-- `S`-equivalence is an equivalence relation. -/
theorem MoveEquivalent.equivalence (S : Set LocalMoveType) :
    Equivalence (MoveEquivalent (b := b) S) :=
  ⟨MoveEquivalent.refl S, MoveEquivalent.symm, MoveEquivalent.trans⟩

end PlabicGraph

/-! ### The relation `∘∼` -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-- The edge `{d, d̄}` **joins a white internal leaf to a white vertex with at least three darts**:
one of `v(d)`, `v(d̄)` is an internal leaf, the other has at least three darts, and both are white.
These are the contractions and splittings excluded from `∘∼`. -/
@[cluster_algebras "def_circ_move_equivalent"]
def IsWhiteLeafEdge (G : PlabicData H b) (d : H) : Prop :=
  (G.IsInternalLeaf (G.vertexOf d) ∧ G.colour d = .white ∧ G.colour (G.inv d) = .white ∧
      3 ≤ (G.vertexOf (G.inv d)).card) ∨
    (G.IsInternalLeaf (G.vertexOf (G.inv d)) ∧ G.colour (G.inv d) = .white ∧
      G.colour d = .white ∧ 3 ≤ (G.vertexOf d).card)

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

/-- A **step of the relation `∘∼`**: one of

* (a) `G'` is isomorphic to `G`;
* (b) `G'` is isomorphic to a square move of `G`;
* (c) `G'` is isomorphic to the removal of a bivalent vertex of `G`, or `G` is isomorphic to the
  removal of a bivalent vertex of `G'`;
* (d) `G'` is isomorphic to the contraction of `G` along an edge `{d, d̄}`, or `G` is isomorphic to
  the contraction of `G'` along an edge `{d, d̄}`, where in either case the edge does not join a
  white internal leaf to a white vertex with at least three darts (in the graph containing the
  edge). -/
@[cluster_algebras "def_circ_move_equivalent"]
def CircStep (G G' : PlabicGraph b) : Prop :=
  G'.Isomorphic G ∨ G.IsSquareMove G' ∨ (G.IsBivalentRemoval G' ∨ G'.IsBivalentRemoval G) ∨
    ((∃ d, ¬G.data.IsWhiteLeafEdge d ∧ G.IsEdgeContraction G' d) ∨
      ∃ d, ¬G'.data.IsWhiteLeafEdge d ∧ G'.IsEdgeContraction G d)

/-- **The relation `∘∼`**: `G ∘∼ G'` if there is a finite sequence `G = G₀, G₁, …, G_r = G'` of
plabic graphs in which each step from `G_{t-1}` to `G_t` is a `CircStep`. -/
@[cluster_algebras "def_circ_move_equivalent"]
def CircMoveEquivalent : PlabicGraph b → PlabicGraph b → Prop :=
  Relation.ReflTransGen CircStep

/-- The relation `∘∼` is reflexive. -/
@[refl]
theorem CircMoveEquivalent.refl (G : PlabicGraph b) : CircMoveEquivalent G G :=
  Relation.ReflTransGen.refl

/-- The relation `∘∼` is transitive. -/
@[trans]
theorem CircMoveEquivalent.trans {G G' G'' : PlabicGraph b} (h : CircMoveEquivalent G G')
    (h' : CircMoveEquivalent G' G'') : CircMoveEquivalent G G'' :=
  Relation.ReflTransGen.trans h h'

/-- A single step of `∘∼` is a `∘∼`-equivalence. -/
theorem CircMoveEquivalent.of_circStep {G G' : PlabicGraph b} (h : CircStep G G') :
    CircMoveEquivalent G G' :=
  Relation.ReflTransGen.single h

/-- Every step of `∘∼` is a step of move equivalence. -/
theorem CircStep.moveStep {G G' : PlabicGraph b} (h : CircStep G G') :
    MoveStep Set.univ G G' := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨.m1, trivial, h⟩
  · exact Or.inr ⟨.m2, trivial, h⟩
  · refine Or.inr ⟨.m3, trivial, ?_⟩
    rcases h with ⟨d, -, h⟩ | ⟨d, -, h⟩
    · exact Or.inl ⟨d, h⟩
    · exact Or.inr ⟨d, h⟩

/-- `G ∘∼ G'` implies `G ∼ G'`. -/
theorem CircMoveEquivalent.moveEquivalent {G G' : PlabicGraph b} (h : CircMoveEquivalent G G') :
    MoveEquivalent Set.univ G G' :=
  Relation.ReflTransGen.mono (fun _ _ => CircStep.moveStep) h

/-- A step of `∘∼` can be reversed. -/
theorem CircStep.symm {G G' : PlabicGraph b} (h : CircStep G G') : CircStep G' G := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr h.symm))

/-- **The relation `∘∼` is symmetric**: if `G ∘∼ G'`, then `G' ∘∼ G`. -/
@[cluster_algebras "lem_circ_move_symmetric", symm]
theorem CircMoveEquivalent.symm {G G' : PlabicGraph b} (h : CircMoveEquivalent G G') :
    CircMoveEquivalent G' G := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.head hst.symm ih

/-- The relation `∘∼` is an equivalence relation. -/
theorem CircMoveEquivalent.equivalence : Equivalence (CircMoveEquivalent (b := b)) :=
  ⟨CircMoveEquivalent.refl, CircMoveEquivalent.symm, CircMoveEquivalent.trans⟩

end PlabicGraph

end ClusterAlgebras
