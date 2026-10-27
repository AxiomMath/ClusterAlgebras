/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap

/-!
# The square move

Let `G` be a plabic graph and `q = (c₁, c₂, c₃, c₄)` an internal face of `G` with
`c_{k+1} = φ(c_k)` (indices modulo `4`), whose four vertices `v(c₁), …, v(c₄)` are internal,
pairwise distinct, trivalent, and alternate in colour around `q`. The *square move* (M1) of `G`
at `q` keeps the disk map `(H, d ↦ d̄, σ, B)` and the labelling `β` of `G`, and exchanges white and
black at the four vertices of `q`. Since only the colouring changes, the result is again a plabic
graph, with the same vertices, boundary vertices, legs, faces and boundary faces as `G`.

## Main definitions

* `ClusterAlgebras.PlabicData.IsSquareMoveFace`: the conditions on the face at which a square
  move applies.
* `ClusterAlgebras.PlabicData.squareMove`: the square move of `G` at a face.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.squareMove`,
  `ClusterAlgebras.PlabicData.boundaryVertices_squareMove`,
  `ClusterAlgebras.PlabicData.leg_squareMove`, `ClusterAlgebras.PlabicData.faces_squareMove`,
  `ClusterAlgebras.PlabicData.boundaryFaces_squareMove`: the square move of a plabic graph is a
  plabic graph with the same boundary vertices, legs, faces and boundary faces.
* `ClusterAlgebras.PlabicData.squareMove_squareMove`,
  `ClusterAlgebras.PlabicData.IsSquareMoveFace.squareMove`: the square move is an involution, and
  it applies again at the same face.

## Implementation notes

* The face `q` is given by its first dart `c = c₁`, and `c_{k+1}` is the corner
  `squareCorner c k = φ^k(c)` for `k : Fin 4`; the condition `φ^4(c) = c` says that `q` consists
  of these four darts, so that the indices are read modulo `4`. The colour `κ(v(c_k))` of a
  vertex is the colour of the dart `c_k`.
* The colouring of `squareMove G c` exchanges the colours at every dart whose vertex is one of the
  vertices `v(c_k)`, and the construction is defined for every dart `c` of any tuple of the shape
  of a plabic graph. That it is a plabic graph when `G` is one does not use the conditions on `q`:
  recolouring whole vertices keeps the colouring constant on each internal vertex.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-- The corner `φ^k(c)` of the face of `G` through `c`, for `k : Fin 4`; indexing the corners
from `c₁ = c`, this is the corner `c_{k+1}`. -/
def squareCorner (c : H) (k : Fin 4) : H := (G.facePerm ^ (k : ℕ)) c

/-- The vertices `v(c₁), …, v(c₄)` at the four corners `c_k = φ^{k-1}(c)` of the face through `c`.
-/
def squareVertices (c : H) : Finset (Finset H) :=
  univ.image fun k : Fin 4 => G.vertexOf (G.squareCorner c k)

/-- The conditions of the **square move** (M1) at the face `q = (c₁, c₂, c₃, c₄)` with `c₁ = c`
and `c_{k+1} = φ(c_k)`: `q` is an internal face, `φ^4(c) = c` (so `q` consists of the four darts
`c_k` and indices are read modulo `4`), and the four vertices `v(c_k)` are internal, pairwise
distinct, consist of exactly three darts each, and alternate in colour,
`κ(v(c_k)) ≠ κ(v(c_{k+1}))`. -/
@[cluster_algebras "def_square_move"]
structure IsSquareMoveFace (c : H) : Prop where
  /-- The face `q` through `c` is an internal face. -/
  faceOf_mem_internalFaces : G.faceOf c ∈ G.internalFaces
  /-- `c₅ = φ^4(c) = c₁`, so `q = (c₁, c₂, c₃, c₄)`. -/
  facePerm_pow_four : (G.facePerm ^ 4) c = c
  /-- Each `v(c_k)` is internal. -/
  vertexOf_mem_internalVertices : ∀ k, G.vertexOf (G.squareCorner c k) ∈ G.internalVertices
  /-- The `v(c_k)` are pairwise distinct. -/
  injective : Function.Injective fun k => G.vertexOf (G.squareCorner c k)
  /-- Each `v(c_k)` consists of exactly three darts. -/
  card_vertexOf : ∀ k, (G.vertexOf (G.squareCorner c k)).card = 3
  /-- Consecutive vertices have different colours: `κ(v(c_k)) ≠ κ(v(c_{k+1}))`. -/
  colour_ne : ∀ k, G.colour (G.squareCorner c k) ≠ G.colour (G.squareCorner c (k + 1))

/-- The **square move** (M1) of `G` at the face through `c`: the tuple `(H, d ↦ d̄, σ, B, κ', β)`
where `κ'` exchanges white and black at the vertices `v(c₁), …, v(c₄)` of `squareVertices c` and
is `κ` elsewhere. It is a move when `G.IsSquareMoveFace c`. -/
@[cluster_algebras "def_square_move"]
def squareMove (c : H) : PlabicData H b where
  toDiskMap := G.toDiskMap
  colour d := if G.vertexOf d ∈ G.squareVertices c then (G.colour d).swap else G.colour d
  leg := G.leg

variable {G}

/-- A vertex lies in `squareVertices c` iff it is `v(c_k)` for some `k : Fin 4`. -/
theorem mem_squareVertices {c : H} {v : Finset H} :
    v ∈ G.squareVertices c ↔ ∃ k, G.vertexOf (G.squareCorner c k) = v := by
  simp [squareVertices]

/-- Each vertex `v(c_k)` lies in `squareVertices c`. -/
theorem vertexOf_squareCorner_mem_squareVertices (c : H) (k : Fin 4) :
    G.vertexOf (G.squareCorner c k) ∈ G.squareVertices c :=
  mem_squareVertices.2 ⟨k, rfl⟩

variable (G)

/-- The square move does not change the disk map. -/
@[simp] theorem toDiskMap_squareMove (c : H) : (G.squareMove c).toDiskMap = G.toDiskMap := rfl

/-- The square move does not change the legs. -/
@[cluster_algebras "lem_square_move_plabic", simp]
theorem leg_squareMove (c : H) : (G.squareMove c).leg = G.leg := rfl

/-- The colouring of the square move exchanges white and black at the darts of the vertices in
`squareVertices c` and is `G.colour` elsewhere. -/
theorem colour_squareMove (c d : H) : (G.squareMove c).colour d =
    if G.vertexOf d ∈ G.squareVertices c then (G.colour d).swap else G.colour d := rfl

/-- At a dart of a vertex in `squareVertices c`, the square move exchanges the colour. -/
theorem colour_squareMove_of_mem {c d : H} (h : G.vertexOf d ∈ G.squareVertices c) :
    (G.squareMove c).colour d = (G.colour d).swap := if_pos h

/-- At a dart of a vertex outside `squareVertices c`, the square move keeps the colour. -/
theorem colour_squareMove_of_notMem {c d : H} (h : G.vertexOf d ∉ G.squareVertices c) :
    (G.squareMove c).colour d = G.colour d := if_neg h

/-- The square move does not change the rotation `σ`. -/
@[simp] theorem rot_squareMove (c : H) : (G.squareMove c).rot = G.rot := rfl

/-- The square move does not change the involution `d ↦ d̄`. -/
@[simp] theorem inv_squareMove (c : H) : (G.squareMove c).inv = G.inv := rfl

/-- The square move does not change the boundary darts `B`. -/
@[simp] theorem bdry_squareMove (c : H) : (G.squareMove c).bdry = G.bdry := rfl

/-- The square move does not change the face permutation `φ`. -/
@[simp] theorem facePerm_squareMove (c : H) : (G.squareMove c).facePerm = G.facePerm := rfl

/-- The square move does not change the vertex of each dart. -/
@[simp] theorem vertexOf_squareMove (c : H) : (G.squareMove c).vertexOf = G.vertexOf := rfl

/-- The square move does not change the face of each dart. -/
@[simp] theorem faceOf_squareMove (c : H) : (G.squareMove c).faceOf = G.faceOf := rfl

/-- The square move does not change the vertex `β(i)` labelled `i`. -/
@[simp] theorem bvertex_squareMove (c : H) : (G.squareMove c).bvertex = G.bvertex := rfl

/-- The square move does not change the vertices. -/
@[simp] theorem vertices_squareMove (c : H) : (G.squareMove c).vertices = G.vertices := rfl

/-- The square move does not change the internal vertices. -/
@[simp] theorem internalVertices_squareMove (c : H) :
    (G.squareMove c).internalVertices = G.internalVertices := rfl

/-- The square move does not change the boundary vertices. -/
@[cluster_algebras "lem_square_move_plabic", simp]
theorem boundaryVertices_squareMove (c : H) :
    (G.squareMove c).boundaryVertices = G.boundaryVertices := rfl

/-- The square move does not change the exterior face. -/
@[simp] theorem exterior_squareMove (c : H) : (G.squareMove c).exterior = G.exterior := rfl

/-- The square move does not change the faces. -/
@[cluster_algebras "lem_square_move_plabic", simp]
theorem faces_squareMove (c : H) : (G.squareMove c).faces = G.faces := rfl

/-- The square move does not change the boundary faces. -/
@[cluster_algebras "lem_square_move_plabic", simp]
theorem boundaryFaces_squareMove (c : H) :
    (G.squareMove c).boundaryFaces = G.boundaryFaces := rfl

/-- The square move does not change the internal faces. -/
@[simp] theorem internalFaces_squareMove (c : H) :
    (G.squareMove c).internalFaces = G.internalFaces := rfl

/-- The square move does not change the corners `squareCorner`. -/
@[simp] theorem squareCorner_squareMove (c : H) :
    (G.squareMove c).squareCorner = G.squareCorner := rfl

/-- The square move does not change the vertices `squareVertices`. -/
@[simp] theorem squareVertices_squareMove (c : H) :
    (G.squareMove c).squareVertices = G.squareVertices := rfl

/-- The square move at a face is an involution. -/
@[simp] theorem squareMove_squareMove (c : H) : (G.squareMove c).squareMove c = G := by
  have hc : ((G.squareMove c).squareMove c).colour = G.colour := by
    funext d
    rw [colour_squareMove, squareVertices_squareMove, vertexOf_squareMove, colour_squareMove]
    split_ifs <;> simp [Shade.swap_swap]
  cases G
  simp only [squareMove] at hc ⊢
  rw [hc]

/-- **A square move gives a plabic graph**: the square move of a plabic graph at any face is a
plabic graph. Its disk map and labelling are those of `G`, so it has
the same vertices, boundary vertices, legs, faces and boundary faces as `G`
(`boundaryVertices_squareMove`, `leg_squareMove`, `faces_squareMove`,
`boundaryFaces_squareMove`). -/
@[cluster_algebras "lem_square_move_plabic"]
theorem IsPlabicGraph.squareMove {G : PlabicData H b} (hG : G.IsPlabicGraph) (c : H) :
    (G.squareMove c).IsPlabicGraph where
  toIsDiskMap := hG.toIsDiskMap
  one_le := hG.one_le
  colour_rot d hd := by
    rw [colour_squareMove, colour_squareMove, rot_squareMove, G.vertexOf_rot,
      hG.colour_rot d (by simpa using hd)]
  leg_notMem_bdry := hG.leg_notMem_bdry
  bvertex_mem := hG.bvertex_mem
  bvertex_injective := hG.bvertex_injective
  exists_bvertex_eq := hG.exists_bvertex_eq
  exists_exterior := hG.exists_exterior

/-- After a square move at `q`, a square move at `q` applies again: the four vertices are
unchanged and their colours still alternate. -/
theorem IsSquareMoveFace.squareMove {G : PlabicData H b} {c : H} (hq : G.IsSquareMoveFace c) :
    (G.squareMove c).IsSquareMoveFace c where
  faceOf_mem_internalFaces := hq.faceOf_mem_internalFaces
  facePerm_pow_four := hq.facePerm_pow_four
  vertexOf_mem_internalVertices := hq.vertexOf_mem_internalVertices
  injective := hq.injective
  card_vertexOf := hq.card_vertexOf
  colour_ne k := by
    rw [squareCorner_squareMove,
      colour_squareMove_of_mem _ (vertexOf_squareCorner_mem_squareVertices c k),
      colour_squareMove_of_mem _ (vertexOf_squareCorner_mem_squareVertices c (k + 1))]
    exact (Function.LeftInverse.injective Shade.swap_swap).ne (hq.colour_ne k)

end PlabicData

end ClusterAlgebras
