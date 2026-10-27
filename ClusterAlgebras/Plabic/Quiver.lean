/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Plabic.Basic

/-!
# The quiver of a plane bipartite graph

The quiver `Q(G)` of a plane bipartite graph `G` has the faces of `G` as vertices, the faces
incident to the boundary being frozen. Each edge off the boundary gives an arrow between the two
faces it separates, oriented so that it sees the white end of the edge on its left and the black
end on its right; arrows between two boundary-incident faces are deleted, and two-cycles are
cancelled.

## Main definitions

* `edgeCount`: the number of edges running from one face to another.
* `plabicArrows`: the arrow counts of `Q(G)`.
* `plabicQuiver`: the quiver `Q(G)` of `G`.

## Main results

* `edgeCount_self`: no edge runs from a face to itself.
* `isArrowSystem_plabicArrows`: `Q(G)` has no loops.
* `twoCycleFree_plabicArrows`: `Q(G)` has no two-cycles.
* `plabicArrows_eq_zero_of_frozen`: `Q(G)` has no arrow between two boundary-incident faces.

## Implementation notes

An edge off the boundary has exactly one dart at its white end, namely `rightSide`. The edges from
a face `f` to a face `f'` are therefore counted as the white darts off the boundary whose orbit is
`f` and whose reverse's orbit is `f'`, with no quotient by the edge involution.

Arrows between two boundary-incident faces are deleted before cancelling two-cycles. Without this
deletion the construction need not produce a quiver: in a quadrilateral with a leg at each corner,
each of the four legs separates two boundary-incident faces.
-/

@[expose] public section

namespace ClusterAlgebras

namespace Plabic

variable {H : Type*} [Fintype H] [DecidableEq H] (G : Plabic H)

/-- The number of edges running from the face `f` to the face `f'`: the number of darts at a white
end, off the boundary, whose orbit is `f` and whose reverse's orbit is `f'`. -/
def edgeCount (f f' : G.Face) : ℕ :=
  (Finset.univ.filter fun d : H => d ∉ G.bdry ∧ G.shade d = Shade.white ∧
      G.orbitOf d = f.val ∧ G.orbitOf (G.rev d) = f'.val).card

/-- In a disk, no edge runs from a face to itself: `G.edgeCount f f = 0`. -/
theorem edgeCount_self (hd : G.IsDisk) (f : G.Face) : G.edgeCount f f = 0 := by
  rw [edgeCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro d - ⟨hb, -, h1, h2⟩
  exact G.sides_not_sameFace hd hb (G.orbitOf_eq_iff.1 (h1.trans h2.symm))

/-- The arrow counts of `Q(G)`: zero between two boundary-incident faces, and otherwise the
cancellation of the two-cycles of `edgeCount`. -/
@[cluster_algebras "def_plabic_quiver"]
def plabicArrows (f f' : G.Face) : ℕ :=
  if f.IncidentBoundary ∧ f'.IncidentBoundary then 0
  else cancellation (G.edgeCount) f f'

/-- In a disk, `Q(G)` has no loops. -/
@[cluster_algebras "lem_plabic_quiver_is_quiver"]
theorem isArrowSystem_plabicArrows (hd : G.IsDisk) : IsArrowSystem (G.plabicArrows) := by
  intro f
  rw [plabicArrows]
  split_ifs with h
  · rfl
  · rw [cancellation, G.edgeCount_self hd]
    simp

/-- `Q(G)` has no two-cycles. -/
@[cluster_algebras "lem_plabic_quiver_is_quiver"]
theorem twoCycleFree_plabicArrows : TwoCycleFree (G.plabicArrows) := by
  intro f f'
  by_cases h : f.IncidentBoundary ∧ f'.IncidentBoundary
  · left; rw [plabicArrows, if_pos h]
  · by_cases h' : f'.IncidentBoundary ∧ f.IncidentBoundary
    · right; rw [plabicArrows, if_pos h']
    · rw [plabicArrows, if_neg h, plabicArrows, if_neg h']
      exact cancellation_twoCycleFree G.edgeCount f f'

/-- `Q(G)` has no arrow between two boundary-incident faces. -/
@[cluster_algebras "lem_plabic_quiver_is_quiver"]
theorem plabicArrows_eq_zero_of_frozen {f f' : G.Face} (h : f.IncidentBoundary)
    (h' : f'.IncidentBoundary) : G.plabicArrows f f' = 0 := by
  rw [plabicArrows, if_pos ⟨h, h'⟩]

/-- The quiver `Q(G)` of the plane bipartite graph `G`: its vertices are the faces, its frozen
vertices those incident to the boundary, and its arrows are given by `plabicArrows`. -/
@[cluster_algebras "def_plabic_quiver"]
def plabicQuiver (hd : G.IsDisk) : Quiver G.Face where
  frozen := Finset.univ.filter fun f : G.Face => f.IncidentBoundary
  arrows := G.plabicArrows
  isArrowSystem := G.isArrowSystem_plabicArrows hd
  twoCycleFree := G.twoCycleFree_plabicArrows
  frozen_eq_zero f hf f' hf' :=
    G.plabicArrows_eq_zero_of_frozen (by simpa using hf) (by simpa using hf')

/-- The arrows of `Q(G)` are given by `plabicArrows`. -/
@[simp]
theorem arrows_plabicQuiver (hd : G.IsDisk) :
    (G.plabicQuiver hd).arrows = G.plabicArrows := rfl

/-- The frozen vertices of `Q(G)` are the boundary-incident faces. -/
@[simp]
theorem mem_frozen_plabicQuiver (hd : G.IsDisk) (f : G.Face) :
    f ∈ (G.plabicQuiver hd).frozen ↔ f.IncidentBoundary := by
  rw [plabicQuiver]; simp

end Plabic

end ClusterAlgebras
