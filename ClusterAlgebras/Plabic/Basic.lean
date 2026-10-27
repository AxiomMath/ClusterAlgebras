/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Quiver

/-!
# Plane bipartite graphs in a disk

A plane bipartite graph in a disk is encoded as a **rotation system**: a finite set of darts, a
fixed-point-free involution `rev` pairing them into edges, and a permutation `rot` whose orbits are
the vertices. The face permutation is `face = rot ∘ rev`, and its orbits are the faces together
with the exterior. A side of an edge is one of its two darts, and the left and right sides are told
apart by which one points out of the white end.

## Main definitions

* `ClusterAlgebras.Plabic`: a plane bipartite graph in a disk, as a rotation system with a
  distinguished set of boundary darts and a designated dart of the exterior.
* `ClusterAlgebras.Plabic.face`: the face permutation `rot ∘ rev`.
* `ClusterAlgebras.Plabic.Face`: the faces of the graph, the orbits of `face` other than the
  exterior.
* `ClusterAlgebras.Plabic.IsDisk`: the conditions quantifying over faces and vertices:
  connectivity, Euler's relation, the description of the boundary, the degree conditions and
  simple connectivity of faces.
* `ClusterAlgebras.Plabic.rightSide`, `ClusterAlgebras.Plabic.leftSide`: the two sides of an edge.

## Main results

* `ClusterAlgebras.Plabic.sides_not_sameFace`: the two sides of an edge off the boundary lie in
  distinct orbits of the face permutation.

## Implementation notes

Orbits are `Equiv.Perm.SameCycle`, and a face is represented by the `Finset` of its darts, so the
type of faces carries `DecidableEq` and `Fintype`.

The boundary of the disk is part of the graph: a leg to a boundary vertex is a bridge of the graph
alone, and a bridge has both its sides in one face, so without the boundary arcs
`ClusterAlgebras.Plabic.sides_not_sameFace` would be false.
-/

@[expose] public section

namespace ClusterAlgebras

/-- The two colours of a bipartite graph's vertices. -/
inductive Shade
  /-- A white vertex. -/
  | white : Shade
  /-- A black vertex. -/
  | black : Shade
  deriving DecidableEq, Repr

namespace Shade

/-- An arbitrary colour, so that partial functions have a default to fall back on. -/
instance instInhabitedShade : Inhabited Shade := ⟨.white⟩

/-- The other colour. -/
def swap : Shade → Shade
  | .white => .black
  | .black => .white

/-- Swapping white gives black. -/
@[simp] theorem swap_white : Shade.white.swap = .black := rfl

/-- Swapping black gives white. -/
@[simp] theorem swap_black : Shade.black.swap = .white := rfl

/-- Swapping never fixes a colour. -/
theorem swap_ne (s : Shade) : s.swap ≠ s := by cases s <;> simp

/-- Swapping twice gives back the colour. -/
@[simp] theorem swap_swap (s : Shade) : s.swap.swap = s := by cases s <;> rfl

end Shade

/-- A **plane bipartite graph in a disk**, as a rotation system on a finite set of darts.

`rev` pairs darts into edges, `rot` is the rotation whose orbits are the vertices, `bdry` carries
the disk's boundary arcs with `extDart` a dart of the exterior, and `shade` colours the vertices —
recorded on darts and constant along each rotation orbit, which is `shade_rot`.

The conditions that quantify over faces or vertices — the boundary being exactly the exterior orbit
and its reverses, Euler's relation, connectivity, and the two degree conditions — are `IsDisk`
below, since they need `face` and so cannot be fields of this structure. -/
@[cluster_algebras "def_plane_bipartite_graph"]
structure Plabic (H : Type*) [Fintype H] [DecidableEq H] where
  /-- The involution pairing darts into edges. -/
  rev : Equiv.Perm H
  /-- Reversal is an involution. -/
  rev_rev : ∀ d, rev (rev d) = d
  /-- No dart is its own reverse, so every edge has two distinct sides. -/
  rev_ne : ∀ d, rev d ≠ d
  /-- The rotation, whose orbits are the vertices. -/
  rot : Equiv.Perm H
  /-- The colour of the vertex a dart points out of. -/
  shade : H → Shade
  /-- The colour is a property of the vertex, not of the dart. -/
  shade_rot : ∀ d, shade (rot d) = shade d
  /-- The darts lying on the disk's boundary. -/
  bdry : Finset H
  /-- The boundary is closed under reversal. -/
  bdry_rev : ∀ d, d ∈ bdry ↔ rev d ∈ bdry
  /-- Every edge off the boundary joins vertices of different colours. -/
  shade_rev : ∀ d, d ∉ bdry → shade (rev d) = (shade d).swap
  /-- A dart of the exterior, which designates it. -/
  extDart : H
  /-- The exterior lies on the boundary. -/
  extDart_mem : extDart ∈ bdry

namespace Plabic

variable {H : Type*} [Fintype H] [DecidableEq H] (G : Plabic H)

/-- **The face permutation** `rot ∘ rev`, whose orbits are the faces and the exterior. -/
def face : Equiv.Perm H := G.rev.trans G.rot

/-- The face permutation, applied. -/
@[simp]
theorem face_apply (d : H) : G.face d = G.rot (G.rev d) := rfl

/-- Two darts lie in one orbit of the face permutation. -/
abbrev SameFace (d e : H) : Prop := G.face.SameCycle d e

/-- Lying in one face is decidable, the darts being finite in number. -/
instance instDecidableRelSameFace : DecidableRel G.SameFace :=
  Equiv.Perm.instDecidableRelSameCycle G.face

/-- **The orbit of a dart under the face permutation**, as a finite set of darts. -/
def orbitOf (d : H) : Finset H := {e ∈ Finset.univ | G.SameFace d e}

/-- Membership in a dart's face orbit, unfolded. -/
@[simp]
theorem mem_orbitOf {d e : H} : e ∈ G.orbitOf d ↔ G.SameFace d e := by simp [orbitOf]

/-- A dart lies in its own orbit. -/
@[simp]
theorem self_mem_orbitOf (d : H) : d ∈ G.orbitOf d :=
  G.mem_orbitOf.2 (Equiv.Perm.SameCycle.refl _ _)

/-- Darts of one orbit have the same orbit, so the representation is faithful. -/
theorem orbitOf_eq_iff {d e : H} : G.orbitOf d = G.orbitOf e ↔ G.SameFace d e := by
  refine ⟨fun h => G.mem_orbitOf.1 (h ▸ G.self_mem_orbitOf e), fun h => ?_⟩
  ext x
  simpa only [mem_orbitOf] using ⟨h.symm.trans, h.trans⟩

/-- **The exterior**: the orbit of the designated dart. -/
def exterior : Finset H := G.orbitOf G.extDart

/-- Membership in the exterior, unfolded. -/
@[simp]
theorem mem_exterior {e : H} : e ∈ G.exterior ↔ G.SameFace G.extDart e := G.mem_orbitOf

/-- The designated dart lies in the exterior. -/
@[simp]
theorem extDart_mem_exterior : G.extDart ∈ G.exterior := G.self_mem_orbitOf _

/-- **A face** of `G`: an orbit of the face permutation other than the exterior. -/
@[cluster_algebras "def_face"]
def Face : Type _ := {s : Finset H // (∃ d, s = G.orbitOf d) ∧ s ≠ G.exterior}

/-- Faces are finsets of darts, so equality is decidable. -/
instance instDecidableEqFace : DecidableEq G.Face :=
  inferInstanceAs (DecidableEq {s : Finset H // (∃ d, s = G.orbitOf d) ∧ s ≠ G.exterior})

/-- There are finitely many faces, which is what `Quiver` requires of its vertex type. -/
instance instFintypeFace : Fintype G.Face :=
  inferInstanceAs (Fintype {s : Finset H // (∃ d, s = G.orbitOf d) ∧ s ≠ G.exterior})

/-- **A face is incident to the boundary** when it contains a boundary dart. -/
@[cluster_algebras "def_face"]
def Face.IncidentBoundary (f : G.Face) : Prop := ∃ d ∈ G.bdry, d ∈ f.val

/-- Incidence to the boundary is decidable. -/
instance instDecidablePredIncidentBoundary :
    DecidablePred (Face.IncidentBoundary (G := G)) := fun _ => by
  rw [Face.IncidentBoundary]
  infer_instance

/-! ### Vertices, and the conditions that make the graph a disk -/

/-- **The orbit of a dart under the rotation**: the vertex it points out of, as the set of darts
there. -/
def vertexOf (d : H) : Finset H := {e ∈ Finset.univ | G.rot.SameCycle d e}

/-- Membership in a dart's vertex, unfolded. -/
@[simp]
theorem mem_vertexOf {d e : H} : e ∈ G.vertexOf d ↔ G.rot.SameCycle d e := by simp [vertexOf]

/-- A dart lies in its own vertex. -/
@[simp]
theorem self_mem_vertexOf (d : H) : d ∈ G.vertexOf d :=
  G.mem_vertexOf.2 (Equiv.Perm.SameCycle.refl _ _)

/-- The vertices of `G`. -/
def vertexSet : Finset (Finset H) := Finset.image G.vertexOf Finset.univ

/-- The orbits of the face permutation: the faces together with the exterior. -/
def orbitSet : Finset (Finset H) := Finset.image G.orbitOf Finset.univ

/-- Membership in the vertex set, unfolded. -/
@[simp]
theorem mem_vertexSet {s : Finset H} : s ∈ G.vertexSet ↔ ∃ d, G.vertexOf d = s := by
  simp [vertexSet]

/-- Membership in the orbit set, unfolded. -/
@[simp]
theorem mem_orbitSet {s : Finset H} : s ∈ G.orbitSet ↔ ∃ d, G.orbitOf d = s := by
  simp [orbitSet]

/-- **A boundary vertex** is one meeting the disk's boundary; the others are **interior**. -/
def IsBoundaryVertex (d : H) : Prop := ∃ e ∈ G.vertexOf d, e ∈ G.bdry

/-- Being a boundary vertex is decidable. -/
instance instDecidablePredIsBoundaryVertex : DecidablePred G.IsBoundaryVertex := fun _ => by
  rw [IsBoundaryVertex]
  infer_instance

/-- **Reachability** in the graph: `rot` and `rev` generate it, so this is connectivity of the
underlying graph together with its boundary arcs. -/
inductive Reach : H → H → Prop
  /-- Every dart reaches itself. -/
  | refl (d : H) : Reach d d
  /-- Turning at a vertex stays in the same component. -/
  | rot {d e : H} : Reach d e → Reach d (G.rot e)
  /-- Crossing an edge stays in the same component. -/
  | rev {d e : H} : Reach d e → Reach d (G.rev e)

/-- **Reachability with one edge deleted**: as `Reach`, but the edge `{c, rev c}` may not be
crossed. `ReachAvoiding c x y` for every `x` and `y` says that edge is not a bridge. -/
inductive ReachAvoiding (c : H) : H → H → Prop
  /-- Every dart reaches itself. -/
  | refl (d : H) : ReachAvoiding c d d
  /-- Turning at a vertex is always allowed. -/
  | rot {d e : H} : ReachAvoiding c d e → ReachAvoiding c d (G.rot e)
  /-- Crossing any edge but the deleted one is allowed. -/
  | rev {d e : H} : ReachAvoiding c d e → e ≠ c → e ≠ G.rev c →
      ReachAvoiding c d (G.rev e)

/-- **The conditions on a plane bipartite graph in a disk that quantify over faces or vertices.**

Euler's relation expresses planarity. Simple connectivity of the faces does not follow from the
other conditions: a four-cycle of interior vertices attached to the rest of the graph by a single
edge satisfies every degree condition and Euler's relation, and that edge has both of its sides in
one face. -/
@[cluster_algebras "def_plane_bipartite_graph"]
structure IsDisk : Prop where
  /-- The graph, boundary included, is connected. -/
  connected : ∀ d e, G.Reach d e
  /-- Euler's relation, which is what planarity means for a rotation system. -/
  planar : G.vertexSet.card + G.orbitSet.card = Fintype.card H / 2 + 2
  /-- The boundary arcs are exactly the exterior's darts and their reverses. -/
  bdry_eq : ∀ d, d ∈ G.bdry ↔ (d ∈ G.exterior ∨ G.rev d ∈ G.exterior)
  /-- The exterior contains exactly one dart of each boundary edge. -/
  ext_one_per_edge : ∀ d ∈ G.exterior, G.rev d ∉ G.exterior
  /-- A boundary vertex has two boundary darts and one other. -/
  bdry_degree : ∀ d, G.IsBoundaryVertex d →
    ((G.vertexOf d).filter (· ∈ G.bdry)).card = 2 ∧
      ((G.vertexOf d).filter (· ∉ G.bdry)).card = 1
  /-- An interior vertex has degree at least two. -/
  int_degree : ∀ d, ¬G.IsBoundaryVertex d → 2 ≤ (G.vertexOf d).card
  /-- **Simple connectivity**: no orbit of the face permutation contains both darts of an edge off
  the boundary. This says the closure of each face is simply connected: a face whose walk crossed
  an edge twice, once on each side, would have an annulus for its closure, and conversely. -/
  simplyConnected : ∀ d ∉ G.bdry, ¬G.SameFace d (G.rev d)

/-! ### The two sides of an edge

A side of an edge is one of its two darts. -/

/-- **The right side of the edge through `d`**: `d` if it points out of a white vertex, else its
reverse; for an edge off the boundary this is the dart pointing out of the white end. -/
@[cluster_algebras "def_edge_sides"]
def rightSide (d : H) : H := if G.shade d = .white then d else G.rev d

/-- **The left side of the edge through `d`**: the other dart. -/
@[cluster_algebras "def_edge_sides"]
def leftSide (d : H) : H := G.rev (G.rightSide d)

/-- The left and right sides of an edge are distinct. -/
theorem leftSide_ne_rightSide (d : H) : G.leftSide d ≠ G.rightSide d :=
  G.rev_ne _

/-- Reversing the right side gives the left side. -/
@[simp]
theorem rev_rightSide (d : H) : G.rev (G.rightSide d) = G.leftSide d := rfl

/-- Reversing the left side gives the right side. -/
@[simp]
theorem rev_leftSide (d : H) : G.rev (G.leftSide d) = G.rightSide d := G.rev_rev _

/-- Reversing a dart does not change which edge it is a side of. -/
@[simp]
theorem rightSide_rev (d : H) (hd : d ∉ G.bdry) : G.rightSide (G.rev d) = G.rightSide d := by
  have hrev := G.shade_rev d hd
  unfold rightSide
  cases hs : G.shade d <;> simp_all [G.rev_rev]

/-- The right side of an edge off the boundary points out of a white vertex. -/
theorem shade_rightSide (d : H) (hd : d ∉ G.bdry) : G.shade (G.rightSide d) = .white := by
  have hrev := G.shade_rev d hd
  unfold rightSide
  cases hs : G.shade d <;> simp_all

/-! ### An edge has two distinct sides lying in two distinct faces -/

/-- The two sides of an edge off the boundary lie in distinct orbits of the face permutation. -/
@[cluster_algebras "lem_edge_faces_distinct"]
theorem sides_not_sameFace (hd : G.IsDisk) {d : H} (hb : d ∉ G.bdry) :
    ¬G.SameFace d (G.rev d) := hd.simplyConnected d hb

/-- The two sides of an edge off the boundary lie in different orbits, as finsets. -/
theorem orbitOf_rightSide_ne_orbitOf_leftSide (hd : G.IsDisk) {d : H} (hb : d ∉ G.bdry) :
    G.orbitOf (G.rightSide d) ≠ G.orbitOf (G.leftSide d) := by
  rw [Ne, G.orbitOf_eq_iff, leftSide]
  refine G.sides_not_sameFace hd ?_
  rw [rightSide]
  split_ifs
  · exact hb
  · exact fun hcon => hb ((G.bdry_rev d).2 hcon)

end Plabic

end ClusterAlgebras
