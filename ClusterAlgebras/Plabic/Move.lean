/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Plabic.Quiver

/-!
# The contraction and spider moves

The contraction move deletes four darts and the spider move adds twelve, so neither is a function
on a fixed dart type. Both are relations between two plabic graphs, carrying an explicit
correspondence between the darts that survive. Whether the result is a plane bipartite graph is a
property of the result, already carried by its own fields.

## Main definitions

* `IsContraction`: `G'` is obtained from `G` by contracting a bivalent interior vertex.
* `IsSpiderMovable`: a face of `G` is a quadrilateral to which the spider move applies.
* `IsSpiderMove`: `G'` is obtained from `G` by the spider move at a quadrilateral face.

## Implementation notes

Contracting at a bivalent interior vertex `v` with darts `d₁` and `d₂` deletes `d₁`, `d₂` and the
two darts `rev d₁`, `rev d₂` facing them, and merges the two neighbouring vertices into one.
Splicing the deleted darts out of the rotation does not merge them: following the rotation from a
dart of the first neighbour, on reaching `rev d₁` one comes back round to the first neighbour. The
two cycles are joined by crossing over: where the rotation would reach `rev d₁`, the merged
rotation goes to `rot (rev d₂)` instead, and vice versa. This is `IsContraction.rot_merged_left`
and `IsContraction.rot_merged_right`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace Plabic

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']

/-- The four darts a contraction at the bivalent vertex of `d₁` and `d₂` deletes: those two, and
the two facing them. -/
def contractDeleted (G : Plabic H) (d₁ d₂ : H) : Finset H :=
  {d₁, G.rev d₁, d₂, G.rev d₂}

/-- **`G'` is the contraction of `G` at the bivalent interior vertex of `d₁` and `d₂`.**

The vertex has exactly the two darts, it is interior, and its two neighbours are interior and
distinct; `G'` is `G` with the four darts of `contractDeleted` removed, everything inherited
through `e`, and the two neighbour vertices merged. Read the other way, this relation is
decontraction. -/
@[cluster_algebras "def_contraction_move"]
structure IsContraction (G : Plabic H) (G' : Plabic H') (d₁ d₂ : H)
    (e : {d : H // d ∉ G.contractDeleted d₁ d₂} ≃ H') : Prop where
  /-- The contracted vertex has exactly the two darts `d₁` and `d₂`. -/
  bivalent : G.vertexOf d₁ = {d₁, d₂}
  /-- They are different darts. -/
  darts_ne : d₁ ≠ d₂
  /-- The contracted vertex is interior. -/
  interior : ¬G.IsBoundaryVertex d₁
  /-- Its first neighbour is interior. -/
  nbr_interior_left : ¬G.IsBoundaryVertex (G.rev d₁)
  /-- Its second neighbour is interior. -/
  nbr_interior_right : ¬G.IsBoundaryVertex (G.rev d₂)
  /-- The two neighbours are distinct vertices, so the contraction merges rather than loops. -/
  nbr_ne : G.vertexOf (G.rev d₁) ≠ G.vertexOf (G.rev d₂)
  /-- Reversal is inherited. -/
  rev_eq : ∀ d, (e.symm (G'.rev d)).val = G.rev (e.symm d).val
  /-- The colouring is inherited; the merged vertex keeps the neighbours' common colour. -/
  shade_eq : ∀ d, G'.shade d = G.shade (e.symm d).val
  /-- The boundary is inherited. -/
  bdry_eq : ∀ d, d ∈ G'.bdry ↔ (e.symm d).val ∈ G.bdry
  /-- Away from the merged vertex the rotation is inherited. -/
  rot_eq : ∀ d, G.rot (e.symm d).val ∉ G.contractDeleted d₁ d₂ →
      (e.symm (G'.rot d)).val = G.rot (e.symm d).val
  /-- **At the merged vertex the two rotations are joined by crossing over.** Where the rotation
  of `G` would reach one of the two facing darts, the merged rotation continues from the other
  one's successor. -/
  rot_merged_left : ∀ d, G.rot (e.symm d).val = G.rev d₁ →
      (e.symm (G'.rot d)).val = G.rot (G.rev d₂)
  /-- The mirror of `rot_merged_left`. -/
  rot_merged_right : ∀ d, G.rot (e.symm d).val = G.rev d₂ →
      (e.symm (G'.rot d)).val = G.rot (G.rev d₁)

/-- Reversal, moved across an equation. -/
theorem rev_eq_iff (G : Plabic H) {d x : H} : G.rev d = x ↔ d = G.rev x :=
  ⟨fun h => by rw [← h, G.rev_rev], fun h => by rw [h, G.rev_rev]⟩

/-- The eight darts of a spider-movable face's four edges, which the move deletes. -/
def spiderDeleted (G : Plabic H) (c₁ c₂ c₃ c₄ : H) : Finset H :=
  {c₁, G.rev c₁, c₂, G.rev c₂, c₃, G.rev c₃, c₄, G.rev c₄}

/-- The deleted set is closed under reversal, being a union of edges. -/
theorem rev_mem_spiderDeleted_iff (G : Plabic H) (c₁ c₂ c₃ c₄ d : H) :
    G.rev d ∈ G.spiderDeleted c₁ c₂ c₃ c₄ ↔ d ∈ G.spiderDeleted c₁ c₂ c₃ c₄ := by
  simp only [spiderDeleted, Finset.mem_insert, Finset.mem_singleton, G.rev_eq_iff, G.rev_rev]
  tauto

/-- The reverse of a dart outside the deleted set is outside it. -/
theorem rev_notMem_spiderDeleted (G : Plabic H) {c₁ c₂ c₃ c₄ d : H}
    (h : d ∉ G.spiderDeleted c₁ c₂ c₃ c₄) : G.rev d ∉ G.spiderDeleted c₁ c₂ c₃ c₄ :=
  fun hc => h ((G.rev_mem_spiderDeleted_iff c₁ c₂ c₃ c₄ d).1 hc)

/-- **A face is spider-movable**: it has exactly four darts, none on the boundary, at four distinct
vertices which alternate in colour and each have at least three darts. -/
def IsSpiderMovable (G : Plabic H) (c₁ c₂ c₃ c₄ : H) : Prop :=
  G.orbitOf c₁ = {c₁, c₂, c₃, c₄} ∧
    G.face c₁ = c₂ ∧ G.face c₂ = c₃ ∧ G.face c₃ = c₄ ∧ G.face c₄ = c₁ ∧
    (∀ c ∈ ({c₁, c₂, c₃, c₄} : Finset H), c ∉ G.bdry) ∧
    G.vertexOf c₁ ≠ G.vertexOf c₂ ∧ G.vertexOf c₂ ≠ G.vertexOf c₃ ∧
      G.vertexOf c₃ ≠ G.vertexOf c₄ ∧ G.vertexOf c₄ ≠ G.vertexOf c₁ ∧
    G.shade c₂ = (G.shade c₁).swap ∧ G.shade c₃ = G.shade c₁ ∧
      G.shade c₄ = (G.shade c₁).swap ∧
    (∀ c ∈ ({c₁, c₂, c₃, c₄} : Finset H), 3 ≤ (G.vertexOf c).card)

/-- **The darts a spider move adds**: those outside the range of the correspondence on surviving
darts. Twelve of them — eight for the new quadrilateral and four legs. -/
def spiderNew (G : Plabic H) (c₁ c₂ c₃ c₄ : H)
    (e : {d : H // d ∉ G.spiderDeleted c₁ c₂ c₃ c₄} ↪ H') : Finset H' :=
  Finset.univ \ Finset.univ.image e

/-- **`G'` is the spider move of `G` at the quadrilateral face of `c₁, c₂, c₃, c₄`.**

The face's four edges are deleted; four new vertices appear, each coloured against the old vertex
it faces, joined into a new four-dart face; and four legs join each old vertex to its new
counterpart, the leg's dart at the old vertex taking the place in that vertex's rotation vacated by
the deleted dart.

`newDarts` is the twelve darts the move adds — eight for the new quadrilateral and four pairs for
the legs, less the four that the correspondence `e` already accounts for. Everything the move does
not touch is inherited through `e`, exactly as for a contraction. -/
@[cluster_algebras "def_spider_move"]
structure IsSpiderMove (G : Plabic H) (G' : Plabic H') (c₁ c₂ c₃ c₄ : H)
    (e : {d : H // d ∉ G.spiderDeleted c₁ c₂ c₃ c₄} ↪ H') : Prop where
  /-- The face is spider-movable. -/
  movable : G.IsSpiderMovable c₁ c₂ c₃ c₄
  /-- Reversal is inherited on the surviving darts. -/
  rev_eq : ∀ d, G'.rev (e d) = e ⟨G.rev d.val, G.rev_notMem_spiderDeleted d.2⟩
  /-- The colouring is inherited on the surviving darts. -/
  shade_eq : ∀ d, G'.shade (e d) = G.shade d.val
  /-- The boundary is inherited, and the move adds no boundary arcs. -/
  bdry_eq : ∀ d, e d ∈ G'.bdry ↔ d.val ∈ G.bdry
  /-- The move adds twelve darts: eight for the new quadrilateral, four legs. -/
  card_spiderNew : (G.spiderNew c₁ c₂ c₃ c₄ e).card = 12
  /-- The new darts contain a four-dart face, which is the moved quadrilateral. -/
  exists_new_face : ∃ u ∈ G.spiderNew c₁ c₂ c₃ c₄ e,
    G'.orbitOf u ⊆ G.spiderNew c₁ c₂ c₃ c₄ e ∧ (G'.orbitOf u).card = 4
  /-- Each new vertex is coloured against the old vertex its leg joins it to. -/
  legs_shade : ∀ i ∈ ({c₁, c₂, c₃, c₄} : Finset H), ∃ x ∈ G.spiderNew c₁ c₂ c₃ c₄ e,
    G'.shade x = (G.shade i).swap ∧ G'.shade (G'.rev x) = G.shade i

end Plabic

end ClusterAlgebras
