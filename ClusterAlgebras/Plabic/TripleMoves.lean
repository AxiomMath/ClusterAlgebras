/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Swivel
public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.Rails

/-!
# Move equivalence, minimal intervals and rails along strand paths

This file collects four small pieces of D. Thurston's theory of minimal triple diagrams.

**Invariants of move equivalence.** An isomorphism of triple diagrams commutes with the strand
maps and carries the endpoints to the endpoints, so it preserves the strand permutation and the
number of triple points; so does a swivel move. Hence move-equivalent triple diagrams share these
invariants, and minimality is invariant under move equivalence.

**Normal form.** Every isomorphism in a sequence of moves can be pushed to the end: if `X ∼ X'`,
then `X'` is isomorphic to a diagram obtained from `X` by a sequence of swivel moves, each at a
digon of the diagram before it, all on the darts of `X`.

**Minimal intervals.** For a permutation `π` of `[1, b]` and `i ∈ [1, b]`, the two intervals of
`i` are the arcs of the circle `ℤ/2b` from the position `2i - 1` of the source `s_i` to the
position `2π(i)` of the target `t_{π(i)}`, and back. An interval is minimal if it contains both
ends `2j - 1`, `2π(j)` of no other `j`.

**Rails along a strand path.** A rail (aligned, closed aligned or staggered) runs along a simple
strand path `P` on the side `ζ` if its darts `ρ_{0,1}, ρ_{0,2}, …, ρ_{N,1}, ρ_{N,2}` are
consecutive entries of the `ζ` list of `P` and none of its points `y_j` lies on `P`.

## Main definitions

* `ClusterAlgebras.TripleData.SwivelStep`: `Y'` is the swivel move of `Y` at a digon of `Y`.
* `ClusterAlgebras.cyclicIcc`: the cyclic interval from `a` to `c` in `Fin n`.
* `ClusterAlgebras.IsIntervalOf`, `ClusterAlgebras.intervalInterior`,
  `ClusterAlgebras.IsMinimalInterval`, `ClusterAlgebras.TripleDiagram.IsMinimalInterval`: the
  intervals of `i`, their interior positions and minimal intervals.
* `ClusterAlgebras.TripleData.RailPoints.IsAlong`, `TripleData.AlignedRail.IsAlong`,
  `TripleData.ClosedAlignedRail.IsAlong`, `TripleData.StaggeredRail.IsAlong`: rails along a strand
  path.

## Main results

* `ClusterAlgebras.TripleDiagram.MoveEquivalent.strandPerm_eq`,
  `ClusterAlgebras.TripleDiagram.MoveEquivalent.card_internalVertices_eq`: move-equivalent triple
  diagrams have the same strand permutation and the same number of triple points.
* `ClusterAlgebras.TripleDiagram.IsMinimal.of_moveEquivalent`: minimality is invariant under move
  equivalence.
* `ClusterAlgebras.TripleDiagram.MoveEquivalent.exists_swivelSteps`: isomorphisms can be postponed;
  `TripleDiagram.moveEquivalent_iff_exists_swivelSteps` is the equivalence.

## Implementation notes

* **Number of arcs.** A triple diagram with `b` arcs is a term of `TripleDiagram b`, and move
  equivalence is a relation on `TripleDiagram b`; so move-equivalent triple diagrams have the same
  number of arcs by construction, and `MoveEquivalent.strandPerm_eq` and
  `MoveEquivalent.card_internalVertices_eq` state the other two invariants.
* **Sequences of swivel moves.** The sequence `X = X₀, X₁, …, X_r` of
  `MoveEquivalent.exists_swivelSteps` is the reflexive transitive closure
  `Relation.ReflTransGen TripleData.SwivelStep` from `X.data` to `X_r`; swivel moves keep the
  darts, so every `X_t` is a triple diagram on the darts of `X`
  (`TripleData.isTripleDiagram_of_reflTransGen_swivelStep`).
* **Positions.** The positions `ℤ/2b` are `Fin (2 * b)`, `0`-indexed as the endpoint labels: FWZ's
  position `2i - 1` of `s_i` is `sourceIndex i` and its position `2π(i)` is
  `targetIndex (π i)`, for the arc label `i : Fin b` (FWZ's `i + 1`). Going clockwise is
  increasing modulo `2b`, and the interval from `a` to `c` is `cyclicIcc a c`, the positions `p`
  with `p - a ≤ c - a` in `Fin (2 * b)`.
* **Permutations.** The intervals are defined for any map `π : Fin b → Fin b`; bijectivity is not
  used, and the strand permutation `TripleData.strandPerm` is such a map.
* **Rails.** All three kinds of rails record their points through `TripleData.RailPoints p q`
  (points `x₀, …, x_p` and `y₁, …, y_q`); being along a strand path is defined once on
  `RailPoints` and specialised to the three kinds (`N = p` is `r`, `n`, `r` respectively). The
  definition makes sense for every list of darts; FWZ apply it to simple strand paths.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Isomorphisms preserve the strand permutation and the triple points -/

namespace TripleData

namespace Iso

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {X : TripleData H b} {X' : TripleData H' b}

/-- An isomorphism maps boundary vertices to boundary vertices. -/
theorem isBoundaryVertex_map_iff (θ : X.Iso X') (v : Finset H) :
    X'.IsBoundaryVertex (v.map θ.toEquiv.toEmbedding) ↔ X.IsBoundaryVertex v := by
  constructor
  · rintro ⟨d', hd', hB⟩
    obtain ⟨d, hd, rfl⟩ := mem_map.1 hd'
    exact ⟨d, hd, (θ.mem_bdry_iff d).1 hB⟩
  · rintro ⟨d, hd, hB⟩
    exact ⟨θ.toEquiv d, mem_map_of_mem _ hd, (θ.mem_bdry_iff d).2 hB⟩

/-- The vertex of `θ d` is a boundary vertex exactly when the vertex of `d` is. -/
theorem isBoundaryVertex_vertexOf_iff (θ : X.Iso X') (d : H) :
    X'.IsBoundaryVertex (X'.vertexOf (θ.toEquiv d)) ↔ X.IsBoundaryVertex (X.vertexOf d) := by
  rw [← θ.map_vertexOf, θ.isBoundaryVertex_map_iff]

/-- The dart `θ d` runs to an endpoint exactly when `d` does. -/
theorem runsToEndpoint_iff (θ : X.Iso X') (d : H) :
    X'.RunsToEndpoint (θ.toEquiv d) ↔ X.RunsToEndpoint d := by
  unfold RunsToEndpoint
  rw [← θ.map_inv, θ.isBoundaryVertex_vertexOf_iff]

/-- An isomorphism intertwines the strand maps: `θ ∘ S = S' ∘ θ`. -/
theorem map_strandMap (θ : X.Iso X') (d : H) :
    θ.toEquiv (X.strandMap d) = X'.strandMap (θ.toEquiv d) := by
  by_cases h : X.RunsToEndpoint d
  · rw [X.strandMap_of_runsToEndpoint h,
      X'.strandMap_of_runsToEndpoint ((θ.runsToEndpoint_iff d).2 h), θ.map_inv]
  · rw [X.strandMap_of_not_runsToEndpoint h,
      X'.strandMap_of_not_runsToEndpoint (mt (θ.runsToEndpoint_iff d).1 h), θ.map_rot, θ.map_rot,
      θ.map_rot, θ.map_inv]

/-- An isomorphism of pre-triple diagrams maps the dart `n_r` of `ε(r)` outside `B` to the dart
`n'_r` of `ε'(r)` outside `B'`. -/
theorem map_endDart (θ : X.Iso X') (hX : X.IsPreTripleDiagram) (hX' : X'.IsPreTripleDiagram)
    (r : Fin (2 * b)) : θ.toEquiv (X.endDart r) = X'.endDart r := by
  have hmem : θ.toEquiv (X.endDart r) ∈ X'.vertexOf (X'.endDart r) := by
    have := θ.map_endpoint r
    rw [endpoint, endpoint] at this
    rw [← this]
    exact mem_map_of_mem _ (X.self_mem_vertexOf _)
  exact DiskMap.eq_of_notMem_bdry hX'.boundaryVertex_card
    (X'.vertexOf_mem_boundaryVertices.1 (hX'.endpoint_mem r)) hmem
    (X'.self_mem_vertexOf _) ((θ.mem_bdry_iff _).not.2 (hX.endDart_notMem_bdry r))
    (hX'.endDart_notMem_bdry r)

/-- An isomorphism of pre-triple diagrams maps the arc from `s_i` onto the arc from `s'_i`, dart by
dart. -/
theorem map_arcDart (θ : X.Iso X') (hX : X.IsPreTripleDiagram) (hX' : X'.IsPreTripleDiagram)
    (i : Fin b) (k : ℕ) : θ.toEquiv (X.arcDart i k) = X'.arcDart i k := by
  induction k with
  | zero => exact θ.map_endDart hX hX' _
  | succ k ih => rw [arcDart_succ, arcDart_succ, θ.map_strandMap, ih]

/-- Isomorphic pre-triple diagrams have the same last index along the arc from `s_i`. -/
theorem arcLastIndex_eq (θ : X.Iso X') (hX : X.IsPreTripleDiagram) (hX' : X'.IsPreTripleDiagram)
    (i : Fin b) : X'.arcLastIndex i = X.arcLastIndex i := by
  unfold arcLastIndex
  rw [Fintype.card_congr θ.toEquiv.symm]
  congr 1
  funext k
  rw [← θ.map_arcDart hX hX' i k]
  exact decide_eq_decide.2 (θ.runsToEndpoint_iff _)

/-- The target `t'_j` is the vertex of `θ d` exactly when `t_j` is the vertex of `d`. -/
theorem findTarget_vertexOf (θ : X.Iso X') (d : H) :
    X'.findTarget (X'.vertexOf (θ.toEquiv d)) = X.findTarget (X.vertexOf d) := by
  unfold findTarget
  congr 1
  funext j
  rw [← θ.map_vertexOf]
  exact decide_eq_decide.2 (by rw [target, ← θ.map_endpoint, map_inj]; rfl)

/-- An isomorphism of pre-triple diagrams preserves the strand permutation. -/
theorem strandPerm_eq (θ : X.Iso X') (hX : X.IsPreTripleDiagram) (hX' : X'.IsPreTripleDiagram) :
    X'.strandPerm = X.strandPerm := by
  funext i
  unfold strandPerm
  rw [θ.arcLastIndex_eq hX hX' i]
  rcases X.arcLastIndex i with _ | k
  · rfl
  · dsimp only
    rw [← θ.map_arcDart hX hX' i k, ← θ.map_inv, θ.findTarget_vertexOf]

/-- Isomorphic triple data have the same number of triple points. -/
theorem card_internalVertices_eq (θ : X.Iso X') :
    X'.internalVertices.card = X.internalVertices.card := by
  have hmap : X'.internalVertices = X.internalVertices.map
      ⟨fun v => v.map θ.toEquiv.toEmbedding, map_injective _⟩ := by
    ext w
    simp only [mem_map, DiskMap.mem_internalVertices, RotationSystem.mem_vertices,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨d', rfl⟩, hb⟩
      refine ⟨X.vertexOf (θ.toEquiv.symm d'), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
      · rwa [← θ.isBoundaryVertex_vertexOf_iff, Equiv.apply_symm_apply]
      · rw [θ.map_vertexOf, Equiv.apply_symm_apply]
    · rintro ⟨v, ⟨⟨d, rfl⟩, hb⟩, rfl⟩
      rw [θ.map_vertexOf]
      exact ⟨⟨_, rfl⟩, by rwa [θ.isBoundaryVertex_vertexOf_iff]⟩
  rw [hmap, card_map]

end Iso

/-! ### Swivel moves preserve the triple points -/

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {d₁ : H}

/-- The vertices of a disk map are its boundary vertices and its internal vertices. -/
private theorem card_boundaryVertices_add_card_internalVertices (M : DiskMap H) :
    M.boundaryVertices.card + M.internalVertices.card = M.vertices.card := by
  unfold DiskMap.boundaryVertices DiskMap.internalVertices
  exact card_filter_add_card_filter_not _

/-- **A swivel move preserves the number of triple points.** -/
theorem IsDigon.card_internalVertices_swivelMove (hX : X.IsPreTripleDiagram)
    (hd : X.IsDigon (X.faceOf d₁)) :
    (X.swivelMove d₁).internalVertices.card = X.internalVertices.card := by
  have h₁ := card_boundaryVertices_add_card_internalVertices X.toDiskMap
  have h₂ := card_boundaryVertices_add_card_internalVertices (X.swivelMove d₁).toDiskMap
  have hb := congrArg card (hd.boundaryVertices_swivelMove hX)
  have hv := hd.card_vertices_swivelMove hX
  omega

/-! ### Sequences of swivel moves -/

/-- `Y'` is **the swivel move of `Y` at a digon of `Y`**: `Y' = Y.swivelMove d₁` for a dart `d₁`
whose face `f(d₁)` is a digon of `Y`. -/
def SwivelStep (Y Y' : TripleData H b) : Prop :=
  ∃ d₁, Y.IsDigon (Y.faceOf d₁) ∧ Y' = Y.swivelMove d₁

/-- The swivel move of a triple diagram at a digon is a triple diagram. -/
theorem SwivelStep.isTripleDiagram {Y Y' : TripleData H b} (h : Y.SwivelStep Y')
    (hY : Y.IsTripleDiagram) : Y'.IsTripleDiagram := by
  obtain ⟨d₁, hd, rfl⟩ := h
  exact hd.isTripleDiagram_swivelMove hY

/-- Every diagram of a sequence of swivel moves starting at a triple diagram is a triple
diagram. -/
theorem isTripleDiagram_of_reflTransGen_swivelStep {Y Y' : TripleData H b}
    (h : Relation.ReflTransGen SwivelStep Y Y') (hY : Y.IsTripleDiagram) : Y'.IsTripleDiagram := by
  induction h with
  | refl => exact hY
  | tail _ hst ih => exact hst.isTripleDiagram ih

/-- An isomorphism `θ : Z → Y` of pre-triple diagrams transports a swivel move of `Z` at a digon
`f(d)` to the swivel move of `Y` at the digon `f(θ d)`. -/
private theorem swivelStep_of_iso {H' : Type*} [Fintype H'] [DecidableEq H'] {Y : TripleData H b}
    {Z : TripleData H' b} (hY : Y.IsPreTripleDiagram) (hZ : Z.IsPreTripleDiagram) (θ : Z.Iso Y)
    {d : H'} (hd : Z.IsDigon (Z.faceOf d)) :
    Y.SwivelStep (Y.swivelMove (θ.toEquiv d)) ∧
      (Z.swivelMove d).Isomorphic (Y.swivelMove (θ.toEquiv d)) :=
  ⟨⟨_, (θ.isDigon_faceOf_map hd).1, rfl⟩, ⟨θ.swivelMove hZ hY d⟩⟩

end TripleData

/-! ### Move equivalence -/

namespace TripleDiagram

variable {b : ℕ}

/-- Isomorphic triple diagrams have the same strand permutation. -/
theorem Isomorphic.strandPerm_eq {X X' : TripleDiagram b} (h : X.Isomorphic X') :
    X'.data.strandPerm = X.data.strandPerm :=
  h.elim fun θ => θ.strandPerm_eq X.isTripleDiagram.toIsPreTripleDiagram
    X'.isTripleDiagram.toIsPreTripleDiagram

/-- Isomorphic triple diagrams have the same number of triple points. -/
theorem Isomorphic.card_internalVertices_eq {X X' : TripleDiagram b} (h : X.Isomorphic X') :
    X'.data.internalVertices.card = X.data.internalVertices.card :=
  h.elim fun θ => θ.card_internalVertices_eq

/-- A swivel move preserves the strand permutation. -/
theorem IsSwivelMove.strandPerm_eq {X X' : TripleDiagram b} (h : X.IsSwivelMove X') :
    X'.data.strandPerm = X.data.strandPerm := by
  obtain ⟨d₁, hd, θ⟩ := h
  have hP := X.isTripleDiagram.toIsPreTripleDiagram
  rw [θ.elim fun θ => θ.strandPerm_eq (hd.isPreTripleDiagram_swivelMove hP)
    X'.isTripleDiagram.toIsPreTripleDiagram]
  exact hd.strandPerm_swivelMove hP

/-- A swivel move preserves the number of triple points. -/
theorem IsSwivelMove.card_internalVertices_eq {X X' : TripleDiagram b} (h : X.IsSwivelMove X') :
    X'.data.internalVertices.card = X.data.internalVertices.card := by
  obtain ⟨d₁, hd, θ⟩ := h
  rw [θ.elim fun θ => θ.card_internalVertices_eq]
  exact hd.card_internalVertices_swivelMove X.isTripleDiagram.toIsPreTripleDiagram

/-- **Move-equivalent triple diagrams share their invariants**, the strand permutation: if
`X ∼ X'`, then `π_{X'} = π_X`. (They have the same number `b` of arcs by construction.) -/
@[cluster_algebras "lem_move_equivalent_invariants"]
theorem MoveEquivalent.strandPerm_eq {X X' : TripleDiagram b} (h : X.MoveEquivalent X') :
    X'.data.strandPerm = X.data.strandPerm := by
  induction h with
  | rel Y Y' h => exact h.elim Isomorphic.strandPerm_eq IsSwivelMove.strandPerm_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- **Move-equivalent triple diagrams share their invariants**, the number of triple points: if
`X ∼ X'`, then `X` and `X'` have the same number of triple points. -/
@[cluster_algebras "lem_move_equivalent_invariants"]
theorem MoveEquivalent.card_internalVertices_eq {X X' : TripleDiagram b}
    (h : X.MoveEquivalent X') :
    X'.data.internalVertices.card = X.data.internalVertices.card := by
  induction h with
  | rel Y Y' h =>
    exact h.elim Isomorphic.card_internalVertices_eq IsSwivelMove.card_internalVertices_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- **Minimality is invariant under move equivalence**: if `X` is minimal and `X ∼ X'`, then
`X'` is minimal. -/
@[cluster_algebras "lem_minimal_move_invariant"]
theorem IsMinimal.of_moveEquivalent {X X' : TripleDiagram b} (hX : X.IsMinimal)
    (h : X.MoveEquivalent X') : X'.IsMinimal := by
  intro X'' hX''
  rw [h.card_internalVertices_eq]
  exact hX X'' (hX''.trans h.strandPerm_eq)

/-- Minimality is a property of move-equivalence classes. -/
theorem MoveEquivalent.isMinimal_iff {X X' : TripleDiagram b} (h : X.MoveEquivalent X') :
    X'.IsMinimal ↔ X.IsMinimal :=
  ⟨fun hX' => hX'.of_moveEquivalent h.symm, fun hX => hX.of_moveEquivalent h⟩

/-- A property invariant along each generating step is invariant along the equivalence relation
they generate. -/
private theorem iff_of_eqvGen {α : Type*} {r : α → α → Prop} {P : α → Prop}
    (hr : ∀ a c, r a c → (P a ↔ P c)) {a c : α} (h : Relation.EqvGen r a c) : P a ↔ P c := by
  induction h with
  | rel a c h => exact hr a c h
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A sequence of swivel moves from `X` followed by an isomorphism to `X'` gives `X ∼ X'`. -/
theorem MoveEquivalent.of_reflTransGen_swivelStep {X X' : TripleDiagram b}
    {Y : TripleData X.Dart b} (hY : Relation.ReflTransGen TripleData.SwivelStep X.data Y)
    (h : Y.Isomorphic X'.data) : X.MoveEquivalent X' := by
  have key : ∀ Y : TripleData X.Dart b, Relation.ReflTransGen TripleData.SwivelStep X.data Y →
      ∃ hYt : Y.IsTripleDiagram,
        X.MoveEquivalent { Dart := X.Dart, data := Y, isTripleDiagram := hYt } := by
    intro Y hY
    induction hY with
    | refl => exact ⟨X.isTripleDiagram, MoveEquivalent.refl X⟩
    | tail _ hst ih =>
      obtain ⟨hYt, hXY⟩ := ih
      obtain ⟨d₁, hd, rfl⟩ := hst
      exact ⟨hd.isTripleDiagram_swivelMove hYt,
        hXY.trans (MoveEquivalent.of_isSwivelMove ⟨d₁, hd, TripleData.Isomorphic.refl _⟩)⟩
  obtain ⟨hYt, hXY⟩ := key Y hY
  exact hXY.trans (MoveEquivalent.of_isomorphic (X' := X') h)

/-- **Isomorphisms can be postponed**: if `X ∼ X'`, there are triple diagrams `X = X₀, X₁, …, X_r`
such that `X_t` is the swivel move of `X_{t-1}` at a digon of `X_{t-1}` for every `t ∈ [1, r]`,
and `X_r` is isomorphic to `X'`. The sequence is a `Relation.ReflTransGen` chain of
`TripleData.SwivelStep` on the darts of `X`; its members are triple diagrams by
`TripleData.isTripleDiagram_of_reflTransGen_swivelStep`. -/
@[cluster_algebras "lem_move_normal_form"]
theorem MoveEquivalent.exists_swivelSteps {X X' : TripleDiagram b} (h : X.MoveEquivalent X') :
    ∃ Y : TripleData X.Dart b,
      Relation.ReflTransGen TripleData.SwivelStep X.data Y ∧ Y.Isomorphic X'.data := by
  let P : TripleDiagram b → Prop := fun Z => ∃ Y : TripleData X.Dart b,
    Relation.ReflTransGen TripleData.SwivelStep X.data Y ∧ Y.Isomorphic Z.data
  have hpre : ∀ {Y : TripleData X.Dart b},
      Relation.ReflTransGen TripleData.SwivelStep X.data Y → Y.IsPreTripleDiagram := fun hY =>
    (TripleData.isTripleDiagram_of_reflTransGen_swivelStep hY
      X.isTripleDiagram).toIsPreTripleDiagram
  have hstep : ∀ Z W : TripleDiagram b, (Z.Isomorphic W ∨ Z.IsSwivelMove W) → (P Z ↔ P W) := by
    rintro Z W (hZW | ⟨d, hd, hψ⟩)
    · exact ⟨fun ⟨Y, hY, hYZ⟩ => ⟨Y, hY, TripleData.Isomorphic.trans _ hYZ hZW⟩,
        fun ⟨Y, hY, hYW⟩ =>
          ⟨Y, hY, TripleData.Isomorphic.trans _ hYW (TripleData.Isomorphic.symm _ hZW)⟩⟩
    · obtain ⟨ψ⟩ := hψ
      have hZ := Z.isTripleDiagram.toIsPreTripleDiagram
      constructor
      · rintro ⟨Y, hY, ⟨θ⟩⟩
        obtain ⟨hst, ⟨χ⟩⟩ := TripleData.swivelStep_of_iso (hpre hY) hZ θ.symm hd
        exact ⟨_, hY.tail hst, ⟨χ.symm.trans ψ⟩⟩
      · rintro ⟨Y, hY, ⟨θ⟩⟩
        obtain ⟨hd', -, ⟨κ⟩⟩ := hd.swivelMove_swivelMove hZ
        obtain ⟨hst, ⟨χ⟩⟩ := TripleData.swivelStep_of_iso (hpre hY)
          (hd.isPreTripleDiagram_swivelMove hZ) (θ.trans ψ.symm).symm hd'
        exact ⟨_, hY.tail hst, ⟨χ.symm.trans κ⟩⟩
  exact (iff_of_eqvGen hstep h).1
    ⟨X.data, Relation.ReflTransGen.refl, TripleData.Isomorphic.refl _⟩

/-- Two triple diagrams are move-equivalent exactly when the second is isomorphic to a sequence of
swivel moves of the first. -/
theorem moveEquivalent_iff_exists_swivelSteps {X X' : TripleDiagram b} :
    X.MoveEquivalent X' ↔ ∃ Y : TripleData X.Dart b,
      Relation.ReflTransGen TripleData.SwivelStep X.data Y ∧ Y.Isomorphic X'.data :=
  ⟨MoveEquivalent.exists_swivelSteps,
    fun ⟨_, hY, h⟩ => MoveEquivalent.of_reflTransGen_swivelStep hY h⟩

end TripleDiagram

/-! ### Cyclic intervals -/

section CyclicInterval

variable {n : ℕ}

/-- The **cyclic interval** from `a` to `c` in `Fin n`, read as `ℤ/n`: the positions met when going
from `a` to `c` by increasing steps modulo `n`, both ends included, i.e. the `p` with
`p - a ≤ c - a`. -/
def cyclicIcc (a c : Fin n) : Finset (Fin n) := {p | p - a ≤ c - a}

/-- `p` lies in the cyclic interval from `a` to `c` iff `p - a ≤ c - a`. -/
theorem mem_cyclicIcc {a c p : Fin n} : p ∈ cyclicIcc a c ↔ p - a ≤ c - a := by
  simp [cyclicIcc]

/-- The value of a difference in `Fin n`. -/
private theorem val_sub_eq_ite (p a : Fin n) :
    ((p - a : Fin n) : ℕ) = if (a : ℕ) ≤ p then (p : ℕ) - a else n - a + p := by
  rw [Fin.val_sub]
  have := a.isLt
  have := p.isLt
  split_ifs with h
  · rw [show n - (a : ℕ) + p = (p - a) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- A cyclic interval contains its left end. -/
@[simp]
theorem left_mem_cyclicIcc (a c : Fin n) : a ∈ cyclicIcc a c := by
  rw [mem_cyclicIcc, Fin.le_def, val_sub_eq_ite, if_pos le_rfl, Nat.sub_self]
  exact Nat.zero_le _

/-- A cyclic interval contains its right end. -/
@[simp]
theorem right_mem_cyclicIcc (a c : Fin n) : c ∈ cyclicIcc a c := mem_cyclicIcc.2 le_rfl

/-- The cyclic interval from `a` to `c` has `(c - a) + 1` positions. -/
theorem card_cyclicIcc [NeZero n] (a c : Fin n) :
    (cyclicIcc a c).card = (c - a : Fin n).val + 1 := by
  have : cyclicIcc a c = (Iic (c - a)).map (Equiv.addRight a).toEmbedding := by
    ext p
    rw [mem_map_equiv, mem_cyclicIcc, mem_Iic]
    simp [sub_eq_add_neg]
  rw [this, card_map, Fin.card_Iic]

/-- Without wrapping around, a cyclic interval is an ordinary interval. -/
theorem cyclicIcc_of_le {a c : Fin n} (h : a ≤ c) : cyclicIcc a c = Icc a c := by
  ext p
  simp only [mem_cyclicIcc, mem_Icc, Fin.le_def, val_sub_eq_ite]
  rw [Fin.le_def] at h
  have := a.isLt
  have := c.isLt
  have := p.isLt
  split_ifs <;> omega

/-- The cyclic interval from `a` to `a` is `{a}`. -/
@[simp]
theorem cyclicIcc_self (a : Fin n) : cyclicIcc a a = {a} := by
  rw [cyclicIcc_of_le le_rfl, Icc_self]

/-- The two cyclic intervals between distinct positions cover the circle. -/
theorem cyclicIcc_union_cyclicIcc {a c : Fin n} (h : a ≠ c) :
    cyclicIcc a c ∪ cyclicIcc c a = univ := by
  ext p
  simp only [mem_union, mem_cyclicIcc, mem_univ, iff_true, Fin.le_def, val_sub_eq_ite]
  have := a.isLt
  have := c.isLt
  have := p.isLt
  rw [Ne, Fin.ext_iff] at h
  split_ifs <;> omega

/-- The two cyclic intervals between two positions meet in their ends. -/
theorem cyclicIcc_inter_cyclicIcc (a c : Fin n) : cyclicIcc a c ∩ cyclicIcc c a = {a, c} := by
  ext p
  simp only [mem_inter, mem_cyclicIcc, mem_insert, mem_singleton, Fin.le_def, val_sub_eq_ite,
    Fin.ext_iff]
  have := a.isLt
  have := c.isLt
  have := p.isLt
  split_ifs <;> omega

/-- The positions of a source and a target are an odd distance apart in both directions. -/
private theorem even_val_sub_add_one {b : ℕ} (i j : Fin b) :
    Even (((targetIndex j - sourceIndex i : Fin (2 * b)) : ℕ) + 1) ∧
      Even (((sourceIndex i - targetIndex j : Fin (2 * b)) : ℕ) + 1) := by
  simp only [val_sub_eq_ite, sourceIndex_val, targetIndex_val, Nat.even_iff]
  have := i.isLt
  have := j.isLt
  constructor <;> split_ifs <;> omega

end CyclicInterval

/-! ### Minimal intervals -/

section MinimalInterval

variable {b : ℕ}

/-- The **intervals of `i`** for a map `π : Fin b → Fin b`: the two cyclic intervals of
`Fin (2 * b)` running clockwise (increasing) from `sourceIndex i` to `targetIndex (π i)`, and from
`targetIndex (π i)` to `sourceIndex i`, both ends included. -/
@[cluster_algebras "def_minimal_interval"]
def IsIntervalOf (π : Fin b → Fin b) (i : Fin b) (I : Finset (Fin (2 * b))) : Prop :=
  I = cyclicIcc (sourceIndex i) (targetIndex (π i)) ∨
    I = cyclicIcc (targetIndex (π i)) (sourceIndex i)

/-- The **interior positions** of an interval `I` of `i`: the positions of `I` other than its ends
`sourceIndex i` and `targetIndex (π i)`. -/
@[cluster_algebras "def_minimal_interval"]
def intervalInterior (π : Fin b → Fin b) (i : Fin b) (I : Finset (Fin (2 * b))) :
    Finset (Fin (2 * b)) :=
  I \ {sourceIndex i, targetIndex (π i)}

/-- A **minimal interval** of `i` for `π`: an interval `I` of `i` such that there is no `j ≠ i`
with both `sourceIndex j` and `targetIndex (π j)` in `I`. -/
@[cluster_algebras "def_minimal_interval"]
def IsMinimalInterval (π : Fin b → Fin b) (i : Fin b) (I : Finset (Fin (2 * b))) : Prop :=
  IsIntervalOf π i I ∧ ∀ j, j ≠ i → ¬(sourceIndex j ∈ I ∧ targetIndex (π j) ∈ I)

namespace IsIntervalOf

variable {π : Fin b → Fin b} {i : Fin b} {I : Finset (Fin (2 * b))}

/-- The position `2i - 1` of `s_i` is an end of every interval of `i`. -/
theorem sourceIndex_mem (h : IsIntervalOf π i I) : sourceIndex i ∈ I := by
  rcases h with rfl | rfl
  · exact left_mem_cyclicIcc _ _
  · exact right_mem_cyclicIcc _ _

/-- The position `2π(i)` of `t_{π(i)}` is an end of every interval of `i`. -/
theorem targetIndex_mem (h : IsIntervalOf π i I) : targetIndex (π i) ∈ I := by
  rcases h with rfl | rfl
  · exact right_mem_cyclicIcc _ _
  · exact left_mem_cyclicIcc _ _

/-- An interval of `i` has two positions more than its interior. -/
theorem card_intervalInterior (h : IsIntervalOf π i I) :
    (intervalInterior π i I).card + 2 = I.card := by
  have hsub : ({sourceIndex i, targetIndex (π i)} : Finset (Fin (2 * b))) ⊆ I :=
    insert_subset_iff.2 ⟨h.sourceIndex_mem, singleton_subset_iff.2 h.targetIndex_mem⟩
  have hcard := card_le_card hsub
  rw [card_pair (sourceIndex_ne_targetIndex _ _)] at hcard
  rw [intervalInterior, card_sdiff_of_subset hsub, card_pair (sourceIndex_ne_targetIndex _ _)]
  omega

/-- An interval of `i` has an even number of interior positions. -/
theorem even_card_intervalInterior (h : IsIntervalOf π i I) :
    Even (intervalInterior π i I).card := by
  have hb : NeZero (2 * b) := ⟨by have := i.isLt; omega⟩
  have hc := h.card_intervalInterior
  have hI : Even I.card := by
    rcases h with rfl | rfl <;> rw [card_cyclicIcc]
    exacts [(even_val_sub_add_one i (π i)).1, (even_val_sub_add_one i (π i)).2]
  rw [← hc] at hI
  exact (Nat.even_add.1 hI).2 even_two

end IsIntervalOf

end MinimalInterval

namespace TripleDiagram

variable {b : ℕ}

/-- A **minimal interval of the triple diagram** `X`, of `i`: a minimal interval of `i` for the
strand permutation `π_X`. -/
@[cluster_algebras "def_minimal_interval"]
abbrev IsMinimalInterval (X : TripleDiagram b) (i : Fin b) (I : Finset (Fin (2 * b))) : Prop :=
  ClusterAlgebras.IsMinimalInterval X.data.strandPerm i I

/-- Move-equivalent triple diagrams have the same minimal intervals. -/
theorem MoveEquivalent.isMinimalInterval_iff {X X' : TripleDiagram b} (h : X.MoveEquivalent X')
    {i : Fin b} {I : Finset (Fin (2 * b))} :
    X'.IsMinimalInterval i I ↔ X.IsMinimalInterval i I := by
  simp only [IsMinimalInterval, h.strandPerm_eq]

end TripleDiagram

/-! ### Rails along a strand path -/

namespace TripleData

namespace RailPoints

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {p q : ℕ}
  (R : X.RailPoints p q)

/-- The darts `(ρ_{0,1}, ρ_{0,2}, ρ_{1,1}, ρ_{1,2}, …, ρ_{p,1}, ρ_{p,2})` of the points
`x₀, …, x_p` of a rail: the entry of index `k` is `ρ_{⌊k/2⌋, k mod 2 + 1}`. -/
def facingDarts : List H :=
  (List.range (2 * (p + 1))).map fun k => R.dart (RailLabel.rho (k / 2) (k % 2 + 1))

/-- A rail with points `x₀, …, x_p` has `2(p + 1)` facing darts. -/
@[simp]
theorem length_facingDarts : R.facingDarts.length = 2 * (p + 1) := by
  simp [facingDarts]

/-- The entry of index `2j` of the facing darts is `ρ_{j,1}`. -/
theorem getElem_facingDarts_two_mul {j : ℕ} (hj : j ≤ p) :
    R.facingDarts[2 * j]'(by simp; omega) = R.dart (RailLabel.rho j 1) := by
  simp only [facingDarts, List.getElem_map, List.getElem_range]
  congr 2 <;> omega

/-- The entry of index `2j + 1` of the facing darts is `ρ_{j,2}`. -/
theorem getElem_facingDarts_two_mul_add_one {j : ℕ} (hj : j ≤ p) :
    R.facingDarts[2 * j + 1]'(by simp; omega) = R.dart (RailLabel.rho j 2) := by
  simp only [facingDarts, List.getElem_map, List.getElem_range]
  congr 2 <;> omega

/-- A rail with points `x₀, …, x_p, y₁, …, y_q` is **along the strand path `P` on side `ζ`**:
`(ρ_{0,1}, ρ_{0,2}, …, ρ_{p,1}, ρ_{p,2})` is a sequence of consecutive entries of the `ζ` list of
`P`, and none of the points `y_j` is the vertex of a dart of `P` or of the reverse of one. -/
@[cluster_algebras "def_rail_along"]
def IsAlong (P : List H) (ζ : StrandSide) : Prop :=
  R.facingDarts <:+: X.sideList ζ P ∧
    ∀ j, 1 ≤ j → j ≤ q → ∀ e ∈ P,
      X.vertexOf (R.eta j) ≠ X.vertexOf e ∧ X.vertexOf (R.eta j) ≠ X.vertexOf (X.inv e)

end RailPoints

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b}

/-- An aligned rail of length `r` is **along the strand path `P` on side `ζ`** if
`(ρ_{0,1}, ρ_{0,2}, …, ρ_{r,1}, ρ_{r,2})` is a sequence of consecutive entries of the `ζ` list of
`P` and none of its points `y₁, …, y_r` is the vertex of a dart of `P` or of the reverse of one. -/
@[cluster_algebras "def_rail_along"]
abbrev AlignedRail.IsAlong {r : ℕ} (R : X.AlignedRail r) (P : List H) (ζ : StrandSide) : Prop :=
  R.toRailPoints.IsAlong P ζ

/-- A closed aligned rail of length `n` is **along the strand path `P` on side `ζ`** if
`(ρ_{0,1}, ρ_{0,2}, …, ρ_{n,1}, ρ_{n,2})` is a sequence of consecutive entries of the `ζ` list of
`P` and none of its points `y₁, …, y_{n-1}` is the vertex of a dart of `P` or of the reverse of
one. -/
@[cluster_algebras "def_rail_along"]
abbrev ClosedAlignedRail.IsAlong {n : ℕ} (R : X.ClosedAlignedRail n) (P : List H)
    (ζ : StrandSide) : Prop :=
  R.railPoints.IsAlong P ζ

/-- A staggered rail of length `r` is **along the strand path `P` on side `ζ`** if
`(ρ_{0,1}, ρ_{0,2}, …, ρ_{r,1}, ρ_{r,2})` is a sequence of consecutive entries of the `ζ` list of
`P` and none of its points `y₁, …, y_r` is the vertex of a dart of `P` or of the reverse of one. -/
@[cluster_algebras "def_rail_along"]
abbrev StaggeredRail.IsAlong {r : ℕ} (R : X.StaggeredRail r) (P : List H) (ζ : StrandSide) :
    Prop :=
  R.toRailPoints.IsAlong P ζ

end TripleData

end ClusterAlgebras
