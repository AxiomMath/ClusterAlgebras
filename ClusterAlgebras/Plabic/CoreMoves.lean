/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Core
public import ClusterAlgebras.Plabic.LocalMoves

/-!
# The core and the skeleton under local moves

The core `K(G)` of a plabic graph `G` is the largest core-like set of darts, and the skeleton
`Γ(G)` keeps the darts of the core at boundary vertices and at vertices with at least three core
darts, walking through the vertices with exactly two core darts. Deleting an internal leaf keeps
the core; removing a bivalent vertex `{d₁, d₂}` or contracting an edge `{d, d̄}` removes those two
darts from the core. Hence the local moves preserve anchoring.

Removing a bivalent vertex does not change the skeleton: the walks of the removal are those of
`G` with the terms `d₁`, `d₂` deleted. Neither does deleting an internal leaf. By induction on the
number of darts, the skeleton of an anchored plabic graph is a plabic graph: delete an internal
leaf or remove a bivalent vertex while there is one, and otherwise every internal vertex has at
least three darts and the graph is its own skeleton.

Contracting an edge `{d, d̄}` of an anchored graph changes the skeleton by at most one contraction.
If `d` is outside the core, the skeleton is unchanged. Otherwise let `p_K + 1` and `q_K + 1` be the
numbers of core darts at `v(d)` and `v(d̄)`: if `p_K, q_K ≥ 2` the skeleton of the contraction is
the contraction of the skeleton along `{d, d̄}`; if `p_K = 1 ≤ q_K - 1` the skeleton of the
contraction is isomorphic to `Γ(G)`, through the bijection exchanging `d̄` for the other core dart
of `v(d)` (and symmetrically); if `p_K = q_K = 1` the skeleton is unchanged. So a move (M2) or (M3)
changes the skeleton by at most a move (M3), and projecting a sequence of moves (M2) and (M3)
between graphs without small internal vertices onto skeletons shows that moves (M2) are not needed
between such graphs.

## Main definitions

* `ClusterAlgebras.PlabicGraph.skeleton`: the skeleton of an anchored plabic graph, bundled as a
  plabic graph.

## Main results

* `ClusterAlgebras.PlabicData.map_core_leafDeletion`: deleting an internal leaf keeps the core.
* `ClusterAlgebras.PlabicData.map_core_bivalentRemoval`: removing a bivalent vertex removes its
  darts from the core.
* `ClusterAlgebras.PlabicData.map_core_contractEdge`: contracting an edge removes its darts from
  the core.
* `ClusterAlgebras.PlabicGraph.MoveStep.isAnchored`: moves preserve anchoring.
* `ClusterAlgebras.PlabicData.exists_skeletonBivalentRemovalIso`: removing a bivalent vertex keeps
  the skeleton.
* `ClusterAlgebras.PlabicData.IsAnchored.isPlabicGraph_skeleton`: the skeleton of an anchored
  plabic graph is a plabic graph.
* `ClusterAlgebras.PlabicData.skeleton_contractEdge`: contracting an edge changes the skeleton by
  at most one contraction.
* `ClusterAlgebras.PlabicGraph.MoveStep.skeleton`: a move (M2) or (M3) changes the skeleton by at
  most a move (M3).
* `ClusterAlgebras.PlabicGraph.MoveEquivalent.exists_chain_m3`: moves (M2) are not needed between
  graphs without small internal vertices.
* `ClusterAlgebras.PlabicData.Iso.map_core`, `ClusterAlgebras.PlabicData.Isomorphic.skeleton`:
  isomorphisms preserve the core and the skeleton.

## Implementation notes

* The darts of the deletion of a leaf, of the removal of a bivalent vertex and of the contraction
  of an edge form a subtype of the darts `H` of `G`; their cores are compared with the core of `G`
  through the inclusion `Function.Embedding.subtype`. An equality `Γ(G') = Γ(G)` of skeletons on
  different sets of darts is stated as an isomorphism whose bijection of darts is the identity on
  the underlying darts of `H`.
* The walk `e₀ = d̄, e_{j+1} = \overline{σ_K(e_j)}` defining the involution of the skeleton is
  handled through its first term lying in `R`, characterised inductively; two walks are compared
  by induction on this characterisation, with the deleted terms handled by separate clauses.
* In `ClusterAlgebras.PlabicData.skeleton_contractEdge` the case where `v(d̄)` has exactly two
  core darts and `v(d)` at least three is reduced to the opposite case through the identification
  of the contractions along `d` and along `d̄`, which are the same tuple. In
  `ClusterAlgebras.PlabicGraph.MoveEquivalent.exists_chain_m3` the sequence
  `G = X₀, …, X_r = G'` is a chain of `Relation.ReflTransGen` of the relation "both graphs have no
  internal vertex with fewer than three darts and the second is isomorphic to the first or obtained
  from it by a move (M3)".

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

universe u

/-! ### First hits of an iteration -/

section FirstHit

variable {α : Type*}

/-- `FirstHit f p x z`: iterating `f` from `x` (included), the first element satisfying `p`
is `z`. -/
private inductive FirstHit (f : α → α) (p : α → Prop) : α → α → Prop
  | stop {x : α} : p x → FirstHit f p x x
  | step {x z : α} : ¬p x → FirstHit f p (f x) z → FirstHit f p x z

variable {f g : α → α} {p q : α → Prop}

private theorem FirstHit.prop {x z : α} (h : FirstHit f p x z) : p z := by
  induction h with
  | stop h => exact h
  | step _ _ ih => exact ih

private theorem firstHit_iff {x z : α} :
    FirstHit f p x z ↔ (p x ∧ x = z) ∨ (¬p x ∧ FirstHit f p (f x) z) := by
  constructor
  · intro h
    cases h with
    | stop h => exact Or.inl ⟨h, rfl⟩
    | step h h' => exact Or.inr ⟨h, h'⟩
  · rintro (⟨h, rfl⟩ | ⟨h, h'⟩)
    exacts [.stop h, .step h h']

private theorem FirstHit.unique {x z z' : α} (h : FirstHit f p x z) (h' : FirstHit f p x z') :
    z = z' := by
  induction h generalizing z' with
  | stop hx =>
    rcases firstHit_iff.1 h' with ⟨_, rfl⟩ | ⟨hn, _⟩
    · rfl
    · exact absurd hx hn
  | step hn _ ih =>
    rcases firstHit_iff.1 h' with ⟨hx, _⟩ | ⟨_, h''⟩
    · exact absurd hx hn
    · exact ih h''

/-- Transfer of a first hit along an invariant `I` on which `g` agrees with `f` at the elements
not satisfying `p`, none of which satisfies `q`. -/
private theorem FirstHit.transfer {x z : α} (I : α → Prop) (hI : ∀ w, I w → ¬p w → I (f w))
    (hfg : ∀ w, I w → ¬p w → g w = f w ∧ ¬q w) (hz : q z) (h : FirstHit f p x z) (hx : I x) :
    FirstHit g q x z := by
  induction h with
  | stop _ => exact .stop hz
  | step hn _ ih =>
    obtain ⟨h1, h2⟩ := hfg _ hx hn
    refine .step h2 ?_
    rw [h1]
    exact ih hz (hI _ hx hn)

private theorem FirstHit.map {β : Type*} {f' : β → β} {p' : β → Prop} (j : β → α)
    (hj : ∀ u, j (f' u) = f (j u)) (hp : ∀ u, p (j u) ↔ p' u) {x z : β}
    (h : FirstHit f' p' x z) : FirstHit f p (j x) (j z) := by
  induction h with
  | stop h => exact .stop ((hp _).2 h)
  | step hn _ ih =>
    refine .step (mt (hp _).1 hn) ?_
    rw [← hj]
    exact ih

private theorem FirstHit.trans {x y z : α} (h : FirstHit f p x y) (h' : FirstHit f q y z)
    (hqp : ∀ w, q w → p w) : FirstHit f q x z := by
  induction h with
  | stop _ => exact h'
  | step hn _ ih => exact .step (mt (hqp _) hn) (ih h')

private theorem FirstHit.sameCycle {π : Perm α} {x z : α} (h : FirstHit π p x z) :
    π.SameCycle x z := by
  induction h with
  | stop _ => exact SameCycle.refl _ _
  | step _ _ ih => exact (sameCycle_apply_right.2 (SameCycle.refl _ _)).trans ih

private theorem firstHit_of_iterate {x : α} {n : ℕ} (hn : p (f^[n] x))
    (hmin : ∀ j < n, ¬p (f^[j] x)) : FirstHit f p x (f^[n] x) := by
  induction n generalizing x with
  | zero => exact .stop hn
  | succ n ih =>
    refine .step (hmin 0 (Nat.succ_pos _)) ?_
    rw [iterate_succ_apply]
    refine ih (by rwa [← iterate_succ_apply]) fun j hj => ?_
    simpa only [iterate_succ_apply] using hmin (j + 1) (by omega)

private theorem exists_firstHit {x : α} (h : ∃ n, p (f^[n] x)) : ∃ z, FirstHit f p x z := by
  classical
  exact ⟨_, firstHit_of_iterate (Nat.find_spec h) fun j hj => Nat.find_min h hj⟩

/-- Along an orbit of a permutation of a finite set, every element of the orbit is hit. -/
private theorem firstHit_eq_of_sameCycle [Finite α] {π : Perm α} {x y : α} (h : π.SameCycle x y) :
    FirstHit π (· = y) x y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  obtain ⟨z, hz⟩ := exists_firstHit (f := π) (p := (· = y)) (x := x)
    ⟨n, by rwa [Perm.iterate_eq_pow]⟩
  exact hz.prop ▸ hz

variable {X : Type*} [Finite X]

private theorem firstHit_firstReturn (π : Perm X) (Y : Set X) (y : Y) :
    FirstHit π (· ∈ Y) (π y) (firstReturn π Y y) := by
  obtain ⟨n, hn⟩ : ∃ n, firstReturnTime π Y y = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (firstReturnTime_pos y)).symm⟩
  have key : ∀ j, π^[j] (π y) = (π ^ (j + 1)) y := fun j => by
    rw [← iterate_succ_apply, Perm.iterate_eq_pow]
  have h := firstHit_of_iterate (f := π) (p := (· ∈ Y)) (x := π y) (n := n)
    (by rw [key, ← hn]; exact pow_firstReturnTime_apply_mem y)
    (fun j hj => by
      rw [key]
      exact pow_apply_notMem_of_lt_firstReturnTime (by omega) (by omega))
  rwa [key, ← hn] at h

private theorem coe_firstReturn_eq_iff {π : Perm X} {Y : Set X} {y : Y} {z : X} :
    (firstReturn π Y y : X) = z ↔ FirstHit π (· ∈ Y) (π y) z :=
  ⟨fun h => h ▸ firstHit_firstReturn π Y y, fun h => (firstHit_firstReturn π Y y).unique h⟩

/-- The first return to `Z` of the first-return map to `Y ⊇ Z` is the first return to `Z`. -/
private theorem coe_firstReturn_firstReturnPerm (π : Perm X) {Y Z : Set X} (hZY : Z ⊆ Y)
    {Z' : Set Y} (hZ : ∀ u : Y, u ∈ Z' ↔ (u : X) ∈ Z) (u : Z') :
    ((firstReturn (firstReturnPerm π Y) Z' u : Y) : X) = firstReturn π Z ⟨u, (hZ u).1 u.2⟩ := by
  have claim : ∀ x z, FirstHit π (· ∈ Z) x z → ∀ v : Y, FirstHit π (· ∈ Y) x v →
      ∃ w : Y, (w : X) = z ∧ FirstHit (firstReturnPerm π Y) (· ∈ Z') v w := by
    intro x z h
    induction h with
    | @stop x hx =>
      intro v hv
      have hxv : x = v := (FirstHit.stop (hZY hx)).unique hv
      exact ⟨v, hxv.symm, .stop ((hZ v).2 (hxv ▸ hx))⟩
    | @step x z hn _ ih =>
      intro v hv
      rcases firstHit_iff.1 hv with ⟨_, hxv⟩ | ⟨_, hv'⟩
      · obtain ⟨w, hw, hw'⟩ := ih (firstReturn π Y v) (by
          rw [hxv]
          exact firstHit_firstReturn π Y v)
        exact ⟨w, hw, .step (fun h => hn (hxv ▸ (hZ v).1 h)) hw'⟩
      · exact ih v hv'
  obtain ⟨w, hw, hw'⟩ := claim _ _ (firstHit_firstReturn π Z ⟨u, (hZ u).1 u.2⟩) _
    (firstHit_firstReturn π Y u)
  rw [← hw]
  exact congrArg Subtype.val (coe_firstReturn_eq_iff.2 hw')

/-- A first return commutes with a map intertwining the permutations and the subsets. -/
private theorem coe_firstReturn_of_semiconj {X' : Type*} [Finite X'] {π : Perm X} {π' : Perm X'}
    (j : X' → X) (hj : ∀ u, j (π' u) = π (j u)) {A : Set X} {A' : Set X'}
    (hA : ∀ u, j u ∈ A ↔ u ∈ A') (y : A') :
    j (firstReturn π' A' y : X') = firstReturn π A ⟨j y, (hA y).2 y.2⟩ := by
  symm
  rw [coe_firstReturn_eq_iff]
  change FirstHit π (· ∈ A) (π (j y)) _
  rw [← hj]
  exact (firstHit_firstReturn π' A' y).map j hj hA

variable [DecidableEq X]

/-- The first return of `π ∘ (p q)` to a set containing `p` and `q` is the first return of `π`
after the transposition. -/
private theorem coe_firstReturn_mul_swap (π : Perm X) {Y : Set X} {p q : X} (hp : p ∈ Y)
    (hq : q ∈ Y) {y : X} (hy : y ∈ Y) (hy' : swap p q y ∈ Y) :
    (firstReturn (π * swap p q) Y ⟨y, hy⟩ : X) = firstReturn π Y ⟨swap p q y, hy'⟩ := by
  rw [coe_firstReturn_eq_iff, Perm.mul_apply]
  refine (firstHit_firstReturn π Y ⟨swap p q y, hy'⟩).transfer (fun _ => True)
    (fun _ _ _ => trivial) (fun w _ hw => ⟨?_, hw⟩) (firstHit_firstReturn _ _ _).prop trivial
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (fun h : w = p => hw (h ▸ hp))
    fun h : w = q => hw (h ▸ hq)]

/-- If the orbit of `p` under `π` avoids `Y` and does not contain `q ∉ Y`, then a first hit of `Y`
under `π` is a first hit of `Y` under `π ∘ (p q)`. -/
private theorem FirstHit.mul_swap {π : Perm X} {Y : Set X} {p q : X}
    (hp : ∀ w, π.SameCycle p w → w ∉ Y) (hq : q ∉ Y) (hpq : ¬π.SameCycle p q) {x z : X}
    (h : FirstHit π (· ∈ Y) x z) : FirstHit (π * swap p q) (· ∈ Y) x z := by
  have sub : ∀ w, π.SameCycle p w → FirstHit (π * swap p q) (· ∈ Y) (π q) z →
      FirstHit (π * swap p q) (· ∈ Y) w z := by
    intro w hw hq'
    obtain ⟨t, h1⟩ : ∃ t, FirstHit π (· = p) w t := ⟨p, firstHit_eq_of_sameCycle hw.symm⟩
    revert hw
    induction h1 with
    | stop hxp =>
      intro _
      subst hxp
      refine .step (hp _ (SameCycle.refl _ _)) ?_
      rwa [Perm.mul_apply, swap_apply_left]
    | @step w _ hn _ ih =>
      intro hw
      refine .step (hp w hw) ?_
      have hwq : w ≠ q := fun h => hpq (h ▸ hw)
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hn hwq]
      exact ih (hw.trans (sameCycle_apply_right.2 (SameCycle.refl _ _)))
  induction h with
  | stop h => exact .stop h
  | @step w z hn h' ih =>
    by_cases hwp : w = p
    · subst hwp
      exact absurd h'.prop
        (hp z ((sameCycle_apply_right.2 (SameCycle.refl _ _)).trans h'.sameCycle))
    by_cases hwq : w = q
    · subst hwq
      refine .step hn ?_
      rw [Perm.mul_apply, swap_apply_right]
      exact sub _ (sameCycle_apply_right.2 (SameCycle.refl _ _)) (ih sub)
    · refine .step hn ?_
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hwp hwq]
      exact ih sub

end FirstHit

/-! ### Isomorphisms built from a bijection of darts -/

namespace PlabicData

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

private theorem sameCycle_map_iff' {β γ : Type*} {f : Perm β} {g : Perm γ} (e : β ≃ γ)
    (h : ∀ x, e (f x) = g (e x)) {x y : β} : g.SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  have hc : e.permCongr f = g := by
    ext x
    simpa [Equiv.permCongr_apply] using h (e.symm x)
  have hpow : ∀ n : ℤ, ∀ x, e ((f ^ n) x) = (g ^ n) (e x) := by
    intro n x
    rw [← hc]
    have : (e.permCongr f) ^ n = e.permCongr (f ^ n) := by
      simpa using (map_zpow (Equiv.permCongrHom e).toMonoidHom f n).symm
    rw [this, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, e.injective (by rw [hpow, hn])⟩,
    fun ⟨n, hn⟩ => ⟨n, by rw [← hpow, hn]⟩⟩

private theorem map_vertexOf_of_semiconj' {G : PlabicData H b} {G' : PlabicData H' b} (e : H ≃ H')
    (h : ∀ x, e (G.rot x) = G'.rot (e x)) (d : H) :
    (G.vertexOf d).map e.toEmbedding = G'.vertexOf (e d) := by
  ext y
  rw [mem_map_equiv, RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf,
    ← sameCycle_map_iff' e h, Equiv.apply_symm_apply]

/-- An isomorphism from a bijection of darts commuting with the involutions and the rotations,
matching `B` with `B'` and the colours of internal vertices, and mapping `leg i` to `leg' i`. -/
private def isoOfMapLeg {G : PlabicData H b} {G' : PlabicData H' b} (e : H ≃ H')
    (map_inv : ∀ d, e (G.inv d) = G'.inv (e d)) (map_rot : ∀ d, e (G.rot d) = G'.rot (e d))
    (mem_bdry_iff : ∀ d, e d ∈ G'.bdry ↔ d ∈ G.bdry)
    (map_colour : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G'.colour (e d) = G.colour d)
    (map_leg : ∀ i, e (G.leg i) = G'.leg i) : G.Iso G' where
  toEquiv := e
  map_inv := map_inv
  map_rot := map_rot
  mem_bdry_iff := mem_bdry_iff
  map_colour := map_colour
  map_bvertex i := by
    rw [bvertex, bvertex, ← map_leg, ← map_vertexOf_of_semiconj' e map_rot]
    ext y
    simp only [mem_map_equiv, mem_filter]
    rw [← mem_bdry_iff (e.symm y), Equiv.apply_symm_apply]

namespace Iso

variable {G : PlabicData H b} {G' : PlabicData H' b}

private theorem card_image_univ_eq_of_equiv (e : H ≃ H') {f : H → Finset H}
    {f' : H' → Finset H'}
    (h : ∀ d, (f d).map e.toEmbedding = f' (e d)) :
    (univ.image f).card = (univ.image f').card := by
  have key : (univ.image f).image (fun v => v.map e.toEmbedding) = univ.image f' := by
    ext v'
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨d, rfl⟩, rfl⟩
      exact ⟨e d, (h d).symm⟩
    · rintro ⟨d', rfl⟩
      exact ⟨_, ⟨e.symm d', rfl⟩, by rw [h, Equiv.apply_symm_apply]⟩
  rw [← key, card_image_of_injective _ (map_injective _)]

-- Isomorphic tuples have the same number of vertices.
private theorem card_vertices_of_iso (θ : G.Iso G') : G.vertices.card = G'.vertices.card :=
  card_image_univ_eq_of_equiv θ.toEquiv θ.map_vertexOf

-- An isomorphism maps each edge `{d, d̄}` onto the edge `{θ d, θ d̄}`.
private theorem map_edgeOf_of_iso (θ : G.Iso G') (d : H) :
    (G.edgeOf d).map θ.toEquiv.toEmbedding = G'.edgeOf (θ.toEquiv d) := by
  simp [RotationSystem.edgeOf, θ.map_inv]

-- Isomorphic tuples have the same number of edges.
private theorem card_edges_of_iso (θ : G.Iso G') : G.edges.card = G'.edges.card :=
  card_image_univ_eq_of_equiv θ.toEquiv θ.map_edgeOf_of_iso

-- Isomorphic tuples have the same number of orbits of the face permutation.
private theorem card_faceOrbits_of_iso (θ : G.Iso G') :
    G.faceOrbits.card = G'.faceOrbits.card :=
  card_image_univ_eq_of_equiv θ.toEquiv θ.map_faceOf

-- An isomorphism maps boundary vertices to boundary vertices, and only those.
private theorem map_mem_boundaryVertices_iff_of_iso (θ : G.Iso G') {v : Finset H} :
    v.map θ.toEquiv.toEmbedding ∈ G'.boundaryVertices ↔ v ∈ G.boundaryVertices := by
  rw [DiskMap.mem_boundaryVertices, DiskMap.mem_boundaryVertices, RotationSystem.mem_vertices,
    RotationSystem.mem_vertices]
  have hb : G'.IsBoundaryVertex (v.map θ.toEquiv.toEmbedding) ↔ G.IsBoundaryVertex v := by
    simp only [DiskMap.IsBoundaryVertex, mem_map_equiv]
    constructor
    · rintro ⟨d, hd, hdB⟩
      exact ⟨_, hd, by rwa [← θ.mem_bdry_iff, Equiv.apply_symm_apply]⟩
    · rintro ⟨d, hd, hdB⟩
      exact ⟨θ.toEquiv d, by simpa using hd, (θ.mem_bdry_iff d).2 hdB⟩
  rw [hb]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨d', hd'⟩
    refine ⟨θ.toEquiv.symm d', map_injective θ.toEquiv.toEmbedding ?_⟩
    rw [θ.map_vertexOf, Equiv.apply_symm_apply, hd']
  · rintro ⟨d, rfl⟩
    exact ⟨θ.toEquiv d, (θ.map_vertexOf d).symm⟩

private theorem map_map_inv_of_iso (θ : G.Iso G') (t : Finset H) :
    (t.map G.inv.toEmbedding).map θ.toEquiv.toEmbedding =
      (t.map θ.toEquiv.toEmbedding).map G'.inv.toEmbedding := by
  rw [map_map, map_map]
  congr 1
  ext x
  simp [θ.map_inv]

end Iso

/-- Plabic graphs are transported along isomorphisms: if `G` is isomorphic to a plabic graph
and its chosen darts `leg i` lie outside `B`, then `G` is a plabic graph. -/
private theorem isPlabicGraph_of_iso {G : PlabicData H b} {G' : PlabicData H' b} (θ : G.Iso G')
    (hG' : G'.IsPlabicGraph) (hleg : ∀ i, G.leg i ∉ G.bdry) : G.IsPlabicGraph := by
  have hθleg : ∀ i, θ.toEquiv (G.leg i) = G'.leg i := by
    intro i
    have h := θ.map_bvertex i
    rw [hG'.filter_bvertex_notMem_bdry] at h
    have hm : θ.toEquiv (G.leg i) ∈
        ((G.bvertex i).filter (· ∉ G.bdry)).map θ.toEquiv.toEmbedding :=
      mem_map_of_mem _ (mem_filter.2 ⟨G.leg_mem_bvertex i, hleg i⟩)
    rw [h] at hm
    exact mem_singleton.1 hm
  have hbv : ∀ i, (G.bvertex i).map θ.toEquiv.toEmbedding = G'.bvertex i := fun i => by
    rw [bvertex, θ.map_vertexOf, hθleg]
    rfl
  have hinv : Involutive G.inv := fun d =>
    θ.toEquiv.injective (by rw [θ.map_inv, θ.map_inv, hG'.inv_involutive])
  have hreach : ∀ {x' y' : H'}, G'.Reach x' y' →
      G.Reach (θ.toEquiv.symm x') (θ.toEquiv.symm y') := by
    intro x' y' h
    induction h with
    | refl => exact RotationSystem.Reach.refl _
    | rot _ ih => rw [θ.symm_map_rot]; exact ih.rot
    | inv _ ih => rw [θ.symm_map_inv]; exact ih.inv
  refine
    { toIsDiskMap :=
        { toIsConnected := RotationSystem.IsConnected.of_reach
            (hG'.nonempty.map θ.toEquiv.symm) hinv
            (fun d h => hG'.inv_ne (θ.toEquiv d) (by rw [← θ.map_inv, h]))
            (fun d e => by
              simpa using hreach (hG'.toIsConnected.reach (θ.toEquiv d) (θ.toEquiv e)))
          inv_mem_bdry := fun d hd => by
            rw [← θ.mem_bdry_iff, θ.map_inv]
            exact hG'.inv_mem_bdry _ ((θ.mem_bdry_iff d).2 hd)
          euler := by
            have h := hG'.euler
            rwa [← θ.card_vertices_of_iso, ← θ.card_edges_of_iso, ← θ.card_faceOrbits_of_iso]
              at h
          boundaryVertex_card := ?_
          exists_orbit := ?_ }
      one_le := hG'.one_le
      colour_rot := ?_
      leg_notMem_bdry := hleg
      bvertex_mem := fun i => θ.map_mem_boundaryVertices_iff_of_iso.1 (by
        rw [hbv]
        exact hG'.bvertex_mem i)
      bvertex_injective := fun i j h => hG'.bvertex_injective (by rw [← hbv, ← hbv, h])
      exists_bvertex_eq := ?_
      exists_exterior := ?_ }
  · intro v hv
    obtain ⟨h1, h2⟩ := hG'.boundaryVertex_card _ (θ.map_mem_boundaryVertices_iff_of_iso.2 hv)
    rw [card_map] at h1
    refine ⟨h1, ?_⟩
    rw [filter_map, card_map] at h2
    rw [← h2]
    congr 1
    exact filter_congr fun x _ => by simp [θ.mem_bdry_iff]
  · obtain ⟨f', hf', hsub, hunion, hdisj⟩ := hG'.exists_orbit
    have hf : (f'.map θ.toEquiv.symm.toEmbedding).map θ.toEquiv.toEmbedding = f' := by
      ext y
      simp
    refine ⟨f'.map θ.toEquiv.symm.toEmbedding, ?_, ?_, ?_, ?_⟩
    · rw [← θ.map_mem_faceOrbits_iff, hf]
      exact hf'
    · intro x hx
      have : θ.toEquiv x ∈ f' := by
        rw [← hf]
        exact mem_map_of_mem _ hx
      exact (θ.mem_bdry_iff x).1 (hsub this)
    · apply map_injective θ.toEquiv.toEmbedding
      rw [map_union, Iso.map_map_inv_of_iso, hf, hunion, θ.map_bdry]
    · rw [← disjoint_map θ.toEquiv.toEmbedding, Iso.map_map_inv_of_iso, hf]
      exact hdisj
  · intro d hd
    have hd' : ¬G'.IsBoundaryVertex (G'.vertexOf (θ.toEquiv d)) := by
      rwa [θ.isBoundaryVertex_vertexOf_iff]
    have hrd : ¬G.IsBoundaryVertex (G.vertexOf (G.rot d)) := by
      rwa [G.vertexOf_rot]
    rw [← θ.map_colour _ hrd, θ.map_rot, hG'.colour_rot _ hd', θ.map_colour _ hd]
  · intro v hv
    obtain ⟨i, hi⟩ := hG'.exists_bvertex_eq _ (θ.map_mem_boundaryVertices_iff_of_iso.2 hv)
    exact ⟨i, map_injective θ.toEquiv.toEmbedding (by rw [hbv, hi])⟩
  · intro i
    obtain ⟨d', hd', h1, h2⟩ := hG'.exists_exterior i
    refine ⟨θ.toEquiv.symm d', ?_, ?_, ?_⟩
    · rw [← θ.map_exterior, mem_map_equiv] at hd'
      exact hd'
    · rw [← hbv, mem_map_equiv] at h1
      exact h1
    · rw [← hbv, mem_map_equiv, θ.symm_map_inv] at h2
      exact h2

/-! ### The core under isomorphisms -/

namespace Iso

variable {G : PlabicData H b} {G' : PlabicData H' b}

/-- An isomorphism maps core-like sets to core-like sets. -/
theorem isCoreLike_map (θ : G.Iso G') {S : Finset H} (hS : G.IsCoreLike S) :
    G'.IsCoreLike (S.map θ.toEquiv.toEmbedding) where
  bdry_subset x hx := by
    rw [mem_map_equiv]
    exact hS.bdry_subset ((θ.mem_bdry_iff _).1 (by rwa [Equiv.apply_symm_apply]))
  inv_mem x hx := by
    obtain ⟨s, hs, rfl⟩ := mem_map.1 hx
    rw [Equiv.coe_toEmbedding, ← θ.map_inv]
    exact mem_map_of_mem _ (hS.inv_mem s hs)
  two_le_card v hv := by
    rintro ⟨x, hxv, hxS⟩
    obtain ⟨s, hs, rfl⟩ := mem_map.1 hxS
    obtain ⟨y, rfl⟩ := G'.mem_vertices.1 hv
    rw [← G'.vertexOf_eq_of_mem hxv, Equiv.coe_toEmbedding, ← θ.map_vertexOf, ← map_inter,
      card_map]
    exact hS.two_le_card_vertexOf hs

private theorem apply_mem_core_of_mem (θ : G.Iso G') {x : H} (hx : x ∈ G.core) :
    θ.toEquiv x ∈ G'.core := by
  obtain ⟨S, hS, hxS⟩ := DiskMap.mem_core.1 hx
  exact (θ.isCoreLike_map hS).subset_core (mem_map_of_mem _ hxS)

/-- An isomorphism maps a dart into the core iff the dart lies in the core. -/
theorem apply_mem_core_iff (θ : G.Iso G') {x : H} : θ.toEquiv x ∈ G'.core ↔ x ∈ G.core := by
  refine ⟨fun h => ?_, apply_mem_core_of_mem θ⟩
  have := apply_mem_core_of_mem θ.symm h
  rwa [show θ.symm.toEquiv (θ.toEquiv x) = x from θ.toEquiv.symm_apply_apply x] at this

/-- An isomorphism maps the core onto the core. -/
theorem map_core (θ : G.Iso G') : G.core.map θ.toEquiv.toEmbedding = G'.core := by
  ext y
  rw [mem_map_equiv, ← θ.apply_mem_core_iff, Equiv.apply_symm_apply]

/-- Anchoring is invariant under isomorphisms of plabic graphs. -/
theorem isAnchored_iff (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (θ : G.Iso G') :
    G.IsAnchored ↔ G'.IsAnchored := by
  simp only [IsAnchored, ← θ.map_leg hG hG', θ.apply_mem_core_iff]

end Iso

/-! ### The core under deleting a leaf, removing a bivalent vertex and contracting an edge -/

variable {G : PlabicData H b}

/-- The dart of an internal leaf is not in the core. -/
theorem notMem_core_of_isInternalLeaf {ℓ : H} (hu : G.IsInternalLeaf (G.vertexOf ℓ)) :
    ℓ ∉ G.core := by
  intro h
  have h2 := DiskMap.two_le_card_vertexOf_inter_core h
  have h1 : #(G.vertexOf ℓ ∩ G.core) ≤ #(G.vertexOf ℓ) := card_le_card inter_subset_left
  rw [hu.2] at h1
  omega

section LeafDeletion

variable {ℓ : H} (hG : G.IsPlabicGraph) (hu : G.IsInternalLeaf (G.vertexOf ℓ))
  (hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices)

include hG hu in
/-- The reverse `ℓ̄` of the dart of an internal leaf is not in the core. -/
theorem inv_notMem_core_of_isInternalLeaf : G.inv ℓ ∉ G.core := fun h =>
  notMem_core_of_isInternalLeaf hu (by simpa [hG.inv_involutive ℓ] using DiskMap.inv_mem_core h)

include hG hu in
private theorem mem_compl_pair_of_mem_core {x : H} (hx : x ∈ G.core) :
    x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) :=
  mem_compl_pair_iff.2 ⟨fun h => notMem_core_of_isInternalLeaf hu (h ▸ hx),
    fun h => inv_notMem_core_of_isInternalLeaf hG hu (h ▸ hx)⟩

include hG hu hv in
/-- If `u = v(ℓ)` is an internal leaf of the plabic graph `G` and `v(ℓ̄)` is internal, the core of
the deletion of `u`, read in `H`, is the core `K(G)`. -/
@[cluster_algebras "lem_leaf_deletion_core"]
theorem map_core_leafDeletion :
    (G.leafDeletion hG hu hv).core.map (Embedding.subtype _) = G.core := by
  set Gl := G.leafDeletion hG hu hv
  have hGl : Gl.IsPlabicGraph := isPlabicGraph_leafDeletion hG hu hv
  have hY : ∀ x ∈ G.core, x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) :=
    fun x hx => mem_compl_pair_of_mem_core hG hu hx
  -- `K(G)` is core-like in the deletion.
  have h1 : Gl.IsCoreLike (G.core.subtype (· ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H))) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun v hv' => ?_⟩
    · rw [mem_subtype]
      exact hG.bdry_subset_core ((mem_leafDeletion_bdry hG hu hv).1 hx)
    · rw [mem_subtype] at hx ⊢
      rw [coe_leafDeletion_inv]
      exact DiskMap.inv_mem_core hx
    · rintro ⟨y, hyv, hyS⟩
      obtain ⟨z, rfl⟩ := Gl.mem_vertices.1 hv'
      rw [← Gl.vertexOf_eq_of_mem hyv, ← card_map (Embedding.subtype _), map_inter,
        map_vertexOf_leafDeletion hG hu hv, subtype_map_of_mem hY, erase_inter,
        erase_eq_of_notMem fun h => inv_notMem_core_of_isInternalLeaf hG hu (mem_inter.1 h).2]
      exact DiskMap.two_le_card_vertexOf_inter_core (mem_subtype.1 hyS)
  -- `K(G^l)` is core-like in `G`.
  have h2 : G.IsCoreLike (Gl.core.map (Embedding.subtype _)) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun v hv' => ?_⟩
    · exact mem_map.2 ⟨⟨x, mem_compl_pair_of_mem_bdry hu hv hx⟩,
        hGl.bdry_subset_core ((mem_leafDeletion_bdry hG hu hv).2 hx), rfl⟩
    · obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
      exact mem_map.2 ⟨Gl.inv y, DiskMap.inv_mem_core hy, coe_leafDeletion_inv hG hu hv y⟩
    · rintro ⟨z, hzv, hzS⟩
      obtain ⟨y, hy, rfl⟩ := mem_map.1 hzS
      obtain ⟨w, rfl⟩ := G.mem_vertices.1 hv'
      rw [← G.vertexOf_eq_of_mem hzv]
      refine (DiskMap.two_le_card_vertexOf_inter_core hy).trans
        ((card_map (Embedding.subtype _)).symm.le.trans (card_le_card fun e he => ?_))
      rw [map_inter, map_vertexOf_leafDeletion hG hu hv] at he
      exact mem_inter.2 ⟨mem_of_mem_erase (mem_inter.1 he).1, (mem_inter.1 he).2⟩
  refine Subset.antisymm h2.subset_core fun x hx => ?_
  exact mem_map.2 ⟨⟨x, hY x hx⟩, h1.subset_core (mem_subtype.2 hx), rfl⟩

end LeafDeletion

section BivalentRemoval

variable {d : H} (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d)

include hd in
private theorem rot_mem_core_of_mem_core (h : d ∈ G.core) : G.rot d ∈ G.core := by
  by_contra h'
  have h2 := DiskMap.two_le_card_vertexOf_inter_core h
  have hsub : G.vertexOf d ∩ G.core ⊆ {d} := by
    intro e he
    rcases hd.mem_vertexOf_iff.1 (mem_inter.1 he).1 with h | h
    · rw [h]; exact mem_singleton_self _
    · exact absurd (h ▸ (mem_inter.1 he).2) h'
  have := card_le_card hsub
  rw [card_singleton] at this
  omega

include hd in
private theorem mem_core_of_rot_mem_core (h : G.rot d ∈ G.core) : d ∈ G.core := by
  by_contra h'
  have h2 := DiskMap.two_le_card_vertexOf_inter_core h
  rw [G.vertexOf_rot] at h2
  have hsub : G.vertexOf d ∩ G.core ⊆ {G.rot d} := by
    intro e he
    rcases hd.mem_vertexOf_iff.1 (mem_inter.1 he).1 with h | h
    · exact absurd (h ▸ (mem_inter.1 he).2) h'
    · rw [h]; exact mem_singleton_self _
  have := card_le_card hsub
  rw [card_singleton] at this
  omega

omit [Fintype H] [DecidableEq H] in
private theorem mem_compl_pair_rot_iff {x : H} :
    x ∈ ({d, G.rot d}ᶜ : Set H) ↔ x ≠ d ∧ x ≠ G.rot d := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

include hG hd in
/-- The core of the removal of the bivalent vertex `{d₁, d₂}` (with `d₁ = d`, `d₂ = σ d`), read in
`H`, is `K(G) \ {d₁, d₂}`. -/
@[cluster_algebras "lem_bivalent_removal_core"]
theorem map_core_bivalentRemoval :
    (G.bivalentRemoval hG hd).core.map (Embedding.subtype _) = G.core \ {d, G.rot d} := by
  set Gr := G.bivalentRemoval hG hd
  have hGr : Gr.IsPlabicGraph := isPlabicGraph_bivalentRemoval hG hd
  have hinv := hG.inv_involutive
  -- `K(G) \ {d₁, d₂}` is core-like in the removal.
  have h1 : Gr.IsCoreLike (G.core.subtype (· ∈ ({d, G.rot d}ᶜ : Set H))) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun v hv' => ?_⟩
    · rw [mem_subtype]
      exact hG.bdry_subset_core ((mem_bivalentRemoval_bdry hG hd).1 hx)
    · rw [mem_subtype] at hx ⊢
      by_cases h₁ : (x : H) = G.inv d
      · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁]
        refine DiskMap.inv_mem_core (rot_mem_core_of_mem_core hd ?_)
        have := DiskMap.inv_mem_core hx
        rwa [h₁, hinv] at this
      by_cases h₂ : (x : H) = G.inv (G.rot d)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂]
        refine DiskMap.inv_mem_core (mem_core_of_rot_mem_core hd ?_)
        have := DiskMap.inv_mem_core hx
        rwa [h₂, hinv] at this
      · rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]
        exact DiskMap.inv_mem_core hx
    · rintro ⟨y, hyv, hyS⟩
      obtain ⟨z, rfl⟩ := Gr.mem_vertices.1 hv'
      rw [← Gr.vertexOf_eq_of_mem hyv, ← card_map (Embedding.subtype _), map_inter,
        map_bivalentRemoval_vertexOf hG hd, subtype_map]
      refine (DiskMap.two_le_card_vertexOf_inter_core (mem_subtype.1 hyS)).trans
        (card_le_card fun e he => ?_)
      obtain ⟨he1, he2⟩ := mem_inter.1 he
      exact mem_inter.2 ⟨he1, mem_filter.2 ⟨he2,
        mem_of_sameCycle_rot_bivalentRemoval hd y.2 (G.mem_vertexOf.1 he1)⟩⟩
  -- `K(G^r)`, together with `{d₁, d₂}` when `d̄₁ ∈ K(G^r)`, is core-like in `G`.
  set S2 := Gr.core.map (Embedding.subtype _) ∪
    (if (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ Gr.core then {d, G.rot d}
      else ∅) with hS2
  have hY : ∀ x ∈ Gr.core.map (Embedding.subtype _), x ≠ d ∧ x ≠ G.rot d := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    exact mem_compl_pair_rot_iff.1 y.2
  have h2 : G.IsCoreLike S2 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun v hv' => ?_⟩
    · exact mem_union_left _ (mem_map.2 ⟨⟨x, hd.mem_of_mem_bdry hx⟩,
        hGr.bdry_subset_core ((mem_bivalentRemoval_bdry hG hd).2 hx), rfl⟩)
    · rcases mem_union.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
        by_cases h₁ : (y : H) = G.inv d
        · have hc : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ Gr.core := by
            rwa [show (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) = y from
              Subtype.ext h₁.symm]
          refine mem_union_right _ ?_
          rw [if_pos hc, Embedding.coe_subtype, h₁, hinv]
          exact mem_insert_self _ _
        by_cases h₂ : (y : H) = G.inv (G.rot d)
        · have hc : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ Gr.core := by
            rw [show (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) = Gr.inv y from
              Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂).symm]
            exact DiskMap.inv_mem_core hy
          refine mem_union_right _ ?_
          rw [if_pos hc, Embedding.coe_subtype, h₂, hinv]
          exact mem_insert_of_mem (mem_singleton_self _)
        · exact mem_union_left _ (mem_map.2 ⟨Gr.inv y, DiskMap.inv_mem_core hy,
            coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂⟩)
      · by_cases hc : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ Gr.core
        · rw [if_pos hc] at hx
          refine mem_union_left _ ?_
          rcases mem_insert.1 hx with h | h
          · rw [h]
            exact mem_map.2 ⟨_, hc, rfl⟩
          · rw [mem_singleton.1 h]
            exact mem_map.2 ⟨_, DiskMap.inv_mem_core hc,
              coe_bivalentRemoval_inv_of_eq_inv hG hd rfl⟩
        · rw [if_neg hc] at hx
          simp at hx
    · rintro ⟨z, hzv, hzS⟩
      obtain ⟨w, rfl⟩ := G.mem_vertices.1 hv'
      rw [← G.vertexOf_eq_of_mem hzv]
      by_cases hzY : z ∈ ({d, G.rot d}ᶜ : Set H)
      · rcases mem_union.1 hzS with hz | hz
        · obtain ⟨y, hy, rfl⟩ := mem_map.1 hz
          have hsub : (Gr.vertexOf y ∩ Gr.core).map (Embedding.subtype _) ⊆
              G.vertexOf (y : H) ∩ S2 := by
            rw [map_inter, map_bivalentRemoval_vertexOf hG hd]
            exact inter_subset_inter_left subset_union_left
          exact (DiskMap.two_le_card_vertexOf_inter_core hy).trans
            ((card_map _).symm.le.trans (card_le_card hsub))
        · exfalso
          have hzY' := mem_compl_pair_rot_iff.1 hzY
          split_ifs at hz with hc
          · rcases mem_insert.1 hz with h | h
            · exact hzY'.1 h
            · exact hzY'.2 (mem_singleton.1 h)
          · simp at hz
      · have hz' : z = d ∨ z = G.rot d := by
          by_contra h
          rw [not_or] at h
          exact hzY (mem_compl_pair_rot_iff.2 h)
        have hc : (⟨G.inv d, hd.inv_mem hG⟩ : ({d, G.rot d}ᶜ : Set H)) ∈ Gr.core := by
          by_contra hc
          rcases mem_union.1 hzS with hz | hz
          · rcases hz' with h | h
            exacts [(hY _ hz).1 h, (hY _ hz).2 h]
          · rw [if_neg hc] at hz
            simp at hz
        have hvd : G.vertexOf z = G.vertexOf d := by
          rcases hz' with h | h
          · rw [h]
          · rw [h, G.vertexOf_rot]
        rw [hvd]
        have hsub : ({d, G.rot d} : Finset H) ⊆ G.vertexOf d ∩ S2 := by
          intro e he
          refine mem_inter.2 ⟨?_, mem_union_right _ (by rwa [if_pos hc])⟩
          rcases mem_insert.1 he with h | h
          · rw [h]; exact G.self_mem_vertexOf _
          · rw [mem_singleton.1 h]; exact G.rot_mem_vertexOf _
        exact (card_pair hd.rot_ne.symm).symm.le.trans (card_le_card hsub)
  ext x
  constructor
  · intro hx
    have hS := h2.subset_core (mem_union_left _ hx)
    obtain ⟨h₁, h₂⟩ := hY _ hx
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
    exact ⟨hS, h₁, h₂⟩
  · intro hx
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hx
    exact mem_map.2 ⟨⟨x, mem_compl_pair_rot_iff.2 hx.2⟩, h1.subset_core (mem_subtype.2 hx.1), rfl⟩

end BivalentRemoval

section ContractEdge

variable {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}
  (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)

include he in
private theorem notMem_vertexOf_inv_of_mem {z : H} (hz : z ∈ G.vertexOf d) :
    z ∉ G.vertexOf (G.inv d) := fun h =>
  he.vertexOf_ne ((G.vertexOf_eq_of_mem hz).symm.trans (G.vertexOf_eq_of_mem h))

private theorem notMem_union_of_mem_vertexOf {y z : H}
    (hy : y ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) (hz : z ∈ G.vertexOf y) :
    z ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := by
  intro hz'
  apply hy
  rcases mem_union.1 hz' with h | h
  · refine mem_union_left _ ?_
    rw [← G.vertexOf_eq_of_mem h, G.vertexOf_eq_of_mem hz]
    exact G.self_mem_vertexOf _
  · refine mem_union_right _ ?_
    rw [← G.vertexOf_eq_of_mem h, G.vertexOf_eq_of_mem hz]
    exact G.self_mem_vertexOf _

include hG he in
/-- The core of the contraction of `G` along `{d, d̄}`, read in `H`, is `K(G) \ {d, d̄}`. -/
@[cluster_algebras "lem_edge_contraction_core"]
theorem map_core_contractEdge :
    (G.contractEdge d hleg).core.map (Embedding.subtype _) = G.core \ {d, G.inv d} := by
  set Gc := G.contractEdge d hleg
  have hGc : Gc.IsPlabicGraph := hG.contractEdge he
  have hinv := hG.inv_involutive
  have hne := he.not_sameCycle
  -- `K(G) \ {d, d̄}` is core-like in the contraction.
  have h1 : Gc.IsCoreLike (G.core.subtype (· ∈ (({d, G.inv d} : Set H)ᶜ : Set H))) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun v hv' => ?_⟩
    · rw [mem_subtype]
      exact hG.bdry_subset_core (mem_contractEdge_bdry.1 hx)
    · rw [mem_subtype] at hx ⊢
      rw [coe_contractEdge_inv hinv]
      exact DiskMap.inv_mem_core hx
    · rintro ⟨y, hyv, hyS⟩
      obtain ⟨z, rfl⟩ := Gc.mem_vertices.1 hv'
      rw [← Gc.vertexOf_eq_of_mem hyv, ← card_map (Embedding.subtype _), map_inter, subtype_map]
      have hyK := mem_subtype.1 hyS
      by_cases hy : (y : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
      · rw [map_vertexOf_contractEdge_of_mem hne hy]
        by_cases hdK : d ∈ G.core
        · have hdK' := DiskMap.inv_mem_core hdK
          obtain ⟨a, ha, had⟩ := exists_mem_ne (DiskMap.two_le_card_vertexOf_inter_core hdK) d
          obtain ⟨c, hc, hcd⟩ :=
            exists_mem_ne (DiskMap.two_le_card_vertexOf_inter_core hdK') (G.inv d)
          have ha1 := (mem_inter.1 ha).1
          have hc1 := (mem_inter.1 hc).1
          have had' : a ≠ G.inv d := fun h =>
            notMem_vertexOf_inv_of_mem he ha1 (by rw [h]; exact G.self_mem_vertexOf _)
          have hcd' : c ≠ d := fun h =>
            notMem_vertexOf_inv_of_mem he (by rw [← h]; exact G.self_mem_vertexOf _)
              (by rwa [h] at hc1 ⊢)
          have hac : a ≠ c := fun h => notMem_vertexOf_inv_of_mem he ha1 (h ▸ hc1)
          refine (card_pair hac).symm.le.trans (card_le_card fun e he' => ?_)
          rcases mem_insert.1 he' with h | h
          · rw [h]
            exact mem_inter.2 ⟨mem_mergedVertex.2 ⟨Or.inl ha1, had, had'⟩,
              mem_filter.2 ⟨(mem_inter.1 ha).2, mem_compl_pair_iff.2 ⟨had, had'⟩⟩⟩
          · rw [mem_singleton.1 h]
            exact mem_inter.2 ⟨mem_mergedVertex.2 ⟨Or.inr hc1, hcd', hcd⟩,
              mem_filter.2 ⟨(mem_inter.1 hc).2, mem_compl_pair_iff.2 ⟨hcd', hcd⟩⟩⟩
        · have hdK' : G.inv d ∉ G.core := fun h => hdK (by
            have := DiskMap.inv_mem_core h
            rwa [hinv] at this)
          refine (DiskMap.two_le_card_vertexOf_inter_core hyK).trans
            (card_le_card fun e he' => ?_)
          obtain ⟨he1, he2⟩ := mem_inter.1 he'
          have heU : e ∈ G.vertexOf d ∨ e ∈ G.vertexOf (G.inv d) := by
            rcases mem_union.1 hy with h | h
            · exact Or.inl (by rwa [← G.vertexOf_eq_of_mem h])
            · exact Or.inr (by rwa [← G.vertexOf_eq_of_mem h])
          have hed : e ≠ d := fun h => hdK (h ▸ he2)
          have hed' : e ≠ G.inv d := fun h => hdK' (h ▸ he2)
          exact mem_inter.2 ⟨mem_mergedVertex.2 ⟨heU, hed, hed'⟩,
            mem_filter.2 ⟨he2, mem_compl_pair_iff.2 ⟨hed, hed'⟩⟩⟩
      · rw [map_vertexOf_contractEdge_of_notMem hne hy]
        refine (DiskMap.two_le_card_vertexOf_inter_core hyK).trans (card_le_card fun e he' => ?_)
        obtain ⟨he1, he2⟩ := mem_inter.1 he'
        exact mem_inter.2 ⟨he1, mem_filter.2 ⟨he2,
          mem_compl_pair_of_notMem (notMem_union_of_mem_vertexOf hy he1)⟩⟩
  -- `K(G^c)`, together with `{d, d̄}` when both endpoints meet it, is core-like in `G`.
  set K' := Gc.core.map (Embedding.subtype _) with hK'
  set A := K'.filter (· ∈ G.vertexOf d) with hA
  set B := K'.filter (· ∈ G.vertexOf (G.inv d)) with hB
  set S2 := K' ∪ (if A.Nonempty ∧ B.Nonempty then {d, G.inv d} else ∅) with hS2
  have hY : ∀ x ∈ K', x ≠ d ∧ x ≠ G.inv d := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    exact mem_compl_pair_iff.1 y.2
  have hAB : ∀ w ∈ K', w ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) → 2 ≤ #(A ∪ B) := by
    intro w hw hwU
    obtain ⟨w, hw', rfl⟩ := mem_map.1 hw
    refine (DiskMap.two_le_card_vertexOf_inter_core hw').trans
      ((card_map (Embedding.subtype _)).symm.le.trans (card_le_card fun e he' => ?_))
    rw [map_inter, map_vertexOf_contractEdge_of_mem hne hwU] at he'
    obtain ⟨he1, he2⟩ := mem_inter.1 he'
    rcases (mem_mergedVertex.1 he1).1 with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨he2, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨he2, h⟩)
  have h2 : G.IsCoreLike S2 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun v hv' => ?_⟩
    · exact mem_union_left _ (mem_map.2 ⟨⟨x, he.mem_of_mem_bdry hx⟩,
        hGc.bdry_subset_core (mem_contractEdge_bdry.2 hx), rfl⟩)
    · rcases mem_union.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
        exact mem_union_left _ (mem_map.2 ⟨Gc.inv y, DiskMap.inv_mem_core hy,
          coe_contractEdge_inv (hleg := hleg) hinv y⟩)
      · refine mem_union_right _ ?_
        split_ifs at hx ⊢ with hc
        · rcases mem_insert.1 hx with h | h
          · rw [h]; exact mem_insert_of_mem (mem_singleton_self _)
          · rw [mem_singleton.1 h, hinv]; exact mem_insert_self _ _
        · simp at hx
    · rintro ⟨z, hzv, hzS⟩
      obtain ⟨w, rfl⟩ := G.mem_vertices.1 hv'
      rw [← G.vertexOf_eq_of_mem hzv]
      by_cases hz : z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
      · by_cases hc : A.Nonempty ∧ B.Nonempty
        · have hsub2 : ({d, G.inv d} : Finset H) ⊆ S2 := by
            rw [hS2, if_pos hc]; exact subset_union_right
          rcases mem_union.1 hz with hzx | hzy
          · rw [G.vertexOf_eq_of_mem hzx]
            obtain ⟨a, ha⟩ := hc.1
            obtain ⟨ha1, ha2⟩ := mem_filter.1 ha
            refine (card_pair (hY a ha1).1.symm).symm.le.trans (card_le_card fun e he' => ?_)
            rcases mem_insert.1 he' with h | h
            · rw [h]
              exact mem_inter.2 ⟨G.self_mem_vertexOf _, hsub2 (mem_insert_self _ _)⟩
            · rw [mem_singleton.1 h]
              exact mem_inter.2 ⟨ha2, mem_union_left _ ha1⟩
          · rw [G.vertexOf_eq_of_mem hzy]
            obtain ⟨c, hc'⟩ := hc.2
            obtain ⟨hc1, hc2⟩ := mem_filter.1 hc'
            refine (card_pair (hY c hc1).2.symm).symm.le.trans (card_le_card fun e he' => ?_)
            rcases mem_insert.1 he' with h | h
            · rw [h]
              exact mem_inter.2 ⟨G.self_mem_vertexOf _,
                hsub2 (mem_insert_of_mem (mem_singleton_self _))⟩
            · rw [mem_singleton.1 h]
              exact mem_inter.2 ⟨hc2, mem_union_left _ hc1⟩
        · have hzK : z ∈ K' := by
            rcases mem_union.1 hzS with h | h
            · exact h
            · rw [if_neg hc] at h; simp at h
          have h2AB := hAB z hzK hz
          rcases mem_union.1 hz with hzx | hzy
          · have hBe : B = ∅ := by
              by_contra hB'
              exact hc ⟨⟨z, mem_filter.2 ⟨hzK, hzx⟩⟩, nonempty_iff_ne_empty.2 hB'⟩
            rw [hBe, union_empty] at h2AB
            rw [G.vertexOf_eq_of_mem hzx]
            refine h2AB.trans (card_le_card fun e he' => ?_)
            obtain ⟨he1, he2⟩ := mem_filter.1 he'
            exact mem_inter.2 ⟨he2, mem_union_left _ he1⟩
          · have hAe : A = ∅ := by
              by_contra hA'
              exact hc ⟨nonempty_iff_ne_empty.2 hA', ⟨z, mem_filter.2 ⟨hzK, hzy⟩⟩⟩
            rw [hAe, empty_union] at h2AB
            rw [G.vertexOf_eq_of_mem hzy]
            refine h2AB.trans (card_le_card fun e he' => ?_)
            obtain ⟨he1, he2⟩ := mem_filter.1 he'
            exact mem_inter.2 ⟨he2, mem_union_left _ he1⟩
      · have hzK : z ∈ K' := by
          rcases mem_union.1 hzS with h | h
          · exact h
          · exfalso
            split_ifs at h
            · rcases mem_insert.1 h with h | h
              · exact hz (mem_union_left _ (by rw [h]; exact G.self_mem_vertexOf _))
              · rw [mem_singleton.1 h] at hz
                exact hz (mem_union_right _ (G.self_mem_vertexOf _))
            · simp at h
        obtain ⟨y, hy, rfl⟩ := mem_map.1 hzK
        have hsub : (Gc.vertexOf y ∩ Gc.core).map (Embedding.subtype _) ⊆
            G.vertexOf (y : H) ∩ S2 := by
          rw [map_inter, map_vertexOf_contractEdge_of_notMem hne hz]
          exact inter_subset_inter_left subset_union_left
        exact (DiskMap.two_le_card_vertexOf_inter_core hy).trans
          ((card_map _).symm.le.trans (card_le_card hsub))
  ext x
  constructor
  · intro hx
    have hS := h2.subset_core (mem_union_left _ hx)
    obtain ⟨h₁, h₂⟩ := hY _ hx
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
    exact ⟨hS, h₁, h₂⟩
  · intro hx
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hx
    exact mem_map.2 ⟨⟨x, mem_compl_pair_iff.2 hx.2⟩, h1.subset_core (mem_subtype.2 hx.1), rfl⟩

end ContractEdge

/-! ### Walks through the core -/

/-- One step `e ↦ \overline{σ_K(e)}` of the walk through the core, extended by the identity
outside the core. -/
private noncomputable def walkStep (G : PlabicData H b) (x : H) : H :=
  if h : x ∈ G.core then G.inv (G.coreRot ⟨x, mem_coe.2 h⟩) else x

private theorem walkStep_of_mem {x : H} (h : x ∈ G.core) :
    G.walkStep x = G.inv (G.coreRot ⟨x, mem_coe.2 h⟩) :=
  dif_pos h

private theorem walkStep_of_notMem {x : H} (h : x ∉ G.core) : G.walkStep x = x :=
  dif_neg h

private theorem coe_coreRot_of_rot_mem {x : (G.core : Set H)} (h : G.rot x ∈ G.core) :
    (G.coreRot x : H) = G.rot x :=
  coe_firstReturn_of_apply_mem (mem_coe.2 h)

/-- The involution of the skeleton is the first hit of `R` along the walk. -/
private theorem firstHit_skeletonInvFun (d : (G.skeletonDarts : Set H)) :
    FirstHit G.walkStep (· ∈ G.skeletonDarts) (G.inv d) (G.skeletonInvFun d) := by
  obtain ⟨n, hn, hmin, h⟩ := exists_coe_skeletonInvFun d
  rw [h]
  have h' := firstHit_of_iterate (f := G.coreWalk) (p := fun e => (e : H) ∈ G.skeletonDarts)
    (x := ⟨G.inv d, mem_coe.2 (DiskMap.inv_mem_core (mem_core_of_mem_skeletonDarts d.2))⟩)
    (n := n) hn hmin
  exact h'.map Subtype.val (fun u => by rw [walkStep_of_mem u.2]; rfl) fun _ => Iff.rfl

private theorem coe_skeletonInvFun_eq_of_firstHit {d : (G.skeletonDarts : Set H)} {t : H}
    (h : FirstHit G.walkStep (· ∈ G.skeletonDarts) (G.inv d) t) :
    (G.skeletonInvFun d : H) = t :=
  (firstHit_skeletonInvFun d).unique h

private theorem notMem_skeletonDarts_of_card_le_two {x : H}
    (hb : ¬G.IsBoundaryVertex (G.vertexOf x)) (h2 : #(G.vertexOf x) ≤ 2) :
    x ∉ G.skeletonDarts := by
  intro h
  rcases (mem_filter.1 h).2 with h' | h'
  · exact hb h'
  · have := card_le_card (inter_subset_left : G.vertexOf x ∩ G.core ⊆ G.vertexOf x)
    omega

/-- The `i`-th leg of the skeleton is the `i`-th leg of `G` when that dart lies in
`G.skeletonDarts`, and its rotation otherwise. -/
theorem coe_skeleton_leg (hG : G.IsPlabicGraph) (i : Fin b) :
    ((G.skeleton hG).leg i : H) =
      if G.leg i ∈ G.skeletonDarts then G.leg i else G.rot (G.leg i) := by
  by_cases h : G.leg i ∈ G.skeletonDarts
  · rw [if_pos h]
    exact coe_skeleton_leg_of_mem hG h
  · rw [if_neg h]
    simp [skeleton, h]

/-! ### Removing a bivalent vertex keeps the skeleton -/

section SkeletonBivalentRemoval

variable {d : H} (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d)

include hG hd in
private theorem mem_bivalentRemoval_core_iff {y : ({d, G.rot d}ᶜ : Set H)} :
    y ∈ (G.bivalentRemoval hG hd).core ↔ (y : H) ∈ G.core := by
  rw [← mem_map' (Embedding.subtype _), map_core_bivalentRemoval hG hd, mem_sdiff]
  have := mem_compl_pair_rot_iff.1 y.2
  simp only [Embedding.coe_subtype, mem_insert, mem_singleton, not_or]
  exact and_iff_left this

include hG hd in
private theorem card_bivalentRemoval_vertexOf_inter_core (y : ({d, G.rot d}ᶜ : Set H)) :
    #((G.bivalentRemoval hG hd).vertexOf y ∩ (G.bivalentRemoval hG hd).core) =
      #(G.vertexOf y ∩ G.core) := by
  rw [← card_map (Embedding.subtype _), map_inter, map_bivalentRemoval_vertexOf hG hd,
    map_core_bivalentRemoval hG hd]
  congr 1
  ext e
  simp only [mem_inter, mem_sdiff, mem_insert, mem_singleton, not_or]
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, mem_compl_pair_rot_iff.1
    (mem_of_sameCycle_rot_bivalentRemoval hd y.2 (G.mem_vertexOf.1 h.1))⟩⟩

include hG hd in
private theorem mem_bivalentRemoval_skeletonDarts_iff {y : ({d, G.rot d}ᶜ : Set H)} :
    y ∈ (G.bivalentRemoval hG hd).skeletonDarts ↔ (y : H) ∈ G.skeletonDarts := by
  simp only [skeletonDarts, mem_filter, mem_bivalentRemoval_core_iff hG hd,
    isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd,
    card_bivalentRemoval_vertexOf_inter_core hG hd]

include hd in
private theorem notMem_skeletonDarts_of_isBivalentRemovable :
    d ∉ G.skeletonDarts ∧ G.rot d ∉ G.skeletonDarts := by
  refine ⟨notMem_skeletonDarts_of_card_le_two hd.not_isBoundaryVertex hd.card_vertexOf.le, ?_⟩
  refine notMem_skeletonDarts_of_card_le_two (by rw [G.vertexOf_rot]; exact hd.not_isBoundaryVertex)
    (by rw [G.vertexOf_rot, hd.card_vertexOf])

include hd in
private theorem mem_compl_pair_rot_of_mem_skeletonDarts {x : H} (hx : x ∈ G.skeletonDarts) :
    x ∈ ({d, G.rot d}ᶜ : Set H) :=
  mem_compl_pair_rot_iff.2 ⟨fun h => (notMem_skeletonDarts_of_isBivalentRemovable hd).1 (h ▸ hx),
    fun h => (notMem_skeletonDarts_of_isBivalentRemovable hd).2 (h ▸ hx)⟩

include hG hd in
private theorem coe_bivalentRemoval_coreRot
    (u : ((G.bivalentRemoval hG hd).core : Set ({d, G.rot d}ᶜ : Set H))) :
    (((G.bivalentRemoval hG hd).coreRot u : ({d, G.rot d}ᶜ : Set H)) : H) =
      G.coreRot ⟨((u : ({d, G.rot d}ᶜ : Set H)) : H),
        mem_coe.2 ((mem_bivalentRemoval_core_iff hG hd).1 (mem_coe.1 u.2))⟩ :=
  coe_firstReturn_of_semiconj Subtype.val (fun _ => rfl)
    (fun _ => (mem_bivalentRemoval_core_iff hG hd).symm) u

include hG hd in
private theorem coe_bivalentRemoval_walkStep {u : ({d, G.rot d}ᶜ : Set H)} (hu : (u : H) ∈ G.core) :
    ((G.bivalentRemoval hG hd).walkStep u : H) =
      if G.walkStep u = d then G.inv (G.rot d)
      else if G.walkStep u = G.rot d then G.inv d else G.walkStep u := by
  have hinv := hG.inv_involutive
  have hu' := (mem_bivalentRemoval_core_iff hG hd).2 hu
  rw [walkStep_of_mem hu', walkStep_of_mem hu]
  have hc := coe_bivalentRemoval_coreRot hG hd ⟨u, mem_coe.2 hu'⟩
  split_ifs with h₁ h₂
  · apply coe_bivalentRemoval_inv_of_eq_inv hG hd
    have := congrArg G.inv h₁
    rw [hinv] at this
    rw [hc]
    exact this
  · apply coe_bivalentRemoval_inv_of_eq_inv_rot hG hd
    have := congrArg G.inv h₂
    rw [hinv] at this
    rw [hc]
    exact this
  · rw [coe_bivalentRemoval_inv_of_ne hG hd, hc]
    · rw [hc]
      intro h
      apply h₁
      rw [h, hinv]
    · rw [hc]
      intro h
      apply h₂
      rw [h, hinv]

include hG hd in
private theorem coe_bivalentRemoval_skeletonInvFun
    (x : ((G.bivalentRemoval hG hd).skeletonDarts : Set ({d, G.rot d}ᶜ : Set H))) :
    (((G.bivalentRemoval hG hd).skeletonInvFun x : ({d, G.rot d}ᶜ : Set H)) : H) =
      G.skeletonInvFun ⟨((x : ({d, G.rot d}ᶜ : Set H)) : H),
        mem_coe.2 ((mem_bivalentRemoval_skeletonDarts_iff hG hd).1 x.2)⟩ := by
  have hinv := hG.inv_involutive
  have hR := notMem_skeletonDarts_of_isBivalentRemovable hd
  have hRr : ∀ u : ({d, G.rot d}ᶜ : Set H),
      u ∈ (G.bivalentRemoval hG hd).skeletonDarts ↔ (u : H) ∈ G.skeletonDarts :=
    fun u => mem_bivalentRemoval_skeletonDarts_iff hG hd
  have claim : ∀ a t, FirstHit G.walkStep (· ∈ G.skeletonDarts) a t →
      (∀ u : ({d, G.rot d}ᶜ : Set H), (u : H) = a → ∃ t' : ({d, G.rot d}ᶜ : Set H),
        (t' : H) = t ∧ FirstHit (G.bivalentRemoval hG hd).walkStep
          (· ∈ (G.bivalentRemoval hG hd).skeletonDarts) u t') ∧
      (a = d → ∀ u : ({d, G.rot d}ᶜ : Set H), (u : H) = G.inv (G.rot d) →
        ∃ t' : ({d, G.rot d}ᶜ : Set H), (t' : H) = t ∧
          FirstHit (G.bivalentRemoval hG hd).walkStep
            (· ∈ (G.bivalentRemoval hG hd).skeletonDarts) u t') ∧
      (a = G.rot d → ∀ u : ({d, G.rot d}ᶜ : Set H), (u : H) = G.inv d →
        ∃ t' : ({d, G.rot d}ᶜ : Set H), (t' : H) = t ∧
          FirstHit (G.bivalentRemoval hG hd).walkStep
            (· ∈ (G.bivalentRemoval hG hd).skeletonDarts) u t') := by
    intro a t h
    induction h with
    | @stop a ha =>
      refine ⟨fun u hu => ⟨u, hu, .stop ((hRr u).2 (hu ▸ ha))⟩, fun h => absurd (h ▸ ha) hR.1,
        fun h => absurd (h ▸ ha) hR.2⟩
    | @step a t ha _ ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      refine ⟨fun u hu => ?_, fun had u hu => ?_, fun had u hu => ?_⟩
      · have hu' : u ∉ (G.bivalentRemoval hG hd).skeletonDarts := fun h => ha (hu ▸ (hRr u).1 h)
        by_cases haK : a ∈ G.core
        · have hstep := coe_bivalentRemoval_walkStep hG hd (u := u) (hu ▸ haK)
          rw [hu] at hstep
          split_ifs at hstep with h1 h2
          · obtain ⟨t', ht', ht''⟩ := ih2 h1 _ hstep
            exact ⟨t', ht', .step hu' ht''⟩
          · obtain ⟨t', ht', ht''⟩ := ih3 h2 _ hstep
            exact ⟨t', ht', .step hu' ht''⟩
          · obtain ⟨t', ht', ht''⟩ := ih1 _ hstep
            exact ⟨t', ht', .step hu' ht''⟩
        · have hst : (G.bivalentRemoval hG hd).walkStep u = u :=
            walkStep_of_notMem fun h => haK (hu ▸ (mem_bivalentRemoval_core_iff hG hd).1 h)
          obtain ⟨t', ht', ht''⟩ := ih1 u (hu.trans (walkStep_of_notMem haK).symm)
          refine ⟨t', ht', .step hu' ?_⟩
          rwa [hst]
      · subst had
        by_cases hdK : a ∈ G.core
        · have : G.walkStep a = G.inv (G.rot a) := by
            rw [walkStep_of_mem hdK,
              coe_coreRot_of_rot_mem (rot_mem_core_of_mem_core hd hdK)]
          exact ih1 u (hu.trans this.symm)
        · exact ih2 (walkStep_of_notMem hdK) u hu
      · subst had
        by_cases hdK : G.rot d ∈ G.core
        · have : G.walkStep (G.rot d) = G.inv d := by
            rw [walkStep_of_mem hdK, coe_coreRot_of_rot_mem (by
              rw [hd.rot_rot]; exact mem_core_of_rot_mem_core hd hdK)]
            change G.inv (G.rot (G.rot d)) = _
            rw [hd.rot_rot]
          exact ih1 u (hu.trans this.symm)
        · exact ih3 (walkStep_of_notMem hdK) u hu
  have hG' := firstHit_skeletonInvFun (G := G)
    ⟨((x : ({d, G.rot d}ᶜ : Set H)) : H),
      mem_coe.2 ((mem_bivalentRemoval_skeletonDarts_iff hG hd).1 x.2)⟩
  obtain ⟨c1, c2, c3⟩ := claim _ _ hG'
  have key : ∃ t' : ({d, G.rot d}ᶜ : Set H), (t' : H) = G.skeletonInvFun
      ⟨((x : ({d, G.rot d}ᶜ : Set H)) : H),
        mem_coe.2 ((mem_bivalentRemoval_skeletonDarts_iff hG hd).1 x.2)⟩ ∧
      FirstHit (G.bivalentRemoval hG hd).walkStep (· ∈ (G.bivalentRemoval hG hd).skeletonDarts)
        ((G.bivalentRemoval hG hd).inv x) t' := by
    by_cases h₁ : ((x : ({d, G.rot d}ᶜ : Set H)) : H) = G.inv d
    · exact c2 (by rw [h₁, hinv]) _
        (coe_bivalentRemoval_inv_of_eq_inv hG hd h₁)
    by_cases h₂ : ((x : ({d, G.rot d}ᶜ : Set H)) : H) = G.inv (G.rot d)
    · exact c3 (by rw [h₂, hinv]) _
        (coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂)
    · exact c1 _ (coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂)
  obtain ⟨t', ht', ht''⟩ := key
  rw [← ht', coe_skeletonInvFun_eq_of_firstHit ht'']

/-- The identification of the darts of `Γ(G^r)` with those of `Γ(G)`. -/
private noncomputable def skeletonBivalentRemovalEquiv :
    ((G.bivalentRemoval hG hd).skeletonDarts : Set ({d, G.rot d}ᶜ : Set H)) ≃
      (G.skeletonDarts : Set H) where
  toFun x := ⟨((x : ({d, G.rot d}ᶜ : Set H)) : H),
    mem_coe.2 ((mem_bivalentRemoval_skeletonDarts_iff hG hd).1 x.2)⟩
  invFun y := ⟨⟨y, mem_compl_pair_rot_of_mem_skeletonDarts hd y.2⟩,
    mem_coe.2 ((mem_bivalentRemoval_skeletonDarts_iff hG hd).2 y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the darts of `Γ(G^r)` with those of `Γ(G)` is an isomorphism. -/
private noncomputable def skeletonBivalentRemovalIso :
    ((G.bivalentRemoval hG hd).skeleton (isPlabicGraph_bivalentRemoval hG hd)).Iso
      (G.skeleton hG) :=
  isoOfMapLeg (skeletonBivalentRemovalEquiv hG hd)
    (fun x => Subtype.ext (by
      change ((((G.bivalentRemoval hG hd).skeletonInvFun x : ({d, G.rot d}ᶜ : Set H))) : H) = _
      rw [coe_bivalentRemoval_skeletonInvFun]
      rfl))
    (fun x => Subtype.ext (by
      change ((firstReturn (G.bivalentRemoval hG hd).rot _ x : ({d, G.rot d}ᶜ : Set H)) : H) =
        (firstReturn G.rot _ _ : H)
      exact coe_firstReturn_of_semiconj Subtype.val (fun _ => rfl)
        (fun _ => (mem_bivalentRemoval_skeletonDarts_iff hG hd).symm) x))
    (fun x => by
      rw [mem_skeleton_bdry, mem_skeleton_bdry, mem_bivalentRemoval_bdry]
      rfl)
    (fun _ _ => rfl)
    (fun i => Subtype.ext (by
      change ((((G.bivalentRemoval hG hd).skeleton _).leg i : ({d, G.rot d}ᶜ : Set H)) : H) = _
      rw [coe_skeleton_leg, coe_skeleton_leg]
      by_cases h : G.leg i ∈ G.skeletonDarts
      · rw [if_pos ((mem_bivalentRemoval_skeletonDarts_iff hG hd).2 h), if_pos h]
        rfl
      · rw [if_neg (mt (mem_bivalentRemoval_skeletonDarts_iff hG hd).1 h), if_neg h]
        rfl))

/-- If `G^r` is the removal of the bivalent vertex `{d, σ d}` of the plabic graph `G`, then
`Γ(G^r) = Γ(G)`: the darts of `Γ(G^r)`, read in `H`, are those of `Γ(G)`, and this identification
is an isomorphism `Γ(G^r) → Γ(G)`. -/
@[cluster_algebras "lem_skeleton_bivalent_removal"]
theorem exists_skeletonBivalentRemovalIso :
    ∃ θ : ((G.bivalentRemoval hG hd).skeleton (isPlabicGraph_bivalentRemoval hG hd)).Iso
      (G.skeleton hG), ∀ x, (θ.toEquiv x : H) = ((x : ({d, G.rot d}ᶜ : Set H)) : H) :=
  ⟨skeletonBivalentRemovalIso hG hd, fun _ => rfl⟩

end SkeletonBivalentRemoval

/-! ### Deleting an internal leaf keeps the skeleton -/

section SkeletonLeafDeletion

variable {ℓ : H} (hG : G.IsPlabicGraph) (hu : G.IsInternalLeaf (G.vertexOf ℓ))
  (hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices)

include hG hu hv in
private theorem mem_leafDeletion_core_iff {y : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)} :
    y ∈ (G.leafDeletion hG hu hv).core ↔ (y : H) ∈ G.core := by
  have h := mem_map' (Embedding.subtype (· ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H))) (a := y)
    (s := (G.leafDeletion hG hu hv).core)
  rw [map_core_leafDeletion hG hu hv] at h
  exact h.symm

include hG hu hv in
private theorem card_leafDeletion_vertexOf_inter_core (y : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    #((G.leafDeletion hG hu hv).vertexOf y ∩ (G.leafDeletion hG hu hv).core) =
      #(G.vertexOf y ∩ G.core) := by
  rw [← card_map (Embedding.subtype _), map_inter, map_vertexOf_leafDeletion hG hu hv,
    map_core_leafDeletion hG hu hv, erase_inter,
    erase_eq_of_notMem fun h => inv_notMem_core_of_isInternalLeaf hG hu (mem_inter.1 h).2]

include hG hu hv in
private theorem mem_leafDeletion_skeletonDarts_iff {y : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)} :
    y ∈ (G.leafDeletion hG hu hv).skeletonDarts ↔ (y : H) ∈ G.skeletonDarts := by
  simp only [skeletonDarts, mem_filter, mem_leafDeletion_core_iff hG hu hv,
    isBoundaryVertex_vertexOf_leafDeletion_iff hG hu hv,
    card_leafDeletion_vertexOf_inter_core hG hu hv]

include hG hu in
private theorem core_subset_compl_pair :
    (G.core : Set H) ⊆ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) :=
  fun _ hx => mem_compl_pair_of_mem_core hG hu (mem_coe.1 hx)

include hG hu hv in
private theorem coe_leafDeletion_coreRot
    (u : ((G.leafDeletion hG hu hv).core : Set (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H))) :
    (((G.leafDeletion hG hu hv).coreRot u : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H) =
      G.coreRot ⟨((u : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H),
        mem_coe.2 ((mem_leafDeletion_core_iff hG hu hv).1 (mem_coe.1 u.2))⟩ := by
  unfold coreRot
  rw [leafDeletion_rot_eq_firstReturnPerm hG hu hv]
  exact coe_firstReturn_firstReturnPerm G.rot (core_subset_compl_pair hG hu)
    (fun v => mem_coe.trans ((mem_leafDeletion_core_iff hG hu hv).trans mem_coe.symm)) u

include hG hu hv in
private theorem coe_leafDeletion_walkStep (u : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    (((G.leafDeletion hG hu hv).walkStep u : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H) =
      G.walkStep u := by
  by_cases hu' : u ∈ (G.leafDeletion hG hu hv).core
  · rw [walkStep_of_mem hu', walkStep_of_mem ((mem_leafDeletion_core_iff hG hu hv).1 hu'),
      coe_leafDeletion_inv, coe_leafDeletion_coreRot hG hu hv]
  · rw [walkStep_of_notMem hu', walkStep_of_notMem (mt (mem_leafDeletion_core_iff hG hu hv).2 hu')]

include hG hu hv in
private theorem coe_leafDeletion_skeletonInvFun
    (x : ((G.leafDeletion hG hu hv).skeletonDarts : Set (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H))) :
    (((G.leafDeletion hG hu hv).skeletonInvFun x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H) =
      G.skeletonInvFun ⟨((x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H),
        mem_coe.2 ((mem_leafDeletion_skeletonDarts_iff hG hu hv).1 (mem_coe.1 x.2))⟩ := by
  symm
  apply coe_skeletonInvFun_eq_of_firstHit
  have h := (firstHit_skeletonInvFun x).map Subtype.val (coe_leafDeletion_walkStep hG hu hv)
    fun u => (mem_leafDeletion_skeletonDarts_iff hG hu hv).symm
  rwa [coe_leafDeletion_inv] at h

/-- The identification of the darts of `Γ(G^l)` with those of `Γ(G)`. -/
private noncomputable def skeletonLeafDeletionEquiv :
    ((G.leafDeletion hG hu hv).skeletonDarts : Set (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) ≃
      (G.skeletonDarts : Set H) where
  toFun x := ⟨((x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H),
    mem_coe.2 ((mem_leafDeletion_skeletonDarts_iff hG hu hv).1 x.2)⟩
  invFun y := ⟨⟨y, mem_compl_pair_of_mem_core hG hu (mem_core_of_mem_skeletonDarts y.2)⟩,
    mem_coe.2 ((mem_leafDeletion_skeletonDarts_iff hG hu hv).2 y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Deleting an internal leaf keeps the skeleton: the identification of the darts of `Γ(G^l)`
with those of `Γ(G)` is an isomorphism. -/
private noncomputable def skeletonLeafDeletionIso :
    ((G.leafDeletion hG hu hv).skeleton (isPlabicGraph_leafDeletion hG hu hv)).Iso
      (G.skeleton hG) :=
  isoOfMapLeg (skeletonLeafDeletionEquiv hG hu hv)
    (fun x => Subtype.ext (by
      change ((((G.leafDeletion hG hu hv).skeletonInvFun x :
        (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H))) : H) = _
      rw [coe_leafDeletion_skeletonInvFun]
      rfl))
    (fun x => Subtype.ext (by
      change ((firstReturn (G.leafDeletion hG hu hv).rot _ x :
        (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H) = (firstReturn G.rot _ _ : H)
      rw [leafDeletion_rot_eq_firstReturnPerm hG hu hv]
      exact coe_firstReturn_firstReturnPerm G.rot
        (fun _ hx => mem_compl_pair_of_mem_core hG hu
          (mem_core_of_mem_skeletonDarts (mem_coe.1 hx)))
        (fun v => mem_coe.trans ((mem_leafDeletion_skeletonDarts_iff hG hu hv).trans
          mem_coe.symm)) x))
    (fun x => by
      rw [mem_skeleton_bdry, mem_skeleton_bdry, mem_leafDeletion_bdry]
      rfl)
    (fun x _ => by
      rw [skeleton_colour, skeleton_colour, leafDeletion_colour]
      split_ifs with h
      · exact colour_eq_of_sameCycle hG (G.vertexOf_mem_internalVertices.1 hv)
          (G.mem_vertexOf.1 h)
      · rfl)
    (fun i => Subtype.ext (by
      change ((((G.leafDeletion hG hu hv).skeleton _).leg i :
        (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) : H) = _
      rw [coe_skeleton_leg, coe_skeleton_leg]
      by_cases h : G.leg i ∈ G.skeletonDarts
      · rw [if_pos ((mem_leafDeletion_skeletonDarts_iff hG hu hv).2 h), if_pos h]
        rfl
      · rw [if_neg (mt (mem_leafDeletion_skeletonDarts_iff hG hu hv).1 h), if_neg h]
        rw [coe_leafDeletion_rot, if_neg]
        · rfl
        · intro h'
          have := G.vertexOf_eq_of_mem (h' ▸ G.rot_mem_vertexOf (G.leg i))
          exact G.vertexOf_mem_internalVertices.1 hv
            (this ▸ G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))))

end SkeletonLeafDeletion

/-! ### The skeleton of an anchored graph is a plabic graph -/

private theorem isPlabicGraph_skeleton_aux (n : ℕ) :
    ∀ (H : Type u) [Fintype H] [DecidableEq H] (G : PlabicData H b) (hG : G.IsPlabicGraph),
      G.IsAnchored → Fintype.card H = n → (G.skeleton hG).IsPlabicGraph := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ G hG hA hn
  have hleg : ∀ i, (G.skeleton hG).leg i ∉ (G.skeleton hG).bdry := fun i => by
    rw [mem_skeleton_bdry, coe_skeleton_leg_of_mem hG (hA.leg_mem_skeletonDarts hG i)]
    exact hG.leg_notMem_bdry i
  by_cases hleaf : ∃ ℓ, G.IsInternalLeaf (G.vertexOf ℓ)
  · obtain ⟨ℓ, hu⟩ := hleaf
    have hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices := by
      by_contra hb
      have hb' : G.IsBoundaryVertex (G.vertexOf (G.inv ℓ)) := by
        by_contra h
        exact hb (G.vertexOf_mem_internalVertices.2 h)
      obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hb')
      have hℓB : ℓ ∉ G.bdry := fun h =>
        G.vertexOf_mem_internalVertices.1 hu.1 (G.isBoundaryVertex_vertexOf_of_mem h)
      have hℓ'B : G.inv ℓ ∉ G.bdry := fun h => hℓB (hG.inv_mem_bdry_iff.1 h)
      have hmem : G.inv ℓ ∈ (G.bvertex i).filter (· ∉ G.bdry) :=
        mem_filter.2 ⟨by rw [hi]; exact G.self_mem_vertexOf _, hℓ'B⟩
      rw [hG.filter_bvertex_notMem_bdry i, mem_singleton] at hmem
      exact inv_notMem_core_of_isInternalLeaf hG hu (hmem ▸ hA i)
    have hGl := isPlabicGraph_leafDeletion hG hu hv
    have hAl : (G.leafDeletion hG hu hv).IsAnchored := fun i =>
      (mem_leafDeletion_core_iff hG hu hv).2 (hA i)
    have hcard : Fintype.card (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := ℓ) (by simp)
    exact isPlabicGraph_of_iso (skeletonLeafDeletionIso hG hu hv).symm
      (ih _ hcard _ _ hGl hAl rfl) hleg
  by_cases h2 : ∃ d, G.vertexOf d ∈ G.internalVertices ∧ #(G.vertexOf d) = 2
  · obtain ⟨d, hdi, hd2⟩ := h2
    have hne : G.inv d ≠ G.rot d := by
      intro h
      have hdr : G.rot d ≠ d := fun h' => hG.inv_ne d (h.trans h')
      have hS : ({d, G.rot d} : Finset H) = G.vertexOf d := by
        refine eq_of_subset_of_card_le (fun e he => ?_) (by rw [hd2, card_pair hdr.symm])
        rcases mem_insert.1 he with h' | h'
        · rw [h']; exact G.self_mem_vertexOf _
        · rw [mem_singleton.1 h']; exact G.rot_mem_vertexOf _
      have key : ∀ z, G.Reach d z → z ∈ G.vertexOf d := by
        intro z hz
        induction hz with
        | refl => exact G.self_mem_vertexOf _
        | @rot e _ ih' =>
          rw [← G.vertexOf_eq_of_mem ih']
          exact G.rot_mem_vertexOf _
        | @inv e _ ih' =>
          rw [← hS] at ih' ⊢
          rcases mem_insert.1 ih' with h' | h'
          · rw [h', h]; exact mem_insert_of_mem (mem_singleton_self _)
          · rw [mem_singleton.1 h', ← h, hG.inv_involutive]; exact mem_insert_self _ _
      obtain ⟨z, -, hzB⟩ := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem ⟨0, hG.one_le⟩)
      have hz := key z (hG.reach d z)
      exact G.vertexOf_mem_internalVertices.1 hdi
        (G.vertexOf_eq_of_mem hz ▸ G.isBoundaryVertex_vertexOf_of_mem hzB)
    have hd : G.IsBivalentRemovable d := ⟨G.vertexOf_mem_internalVertices.1 hdi, hd2, hne⟩
    have hGr := isPlabicGraph_bivalentRemoval hG hd
    have hAr : (G.bivalentRemoval hG hd).IsAnchored := fun i =>
      (mem_bivalentRemoval_core_iff hG hd).2 (hA i)
    have hcard : Fintype.card ({d, G.rot d}ᶜ : Set H) < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := d) (by simp)
    exact isPlabicGraph_of_iso (skeletonBivalentRemovalIso hG hd).symm
      (ih _ hcard _ _ hGr hAr rfl) hleg
  have h3 : ∀ v ∈ G.internalVertices, 3 ≤ #v := by
    intro v hv
    obtain ⟨d, rfl⟩ := G.mem_vertices.1 (mem_filter.1 hv).1
    have h1 : 0 < #(G.vertexOf d) := card_pos.2 ⟨d, G.self_mem_vertexOf d⟩
    have hne1 : #(G.vertexOf d) ≠ 1 := fun h => hleaf ⟨d, hv, h⟩
    have hne2 : #(G.vertexOf d) ≠ 2 := fun h => h2 ⟨d, hv, h⟩
    omega
  exact isPlabicGraph_of_iso (skeletonIsoOfThick hG h3) hG hleg

/-- The skeleton of an anchored plabic graph is a plabic graph. -/
@[cluster_algebras "lem_skeleton_plabic"]
theorem IsAnchored.isPlabicGraph_skeleton (hG : G.IsPlabicGraph) (hA : G.IsAnchored) :
    (G.skeleton hG).IsPlabicGraph :=
  isPlabicGraph_skeleton_aux _ H G hG hA rfl

/-! ### The skeleton under isomorphisms -/

/-- A vertex of the skeleton is a boundary vertex iff the corresponding vertex of `G` is. -/
theorem isBoundaryVertex_skeleton_vertexOf_iff (hG : G.IsPlabicGraph)
    (x : (G.skeletonDarts : Set H)) :
    (G.skeleton hG).IsBoundaryVertex ((G.skeleton hG).vertexOf x) ↔
      G.IsBoundaryVertex (G.vertexOf x) := by
  constructor
  · rintro ⟨y, hy, hyB⟩
    refine ⟨y, ?_, (mem_skeleton_bdry hG).1 hyB⟩
    have := mem_map_of_mem (Embedding.subtype (· ∈ (G.skeletonDarts : Set H))) hy
    rw [map_skeleton_vertexOf] at this
    exact (mem_inter.1 this).1
  · rintro ⟨z, hz, hzB⟩
    have hzR : z ∈ G.skeletonDarts := mem_filter.2 ⟨hG.bdry_subset_core hzB,
      Or.inl (by rw [G.vertexOf_eq_of_mem hz]; exact ⟨z, hz, hzB⟩)⟩
    refine ⟨⟨z, mem_coe.2 hzR⟩, ?_, (mem_skeleton_bdry hG).2 hzB⟩
    rw [← mem_map' (Embedding.subtype (· ∈ (G.skeletonDarts : Set H))), map_skeleton_vertexOf]
    exact mem_inter.2 ⟨hz, hzR⟩

section SkeletonIso

variable {G' : PlabicData H' b} (θ : G.Iso G')

private theorem Iso.apply_mem_skeletonDarts_iff {x : H} :
    θ.toEquiv x ∈ G'.skeletonDarts ↔ x ∈ G.skeletonDarts := by
  have hc : #(G'.vertexOf (θ.toEquiv x) ∩ G'.core) = #(G.vertexOf x ∩ G.core) := by
    rw [← θ.map_vertexOf, ← θ.map_core, ← map_inter, card_map]
  simp only [skeletonDarts, mem_filter, θ.apply_mem_core_iff, θ.isBoundaryVertex_vertexOf_iff, hc]

private theorem Iso.apply_coreRot (x : (G.core : Set H)) :
    θ.toEquiv (G.coreRot x) =
      G'.coreRot ⟨θ.toEquiv x, mem_coe.2 (θ.apply_mem_core_iff.2 (mem_coe.1 x.2))⟩ :=
  coe_firstReturn_of_semiconj θ.toEquiv θ.map_rot (fun _ => θ.apply_mem_core_iff) x

private theorem Iso.apply_walkStep (x : H) :
    θ.toEquiv (G.walkStep x) = G'.walkStep (θ.toEquiv x) := by
  by_cases hx : x ∈ G.core
  · rw [walkStep_of_mem hx, walkStep_of_mem (θ.apply_mem_core_iff.2 hx), θ.map_inv,
      θ.apply_coreRot]
  · rw [walkStep_of_notMem hx, walkStep_of_notMem (mt θ.apply_mem_core_iff.1 hx)]

private theorem Iso.apply_skeletonInvFun (x : (G.skeletonDarts : Set H)) :
    θ.toEquiv (G.skeletonInvFun x) = G'.skeletonInvFun
      ⟨θ.toEquiv x, mem_coe.2 (θ.apply_mem_skeletonDarts_iff.2 (mem_coe.1 x.2))⟩ := by
  symm
  apply coe_skeletonInvFun_eq_of_firstHit
  have h := (firstHit_skeletonInvFun x).map θ.toEquiv θ.apply_walkStep
    fun _ => θ.apply_mem_skeletonDarts_iff
  rwa [θ.map_inv] at h

/-- The bijection between the darts of the skeletons induced by an isomorphism. -/
private def Iso.skeletonEquiv : (G.skeletonDarts : Set H) ≃ (G'.skeletonDarts : Set H') where
  toFun x := ⟨θ.toEquiv x, mem_coe.2 (θ.apply_mem_skeletonDarts_iff.2 (mem_coe.1 x.2))⟩
  invFun y := ⟨θ.toEquiv.symm y, mem_coe.2 (θ.apply_mem_skeletonDarts_iff.1
    (by rw [Equiv.apply_symm_apply]; exact mem_coe.1 y.2))⟩
  left_inv x := Subtype.ext (θ.toEquiv.symm_apply_apply x)
  right_inv y := Subtype.ext (θ.toEquiv.apply_symm_apply y)

/-- An isomorphism of plabic graphs induces an isomorphism of their skeletons. -/
private noncomputable def Iso.skeletonIso (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) :
    (G.skeleton hG).Iso (G'.skeleton hG') :=
  isoOfMapLeg θ.skeletonEquiv
    (fun x => Subtype.ext (by
      change θ.toEquiv (G.skeletonInvFun x) = (G'.skeletonInvFun _ : H')
      rw [θ.apply_skeletonInvFun]
      rfl))
    (fun x => Subtype.ext (by
      change θ.toEquiv (firstReturn G.rot _ x) = (firstReturn G'.rot _ _ : H')
      exact coe_firstReturn_of_semiconj θ.toEquiv θ.map_rot
        (fun _ => θ.apply_mem_skeletonDarts_iff) x))
    (fun x => by
      rw [mem_skeleton_bdry, mem_skeleton_bdry]
      exact θ.mem_bdry_iff x)
    (fun x hx => θ.map_colour x ((isBoundaryVertex_skeleton_vertexOf_iff hG x).not.1 hx))
    (fun i => Subtype.ext (by
      change θ.toEquiv ((G.skeleton hG).leg i : H) = _
      rw [coe_skeleton_leg, coe_skeleton_leg, ← θ.map_leg hG hG' i]
      by_cases h : G.leg i ∈ G.skeletonDarts
      · rw [if_pos h, if_pos (θ.apply_mem_skeletonDarts_iff.2 h)]
      · rw [if_neg h, if_neg (mt θ.apply_mem_skeletonDarts_iff.1 h), θ.map_rot]))

end SkeletonIso

/-- Isomorphic plabic graphs have isomorphic skeletons. -/
theorem Isomorphic.skeleton {G' : PlabicData H' b} (hG : G.IsPlabicGraph)
    (hG' : G'.IsPlabicGraph) (h : G.Isomorphic G') : (G.skeleton hG).Isomorphic (G'.skeleton hG') :=
  h.elim fun θ => ⟨θ.skeletonIso hG hG'⟩

/-! ### Contracting an edge: the core rotation and the darts of the skeleton -/

/-- In a plabic graph, `σ(g_i)` lies in `B`. -/
private theorem rot_leg_mem_bdry (hG : G.IsPlabicGraph) (i : Fin b) :
    G.rot (G.leg i) ∈ G.bdry := by
  have hb := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  by_contra h
  exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hb
    (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hb (G.rot_mem_vertexOf _)
      (G.self_mem_vertexOf _) h (hG.leg_notMem_bdry i))

section SkeletonContractEdge

variable {d : H} {hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)}
  (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)

include hG he in
private theorem mem_contractEdge_core_iff {y : (({d, G.inv d} : Set H)ᶜ : Set H)} :
    y ∈ (G.contractEdge d hleg).core ↔ (y : H) ∈ G.core := by
  rw [← mem_map' (Embedding.subtype _), map_core_contractEdge hG he, mem_sdiff]
  have := mem_compl_pair_iff.1 y.2
  simp only [Embedding.coe_subtype, mem_insert, mem_singleton, not_or]
  exact and_iff_left this

include hG he in
/-- The core rotation of the contraction is the first return of `τ = σ ∘ (d d̄)` to
`K(G) \ {d, d̄}`. -/
private theorem coe_contractEdge_coreRot
    (u : ((G.contractEdge d hleg).core : Set (({d, G.inv d} : Set H)ᶜ : Set H))) :
    (((G.contractEdge d hleg).coreRot u : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      firstReturn (G.rot * swap d (G.inv d))
        ((G.core : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H))
        ⟨((u : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
          ⟨mem_coe.2 ((mem_contractEdge_core_iff hG he).1 (mem_coe.1 u.2)),
            (u : (({d, G.inv d} : Set H)ᶜ : Set H)).2⟩⟩ :=
  coe_firstReturn_firstReturnPerm _ Set.inter_subset_right
    (fun v => mem_coe.trans ((mem_contractEdge_core_iff hG he).trans
      ⟨fun h => ⟨mem_coe.2 h, v.2⟩, fun h => mem_coe.1 h.1⟩)) u

/-- The rotation of the skeleton of the contraction is the first return of `τ = σ ∘ (d d̄)` to
its darts. -/
private theorem coe_contractEdge_skeleton_rot {Z : Set H}
    (hZ : ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H),
      u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ Z)
    (hZY : Z ⊆ (({d, G.inv d} : Set H)ᶜ : Set H)) (hGc : (G.contractEdge d hleg).IsPlabicGraph)
    (x : ((G.contractEdge d hleg).skeletonDarts : Set (({d, G.inv d} : Set H)ᶜ : Set H))) :
    ((((G.contractEdge d hleg).skeleton hGc).rot x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      firstReturn (G.rot * swap d (G.inv d)) Z
        ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H), (hZ _).1 (mem_coe.1 x.2)⟩ :=
  coe_firstReturn_firstReturnPerm _ hZY (fun v => mem_coe.trans (hZ v)) x

include hG in
private theorem coe_contractEdge_walkStep {u : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hu : u ∈ (G.contractEdge d hleg).core) :
    (((G.contractEdge d hleg).walkStep u : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      G.inv (((G.contractEdge d hleg).coreRot ⟨u, mem_coe.2 hu⟩ :
        (({d, G.inv d} : Set H)ᶜ : Set H)) : H) := by
  rw [walkStep_of_mem hu, coe_contractEdge_inv hG.inv_involutive]

/-- At a dart `x` of the core whose vertex has at least two darts of the core, `σ_K x ≠ x`. -/
private theorem coreRot_ne_self {x : (G.core : Set H)} (h : 2 ≤ #(G.vertexOf x ∩ G.core)) :
    (G.coreRot x : H) ≠ x := by
  intro hx
  obtain ⟨y, hy, hyx⟩ := exists_mem_ne h x
  have hfix : G.coreRot x = x := Subtype.ext hx
  have hs : G.coreRot.SameCycle x ⟨y, mem_coe.2 (mem_inter.1 hy).2⟩ :=
    sameCycle_coreRot_iff.2 (G.mem_vertexOf.1 (mem_inter.1 hy).1)
  exact hyx (congrArg Subtype.val (hs.eq_of_left hfix).symm)

include hG in
private theorem inv_notMem_core_of_notMem (hdK : d ∉ G.core) : G.inv d ∉ G.core :=
  fun h => hdK (by
    have := DiskMap.inv_mem_core h
    rwa [hG.inv_involutive] at this)

include hG he in
/-- Not both endpoints of an edge outside the core meet the core. -/
private theorem forall_notMem_core_of_notMem (hdK : d ∉ G.core) :
    (∀ w, G.rot.SameCycle d w → w ∉ G.core) ∨
      ∀ w, G.rot.SameCycle (G.inv d) w → w ∉ G.core := by
  by_contra hc
  simp only [not_or, not_forall, not_not] at hc
  obtain ⟨⟨a, ha, haK⟩, ⟨c, hc, hcK⟩⟩ := hc
  have hinv := hG.inv_involutive
  have hdK' := inv_notMem_core_of_notMem hG hdK
  have hS : G.IsCoreLike (insert d (insert (G.inv d) G.core)) := by
    refine ⟨fun x hx => mem_insert_of_mem (mem_insert_of_mem (hG.bdry_subset_core hx)),
      fun x hx => ?_, fun v hv => ?_⟩
    · rcases mem_insert.1 hx with rfl | hx
      · exact mem_insert_of_mem (mem_insert_self _ _)
      rcases mem_insert.1 hx with rfl | hx
      · rw [hinv]
        exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_of_mem (DiskMap.inv_mem_core hx))
    · rintro ⟨z, hzv, hzS⟩
      obtain ⟨w, rfl⟩ := G.mem_vertices.1 hv
      rw [← G.vertexOf_eq_of_mem hzv]
      rcases mem_insert.1 hzS with rfl | hzS
      · have had : a ≠ z := fun h => hdK (h ▸ haK)
        refine (card_pair had.symm).symm.le.trans (card_le_card fun e he' => ?_)
        rcases mem_insert.1 he' with rfl | he'
        · exact mem_inter.2 ⟨G.self_mem_vertexOf _, mem_insert_self _ _⟩
        · rw [mem_singleton.1 he']
          exact mem_inter.2 ⟨G.mem_vertexOf.2 ha, mem_insert_of_mem (mem_insert_of_mem haK)⟩
      rcases mem_insert.1 hzS with rfl | hzS
      · have hcd : c ≠ G.inv d := fun h => hdK' (h ▸ hcK)
        refine (card_pair hcd.symm).symm.le.trans (card_le_card fun e he' => ?_)
        rcases mem_insert.1 he' with rfl | he'
        · exact mem_inter.2 ⟨G.self_mem_vertexOf _, mem_insert_of_mem (mem_insert_self _ _)⟩
        · rw [mem_singleton.1 he']
          exact mem_inter.2 ⟨G.mem_vertexOf.2 hc, mem_insert_of_mem (mem_insert_of_mem hcK)⟩
      · exact (DiskMap.two_le_card_vertexOf_inter_core hzS).trans (card_le_card
          (inter_subset_inter_left (fun e he' => mem_insert_of_mem (mem_insert_of_mem he'))))
  exact hdK (hS.subset_core (mem_insert_self _ _))

include hG he in
/-- If the edge is outside the core, `τ = σ ∘ (d d̄)` and `σ` have the same first hits of any
subset `Z` of the core. -/
private theorem firstHit_contract_of_notMem (hdK : d ∉ G.core) {Z : Set H}
    (hZ : Z ⊆ (G.core : Set H)) {x z : H} (h : FirstHit G.rot (· ∈ Z) x z) :
    FirstHit (G.rot * swap d (G.inv d)) (· ∈ Z) x z := by
  have hdK' := inv_notMem_core_of_notMem hG hdK
  rcases forall_notMem_core_of_notMem hG he hdK with h1 | h1
  · exact h.mul_swap (fun w hw hwZ => h1 w hw (hZ hwZ)) (fun h' => hdK' (hZ h'))
      he.not_sameCycle
  · rw [swap_comm]
    exact h.mul_swap (fun w hw hwZ => h1 w hw (hZ hwZ)) (fun h' => hdK (hZ h'))
      fun h' => he.not_sameCycle h'.symm

/-! #### An edge outside the core -/

section NotMem

variable (hdK : d ∉ G.core)

include hG hdK in
private theorem mem_compl_pair_of_mem_core' {x : H} (hx : x ∈ G.core) :
    x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) :=
  mem_compl_pair_iff.2
    ⟨fun h => hdK (h ▸ hx), fun h => inv_notMem_core_of_notMem hG hdK (h ▸ hx)⟩

include hG he hdK in
private theorem map_core_contractEdge_of_notMem :
    (G.contractEdge d hleg).core.map (Embedding.subtype _) = G.core := by
  rw [map_core_contractEdge hG he]
  refine sdiff_eq_self_of_disjoint (disjoint_left.2 fun x hx hx' => ?_)
  exact mem_compl_pair_iff.1 (mem_compl_pair_of_mem_core' hG hdK hx)
    |>.elim (fun h1 h2 => by
      rcases mem_insert.1 hx' with h | h
      · exact h1 h
      · exact h2 (mem_singleton.1 h))

include hG he hdK in
private theorem card_contractEdge_vertexOf_inter_core_of_notMem
    {u : (({d, G.inv d} : Set H)ᶜ : Set H)} (hu : (u : H) ∈ G.core) :
    #((G.contractEdge d hleg).vertexOf u ∩ (G.contractEdge d hleg).core) =
      #(G.vertexOf u ∩ G.core) := by
  rw [← card_map (Embedding.subtype _), map_inter, map_core_contractEdge_of_notMem hG he hdK]
  by_cases hU : (u : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
  · rw [map_vertexOf_contractEdge_of_mem he.not_sameCycle hU]
    congr 1
    have hinv := hG.inv_involutive
    rcases forall_notMem_core_of_notMem hG he hdK with h1 | h1
    · have hUy : (u : H) ∈ G.vertexOf (G.inv d) :=
        (mem_union.1 hU).resolve_left fun h => h1 _ (G.mem_vertexOf.1 h) hu
      rw [G.vertexOf_eq_of_mem hUy]
      ext e
      simp only [mem_inter, mem_mergedVertex]
      constructor
      · rintro ⟨⟨h | h, -, -⟩, heK⟩
        · exact absurd heK (h1 _ (G.mem_vertexOf.1 h))
        · exact ⟨h, heK⟩
      · rintro ⟨h, heK⟩
        exact ⟨⟨Or.inr h, fun h' => hdK (h' ▸ heK), fun h' => (mem_compl_pair_iff.1
          (mem_compl_pair_of_mem_core' hG hdK heK)).2 h'⟩, heK⟩
    · have hUx : (u : H) ∈ G.vertexOf d :=
        (mem_union.1 hU).resolve_right fun h => h1 _ (G.mem_vertexOf.1 h) hu
      rw [G.vertexOf_eq_of_mem hUx]
      ext e
      simp only [mem_inter, mem_mergedVertex]
      constructor
      · rintro ⟨⟨h | h, -, -⟩, heK⟩
        · exact ⟨h, heK⟩
        · exact absurd heK (h1 _ (G.mem_vertexOf.1 h))
      · rintro ⟨h, heK⟩
        exact ⟨⟨Or.inl h, fun h' => hdK (h' ▸ heK), fun h' => (mem_compl_pair_iff.1
          (mem_compl_pair_of_mem_core' hG hdK heK)).2 h'⟩, heK⟩
  · rw [map_vertexOf_contractEdge_of_notMem he.not_sameCycle hU]

include hG he hdK in
private theorem mem_contractEdge_skeletonDarts_iff_of_notMem
    {u : (({d, G.inv d} : Set H)ᶜ : Set H)} :
    u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ G.skeletonDarts := by
  simp only [skeletonDarts, mem_filter, mem_contractEdge_core_iff hG he,
    isBoundaryVertex_vertexOf_contractEdge_iff he]
  exact and_congr_right fun hu => by
    rw [card_contractEdge_vertexOf_inter_core_of_notMem hG he hdK hu]

include hG he hdK in
private theorem coe_contractEdge_coreRot_of_notMem
    (u : ((G.contractEdge d hleg).core : Set (({d, G.inv d} : Set H)ᶜ : Set H))) :
    (((G.contractEdge d hleg).coreRot u : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      G.coreRot ⟨((u : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
        mem_coe.2 ((mem_contractEdge_core_iff hG he).1 (mem_coe.1 u.2))⟩ := by
  have hu := (mem_contractEdge_core_iff hG he).1 (mem_coe.1 u.2)
  rw [coe_contractEdge_coreRot hG he, coe_firstReturn_eq_iff]
  have hY := mem_compl_pair_iff.1 (u : (({d, G.inv d} : Set H)ᶜ : Set H)).2
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hY.1 hY.2]
  have h := firstHit_contract_of_notMem hG he hdK (Subset.refl _)
    (firstHit_firstReturn G.rot (G.core : Set H) ⟨_, mem_coe.2 hu⟩)
  refine h.transfer (fun _ => True) (fun _ _ _ => trivial) (fun w _ hw => ⟨rfl, fun h' => hw h'.1⟩)
    ⟨(firstHit_firstReturn G.rot (G.core : Set H) ⟨_, mem_coe.2 hu⟩).prop,
      mem_compl_pair_of_mem_core' hG hdK (mem_coe.1
        (firstHit_firstReturn G.rot (G.core : Set H) ⟨_, mem_coe.2 hu⟩).prop)⟩ trivial

include hG he hdK in
private theorem coe_contractEdge_walkStep_of_notMem (u : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (((G.contractEdge d hleg).walkStep u : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      G.walkStep u := by
  by_cases hu : u ∈ (G.contractEdge d hleg).core
  · rw [coe_contractEdge_walkStep hG hu, coe_contractEdge_coreRot_of_notMem hG he hdK,
      walkStep_of_mem ((mem_contractEdge_core_iff hG he).1 hu)]
  · rw [walkStep_of_notMem hu, walkStep_of_notMem (mt (mem_contractEdge_core_iff hG he).2 hu)]

/-- If the edge is outside the core, the identification of the darts of the skeletons of the
contraction and of `G` is an isomorphism. -/
private noncomputable def skeletonContractEdgeIsoOfNotMem
    (hGc : (G.contractEdge d hleg).IsPlabicGraph) :
    ((G.contractEdge d hleg).skeleton hGc).Iso (G.skeleton hG) :=
  isoOfMapLeg
    { toFun := fun x => ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
        mem_coe.2 ((mem_contractEdge_skeletonDarts_iff_of_notMem hG he hdK).1 x.2)⟩
      invFun := fun y => ⟨⟨y, mem_compl_pair_of_mem_core' hG hdK
          (mem_core_of_mem_skeletonDarts y.2)⟩,
        mem_coe.2 ((mem_contractEdge_skeletonDarts_iff_of_notMem hG he hdK).2 y.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun x => Subtype.ext (by
      change ((((G.contractEdge d hleg).skeletonInvFun x :
        (({d, G.inv d} : Set H)ᶜ : Set H))) : H) = (G.skeletonInvFun _ : H)
      symm
      apply coe_skeletonInvFun_eq_of_firstHit
      have h := (firstHit_skeletonInvFun x).map Subtype.val
        (coe_contractEdge_walkStep_of_notMem hG he hdK)
        fun u => (mem_contractEdge_skeletonDarts_iff_of_notMem hG he hdK).symm
      rwa [coe_contractEdge_inv hG.inv_involutive] at h))
    (fun x => Subtype.ext (by
      change ((((G.contractEdge d hleg).skeleton hGc).rot x :
        (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = (firstReturn G.rot _ _ : H)
      rw [coe_contractEdge_skeleton_rot (Z := (G.skeletonDarts : Set H))
        (fun u => (mem_contractEdge_skeletonDarts_iff_of_notMem hG he hdK).trans mem_coe.symm)
        (fun y hy => mem_compl_pair_of_mem_core' hG hdK
          (mem_core_of_mem_skeletonDarts (mem_coe.1 hy))) hGc, coe_firstReturn_eq_iff]
      have hY := mem_compl_pair_iff.1 (x : (({d, G.inv d} : Set H)ᶜ : Set H)).2
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hY.1 hY.2]
      exact firstHit_contract_of_notMem hG he hdK
        (fun y hy => mem_coe.2 (mem_core_of_mem_skeletonDarts (mem_coe.1 hy)))
        (firstHit_firstReturn G.rot (G.skeletonDarts : Set H)
          ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
            mem_coe.2 ((mem_contractEdge_skeletonDarts_iff_of_notMem hG he hdK).1 x.2)⟩)))
    (fun x => by
      rw [mem_skeleton_bdry, mem_skeleton_bdry, mem_contractEdge_bdry]
      rfl)
    (fun _ _ => rfl)
    (fun i => Subtype.ext (by
      change ((((G.contractEdge d hleg).skeleton hGc).leg i :
        (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = _
      rw [coe_skeleton_leg, coe_skeleton_leg]
      by_cases h : G.leg i ∈ G.skeletonDarts
      · rw [if_pos ((mem_contractEdge_skeletonDarts_iff_of_notMem hG he hdK).2 h), if_pos h]
        rfl
      · rw [if_neg (mt (mem_contractEdge_skeletonDarts_iff_of_notMem hG he hdK).1 h), if_neg h,
          coe_contractEdge_rot_of_mem]
        · rfl
        · exact he.mem_of_mem_bdry (rot_leg_mem_bdry hG i)))

end NotMem

/-! #### Darts of the skeleton of the contraction -/

private theorem firstHit_coreRot (x : (G.core : Set H)) :
    FirstHit G.rot (· ∈ (G.core : Set H)) (G.rot x) (G.coreRot x) :=
  firstHit_firstReturn G.rot _ x

private theorem mem_vertexOf_of_coreRot_eq {w x : H} (hw : w ∈ G.core)
    (h : (G.coreRot ⟨w, mem_coe.2 hw⟩ : H) = x) : w ∈ G.vertexOf x := by
  subst h
  exact G.mem_vertexOf.2 (sameCycle_coreRot_apply _).symm

private theorem mem_skeletonDarts_iff_of_mem_vertexOf {x y : H} (hx : x ∈ G.vertexOf y)
    (hy : ¬G.IsBoundaryVertex (G.vertexOf y)) :
    x ∈ G.skeletonDarts ↔ x ∈ G.core ∧ 3 ≤ #(G.vertexOf y ∩ G.core) := by
  rw [skeletonDarts, mem_filter, G.vertexOf_eq_of_mem hx]
  exact and_congr_right fun _ => or_iff_right hy

include hG he in
private theorem mem_contractEdge_skeletonDarts_iff_of_notMem_union
    {u : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hU : (u : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ G.skeletonDarts := by
  have hc : #((G.contractEdge d hleg).vertexOf u ∩ (G.contractEdge d hleg).core) =
      #(G.vertexOf u ∩ G.core) := by
    rw [← card_map (Embedding.subtype _), map_inter,
      map_vertexOf_contractEdge_of_notMem he.not_sameCycle hU, map_core_contractEdge hG he]
    congr 1
    ext e
    simp only [mem_inter, mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, fun h => ?_⟩
      have := notMem_union_of_mem_vertexOf hU h1
      rcases h with h | h <;> rw [h] at this
      · exact this (mem_union_left _ (G.self_mem_vertexOf _))
      · exact this (mem_union_right _ (G.self_mem_vertexOf _))
  simp only [skeletonDarts, mem_filter, mem_contractEdge_core_iff hG he,
    isBoundaryVertex_vertexOf_contractEdge_iff he, hc]

section MemCore

variable (hdK : d ∈ G.core)

include hdK in
private theorem firstHit_tau_of_mem {Z : Set H} (hZ : Z ⊆ (G.core : Set H)) {w0 z : H}
    (h : FirstHit G.rot (· ∈ (G.core : Set H)) w0 z) (hz : z ∈ Z) :
    FirstHit (G.rot * swap d (G.inv d)) (· ∈ Z) w0 z := by
  have hdK' : G.inv d ∈ G.core := DiskMap.inv_mem_core hdK
  refine h.transfer (fun _ => True) (fun _ _ _ => trivial)
    (fun w _ hw => ⟨?_, fun h' => hw (hZ h')⟩) hz trivial
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne (fun h' => hw (by rw [h']; exact mem_coe.2 hdK))
    (fun h' => hw (by rw [h']; exact mem_coe.2 hdK'))]

include hdK in
private theorem coe_firstReturn_tau_of_ne {x : H}
    (hx : x ∈ (G.core : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H))
    (h1 : (G.coreRot ⟨x, hx.1⟩ : H) ≠ d) (h2 : (G.coreRot ⟨x, hx.1⟩ : H) ≠ G.inv d) :
    (firstReturn (G.rot * swap d (G.inv d))
      ((G.core : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H)) ⟨x, hx⟩ : H) =
      G.coreRot ⟨x, hx.1⟩ := by
  rw [coe_firstReturn_eq_iff]
  have hY := mem_compl_pair_iff.1 hx.2
  change FirstHit _ _ ((G.rot * swap d (G.inv d)) x) _
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hY.1 hY.2]
  exact firstHit_tau_of_mem hdK Set.inter_subset_left (firstHit_coreRot ⟨x, hx.1⟩)
    ⟨(firstHit_coreRot ⟨x, hx.1⟩).prop, mem_compl_pair_iff.2 ⟨h1, h2⟩⟩

include he hdK in
private theorem coreRot_inv_mem_compl_pair :
    (G.coreRot ⟨G.inv d, mem_coe.2 (DiskMap.inv_mem_core hdK)⟩ : H) ∈
      (({d, G.inv d} : Set H)ᶜ : Set H) := by
  refine mem_compl_pair_iff.2 ⟨fun h => ?_, coreRot_ne_self
    (DiskMap.two_le_card_vertexOf_inter_core (DiskMap.inv_mem_core hdK))⟩
  have := sameCycle_coreRot_apply ⟨G.inv d, mem_coe.2 (DiskMap.inv_mem_core hdK)⟩
  rw [h] at this
  exact notMem_vertexOf_inv_of_mem he (G.self_mem_vertexOf d) (G.mem_vertexOf.2 this)

include he hdK in
private theorem coreRot_mem_compl_pair :
    (G.coreRot ⟨d, mem_coe.2 hdK⟩ : H) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
  refine mem_compl_pair_iff.2 ⟨coreRot_ne_self (DiskMap.two_le_card_vertexOf_inter_core hdK),
    fun h => ?_⟩
  have := sameCycle_coreRot_apply ⟨d, mem_coe.2 hdK⟩
  rw [h] at this
  exact notMem_vertexOf_inv_of_mem he (G.mem_vertexOf.2 this)
    (G.self_mem_vertexOf _)

include he hdK in
private theorem coe_firstReturn_tau_of_eq {x : H}
    (hx : x ∈ (G.core : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H))
    (h1 : (G.coreRot ⟨x, hx.1⟩ : H) = d) :
    (firstReturn (G.rot * swap d (G.inv d))
      ((G.core : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H)) ⟨x, hx⟩ : H) =
      G.coreRot ⟨G.inv d, mem_coe.2 (DiskMap.inv_mem_core hdK)⟩ := by
  rw [coe_firstReturn_eq_iff]
  have hY := mem_compl_pair_iff.1 hx.2
  change FirstHit _ _ ((G.rot * swap d (G.inv d)) x) _
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hY.1 hY.2]
  have hs := firstHit_coreRot ⟨x, hx.1⟩
  rw [h1] at hs
  refine (firstHit_tau_of_mem hdK (Subset.refl _) hs (mem_coe.2 hdK)).trans ?_
    (fun w hw => hw.1)
  refine .step (fun h => (mem_compl_pair_iff.1 h.2).1 rfl) ?_
  rw [Perm.mul_apply, swap_apply_left]
  have hs' := firstHit_coreRot ⟨G.inv d, mem_coe.2 (DiskMap.inv_mem_core hdK)⟩
  exact firstHit_tau_of_mem hdK Set.inter_subset_left hs'
    ⟨hs'.prop, coreRot_inv_mem_compl_pair he hdK⟩

include he hdK in
private theorem coe_firstReturn_tau_of_eq_inv {x : H}
    (hx : x ∈ (G.core : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H))
    (h2 : (G.coreRot ⟨x, hx.1⟩ : H) = G.inv d) :
    (firstReturn (G.rot * swap d (G.inv d))
      ((G.core : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H)) ⟨x, hx⟩ : H) =
      G.coreRot ⟨d, mem_coe.2 hdK⟩ := by
  rw [coe_firstReturn_eq_iff]
  have hY := mem_compl_pair_iff.1 hx.2
  change FirstHit _ _ ((G.rot * swap d (G.inv d)) x) _
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hY.1 hY.2]
  have hs := firstHit_coreRot ⟨x, hx.1⟩
  rw [h2] at hs
  refine (firstHit_tau_of_mem hdK (Subset.refl _) hs
    (mem_coe.2 (DiskMap.inv_mem_core hdK))).trans ?_ (fun w hw => hw.1)
  refine .step (fun h => (mem_compl_pair_iff.1 h.2).2 rfl) ?_
  rw [Perm.mul_apply, swap_apply_right]
  have hs' := firstHit_coreRot ⟨d, mem_coe.2 hdK⟩
  exact firstHit_tau_of_mem hdK Set.inter_subset_left hs'
    ⟨hs'.prop, coreRot_mem_compl_pair he hdK⟩

include hG he hdK in
/-- The walk step of the contraction, when the edge lies in the core. -/
private theorem coe_contractEdge_walkStep_of_mem {u : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hu : (u : H) ∈ G.core) :
    (((G.contractEdge d hleg).walkStep u : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      if (G.coreRot ⟨u, mem_coe.2 hu⟩ : H) = d then
        G.walkStep (G.inv d)
      else if (G.coreRot ⟨u, mem_coe.2 hu⟩ : H) = G.inv d then G.walkStep d
      else G.walkStep u := by
  have hu' : u ∈ (G.contractEdge d hleg).core := (mem_contractEdge_core_iff hG he).2 hu
  rw [coe_contractEdge_walkStep hG hu', coe_contractEdge_coreRot hG he,
    walkStep_of_mem hu, walkStep_of_mem hdK, walkStep_of_mem (DiskMap.inv_mem_core hdK)]
  split_ifs with h1 h2
  · rw [coe_firstReturn_tau_of_eq he hdK _ h1]
  · rw [coe_firstReturn_tau_of_eq_inv he hdK _ h2]
  · rw [coe_firstReturn_tau_of_ne hdK _ h1 h2]

include hG he hdK in
private theorem card_contractEdge_vertexOf_inter_core_add_two
    {u : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hU : (u : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    #((G.contractEdge d hleg).vertexOf u ∩ (G.contractEdge d hleg).core) + 2 =
      #(G.vertexOf d ∩ G.core) + #(G.vertexOf (G.inv d) ∩ G.core) := by
  rw [← card_map (Embedding.subtype _), map_inter,
    map_vertexOf_contractEdge_of_mem he.not_sameCycle hU, map_core_contractEdge hG he]
  have hdK' := DiskMap.inv_mem_core hdK
  have hdisj : Disjoint (G.vertexOf d ∩ G.core) (G.vertexOf (G.inv d) ∩ G.core) :=
    disjoint_left.2 fun e h1 h2 =>
      notMem_vertexOf_inv_of_mem he (mem_inter.1 h1).1 (mem_inter.1 h2).1
  have hpair : #({d, G.inv d} : Finset H) = 2 := card_pair (hG.inv_ne d).symm
  have hdisj2 : Disjoint (G.mergedVertex d ∩ (G.core \ {d, G.inv d})) {d, G.inv d} :=
    disjoint_left.2 fun e h1 h2 => (mem_sdiff.1 (mem_inter.1 h1).2).2 h2
  rw [← card_union_of_disjoint hdisj, ← hpair, ← card_union_of_disjoint hdisj2]
  congr 1
  ext e
  simp only [mem_union, mem_inter, mem_mergedVertex, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro (⟨⟨h | h, -, -⟩, heK, -⟩ | h | h)
    · exact Or.inl ⟨h, heK⟩
    · exact Or.inr ⟨h, heK⟩
    · rw [h]
      exact Or.inl ⟨G.self_mem_vertexOf _, hdK⟩
    · rw [h]
      exact Or.inr ⟨G.self_mem_vertexOf _, hdK'⟩
  · rintro (⟨h, heK⟩ | ⟨h, heK⟩)
    · by_cases h1 : e = d
      · exact Or.inr (Or.inl h1)
      by_cases h2 : e = G.inv d
      · exact Or.inr (Or.inr h2)
      exact Or.inl ⟨⟨Or.inl h, h1, h2⟩, heK, fun h' => h'.elim h1 h2⟩
    · by_cases h1 : e = d
      · exact Or.inr (Or.inl h1)
      by_cases h2 : e = G.inv d
      · exact Or.inr (Or.inr h2)
      exact Or.inl ⟨⟨Or.inr h, h1, h2⟩, heK, fun h' => h'.elim h1 h2⟩

include hG he hdK in
private theorem mem_contractEdge_skeletonDarts_iff_of_mem_union
    {u : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (hU : (u : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    u ∈ (G.contractEdge d hleg).skeletonDarts ↔
      (u : H) ∈ G.core ∧ 5 ≤ #(G.vertexOf d ∩ G.core) + #(G.vertexOf (G.inv d) ∩ G.core) := by
  have hb : ¬(G.contractEdge d hleg).IsBoundaryVertex ((G.contractEdge d hleg).vertexOf u) := by
    rw [isBoundaryVertex_vertexOf_contractEdge_iff he]
    exact fun h => he.notMem_of_isBoundaryVertex h hU
  have hc := card_contractEdge_vertexOf_inter_core_add_two hG he hdK (hleg := hleg) hU
  simp only [skeletonDarts, mem_filter, mem_contractEdge_core_iff hG he]
  constructor
  · rintro ⟨hu, h | h⟩
    · exact absurd h hb
    · exact ⟨hu, by omega⟩
  · rintro ⟨hu, h⟩
    exact ⟨hu, Or.inr (by omega)⟩

/-- The identification of the darts of `Γ(G^c)` with those of `Γ(G)`, when they have the same
darts and the same rotations and involutions. -/
private noncomputable def skeletonContractEdgeIsoOfEq
    (hGc : (G.contractEdge d hleg).IsPlabicGraph)
    (hR : ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H),
      u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ G.skeletonDarts)
    (hRY : ∀ x ∈ G.skeletonDarts, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
    (hinvc : ∀ x : ((G.contractEdge d hleg).skeletonDarts :
        Set (({d, G.inv d} : Set H)ᶜ : Set H)),
      (((G.contractEdge d hleg).skeletonInvFun x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
        G.skeletonInvFun ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
          mem_coe.2 ((hR _).1 (mem_coe.1 x.2))⟩)
    (hrot : ∀ x : (G.skeletonDarts : Set H),
      (firstReturn (G.rot * swap d (G.inv d)) (G.skeletonDarts : Set H) x : H) =
        firstReturn G.rot (G.skeletonDarts : Set H) x) :
    ((G.contractEdge d hleg).skeleton hGc).Iso (G.skeleton hG) :=
  isoOfMapLeg
    { toFun := fun x => ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
        mem_coe.2 ((hR _).1 (mem_coe.1 x.2))⟩
      invFun := fun y => ⟨⟨y, hRY y (mem_coe.1 y.2)⟩, mem_coe.2 ((hR _).2 (mem_coe.1 y.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun x => Subtype.ext (by
      change ((((G.contractEdge d hleg).skeletonInvFun x :
        (({d, G.inv d} : Set H)ᶜ : Set H))) : H) = (G.skeletonInvFun _ : H)
      rw [hinvc]
      rfl))
    (fun x => Subtype.ext (by
      change ((((G.contractEdge d hleg).skeleton hGc).rot x :
        (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = (firstReturn G.rot _ _ : H)
      rw [coe_contractEdge_skeleton_rot (Z := (G.skeletonDarts : Set H))
        (fun u => (hR u).trans mem_coe.symm) (fun y hy => hRY y (mem_coe.1 hy)) hGc]
      exact hrot ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
        mem_coe.2 ((hR _).1 (mem_coe.1 x.2))⟩))
    (fun x => by
      rw [mem_skeleton_bdry, mem_skeleton_bdry, mem_contractEdge_bdry]
      rfl)
    (fun _ _ => rfl)
    (fun i => Subtype.ext (by
      change ((((G.contractEdge d hleg).skeleton hGc).leg i :
        (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = _
      rw [coe_skeleton_leg, coe_skeleton_leg]
      by_cases h : G.leg i ∈ G.skeletonDarts
      · rw [if_pos ((hR _).2 h), if_pos h]
        rfl
      · rw [if_neg (mt (hR _).1 h), if_neg h, coe_contractEdge_rot_of_mem]
        · rfl
        · exact he.mem_of_mem_bdry (rot_leg_mem_bdry hG i)))

/-! #### Both endpoints with exactly two core darts -/

include hG he hdK in
private theorem skeleton_contractEdge_isomorphic_of_two_two
    (hX : #(G.vertexOf d ∩ G.core) = 2) (hY : #(G.vertexOf (G.inv d) ∩ G.core) = 2)
    (hGc : (G.contractEdge d hleg).IsPlabicGraph) :
    ((G.contractEdge d hleg).skeleton hGc).Isomorphic (G.skeleton hG) := by
  have hinv := hG.inv_involutive
  have hdK' := DiskMap.inv_mem_core hdK
  have hXR : ∀ w ∈ G.vertexOf d, w ∉ G.skeletonDarts := fun w hw h => by
    have := ((mem_skeletonDarts_iff_of_mem_vertexOf hw he.not_isBoundaryVertex).1 h).2
    omega
  have hYR : ∀ w ∈ G.vertexOf (G.inv d), w ∉ G.skeletonDarts := fun w hw h => by
    have := ((mem_skeletonDarts_iff_of_mem_vertexOf hw he.not_isBoundaryVertex_inv).1 h).2
    omega
  have hR : ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H),
      u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ G.skeletonDarts := by
    intro u
    by_cases hU : (u : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · rw [mem_contractEdge_skeletonDarts_iff_of_mem_union hG he hdK hU, hX, hY]
      constructor
      · rintro ⟨-, h⟩
        omega
      · intro h
        rcases mem_union.1 hU with h' | h'
        · exact absurd h (hXR _ h')
        · exact absurd h (hYR _ h')
    · exact mem_contractEdge_skeletonDarts_iff_of_notMem_union hG he hU
  have hRY : ∀ x ∈ G.skeletonDarts, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := fun x hx =>
    mem_compl_pair_iff.2 ⟨fun h => hXR x (h ▸ G.self_mem_vertexOf d) hx,
      fun h => hYR x (h ▸ G.self_mem_vertexOf _) hx⟩
  -- the walks of `G^c` are those of `G` with the terms `d`, `d̄` deleted
  have claim : ∀ w t, FirstHit G.walkStep (· ∈ G.skeletonDarts) w t →
      (∀ u : (({d, G.inv d} : Set H)ᶜ : Set H), (u : H) = w →
        ∃ t' : (({d, G.inv d} : Set H)ᶜ : Set H), (t' : H) = t ∧
          FirstHit (G.contractEdge d hleg).walkStep
            (· ∈ (G.contractEdge d hleg).skeletonDarts) u t') ∧
      (w = d → ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H), (u : H) = G.walkStep d →
        ∃ t' : (({d, G.inv d} : Set H)ᶜ : Set H), (t' : H) = t ∧
          FirstHit (G.contractEdge d hleg).walkStep
            (· ∈ (G.contractEdge d hleg).skeletonDarts) u t') ∧
      (w = G.inv d → ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H), (u : H) = G.walkStep (G.inv d) →
        ∃ t' : (({d, G.inv d} : Set H)ᶜ : Set H), (t' : H) = t ∧
          FirstHit (G.contractEdge d hleg).walkStep
            (· ∈ (G.contractEdge d hleg).skeletonDarts) u t') := by
    intro w t h
    induction h with
    | @stop w hw =>
      refine ⟨fun u hu => ⟨u, hu, .stop ((hR u).2 (hu ▸ hw))⟩,
        fun h => absurd (h ▸ hw) (hXR _ (G.self_mem_vertexOf d)),
        fun h => absurd (h ▸ hw) (hYR _ (G.self_mem_vertexOf _))⟩
    | @step w t hw _ ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      refine ⟨fun u hu => ?_, fun h u hu => ih1 u (h ▸ hu), fun h u hu => ih1 u (h ▸ hu)⟩
      subst hu
      have hu' : u ∉ (G.contractEdge d hleg).skeletonDarts := fun h => hw ((hR u).1 h)
      by_cases hwK : (u : H) ∈ G.core
      · have hstep := coe_contractEdge_walkStep_of_mem hG he hdK (hleg := hleg) hwK
        have hwalk := walkStep_of_mem hwK
        split_ifs at hstep with h1 h2
        · obtain ⟨t', ht', ht''⟩ := ih3 (by rw [hwalk, h1]) _ hstep
          exact ⟨t', ht', .step hu' ht''⟩
        · obtain ⟨t', ht', ht''⟩ := ih2 (by rw [hwalk, h2, hinv]) _ hstep
          exact ⟨t', ht', .step hu' ht''⟩
        · obtain ⟨t', ht', ht''⟩ := ih1 _ hstep
          exact ⟨t', ht', .step hu' ht''⟩
      · have hst : (G.contractEdge d hleg).walkStep u = u :=
          walkStep_of_notMem fun h => hwK ((mem_contractEdge_core_iff hG he).1 h)
        obtain ⟨t', ht', ht''⟩ := ih1 u (walkStep_of_notMem hwK).symm
        refine ⟨t', ht', .step hu' ?_⟩
        rwa [hst]
  refine ⟨skeletonContractEdgeIsoOfEq hG he hGc hR hRY (fun x => ?_) (fun x => ?_)⟩
  · obtain ⟨c1, -, -⟩ := claim _ _ (firstHit_skeletonInvFun (G := G)
      ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H), mem_coe.2 ((hR _).1 (mem_coe.1 x.2))⟩)
    obtain ⟨t', ht', ht''⟩ := c1 ((G.contractEdge d hleg).inv x)
      (coe_contractEdge_inv hinv _)
    rw [← ht', coe_skeletonInvFun_eq_of_firstHit ht'']
  · rw [coe_firstReturn_eq_iff]
    have hY := mem_compl_pair_iff.1 (hRY _ (mem_coe.1 x.2))
    change FirstHit _ _ ((G.rot * swap d (G.inv d)) x) _
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hY.1 hY.2]
    exact (firstHit_firstReturn G.rot _ x).mul_swap
      (fun w hw hwR => hXR w (G.mem_vertexOf.2 hw) (mem_coe.1 hwR))
      (fun h => hYR _ (G.self_mem_vertexOf _) (mem_coe.1 h)) he.not_sameCycle

/-! #### One endpoint with exactly two core darts -/

include hG he hdK in
private theorem skeleton_contractEdge_isomorphic_of_two_three
    (hX : #(G.vertexOf d ∩ G.core) = 2) (hY : 3 ≤ #(G.vertexOf (G.inv d) ∩ G.core))
    (hGc : (G.contractEdge d hleg).IsPlabicGraph) :
    ((G.contractEdge d hleg).skeleton hGc).Isomorphic (G.skeleton hG) := by
  have hinv := hG.inv_involutive
  have hdK' := DiskMap.inv_mem_core hdK
  obtain ⟨a, ha⟩ : ∃ a, (G.coreRot ⟨d, mem_coe.2 hdK⟩ : H) = a := ⟨_, rfl⟩
  have haX : a ∈ G.vertexOf d :=
    ha ▸ G.mem_vertexOf.2 (sameCycle_coreRot_apply ⟨d, mem_coe.2 hdK⟩)
  have haK : a ∈ G.core := ha ▸ mem_coe.1 (G.coreRot ⟨d, mem_coe.2 hdK⟩).2
  have had : a ≠ d := ha ▸ coreRot_ne_self (x := ⟨d, mem_coe.2 hdK⟩)
    (DiskMap.two_le_card_vertexOf_inter_core hdK)
  have haid : a ≠ G.inv d := fun h =>
    notMem_vertexOf_inv_of_mem he haX (h ▸ G.self_mem_vertexOf _)
  have haY : a ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := mem_compl_pair_iff.2 ⟨had, haid⟩
  have hXK : ∀ e ∈ G.vertexOf d, e ∈ G.core → e = d ∨ e = a := by
    have hsub : ({d, a} : Finset H) ⊆ G.vertexOf d ∩ G.core :=
      insert_subset_iff.2 ⟨mem_inter.2 ⟨G.self_mem_vertexOf _, hdK⟩,
        singleton_subset_iff.2 (mem_inter.2 ⟨haX, haK⟩)⟩
    have heq := eq_of_subset_of_card_le hsub (by rw [hX, card_pair had.symm])
    intro e he1 he2
    simpa using (heq ▸ mem_inter.2 ⟨he1, he2⟩ : e ∈ ({d, a} : Finset H))
  have hXR : ∀ w ∈ G.vertexOf d, w ∉ G.skeletonDarts := fun w hw h => by
    have := ((mem_skeletonDarts_iff_of_mem_vertexOf hw he.not_isBoundaryVertex).1 h).2
    omega
  have hYR : ∀ w ∈ G.vertexOf (G.inv d), w ∈ G.core → w ∈ G.skeletonDarts := fun w hw hwK =>
    (mem_skeletonDarts_iff_of_mem_vertexOf hw he.not_isBoundaryVertex_inv).2 ⟨hwK, hY⟩
  have hdR : d ∉ G.skeletonDarts := hXR d (G.self_mem_vertexOf d)
  have hidR : G.inv d ∈ G.skeletonDarts := hYR _ (G.self_mem_vertexOf _) hdK'
  have haR : a ∉ G.skeletonDarts := hXR a haX
  have hσa : (G.coreRot ⟨a, mem_coe.2 haK⟩ : H) = d := by
    have h1 : (G.coreRot ⟨a, mem_coe.2 haK⟩ : H) ∈ G.vertexOf d := by
      rw [← G.vertexOf_eq_of_mem haX]
      exact G.mem_vertexOf.2 (sameCycle_coreRot_apply ⟨a, mem_coe.2 haK⟩)
    have h2 := coreRot_ne_self (x := ⟨a, mem_coe.2 haK⟩)
      (by rw [G.vertexOf_eq_of_mem haX, hX])
    exact (hXK _ h1 (mem_coe.1 (G.coreRot ⟨a, mem_coe.2 haK⟩).2)).resolve_right h2
  have hσd : ∀ w (hw : w ∈ G.core), w ≠ d → (G.coreRot ⟨w, mem_coe.2 hw⟩ : H) = d → w = a :=
    fun w hw hwd h => (hXK w (mem_vertexOf_of_coreRot_eq hw h) hw).resolve_left hwd
  have hσid : ∀ w (hw : w ∈ G.core), (G.coreRot ⟨w, mem_coe.2 hw⟩ : H) = G.inv d →
      w ∈ G.skeletonDarts :=
    fun w hw h => hYR w (mem_vertexOf_of_coreRot_eq hw h) hw
  have hRc : ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H),
      u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ G.skeletonDarts ∨ (u : H) = a := by
    intro u
    by_cases hU : (u : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · rw [mem_contractEdge_skeletonDarts_iff_of_mem_union hG he hdK hU, hX]
      have hY5 : 5 ≤ 2 + #(G.vertexOf (G.inv d) ∩ G.core) := by omega
      simp only [hY5, and_true]
      rcases mem_union.1 hU with h | h
      · constructor
        · intro hu
          exact Or.inr ((hXK _ h hu).resolve_left (mem_compl_pair_iff.1 u.2).1)
        · rintro (h' | h')
          · exact absurd h' (hXR _ h)
          · rwa [h']
      · constructor
        · intro hu
          exact Or.inl (hYR _ h hu)
        · rintro (h' | h')
          · exact mem_core_of_mem_skeletonDarts h'
          · rw [h'] at h; exact absurd h (notMem_vertexOf_inv_of_mem he haX)
    · rw [mem_contractEdge_skeletonDarts_iff_of_notMem_union hG he hU]
      exact ⟨Or.inl, fun h => h.resolve_right fun h' => hU (mem_union_left _ (h' ▸ haX))⟩
  -- the bijection `θ : R → R^c`, the identity except `θ(d̄) = a`
  let c : H → H := fun x => if x = G.inv d then a else x
  have hc1 : ∀ {x : H}, x = G.inv d → c x = a := fun h => if_pos h
  have hc2 : ∀ {x : H}, x ≠ G.inv d → c x = x := fun h => if_neg h
  have hcY : ∀ x : (G.skeletonDarts : Set H), c x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
    intro x
    by_cases h : (x : H) = G.inv d
    · rwa [hc1 h]
    · rw [hc2 h]; exact mem_compl_pair_iff.2 ⟨fun h' => hdR (h' ▸ mem_coe.1 x.2), h⟩
  have hcRc' : ∀ x : (G.skeletonDarts : Set H), c x ∈ G.skeletonDarts ∨ c x = a := by
    intro x
    by_cases h : (x : H) = G.inv d
    · exact Or.inr (hc1 h)
    · rw [hc2 h]; exact Or.inl (mem_coe.1 x.2)
  have hcRc : ∀ x : (G.skeletonDarts : Set H),
      (⟨c x, hcY x⟩ : (({d, G.inv d} : Set H)ᶜ : Set H)) ∈
        (G.contractEdge d hleg).skeletonDarts := fun x => (hRc _).2 (hcRc' x)
  have hinvmem : ∀ y : ((G.contractEdge d hleg).skeletonDarts :
      Set (({d, G.inv d} : Set H)ᶜ : Set H)),
      (if ((y : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = a then G.inv d
        else ((y : (({d, G.inv d} : Set H)ᶜ : Set H)) : H)) ∈ (G.skeletonDarts : Set H) := by
    intro y
    split_ifs with h
    · exact mem_coe.2 hidR
    · exact mem_coe.2 (((hRc _).1 (mem_coe.1 y.2)).resolve_right h)
  let E : (G.skeletonDarts : Set H) ≃
      ((G.contractEdge d hleg).skeletonDarts : Set (({d, G.inv d} : Set H)ᶜ : Set H)) :=
    { toFun := fun x => ⟨⟨c x, hcY x⟩, mem_coe.2 (hcRc x)⟩
      invFun := fun y => ⟨_, hinvmem y⟩
      left_inv := fun x => by
        apply Subtype.ext
        change (if c x = a then G.inv d else c x) = x
        by_cases h : (x : H) = G.inv d
        · rw [hc1 h, if_pos rfl, h]
        · rw [hc2 h, if_neg (fun h' : (x : H) = a => haR (h' ▸ mem_coe.1 x.2))]
      right_inv := fun y => by
        apply Subtype.ext
        apply Subtype.ext
        change c (if ((y : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = a then G.inv d
          else ((y : (({d, G.inv d} : Set H)ᶜ : Set H)) : H)) = _
        by_cases h : ((y : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = a
        · rw [if_pos h, hc1 rfl, h]
        · rw [if_neg h, hc2 (mem_compl_pair_iff.1 (y : (({d, G.inv d} : Set H)ᶜ : Set H)).2).2] }
  have hE : ∀ x, (((E x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H)) = c x := fun _ => rfl
  -- first hits for the rotations
  let Zb : Set H := {y | (y ∈ G.skeletonDarts ∧ y ≠ G.inv d) ∨ y = a}
  have hZb : ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H),
      u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ Zb := by
    intro u
    rw [hRc]
    simp only [Zb, Set.mem_setOf_eq]
    have := (mem_compl_pair_iff.1 u.2).2
    tauto
  have hZbY : Zb ⊆ (({d, G.inv d} : Set H)ᶜ : Set H) := by
    rintro y (⟨hy, hy'⟩ | hy)
    · exact mem_compl_pair_iff.2 ⟨fun h => hdR (h ▸ hy), hy'⟩
    · rwa [hy]
  have hT : ∀ {w0 z : H}, FirstHit G.rot (· ∈ (G.skeletonDarts : Set H)) w0 z →
      (∀ w, G.rot.SameCycle w0 w → w ≠ d ∧ w ≠ a) → z ≠ G.inv d →
      FirstHit (G.rot * swap d (G.inv d)) (· ∈ Zb) w0 z := by
    intro w0 z h hV hz
    refine h.transfer (fun w => G.rot.SameCycle w0 w)
      (fun w hw _ => hw.trans (sameCycle_apply_right.2 (SameCycle.refl _ _)))
      (fun w hw hwR => ⟨?_, ?_⟩) (Or.inl ⟨mem_coe.1 h.prop, hz⟩) (SameCycle.refl _ _)
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hV w hw).1
        (fun h' => hwR (by rw [h']; exact mem_coe.2 hidR))]
    · rintro (⟨h1, -⟩ | h1)
      · exact hwR (mem_coe.2 h1)
      · exact (hV w hw).2 h1
  have hT2 : ∀ {w0 : H}, FirstHit G.rot (· ∈ (G.skeletonDarts : Set H)) w0 (G.inv d) →
      (∀ w, G.rot.SameCycle w0 w → w ≠ d ∧ w ≠ a) →
      FirstHit (G.rot * swap d (G.inv d)) (· ∈ Zb) w0 a := by
    intro w0 h hV
    have h1 : FirstHit (G.rot * swap d (G.inv d))
        (· ∈ (G.skeletonDarts : Set H) ∪ ({a} : Set H)) w0 (G.inv d) := by
      refine h.transfer (fun w => G.rot.SameCycle w0 w)
        (fun w hw _ => hw.trans (sameCycle_apply_right.2 (SameCycle.refl _ _)))
        (fun w hw hwR => ⟨?_, ?_⟩) (Or.inl (mem_coe.2 hidR)) (SameCycle.refl _ _)
      · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (hV w hw).1
          (fun h' => hwR (by rw [h']; exact mem_coe.2 hidR))]
      · rintro (h1 | h1)
        · exact hwR h1
        · exact (hV w hw).2 h1
    have h2 : FirstHit (G.rot * swap d (G.inv d)) (· ∈ Zb) (G.inv d) a := by
      refine .step ?_ ?_
      · rintro (⟨-, h⟩ | h)
        · exact h rfl
        · exact haid h.symm
      · rw [Perm.mul_apply, swap_apply_right]
        have hs := firstHit_coreRot ⟨d, mem_coe.2 hdK⟩
        rw [ha] at hs
        refine hs.transfer (fun _ => True) (fun _ _ _ => trivial)
          (fun w _ hw => ⟨?_, ?_⟩) (Or.inr rfl) trivial
        · rw [Perm.mul_apply, swap_apply_of_ne_of_ne
            (fun h' => hw (by rw [h']; exact mem_coe.2 hdK))
            (fun h' => hw (by rw [h']; exact mem_coe.2 hdK'))]
        · rintro (⟨h1, -⟩ | h1)
          · exact hw (mem_coe.2 (mem_core_of_mem_skeletonDarts h1))
          · exact hw (by rw [h1]; exact mem_coe.2 haK)
    refine h1.trans h2 ?_
    rintro w (⟨h, -⟩ | h)
    · exact Or.inl (mem_coe.2 h)
    · exact Or.inr h
  have hTc : ∀ {w0 z : H}, FirstHit G.rot (· ∈ (G.skeletonDarts : Set H)) w0 z →
      (∀ w, G.rot.SameCycle w0 w → w ≠ d ∧ w ≠ a) →
      FirstHit (G.rot * swap d (G.inv d)) (· ∈ Zb) w0 (c z) := by
    intro w0 z h hV
    by_cases hz : z = G.inv d
    · subst hz
      rw [hc1 rfl]
      exact hT2 h hV
    · rw [hc2 hz]
      exact hT h hV hz
  have hVout : ∀ x ∈ G.skeletonDarts, x ∉ G.vertexOf (G.inv d) →
      ∀ w, G.rot.SameCycle x w → w ≠ d ∧ w ≠ a := by
    intro x hx _ w hw
    refine ⟨fun h => hXR x (G.mem_vertexOf.2 (h ▸ hw).symm) hx,
      fun h => hXR x ?_ hx⟩
    rw [← G.vertexOf_eq_of_mem haX]
    exact G.mem_vertexOf.2 (h ▸ hw).symm
  have hVin : ∀ w0, w0 ∈ G.vertexOf (G.inv d) → ∀ w, G.rot.SameCycle w0 w → w ≠ d ∧ w ≠ a := by
    intro w0 hw0 w hw
    have hwy : w ∈ G.vertexOf (G.inv d) := by
      rw [← G.vertexOf_eq_of_mem hw0]
      exact G.mem_vertexOf.2 hw
    refine ⟨fun h => notMem_vertexOf_inv_of_mem he (G.self_mem_vertexOf d) (h ▸ hwy),
      fun h => notMem_vertexOf_inv_of_mem he haX (h ▸ hwy)⟩
  have hrot : ∀ x : (G.skeletonDarts : Set H),
      (firstReturn (G.rot * swap d (G.inv d)) Zb ⟨c x, (hZb _).1 (hcRc x)⟩ : H) =
        c (firstReturn G.rot (G.skeletonDarts : Set H) x) := by
    intro x
    rw [coe_firstReturn_eq_iff]
    have hxR := mem_coe.1 x.2
    have hfr := firstHit_firstReturn G.rot (G.skeletonDarts : Set H) x
    by_cases hx : (x : H) = G.inv d
    · have hcx : c x = a := if_pos hx
      change FirstHit _ _ ((G.rot * swap d (G.inv d)) (c x)) _
      rw [hcx, Perm.mul_apply, swap_apply_of_ne_of_ne had haid]
      have hs := firstHit_coreRot ⟨a, mem_coe.2 haK⟩
      rw [hσa] at hs
      refine (firstHit_tau_of_mem hdK (Subset.refl _) hs (mem_coe.2 hdK)).trans ?_
        (fun w hw => ?_)
      · refine .step ?_ ?_
        · rintro (⟨h, -⟩ | h)
          · exact hdR h
          · exact had h.symm
        rw [Perm.mul_apply, swap_apply_left]
        rw [hx] at hfr
        exact hTc hfr (hVin _ (G.rot_mem_vertexOf (G.inv d)))
      · rcases hw with ⟨h, -⟩ | h
        · exact mem_coe.2 (mem_core_of_mem_skeletonDarts h)
        · rw [h]; exact mem_coe.2 haK
    · have hcx : c x = x := if_neg hx
      have hY' := mem_compl_pair_iff.1 (hcY x)
      change FirstHit _ _ ((G.rot * swap d (G.inv d)) (c x)) _
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hY'.1 hY'.2, hcx]
      by_cases hxy : (x : H) ∈ G.vertexOf (G.inv d)
      · exact hTc hfr fun w hw =>
          hVin _ hxy w ((sameCycle_apply_right.2 (SameCycle.refl _ _)).trans hw)
      · exact hTc hfr fun w hw =>
          hVout _ hxR hxy w ((sameCycle_apply_right.2 (SameCycle.refl _ _)).trans hw)
  -- the walks
  have hwa : G.walkStep a = G.inv d := by
    rw [walkStep_of_mem haK, hσa]
  have hwd : G.walkStep d = G.inv a := by
    rw [walkStep_of_mem hdK, ha]
  have claim : ∀ w t, FirstHit G.walkStep (· ∈ G.skeletonDarts) w t →
      (∀ u : (({d, G.inv d} : Set H)ᶜ : Set H), (u : H) = w →
        ∃ t' : (({d, G.inv d} : Set H)ᶜ : Set H), (t' : H) = c t ∧
          FirstHit (G.contractEdge d hleg).walkStep
            (· ∈ (G.contractEdge d hleg).skeletonDarts) u t') ∧
      (w = d → ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H), (u : H) = G.walkStep d →
        ∃ t' : (({d, G.inv d} : Set H)ᶜ : Set H), (t' : H) = c t ∧
          FirstHit (G.contractEdge d hleg).walkStep
            (· ∈ (G.contractEdge d hleg).skeletonDarts) u t') := by
    intro w t h
    induction h with
    | @stop w hw =>
      refine ⟨fun u hu => ⟨u, ?_, .stop ((hRc u).2 (Or.inl (hu ▸ hw)))⟩,
        fun h => absurd (h ▸ hw) hdR⟩
      rw [← hu]
      exact (if_neg (mem_compl_pair_iff.1 u.2).2).symm
    | @step w t hw h' ih =>
      obtain ⟨ih1, -⟩ := ih
      refine ⟨fun u hu => ?_, fun h u hu => ih1 u (h ▸ hu)⟩
      subst hu
      by_cases hua : (u : H) = a
      · refine ⟨u, ?_, .stop ((hRc u).2 (Or.inr hua))⟩
        rw [hua, hwa] at h'
        have ht := (FirstHit.stop hidR).unique h'
        rw [← ht, hua]
        exact (if_pos rfl).symm
      have hu' : u ∉ (G.contractEdge d hleg).skeletonDarts := fun h => ((hRc u).1 h).elim hw hua
      by_cases hwK : (u : H) ∈ G.core
      · have hstep := coe_contractEdge_walkStep_of_mem hG he hdK (hleg := hleg) hwK
        split_ifs at hstep with h1 h2
        · exact absurd (hσd _ hwK (mem_compl_pair_iff.1 u.2).1 h1) hua
        · exact absurd (hσid _ hwK h2) hw
        · obtain ⟨t', ht', ht''⟩ := ih1 _ hstep
          exact ⟨t', ht', .step hu' ht''⟩
      · have hst : (G.contractEdge d hleg).walkStep u = u :=
          walkStep_of_notMem fun h => hwK ((mem_contractEdge_core_iff hG he).1 h)
        obtain ⟨t', ht', ht''⟩ := ih1 u (walkStep_of_notMem hwK).symm
        refine ⟨t', ht', .step hu' ?_⟩
        rwa [hst]
  have hinvE : ∀ x : (G.skeletonDarts : Set H),
      c (G.skeletonInvFun x) = (((G.contractEdge d hleg).skeletonInvFun (E x) :
        (({d, G.inv d} : Set H)ᶜ : Set H)) : H) := by
    intro x
    obtain ⟨c1, c2⟩ := claim _ _ (firstHit_skeletonInvFun x)
    have hu0 := coe_contractEdge_inv (hleg := hleg) hinv (E x : (({d, G.inv d} : Set H)ᶜ : Set H))
    rw [hE] at hu0
    have key : ∃ t' : (({d, G.inv d} : Set H)ᶜ : Set H), (t' : H) = c (G.skeletonInvFun x) ∧
        FirstHit (G.contractEdge d hleg).walkStep (· ∈ (G.contractEdge d hleg).skeletonDarts)
          ((G.contractEdge d hleg).inv (E x)) t' := by
      by_cases hx : (x : H) = G.inv d
      · refine c2 (by rw [hx, hinv]) _ ?_
        rw [hu0, hwd]
        exact congrArg G.inv (if_pos hx)
      · refine c1 _ ?_
        rw [hu0]
        exact congrArg G.inv (if_neg hx)
    obtain ⟨t', ht', ht''⟩ := key
    rw [coe_skeletonInvFun_eq_of_firstHit ht'', ht']
  refine ⟨(isoOfMapLeg E (fun x => Subtype.ext (Subtype.ext (by
      change c (G.skeletonInvFun x) = _
      rw [hinvE]
      rfl))) (fun x => Subtype.ext (Subtype.ext (by
      change c (firstReturn G.rot (G.skeletonDarts : Set H) x) =
        ((((G.contractEdge d hleg).skeleton hGc).rot (E x) :
          (({d, G.inv d} : Set H)ᶜ : Set H)) : H)
      rw [coe_contractEdge_skeleton_rot hZb hZbY hGc, ← hrot]
      rfl))) (fun x => ?_) (fun x hx => ?_) (fun i => ?_)).symm⟩
  · rw [mem_skeleton_bdry, mem_skeleton_bdry, mem_contractEdge_bdry]
    change c x ∈ G.bdry ↔ _
    simp only [c]
    split_ifs with h
    · rw [h]
      exact ⟨fun h' => absurd (G.isBoundaryVertex_vertexOf_of_mem h')
          (by rw [G.vertexOf_eq_of_mem haX]; exact he.not_isBoundaryVertex),
        fun h' => absurd (G.isBoundaryVertex_vertexOf_of_mem h') he.not_isBoundaryVertex_inv⟩
    · exact Iff.rfl
  · change G.colour (c x) = G.colour x
    simp only [c]
    split_ifs with h
    · rw [h, he.colour_inv]
      exact colour_eq_of_sameCycle hG he.not_isBoundaryVertex (G.mem_vertexOf.1 haX)
    · rfl
  · apply Subtype.ext
    apply Subtype.ext
    change c ((G.skeleton hG).leg i : H) = _
    have hb := G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
    have hnot : ∀ z, G.vertexOf z = G.vertexOf (G.leg i) → z ≠ G.inv d := fun z hz h =>
      he.not_isBoundaryVertex_inv (by rw [← h, hz]; exact hb)
    have hnota : G.leg i ≠ a := fun h => he.not_isBoundaryVertex (by
      rw [← G.vertexOf_eq_of_mem haX, ← h]; exact hb)
    rw [coe_skeleton_leg, coe_skeleton_leg]
    by_cases h : G.leg i ∈ G.skeletonDarts
    · rw [if_pos h, if_pos ((hRc _).2 (Or.inl h))]
      exact if_neg (hnot _ rfl)
    · rw [if_neg h, if_neg (fun h' => ((hRc _).1 h').elim h hnota), coe_contractEdge_rot_of_mem]
      · exact if_neg (hnot _ (G.vertexOf_rot _))
      · exact he.mem_of_mem_bdry (rot_leg_mem_bdry hG i)

/-! #### Both endpoints with at least three core darts -/

include hG he hdK in
private theorem skeleton_contractEdge_of_three_three (hA : G.IsAnchored)
    (hX : 3 ≤ #(G.vertexOf d ∩ G.core)) (hY : 3 ≤ #(G.vertexOf (G.inv d) ∩ G.core))
    (hGc : (G.contractEdge d hleg).IsPlabicGraph) :
    ∃ (hdR : d ∈ G.skeletonDarts)
      (he' : (G.skeleton hG).IsContractibleEdge ⟨d, mem_coe.2 hdR⟩),
      (((G.skeleton hG).inv ⟨d, mem_coe.2 hdR⟩ : (G.skeletonDarts : Set H)) : H) = G.inv d ∧
      ∃ θ : ((G.contractEdge d hleg).skeleton hGc).Iso
          ((G.skeleton hG).contractEdge ⟨d, mem_coe.2 hdR⟩
            (he'.leg_mem (hA.isPlabicGraph_skeleton hG))),
        ∀ x, ((θ.toEquiv x : (G.skeletonDarts : Set H)) : H) =
          ((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) := by
  have hinv := hG.inv_involutive
  have hdK' := DiskMap.inv_mem_core hdK
  have hΓ := hA.isPlabicGraph_skeleton hG
  have hXR : ∀ w ∈ G.vertexOf d, w ∈ G.core → w ∈ G.skeletonDarts := fun w hw hwK =>
    (mem_skeletonDarts_iff_of_mem_vertexOf hw he.not_isBoundaryVertex).2 ⟨hwK, hX⟩
  have hYR : ∀ w ∈ G.vertexOf (G.inv d), w ∈ G.core → w ∈ G.skeletonDarts := fun w hw hwK =>
    (mem_skeletonDarts_iff_of_mem_vertexOf hw he.not_isBoundaryVertex_inv).2 ⟨hwK, hY⟩
  have hdR : d ∈ G.skeletonDarts := hXR d (G.self_mem_vertexOf d) hdK
  have hidR : G.inv d ∈ G.skeletonDarts := hYR _ (G.self_mem_vertexOf _) hdK'
  have hΓinv : (((G.skeleton hG).inv ⟨d, mem_coe.2 hdR⟩ : (G.skeletonDarts : Set H)) : H) =
      G.inv d := by
    rw [coe_skeleton_inv]
    exact coe_skeletonInvFun_eq_of_firstHit (.stop hidR)
  have he' : (G.skeleton hG).IsContractibleEdge ⟨d, mem_coe.2 hdR⟩ :=
    { vertexOf_ne := fun h => by
        have h1 := congrArg (Finset.map (Embedding.subtype (· ∈ (G.skeletonDarts : Set H)))) h
        rw [map_skeleton_vertexOf, map_skeleton_vertexOf, hΓinv] at h1
        have : d ∈ G.vertexOf (G.inv d) ∩ G.skeletonDarts :=
          h1 ▸ mem_inter.2 ⟨G.self_mem_vertexOf d, hdR⟩
        exact notMem_vertexOf_inv_of_mem he (G.self_mem_vertexOf d) (mem_inter.1 this).1
      mem_internalVertices := (G.skeleton hG).vertexOf_mem_internalVertices.2
        ((isBoundaryVertex_skeleton_vertexOf_iff hG _).not.2 he.not_isBoundaryVertex)
      inv_mem_internalVertices := (G.skeleton hG).vertexOf_mem_internalVertices.2
        ((isBoundaryVertex_skeleton_vertexOf_iff hG _).not.2
          (by rw [hΓinv]; exact he.not_isBoundaryVertex_inv))
      colour_inv := by
        rw [skeleton_colour, skeleton_colour, hΓinv]
        exact he.colour_inv }
  refine ⟨hdR, he', hΓinv, ?_⟩
  have hR : ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H),
      u ∈ (G.contractEdge d hleg).skeletonDarts ↔ (u : H) ∈ G.skeletonDarts := by
    intro u
    by_cases hU : (u : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · rw [mem_contractEdge_skeletonDarts_iff_of_mem_union hG he hdK hU]
      constructor
      · rintro ⟨hu, -⟩
        rcases mem_union.1 hU with h | h
        · exact hXR _ h hu
        · exact hYR _ h hu
      · intro h
        exact ⟨mem_core_of_mem_skeletonDarts h, by omega⟩
    · exact mem_contractEdge_skeletonDarts_iff_of_notMem_union hG he hU
  have hS' : ∀ v : (G.skeletonDarts : Set H),
      v ∈ (({⟨d, mem_coe.2 hdR⟩, (G.skeleton hG).inv ⟨d, mem_coe.2 hdR⟩} :
        Set (G.skeletonDarts : Set H))ᶜ : Set (G.skeletonDarts : Set H)) ↔
      (v : H) ∈ (G.skeletonDarts : Set H) ∩ (({d, G.inv d} : Set H)ᶜ : Set H) := by
    intro v
    rw [mem_compl_pair_iff, Set.mem_inter_iff, mem_compl_pair_iff]
    refine ⟨fun h => ⟨v.2, fun h' => h.1 (Subtype.ext h'), fun h' => h.2 (Subtype.ext
      (h'.trans hΓinv.symm))⟩, fun h => ⟨fun h' => h.2.1 (congrArg Subtype.val h'),
      fun h' => h.2.2 ((congrArg Subtype.val h').trans hΓinv)⟩⟩
  -- the equivalence of darts
  let E : ((G.contractEdge d hleg).skeletonDarts : Set (({d, G.inv d} : Set H)ᶜ : Set H)) ≃
      (({⟨d, mem_coe.2 hdR⟩, (G.skeleton hG).inv ⟨d, mem_coe.2 hdR⟩} :
        Set (G.skeletonDarts : Set H))ᶜ : Set (G.skeletonDarts : Set H)) :=
    { toFun := fun x => ⟨⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
          mem_coe.2 ((hR _).1 (mem_coe.1 x.2))⟩,
        (hS' _).2 ⟨mem_coe.2 ((hR _).1 (mem_coe.1 x.2)), (x : (({d, G.inv d} : Set H)ᶜ : Set H)).2⟩⟩
      invFun := fun y => ⟨⟨((y : (G.skeletonDarts : Set H)) : H), ((hS' _).1 y.2).2⟩,
        mem_coe.2 ((hR _).2 (mem_coe.1 ((hS' _).1 y.2).1))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  -- rotations
  have hperm : (G.skeleton hG).rot * swap ⟨d, mem_coe.2 hdR⟩ ((G.skeleton hG).inv
      ⟨d, mem_coe.2 hdR⟩) =
        firstReturnPerm (G.rot * swap d (G.inv d)) (G.skeletonDarts : Set H) := by
    refine Equiv.ext fun y => Subtype.ext ?_
    have hsw : swap d (G.inv d) (y : H) = ((swap ⟨d, mem_coe.2 hdR⟩
        ((G.skeleton hG).inv ⟨d, mem_coe.2 hdR⟩) y : (G.skeletonDarts : Set H)) : H) := by
      rw [Subtype.val_injective.map_swap, hΓinv]
    have hy' : swap d (G.inv d) (y : H) ∈ (G.skeletonDarts : Set H) := by
      rw [hsw]
      exact Subtype.mem _
    rw [Perm.mul_apply, coe_firstReturnPerm, coe_firstReturn_mul_swap G.rot (mem_coe.2 hdR)
      (mem_coe.2 hidR) y.2 hy']
    exact congrArg (fun z => (firstReturn G.rot (G.skeletonDarts : Set H) z : H))
      (Subtype.ext hsw.symm)
  -- walks
  have claim : ∀ w t, FirstHit G.walkStep (· ∈ G.skeletonDarts) w t →
      t ∈ (({d, G.inv d} : Set H)ᶜ : Set H) →
      ∀ u : (({d, G.inv d} : Set H)ᶜ : Set H), (u : H) = w →
        ∃ t' : (({d, G.inv d} : Set H)ᶜ : Set H), (t' : H) = t ∧
          FirstHit (G.contractEdge d hleg).walkStep
            (· ∈ (G.contractEdge d hleg).skeletonDarts) u t' := by
    intro w t h ht
    induction h with
    | @stop w hw => exact fun u hu => ⟨u, hu, .stop ((hR u).2 (hu ▸ hw))⟩
    | @step w t hw _ ih =>
      intro u hu
      subst hu
      have hu' : u ∉ (G.contractEdge d hleg).skeletonDarts := fun h => hw ((hR u).1 h)
      by_cases hwK : (u : H) ∈ G.core
      · have hstep := coe_contractEdge_walkStep_of_mem hG he hdK (hleg := hleg) hwK
        split_ifs at hstep with h1 h2
        · exact absurd (hXR _ (mem_vertexOf_of_coreRot_eq hwK h1) hwK) hw
        · exact absurd (hYR _ (mem_vertexOf_of_coreRot_eq hwK h2) hwK) hw
        · obtain ⟨t', ht', ht''⟩ := ih ht _ hstep
          exact ⟨t', ht', .step hu' ht''⟩
      · have hst : (G.contractEdge d hleg).walkStep u = u :=
          walkStep_of_notMem fun h => hwK ((mem_contractEdge_core_iff hG he).1 h)
        obtain ⟨t', ht', ht''⟩ := ih ht u (walkStep_of_notMem hwK).symm
        refine ⟨t', ht', .step hu' ?_⟩
        rwa [hst]
  have hinvΓ := involutive_skeletonInvFun hinv (G := G)
  have hinvc : ∀ x : ((G.contractEdge d hleg).skeletonDarts :
        Set (({d, G.inv d} : Set H)ᶜ : Set H)),
      (((G.contractEdge d hleg).skeletonInvFun x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
        G.skeletonInvFun ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
          mem_coe.2 ((hR _).1 (mem_coe.1 x.2))⟩ := by
    intro x
    set y : (G.skeletonDarts : Set H) := ⟨((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H),
      mem_coe.2 ((hR _).1 (mem_coe.1 x.2))⟩ with hy
    have hxY := mem_compl_pair_iff.1 (x : (({d, G.inv d} : Set H)ᶜ : Set H)).2
    have hdR' : G.skeletonInvFun ⟨d, mem_coe.2 hdR⟩ = ⟨G.inv d, mem_coe.2 hidR⟩ :=
      Subtype.ext ((coe_skeleton_inv hG _).symm.trans hΓinv)
    have htY : (G.skeletonInvFun y : H) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
      refine mem_compl_pair_iff.2 ⟨fun h => hxY.2 ?_, fun h => hxY.1 ?_⟩
      · have h' : G.skeletonInvFun y = ⟨d, mem_coe.2 hdR⟩ := Subtype.ext h
        have := congrArg G.skeletonInvFun h'
        rw [hinvΓ, hdR'] at this
        exact congrArg Subtype.val this
      · have h' : G.skeletonInvFun y = ⟨G.inv d, mem_coe.2 hidR⟩ := Subtype.ext h
        have := congrArg G.skeletonInvFun h'
        rw [hinvΓ, ← hdR', hinvΓ] at this
        exact congrArg Subtype.val this
    obtain ⟨t', ht', ht''⟩ := claim _ _ (firstHit_skeletonInvFun y) htY
      ((G.contractEdge d hleg).inv x) (coe_contractEdge_inv hinv _)
    rw [← ht', coe_skeletonInvFun_eq_of_firstHit ht'']
  refine ⟨isoOfMapLeg E (fun x => Subtype.ext (Subtype.ext ?_)) (fun x => Subtype.ext
    (Subtype.ext ?_)) (fun x => ?_) (fun _ _ => rfl) (fun i => Subtype.ext (Subtype.ext ?_)),
    fun _ => rfl⟩
  · change (((G.contractEdge d hleg).skeletonInvFun x : (({d, G.inv d} : Set H)ᶜ : Set H)) :
      H) = ((((G.skeleton hG).contractEdge _ _).inv (E x) : (G.skeletonDarts : Set H)) : H)
    rw [coe_contractEdge_inv hΓ.inv_involutive, coe_skeleton_inv, hinvc]
    rfl
  · change ((((G.contractEdge d hleg).skeleton hGc).rot x :
      (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
        ((((G.skeleton hG).contractEdge _ _).rot (E x) : (G.skeletonDarts : Set H)) : H)
    rw [coe_contractEdge_skeleton_rot (Z := (G.skeletonDarts : Set H) ∩
      (({d, G.inv d} : Set H)ᶜ : Set H)) (fun u => (hR u).trans ⟨fun h => ⟨mem_coe.2 h, u.2⟩,
        fun h => mem_coe.1 h.1⟩) Set.inter_subset_right hGc, contractEdge_rot]
    unfold inducedRotationPerm
    rw [hperm]
    exact (coe_firstReturn_firstReturnPerm _ Set.inter_subset_left hS' (E x)).symm
  · exact (mem_contractEdge_bdry.trans (mem_skeleton_bdry hG)).trans
      ((mem_skeleton_bdry hGc).trans mem_contractEdge_bdry).symm
  · change ((((G.contractEdge d hleg).skeleton hGc).leg i :
      (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
        ((((G.skeleton hG).contractEdge ⟨d, mem_coe.2 hdR⟩ (he'.leg_mem hΓ)).leg i :
          (G.skeletonDarts : Set H)) : H)
    rw [coe_contractEdge_leg, coe_skeleton_leg, coe_skeleton_leg]
    by_cases h : G.leg i ∈ G.skeletonDarts
    · rw [if_pos h, if_pos ((hR _).2 h)]
      rfl
    · rw [if_neg h, if_neg (mt (hR _).1 h), coe_contractEdge_rot_of_mem]
      · rfl
      · exact he.mem_of_mem_bdry (rot_leg_mem_bdry hG i)

end MemCore

/-! #### Contracting along `d̄` instead of `d` -/

private theorem IsContractibleEdge.inv' (hinv : Involutive G.inv) (he : G.IsContractibleEdge d) :
    G.IsContractibleEdge (G.inv d) where
  vertexOf_ne := by rw [hinv]; exact he.vertexOf_ne.symm
  mem_internalVertices := he.inv_mem_internalVertices
  inv_mem_internalVertices := by rw [hinv]; exact he.mem_internalVertices
  colour_inv := by rw [hinv]; exact he.colour_inv.symm

/-- The contractions along `d` and along `d̄` are the same tuple. -/
private noncomputable def contractEdgeInvIso (hinv : Involutive G.inv)
    {hleg' : ∀ i, G.leg i ∈ (({G.inv d, G.inv (G.inv d)} : Set H)ᶜ : Set H)} :
    (G.contractEdge d hleg).Iso (G.contractEdge (G.inv d) hleg') :=
  have hmem : ∀ x : H, x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) ↔
      x ∈ (({G.inv d, G.inv (G.inv d)} : Set H)ᶜ : Set H) := fun x => by
    rw [mem_compl_pair_iff, mem_compl_pair_iff, hinv]
    exact And.comm
  isoOfMapLeg (Equiv.subtypeEquivRight hmem)
    (fun x => Subtype.ext (by
      change ((G.contractEdge d hleg).inv x : H) = ((G.contractEdge (G.inv d) hleg').inv _ : H)
      rw [coe_contractEdge_inv hinv, coe_contractEdge_inv hinv]
      rfl))
    (fun x => Subtype.ext (by
      change (firstReturn (G.rot * swap d (G.inv d)) _ x : H) =
        (firstReturn (G.rot * swap (G.inv d) (G.inv (G.inv d))) _ _ : H)
      symm
      rw [coe_firstReturn_eq_iff]
      have hτ : ∀ w, (G.rot * swap (G.inv d) (G.inv (G.inv d))) w =
          (G.rot * swap d (G.inv d)) w := fun w => by rw [hinv, swap_comm]
      change FirstHit _ _ ((G.rot * swap (G.inv d) (G.inv (G.inv d))) x) _
      rw [hτ]
      exact (firstHit_firstReturn _ _ x).transfer (fun _ => True) (fun _ _ _ => trivial)
        (fun w _ hw => ⟨hτ w, fun h => hw ((hmem w).2 h)⟩)
        ((hmem _).1 (firstReturn _ _ x).2) trivial))
    (fun x => by
      rw [mem_contractEdge_bdry, mem_contractEdge_bdry]
      rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)

/-- Let `G` be an anchored plabic graph and `{d, d̄}` an edge whose endpoints are distinct internal
vertices of the same colour. Then `Γ(G^c)` is isomorphic to `Γ(G)`, or `d` and `d̄` are darts of
`Γ(G)`, forming an edge of its graph whose endpoints are distinct internal vertices of the same
colour, and `Γ(G^c)` is the contraction of `Γ(G)` along `{d, d̄}`: the identification of their
darts in `H` is an isomorphism. -/
@[cluster_algebras "lem_skeleton_contraction"]
theorem skeleton_contractEdge (hA : G.IsAnchored) :
    ((G.contractEdge d (he.leg_mem hG)).skeleton (hG.contractEdge he)).Isomorphic
      (G.skeleton hG) ∨
    ∃ (hdR : d ∈ G.skeletonDarts)
      (he' : (G.skeleton hG).IsContractibleEdge ⟨d, mem_coe.2 hdR⟩),
      (((G.skeleton hG).inv ⟨d, mem_coe.2 hdR⟩ : (G.skeletonDarts : Set H)) : H) = G.inv d ∧
      ∃ θ : ((G.contractEdge d (he.leg_mem hG)).skeleton (hG.contractEdge he)).Iso
          ((G.skeleton hG).contractEdge ⟨d, mem_coe.2 hdR⟩
            (he'.leg_mem (hA.isPlabicGraph_skeleton hG))),
        ∀ x, ((θ.toEquiv x : (G.skeletonDarts : Set H)) : H) =
          ((x : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) := by
  have hinv := hG.inv_involutive
  by_cases hdK : d ∈ G.core
  · have h2X := DiskMap.two_le_card_vertexOf_inter_core hdK
    have hdK' := DiskMap.inv_mem_core hdK
    have h2Y := DiskMap.two_le_card_vertexOf_inter_core hdK'
    rcases (show #(G.vertexOf d ∩ G.core) = 2 ∨ 3 ≤ #(G.vertexOf d ∩ G.core) by omega) with
      hX | hX <;>
    rcases (show #(G.vertexOf (G.inv d) ∩ G.core) = 2 ∨
      3 ≤ #(G.vertexOf (G.inv d) ∩ G.core) by omega) with hY | hY
    · exact Or.inl (skeleton_contractEdge_isomorphic_of_two_two hG he hdK hX hY _)
    · exact Or.inl (skeleton_contractEdge_isomorphic_of_two_three hG he hdK hX hY _)
    · have he' := he.inv' hinv
      refine Or.inl (Isomorphic.trans _ (Isomorphic.skeleton (hG.contractEdge he)
        (hG.contractEdge he') ⟨contractEdgeInvIso hinv (hleg' := he'.leg_mem hG)⟩) ?_)
      exact skeleton_contractEdge_isomorphic_of_two_three hG he' hdK' hY
        (by rw [hinv]; exact hX) _
    · exact Or.inr (skeleton_contractEdge_of_three_three hG he hdK hA hX hY _)
  · exact Or.inl ⟨skeletonContractEdgeIsoOfNotMem hG he hdK _⟩

end SkeletonContractEdge

/-- Every internal vertex of the skeleton consists of at least three darts. -/
theorem three_le_card_of_mem_skeleton_internalVertices (hG : G.IsPlabicGraph) {v : Finset _}
    (hv : v ∈ (G.skeleton hG).internalVertices) : 3 ≤ #v := by
  obtain ⟨x, rfl⟩ := (G.skeleton hG).mem_vertices.1 (mem_filter.1 hv).1
  have hb : ¬G.IsBoundaryVertex (G.vertexOf x) :=
    (isBoundaryVertex_skeleton_vertexOf_iff hG x).not.1 (mem_filter.1 hv).2
  have h3 := ((mem_filter.1 (mem_coe.1 x.2)).2).resolve_left hb
  rw [← card_map (Embedding.subtype (· ∈ (G.skeletonDarts : Set H))), map_skeleton_vertexOf]
  refine h3.trans (card_le_card fun e he => ?_)
  obtain ⟨he1, he2⟩ := mem_inter.1 he
  exact mem_inter.2 ⟨he1, mem_skeletonDarts_of_sameCycle (mem_coe.1 x.2) he2
    (G.mem_vertexOf.1 he1)⟩

end PlabicData

/-! ### Moves preserve anchoring -/

namespace PlabicGraph

variable {b : ℕ}

/-- If `G` is an anchored plabic graph and `G'` is isomorphic to `G` or obtained from `G` by a
local move, then `G'` is anchored. -/
@[cluster_algebras "lem_anchored_step"]
theorem MoveStep.isAnchored {S : Set LocalMoveType} {G G' : PlabicGraph b} (h : MoveStep S G G')
    (hA : G.data.IsAnchored) : G'.data.IsAnchored := by
  rcases h with hθ | ⟨t, -, ht⟩
  · obtain ⟨θ⟩ := hθ
    exact (θ.isAnchored_iff G'.isPlabicGraph G.isPlabicGraph).2 hA
  cases t with
  | m1 =>
    obtain ⟨c, -, hθ⟩ := ht
    obtain ⟨θ⟩ := hθ
    exact (θ.isAnchored_iff G'.isPlabicGraph (G.isPlabicGraph.squareMove c)).2 hA
  | m2 =>
    rcases ht with ⟨d, hd, hθ⟩ | ⟨d, hd, hθ⟩ <;> obtain ⟨θ⟩ := hθ
    · refine (θ.isAnchored_iff G'.isPlabicGraph
        (PlabicData.isPlabicGraph_bivalentRemoval _ hd)).2 fun i => ?_
      refine (mem_map' (Embedding.subtype _)).1 ?_
      rw [PlabicData.map_core_bivalentRemoval]
      have hl := hd.leg_mem G.isPlabicGraph i
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hl
      exact mem_sdiff.2 ⟨hA i, by simp only [mem_insert, mem_singleton, not_or]; exact hl⟩
    · have hA' := (θ.isAnchored_iff G.isPlabicGraph
        (PlabicData.isPlabicGraph_bivalentRemoval _ hd)).1 hA
      intro i
      have := mem_map_of_mem (Embedding.subtype _) (hA' i)
      rw [PlabicData.map_core_bivalentRemoval] at this
      exact (mem_sdiff.1 this).1
  | m3 =>
    rcases ht with ⟨d, he, hθ⟩ | ⟨d, he, hθ⟩ <;> obtain ⟨θ⟩ := hθ
    · refine (θ.isAnchored_iff G'.isPlabicGraph (G.isPlabicGraph.contractEdge he)).2 fun i => ?_
      refine (mem_map' (Embedding.subtype _)).1 ?_
      rw [PlabicData.map_core_contractEdge G.isPlabicGraph he]
      have hl := PlabicData.mem_compl_pair_iff.1 (he.leg_mem G.isPlabicGraph i)
      exact mem_sdiff.2 ⟨hA i, by simp only [mem_insert, mem_singleton, not_or]; exact hl⟩
    · have hA' := (θ.isAnchored_iff G.isPlabicGraph (G'.isPlabicGraph.contractEdge he)).1 hA
      intro i
      have := mem_map_of_mem (Embedding.subtype _) (hA' i)
      rw [PlabicData.map_core_contractEdge G'.isPlabicGraph he] at this
      exact (mem_sdiff.1 this).1

end PlabicGraph

/-! ### Moves of type (M2) and (M3) on skeletons -/

namespace PlabicGraph

variable {b : ℕ}

/-- The skeleton `Γ(G)` of an anchored plabic graph, bundled as a plabic graph. -/
noncomputable abbrev skeleton (G : PlabicGraph b) (hA : G.data.IsAnchored) : PlabicGraph b where
  Dart := (G.data.skeletonDarts : Set G.Dart)
  data := G.data.skeleton G.isPlabicGraph
  isPlabicGraph := hA.isPlabicGraph_skeleton G.isPlabicGraph

/-- If `G` is an anchored plabic graph and `G'` is isomorphic to `G` or obtained from `G` by a
local move of type (M2) or (M3), then `Γ(G')` is isomorphic to `Γ(G)` or obtained from `Γ(G)` by
a local move of type (M3). -/
@[cluster_algebras "lem_skeleton_step"]
theorem MoveStep.skeleton {G G' : PlabicGraph b} (hA : G.data.IsAnchored)
    (h : MoveStep {LocalMoveType.m2, LocalMoveType.m3} G G') :
    MoveStep {LocalMoveType.m3} (G.skeleton hA) (G'.skeleton (h.isAnchored hA)) := by
  have hA' := h.isAnchored hA
  rcases h with hθ | ⟨t, ht, hm⟩
  · exact Or.inl (PlabicData.Isomorphic.skeleton G'.isPlabicGraph G.isPlabicGraph hθ)
  rcases ht with rfl | rfl
  · rcases hm with ⟨d, hd, hθ⟩ | ⟨d, hd, hθ⟩
    · obtain ⟨θ, -⟩ := PlabicData.exists_skeletonBivalentRemovalIso G.isPlabicGraph hd
      exact Or.inl (PlabicData.Isomorphic.trans _ (PlabicData.Isomorphic.skeleton
        G'.isPlabicGraph (PlabicData.isPlabicGraph_bivalentRemoval _ hd) hθ) ⟨θ⟩)
    · obtain ⟨θ, -⟩ := PlabicData.exists_skeletonBivalentRemovalIso G'.isPlabicGraph hd
      exact Or.inl (PlabicData.Isomorphic.symm _ (PlabicData.Isomorphic.trans _
        (PlabicData.Isomorphic.skeleton G.isPlabicGraph
          (PlabicData.isPlabicGraph_bivalentRemoval _ hd) hθ) ⟨θ⟩))
  · rcases hm with ⟨d, he, hθ⟩ | ⟨d, he, hθ⟩
    · have hθ' := PlabicData.Isomorphic.skeleton G'.isPlabicGraph
        (G.isPlabicGraph.contractEdge he) hθ
      rcases PlabicData.skeleton_contractEdge G.isPlabicGraph he hA with h1 | ⟨hdR, he', -, θ, -⟩
      · exact Or.inl (PlabicData.Isomorphic.trans _ hθ' h1)
      · exact Or.inr ⟨LocalMoveType.m3, Set.mem_singleton _,
          Or.inl ⟨⟨d, mem_coe.2 hdR⟩, he', PlabicData.Isomorphic.trans _ hθ' ⟨θ⟩⟩⟩
    · have hθ' := PlabicData.Isomorphic.skeleton G.isPlabicGraph
        (G'.isPlabicGraph.contractEdge he) hθ
      rcases PlabicData.skeleton_contractEdge G'.isPlabicGraph he hA' with h1 | ⟨hdR, he', -, θ, -⟩
      · exact Or.inl (PlabicData.Isomorphic.symm _ (PlabicData.Isomorphic.trans _ hθ' h1))
      · exact Or.inr ⟨LocalMoveType.m3, Set.mem_singleton _,
          Or.inr ⟨⟨d, mem_coe.2 hdR⟩, he', PlabicData.Isomorphic.trans _ hθ' ⟨θ⟩⟩⟩

/-- If `G` and `G'` are `{M2, M3}`-equivalent plabic graphs in each of which every internal vertex
consists of at least three darts, then there is a sequence `G = X₀, X₁, …, X_r = G'` of plabic
graphs, in each of which every internal vertex consists of at least three darts, such that each
`X_t` is isomorphic to `X_{t-1}` or obtained from it by a local move of type (M3). -/
@[cluster_algebras "lem_m2_moves_unnecessary"]
theorem MoveEquivalent.exists_chain_m3 {G G' : PlabicGraph b}
    (hG : ∀ v ∈ G.data.internalVertices, 3 ≤ #v) (hG' : ∀ v ∈ G'.data.internalVertices, 3 ≤ #v)
    (h : MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} G G') :
    Relation.ReflTransGen (fun X Y : PlabicGraph b => (∀ v ∈ X.data.internalVertices, 3 ≤ #v) ∧
      (∀ v ∈ Y.data.internalVertices, 3 ≤ #v) ∧ MoveStep {LocalMoveType.m3} X Y) G G' := by
  have hA : G.data.IsAnchored := G.isPlabicGraph.isAnchored fun v hv => by
    have := hG v hv
    omega
  have hthick : ∀ (X : PlabicGraph b) (hX : X.data.IsAnchored),
      ∀ v ∈ (X.skeleton hX).data.internalVertices, 3 ≤ #v := fun X _ _ hv =>
    PlabicData.three_le_card_of_mem_skeleton_internalVertices X.isPlabicGraph hv
  have key : ∀ Gt, MoveEquivalent {LocalMoveType.m2, LocalMoveType.m3} G Gt →
      ∃ hAt : Gt.data.IsAnchored, Relation.ReflTransGen
        (fun X Y : PlabicGraph b => (∀ v ∈ X.data.internalVertices, 3 ≤ #v) ∧
          (∀ v ∈ Y.data.internalVertices, 3 ≤ #v) ∧ MoveStep {LocalMoveType.m3} X Y)
        (G.skeleton hA) (Gt.skeleton hAt) := by
    intro Gt hGt
    change Relation.ReflTransGen _ G Gt at hGt
    induction hGt with
    | refl => exact ⟨hA, .refl⟩
    | @tail Gs Gu _ hstep ih =>
      obtain ⟨hAs, hrel⟩ := ih
      exact ⟨hstep.isAnchored hAs, hrel.tail ⟨hthick _ _, hthick _ _, hstep.skeleton hAs⟩⟩
  obtain ⟨hA', hrel⟩ := key G' h
  refine Relation.ReflTransGen.head ⟨hG, hthick _ _,
    Or.inl ⟨PlabicData.skeletonIsoOfThick G.isPlabicGraph hG⟩⟩ (hrel.tail ⟨hthick _ _, hG',
      Or.inl ⟨(PlabicData.skeletonIsoOfThick G'.isPlabicGraph hG').symm⟩⟩)

end PlabicGraph

end ClusterAlgebras
