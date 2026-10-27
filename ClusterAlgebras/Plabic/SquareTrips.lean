/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FirstReturn
public import ClusterAlgebras.Plabic.SquareMove
public import ClusterAlgebras.Plabic.Trips

/-!
# Trips through a square face

Let `G` be a plabic graph and `q = (c₁, c₂, c₃, c₄)` an internal face of `G` at which a square
move applies: `c_{k+1} = φ(c_k)`, and the four vertices `x_k = v(c_k)` are internal, pairwise
distinct, trivalent and alternate in colour. Put `e_k = σ(c_k)`. Since `c_k = σ(c̄_{k-1})`, the
rotation at `x_k` is the `3`-cycle `(c̄_{k-1} c_k e_k)`, and the trip map `T` of `G` is explicit on
the twelve darts `c_{k-1}`, `c̄_k`, `ē_k` arriving at the corners: if `x_k` is black then
`T(c_{k-1}) = c_k`, `T(c̄_k) = e_k`, `T(ē_k) = c̄_{k-1}`, and if `x_k` is white then
`T(c_{k-1}) = e_k`, `T(c̄_k) = c̄_{k-1}`, `T(ē_k) = c_k`.

Following a trip into the square along `ē_k`, it leaves it along `e_{k+2}` after crossing two
edges of `q`, whatever the colours. So the first-return maps of the trip maps of `G` and of its
square move `G'` to the darts off the edges of `q` agree, and every trip meets these darts. Hence
`G` has a roundtrip if and only if `G'` has one.

## Main definitions

* `ClusterAlgebras.PlabicData.squareEdgeDarts`: the eight darts `c_k`, `c̄_k` of the edges of `q`.

## Main results

* `ClusterAlgebras.PlabicData.IsSquareMoveFace.tripMap_eq`: the trip map on the twelve darts at
  the corners of `q`, when `v(c₁)` is black.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasRoundtrip_squareMove_iff`: a square move keeps
  roundtrips.
* `ClusterAlgebras.PlabicData.IsSquareMoveFace.firstReturnPerm_tripEquiv_squareMove`: the trip
  maps of `G` and of its square move have the same first return to the darts off the edges of `q`.

## Implementation notes

* As in `ClusterAlgebras.Plabic.SquareMove`, the face is given by its first dart `c = c₁`,
  and `c_{k+1}` is `squareCorner c k` for the `0`-indexed `k : Fin 4`, so that indices are read
  modulo `4` by the arithmetic of `Fin 4`.
* The trip map is the permutation `IsPlabicGraph.tripEquiv` of all darts, which preserves `B`.
  The first return is taken to the complement `Y` of the eight darts `c_k`, `c̄_k`
  (`squareEdgeDarts`), which contains `B`; a roundtrip is then an orbit disjoint from the set of
  darts that are in `B` or are legs, and this set lies in `Y`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Equiv Equiv.Perm Function

/-- If `π` sends `y ∈ Y` to `a ∉ Y`, then `a` to `b ∉ Y`, then `b` to `z ∈ Y`, the first return of
`y` to `Y` is `z`. -/
theorem coe_firstReturn_of_apply_apply_apply {X : Type*} [Finite X] {π : Perm X} {Y : Set X}
    {y : Y} {a b z : X} (ha : π y = a) (hb : π a = b) (hz : π b = z) (haY : a ∉ Y) (hbY : b ∉ Y)
    (hzY : z ∈ Y) : (firstReturn π Y y : X) = z := by
  have h3 : (π ^ 3) y = z := by
    rw [pow_three, Perm.mul_apply, Perm.mul_apply, ha, hb, hz]
  refine (coe_firstReturn_of_pow (m := 3) (by norm_num) (h3 ▸ hzY) fun j hj hj3 => ?_).trans h3
  interval_cases j
  · rwa [pow_one, ha]
  · rwa [pow_two, Perm.mul_apply, ha, hb]

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Trivalent vertices -/

/-- At a vertex with exactly three darts, `σ(x) ≠ x` and `σ²(x) ≠ x`. -/
theorem rot_ne_of_card_vertexOf_eq_three {x : H} (h : (G.vertexOf x).card = 3) :
    G.rot x ≠ x ∧ G.rot (G.rot x) ≠ x := by
  have h2 : G.rot (G.rot x) ≠ x := fun h2 => by
    have := G.card_vertexOf_le_two h2
    omega
  exact ⟨fun h1 => h2 (by rw [h1, h1]), h2⟩

/-- A vertex with exactly three darts is `{x, σ(x), σ²(x)}`. -/
theorem vertexOf_eq_of_card_vertexOf_eq_three {x : H} (h : (G.vertexOf x).card = 3) :
    G.vertexOf x = {x, G.rot x, G.rot (G.rot x)} := by
  obtain ⟨h1, h2⟩ := rot_ne_of_card_vertexOf_eq_three h
  have h12 : G.rot (G.rot x) ≠ G.rot x := fun h12 => h1 (G.rot.injective h12)
  have hsub : ({x, G.rot x, G.rot (G.rot x)} : Finset H) ⊆ G.vertexOf x := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact G.self_mem_vertexOf _
    · exact G.rot_mem_vertexOf _
    · have := G.rot_mem_vertexOf (G.rot x)
      rwa [G.vertexOf_rot] at this
  have hcard : ({x, G.rot x, G.rot (G.rot x)} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h12.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.symm, h2.symm⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- At a vertex with exactly three darts, `σ³(x) = x`. -/
theorem rot_rot_rot_of_card_vertexOf_eq_three {x : H} (h : (G.vertexOf x).card = 3) :
    G.rot (G.rot (G.rot x)) = x := by
  obtain ⟨h1, h2⟩ := rot_ne_of_card_vertexOf_eq_three h
  have hmem : G.rot (G.rot (G.rot x)) ∈ G.vertexOf x := by
    have := G.self_mem_vertexOf (G.rot (G.rot (G.rot x)))
    rwa [G.vertexOf_rot, G.vertexOf_rot, G.vertexOf_rot] at this
  rw [vertexOf_eq_of_card_vertexOf_eq_three h] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h3 | h3 | h3
  · exact h3
  · exact absurd (G.rot.injective h3) h2
  · exact absurd (G.rot.injective (G.rot.injective h3)) h1

/-! ### The darts of a square face -/

variable (G) in
/-- The eight darts `c_k`, `c̄_k` of the edges of the face `(c₁, c₂, c₃, c₄)` through `c`, with
`c_{k+1} = squareCorner c k`. -/
def squareEdgeDarts (c : H) : Set H :=
  {d | ∃ k, G.squareCorner c k = d ∨ G.inv (G.squareCorner c k) = d}

/-- The square move at `c` does not change the darts `c_k`, `c̄_k` of the edges of the face. -/
@[simp]
theorem squareEdgeDarts_squareMove (c : H) :
    (G.squareMove c).squareEdgeDarts c = G.squareEdgeDarts c := rfl

omit [Fintype H] [DecidableEq H] in
/-- The first corner dart of the face through `c` is `c` itself: `c₁ = c`. -/
@[simp]
theorem squareCorner_zero (c : H) : G.squareCorner c 0 = c := by
  simp [squareCorner]

/-- Away from the corners of the face, the square move does not change the turns. -/
theorem turn_squareMove_of_notMem {c z : H} (h : G.vertexOf z ∉ G.squareVertices c) :
    (G.squareMove c).turn z = G.turn z := by
  unfold turn
  rw [colour_squareMove_of_notMem G h]
  rfl

namespace IsSquareMoveFace

variable {c : H} (hq : G.IsSquareMoveFace c)

include hq

/-- `φ(c_k) = c_{k+1}`, indices modulo `4`. -/
theorem facePerm_squareCorner (k : Fin 4) :
    G.facePerm (G.squareCorner c k) = G.squareCorner c (k + 1) := by
  rw [squareCorner, squareCorner, ← Perm.mul_apply, ← pow_succ', Fin.val_add_one]
  split_ifs with h
  · subst h
    simpa using hq.facePerm_pow_four
  · rfl

/-- `σ(c̄_k) = c_{k+1}`: the dart `c̄_k` lies at `v(c_{k+1})`. -/
theorem rot_inv_squareCorner (k : Fin 4) :
    G.rot (G.inv (G.squareCorner c k)) = G.squareCorner c (k + 1) :=
  (G.facePerm_apply _).symm.trans (hq.facePerm_squareCorner k)

/-- The dart `c̄_k` lies at the vertex `v(c_{k+1})`. -/
theorem vertexOf_inv_squareCorner (k : Fin 4) :
    G.vertexOf (G.inv (G.squareCorner c k)) = G.vertexOf (G.squareCorner c (k + 1)) := by
  rw [← hq.rot_inv_squareCorner k, G.vertexOf_rot]

/-- The rotation at `v(c_{k+1})` is the `3`-cycle `(c̄_k c_{k+1} e_{k+1})`: `σ(e_{k+1}) = c̄_k`. -/
theorem rot_rot_squareCorner (k : Fin 4) :
    G.rot (G.rot (G.squareCorner c (k + 1))) = G.inv (G.squareCorner c k) := by
  have h := rot_rot_rot_of_card_vertexOf_eq_three (x := G.inv (G.squareCorner c k))
    (by rw [hq.vertexOf_inv_squareCorner]; exact hq.card_vertexOf _)
  rwa [hq.rot_inv_squareCorner] at h

/-- `σ(c_k) ≠ c_k`. -/
theorem rot_squareCorner_ne (k : Fin 4) : G.rot (G.squareCorner c k) ≠ G.squareCorner c k :=
  (rot_ne_of_card_vertexOf_eq_three (hq.card_vertexOf k)).1

/-- `σ(c_{k+1}) ≠ c̄_k`. -/
theorem rot_squareCorner_ne_inv (k : Fin 4) :
    G.rot (G.squareCorner c (k + 1)) ≠ G.inv (G.squareCorner c k) := by
  intro h
  have := hq.rot_rot_squareCorner k
  rw [h, hq.rot_inv_squareCorner] at this
  exact hq.rot_squareCorner_ne (k + 1) (h.trans this.symm)

/-- The vertex `v(c_k)` is not a boundary vertex. -/
theorem not_isBoundaryVertex (k : Fin 4) :
    ¬G.IsBoundaryVertex (G.vertexOf (G.squareCorner c k)) :=
  (G.mem_internalVertices.1 (hq.vertexOf_mem_internalVertices k)).2

/-- The vertex of `c̄_k` is not a boundary vertex. -/
theorem not_isBoundaryVertex_inv (k : Fin 4) :
    ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.squareCorner c k))) := by
  rw [hq.vertexOf_inv_squareCorner]
  exact hq.not_isBoundaryVertex _

/-- The vertex of `e_k = σ(c_k)` is not a boundary vertex. -/
theorem not_isBoundaryVertex_rot (k : Fin 4) :
    ¬G.IsBoundaryVertex (G.vertexOf (G.rot (G.squareCorner c k))) := by
  rw [G.vertexOf_rot]
  exact hq.not_isBoundaryVertex _

/-- A dart whose vertex is no corner of the face is not one of the darts `c_k`, `c̄_k`. -/
theorem notMem_squareEdgeDarts {d : H}
    (h : ∀ k, G.vertexOf d ≠ G.vertexOf (G.squareCorner c k)) : d ∉ G.squareEdgeDarts c := by
  rintro ⟨k, rfl | rfl⟩
  · exact h k rfl
  · exact h (k + 1) (hq.vertexOf_inv_squareCorner k)

/-- The dart `e_k = σ(c_k)` is not one of the darts `c_j`, `c̄_j`. -/
theorem rot_squareCorner_notMem (k : Fin 4) :
    G.rot (G.squareCorner c k) ∉ G.squareEdgeDarts c := by
  rintro ⟨j, h | h⟩
  · have hv := congrArg G.vertexOf h
    rw [G.vertexOf_rot] at hv
    rw [hq.injective hv] at h
    exact hq.rot_squareCorner_ne k h.symm
  · have hv := congrArg G.vertexOf h
    rw [G.vertexOf_rot, hq.vertexOf_inv_squareCorner] at hv
    have hk := hq.injective hv
    subst hk
    exact hq.rot_squareCorner_ne_inv j h.symm

variable (hG : G.IsPlabicGraph)

include hG

/-- The dart `ē_k` is not one of the darts `c_j`, `c̄_j`. -/
theorem inv_rot_squareCorner_notMem (k : Fin 4) :
    G.inv (G.rot (G.squareCorner c k)) ∉ G.squareEdgeDarts c := by
  rintro ⟨j, h | h⟩
  · refine hq.rot_squareCorner_notMem k ⟨j, Or.inr ?_⟩
    rw [h, hG.inv_involutive]
  · refine hq.rot_squareCorner_notMem k ⟨j, Or.inl ?_⟩
    exact G.inv.injective h

/-- The dart `c̄_k` has the colour of `c_{k+1}`. -/
theorem colour_inv_squareCorner (k : Fin 4) :
    G.colour (G.inv (G.squareCorner c k)) = G.colour (G.squareCorner c (k + 1)) := by
  rw [← hq.rot_inv_squareCorner k, hG.colour_rot]
  rw [hq.vertexOf_inv_squareCorner]
  exact hq.not_isBoundaryVertex _

/-- The dart `e_k = σ(c_k)` has the colour of `c_k`. -/
theorem colour_rot_squareCorner (k : Fin 4) :
    G.colour (G.rot (G.squareCorner c k)) = G.colour (G.squareCorner c k) :=
  hG.colour_rot _ (hq.not_isBoundaryVertex k)

omit hG in
/-- The colours alternate around the face. -/
theorem colour_squareCorner_add_one (k : Fin 4) :
    G.colour (G.squareCorner c (k + 1)) = (G.colour (G.squareCorner c k)).swap := by
  have := hq.colour_ne k
  revert this
  cases G.colour (G.squareCorner c k) <;> cases G.colour (G.squareCorner c (k + 1)) <;> simp

omit hG in
/-- The colours alternate around the face, read backwards. -/
theorem colour_squareCorner_eq_swap (k : Fin 4) :
    G.colour (G.squareCorner c k) = (G.colour (G.squareCorner c (k + 1))).swap := by
  rw [hq.colour_squareCorner_add_one]
  cases G.colour (G.squareCorner c k) <;> rfl

/-! ### The trip map at the corners -/

/-- If `v(c_{k+1})` is black, `T(c_k) = c_{k+1}`. -/
theorem tripMap_squareCorner_of_black (k : Fin 4)
    (h : G.colour (G.squareCorner c (k + 1)) = .black) :
    G.tripMap (G.squareCorner c k) = G.squareCorner c (k + 1) := by
  rw [tripMap_apply, turn_of_black (hq.not_isBoundaryVertex_inv k)
    (by rw [hq.colour_inv_squareCorner hG, h]),
    hq.rot_inv_squareCorner]

/-- If `v(c_{k+1})` is white, `T(c_k) = e_{k+1}`. -/
theorem tripMap_squareCorner_of_white (k : Fin 4)
    (h : G.colour (G.squareCorner c (k + 1)) = .white) :
    G.tripMap (G.squareCorner c k) = G.rot (G.squareCorner c (k + 1)) := by
  rw [tripMap_apply, turn_of_white (hq.not_isBoundaryVertex_inv k)
    (by rw [hq.colour_inv_squareCorner hG, h]),
    Equiv.symm_apply_eq, hq.rot_rot_squareCorner]

/-- If `v(c_k)` is black, `T(c̄_k) = e_k`. -/
theorem tripMap_inv_squareCorner_of_black (k : Fin 4)
    (h : G.colour (G.squareCorner c k) = .black) :
    G.tripMap (G.inv (G.squareCorner c k)) = G.rot (G.squareCorner c k) := by
  rw [tripMap_apply, hG.inv_involutive, turn_of_black (hq.not_isBoundaryVertex _) h]

/-- If `v(c_{k+1})` is white, `T(c̄_{k+1}) = c̄_k`. -/
theorem tripMap_inv_squareCorner_of_white (k : Fin 4)
    (h : G.colour (G.squareCorner c (k + 1)) = .white) :
    G.tripMap (G.inv (G.squareCorner c (k + 1))) = G.inv (G.squareCorner c k) := by
  rw [tripMap_apply, hG.inv_involutive, turn_of_white (hq.not_isBoundaryVertex _) h,
    Equiv.symm_apply_eq, hq.rot_inv_squareCorner]

/-- If `v(c_{k+1})` is black, `T(ē_{k+1}) = c̄_k`. -/
theorem tripMap_inv_rot_squareCorner_of_black (k : Fin 4)
    (h : G.colour (G.squareCorner c (k + 1)) = .black) :
    G.tripMap (G.inv (G.rot (G.squareCorner c (k + 1)))) = G.inv (G.squareCorner c k) := by
  rw [tripMap_apply, hG.inv_involutive, turn_of_black (hq.not_isBoundaryVertex_rot _)
    (by rw [hq.colour_rot_squareCorner hG, h]),
    hq.rot_rot_squareCorner]

/-- If `v(c_k)` is white, `T(ē_k) = c_k`. -/
theorem tripMap_inv_rot_squareCorner_of_white (k : Fin 4)
    (h : G.colour (G.squareCorner c k) = .white) :
    G.tripMap (G.inv (G.rot (G.squareCorner c k))) = G.squareCorner c k := by
  rw [tripMap_apply, hG.inv_involutive, turn_of_white (hq.not_isBoundaryVertex_rot _)
    (by rw [hq.colour_rot_squareCorner hG, h]),
    Equiv.symm_apply_apply]

/-- **Trips through a square**. Let `q = (c₁, c₂, c₃, c₄)` be a face of the plabic graph `G` at
which a square move applies, with `v(c₁)` black, and put `e_k = σ(c_k)`. Here `c_{k+1}` is
`G.squareCorner c k` for `k : Fin 4`, so `c₁ = c`. Then the trip map `T` satisfies
`T(ē₁) = c̄₄`, `T(c̄₄) = c̄₃`, `T(c̄₃) = e₃`;
`T(ē₂) = c₂`, `T(c₂) = c₃`, `T(c₃) = e₄`;
`T(ē₃) = c̄₂`, `T(c̄₂) = c̄₁`, `T(c̄₁) = e₁`;
`T(ē₄) = c₄`, `T(c₄) = c₁`, `T(c₁) = e₂`. -/
@[cluster_algebras "lem_square_trip_map"]
theorem tripMap_eq (hc : G.colour c = .black) :
    (G.tripMap (G.inv (G.rot (G.squareCorner c 0))) = G.inv (G.squareCorner c 3) ∧
      G.tripMap (G.inv (G.squareCorner c 3)) = G.inv (G.squareCorner c 2) ∧
      G.tripMap (G.inv (G.squareCorner c 2)) = G.rot (G.squareCorner c 2)) ∧
    (G.tripMap (G.inv (G.rot (G.squareCorner c 1))) = G.squareCorner c 1 ∧
      G.tripMap (G.squareCorner c 1) = G.squareCorner c 2 ∧
      G.tripMap (G.squareCorner c 2) = G.rot (G.squareCorner c 3)) ∧
    (G.tripMap (G.inv (G.rot (G.squareCorner c 2))) = G.inv (G.squareCorner c 1) ∧
      G.tripMap (G.inv (G.squareCorner c 1)) = G.inv (G.squareCorner c 0) ∧
      G.tripMap (G.inv (G.squareCorner c 0)) = G.rot (G.squareCorner c 0)) ∧
    (G.tripMap (G.inv (G.rot (G.squareCorner c 3))) = G.squareCorner c 3 ∧
      G.tripMap (G.squareCorner c 3) = G.squareCorner c 0 ∧
      G.tripMap (G.squareCorner c 0) = G.rot (G.squareCorner c 1)) := by
  have h0 : G.colour (G.squareCorner c 0) = .black := by rwa [squareCorner_zero]
  have h1 : G.colour (G.squareCorner c 1) = .white := by
    have := hq.colour_squareCorner_add_one 0
    rwa [h0, zero_add] at this
  have h2 : G.colour (G.squareCorner c 2) = .black := by
    have := hq.colour_squareCorner_add_one 1
    rwa [h1] at this
  have h3 : G.colour (G.squareCorner c 3) = .white := by
    have := hq.colour_squareCorner_add_one 2
    rwa [h2] at this
  exact ⟨⟨hq.tripMap_inv_rot_squareCorner_of_black hG 3 h0,
      hq.tripMap_inv_squareCorner_of_white hG 2 h3,
      hq.tripMap_inv_squareCorner_of_black hG 2 h2⟩,
    ⟨hq.tripMap_inv_rot_squareCorner_of_white hG 1 h1,
      hq.tripMap_squareCorner_of_black hG 1 h2,
      hq.tripMap_squareCorner_of_white hG 2 h3⟩,
    ⟨hq.tripMap_inv_rot_squareCorner_of_black hG 1 h2,
      hq.tripMap_inv_squareCorner_of_white hG 0 h1,
      hq.tripMap_inv_squareCorner_of_black hG 0 h0⟩,
    ⟨hq.tripMap_inv_rot_squareCorner_of_white hG 3 h3,
      hq.tripMap_squareCorner_of_black hG 3 h0,
      hq.tripMap_squareCorner_of_white hG 0 h1⟩⟩

/-! ### First returns to the darts off the square -/

/-- The darts that are in `B` or are legs are not among the darts `c_k`, `c̄_k`: they lie at
boundary vertices. -/
theorem setOf_mem_bdry_or_isLeg_subset :
    {z | z ∈ G.bdry ∨ G.IsLeg z} ⊆ (G.squareEdgeDarts c)ᶜ := by
  intro z hz
  refine hq.notMem_squareEdgeDarts fun k hk => hq.not_isBoundaryVertex k ?_
  rw [← hk]
  rcases hz with hb | ⟨j, rfl⟩
  · exact G.isBoundaryVertex_vertexOf_of_mem hb
  · exact (G.mem_boundaryVertices.1 (hG.bvertex_mem j)).2

/-- Every trip meets a dart that is not one of the darts `c_k`, `c̄_k`. -/
theorem exists_sameCycle_notMem_squareEdgeDarts (x : H) :
    ∃ y ∈ (G.squareEdgeDarts c)ᶜ, hG.tripEquiv.SameCycle x y := by
  have one : G.tripMap x ∉ G.squareEdgeDarts c →
      ∃ y ∈ (G.squareEdgeDarts c)ᶜ, hG.tripEquiv.SameCycle x y := fun h =>
    ⟨G.tripMap x, h, sameCycle_apply_right.2 (SameCycle.refl _ _)⟩
  have two : G.tripMap (G.tripMap x) ∉ G.squareEdgeDarts c →
      ∃ y ∈ (G.squareEdgeDarts c)ᶜ, hG.tripEquiv.SameCycle x y := fun h =>
    ⟨G.tripMap (G.tripMap x), h,
      sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))⟩
  rcases em' (x ∈ G.squareEdgeDarts c) with hx | ⟨k, rfl | rfl⟩
  · exact ⟨x, hx, SameCycle.refl _ _⟩
  · cases hcol : G.colour (G.squareCorner c (k + 1))
    · apply one
      rw [hq.tripMap_squareCorner_of_white hG k hcol]
      exact hq.rot_squareCorner_notMem _
    · apply two
      have hcol' : G.colour (G.squareCorner c (k + 1 + 1)) = .white := by
        rw [hq.colour_squareCorner_add_one, hcol]; rfl
      rw [hq.tripMap_squareCorner_of_black hG k hcol,
        hq.tripMap_squareCorner_of_white hG (k + 1) hcol']
      exact hq.rot_squareCorner_notMem _
  · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by simp⟩
    cases hcol : G.colour (G.squareCorner c (i + 1))
    · apply two
      have hcol' : G.colour (G.squareCorner c i) = .black := by
        rw [hq.colour_squareCorner_eq_swap, hcol]; rfl
      rw [hq.tripMap_inv_squareCorner_of_white hG i hcol,
        hq.tripMap_inv_squareCorner_of_black hG i hcol']
      exact hq.rot_squareCorner_notMem _
    · apply one
      rw [hq.tripMap_inv_squareCorner_of_black hG _ hcol]
      exact hq.rot_squareCorner_notMem _

/-- A trip entering the square along `ē_k` leaves it along `e_{k+2}`: the first return of the trip
map to the darts off the edges of the face sends `ē_k` to `e_{k+2}`, whatever the colours. -/
theorem coe_firstReturn_inv_rot_squareCorner (k : Fin 4) (y : ((G.squareEdgeDarts c)ᶜ : Set H))
    (hy : (y : H) = G.inv (G.rot (G.squareCorner c k))) :
    (firstReturn hG.tripEquiv (G.squareEdgeDarts c)ᶜ y : H) =
      G.rot (G.squareCorner c (k + 2)) := by
  have hE : ∀ j, G.squareCorner c j ∉ (G.squareEdgeDarts c)ᶜ := fun j h => h ⟨j, Or.inl rfl⟩
  have hE' : ∀ j, G.inv (G.squareCorner c j) ∉ (G.squareEdgeDarts c)ᶜ := fun j h =>
    h ⟨j, Or.inr rfl⟩
  cases hcol : G.colour (G.squareCorner c k)
  · have hc1 : G.colour (G.squareCorner c (k + 1)) = .black := by
      rw [hq.colour_squareCorner_add_one, hcol]; rfl
    have hc2 : G.colour (G.squareCorner c (k + 1 + 1)) = .white := by
      rw [hq.colour_squareCorner_add_one, hc1]; rfl
    have e1 : G.tripMap y = G.squareCorner c k := by
      rw [hy]; exact hq.tripMap_inv_rot_squareCorner_of_white hG k hcol
    have e3 := hq.tripMap_squareCorner_of_white hG (k + 1) hc2
    rw [show k + 1 + 1 = k + 2 by rw [add_assoc]; rfl] at e3
    exact coe_firstReturn_of_apply_apply_apply e1 (hq.tripMap_squareCorner_of_black hG k hc1) e3
      (hE _) (hE _) (hq.rot_squareCorner_notMem _)
  · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 + 1 := ⟨k - 1 - 1, by simp⟩
    have hc1 : G.colour (G.squareCorner c (i + 1)) = .white := by
      rw [hq.colour_squareCorner_eq_swap, hcol]; rfl
    have hc0 : G.colour (G.squareCorner c i) = .black := by
      rw [hq.colour_squareCorner_eq_swap, hc1]; rfl
    have e1 : G.tripMap y = G.inv (G.squareCorner c (i + 1)) := by
      rw [hy]; exact hq.tripMap_inv_rot_squareCorner_of_black hG (i + 1) hcol
    have hi : i + 1 + 1 + 2 = i := by
      rw [add_assoc, add_assoc, show (1 + (1 + 2) : Fin 4) = 0 from rfl, add_zero]
    rw [hi]
    exact coe_firstReturn_of_apply_apply_apply e1 (hq.tripMap_inv_squareCorner_of_white hG i hc1)
      (hq.tripMap_inv_squareCorner_of_black hG i hc0) (hE' _) (hE' _)
      (hq.rot_squareCorner_notMem _)

/-- **The first returns agree.** The trip maps of `G` and of its square move at `q` have the same
first-return map to the darts other than `c_k`, `c̄_k`. -/
theorem firstReturnPerm_tripEquiv_squareMove :
    firstReturnPerm (hG.squareMove c).tripEquiv (G.squareEdgeDarts c)ᶜ =
      firstReturnPerm hG.tripEquiv (G.squareEdgeDarts c)ᶜ := by
  ext y
  simp only [coe_firstReturnPerm]
  by_cases hv : ∃ k, G.vertexOf (G.inv y) = G.vertexOf (G.squareCorner c k)
  · obtain ⟨k, hk⟩ := hv
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by simp⟩
    have hmem : G.inv y ∈ G.vertexOf (G.inv (G.squareCorner c i)) := by
      rw [hq.vertexOf_inv_squareCorner, ← hk]
      exact G.self_mem_vertexOf _
    rw [vertexOf_eq_of_card_vertexOf_eq_three (by
      rw [hq.vertexOf_inv_squareCorner]; exact hq.card_vertexOf _), hq.rot_inv_squareCorner] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact absurd ⟨i, Or.inl (G.inv.injective h).symm⟩ y.2
    · refine absurd ⟨i + 1, Or.inr ?_⟩ y.2
      rw [← h, hG.inv_involutive]
    · have hy : (y : H) = G.inv (G.rot (G.squareCorner c (i + 1))) := by
        rw [← h, hG.inv_involutive]
      have h' : ((firstReturn (hG.squareMove c).tripEquiv (G.squareEdgeDarts c)ᶜ y : H)) =
          G.rot (G.squareCorner c (i + 1 + 2)) :=
        hq.squareMove.coe_firstReturn_inv_rot_squareCorner (hG.squareMove c) (i + 1) y hy
      rw [h', hq.coe_firstReturn_inv_rot_squareCorner hG (i + 1) y hy]
  · simp only [not_exists] at hv
    have hnot : G.vertexOf (G.inv y) ∉ G.squareVertices c := fun h => by
      obtain ⟨k, hk⟩ := mem_squareVertices.1 h
      exact hv k hk.symm
    have hT : (G.squareMove c).tripMap y = G.tripMap y := turn_squareMove_of_notMem hnot
    have hTY : G.tripMap y ∈ (G.squareEdgeDarts c)ᶜ := by
      refine hq.notMem_squareEdgeDarts ?_
      rw [tripMap_apply, vertexOf_turn]
      exact hv
    rw [coe_firstReturn_of_apply_mem (π := hG.tripEquiv) hTY]
    refine (coe_firstReturn_of_apply_mem (π := (hG.squareMove c).tripEquiv) ?_).trans hT
    change (G.squareMove c).tripMap y ∈ _
    rwa [hT]

end IsSquareMoveFace

/-- A plabic graph has a roundtrip exactly when some orbit of its trip map, as a permutation of
all darts, avoids the darts that are in `B` or are legs. -/
theorem IsPlabicGraph.hasRoundtrip_iff_exists_forall_sameCycle (hG : G.IsPlabicGraph) :
    G.HasRoundtrip ↔
      ∃ x, ∀ z, hG.tripEquiv.SameCycle x z → z ∉ {z | z ∈ G.bdry ∨ G.IsLeg z} := by
  have hit : ∀ (n : ℕ) (d : H), G.tripMap^[n] d ∈ G.bdry ↔ d ∈ G.bdry := by
    intro n d
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', tripMap_mem_bdry_iff hG, ih]
  rw [hasRoundtrip_iff]
  constructor
  · rintro ⟨d, hd, h⟩
    refine ⟨d, fun z hz => ?_⟩
    obtain ⟨n, rfl⟩ := hz.exists_nat_pow_eq
    rw [hG.tripEquiv_pow_apply]
    rintro (hb | hl)
    · exact hd ((hit n d).1 hb)
    · exact h n hl
  · rintro ⟨x, hx⟩
    refine ⟨x, fun hb => hx x (SameCycle.refl _ _) (Or.inl hb), fun n hl => hx _ ?_ (Or.inr hl)⟩
    rw [← hG.tripEquiv_pow_apply]
    exact sameCycle_pow_right.2 (SameCycle.refl _ _)

/-- **A square move keeps roundtrips**: if a square move applies to the plabic graph `G` at the
face `q` through `c`, then the square move of `G` at `q` has a roundtrip if and only if `G` has
one. -/
@[cluster_algebras "lem_square_move_roundtrip"]
theorem IsPlabicGraph.hasRoundtrip_squareMove_iff (hG : G.IsPlabicGraph) {c : H}
    (hq : G.IsSquareMoveFace c) : (G.squareMove c).HasRoundtrip ↔ G.HasRoundtrip := by
  have hG' := hG.squareMove c
  have hq' := hq.squareMove
  have h1 := exists_forall_sameCycle_notMem_iff hG.tripEquiv
    (hq.setOf_mem_bdry_or_isLeg_subset hG) (hq.exists_sameCycle_notMem_squareEdgeDarts hG)
  have h2 := exists_forall_sameCycle_notMem_iff (Y := (G.squareEdgeDarts c)ᶜ)
    (L := {z | z ∈ G.bdry ∨ G.IsLeg z}) hG'.tripEquiv
    (hq'.setOf_mem_bdry_or_isLeg_subset hG') (hq'.exists_sameCycle_notMem_squareEdgeDarts hG')
  rw [hq.firstReturnPerm_tripEquiv_squareMove hG] at h2
  rw [hasRoundtrip_iff_exists_forall_sameCycle hG', hasRoundtrip_iff_exists_forall_sameCycle hG]
  exact h2.trans h1.symm

end PlabicData

end ClusterAlgebras
