/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.LollipopMoves
public import ClusterAlgebras.Plabic.FlipMoves
public import ClusterAlgebras.Plabic.NormalPlabic
public import ClusterAlgebras.Plabic.Excision
public import ClusterAlgebras.Plabic.Trees
public import ClusterAlgebras.Plabic.PlabicQuiver

/-!
# Cutting a plabic graph along a loop

Let `K` be a nearly leafless plabic graph and `u` an internal vertex of `K` whose rotation is the
cycle `(d, a₁, …, a_k, d̄, b₁, …, b_l)` with `k, l ≥ 1`, such that the side of `(u, d)` contains no
dart of the boundary. Splitting `u` into the two vertices `(e, a₁, …, a_k)` and
`(e*, d̄, b₁, …, b_l, d)` joined by a new edge `{e, e*}`, the side of `(u, d)` together with `e` is
closed under the rotation and, except at `e`, under the involution. Cutting the new edge, the
inside becomes a plabic graph `R` with one boundary vertex (its leg is glued to `e`), the outside
becomes a plabic graph `Y` with a new leaf `{f}` glued to `e*`, and gluing `R` into the leaf `{f}`
gives back the splitting. Euler's relation for the splitting, together with the Euler bound for
the connected rotation systems `Y` and `R`, shows that both satisfy Euler's relation.

## Main definitions

* `ClusterAlgebras.PlabicData.IsLoopCutSite M C e`: a set `C` of darts of `M` containing `e` but
  not `ē`, closed under the rotation and, away from `e`, under the involution, and containing no
  boundary arc and no leg.
* `ClusterAlgebras.PlabicData.loopCutInside`, `ClusterAlgebras.PlabicData.loopCutOutside`: the
  inside `R` (with one boundary vertex) and the outside `Y` (with a new leaf `{f}`) of the cut of
  `M` along the edge `{e, ē}`.

## Main results

* `ClusterAlgebras.PlabicData.isPlabicGraph_loopCutInside`,
  `ClusterAlgebras.PlabicData.isPlabicGraph_loopCutOutside`,
  `ClusterAlgebras.PlabicData.isomorphic_leafGluing_loopCut`: both sides of a cut of a plabic
  graph are plabic graphs, and gluing the inside into the leaf of the outside gives back `M`.
* `ClusterAlgebras.PlabicGraph.exists_leafGluing_of_loop`: cutting a graph along a loop.

## Implementation notes

* The darts of the inside `R` are the darts `C` of the side together with `e`, and three new
  darts: the leg `g = Sum.inr 0`, and the boundary arcs `p = Sum.inr 1`, `p̄ = Sum.inr 2`. The
  darts of the outside `Y` are the remaining darts of the splitting together with the new leaf
  `f = Sum.inr ()`. The sets of darts of `Y` and `R` are disjoint because the gluing lives on a
  subset of `H_Y ⊕ H_R` (`ClusterAlgebras.PlabicData.leafGluing`); the gluing is isomorphic to the
  splitting, which is how `K ∼ Y⟨f ← R⟩` is obtained.
* The rotation at `u = v(d)` being the cycle `(d, a₁, …, a_k, d̄, b₁, …, b_l)` with `k, l ≥ 1` is
  stated as `d̄ ∈ v(d)`, `σ d ≠ d̄` and `σ d̄ ≠ d`.
* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

open Finset Function Equiv Equiv.Perm

namespace ClusterAlgebras

/-! ### Orbits of sums and restrictions of permutations -/

section SumCongr

variable {α β : Type*}

private theorem sumCongr_zpow' (a : Perm α) (b : Perm β) (n : ℤ) :
    Perm.sumCongr a b ^ n = Perm.sumCongr (a ^ n) (b ^ n) := by
  have := map_zpow (sumCongrHom α β) (a, b) n
  simpa using this.symm

private theorem sameCycle_sumCongr_inl' (a : Perm α) (b : Perm β) {x y : α} :
    (Perm.sumCongr a b).SameCycle (Sum.inl x) (Sum.inl y) ↔ a.SameCycle x y := by
  constructor
  · rintro ⟨n, hn⟩
    rw [sumCongr_zpow', Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] at hn
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [sumCongr_zpow', Perm.sumCongr_apply, Sum.map_inl, hn]⟩

private theorem not_sameCycle_sumCongr_inl_inr' (a : Perm α) (b : Perm β) {x : α} {y : β} :
    ¬(Perm.sumCongr a b).SameCycle (Sum.inl x) (Sum.inr y) := by
  rintro ⟨n, hn⟩
  rw [sumCongr_zpow', Perm.sumCongr_apply, Sum.map_inl] at hn
  exact Sum.inl_ne_inr hn

private theorem not_sameCycle_sumCongr_inr_inl' (a : Perm α) (b : Perm β) {x : β} {y : α} :
    ¬(Perm.sumCongr a b).SameCycle (Sum.inr x) (Sum.inl y) := fun h =>
  not_sameCycle_sumCongr_inl_inr' a b h.symm

end SumCongr

/-- An equivalence intertwining two permutations maps their cycles onto each other. -/
private theorem sameCycle_map_equiv {α β : Type*} {f : Perm α} {g : Perm β} (e : α ≃ β)
    (h : ∀ x, e (f x) = g (e x)) {x y : α} : g.SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  have hpow : ∀ n : ℤ, ∀ x, e ((f ^ n) x) = (g ^ n) (e x) := by
    have hc : e.permCongr f = g := by
      ext x
      simpa [Equiv.permCongr_apply] using h (e.symm x)
    intro n x
    rw [← hc]
    have : (e.permCongr f) ^ n = e.permCongr (f ^ n) := by
      simpa using (map_zpow (Equiv.permCongrHom e).toMonoidHom f n).symm
    rw [this, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, e.injective (by rw [hpow, hn])⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hpow, hn]⟩

private theorem mem_of_sameCycle_of_mapsTo'' {α : Type*} [Finite α] {π : Perm α} {S : Set α}
    (hS : ∀ y ∈ S, π y ∈ S) {x y : α} (hx : x ∈ S) (h : π.SameCycle x y) : y ∈ S := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact Set.MapsTo.perm_pow hS n hx

namespace RotationSystem

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']

/-- An equivalence of darts intertwining the rotations maps vertices onto vertices. -/
private theorem map_vertexOf_of_semiconj (R : RotationSystem H) (R' : RotationSystem H')
    (e : H ≃ H') (h : ∀ x, e (R.rot x) = R'.rot (e x)) (x : H) :
    (R.vertexOf x).map e.toEmbedding = R'.vertexOf (e x) := by
  ext y
  rw [mem_map_equiv, mem_vertexOf, mem_vertexOf, ← sameCycle_map_equiv e h,
    Equiv.apply_symm_apply]

/-- An equivalence of darts intertwining the rotations and the involutions preserves the numbers
of vertices, edges and orbits of the face permutation. -/
private theorem card_eq_of_semiconj (R : RotationSystem H) (R' : RotationSystem H')
    (e : H ≃ H') (hrot : ∀ x, e (R.rot x) = R'.rot (e x))
    (hinv : ∀ x, e (R.inv x) = R'.inv (e x)) :
    R.vertices.card = R'.vertices.card ∧ R.edges.card = R'.edges.card ∧
      R.faceOrbits.card = R'.faceOrbits.card := by
  have hφ : ∀ x, e (R.facePerm x) = R'.facePerm (e x) := fun x => by
    rw [facePerm_apply, facePerm_apply, hrot, hinv]
  have himg : ∀ (F : H → Finset H) (F' : H' → Finset H'),
      (∀ x, (F x).map e.toEmbedding = F' (e x)) →
      ((univ : Finset H).image F).card = ((univ : Finset H').image F').card := by
    intro F F' hF
    have : (univ : Finset H').image F' = ((univ : Finset H).image F).image
        (fun s => s.map e.toEmbedding) := by
      ext s
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨F (e.symm x), ⟨_, rfl⟩, by rw [hF, Equiv.apply_symm_apply]⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨e x, (hF x).symm⟩
    rw [this, card_image_of_injective _ (map_injective _)]
  refine ⟨himg _ _ (R.map_vertexOf_of_semiconj R' e hrot), himg _ _ fun x => ?_,
    himg _ _ fun x => ?_⟩
  · ext y
    simp only [edgeOf, mem_map_equiv, mem_insert, mem_singleton, ← hinv]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [← h, Equiv.apply_symm_apply])
      · exact Or.inr (by rw [← h, Equiv.apply_symm_apply])
    · rintro (rfl | rfl) <;> simp
  · ext y
    rw [mem_map_equiv, mem_faceOf, mem_faceOf, ← sameCycle_map_equiv e hφ,
      Equiv.apply_symm_apply]

end RotationSystem

/-! ### Cutting a plabic graph along an edge -/

namespace PlabicData

variable {H : Type} [DecidableEq H] {b : ℕ}

/-- The hypotheses for cutting `M` along the edge `{e, ē}` with inside `C`: `C` contains `e` but
not `ē`, is closed under the rotation and, away from `e`, under the involution, and contains no
boundary arc and no leg. -/
structure IsLoopCutSite (M : PlabicData H b) (C : Finset H) (e : H) : Prop where
  /-- `d ↦ d̄` is an involution. -/
  inv_involutive : Involutive M.inv
  /-- `d ↦ d̄` has no fixed point. -/
  inv_ne : ∀ x, M.inv x ≠ x
  /-- `e ∈ C`. -/
  mem : e ∈ C
  /-- `ē ∉ C`. -/
  inv_notMem : M.inv e ∉ C
  /-- `C` is closed under `d ↦ d̄` away from `e`. -/
  inv_mem : ∀ c ∈ C, c ≠ e → M.inv c ∈ C
  /-- `C` is closed under the rotation. -/
  rot_mem : ∀ c ∈ C, M.rot c ∈ C
  /-- `C` contains no boundary arc. -/
  notMem_bdry : ∀ c ∈ C, c ∉ M.bdry
  /-- `C` contains no leg. -/
  leg_notMem : ∀ i, M.leg i ∉ C

variable {M : PlabicData H b} {C : Finset H} {e : H}

namespace IsLoopCutSite

variable (h : M.IsLoopCutSite C e)

include h

omit [DecidableEq H] in
/-- A dart lies in `C` if and only if its image under the rotation does. -/
theorem rot_mem_iff (x : H) : M.rot x ∈ C ↔ x ∈ C := by
  classical
  refine ⟨fun hx => ?_, h.rot_mem x⟩
  have hsub : C.image M.rot ⊆ C := image_subset_iff.2 h.rot_mem
  have heq := eq_of_subset_of_card_le hsub (by rw [card_image_of_injective _ M.rot.injective])
  rw [← heq] at hx
  obtain ⟨c, hc, hcx⟩ := mem_image.1 hx
  rwa [← M.rot.injective hcx]

omit [DecidableEq H] in
/-- For a dart `x ∉ C`, `x̄ ∈ C` if and only if `x = ē`. -/
theorem inv_mem_iff_of_notMem {x : H} (hx : x ∉ C) : M.inv x ∈ C ↔ x = M.inv e := by
  constructor
  · intro hix
    by_cases hie : M.inv x = e
    · rw [← hie, h.inv_involutive x]
    · have := h.inv_mem _ hix hie
      rw [h.inv_involutive x] at this
      exact absurd this hx
  · rintro rfl
    rw [h.inv_involutive e]
    exact h.mem

omit [DecidableEq H] in
/-- For a dart `c ∈ C`, `c̄ ≠ e`. -/
theorem inv_ne_of_mem {c : H} (hc : c ∈ C) : M.inv c ≠ e := fun hie =>
  h.inv_notMem (by rwa [← hie, h.inv_involutive c])

variable [Fintype H]

/-- The vertex of a dart of `C` is contained in `C`. -/
theorem vertexOf_subset {c : H} (hc : c ∈ C) : ∀ y ∈ M.vertexOf c, y ∈ C := fun _ hy =>
  mem_of_sameCycle_of_mapsTo'' (S := (C : Set H)) (fun z hz => h.rot_mem z hz) hc
    ((RotationSystem.mem_vertexOf _).1 hy)

/-- The vertex of a dart outside `C` is disjoint from `C`. -/
theorem vertexOf_subset_compl {x : H} (hx : x ∉ C) : ∀ y ∈ M.vertexOf x, y ∉ C := fun _ hy =>
  mem_of_sameCycle_of_mapsTo'' (S := {z | z ∉ C}) (fun z hz => (not_congr (h.rot_mem_iff z)).2 hz)
    hx ((RotationSystem.mem_vertexOf _).1 hy)

/-- The vertex of a dart of `C` is not a boundary vertex. -/
theorem not_isBoundaryVertex {c : H} (hc : c ∈ C) :
    ¬M.IsBoundaryVertex (M.vertexOf c) := fun ⟨y, hy, hyB⟩ =>
  h.notMem_bdry y (h.vertexOf_subset hc y hy) hyB

end IsLoopCutSite

/-- The involution of the inside: the involution of `M` on `C \ {e}`, with `e ↔ g = Sum.inr 0`
and `p = Sum.inr 1 ↔ p̄ = Sum.inr 2`. -/
def loopCutInsideInv (h : M.IsLoopCutSite C e) : {x // x ∈ C} ⊕ Fin 3 → {x // x ∈ C} ⊕ Fin 3
  | .inl c => if hc : c.1 = e then .inr 0 else .inl ⟨M.inv c, h.inv_mem c c.2 hc⟩
  | .inr i => if i = 0 then .inl ⟨e, h.mem⟩ else if i = 1 then .inr 2 else .inr 1

/-- `loopCutInsideInv h` is an involution. -/
theorem loopCutInsideInv_involutive (h : M.IsLoopCutSite C e) :
    Involutive (loopCutInsideInv h) := by
  rintro (⟨c, hc⟩ | i)
  · by_cases hce : c = e
    · subst hce
      simp [loopCutInsideInv]
    · have h1 : M.inv c ≠ e := h.inv_ne_of_mem hc
      simp [loopCutInsideInv, hce, h1, h.inv_involutive c]
  · fin_cases i <;> simp [loopCutInsideInv]

/-- The **inside** of a cut: the darts `C` with the rotation and colours of `M`, a new boundary
vertex `(p̄, p, g)` with boundary arcs `p, p̄` and leg `g` glued to `e`. -/
def loopCutInside (h : M.IsLoopCutSite C e) : PlabicData ({x // x ∈ C} ⊕ Fin 3) 1 where
  inv := Involutive.toPerm _ (loopCutInsideInv_involutive h)
  rot := Perm.sumCongr (M.rot.subtypePerm h.rot_mem_iff) (finRotate 3).symm
  bdry := {.inr 1, .inr 2}
  colour := Sum.elim (fun c => M.colour c) fun _ => M.colour e
  leg _ := .inr 0

/-- The involution of the outside: the involution of `M` away from `ē`, with `ē ↔ f`. -/
def loopCutOutsideInv (h : M.IsLoopCutSite C e) : {x // x ∉ C} ⊕ Unit → {x // x ∉ C} ⊕ Unit
  | .inl x => if hx : M.inv x ∈ C then .inr () else .inl ⟨M.inv x, hx⟩
  | .inr _ => .inl ⟨M.inv e, h.inv_notMem⟩

/-- `loopCutOutsideInv h` is an involution. -/
theorem loopCutOutsideInv_involutive (h : M.IsLoopCutSite C e) :
    Involutive (loopCutOutsideInv h) := by
  rintro (⟨x, hx⟩ | u)
  · by_cases hix : M.inv x ∈ C
    · have : x = M.inv e := (h.inv_mem_iff_of_notMem hx).1 hix
      subst this
      simp [loopCutOutsideInv, hix]
    · simp [loopCutOutsideInv, hix, h.inv_involutive x, hx]
  · simp [loopCutOutsideInv, h.inv_involutive e, h.mem]

/-- The **outside** of a cut: the darts outside `C` with the data of `M`, and a new leaf `{f}`,
`f = Sum.inr ()`, glued to `ē` and coloured as `ē`. -/
def loopCutOutside (h : M.IsLoopCutSite C e) : PlabicData ({x // x ∉ C} ⊕ Unit) b where
  inv := Involutive.toPerm _ (loopCutOutsideInv_involutive h)
  rot := Perm.sumCongr (M.rot.subtypePerm fun x => not_congr (h.rot_mem_iff x)) 1
  bdry := (M.bdry.subtype (· ∉ C)).map Embedding.inl
  colour := Sum.elim (fun x => M.colour x) fun _ => M.colour (M.inv e)
  leg i := .inl ⟨M.leg i, h.leg_notMem i⟩

section CutAPI

variable (h : M.IsLoopCutSite C e)

/-- The involution of the inside agrees with that of `M` on `C \ {e}`. -/
theorem loopCutInside_inv_inl_of_ne {c : {x // x ∈ C}} (hc : c.1 ≠ e) :
    (loopCutInside h).inv (.inl c) = .inl ⟨M.inv c, h.inv_mem c c.2 hc⟩ := by
  simp [loopCutInside, loopCutInsideInv, Involutive.coe_toPerm, hc]

/-- The involution of the inside sends `e` to the leg `g = Sum.inr 0`. -/
theorem loopCutInside_inv_inl_e : (loopCutInside h).inv (.inl ⟨e, h.mem⟩) = .inr 0 := by
  simp [loopCutInside, loopCutInsideInv, Involutive.coe_toPerm]

/-- The involution of the inside sends the leg `g = Sum.inr 0` to `e`. -/
theorem loopCutInside_inv_inr_zero : (loopCutInside h).inv (.inr 0) = .inl ⟨e, h.mem⟩ := by
  simp [loopCutInside, loopCutInsideInv, Involutive.coe_toPerm]

/-- The involution of the inside sends `p = Sum.inr 1` to `p̄ = Sum.inr 2`. -/
theorem loopCutInside_inv_inr_one : (loopCutInside h).inv (.inr 1) = .inr 2 := by
  simp [loopCutInside, loopCutInsideInv, Involutive.coe_toPerm]

/-- The involution of the inside sends `p̄ = Sum.inr 2` to `p = Sum.inr 1`. -/
theorem loopCutInside_inv_inr_two : (loopCutInside h).inv (.inr 2) = .inr 1 := by
  simp [loopCutInside, loopCutInsideInv, Involutive.coe_toPerm]

/-- The rotation of the inside agrees with that of `M` on `C`. -/
theorem loopCutInside_rot_inl (c : {x // x ∈ C}) :
    (loopCutInside h).rot (.inl c) = .inl ⟨M.rot c, (h.rot_mem_iff c).2 c.2⟩ := rfl

/-- The rotation of the inside sends `g = Sum.inr 0` to `p̄ = Sum.inr 2`. -/
theorem loopCutInside_rot_inr_zero : (loopCutInside h).rot (.inr 0) = .inr 2 := by
  simp only [loopCutInside, Perm.sumCongr_apply, Sum.map_inr]
  exact congrArg Sum.inr (by decide)

/-- The rotation of the inside sends `p = Sum.inr 1` to `g = Sum.inr 0`. -/
theorem loopCutInside_rot_inr_one : (loopCutInside h).rot (.inr 1) = .inr 0 := by
  simp only [loopCutInside, Perm.sumCongr_apply, Sum.map_inr]
  exact congrArg Sum.inr (by decide)

/-- The rotation of the inside sends `p̄ = Sum.inr 2` to `p = Sum.inr 1`. -/
theorem loopCutInside_rot_inr_two : (loopCutInside h).rot (.inr 2) = .inr 1 := by
  simp only [loopCutInside, Perm.sumCongr_apply, Sum.map_inr]
  exact congrArg Sum.inr (by decide)

/-- The inverse rotation of the inside sends its leg to `p = Sum.inr 1`. -/
theorem loopCutInside_rot_symm_leg :
    (loopCutInside h).rot.symm ((loopCutInside h).leg 0) = .inr 1 := by
  rw [Equiv.symm_apply_eq]
  exact (loopCutInside_rot_inr_one h).symm

/-- The boundary arcs of the inside are `p = Sum.inr 1` and `p̄ = Sum.inr 2`. -/
theorem mem_loopCutInside_bdry {x : {x // x ∈ C} ⊕ Fin 3} :
    x ∈ (loopCutInside h).bdry ↔ x = .inr 1 ∨ x = .inr 2 := by
  simp [loopCutInside]

/-- The involution of the outside sends a dart `x ∉ C` with `x̄ ∈ C` to the leaf `f`. -/
theorem loopCutOutside_inv_inl_of_mem {x : {x // x ∉ C}} (hx : M.inv x ∈ C) :
    (loopCutOutside h).inv (.inl x) = .inr () := by
  simp [loopCutOutside, loopCutOutsideInv, Involutive.coe_toPerm, hx]

/-- The involution of the outside agrees with that of `M` at a dart `x ∉ C` with `x̄ ∉ C`. -/
theorem loopCutOutside_inv_inl_of_notMem {x : {x // x ∉ C}} (hx : M.inv x ∉ C) :
    (loopCutOutside h).inv (.inl x) = .inl ⟨M.inv x, hx⟩ := by
  simp [loopCutOutside, loopCutOutsideInv, Involutive.coe_toPerm, hx]

/-- The involution of the outside sends the leaf `f` to `ē`. -/
theorem loopCutOutside_inv_inr : (loopCutOutside h).inv (.inr ()) = .inl ⟨M.inv e, h.inv_notMem⟩ :=
  rfl

/-- The rotation of the outside agrees with that of `M` away from the leaf `f`. -/
theorem loopCutOutside_rot_inl (x : {x // x ∉ C}) :
    (loopCutOutside h).rot (.inl x) = .inl ⟨M.rot x, (not_congr (h.rot_mem_iff x)).2 x.2⟩ := rfl

/-- The rotation of the outside fixes the leaf `f`. -/
theorem loopCutOutside_rot_inr : (loopCutOutside h).rot (.inr ()) = .inr () := rfl

/-- A dart `x ∉ C` is a boundary arc of the outside if and only if it is one of `M`. -/
theorem inl_mem_loopCutOutside_bdry {x : {x // x ∉ C}} :
    (.inl x : {x // x ∉ C} ⊕ Unit) ∈ (loopCutOutside h).bdry ↔ x.1 ∈ M.bdry := by
  simp [loopCutOutside]

/-- The leaf `f` is not a boundary arc of the outside. -/
theorem inr_notMem_loopCutOutside_bdry :
    (.inr () : {x // x ∉ C} ⊕ Unit) ∉ (loopCutOutside h).bdry := by
  simp [loopCutOutside]

/-- The inside can be glued into the leaf `{f}` of the outside. -/
theorem isLeafGluingSite_loopCut :
    (loopCutOutside h).IsLeafGluingSite (.inr ()) (loopCutInside h) (.inr 1) (.inr 0) where
  inv_involutive_left := loopCutOutsideInv_involutive h
  inv_ne_left := by
    rintro (x | u)
    · by_cases hx : M.inv x ∈ C
      · rw [loopCutOutside_inv_inl_of_mem h hx]; simp
      · rw [loopCutOutside_inv_inl_of_notMem h hx]
        simpa [Subtype.ext_iff] using h.inv_ne x
    · rw [loopCutOutside_inv_inr]; simp
  inv_involutive_right := loopCutInsideInv_involutive h
  inv_ne_right := by
    rintro (c | i)
    · by_cases hc : c.1 = e
      · have : c = ⟨e, h.mem⟩ := Subtype.ext hc
        subst this
        rw [loopCutInside_inv_inl_e]; simp
      · rw [loopCutInside_inv_inl_of_ne h hc]
        simpa [Subtype.ext_iff] using h.inv_ne c
    · fin_cases i
      · rw [show ((⟨0, by norm_num⟩ : Fin 3)) = 0 from rfl, loopCutInside_inv_inr_zero]; simp
      · rw [show ((⟨1, by norm_num⟩ : Fin 3)) = 1 from rfl, loopCutInside_inv_inr_one]; simp
      · rw [show ((⟨2, by norm_num⟩ : Fin 3)) = 2 from rfl, loopCutInside_inv_inr_two]; simp
  notMem_bdry_left := inr_notMem_loopCutOutside_bdry h
  rot_left := rfl
  leg_ne i := by simp [loopCutOutside]
  bdry_right := by rw [loopCutInside_inv_inr_one]; rfl
  notMem_bdry_right := by rw [mem_loopCutInside_bdry]; simp
  rot_inv_right := by rw [loopCutInside_inv_inr_one, loopCutInside_rot_inr_two]
  rot_right := loopCutInside_rot_inr_one h
  rot_rot_right := by rw [loopCutInside_rot_inr_zero, loopCutInside_inv_inr_one]

end CutAPI

/-! ### The gluing of the inside into the outside -/

section CutIso

variable (h : M.IsLoopCutSite C e)

/-- The darts of `M`, as the darts of the gluing of the inside into the leaf of the outside. -/
def loopCutEquiv : H ≃ leafGluingDarts (Sum.inr () : {x // x ∉ C} ⊕ Unit) (loopCutInside h)
    (.inr 1) (.inr 0) where
  toFun x := if hx : x ∈ C then ⟨.inr (.inl ⟨x, hx⟩), by simp [loopCutInside_inv_inr_one h]⟩
    else ⟨.inl (.inl ⟨x, hx⟩), by simp⟩
  invFun y := Sum.elim (Sum.elim Subtype.val fun _ => M.inv e)
    (Sum.elim Subtype.val fun _ => e) y.1
  left_inv x := by by_cases hx : x ∈ C <;> simp [hx]
  right_inv := by
    rintro ⟨(⟨x, hx⟩ | u) | (⟨c, hc⟩ | i), hy⟩
    · simp [hx]
    · exfalso
      simp at hy
    · simp [hc]
    · exfalso
      fin_cases i <;> simp [loopCutInside_inv_inr_one h] at hy

/-- `loopCutEquiv h` sends a dart of `C` to the corresponding dart of the inside. -/
theorem coe_loopCutEquiv_of_mem {x : H} (hx : x ∈ C) :
    (loopCutEquiv h x).1 = .inr (.inl ⟨x, hx⟩) := by
  simp [loopCutEquiv, hx]

/-- `loopCutEquiv h` sends a dart outside `C` to the corresponding dart of the outside. -/
theorem coe_loopCutEquiv_of_notMem {x : H} (hx : x ∉ C) :
    (loopCutEquiv h x).1 = .inl (.inl ⟨x, hx⟩) := by
  simp [loopCutEquiv, hx]

/-- `loopCutEquiv h` intertwines the rotation of `M` and that of the gluing. -/
theorem loopCutEquiv_rot (x : H) : loopCutEquiv h (M.rot x) =
    ((loopCutOutside h).leafGluing (isLeafGluingSite_loopCut h)).rot (loopCutEquiv h x) := by
  apply Subtype.ext
  rw [coe_leafGluing_rot]
  by_cases hx : x ∈ C
  · rw [coe_loopCutEquiv_of_mem h ((h.rot_mem_iff x).2 hx), coe_loopCutEquiv_of_mem h hx]
    rfl
  · rw [coe_loopCutEquiv_of_notMem h ((not_congr (h.rot_mem_iff x)).2 hx),
      coe_loopCutEquiv_of_notMem h hx]
    rfl

/-- `loopCutEquiv h` intertwines the involution of `M` and that of the gluing. -/
theorem loopCutEquiv_inv (x : H) : loopCutEquiv h (M.inv x) =
    ((loopCutOutside h).leafGluing (isLeafGluingSite_loopCut h)).inv (loopCutEquiv h x) := by
  have hs := isLeafGluingSite_loopCut h
  apply Subtype.ext
  rw [coe_leafGluing_inv]
  by_cases hx : x ∈ C
  · by_cases hxe : x = e
    · subst hxe
      rw [coe_loopCutEquiv_of_mem h hx, coe_loopCutEquiv_of_notMem h h.inv_notMem]
      have : (Sum.inr (Sum.inl ⟨x, hx⟩) : ({x // x ∉ C} ⊕ Unit) ⊕ ({x // x ∈ C} ⊕ Fin 3)) =
          Sum.inr ((loopCutInside h).inv (.inr 0)) := by
        rw [loopCutInside_inv_inr_zero]
      rw [this, hs.leafGluingInv_inr_inv_g, loopCutOutside_inv_inr]
    · have hix := h.inv_mem x hx hxe
      rw [coe_loopCutEquiv_of_mem h hx, coe_loopCutEquiv_of_mem h hix,
        hs.leafGluingInv_of_ne (by simp) (by simp) (by simp) ?_]
      · simp [loopCutInside_inv_inl_of_ne h (c := ⟨x, hx⟩) hxe]
      · rw [loopCutInside_inv_inr_zero]
        simpa using hxe
  · by_cases hxe : x = M.inv e
    · subst hxe
      rw [coe_loopCutEquiv_of_notMem h hx, h.inv_involutive e, coe_loopCutEquiv_of_mem h h.mem]
      have : (Sum.inl (Sum.inl ⟨M.inv e, hx⟩) :
          ({x // x ∉ C} ⊕ Unit) ⊕ ({x // x ∈ C} ⊕ Fin 3)) =
          Sum.inl ((loopCutOutside h).inv (.inr ())) := by
        rw [loopCutOutside_inv_inr]
      rw [this, hs.leafGluingInv_inl_inv_f, loopCutInside_inv_inr_zero]
    · have hix : M.inv x ∉ C := fun hc => hxe ((h.inv_mem_iff_of_notMem hx).1 hc)
      rw [coe_loopCutEquiv_of_notMem h hx, coe_loopCutEquiv_of_notMem h hix,
        hs.leafGluingInv_of_ne (by simp) ?_ (by simp) (by simp)]
      · simp [loopCutOutside_inv_inl_of_notMem h (x := ⟨x, hx⟩) hix]
      · rw [loopCutOutside_inv_inr]
        simpa using hxe

/-- `loopCutEquiv h` maps the boundary arcs of `M` onto those of the gluing. -/
theorem loopCutEquiv_mem_bdry_iff (x : H) :
    loopCutEquiv h x ∈ ((loopCutOutside h).leafGluing (isLeafGluingSite_loopCut h)).bdry ↔
      x ∈ M.bdry := by
  rw [mem_leafGluing_bdry]
  by_cases hx : x ∈ C
  · rw [coe_loopCutEquiv_of_mem h hx]
    simpa using h.notMem_bdry x hx
  · rw [coe_loopCutEquiv_of_notMem h hx, mem_map]
    simp only [Embedding.inl_apply, Sum.inl.injEq, exists_eq_right]
    exact inl_mem_loopCutOutside_bdry h

/-- `loopCutEquiv h` sends each leg of `M` to the corresponding leg of the gluing. -/
theorem loopCutEquiv_leg (i : Fin b) : loopCutEquiv h (M.leg i) =
    ((loopCutOutside h).leafGluing (isLeafGluingSite_loopCut h)).leg i :=
  Subtype.ext (by rw [coe_loopCutEquiv_of_notMem h (h.leg_notMem i), coe_leafGluing_leg]; rfl)

variable [Fintype H]

/-- `M` is isomorphic to the gluing of its inside into the leaf of its outside. -/
theorem isomorphic_leafGluing_loopCut {p g : {x // x ∈ C} ⊕ Fin 3} (hp : p = .inr 1)
    (hg : g = .inr 0)
    (hs : (loopCutOutside h).IsLeafGluingSite (.inr ()) (loopCutInside h) p g) :
    M.Isomorphic ((loopCutOutside h).leafGluing hs) := by
  subst hp hg
  have hvx : ∀ x, (M.vertexOf x).map (loopCutEquiv h).toEmbedding =
      ((loopCutOutside h).leafGluing hs).vertexOf (loopCutEquiv h x) :=
    RotationSystem.map_vertexOf_of_semiconj _ _ _ (loopCutEquiv_rot h)
  refine ⟨{ toEquiv := loopCutEquiv h
            map_inv := loopCutEquiv_inv h
            map_rot := loopCutEquiv_rot h
            mem_bdry_iff := loopCutEquiv_mem_bdry_iff h
            map_colour := fun x _ => ?_
            map_bvertex := fun i => ?_ }⟩
  · rw [leafGluing_colour]
    by_cases hx : x ∈ C
    · rw [coe_loopCutEquiv_of_mem h hx]; rfl
    · rw [coe_loopCutEquiv_of_notMem h hx]; rfl
  · ext y
    have e1 : y ∈ ((loopCutOutside h).leafGluing hs).bvertex i ↔
        (loopCutEquiv h).symm y ∈ M.bvertex i := by
      rw [bvertex, bvertex, ← loopCutEquiv_leg h, ← hvx, mem_map_equiv]
    have e2 : y ∈ ((loopCutOutside h).leafGluing hs).bdry ↔
        (loopCutEquiv h).symm y ∈ M.bdry := by
      rw [← loopCutEquiv_mem_bdry_iff h, Equiv.apply_symm_apply]
    simp only [mem_map_equiv, mem_filter, e1, e2]

/-- The gluing of the inside into the leaf of the outside is isomorphic to `M`. -/
theorem leafGluing_loopCut_isomorphic {p g : {x // x ∈ C} ⊕ Fin 3} (hp : p = .inr 1)
    (hg : g = .inr 0)
    (hs : (loopCutOutside h).IsLeafGluingSite (.inr ()) (loopCutInside h) p g) :
    ((loopCutOutside h).leafGluing hs).Isomorphic M :=
  (isomorphic_leafGluing_loopCut h hp hg hs).symm

end CutIso

/-! ### Connectivity of the two sides -/

section CutConnected

variable [Fintype H] (h : M.IsLoopCutSite C e) (hM : M.IsPlabicGraph)

include hM

/-- For a plabic graph `M`, every dart of the inside is connected to `e`. -/
theorem loopCutInside_reach (x : {x // x ∈ C} ⊕ Fin 3) :
    (loopCutInside h).Reach x (.inl ⟨e, h.mem⟩) := by
  set R := loopCutInside h
  have h0 : R.Reach (.inr 0) (.inl ⟨e, h.mem⟩) := by
    have := (RotationSystem.Reach.refl (R := R.toRotationSystem) (.inr 0)).inv
    rwa [show R.toRotationSystem.inv (.inr 0) = _ from loopCutInside_inv_inr_zero h] at this
  have h1 : R.Reach (.inr 1) (.inl ⟨e, h.mem⟩) := by
    have := (RotationSystem.Reach.refl (R := R.toRotationSystem) (.inr 1)).rot
    rw [show R.toRotationSystem.rot (.inr 1) = _ from loopCutInside_rot_inr_one h] at this
    exact this.trans h0
  rcases x with ⟨c0, hc0⟩ | i
  · have key : ∀ z, M.Reach c0 z → R.Reach (.inl ⟨c0, hc0⟩) (.inl ⟨e, h.mem⟩) ∨
        ∃ hz : z ∈ C, R.Reach (.inl ⟨c0, hc0⟩) (.inl ⟨z, hz⟩) := by
      intro z hz
      induction hz with
      | refl => exact Or.inr ⟨hc0, .refl _⟩
      | @rot w _ ih =>
        rcases ih with ih | ⟨hw, hr⟩
        · exact Or.inl ih
        · exact Or.inr ⟨h.rot_mem _ hw, hr.rot⟩
      | @inv w _ ih =>
        rcases ih with ih | ⟨hw, hr⟩
        · exact Or.inl ih
        · by_cases hwe : w = e
          · subst hwe
            exact Or.inl hr
          · refine Or.inr ⟨h.inv_mem w hw hwe, ?_⟩
            have := hr.inv
            rwa [show R.toRotationSystem.inv (.inl ⟨w, hw⟩) = _ from
              loopCutInside_inv_inl_of_ne h (c := ⟨w, hw⟩) hwe] at this
    rcases key e (hM.toIsConnected.reach c0 e) with h' | ⟨_, h'⟩
    · exact h'
    · exact h'
  · fin_cases i
    · exact h0
    · exact h1
    · have := (RotationSystem.Reach.refl (R := R.toRotationSystem) (.inr 2)).rot
      rw [show R.toRotationSystem.rot (.inr 2) = _ from loopCutInside_rot_inr_two h] at this
      exact this.trans h1

/-- For a plabic graph `M`, every dart of the outside is connected to `ē`. -/
theorem loopCutOutside_reach (x : {x // x ∉ C} ⊕ Unit) :
    (loopCutOutside h).Reach x (.inl ⟨M.inv e, h.inv_notMem⟩) := by
  set Y := loopCutOutside h
  rcases x with ⟨x0, hx0⟩ | u
  · have key : ∀ z, M.Reach x0 z → Y.Reach (.inl ⟨x0, hx0⟩) (.inl ⟨M.inv e, h.inv_notMem⟩) ∨
        ∃ hz : z ∉ C, Y.Reach (.inl ⟨x0, hx0⟩) (.inl ⟨z, hz⟩) := by
      intro z hz
      induction hz with
      | refl => exact Or.inr ⟨hx0, .refl _⟩
      | @rot w _ ih =>
        rcases ih with ih | ⟨hw, hr⟩
        · exact Or.inl ih
        · exact Or.inr ⟨(not_congr (h.rot_mem_iff w)).2 hw, hr.rot⟩
      | @inv w _ ih =>
        rcases ih with ih | ⟨hw, hr⟩
        · exact Or.inl ih
        · by_cases hwe : M.inv w ∈ C
          · obtain rfl : w = M.inv e := (h.inv_mem_iff_of_notMem hw).1 hwe
            exact Or.inl hr
          · refine Or.inr ⟨hwe, ?_⟩
            have := hr.inv
            rwa [show Y.toRotationSystem.inv (.inl ⟨w, hw⟩) = _ from
              loopCutOutside_inv_inl_of_notMem h (x := ⟨w, hw⟩) hwe] at this
    rcases key (M.inv e) (hM.toIsConnected.reach x0 _) with h' | ⟨_, h'⟩
    · exact h'
    · exact h'
  · have := (RotationSystem.Reach.refl (R := Y.toRotationSystem) (.inr u)).inv
    rwa [show Y.toRotationSystem.inv (.inr u) = _ from loopCutOutside_inv_inr h] at this

/-- The inside of a cut of a plabic graph is connected. -/
theorem isConnected_loopCutInside : (loopCutInside h).IsConnected :=
  RotationSystem.IsConnected.of_reach ⟨.inr 0⟩ (isLeafGluingSite_loopCut h).inv_involutive_right
    (isLeafGluingSite_loopCut h).inv_ne_right fun x y =>
      (loopCutInside_reach h hM x).trans (loopCutInside_reach h hM y).symm

/-- The outside of a cut of a plabic graph is connected. -/
theorem isConnected_loopCutOutside : (loopCutOutside h).IsConnected :=
  RotationSystem.IsConnected.of_reach ⟨.inr ()⟩ (isLeafGluingSite_loopCut h).inv_involutive_left
    (isLeafGluingSite_loopCut h).inv_ne_left fun x y =>
      (loopCutOutside_reach h hM x).trans (loopCutOutside_reach h hM y).symm

/-- Both sides of the cut satisfy Euler's relation. -/
theorem euler_loopCut :
    ((loopCutOutside h).vertices.card : ℤ) - (loopCutOutside h).edges.card +
        (loopCutOutside h).faceOrbits.card = 2 ∧
      ((loopCutInside h).vertices.card : ℤ) - (loopCutInside h).edges.card +
        (loopCutInside h).faceOrbits.card = 2 := by
  have hs := isLeafGluingSite_loopCut h
  obtain ⟨c1, c2, c3⟩ := RotationSystem.card_eq_of_semiconj M.toRotationSystem
    ((loopCutOutside h).leafGluing hs).toRotationSystem (loopCutEquiv h) (loopCutEquiv_rot h)
    (loopCutEquiv_inv h)
  have h1 := hs.card_vertices_leafGluing
  have h2 := hs.card_edges_leafGluing
  have h3 := hs.card_faceOrbits_leafGluing
  have hY := (isConnected_loopCutOutside h hM).euler_le
  have hR := (isConnected_loopCutInside h hM).euler_le
  have hMe := hM.euler
  constructor <;> omega

end CutConnected

/-! ### The two sides are plabic graphs -/

section CutPlabic

variable (h : M.IsLoopCutSite C e)

/-- The vertex of the inside at a dart `c ∈ C` is the vertex of `c` in `M`. -/
theorem loopCutInside_vertexOf_inl [Fintype H] (c : {x // x ∈ C}) :
    (loopCutInside h).vertexOf (.inl c) =
      ((M.vertexOf c).subtype (· ∈ C)).map Embedding.inl := by
  ext y
  rcases y with c' | j
  · simp only [RotationSystem.mem_vertexOf, mem_map, mem_subtype, Embedding.inl_apply,
      Sum.inl.injEq, exists_eq_right]
    exact (sameCycle_sumCongr_inl' _ _).trans sameCycle_subtypePerm
  · simp only [RotationSystem.mem_vertexOf, mem_map, Embedding.inl_apply, reduceCtorEq,
      and_false, exists_false, iff_false]
    exact not_sameCycle_sumCongr_inl_inr' _ _

/-- The new boundary vertex of the inside is `{g, p, p̄}`. -/
theorem loopCutInside_vertexOf_inr (i : Fin 3) :
    (loopCutInside h).vertexOf (.inr i) = {.inr 0, .inr 1, .inr 2} := by
  have hc : ∀ j : Fin 3, (loopCutInside h).rot.SameCycle (.inr 0) (.inr j) := by
    have a : (loopCutInside h).rot.SameCycle (.inr 0) (.inr 2) := by
      rw [← loopCutInside_rot_inr_zero h]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    have b : (loopCutInside h).rot.SameCycle (.inr 2) (.inr 1) := by
      rw [← loopCutInside_rot_inr_two h]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    intro j
    fin_cases j
    · exact SameCycle.refl _ _
    · exact a.trans b
    · exact a
  ext y
  rw [RotationSystem.mem_vertexOf]
  constructor
  · intro hy
    rcases y with c | j
    · exact absurd hy (not_sameCycle_sumCongr_inr_inl' _ _)
    · fin_cases j <;> simp
  · intro hy
    obtain ⟨j, rfl⟩ : ∃ j, y = .inr j := by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    exact (hc i).symm.trans (hc j)

/-- The vertex of the inside at a dart of `C` is not a boundary vertex. -/
theorem not_isBoundaryVertex_loopCutInside_inl (c : {x // x ∈ C}) :
    ¬(loopCutInside h).IsBoundaryVertex ((loopCutInside h).vertexOf (.inl c)) := by
  rintro ⟨y, hy, hyB⟩
  rw [mem_loopCutInside_bdry] at hyB
  rcases hyB with rfl | rfl <;>
    exact not_sameCycle_sumCongr_inl_inr' _ _ ((RotationSystem.mem_vertexOf _).1 hy)

/-- The vertex `{g, p, p̄}` of the inside is a boundary vertex. -/
theorem isBoundaryVertex_loopCutInside_inr (i : Fin 3) :
    (loopCutInside h).IsBoundaryVertex ((loopCutInside h).vertexOf (.inr i)) :=
  ⟨.inr 1, by rw [loopCutInside_vertexOf_inr]; simp, by rw [mem_loopCutInside_bdry]; simp⟩

/-- Two darts outside `C` lie in the same cycle of the rotation of the outside if and only if
they do in `M`. -/
theorem sameCycle_loopCutOutside_inl_iff {x y : {x // x ∉ C}} :
    (loopCutOutside h).rot.SameCycle (.inl x) (.inl y) ↔ M.rot.SameCycle x y :=
  (sameCycle_sumCongr_inl' _ _).trans sameCycle_subtypePerm

/-- The darts of the vertex of the outside at `x ∉ C` are the darts of the vertex of `x` in
`M`. -/
theorem mem_loopCutOutside_vertexOf_inl [Fintype H] {x : {x // x ∉ C}} {y : {x // x ∉ C} ⊕ Unit} :
    y ∈ (loopCutOutside h).vertexOf (.inl x) ↔
      ∃ z : {x // x ∉ C}, y = .inl z ∧ z.1 ∈ M.vertexOf x.1 := by
  rcases y with z | u
  · rw [RotationSystem.mem_vertexOf, sameCycle_loopCutOutside_inl_iff]
    simp [RotationSystem.mem_vertexOf]
  · rw [RotationSystem.mem_vertexOf]
    simp only [reduceCtorEq, false_and, exists_false, iff_false]
    exact not_sameCycle_sumCongr_inl_inr' _ _

/-- The vertex of the outside at a dart `x ∉ C` is the vertex of `x` in `M`. -/
theorem loopCutOutside_vertexOf_inl [Fintype H] (x : {x // x ∉ C}) :
    (loopCutOutside h).vertexOf (.inl x) =
      ((M.vertexOf x).subtype (· ∉ C)).map Embedding.inl := by
  ext y
  rw [mem_loopCutOutside_vertexOf_inl]
  simp only [mem_map, mem_subtype, Embedding.inl_apply]
  exact ⟨fun ⟨z, hz, hzv⟩ => ⟨z, hzv, hz.symm⟩, fun ⟨z, hzv, hz⟩ => ⟨z, hz.symm, hzv⟩⟩

/-- The vertex of the outside at the leaf `f` is `{f}`. -/
theorem loopCutOutside_vertexOf_inr [Fintype H] (u : Unit) :
    (loopCutOutside h).vertexOf (.inr u) = {.inr ()} := by
  ext y
  rw [RotationSystem.mem_vertexOf, mem_singleton]
  rcases y with z | v
  · simp only [reduceCtorEq, iff_false]
    exact not_sameCycle_sumCongr_inr_inl' _ _
  · cases u
    cases v
    exact iff_of_true (SameCycle.refl _ _) rfl

private theorem card_map_inl_subtype {s : Finset H} (hs : ∀ y ∈ s, y ∉ C) :
    ((s.subtype (· ∉ C)).map (Embedding.inl (β := Unit))).card = s.card := by
  rw [card_map, card_subtype, filter_true_of_mem hs]

/-- The vertex of the outside at `x ∉ C` is a boundary vertex if and only if the vertex of `x`
in `M` is. -/
theorem isBoundaryVertex_loopCutOutside_inl_iff [Fintype H] (x : {x // x ∉ C}) :
    (loopCutOutside h).IsBoundaryVertex ((loopCutOutside h).vertexOf (.inl x)) ↔
      M.IsBoundaryVertex (M.vertexOf x) := by
  constructor
  · rintro ⟨y, hy, hyB⟩
    obtain ⟨z, rfl, hz⟩ := (mem_loopCutOutside_vertexOf_inl h).1 hy
    exact ⟨z, hz, (inl_mem_loopCutOutside_bdry h).1 hyB⟩
  · rintro ⟨z, hz, hzB⟩
    exact ⟨.inl ⟨z, h.vertexOf_subset_compl x.2 z hz⟩,
      (mem_loopCutOutside_vertexOf_inl h).2 ⟨_, rfl, hz⟩,
      (inl_mem_loopCutOutside_bdry h).2 hzB⟩

/-- The leaf `{f}` of the outside is not a boundary vertex. -/
theorem not_isBoundaryVertex_loopCutOutside_inr [Fintype H] (u : Unit) :
    ¬(loopCutOutside h).IsBoundaryVertex ((loopCutOutside h).vertexOf (.inr u)) := by
  rintro ⟨y, hy, hyB⟩
  rw [loopCutOutside_vertexOf_inr, mem_singleton] at hy
  subst hy
  exact inr_notMem_loopCutOutside_bdry h hyB

/-- The boundary arcs of the outside are the boundary arcs of `M`. -/
theorem mem_loopCutOutside_bdry {y : {x // x ∉ C} ⊕ Unit} :
    y ∈ (loopCutOutside h).bdry ↔ ∃ z : {x // x ∉ C}, y = .inl z ∧ z.1 ∈ M.bdry := by
  rcases y with z | u
  · rw [inl_mem_loopCutOutside_bdry]
    simp
  · simpa using inr_notMem_loopCutOutside_bdry h

/-- The exterior of the outside consists of the darts of the exterior of `M`. -/
theorem mem_loopCutOutside_exterior {y : {x // x ∉ C} ⊕ Unit} :
    y ∈ (loopCutOutside h).exterior ↔ ∃ z : {x // x ∉ C}, y = .inl z ∧ z.1 ∈ M.exterior := by
  rw [DiskMap.mem_exterior]
  rcases y with z | u
  · rw [show (loopCutOutside h).toRotationSystem.rot (.inl z) = _ from loopCutOutside_rot_inl h z,
      inl_mem_loopCutOutside_bdry, inl_mem_loopCutOutside_bdry]
    simp [DiskMap.mem_exterior]
  · cases u
    exact iff_of_false (fun hh => inr_notMem_loopCutOutside_bdry h hh.1) (by simp)

/-- For a plabic graph `M`, the involution of the outside agrees with that of `M` at a boundary
arc. -/
theorem loopCutOutside_inv_inl_of_mem_bdry [Fintype H] {z : {x // x ∉ C}} (hz : z.1 ∈ M.bdry)
    (hM : M.IsPlabicGraph) : (loopCutOutside h).inv (.inl z) =
      .inl ⟨M.inv z, fun hc => h.notMem_bdry _ hc (hM.inv_mem_bdry _ hz)⟩ :=
  loopCutOutside_inv_inl_of_notMem h _

variable [Fintype H] (hM : M.IsPlabicGraph)

include hM

/-- **The inside of a cut is a plabic graph** with one boundary vertex. -/
theorem isPlabicGraph_loopCutInside : (loopCutInside h).IsPlabicGraph := by
  have hT := loopCutInside_vertexOf_inr h
  have hbv : ∀ v ∈ (loopCutInside h).boundaryVertices, v = {.inr 0, .inr 1, .inr 2} := by
    intro v hv
    obtain ⟨hvV, hvB⟩ := (loopCutInside h).mem_boundaryVertices.1 hv
    obtain ⟨x, rfl⟩ := (loopCutInside h).mem_vertices.1 hvV
    rcases x with c | i
    · exact absurd hvB (not_isBoundaryVertex_loopCutInside_inl h c)
    · exact hT i
  have hface : (loopCutInside h).faceOf (.inr 1) = {.inr 1} := by
    refine RotationSystem.faceOf_eq_singleton _ ?_
    rw [RotationSystem.facePerm_apply,
      show (loopCutInside h).toRotationSystem.inv (.inr 1) = _ from loopCutInside_inv_inr_one h]
    exact loopCutInside_rot_inr_two h
  refine
    { toIsDiskMap :=
        { toIsConnected := isConnected_loopCutInside h hM
          inv_mem_bdry := ?_
          euler := (euler_loopCut h hM).2
          boundaryVertex_card := ?_
          exists_orbit := ?_ }
      one_le := le_rfl
      colour_rot := ?_
      leg_notMem_bdry := fun _ => by
        change (.inr 0 : {x // x ∈ C} ⊕ Fin 3) ∉ (loopCutInside h).bdry
        rw [mem_loopCutInside_bdry]
        simp
      bvertex_mem := fun _ => (loopCutInside h).vertexOf_mem_boundaryVertices.2
        (isBoundaryVertex_loopCutInside_inr h 0)
      bvertex_injective := fun i j _ => Subsingleton.elim i j
      exists_bvertex_eq := fun v hv => ⟨0, by rw [hbv v hv]; exact hT 0⟩
      exists_exterior := fun i => ⟨.inr 1, ?_, ?_, ?_⟩ }
  · intro d hd
    rw [mem_loopCutInside_bdry] at hd ⊢
    rcases hd with rfl | rfl
    · exact Or.inr (loopCutInside_inv_inr_one h)
    · exact Or.inl (loopCutInside_inv_inr_two h)
  · intro v hv
    rw [hbv v hv]
    have hf : ({.inr 0, .inr 1, .inr 2} : Finset ({x // x ∈ C} ⊕ Fin 3)).filter
        (· ∈ (loopCutInside h).bdry) = {.inr 1, .inr 2} := by
      ext y
      simp only [mem_filter, mem_insert, mem_singleton, mem_loopCutInside_bdry]
      exact ⟨And.right, by rintro (rfl | rfl) <;> simp⟩
    rw [hf, card_insert_of_notMem (by simp), card_pair (by simp)]
    exact ⟨rfl, rfl⟩
  · refine ⟨{.inr 1}, hface ▸ (loopCutInside h).faceOf_mem_faceOrbits _, ?_, ?_, ?_⟩
    · rw [singleton_subset_iff, mem_loopCutInside_bdry]
      simp
    · rw [map_singleton, Equiv.coe_toEmbedding,
        show (loopCutInside h).toRotationSystem.inv (.inr 1) = _ from loopCutInside_inv_inr_one h]
      rfl
    · rw [map_singleton, Equiv.coe_toEmbedding,
        show (loopCutInside h).toRotationSystem.inv (.inr 1) = _ from loopCutInside_inv_inr_one h]
      simp
  · rintro (c | i) hv
    · exact hM.colour_rot c (h.not_isBoundaryVertex c.2)
    · exact absurd (isBoundaryVertex_loopCutInside_inr h i) hv
  · rw [DiskMap.mem_exterior, mem_loopCutInside_bdry, mem_loopCutInside_bdry,
      show (loopCutInside h).toRotationSystem.rot (.inr 1) = _ from loopCutInside_rot_inr_one h]
    simp
  · change _ ∈ (loopCutInside h).vertexOf (.inr 0)
    rw [hT]
    simp
  · change _ ∈ (loopCutInside h).vertexOf (.inr 0)
    rw [hT, show (loopCutInside h).toRotationSystem.inv (.inr 1) = _ from
      loopCutInside_inv_inr_one h]
    simp

/-- The face permutation of the outside agrees with that of `M` at a boundary arc. -/
theorem loopCutOutside_facePerm_inl_of_mem_bdry {z : {x // x ∉ C}} (hz : z.1 ∈ M.bdry) :
    (loopCutOutside h).facePerm (.inl z) = .inl ⟨M.facePerm z,
      (not_congr (h.rot_mem_iff _)).2 fun hc => h.notMem_bdry _ hc (hM.inv_mem_bdry _ hz)⟩ := by
  rw [RotationSystem.facePerm_apply,
    show (loopCutOutside h).toRotationSystem.inv (.inl z) = _ from
      loopCutOutside_inv_inl_of_mem_bdry h hz hM]
  rfl

/-- Iterating the face permutation of the outside from an exterior arc of `M` agrees with
iterating that of `M`, provided the face permutation of `M` preserves its exterior. -/
theorem loopCutOutside_facePerm_pow_inl_of_mem_exterior
    (hclosed : ∀ x ∈ M.exterior, M.facePerm x ∈ M.exterior) {x0 : H} (hx0 : x0 ∈ M.exterior)
    (m : ℕ) : ∃ hm : (M.facePerm ^ m) x0 ∉ C, (M.facePerm ^ m) x0 ∈ M.exterior ∧
      ((loopCutOutside h).facePerm ^ m)
          (.inl ⟨x0, fun hc => h.notMem_bdry _ hc (M.exterior_subset_bdry hx0)⟩) =
        .inl ⟨(M.facePerm ^ m) x0, hm⟩ := by
  induction m with
  | zero => exact ⟨fun hc => h.notMem_bdry _ hc (M.exterior_subset_bdry hx0), hx0, rfl⟩
  | succ m ih =>
    obtain ⟨hm, hmE, hmeq⟩ := ih
    have hE := hclosed _ hmE
    refine ⟨fun hc => h.notMem_bdry _ hc (M.exterior_subset_bdry (by
      rwa [pow_succ', Perm.mul_apply])), by rwa [pow_succ', Perm.mul_apply], ?_⟩
    rw [pow_succ', Perm.mul_apply, hmeq,
      loopCutOutside_facePerm_inl_of_mem_bdry h hM (M.exterior_subset_bdry hmE)]
    simp only [Sum.inl.injEq, Subtype.mk.injEq]
    rw [pow_succ', Perm.mul_apply]

/-- The exterior of the outside is an orbit of its face permutation. -/
theorem loopCutOutside_exterior_mem_faceOrbits :
    (loopCutOutside h).exterior ∈ (loopCutOutside h).faceOrbits := by
  obtain ⟨x0, hx0, -, -⟩ := hM.exists_exterior ⟨0, hM.one_le⟩
  have hext := hM.exterior_mem_faceOrbits
  obtain ⟨w, hw⟩ := M.mem_faceOrbits.1 hext
  have hx0' : M.faceOf x0 = M.exterior := by rw [← hw, M.faceOf_eq_of_mem (hw ▸ hx0)]
  have hclosed : ∀ x ∈ M.exterior, M.facePerm x ∈ M.exterior := fun x hx => by
    rw [← hx0'] at hx ⊢
    rw [← M.faceOf_eq_of_mem hx]
    exact M.facePerm_mem_faceOf x
  have hx0C : x0 ∉ C := fun hc => h.notMem_bdry _ hc (M.exterior_subset_bdry hx0)
  refine (loopCutOutside h).mem_faceOrbits.2 ⟨.inl ⟨x0, hx0C⟩, ?_⟩
  ext y
  rw [RotationSystem.mem_faceOf]
  constructor
  · intro hy
    refine mem_of_sameCycle_of_mapsTo'' (S := {y | y ∈ (loopCutOutside h).exterior}) ?_ ?_ hy
    · intro y hy
      obtain ⟨z, rfl, hz⟩ := (mem_loopCutOutside_exterior h).1 hy
      rw [Set.mem_setOf_eq, loopCutOutside_facePerm_inl_of_mem_bdry h hM
        (M.exterior_subset_bdry hz)]
      exact (mem_loopCutOutside_exterior h).2 ⟨_, rfl, hclosed _ hz⟩
    · exact (mem_loopCutOutside_exterior h).2 ⟨_, rfl, hx0⟩
  · intro hy
    obtain ⟨z, rfl, hz⟩ := (mem_loopCutOutside_exterior h).1 hy
    rw [← hx0', RotationSystem.mem_faceOf] at hz
    obtain ⟨n, hn⟩ := hz.exists_nat_pow_eq
    obtain ⟨hm, -, hmeq⟩ := loopCutOutside_facePerm_pow_inl_of_mem_exterior h hM hclosed hx0 n
    refine ⟨n, ?_⟩
    rw [zpow_natCast, hmeq]
    congr 2

omit hM in
/-- Every boundary vertex of the outside is the vertex of a dart of `M` at a boundary vertex. -/
theorem exists_eq_vertexOf_inl_of_mem_boundaryVertices_loopCutOutside :
    ∀ v ∈ (loopCutOutside h).boundaryVertices, ∃ x : {x // x ∉ C},
      v = (loopCutOutside h).vertexOf (.inl x) ∧ M.IsBoundaryVertex (M.vertexOf x) := by
  intro v hv
  obtain ⟨hvV, hvB⟩ := (loopCutOutside h).mem_boundaryVertices.1 hv
  obtain ⟨y, rfl⟩ := (loopCutOutside h).mem_vertices.1 hvV
  rcases y with x | u
  · exact ⟨x, rfl, (isBoundaryVertex_loopCutOutside_inl_iff h x).1 hvB⟩
  · exact absurd hvB (not_isBoundaryVertex_loopCutOutside_inr h u)

/-- Every boundary vertex of the outside has three darts, two of them boundary arcs. -/
theorem loopCutOutside_boundaryVertex_card : ∀ v ∈ (loopCutOutside h).boundaryVertices,
    v.card = 3 ∧ (v.filter (· ∈ (loopCutOutside h).bdry)).card = 2 := by
  intro v hv
  obtain ⟨x, rfl, hx⟩ := exists_eq_vertexOf_inl_of_mem_boundaryVertices_loopCutOutside h v hv
  obtain ⟨h3, h2⟩ := hM.boundaryVertex_card _ (M.vertexOf_mem_boundaryVertices.2 hx)
  have hsub := h.vertexOf_subset_compl x.2
  have hf : ((loopCutOutside h).vertexOf (.inl x)).filter (· ∈ (loopCutOutside h).bdry) =
      (((M.vertexOf x).filter (· ∈ M.bdry)).subtype (· ∉ C)).map Embedding.inl := by
    rw [loopCutOutside_vertexOf_inl]
    ext y
    rcases y with z | u
    · simp [inl_mem_loopCutOutside_bdry h]
    · simp [inr_notMem_loopCutOutside_bdry h]
  rw [hf, loopCutOutside_vertexOf_inl, card_map_inl_subtype hsub,
    card_map_inl_subtype fun y hy => hsub y (mem_filter.1 hy).1]
  exact ⟨h3, h2⟩

/-- The boundary arcs of the outside are its exterior together with the reverse of it. -/
theorem loopCutOutside_exterior_union_map_inv :
    (loopCutOutside h).exterior ∪ (loopCutOutside h).exterior.map
      (loopCutOutside h).inv.toEmbedding = (loopCutOutside h).bdry := by
  ext y
  rw [mem_union, mem_map, mem_loopCutOutside_bdry, mem_loopCutOutside_exterior]
  constructor
  · rintro (⟨z, rfl, hz⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨z, rfl, M.exterior_subset_bdry hz⟩
    · obtain ⟨z, rfl, hz⟩ := (mem_loopCutOutside_exterior h).1 hw
      rw [Equiv.coe_toEmbedding,
        loopCutOutside_inv_inl_of_mem_bdry h (M.exterior_subset_bdry hz) hM]
      exact ⟨_, rfl, hM.inv_mem_bdry _ (M.exterior_subset_bdry hz)⟩
  · rintro ⟨z, rfl, hz⟩
    rw [← hM.exterior_spec.2.2.1, mem_union, mem_map] at hz
    rcases hz with hz | ⟨w, hw, hwz⟩
    · exact Or.inl ⟨z, rfl, hz⟩
    · refine Or.inr ⟨.inl ⟨w, fun hc => h.notMem_bdry _ hc (M.exterior_subset_bdry hw)⟩,
        (mem_loopCutOutside_exterior h).2 ⟨_, rfl, hw⟩, ?_⟩
      rw [Equiv.coe_toEmbedding,
        loopCutOutside_inv_inl_of_mem_bdry h (M.exterior_subset_bdry hw) hM]
      exact congrArg Sum.inl (Subtype.ext hwz)

/-- The exterior of the outside is disjoint from its reverse. -/
theorem disjoint_loopCutOutside_exterior_map_inv :
    Disjoint (loopCutOutside h).exterior
      ((loopCutOutside h).exterior.map (loopCutOutside h).inv.toEmbedding) := by
  rw [disjoint_left]
  intro y hy hy'
  obtain ⟨z, rfl, hz⟩ := (mem_loopCutOutside_exterior h).1 hy
  obtain ⟨w, hw, hwz⟩ := mem_map.1 hy'
  obtain ⟨w', rfl, hw'⟩ := (mem_loopCutOutside_exterior h).1 hw
  rw [Equiv.coe_toEmbedding, loopCutOutside_inv_inl_of_mem_bdry h (M.exterior_subset_bdry hw') hM,
    Sum.inl.injEq, Subtype.ext_iff] at hwz
  exact disjoint_left.1 hM.exterior_spec.2.2.2 hz (mem_map.2 ⟨w', hw', hwz⟩)

/-- **The outside of a cut is a plabic graph**, with the boundary vertices of `M`. -/
theorem isPlabicGraph_loopCutOutside : (loopCutOutside h).IsPlabicGraph := by
  have hnC : ∀ x ∈ M.bdry, x ∉ C := fun x hx hc => h.notMem_bdry x hc hx
  have hinvB : ∀ (z : {x // x ∉ C}) (hz : z.1 ∈ M.bdry), (loopCutOutside h).inv (.inl z) =
      .inl ⟨M.inv z, hnC _ (hM.inv_mem_bdry _ hz)⟩ := fun z hz =>
    loopCutOutside_inv_inl_of_mem_bdry h hz hM
  have hbv : ∀ i, (loopCutOutside h).bvertex i =
      (loopCutOutside h).vertexOf (.inl ⟨M.leg i, h.leg_notMem i⟩) := fun _ => rfl
  refine
    { toIsDiskMap :=
        { toIsConnected := isConnected_loopCutOutside h hM
          inv_mem_bdry := ?_
          euler := (euler_loopCut h hM).1
          boundaryVertex_card := loopCutOutside_boundaryVertex_card h hM
          exists_orbit := ⟨_, loopCutOutside_exterior_mem_faceOrbits h hM,
            (loopCutOutside h).exterior_subset_bdry, loopCutOutside_exterior_union_map_inv h hM,
            disjoint_loopCutOutside_exterior_map_inv h hM⟩ }
      one_le := hM.one_le
      colour_rot := ?_
      leg_notMem_bdry := fun i => by
        change (.inl _ : {x // x ∉ C} ⊕ Unit) ∉ _
        rw [inl_mem_loopCutOutside_bdry]
        exact hM.leg_notMem_bdry i
      bvertex_mem := fun i => (loopCutOutside h).vertexOf_mem_boundaryVertices.2
        ((isBoundaryVertex_loopCutOutside_inl_iff h _).2
          (M.vertexOf_mem_boundaryVertices.1 (hM.bvertex_mem i)))
      bvertex_injective := ?_
      exists_bvertex_eq := ?_
      exists_exterior := ?_ }
  · intro y hy
    obtain ⟨z, rfl, hz⟩ := (mem_loopCutOutside_bdry h).1 hy
    rw [hinvB z hz, inl_mem_loopCutOutside_bdry]
    exact hM.inv_mem_bdry _ hz
  · rintro (x | u) hv
    · exact hM.colour_rot x (mt (isBoundaryVertex_loopCutOutside_inl_iff h x).2 hv)
    · rfl
  · intro i j hij
    rw [hbv, hbv, RotationSystem.vertexOf_eq_vertexOf_iff, sameCycle_loopCutOutside_inl_iff,
      ← RotationSystem.vertexOf_eq_vertexOf_iff] at hij
    exact hM.bvertex_injective hij
  · intro v hv
    obtain ⟨x, rfl, hx⟩ := exists_eq_vertexOf_inl_of_mem_boundaryVertices_loopCutOutside h v hv
    obtain ⟨i, hi⟩ := hM.exists_bvertex_eq _ (M.vertexOf_mem_boundaryVertices.2 hx)
    exact ⟨i, by rwa [hbv, RotationSystem.vertexOf_eq_vertexOf_iff,
      sameCycle_loopCutOutside_inl_iff, ← RotationSystem.vertexOf_eq_vertexOf_iff]⟩
  · intro i
    obtain ⟨d, hd, hdv, hdiv⟩ := hM.exists_exterior i
    have hdB := M.exterior_subset_bdry hd
    refine ⟨.inl ⟨d, hnC _ hdB⟩, (mem_loopCutOutside_exterior h).2 ⟨_, rfl, hd⟩, ?_, ?_⟩
    · rw [hbv, mem_loopCutOutside_vertexOf_inl]
      exact ⟨_, rfl, hdv⟩
    · rw [hinvB _ hdB, hbv, mem_loopCutOutside_vertexOf_inl]
      exact ⟨_, rfl, hdiv⟩

end CutPlabic

end PlabicData

/-! ### The arcs of a loop -/

namespace RotationSystem

variable {H₀ : Type*} [Fintype H₀] [DecidableEq H₀] {R : RotationSystem H₀}

/-- If the rotation at `v(x)` is the cycle `(x, a₁, …, a_k, y, b₁, …, b_l)`, the open arc from `x`
to `y` is `{a₁, …, a_k}`. -/
private theorem rotArc_eq_of_toList {x y : H₀} {as bs : List H₀}
    (hL : R.rot.toList x = x :: as ++ y :: bs) : R.rotArc x y = {z | z ∈ as} := by
  have hnd := nodup_of_toList hL
  have hget : ∀ n (hn : n < (x :: as ++ y :: bs).length),
      (R.rot ^ n) x = (x :: as ++ y :: bs)[n] := fun n hn => by
    rw [← Equiv.Perm.getElem_toList R.rot x n (by rwa [hL])]
    exact List.getElem_of_eq hL _
  have hlen : (x :: as ++ y :: bs).length = as.length + bs.length + 2 := by
    simp only [List.cons_append, List.length_cons, List.length_append]
    omega
  have hy : (R.rot ^ (as.length + 1)) x = y := by
    rw [hget _ (by omega)]
    simp [List.getElem_append_right]
  have has : ∀ k (hk : k < as.length), (x :: as ++ y :: bs)[k + 1]'(by omega) = as[k] := by
    intro k hk
    simp [List.getElem_append_left hk]
  have hdist : R.rotDist x y = as.length + 1 := by
    apply le_antisymm
      (Nat.sInf_le (show as.length + 1 ∈ {m | 0 < m ∧ (R.rot ^ m) x = y} from ⟨by omega, hy⟩))
    obtain ⟨hpos, heq⟩ := Nat.sInf_mem (s := {m | 0 < m ∧ (R.rot ^ m) x = y}) ⟨_, by omega, hy⟩
    by_contra hlt
    push Not at hlt
    change sInf {m | 0 < m ∧ (R.rot ^ m) x = y} < as.length + 1 at hlt
    have h1 := hget _ (by omega : sInf {m | 0 < m ∧ (R.rot ^ m) x = y} < _)
    have h2 := hget (as.length + 1) (by omega)
    rw [heq] at h1
    rw [hy] at h2
    have := (hnd.getElem_inj_iff).1 (h1.symm.trans h2)
    omega
  ext a
  rw [mem_rotArc, hdist, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, hm0, hm, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hget _ (by omega), has k (by omega)]
    exact List.getElem_mem _
  · intro ha
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
    exact ⟨k + 1, by omega, by omega, by rw [hget _ (by omega), has k hk]⟩

/-- If the rotation at `v(d)` is the cycle `(d, a₁, …, a_k, d̄, b₁, …, b_l)`, the relation
`LoopStep d` is `ArcLoopStep d [a₁, …, a_k] [b₁, …, b_l]`. -/
private theorem loopStep_eq_arcLoopStep {d : H₀} {as bs : List H₀}
    (hL : R.rot.toList d = d :: as ++ R.inv d :: bs) :
    R.LoopStep d = R.ArcLoopStep d as bs := by
  have hA := rotArc_eq_of_toList hL
  have hB := rotArc_eq_of_toList (toList_eq_of_toList hL)
  funext z z'
  simp only [LoopStep, ArcLoopStep, hA, hB, Set.mem_setOf_eq, eq_iff_iff]
  tauto

end RotationSystem

/-! ### The side of a loop -/

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}
  (hG : G.IsPlabicGraph) {d : H} {as bs : List H}
  (hL : G.rot.toList d = d :: as ++ G.inv d :: bs) (has : as ≠ []) (hbs : bs ≠ [])

include hG hL

omit hG has hbs in
private theorem mem_toList_iff_of_loop {z : H} : z ∈ G.vertexOf d ↔ z = d ∨ z ∈ as ∨
    z = G.inv d ∨ z ∈ bs := by
  rw [RotationSystem.mem_vertexOf, ← mem_toList_of_toList hL, hL]
  simp

omit hG has hbs in
private theorem notMem_as_of_loop : d ∉ as ∧ G.inv d ∉ as ∧ d ∉ bs ∧ G.inv d ∉ bs ∧
    ∀ z ∈ as, z ∉ bs := by
  have hnd := nodup_of_toList hL
  rw [List.nodup_append] at hnd
  obtain ⟨h1, h2, h3⟩ := hnd
  refine ⟨(List.nodup_cons.1 h1).1,
    fun h => h3 _ (List.mem_cons_of_mem _ h) _ List.mem_cons_self rfl,
    fun h => h3 _ List.mem_cons_self _ (List.mem_cons_of_mem _ h) rfl, (List.nodup_cons.1 h2).1,
    fun z hz hzb => h3 z (List.mem_cons_of_mem _ hz) z (List.mem_cons_of_mem _ hzb) rfl⟩

include has hbs

private theorem notMem_bs_of_mem_loopSide {z : H} (hz : z ∈ G.loopSide d) : z ∉ bs := by
  intro hzb
  rw [RotationSystem.loopSide, Set.mem_setOf_eq, RotationSystem.loopStep_eq_arcLoopStep hL] at hz
  exact hG.toIsDiskMap.loop_separates hL has hbs
    ⟨_, apply_mem_of_toList hL has, z, hzb, hz.2.2⟩

omit hG hbs in
private theorem rot_mem_as_of_loop : G.rot d ∈ as := apply_mem_of_toList hL has

omit hG hbs in
private theorem mem_loopSide_of_mem_as {z : H} (hz : z ∈ as) : z ∈ G.loopSide d := by
  obtain ⟨h1, h2, -, -, -⟩ := notMem_as_of_loop hL
  have hσ := rot_mem_as_of_loop hL has
  refine ⟨fun h => h1 (h ▸ hz), fun h => h2 (h ▸ hz), ?_⟩
  rcases eq_or_ne z (G.rot d) with rfl | hne
  · exact .refl
  · refine .single ⟨fun h => h1 (h ▸ hσ), fun h => h2 (h ▸ hσ), fun h => h1 (h ▸ hz),
      fun h => h2 (h ▸ hz), Or.inr (Or.inr (Or.inl ?_))⟩
    rw [RotationSystem.rotArc_eq_of_toList hL]
    exact ⟨hσ, hz⟩

private theorem mem_as_of_mem_loopSide {z : H} (hz : z ∈ G.loopSide d) (hzu : z ∈ G.vertexOf d) :
    z ∈ as := by
  rcases (mem_toList_iff_of_loop hL).1 hzu with h | h | h | h
  · exact absurd h hz.1
  · exact h
  · exact absurd h hz.2.1
  · exact absurd h (notMem_bs_of_mem_loopSide hG hL has hbs hz)

omit hL has hbs in
private theorem inv_mem_loopSide {z : H} (hz : z ∈ G.loopSide d) : G.inv z ∈ G.loopSide d := by
  refine RotationSystem.LoopStep.mem_loopSide hz ⟨hz.1, hz.2.1, fun h => hz.2.1 ?_,
    fun h => hz.1 ?_, Or.inl rfl⟩
  · rw [← h, hG.inv_involutive]
  · exact G.inv.injective h

private theorem rot_mem_loopSide_of_ne {z : H} (hz : z ∈ G.loopSide d) (hne : G.rot z ≠ G.inv d) :
    G.rot z ∈ G.loopSide d := by
  have hσu : G.rot z ∈ G.vertexOf d ↔ z ∈ G.vertexOf d := by
    rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  by_cases hzu : z ∈ G.vertexOf d
  · have hza := mem_as_of_mem_loopSide hG hL has hbs hz hzu
    obtain ⟨h1, h2, -, -, -⟩ := notMem_as_of_loop hL
    have hσa : G.rot z ∈ as :=
      (apply_mem_or_eq_of_toList hL (List.mem_cons_of_mem _ hza)).resolve_right hne
    exact mem_loopSide_of_mem_as hL has hσa
  · refine RotationSystem.LoopStep.mem_loopSide hz ⟨hz.1, hz.2.1, fun h => hzu ?_,
      fun h => hzu ?_, Or.inr (Or.inl ⟨hzu, Or.inl rfl⟩)⟩
    · rw [← hσu, h]; exact G.self_mem_vertexOf d
    · rw [← hσu, h]
      exact (mem_toList_iff_of_loop hL).2 (Or.inr (Or.inr (Or.inl rfl)))

private theorem leg_notMem_loopSide (hu : ¬G.IsBoundaryVertex (G.vertexOf d))
    (hS : ∀ z ∈ G.loopSide d, z ∉ G.bdry) (i : Fin b) : G.leg i ∉ G.loopSide d := by
  intro hi
  have hbv : G.IsBoundaryVertex (G.vertexOf (G.leg i)) :=
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hσ : G.rot (G.leg i) ∈ G.bdry := by
    by_contra hσB
    exact DiskMap.rot_ne_of_isBoundaryVertex hG.boundaryVertex_card hbv
      (DiskMap.eq_of_notMem_bdry hG.boundaryVertex_card hbv (G.rot_mem_vertexOf _)
        (G.self_mem_vertexOf _) hσB (hG.leg_notMem_bdry i))
  refine hS _ (rot_mem_loopSide_of_ne hG hL has hbs hi fun h => hu ?_) hσ
  have hmem : G.inv d ∈ G.vertexOf d := (mem_toList_iff_of_loop hL).2
    (Or.inr (Or.inr (Or.inl rfl)))
  rw [← G.vertexOf_eq_of_mem hmem, ← h, G.vertexOf_rot]
  exact hbv

end PlabicData

/-! ### Cutting a graph along a loop -/

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- **Cutting a graph along a loop**. Let `K` be a nearly leafless plabic graph and `u = v(d)` an
internal vertex of `K` whose rotation is the cycle `(d, a₁, …, a_k, d̄, b₁, …, b_l)` with
`k, l ≥ 1` (that is, `d̄ ∈ v(d)`, `σ d ≠ d̄` and `σ d̄ ≠ d`), such that the side of `(u, d)`
contains no dart of `B`. Then there are plabic graphs `Y` and `R` and a dart `f` of `Y` with
`f ∉ B_Y`, `σ_Y f = f` and `κ_Y({f}) = κ(u)`, such that `R` has one boundary vertex, no internal
leaf and fewer faces than `K`, `K ∼ Y⟨f ← R⟩`, and `Y` is move-equivalent to a plabic graph with
an internal face consisting of exactly one dart. -/
@[cluster_algebras "lem_loop_decomposition"]
theorem exists_leafGluing_of_loop (K : PlabicGraph b) (hK : K.data.IsNearlyLeafless)
    {d : K.Dart} (hu : ¬K.data.IsBoundaryVertex (K.data.vertexOf d))
    (hloop : K.data.inv d ∈ K.data.vertexOf d) (hk : K.data.rot d ≠ K.data.inv d)
    (hl : K.data.rot (K.data.inv d) ≠ d) (hS : ∀ z ∈ K.data.loopSide d, z ∉ K.data.bdry) :
    ∃ (Y : PlabicGraph b) (f : Y.Dart) (hf : f ∉ Y.data.bdry) (hff : Y.data.rot f = f)
      (R : PlabicGraph 1), Y.data.colour f = K.data.colour d ∧
      (∀ v, ¬R.data.IsInternalLeaf v) ∧ R.data.faces.card < K.data.faces.card ∧
      MoveEquivalent Set.univ K (Y.leafGluing hf hff R) ∧
      ∃ Y' : PlabicGraph b, MoveEquivalent Set.univ Y Y' ∧
        ∃ φ ∈ Y'.data.internalFaces, φ.card = 1 := by
  have hG := K.isPlabicGraph
  have hdι : K.data.inv d ≠ d := hG.inv_ne d
  have hsupp : d ∈ K.data.rot.support := by
    rw [Equiv.Perm.mem_support]
    intro h
    exact hdι ((K.data.mem_vertexOf.1 hloop).eq_of_left h).symm
  have hmem : K.data.inv d ∈ K.data.rot.toList d :=
    Equiv.Perm.mem_toList_iff.2 ⟨K.data.mem_vertexOf.1 hloop, hsupp⟩
  obtain ⟨s0, bs, hst⟩ := List.append_of_mem hmem
  obtain ⟨as, rfl⟩ : ∃ as, s0 = d :: as := by
    have h0 := Equiv.Perm.toList_getElem_zero K.data.rot d hsupp
    rw [List.getElem_of_eq hst] at h0
    cases s0 with
    | nil =>
      simp only [List.nil_append, List.getElem_cons_zero] at h0
      exact absurd h0 hdι
    | cons a as =>
      simp only [List.cons_append, List.getElem_cons_zero] at h0
      exact ⟨as, by rw [h0]⟩
  have hL : K.data.rot.toList d = d :: as ++ K.data.inv d :: bs := hst
  have has : as ≠ [] := by
    rintro rfl
    have := apply_mem_or_eq_of_toList hL List.mem_cons_self
    simp only [List.not_mem_nil, false_or] at this
    exact hk this
  have hbs : bs ≠ [] := by
    rintro rfl
    have := apply_mem_or_eq_of_toList (toList_eq_of_toList hL) List.mem_cons_self
    simp only [List.not_mem_nil, false_or] at this
    exact hl this
  obtain ⟨s, hs⟩ : ∃ s, s = K.data.rot d := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, as.length = q + 1 :=
    ⟨as.length - 1, by have := List.length_pos_iff.2 has; omega⟩
  have hzs : ¬K.data.IsBoundaryVertex (K.data.vertexOf s) := by rwa [hs, K.data.vertexOf_rot]
  have hσp : (K.data.rot ^ (q + 1)) s = K.data.inv d := by
    have hlen : as.length + 1 < (K.data.rot.toList d).length := by rw [hL]; simp
    have hy : K.data.inv d = (K.data.rot ^ (as.length + 1)) d := by
      rw [← Equiv.Perm.getElem_toList (n := as.length + 1) _ _ hlen, List.getElem_of_eq hL]
      simp [List.getElem_append_right]
    rw [hy, hq, pow_succ (n := q + 1), Perm.mul_apply, hs]
  have hrot_inl : ∀ x, (K.data.vertexSplit s (q + 1)).rot (.inl x) =
      if K.data.rot x = K.data.inv d then .inr 0 else if x = d then .inr 1
      else .inl (K.data.rot x) := by
    intro x
    rw [rot_vertexSplit, splitRot_inl]
    have e1 : (q + 1 ≠ 0 ∧ x = (K.data.rot ^ (q + 1 - 1)) s) ↔
        K.data.rot x = K.data.inv d := by
      rw [Nat.add_sub_cancel, ← hσp, pow_succ', Perm.mul_apply, K.data.rot.injective.eq_iff]
      simp
    have e2 : K.data.rot x = s ↔ x = d := by rw [hs]; exact K.data.rot.injective.eq_iff
    simp only [e1, e2]
  have hrot0 : (K.data.vertexSplit s (q + 1)).rot (.inr 0) = .inl s := by
    rw [rot_vertexSplit, splitRot_inr_zero, if_neg (Nat.succ_ne_zero q)]
  have hrot1 : (K.data.vertexSplit s (q + 1)).rot (.inr 1) = .inl (K.data.inv d) := by
    rw [rot_vertexSplit, splitRot_inr_one, if_neg, hσp]
    rintro ⟨-, h⟩
    rw [hσp] at h
    exact hk (hs.symm.trans h.symm)
  have hpcard : q + 1 ≤ (K.data.vertexOf s).card := by
    rw [hs, K.data.vertexOf_rot]
    have hasnd : as.Nodup := (List.nodup_cons.1 (List.nodup_append.1 (nodup_of_toList hL)).1).2
    rw [← hq, ← List.toFinset_card_of_nodup hasnd]
    refine card_le_card fun z hz => ?_
    rw [List.mem_toFinset] at hz
    exact (mem_toList_iff_of_loop hL).2 (Or.inr (Or.inl hz))
  have hM := hG.vertexSplit hzs (q + 1)
  set M := K.data.vertexSplit s (q + 1) with hMdef
  obtain ⟨C, hCl, hC0, hC1⟩ : ∃ C : Finset (K.Dart ⊕ Fin 2),
      (∀ z, (Sum.inl z : K.Dart ⊕ Fin 2) ∈ C ↔ z ∈ K.data.loopSide d) ∧ Sum.inr 0 ∈ C ∧
        Sum.inr 1 ∉ C := by
    classical
    exact ⟨insert (.inr 0) ((univ.filter (· ∈ K.data.loopSide d)).map Embedding.inl),
      fun z => by simp, by simp, by simp⟩
  have hcut : M.IsLoopCutSite C (.inr 0) :=
    { inv_involutive := splitInv_involutive hG.inv_involutive
      inv_ne := splitInv_ne _ hG.inv_ne
      mem := hC0
      inv_notMem := hC1
      inv_mem := by
        rintro (z | i) hc hne
        · exact (hCl _).2 (inv_mem_loopSide hG ((hCl z).1 hc))
        · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
          · exact absurd rfl hne
          · exact absurd hc hC1
      rot_mem := by
        rintro (z | i) hc
        · have hz := (hCl z).1 hc
          rw [hrot_inl]
          split_ifs with h1 h2
          · exact hC0
          · exact absurd h2 hz.1
          · exact (hCl _).2 (rot_mem_loopSide_of_ne hG hL has hbs hz h1)
        · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
          · rw [hrot0, hs]
            exact (hCl _).2 (mem_loopSide_of_mem_as hL has (rot_mem_as_of_loop hL has))
          · exact absurd hc hC1
      notMem_bdry := by
        rintro (z | i) hc
        · rw [hMdef, bdry_vertexSplit, mem_map]
          rintro ⟨y, hy, hyz⟩
          rw [Embedding.inl_apply, Sum.inl.injEq] at hyz
          subst hyz
          exact hS _ ((hCl y).1 hc) hy
        · simp [hMdef]
      leg_notMem := fun i hc => leg_notMem_loopSide hG hL has hbs hu hS i ((hCl _).1 hc) }
  have hY := isPlabicGraph_loopCutOutside hcut hM
  have hR := isPlabicGraph_loopCutInside hcut hM
  let Yb : PlabicGraph b := ⟨_, loopCutOutside hcut, hY⟩
  let Rb : PlabicGraph 1 := ⟨_, loopCutInside hcut, hR⟩
  have hf : (Sum.inr () : Yb.Dart) ∉ Yb.data.bdry := inr_notMem_loopCutOutside_bdry hcut
  have hff : Yb.data.rot (Sum.inr ()) = Sum.inr () := rfl
  have hchain : MoveEquivalent Set.univ K (Yb.leafGluing hf hff Rb) := by
    refine MoveEquivalent.trans (G' := K.vertexSplit hzs (q + 1)) ?_ ?_
    · exact MoveEquivalent.of_isLocalMove (t := .m3) (Set.mem_univ _)
        (Or.inr ⟨Sum.inr 0, K.data.isContractibleEdge_vertexSplit s (q + 1) hzs hpcard,
          K.data.isomorphic_contractEdge_vertexSplit s (q + 1) hG.inv_involutive⟩)
    · exact MoveEquivalent.of_isomorphic (leafGluing_loopCut_isomorphic hcut
        (loopCutInside_rot_symm_leg hcut) rfl (isLeafGluingSite_of_isPlabicGraph hY hR hf hff))
  have hdS : (Sum.inl d : K.Dart ⊕ Fin 2) ∉ C := fun h => ((hCl d).1 h).1 rfl
  have hdbS : (Sum.inl (K.data.inv d) : K.Dart ⊕ Fin 2) ∉ C := fun h => ((hCl _).1 h).2.1 rfl
  have hιu : K.data.inv d ∉ K.data.bdry := fun h => hu ⟨_, hloop, h⟩
  set xd : {x // x ∉ C} := ⟨.inl d, hdS⟩
  set xb : {x // x ∉ C} := ⟨.inl (K.data.inv d), hdbS⟩
  set xe : {x // x ∉ C} := ⟨.inr 1, hC1⟩
  have hinvb : (loopCutOutside hcut).inv (.inl xb) = .inl xd := by
    rw [loopCutOutside_inv_inl_of_notMem hcut (x := xb)
      (by change Sum.inl (K.data.inv (K.data.inv d)) ∉ C; rw [hG.inv_involutive]; exact hdS)]
    simp only [Sum.inl.injEq, Subtype.mk.injEq, xb, xd]
    change Sum.inl (K.data.inv (K.data.inv d)) = _
    rw [hG.inv_involutive]
  have hrotd : (loopCutOutside hcut).rot (.inl xd) = .inl xe := by
    rw [loopCutOutside_rot_inl]
    simp only [Sum.inl.injEq, Subtype.mk.injEq, xd, xe]
    rw [hrot_inl, if_neg hk, if_pos rfl]
  have hinvf : (loopCutOutside hcut).inv (.inr ()) = .inl xe := rfl
  have hrote : (loopCutOutside hcut).rot (.inl xe) = .inl xb := by
    rw [loopCutOutside_rot_inl]
    simp only [Sum.inl.injEq, Subtype.mk.injEq, xe, xb]
    exact hrot1
  have hxbB : (Sum.inl xb : {x // x ∉ C} ⊕ Unit) ∉ (loopCutOutside hcut).bdry := by
    rw [inl_mem_loopCutOutside_bdry]
    change Sum.inl (K.data.inv d) ∉ K.data.bdry.map Embedding.inl
    simpa using hιu
  have hxeB : (Sum.inl xe : {x // x ∉ C} ⊕ Unit) ∉ (loopCutOutside hcut).bdry := by
    rw [inl_mem_loopCutOutside_bdry]
    change Sum.inr 1 ∉ K.data.bdry.map Embedding.inl
    simp
  have hface3 : ∀ y ∈ (loopCutOutside hcut).faceOf (.inl xb), y ∉ (loopCutOutside hcut).bdry := by
    intro y hy
    have hT : ∀ z ∈ ({.inl xb, .inl xe, .inr ()} : Set ({x // x ∉ C} ⊕ Unit)),
        (loopCutOutside hcut).facePerm z ∈
          ({.inl xb, .inl xe, .inr ()} : Set ({x // x ∉ C} ⊕ Unit)) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · rw [RotationSystem.facePerm_apply, hinvb, hrotd]
        exact Or.inr (Or.inl rfl)
      · rw [RotationSystem.facePerm_apply,
          loopCutOutside_inv_inl_of_mem hcut (x := xe) (show Sum.inr 0 ∈ C from hC0)]
        exact Or.inr (Or.inr rfl)
      · rw [RotationSystem.facePerm_apply, hinvf, hrote]
        exact Or.inl rfl
    have := mem_of_sameCycle_of_mapsTo'' hT (by simp) ((RotationSystem.mem_faceOf _).1 hy)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    rcases this with rfl | rfl | rfl
    · exact hxbB
    · exact hxeB
    · exact inr_notMem_loopCutOutside_bdry hcut
  have hYfaces : 2 ≤ (loopCutOutside hcut).faces.card := by
    obtain ⟨z0, hz0, -, -⟩ := hY.exists_exterior ⟨0, hY.one_le⟩
    have hz0B := (loopCutOutside hcut).exterior_subset_bdry hz0
    have hF1 : (loopCutOutside hcut).faceOf (.inl xb) ∈ (loopCutOutside hcut).faces :=
      (loopCutOutside hcut).faceOf_mem_faces hxbB
    have hF2 : (loopCutOutside hcut).faceOf ((loopCutOutside hcut).inv z0) ∈
        (loopCutOutside hcut).faces := by
      refine (loopCutOutside hcut).mem_faces.2
        ⟨fun h => ?_, (loopCutOutside hcut).faceOf_mem_faceOrbits _⟩
      have h1 : (loopCutOutside hcut).inv z0 ∈ (loopCutOutside hcut).exterior :=
        h ▸ (loopCutOutside hcut).self_mem_faceOf _
      exact disjoint_left.1 hY.disjoint_exterior_map_inv h1 (mem_map_of_mem _ hz0)
    have hne : (loopCutOutside hcut).faceOf (.inl xb) ≠
        (loopCutOutside hcut).faceOf ((loopCutOutside hcut).inv z0) := by
      intro h
      exact hface3 _ (h ▸ (loopCutOutside hcut).self_mem_faceOf _) (hY.inv_mem_bdry _ hz0B)
    have := card_le_card (show {(loopCutOutside hcut).faceOf (.inl xb),
        (loopCutOutside hcut).faceOf ((loopCutOutside hcut).inv z0)} ⊆
        (loopCutOutside hcut).faces by
      intro F hF
      simp only [mem_insert, mem_singleton] at hF
      rcases hF with rfl | rfl
      · exact hF1
      · exact hF2)
    rwa [card_pair hne] at this
  have hrot_ne : ∀ c ∈ C, M.rot c ≠ c := by
    rintro (z | i) hc
    · have hz := (hCl z).1 hc
      rw [hrot_inl]
      split_ifs with h1 h2
      · simp
      · simp
      · intro hzz
        have hzz : K.data.rot z = z := Sum.inl_injective hzz
        have hvz : K.data.vertexOf z = {z} := by
          ext y
          rw [RotationSystem.mem_vertexOf, mem_singleton]
          exact ⟨fun hy => (hy.eq_of_left hzz).symm, fun h => h ▸ SameCycle.refl _ _⟩
        have hleaf : K.data.IsInternalLeaf (K.data.vertexOf z) := by
          refine ⟨K.data.vertexOf_mem_internalVertices.2 ?_, by rw [hvz, card_singleton]⟩
          rintro ⟨y, hy, hyB⟩
          rw [hvz, mem_singleton] at hy
          subst hy
          exact hS _ hz hyB
        obtain ⟨i, -, y, hy, hyi⟩ := hK _ hleaf
        rw [hvz, mem_singleton] at hy
        subst hy
        have hiz := inv_mem_loopSide hG hz
        have hleg : K.data.inv y = K.data.leg i := by
          have hmem : K.data.inv y ∈ (K.data.bvertex i).filter (· ∉ K.data.bdry) :=
            mem_filter.2 ⟨hyi, hS _ hiz⟩
          rw [hG.filter_bvertex_notMem_bdry, mem_singleton] at hmem
          exact hmem
        exact leg_notMem_loopSide hG hL has hbs hu hS i (hleg ▸ hiz)
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · rw [hrot0]
        simp
      · exact absurd hc hC1
  refine ⟨Yb, .inr (), hf, hff, Rb, ?_, ?_, ?_, hchain, ?_⟩
  · change K.data.colour s = K.data.colour d
    rw [hs]
    exact hG.colour_rot d hu
  · rintro v ⟨hv, hcard⟩
    obtain ⟨hvV, hvB⟩ := (loopCutInside hcut).mem_internalVertices.1 hv
    obtain ⟨x, rfl⟩ := (loopCutInside hcut).mem_vertices.1 hvV
    rcases x with c | i
    · have hne : (loopCutInside hcut).rot (.inl c) ≠ .inl c := by
        rw [loopCutInside_rot_inl]
        simpa [Subtype.ext_iff] using hrot_ne c c.2
      have h2 := card_le_card (show ({.inl c, (loopCutInside hcut).rot (.inl c)} : Finset _) ⊆
          (loopCutInside hcut).vertexOf (.inl c) by
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact (loopCutInside hcut).self_mem_vertexOf _
        · exact (loopCutInside hcut).rot_mem_vertexOf _)
      rw [card_pair hne.symm] at h2
      change ((loopCutInside hcut).vertexOf (.inl c)).card = 1 at hcard
      omega
    · exact hvB (isBoundaryVertex_loopCutInside_inr hcut i)
  · have hfaces := (MoveEquivalent.card_eq hchain).2.1
    have hglue : (Yb.leafGluing hf hff Rb).data.faces.card + 1 =
        (loopCutOutside hcut).faces.card + (loopCutInside hcut).faces.card :=
      (isLeafGluingSite_of_isPlabicGraph hY hR hf hff).card_faces_leafGluing hY hR
    change (loopCutInside hcut).faces.card < K.data.faces.card
    omega
  · have hext : M.IsContractibleEdge (.inr 0) :=
      K.data.isContractibleEdge_vertexSplit s (q + 1) hzs hpcard
    have he : (loopCutOutside hcut).IsContractibleEdge (.inr ()) :=
      { vertexOf_ne := by
          intro h
          have : (Sum.inl xe : {x // x ∉ C} ⊕ Unit) ∈ (loopCutOutside hcut).vertexOf (.inr ()) := by
            rw [h, hinvf]
            exact (loopCutOutside hcut).self_mem_vertexOf _
          rw [loopCutOutside_vertexOf_inr, mem_singleton] at this
          simp at this
        mem_internalVertices :=
          (loopCutOutside hcut).vertexOf_mem_internalVertices.2
            (not_isBoundaryVertex_loopCutOutside_inr hcut ())
        inv_mem_internalVertices := by
          rw [hinvf]
          refine (loopCutOutside hcut).vertexOf_mem_internalVertices.2 fun hb => ?_
          exact M.vertexOf_mem_internalVertices.1 hext.inv_mem_internalVertices
            ((isBoundaryVertex_loopCutOutside_inl_iff hcut xe).1 hb)
        colour_inv := rfl }
    refine ⟨Yb.contractEdge he, MoveEquivalent.of_isLocalMove (t := .m3) (Set.mem_univ _)
      (Or.inl ⟨.inr (), he, PlabicData.Isomorphic.refl _⟩), ?_⟩
    have hx' : (Sum.inl xb : {x // x ∉ C} ⊕ Unit) ∈
        (({Sum.inr (), (loopCutOutside hcut).inv (Sum.inr ())} : Set ({x // x ∉ C} ⊕ Unit))ᶜ) :=
      mem_compl_pair_iff.2 ⟨by simp, by rw [hinvf]; simp [xb, xe]⟩
    set x' : (Yb.contractEdge he).Dart := ⟨.inl xb, hx'⟩ with hx'def
    have hx'B : x' ∉ (Yb.contractEdge he).data.bdry := fun h =>
      hxbB (mem_contractEdge_bdry.1 h)
    have hfix : (Yb.contractEdge he).data.facePerm x' = x' := by
      change ((loopCutOutside hcut).contractEdge (.inr ()) (he.leg_mem hY)).rot
        (((loopCutOutside hcut).contractEdge (.inr ()) (he.leg_mem hY)).inv x') = x'
      have hinv' : ((loopCutOutside hcut).contractEdge (.inr ()) (he.leg_mem hY)).inv x' =
          ⟨.inl xd, mem_compl_pair_iff.2 ⟨by simp, by rw [hinvf]; simp [xd, xe]⟩⟩ :=
        Subtype.ext (by rw [coe_contractEdge_inv hY.inv_involutive]; exact hinvb)
      rw [hinv']
      apply Subtype.ext
      rw [coe_contractEdge_rot_of_eq_inv_of_eq (hrotd.trans hinvf.symm) rfl
        (mem_compl_pair_iff.2 ⟨by rw [hinvf, hrote]; simp, by rw [hinvf, hrote]; simp [xb, xe]⟩)]
      exact hrote
    refine ⟨(Yb.contractEdge he).data.faceOf x', ?_, ?_⟩
    · rw [RotationSystem.faceOf_eq_singleton _ hfix, DiskMap.mem_internalFaces]
      refine ⟨?_, disjoint_singleton_left.2 hx'B⟩
      rw [← RotationSystem.faceOf_eq_singleton _ hfix]
      exact (Yb.contractEdge he).data.faceOf_mem_faces hx'B
    · rw [RotationSystem.faceOf_eq_singleton _ hfix, card_singleton]

end PlabicGraph

end ClusterAlgebras
