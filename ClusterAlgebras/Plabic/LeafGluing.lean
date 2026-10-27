/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DiskMap
public import ClusterAlgebras.Plabic.FirstReturn
public import ClusterAlgebras.Plabic.TripleDiagram

/-!
# Gluing a plabic graph into a leaf

Let `Y = (H_Y, ι_Y, σ_Y, B_Y, κ_Y, β_Y)` be a plabic graph and `f` a dart of `Y` forming an
internal leaf: `f ∉ B_Y` and `σ_Y f = f`. Let `R` be a plabic graph with one boundary vertex
`β_R(1) = {p̄, p, g}`, on which `σ_R` is the cycle `p̄ ↦ p ↦ g ↦ p̄`, with `B_R = {p, p̄}` and
leg `g`. Gluing `R` into the leaf `{f}` deletes the leaf of `Y` and the boundary vertex of `R`,
and joins the two dangling darts `f* = ι_Y f` and `ḡ = ι_R g` into one edge `{f*, ḡ}`. The result
has the boundary of `Y`. Its vertices, edges and orbits of the face permutation are those of `Y`
and `R` with two of each removed, so it is again a plabic graph, with as many faces as `Y` and `R`
together minus one.

## Main definitions

* `ClusterAlgebras.PlabicData.IsLeafGluingSite Y f R p g`: the hypotheses under which `R` can be
  glued into the leaf `{f}` of `Y`.
* `ClusterAlgebras.PlabicData.leafGluing`: the gluing `Y⟨f ← R⟩` of `R` into the leaf `{f}` of
  `Y`.

## Main results

* `ClusterAlgebras.PlabicData.IsLeafGluingSite.card_faceOrbits_leafGluing`: the face permutation
  of the gluing has as many orbits as those of `Y` and `R` together, minus two.
* `ClusterAlgebras.PlabicData.isLeafGluingSite_of_isPlabicGraph`,
  `ClusterAlgebras.PlabicData.IsLeafGluingSite.isPlabicGraph_leafGluing`,
  `ClusterAlgebras.PlabicData.IsLeafGluingSite.card_faces_leafGluing`: a gluing of plabic graphs
  is a plabic graph, with as many faces as `Y` and `R` together minus one.

## Implementation notes

* FWZ assume `H_Y ∩ H_R = ∅` and take the darts in `H_Y ∪ H_R`; here the darts of the
  gluing form the subset `leafGluingDarts f R p g` of the disjoint union `H_Y ⊕ H_R`, the
  complement of `{f, p̄, p, g}`.
* The involution of the gluing is the restriction of the conjugate of `ι_Y ⊕ ι_R` by the
  transposition of `f` and `ḡ`; this conjugate pairs `f*` with `ḡ` and `f` with `g`, and agrees
  with `ι_Y ⊕ ι_R` elsewhere. The rotation is the restriction of `σ_Y ⊕ σ_R`.
* The labelling `β_Y` is recorded by the legs of `Y` (`PlabicData.leg`), which must therefore
  avoid `f`: this is the hypothesis `IsLeafGluingSite.leg_ne`, automatic for a plabic graph `Y`.
* The darts `p` and `g` are data of the hypotheses. For a plabic graph `R` with one boundary
  vertex they are `p = σ_R⁻¹(g₁)` and the leg `g = g₁` (`isLeafGluingSite_of_isPlabicGraph`), so
  the gluing depends only on `Y`, `f` and `R`. The labelling of `R` plays no role, and the
  remaining results are stated for any number of labels of `R`.
* Orbits are counted with `numOrbits`. The face permutation (respectively the rotation) of the
  gluing is the first-return map, to the darts of the gluing, of the permutation of `H_Y ⊕ H_R`
  obtained from `φ_Y ⊕ φ_R` (respectively `σ_Y ⊕ σ_R`) by merging orbits along two
  transpositions; each merge removes one orbit.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Function Equiv Equiv.Perm

/-! ### Orbits of a sum of permutations -/

section SumCongr

variable {α β : Type*}

/-- The powers of `a ⊕ b` are the sums of the powers. -/
private theorem sumCongr_zpow (a : Perm α) (b : Perm β) (n : ℤ) :
    Perm.sumCongr a b ^ n = Perm.sumCongr (a ^ n) (b ^ n) := by
  simpa using (map_zpow (Perm.sumCongrHom α β) (a, b) n).symm

/-- Two darts of `α` lie in one orbit of `a ⊕ b` iff they lie in one orbit of `a`. -/
@[simp]
private theorem sameCycle_sumCongr_inl_inl {a : Perm α} {b : Perm β} {x y : α} :
    (Perm.sumCongr a b).SameCycle (Sum.inl x) (Sum.inl y) ↔ a.SameCycle x y := by
  simp [Perm.SameCycle, sumCongr_zpow]

/-- Two darts of `β` lie in one orbit of `a ⊕ b` iff they lie in one orbit of `b`. -/
@[simp]
private theorem sameCycle_sumCongr_inr_inr {a : Perm α} {b : Perm β} {x y : β} :
    (Perm.sumCongr a b).SameCycle (Sum.inr x) (Sum.inr y) ↔ b.SameCycle x y := by
  simp [Perm.SameCycle, sumCongr_zpow]

/-- No orbit of `a ⊕ b` meets both `α` and `β`. -/
@[simp]
private theorem not_sameCycle_sumCongr_inl_inr {a : Perm α} {b : Perm β} {x : α} {y : β} :
    ¬(Perm.sumCongr a b).SameCycle (Sum.inl x) (Sum.inr y) := by
  simp [Perm.SameCycle, sumCongr_zpow]

/-- No orbit of `a ⊕ b` meets both `β` and `α`. -/
@[simp]
private theorem not_sameCycle_sumCongr_inr_inl {a : Perm α} {b : Perm β} {x : β} {y : α} :
    ¬(Perm.sumCongr a b).SameCycle (Sum.inr x) (Sum.inl y) := by
  simp [Perm.SameCycle, sumCongr_zpow]

/-- The orbits of `a ⊕ b` are those of `a` and those of `b`. -/
private theorem numOrbits_sumCongr [Finite α] [Finite β] (a : Perm α) (b : Perm β) :
    numOrbits (Perm.sumCongr a b) = numOrbits a + numOrbits b := by
  unfold numOrbits
  rw [← Nat.card_sum]
  refine Nat.card_congr
    { toFun := Quotient.lift (Sum.elim (fun x => Sum.inl ⟦x⟧) (fun y => Sum.inr ⟦y⟧)) ?_
      invFun := Sum.elim
        (Quotient.map Sum.inl fun x y h => sameCycle_sumCongr_inl_inl.2 h)
        (Quotient.map Sum.inr fun x y h => sameCycle_sumCongr_inr_inr.2 h)
      left_inv := ?_
      right_inv := ?_ }
  · rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (Quotient.sound (sameCycle_sumCongr_inl_inl.1 h))
    · exact absurd h not_sameCycle_sumCongr_inl_inr
    · exact absurd h not_sameCycle_sumCongr_inr_inl
    · exact congrArg Sum.inr (Quotient.sound (sameCycle_sumCongr_inr_inr.1 h))
  · intro q
    induction q using Quotient.inductionOn with | h x => ?_
    rcases x with x | x <;> rfl
  · rintro (q | q)
    · induction q using Quotient.inductionOn with | h x => rfl
    · induction q using Quotient.inductionOn with | h x => rfl

/-- Two successive merges of distinct orbits remove two orbits. -/
theorem numOrbits_eq_numOrbits_mul_swap_mul_swap_add_two [Finite α] [DecidableEq α] {Φ : Perm α}
    {a b c d : α} (hab : ¬Φ.SameCycle a b) (hcd : ¬(Φ * swap a b).SameCycle c d) :
    numOrbits Φ = numOrbits (Φ * swap a b * swap c d) + 2 := by
  have h₁ := numOrbits_eq_add_one_of_merge hab fun _ _ => sameCycle_mul_swap_iff Φ hab
  have h₂ := numOrbits_eq_add_one_of_merge hcd fun _ _ => sameCycle_mul_swap_iff _ hcd
  omega

end SumCongr

/-- A permutation's orbit through `x` stays inside any set containing `x` and closed under it. -/
private theorem mem_of_sameCycle_of_forall_mem {α : Type*} [Finite α] {π : Perm α} {S : Set α}
    (hS : ∀ y ∈ S, π y ∈ S) {x y : α} (hx : x ∈ S) (h : π.SameCycle x y) : y ∈ S := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hS _ ih

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

/-- The orbits of the face permutation are counted by `numOrbits`. -/
private theorem card_faceOrbits_eq_numOrbits : R.faceOrbits.card = numOrbits R.facePerm :=
  (numOrbits_eq_card_image R.facePerm).symm

/-- The vertices are counted by `numOrbits`. -/
private theorem card_vertices_eq_numOrbits : R.vertices.card = numOrbits R.rot :=
  (numOrbits_eq_card_image R.rot).symm

/-- A rotation system whose involution is fixed-point-free has half as many edges as darts. -/
private theorem two_mul_card_edges (hinv : Involutive R.inv) (hfix : ∀ d, R.inv d ≠ d) :
    2 * R.edges.card = Fintype.card H := by
  have hfib : ∀ s ∈ univ.image R.edgeOf,
      ({a ∈ univ | R.edgeOf a = s} : Finset H).card = 2 := by
    intro s hs
    obtain ⟨d, -, rfl⟩ := mem_image.1 hs
    have : ({a ∈ univ | R.edgeOf a = R.edgeOf d} : Finset H) = R.edgeOf d := by
      ext a
      simp only [mem_filter, mem_univ, true_and, mem_edgeOf]
      refine ⟨fun h => R.mem_edgeOf.1 (h ▸ R.mem_edgeOf.2 (Or.inl rfl)), ?_⟩
      rintro (rfl | rfl)
      · rfl
      · ext x
        simp only [mem_edgeOf, hinv d]
        tauto
    rw [this, edgeOf, card_pair (hfix d).symm]
  rw [← card_univ, card_eq_sum_card_image R.edgeOf univ, sum_const_nat hfib, edges, mul_comm]

end RotationSystem

namespace PlabicData

variable {HY HR : Type*} [DecidableEq HR] {b c : ℕ}

/-! ### The data of a gluing -/

/-- The hypotheses of the gluing of `R` into the leaf `{f}` of `Y`: `ι_Y` and `ι_R` are
fixed-point-free involutions; `f ∉ B_Y` and `σ_Y f = f`; the legs of `Y` avoid `f`;
`B_R = {p, p̄}`, `g ∉ B_R`, and `σ_R` permutes `{p̄, p, g}` as the cycle `p̄ ↦ p ↦ g ↦ p̄`. -/
structure IsLeafGluingSite (Y : PlabicData HY b) (f : HY) (R : PlabicData HR c) (p g : HR) :
    Prop where
  /-- `ι_Y` is an involution. -/
  inv_involutive_left : Involutive Y.inv
  /-- `ι_Y` has no fixed point. -/
  inv_ne_left : ∀ d, Y.inv d ≠ d
  /-- `ι_R` is an involution. -/
  inv_involutive_right : Involutive R.inv
  /-- `ι_R` has no fixed point. -/
  inv_ne_right : ∀ d, R.inv d ≠ d
  /-- `f ∉ B_Y`. -/
  notMem_bdry_left : f ∉ Y.bdry
  /-- `σ_Y f = f`. -/
  rot_left : Y.rot f = f
  /-- The legs of `Y` avoid `f`. -/
  leg_ne : ∀ i, Y.leg i ≠ f
  /-- `B_R = {p, p̄}`. -/
  bdry_right : R.bdry = {p, R.inv p}
  /-- `g ∉ B_R`. -/
  notMem_bdry_right : g ∉ R.bdry
  /-- `σ_R p̄ = p`. -/
  rot_inv_right : R.rot (R.inv p) = p
  /-- `σ_R p = g`. -/
  rot_right : R.rot p = g
  /-- `σ_R g = p̄`. -/
  rot_rot_right : R.rot g = R.inv p

/-- The darts `(H_Y \ {f}) ∪ (H_R \ {p̄, p, g})` of the gluing of `R` into the leaf `{f}`, as a
subset of `H_Y ⊕ H_R`. -/
abbrev leafGluingDarts (f : HY) (R : PlabicData HR c) (p g : HR) : Set (HY ⊕ HR) :=
  {Sum.inl f, Sum.inr (R.inv p), Sum.inr p, Sum.inr g}ᶜ

omit [DecidableEq HR] in
/-- A dart of the gluing is none of `f`, `p̄`, `p`, `g`. -/
theorem ne_of_mem_leafGluingDarts {f : HY} {R : PlabicData HR c} {p g : HR} {x : HY ⊕ HR}
    (hx : x ∈ leafGluingDarts f R p g) :
    x ≠ Sum.inl f ∧ x ≠ Sum.inr (R.inv p) ∧ x ≠ Sum.inr p ∧ x ≠ Sum.inr g := by
  simpa [not_or] using hx

section Basic

variable {Y : PlabicData HY b} {f : HY} {R : PlabicData HR c} {p g : HR}

namespace IsLeafGluingSite

variable (h : Y.IsLeafGluingSite f R p g)

include h

/-- `ι_Y` is an involution. -/
theorem inv_inv_left (d : HY) : Y.inv (Y.inv d) = d := h.inv_involutive_left d

/-- `ι_R` is an involution. -/
theorem inv_inv_right (d : HR) : R.inv (R.inv d) = d := h.inv_involutive_right d

/-- `f* ≠ f`. -/
theorem inv_ne_self_left : Y.inv f ≠ f := h.inv_ne_left f

/-- `σ_Y f* ≠ f`. -/
theorem rot_inv_ne_left : Y.rot (Y.inv f) ≠ f := fun e =>
  h.inv_ne_self_left (Y.rot.injective (e.trans h.rot_left.symm))

/-- `σ_Y d = f` iff `d = f`. -/
theorem rot_eq_f_iff {d : HY} : Y.rot d = f ↔ d = f :=
  Y.rot.injective.eq_iff' h.rot_left

/-- `p ∈ B_R`. -/
theorem mem_bdry_p : p ∈ R.bdry := by simp [h.bdry_right]

/-- `p̄ ∈ B_R`. -/
theorem mem_bdry_inv_p : R.inv p ∈ R.bdry := by simp [h.bdry_right]

/-- `p ≠ p̄`. -/
theorem p_ne_inv_p : p ≠ R.inv p := (h.inv_ne_right p).symm

/-- `g ≠ p`. -/
theorem g_ne_p : g ≠ p := fun e => h.notMem_bdry_right (e ▸ h.mem_bdry_p)

/-- `g ≠ p̄`. -/
theorem g_ne_inv_p : g ≠ R.inv p := fun e => h.notMem_bdry_right (e ▸ h.mem_bdry_inv_p)

/-- `ḡ ≠ g`. -/
theorem inv_g_ne_g : R.inv g ≠ g := h.inv_ne_right g

/-- `ḡ ≠ p`. -/
theorem inv_g_ne_p : R.inv g ≠ p := fun e => h.g_ne_inv_p (by rw [← e, h.inv_inv_right])

/-- `ḡ ≠ p̄`. -/
theorem inv_g_ne_inv_p : R.inv g ≠ R.inv p := fun e => h.g_ne_p (R.inv.injective e)

/-- `σ_R d = p̄` iff `d = g`. -/
theorem rot_eq_inv_p_iff {d : HR} : R.rot d = R.inv p ↔ d = g :=
  R.rot.injective.eq_iff' h.rot_rot_right

/-- `σ_R d = p` iff `d = p̄`. -/
theorem rot_eq_p_iff {d : HR} : R.rot d = p ↔ d = R.inv p :=
  R.rot.injective.eq_iff' h.rot_inv_right

/-- `σ_R d = g` iff `d = p`. -/
theorem rot_eq_g_iff {d : HR} : R.rot d = g ↔ d = p :=
  R.rot.injective.eq_iff' h.rot_right

/-- `ι_R d = g` iff `d = ḡ`. -/
theorem inv_eq_g_iff {d : HR} : R.inv d = g ↔ d = R.inv g :=
  h.inv_involutive_right.eq_iff

/-- `ι_R d = p` iff `d = p̄`. -/
theorem inv_eq_p_iff {d : HR} : R.inv d = p ↔ d = R.inv p :=
  h.inv_involutive_right.eq_iff

/-- `ι_Y d = f` iff `d = f*`. -/
theorem inv_eq_f_iff {d : HY} : Y.inv d = f ↔ d = Y.inv f :=
  h.inv_involutive_left.eq_iff

end IsLeafGluingSite

end Basic

variable [DecidableEq HY]

/-- The involution of `H_Y ⊕ H_R` pairing `f*` with `ḡ` and `f` with `g`, and agreeing with
`ι_Y ⊕ ι_R` elsewhere. -/
def leafGluingInv (Y : PlabicData HY b) (f : HY) (R : PlabicData HR c) (g : HR) :
    Perm (HY ⊕ HR) :=
  swap (Sum.inl f) (Sum.inr (R.inv g)) * Perm.sumCongr Y.inv R.inv *
    swap (Sum.inl f) (Sum.inr (R.inv g))

/-- `leafGluingInv Y f R g` is the conjugate of `ι_Y ⊕ ι_R` by the transposition of `f` and `ḡ`. -/
theorem leafGluingInv_apply (Y : PlabicData HY b) (f : HY) (R : PlabicData HR c) (g : HR)
    (x : HY ⊕ HR) :
    leafGluingInv Y f R g x = swap (Sum.inl f) (Sum.inr (R.inv g))
      (Perm.sumCongr Y.inv R.inv (swap (Sum.inl f) (Sum.inr (R.inv g)) x)) :=
  rfl

namespace IsLeafGluingSite

variable {Y : PlabicData HY b} {f : HY} {R : PlabicData HR c} {p g : HR}
  (h : Y.IsLeafGluingSite f R p g)

include h

omit [DecidableEq HY] in
/-- A dart lies in the gluing iff its image under `σ_Y ⊕ σ_R` does. -/
theorem rot_mem_iff (x : HY ⊕ HR) :
    Perm.sumCongr Y.rot R.rot x ∈ leafGluingDarts f R p g ↔ x ∈ leafGluingDarts f R p g := by
  rcases x with y | r
  · simp [h.rot_eq_f_iff]
  · simp only [Perm.sumCongr_apply, Sum.map_inr, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, reduceCtorEq, Sum.inr.injEq, false_or, h.rot_eq_inv_p_iff,
      h.rot_eq_p_iff, h.rot_eq_g_iff]
    tauto

omit [DecidableEq HY] in
/-- `ι_Y ⊕ ι_R` is an involution. -/
theorem sumCongr_inv_inv (x : HY ⊕ HR) :
    Perm.sumCongr Y.inv R.inv (Perm.sumCongr Y.inv R.inv x) = x := by
  rcases x with y | r
  · simp [h.inv_inv_left]
  · simp [h.inv_inv_right]

/-- The involution of the gluing sends `f` to `g`. -/
theorem leafGluingInv_inl_f : leafGluingInv Y f R g (Sum.inl f) = Sum.inr g := by
  rw [leafGluingInv_apply, swap_apply_left, Perm.sumCongr_apply, Sum.map_inr, h.inv_inv_right,
    swap_apply_of_ne_of_ne (x := Sum.inr g) (by simp) (by simpa using h.inv_g_ne_g.symm)]

/-- The involution of the gluing sends `g` to `f`. -/
theorem leafGluingInv_inr_g : leafGluingInv Y f R g (Sum.inr g) = Sum.inl f := by
  rw [leafGluingInv_apply,
    swap_apply_of_ne_of_ne (x := Sum.inr g) (by simp) (by simpa using h.inv_g_ne_g.symm),
    Perm.sumCongr_apply, Sum.map_inr, swap_apply_right]

/-- The involution of the gluing sends `f*` to `ḡ`. -/
theorem leafGluingInv_inl_inv_f :
    leafGluingInv Y f R g (Sum.inl (Y.inv f)) = Sum.inr (R.inv g) := by
  rw [leafGluingInv_apply,
    swap_apply_of_ne_of_ne (x := Sum.inl (Y.inv f)) (by simpa using h.inv_ne_self_left) (by simp),
    Perm.sumCongr_apply, Sum.map_inl, h.inv_inv_left, swap_apply_left]

/-- The involution of the gluing sends `ḡ` to `f*`. -/
theorem leafGluingInv_inr_inv_g :
    leafGluingInv Y f R g (Sum.inr (R.inv g)) = Sum.inl (Y.inv f) := by
  rw [leafGluingInv_apply, swap_apply_right, Perm.sumCongr_apply, Sum.map_inl,
    swap_apply_of_ne_of_ne (x := Sum.inl (Y.inv f)) (by simpa using h.inv_ne_self_left) (by simp)]

/-- Away from `f, f*, g, ḡ`, the involution of the gluing is `ι_Y ⊕ ι_R`. -/
theorem leafGluingInv_of_ne {x : HY ⊕ HR} (h1 : x ≠ Sum.inl f) (h2 : x ≠ Sum.inl (Y.inv f))
    (h3 : x ≠ Sum.inr g) (h4 : x ≠ Sum.inr (R.inv g)) :
    leafGluingInv Y f R g x = Perm.sumCongr Y.inv R.inv x := by
  rw [leafGluingInv_apply, swap_apply_of_ne_of_ne (x := x) h1 h4]
  refine swap_apply_of_ne_of_ne ?_ ?_
  · rcases x with y | r
    · simp only [Perm.sumCongr_apply, Sum.map_inl, ne_eq, Sum.inl.injEq]
      exact fun e => h2 (by rw [← e, h.inv_inv_left])
    · simp
  · rcases x with y | r
    · simp
    · simp only [Perm.sumCongr_apply, Sum.map_inr, ne_eq, Sum.inr.injEq]
      exact fun e => h3 (by rw [R.inv.injective e])

/-- `leafGluingInv Y f R g` is an involution. -/
theorem leafGluingInv_leafGluingInv (x : HY ⊕ HR) :
    leafGluingInv Y f R g (leafGluingInv Y f R g x) = x := by
  rw [leafGluingInv_apply, leafGluingInv_apply, swap_apply_self, h.sumCongr_inv_inv,
    swap_apply_self]

/-- The involution of the gluing maps the complement of the darts of the gluing into itself. -/
theorem leafGluingInv_notMem_of_notMem {x : HY ⊕ HR} (hx : x ∉ leafGluingDarts f R p g) :
    leafGluingInv Y f R g x ∉ leafGluingDarts f R p g := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    not_and_or, not_not] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · simp [h.leafGluingInv_inl_f]
  · rw [h.leafGluingInv_of_ne (by simp) (by simp) (by simpa using h.g_ne_inv_p.symm)
      (by simpa using h.inv_g_ne_inv_p.symm)]
    simp [h.inv_inv_right]
  · rw [h.leafGluingInv_of_ne (by simp) (by simp) (by simpa using h.g_ne_p.symm)
      (by simpa using h.inv_g_ne_p.symm)]
    simp
  · simp [h.leafGluingInv_inr_g]

/-- A dart lies in the gluing iff its image under the involution does. -/
theorem leafGluingInv_mem_iff (x : HY ⊕ HR) :
    leafGluingInv Y f R g x ∈ leafGluingDarts f R p g ↔ x ∈ leafGluingDarts f R p g :=
  ⟨not_imp_not.1 h.leafGluingInv_notMem_of_notMem, fun hx =>
    not_imp_not.1 h.leafGluingInv_notMem_of_notMem (by rwa [h.leafGluingInv_leafGluingInv])⟩

omit [DecidableEq HY] in
/-- Every leg of `Y` is a dart of the gluing. -/
theorem leg_mem (i : Fin b) : Sum.inl (Y.leg i) ∈ leafGluingDarts f R p g := by
  simp [h.leg_ne i]

end IsLeafGluingSite

/-- The gluing `Y⟨f ← R⟩` of `R` into the leaf `{f}` of `Y`. Its darts are
`H' = (H_Y \ {f}) ∪ (H_R \ {p̄, p, g})` (`leafGluingDarts`); the involution `ι'` pairs
`f* = ι_Y f` with `ḡ = ι_R g` and agrees with `ι_Y` and `ι_R` elsewhere; the rotation `σ'` is the
restriction of `σ_Y` and `σ_R`; the boundary is `B_Y`; each dart has its colour in `Y` or in `R`
(which matters only at internal vertices); and the labelling is that of `Y`, recorded by its
legs. -/
@[cluster_algebras "def_leaf_gluing"]
def leafGluing (Y : PlabicData HY b) {f : HY} {R : PlabicData HR c} {p g : HR}
    (h : Y.IsLeafGluingSite f R p g) : PlabicData (leafGluingDarts f R p g) b where
  inv := (leafGluingInv Y f R g).subtypePerm h.leafGluingInv_mem_iff
  rot := (Perm.sumCongr Y.rot R.rot).subtypePerm h.rot_mem_iff
  bdry := (Y.bdry.map Embedding.inl).subtype (· ∈ leafGluingDarts f R p g)
  colour x := Sum.elim Y.colour R.colour x.1
  leg i := ⟨Sum.inl (Y.leg i), h.leg_mem i⟩

/-! ### Basic API of the gluing -/

section API

variable {Y : PlabicData HY b} {f : HY} {R : PlabicData HR c} {p g : HR}
  (h : Y.IsLeafGluingSite f R p g)

/-- The rotation of the gluing is the restriction of `σ_Y ⊕ σ_R`. -/
@[simp]
theorem coe_leafGluing_rot (x : leafGluingDarts f R p g) :
    ((Y.leafGluing h).rot x : HY ⊕ HR) = Perm.sumCongr Y.rot R.rot x :=
  rfl

/-- The involution of the gluing is the restriction of `leafGluingInv Y f R g`. -/
@[simp]
theorem coe_leafGluing_inv (x : leafGluingDarts f R p g) :
    ((Y.leafGluing h).inv x : HY ⊕ HR) = leafGluingInv Y f R g x :=
  rfl

/-- The face permutation of the gluing restricts `(σ_Y ⊕ σ_R) ∘ leafGluingInv Y f R g`. -/
theorem coe_leafGluing_facePerm (x : leafGluingDarts f R p g) :
    ((Y.leafGluing h).facePerm x : HY ⊕ HR) =
      Perm.sumCongr Y.rot R.rot (leafGluingInv Y f R g x) :=
  rfl

/-- A dart of the gluing is a boundary dart iff it is a boundary dart of `Y`. -/
theorem mem_leafGluing_bdry {x : leafGluingDarts f R p g} :
    x ∈ (Y.leafGluing h).bdry ↔ (x : HY ⊕ HR) ∈ Y.bdry.map Embedding.inl :=
  Finset.mem_subtype

/-- The legs of the gluing are those of `Y`. -/
@[simp]
theorem coe_leafGluing_leg (i : Fin b) :
    ((Y.leafGluing h).leg i : HY ⊕ HR) = Sum.inl (Y.leg i) :=
  rfl

/-- Each dart of the gluing has its colour in `Y` or in `R`. -/
theorem leafGluing_colour (x : leafGluingDarts f R p g) :
    (Y.leafGluing h).colour x = Sum.elim Y.colour R.colour x.1 :=
  rfl

end API

namespace IsLeafGluingSite

variable {Y : PlabicData HY b} {f : HY} {R : PlabicData HR c} {p g : HR}
  (h : Y.IsLeafGluingSite f R p g)

include h

omit [DecidableEq HY] in
/-- `f*` is a dart of the gluing. -/
theorem inl_inv_f_mem : Sum.inl (Y.inv f) ∈ leafGluingDarts f R p g := by
  simpa using h.inv_ne_self_left

omit [DecidableEq HY] in
/-- `ḡ` is a dart of the gluing. -/
theorem inr_inv_g_mem : Sum.inr (R.inv g) ∈ leafGluingDarts f R p g := by
  simp [h.inv_g_ne_inv_p, h.inv_g_ne_p, h.inv_g_ne_g]

/-- Away from `f*` and `ḡ`, the face permutation of the gluing is `φ_Y ⊕ φ_R`. -/
theorem coe_leafGluing_facePerm_of_ne {x : leafGluingDarts f R p g}
    (h1 : (x : HY ⊕ HR) ≠ Sum.inl (Y.inv f)) (h2 : (x : HY ⊕ HR) ≠ Sum.inr (R.inv g)) :
    ((Y.leafGluing h).facePerm x : HY ⊕ HR) = Perm.sumCongr Y.facePerm R.facePerm x := by
  obtain ⟨hx1, -, -, hx4⟩ := ne_of_mem_leafGluingDarts x.2
  rw [coe_leafGluing_facePerm, h.leafGluingInv_of_ne hx1 h1 hx4 h2]
  rcases (x : HY ⊕ HR) with y | r <;> rfl

/-- Away from `f*` and `ḡ`, the involution of the gluing is `ι_Y ⊕ ι_R`. -/
theorem coe_leafGluing_inv_of_ne {x : leafGluingDarts f R p g}
    (h1 : (x : HY ⊕ HR) ≠ Sum.inl (Y.inv f)) (h2 : (x : HY ⊕ HR) ≠ Sum.inr (R.inv g)) :
    ((Y.leafGluing h).inv x : HY ⊕ HR) = Perm.sumCongr Y.inv R.inv x := by
  obtain ⟨hx1, -, -, hx4⟩ := ne_of_mem_leafGluingDarts x.2
  rw [coe_leafGluing_inv, h.leafGluingInv_of_ne hx1 h1 hx4 h2]

/-! ### Counting orbits -/

omit [DecidableEq HY] in
/-- If `Ψ` runs `f* ↦ f` and `ḡ ↦ p̄ ↦ p ↦ g`, every orbit of `Ψ` meets the darts of the
gluing. -/
theorem exists_sameCycle_mem_leafGluingDarts {Ψ : Perm (HY ⊕ HR)}
    (e1 : Ψ (Sum.inl (Y.inv f)) = Sum.inl f) (e3 : Ψ (Sum.inr (R.inv g)) = Sum.inr (R.inv p))
    (e4 : Ψ (Sum.inr (R.inv p)) = Sum.inr p) (e5 : Ψ (Sum.inr p) = Sum.inr g) (x : HY ⊕ HR) :
    ∃ y ∈ leafGluingDarts f R p g, Ψ.SameCycle x y := by
  by_cases hx : x ∈ leafGluingDarts f R p g
  · exact ⟨x, hx, SameCycle.refl _ _⟩
  have hx' : x = Sum.inl f ∨ x = Sum.inr (R.inv p) ∨ x = Sum.inr p ∨ x = Sum.inr g := by
    simpa only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_not] using hx
  have s1 : Ψ.SameCycle (Sum.inr (R.inv g)) (Ψ (Sum.inr (R.inv g))) :=
    sameCycle_apply_right.2 (SameCycle.refl _ _)
  have s2 : Ψ.SameCycle (Sum.inr (R.inv g)) (Ψ (Ψ (Sum.inr (R.inv g)))) :=
    sameCycle_apply_right.2 s1
  have s3 : Ψ.SameCycle (Sum.inr (R.inv g)) (Ψ (Ψ (Ψ (Sum.inr (R.inv g))))) :=
    sameCycle_apply_right.2 s2
  rw [e3] at s1 s2 s3
  rw [e4] at s2 s3
  rw [e5] at s3
  rcases hx' with rfl | rfl | rfl | rfl
  · refine ⟨_, h.inl_inv_f_mem, ?_⟩
    have := (sameCycle_apply_right (f := Ψ)).2 (SameCycle.refl Ψ (Sum.inl (Y.inv f)))
    rw [e1] at this
    exact this.symm
  · exact ⟨_, h.inr_inv_g_mem, s1.symm⟩
  · exact ⟨_, h.inr_inv_g_mem, s2.symm⟩
  · exact ⟨_, h.inr_inv_g_mem, s3.symm⟩

omit [DecidableEq HY] in
/-- A permutation `π` of the darts of the gluing is the first-return map of `Ψ` once `Ψ` agrees
with `π` away from `f*` and `ḡ`, and runs `f* ↦ f ↦ π f*` and `ḡ ↦ p̄ ↦ p ↦ g ↦ π ḡ`. -/
theorem eq_firstReturnPerm_of_chain [Finite HY] [Finite HR] (π : Perm (leafGluingDarts f R p g))
    {Ψ : Perm (HY ⊕ HR)}
    (hΨ : ∀ v (hv : v ∈ leafGluingDarts f R p g), v ≠ Sum.inl (Y.inv f) →
      v ≠ Sum.inr (R.inv g) → Ψ v = π ⟨v, hv⟩)
    (e1 : Ψ (Sum.inl (Y.inv f)) = Sum.inl f) (e2 : Ψ (Sum.inl f) = π ⟨_, h.inl_inv_f_mem⟩)
    (e3 : Ψ (Sum.inr (R.inv g)) = Sum.inr (R.inv p)) (e4 : Ψ (Sum.inr (R.inv p)) = Sum.inr p)
    (e5 : Ψ (Sum.inr p) = Sum.inr g) (e6 : Ψ (Sum.inr g) = π ⟨_, h.inr_inv_g_mem⟩) :
    π = firstReturnPerm Ψ (leafGluingDarts f R p g) := by
  ext ⟨v, hv⟩
  rw [coe_firstReturnPerm]
  by_cases hv1 : v = Sum.inl (Y.inv f)
  · subst hv1
    rw [coe_firstReturn_of_pow (m := 2) two_pos]
    · simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, e1, e2]
    · simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, e1, e2]
      exact Subtype.property _
    · intro j hj hj2
      obtain rfl : j = 1 := by omega
      simp [e1]
  by_cases hv2 : v = Sum.inr (R.inv g)
  · subst hv2
    rw [coe_firstReturn_of_pow (m := 4) (by norm_num)]
    · simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, e3, e4, e5, e6]
    · simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, e3, e4, e5, e6]
      exact Subtype.property _
    · intro j hj hj4
      obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
      all_goals simp [pow_succ, Perm.mul_apply, e3, e4, e5]
  · have hmem : Ψ v ∈ leafGluingDarts f R p g := by
      rw [hΨ v hv hv1 hv2]
      exact Subtype.property _
    rw [coe_firstReturn_of_apply_mem hmem, hΨ v hv hv1 hv2]

omit [DecidableEq HY] in
/-- The orbit of `σ_R` through `p̄`, `p` or `g` is `{p̄, p, g}`. -/
theorem mem_triple_of_sameCycle [Finite HR] {z r : HR} (hz : z = R.inv p ∨ z = p ∨ z = g)
    (hs : R.rot.SameCycle z r) : r = R.inv p ∨ r = p ∨ r = g := by
  have hT : ∀ y ∈ ({R.inv p, p, g} : Set HR), R.rot y ∈ ({R.inv p, p, g} : Set HR) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rcases hy with rfl | rfl | rfl
    · simp [h.rot_inv_right]
    · simp [h.rot_right]
    · simp [h.rot_rot_right]
  simpa using mem_of_sameCycle_of_forall_mem hT (by simpa using hz) hs

variable [Fintype HY] [Fintype HR]

omit [Fintype HY] [Fintype HR] in
/-- If `Φ * swap a b * swap c d` merges two pairs of cycles of `Φ` and runs `f* ↦ f` and
`ḡ ↦ p̄ ↦ p ↦ g`, its first return to the darts of the gluing has two orbits fewer than `Φ`. -/
theorem numOrbits_firstReturnPerm_add_two [Finite HY] [Finite HR] {Φ : Perm (HY ⊕ HR)}
    {a b c d : HY ⊕ HR}
    (hab : ¬Φ.SameCycle a b) (hcd : ¬(Φ * swap a b).SameCycle c d)
    (e1 : (Φ * swap a b * swap c d) (Sum.inl (Y.inv f)) = Sum.inl f)
    (e3 : (Φ * swap a b * swap c d) (Sum.inr (R.inv g)) = Sum.inr (R.inv p))
    (e4 : (Φ * swap a b * swap c d) (Sum.inr (R.inv p)) = Sum.inr p)
    (e5 : (Φ * swap a b * swap c d) (Sum.inr p) = Sum.inr g) :
    numOrbits (firstReturnPerm (Φ * swap a b * swap c d) (leafGluingDarts f R p g)) + 2 =
      numOrbits Φ := by
  rw [numOrbits_firstReturnPerm _ _ (h.exists_sameCycle_mem_leafGluingDarts e1 e3 e4 e5),
    numOrbits_eq_numOrbits_mul_swap_mul_swap_add_two hab hcd]

/-- The face permutation `φ' = σ' ∘ ι'` of the gluing has as many orbits as `φ_Y` and `φ_R`
together, minus two. -/
@[cluster_algebras "lem_leaf_gluing_faces"]
theorem card_faceOrbits_leafGluing :
    (Y.leafGluing h).faceOrbits.card + 2 = Y.faceOrbits.card + R.faceOrbits.card := by
  set D := leafGluingDarts f R p g
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = Perm.sumCongr Y.facePerm R.facePerm := ⟨_, rfl⟩
  have hΦl : ∀ y, Φ (Sum.inl y) = Sum.inl (Y.rot (Y.inv y)) := fun y => by rw [hΦ]; rfl
  have hΦr : ∀ r, Φ (Sum.inr r) = Sum.inr (R.rot (R.inv r)) := fun r => by rw [hΦ]; rfl
  set Ψ₁ := Φ * Equiv.swap (Sum.inl f) (Sum.inr g) with hΨ₁
  set Ψ := Ψ₁ * Equiv.swap (Sum.inr p) (Sum.inr (R.inv p)) with hΨ
  have hΨapp : ∀ x, Ψ x =
      Φ (Equiv.swap (Sum.inl f) (Sum.inr g) (Equiv.swap (Sum.inr p) (Sum.inr (R.inv p)) x)) :=
    fun x => rfl
  have hΨD : ∀ x ∈ D, Ψ x = Φ x := fun x hx => by
    obtain ⟨h1, h2, h3, h4⟩ := ne_of_mem_leafGluingDarts hx
    rw [hΨapp, swap_apply_of_ne_of_ne h3 h2, swap_apply_of_ne_of_ne h1 h4]
  have e1 : Ψ (Sum.inl (Y.inv f)) = Sum.inl f := by
    rw [hΨD _ h.inl_inv_f_mem, hΦl, h.inv_inv_left, h.rot_left]
  have e3 : Ψ (Sum.inr (R.inv g)) = Sum.inr (R.inv p) := by
    rw [hΨD _ h.inr_inv_g_mem, hΦr, h.inv_inv_right, h.rot_rot_right]
  have e4 : Ψ (Sum.inr (R.inv p)) = Sum.inr p := by
    rw [hΨapp, swap_apply_right, swap_apply_of_ne_of_ne (a := Sum.inl f) (b := Sum.inr g)
      (x := Sum.inr p) (by simp) (by simpa using h.g_ne_p.symm), hΦr, h.rot_inv_right]
  have e5 : Ψ (Sum.inr p) = Sum.inr g := by
    rw [hΨapp, swap_apply_left, swap_apply_of_ne_of_ne (a := Sum.inl f) (b := Sum.inr g)
      (x := Sum.inr (R.inv p)) (by simp) (by simpa using h.g_ne_inv_p.symm), hΦr,
      h.inv_inv_right, h.rot_right]
  have hfp : (Y.leafGluing h).facePerm = firstReturnPerm Ψ D := by
    refine h.eq_firstReturnPerm_of_chain _ (fun v hv hv1 hv2 => ?_) e1 ?_ e3 e4 e5 ?_
    · rw [hΨD v hv, h.coe_leafGluing_facePerm_of_ne (x := ⟨v, hv⟩) hv1 hv2, hΦ]
    · rw [hΨapp, swap_apply_of_ne_of_ne (a := Sum.inr p) (b := Sum.inr (R.inv p))
        (x := Sum.inl f) (by simp) (by simp), swap_apply_left, hΦr, coe_leafGluing_facePerm,
        h.leafGluingInv_inl_inv_f]
      rfl
    · rw [hΨapp, swap_apply_of_ne_of_ne (a := Sum.inr p) (b := Sum.inr (R.inv p))
        (x := Sum.inr g) (by simpa using h.g_ne_p) (by simpa using h.g_ne_inv_p),
        swap_apply_right, hΦl, coe_leafGluing_facePerm, h.leafGluingInv_inr_inv_g]
      rfl
  have hn₁ : ¬Φ.SameCycle (Sum.inl f) (Sum.inr g) := hΦ ▸ not_sameCycle_sumCongr_inl_inr
  have hfix : Ψ₁ (Sum.inr p) = Sum.inr p := by
    rw [hΨ₁, Perm.mul_apply, swap_apply_of_ne_of_ne (by simp)
      (by simpa using h.g_ne_p.symm), hΦr, h.rot_inv_right]
  have hn₂ : ¬Ψ₁.SameCycle (Sum.inr p) (Sum.inr (R.inv p)) := fun hs =>
    h.p_ne_inv_p (Sum.inr_injective (hs.eq_of_left hfix))
  simp only [RotationSystem.card_faceOrbits_eq_numOrbits]
  change numOrbits (Y.leafGluing h).facePerm + 2 = numOrbits Y.facePerm + numOrbits R.facePerm
  rw [hfp, ← numOrbits_sumCongr, ← hΦ]
  exact h.numOrbits_firstReturnPerm_add_two hn₁ hn₂ e1 e3 e4 e5

/-- The vertices of the gluing are those of `Y` other than `{f}` and those of `R` other than
`{p̄, p, g}`: their number is that of `Y` and `R` together, minus two. -/
theorem card_vertices_leafGluing :
    (Y.leafGluing h).vertices.card + 2 = Y.vertices.card + R.vertices.card := by
  set D := leafGluingDarts f R p g
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = Perm.sumCongr Y.rot R.rot := ⟨_, rfl⟩
  have hSl : ∀ y, S₀ (Sum.inl y) = Sum.inl (Y.rot y) := fun y => by rw [hS₀]; rfl
  have hSr : ∀ r, S₀ (Sum.inr r) = Sum.inr (R.rot r) := fun r => by rw [hS₀]; rfl
  set S₁ := S₀ * Equiv.swap (Sum.inl f) (Sum.inl (Y.inv f)) with hS₁
  set S₂ := S₁ * Equiv.swap (Sum.inr g) (Sum.inr (R.inv g)) with hS₂
  have hSapp : ∀ x, S₂ x = S₀ (Equiv.swap (Sum.inl f) (Sum.inl (Y.inv f))
      (Equiv.swap (Sum.inr g) (Sum.inr (R.inv g)) x)) := fun x => rfl
  have a1 : S₂ (Sum.inl (Y.inv f)) = Sum.inl f := by
    rw [hSapp, swap_apply_of_ne_of_ne (a := Sum.inr g) (b := Sum.inr (R.inv g))
      (x := Sum.inl (Y.inv f)) (by simp) (by simp), swap_apply_right, hSl, h.rot_left]
  have a3 : S₂ (Sum.inr (R.inv g)) = Sum.inr (R.inv p) := by
    rw [hSapp, swap_apply_right, swap_apply_of_ne_of_ne (a := Sum.inl f)
      (b := Sum.inl (Y.inv f)) (x := Sum.inr g) (by simp) (by simp), hSr, h.rot_rot_right]
  have a4 : S₂ (Sum.inr (R.inv p)) = Sum.inr p := by
    rw [hSapp, swap_apply_of_ne_of_ne (a := Sum.inr g) (b := Sum.inr (R.inv g))
      (x := Sum.inr (R.inv p)) (by simpa using h.g_ne_inv_p.symm)
      (by simpa using h.inv_g_ne_inv_p.symm), swap_apply_of_ne_of_ne (by simp) (by simp), hSr,
      h.rot_inv_right]
  have a5 : S₂ (Sum.inr p) = Sum.inr g := by
    rw [hSapp, swap_apply_of_ne_of_ne (a := Sum.inr g) (b := Sum.inr (R.inv g))
      (x := Sum.inr p) (by simpa using h.g_ne_p.symm) (by simpa using h.inv_g_ne_p.symm),
      swap_apply_of_ne_of_ne (by simp) (by simp), hSr, h.rot_right]
  have hrot : (Y.leafGluing h).rot = firstReturnPerm S₂ D := by
    refine h.eq_firstReturnPerm_of_chain _ (fun v hv hv1 hv2 => ?_) a1 ?_ a3 a4 a5 ?_
    · obtain ⟨h1, -, -, h3⟩ := ne_of_mem_leafGluingDarts hv
      rw [hSapp, swap_apply_of_ne_of_ne h3 hv2, swap_apply_of_ne_of_ne h1 hv1, hS₀]
      rfl
    · rw [hSapp, swap_apply_of_ne_of_ne (a := Sum.inr g) (b := Sum.inr (R.inv g))
        (x := Sum.inl f) (by simp) (by simp), swap_apply_left, hSl]
      rfl
    · rw [hSapp, swap_apply_left, swap_apply_of_ne_of_ne (a := Sum.inl f)
        (b := Sum.inl (Y.inv f)) (x := Sum.inr (R.inv g)) (by simp) (by simp), hSr]
      rfl
  have hn₁ : ¬S₀.SameCycle (Sum.inl f) (Sum.inl (Y.inv f)) := fun hs =>
    h.inv_ne_self_left (Sum.inl_injective
      (hs.eq_of_left (show S₀ (Sum.inl f) = Sum.inl f by rw [hSl, h.rot_left]))).symm
  have hn₂ : ¬S₁.SameCycle (Sum.inr g) (Sum.inr (R.inv g)) := by
    rw [hS₁, sameCycle_mul_swap_iff S₀ hn₁, hS₀]
    simp only [sameCycle_sumCongr_inr_inr, not_sameCycle_sumCongr_inr_inl, false_and, or_false]
    exact fun hs => (h.mem_triple_of_sameCycle (by simp) hs).elim h.inv_g_ne_inv_p
      fun e => e.elim h.inv_g_ne_p h.inv_g_ne_g
  simp only [RotationSystem.card_vertices_eq_numOrbits]
  change numOrbits (Y.leafGluing h).rot + 2 = numOrbits Y.rot + numOrbits R.rot
  rw [hrot, ← numOrbits_sumCongr, ← hS₀]
  exact h.numOrbits_firstReturnPerm_add_two hn₁ hn₂ a1 a3 a4 a5

omit [Fintype HY] [Fintype HR] in
/-- The involution of the gluing is an involution. -/
theorem leafGluing_inv_involutive : Involutive (Y.leafGluing h).inv := fun x =>
  Subtype.ext (h.leafGluingInv_leafGluingInv x)

omit [Fintype HY] [Fintype HR] in
/-- The involution of the gluing has no fixed point. -/
theorem leafGluing_inv_ne (x : leafGluingDarts f R p g) : (Y.leafGluing h).inv x ≠ x := by
  intro hx
  have hx' := congrArg Subtype.val hx
  obtain ⟨v, hv⟩ := x
  simp only [coe_leafGluing_inv] at hx'
  by_cases hv1 : v = Sum.inl (Y.inv f)
  · subst hv1
    simp [h.leafGluingInv_inl_inv_f] at hx'
  by_cases hv2 : v = Sum.inr (R.inv g)
  · subst hv2
    simp [h.leafGluingInv_inr_inv_g] at hx'
  obtain ⟨h1, -, -, h3⟩ := ne_of_mem_leafGluingDarts hv
  rw [h.leafGluingInv_of_ne h1 hv1 h3 hv2] at hx'
  rcases v with y | r
  · exact h.inv_ne_left y (Sum.inl_injective hx')
  · exact h.inv_ne_right r (Sum.inr_injective hx')

/-- The gluing has four darts fewer than `Y` and `R` together. -/
theorem card_leafGluingDarts :
    Fintype.card (leafGluingDarts f R p g) + 4 = Fintype.card HY + Fintype.card HR := by
  rw [Fintype.card_subtype, ← Fintype.card_sum]
  have hT : (univ.filter (· ∈ leafGluingDarts f R p g)) =
      univ \ {Sum.inl f, Sum.inr (R.inv p), Sum.inr p, Sum.inr g} := by
    ext x
    simp
  rw [hT, card_sdiff_of_subset (subset_univ _), card_univ]
  have h4 : ({Sum.inl f, Sum.inr (R.inv p), Sum.inr p, Sum.inr g} : Finset (HY ⊕ HR)).card = 4 := by
    rw [card_insert_of_notMem (by simp), card_insert_of_notMem
      (by simp [h.p_ne_inv_p.symm, h.g_ne_inv_p.symm]), card_pair (by simpa using h.g_ne_p.symm)]
  have : 4 ≤ Fintype.card (HY ⊕ HR) := h4 ▸ card_le_univ _
  omega

/-- The edges of the gluing are those of `Y` other than `{f, f*}`, those of `R` other than
`{p, p̄}` and `{g, ḡ}`, and `{f*, ḡ}`: their number is that of `Y` and `R` together, minus two. -/
theorem card_edges_leafGluing :
    (Y.leafGluing h).edges.card + 2 = Y.edges.card + R.edges.card := by
  have h1 := (Y.leafGluing h).two_mul_card_edges h.leafGluing_inv_involutive h.leafGluing_inv_ne
  have h2 := Y.two_mul_card_edges h.inv_involutive_left h.inv_ne_left
  have h3 := R.two_mul_card_edges h.inv_involutive_right h.inv_ne_right
  have h4 := h.card_leafGluingDarts
  omega

/-! ### The gluing of plabic graphs -/

omit [Fintype HY] [Fintype HR] in
/-- Two darts of the gluing lie in one orbit of its rotation iff they lie in one orbit of
`σ_Y ⊕ σ_R`. -/
theorem sameCycle_leafGluing_rot_iff {x z : leafGluingDarts f R p g} :
    (Y.leafGluing h).rot.SameCycle x z ↔ (Perm.sumCongr Y.rot R.rot).SameCycle x z :=
  sameCycle_subtypePerm (h := h.rot_mem_iff)

/-- For darts `a`, `e` of `Y` in the gluing, `e` lies at the vertex of `a` in the gluing
iff it does in `Y`. -/
theorem mem_leafGluing_vertexOf_iff_of_inl {x z : leafGluingDarts f R p g} {a e : HY}
    (hx : (x : HY ⊕ HR) = Sum.inl a) (hz : (z : HY ⊕ HR) = Sum.inl e) :
    z ∈ (Y.leafGluing h).vertexOf x ↔ e ∈ Y.vertexOf a := by
  rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf,
    h.sameCycle_leafGluing_rot_iff, hx, hz, sameCycle_sumCongr_inl_inl]

/-- No dart of `R` lies at the vertex of a dart of `Y` in the gluing. -/
theorem notMem_leafGluing_vertexOf_of_inr {x z : leafGluingDarts f R p g} {a : HY} {r : HR}
    (hx : (x : HY ⊕ HR) = Sum.inl a) (hz : (z : HY ⊕ HR) = Sum.inr r) :
    z ∉ (Y.leafGluing h).vertexOf x := by
  rw [RotationSystem.mem_vertexOf, h.sameCycle_leafGluing_rot_iff, hx, hz]
  exact not_sameCycle_sumCongr_inl_inr

omit [Fintype HR] in
/-- A dart of `Y` at the vertex of a dart of the gluing is a dart of the gluing. -/
theorem inl_mem_of_mem_vertexOf {a e : HY} (ha : Sum.inl a ∈ leafGluingDarts f R p g)
    (he : e ∈ Y.vertexOf a) : Sum.inl e ∈ leafGluingDarts f R p g := by
  have haf : a ≠ f := by simpa using ha
  have hef : e ≠ f := by
    rintro rfl
    exact haf (((RotationSystem.mem_vertexOf _).1 he).symm.eq_of_left h.rot_left).symm
  simpa using hef

omit [Fintype HY] [Fintype HR] in
/-- A dart of the gluing is a boundary dart iff it is a boundary dart of `Y`. -/
theorem mem_leafGluing_bdry_iff {x : leafGluingDarts f R p g} :
    x ∈ (Y.leafGluing h).bdry ↔ ∃ a ∈ Y.bdry, (x : HY ⊕ HR) = Sum.inl a := by
  rw [mem_leafGluing_bdry, Finset.mem_map]
  simp only [Embedding.inl_apply]
  exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩

omit [Fintype HY] [Fintype HR] [DecidableEq HY] in
/-- Every boundary dart of `Y` is a dart of the gluing. -/
theorem inl_mem_of_mem_bdry {a : HY} (ha : a ∈ Y.bdry) :
    Sum.inl a ∈ leafGluingDarts f R p g := by
  simpa using fun e : a = f => h.notMem_bdry_left (e ▸ ha)

/-- A vertex of the gluing is a boundary vertex iff it is that of a boundary vertex of `Y`. -/
theorem isBoundaryVertex_leafGluing_vertexOf_iff {x : leafGluingDarts f R p g} :
    (Y.leafGluing h).IsBoundaryVertex ((Y.leafGluing h).vertexOf x) ↔
      ∃ a, (x : HY ⊕ HR) = Sum.inl a ∧ Y.IsBoundaryVertex (Y.vertexOf a) := by
  constructor
  · rintro ⟨z, hz, hzB⟩
    obtain ⟨e, heB, hze⟩ := h.mem_leafGluing_bdry_iff.1 hzB
    obtain ⟨v, hv⟩ := x
    rcases v with a | r
    · refine ⟨a, rfl, e, ?_, heB⟩
      exact (h.mem_leafGluing_vertexOf_iff_of_inl (x := ⟨_, hv⟩) rfl hze).1 hz
    · exfalso
      rw [RotationSystem.mem_vertexOf, h.sameCycle_leafGluing_rot_iff, hze] at hz
      exact not_sameCycle_sumCongr_inr_inl hz
  · rintro ⟨a, hxa, e, he, heB⟩
    have hmem : Sum.inl e ∈ leafGluingDarts f R p g :=
      h.inl_mem_of_mem_vertexOf (hxa ▸ x.2) he
    refine ⟨⟨_, hmem⟩, (h.mem_leafGluing_vertexOf_iff_of_inl hxa rfl).2 he, ?_⟩
    exact h.mem_leafGluing_bdry_iff.2 ⟨e, heB, rfl⟩

variable (hY : Y.IsPlabicGraph)

include hY

omit [Fintype HR] in
/-- For a plabic graph `Y`, `f* ∉ B_Y`. -/
theorem inv_f_notMem_bdry : Y.inv f ∉ Y.bdry := fun hb =>
  h.notMem_bdry_left (by simpa [h.inv_inv_left] using hY.inv_mem_bdry _ hb)

omit [Fintype HR] in
/-- On the darts of `B_Y`, the involution of the gluing is that of `Y`. -/
theorem coe_leafGluing_inv_of_mem_bdry {x : leafGluingDarts f R p g} {a : HY}
    (hxa : (x : HY ⊕ HR) = Sum.inl a) (ha : a ∈ Y.bdry) :
    ((Y.leafGluing h).inv x : HY ⊕ HR) = Sum.inl (Y.inv a) := by
  have h1 : (x : HY ⊕ HR) ≠ Sum.inl (Y.inv f) := by
    rw [hxa]
    intro e
    exact h.inv_f_notMem_bdry hY (Sum.inl_injective e ▸ ha)
  rw [h.coe_leafGluing_inv_of_ne h1 (by simp [hxa]), hxa]
  rfl

omit [Fintype HR] in
/-- On the darts of `B_Y`, the face permutation of the gluing is that of `Y`. -/
theorem coe_leafGluing_facePerm_of_mem_bdry {x : leafGluingDarts f R p g} {a : HY}
    (hxa : (x : HY ⊕ HR) = Sum.inl a) (ha : a ∈ Y.bdry) :
    ((Y.leafGluing h).facePerm x : HY ⊕ HR) = Sum.inl (Y.facePerm a) := by
  rw [RotationSystem.facePerm_apply, coe_leafGluing_rot, h.coe_leafGluing_inv_of_mem_bdry hY hxa ha]
  rfl

omit [Fintype HY] [Fintype HR] hY in
/-- The exterior of the gluing is that of `Y`. -/
theorem mem_leafGluing_exterior_iff {x : leafGluingDarts f R p g} :
    x ∈ (Y.leafGluing h).exterior ↔ ∃ a, (x : HY ⊕ HR) = Sum.inl a ∧ a ∈ Y.exterior := by
  rw [DiskMap.mem_exterior, h.mem_leafGluing_bdry_iff, h.mem_leafGluing_bdry_iff]
  obtain ⟨v, hv⟩ := x
  rcases v with a | r
  · simp only [coe_leafGluing_rot, Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq,
      exists_eq_right', DiskMap.mem_exterior]
    exact ⟨fun ⟨h1, h2⟩ => ⟨a, rfl, h1, h2⟩, fun ⟨a', e, h1, h2⟩ => e ▸ ⟨h1, h2⟩⟩
  · simp

omit [Fintype HR] in
/-- Every dart of `Y` in the gluing is reachable from `f*`. -/
theorem reach_inl_leafGluing {y : HY} (hy : Sum.inl y ∈ leafGluingDarts f R p g) :
    (Y.leafGluing h).Reach ⟨Sum.inl (Y.inv f), h.inl_inv_f_mem⟩ ⟨_, hy⟩ := by
  set G := Y.leafGluing h
  revert hy
  induction hY.toIsDiskMap.toIsConnected.reach (Y.inv f) y with
  | refl => exact fun _ => RotationSystem.Reach.refl _
  | @rot e _ ih =>
    intro hy
    have he : Sum.inl e ∈ leafGluingDarts f R p g := (h.rot_mem_iff (Sum.inl e)).1 hy
    have hrot : G.rot ⟨_, he⟩ = ⟨_, hy⟩ := Subtype.ext rfl
    rw [← hrot]
    exact (ih he).rot
  | @inv e _ ih =>
    intro hy
    by_cases hef : e = f
    · subst hef
      exact RotationSystem.Reach.refl _
    have he : Sum.inl e ∈ leafGluingDarts f R p g := by simpa using hef
    have hef' : e ≠ Y.inv f := by
      rintro rfl
      simp [h.inv_inv_left] at hy
    have hinv : G.inv ⟨_, he⟩ = ⟨_, hy⟩ :=
      Subtype.ext ((h.coe_leafGluing_inv_of_ne (x := ⟨_, he⟩) (by simpa using hef')
        (by simp)).trans rfl)
    rw [← hinv]
    exact (ih he).inv

omit [Fintype HY] hY in
/-- Every dart of `R` in the gluing is reachable from `f*`. -/
theorem reach_inr_leafGluing (hR : R.toDiskMap.IsDiskMap) {r : HR}
    (hr : Sum.inr r ∈ leafGluingDarts f R p g) :
    (Y.leafGluing h).Reach ⟨Sum.inl (Y.inv f), h.inl_inv_f_mem⟩ ⟨_, hr⟩ := by
  set G := Y.leafGluing h
  have hbase : G.Reach ⟨Sum.inl (Y.inv f), h.inl_inv_f_mem⟩ ⟨_, h.inr_inv_g_mem⟩ := by
    have hinv : G.inv ⟨Sum.inl (Y.inv f), h.inl_inv_f_mem⟩ = ⟨_, h.inr_inv_g_mem⟩ :=
      Subtype.ext h.leafGluingInv_inl_inv_f
    rw [← hinv]
    exact (RotationSystem.Reach.refl _).inv
  revert hr
  induction hR.toIsConnected.reach (R.inv g) r with
  | refl => exact fun _ => hbase
  | @rot e _ ih =>
    intro hr
    have he : Sum.inr e ∈ leafGluingDarts f R p g := (h.rot_mem_iff (Sum.inr e)).1 hr
    have hrot : G.rot ⟨_, he⟩ = ⟨_, hr⟩ := Subtype.ext rfl
    rw [← hrot]
    exact (ih he).rot
  | @inv e _ ih =>
    intro hr
    by_cases he : Sum.inr e ∈ leafGluingDarts f R p g
    · have heg : e ≠ R.inv g := by
        rintro rfl
        simp [h.inv_inv_right] at hr
      have hinv : G.inv ⟨_, he⟩ = ⟨_, hr⟩ :=
        Subtype.ext ((h.coe_leafGluing_inv_of_ne (x := ⟨_, he⟩) (by simp)
          (by simpa using heg)).trans rfl)
      rw [← hinv]
      exact (ih he).inv
    · have he' : e = R.inv p ∨ e = p ∨ e = g := by
        simpa only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, reduceCtorEq, Sum.inr.injEq, false_or, not_not] using he
      rcases he' with rfl | rfl | rfl
      · simp [h.inv_inv_right] at hr
      · simp at hr
      · exact hbase

/-- The gluing of plabic graphs is a connected rotation system. -/
theorem isConnected_leafGluing (hR : R.toDiskMap.IsDiskMap) :
    (Y.leafGluing h).IsConnected := by
  have hreach : ∀ x, (Y.leafGluing h).Reach ⟨Sum.inl (Y.inv f), h.inl_inv_f_mem⟩ x := by
    rintro ⟨y | r, hv⟩
    exacts [h.reach_inl_leafGluing hY hv, h.reach_inr_leafGluing hR hv]
  exact RotationSystem.IsConnected.of_reach ⟨⟨_, h.inl_inv_f_mem⟩⟩ h.leafGluing_inv_involutive
    h.leafGluing_inv_ne fun d e => (hreach d).symm.trans (hreach e)

omit [Fintype HR] in
/-- The boundary of the gluing is closed under the involution. -/
theorem inv_mem_leafGluing_bdry {x : leafGluingDarts f R p g}
    (hx : x ∈ (Y.leafGluing h).bdry) : (Y.leafGluing h).inv x ∈ (Y.leafGluing h).bdry := by
  obtain ⟨a, ha, hxa⟩ := h.mem_leafGluing_bdry_iff.1 hx
  exact h.mem_leafGluing_bdry_iff.2 ⟨_, hY.inv_mem_bdry _ ha,
    h.coe_leafGluing_inv_of_mem_bdry hY hxa ha⟩

/-- The orbit of `φ` in the gluing through an exterior dart of `Y` is the exterior of the
gluing. -/
theorem faceOf_leafGluing_of_mem_exterior {z₀ : HY} (hz₀ : z₀ ∈ Y.exterior) :
    (Y.leafGluing h).faceOf ⟨_, h.inl_mem_of_mem_bdry (Y.exterior_subset_bdry hz₀)⟩ =
      (Y.leafGluing h).exterior := by
  set G := Y.leafGluing h
  have hYext : Y.faceOf z₀ = Y.exterior := by
    obtain ⟨w, hw⟩ := Y.mem_faceOrbits.1 hY.toIsDiskMap.exterior_mem_faceOrbits
    rw [← hw] at hz₀ ⊢
    exact Y.faceOf_eq_of_mem hz₀
  set x₀ : leafGluingDarts f R p g := ⟨_, h.inl_mem_of_mem_bdry (Y.exterior_subset_bdry hz₀)⟩
  have hext : ∀ n : ℕ, (Y.facePerm ^ n) z₀ ∈ Y.exterior := fun n => by
    rw [← hYext, RotationSystem.mem_faceOf]
    exact sameCycle_pow_apply_self _ _ _
  have hpow : ∀ n : ℕ, ((G.facePerm ^ n) x₀ : HY ⊕ HR) = Sum.inl ((Y.facePerm ^ n) z₀) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply,
        h.coe_leafGluing_facePerm_of_mem_bdry hY ih (Y.exterior_subset_bdry (hext n)), pow_succ',
        Perm.mul_apply]
  ext x
  rw [RotationSystem.mem_faceOf, h.mem_leafGluing_exterior_iff]
  constructor
  · intro hs
    obtain ⟨n, rfl⟩ := hs.exists_nat_pow_eq
    exact ⟨_, hpow n, hext n⟩
  · rintro ⟨a, hxa, ha⟩
    rw [← hYext, RotationSystem.mem_faceOf] at ha
    obtain ⟨n, hn⟩ := ha.exists_nat_pow_eq
    exact ⟨n, Subtype.ext (by rw [zpow_natCast, hpow n, hn, hxa])⟩

/-- Every boundary vertex of the gluing has three darts, two of them in the boundary. -/
theorem boundaryVertex_card_leafGluing {v : Finset (leafGluingDarts f R p g)}
    (hv : v ∈ (Y.leafGluing h).boundaryVertices) :
    v.card = 3 ∧ (v.filter (· ∈ (Y.leafGluing h).bdry)).card = 2 := by
  set G := Y.leafGluing h
  obtain ⟨hvV, hb⟩ := G.mem_boundaryVertices.1 hv
  obtain ⟨x, rfl⟩ := G.mem_vertices.1 hvV
  obtain ⟨a, hxa, hYb⟩ := (h.isBoundaryVertex_leafGluing_vertexOf_iff).1 hb
  obtain ⟨h3, h2⟩ :=
    hY.boundaryVertex_card _ (Y.mem_boundaryVertices.2 ⟨Y.vertexOf_mem_vertices a, hYb⟩)
  have hmap : (G.vertexOf x).map (Embedding.subtype _) = (Y.vertexOf a).map Embedding.inl := by
    ext w
    simp only [Finset.mem_map, Embedding.coe_subtype, Embedding.inl_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, hu⟩ := z
      rcases u with e | r
      · exact ⟨e, (h.mem_leafGluing_vertexOf_iff_of_inl hxa rfl).1 hz, rfl⟩
      · exact absurd hz (h.notMem_leafGluing_vertexOf_of_inr hxa rfl)
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨_, h.inl_mem_of_mem_vertexOf (hxa ▸ x.2) he⟩,
        (h.mem_leafGluing_vertexOf_iff_of_inl hxa rfl).2 he, rfl⟩
  have hmapB : ((G.vertexOf x).filter (· ∈ G.bdry)).map (Embedding.subtype _) =
      ((Y.vertexOf a).filter (· ∈ Y.bdry)).map Embedding.inl := by
    ext w
    simp only [Finset.mem_map, Finset.mem_filter, Embedding.coe_subtype, Embedding.inl_apply]
    constructor
    · rintro ⟨z, ⟨hz, hzB⟩, rfl⟩
      obtain ⟨e, heB, hze⟩ := h.mem_leafGluing_bdry_iff.1 hzB
      exact ⟨e, ⟨(h.mem_leafGluing_vertexOf_iff_of_inl hxa hze).1 hz, heB⟩, hze.symm⟩
    · rintro ⟨e, ⟨he, heB⟩, rfl⟩
      exact ⟨⟨_, h.inl_mem_of_mem_vertexOf (hxa ▸ x.2) he⟩,
        ⟨(h.mem_leafGluing_vertexOf_iff_of_inl hxa rfl).2 he,
          h.mem_leafGluing_bdry_iff.2 ⟨e, heB, rfl⟩⟩, rfl⟩
  exact ⟨by rw [← h3, ← card_map (Embedding.subtype _), hmap, card_map],
    by rw [← h2, ← card_map (Embedding.subtype _), hmapB, card_map]⟩

omit [Fintype HR] in
/-- The exterior of the gluing and its image under the involution cover the boundary. -/
theorem exterior_union_map_inv_leafGluing :
    (Y.leafGluing h).exterior ∪ (Y.leafGluing h).exterior.map (Y.leafGluing h).inv.toEmbedding =
      (Y.leafGluing h).bdry := by
  set G := Y.leafGluing h
  have hsymm : ∀ x, G.inv.symm x = G.inv x := fun x => by
    rw [Equiv.symm_apply_eq, h.leafGluing_inv_involutive]
  have hsymmY : ∀ y, Y.inv.symm y = Y.inv y := fun y => by
    rw [Equiv.symm_apply_eq, h.inv_inv_left]
  ext x
  rw [mem_union, mem_map_equiv, hsymm]
  constructor
  · rintro (hx | hx)
    · exact G.exterior_subset_bdry hx
    · have := h.inv_mem_leafGluing_bdry hY (G.exterior_subset_bdry hx)
      rwa [h.leafGluing_inv_involutive] at this
  · intro hx
    obtain ⟨a, haB, hxa⟩ := h.mem_leafGluing_bdry_iff.1 hx
    have ha := haB
    rw [← hY.exterior_union_map_inv, mem_union, mem_map_equiv, hsymmY] at ha
    rcases ha with ha | ha
    · exact Or.inl ((h.mem_leafGluing_exterior_iff).2 ⟨a, hxa, ha⟩)
    · exact Or.inr ((h.mem_leafGluing_exterior_iff).2
        ⟨_, h.coe_leafGluing_inv_of_mem_bdry hY hxa haB, ha⟩)

omit [Fintype HR] in
/-- The exterior of the gluing is disjoint from its image under the involution. -/
theorem disjoint_exterior_map_inv_leafGluing :
    Disjoint (Y.leafGluing h).exterior
      ((Y.leafGluing h).exterior.map (Y.leafGluing h).inv.toEmbedding) := by
  have hsymm : ∀ x, (Y.leafGluing h).inv.symm x = (Y.leafGluing h).inv x := fun x => by
    rw [Equiv.symm_apply_eq, h.leafGluing_inv_involutive]
  have hsymmY : ∀ y, Y.inv.symm y = Y.inv y := fun y => by
    rw [Equiv.symm_apply_eq, h.inv_inv_left]
  rw [disjoint_left]
  intro x hx hx'
  rw [mem_map_equiv, hsymm] at hx'
  obtain ⟨a, hxa, ha⟩ := (h.mem_leafGluing_exterior_iff).1 hx
  obtain ⟨a', hxa', ha'⟩ := (h.mem_leafGluing_exterior_iff).1 hx'
  rw [h.coe_leafGluing_inv_of_mem_bdry hY hxa (Y.exterior_subset_bdry ha)] at hxa'
  obtain rfl := Sum.inl_injective hxa'
  exact disjoint_left.1 hY.disjoint_exterior_map_inv ha (by rwa [mem_map_equiv, hsymmY])

/-- The gluing of plabic graphs is a disk map. -/
theorem isDiskMap_leafGluing (hR : R.toDiskMap.IsDiskMap) : (Y.leafGluing h).IsDiskMap := by
  set G := Y.leafGluing h
  obtain ⟨z₀, hz₀, -⟩ := hY.exists_exterior ⟨0, hY.one_le⟩
  refine
    { toIsConnected := h.isConnected_leafGluing hY hR
      inv_mem_bdry := fun _ => h.inv_mem_leafGluing_bdry hY
      euler := ?_
      boundaryVertex_card := fun _ => h.boundaryVertex_card_leafGluing hY
      exists_orbit := ⟨G.exterior,
        G.mem_faceOrbits.2 ⟨_, h.faceOf_leafGluing_of_mem_exterior hY hz₀⟩,
        G.exterior_subset_bdry, h.exterior_union_map_inv_leafGluing hY,
        h.disjoint_exterior_map_inv_leafGluing hY⟩ }
  have hV : G.vertices.card + 2 = Y.vertices.card + R.vertices.card :=
    h.card_vertices_leafGluing
  have hE : G.edges.card + 2 = Y.edges.card + R.edges.card := h.card_edges_leafGluing
  have hF : G.faceOrbits.card + 2 = Y.faceOrbits.card + R.faceOrbits.card :=
    h.card_faceOrbits_leafGluing
  have hYe := hY.euler
  have hRe := hR.euler
  omega

/-- If `Y` and `R` are plabic graphs, then so is `Y⟨f ← R⟩`, with the `b` boundary vertices of
`Y`. -/
@[cluster_algebras "lem_leaf_gluing_plabic"]
theorem isPlabicGraph_leafGluing (hR : R.IsPlabicGraph) : (Y.leafGluing h).IsPlabicGraph where
  toIsDiskMap := h.isDiskMap_leafGluing hY hR.toIsDiskMap
  one_le := hY.one_le
  colour_rot := by
    rintro ⟨v, hv⟩ hd
    rcases v with a | r
    · change Y.colour (Y.rot a) = Y.colour a
      exact hY.colour_rot a fun hb =>
        hd ((h.isBoundaryVertex_leafGluing_vertexOf_iff).2 ⟨a, rfl, hb⟩)
    · change R.colour (R.rot r) = R.colour r
      refine hR.colour_rot r fun ⟨z, hz, hzB⟩ => ?_
      rw [h.bdry_right, mem_insert, mem_singleton] at hzB
      have := h.mem_triple_of_sameCycle (z := z) (r := r) (by tauto)
        ((RotationSystem.mem_vertexOf _).1 hz).symm
      simp only [leafGluingDarts, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        reduceCtorEq, Sum.inr.injEq, false_or] at hv
      exact hv this
  leg_notMem_bdry i := by
    rw [h.mem_leafGluing_bdry_iff]
    rintro ⟨a, ha, e⟩
    rw [coe_leafGluing_leg] at e
    exact hY.leg_notMem_bdry i (Sum.inl_injective e ▸ ha)
  bvertex_mem i := by
    refine (Y.leafGluing h).vertexOf_mem_boundaryVertices.2
      ((h.isBoundaryVertex_leafGluing_vertexOf_iff).2 ⟨Y.leg i, rfl, ?_⟩)
    exact Y.vertexOf_mem_boundaryVertices.1 (hY.bvertex_mem i)
  bvertex_injective i j hij := by
    have hj : (Y.leafGluing h).leg j ∈ (Y.leafGluing h).bvertex i := by
      rw [hij]
      exact (Y.leafGluing h).leg_mem_bvertex j
    have := (h.mem_leafGluing_vertexOf_iff_of_inl (coe_leafGluing_leg h i)
      (coe_leafGluing_leg h j)).1 hj
    exact hY.bvertex_injective (Y.vertexOf_eq_of_mem this).symm
  exists_bvertex_eq v hv := by
    obtain ⟨hvV, hb⟩ := (Y.leafGluing h).mem_boundaryVertices.1 hv
    obtain ⟨x, rfl⟩ := (Y.leafGluing h).mem_vertices.1 hvV
    obtain ⟨a, hxa, hYb⟩ := (h.isBoundaryVertex_leafGluing_vertexOf_iff).1 hb
    obtain ⟨i, hi⟩ :=
      hY.exists_bvertex_eq _ (Y.mem_boundaryVertices.2 ⟨Y.vertexOf_mem_vertices a, hYb⟩)
    refine ⟨i, ((Y.leafGluing h).vertexOf_eq_of_mem ?_).symm⟩
    rw [h.mem_leafGluing_vertexOf_iff_of_inl (coe_leafGluing_leg h i) hxa]
    change a ∈ Y.bvertex i
    rw [hi]
    exact Y.self_mem_vertexOf a
  exists_exterior i := by
    obtain ⟨d, hd, hdv, hdiv⟩ := hY.exists_exterior i
    have hdB := Y.exterior_subset_bdry hd
    exact ⟨⟨_, h.inl_mem_of_mem_bdry hdB⟩, (h.mem_leafGluing_exterior_iff).2 ⟨d, rfl, hd⟩,
      (h.mem_leafGluing_vertexOf_iff_of_inl (coe_leafGluing_leg h _) rfl).2 hdv,
      (h.mem_leafGluing_vertexOf_iff_of_inl (coe_leafGluing_leg h _)
        (h.coe_leafGluing_inv_of_mem_bdry hY rfl hdB)).2 hdiv⟩

/-- If `Y` and `R` are plabic graphs, then `Y⟨f ← R⟩` has as many faces as `Y` and `R` together,
minus one. -/
@[cluster_algebras "lem_leaf_gluing_plabic"]
theorem card_faces_leafGluing (hR : R.IsPlabicGraph) :
    (Y.leafGluing h).faces.card + 1 = Y.faces.card + R.faces.card := by
  have h1 := card_erase_add_one (h.isDiskMap_leafGluing hY hR.toIsDiskMap).exterior_mem_faceOrbits
  have h2 := card_erase_add_one hY.toIsDiskMap.exterior_mem_faceOrbits
  have h3 := card_erase_add_one hR.toIsDiskMap.exterior_mem_faceOrbits
  have h4 := h.card_faceOrbits_leafGluing
  simp only [DiskMap.faces]
  omega

end IsLeafGluingSite

/-- If `Y` is a plabic graph, `f ∉ B_Y` with `σ_Y f = f`, and `R` is a plabic graph with one
boundary vertex, then `R` can be glued into the leaf `{f}` of `Y` along `p = σ_R⁻¹(g₁)` and its leg
`g = g₁`. -/
@[cluster_algebras "lem_leaf_gluing_plabic"]
theorem isLeafGluingSite_of_isPlabicGraph [Fintype HY] [Fintype HR] {Y : PlabicData HY b}
    {f : HY} {R : PlabicData HR 1} (hY : Y.IsPlabicGraph) (hR : R.IsPlabicGraph)
    (hf : f ∉ Y.bdry) (hff : Y.rot f = f) :
    Y.IsLeafGluingSite f R (R.rot.symm (R.leg 0)) (R.leg 0) := by
  obtain ⟨d, hd, hdv, hdiv⟩ := hR.exists_exterior 0
  rw [show finRotate 1 0 = 0 from Subsingleton.elim _ _] at hdv
  obtain ⟨hset, h1, h2, h3⟩ := DiskMap.rot_cycle_of_mem_boundaryVertices hR.inv_involutive
    hR.inv_mem_bdry hR.boundaryVertex_card hR.exists_orbit (hR.bvertex_mem 0) hd hdv hd hdiv
    (R.leg_mem_bvertex 0) (hR.leg_notMem_bdry 0)
  have hp : R.rot.symm (R.leg 0) = d := by rw [Equiv.symm_apply_eq, h2]
  rw [hp]
  refine ⟨hY.inv_involutive, hY.inv_ne, hR.inv_involutive, hR.inv_ne, hf, hff, fun i e => ?_, ?_,
    hR.leg_notMem_bdry 0, h1, h2, h3⟩
  · exact DiskMap.rot_ne_of_isBoundaryVertex hY.boundaryVertex_card
      (Y.vertexOf_mem_boundaryVertices.1 (hY.bvertex_mem i)) (by rw [e, hff])
  · ext x
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hR.exists_bvertex_eq _
        (R.vertexOf_mem_boundaryVertices.2 (R.isBoundaryVertex_vertexOf_of_mem hx))
      obtain rfl : i = 0 := Subsingleton.elim _ _
      have hxv : x ∈ R.bvertex 0 := by
        rw [hi]
        exact R.self_mem_vertexOf x
      simp only [hset, mem_insert, mem_singleton] at hxv
      rcases hxv with rfl | rfl | rfl
      exacts [Or.inr rfl, Or.inl rfl, absurd hx (hR.leg_notMem_bdry 0)]
    · rintro (rfl | rfl)
      · exact R.exterior_subset_bdry hd
      · exact hR.inv_mem_bdry _ (R.exterior_subset_bdry hd)

end PlabicData

end ClusterAlgebras
