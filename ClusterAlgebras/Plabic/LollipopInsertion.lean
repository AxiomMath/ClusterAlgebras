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
# Inserting and extracting a lollipop

Let `A` be a plabic graph with `b' ≥ 1` boundary vertices, `i ∈ [1, b' + 1]` and `c` a colour.
Let `i' = i` if `i ≤ b'` and `i' = 1` if `i = b' + 1`, let `h = σ⁻¹(g_{i'})` be the dart of the
exterior at `β(i')` and `h̄` its partner, which lies at `β(i' - 1)`. The *insertion of a lollipop
of colour `c` at `i`* places a new boundary vertex `ν = (e₁, e₂, g°)` on the boundary arc
`{h, h̄}`, pairing `h` with `e₁` and `h̄` with `e₂`, and attaches to it, through the new edge
`{g°, ḡ°}`, a new internal leaf `{ḡ°}` of colour `c`. The new vertex receives the label `i`, and
the labels `j ≥ i` of `A` move up by one. The result is a plabic graph with `b' + 1` boundary
vertices and as many faces as `A`, and `{ḡ°}` is a lollipop at `i`. Conversely, every plabic
graph with at least two boundary vertices and a lollipop at `i` is, up to isomorphism, obtained
in this way.

## Main definitions

* `ClusterAlgebras.insertionNext`: the label `i'` of `A`.
* `ClusterAlgebras.PlabicData.lollipopArc`: the dart `h = σ⁻¹(g_{i'})`.
* `ClusterAlgebras.PlabicData.lollipopInsertion`: the insertion `I_i(A, c)` of a lollipop.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.lollipopInsertion`,
  `ClusterAlgebras.PlabicData.card_faces_lollipopInsertion`,
  `ClusterAlgebras.PlabicData.lollipopInsertion_leg_succAbove`,
  `ClusterAlgebras.PlabicData.isLollipopOfColour_lollipopInsertion`: the insertion is a plabic
  graph with as many faces as `A`, the legs of `A`, and a lollipop of colour `c` at `i`.
* `ClusterAlgebras.PlabicData.isPlabicGraph_lollipopInsertion_iff`: conversely, `A` is a plabic
  graph if `I_i(A, c)` is.
* `ClusterAlgebras.PlabicData.Iso.isPlabicGraph`: a tuple isomorphic to a plabic graph, with its
  legs outside `B`, is a plabic graph.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.exists_isomorphic_lollipopInsertion`: a lollipop can
  be extracted.

## Implementation notes

* The darts of `I_i(A, c)` are `H ⊕ Fin 4`, with `e₁ = inr 0`, `e₂ = inr 1`, `g° = inr 2` and
  `ḡ° = inr 3`; by [FWZ], any other choice of four new darts gives an isomorphic tuple.
* Labels are `0`-indexed: `i : Fin (b + 1)` is the label `i + 1` of [FWZ]. The relabelling
  `j ↦ j⁺` is `Fin.succAbove i`, and the label `i'` is `insertionNext i`, which is `i` unless `i`
  is the last label, and then `0`. The number of boundary vertices of `A` is a parameter `b` with
  `[NeZero b]`.
* The involution of `I_i(A, c)` is written as a product of transpositions with the extension
  of `d ↦ d̄` by `(g° ḡ°)`, so that it is a permutation without hypotheses; its values are those
  of [FWZ] when `d ↦ d̄` is an involution without fixed point at `h`. The colour of every new
  dart is `c`; only the colour of the new internal vertex `{ḡ°}` matters.
* The extraction is proved by building `A` on the darts of `K` outside `β(i) ∪ u`, an isomorphism
  of `K` with `I_i(A, κ(u))`, and the converse of the insertion lemma: if `I_i(A, c)` is a plabic
  graph, so is `A`. Plabic graphs are transported along isomorphisms whose target has its legs
  outside `B` (`PlabicData.Iso.isPlabicGraph`).

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm

/-! ### Preliminaries -/

/-- Two maps on a finite type with the same fibres have images of the same size. -/
private theorem card_image_univ_eq_card_image_pair {α γ δ : Type*} [Fintype α] [DecidableEq γ]
    [DecidableEq δ] {f : α → γ} {g : α → δ} (h : ∀ a a', f a = f a' → g a = g a') :
    (univ.image f).card = (univ.image fun a => (f a, g a)).card := by
  rw [← card_image_of_injOn (f := Prod.fst) (s := univ.image fun a => (f a, g a)), image_image]
  · rfl
  · rintro ⟨_, _⟩ hx ⟨_, _⟩ hy hxy
    obtain ⟨a, -, ha⟩ := mem_image.1 (mem_coe.1 hx)
    obtain ⟨a', -, ha'⟩ := mem_image.1 (mem_coe.1 hy)
    simp only [Prod.mk.injEq] at ha ha'
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨rfl, rfl⟩ := ha'
    simp only at hxy
    rw [hxy, h a a' hxy]

/-- Two maps on a finite type with the same fibres have images of the same size. -/
private theorem card_image_univ_eq_of_iff {α γ δ : Type*} [Fintype α] [DecidableEq γ]
    [DecidableEq δ]
    {f : α → γ} {g : α → δ} (h : ∀ a a', f a = f a' ↔ g a = g a') :
    (univ.image f).card = (univ.image g).card := by
  rw [card_image_univ_eq_card_image_pair (fun a a' => (h a a').1),
    card_image_univ_eq_card_image_pair (f := g) (g := f) (fun a a' => (h a a').2),
    ← card_image_of_injective _ Prod.swap_injective, image_image]
  rfl

private theorem Equiv.Perm.sumCongr_zpow {α β : Type*} (f : Perm α) (g : Perm β) (n : ℤ) :
    Equiv.Perm.sumCongr f g ^ n = Equiv.Perm.sumCongr (f ^ n) (g ^ n) := by
  have := map_zpow (sumCongrHom α β) (f, g) n
  simpa using this.symm

private theorem Equiv.Perm.sameCycle_sumCongr_inl_inl {α β : Type*} {f : Perm α} {g : Perm β}
    {x y : α} :
    (Equiv.Perm.sumCongr f g).SameCycle (Sum.inl x) (Sum.inl y) ↔ f.SameCycle x y := by
  simp [SameCycle, Equiv.Perm.sumCongr_zpow]

private theorem Equiv.Perm.not_sameCycle_sumCongr_inl_inr {α β : Type*} {f : Perm α} {g : Perm β}
    {x : α} {y : β} : ¬(Equiv.Perm.sumCongr f g).SameCycle (Sum.inl x) (Sum.inr y) := by
  simp [SameCycle, Equiv.Perm.sumCongr_zpow]

private theorem inl_mem_map_inl {α β : Type*} {s : Finset α} {x : α} :
    (Sum.inl x : α ⊕ β) ∈ s.map Function.Embedding.inl ↔ x ∈ s :=
  mem_map' Function.Embedding.inl

/-- Every element of `Fin 4` is one of `0, 1, 2, 3`. -/
private theorem fin_four_cases (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  revert k
  decide

namespace RotationSystem

variable {X : Type*} [Fintype X] [DecidableEq X] (R : RotationSystem X)

/-- A set of darts closed under a fixed-point-free involution has twice as many elements as it
meets edges. -/
private theorem card_eq_two_mul_card_edges (hinv : Function.Involutive R.inv)
    (hne : ∀ d, R.inv d ≠ d) :
    Fintype.card X = 2 * R.edges.card := by
  rw [← Finset.card_univ (α := X), card_eq_sum_card_image R.edgeOf univ, edges, mul_comm]
  refine sum_const_nat fun t ht => ?_
  obtain ⟨d, -, rfl⟩ := mem_image.1 ht
  have : ({a ∈ univ | R.edgeOf a = R.edgeOf d} : Finset X) = {d, R.inv d} := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro h
      exact R.mem_edgeOf.1 (h ▸ R.mem_edgeOf.2 (Or.inl rfl))
    · rintro (rfl | rfl)
      · rfl
      · ext x
        simp only [mem_edgeOf, hinv d]
        tauto
  rw [this, card_pair (hne d).symm]

/-- A vertex visited by a `3`-cycle of the rotation consists of the three darts of the cycle. -/
private theorem vertexOf_eq_of_rot_three {a b c : X} (hab : R.rot a = b) (hbc : R.rot b = c)
    (hca : R.rot c = a) : R.vertexOf a = {a, b, c} := by
  ext y
  rw [mem_vertexOf]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have := ih (sameCycle_pow_apply_self _ a n)
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with h | h | h <;> rw [h] <;> simp [hab, hbc, hca]
  · simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact SameCycle.refl _ _
    · rw [← hab]
      exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · rw [← hbc, ← hab]
      exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-- The vertex of a fixed point of the rotation is a singleton. -/
private theorem vertexOf_eq_singleton {a : X} (ha : R.rot a = a) : R.vertexOf a = {a} := by
  ext y
  rw [mem_vertexOf, mem_singleton]
  exact ⟨fun h => (h.eq_of_left ha).symm, fun h => h ▸ SameCycle.refl _ _⟩

end RotationSystem

/-! ### The label `i'` -/

/-- The label `i'` in `Fin b` attached to a label `i : Fin (b + 1)`: `i` itself unless `i` is the
last label, and the first label `0` if it is. -/
def insertionNext {b : ℕ} [NeZero b] (i : Fin (b + 1)) : Fin b :=
  Fin.lastCases (motive := fun _ => Fin b) 0 id i

/-- The label `i'` of the last label is `0`. -/
@[simp]
theorem insertionNext_last {b : ℕ} [NeZero b] : insertionNext (Fin.last b) = 0 := by
  simp [insertionNext]

/-- The label `i'` of a label `j` other than the last is `j` itself. -/
@[simp]
theorem insertionNext_castSucc {b : ℕ} [NeZero b] (j : Fin b) :
    insertionNext j.castSucc = j := by
  simp [insertionNext]

/-- The value of the label `i'` is that of `i` if `i < b`, and `0` otherwise. -/
theorem val_insertionNext {b : ℕ} [NeZero b] (i : Fin (b + 1)) :
    (insertionNext i : ℕ) = if (i : ℕ) < b then (i : ℕ) else (0 : ℕ) := by
  induction i using Fin.lastCases with
  | last => simp [insertionNext]
  | cast j => simp [insertionNext, j.2]

private theorem val_succAbove' {b : ℕ} (i : Fin (b + 1)) (j : Fin b) :
    (i.succAbove j : ℕ) = if (j : ℕ) < i then (j : ℕ) else j + 1 := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
    simp

private theorem val_finRotate' {n : ℕ} (i : Fin n) :
    (finRotate n i : ℕ) = if (i : ℕ) + 1 = n then (0 : ℕ) else (i : ℕ) + 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by have := i.2; omega⟩
  rw [coe_finRotate]
  simp [Fin.ext_iff]

/-- The label following `i` is the image `(i')⁺` of `i'`. -/
theorem finRotate_eq_succAbove_insertionNext {b : ℕ} [NeZero b] (i : Fin (b + 1)) :
    finRotate (b + 1) i = i.succAbove (insertionNext i) := by
  induction i using Fin.lastCases with
  | last =>
    rw [insertionNext_last, finRotate_last, Fin.succAbove_last]
    rfl
  | cast j =>
    rw [insertionNext_castSucc, Fin.succAbove_of_le_castSucc _ _ le_rfl]
    ext
    rw [coe_finRotate, if_neg (Fin.castSucc_lt_last j).ne]
    simp

/-- For a label `j` among `b`, the label following `j⁺` among `b + 1` is `i` when the label
following `j` is `i'`, and `(j + 1)⁺` otherwise. -/
theorem finRotate_succAbove {b : ℕ} [NeZero b] (i : Fin (b + 1)) (j : Fin b) :
    (finRotate (b + 1) (i.succAbove j) = i ∧ finRotate b j = insertionNext i) ∨
      (finRotate (b + 1) (i.succAbove j) = i.succAbove (finRotate b j) ∧
        finRotate b j ≠ insertionNext i) := by
  simp only [Fin.ext_iff, ne_eq, val_succAbove', val_insertionNext, val_finRotate']
  have hi := i.2
  have hj := j.2
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  split_ifs <;> first | omega | simp

/-! ### The insertion of a lollipop -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} [NeZero b]

/-- The dart `h = σ⁻¹(g_{i'})` of `A` on whose edge `{h, h̄}` the new boundary vertex is placed. -/
def lollipopArc (A : PlabicData H b) (i : Fin (b + 1)) : H :=
  A.rot.symm (A.leg (insertionNext i))

/-- **Inserting a lollipop**. For a tuple `A` of the shape of a plabic
graph with `b ≥ 1` boundary vertices, a label `i` among `b + 1` and a colour `c`, the tuple
`I_i(A, c)` on the darts `H ⊕ Fin 4`, where `e₁ = inr 0`, `e₂ = inr 1`, `g° = inr 2` and
`ḡ° = inr 3`. With `h = lollipopArc A i`, its involution agrees with that of `A` except that it
pairs `h` with `e₁`, `h̄` with `e₂` and `g°` with `ḡ°`; its rotation agrees with that of `A` on
`H` and has the cycles `(e₁ e₂ g°)` and `(ḡ°)`; its boundary arcs are `B ∪ {e₁, e₂}`; the new
darts have the colour `c`; its leg at `i` is `g°`, and its leg at `j⁺ = i.succAbove j` is the leg
of `A` at `j`. -/
@[cluster_algebras "def_lollipop_insertion"]
def lollipopInsertion (A : PlabicData H b) (i : Fin (b + 1)) (c : Shade) :
    PlabicData (H ⊕ Fin 4) (b + 1) where
  inv := Perm.sumCongr A.inv (swap 2 3) *
    swap (Sum.inl (A.lollipopArc i)) (Sum.inl (A.inv (A.lollipopArc i))) *
    swap (Sum.inl (A.lollipopArc i)) (Sum.inr 0) *
    swap (Sum.inl (A.inv (A.lollipopArc i))) (Sum.inr 1)
  rot := Perm.sumCongr A.rot (swap 0 1 * swap 1 2)
  bdry := A.bdry.map Function.Embedding.inl ∪ {Sum.inr 0, Sum.inr 1}
  colour := Sum.elim A.colour fun _ => c
  leg := Fin.insertNth (α := fun _ => H ⊕ Fin 4) i (Sum.inr 2) fun j => Sum.inl (A.leg j)

variable (A : PlabicData H b) (i : Fin (b + 1)) (c : Shade)

/-! #### Values -/

omit [Fintype H] in
/-- The rotation of `I_i(A, c)` at a dart of `A` is the rotation of `A`. -/
@[simp]
theorem lollipopInsertion_rot_inl (x : H) :
    (A.lollipopInsertion i c).rot (Sum.inl x) = Sum.inl (A.rot x) := rfl

omit [Fintype H] in
/-- The rotation of `I_i(A, c)` sends `e₁` to `e₂`. -/
@[simp]
theorem lollipopInsertion_rot_inr_zero :
    (A.lollipopInsertion i c).rot (Sum.inr 0) = Sum.inr 1 := rfl

omit [Fintype H] in
/-- The rotation of `I_i(A, c)` sends `e₂` to `g°`. -/
@[simp]
theorem lollipopInsertion_rot_inr_one : (A.lollipopInsertion i c).rot (Sum.inr 1) = Sum.inr 2 := rfl

omit [Fintype H] in
/-- The rotation of `I_i(A, c)` sends `g°` to `e₁`. -/
@[simp]
theorem lollipopInsertion_rot_inr_two : (A.lollipopInsertion i c).rot (Sum.inr 2) = Sum.inr 0 := rfl

omit [Fintype H] in
/-- The rotation of `I_i(A, c)` fixes `ḡ°`. -/
@[simp]
theorem lollipopInsertion_rot_inr_three :
    (A.lollipopInsertion i c).rot (Sum.inr 3) = Sum.inr 3 := rfl

omit [Fintype H] in
/-- A dart of `A` is a boundary arc of `I_i(A, c)` iff it is a boundary arc of `A`. -/
@[simp]
theorem mem_lollipopInsertion_bdry_inl {x : H} :
    Sum.inl x ∈ (A.lollipopInsertion i c).bdry ↔ x ∈ A.bdry := by
  simp [lollipopInsertion]

omit [Fintype H] in
/-- The new boundary arcs of `I_i(A, c)` are `e₁` and `e₂`. -/
@[simp]
theorem mem_lollipopInsertion_bdry_inr {k : Fin 4} :
    Sum.inr k ∈ (A.lollipopInsertion i c).bdry ↔ k = 0 ∨ k = 1 := by
  simp [lollipopInsertion]

omit [Fintype H] in
/-- The colour of a dart of `A` in `I_i(A, c)` is its colour in `A`. -/
@[simp]
theorem lollipopInsertion_colour_inl (x : H) :
    (A.lollipopInsertion i c).colour (Sum.inl x) = A.colour x := rfl

omit [Fintype H] in
/-- Every new dart of `I_i(A, c)` has the colour `c`. -/
@[simp]
theorem lollipopInsertion_colour_inr (k : Fin 4) :
    (A.lollipopInsertion i c).colour (Sum.inr k) = c := rfl

omit [Fintype H] in
/-- The leg of `I_i(A, c)` at `i` is `g°`. -/
@[simp]
theorem lollipopInsertion_leg_self : (A.lollipopInsertion i c).leg i = Sum.inr 2 := by
  simp [lollipopInsertion]

omit [Fintype H] in
/-- **An insertion is a plabic graph**: the leg of `I_i(A, c)` at `j⁺` is the leg of `A` at
`j`. -/
@[simp, cluster_algebras "lem_lollipop_insertion_plabic"]
theorem lollipopInsertion_leg_succAbove (j : Fin b) :
    (A.lollipopInsertion i c).leg (i.succAbove j) = Sum.inl (A.leg j) := by
  simp [lollipopInsertion]

omit [Fintype H] in
/-- The involution of `I_i(A, c)` agrees with that of `A` at a dart of `A` other than `h` and
`h̄`. -/
theorem lollipopInsertion_inv_inl_of_ne {x : H} (h₁ : x ≠ A.lollipopArc i)
    (h₂ : x ≠ A.inv (A.lollipopArc i)) :
    (A.lollipopInsertion i c).inv (Sum.inl x) = Sum.inl (A.inv x) := by
  simp [lollipopInsertion, swap_apply_of_ne_of_ne, h₁, h₂]

omit [Fintype H] in
/-- The involution of `I_i(A, c)` sends `h̄` to `e₂`. -/
theorem lollipopInsertion_inv_inl_inv :
    (A.lollipopInsertion i c).inv (Sum.inl (A.inv (A.lollipopArc i))) = Sum.inr 1 := by
  simp [lollipopInsertion, swap_apply_of_ne_of_ne]

omit [Fintype H] in
/-- The involution of `I_i(A, c)` sends `e₁` to the image of `h̄` under the involution of `A`. -/
theorem lollipopInsertion_inv_inr_zero :
    (A.lollipopInsertion i c).inv (Sum.inr 0) = Sum.inl (A.inv (A.inv (A.lollipopArc i))) := by
  simp [lollipopInsertion, swap_apply_of_ne_of_ne]

omit [Fintype H] in
/-- The involution of `I_i(A, c)` sends `g°` to `ḡ°`. -/
@[simp]
theorem lollipopInsertion_inv_inr_two : (A.lollipopInsertion i c).inv (Sum.inr 2) = Sum.inr 3 := by
  simp [lollipopInsertion, swap_apply_of_ne_of_ne]

omit [Fintype H] in
/-- The involution of `I_i(A, c)` sends `ḡ°` to `g°`. -/
@[simp]
theorem lollipopInsertion_inv_inr_three :
    (A.lollipopInsertion i c).inv (Sum.inr 3) = Sum.inr 2 := by
  simp [lollipopInsertion, swap_apply_of_ne_of_ne]

section

variable {A i} (hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i)

include hh

omit [Fintype H] in
/-- If `h̄ ≠ h`, the involution of `I_i(A, c)` sends `h` to `e₁`. -/
theorem lollipopInsertion_inv_inl_self :
    (A.lollipopInsertion i c).inv (Sum.inl (A.lollipopArc i)) = Sum.inr 0 := by
  simp [lollipopInsertion, swap_apply_of_ne_of_ne, Ne.symm hh]

omit [Fintype H] in
/-- If `h̄ ≠ h`, the involution of `I_i(A, c)` sends `e₂` to `h̄`. -/
theorem lollipopInsertion_inv_inr_one :
    (A.lollipopInsertion i c).inv (Sum.inr 1) = Sum.inl (A.inv (A.lollipopArc i)) := by
  simp [lollipopInsertion, swap_apply_of_ne_of_ne, hh]

end

/-! #### The rotation system -/

section RotationSystem

variable {A i}

/-- The dart `h` of `A`. -/
local notation "𝔥" => A.lollipopArc i

/-- The dart of `A` attached to a dart of `I_i(A, c)`: a dart of `A` itself, `h` for `e₂`, and
`h̄` for `e₁`, `g°` and `ḡ°`. Two darts of `I_i(A, c)` lie in one orbit of its face permutation
iff the attached darts lie in one orbit of `φ_A`. -/
private def proj (A : PlabicData H b) (i : Fin (b + 1)) : H ⊕ Fin 4 → H
  | Sum.inl x => x
  | Sum.inr k => if k = 1 then A.lollipopArc i else A.inv (A.lollipopArc i)

omit [Fintype H] [DecidableEq H] in
@[simp]
private theorem proj_inl (x : H) : proj A i (Sum.inl x) = x := rfl

omit [Fintype H] [DecidableEq H] in
@[simp]
private theorem proj_inr_zero : proj A i (Sum.inr 0) = A.inv (A.lollipopArc i) := rfl

omit [Fintype H] [DecidableEq H] in
@[simp]
private theorem proj_inr_one : proj A i (Sum.inr 1) = A.lollipopArc i := rfl

omit [Fintype H] [DecidableEq H] in
@[simp]
private theorem proj_inr_two : proj A i (Sum.inr 2) = A.inv (A.lollipopArc i) := rfl

omit [Fintype H] [DecidableEq H] in
@[simp]
private theorem proj_inr_three : proj A i (Sum.inr 3) = A.inv (A.lollipopArc i) := rfl

private theorem sameCycle_of_apply_eq {α : Type*} {f : Perm α} {x y : α} (h : f x = y) :
    f.SameCycle x y :=
  h ▸ sameCycle_apply_right.2 (SameCycle.refl f x)

section Involution

variable (hinv : Function.Involutive A.inv) (hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i)

include hinv hh

omit hh in
omit [Fintype H] in
/-- If the involution of `A` is an involution, the involution of `I_i(A, c)` sends `e₁` to
`h`. -/
theorem lollipopInsertion_inv_inr_zero' :
    (A.lollipopInsertion i c).inv (Sum.inr 0) = Sum.inl (A.lollipopArc i) := by
  rw [lollipopInsertion_inv_inr_zero, hinv]

omit [Fintype H] in
/-- The involution of `I_i(A, c)` is an involution. -/
theorem lollipopInsertion_inv_involutive : Function.Involutive (A.lollipopInsertion i c).inv := by
  intro z
  rcases z with x | k
  · by_cases h₁ : x = 𝔥
    · subst h₁
      rw [lollipopInsertion_inv_inl_self c hh, lollipopInsertion_inv_inr_zero' c hinv]
    by_cases h₂ : x = A.inv 𝔥
    · subst h₂
      rw [lollipopInsertion_inv_inl_inv, lollipopInsertion_inv_inr_one c hh]
    have h₃ : A.inv x ≠ 𝔥 := fun he => h₂ (by rw [← he, hinv])
    have h₄ : A.inv x ≠ A.inv 𝔥 := fun he => h₁ (A.inv.injective he)
    rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂, lollipopInsertion_inv_inl_of_ne A i c h₃ h₄,
      hinv]
  · rcases fin_four_cases k with rfl | rfl | rfl | rfl
    · rw [lollipopInsertion_inv_inr_zero' c hinv, lollipopInsertion_inv_inl_self c hh]
    · rw [lollipopInsertion_inv_inr_one c hh, lollipopInsertion_inv_inl_inv]
    · simp
    · simp

omit [Fintype H] in
/-- The involution of `I_i(A, c)` has no fixed point iff that of `A` has none. -/
theorem lollipopInsertion_inv_ne_iff :
    (∀ z, (A.lollipopInsertion i c).inv z ≠ z) ↔ ∀ x, A.inv x ≠ x := by
  constructor
  · intro hI x hx
    by_cases h₁ : x = 𝔥
    · exact hh (h₁ ▸ hx)
    by_cases h₂ : x = A.inv 𝔥
    · subst h₂
      rw [hinv] at hx
      exact hh hx.symm
    exact hI (Sum.inl x) (by rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂, hx])
  · intro hA z
    rcases z with x | k
    · by_cases h₁ : x = 𝔥
      · subst h₁
        rw [lollipopInsertion_inv_inl_self c hh]
        simp
      by_cases h₂ : x = A.inv 𝔥
      · subst h₂
        rw [lollipopInsertion_inv_inl_inv]
        simp
      rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂]
      simpa using hA x
    · rcases fin_four_cases k with rfl | rfl | rfl | rfl
      · rw [lollipopInsertion_inv_inr_zero' c hinv]
        simp
      · rw [lollipopInsertion_inv_inr_one c hh]
        simp
      · simp
      · simp

omit [Fintype H] in
/-- The face permutation moves the attached dart along an orbit of `φ_A`. -/
private theorem sameCycle_proj_facePerm (z : H ⊕ Fin 4) :
    A.facePerm.SameCycle (proj A i z) (proj A i ((A.lollipopInsertion i c).facePerm z)) := by
  rcases z with x | k
  · by_cases h₁ : x = 𝔥
    · subst h₁
      rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inl_self c hh,
        lollipopInsertion_rot_inr_zero, proj_inr_one, proj_inl]
    by_cases h₂ : x = A.inv 𝔥
    · subst h₂
      rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inl_inv,
        lollipopInsertion_rot_inr_one, proj_inr_two, proj_inl]
    rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inl_of_ne A i c h₁ h₂]
    exact sameCycle_of_apply_eq rfl
  · rcases fin_four_cases k with rfl | rfl | rfl | rfl
    · rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inr_zero' c hinv]
      refine sameCycle_of_apply_eq ?_
      simp [hinv 𝔥]
    · rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inr_one c hh]
      exact sameCycle_of_apply_eq rfl
    · rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inr_two,
        lollipopInsertion_rot_inr_three, proj_inr_two, proj_inr_three]
    · rw [RotationSystem.facePerm_apply, lollipopInsertion_inv_inr_three,
        lollipopInsertion_rot_inr_two, proj_inr_three, proj_inr_zero]

omit [Fintype H] in
/-- Orbits of the face permutation of `I_i(A, c)` map into orbits of `φ_A`. -/
private theorem sameCycle_proj_of_sameCycle [Finite H] {z z' : H ⊕ Fin 4}
    (hz : (A.lollipopInsertion i c).facePerm.SameCycle z z') :
    A.facePerm.SameCycle (proj A i z) (proj A i z') := by
  have := Fintype.ofFinite H
  obtain ⟨n, rfl⟩ := hz.exists_nat_pow_eq
  clear hz
  induction n with
  | zero => exact SameCycle.refl _ _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (sameCycle_proj_facePerm c hinv hh _)

omit [Fintype H] in
/-- A dart of `A` and its image under `φ_A` lie in one orbit of the face permutation of
`I_i(A, c)`. -/
private theorem sameCycle_inl_facePerm (x : H) :
    (A.lollipopInsertion i c).facePerm.SameCycle (Sum.inl x) (Sum.inl (A.facePerm x)) := by
  set φ := (A.lollipopInsertion i c).facePerm
  by_cases h₁ : x = 𝔥
  · subst h₁
    have e1 : φ (Sum.inl 𝔥) = Sum.inr 1 := by
      simp [φ, lollipopInsertion_inv_inl_self c hh]
    have e2 : φ (Sum.inr 1) = Sum.inl (A.facePerm 𝔥) := by
      simp [φ, lollipopInsertion_inv_inr_one c hh]
    exact (sameCycle_of_apply_eq e1).trans (sameCycle_of_apply_eq e2)
  by_cases h₂ : x = A.inv 𝔥
  · subst h₂
    have e1 : φ (Sum.inl (A.inv 𝔥)) = Sum.inr 2 := by
      simp [φ, lollipopInsertion_inv_inl_inv]
    have e2 : φ (Sum.inr 2) = Sum.inr 3 := by simp [φ]
    have e3 : φ (Sum.inr 3) = Sum.inr 0 := by simp [φ]
    have e4 : φ (Sum.inr 0) = Sum.inl (A.facePerm (A.inv 𝔥)) := by
      simp [φ, lollipopInsertion_inv_inr_zero' c hinv, hinv 𝔥]
    exact (sameCycle_of_apply_eq e1).trans ((sameCycle_of_apply_eq e2).trans
      ((sameCycle_of_apply_eq e3).trans (sameCycle_of_apply_eq e4)))
  · refine sameCycle_of_apply_eq ?_
    simp [φ, lollipopInsertion_inv_inl_of_ne A i c h₁ h₂]

omit [Fintype H] in
private theorem sameCycle_inl_of_sameCycle [Finite H] {x y : H} (hxy : A.facePerm.SameCycle x y) :
    (A.lollipopInsertion i c).facePerm.SameCycle (Sum.inl x) (Sum.inl y) := by
  have := Fintype.ofFinite H
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact SameCycle.refl _ _
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (sameCycle_inl_facePerm c hinv hh _)

omit [Fintype H] in
omit hinv in
/-- Every dart of `I_i(A, c)` lies in the orbit of the face permutation of its attached dart. -/
private theorem sameCycle_inl_proj (z : H ⊕ Fin 4) :
    (A.lollipopInsertion i c).facePerm.SameCycle (Sum.inl (proj A i z)) z := by
  set φ := (A.lollipopInsertion i c).facePerm
  have e1 : φ (Sum.inl (A.inv 𝔥)) = Sum.inr 2 := by simp [φ, lollipopInsertion_inv_inl_inv]
  have e2 : φ (Sum.inr 2) = Sum.inr 3 := by simp [φ]
  have e3 : φ (Sum.inr 3) = Sum.inr 0 := by simp [φ]
  rcases z with x | k
  · exact SameCycle.refl _ _
  · rcases fin_four_cases k with rfl | rfl | rfl | rfl
    · exact (sameCycle_of_apply_eq e1).trans
        ((sameCycle_of_apply_eq e2).trans (sameCycle_of_apply_eq e3))
    · exact sameCycle_of_apply_eq (by simp [φ, lollipopInsertion_inv_inl_self c hh])
    · exact sameCycle_of_apply_eq e1
    · exact (sameCycle_of_apply_eq e1).trans (sameCycle_of_apply_eq e2)

omit [Fintype H] in
/-- Two darts of `I_i(A, c)` lie in one orbit of its face permutation iff their attached darts
lie in one orbit of `φ_A`. -/
private theorem sameCycle_facePerm_iff [Finite H] {z z' : H ⊕ Fin 4} :
    (A.lollipopInsertion i c).facePerm.SameCycle z z' ↔
      A.facePerm.SameCycle (proj A i z) (proj A i z') := by
  refine ⟨sameCycle_proj_of_sameCycle c hinv hh, fun hA => ?_⟩
  exact ((sameCycle_inl_proj c hh z).symm.trans
    (sameCycle_inl_of_sameCycle c hinv hh hA)).trans (sameCycle_inl_proj c hh z')

omit [Fintype H] in
/-- A dart `x` of `A` lies in the orbit of `I_i(A, c)` through `inl y` iff it lies in the
orbit of `A` through `y`. -/
theorem sameCycle_lollipopInsertion_facePerm_inl_iff [Finite H] {x y : H} :
    (A.lollipopInsertion i c).facePerm.SameCycle (Sum.inl x) (Sum.inl y) ↔
      A.facePerm.SameCycle x y :=
  sameCycle_facePerm_iff c hinv hh

/-- `I_i(A, c)` has as many orbits of its face permutation as `A`. -/
theorem card_faceOrbits_lollipopInsertion :
    (A.lollipopInsertion i c).faceOrbits.card = A.faceOrbits.card := by
  have hsurj : Function.Surjective (proj A i) := fun x => ⟨Sum.inl x, rfl⟩
  rw [RotationSystem.faceOrbits, RotationSystem.faceOrbits,
    card_image_univ_eq_of_iff (g := A.faceOf ∘ proj A i), ← image_image,
    image_univ_of_surjective hsurj]
  intro z z'
  rw [Function.comp_apply, Function.comp_apply, RotationSystem.faceOf_eq_faceOf_iff,
    RotationSystem.faceOf_eq_faceOf_iff]
  exact sameCycle_facePerm_iff c hinv hh

omit [Fintype H] in
omit hinv in
/-- In `I_i(A, c)`, a dart of `A` reaches a dart of `A` whenever it does so in `A`. -/
theorem reach_lollipopInsertion_inl {x y : H} (hxy : A.Reach x y) :
    (A.lollipopInsertion i c).Reach (Sum.inl x) (Sum.inl y) := by
  induction hxy with
  | refl => exact RotationSystem.Reach.refl _
  | @rot e _ ih => exact ih.rot
  | @inv e _ ih =>
    by_cases h₁ : e = 𝔥
    · subst h₁
      have := ((ih.inv).rot).inv
      rwa [lollipopInsertion_inv_inl_self c hh, lollipopInsertion_rot_inr_zero,
        lollipopInsertion_inv_inr_one c hh] at this
    by_cases h₂ : e = A.inv 𝔥
    · subst h₂
      have := (((ih.inv).rot).rot).inv
      rwa [lollipopInsertion_inv_inl_inv, lollipopInsertion_rot_inr_one,
        lollipopInsertion_rot_inr_two, lollipopInsertion_inv_inr_zero] at this
    · have := ih.inv
      rwa [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂] at this

omit [Fintype H] in
/-- Every dart of `I_i(A, c)` reaches its attached dart. -/
private theorem reach_inl_proj (z : H ⊕ Fin 4) :
    (A.lollipopInsertion i c).Reach z (Sum.inl (proj A i z)) := by
  have r0 : (A.lollipopInsertion i c).Reach (Sum.inr 0) (Sum.inl (A.inv 𝔥)) := by
    have := (RotationSystem.Reach.refl (R := (A.lollipopInsertion i c).toRotationSystem)
      (Sum.inr 0)).rot.inv
    rwa [lollipopInsertion_rot_inr_zero, lollipopInsertion_inv_inr_one c hh] at this
  have r2 : (A.lollipopInsertion i c).Reach (Sum.inr 2) (Sum.inr 0) := by
    have := (RotationSystem.Reach.refl (R := (A.lollipopInsertion i c).toRotationSystem)
      (Sum.inr 2)).rot
    rwa [lollipopInsertion_rot_inr_two] at this
  rcases z with x | k
  · exact RotationSystem.Reach.refl _
  · rcases fin_four_cases k with rfl | rfl | rfl | rfl
    · exact r0
    · have := (RotationSystem.Reach.refl (R := (A.lollipopInsertion i c).toRotationSystem)
        (Sum.inr 1)).rot
      rw [lollipopInsertion_rot_inr_one] at this
      have := (this.trans r2).inv
      rwa [lollipopInsertion_inv_inr_zero' c hinv] at this
    · exact r2.trans r0
    · have := (RotationSystem.Reach.refl (R := (A.lollipopInsertion i c).toRotationSystem)
        (Sum.inr 3)).inv
      rw [lollipopInsertion_inv_inr_three] at this
      exact (this.trans r2).trans r0

omit [Fintype H] in
/-- A path of `I_i(A, c)` gives a path of `A` between the attached darts. -/
private theorem reach_proj {z z' : H ⊕ Fin 4} (hz : (A.lollipopInsertion i c).Reach z z') :
    A.Reach (proj A i z) (proj A i z') := by
  have hh' : A.Reach 𝔥 (A.inv 𝔥) := (RotationSystem.Reach.refl 𝔥).inv
  have hh'' : A.Reach (A.inv 𝔥) 𝔥 := by
    have := (RotationSystem.Reach.refl (R := A.toRotationSystem) (A.inv 𝔥)).inv
    rwa [hinv 𝔥] at this
  induction hz with
  | refl => exact RotationSystem.Reach.refl _
  | @rot e _ ih =>
    refine ih.trans ?_
    rcases e with x | k
    · exact (RotationSystem.Reach.refl x).rot
    · rcases fin_four_cases k with rfl | rfl | rfl | rfl
      · simpa using hh''
      · simpa using hh'
      · simpa using RotationSystem.Reach.refl _
      · simpa using RotationSystem.Reach.refl _
  | @inv e _ ih =>
    refine ih.trans ?_
    rcases e with x | k
    · by_cases h₁ : x = 𝔥
      · subst h₁
        rw [lollipopInsertion_inv_inl_self c hh]
        simpa using hh'
      by_cases h₂ : x = A.inv 𝔥
      · subst h₂
        rw [lollipopInsertion_inv_inl_inv]
        simpa using hh''
      rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂]
      exact (RotationSystem.Reach.refl x).inv
    · rcases fin_four_cases k with rfl | rfl | rfl | rfl
      · rw [lollipopInsertion_inv_inr_zero' c hinv]
        simpa using hh''
      · rw [lollipopInsertion_inv_inr_one c hh]
        simpa using hh'
      · simpa using RotationSystem.Reach.refl _
      · simpa using RotationSystem.Reach.refl _

omit [Fintype H] in
/-- `I_i(A, c)` is a connected rotation system iff `A` is. -/
theorem isConnected_lollipopInsertion_iff [Finite H] :
    (A.lollipopInsertion i c).IsConnected ↔ A.IsConnected := by
  have := Fintype.ofFinite H
  constructor
  · intro hI
    refine RotationSystem.IsConnected.of_reach ⟨A.leg 0⟩ hinv
      ((lollipopInsertion_inv_ne_iff c hinv hh).1 hI.inv_ne) fun x y => ?_
    simpa using reach_proj c hinv hh (hI.reach (Sum.inl x) (Sum.inl y))
  · intro hA
    refine RotationSystem.IsConnected.of_reach ⟨Sum.inr 0⟩
      (lollipopInsertion_inv_involutive c hinv hh)
      ((lollipopInsertion_inv_ne_iff c hinv hh).2 hA.inv_ne) fun z w => ?_
    exact ((reach_inl_proj c hinv hh z).trans
      (reach_lollipopInsertion_inl c hh (hA.reach _ _))).trans
      (reach_inl_proj c hinv hh w).symm

end Involution

/-! #### Vertices -/

omit [Fintype H] in
private theorem rot_lollipopInsertion_eq :
    (A.lollipopInsertion i c).rot = Perm.sumCongr A.rot (swap 0 1 * swap 1 2) := rfl

/-- The vertex of `I_i(A, c)` at a dart of `A` is the vertex of `A` at that dart. -/
theorem lollipopInsertion_vertexOf_inl (x : H) :
    (A.lollipopInsertion i c).vertexOf (Sum.inl x) = (A.vertexOf x).map Function.Embedding.inl := by
  ext z
  rcases z with y | k
  · simp [RotationSystem.mem_vertexOf, rot_lollipopInsertion_eq,
      Equiv.Perm.sameCycle_sumCongr_inl_inl]
  · simp [RotationSystem.mem_vertexOf, rot_lollipopInsertion_eq,
      Equiv.Perm.not_sameCycle_sumCongr_inl_inr]

/-- The new boundary vertex `ν = (e₁ e₂ g°)`. -/
theorem lollipopInsertion_vertexOf_inr_zero :
    (A.lollipopInsertion i c).vertexOf (Sum.inr 0) = {Sum.inr 0, Sum.inr 1, Sum.inr 2} :=
  RotationSystem.vertexOf_eq_of_rot_three _ (lollipopInsertion_rot_inr_zero A i c)
    (lollipopInsertion_rot_inr_one A i c) (lollipopInsertion_rot_inr_two A i c)

/-- The vertex of `I_i(A, c)` at each of `e₁`, `e₂` and `g°` is `ν = (e₁ e₂ g°)`. -/
theorem lollipopInsertion_vertexOf_inr_of_ne {k : Fin 4} (hk : k ≠ 3) :
    (A.lollipopInsertion i c).vertexOf (Sum.inr k) = {Sum.inr 0, Sum.inr 1, Sum.inr 2} := by
  rw [← lollipopInsertion_vertexOf_inr_zero (A := A) (i := i) (c := c)]
  rcases fin_four_cases k with rfl | rfl | rfl | rfl
  · rfl
  · rw [← lollipopInsertion_rot_inr_zero A i c, RotationSystem.vertexOf_rot]
  · rw [← lollipopInsertion_rot_inr_one A i c, RotationSystem.vertexOf_rot,
      ← lollipopInsertion_rot_inr_zero A i c, RotationSystem.vertexOf_rot]
  · exact absurd rfl hk

/-- The new internal leaf `{ḡ°}`. -/
theorem lollipopInsertion_vertexOf_inr_three :
    (A.lollipopInsertion i c).vertexOf (Sum.inr 3) = {Sum.inr 3} :=
  RotationSystem.vertexOf_eq_singleton _ (lollipopInsertion_rot_inr_three A i c)

/-- The vertex of `I_i(A, c)` at a dart of `A` is a boundary vertex iff the vertex of `A` at that
dart is. -/
theorem isBoundaryVertex_lollipopInsertion_vertexOf_inl (x : H) :
    (A.lollipopInsertion i c).IsBoundaryVertex ((A.lollipopInsertion i c).vertexOf (Sum.inl x)) ↔
      A.IsBoundaryVertex (A.vertexOf x) := by
  rw [lollipopInsertion_vertexOf_inl]
  simp [DiskMap.IsBoundaryVertex]

/-- The new vertex `ν` of `I_i(A, c)` is a boundary vertex. -/
theorem isBoundaryVertex_lollipopInsertion_vertexOf_inr_of_ne {k : Fin 4} (hk : k ≠ 3) :
    (A.lollipopInsertion i c).IsBoundaryVertex
      ((A.lollipopInsertion i c).vertexOf (Sum.inr k)) := by
  rw [lollipopInsertion_vertexOf_inr_of_ne c hk]
  exact ⟨Sum.inr 0, by simp, by simp⟩

/-- The new leaf `{ḡ°}` of `I_i(A, c)` is not a boundary vertex. -/
theorem not_isBoundaryVertex_lollipopInsertion_vertexOf_inr_three :
    ¬(A.lollipopInsertion i c).IsBoundaryVertex
      ((A.lollipopInsertion i c).vertexOf (Sum.inr 3)) := by
  rw [lollipopInsertion_vertexOf_inr_three]
  simp [DiskMap.IsBoundaryVertex]

/-- The vertices of `I_i(A, c)` are those of `A`, `ν` and `{ḡ°}`. -/
theorem lollipopInsertion_vertices :
    (A.lollipopInsertion i c).vertices =
      A.vertices.image (Finset.map Function.Embedding.inl) ∪
        {{Sum.inr 0, Sum.inr 1, Sum.inr 2}, {Sum.inr 3}} := by
  ext v
  simp only [RotationSystem.mem_vertices, mem_union, mem_image, mem_insert, mem_singleton]
  constructor
  · rintro ⟨z, rfl⟩
    rcases z with x | k
    · exact Or.inl ⟨_, ⟨x, rfl⟩, (lollipopInsertion_vertexOf_inl (A := A) (i := i) c x).symm⟩
    · by_cases hk : k = 3
      · subst hk
        exact Or.inr (Or.inr (lollipopInsertion_vertexOf_inr_three (A := A) (i := i) c))
      · exact Or.inr (Or.inl (lollipopInsertion_vertexOf_inr_of_ne c hk))
  · rintro (⟨_, ⟨x, rfl⟩, rfl⟩ | rfl | rfl)
    · exact ⟨Sum.inl x, lollipopInsertion_vertexOf_inl (A := A) (i := i) c x⟩
    · exact ⟨Sum.inr 0, lollipopInsertion_vertexOf_inr_zero (A := A) (i := i) c⟩
    · exact ⟨Sum.inr 3, lollipopInsertion_vertexOf_inr_three (A := A) (i := i) c⟩

/-- `I_i(A, c)` has two vertices more than `A`. -/
theorem card_vertices_lollipopInsertion :
    (A.lollipopInsertion i c).vertices.card = A.vertices.card + 2 := by
  have hne : ({Sum.inr 0, Sum.inr 1, Sum.inr 2} : Finset (H ⊕ Fin 4)) ≠ {Sum.inr 3} := by
    intro h
    have : (Sum.inr 0 : H ⊕ Fin 4) ∈ ({Sum.inr 3} : Finset (H ⊕ Fin 4)) := h ▸ by simp
    simp at this
  rw [lollipopInsertion_vertices, card_union_of_disjoint, card_image_of_injective _
    (Finset.map_injective _), card_pair hne]
  rw [disjoint_left]
  rintro _ hv hv'
  obtain ⟨_, hw, rfl⟩ := mem_image.1 hv
  obtain ⟨x, rfl⟩ := A.mem_vertices.1 hw
  have hx : (Sum.inl x : H ⊕ Fin 4) ∈ (A.vertexOf x).map Function.Embedding.inl :=
    mem_map_of_mem _ (A.self_mem_vertexOf x)
  simp only [mem_insert, mem_singleton] at hv'
  rcases hv' with h | h <;> rw [h] at hx <;> simp at hx

/-- `I_i(A, c)` has two edges more than `A`, when `d ↦ d̄` is a fixed-point-free involution. -/
theorem card_edges_lollipopInsertion (hinv : Function.Involutive A.inv)
    (hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i) (hfix : ∀ x, A.inv x ≠ x) :
    (A.lollipopInsertion i c).edges.card = A.edges.card + 2 := by
  have h1 := (A.lollipopInsertion i c).card_eq_two_mul_card_edges
    (lollipopInsertion_inv_involutive c hinv hh) ((lollipopInsertion_inv_ne_iff c hinv hh).2 hfix)
  have h2 := A.card_eq_two_mul_card_edges hinv hfix
  simp only [Fintype.card_sum, Fintype.card_fin] at h1
  omega

/-! #### The exterior -/

omit [Fintype H] in
/-- A dart of `A` lies in the exterior of `I_i(A, c)` iff it lies in the exterior of `A`. -/
@[simp]
theorem mem_lollipopInsertion_exterior_inl {x : H} :
    Sum.inl x ∈ (A.lollipopInsertion i c).exterior ↔ x ∈ A.exterior := by
  simp [DiskMap.mem_exterior]

omit [Fintype H] in
/-- The only new dart in the exterior of `I_i(A, c)` is `e₂`. -/
@[simp]
theorem mem_lollipopInsertion_exterior_inr {k : Fin 4} :
    Sum.inr k ∈ (A.lollipopInsertion i c).exterior ↔ k = 1 := by
  rcases fin_four_cases k with rfl | rfl | rfl | rfl <;> simp [DiskMap.mem_exterior]

end RotationSystem

/-! #### Plabic graphs -/

section Plabic

variable {A i}

/-- The dart `h` of `A`. -/
local notation "𝔥" => A.lollipopArc i

omit [NeZero b] in
/-- In a plabic graph, the only dart of the exterior at `β(k)` is `σ⁻¹(g_k)`. -/
theorem IsPlabicGraph.eq_rot_symm_leg_of_mem_exterior (hA : A.IsPlabicGraph) {d : H} {k : Fin b}
    (hd : d ∈ A.exterior) (hdk : d ∈ A.bvertex k) : d = A.rot.symm (A.leg k) := by
  have hv : A.IsBoundaryVertex (A.vertexOf (A.leg k)) :=
    A.vertexOf_mem_boundaryVertices.1 (hA.bvertex_mem k)
  rw [PlabicData.bvertex] at hdk
  have hr : A.rot d ∈ A.vertexOf (A.leg k) := by
    rw [RotationSystem.mem_vertexOf] at hdk ⊢
    exact sameCycle_apply_right.2 hdk
  have := DiskMap.eq_of_notMem_bdry hA.boundaryVertex_card hv hr (A.self_mem_vertexOf _)
    (A.mem_exterior.1 hd).2 (hA.leg_notMem_bdry k)
  rw [← this, Equiv.symm_apply_apply]

omit [NeZero b] in
/-- In a plabic graph, `σ⁻¹(g_k)` is the dart of the exterior at `β(k)`. -/
theorem IsPlabicGraph.rot_symm_leg_mem_exterior (hA : A.IsPlabicGraph) (k : Fin b) :
    A.rot.symm (A.leg k) ∈ A.exterior := by
  have hv : A.IsBoundaryVertex (A.vertexOf (A.leg k)) :=
    A.vertexOf_mem_boundaryVertices.1 (hA.bvertex_mem k)
  refine A.mem_exterior.2 ⟨?_, by rw [Equiv.apply_symm_apply]; exact hA.leg_notMem_bdry k⟩
  by_contra hB
  have := DiskMap.eq_of_notMem_bdry hA.boundaryVertex_card hv (A.rot_symm_mem_vertexOf _)
    (A.self_mem_vertexOf _) hB (hA.leg_notMem_bdry k)
  apply DiskMap.rot_ne_of_isBoundaryVertex hA.boundaryVertex_card hv
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

/-- In a plabic graph, `h` lies in the exterior. -/
theorem IsPlabicGraph.lollipopArc_mem_exterior (hA : A.IsPlabicGraph) : 𝔥 ∈ A.exterior :=
  hA.rot_symm_leg_mem_exterior _

/-- In a plabic graph, `h̄` does not lie in the exterior. -/
theorem IsPlabicGraph.inv_lollipopArc_notMem_exterior (hA : A.IsPlabicGraph) :
    A.inv 𝔥 ∉ A.exterior := fun h' =>
  disjoint_left.1 hA.toIsDiskMap.disjoint_exterior_map_inv h'
    (by simpa using hA.lollipopArc_mem_exterior)

/-- `h` lies at `β(i')`. -/
theorem lollipopArc_mem_bvertex : 𝔥 ∈ A.bvertex (insertionNext i) :=
  A.rot_symm_mem_vertexOf _

/-- The boundary vertex `β(i)` of `I_i(A, c)` is `ν = (e₁ e₂ g°)`. -/
theorem lollipopInsertion_bvertex_self :
    (A.lollipopInsertion i c).bvertex i = {Sum.inr 0, Sum.inr 1, Sum.inr 2} := by
  rw [PlabicData.bvertex, lollipopInsertion_leg_self,
    lollipopInsertion_vertexOf_inr_of_ne (k := 2) c (by decide)]

/-- The boundary vertex `β(j⁺)` of `I_i(A, c)` is the boundary vertex `β(j)` of `A`. -/
theorem lollipopInsertion_bvertex_succAbove (j : Fin b) :
    (A.lollipopInsertion i c).bvertex (i.succAbove j) =
      (A.bvertex j).map Function.Embedding.inl := by
  rw [PlabicData.bvertex, lollipopInsertion_leg_succAbove, lollipopInsertion_vertexOf_inl]
  rfl

private theorem mem_map_inv_iff {X : Type*} {M : DiskMap X}
    (hinv : Function.Involutive M.inv) {s : Finset X} {d : X} :
    d ∈ s.map M.inv.toEmbedding ↔ M.inv d ∈ s := by
  rw [mem_map_equiv]
  have : M.inv.symm d = M.inv d := by rw [Equiv.symm_apply_eq, hinv]
  rw [this]

private theorem union_eq_bdry_iff {X : Type*} [DecidableEq X] (M : DiskMap X)
    (hinv : Function.Involutive M.inv) :
    M.exterior ∪ M.exterior.map M.inv.toEmbedding = M.bdry ↔
      ∀ d, d ∈ M.bdry ↔ (d ∈ M.exterior ∨ M.inv d ∈ M.exterior) := by
  rw [Finset.ext_iff]
  refine forall_congr' fun d => ?_
  rw [mem_union, mem_map_inv_iff hinv]
  exact Iff.comm

private theorem disjoint_map_inv_iff {X : Type*} [DecidableEq X] (M : DiskMap X)
    (hinv : Function.Involutive M.inv) :
    Disjoint M.exterior (M.exterior.map M.inv.toEmbedding) ↔
      ∀ d, d ∈ M.exterior → M.inv d ∉ M.exterior := by
  rw [disjoint_left]
  refine forall_congr' fun d => ?_
  rw [mem_map_inv_iff hinv]

private theorem mem_faceOrbits_iff_eq_faceOf {X : Type*} [Fintype X] [DecidableEq X]
    (R : RotationSystem X) {s : Finset X} {d : X} (hd : d ∈ s) :
    s ∈ R.faceOrbits ↔ s = R.faceOf d := by
  constructor
  · intro hs
    obtain ⟨d₀, rfl⟩ := R.mem_faceOrbits.1 hs
    exact (R.faceOf_eq_of_mem hd).symm
  · rintro rfl
    exact R.faceOf_mem_faceOrbits d

omit [Fintype H] in
private theorem card_filter_map_inl (s : Finset H) :
    ((s.map Function.Embedding.inl).filter (· ∈ (A.lollipopInsertion i c).bdry)).card =
      (s.filter (· ∈ A.bdry)).card := by
  rw [filter_map, card_map]
  exact congrArg Finset.card (filter_congr fun x _ => by simp)

/-- The conditions on boundary vertices hold for `I_i(A, c)` iff they hold for `A`. -/
theorem boundaryVertex_card_lollipopInsertion_iff :
    (∀ v ∈ (A.lollipopInsertion i c).boundaryVertices,
      v.card = 3 ∧ (v.filter (· ∈ (A.lollipopInsertion i c).bdry)).card = 2) ↔
      ∀ v ∈ A.boundaryVertices, v.card = 3 ∧ (v.filter (· ∈ A.bdry)).card = 2 := by
  constructor
  · intro hI v hv
    obtain ⟨hvV, hvB⟩ := A.mem_boundaryVertices.1 hv
    obtain ⟨x, rfl⟩ := A.mem_vertices.1 hvV
    have := hI _ ((A.lollipopInsertion i c).vertexOf_mem_boundaryVertices.2
      ((isBoundaryVertex_lollipopInsertion_vertexOf_inl c x).2 hvB))
    rwa [lollipopInsertion_vertexOf_inl, card_map, card_filter_map_inl] at this
  · intro hA v hv
    obtain ⟨hvV, hvB⟩ := (A.lollipopInsertion i c).mem_boundaryVertices.1 hv
    obtain ⟨z, rfl⟩ := (A.lollipopInsertion i c).mem_vertices.1 hvV
    rcases z with x | k
    · rw [isBoundaryVertex_lollipopInsertion_vertexOf_inl] at hvB
      rw [lollipopInsertion_vertexOf_inl, card_map, card_filter_map_inl]
      exact hA _ (A.vertexOf_mem_boundaryVertices.2 hvB)
    · by_cases hk : k = 3
      · subst hk
        exact absurd hvB (not_isBoundaryVertex_lollipopInsertion_vertexOf_inr_three c)
      · rw [lollipopInsertion_vertexOf_inr_of_ne c hk]
        have hf : ({Sum.inr 0, Sum.inr 1, Sum.inr 2} : Finset (H ⊕ Fin 4)).filter
            (· ∈ (A.lollipopInsertion i c).bdry) = {Sum.inr 0, Sum.inr 1} := by
          ext z
          simp only [mem_filter, mem_insert, mem_singleton]
          constructor
          · rintro ⟨h | h | h, hz⟩ <;> subst h <;> simp_all
          · rintro (h | h) <;> subst h <;> simp
        rw [hf]
        constructor
        · rw [card_insert_of_notMem (by simp : (Sum.inr 0 : H ⊕ Fin 4) ∉
            ({Sum.inr 1, Sum.inr 2} : Finset (H ⊕ Fin 4))),
            card_pair (by simp : (Sum.inr 1 : H ⊕ Fin 4) ≠ Sum.inr 2)]
        · exact card_pair (by simp)

/-- The colouring of `I_i(A, c)` is constant on internal vertices iff that of `A` is. -/
theorem colour_rot_lollipopInsertion_iff :
    (∀ z, ¬(A.lollipopInsertion i c).IsBoundaryVertex ((A.lollipopInsertion i c).vertexOf z) →
      (A.lollipopInsertion i c).colour ((A.lollipopInsertion i c).rot z) =
        (A.lollipopInsertion i c).colour z) ↔
      ∀ x, ¬A.IsBoundaryVertex (A.vertexOf x) → A.colour (A.rot x) = A.colour x := by
  constructor
  · intro hI x hx
    simpa using hI (Sum.inl x) (by rwa [isBoundaryVertex_lollipopInsertion_vertexOf_inl])
  · intro hA z hz
    rcases z with x | k
    · rw [isBoundaryVertex_lollipopInsertion_vertexOf_inl] at hz
      simpa using hA x hz
    · rcases fin_four_cases k with rfl | rfl | rfl | rfl <;> simp

section Exterior

variable (hinv : Function.Involutive A.inv) (hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i)
  (hext : A.lollipopArc i ∈ A.exterior) (hext' : A.inv (A.lollipopArc i) ∉ A.exterior)

include hinv hh hext hext'

omit hinv hh in
omit [Fintype H] in
private theorem mem_exterior_iff_proj (z : H ⊕ Fin 4) :
    z ∈ (A.lollipopInsertion i c).exterior ↔ proj A i z ∈ A.exterior := by
  rcases z with x | k
  · simp
  · rcases fin_four_cases k with rfl | rfl | rfl | rfl <;> simp [hext, hext']

omit hext hext' in
private theorem mem_faceOf_inr_one_iff (z : H ⊕ Fin 4) :
    z ∈ (A.lollipopInsertion i c).faceOf (Sum.inr 1) ↔ proj A i z ∈ A.faceOf 𝔥 := by
  rw [RotationSystem.mem_faceOf, RotationSystem.mem_faceOf, sameCycle_facePerm_iff c hinv hh,
    proj_inr_one]

/-- The exterior of `I_i(A, c)` is an orbit of its face permutation iff that of `A` is. -/
theorem exterior_mem_faceOrbits_lollipopInsertion_iff :
    (A.lollipopInsertion i c).exterior ∈ (A.lollipopInsertion i c).faceOrbits ↔
      A.exterior ∈ A.faceOrbits := by
  rw [mem_faceOrbits_iff_eq_faceOf _ (d := Sum.inr 1) (by simp),
    mem_faceOrbits_iff_eq_faceOf _ hext, Finset.ext_iff, Finset.ext_iff]
  constructor
  · intro h x
    have := h (Sum.inl x)
    rwa [mem_exterior_iff_proj c hext hext', mem_faceOf_inr_one_iff c hinv hh,
      proj_inl] at this
  · intro h z
    rw [mem_exterior_iff_proj c hext hext', mem_faceOf_inr_one_iff c hinv hh]
    exact h _

omit [Fintype H] in
/-- The boundary of `I_i(A, c)` is its exterior together with its reverse iff the same holds
for `A`. -/
theorem union_lollipopInsertion_iff :
    (∀ z, z ∈ (A.lollipopInsertion i c).bdry ↔ (z ∈ (A.lollipopInsertion i c).exterior ∨
        (A.lollipopInsertion i c).inv z ∈ (A.lollipopInsertion i c).exterior)) ↔
      ∀ x, x ∈ A.bdry ↔ (x ∈ A.exterior ∨ A.inv x ∈ A.exterior) := by
  have hB := A.exterior_subset_bdry hext
  constructor
  · intro hI x
    by_cases h₁ : x = 𝔥
    · subst h₁
      simp [-DiskMap.mem_exterior, hext, hB]
    by_cases h₂ : x = A.inv 𝔥
    · subst h₂
      have := hI (Sum.inl (A.inv 𝔥))
      rw [lollipopInsertion_inv_inl_inv] at this
      simp only [mem_lollipopInsertion_bdry_inl, mem_lollipopInsertion_exterior_inr,
        mem_lollipopInsertion_exterior_inl, or_true, iff_true] at this
      simp [hinv 𝔥, hext, this]
    simpa [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂] using hI (Sum.inl x)
  · intro hA z
    rcases z with x | k
    · by_cases h₁ : x = 𝔥
      · subst h₁
        rw [lollipopInsertion_inv_inl_self c hh]
        simp [-DiskMap.mem_exterior, hext, hB]
      by_cases h₂ : x = A.inv 𝔥
      · subst h₂
        rw [lollipopInsertion_inv_inl_inv]
        simpa [hinv 𝔥, hext, hext'] using hA (A.inv 𝔥)
      rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂]
      simpa using hA x
    · rcases fin_four_cases k with rfl | rfl | rfl | rfl
      · rw [lollipopInsertion_inv_inr_zero' c hinv]
        simpa using hext
      · rw [lollipopInsertion_inv_inr_one c hh]
        simp
      · simp
      · simp

omit [Fintype H] in
omit hinv hext in
/-- The exterior of `I_i(A, c)` is disjoint from its reverse iff that of `A` is. -/
theorem disjoint_lollipopInsertion_iff :
    (∀ z, z ∈ (A.lollipopInsertion i c).exterior →
        (A.lollipopInsertion i c).inv z ∉ (A.lollipopInsertion i c).exterior) ↔
      ∀ x, x ∈ A.exterior → A.inv x ∉ A.exterior := by
  constructor
  · intro hI x hx
    by_cases h₁ : x = 𝔥
    · subst h₁
      exact hext'
    by_cases h₂ : x = A.inv 𝔥
    · subst h₂
      exact absurd hx hext'
    simpa [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂] using hI (Sum.inl x) (by simpa using hx)
  · intro hA z hz
    rcases z with x | k
    · by_cases h₁ : x = 𝔥
      · subst h₁
        rw [lollipopInsertion_inv_inl_self c hh]
        simp
      by_cases h₂ : x = A.inv 𝔥
      · subst h₂
        exact absurd (by simpa using hz) hext'
      rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂]
      simpa using hA x (by simpa using hz)
    · rcases fin_four_cases k with rfl | rfl | rfl | rfl
      · simp at hz
      · rw [lollipopInsertion_inv_inr_one c hh]
        simpa using hext'
      · simp at hz
      · simp at hz

end Exterior

end Plabic

end PlabicData

/-! ### The insertion of a lollipop is a plabic graph -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} [NeZero b]

/-- Euler's relation holds for `I_i(A, c)` iff it holds for `A`. -/
theorem euler_lollipopInsertion_iff {A : PlabicData H b} {i : Fin (b + 1)} (c : Shade)
    (hinv : Function.Involutive A.inv) (hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i)
    (hfix : ∀ x, A.inv x ≠ x) :
    ((A.lollipopInsertion i c).vertices.card : ℤ) - (A.lollipopInsertion i c).edges.card +
        (A.lollipopInsertion i c).faceOrbits.card = 2 ↔
      (A.vertices.card : ℤ) - A.edges.card + A.faceOrbits.card = 2 := by
  rw [card_vertices_lollipopInsertion, card_edges_lollipopInsertion c hinv hh hfix,
    card_faceOrbits_lollipopInsertion c hinv hh]
  push_cast
  constructor <;> intro h <;> linarith

/-- The boundary darts of `I_i(A, c)` are closed under the involution. -/
theorem IsPlabicGraph.inv_mem_bdry_lollipopInsertion {A : PlabicData H b}
    (hA : A.IsPlabicGraph) (i : Fin (b + 1)) (c : Shade) :
    ∀ z ∈ (A.lollipopInsertion i c).bdry,
      (A.lollipopInsertion i c).inv z ∈ (A.lollipopInsertion i c).bdry := by
  have hinv := hA.inv_involutive
  have hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i := hA.inv_ne _
  have hB := A.exterior_subset_bdry (hA.lollipopArc_mem_exterior (i := i))
  have hB' : A.inv (A.lollipopArc i) ∈ A.bdry := hA.inv_mem_bdry _ hB
  intro z hz
  rcases z with x | k
  · by_cases h₁ : x = A.lollipopArc i
    · subst h₁
      rw [lollipopInsertion_inv_inl_self c hh]
      simp
    by_cases h₂ : x = A.inv (A.lollipopArc i)
    · subst h₂
      rw [lollipopInsertion_inv_inl_inv]
      simp
    rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂]
    simpa using hA.inv_mem_bdry x (by simpa using hz)
  · rcases fin_four_cases k with rfl | rfl | rfl | rfl
    · rw [lollipopInsertion_inv_inr_zero' c hinv]
      simpa using hB
    · rw [lollipopInsertion_inv_inr_one c hh]
      simpa using hB'
    · simp at hz
    · simp at hz

/-- The boundary labelling of `I_i(A, c)` is injective. -/
theorem IsPlabicGraph.bvertex_injective_lollipopInsertion {A : PlabicData H b}
    (hA : A.IsPlabicGraph) (i : Fin (b + 1)) (c : Shade) :
    Function.Injective (A.lollipopInsertion i c).bvertex := by
  have hne : ∀ j : Fin b, (A.lollipopInsertion i c).bvertex i ≠
      (A.lollipopInsertion i c).bvertex (i.succAbove j) := by
    intro j h
    rw [lollipopInsertion_bvertex_self, lollipopInsertion_bvertex_succAbove] at h
    have : (Sum.inr 0 : H ⊕ Fin 4) ∈ (A.bvertex j).map Function.Embedding.inl :=
      h ▸ by simp
    simp at this
  intro k k' hkk'
  rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, rfl⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove i k' with hk' | ⟨j', rfl⟩
  · rw [hk, hk']
  · rw [hk] at hkk'
    exact absurd hkk' (hne j')
  · rw [hk'] at hkk'
    exact absurd hkk'.symm (hne j)
  · rw [lollipopInsertion_bvertex_succAbove, lollipopInsertion_bvertex_succAbove] at hkk'
    rw [hA.bvertex_injective (Finset.map_injective _ hkk')]

/-- The boundary labelling of `I_i(A, c)` is onto the boundary vertices. -/
theorem IsPlabicGraph.exists_bvertex_eq_lollipopInsertion {A : PlabicData H b}
    (hA : A.IsPlabicGraph) (i : Fin (b + 1)) (c : Shade) :
    ∀ v ∈ (A.lollipopInsertion i c).boundaryVertices,
      ∃ k, (A.lollipopInsertion i c).bvertex k = v := by
  intro v hv
  obtain ⟨hvV, hvB⟩ := (A.lollipopInsertion i c).mem_boundaryVertices.1 hv
  obtain ⟨z, rfl⟩ := (A.lollipopInsertion i c).mem_vertices.1 hvV
  rcases z with x | k
  · rw [isBoundaryVertex_lollipopInsertion_vertexOf_inl] at hvB
    obtain ⟨j, hj⟩ := hA.exists_bvertex_eq _ (A.vertexOf_mem_boundaryVertices.2 hvB)
    exact ⟨i.succAbove j, by
      rw [lollipopInsertion_bvertex_succAbove, hj, lollipopInsertion_vertexOf_inl]⟩
  · by_cases hk : k = 3
    · subst hk
      exact absurd hvB (not_isBoundaryVertex_lollipopInsertion_vertexOf_inr_three c)
    · exact ⟨i, by rw [lollipopInsertion_bvertex_self, lollipopInsertion_vertexOf_inr_of_ne c hk]⟩

/-- The boundary vertices of `I_i(A, c)` are labelled clockwise. -/
theorem IsPlabicGraph.exists_exterior_lollipopInsertion {A : PlabicData H b}
    (hA : A.IsPlabicGraph) (i : Fin (b + 1)) (c : Shade) :
    ∀ k, ∃ d ∈ (A.lollipopInsertion i c).exterior,
      d ∈ (A.lollipopInsertion i c).bvertex (finRotate (b + 1) k) ∧
      (A.lollipopInsertion i c).inv d ∈ (A.lollipopInsertion i c).bvertex k := by
  have hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i := hA.inv_ne _
  have hext := hA.lollipopArc_mem_exterior (i := i)
  have hext' := hA.inv_lollipopArc_notMem_exterior (i := i)
  intro k
  rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, rfl⟩
  · rw [hk]
    refine ⟨Sum.inl (A.lollipopArc i), by simpa using hext, ?_, ?_⟩
    · rw [finRotate_eq_succAbove_insertionNext, lollipopInsertion_bvertex_succAbove]
      simpa using lollipopArc_mem_bvertex
    · rw [lollipopInsertion_inv_inl_self c hh, lollipopInsertion_bvertex_self]
      simp
  · obtain ⟨d, hd, hdv, hdv'⟩ := hA.exists_exterior j
    rcases finRotate_succAbove i j with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2] at hdv
      obtain rfl : d = A.lollipopArc i := hA.eq_rot_symm_leg_of_mem_exterior hd hdv
      refine ⟨Sum.inr 1, by simp, ?_, ?_⟩
      · rw [h1, lollipopInsertion_bvertex_self]
        simp
      · rw [lollipopInsertion_inv_inr_one c hh, lollipopInsertion_bvertex_succAbove]
        simpa using hdv'
    · refine ⟨Sum.inl d, by simpa using hd, ?_, ?_⟩
      · rw [h1, lollipopInsertion_bvertex_succAbove]
        simpa using hdv
      · have hne1 : d ≠ A.lollipopArc i := by
          rintro rfl
          exact h2 (hA.bvertex_injective ((A.vertexOf_eq_of_mem hdv).symm.trans
            (A.vertexOf_eq_of_mem lollipopArc_mem_bvertex)))
        have hne2 : d ≠ A.inv (A.lollipopArc i) := by
          rintro rfl
          exact hext' hd
        rw [lollipopInsertion_inv_inl_of_ne A i c hne1 hne2, lollipopInsertion_bvertex_succAbove]
        simpa using hdv'

/-- **An insertion is a plabic graph**: if `A` is a plabic graph with `b ≥ 1` boundary vertices,
then `I_i(A, c)` is a plabic graph with `b + 1` boundary vertices. -/
@[cluster_algebras "lem_lollipop_insertion_plabic"]
theorem IsPlabicGraph.lollipopInsertion {A : PlabicData H b} (hA : A.IsPlabicGraph)
    (i : Fin (b + 1)) (c : Shade) : (A.lollipopInsertion i c).IsPlabicGraph := by
  have hinv := hA.inv_involutive
  have hh : A.inv (A.lollipopArc i) ≠ A.lollipopArc i := hA.inv_ne _
  have hext := hA.lollipopArc_mem_exterior (i := i)
  have hext' := hA.inv_lollipopArc_notMem_exterior (i := i)
  have hIinv := lollipopInsertion_inv_involutive c hinv hh
  refine ⟨⟨(isConnected_lollipopInsertion_iff c hinv hh).2 hA.toIsConnected,
    hA.inv_mem_bdry_lollipopInsertion i c,
    (euler_lollipopInsertion_iff c hinv hh hA.inv_ne).2 hA.euler,
    (boundaryVertex_card_lollipopInsertion_iff c).2 hA.boundaryVertex_card,
    ⟨_, (exterior_mem_faceOrbits_lollipopInsertion_iff c hinv hh hext hext').2
      hA.toIsDiskMap.exterior_mem_faceOrbits,
      (A.lollipopInsertion i c).exterior_subset_bdry,
      (union_eq_bdry_iff (A.lollipopInsertion i c).toDiskMap hIinv).2
        ((union_lollipopInsertion_iff c hinv hh hext hext').2
          ((union_eq_bdry_iff A.toDiskMap hinv).1 hA.toIsDiskMap.exterior_union_map_inv)),
      (disjoint_map_inv_iff (A.lollipopInsertion i c).toDiskMap hIinv).2
        ((disjoint_lollipopInsertion_iff c hh hext').2
          ((disjoint_map_inv_iff A.toDiskMap hinv).1
            hA.toIsDiskMap.disjoint_exterior_map_inv))⟩⟩,
    by omega, (colour_rot_lollipopInsertion_iff c).2 hA.colour_rot, ?_, ?_,
    hA.bvertex_injective_lollipopInsertion i c, hA.exists_bvertex_eq_lollipopInsertion i c,
    hA.exists_exterior_lollipopInsertion i c⟩
  · -- the legs lie outside `B`
    intro k
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · simp
    · simpa using hA.leg_notMem_bdry j
  · -- the labelled vertices are boundary vertices
    intro k
    rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, rfl⟩
    · rw [hk, PlabicData.bvertex, lollipopInsertion_leg_self]
      exact (A.lollipopInsertion i c).vertexOf_mem_boundaryVertices.2
        (isBoundaryVertex_lollipopInsertion_vertexOf_inr_of_ne c (by decide))
    · rw [PlabicData.bvertex, lollipopInsertion_leg_succAbove]
      exact (A.lollipopInsertion i c).vertexOf_mem_boundaryVertices.2
        ((isBoundaryVertex_lollipopInsertion_vertexOf_inl c _).2
          (A.vertexOf_mem_boundaryVertices.1 (hA.bvertex_mem j)))

omit [Fintype H] in
/-- If the involution of `I_i(A, c)` is an involution, then `h̄ ≠ h`. -/
theorem lollipopArc_ne_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)} (c : Shade)
    (hI : Function.Involutive (A.lollipopInsertion i c).inv) :
    A.inv (A.lollipopArc i) ≠ A.lollipopArc i := by
  intro h
  have h1 : (A.lollipopInsertion i c).inv (Sum.inl (A.lollipopArc i)) = Sum.inr 1 := by
    simp [lollipopInsertion, h, swap_apply_of_ne_of_ne]
  have h2 : (A.lollipopInsertion i c).inv (Sum.inr 1) = Sum.inr 0 := by
    simp [lollipopInsertion, h, swap_apply_of_ne_of_ne]
  have := hI (Sum.inl (A.lollipopArc i))
  rw [h1, h2] at this
  exact Sum.inr_ne_inl this

omit [Fintype H] in
/-- If the involution of `I_i(A, c)` is an involution, so is that of `A`. -/
theorem inv_involutive_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)} (c : Shade)
    (hI : Function.Involutive (A.lollipopInsertion i c).inv) : Function.Involutive A.inv := by
  have hh := lollipopArc_ne_of_lollipopInsertion c hI
  have h𝔥 : A.inv (A.inv (A.lollipopArc i)) = A.lollipopArc i := by
    have := hI (Sum.inl (A.lollipopArc i))
    rw [lollipopInsertion_inv_inl_self c hh, lollipopInsertion_inv_inr_zero] at this
    exact Sum.inl_injective this
  intro x
  by_cases h₁ : x = A.lollipopArc i
  · subst h₁
    exact h𝔥
  by_cases h₂ : x = A.inv (A.lollipopArc i)
  · subst h₂
    rw [h𝔥]
  have := hI (Sum.inl x)
  rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂] at this
  by_cases h₃ : A.inv x = A.lollipopArc i
  · rw [h₃, lollipopInsertion_inv_inl_self c hh] at this
    simp at this
  by_cases h₄ : A.inv x = A.inv (A.lollipopArc i)
  · rw [h₄, lollipopInsertion_inv_inl_inv] at this
    simp at this
  rw [lollipopInsertion_inv_inl_of_ne A i c h₃ h₄] at this
  exact Sum.inl_injective this

/-- If `I_i(A, c)` is a plabic graph, the legs of `A` are not in `B`. -/
theorem leg_notMem_bdry_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)} {c : Shade}
    (hI : (A.lollipopInsertion i c).IsPlabicGraph) (j : Fin b) : A.leg j ∉ A.bdry := by
  simpa [lollipopInsertion_leg_succAbove] using hI.leg_notMem_bdry (i.succAbove j)

/-- If `I_i(A, c)` is a plabic graph, the dart `h` lies in the exterior of `A`. -/
theorem lollipopArc_mem_exterior_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)}
    {c : Shade} (hI : (A.lollipopInsertion i c).IsPlabicGraph) :
    A.lollipopArc i ∈ A.exterior := by
  refine A.mem_exterior.2 ⟨?_, ?_⟩
  · simpa [lollipopInsertion_inv_inr_zero' c (inv_involutive_of_lollipopInsertion c
      hI.inv_involutive)] using hI.inv_mem_bdry (Sum.inr 0) (by simp)
  · rw [lollipopArc, Equiv.apply_symm_apply]
    exact leg_notMem_bdry_of_lollipopInsertion hI _

/-- If `I_i(A, c)` is a plabic graph, the partner `h̄` of `h` is not in the exterior of `A`. -/
theorem inv_lollipopArc_notMem_exterior_of_lollipopInsertion {A : PlabicData H b}
    {i : Fin (b + 1)} {c : Shade} (hI : (A.lollipopInsertion i c).IsPlabicGraph) :
    A.inv (A.lollipopArc i) ∉ A.exterior := by
  have := disjoint_left.1 hI.toIsDiskMap.disjoint_exterior_map_inv
    (show Sum.inr 1 ∈ (A.lollipopInsertion i c).exterior by simp)
  rw [mem_map_inv_iff hI.inv_involutive,
    lollipopInsertion_inv_inr_one c (lollipopArc_ne_of_lollipopInsertion c hI.inv_involutive)]
    at this
  simpa using this

/-- If `I_i(A, c)` is a plabic graph, the labelling `β` of `A` is injective. -/
theorem bvertex_injective_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)}
    {c : Shade} (hI : (A.lollipopInsertion i c).IsPlabicGraph) :
    Function.Injective A.bvertex := by
  intro j j' h
  apply Fin.succAbove_right_injective (p := i)
  apply hI.bvertex_injective
  rw [lollipopInsertion_bvertex_succAbove, lollipopInsertion_bvertex_succAbove, h]

/-- If `I_i(A, c)` is a plabic graph, the boundary darts of `A` are closed under `d ↦ d̄`. -/
theorem inv_mem_bdry_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)} {c : Shade}
    (hI : (A.lollipopInsertion i c).IsPlabicGraph) : ∀ x ∈ A.bdry, A.inv x ∈ A.bdry := by
  have hh := lollipopArc_ne_of_lollipopInsertion c hI.inv_involutive
  intro x hx
  by_cases h₁ : x = A.lollipopArc i
  · subst h₁
    have := hI.inv_mem_bdry (Sum.inr 1) (by simp)
    rw [lollipopInsertion_inv_inr_one c hh] at this
    simpa using this
  by_cases h₂ : x = A.inv (A.lollipopArc i)
  · subst h₂
    rw [inv_involutive_of_lollipopInsertion c hI.inv_involutive]
    exact (A.mem_exterior.1 (lollipopArc_mem_exterior_of_lollipopInsertion hI)).1
  have := hI.inv_mem_bdry (Sum.inl x) (by simpa using hx)
  rw [lollipopInsertion_inv_inl_of_ne A i c h₁ h₂] at this
  simpa using this

/-- If `I_i(A, c)` is a plabic graph, each `β(j)` of `A` is a boundary vertex. -/
theorem bvertex_mem_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)} {c : Shade}
    (hI : (A.lollipopInsertion i c).IsPlabicGraph) (j : Fin b) :
    A.bvertex j ∈ A.boundaryVertices := by
  have := hI.bvertex_mem (i.succAbove j)
  rw [PlabicData.bvertex, lollipopInsertion_leg_succAbove] at this
  exact A.vertexOf_mem_boundaryVertices.2 ((isBoundaryVertex_lollipopInsertion_vertexOf_inl c _).1
    ((A.lollipopInsertion i c).vertexOf_mem_boundaryVertices.1 this))

/-- If `I_i(A, c)` is a plabic graph, the labelling `β` of `A` is onto the boundary vertices. -/
theorem exists_bvertex_eq_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)}
    {c : Shade} (hI : (A.lollipopInsertion i c).IsPlabicGraph) :
    ∀ v ∈ A.boundaryVertices, ∃ j, A.bvertex j = v := by
  intro v hv
  obtain ⟨hvV, hvB⟩ := A.mem_boundaryVertices.1 hv
  obtain ⟨x, rfl⟩ := A.mem_vertices.1 hvV
  obtain ⟨k, hk⟩ := hI.exists_bvertex_eq _
    ((A.lollipopInsertion i c).vertexOf_mem_boundaryVertices.2
    ((isBoundaryVertex_lollipopInsertion_vertexOf_inl c x).2 hvB))
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · rw [lollipopInsertion_bvertex_self, lollipopInsertion_vertexOf_inl] at hk
    have : (Sum.inr 0 : H ⊕ Fin 4) ∈ (A.vertexOf x).map Function.Embedding.inl :=
      hk ▸ by simp
    simp at this
  · rw [lollipopInsertion_bvertex_succAbove, lollipopInsertion_vertexOf_inl] at hk
    exact ⟨j, Finset.map_injective _ hk⟩

/-- If `I_i(A, c)` is a plabic graph, the boundary vertices of `A` are labelled clockwise. -/
theorem exists_exterior_of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)}
    {c : Shade} (hI : (A.lollipopInsertion i c).IsPlabicGraph) (j : Fin b) :
    ∃ d ∈ A.exterior, d ∈ A.bvertex (finRotate b j) ∧ A.inv d ∈ A.bvertex j := by
  have hh := lollipopArc_ne_of_lollipopInsertion c hI.inv_involutive
  obtain ⟨d, hd, hdv, hdv'⟩ := hI.exists_exterior (i.succAbove j)
  rcases finRotate_succAbove i j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, lollipopInsertion_bvertex_self] at hdv
    have hd1 : d = Sum.inr 1 := by
      simp only [mem_insert, mem_singleton] at hdv
      rcases hdv with rfl | rfl | rfl
      · simp at hd
      · rfl
      · simp at hd
    subst hd1
    rw [lollipopInsertion_inv_inr_one c hh, lollipopInsertion_bvertex_succAbove] at hdv'
    refine ⟨A.lollipopArc i, lollipopArc_mem_exterior_of_lollipopInsertion hI, ?_,
      by simpa using hdv'⟩
    rw [h2]
    exact lollipopArc_mem_bvertex
  · rw [h1, lollipopInsertion_bvertex_succAbove] at hdv
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hdv
    have hxe : x ∈ A.exterior := by simpa using hd
    have hne2 : x ≠ A.inv (A.lollipopArc i) := by
      rintro rfl
      exact inv_lollipopArc_notMem_exterior_of_lollipopInsertion hI hxe
    have hne1 : x ≠ A.lollipopArc i := by
      rintro rfl
      exact h2 (bvertex_injective_of_lollipopInsertion hI ((A.vertexOf_eq_of_mem hx).symm.trans
        (A.vertexOf_eq_of_mem lollipopArc_mem_bvertex)))
    refine ⟨x, hxe, hx, ?_⟩
    rw [Function.Embedding.inl_apply, lollipopInsertion_inv_inl_of_ne A i c hne1 hne2,
      lollipopInsertion_bvertex_succAbove] at hdv'
    simpa using hdv'

/-- **The converse of the insertion lemma**: if `I_i(A, c)` is a plabic graph, so is `A`. -/
theorem IsPlabicGraph.of_lollipopInsertion {A : PlabicData H b} {i : Fin (b + 1)} {c : Shade}
    (hI : (A.lollipopInsertion i c).IsPlabicGraph) : A.IsPlabicGraph := by
  have hIinv := hI.inv_involutive
  have hinv := inv_involutive_of_lollipopInsertion c hIinv
  have hh := lollipopArc_ne_of_lollipopInsertion c hIinv
  have hext := lollipopArc_mem_exterior_of_lollipopInsertion hI
  have hext' := inv_lollipopArc_notMem_exterior_of_lollipopInsertion hI
  refine ⟨⟨(isConnected_lollipopInsertion_iff c hinv hh).1 hI.toIsConnected,
    inv_mem_bdry_of_lollipopInsertion hI,
    (euler_lollipopInsertion_iff c hinv hh ((lollipopInsertion_inv_ne_iff c hinv hh).1
      hI.inv_ne)).1 hI.euler,
    (boundaryVertex_card_lollipopInsertion_iff c).1 hI.boundaryVertex_card,
    ⟨_, (exterior_mem_faceOrbits_lollipopInsertion_iff c hinv hh hext hext').1
      hI.toIsDiskMap.exterior_mem_faceOrbits,
      A.exterior_subset_bdry,
      (union_eq_bdry_iff A.toDiskMap hinv).2
        ((union_lollipopInsertion_iff c hinv hh hext hext').1
          ((union_eq_bdry_iff (A.lollipopInsertion i c).toDiskMap hIinv).1
            hI.toIsDiskMap.exterior_union_map_inv)),
      (disjoint_map_inv_iff A.toDiskMap hinv).2
        ((disjoint_lollipopInsertion_iff c hh hext').1
          ((disjoint_map_inv_iff (A.lollipopInsertion i c).toDiskMap hIinv).1
            hI.toIsDiskMap.disjoint_exterior_map_inv))⟩⟩,
    Nat.pos_of_ne_zero (NeZero.ne b), (colour_rot_lollipopInsertion_iff c).1 hI.colour_rot,
    leg_notMem_bdry_of_lollipopInsertion hI, bvertex_mem_of_lollipopInsertion hI,
    bvertex_injective_of_lollipopInsertion hI, exists_bvertex_eq_of_lollipopInsertion hI,
    exists_exterior_of_lollipopInsertion hI⟩

/-- `I_i(A, c)` is a plabic graph exactly when `A` is. -/
theorem isPlabicGraph_lollipopInsertion_iff {A : PlabicData H b} {i : Fin (b + 1)} {c : Shade} :
    (A.lollipopInsertion i c).IsPlabicGraph ↔ A.IsPlabicGraph :=
  ⟨IsPlabicGraph.of_lollipopInsertion, fun hA => hA.lollipopInsertion i c⟩

/-- **An insertion is a plabic graph**: `I_i(A, c)` has as many faces as `A`. -/
@[cluster_algebras "lem_lollipop_insertion_plabic"]
theorem card_faces_lollipopInsertion {A : PlabicData H b} (hA : A.IsPlabicGraph)
    (i : Fin (b + 1)) (c : Shade) : (A.lollipopInsertion i c).faces.card = A.faces.card := by
  have hI := hA.lollipopInsertion i c
  rw [DiskMap.faces, DiskMap.faces, card_erase_of_mem hI.toIsDiskMap.exterior_mem_faceOrbits,
    card_erase_of_mem hA.toIsDiskMap.exterior_mem_faceOrbits,
    card_faceOrbits_lollipopInsertion c hA.inv_involutive (hA.inv_ne _)]

/-- **An insertion is a plabic graph**: `{ḡ°}` is a lollipop of colour `c` at the label `i` of
`I_i(A, c)`. -/
@[cluster_algebras "lem_lollipop_insertion_plabic"]
theorem isLollipopOfColour_lollipopInsertion (A : PlabicData H b) (i : Fin (b + 1)) (c : Shade) :
    (A.lollipopInsertion i c).IsLollipopOfColour i c {Sum.inr 3} := by
  refine ⟨⟨⟨?_, by simp⟩, Sum.inr 3, mem_singleton_self _, ?_⟩, ?_⟩
  · rw [← lollipopInsertion_vertexOf_inr_three (A := A) (i := i) (c := c)]
    exact (A.lollipopInsertion i c).vertexOf_mem_internalVertices.2
      (not_isBoundaryVertex_lollipopInsertion_vertexOf_inr_three c)
  · rw [lollipopInsertion_inv_inr_three, lollipopInsertion_bvertex_self]
    simp
  · intro d hd
    rw [mem_singleton] at hd
    subst hd
    rfl

end PlabicData

/-! ### Transporting plabic graphs along isomorphisms -/

/-- A bijection intertwining two permutations of finite sets matches their orbits. -/
private theorem sameCycle_iff_of_semiconj' {α β : Type*} [Finite α] [Finite β] {f : Perm α}
    {g : Perm β} (θ : α ≃ β) (h : ∀ x, θ (f x) = g (θ x)) {x y : α} :
    g.SameCycle (θ x) (θ y) ↔ f.SameCycle x y := by
  have hpow (n : ℕ) (x : α) : θ ((f ^ n) x) = (g ^ n) (θ x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, h, ih]
  constructor
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact θ.injective ((hpow n x).trans hn)
  · intro hxy
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← hpow, hn]⟩

/-- Two families of finite sets matched by a bijection have equally many members. -/
private theorem card_image_univ_of_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (θ : α ≃ β) (f : α → Finset α) (f' : β → Finset β)
    (h : ∀ d, (f d).map θ.toEmbedding = f' (θ d)) :
    (univ.image f').card = (univ.image f).card := by
  have : univ.image f' = (univ.image f).image (Finset.map θ.toEmbedding) := by
    rw [image_image]
    ext v
    simp only [mem_image, mem_univ, true_and, Function.comp_apply, h]
    constructor
    · rintro ⟨d', rfl⟩
      exact ⟨θ.symm d', by simp⟩
    · rintro ⟨d, rfl⟩
      exact ⟨θ d, rfl⟩
  rw [this, card_image_of_injective _ (Finset.map_injective _)]

namespace PlabicData

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}
  {G : PlabicData H b} {G' : PlabicData H' b}

namespace Iso

variable (θ : G.Iso G')

include θ

private theorem map_facePerm (d : H) : θ.toEquiv (G.facePerm d) = G'.facePerm (θ.toEquiv d) := by
  simp [θ.map_rot, θ.map_inv]

private theorem map_faceOf (d : H) :
    (G.faceOf d).map θ.toEquiv.toEmbedding = G'.faceOf (θ.toEquiv d) := by
  ext y
  rw [mem_map_equiv, RotationSystem.mem_faceOf, RotationSystem.mem_faceOf]
  conv_rhs => rw [← θ.toEquiv.apply_symm_apply y]
  rw [sameCycle_iff_of_semiconj' θ.toEquiv θ.map_facePerm]

private theorem map_edgeOf (d : H) :
    (G.edgeOf d).map θ.toEquiv.toEmbedding = G'.edgeOf (θ.toEquiv d) := by
  simp [RotationSystem.edgeOf, θ.map_inv]

private theorem card_vertices : G'.vertices.card = G.vertices.card :=
  card_image_univ_of_map θ.toEquiv _ _ θ.map_vertexOf

private theorem card_edges : G'.edges.card = G.edges.card :=
  card_image_univ_of_map θ.toEquiv _ _ θ.map_edgeOf

private theorem card_faceOrbits : G'.faceOrbits.card = G.faceOrbits.card :=
  card_image_univ_of_map θ.toEquiv _ _ θ.map_faceOf

private theorem reach {x y : H} (h : G.Reach x y) : G'.Reach (θ.toEquiv x) (θ.toEquiv y) := by
  induction h with
  | refl => exact RotationSystem.Reach.refl _
  | rot _ ih => rw [θ.map_rot]; exact ih.rot
  | inv _ ih => rw [θ.map_inv]; exact ih.inv

/-- For a plabic graph `G`, an isomorphism maps each labelled vertex `β(i)` onto `β'(i)`. -/
private theorem map_bvertex_of_notMem (i : Fin b) (hleg : G.leg i ∉ G.bdry) :
    (G.bvertex i).map θ.toEquiv.toEmbedding = G'.bvertex i := by
  have hmem : θ.toEquiv (G.leg i) ∈ G'.bvertex i := by
    have h2 : θ.toEquiv (G.leg i) ∈
        ((G.bvertex i).filter (· ∉ G.bdry)).map θ.toEquiv.toEmbedding :=
      mem_map_of_mem _ (mem_filter.2 ⟨G.leg_mem_bvertex i, hleg⟩)
    rw [θ.map_bvertex i] at h2
    exact (mem_filter.1 h2).1
  rw [PlabicData.bvertex, θ.map_vertexOf]
  exact G'.vertexOf_eq_of_mem hmem

/-- A tuple isomorphic to a connected tuple is connected. -/
theorem isConnected (hG : G.IsConnected) : G'.IsConnected := by
  set e := θ.toEquiv
  have hsymm : ∀ d', e (e.symm d') = d' := e.apply_symm_apply
  have hinv' : ∀ d', G'.inv d' = e (G.inv (e.symm d')) := fun d' => by
    rw [θ.map_inv, hsymm]
  refine RotationSystem.IsConnected.of_reach ⟨e (Classical.choice hG.nonempty)⟩ ?_ ?_ ?_
  · intro d'
    rw [hinv', hinv', Equiv.symm_apply_apply, hG.inv_involutive, hsymm]
  · intro d' h
    rw [hinv'] at h
    apply hG.inv_ne (e.symm d')
    apply e.injective
    rw [h, hsymm]
  · intro d' f'
    have := θ.reach (hG.reach (e.symm d') (e.symm f'))
    rwa [hsymm, hsymm] at this

private theorem boundaryVertex_card (hG : G.IsPlabicGraph) : ∀ v ∈ G'.boundaryVertices,
    v.card = 3 ∧ (v.filter (· ∈ G'.bdry)).card = 2 := by
  intro v' hv'
  obtain ⟨hvV, hvB⟩ := G'.mem_boundaryVertices.1 hv'
  obtain ⟨d', rfl⟩ := G'.mem_vertices.1 hvV
  obtain ⟨d, rfl⟩ : ∃ d, θ.toEquiv d = d' := ⟨θ.toEquiv.symm d', θ.toEquiv.apply_symm_apply d'⟩
  rw [θ.isBoundaryVertex_vertexOf_iff] at hvB
  obtain ⟨h3, h2⟩ := hG.boundaryVertex_card _ (G.vertexOf_mem_boundaryVertices.2 hvB)
  rw [← θ.map_vertexOf, card_map, filter_map, card_map]
  refine ⟨h3, ?_⟩
  rw [← h2]
  exact congrArg Finset.card (filter_congr fun x _ => θ.mem_bdry_iff x)

/-- The boundary labelling of a tuple isomorphic to a plabic graph is onto the boundary
vertices. -/
theorem exists_bvertex_eq (hG : G.IsPlabicGraph) :
    ∀ v ∈ G'.boundaryVertices, ∃ k, G'.bvertex k = v := by
  intro v' hv'
  obtain ⟨hvV, hvB⟩ := G'.mem_boundaryVertices.1 hv'
  obtain ⟨d', rfl⟩ := G'.mem_vertices.1 hvV
  obtain ⟨d, rfl⟩ : ∃ d, θ.toEquiv d = d' := ⟨θ.toEquiv.symm d', θ.toEquiv.apply_symm_apply d'⟩
  rw [θ.isBoundaryVertex_vertexOf_iff] at hvB
  obtain ⟨k, hk⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hvB)
  exact ⟨k, by rw [← θ.map_bvertex_of_notMem k (hG.leg_notMem_bdry k), hk, θ.map_vertexOf]⟩

/-- The boundary vertices of a tuple isomorphic to a plabic graph are labelled clockwise. -/
theorem exists_exterior (hG : G.IsPlabicGraph) :
    ∀ k, ∃ d ∈ G'.exterior, d ∈ G'.bvertex (finRotate b k) ∧ G'.inv d ∈ G'.bvertex k := by
  intro k
  obtain ⟨d, hd, hdv, hdv'⟩ := hG.exists_exterior k
  refine ⟨θ.toEquiv d, ?_, ?_, ?_⟩
  · rwa [← θ.map_exterior, mem_map_equiv, Equiv.symm_apply_apply]
  · rw [← θ.map_bvertex_of_notMem _ (hG.leg_notMem_bdry _)]
    exact mem_map_of_mem _ hdv
  · rw [← θ.map_inv, ← θ.map_bvertex_of_notMem _ (hG.leg_notMem_bdry _)]
    exact mem_map_of_mem _ hdv'

/-- **Plabic graphs are transported along isomorphisms**: a tuple isomorphic to a plabic graph,
whose chosen darts `leg i` lie outside `B`, is a plabic graph. (An isomorphism only matches the
darts of the labelled vertices outside `B`, so the condition on `leg i` is needed.) -/
theorem isPlabicGraph (hG : G.IsPlabicGraph) (hleg : ∀ i, G'.leg i ∉ G'.bdry) :
    G'.IsPlabicGraph := by
  set e := θ.toEquiv
  have hsymm : ∀ d', e (e.symm d') = d' := e.apply_symm_apply
  have hext : ∀ d, e d ∈ G'.exterior ↔ d ∈ G.exterior := by
    intro d
    rw [← θ.map_exterior, mem_map_equiv, Equiv.symm_apply_apply]
  have hbv : ∀ d, G'.IsBoundaryVertex (G'.vertexOf (e d)) ↔ G.IsBoundaryVertex (G.vertexOf d) :=
    θ.isBoundaryVertex_vertexOf_iff
  have hbvert : ∀ k, G'.bvertex k = (G.bvertex k).map e.toEmbedding := fun k =>
    (θ.map_bvertex_of_notMem k (hG.leg_notMem_bdry k)).symm
  have hconn := θ.isConnected hG.toIsConnected
  refine ⟨⟨hconn, ?_, ?_, θ.boundaryVertex_card hG,
    ⟨G'.exterior, ?_, G'.exterior_subset_bdry, ?_, ?_⟩⟩, hG.one_le, ?_, hleg, ?_, ?_,
    θ.exists_bvertex_eq hG, θ.exists_exterior hG⟩
  · intro d' hd'
    rw [show G'.inv d' = e (G.inv (e.symm d')) by rw [θ.map_inv, hsymm], θ.mem_bdry_iff]
    exact hG.inv_mem_bdry _ (by rwa [← θ.mem_bdry_iff, hsymm])
  · rw [θ.card_vertices, θ.card_edges, θ.card_faceOrbits]
    exact hG.euler
  · rw [← θ.map_exterior]
    obtain ⟨d₀, hd₀⟩ := G.mem_faceOrbits.1 hG.toIsDiskMap.exterior_mem_faceOrbits
    rw [← hd₀, θ.map_faceOf]
    exact G'.faceOf_mem_faceOrbits _
  · refine (union_eq_bdry_iff G'.toDiskMap hconn.inv_involutive).2 fun d' => ?_
    obtain ⟨d, rfl⟩ : ∃ d, e d = d' := ⟨e.symm d', hsymm d'⟩
    rw [θ.mem_bdry_iff, ← θ.map_inv, hext, hext]
    exact (union_eq_bdry_iff G.toDiskMap hG.inv_involutive).1
      hG.toIsDiskMap.exterior_union_map_inv d
  · refine (disjoint_map_inv_iff G'.toDiskMap hconn.inv_involutive).2 fun d' => ?_
    obtain ⟨d, rfl⟩ : ∃ d, e d = d' := ⟨e.symm d', hsymm d'⟩
    rw [← θ.map_inv, hext, hext]
    exact (disjoint_map_inv_iff G.toDiskMap hG.inv_involutive).1
      hG.toIsDiskMap.disjoint_exterior_map_inv d
  · intro d' hd'
    obtain ⟨d, rfl⟩ : ∃ d, e d = d' := ⟨e.symm d', hsymm d'⟩
    rw [hbv] at hd'
    rw [← θ.map_rot, θ.map_colour _ (by rwa [G.vertexOf_rot]), θ.map_colour _ hd',
      hG.colour_rot d hd']
  · intro k
    rw [hbvert, PlabicData.bvertex, θ.map_vertexOf]
    exact G'.vertexOf_mem_boundaryVertices.2
      ((hbv _).2 (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem k)))
  · intro k k' h
    rw [hbvert, hbvert] at h
    exact hG.bvertex_injective (Finset.map_injective _ h)

end Iso

end PlabicData

/-! ### Extracting a lollipop -/

namespace PlabicData

section Extraction

attribute [-simp] finRotate_apply

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} [NeZero b] {K : PlabicData H (b + 1)}
  {i : Fin (b + 1)} {c : Shade}

/-- The leg `g = g_i`. -/
local notation "𝔤" => K.leg i
/-- Its partner `ḡ`, the dart of the lollipop. -/
local notation "𝔟" => K.inv (K.leg i)
/-- The dart `p_i = σ⁻¹(g_i)` of the exterior at `β(i)`. -/
local notation "𝔭" => K.rot.symm (K.leg i)
/-- Its partner `p̄_i`. -/
local notation "𝔮" => K.inv (K.rot.symm (K.leg i))
/-- The dart `p_{i+1} = σ⁻¹(g_{i+1})` of the exterior at `β(i + 1)`. -/
local notation "𝔫" => K.rot.symm (K.leg (finRotate (b + 1) i))
/-- Its partner `p̄_{i+1}`, the third dart of `β(i)`. -/
local notation "𝔪" => K.inv (K.rot.symm (K.leg (finRotate (b + 1) i)))

omit [Fintype H] [DecidableEq H] in
private theorem finRotate_ne_self (i : Fin (b + 1)) : finRotate (b + 1) i ≠ i := by
  intro h
  have := congrArg Fin.val h
  rw [val_finRotate'] at this
  have hb : 0 < b := Nat.pos_of_ne_zero (NeZero.ne b)
  split_ifs at this <;> omega

/-- The facts about a plabic graph `K` with a lollipop of colour `c` at `i` used to extract the
lollipop. -/
structure LollipopExtractionFacts (K : PlabicData H (b + 1)) (i : Fin (b + 1)) (c : Shade) :
    Prop where
  /-- The involution of `K` is an involution. -/
  inv_involutive : Function.Involutive K.inv
  inv_ne : ∀ x, K.inv x ≠ x
  rot_m : K.rot (K.inv (K.rot.symm (K.leg (finRotate (b + 1) i)))) = (K.rot.symm (K.leg i))
  rot_p : K.rot (K.rot.symm (K.leg i)) = (K.leg i)
  rot_g : K.rot (K.leg i) = (K.inv (K.rot.symm (K.leg (finRotate (b + 1) i))))
  rot_b : K.rot (K.inv (K.leg i)) = (K.inv (K.leg i))
  m_mem : (K.inv (K.rot.symm (K.leg (finRotate (b + 1) i)))) ∈ K.bdry
  p_mem : (K.rot.symm (K.leg i)) ∈ K.bdry
  g_notMem : (K.leg i) ∉ K.bdry
  b_notMem : (K.inv (K.leg i)) ∉ K.bdry
  n_mem : (K.rot.symm (K.leg (finRotate (b + 1) i))) ∈ K.bdry
  q_mem : (K.inv (K.rot.symm (K.leg i))) ∈ K.bdry
  m_ne_p : (K.inv (K.rot.symm (K.leg (finRotate (b + 1) i)))) ≠ (K.rot.symm (K.leg i))
  n_ne_p : (K.rot.symm (K.leg (finRotate (b + 1) i))) ≠ (K.rot.symm (K.leg i))
  n_ne_q : (K.rot.symm (K.leg (finRotate (b + 1) i))) ≠ (K.inv (K.rot.symm (K.leg i)))
  isBoundaryVertex_g : K.IsBoundaryVertex (K.vertexOf (K.leg i))
  not_isBoundaryVertex_b : ¬K.IsBoundaryVertex (K.vertexOf (K.inv (K.leg i)))
  colour_b : K.colour (K.inv (K.leg i)) = c
  leg_succAbove_ne_g : ∀ j, K.leg (i.succAbove j) ≠ (K.leg i)
  leg_succAbove_ne_b : ∀ j, K.leg (i.succAbove j) ≠ (K.inv (K.leg i))
  leg_notMem : ∀ k, K.leg k ∉ K.bdry

omit [NeZero b] in
/-- The dart `ḡ_i` of a lollipop at `i` of colour `c` lies outside `B`, at an internal vertex of
colour `c`, and is fixed by the rotation. -/
private theorem IsPlabicGraph.inv_leg_of_isLollipopOfColour {u : Finset H}
    (hK : K.IsPlabicGraph) (hu : K.IsLollipopOfColour i c u) :
    𝔟 ∉ K.bdry ∧ ¬K.IsBoundaryVertex (K.vertexOf 𝔟) ∧ K.colour 𝔟 = c ∧ K.rot 𝔟 = 𝔟 := by
  have hinv := hK.inv_involutive
  obtain ⟨⟨⟨hui, hu1⟩, d, hdu, hdi⟩, hcol⟩ := hu
  obtain ⟨huV, huB⟩ := K.mem_internalVertices.1 hui
  have hdB : d ∉ K.bdry := fun h => huB ⟨d, hdu, h⟩
  have hidB : K.inv d ∉ K.bdry := fun h => hdB (hK.toIsDiskMap.inv_mem_bdry_iff.1 h)
  have hid : K.inv d = 𝔤 := by
    have : K.inv d ∈ (K.bvertex i).filter (· ∉ K.bdry) := mem_filter.2 ⟨hdi, hidB⟩
    rwa [hK.filter_bvertex_notMem_bdry, mem_singleton] at this
  obtain rfl : d = 𝔟 := by rw [← hid, hinv]
  obtain ⟨y, rfl⟩ := K.mem_vertices.1 huV
  have hvu : K.vertexOf 𝔟 = K.vertexOf y := K.vertexOf_eq_of_mem hdu
  have hrb : K.rot 𝔟 = 𝔟 := by
    obtain ⟨a, ha⟩ := card_eq_one.1 hu1
    have h1 := K.rot_mem_vertexOf 𝔟
    rw [hvu, ha, mem_singleton] at h1
    rw [ha, mem_singleton] at hdu
    rw [h1, hdu]
  exact ⟨hdB, by rwa [hvu], hcol _ hdu, hrb⟩

/-- The darts `n_i` and `p_i` of `β(i + 1)` and `β(i)` are distinct. -/
private theorem IsPlabicGraph.rot_symm_leg_finRotate_ne (hK : K.IsPlabicGraph) : 𝔫 ≠ 𝔭 := by
  intro h
  apply finRotate_ne_self i
  apply hK.bvertex_injective
  have h1 := K.vertexOf_eq_of_mem (K.rot_symm_mem_vertexOf (K.leg (finRotate (b + 1) i)))
  have h2 := K.vertexOf_eq_of_mem (K.rot_symm_mem_vertexOf (K.leg i))
  rw [h] at h1
  exact h1.symm.trans h2

private theorem IsPlabicGraph.lollipopExtractionFacts {u : Finset H} (hK : K.IsPlabicGraph)
    (hu : K.IsLollipopOfColour i c u) : LollipopExtractionFacts K i c := by
  have hinv := hK.inv_involutive
  have hp := hK.rot_symm_leg_mem_exterior i
  have hn := hK.rot_symm_leg_mem_exterior (finRotate (b + 1) i)
  have hv : K.IsBoundaryVertex (K.vertexOf 𝔤) :=
    K.vertexOf_mem_boundaryVertices.1 (hK.bvertex_mem i)
  -- the rotation at `β(i)`
  obtain ⟨d, hd, hdv, hdv'⟩ := hK.exists_exterior i
  obtain rfl := hK.eq_rot_symm_leg_of_mem_exterior hd hdv
  obtain ⟨-, hr1, hr2, hr3⟩ := DiskMap.rot_cycle_of_mem_boundaryVertices (M := K.toDiskMap)
    hinv hK.inv_mem_bdry hK.boundaryVertex_card hK.exists_orbit (hK.bvertex_mem i) hp
    (K.rot_symm_mem_vertexOf _) hn hdv' (K.leg_mem_bvertex i) (hK.leg_notMem_bdry i)
  obtain ⟨hdB, hbB, hcolb, hrb⟩ := hK.inv_leg_of_isLollipopOfColour hu
  have hpB := K.exterior_subset_bdry hp
  have hnB := K.exterior_subset_bdry hn
  have hmext : 𝔪 ∉ K.exterior := fun h =>
    disjoint_left.1 hK.toIsDiskMap.disjoint_exterior_map_inv h (by simpa using hn)
  have hqext : 𝔮 ∉ K.exterior := fun h =>
    disjoint_left.1 hK.toIsDiskMap.disjoint_exterior_map_inv h (by simpa using hp)
  refine
    { inv_involutive := hinv
      inv_ne := hK.inv_ne
      rot_m := hr1
      rot_p := hr2
      rot_g := hr3
      rot_b := hrb
      m_mem := hK.inv_mem_bdry _ hnB
      p_mem := hpB
      g_notMem := hK.leg_notMem_bdry i
      b_notMem := hdB
      n_mem := hnB
      q_mem := hK.inv_mem_bdry _ hpB
      m_ne_p := fun h => hmext (h ▸ hp)
      n_ne_p := hK.rot_symm_leg_finRotate_ne
      n_ne_q := fun h => hqext (h ▸ hn)
      isBoundaryVertex_g := hv
      not_isBoundaryVertex_b := hbB
      colour_b := hcolb
      leg_succAbove_ne_g := ?_
      leg_succAbove_ne_b := ?_
      leg_notMem := hK.leg_notMem_bdry }
  · intro j h
    apply Fin.succAbove_ne i j
    apply hK.bvertex_injective
    simp only [PlabicData.bvertex, h]
  · intro j h
    have := K.vertexOf_mem_boundaryVertices.1 (hK.bvertex_mem (i.succAbove j))
    rw [h] at this
    exact hbB this

/-- The darts `p̄_{i+1}, p_i, g_i, ḡ_i` of `β(i)` and of the lollipop at `i`. -/
private def exDarts (K : PlabicData H (b + 1)) (i : Fin (b + 1)) : Finset H :=
  {K.inv (K.rot.symm (K.leg (finRotate (b + 1) i))), K.rot.symm (K.leg i), K.leg i,
    K.inv (K.leg i)}

omit [Fintype H] in
omit [NeZero b] in
private theorem mem_exDarts {x : H} : x ∈ exDarts K i ↔ x = 𝔪 ∨ x = 𝔭 ∨ x = 𝔤 ∨ x = 𝔟 := by
  simp [exDarts]

/-- The involution of the extracted graph, before restriction: `d ↦ d̄` with `p_{i+1}` paired with
`p̄_i` and `p̄_{i+1}` with `p_i`. -/
private def exInv (K : PlabicData H (b + 1)) (i : Fin (b + 1)) : Perm H :=
  swap (K.inv (K.rot.symm (K.leg (finRotate (b + 1) i)))) (K.inv (K.rot.symm (K.leg i))) *
    K.inv * swap (K.inv (K.rot.symm (K.leg (finRotate (b + 1) i)))) (K.inv (K.rot.symm (K.leg i)))

namespace LollipopExtractionFacts

variable (F : LollipopExtractionFacts K i c)

include F

omit [NeZero b] in
private theorem m_ne_g : 𝔪 ≠ 𝔤 := fun h => F.g_notMem (h ▸ F.m_mem)

omit [NeZero b] in
private theorem m_ne_b : 𝔪 ≠ 𝔟 := fun h => F.b_notMem (h ▸ F.m_mem)

omit [NeZero b] in
private theorem p_ne_g : 𝔭 ≠ 𝔤 := fun h => F.g_notMem (h ▸ F.p_mem)

omit [NeZero b] in
private theorem p_ne_b : 𝔭 ≠ 𝔟 := fun h => F.b_notMem (h ▸ F.p_mem)

omit [NeZero b] in
private theorem g_ne_b : 𝔤 ≠ 𝔟 := fun h => F.inv_ne 𝔤 h.symm

omit [NeZero b] in
private theorem n_ne_m : 𝔫 ≠ 𝔪 := fun h => F.inv_ne 𝔫 h.symm

omit [NeZero b] in
private theorem n_ne_g : 𝔫 ≠ 𝔤 := fun h => F.g_notMem (h ▸ F.n_mem)

omit [NeZero b] in
private theorem n_ne_b : 𝔫 ≠ 𝔟 := fun h => F.b_notMem (h ▸ F.n_mem)

omit [NeZero b] in
private theorem q_ne_m : 𝔮 ≠ 𝔪 := fun h => F.n_ne_p (K.inv.injective h).symm

omit [NeZero b] in
private theorem q_ne_p : 𝔮 ≠ 𝔭 := F.inv_ne 𝔭

omit [NeZero b] in
private theorem q_ne_g : 𝔮 ≠ 𝔤 := fun h => F.g_notMem (h ▸ F.q_mem)

omit [NeZero b] in
private theorem q_ne_b : 𝔮 ≠ 𝔟 := fun h => F.b_notMem (h ▸ F.q_mem)

omit [NeZero b] in
private theorem inv_m : K.inv 𝔪 = 𝔫 := F.inv_involutive _

omit [NeZero b] in
private theorem inv_q : K.inv 𝔮 = 𝔭 := F.inv_involutive _

omit [NeZero b] in
private theorem inv_b : K.inv 𝔟 = 𝔤 := F.inv_involutive _

omit [NeZero b] in
private theorem n_notMem : 𝔫 ∉ exDarts K i := by
  rw [mem_exDarts]
  rintro (h | h | h | h)
  exacts [F.n_ne_m h, F.n_ne_p h, F.n_ne_g h, F.n_ne_b h]

omit [NeZero b] in
private theorem q_notMem : 𝔮 ∉ exDarts K i := by
  rw [mem_exDarts]
  rintro (h | h | h | h)
  exacts [F.q_ne_m h, F.q_ne_p h, F.q_ne_g h, F.q_ne_b h]

omit [NeZero b] in
private theorem leg_succAbove_notMem (j : Fin b) : K.leg (i.succAbove j) ∉ exDarts K i := by
  rw [mem_exDarts]
  rintro (h | h | h | h)
  · exact F.leg_notMem _ (h ▸ F.m_mem)
  · exact F.leg_notMem _ (h ▸ F.p_mem)
  · exact F.leg_succAbove_ne_g j h
  · exact F.leg_succAbove_ne_b j h

omit [NeZero b] in
private theorem exInv_m : exInv K i 𝔪 = 𝔭 := by
  rw [exInv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, F.inv_q,
    swap_apply_of_ne_of_ne F.m_ne_p.symm F.q_ne_p.symm]

omit [NeZero b] in
private theorem exInv_p : exInv K i 𝔭 = 𝔪 := by
  rw [exInv, Perm.mul_apply, Perm.mul_apply,
    swap_apply_of_ne_of_ne F.m_ne_p.symm F.q_ne_p.symm, swap_apply_right]

omit [NeZero b] in
private theorem exInv_g : exInv K i 𝔤 = 𝔟 := by
  rw [exInv, Perm.mul_apply, Perm.mul_apply,
    swap_apply_of_ne_of_ne F.m_ne_g.symm F.q_ne_g.symm,
    swap_apply_of_ne_of_ne F.m_ne_b.symm F.q_ne_b.symm]

omit [NeZero b] in
private theorem exInv_b : exInv K i 𝔟 = 𝔤 := by
  rw [exInv, Perm.mul_apply, Perm.mul_apply,
    swap_apply_of_ne_of_ne F.m_ne_b.symm F.q_ne_b.symm, F.inv_b,
    swap_apply_of_ne_of_ne F.m_ne_g.symm F.q_ne_g.symm]

omit [NeZero b] in
private theorem exInv_n : exInv K i 𝔫 = 𝔮 := by
  rw [exInv, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne F.n_ne_m F.n_ne_q,
    swap_apply_left]

omit [NeZero b] in
private theorem exInv_involutive : Function.Involutive (exInv K i) := by
  intro x
  simp only [exInv, Perm.mul_apply, swap_apply_self, F.inv_involutive _]

omit [Fintype H] F in
omit [NeZero b] in
/-- On a dart outside `β(i) ∪ u`, other than `p_{i+1}` and `p̄_i`, the involution is `d ↦ d̄`. -/
private theorem exInv_of_ne {x : H} (hx : x ∉ exDarts K i) (h₁ : x ≠ 𝔫) (h₂ : x ≠ 𝔮) :
    exInv K i x = K.inv x := by
  rw [mem_exDarts] at hx
  simp only [not_or] at hx
  have h₃ : K.inv x ≠ 𝔪 := fun h => h₁ (K.inv.injective h)
  have h₄ : K.inv x ≠ 𝔮 := fun h => hx.2.1 (K.inv.injective h)
  rw [exInv, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hx.1 h₂,
    swap_apply_of_ne_of_ne h₃ h₄]

omit [NeZero b] in
private theorem exInv_mem_of_mem {x : H} (hx : x ∈ exDarts K i) : exInv K i x ∈ exDarts K i := by
  rcases mem_exDarts.1 hx with rfl | rfl | rfl | rfl
  · rw [F.exInv_m]; simp [mem_exDarts]
  · rw [F.exInv_p]; simp [mem_exDarts]
  · rw [F.exInv_g]; simp [mem_exDarts]
  · rw [F.exInv_b]; simp [mem_exDarts]

omit [NeZero b] in
private theorem exInv_notMem_iff (x : H) : exInv K i x ∉ exDarts K i ↔ x ∉ exDarts K i := by
  refine ⟨fun h hx => h (F.exInv_mem_of_mem hx), fun h hx => h ?_⟩
  have := F.exInv_mem_of_mem hx
  rwa [F.exInv_involutive x] at this

omit [NeZero b] in
private theorem rot_notMem_iff (x : H) : K.rot x ∉ exDarts K i ↔ x ∉ exDarts K i := by
  refine ⟨fun h hx => h ?_, fun h hx => h ?_⟩
  · rcases mem_exDarts.1 hx with rfl | rfl | rfl | rfl
    · rw [F.rot_m]; simp [mem_exDarts]
    · rw [F.rot_p]; simp [mem_exDarts]
    · rw [F.rot_g]; simp [mem_exDarts]
    · rw [F.rot_b]; simp [mem_exDarts]
  · rw [mem_exDarts]
    rcases mem_exDarts.1 hx with h' | h' | h' | h'
    · exact Or.inr (Or.inr (Or.inl (K.rot.injective (h'.trans F.rot_g.symm))))
    · exact Or.inl (K.rot.injective (h'.trans F.rot_m.symm))
    · exact Or.inr (Or.inl (K.rot.injective (h'.trans F.rot_p.symm)))
    · exact Or.inr (Or.inr (Or.inr (K.rot.injective (h'.trans F.rot_b.symm))))

end LollipopExtractionFacts

/-- The plabic graph `A` extracted from `K`: the darts of `K` outside `β(i) ∪ u`, the involution
of `K` with `p_{i+1}` paired with `p̄_i`, the restricted rotation, boundary arcs and colours, and
the label `j` at `β(j⁺)`. -/
private def exGraph (F : LollipopExtractionFacts K i c) : PlabicData {x // x ∉ exDarts K i} b where
  inv := (exInv K i).subtypePerm F.exInv_notMem_iff
  rot := K.rot.subtypePerm F.rot_notMem_iff
  bdry := univ.filter fun x => (x : H) ∈ K.bdry
  colour x := K.colour x
  leg j := ⟨K.leg (i.succAbove j), F.leg_succAbove_notMem j⟩

namespace LollipopExtractionFacts

variable (F : LollipopExtractionFacts K i c)

omit [NeZero b] in
@[simp]
private theorem coe_exGraph_inv (y : {x // x ∉ exDarts K i}) :
    ((exGraph F).inv y : H) = exInv K i y := rfl

omit [NeZero b] in
@[simp]
private theorem coe_exGraph_rot (y : {x // x ∉ exDarts K i}) :
    ((exGraph F).rot y : H) = K.rot y := rfl

omit [NeZero b] in
@[simp]
private theorem coe_exGraph_leg (j : Fin b) :
    ((exGraph F).leg j : H) = K.leg (i.succAbove j) := rfl

omit [NeZero b] in
@[simp]
private theorem exGraph_colour (y : {x // x ∉ exDarts K i}) :
    (exGraph F).colour y = K.colour y := rfl

omit [NeZero b] in
@[simp]
private theorem mem_exGraph_bdry {y : {x // x ∉ exDarts K i}} :
    y ∈ (exGraph F).bdry ↔ (y : H) ∈ K.bdry := by
  simp [exGraph]

private theorem exGraph_lollipopArc : (exGraph F).lollipopArc i = ⟨𝔫, F.n_notMem⟩ := by
  change (exGraph F).rot.symm ((exGraph F).leg (insertionNext i)) = _
  rw [Equiv.symm_apply_eq]
  ext
  rw [coe_exGraph_leg, coe_exGraph_rot, Equiv.apply_symm_apply,
    ← finRotate_eq_succAbove_insertionNext]

private theorem exGraph_inv_lollipopArc :
    (exGraph F).inv ((exGraph F).lollipopArc i) = ⟨𝔮, F.q_notMem⟩ := by
  rw [exGraph_lollipopArc]
  ext
  rw [coe_exGraph_inv, F.exInv_n]

omit [NeZero b] in
private theorem exGraph_inv_involutive : Function.Involutive (exGraph F).inv := fun y => by
  ext
  rw [coe_exGraph_inv, coe_exGraph_inv, F.exInv_involutive]

private theorem exGraph_inv_lollipopArc_ne :
    (exGraph F).inv ((exGraph F).lollipopArc i) ≠ (exGraph F).lollipopArc i := by
  rw [exGraph_inv_lollipopArc, exGraph_lollipopArc]
  intro h
  exact F.n_ne_q (congrArg Subtype.val h).symm

/-- The bijection of the darts of `K` with those of `I_i(A, c)`: `p̄_{i+1}, p_i, g_i, ḡ_i` go to
`e₁, e₂, g°, ḡ°`, and the other darts to themselves. -/
private def exEquiv (F : LollipopExtractionFacts K i c) : H ≃ {x // x ∉ exDarts K i} ⊕ Fin 4 where
  toFun x := if hx : x ∈ exDarts K i then
      Sum.inr (if x = 𝔪 then 0 else if x = 𝔭 then 1 else if x = 𝔤 then 2 else 3)
    else Sum.inl ⟨x, hx⟩
  invFun := Sum.elim Subtype.val ![𝔪, 𝔭, 𝔤, 𝔟]
  left_inv x := by
    by_cases hx : x ∈ exDarts K i
    · rcases mem_exDarts.1 hx with rfl | rfl | rfl | rfl <;>
        simp [mem_exDarts, F.m_ne_p, F.m_ne_g, F.m_ne_b, F.p_ne_g, F.p_ne_b, F.g_ne_b,
          F.m_ne_p.symm, F.m_ne_g.symm, F.m_ne_b.symm, F.p_ne_g.symm, F.p_ne_b.symm,
          F.g_ne_b.symm]
    · simp [hx]
  right_inv z := by
    rcases z with ⟨x, hx⟩ | k
    · simp [hx]
    · rcases fin_four_cases k with rfl | rfl | rfl | rfl <;>
        simp [mem_exDarts, F.m_ne_p, F.m_ne_g, F.m_ne_b, F.p_ne_g, F.p_ne_b, F.g_ne_b,
          F.m_ne_p.symm, F.m_ne_g.symm, F.m_ne_b.symm, F.p_ne_g.symm, F.p_ne_b.symm,
          F.g_ne_b.symm]

omit [NeZero b] in
private theorem exEquiv_m : exEquiv F 𝔪 = Sum.inr 0 := by
  simp [exEquiv, mem_exDarts]

omit [NeZero b] in
private theorem exEquiv_p : exEquiv F 𝔭 = Sum.inr 1 := by
  simp [exEquiv, mem_exDarts, F.m_ne_p.symm]

omit [NeZero b] in
private theorem exEquiv_g : exEquiv F 𝔤 = Sum.inr 2 := by
  simp [exEquiv, mem_exDarts, F.m_ne_g.symm, F.p_ne_g.symm]

omit [NeZero b] in
private theorem exEquiv_b : exEquiv F 𝔟 = Sum.inr 3 := by
  simp [exEquiv, mem_exDarts, F.m_ne_b.symm, F.p_ne_b.symm, F.g_ne_b.symm]

omit [NeZero b] in
private theorem exEquiv_of_notMem {x : H} (hx : x ∉ exDarts K i) :
    exEquiv F x = Sum.inl ⟨x, hx⟩ := by
  simp [exEquiv, hx]

private theorem exEquiv_map_inv (x : H) :
    exEquiv F (K.inv x) = ((exGraph F).lollipopInsertion i c).inv (exEquiv F x) := by
  have hinvA := F.exGraph_inv_involutive
  have hhA := F.exGraph_inv_lollipopArc_ne
  by_cases hx : x ∈ exDarts K i
  · rcases mem_exDarts.1 hx with rfl | rfl | rfl | rfl
    · rw [F.inv_m, exEquiv_of_notMem F F.n_notMem, exEquiv_m,
        lollipopInsertion_inv_inr_zero' c hinvA, F.exGraph_lollipopArc]
    · rw [exEquiv_of_notMem F F.q_notMem, exEquiv_p, lollipopInsertion_inv_inr_one c hhA,
        F.exGraph_inv_lollipopArc]
    · rw [exEquiv_b, exEquiv_g, lollipopInsertion_inv_inr_two]
    · rw [F.inv_b, exEquiv_g, exEquiv_b, lollipopInsertion_inv_inr_three]
  by_cases h₁ : x = 𝔫
  · subst h₁
    rw [exEquiv_m, exEquiv_of_notMem F hx, ← F.exGraph_lollipopArc,
      lollipopInsertion_inv_inl_self c hhA]
  by_cases h₂ : x = 𝔮
  · subst h₂
    rw [F.inv_q, exEquiv_p, exEquiv_of_notMem F hx, ← F.exGraph_inv_lollipopArc,
      lollipopInsertion_inv_inl_inv]
  have hx' : K.inv x ∉ exDarts K i := by
    rw [← exInv_of_ne hx h₁ h₂]
    exact (F.exInv_notMem_iff x).2 hx
  have hne₁ : (⟨x, hx⟩ : {x // x ∉ exDarts K i}) ≠ (exGraph F).lollipopArc i := by
    rw [F.exGraph_lollipopArc]
    intro h
    exact h₁ (congrArg Subtype.val h)
  have hne₂ : (⟨x, hx⟩ : {x // x ∉ exDarts K i}) ≠
      (exGraph F).inv ((exGraph F).lollipopArc i) := by
    rw [F.exGraph_inv_lollipopArc]
    intro h
    exact h₂ (congrArg Subtype.val h)
  rw [exEquiv_of_notMem F hx', exEquiv_of_notMem F hx,
    lollipopInsertion_inv_inl_of_ne _ _ c hne₁ hne₂]
  congr 1
  ext
  rw [coe_exGraph_inv, exInv_of_ne hx h₁ h₂]

private theorem exEquiv_map_rot (x : H) :
    exEquiv F (K.rot x) = ((exGraph F).lollipopInsertion i c).rot (exEquiv F x) := by
  by_cases hx : x ∈ exDarts K i
  · rcases mem_exDarts.1 hx with rfl | rfl | rfl | rfl
    · rw [F.rot_m, exEquiv_p, exEquiv_m, lollipopInsertion_rot_inr_zero]
    · rw [F.rot_p, exEquiv_g, exEquiv_p, lollipopInsertion_rot_inr_one]
    · rw [F.rot_g, exEquiv_m, exEquiv_g, lollipopInsertion_rot_inr_two]
    · rw [F.rot_b, exEquiv_b, lollipopInsertion_rot_inr_three]
  · rw [exEquiv_of_notMem F ((F.rot_notMem_iff x).2 hx), exEquiv_of_notMem F hx,
      lollipopInsertion_rot_inl]
    rfl

private theorem exEquiv_mem_bdry_iff (x : H) :
    exEquiv F x ∈ ((exGraph F).lollipopInsertion i c).bdry ↔ x ∈ K.bdry := by
  by_cases hx : x ∈ exDarts K i
  · rcases mem_exDarts.1 hx with rfl | rfl | rfl | rfl
    · rw [exEquiv_m]; simp [F.m_mem]
    · rw [exEquiv_p]; simp [F.p_mem]
    · rw [exEquiv_g]; simp [F.g_notMem]
    · rw [exEquiv_b]; simp [F.b_notMem]
  · rw [exEquiv_of_notMem F hx, mem_lollipopInsertion_bdry_inl, mem_exGraph_bdry]

private theorem exEquiv_map_colour (x : H) (hx : ¬K.IsBoundaryVertex (K.vertexOf x)) :
    ((exGraph F).lollipopInsertion i c).colour (exEquiv F x) = K.colour x := by
  have hm : K.vertexOf 𝔪 = K.vertexOf 𝔤 := by rw [← F.rot_g, K.vertexOf_rot]
  have hp : K.vertexOf 𝔭 = K.vertexOf 𝔤 := by rw [← F.rot_m, K.vertexOf_rot, hm]
  by_cases hX : x ∈ exDarts K i
  · rcases mem_exDarts.1 hX with rfl | rfl | rfl | rfl
    · exact absurd (hm ▸ F.isBoundaryVertex_g) hx
    · exact absurd (hp ▸ F.isBoundaryVertex_g) hx
    · exact absurd F.isBoundaryVertex_g hx
    · rw [exEquiv_b, lollipopInsertion_colour_inr, F.colour_b]
  · rw [exEquiv_of_notMem F hX, lollipopInsertion_colour_inl, exGraph_colour]

private theorem exEquiv_map_bvertex (hK : K.IsPlabicGraph) (k : Fin (b + 1)) :
    ((K.bvertex k).filter (· ∉ K.bdry)).map (exEquiv F).toEmbedding =
      (((exGraph F).lollipopInsertion i c).bvertex k).filter
        (· ∉ ((exGraph F).lollipopInsertion i c).bdry) := by
  rw [hK.filter_bvertex_notMem_bdry k, map_singleton, Equiv.coe_toEmbedding]
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
  · rw [exEquiv_g, lollipopInsertion_bvertex_self]
    ext z
    simp only [mem_singleton, mem_filter, mem_insert]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h | h | h, hz⟩ <;> subst h <;> simp_all
  · rw [exEquiv_of_notMem F (F.leg_succAbove_notMem j), lollipopInsertion_bvertex_succAbove]
    ext z
    rw [mem_singleton, mem_filter]
    rcases z with y | k
    · rw [inl_mem_map_inl, mem_lollipopInsertion_bdry_inl, mem_exGraph_bdry]
      have h := congrArg (fun s => (y : H) ∈ s) (hK.filter_bvertex_notMem_bdry (i.succAbove j))
      simp only [mem_filter, mem_singleton, eq_iff_iff] at h
      have hv : y ∈ (exGraph F).bvertex j ↔ (y : H) ∈ K.bvertex (i.succAbove j) := by
        rw [PlabicData.bvertex, PlabicData.bvertex, RotationSystem.mem_vertexOf,
          RotationSystem.mem_vertexOf,
          show (exGraph F).rot = K.rot.subtypePerm F.rot_notMem_iff from rfl,
          Equiv.Perm.sameCycle_subtypePerm, coe_exGraph_leg]
      rw [hv, h, Sum.inl.injEq, Subtype.ext_iff, eq_comm]
    · simp

/-- The isomorphism of `K` with `I_i(A, c)`. -/
private def exIso (hK : K.IsPlabicGraph) (F : LollipopExtractionFacts K i c) :
    K.Iso ((exGraph F).lollipopInsertion i c) where
  toEquiv := exEquiv F
  map_inv := exEquiv_map_inv F
  map_rot := exEquiv_map_rot F
  mem_bdry_iff := exEquiv_mem_bdry_iff F
  map_colour := exEquiv_map_colour F
  map_bvertex := exEquiv_map_bvertex F hK

end LollipopExtractionFacts

/-- **A lollipop can be extracted**: if `K` is a plabic graph with `b + 1 ≥ 2` boundary vertices
and `u` is a lollipop of colour `c` at the label `i`, then `K` is isomorphic to `I_i(A, c)` for a
plabic graph `A` with `b` boundary vertices. -/
@[cluster_algebras "lem_lollipop_extraction"]
theorem IsPlabicGraph.exists_isomorphic_lollipopInsertion (hK : K.IsPlabicGraph) {u : Finset H}
    (hu : K.IsLollipopOfColour i c u) :
    ∃ A : PlabicGraph b, K.Isomorphic (A.data.lollipopInsertion i c) := by
  have F := hK.lollipopExtractionFacts hu
  have hleg : ∀ k, ((exGraph F).lollipopInsertion i c).leg k ∉
      ((exGraph F).lollipopInsertion i c).bdry := by
    intro k
    rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨j, rfl⟩
    · simp
    · rw [lollipopInsertion_leg_succAbove, mem_lollipopInsertion_bdry_inl, F.mem_exGraph_bdry,
        F.coe_exGraph_leg]
      exact F.leg_notMem _
  have hI := (LollipopExtractionFacts.exIso hK F).isPlabicGraph hK hleg
  exact ⟨⟨{x // x ∉ exDarts K i}, exGraph F, IsPlabicGraph.of_lollipopInsertion hI⟩,
    ⟨LollipopExtractionFacts.exIso hK F⟩⟩

end Extraction

end PlabicData

end ClusterAlgebras
