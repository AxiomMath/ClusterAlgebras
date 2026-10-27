/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Basic
public import ClusterAlgebras.Rings.CyclicShiftQuiver
public import ClusterAlgebras.Rings.RectanglesExchange

/-!
# The cyclic shift mutation sequence

Let `2 ≤ a ≤ b - 2` and let `λ` be a rectangle labelling. Mutating the cyclic shift
`Σ^i_{a,b}(λ)` of the rectangles seed at the mutable rectangles, row by row from the bottom
mutable row to the top one and from left to right in each row (`cyclicShiftOrder`), gives the
cyclic shift `Σ^{i-1}_{a,b}(λ)`, up to a relabelling of the frozen vertices
(`rectanglesSeedShift_cyclicShift_mutation`).

The proof follows the sequence step by step. When the next rectangle to mutate is `(R, Q₀)`,
the seed reached is `relSeed` of the labels `csLabel` (`J(v) - 1` at the rectangles already
mutated, `J(v)` elsewhere, all shifted by `i`) and of the arrows `csArrow`
(`ClusterAlgebras.Rings.CyclicShiftQuiver`). At `(R, Q₀)` these arrows have two
in-neighbours `x₁, x₂` and two out-neighbours `y₁, y₂`, and the mutation is the three-term
Plücker relation `P_{S∪{β,δ}} P_{S∪{α,γ}} = P_{S∪{γ,δ}} P_{S∪{α,β}} + P_{S∪{α,δ}} P_{S∪{β,γ}}`
(`pluckerCoord_union_mul_pluckerCoord_union`), moved by the rotation `ρ^{-i}`.

## Main definitions

* `ClusterAlgebras.relSeed`: the seed with prescribed entries and the signed counts of a relation.
* `ClusterAlgebras.csLabel`: the labels of the seeds along the sequence.
* `ClusterAlgebras.csSeed`: the seeds along the sequence.
* `ClusterAlgebras.csReindex`: the relabelling `λ⁻¹ ∘ σ ∘ λ` of the frozen vertices.

## Main results

* `ClusterAlgebras.seedMutation_relSeed`: the mutation of a `relSeed` at a vertex of degree four.
* `ClusterAlgebras.seedMutation_csSeed`: one step of the sequence.
* `ClusterAlgebras.rectanglesSeedShift_cyclicShift_mutation`: mutating `Σ^i_{a,b}(λ)` along
  `cyclicShiftOrder` gives `Σ^{i-1}_{a,b}(λ)` up to a relabelling of the frozen vertices.

## Implementation notes

* Rows and columns are `0`-based, `c = b - a`; the sequence starts at `(a - 2, 0)` and ends at
  `(0, c - 2)`.
* Fomin, Williams and Zelevinsky state the result with `Σ^{i+1}`; with their own labels and arrows
  the sequence lowers every label by one, and permutes the frozen vertices.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Seeds of a relation -/

section Generic

variable {V : Type*} {F : Type*} [Field F] {m n : ℕ}

open Classical in
/-- The signed count of a relation `A`: `1` when `A u v`, minus `1` when `A v u`. -/
noncomputable def relSign (A : V → V → Prop) (u v : V) : ℤ :=
  (if A u v then 1 else 0) - (if A v u then 1 else 0)

/-- The seed with extended cluster `x ∘ e` whose matrix has entries the signed counts of `A`. -/
noncomputable def relSeed (e : Fin m ≃ V) (hmn : n ≤ m) (x : V → F) (A : V → V → Prop) :
    SeedData F m n where
  extCluster := x ∘ e
  extExchangeMatrix := Matrix.of fun i j => relSign A (e i) (e (Fin.castLE hmn j))

open Classical in
/-- The signed counts at a vertex `κ` whose in- and out-neighbours are `X` and `Y`. -/
theorem relSign_eq_of_iff {A : V → V → Prop} {X Y : V → Prop} {κ : V}
    (hin : ∀ u, A u κ ↔ X u) (hout : ∀ u, A κ u ↔ Y u) (u : V) :
    relSign A u κ = (if X u then 1 else 0) - (if Y u then 1 else 0) ∧
      relSign A κ u = (if Y u then 1 else 0) - (if X u then 1 else 0) := by
  refine ⟨?_, ?_⟩ <;> simp only [relSign, hin, hout]

open Classical in
/-- The signed count after a mutation, from the arrows after it: arrows from in- to
out-neighbours are added, the opposite ones removed. -/
theorem relSign_step {A A' : V → V → Prop} {X Y : V → Prop} {u w : V}
    (h₁ : A' u w ↔ (A u w ∧ ¬(Y u ∧ X w)) ∨ (X u ∧ Y w ∧ ¬A w u))
    (h₂ : A' w u ↔ (A w u ∧ ¬(Y w ∧ X u)) ∨ (X w ∧ Y u ∧ ¬A u w))
    (h₃ : ¬(A u w ∧ A w u)) (h₄ : X u → Y w → ¬A u w) (h₅ : X w → Y u → ¬A w u)
    (h₆ : ¬(X u ∧ Y u)) (h₇ : ¬(X w ∧ Y w)) :
    relSign A' u w = relSign A u w + (if X u ∧ Y w then 1 else 0) -
      (if Y u ∧ X w then 1 else 0) := by
  simp only [relSign]
  by_cases a₁ : A u w <;> by_cases a₂ : A w u <;> by_cases a₃ : X u <;> by_cases a₄ : Y u <;>
    by_cases a₅ : X w <;> by_cases a₆ : Y w <;>
    simp only [a₁, a₂, a₃, a₄, a₅, a₆, and_true, not_true_eq_false, and_false, or_false,
      not_false_eq_true, if_true, if_false, or_true, true_implies, imp_false]
      at h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⊢ <;>
    simp only [h₁, h₂, if_true, if_false] <;> norm_num

open Classical in
/-- **The mutation of a relation seed** at a vertex `κ` with two in-neighbours `x₁, x₂` and two
out-neighbours `y₁, y₂`: the entry at `κ` becomes `y`, where
`x(κ) y = x(x₁) x(x₂) + x(y₁) x(y₂)`, and the arrows become `A'`, provided `A'` reverses the
arrows at `κ` and changes the signed counts elsewhere by the paths through `κ`. -/
theorem seedMutation_relSeed [Finite V] [DecidableEq V] (e : Fin m ≃ V) (hmn : n ≤ m)
    (x : V → F) (A A' : V → V → Prop) (k : Fin n) (X Y : V → Prop) (x₁ x₂ y₁ y₂ : V) (y : F)
    (hX : ∀ u, X u ↔ u = x₁ ∨ u = x₂) (hY : ∀ u, Y u ↔ u = y₁ ∨ u = y₂)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂) (hXY : ∀ u, ¬(X u ∧ Y u))
    (hin : ∀ u, A u (e (Fin.castLE hmn k)) ↔ X u) (hout : ∀ u, A (e (Fin.castLE hmn k)) u ↔ Y u)
    (hin' : ∀ u, A' u (e (Fin.castLE hmn k)) ↔ Y u)
    (hout' : ∀ u, A' (e (Fin.castLE hmn k)) u ↔ X u)
    (hstep : ∀ u (j : Fin n), u ≠ e (Fin.castLE hmn k) → j ≠ k →
      relSign A' u (e (Fin.castLE hmn j)) = relSign A u (e (Fin.castLE hmn j)) +
        (if X u ∧ Y (e (Fin.castLE hmn j)) then 1 else 0) -
        (if Y u ∧ X (e (Fin.castLE hmn j)) then 1 else 0))
    (hxk : x (e (Fin.castLE hmn k)) * y = x x₁ * x x₂ + x y₁ * x y₂)
    (hk : x (e (Fin.castLE hmn k)) ≠ 0) :
    seedMutation hmn (relSeed e hmn x A) k =
      relSeed e hmn (Function.update x (e (Fin.castLE hmn k)) y) A' := by
  have := Fintype.ofFinite V
  set κ := e (Fin.castLE hmn k) with hκ
  have hc := relSign_eq_of_iff hin hout
  have hc' := relSign_eq_of_iff hin' hout'
  have hpos : ∀ u, (relSign A u κ).toNat = if X u then 1 else 0 := by
    intro u; rw [(hc u).1]; have := hXY u; split_ifs <;> simp_all
  have hneg : ∀ u, (-relSign A u κ).toNat = if Y u then 1 else 0 := by
    intro u; rw [(hc u).1]; have := hXY u; split_ifs <;> simp_all
  have hfX : univ.filter X = {x₁, x₂} := by ext u; simp [hX]
  have hfY : univ.filter Y = {y₁, y₂} := by ext u; simp [hY]
  refine SeedData.ext ?_ ?_
  · simp only [seedMutation, relSeed]
    rw [Function.update_comp_equiv, Equiv.symm_apply_apply]
    congr 1
    change _ / x κ = y
    rw [div_eq_iff hk, mul_comm y, hxk, exchangeMonomialPos_eq_prod,
      exchangeMonomialNeg_eq_prod]
    simp only [Matrix.of_apply, Function.comp_apply]
    rw [Equiv.prod_comp e (fun v => x v ^ (relSign A v κ).toNat),
      Equiv.prod_comp e (fun v => x v ^ (-relSign A v κ).toNat)]
    simp only [hpos, hneg, pow_ite, pow_one, pow_zero]
    rw [← prod_filter, ← prod_filter, hfX, hfY, prod_pair hx, prod_pair hy]
  · ext i j
    simp only [seedMutation, relSeed, Matrix.of_apply]
    by_cases h : i = Fin.castLE hmn k ∨ j = k
    · rw [matrixMutation_apply_of_eq hmn _ k h]
      simp only [Matrix.of_apply]
      rcases h with rfl | rfl
      · rw [← hκ, (hc' _).2, (hc _).2]; ring
      · rw [← hκ, (hc' _).1, (hc _).1]; ring
    · rw [not_or] at h
      rw [matrixMutation_apply_of_ne_eq_max hmn _ k h.1 h.2]
      simp only [Matrix.of_apply]
      have hi : e i ≠ κ := fun h' => h.1 (e.injective h')
      rw [hstep (e i) j hi h.2, ← hκ, (hc _).1, (hc _).2]
      have h1 := hXY (e i)
      have h2 := hXY (e (Fin.castLE hmn j))
      by_cases a1 : X (e i) <;> by_cases a2 : Y (e i) <;>
        by_cases a3 : X (e (Fin.castLE hmn j)) <;> by_cases a4 : Y (e (Fin.castLE hmn j)) <;>
        simp only [a1, a2, a3, a4, and_self, and_true, and_false, if_true, if_false,
          not_true_eq_false, not_false_eq_true] at h1 h2 ⊢ <;>
        norm_num

end Generic

/-! ### Labels -/

section Labels

variable {a b : ℕ}

/-- Membership in `(J + 1) mod b`. -/
theorem mem_cyclicShift_one {J : Finset (Fin b)} {x : Fin b} :
    x ∈ cyclicShift 1 J ↔ (finRotate b).symm x ∈ J := by
  rw [cyclicShift, zpow_one]
  exact mem_map_equiv

/-- Membership in `(J - 1) mod b`. -/
theorem mem_cyclicShift_neg_one {J : Finset (Fin b)} {x : Fin b} :
    x ∈ cyclicShift (-1) J ↔ finRotate b x ∈ J := by
  rw [cyclicShift_neg_one, mem_map_equiv, Equiv.symm_symm]

/-- **The boundary rotation shifts the labels of the frozen vertices**: `J(σ(v)) = J(v) + 1`. -/
theorem rectLabel_csRot (ha : 2 ≤ a) (hc : 2 ≤ b - a) {v : RectVertex a b}
    (hv : ¬CsMutV a b v) : rectLabel a b (csRot a b v) = cyclicShift 1 (rectLabel a b v) := by
  rcases v with _ | ⟨p, q⟩
  · rw [csRot_none (by omega) (by omega)]
    ext x
    simp only [rectLabel, mem_cyclicShift_one, mem_filter, mem_univ, true_and,
      val_finRotate_symm]
    split_ifs <;> omega
  · rcases csRot_some_cases p q with ⟨hm, h⟩ | ⟨h0, hm1, hm2, h⟩ | ⟨h0, hm, h⟩ |
      ⟨hm1, hm2, h⟩
    · exact absurd hm hv
    all_goals
      rw [h]
      ext x
      simp only [rectLabel, mem_cyclicShift_one, mem_filter, mem_univ, true_and,
        val_finRotate_symm]
      split_ifs <;> omega

open Classical in
/-- The labels of the seed reached once the rectangles of `M` are mutated: `J(v) - 1` at a
mutated rectangle, `J(v)` elsewhere. -/
noncomputable def csLabel (a b : ℕ) (M : ℕ → ℕ → Prop) : RectVertex a b → Finset (Fin b)
  | none => rectLabel a b none
  | some (p, q) =>
      if M p q then cyclicShift (-1) (rectLabel a b (some (p, q))) else rectLabel a b (some (p, q))

/-- The in-neighbour `(R - 1, Q₀)` of `(R, Q₀)`, or `∅` when `R = 0`. -/
def csX₁ (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : RectVertex a b :=
  if R = 0 then none else some (⟨R - 1, by omega⟩, ⟨Q₀, by omega⟩)

/-- The in-neighbour `(R + 1, Q₀)` of `(R, Q₀)`, or `(a - 1, Q₀ + 1)` when `R + 2 = a`. -/
def csX₂ (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : RectVertex a b :=
  if R + 2 = a then some (⟨R + 1, by omega⟩, ⟨Q₀ + 1, by omega⟩)
  else some (⟨R + 1, by omega⟩, ⟨Q₀, by omega⟩)

/-- The out-neighbour `(R, Q₀ + 1)` of `(R, Q₀)`. -/
def csY₁ (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : RectVertex a b :=
  some (⟨R, by omega⟩, ⟨Q₀ + 1, by omega⟩)

/-- The out-neighbour `(R, Q₀ - 1)` of `(R, Q₀)`, or `(a - 1, 0)` when `Q₀ = 0`. -/
def csY₂ (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : RectVertex a b :=
  if Q₀ = 0 then some (⟨a - 1, by omega⟩, ⟨0, by omega⟩)
  else some (⟨R, by omega⟩, ⟨Q₀ - 1, by omega⟩)

/-- The column `α = c - Q₀ - 2` of the exchange at `(R, Q₀)`. -/
def csColα (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : Fin b :=
  ⟨b - a - Q₀ - 2, by omega⟩

/-- The column `β = c - Q₀ - 1 + R` of the exchange at `(R, Q₀)`. -/
def csColβ (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : Fin b :=
  ⟨b - a - Q₀ - 1 + R, by omega⟩

/-- The column `γ = c + R` of the exchange at `(R, Q₀)`. -/
def csColγ (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : Fin b :=
  ⟨b - a + R, by omega⟩

/-- The column `δ = b - 1` of the exchange at `(R, Q₀)`. -/
def csColδ (R Q₀ : ℕ) (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a) : Fin b :=
  ⟨b - 1, by omega⟩

/-- The common columns `S = [c - Q₀ - 1, c - Q₀ - 2 + R] ∪ [c + R + 1, b - 2]` of the six labels
of the exchange at `(R, Q₀)`. -/
def csBase (a b R Q₀ : ℕ) : Finset (Fin b) :=
  univ.filter fun x => (b - a - Q₀ - 1 ≤ (x : ℕ) ∧ (x : ℕ) < b - a - Q₀ - 1 + R) ∨
    (b - a + R + 1 ≤ (x : ℕ) ∧ (x : ℕ) + 2 ≤ b)

/-- Proves an identity between labels and sets of columns by comparing column indices. -/
local macro "cs_ext" : tactic =>
  `(tactic| (simp only [csLabel, CsDone]; (try split_ifs) <;>
    (ext x; simp only [rectLabel, csBase, csColα, csColβ, csColγ, csColδ,
      mem_cyclicShift_neg_one, mem_union, mem_insert, mem_singleton, mem_filter, mem_univ,
      true_and, Fin.ext_iff, val_finRotate]; (try split_ifs) <;> first | omega | grind)))

variable {R Q₀ : ℕ} (hR : R + 2 ≤ a) (hQ : Q₀ + 2 ≤ b - a)

include hR hQ

/-- The in-neighbours of `(R, Q₀)` are `x₁` and `x₂`. -/
theorem csInNbr_iff (u : RectVertex a b) :
    CsInNbr a b R Q₀ u ↔ u = csX₁ R Q₀ hR hQ ∨ u = csX₂ R Q₀ hR hQ := by
  rcases u with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ <;> simp only [CsInNbr, csX₁, csX₂] <;>
    split_ifs <;> simp [Fin.ext_iff] <;> omega

/-- The out-neighbours of `(R, Q₀)` are `y₁` and `y₂`. -/
theorem csOutNbr_iff (u : RectVertex a b) :
    CsOutNbr a b R Q₀ u ↔ u = csY₁ R Q₀ hR hQ ∨ u = csY₂ R Q₀ hR hQ := by
  rcases u with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ <;> simp only [CsOutNbr, csY₁, csY₂] <;>
    split_ifs <;> simp [Fin.ext_iff] <;> omega

/-- `x₁ ≠ x₂`. -/
theorem csX₁_ne_csX₂ : csX₁ R Q₀ hR hQ ≠ (csX₂ R Q₀ hR hQ : RectVertex a b) := by
  simp only [csX₁, csX₂]
  split_ifs <;> simp [Fin.ext_iff]

/-- `y₁ ≠ y₂`. -/
theorem csY₁_ne_csY₂ : csY₁ R Q₀ hR hQ ≠ (csY₂ R Q₀ hR hQ : RectVertex a b) := by
  simp only [csY₁, csY₂]
  split_ifs
  · simp [Fin.ext_iff]
  · simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq]
    omega

/-- `J(R, Q₀) = S ∪ {β, δ}`. -/
theorem rectLabel_center :
    rectLabel a b (some (⟨R, by omega⟩, ⟨Q₀, by omega⟩)) =
      csBase a b R Q₀ ∪ {csColβ R Q₀ hR hQ, csColδ R Q₀ hR hQ} := by
  ext x
  simp only [rectLabel, csBase, csColβ, csColδ, mem_union, mem_insert, mem_singleton,
    mem_filter, mem_univ, true_and, Fin.ext_iff]
  omega

/-- `J(R, Q₀) - 1 = S ∪ {α, γ}`. -/
theorem cyclicShift_rectLabel_center :
    cyclicShift (-1) (rectLabel a b (some (⟨R, by omega⟩, ⟨Q₀, by omega⟩))) =
      csBase a b R Q₀ ∪ {csColα R Q₀ hR hQ, csColγ R Q₀ hR hQ} := by
  ext x
  simp only [rectLabel, csBase, csColα, csColγ, mem_cyclicShift_neg_one, mem_union, mem_insert,
    mem_singleton, mem_filter, mem_univ, true_and, Fin.ext_iff, val_finRotate]
  split_ifs <;> omega

/-- The label of `x₁` is `S ∪ {γ, δ}`. -/
theorem csLabel_csX₁ :
    csLabel a b (CsDone a b R Q₀) (csX₁ R Q₀ hR hQ) =
      csBase a b R Q₀ ∪ {csColγ R Q₀ hR hQ, csColδ R Q₀ hR hQ} := by
  unfold csX₁
  split_ifs <;> cs_ext

/-- The label of `x₂` is `S ∪ {α, β}`. -/
theorem csLabel_csX₂ :
    csLabel a b (CsDone a b R Q₀) (csX₂ R Q₀ hR hQ) =
      csBase a b R Q₀ ∪ {csColα R Q₀ hR hQ, csColβ R Q₀ hR hQ} := by
  unfold csX₂
  split_ifs <;> cs_ext

/-- The label of `y₁` is `S ∪ {α, δ}`. -/
theorem csLabel_csY₁ :
    csLabel a b (CsDone a b R Q₀) (csY₁ R Q₀ hR hQ) =
      csBase a b R Q₀ ∪ {csColα R Q₀ hR hQ, csColδ R Q₀ hR hQ} := by
  unfold csY₁
  cs_ext

/-- The label of `y₂` is `S ∪ {β, γ}`. -/
theorem csLabel_csY₂ :
    csLabel a b (CsDone a b R Q₀) (csY₂ R Q₀ hR hQ) =
      csBase a b R Q₀ ∪ {csColβ R Q₀ hR hQ, csColγ R Q₀ hR hQ} := by
  unfold csY₂
  split_ifs <;> cs_ext

/-- **The exchange relation at `(R, Q₀)`**, shifted by `i`:
`P_{J+i} P_{J-1+i} = P_{x₁} P_{x₂} + P_{y₁} P_{y₂}` for the labels shifted by `i`. -/
theorem pluckerCoord_center_mul (i : ℤ) :
    pluckerCoord (complexGenericMatrix a b)
        (cyclicShift i (rectLabel a b (some (⟨R, by omega⟩, ⟨Q₀, by omega⟩)))) *
      pluckerCoord (complexGenericMatrix a b)
        (cyclicShift i (cyclicShift (-1) (rectLabel a b (some (⟨R, by omega⟩, ⟨Q₀, by omega⟩))))) =
    pluckerCoord (complexGenericMatrix a b)
        (cyclicShift i (csLabel a b (CsDone a b R Q₀) (csX₁ R Q₀ hR hQ))) *
      pluckerCoord (complexGenericMatrix a b)
        (cyclicShift i (csLabel a b (CsDone a b R Q₀) (csX₂ R Q₀ hR hQ))) +
    pluckerCoord (complexGenericMatrix a b)
        (cyclicShift i (csLabel a b (CsDone a b R Q₀) (csY₁ R Q₀ hR hQ))) *
      pluckerCoord (complexGenericMatrix a b)
        (cyclicShift i (csLabel a b (CsDone a b R Q₀) (csY₂ R Q₀ hR hQ))) := by
  have key := pluckerCoord_union_mul_pluckerCoord_union (complexGenericMatrix a b)
    (csBase a b R Q₀) (α := csColα R Q₀ hR hQ) (β := csColβ R Q₀ hR hQ)
    (γ := csColγ R Q₀ hR hQ) (δ := csColδ R Q₀ hR hQ)
    (by simp only [csBase, csColα, mem_filter, mem_univ, true_and]; omega)
    (by simp only [csBase, csColβ, mem_filter, mem_univ, true_and]; omega)
    (by simp only [csBase, csColγ, mem_filter, mem_univ, true_and]; omega)
    (by simp only [csBase, csColδ, mem_filter, mem_univ, true_and]; omega)
    (by simp only [Fin.lt_def, csColα, csColβ]; omega)
    (by simp only [Fin.lt_def, csColβ, csColγ]; omega)
    (by simp only [Fin.lt_def, csColγ, csColδ]; omega)
  have h := congrArg (rotationEquiv a b ^ (-i)) key
  simp only [map_mul, map_add, rotationEquiv_zpow_pluckerCoord, neg_neg] at h
  rw [cyclicShift_rectLabel_center hR hQ, rectLabel_center hR hQ, csLabel_csX₁ hR hQ,
    csLabel_csX₂ hR hQ, csLabel_csY₁ hR hQ, csLabel_csY₂ hR hQ]
  linear_combination h

end Labels

/-! ### The seeds along the sequence -/

section Seeds

variable {a b m n : ℕ}

/-- The seed reached along the cyclic shift sequence from `Σ^i_{a,b}(λ)` once the rectangles of
`M` are mutated: the Plücker coordinates of the labels `csLabel`, shifted by `i`, and the signed
counts of the arrows `csArrow`. -/
noncomputable def csSeed (L : RectangleLabelling a b m n) (i : ℤ) (M : ℕ → ℕ → Prop) :
    SeedData (FractionRing (ComplexPoly a b)) m n :=
  relSeed L.equiv L.le
    (fun v => algebraMap _ _ (pluckerCoord (complexGenericMatrix a b)
      (cyclicShift i (csLabel a b M v))))
    (csArrow a b M)

/-- A vertex is mutable exactly when it is not frozen. -/
theorem csMutV_iff_not_rectFrozen (v : RectVertex a b) : CsMutV a b v ↔ ¬RectFrozen a b v := by
  rcases v with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  · simp [CsMutV, RectFrozen]
  · simp only [CsMutV, CsMut, RectFrozen, not_or]
    omega

/-- The vertex of a mutable index is mutable. -/
theorem RectangleLabelling.csMutV_castLE (L : RectangleLabelling a b m n) (j : Fin n) :
    CsMutV a b (L.equiv (Fin.castLE L.le j)) :=
  (csMutV_iff_not_rectFrozen _).2 (L.not_rectFrozen_castLE j)

/-- A Plücker coordinate of a shifted label, read in `ℂ(z)`, is nonzero. -/
theorem algebraMap_pluckerCoord_cyclicShift_ne_zero (i : ℤ) (pq : Fin a × Fin (b - a)) :
    algebraMap (ComplexPoly a b) (FractionRing (ComplexPoly a b))
      (pluckerCoord (complexGenericMatrix a b) (cyclicShift i (rectLabel a b (some pq)))) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
    (minor_complexGenericMatrix_ne_zero (by
      rw [card_cyclicShift, card_rectLabel_some, card_univ, Fintype.card_fin]))

/-- The first seed of the sequence is `Σ^i_{a,b}(λ)`. -/
theorem rectanglesSeedShift_eq_csSeed (L : RectangleLabelling a b m n) (i : ℤ) :
    rectanglesSeedShift L i = csSeed L i (CsDone a b (a - 2) 0) := by
  refine SeedData.ext ?_ ?_
  · funext ℓ
    simp only [rectanglesSeedShift, csSeed, relSeed, Function.comp_apply]
    congr 3
    rcases L.equiv ℓ with _ | ⟨p, q⟩
    · rfl
    · simp only [csLabel]
      rw [if_neg (not_csDone_start _ _)]
  · ext ℓ j
    simp only [rectanglesSeedShift, csSeed, relSeed, Matrix.of_apply, signedCount, relSign,
      csArrow_start_iff, rectArrows_eq_ite, and_comm (a := RectFrozen a b (L.equiv ℓ))]
    split_ifs <;> simp

end Seeds

/-! ### One step of the sequence -/

section Step

variable {a b m n : ℕ}

/-- **One step of the cyclic shift sequence.** If `λ(k) = (R, Q₀)`, the entry of the seed in
position `k` is nonzero, and mutating at `k` marks `(R, Q₀)` as mutated: its label becomes
`J(R, Q₀) - 1` and the arrows become those of the next state. -/
theorem seedMutation_csSeed (L : RectangleLabelling a b m n) (i : ℤ) (k : Fin n) {R Q₀ : ℕ}
    (hR' : R < a) (hQ' : Q₀ < b - a)
    (hk : L.equiv (Fin.castLE L.le k) = some (⟨R, hR'⟩, ⟨Q₀, hQ'⟩)) :
    (csSeed L i (CsDone a b R Q₀)).extCluster (Fin.castLE L.le k) ≠ 0 ∧
      seedMutation L.le (csSeed L i (CsDone a b R Q₀)) k =
        csSeed L i (CsDone a b R (Q₀ + 1)) := by
  classical
  obtain ⟨hr, hs⟩ := L.lt_of_equiv_castLE_eq_some k hk
  have hR : R + 2 ≤ a := by simp only at hr; omega
  have hQ : Q₀ + 2 ≤ b - a := by simp only at hs; omega
  set κ : RectVertex a b := some (⟨R, hR'⟩, ⟨Q₀, hQ'⟩) with hκ
  have hlabκ : csLabel a b (CsDone a b R Q₀) κ = rectLabel a b κ := by
    simp only [κ, csLabel]
    rw [if_neg (by simp [CsDone])]
  set x : RectVertex a b → FractionRing (ComplexPoly a b) := fun v =>
    algebraMap _ _ (pluckerCoord (complexGenericMatrix a b)
      (cyclicShift i (csLabel a b (CsDone a b R Q₀) v))) with hx
  have hne : x κ ≠ 0 := by
    simp only [x, hlabκ]
    exact algebraMap_pluckerCoord_cyclicShift_ne_zero i _
  refine ⟨by simp only [csSeed, relSeed, Function.comp_apply, hk]; exact hne, ?_⟩
  have hstep : ∀ u (j : Fin n), u ≠ L.equiv (Fin.castLE L.le k) → j ≠ k →
      relSign (csArrow a b (CsDone a b R (Q₀ + 1))) u (L.equiv (Fin.castLE L.le j)) =
        relSign (csArrow a b (CsDone a b R Q₀)) u (L.equiv (Fin.castLE L.le j)) +
          (if CsInNbr a b R Q₀ u ∧ CsOutNbr a b R Q₀ (L.equiv (Fin.castLE L.le j)) then 1
            else 0) -
          (if CsOutNbr a b R Q₀ u ∧ CsInNbr a b R Q₀ (L.equiv (Fin.castLE L.le j)) then 1
            else 0) := by
    intro u j hu hj
    have hw : L.equiv (Fin.castLE L.le j) ≠ L.equiv (Fin.castLE L.le k) :=
      fun h => hj (Fin.castLE_injective _ (L.equiv.injective h))
    rw [hk] at hu hw
    exact relSign_step
      (csArrow_step ⟨R, hR'⟩ ⟨Q₀, hQ'⟩ hR hQ u _ hu hw (Or.inr (L.csMutV_castLE j)))
      (csArrow_step ⟨R, hR'⟩ ⟨Q₀, hQ'⟩ hR hQ _ u hw hu (Or.inl (L.csMutV_castLE j)))
      (not_csArrow_and_csArrow R Q₀ hR hQ u _)
      (not_csArrow_of_csInNbr_of_csOutNbr R Q₀ hR hQ u _)
      (not_csArrow_of_csInNbr_of_csOutNbr R Q₀ hR hQ _ u)
      (not_csInNbr_and_csOutNbr R Q₀ hR u) (not_csInNbr_and_csOutNbr R Q₀ hR _)
  have hxk : x (L.equiv (Fin.castLE L.le k)) *
      algebraMap _ _ (pluckerCoord (complexGenericMatrix a b)
        (cyclicShift i (cyclicShift (-1) (rectLabel a b κ)))) =
      x (csX₁ R Q₀ hR hQ) * x (csX₂ R Q₀ hR hQ) + x (csY₁ R Q₀ hR hQ) * x (csY₂ R Q₀ hR hQ) := by
    rw [hk]
    simp only [x, hlabκ, ← map_mul, ← map_add]
    exact congrArg _ (pluckerCoord_center_mul hR hQ i)
  have key := seedMutation_relSeed L.equiv L.le x (csArrow a b (CsDone a b R Q₀))
    (csArrow a b (CsDone a b R (Q₀ + 1))) k (CsInNbr a b R Q₀) (CsOutNbr a b R Q₀)
    (csX₁ R Q₀ hR hQ) (csX₂ R Q₀ hR hQ) (csY₁ R Q₀ hR hQ) (csY₂ R Q₀ hR hQ) _
    (csInNbr_iff hR hQ) (csOutNbr_iff hR hQ) (csX₁_ne_csX₂ hR hQ) (csY₁_ne_csY₂ hR hQ)
    (not_csInNbr_and_csOutNbr R Q₀ hR)
    (by rw [hk]; exact csArrow_to_center ⟨R, hR'⟩ ⟨Q₀, hQ'⟩ hR hQ)
    (by rw [hk]; exact csArrow_from_center ⟨R, hR'⟩ ⟨Q₀, hQ'⟩ hR hQ)
    (by rw [hk]; exact csArrow_succ_to_center ⟨R, hR'⟩ ⟨Q₀, hQ'⟩ hR hQ)
    (by rw [hk]; exact csArrow_succ_from_center ⟨R, hR'⟩ ⟨Q₀, hQ'⟩ hR hQ)
    hstep hxk (by rw [hk]; exact hne)
  refine key.trans ?_
  simp only [csSeed]
  congr 1
  funext v
  rw [hk]
  by_cases hv : v = κ
  · rw [hv, Function.update_self]
    simp only [κ, csLabel]
    rw [if_pos ⟨hR, hQ, Or.inr ⟨rfl, Nat.lt_succ_self _⟩⟩]
  · rw [Function.update_of_ne hv]
    rcases v with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    · rfl
    · have hpq : ¬(p = R ∧ q = Q₀) := by
        rintro ⟨rfl, rfl⟩
        exact hv rfl
      simp only [x, csLabel]
      by_cases hc : CsDone a b R Q₀ p q
      · rw [if_pos hc, if_pos (by simp only [CsDone] at hc ⊢; grind)]
      · rw [if_neg hc, if_neg (by simp only [CsDone] at hc ⊢; grind)]

end Step

/-! ### The last seed -/

section End

variable {a b m n : ℕ}

/-- The relabelling `π = λ⁻¹ ∘ σ ∘ λ` of the frozen vertices by the boundary rotation. -/
def csReindex (L : RectangleLabelling a b m n) (ha : 2 ≤ a) (hc : 2 ≤ b - a) :
    ReindexingMap m n m n where
  toFun ℓ := L.equiv.symm (csRot a b (L.equiv ℓ))
  injective := L.equiv.symm.injective.comp ((csRot_injective ha hc).comp L.equiv.injective)
  lt_of_lt ℓ hℓ := by
    have hm : CsMutV a b (L.equiv ℓ) := by
      rw [csMutV_iff_not_rectFrozen, L.frozen_iff]
      omega
    rw [csRot_of_csMutV hm, Equiv.symm_apply_apply]
    exact hℓ

/-- `λ(π(ℓ)) = σ(λ(ℓ))`. -/
theorem csReindex_apply (L : RectangleLabelling a b m n) (ha : 2 ≤ a) (hc : 2 ≤ b - a)
    (ℓ : Fin m) : L.equiv (csReindex L ha hc ℓ) = csRot a b (L.equiv ℓ) :=
  Equiv.apply_symm_apply _ _

/-- `π` fixes the mutable indices. -/
theorem csReindex_of_lt (L : RectangleLabelling a b m n) (ha : 2 ≤ a) (hc : 2 ≤ b - a)
    (ℓ : Fin m) (hℓ : (ℓ : ℕ) < n) : csReindex L ha hc ℓ = ℓ := by
  have hm : CsMutV a b (L.equiv ℓ) := by
    rw [csMutV_iff_not_rectFrozen, L.frozen_iff]
    omega
  apply L.equiv.injective
  rw [csReindex_apply, csRot_of_csMutV hm]

/-- `π` is a restriction map: it sends frozen indices to frozen indices. -/
theorem csReindex_isRestriction (L : RectangleLabelling a b m n) (ha : 2 ≤ a)
    (hc : 2 ≤ b - a) : (csReindex L ha hc).IsRestriction := by
  intro ℓ hℓ
  rw [← L.frozen_iff, csReindex_apply, rectFrozen_csRot_iff ha hc, L.frozen_iff]
  exact hℓ

/-- `π` is a bijection. -/
theorem csReindex_bijective (L : RectangleLabelling a b m n) (ha : 2 ≤ a) (hc : 2 ≤ b - a) :
    Function.Bijective (csReindex L ha hc) :=
  Finite.injective_iff_bijective.1 (csReindex L ha hc).injective

/-- **The last seed of the sequence** is `Σ^{i-1}_{a,b}(λ)`, relabelled by `π`. -/
theorem csSeed_end (L : RectangleLabelling a b m n) (ha : 2 ≤ a) (hc : 2 ≤ b - a) (i : ℤ) :
    csSeed L i (CsDone a b 0 (b - a - 1)) =
      (rectanglesSeedShift L (i - 1)).reindex L.le (csReindex L ha hc) := by
  refine SeedData.ext ?_ ?_
  · funext ℓ
    simp only [csSeed, relSeed, SeedData.reindex_extCluster, Function.comp_apply,
      rectanglesSeedShift, csReindex_apply]
    congr 2
    generalize L.equiv ℓ = v
    by_cases hm : CsMutV a b v
    · rw [csRot_of_csMutV hm]
      rcases v with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
      · exact hm.elim
      · simp only [csLabel]
        rw [if_pos (by simp only [CsMutV, CsMut] at hm; simp only [CsDone]; omega),
          cyclicShift_cyclicShift]
        rfl
    · rw [rectLabel_csRot ha hc hm, cyclicShift_cyclicShift]
      have hlab : csLabel a b (CsDone a b 0 (b - a - 1)) v = rectLabel a b v := by
        rcases v with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
        · rfl
        · simp only [csLabel]
          rw [if_neg (by simp only [CsMutV, CsMut] at hm; simp only [CsDone]; omega)]
      rw [hlab]
      congr 1
      ring
  · ext ℓ j
    simp only [csSeed, relSeed, SeedData.reindex_extExchangeMatrix, matrixReindex_apply,
      rectanglesSeedShift, Matrix.of_apply, ReindexingMap.castLE_col, csReindex_apply,
      signedCount, relSign, csArrow_end_iff ha hc, rectArrows_eq_ite,
      and_comm (a := RectFrozen a b (csRot a b (L.equiv ℓ)))]
    split_ifs <;> simp

end End

/-! ### The whole sequence -/

section Sequence

variable {a b m n : ℕ}

/-- Mutation along `s ++ s'` is defined when it is along `s`, and then along `s'`. -/
theorem isMutationSeqDefined_append {F : Type*} [Field F] (hmn : n ≤ m) (S : SeedData F m n)
    (s s' : List (Fin n)) :
    IsMutationSeqDefined hmn S (s ++ s') ↔
      IsMutationSeqDefined hmn S s ∧ IsMutationSeqDefined hmn (seedMutationSeq hmn S s) s' := by
  induction s generalizing S with
  | nil => simp
  | cons k s ih => simp only [List.cons_append, isMutationSeqDefined_cons, ih, and_assoc,
      seedMutationSeq_cons]

/-- A rectangle read as a pair of numbers. -/
def csNat (a b : ℕ) : RectVertex a b → Option (ℕ × ℕ) :=
  Option.map fun pq => ((pq.1 : ℕ), (pq.2 : ℕ))

/-- A rectangle read as the pair `(R, Q)` is `(R, Q)`. -/
theorem csNat_eq_some {v : RectVertex a b} {R Q : ℕ} (h : csNat a b v = some (R, Q)) :
    ∃ (hR : R < a) (hQ : Q < b - a), v = some (⟨R, hR⟩, ⟨Q, hQ⟩) := by
  rcases v with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  · simp [csNat] at h
  · simp only [csNat, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hp, hq, rfl⟩

/-- The pairs of numbers of the columns `0, …, c - 2` of a row, as `Fin`s. -/
theorem map_val_filter_finRange (c : ℕ) :
    ((List.finRange c).filter fun q : Fin c => (q : ℕ) + 1 < c).map Fin.val =
      List.range (c - 1) := by
  have : ((List.finRange c).filter fun q : Fin c => (q : ℕ) + 1 < c) =
      (List.finRange c).filter ((fun q : ℕ => q + 1 < c) ∘ Fin.val) := rfl
  rw [this, ← List.filter_map, List.map_coe_finRange_eq_range]
  rcases c with _ | c
  · rfl
  · rw [List.range_succ, List.filter_append]
    simp

/-- The rows `a - 2, …, 0`, as `Fin`s. -/
theorem map_val_reverse_filter_finRange (a : ℕ) :
    ((List.finRange a).reverse.filter fun p : Fin a => (p : ℕ) + 1 < a).map Fin.val =
      (List.range (a - 1)).reverse := by
  rw [List.filter_reverse, List.map_reverse, map_val_filter_finRange]

/-- The vertices of `cyclicShiftOrder a b`, read as pairs of numbers. -/
theorem map_csNat_cyclicShiftOrder :
    (cyclicShiftOrder a b).map (csNat a b) =
      (List.range (a - 1)).reverse.flatMap
        fun p => (List.range (b - a - 1)).map fun q => some (p, q) := by
  simp only [csNat, cyclicShiftOrder, List.map_flatMap, List.map_map]
  rw [← map_val_reverse_filter_finRange, List.flatMap_map]
  congr 1
  funext p
  rw [← map_val_filter_finRange, List.map_map]
  rfl

/-- **The sweep of row `R`**: from the state `(R, Q₀)`, mutation along the rest of row `R` is
defined and reaches the state at the end of the row. -/
theorem csSeed_row (L : RectangleLabelling a b m n) (i : ℤ) (R : ℕ) :
    ∀ (d Q₀ : ℕ), Q₀ + d + 1 = b - a → ∀ t : List (Fin n),
      t.map (fun k => csNat a b (L.equiv (Fin.castLE L.le k))) =
        (List.range' Q₀ d).map (fun q => some (R, q)) →
      IsMutationSeqDefined L.le (csSeed L i (CsDone a b R Q₀)) t ∧
        seedMutationSeq L.le (csSeed L i (CsDone a b R Q₀)) t =
          csSeed L i (CsDone a b R (b - a - 1)) := by
  intro d
  induction d with
  | zero =>
    intro Q₀ hQ t ht
    simp only [List.range'_zero, List.map_nil, List.map_eq_nil_iff] at ht
    subst ht
    rw [show Q₀ = b - a - 1 by omega]
    exact ⟨trivial, rfl⟩
  | succ d ih =>
    intro Q₀ hQ t ht
    rw [List.range'_succ, List.map_cons] at ht
    obtain ⟨k, t', rfl, hk, ht'⟩ := List.map_eq_cons_iff.1 ht
    obtain ⟨hR', hQ', hk'⟩ := csNat_eq_some hk
    obtain ⟨hne, hmut⟩ := seedMutation_csSeed L i k hR' hQ' hk'
    obtain ⟨h1, h2⟩ := ih (Q₀ + 1) (by omega) t' ht'
    exact ⟨⟨hne, by rw [hmut]; exact h1⟩, by rw [seedMutationSeq_cons, hmut, h2]⟩

/-- **The sweep of rows `R, …, 0`**: from the state `(R, 0)`, mutation along the rest of the
sequence is defined and reaches the last state. -/
theorem csSeed_rows (L : RectangleLabelling a b m n) (i : ℤ) (hc : 2 ≤ b - a) :
    ∀ R, R + 2 ≤ a → ∀ t : List (Fin n),
      t.map (fun k => csNat a b (L.equiv (Fin.castLE L.le k))) =
        (List.range (R + 1)).reverse.flatMap
          (fun p => (List.range (b - a - 1)).map fun q => some (p, q)) →
      IsMutationSeqDefined L.le (csSeed L i (CsDone a b R 0)) t ∧
        seedMutationSeq L.le (csSeed L i (CsDone a b R 0)) t =
          csSeed L i (CsDone a b 0 (b - a - 1)) := by
  intro R
  induction R with
  | zero =>
    intro _ t ht
    rw [zero_add, List.range_one, List.reverse_singleton, List.flatMap_singleton,
      List.range_eq_range'] at ht
    exact csSeed_row L i 0 (b - a - 1) 0 (by omega) t ht
  | succ R ih =>
    intro hR t ht
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons] at ht
    obtain ⟨t₁, t₂, rfl, ht₁, ht₂⟩ := List.map_eq_append_iff.1 ht
    rw [List.range_eq_range'] at ht₁
    obtain ⟨h1, h2⟩ := csSeed_row L i (R + 1) (b - a - 1) 0 (by omega) t₁ ht₁
    rw [csDone_end_row (R + 1) (by omega), Nat.add_sub_cancel] at h2
    obtain ⟨h3, h4⟩ := ih (by omega) t₂ ht₂
    refine ⟨(isMutationSeqDefined_append _ _ _ _).2 ⟨h1, by rw [h2]; exact h3⟩, ?_⟩
    rw [seedMutationSeq_append, h2, h4]

end Sequence

/-! ### The cyclic shift mutation sequence -/

/-- **The cyclic shift mutation sequence.** Let `2 ≤ a ≤ b - 2`, let `λ` be a rectangle labelling,
and let `s` be the sequence of the indices `λ⁻¹(p, q)` of the mutable vertices, listed with `p`
decreasing from `a - 1` to `1` and, for each `p`, with `q` increasing from `1` to `b - a - 1`
(`cyclicShiftOrder`). Then for every `i ∈ ℤ` the mutation `μ_s(Σ^i_{a,b}(λ))` is defined, and there
is a bijective restriction map `π` from `(m, n)` to `(m, n)` with `π(ℓ) = ℓ` for `ℓ ∈ [1, n]` such
that `μ_s(Σ^i_{a,b}(λ)) = (Σ^{i-1}_{a,b}(λ))^π`.

Each mutation is a three-term Plücker relation (`seedMutation_csSeed`), and `π` moves the frozen
vertices one step along the boundary of the rectangle (`csRot`). -/
@[cluster_algebras "lem_cyclic_shift_mutation"]
theorem rectanglesSeedShift_cyclicShift_mutation {a b m n : ℕ} (ha : 2 ≤ a) (hab : a + 2 ≤ b)
    (L : RectangleLabelling a b m n) (s : List (Fin n))
    (hs : s.map (fun k => L.equiv (Fin.castLE L.le k)) = cyclicShiftOrder a b) (i : ℤ) :
    IsMutationSeqDefined L.le (rectanglesSeedShift L i) s ∧
      ∃ π : ReindexingMap m n m n, π.IsRestriction ∧ Function.Bijective π ∧
        (∀ ℓ : Fin m, (ℓ : ℕ) < n → π ℓ = ℓ) ∧
        seedMutationSeq L.le (rectanglesSeedShift L i) s =
          (rectanglesSeedShift L (i - 1)).reindex L.le π := by
  have hc : 2 ≤ b - a := by omega
  have hs' : s.map (fun k => csNat a b (L.equiv (Fin.castLE L.le k))) =
      (List.range (a - 2 + 1)).reverse.flatMap
        (fun p => (List.range (b - a - 1)).map fun q => some (p, q)) := by
    have h := congrArg (List.map (csNat a b)) hs
    rw [List.map_map] at h
    rw [show a - 2 + 1 = a - 1 by omega]
    exact h.trans map_csNat_cyclicShiftOrder
  obtain ⟨hdef, heq⟩ := csSeed_rows L i hc (a - 2) (by omega) s hs'
  rw [rectanglesSeedShift_eq_csSeed L i]
  exact ⟨hdef, csReindex L ha hc, csReindex_isRestriction L ha hc, csReindex_bijective L ha hc,
    csReindex_of_lt L ha hc, heq.trans (csSeed_end L ha hc i)⟩

end ClusterAlgebras
