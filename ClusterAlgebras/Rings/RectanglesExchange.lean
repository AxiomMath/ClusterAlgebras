/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.RectanglesQuiver
public import ClusterAlgebras.Rings.Rotation
public import ClusterAlgebras.Rings.SLMinors

/-!
# The exchanges at the rectangles seed

Let `z` be the generic `a × b` matrix over `ℂ`, `c = b - a`, and `λ` a rectangle labelling. At a
mutable vertex `(p, q)` of the rectangles quiver `Q_{a,b}`, so `p ∈ [1, a - 1]` and
`q ∈ [1, c - 1]`, write
`u = c - q + 1`, `v = c - q + p`, `w = c + p + 1`, `x = u - 1`, `y = v + 1`, `t = w - 1`, so that
the label of the vertex is `J = J(p, q) = [u, v] ∪ [w, b]`. The labels of the neighbours of
`(p, q)` are obtained from `J` by exchanging one element of `{u, v, w}` for one of `{x, y, t}`.

The vertex `(p, q)` has degree four when `p = 1` or `q = 1`, and six otherwise. Mutating the
rectangles seed `Σ_{a,b}(λ)` at the index `k = λ⁻¹(p, q)` replaces `P_J` by

* `P_{(J ∖ {v, w}) ∪ {x, y}}` at a vertex of degree four, by the three-term Plücker relation
  (`seedMutation_rectanglesSeed_of_degree_four`);
* `Ω_{p,q} = P_{S∪{x,u,t}} P_{S∪{v,y,w}} - P_{S∪{x,u,w}} P_{S∪{v,y,t}}` at a vertex of degree six,
  where `S = J ∖ {u, v, w}`, by two three-term Plücker relations
  (`seedMutation_rectanglesSeed_of_degree_six`);

and in the second case `P_J` does not divide `Ω_{p,q}` in `ℂ[z]`
(`not_pluckerCoord_dvd_rectOmega`).

## Main definitions

* `ClusterAlgebras.rectColU`, `rectColV`, `rectColW`, `rectColX`, `rectColY`, `rectColT`: the
  columns `u, v, w, x, y, t` of a vertex.
* `ClusterAlgebras.rectBase`: the set `S = J(p, q) ∖ {u, v, w}`.
* `ClusterAlgebras.rectOmega`: the polynomial `Ω_{p,q}`, for a matrix over any commutative ring.
* `ClusterAlgebras.unitColMatrix`: the `0`/`1` matrix whose columns are prescribed unit vectors.

## Main results

* `ClusterAlgebras.rectLabel_q_succ` and its five siblings, `ClusterAlgebras.rectLabel_none_eq`:
  the labels of the neighbours of a vertex.
* `ClusterAlgebras.seedMutation_rectanglesSeed_of_degree_four`,
  `ClusterAlgebras.rectLabel_sdiff_union_ne`: the exchange at a vertex of degree four.
* `ClusterAlgebras.seedMutation_rectanglesSeed_of_degree_six`,
  `ClusterAlgebras.rectCol_lt_chain`, `ClusterAlgebras.rectCol_notMem_rectBase`: the exchange at a
  vertex of degree six.
* `ClusterAlgebras.not_pluckerCoord_dvd_rectOmega`: `P_{S∪{u,v,w}} ∤ Ω_{p,q}` in `ℂ[z]`.

## Implementation notes

* Rows, columns and rectangles are `0`-based, as in `rectLabel`: the vertex `some (p, q)` is
  FWZ's `(p + 1, q + 1)`, and FWZ's column `j` is column `j - 1`. So `u = c - q - 1`,
  `v = c - q - 1 + p`, `w = c + p + 1`, `x = c - q - 2`, `y = c - q + p`, `t = c + p`, and the
  vertex has degree four when `p = 0` or `q = 0`. The column `w` exists only for `p + 1 < a`, so
  `rectColW` takes that as a hypothesis; `x` is the truncated difference, which is `u - 1` for a
  mutable vertex.
* FWZ assume `2 ≤ a ≤ b - 2`, and `3 ≤ a ≤ b - 3` for the coprimality. Neither is used:
  a mutable vertex exists only when `a, b - a ≥ 2`, and one with `p, q ≥ 1` only when
  `a, b - a ≥ 3`. The exchange statements take the vertex as `λ(k)` for an index `k < n`, which
  makes it mutable; they still take `p + 1 < a` as a hypothesis, since `w` occurs in the
  statement. The coprimality, which mentions no labelling, takes the mutability of `(p, q)` as
  hypotheses.
* **Coprimality is proved by evaluation**, not by FWZ's specialization to `3 × b` matrices
  and degree count. If `P_J` divided `Ω_{p,q}`, then `Ω_{p,q}` would vanish at every matrix at
  which `P_J` vanishes. The `0`/`1` matrix `M` whose columns `u, v` are the unit vector `e₁`,
  columns `y, t` are `e₂`, columns `x, w` are `e₃`, and whose columns in `S` are the remaining
  unit vectors `e₄, …, e_a`, one each, has `P_J(M) = 0 = P_{S∪{v,y,t}}(M)`, two columns being
  equal, while `P_{S∪{x,u,t}}(M)` and `P_{S∪{v,y,w}}(M)` are `±1`, the columns being distinct unit
  vectors. So `Ω_{p,q}(M) = ±1 ≠ 0`. The argument works over any nontrivial commutative ring.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Matrix

variable {a b m n : ℕ}

/-! ### The columns of a vertex -/

/-- The column `u = c - q + 1` of the vertex `(p, q)` (`b - a - 1 - q` with `0`-based indices),
the least element of its label. -/
def rectColU (pq : Fin a × Fin (b - a)) : Fin b :=
  ⟨b - a - 1 - pq.2, by have := pq.2.isLt; omega⟩

/-- The column `v = c - q + p` of the vertex `(p, q)` (`b - a - 1 - q + p` with `0`-based
indices), the end of the first interval of its label. -/
def rectColV (pq : Fin a × Fin (b - a)) : Fin b :=
  ⟨b - a - 1 - pq.2 + pq.1, by have := pq.1.isLt; have := pq.2.isLt; omega⟩

/-- The column `w = c + p + 1` of the vertex `(p, q)` (`b - a + p + 1` with `0`-based indices),
the start of the second interval of its label; it exists when `p + 1 < a`. -/
def rectColW (pq : Fin a × Fin (b - a)) (hp : (pq.1 : ℕ) + 1 < a) : Fin b :=
  ⟨b - a + pq.1 + 1, by have := pq.2.isLt; omega⟩

/-- The column `x = u - 1` of the vertex `(p, q)` (`b - a - 2 - q` with `0`-based indices, the
truncated difference). -/
def rectColX (pq : Fin a × Fin (b - a)) : Fin b :=
  ⟨b - a - 2 - pq.2, by have := pq.2.isLt; omega⟩

/-- The column `y = v + 1` of the vertex `(p, q)` (`b - a - q + p` with `0`-based indices). -/
def rectColY (pq : Fin a × Fin (b - a)) : Fin b :=
  ⟨b - a - pq.2 + pq.1, by have := pq.1.isLt; have := pq.2.isLt; omega⟩

/-- The column `t = w - 1` of the vertex `(p, q)` (`b - a + p` with `0`-based indices). -/
def rectColT (pq : Fin a × Fin (b - a)) : Fin b :=
  ⟨b - a + pq.1, by have := pq.1.isLt; have := pq.2.isLt; omega⟩

/-- The set `S = J(p, q) ∖ {u, v, w}`. -/
def rectBase (pq : Fin a × Fin (b - a)) (hp : (pq.1 : ℕ) + 1 < a) : Finset (Fin b) :=
  rectLabel a b (some pq) \ {rectColU pq, rectColV pq, rectColW pq hp}

/-- The index of the column `u`. -/
@[simp] theorem val_rectColU (pq : Fin a × Fin (b - a)) :
    (rectColU pq : ℕ) = b - a - 1 - pq.2 := rfl

/-- The index of the column `v`. -/
@[simp] theorem val_rectColV (pq : Fin a × Fin (b - a)) :
    (rectColV pq : ℕ) = b - a - 1 - pq.2 + pq.1 := rfl

/-- The index of the column `w`. -/
@[simp] theorem val_rectColW (pq : Fin a × Fin (b - a)) (hp : (pq.1 : ℕ) + 1 < a) :
    (rectColW pq hp : ℕ) = b - a + pq.1 + 1 := rfl

/-- The index of the column `x`. -/
@[simp] theorem val_rectColX (pq : Fin a × Fin (b - a)) :
    (rectColX pq : ℕ) = b - a - 2 - pq.2 := rfl

/-- The index of the column `y`. -/
@[simp] theorem val_rectColY (pq : Fin a × Fin (b - a)) :
    (rectColY pq : ℕ) = b - a - pq.2 + pq.1 := rfl

/-- The index of the column `t`. -/
@[simp] theorem val_rectColT (pq : Fin a × Fin (b - a)) :
    (rectColT pq : ℕ) = b - a + pq.1 := rfl

/-- `S = J(p, q) ∖ {u, v, w}` is `[u + 1, v - 1] ∪ [w + 1, b]`. -/
theorem mem_rectBase_iff {pq : Fin a × Fin (b - a)} (hp : (pq.1 : ℕ) + 1 < a) {c : Fin b} :
    c ∈ rectBase pq hp ↔ (b - a - 1 - pq.2 < (c : ℕ) ∧ (c : ℕ) < b - a - 1 - pq.2 + pq.1) ∨
      b - a + pq.1 + 1 < (c : ℕ) := by
  have := pq.2.isLt
  simp only [rectBase, rectLabel, mem_sdiff, mem_filter, mem_univ, true_and, mem_insert,
    mem_singleton, Fin.ext_iff, val_rectColU, val_rectColV, val_rectColW]
  omega

/-- Proves an identity between labels and sets of columns by comparing column indices. -/
local macro "rect_ext" : tactic =>
  `(tactic| (ext c; simp only [rectLabel, mem_rectBase_iff, mem_union, mem_sdiff, mem_insert,
    mem_erase, mem_singleton, mem_filter, mem_univ, true_and, ne_eq, Fin.ext_iff, val_rectColU,
    val_rectColV, val_rectColW, val_rectColX, val_rectColY, val_rectColT]; omega))

/-- The label of a rectangle has `a` elements. -/
theorem card_rectLabel_some (pq : Fin a × Fin (b - a)) : (rectLabel a b (some pq)).card = a := by
  obtain ⟨p, q⟩ := pq
  have hp := p.isLt
  have hq := q.isLt
  have h : (rectLabel a b (some (p, q))).map Fin.valEmbedding =
      Icc (b - a - 1 - q) (b - a - 1 - q + p) ∪ Icc (b - a + p + 1) (b - 1) := by
    ext c
    simp only [rectLabel, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_union, mem_Icc]
    refine ⟨fun ⟨x, hx, hxc⟩ => by have := x.isLt; omega, fun h => ⟨⟨c, by omega⟩, ?_, rfl⟩⟩
    simp only
    omega
  rw [← card_map Fin.valEmbedding, h, card_union_of_disjoint, Nat.card_Icc, Nat.card_Icc]
  · omega
  · exact disjoint_left.2 fun c h1 h2 => by simp only [mem_Icc] at h1 h2; omega

/-- The label of a rectangle of positive height has `a - 3` elements outside `{u, v, w}`. -/
theorem card_rectBase {pq : Fin a × Fin (b - a)} (hp : (pq.1 : ℕ) + 1 < a)
    (hp1 : 1 ≤ (pq.1 : ℕ)) : (rectBase pq hp).card + 3 = a := by
  have := pq.2.isLt
  have hsub : {rectColU pq, rectColV pq, rectColW pq hp} ⊆ rectLabel a b (some pq) := by
    intro c hc
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp [rectLabel, rectColU, rectColV, rectColW] <;> omega
  have h3 : ({rectColU pq, rectColV pq, rectColW pq hp} : Finset (Fin b)).card = 3 :=
    card_eq_three.2 ⟨_, _, _, by simp [rectColU, rectColV, Fin.ext_iff]; omega,
      by simp [rectColU, rectColW, Fin.ext_iff]; omega,
      by simp [rectColV, rectColW, Fin.ext_iff]; omega, rfl⟩
  have h := card_rectLabel_some (a := a) (b := b) pq
  rw [rectBase, card_sdiff_of_subset hsub, h3]
  have := card_le_card hsub
  omega

/-! ### The labels of the neighbours -/

/-- The label of `(p, q + 1)`: `J(p, q + 1) = (J ∖ {v}) ∪ {x}`. -/
theorem rectLabel_q_succ {p p' : Fin a} {q q' : Fin (b - a)} (hp : (p' : ℕ) = p)
    (hq : (q' : ℕ) = q + 1) :
    rectLabel a b (some (p', q')) =
      insert (rectColX (p, q)) ((rectLabel a b (some (p, q))).erase (rectColV (p, q))) := by
  have := p.isLt; have := q.isLt; have := p'.isLt; have := q'.isLt
  rect_ext

/-- The label of `(p + 1, q)`: `J(p + 1, q) = (J ∖ {w}) ∪ {y}`. -/
theorem rectLabel_p_succ {p p' : Fin a} {q q' : Fin (b - a)} (hp : (p' : ℕ) = p + 1)
    (hq : (q' : ℕ) = q) :
    rectLabel a b (some (p', q')) = insert (rectColY (p, q))
      ((rectLabel a b (some (p, q))).erase
        (rectColW (p, q) (by have := p'.isLt; dsimp only; omega))) := by
  have := p.isLt; have := q.isLt; have := p'.isLt; have := q'.isLt
  rect_ext

/-- The label of `(p - 1, q - 1)`: `J(p - 1, q - 1) = (J ∖ {u}) ∪ {t}`. -/
theorem rectLabel_pred_pred {p p' : Fin a} {q q' : Fin (b - a)} (hp : (p' : ℕ) + 1 = p)
    (hq : (q' : ℕ) + 1 = q) :
    rectLabel a b (some (p', q')) =
      insert (rectColT (p, q)) ((rectLabel a b (some (p, q))).erase (rectColU (p, q))) := by
  have := p.isLt; have := q.isLt; have := p'.isLt; have := q'.isLt
  rect_ext

/-- The label of `(p, q - 1)`: `J(p, q - 1) = (J ∖ {u}) ∪ {y}`. -/
theorem rectLabel_q_pred {p p' : Fin a} {q q' : Fin (b - a)} (hp : (p' : ℕ) = p)
    (hq : (q' : ℕ) + 1 = q) :
    rectLabel a b (some (p', q')) =
      insert (rectColY (p, q)) ((rectLabel a b (some (p, q))).erase (rectColU (p, q))) := by
  have := p.isLt; have := q.isLt; have := p'.isLt; have := q'.isLt
  rect_ext

/-- The label of `(p - 1, q)`: `J(p - 1, q) = (J ∖ {v}) ∪ {t}`. -/
theorem rectLabel_p_pred {p p' : Fin a} {q q' : Fin (b - a)} (hp : (p' : ℕ) + 1 = p)
    (hq : (q' : ℕ) = q) :
    rectLabel a b (some (p', q')) =
      insert (rectColT (p, q)) ((rectLabel a b (some (p, q))).erase (rectColV (p, q))) := by
  have := p.isLt; have := q.isLt; have := p'.isLt; have := q'.isLt
  rect_ext

/-- The label of `(p + 1, q + 1)`: `J(p + 1, q + 1) = (J ∖ {w}) ∪ {x}`. -/
theorem rectLabel_succ_succ {p p' : Fin a} {q q' : Fin (b - a)} (hp : (p' : ℕ) = p + 1)
    (hq : (q' : ℕ) = q + 1) :
    rectLabel a b (some (p', q')) = insert (rectColX (p, q))
      ((rectLabel a b (some (p, q))).erase
        (rectColW (p, q) (by have := p'.isLt; dsimp only; omega))) := by
  have := p.isLt; have := q.isLt; have := p'.isLt; have := q'.isLt
  rect_ext

/-- The label of the empty rectangle: `J(∅) = (J(1, 1) ∖ {u}) ∪ {y}`. -/
theorem rectLabel_none_eq {p : Fin a} {q : Fin (b - a)} (hp : (p : ℕ) = 0) (hq : (q : ℕ) = 0) :
    rectLabel a b none =
      insert (rectColY (p, q)) ((rectLabel a b (some (p, q))).erase (rectColU (p, q))) := by
  have := p.isLt; have := q.isLt
  rect_ext

/-! ### The exchange polynomial at a vertex of the rectangles seed -/

section Exchange

/-- At a mutable vertex `w`, the positive part of `β(v, w)` is `1` exactly for the steps
`v → w`. -/
theorem toNat_signedCount_rectArrows {v w : RectVertex a b} (hw : ¬RectFrozen a b w) :
    (signedCount (rectArrows a b) v w).toNat = if RectStep a b v w then 1 else 0 := by
  have h2 := not_rectStep_and_rectStep v w
  simp only [signedCount, rectArrows_eq_ite, hw, and_false, not_false_eq_true, true_and,
    false_and]
  split_ifs <;> simp_all

/-- At a mutable vertex `w`, the negative part of `β(v, w)` is `1` exactly for the steps
`w → v`. -/
theorem toNat_neg_signedCount_rectArrows {v w : RectVertex a b} (hw : ¬RectFrozen a b w) :
    (-signedCount (rectArrows a b) v w).toNat = if RectStep a b w v then 1 else 0 := by
  have h2 := not_rectStep_and_rectStep v w
  simp only [signedCount, rectArrows_eq_ite, hw, and_false, not_false_eq_true, true_and,
    false_and]
  split_ifs <;> simp_all

/-- The entry of `Σ_{a,b}(λ)` in position `i` is `P_{J(λ(i))}`. -/
theorem rectanglesSeed_extCluster (L : RectangleLabelling a b m n) (i : Fin m) :
    (rectanglesSeed L).extCluster i =
      algebraMap _ _ (pluckerCoord (complexGenericMatrix a b) (rectLabel a b (L.equiv i))) := by
  simp [rectanglesSeed, rectanglesSeedShift]

/-- The vertex `λ(k)` of a mutable index `k` is a mutable rectangle. -/
theorem RectangleLabelling.lt_of_equiv_castLE_eq_some (L : RectangleLabelling a b m n)
    (k : Fin n) {p : Fin a} {q : Fin (b - a)} (hk : L.equiv (Fin.castLE L.le k) = some (p, q)) :
    (p : ℕ) + 1 < a ∧ (q : ℕ) + 1 < b - a := by
  have h := L.not_rectFrozen_castLE k
  rw [hk] at h
  simp only [RectFrozen, not_or] at h
  have := p.isLt
  have := q.isLt
  omega

/-- **The exchange relation at the rectangles seed.** The entry in position `k` of
`μ_k(Σ_{a,b}(λ))` is `(∏_{v → λ(k)} P_{J(v)} + ∏_{λ(k) → v} P_{J(v)}) / P_{J(λ(k))}`. -/
theorem seedMutation_rectanglesSeed_extCluster_castLE (L : RectangleLabelling a b m n)
    (k : Fin n) :
    (seedMutation L.le (rectanglesSeed L) k).extCluster (Fin.castLE L.le k) =
      algebraMap _ _
        ((∏ v ∈ univ.filter (RectStep a b · (L.equiv (Fin.castLE L.le k))),
            pluckerCoord (complexGenericMatrix a b) (rectLabel a b v)) +
          ∏ v ∈ univ.filter (RectStep a b (L.equiv (Fin.castLE L.le k))),
            pluckerCoord (complexGenericMatrix a b) (rectLabel a b v)) /
      algebraMap _ _ (pluckerCoord (complexGenericMatrix a b)
        (rectLabel a b (L.equiv (Fin.castLE L.le k)))) := by
  have hw := L.not_rectFrozen_castLE k
  simp only [seedMutation, Function.update_self, exchangeMonomialPos_eq_prod,
    exchangeMonomialNeg_eq_prod, rectanglesSeed_extCluster, map_add, map_prod]
  congr 2
  · rw [prod_filter]
    refine Fintype.prod_equiv L.equiv _ _ fun i => ?_
    simp only [rectanglesSeed, rectanglesSeedShift, Matrix.of_apply,
      toNat_signedCount_rectArrows hw]
    split_ifs <;> simp
  · rw [prod_filter]
    refine Fintype.prod_equiv L.equiv _ _ fun i => ?_
    simp only [rectanglesSeed, rectanglesSeedShift, Matrix.of_apply,
      toNat_neg_signedCount_rectArrows hw]
    split_ifs <;> simp

/-- The Plücker coordinate of a label is a nonzero polynomial. -/
theorem pluckerCoord_rectLabel_some_ne_zero (pq : Fin a × Fin (b - a)) :
    pluckerCoord (complexGenericMatrix a b) (rectLabel a b (some pq)) ≠ 0 :=
  minor_complexGenericMatrix_ne_zero (by rw [card_rectLabel_some, card_univ, Fintype.card_fin])

/-- A product over three distinct elements. -/
private theorem prod_three {M α : Type*} [CommMonoid M] [DecidableEq α] (f : α → M)
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∏ v ∈ ({x, y, z} : Finset α), f v = f x * f y * f z := by
  rw [prod_insert (by simp [hxy, hxz]), prod_pair hyz, mul_assoc]

end Exchange

/-! ### Vertices of degree four -/

section DegreeFour

variable {M : Type*} [CommMonoid M]

/-- At a vertex `(p, q)` of degree four, the steps into `(p, q)` come from `(p + 1, q + 1)` and
from one more vertex, whose label is `S' ∪ {y, w}`, where `S' = J ∖ {v, w}`. -/
private theorem exists_filter_rectStep_in_of_degree_four {p : Fin a} {q : Fin (b - a)}
    (hp : (p : ℕ) + 1 < a) (hq : (q : ℕ) + 1 < b - a) (hdeg : (p : ℕ) = 0 ∨ (q : ℕ) = 0) :
    ∃ v₀ : RectVertex a b,
      univ.filter (RectStep a b · (some (p, q))) = {some (⟨p + 1, hp⟩, ⟨q + 1, hq⟩), v₀} ∧
      rectLabel a b v₀ = rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
        {rectColY (p, q), rectColW (p, q) hp} := by
  have := p.isLt
  have := q.isLt
  by_cases hq0 : (q : ℕ) = 0
  · by_cases hp0 : (p : ℕ) = 0
    · refine ⟨none, ?_, by rect_ext⟩
      ext v
      rcases v with _ | ⟨p', q'⟩
      · simp [RectStep]; omega
      · simp only [RectStep, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
          Option.some.injEq, Prod.ext_iff, Fin.ext_iff, reduceCtorEq, or_false]
        omega
    · refine ⟨some (⟨p - 1, by omega⟩, q), ?_, by rect_ext⟩
      ext v
      rcases v with _ | ⟨p', q'⟩
      · simp [RectStep]; omega
      · simp only [RectStep, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
          Option.some.injEq, Prod.ext_iff, Fin.ext_iff]
        omega
  · refine ⟨some (p, ⟨q - 1, by omega⟩), ?_, by rect_ext⟩
    ext v
    rcases v with _ | ⟨p', q'⟩
    · simp [RectStep]; omega
    · simp only [RectStep, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Option.some.injEq, Prod.ext_iff, Fin.ext_iff]
      omega

/-- At a vertex of degree four, the steps into `(p, q)` come from `(p + 1, q + 1)`, whose label
is `S' ∪ {x, v}`, and from one vertex with label `S' ∪ {y, w}`, where `S' = J ∖ {v, w}`. -/
theorem prod_filter_rectStep_in_of_degree_four {p : Fin a} {q : Fin (b - a)}
    (hp : (p : ℕ) + 1 < a) (hq : (q : ℕ) + 1 < b - a) (hdeg : (p : ℕ) = 0 ∨ (q : ℕ) = 0)
    (g : Finset (Fin b) → M) :
    ∏ v ∈ univ.filter (RectStep a b · (some (p, q))), g (rectLabel a b v) =
      g (rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
          {rectColX (p, q), rectColV (p, q)}) *
        g (rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
          {rectColY (p, q), rectColW (p, q) hp}) := by
  have := p.isLt
  have := q.isLt
  have hsucc : rectLabel a b (some (⟨p + 1, hp⟩, ⟨q + 1, hq⟩)) =
      rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
        {rectColX (p, q), rectColV (p, q)} := by
    rect_ext
  obtain ⟨v₀, hv₀, hJ⟩ := exists_filter_rectStep_in_of_degree_four hp hq hdeg
  have hne : some (⟨(p : ℕ) + 1, hp⟩, ⟨(q : ℕ) + 1, hq⟩) ≠ v₀ := by
    intro h
    have : rectColX (p, q) ∈ rectLabel a b (some (p, q)) \
        {rectColV (p, q), rectColW (p, q) hp} ∪ {rectColY (p, q), rectColW (p, q) hp} := by
      rw [← hJ, ← h, hsucc]; simp
    simp only [rectLabel, rectColX, rectColY, rectColV, rectColW, mem_union, mem_sdiff,
      mem_insert, mem_singleton, mem_filter, mem_univ, true_and, Fin.ext_iff] at this
    omega
  rw [hv₀, prod_pair hne, hsucc, hJ]

/-- At a vertex of degree four, the steps out of `(p, q)` go to `(p, q + 1)` and `(p + 1, q)`,
whose labels are `S' ∪ {x, w}` and `S' ∪ {v, y}`, where `S' = J ∖ {v, w}`. -/
theorem prod_filter_rectStep_out_of_degree_four {p : Fin a} {q : Fin (b - a)}
    (hp : (p : ℕ) + 1 < a) (hq : (q : ℕ) + 1 < b - a) (hdeg : (p : ℕ) = 0 ∨ (q : ℕ) = 0)
    (g : Finset (Fin b) → M) :
    ∏ v ∈ univ.filter (RectStep a b (some (p, q)) ·), g (rectLabel a b v) =
      g (rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
          {rectColX (p, q), rectColW (p, q) hp}) *
        g (rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
          {rectColV (p, q), rectColY (p, q)}) := by
  have := p.isLt
  have := q.isLt
  have hset : univ.filter (RectStep a b (some (p, q)) ·) =
      {some (p, ⟨q + 1, hq⟩), some (⟨p + 1, hp⟩, q)} := by
    ext v
    rcases v with _ | ⟨p', q'⟩
    · simp [RectStep]
    · simp only [RectStep, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Option.some.injEq, Prod.ext_iff, Fin.ext_iff]
      omega
  rw [hset, prod_pair (by simp [Fin.ext_iff])]
  congr 2 <;> rect_ext

/-- **The exchange at a vertex of degree four.** If `λ(k) = (p, q)` with `p = 1` or `q = 1`
(`0` here), the entry in position `k` of `μ_k(Σ_{a,b}(λ))` is
`P_{(J ∖ {v, w}) ∪ {u - 1, v + 1}}`, where `J = J(p, q)`. -/
@[cluster_algebras "lem_rectangles_degree_four"]
theorem seedMutation_rectanglesSeed_of_degree_four (L : RectangleLabelling a b m n) (k : Fin n)
    {p : Fin a} {q : Fin (b - a)} (hk : L.equiv (Fin.castLE L.le k) = some (p, q))
    (hp : (p : ℕ) + 1 < a) (hdeg : (p : ℕ) = 0 ∨ (q : ℕ) = 0) :
    (seedMutation L.le (rectanglesSeed L) k).extCluster (Fin.castLE L.le k) =
      algebraMap _ _ (pluckerCoord (complexGenericMatrix a b)
        (rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
          {rectColX (p, q), rectColY (p, q)})) := by
  have hq := (L.lt_of_equiv_castLE_eq_some k hk).2
  have := p.isLt
  have := q.isLt
  set S := rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp}
  have hJ : rectLabel a b (some (p, q)) = S ∪ {rectColV (p, q), rectColW (p, q) hp} := by
    ext c
    simp only [S, rectLabel, rectColV, rectColW, mem_union, mem_sdiff, mem_insert,
      mem_singleton, mem_filter, mem_univ, true_and, Fin.ext_iff]
    omega
  have hS : ∀ c ∈ ({rectColX (p, q), rectColV (p, q), rectColY (p, q), rectColW (p, q) hp} :
      Finset (Fin b)), c ∉ S := by
    intro c hc
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [S, rectLabel, rectColX, rectColV, rectColY, rectColW, Fin.ext_iff] <;> omega
  have h3 := pluckerCoord_union_mul_pluckerCoord_union (complexGenericMatrix a b) S
    (α := rectColX (p, q)) (β := rectColV (p, q)) (γ := rectColY (p, q))
    (δ := rectColW (p, q) hp) (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp))
    (hS _ (by simp)) (by simp only [Fin.lt_def, val_rectColX, val_rectColV]; omega)
    (by simp only [Fin.lt_def, val_rectColV, val_rectColY]; omega)
    (by simp only [Fin.lt_def, val_rectColY, val_rectColW]; omega)
  have hJ' : pluckerCoord (complexGenericMatrix a b) (rectLabel a b (some (p, q))) =
      pluckerCoord (complexGenericMatrix a b) (S ∪ {rectColV (p, q), rectColW (p, q) hp}) :=
    congrArg _ hJ
  rw [seedMutation_rectanglesSeed_extCluster_castLE, hk,
    prod_filter_rectStep_in_of_degree_four hp hq hdeg,
    prod_filter_rectStep_out_of_degree_four hp hq hdeg, div_eq_iff, ← map_mul]
  · congr 1
    rw [hJ', h3]
  · exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (pluckerCoord_rectLabel_some_ne_zero _)

/-- **The new label at a vertex of degree four is new**: `(J ∖ {v, w}) ∪ {u - 1, v + 1} ≠ J`,
since `u - 1 ∉ J`. -/
@[cluster_algebras "lem_rectangles_degree_four"]
theorem rectLabel_sdiff_union_ne {p : Fin a} {q : Fin (b - a)} (hp : (p : ℕ) + 1 < a)
    (hq : (q : ℕ) + 1 < b - a) :
    rectLabel a b (some (p, q)) \ {rectColV (p, q), rectColW (p, q) hp} ∪
      {rectColX (p, q), rectColY (p, q)} ≠ rectLabel a b (some (p, q)) := by
  intro h
  have : rectColX (p, q) ∈ rectLabel a b (some (p, q)) := by rw [← h]; simp
  simp only [rectLabel, rectColX, mem_filter, mem_univ, true_and] at this
  omega

end DegreeFour

/-! ### Vertices of degree six -/

section DegreeSix

variable {R : Type*} [CommRing R]

/-- **The degree-six exchange identity.** For a set `S` of columns of a matrix `z` and columns
`x < u < v < y < t < w` outside `S`, writing `P_{Sxut}` for `P_{S∪{x,u,t}}(z)` and so on,
`P_{Suvw} (P_{Sxut} P_{Svyw} - P_{Sxuw} P_{Svyt}) =
P_{Sxuv} P_{Sutw} P_{Svyw} + P_{Sxuw} P_{Suvy} P_{Svtw}`. -/
theorem pluckerCoord_mul_omega (z : Matrix (Fin a) (Fin b) R) (S : Finset (Fin b))
    {x u v y t w : Fin b} (hx : x ∉ S) (hu : u ∉ S) (hv : v ∉ S) (hy : y ∉ S) (ht : t ∉ S)
    (hw : w ∉ S) (hxu : x < u) (huv : u < v) (hvy : v < y) (hyt : y < t) (htw : t < w) :
    pluckerCoord z (S ∪ {u, v, w}) * (pluckerCoord z (S ∪ {x, u, t}) *
        pluckerCoord z (S ∪ {v, y, w}) -
      pluckerCoord z (S ∪ {x, u, w}) * pluckerCoord z (S ∪ {v, y, t})) =
      pluckerCoord z (S ∪ {x, u, v}) * pluckerCoord z (S ∪ {u, t, w}) *
          pluckerCoord z (S ∪ {v, y, w}) +
        pluckerCoord z (S ∪ {x, u, w}) * pluckerCoord z (S ∪ {u, v, y}) *
          pluckerCoord z (S ∪ {v, t, w}) := by
  have h1 := pluckerCoord_union_mul_pluckerCoord_union z (insert v S)
    (α := u) (β := y) (γ := t) (δ := w) (by simp [hu, huv.ne]) (by simp [hy, hvy.ne'])
    (by simp [ht, (hvy.trans hyt).ne']) (by simp [hw, (hvy.trans (hyt.trans htw)).ne'])
    (huv.trans hvy) hyt htw
  have h2 := pluckerCoord_union_mul_pluckerCoord_union z (insert u S)
    (α := x) (β := v) (γ := t) (δ := w) (by simp [hx, hxu.ne]) (by simp [hv, huv.ne'])
    (by simp [ht, (huv.trans (hvy.trans hyt)).ne'])
    (by simp [hw, (huv.trans (hvy.trans (hyt.trans htw))).ne'])
    (hxu.trans huv) (hvy.trans hyt) htw
  have e : ∀ (c d e : Fin b) (X : Finset (Fin b)), X = {c, d, e} →
      insert c S ∪ {d, e} = S ∪ X := by
    rintro c d e X rfl
    ext i; simp; tauto
  rw [e v u t {u, v, t} (by ext; simp; tauto), e v y w {v, y, w} rfl,
    e v u y {u, v, y} (by ext; simp; tauto), e v t w {v, t, w} rfl,
    e v u w {u, v, w} (by ext; simp; tauto), e v y t {v, y, t} rfl] at h1
  rw [e u x t {x, u, t} (by ext; simp; tauto), e u v w {u, v, w} rfl,
    e u x v {x, u, v} (by ext; simp; tauto), e u t w {u, t, w} rfl,
    e u x w {x, u, w} (by ext; simp; tauto), e u v t {u, v, t} rfl] at h2
  linear_combination (pluckerCoord z (S ∪ {v, y, w})) * h2 +
    (pluckerCoord z (S ∪ {x, u, w})) * h1

/-- The polynomial `Ω_{p,q} = P_{S∪{x,u,t}} P_{S∪{v,y,w}} - P_{S∪{x,u,w}} P_{S∪{v,y,t}}` in the
Plücker coordinates of a matrix `z`, where `S = J(p, q) ∖ {u, v, w}`: the new entry at a vertex of
degree six, for `z` the generic matrix. -/
@[cluster_algebras "lem_rectangles_degree_six"]
def rectOmega (z : Matrix (Fin a) (Fin b) R) (pq : Fin a × Fin (b - a))
    (hp : (pq.1 : ℕ) + 1 < a) : R :=
  pluckerCoord z (rectBase pq hp ∪ {rectColX pq, rectColU pq, rectColT pq}) *
      pluckerCoord z (rectBase pq hp ∪ {rectColV pq, rectColY pq, rectColW pq hp}) -
    pluckerCoord z (rectBase pq hp ∪ {rectColX pq, rectColU pq, rectColW pq hp}) *
      pluckerCoord z (rectBase pq hp ∪ {rectColV pq, rectColY pq, rectColT pq})

/-- A ring homomorphism carries `Ω_{p,q}(z)` to `Ω_{p,q}` of the image of `z`. -/
theorem RingHom.map_rectOmega {R' : Type*} [CommRing R'] (f : R →+* R')
    (z : Matrix (Fin a) (Fin b) R) (pq : Fin a × Fin (b - a)) (hp : (pq.1 : ℕ) + 1 < a) :
    f (rectOmega z pq hp) = rectOmega (z.map f) pq hp := by
  simp [rectOmega, RingHom.map_pluckerCoord]

/-- **The columns of a vertex of degree six are in order**: `x < u < v < y < t < w`. -/
@[cluster_algebras "lem_rectangles_degree_six"]
theorem rectCol_lt_chain {pq : Fin a × Fin (b - a)} (hp : (pq.1 : ℕ) + 1 < a)
    (hq : (pq.2 : ℕ) + 1 < b - a) (hp1 : 1 ≤ (pq.1 : ℕ)) (hq1 : 1 ≤ (pq.2 : ℕ)) :
    rectColX pq < rectColU pq ∧ rectColU pq < rectColV pq ∧ rectColV pq < rectColY pq ∧
      rectColY pq < rectColT pq ∧ rectColT pq < rectColW pq hp := by
  simp only [Fin.lt_def, val_rectColX, val_rectColU, val_rectColV, val_rectColY, val_rectColT,
    val_rectColW]
  omega

/-- **The columns of a vertex of degree six lie outside `S = J(p, q) ∖ {u, v, w}`.** -/
@[cluster_algebras "lem_rectangles_degree_six"]
theorem rectCol_notMem_rectBase {pq : Fin a × Fin (b - a)} (hp : (pq.1 : ℕ) + 1 < a)
    (hq : (pq.2 : ℕ) + 1 < b - a) :
    rectColX pq ∉ rectBase pq hp ∧ rectColU pq ∉ rectBase pq hp ∧
      rectColV pq ∉ rectBase pq hp ∧ rectColY pq ∉ rectBase pq hp ∧
      rectColT pq ∉ rectBase pq hp ∧ rectColW pq hp ∉ rectBase pq hp := by
  have := pq.1.isLt
  simp only [mem_rectBase_iff, val_rectColX, val_rectColU, val_rectColV, val_rectColY,
    val_rectColT, val_rectColW]
  omega

/-- The steps into a vertex `(p, q)` of degree six come from `(p, q - 1)`, `(p - 1, q)` and
`(p + 1, q + 1)`, whose labels are `S ∪ {v, y, w}`, `S ∪ {u, t, w}` and `S ∪ {x, u, v}`. -/
theorem prod_filter_rectStep_in_of_degree_six {M : Type*} [CommMonoid M] {p : Fin a}
    {q : Fin (b - a)} (hp : (p : ℕ) + 1 < a) (hq : (q : ℕ) + 1 < b - a) (hp1 : 1 ≤ (p : ℕ))
    (hq1 : 1 ≤ (q : ℕ)) (g : Finset (Fin b) → M) :
    ∏ v ∈ univ.filter (RectStep a b · (some (p, q))), g (rectLabel a b v) =
      g (rectBase (p, q) hp ∪ {rectColV (p, q), rectColY (p, q), rectColW (p, q) hp}) *
        g (rectBase (p, q) hp ∪ {rectColU (p, q), rectColT (p, q), rectColW (p, q) hp}) *
        g (rectBase (p, q) hp ∪ {rectColX (p, q), rectColU (p, q), rectColV (p, q)}) := by
  have := p.isLt
  have := q.isLt
  have hset : univ.filter (RectStep a b · (some (p, q))) =
      {some (p, ⟨q - 1, by omega⟩), some (⟨p - 1, by omega⟩, q),
        some (⟨p + 1, hp⟩, ⟨q + 1, hq⟩)} := by
    ext v
    rcases v with _ | ⟨p', q'⟩
    · simp [RectStep]; omega
    · simp only [RectStep, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Option.some.injEq, Prod.ext_iff, Fin.ext_iff]
      omega
  rw [hset, prod_three _ (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff])]
  congr 1
  · congr 1 <;> congr 1 <;> rect_ext
  · congr 1; rect_ext

/-- The steps out of a vertex `(p, q)` of degree six go to `(p, q + 1)`, `(p + 1, q)` and
`(p - 1, q - 1)`, whose labels are `S ∪ {x, u, w}`, `S ∪ {u, v, y}` and `S ∪ {v, t, w}`. -/
theorem prod_filter_rectStep_out_of_degree_six {M : Type*} [CommMonoid M] {p : Fin a}
    {q : Fin (b - a)} (hp : (p : ℕ) + 1 < a) (hq : (q : ℕ) + 1 < b - a) (hp1 : 1 ≤ (p : ℕ))
    (hq1 : 1 ≤ (q : ℕ)) (g : Finset (Fin b) → M) :
    ∏ v ∈ univ.filter (RectStep a b (some (p, q)) ·), g (rectLabel a b v) =
      g (rectBase (p, q) hp ∪ {rectColX (p, q), rectColU (p, q), rectColW (p, q) hp}) *
        g (rectBase (p, q) hp ∪ {rectColU (p, q), rectColV (p, q), rectColY (p, q)}) *
        g (rectBase (p, q) hp ∪ {rectColV (p, q), rectColT (p, q), rectColW (p, q) hp}) := by
  have := p.isLt
  have := q.isLt
  have hset : univ.filter (RectStep a b (some (p, q)) ·) =
      {some (p, ⟨q + 1, hq⟩), some (⟨p + 1, hp⟩, q),
        some (⟨p - 1, by omega⟩, ⟨q - 1, by omega⟩)} := by
    ext v
    rcases v with _ | ⟨p', q'⟩
    · simp [RectStep]
    · simp only [RectStep, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
        Option.some.injEq, Prod.ext_iff, Fin.ext_iff]
      omega
  rw [hset, prod_three _ (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff]; omega)]
  congr 1
  · congr 1 <;> congr 1 <;> rect_ext
  · congr 1; rect_ext

/-- **The exchange at a vertex of degree six.** If `λ(k) = (p, q)` with `p, q ≥ 2` (`≥ 1` here),
the entry in position `k` of `μ_k(Σ_{a,b}(λ))` is `Ω_{p,q}`. -/
@[cluster_algebras "lem_rectangles_degree_six"]
theorem seedMutation_rectanglesSeed_of_degree_six (L : RectangleLabelling a b m n) (k : Fin n)
    {p : Fin a} {q : Fin (b - a)} (hk : L.equiv (Fin.castLE L.le k) = some (p, q))
    (hp : (p : ℕ) + 1 < a) (hp1 : 1 ≤ (p : ℕ)) (hq1 : 1 ≤ (q : ℕ)) :
    (seedMutation L.le (rectanglesSeed L) k).extCluster (Fin.castLE L.le k) =
      algebraMap _ _ (rectOmega (complexGenericMatrix a b) (p, q) hp) := by
  have hq := (L.lt_of_equiv_castLE_eq_some k hk).2
  have := p.isLt
  have := q.isLt
  have hJ' : pluckerCoord (complexGenericMatrix a b) (rectLabel a b (some (p, q))) =
      pluckerCoord (complexGenericMatrix a b)
        (rectBase (p, q) hp ∪ {rectColU (p, q), rectColV (p, q), rectColW (p, q) hp}) := by
    congr 1; rect_ext
  obtain ⟨hxu, huv, hvy, hyt, htw⟩ := rectCol_lt_chain (pq := (p, q)) hp hq hp1 hq1
  obtain ⟨hx, hu, hv, hy, ht, hw⟩ := rectCol_notMem_rectBase (pq := (p, q)) hp hq
  have h := pluckerCoord_mul_omega (complexGenericMatrix a b) _ hx hu hv hy ht hw hxu huv hvy
    hyt htw
  rw [seedMutation_rectanglesSeed_extCluster_castLE, hk,
    prod_filter_rectStep_in_of_degree_six hp hq hp1 hq1,
    prod_filter_rectStep_out_of_degree_six hp hq hp1 hq1, div_eq_iff, ← map_mul]
  · congr 1
    rw [hJ', rectOmega]
    linear_combination (-1 : ComplexPoly a b) * h
  · exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      (pluckerCoord_rectLabel_some_ne_zero _)

end DegreeSix

/-! ### Coprimality at a vertex of degree six -/

section Coprime

variable {K : Type*} [CommRing K]

variable (K) in
/-- The `0`/`1` matrix whose column `c` is the unit vector of row `ρ c`. -/
def unitColMatrix (ρ : Fin b → Fin a) : Matrix (Fin a) (Fin b) K :=
  Matrix.of fun r c => if ρ c = r then 1 else 0

/-- The entry of `unitColMatrix K ρ` in row `r` and column `c` is `1` if `ρ c = r` and `0`
otherwise. -/
@[simp]
theorem unitColMatrix_apply (ρ : Fin b → Fin a) (r : Fin a) (c : Fin b) :
    unitColMatrix K ρ r c = if ρ c = r then 1 else 0 :=
  rfl

/-- If `ρ` is injective on a set `C` of `a` columns, the columns `C` of `unitColMatrix K ρ` are
distinct unit vectors, so `P_C` is a unit. -/
theorem isUnit_pluckerCoord_unitColMatrix (ρ : Fin b → Fin a) {C : Finset (Fin b)}
    (hC : C.card = a) (hρ : Set.InjOn ρ C) :
    IsUnit (pluckerCoord (unitColMatrix K ρ) C) := by
  rw [pluckerCoord_eq_det _ hC]
  set e := C.orderEmbOfFin hC
  apply isUnit_det_of_left_inverse (B := ((unitColMatrix K ρ).submatrix id e)ᵀ)
  ext i j
  simp only [mul_apply, transpose_apply, submatrix_apply, id, unitColMatrix_apply,
    mul_ite, mul_one, mul_zero, one_apply]
  rw [sum_ite_eq, if_pos (mem_univ _)]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg]
    exact fun h' => h (e.injective (hρ (C.orderEmbOfFin_mem hC i) (C.orderEmbOfFin_mem hC j)
      h'))

/-- If `ρ` takes the same value at two columns of `C`, then `P_C(unitColMatrix K ρ) = 0`. -/
theorem pluckerCoord_unitColMatrix_eq_zero (ρ : Fin b → Fin a) {C : Finset (Fin b)}
    (hC : C.card = a) {c c' : Fin b} (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c')
    (h : ρ c = ρ c') : pluckerCoord (unitColMatrix K ρ) C = 0 := by
  rw [pluckerCoord_eq_det _ hC]
  obtain ⟨i, rfl⟩ : c ∈ Set.range (C.orderEmbOfFin hC) := by rwa [range_orderEmbOfFin]
  obtain ⟨j, rfl⟩ : c' ∈ Set.range (C.orderEmbOfFin hC) := by rwa [range_orderEmbOfFin]
  exact det_zero_of_column_eq (i := i) (j := j) (fun hij => hne (by rw [hij])) fun r => by
    simp [h]

/-- Evaluating the matrix of indeterminates at `unitColMatrix K ρ` gives `unitColMatrix K ρ`. -/
theorem mvPolynomialX_map_eval_unitColMatrix (ρ : Fin b → Fin a) :
    (mvPolynomialX (Fin a) (Fin b) K).map
      (MvPolynomial.eval fun rc => unitColMatrix K ρ rc.1 rc.2) = unitColMatrix K ρ := by
  ext r c
  simp [mvPolynomialX_apply]

/-- A set `S` together with three distinct columns outside it. -/
private theorem card_union_three {S : Finset (Fin b)} {α β γ : Fin b} (hα : α ∉ S)
    (hβ : β ∉ S) (hγ : γ ∉ S) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    (S ∪ {α, β, γ}).card = S.card + 3 := by
  rw [card_union_of_disjoint (by simp [hα, hβ, hγ]),
    card_eq_three.2 ⟨α, β, γ, hαβ, hαγ, hβγ, rfl⟩]

/-- The row assigned to a column `n` (`0`-based) of a vertex `(p, q)` of degree six: `0` to `u`
and `v`, `1` to `y` and `t`, `2` to `x` and `w`, and the rows `3, …, a - 1` in order to the
columns of `S = [u + 1, v - 1] ∪ [w + 1, b - 1]`. -/
private def omegaRow (a b p q n : ℕ) : ℕ :=
  if n = b - a - 1 - q ∨ n = b - a - 1 - q + p then 0
  else if n = b - a - q + p ∨ n = b - a + p then 1
  else if n = b - a - 2 - q ∨ n = b - a + p + 1 then 2
  else if n < b - a + p + 1 then n - (b - a - 1 - q) + 2
  else n - (b - a + p + 1) + p + 1

/-- The rows of the columns of `S ∪ {x, u, t}`. -/
private theorem omegaRow_cases_xut {a b p q n : ℕ} (hq : q + 1 < b - a)
    (hn : (b - a - 1 - q < n ∧ n < b - a - 1 - q + p) ∨ b - a + p + 1 < n ∨
      n = b - a - 2 - q ∨ n = b - a - 1 - q ∨ n = b - a + p) :
    (b - a - 1 - q < n ∧ n < b - a - 1 - q + p ∧
        omegaRow a b p q n = n - (b - a - 1 - q) + 2) ∨
      (b - a + p + 1 < n ∧ omegaRow a b p q n = n - (b - a + p + 1) + p + 1) ∨
      (n = b - a - 2 - q ∧ omegaRow a b p q n = 2) ∨
      (n = b - a - 1 - q ∧ omegaRow a b p q n = 0) ∨
      (n = b - a + p ∧ omegaRow a b p q n = 1) := by
  unfold omegaRow
  rcases hn with ⟨h1, h2⟩ | h | rfl | rfl | rfl <;> split_ifs <;> omega

/-- The rows of the columns of `S ∪ {v, y, w}`. -/
private theorem omegaRow_cases_vyw {a b p q n : ℕ} (hq : q + 1 < b - a)
    (hn : (b - a - 1 - q < n ∧ n < b - a - 1 - q + p) ∨ b - a + p + 1 < n ∨
      n = b - a - 1 - q + p ∨ n = b - a - q + p ∨ n = b - a + p + 1) :
    (b - a - 1 - q < n ∧ n < b - a - 1 - q + p ∧
        omegaRow a b p q n = n - (b - a - 1 - q) + 2) ∨
      (b - a + p + 1 < n ∧ omegaRow a b p q n = n - (b - a + p + 1) + p + 1) ∨
      (n = b - a - 1 - q + p ∧ omegaRow a b p q n = 0) ∨
      (n = b - a - q + p ∧ omegaRow a b p q n = 1) ∨
      (n = b - a + p + 1 ∧ omegaRow a b p q n = 2) := by
  unfold omegaRow
  rcases hn with ⟨h1, h2⟩ | h | rfl | rfl | rfl <;> split_ifs <;> omega

/-- The row `ρ(c)` of the unit vector in column `c` of the matrix of a vertex `(p, q)` of degree
six: `omegaRow`, cut off at `a - 1`. -/
private def omegaRowFin (p : Fin a) (q : Fin (b - a)) (c : Fin b) : Fin a :=
  ⟨min (omegaRow a b p q c) (a - 1), by have := p.isLt; omega⟩

/-- The columns of `S ∪ {x, u, t}` have distinct rows. -/
private theorem injOn_omegaRowFin_xut {p : Fin a} {q : Fin (b - a)} (hp : (p : ℕ) + 1 < a)
    (hq : (q : ℕ) + 1 < b - a) (hp1 : 1 ≤ (p : ℕ)) :
    Set.InjOn (omegaRowFin p q)
      ↑(rectBase (p, q) hp ∪ {rectColX (p, q), rectColU (p, q), rectColT (p, q)}) := by
  intro c hc c' hc' h
  have hm : ∀ d : Fin b, d ∈ (↑(rectBase (p, q) hp ∪
      {rectColX (p, q), rectColU (p, q), rectColT (p, q)}) : Set (Fin b)) →
      ((b - a - 1 - q < (d : ℕ) ∧ (d : ℕ) < b - a - 1 - q + p) ∨ b - a + p + 1 < (d : ℕ) ∨
        (d : ℕ) = b - a - 2 - q ∨ (d : ℕ) = b - a - 1 - q ∨ (d : ℕ) = b - a + p) := by
    intro d hd
    simp only [coe_union, coe_insert, coe_singleton, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, mem_coe, mem_rectBase_iff, Fin.ext_iff, val_rectColX,
      val_rectColU, val_rectColT] at hd
    exact or_assoc.1 hd
  have e := omegaRow_cases_xut hq (hm c hc)
  have e' := omegaRow_cases_xut hq (hm c' hc')
  simp only [omegaRowFin, Fin.mk.injEq] at h
  have := p.isLt
  have := q.isLt
  have := c.isLt
  have := c'.isLt
  ext
  omega

/-- The columns of `S ∪ {v, y, w}` have distinct rows. -/
private theorem injOn_omegaRowFin_vyw {p : Fin a} {q : Fin (b - a)} (hp : (p : ℕ) + 1 < a)
    (hq : (q : ℕ) + 1 < b - a) (hp1 : 1 ≤ (p : ℕ)) :
    Set.InjOn (omegaRowFin p q)
      ↑(rectBase (p, q) hp ∪ {rectColV (p, q), rectColY (p, q), rectColW (p, q) hp}) := by
  intro c hc c' hc' h
  have hm : ∀ d : Fin b, d ∈ (↑(rectBase (p, q) hp ∪
      {rectColV (p, q), rectColY (p, q), rectColW (p, q) hp}) : Set (Fin b)) →
      ((b - a - 1 - q < (d : ℕ) ∧ (d : ℕ) < b - a - 1 - q + p) ∨ b - a + p + 1 < (d : ℕ) ∨
        (d : ℕ) = b - a - 1 - q + p ∨ (d : ℕ) = b - a - q + p ∨
        (d : ℕ) = b - a + p + 1) := by
    intro d hd
    simp only [coe_union, coe_insert, coe_singleton, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, mem_coe, mem_rectBase_iff, Fin.ext_iff, val_rectColV,
      val_rectColY, val_rectColW] at hd
    exact or_assoc.1 hd
  have e := omegaRow_cases_vyw hq (hm c hc)
  have e' := omegaRow_cases_vyw hq (hm c' hc')
  simp only [omegaRowFin, Fin.mk.injEq] at h
  have := p.isLt
  have := q.isLt
  have := c.isLt
  have := c'.isLt
  ext
  omega

/-- **`P_{S∪{u,v,w}}` does not divide `Ω_{p,q}`**, for the matrix of indeterminates over a
nontrivial commutative ring and a mutable vertex `(p, q)` of degree six. -/
theorem not_pluckerCoord_dvd_rectOmega_mvPolynomialX [Nontrivial K] {p : Fin a}
    {q : Fin (b - a)} (hp : (p : ℕ) + 1 < a) (hq : (q : ℕ) + 1 < b - a) (hp1 : 1 ≤ (p : ℕ))
    (hq1 : 1 ≤ (q : ℕ)) :
    ¬pluckerCoord (mvPolynomialX (Fin a) (Fin b) K)
        (rectBase (p, q) hp ∪ {rectColU (p, q), rectColV (p, q), rectColW (p, q) hp}) ∣
      rectOmega (mvPolynomialX (Fin a) (Fin b) K) (p, q) hp := by
  have := p.isLt
  have := q.isLt
  obtain ⟨hxu, huv, hvy, hyt, htw⟩ := rectCol_lt_chain (pq := (p, q)) hp hq hp1 hq1
  obtain ⟨hx, hu, hv, hy, ht, hw⟩ := rectCol_notMem_rectBase (pq := (p, q)) hp hq
  have hcard := fun α β γ hα hβ hγ hαβ hαγ hβγ =>
    (card_union_three (S := rectBase (p, q) hp) (α := α) (β := β) (γ := γ) hα hβ hγ hαβ hαγ
      hβγ).trans (card_rectBase (pq := (p, q)) hp hp1)
  let ρ : Fin b → Fin a := omegaRowFin p q
  have hρuv : ρ (rectColU (p, q)) = ρ (rectColV (p, q)) := by
    have e := omegaRow_cases_xut (p := p) (n := (rectColU (p, q) : ℕ)) hq (by simp)
    have e' := omegaRow_cases_vyw (p := p) (n := (rectColV (p, q) : ℕ)) hq (by simp)
    simp only [ρ, omegaRowFin, Fin.mk.injEq, val_rectColU, val_rectColV] at e e' ⊢
    omega
  have hρyt : ρ (rectColY (p, q)) = ρ (rectColT (p, q)) := by
    have e := omegaRow_cases_vyw (p := p) (n := (rectColY (p, q) : ℕ)) hq (by simp)
    have e' := omegaRow_cases_xut (p := p) (n := (rectColT (p, q) : ℕ)) hq (by simp)
    simp only [ρ, omegaRowFin, Fin.mk.injEq, val_rectColY, val_rectColT] at e e' ⊢
    omega
  intro hdvd
  have h := map_dvd (MvPolynomial.eval fun rc => unitColMatrix K ρ rc.1 rc.2) hdvd
  rw [RingHom.map_pluckerCoord, RingHom.map_rectOmega, mvPolynomialX_map_eval_unitColMatrix,
    pluckerCoord_unitColMatrix_eq_zero ρ (hcard _ _ _ hu hv hw huv.ne (huv.trans (hvy.trans
      (hyt.trans htw))).ne (hvy.trans (hyt.trans htw)).ne) (c := rectColU (p, q))
      (c' := rectColV (p, q)) (by simp) (by simp) huv.ne hρuv,
    zero_dvd_iff, rectOmega,
    pluckerCoord_unitColMatrix_eq_zero ρ (C := rectBase (p, q) hp ∪ {rectColV (p, q),
      rectColY (p, q), rectColT (p, q)}) (hcard _ _ _ hv hy ht hvy.ne (hvy.trans hyt).ne hyt.ne)
      (c := rectColY (p, q)) (c' := rectColT (p, q)) (by simp) (by simp) hyt.ne hρyt,
    mul_zero, sub_zero] at h
  refine ((isUnit_pluckerCoord_unitColMatrix ρ ?_ (injOn_omegaRowFin_xut hp hq hp1)).mul
    (isUnit_pluckerCoord_unitColMatrix ρ ?_ (injOn_omegaRowFin_vyw hp hq hp1))).ne_zero h
  · exact hcard _ _ _ hx hu ht hxu.ne (hxu.trans (huv.trans (hvy.trans hyt))).ne
      (huv.trans (hvy.trans hyt)).ne
  · exact hcard _ _ _ hv hy hw hvy.ne (hvy.trans (hyt.trans htw)).ne (hyt.trans htw).ne

/-- **The new variable at a vertex of degree six is coprime to the old.** For a mutable vertex
`(p, q)` with `p, q ≥ 2` (`≥ 1` here), `P_{S∪{u,v,w}}` does not divide `Ω_{p,q}` in `ℂ[z]`. -/
@[cluster_algebras "lem_rectangles_degree_six_coprime"]
theorem not_pluckerCoord_dvd_rectOmega {p : Fin a} {q : Fin (b - a)} (hp : (p : ℕ) + 1 < a)
    (hq : (q : ℕ) + 1 < b - a) (hp1 : 1 ≤ (p : ℕ)) (hq1 : 1 ≤ (q : ℕ)) :
    ¬pluckerCoord (complexGenericMatrix a b)
        (rectBase (p, q) hp ∪ {rectColU (p, q), rectColV (p, q), rectColW (p, q) hp}) ∣
      rectOmega (complexGenericMatrix a b) (p, q) hp := by
  rw [complexGenericMatrix_eq_mvPolynomialX]
  exact not_pluckerCoord_dvd_rectOmega_mvPolynomialX hp hq hp1 hq1

end Coprime

end ClusterAlgebras
