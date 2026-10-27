/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Rings.Seeds
public import ClusterAlgebras.Subpattern.SeedReindex
public import ClusterAlgebras.Restriction.Reindexing
public import ClusterAlgebras.ExchangeMatrix

/-!
# The rectangles quiver

The rectangles quiver `Q_{a,b} = (V_{a,b}, F_{a,b}, α)` is a quiver: `α` has no loops, its arrows
`(p, q) → (p', q')` have `(p' - p, q' - q) ∈ {(0, 1), (1, 0), (-1, -1)}`, a set disjoint from its
negative, the empty rectangle receives no arrow, and arrows between two frozen vertices are
excluded by definition. A rectangle labelling is then a labelling of this quiver, and the matrix of
`Σ^i_{a,b}(λ)` is its extended exchange matrix.

The rectangles of `V_{a-1,b-1}` are rectangles of `V_{a,b}`: the two have the same width
`c = b - a`, and the heights of the first are at most `a - 1`. Under this inclusion the labels
satisfy `J_{a,b}(v) = J_{a-1,b-1}(v) ∪ {b}`, and the inclusion read through two rectangle
labellings `λ'`, `λ` is a reindexing map `r = λ⁻¹ ∘ ι ∘ λ'`, closed for the matrix of
`Σ_{a,b}(λ)`, along which that matrix reindexes to the matrix of `Σ_{a-1,b-1}(λ')`: every
neighbour of a mutable vertex of `Q_{a-1,b-1}` lies in `V_{a-1,b-1}`, and the arrows at such a
vertex are the same in both quivers.

## Main definitions

* `ClusterAlgebras.rectanglesQuiver a b`: the quiver `Q_{a,b}`.
* `ClusterAlgebras.RectangleLabelling.toLabelling`: a rectangle labelling as a labelling of
  `Q_{a,b}`.
* `ClusterAlgebras.rectVertexEmbedding a b`: the inclusion `V_{a-1,b-1} ↪ V_{a,b}`.
* `ClusterAlgebras.rectRestrictReindex L' L`: the reindexing map `λ⁻¹ ∘ ι ∘ λ'`.

## Main results

* `ClusterAlgebras.isArrowSystem_rectArrows`, `ClusterAlgebras.twoCycleFree_rectArrows`,
  `ClusterAlgebras.rectArrows_eq_zero_of_rectFrozen`: the axioms of a quiver for `Q_{a,b}`.
* `ClusterAlgebras.extExchangeMatrix_rectanglesSeedShift`: the matrix of `Σ^i_{a,b}(λ)` is
  `B̃(Q_{a,b}, λ)`.
* `ClusterAlgebras.rectLabel_rectVertexEmbedding`: `J_{a,b}(v) = J_{a-1,b-1}(v) ∪ {b}`.
* `ClusterAlgebras.isClosedFor_rectRestrictReindex`,
  `ClusterAlgebras.matrixReindex_rectRestrictReindex`: `r` is closed for the matrix of
  `Σ_{a,b}(λ)`, which reindexes along `r` to the matrix of `Σ_{a-1,b-1}(λ')`.

## Implementation notes

* FWZ assume `1 ≤ a < b` for `Q_{a,b}` to be a quiver and `3 ≤ a ≤ b - 2` for the
  restriction; neither is used. With the vertex type `Option (Fin a × Fin (b - a))`, a mutable
  vertex `(p, q)` of `V_{a-1,b-1}` has `p + 1 < a - 1` and `q + 1 < (b - 1) - (a - 1) = b - a`
  whenever such a vertex exists, which is all the argument needs. The inclusion
  `V_{a-1,b-1} ↪ V_{a,b}` is defined for all `a`, `b`, as `(b - 1) - (a - 1) ≤ b - a` always.
* The label identity needs `1 ≤ a` (for `a = 0` both sides are degenerate and differ) and `1 ≤ b`
  (for the column `b` to exist); the column `b` is `⟨b - 1, _⟩ : Fin b` in the 0-based columns.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 6][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### The rectangles quiver is a quiver -/

section Quiver

variable {a b : ℕ}

/-- No rectangle steps to itself. -/
theorem not_rectStep_self (v : RectVertex a b) : ¬RectStep a b v v := by
  rcases v with _ | ⟨p, q⟩ <;> simp [RectStep]

/-- No two rectangles step to each other. -/
theorem not_rectStep_and_rectStep (v w : RectVertex a b) :
    ¬(RectStep a b v w ∧ RectStep a b w v) := by
  rcases v with _ | ⟨p, q⟩ <;> rcases w with _ | ⟨p', q'⟩ <;> simp [RectStep]
  omega

/-- `α(v, w)` is `1` or `0` according to whether `v → w` is an arrow of `Q_{a,b}`. -/
theorem rectArrows_eq_ite (v w : RectVertex a b) : rectArrows a b v w =
    if ¬(RectFrozen a b v ∧ RectFrozen a b w) ∧ RectStep a b v w then 1 else 0 :=
  rfl

/-- `α(v, w)` is nonzero exactly when `v` and `w` are not both frozen and `v → w` is a step. -/
theorem rectArrows_ne_zero_iff {v w : RectVertex a b} : rectArrows a b v w ≠ 0 ↔
    ¬(RectFrozen a b v ∧ RectFrozen a b w) ∧ RectStep a b v w := by
  rw [rectArrows_eq_ite]
  split_ifs with h
  · exact iff_of_true one_ne_zero h
  · exact iff_of_false (fun h0 => h0 rfl) h

/-- The arrows of `Q_{a,b}` form an arrow system: no rectangle carries an arrow to itself. -/
@[cluster_algebras "lem_rectangles_quiver_is_quiver"]
theorem isArrowSystem_rectArrows (a b : ℕ) : IsArrowSystem (rectArrows a b) := fun v => by
  simp [rectArrows_eq_ite, not_rectStep_self]

/-- The arrows of `Q_{a,b}` are two-cycle-free. -/
@[cluster_algebras "lem_rectangles_quiver_is_quiver"]
theorem twoCycleFree_rectArrows (a b : ℕ) : TwoCycleFree (rectArrows a b) := fun v w => by
  by_contra h
  push Not at h
  exact not_rectStep_and_rectStep v w
    ⟨(rectArrows_ne_zero_iff.1 h.1).2, (rectArrows_ne_zero_iff.1 h.2).2⟩

/-- No arrow of `Q_{a,b}` joins two frozen rectangles. -/
@[cluster_algebras "lem_rectangles_quiver_is_quiver"]
theorem rectArrows_eq_zero_of_rectFrozen {v w : RectVertex a b} (hv : RectFrozen a b v)
    (hw : RectFrozen a b w) : rectArrows a b v w = 0 := by
  simp [rectArrows_eq_ite, hv, hw]

/-- The **rectangles quiver** `Q_{a,b}`, with frozen set `F_{a,b}` and arrows `α`. -/
@[cluster_algebras "lem_rectangles_quiver_is_quiver"]
def rectanglesQuiver (a b : ℕ) : Quiver (RectVertex a b) where
  frozen := Finset.univ.filter (RectFrozen a b)
  arrows := rectArrows a b
  isArrowSystem := isArrowSystem_rectArrows a b
  twoCycleFree := twoCycleFree_rectArrows a b
  frozen_eq_zero _ hv _ hw :=
    rectArrows_eq_zero_of_rectFrozen (Finset.mem_filter.1 hv).2 (Finset.mem_filter.1 hw).2

/-- The frozen vertices of `Q_{a,b}` are those of `F_{a,b}`. -/
@[simp]
theorem mem_frozen_rectanglesQuiver {v : RectVertex a b} :
    v ∈ (rectanglesQuiver a b).frozen ↔ RectFrozen a b v := by
  simp [rectanglesQuiver]

/-- The arrows of `Q_{a,b}` are `α`. -/
@[simp]
theorem arrows_rectanglesQuiver : (rectanglesQuiver a b).arrows = rectArrows a b :=
  rfl

end Quiver

/-! ### Rectangle labellings are labellings of `Q_{a,b}` -/

section Labelling

variable {a b m n : ℕ}

/-- A rectangle labelling, read as a labelling of the quiver `Q_{a,b}`. -/
def RectangleLabelling.toLabelling (L : RectangleLabelling a b m n) :
    Labelling (rectanglesQuiver a b) m n where
  equiv := L.equiv
  le := L.le
  mem_frozen_iff i := mem_frozen_rectanglesQuiver.trans (L.frozen_iff i)

/-- A labelling of the quiver `Q_{a,b}`, read as a rectangle labelling. -/
def RectangleLabelling.ofLabelling (L : Labelling (rectanglesQuiver a b) m n) :
    RectangleLabelling a b m n where
  equiv := L.equiv
  le := L.le
  frozen_iff i := mem_frozen_rectanglesQuiver.symm.trans (L.mem_frozen_iff i)

/-- The bijection of `λ` read as a labelling of `Q_{a,b}` is that of `λ`. -/
@[simp]
theorem RectangleLabelling.toLabelling_equiv (L : RectangleLabelling a b m n) :
    L.toLabelling.equiv = L.equiv :=
  rfl

/-- The bijection of a labelling of `Q_{a,b}` read as a rectangle labelling is unchanged. -/
@[simp]
theorem RectangleLabelling.ofLabelling_equiv (L : Labelling (rectanglesQuiver a b) m n) :
    (RectangleLabelling.ofLabelling L).equiv = L.equiv :=
  rfl

/-- The matrix of the cyclic shift `Σ^i_{a,b}(λ)` is the extended exchange matrix
`B̃(Q_{a,b}, λ)`. -/
theorem extExchangeMatrix_rectanglesSeedShift (L : RectangleLabelling a b m n) (i : ℤ) :
    (rectanglesSeedShift L i).extExchangeMatrix =
      extExchangeMatrix (rectanglesQuiver a b) L.toLabelling :=
  rfl

/-- The matrix of the rectangles seed `Σ_{a,b}(λ)` is the extended exchange matrix
`B̃(Q_{a,b}, λ)`. -/
theorem extExchangeMatrix_rectanglesSeed (L : RectangleLabelling a b m n) :
    (rectanglesSeed L).extExchangeMatrix =
      extExchangeMatrix (rectanglesQuiver a b) L.toLabelling :=
  rfl

end Labelling

/-! ### Restricting to the top `a - 1` rows -/

section Restriction

variable {a b : ℕ}

/-- The **inclusion** `V_{a-1,b-1} ↪ V_{a,b}`: a `(p + 1) × (q + 1)` rectangle with `p < a - 1`
and `q < (b - 1) - (a - 1)` is the same rectangle in `V_{a,b}`, and `∅` goes to `∅`. -/
def rectVertexEmbedding (a b : ℕ) : RectVertex (a - 1) (b - 1) ↪ RectVertex a b :=
  ((Fin.castLEEmb (Nat.sub_le a 1)).prodMap (Fin.castLEEmb (by omega))).optionMap

/-- The inclusion sends `∅` to `∅`. -/
@[simp]
theorem rectVertexEmbedding_none : rectVertexEmbedding a b none = none :=
  rfl

/-- The inclusion keeps the height and the width of a rectangle. -/
@[simp]
theorem rectVertexEmbedding_some (p : Fin (a - 1)) (q : Fin (b - 1 - (a - 1))) :
    rectVertexEmbedding a b (some (p, q)) =
      some (Fin.castLE (Nat.sub_le a 1) p, Fin.castLE (by omega) q) :=
  rfl

/-- The steps of `Q_{a-1,b-1}` are the steps of `Q_{a,b}` between rectangles of `V_{a-1,b-1}`. -/
theorem rectStep_rectVertexEmbedding_iff (v w : RectVertex (a - 1) (b - 1)) :
    RectStep a b (rectVertexEmbedding a b v) (rectVertexEmbedding a b w) ↔
      RectStep (a - 1) (b - 1) v w := by
  rcases v with _ | ⟨p, q⟩ <;> rcases w with _ | ⟨p', q'⟩ <;>
    simp [RectStep]

/-- A mutable rectangle of `Q_{a-1,b-1}` is mutable in `Q_{a,b}`. -/
theorem not_rectFrozen_rectVertexEmbedding {v : RectVertex (a - 1) (b - 1)}
    (hv : ¬RectFrozen (a - 1) (b - 1) v) : ¬RectFrozen a b (rectVertexEmbedding a b v) := by
  rcases v with _ | ⟨p, q⟩
  · exact absurd trivial hv
  · have := p.isLt
    have := q.isLt
    simp only [RectFrozen, not_or, rectVertexEmbedding_some, Fin.val_castLE] at hv ⊢
    omega

/-- At a mutable rectangle `v` of `Q_{a-1,b-1}`, the arrows of `Q_{a,b}` out of `v` towards
rectangles of `V_{a-1,b-1}` are those of `Q_{a-1,b-1}`. -/
theorem rectArrows_rectVertexEmbedding_left {v : RectVertex (a - 1) (b - 1)}
    (hv : ¬RectFrozen (a - 1) (b - 1) v) (w : RectVertex (a - 1) (b - 1)) :
    rectArrows a b (rectVertexEmbedding a b v) (rectVertexEmbedding a b w) =
      rectArrows (a - 1) (b - 1) v w := by
  simp only [rectArrows_eq_ite, rectStep_rectVertexEmbedding_iff, hv,
    not_rectFrozen_rectVertexEmbedding hv, false_and, not_false_eq_true, true_and]

/-- At a mutable rectangle `v` of `Q_{a-1,b-1}`, the arrows of `Q_{a,b}` into `v` from
rectangles of `V_{a-1,b-1}` are those of `Q_{a-1,b-1}`. -/
theorem rectArrows_rectVertexEmbedding_right {v : RectVertex (a - 1) (b - 1)}
    (hv : ¬RectFrozen (a - 1) (b - 1) v) (w : RectVertex (a - 1) (b - 1)) :
    rectArrows a b (rectVertexEmbedding a b w) (rectVertexEmbedding a b v) =
      rectArrows (a - 1) (b - 1) w v := by
  simp only [rectArrows_eq_ite, rectStep_rectVertexEmbedding_iff, hv,
    not_rectFrozen_rectVertexEmbedding hv, and_false, not_false_eq_true, true_and]

/-- A rectangle of `V_{a,b}` joined by a step, in either direction, to a mutable rectangle of
`Q_{a-1,b-1}` lies in `V_{a-1,b-1}`. -/
theorem mem_range_rectVertexEmbedding_of_rectStep {v : RectVertex (a - 1) (b - 1)}
    (hv : ¬RectFrozen (a - 1) (b - 1) v) {w : RectVertex a b}
    (hw : RectStep a b w (rectVertexEmbedding a b v) ∨
      RectStep a b (rectVertexEmbedding a b v) w) :
    w ∈ Set.range (rectVertexEmbedding a b) := by
  rcases w with _ | ⟨p', q'⟩
  · exact ⟨none, rfl⟩
  rcases v with _ | ⟨p, q⟩
  · exact absurd trivial hv
  have := p.isLt
  have := q.isLt
  have := p'.isLt
  have := q'.isLt
  simp only [RectFrozen, not_or, rectVertexEmbedding_some, RectStep, Fin.val_castLE] at hv hw
  exact ⟨some (⟨p', by omega⟩, ⟨q', by omega⟩), rfl⟩

/-- **The labels of `V_{a-1,b-1}` inside `V_{a,b}`**: `J_{a,b}(v) = J_{a-1,b-1}(v) ∪ {b}`, the
columns `[1, b - 1]` being read in `[1, b]`. -/
theorem rectLabel_rectVertexEmbedding (ha : 1 ≤ a) (hb : 1 ≤ b) (v : RectVertex (a - 1) (b - 1)) :
    rectLabel a b (rectVertexEmbedding a b v) =
      (rectLabel (a - 1) (b - 1) v).map (Fin.castLEEmb (Nat.sub_le b 1)) ∪
        {⟨b - 1, by omega⟩} := by
  ext x
  have hx := x.isLt
  rcases v with _ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  all_goals
    simp only [rectVertexEmbedding_none, rectVertexEmbedding_some, rectLabel, Finset.mem_union,
      Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.castLEEmb_apply,
      Finset.mem_singleton, Fin.val_castLE]
    refine ⟨fun h => ?_, ?_⟩
    · by_cases hxb : (x : ℕ) = b - 1
      · exact Or.inr (Fin.ext hxb)
      · exact Or.inl ⟨⟨x, by omega⟩, by simp only; omega, Fin.ext rfl⟩
    · rintro (⟨y, hy, rfl⟩ | rfl)
      · simp only [Fin.val_castLE]
        omega
      · simp only
        omega

variable {m' n' m n : ℕ}

/-- The **reindexing map** `r = λ⁻¹ ∘ ι ∘ λ'` of two rectangle labellings `λ'` of `V_{a-1,b-1}`
and `λ` of `V_{a,b}`, `ι` being the inclusion `V_{a-1,b-1} ↪ V_{a,b}`: it is injective, and sends
mutable indices to mutable indices since a mutable rectangle of `Q_{a-1,b-1}` is mutable in
`Q_{a,b}`. -/
@[cluster_algebras "lem_rectangles_restriction"]
def rectRestrictReindex (L' : RectangleLabelling (a - 1) (b - 1) m' n')
    (L : RectangleLabelling a b m n) : ReindexingMap m' n' m n where
  toFun i := L.equiv.symm (rectVertexEmbedding a b (L'.equiv i))
  injective := L.equiv.symm.injective.comp
    ((rectVertexEmbedding a b).injective.comp L'.equiv.injective)
  lt_of_lt i hi := by
    have h := not_rectFrozen_rectVertexEmbedding (v := L'.equiv i) (by rw [L'.frozen_iff]; omega)
    rw [← Equiv.apply_symm_apply L.equiv (rectVertexEmbedding a b _), L.frozen_iff] at h
    omega

/-- The value of `r = λ⁻¹ ∘ ι ∘ λ'` at an index. -/
@[simp]
theorem rectRestrictReindex_apply (L' : RectangleLabelling (a - 1) (b - 1) m' n')
    (L : RectangleLabelling a b m n) (i : Fin m') :
    rectRestrictReindex L' L i = L.equiv.symm (rectVertexEmbedding a b (L'.equiv i)) :=
  rfl

/-- The vertex of `Q_{a,b}` named by the column `r(q)` is the image of the mutable vertex
`λ'(q)`. -/
theorem equiv_castLE_col_rectRestrictReindex (L' : RectangleLabelling (a - 1) (b - 1) m' n')
    (L : RectangleLabelling a b m n) (q : Fin n') :
    L.equiv (Fin.castLE L.le ((rectRestrictReindex L' L).col L'.le q)) =
      rectVertexEmbedding a b (L'.equiv (Fin.castLE L'.le q)) := by
  rw [ReindexingMap.castLE_col, rectRestrictReindex_apply, Equiv.apply_symm_apply]

/-- The vertex that a rectangle labelling assigns to a column index is not frozen. -/
theorem RectangleLabelling.not_rectFrozen_castLE {a' b' : ℕ}
    (L : RectangleLabelling a' b' m n) (q : Fin n) :
    ¬RectFrozen a' b' (L.equiv (Fin.castLE L.le q)) := by
  rw [L.frozen_iff, Fin.val_castLE]
  have := q.isLt
  omega

/-- The reindexing map `r` is **closed** for the matrix of `Σ^k_{a,b}(λ)`: every vertex joined
by an arrow of `Q_{a,b}` to a mutable vertex of `Q_{a-1,b-1}` lies in `V_{a-1,b-1}`. -/
theorem isClosedFor_rectRestrictReindex_rectanglesSeedShift
    (L' : RectangleLabelling (a - 1) (b - 1) m' n') (L : RectangleLabelling a b m n) (k : ℤ) :
    (rectRestrictReindex L' L).IsClosedFor L'.le (rectanglesSeedShift L k).extExchangeMatrix := by
  intro q i hne
  have hv := L'.not_rectFrozen_castLE q
  simp only [rectanglesSeedShift, Matrix.of_apply, equiv_castLE_col_rectRestrictReindex,
    signedCount] at hne
  have hw : RectStep a b (L.equiv i) (rectVertexEmbedding a b (L'.equiv (Fin.castLE L'.le q))) ∨
      RectStep a b (rectVertexEmbedding a b (L'.equiv (Fin.castLE L'.le q))) (L.equiv i) := by
    by_contra h
    push Not at h
    simp [rectArrows_eq_ite, h.1, h.2] at hne
  obtain ⟨u, hu⟩ := mem_range_rectVertexEmbedding_of_rectStep hv hw
  exact ⟨L'.equiv.symm u, by simp [hu]⟩

/-- Along `r`, the matrix of `Σ^k_{a,b}(λ)` reindexes to the matrix of `Σ^l_{a-1,b-1}(λ')`, for
any shifts `k` and `l`: the arrows at a mutable vertex of `Q_{a-1,b-1}` are the same in both
quivers. -/
theorem matrixReindex_rectRestrictReindex_rectanglesSeedShift
    (L' : RectangleLabelling (a - 1) (b - 1) m' n') (L : RectangleLabelling a b m n) (k l : ℤ) :
    matrixReindex L'.le (rectanglesSeedShift L k).extExchangeMatrix (rectRestrictReindex L' L) =
      (rectanglesSeedShift L' l).extExchangeMatrix := by
  ext i q
  have hv := L'.not_rectFrozen_castLE q
  simp only [matrixReindex_apply, rectanglesSeedShift, Matrix.of_apply,
    equiv_castLE_col_rectRestrictReindex, rectRestrictReindex_apply, Equiv.apply_symm_apply,
    signedCount, rectArrows_rectVertexEmbedding_left hv, rectArrows_rectVertexEmbedding_right hv]

/-- **Restricting `Q_{a,b}` to the top `a - 1` rows**: the reindexing map `r = λ⁻¹ ∘ ι ∘ λ'` is
closed for the matrix `B̃` of `Σ_{a,b}(λ)`. -/
@[cluster_algebras "lem_rectangles_restriction"]
theorem isClosedFor_rectRestrictReindex (L' : RectangleLabelling (a - 1) (b - 1) m' n')
    (L : RectangleLabelling a b m n) :
    (rectRestrictReindex L' L).IsClosedFor L'.le (rectanglesSeed L).extExchangeMatrix :=
  isClosedFor_rectRestrictReindex_rectanglesSeedShift L' L 0

/-- **Restricting `Q_{a,b}` to the top `a - 1` rows**: along `r = λ⁻¹ ∘ ι ∘ λ'`, the matrix `B̃`
of `Σ_{a,b}(λ)` reindexes to the matrix of `Σ_{a-1,b-1}(λ')`. -/
@[cluster_algebras "lem_rectangles_restriction"]
theorem matrixReindex_rectRestrictReindex (L' : RectangleLabelling (a - 1) (b - 1) m' n')
    (L : RectangleLabelling a b m n) :
    matrixReindex L'.le (rectanglesSeed L).extExchangeMatrix (rectRestrictReindex L' L) =
      (rectanglesSeed L').extExchangeMatrix :=
  matrixReindex_rectRestrictReindex_rectanglesSeedShift L' L 0 0

end Restriction

end ClusterAlgebras
