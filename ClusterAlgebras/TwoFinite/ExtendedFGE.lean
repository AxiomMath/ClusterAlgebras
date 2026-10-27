/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.ExtendedBCD

/-!
# The extended Dynkin trees of types `E`, `F`, `G` are not `2`-finite

No skew-symmetrizable integer matrix whose diagram is one of the extended Dynkin trees
`F₄^{(1)}`, `G₂^{(1)}(a)`, `E₆^{(1)} = T_{2,2,2}`, `E₇^{(1)} = T_{1,3,3}` or
`E₈^{(1)} = T_{1,2,5}` is `2`-finite.

## Main results

* `ClusterAlgebras.not_isTwoFinite_of_isF4AffineShape`: no matrix of shape `F₄^{(1)}` is
  `2`-finite.
* `ClusterAlgebras.not_isTwoFinite_of_isG2AffineShape`: no matrix of shape `G₂^{(1)}(a)` is
  `2`-finite.
* `ClusterAlgebras.not_isTwoFinite_of_isE6AffineShape`,
  `ClusterAlgebras.not_isTwoFinite_of_isE7AffineShape`,
  `ClusterAlgebras.not_isTwoFinite_of_isE8AffineShape`: no matrix of shape `E₆^{(1)}`,
  `E₇^{(1)}` or `E₈^{(1)}` is `2`-finite.

## Implementation notes

Each of these shapes is a tree, so by `IsTreeDiagram.diagramEquiv_of_diagramWeight_eq` a
matrix `B` of the shape is `2`-finite exactly when one fixed orientation `Z` of the tree is,
the indices of `Z` being the positions of the enumeration of the shape. In [FWZ], the trees
`F₄^{(1)}` and `G₂^{(1)}(a)` mutate to chordless cycles whose weights are not in `L_m`, and
the trees of type `E` are handled through the relations `T_{2,2,2} ∼ S²_{2,2,1} ⊃ D₅^{(1)}`,
`T_{3,1,3} ∼ S³_{3,1,1} ⊃ E₆^{(1)}` and `T_{2,1,5} ∼ S⁵_{2,1,1} ⊃ E₇^{(1)}` and crowns.
Here instead each orientation `Z` is shown not to be `2`-finite by an explicit sequence of
mutations producing a pair of weight `4`; the sequences have lengths `5` (`F₄^{(1)}`), at
most `2` (`G₂^{(1)}(a)`), `9`, `14` and `22` (`E₆^{(1)}`, `E₇^{(1)}`, `E₈^{(1)}`), and the
resulting weights are evaluated by the kernel.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {N : ℕ}

/-! ### Trees given by a model -/

section Tree

/-- A graph on `[0, m)`, `m ≥ 1`, in which every nonzero vertex has a smaller neighbour is
connected. -/
theorem connected_of_exists_lower_adj {m : ℕ} (hm : 0 < m) {G : SimpleGraph (Fin m)}
    (h : ∀ j : Fin m, 0 < (j : ℕ) → ∃ i, i < j ∧ G.Adj i j) : G.Connected := by
  have key : ∀ k (j : Fin m), (j : ℕ) = k → G.Reachable ⟨0, hm⟩ j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j hj
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [show j = ⟨0, hm⟩ from Fin.ext hj]
      · obtain ⟨i, hij, hadj⟩ := h j (hj ▸ hk)
        exact (ih i (hj ▸ hij) i rfl).trans hadj.reachable
  rw [SimpleGraph.connected_iff]
  exact ⟨fun u v => (key _ u rfl).symm.trans (key _ v rfl), ⟨⟨0, hm⟩⟩⟩

/-- A connected graph on `[0, m)` in which every vertex has at most one smaller neighbour is a
tree. -/
theorem isTree_of_lower_unique {m : ℕ} {G : SimpleGraph (Fin m)} (hG : G.Connected)
    (hlow : ∀ i i' j : Fin m, i < j → i' < j → G.Adj i j → G.Adj i' j → i = i') : G.IsTree := by
  classical
  have key : ∀ a b : Fin m, G.Adj a b → ∃ i j, i < j ∧ G.Adj i j ∧ s(a, b) = s(i, j) := by
    intro a b hab
    rcases lt_or_gt_of_ne hab.ne with h | h
    · exact ⟨a, b, h, hab, rfl⟩
    · exact ⟨b, a, h, hab.symm, Sym2.eq_swap⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hG, le_antisymm ?_ hG.card_vert_le_card_edgeSet_add_one⟩
  obtain ⟨v⟩ := hG.nonempty
  let f : G.edgeSet → Fin m := fun e => e.1.sup
  have hf : Function.Injective f := by
    rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ heq
    induction e₁ using Sym2.inductionOn with | hf a b => ?_
    induction e₂ using Sym2.inductionOn with | hf c d => ?_
    obtain ⟨i, j, hij, hadj, hab⟩ := key a b h₁
    obtain ⟨i', j', hij', hadj', hcd⟩ := key c d h₂
    simp only [f, hab, hcd, Sym2.sup_mk, max_eq_right hij.le, max_eq_right hij'.le] at heq
    subst heq
    simp only [hab, hcd, hlow i i' j hij hij' hadj hadj']
  have h0 : (⟨0, v.pos⟩ : Fin m) ∉ Set.range f := by
    rintro ⟨⟨e, he⟩, hfe⟩
    induction e using Sym2.inductionOn with | hf a b => ?_
    obtain ⟨i, j, hij, -, hab⟩ := key a b he
    simp only [f, hab, Sym2.sup_mk, max_eq_right hij.le] at hfe
    subst hfe
    exact absurd hij (by simp [Fin.lt_def])
  have := Fintype.card_lt_of_injective_of_notMem f hf h0
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  simp only [Fintype.card_fin] at this
  omega

/-- A matrix whose weights on `[0, M)` are those of a model `f` in which every position
`q > 0` is joined to exactly one smaller position is a tree diagram. -/
private theorem isTreeDiagram_of_diagramWeight_eq_orderedModel {M : ℕ} {f : ℕ → ℕ → ℕ}
    {C : Matrix (Fin M) (Fin M) ℤ} (hM : 0 < M)
    (hC : ∀ p q : Fin M, p ≠ q → diagramWeight C p q = orderedModel f p q)
    (hlow : ∀ q : Fin M, 0 < (q : ℕ) → ∃ p : Fin M, p < q ∧ 0 < f p q)
    (huniq : ∀ p p' q : Fin M, p < q → p' < q → 0 < f p q → 0 < f p' q → p = p') :
    IsTreeDiagram C := by
  have hadj : ∀ p q : Fin M, p < q → ((diagramGraph C).Adj p q ↔ 0 < f p q) := by
    intro p q hpq
    rw [diagramGraph_adj, hC p q hpq.ne, orderedModel, if_pos (show (p : ℕ) < q from hpq)]
    exact ⟨And.right, fun h => ⟨hpq.ne, h⟩⟩
  refine isTree_of_lower_unique (connected_of_exists_lower_adj hM fun q hq => ?_)
    fun p p' q hp hp' h h' => huniq p p' q hp hp' ((hadj p q hp).1 h) ((hadj p' q hp').1 h')
  obtain ⟨p, hpq, hp⟩ := hlow q hq
  exact ⟨p, hpq, (hadj p q hpq).2 hp⟩

end Tree

/-! ### Reduction to one orientation -/

section Reduction

/-- **A matrix of a tree shape is `2`-finite only if a fixed orientation of the tree is.** If
the model `f` on `M` positions is a tree in which every position `q > 0` is joined to exactly
one smaller position, `Z` is a skew-symmetrizable matrix on the positions with the weights of
`f`, and `Z` is not `2`-finite, then no matrix of shape `f` is `2`-finite. -/
private theorem not_isTwoFinite_of_isShapeOf {M : ℕ} {f : ℕ → ℕ → ℕ} (hM : 0 < M)
    (hlow : ∀ q : Fin M, 0 < (q : ℕ) → ∃ p : Fin M, p < q ∧ 0 < f p q)
    (huniq : ∀ p p' q : Fin M, p < q → p' < q → 0 < f p q → 0 < f p' q → p = p')
    {Z : Matrix (Fin M) (Fin M) ℤ} (hZ : SkewSymmetrizable Z)
    (hZw : ∀ p q : Fin M, p ≠ q → diagramWeight Z p q = orderedModel f p q)
    (hZn : ¬IsTwoFinite Z) {B : Matrix (Fin N) (Fin N) ℤ}
    (hS : IsShapeOf (diagramWeight B) M f) : ¬IsTwoFinite B := by
  obtain ⟨e, he⟩ := hS
  intro hB
  have hC := hB.submatrix e.toEmbedding
  have hCw : ∀ p q : Fin M, p ≠ q →
      diagramWeight (B.submatrix e.toEmbedding e.toEmbedding) p q = orderedModel f p q :=
    fun p q h => he p q h
  have hT := isTreeDiagram_of_diagramWeight_eq_orderedModel hM hCw hlow huniq
  have hw : ∀ i j, diagramWeight Z i j =
      diagramWeight (B.submatrix e.toEmbedding e.toEmbedding) (Equiv.refl _ i)
        (Equiv.refl _ j) := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [diagramWeight, hZ.diag_eq_zero, hB.1.diag_eq_zero]
    · exact (hZw i j h).trans (hCw i j h).symm
  exact hZn ((IsTreeDiagram.diagramEquiv_of_diagramWeight_eq hC.1 hZ hT hw).2.1 hC)

/-- A matrix with a mutation having a pair of weight at least `4` is not `2`-finite. -/
private theorem not_isTwoFinite_of_three_lt_diagramWeight {n : ℕ}
    {Z : Matrix (Fin n) (Fin n) ℤ} (s : List (Fin n)) (i j : Fin n)
    (h : 3 < diagramWeight (matrixMutationList le_rfl Z s) i j) : ¬IsTwoFinite Z :=
  fun hZ => ((hZ.matrixMutationList s).diagramWeight_le_three i j).not_gt h

end Reduction

/-! ### Orientations of the trees -/

section Orientations

/-- The orientation `x₁ → x₂ → x₃ → x₄ → x₅` of `F₄^{(1)}`, with `b₂₃ = 1`, `b₃₂ = -2`. -/
private def f4AffineOrientation : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0;
    -1, 0, 1, 0, 0;
    0, -2, 0, 1, 0;
    0, 0, -1, 0, 1;
    0, 0, 0, -1, 0]

/-- The orientation `x₀ → x₁ → x₂` of `G₂^{(1)}(a)`, with `b₀₁ = 1`, `b₁₀ = -3`, `b₁₂ = 1`,
`b₂₁ = -a`. -/
private def g2AffineOrientation (a : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, 0;
    -3, 0, 1;
    0, -a, 0]

/-- The orientation of `T_{2,2,2}` with all arrows pointing away from the centre. -/
private def e6AffineOrientation : Matrix (Fin 7) (Fin 7) ℤ :=
  !![0, 1, 0, 1, 0, 1, 0;
    -1, 0, 1, 0, 0, 0, 0;
    0, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 1, 0, 0;
    0, 0, 0, -1, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, -1, 0]

/-- The orientation of `T_{1,3,3}` with all arrows pointing away from the centre. -/
private def e7AffineOrientation : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, 1, 1, 0, 0, 1, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, -1, 0, 1, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, -1, 0, 1;
    0, 0, 0, 0, 0, 0, -1, 0]

/-- The orientation of `T_{1,2,5}` with all arrows pointing away from the centre. -/
private def e8AffineOrientation : Matrix (Fin 9) (Fin 9) ℤ :=
  !![0, 1, 1, 0, 1, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, -1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 1, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, -1, 0]

end Orientations

/-- **No matrix of shape `F₄^{(1)}` is `2`-finite.** -/
@[cluster_algebras "lem_extended_FG"]
theorem not_isTwoFinite_of_isF4AffineShape {B : Matrix (Fin N) (Fin N) ℤ}
    (hS : IsF4AffineShape (diagramWeight B)) : ¬IsTwoFinite B :=
  not_isTwoFinite_of_isShapeOf (Z := f4AffineOrientation) (by norm_num) (by decide) (by decide)
    ⟨![2, 2, 1, 1, 1], by decide, by decide⟩ (by decide)
    (not_isTwoFinite_of_three_lt_diagramWeight [2, 1, 3, 0, 2] 3 4 (by decide)) hS

/-- **No matrix of shape `G₂^{(1)}(a)`, `a ∈ {1, 2, 3}`, is `2`-finite.** -/
@[cluster_algebras "lem_extended_FG"]
theorem not_isTwoFinite_of_isG2AffineShape {B : Matrix (Fin N) (Fin N) ℤ} {a : ℕ}
    (hS : IsG2AffineShape (diagramWeight B) a) : ¬IsTwoFinite B := by
  obtain ⟨ha, hS⟩ := hS
  rcases ha with rfl | rfl | rfl
  · exact not_isTwoFinite_of_isShapeOf (Z := g2AffineOrientation 1) (by norm_num) (by decide)
      (by decide) ⟨![3, 1, 1], by decide, by decide⟩ (by decide)
      (not_isTwoFinite_of_three_lt_diagramWeight [1, 0] 1 2 (by decide)) hS
  · exact not_isTwoFinite_of_isShapeOf (Z := g2AffineOrientation 2) (by norm_num) (by decide)
      (by decide) ⟨![6, 2, 1], by decide, by decide⟩ (by decide)
      (not_isTwoFinite_of_three_lt_diagramWeight [1] 0 2 (by decide)) hS
  · exact not_isTwoFinite_of_isShapeOf (Z := g2AffineOrientation 3) (by norm_num) (by decide)
      (by decide) ⟨![9, 3, 1], by decide, by decide⟩ (by decide)
      (not_isTwoFinite_of_three_lt_diagramWeight [1] 0 2 (by decide)) hS

/-- **No matrix of shape `E₆^{(1)} = T_{2,2,2}` is `2`-finite.** -/
@[cluster_algebras "lem_extended_E"]
theorem not_isTwoFinite_of_isE6AffineShape {B : Matrix (Fin N) (Fin N) ℤ}
    (hS : IsE6AffineShape (diagramWeight B)) : ¬IsTwoFinite B :=
  not_isTwoFinite_of_isShapeOf (Z := e6AffineOrientation) (by norm_num) (by decide) (by decide)
    ⟨fun _ => 1, by decide, by decide⟩ (by decide)
    (not_isTwoFinite_of_three_lt_diagramWeight [1, 2, 0, 3, 5, 2, 0, 4, 6] 1 2 (by decide)) hS

/-- **No matrix of shape `E₇^{(1)} = T_{1,3,3}` is `2`-finite.** -/
@[cluster_algebras "lem_extended_E"]
theorem not_isTwoFinite_of_isE7AffineShape {B : Matrix (Fin N) (Fin N) ℤ}
    (hS : IsE7AffineShape (diagramWeight B)) : ¬IsTwoFinite B :=
  not_isTwoFinite_of_isShapeOf (Z := e7AffineOrientation) (by norm_num) (by decide) (by decide)
    ⟨fun _ => 1, by decide, by decide⟩ (by decide)
    (not_isTwoFinite_of_three_lt_diagramWeight [7, 3, 1, 0, 5, 6, 7, 2, 1, 0, 3, 1, 5, 4] 3 6
      (by decide)) hS

set_option maxRecDepth 4000 in
/-- **No matrix of shape `E₈^{(1)} = T_{1,2,5}` is `2`-finite.** -/
@[cluster_algebras "lem_extended_E"]
theorem not_isTwoFinite_of_isE8AffineShape {B : Matrix (Fin N) (Fin N) ℤ}
    (hS : IsE8AffineShape (diagramWeight B)) : ¬IsTwoFinite B :=
  not_isTwoFinite_of_isShapeOf (Z := e8AffineOrientation) (by norm_num) (by decide) (by decide)
    ⟨fun _ => 1, by decide, by decide⟩ (by decide)
    (not_isTwoFinite_of_three_lt_diagramWeight
      [5, 4, 2, 8, 0, 6, 5, 1, 3, 7, 4, 1, 8, 7, 0, 4, 2, 7, 1, 5, 4, 6] 0 2 (by decide)) hS

end ClusterAlgebras
