/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.AddVertex

/-!
# A path with one more vertex

A connected `2`-finite diagram consisting of a linearly oriented path and one more vertex is of
Dynkin class; and so is a connected `2`-finite diagram one of whose subdiagrams on all but one
vertex is mutation equivalent to a path diagram.

## Main results

* `ClusterAlgebras.IsLinearlyOrientedPath.exists_isOfDynkinClass`: a connected `2`-finite
  diagram on `m + 1` vertices containing a linearly oriented induced path on `m` vertices is of
  Dynkin class of rank `m + 1`.
* `ClusterAlgebras.exists_isOfDynkinClass_of_diagramEquiv_isPathDiagram`: a connected
  `2`-finite diagram on `M + 1` vertices whose subdiagram on all but one vertex is mutation
  equivalent to a path diagram is of Dynkin class of rank `M + 1`.

## Implementation notes

* Reindexing `B` along the permutation sending `0, …, m - 1, m` to `p₁, …, p_m, u` reduces
  `ClusterAlgebras.IsLinearlyOrientedPath.exists_isOfDynkinClass` to the case where the path is
  `0, 1, …, m - 1` and the extra vertex is `m`. There every subdiagram used in the proof, every
  enumeration of a crown, and every tree is given by an explicit function on the values of the
  indices, so that the adjacencies to check become linear arithmetic.
* A finite graph is recognised as a tree through a ranking of its vertices in which every vertex
  but one has exactly one neighbour of smaller rank: the edges are then in bijection with the
  vertices other than the root.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

private theorem exists_isOfDynkinClass_of_isTreeDiagram {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsTwoFinite B) (hT : IsTreeDiagram B) :
    ∃ X : DynkinSymbol, X.rank = n ∧ IsOfDynkinClass B [X] := by
  obtain ⟨X, hX, hX'⟩ := hB.hasDynkinShape_of_isTreeDiagram hT
  exact ⟨X, hX.rank_eq, hX'⟩

private theorem exists_isOfDynkinClass_of_matrixMutationList {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsTwoFinite B) (t : List (Fin n))
    (h : ∃ X : DynkinSymbol, X.rank = n ∧ IsOfDynkinClass (matrixMutationList le_rfl B t) [X]) :
    ∃ X : DynkinSymbol, X.rank = n ∧ IsOfDynkinClass B [X] := by
  obtain ⟨X, hX, hX'⟩ := h
  exact ⟨X, hX, hX'.of_diagramEquiv hB.1 (hB.matrixMutationList t).1
    (mutationEquiv_matrixMutationList B t).diagramEquiv⟩

/-! ### Indices given by their values -/

/-- The weight of the indices with values `x` and `y`, and `0` if one is out of range. -/
private def wt (B : Matrix (Fin n) (Fin n) ℤ) (x y : ℕ) : ℕ :=
  if h : x < n ∧ y < n then diagramWeight B ⟨x, h.1⟩ ⟨y, h.2⟩ else 0

private theorem wt_val (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    wt B i j = diagramWeight B i j := by
  simp [wt, i.isLt, j.isLt]

private theorem wt_comm (B : Matrix (Fin n) (Fin n) ℤ) (x y : ℕ) : wt B x y = wt B y x := by
  unfold wt
  by_cases h : x < n ∧ y < n
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, diagramWeight_comm]
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩)]

/-- The entry at the indices with values `x` and `y`, and `0` if one is out of range. -/
private def ent (B : Matrix (Fin n) (Fin n) ℤ) (x y : ℕ) : ℤ :=
  if h : x < n ∧ y < n then B ⟨x, h.1⟩ ⟨y, h.2⟩ else 0

private theorem ent_val (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ent B i j = B i j := by
  simp [ent, i.isLt, j.isLt]

private theorem ent_pos_asymm {B : Matrix (Fin n) (Fin n) ℤ} (hS : SkewSymmetrizable B)
    {x y : ℕ} (h : 0 < ent B x y) : ¬0 < ent B y x := by
  unfold ent at h ⊢
  by_cases hxy : x < n ∧ y < n
  · rw [dif_pos hxy] at h
    rw [dif_pos ⟨hxy.2, hxy.1⟩]
    rcases hS.entries_sign ⟨x, hxy.1⟩ ⟨y, hxy.2⟩ with h' | h' | h' <;> omega
  · rw [dif_neg hxy] at h
    exact absurd h (lt_irrefl _)

/-- The greatest number below `a` with a property `P`, when there is one. -/
private theorem exists_greatest_lt {P : ℕ → Prop} {a : ℕ} (h : ∃ e < a, P e) :
    ∃ e < a, P e ∧ ∀ x, e < x → x < a → ¬P x := by
  induction a with
  | zero =>
    obtain ⟨e, he, -⟩ := h
    omega
  | succ a ih =>
    by_cases hP : P a
    · exact ⟨a, by omega, hP, fun x hx hx' => by omega⟩
    obtain ⟨e, he, hPe⟩ := h
    obtain ⟨e', he', hPe', hmax⟩ :=
      ih ⟨e, Nat.lt_of_le_of_ne (by omega) fun h => hP (h ▸ hPe), hPe⟩
    refine ⟨e', by omega, hPe', fun x hx hx' => ?_⟩
    rcases (show x < a ∨ x = a by omega) with h | rfl
    · exact hmax x hx h
    · exact hP

/-- A map `Fin L → Fin n` given by its values. -/
private def arithMap {L : ℕ} (g : ℕ → ℕ) (hg : ∀ t < L, g t < n) : Fin L → Fin n :=
  fun t => ⟨g t, hg t t.2⟩

@[simp] private theorem arithMap_val {L : ℕ} (g : ℕ → ℕ) (hg : ∀ t < L, g t < n) (t : Fin L) :
    (arithMap g hg t : ℕ) = g t := rfl

private theorem arithMap_injective {L : ℕ} {g : ℕ → ℕ} {hg : ∀ t < L, g t < n}
    (hinj : ∀ s t, s < L → t < L → g s = g t → s = t) : Function.Injective (arithMap g hg) :=
  fun s t h => Fin.ext (hinj s t s.2 t.2 (congrArg Fin.val h))

private theorem diagramWeight_eq_zero_of_not_adj {B : Matrix (Fin n) (Fin n) ℤ}
    (hS : SkewSymmetrizable B) {i j : Fin n} (h : ¬(diagramGraph B).Adj i j) :
    diagramWeight B i j = 0 := by
  by_cases hij : i = j
  · subst hij
    simp [diagramWeight, hS.diag_eq_zero]
  · by_contra h0
    exact h ⟨hij, Nat.pos_of_ne_zero h0⟩

private theorem isInducedPath_arithMap {B : Matrix (Fin n) (Fin n) ℤ} {Q : ℕ → ℕ → Prop}
    {D : ℕ → Prop} (hA : ∀ i j : Fin n, D i → D j → ((diagramGraph B).Adj i j ↔ Q i j))
    {L : ℕ} (g : ℕ → ℕ) (hg : ∀ t < L, g t < n) (hgD : ∀ t < L, D (g t)) (hL : 1 ≤ L)
    (hinj : ∀ s t, s < L → t < L → g s = g t → s = t)
    (hadj : ∀ s t, s < L → t < L → s ≠ t → (Q (g s) (g t) ↔ s + 1 = t ∨ t + 1 = s)) :
    IsInducedPath B (arithMap g hg) :=
  ⟨hL, arithMap_injective hinj, fun s t hst =>
    (hA _ _ (hgD s s.2) (hgD t t.2)).trans (hadj s t s.2 t.2 (fun h => hst (Fin.ext h)))⟩

private theorem isChordlessCycle_arithMap {B : Matrix (Fin n) (Fin n) ℤ} {Q : ℕ → ℕ → Prop}
    {D : ℕ → Prop} (hA : ∀ i j : Fin n, D i → D j → ((diagramGraph B).Adj i j ↔ Q i j))
    {L : ℕ} (g : ℕ → ℕ) (hg : ∀ t < L, g t < n) (hgD : ∀ t < L, D (g t)) (hL : 3 ≤ L)
    (hinj : ∀ s t, s < L → t < L → g s = g t → s = t)
    (hadj : ∀ s t, s < L → t < L → s ≠ t → (Q (g s) (g t) ↔
      (t = s + 1 ∨ s = t + 1 ∨ (s + 1 = L ∧ t = 0) ∨ (t + 1 = L ∧ s = 0)))) :
    IsChordlessCycle B (arithMap g hg) := by
  refine ⟨hL, arithMap_injective hinj, fun s t hst => ?_⟩
  refine (hA _ _ (hgD s s.2) (hgD t t.2)).trans
    ((hadj s t s.2 t.2 (fun h => hst (Fin.ext h))).trans ?_)
  rw [Fin.ext_iff, Fin.ext_iff, val_finRotate_eq_ite, val_finRotate_eq_ite]
  have := s.2
  have := t.2
  have : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
  split_ifs <;> omega

private theorem cycleWeights_arithMap (B : Matrix (Fin n) (Fin n) ℤ) {L : ℕ} (g : ℕ → ℕ)
    (hg : ∀ t < L, g t < n) (k : Fin L) :
    cycleWeights B (arithMap g hg) k = wt B (g k) (g (if (k : ℕ) + 1 = L then 0 else k + 1)) := by
  rw [cycleWeights, ← wt_val, arithMap_val, arithMap_val, val_finRotate_eq_ite]

/-! ### Recognising trees -/

private theorem isTree_of_existsUnique_lt_adj {V : Type*} [Finite V] {G : SimpleGraph V}
    (r : V → ℕ) (hr : Function.Injective r) (o : V) (ho : ∀ w, G.Adj w o → r o < r w)
    (h : ∀ v, v ≠ o → ∃! w, r w < r v ∧ G.Adj w v) : G.IsTree := by
  classical
  have := Fintype.ofFinite V
  choose par hpar huniq using h
  have hreach : ∀ k, ∀ v, r v = k → G.Reachable o v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv
      by_cases hvo : v = o
      · subst hvo
        rfl
      · obtain ⟨h1, h2⟩ := hpar v hvo
        exact (ih _ (hv ▸ h1) _ rfl).trans h2.reachable
  have hconn : G.Connected := (SimpleGraph.connected_iff _).2
    ⟨fun x y => (hreach _ x rfl).symm.trans (hreach _ y rfl), ⟨o⟩⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hcard : Nat.card {v // v ≠ o} = Nat.card G.edgeSet := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun v => ⟨s(v.1, par v.1 v.2), (hpar v.1 v.2).2.symm⟩) ⟨?_, ?_⟩
    · rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
      simp only [Subtype.mk.injEq, Sym2.eq_iff] at hvw
      rcases hvw with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h1
      · have := (hpar v hv).1
        have := (hpar w hw).1
        subst h1
        rw [h2] at this
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : G.Adj x y := he
        rcases lt_or_gt_of_ne (hr.ne hxy.ne) with hlt | hlt
        · have hy : y ≠ o := by
            rintro rfl
            exact absurd (ho x hxy) (by omega)
          refine ⟨⟨y, hy⟩, ?_⟩
          simp only [Subtype.mk.injEq]
          rw [← huniq y hy x ⟨hlt, hxy⟩, Sym2.eq_swap]
        · have hx : x ≠ o := by
            rintro rfl
            exact absurd (ho y hxy.symm) (by omega)
          refine ⟨⟨x, hx⟩, ?_⟩
          simp only [Subtype.mk.injEq]
          rw [← huniq x hx y ⟨hlt, hxy.symm⟩]
  rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨o⟩
  omega

private theorem isTree_arith {G : SimpleGraph (Fin n)} {Q : ℕ → ℕ → Prop}
    (hA : ∀ i j : Fin n, G.Adj i j ↔ Q i j) (r : ℕ → ℕ)
    (hr : ∀ x y, x < n → y < n → r x = r y → x = y) (o : ℕ) (ho : o < n)
    (hoQ : ∀ x, x < n → Q x o → r o < r x) (par : ℕ → ℕ)
    (hpar : ∀ v, v < n → v ≠ o → par v < n ∧ r (par v) < r v ∧ Q (par v) v)
    (huniq : ∀ v w, v < n → w < n → v ≠ o → r w < r v → Q w v → w = par v) : G.IsTree := by
  refine isTree_of_existsUnique_lt_adj (fun i : Fin n => r i)
    (fun i j h => Fin.ext (hr i j i.2 j.2 h)) ⟨o, ho⟩
    (fun w hw => hoQ w w.2 ((hA w ⟨o, ho⟩).1 hw)) (fun v hv => ?_)
  have hv' : (v : ℕ) ≠ o := fun h => hv (Fin.ext h)
  obtain ⟨h1, h2, h3⟩ := hpar v v.2 hv'
  refine ⟨⟨par v, h1⟩, ⟨h2, (hA _ _).2 h3⟩, fun w hw => Fin.ext ?_⟩
  exact huniq v w v.2 w.2 hv' hw.1 ((hA w v).1 hw.2)

/-- A matrix whose weights are those of a tree `T_{α,β,γ}` is a tree diagram. -/
theorem IsTShape.isTreeDiagram {C : Matrix (Fin n) (Fin n) ℤ} {α β γ : ℕ}
    (hT : IsTShape (diagramWeight C) α β γ) :
    IsTreeDiagram C := by
  obtain ⟨e, he⟩ := hT
  have hadj : ∀ p q : Fin (α + β + γ + 1),
      (diagramGraph C).Adj (e p) (e q) ↔ p ≠ q ∧ 0 < orderedModel (tShapeModel α β γ) p q := by
    intro p q
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [diagramGraph_adj, he p q hpq]
      exact ⟨fun h => ⟨hpq, h.2⟩, fun h => ⟨e.injective.ne hpq, h.2⟩⟩
  let par : ℕ → ℕ := fun q => if q = α + 1 ∨ q = α + β + 1 then 0 else q - 1
  refine isTree_of_existsUnique_lt_adj (fun v => (e.symm v : ℕ))
    (fun v w h => e.symm.injective (Fin.ext h)) (e ⟨0, by omega⟩) (fun w hw => ?_)
    (fun v hv => ?_)
  · rw [← e.apply_symm_apply w, hadj] at hw
    simp only [Equiv.symm_apply_apply]
    have : (e.symm w : ℕ) ≠ 0 := fun h => hw.1 (Fin.ext h)
    change 0 < (e.symm w : ℕ)
    omega
  · obtain ⟨q, rfl⟩ := e.surjective v
    have hq : (q : ℕ) ≠ 0 := fun h => hv (congrArg e (Fin.ext h))
    have hq' := q.2
    have hpar : par q < α + β + γ + 1 := by simp only [par]; split_ifs <;> omega
    refine ⟨e ⟨par q, hpar⟩, ?_, fun w hw => ?_⟩
    · simp only [Equiv.symm_apply_apply]
      rw [hadj]
      refine ⟨?_, fun h => ?_, ?_⟩
      · simp only [par]; split_ifs <;> omega
      · have := congrArg Fin.val h
        simp only [par] at this
        split_ifs at this <;> omega
      · simp only [orderedModel, tShapeModel, par]
        split_ifs <;> omega
    · obtain ⟨p, rfl⟩ := e.surjective w
      simp only [Equiv.symm_apply_apply] at hw ⊢
      rw [hadj] at hw
      obtain ⟨hlt, hpq, hpos⟩ := hw
      congr 1
      apply Fin.ext
      simp only [orderedModel, tShapeModel, par] at hpos ⊢
      have : (p : ℕ) < q := hlt
      split_ifs at hpos ⊢ <;> omega

/-! ### Subdiagrams of extended Dynkin shapes -/

private theorem IsInducedPath.diagramWeight_eq_zero {B : Matrix (Fin n) (Fin n) ℤ} {L : ℕ}
    {q : Fin L → Fin n} (hq : IsInducedPath B q) {i j : Fin L} (hij : i ≠ j)
    (h : (i : ℕ) + 1 ≠ j) (h' : (j : ℕ) + 1 ≠ i) : diagramWeight B (q i) (q j) = 0 := by
  by_contra h0
  have := (hq.2.2 i j hij).1 ⟨hq.2.1.ne hij, Nat.pos_of_ne_zero h0⟩
  omega

private theorem IsInducedPath.isShapeOf {B : Matrix (Fin n) (Fin n) ℤ} {L : ℕ}
    {q : Fin L → Fin n} (hq : IsInducedPath B q) (F : ℕ → ℕ → ℕ)
    (hF0 : ∀ i j, i + 1 < j → j < L → F i j = 0)
    (hF : ∀ i j : Fin L, (i : ℕ) + 1 = j → diagramWeight B (q i) (q j) = F i j) :
    IsShapeOf (diagramWeight (B.submatrix q q)) L F := by
  refine isShapeOf_submatrix_of_lt (v := q) (f := F) (fun i j hij => ?_)
  have hij' : (i : ℕ) < j := hij
  by_cases hc : (i : ℕ) + 1 = j
  · exact hF i j hc
  · rw [hq.diagramWeight_eq_zero hij.ne hc (by omega), hF0 i j (by omega) j.2]

/-- Three vertices of an induced path, the first two of weight `3`: a subdiagram of shape
`G₂^{(1)}(a)`. -/
private theorem IsInducedPath.not_isTwoFinite_of_weight_three {B : Matrix (Fin n) (Fin n) ℤ}
    {q : Fin 3 → Fin n} (hq : IsInducedPath B q) (h3 : diagramWeight B (q 0) (q 1) = 3)
    (hB : IsTwoFinite B) : False := by
  have hw1 : 0 < diagramWeight B (q 1) (q 2) := ((hq.2.2 1 2 (by decide)).2 (by simp)).2
  have hw3 : diagramWeight B (q 1) (q 2) ≤ 3 := hB.diagramWeight_le_three _ _
  let r : Fin 3 ↪ Fin n := ⟨q, hq.2.1⟩
  refine not_isTwoFinite_of_isG2AffineShape (B := B.submatrix r r)
    (a := diagramWeight B (q 1) (q 2)) ⟨by omega, ?_⟩ (hB.submatrix r)
  refine hq.isShapeOf _ (fun i j h h' => ?_) (fun i j hij => ?_)
  · unfold g2AffineModel
    split_ifs <;> omega
  · fin_cases i <;> fin_cases j <;> simp_all [g2AffineModel]

/-- An induced path with weights `2, 1, …, 1, 2`: a subdiagram of shape `C_k^{(1)}`. -/
private theorem IsInducedPath.not_isTwoFinite_of_cAffine {B : Matrix (Fin n) (Fin n) ℤ}
    {k : ℕ} (hk : 2 ≤ k) {q : Fin (k + 1) → Fin n} (hq : IsInducedPath B q)
    (hw : ∀ i j : Fin (k + 1), (i : ℕ) + 1 = j →
      diagramWeight B (q i) (q j) = if (i : ℕ) = 0 ∨ (j : ℕ) = k then 2 else 1)
    (hB : IsTwoFinite B) : False := by
  let r : Fin (k + 1) ↪ Fin n := ⟨q, hq.2.1⟩
  refine not_isTwoFinite_of_isCAffineShape (B := B.submatrix r r) (k := k)
    ⟨hk, hq.isShapeOf _ (fun i j h h' => ?_) (fun i j hij => ?_)⟩ (hB.submatrix r)
  · unfold cAffineModel
    split_ifs <;> omega
  · rw [hw i j hij]
    have := j.2
    unfold cAffineModel
    split_ifs <;> omega

/-- An induced path `q` with weights `1, …, 1, 2` and a vertex `y` attached to `q₁` alone with
weight `1`: a subdiagram of shape `B_k^{(1)}`. -/
private theorem IsInducedPath.not_isTwoFinite_of_bAffine {B : Matrix (Fin n) (Fin n) ℤ}
    {k : ℕ} (hk : 3 ≤ k) {q : Fin k → Fin n} (hq : IsInducedPath B q) {y : Fin n}
    (hy : y ∉ Set.range q) (hyadj : ∀ i, (diagramGraph B).Adj y (q i) ↔ (i : ℕ) = 1)
    (hy1 : ∀ i : Fin k, (i : ℕ) = 1 → diagramWeight B y (q i) = 1)
    (hw : ∀ i j : Fin k, (i : ℕ) + 1 = j →
      diagramWeight B (q i) (q j) = if (j : ℕ) + 1 = k then 2 else 1)
    (hB : IsTwoFinite B) : False := by
  let r : Fin (k + 1) ↪ Fin n := ⟨Fin.cons y q, Fin.cons_injective_of_injective hy hq.2.1⟩
  refine not_isTwoFinite_of_isBAffineShape (B := B.submatrix r r) (k := k)
    ⟨hk, isShapeOf_submatrix_of_lt (fun i j hij => ?_)⟩ (hB.submatrix r)
  have hij' : (i : ℕ) < j := hij
  induction j using Fin.cases with
  | zero => simp at hij'
  | succ j =>
    induction i using Fin.cases with
    | zero =>
      simp only [r, Function.Embedding.coeFn_mk, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
        Fin.val_succ]
      by_cases hj : (j : ℕ) = 1
      · rw [hy1 j hj]
        unfold bAffineModel
        split_ifs <;> omega
      · rw [diagramWeight_eq_zero_of_not_adj hB.1 (by rw [hyadj]; exact hj)]
        unfold bAffineModel
        split_ifs <;> omega
    | succ i =>
      simp only [r, Function.Embedding.coeFn_mk, Fin.cons_succ, Fin.val_succ] at hij' ⊢
      have hj := j.2
      by_cases hc : (i : ℕ) + 1 = j
      · rw [hw i j hc]
        unfold bAffineModel
        split_ifs <;> omega
      · rw [hq.diagramWeight_eq_zero (fun h => by subst h; omega) hc (by omega)]
        unfold bAffineModel
        split_ifs <;> omega

/-! ### The normalized setting: the path is `0, 1, …, m - 1` and the extra vertex is `m` -/

section Normalized

variable {m : ℕ} {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ}

private theorem path_adj (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1)))
    (i j : Fin (m + 1)) (hi : (i : ℕ) < m) (hj : (j : ℕ) < m) :
    (diagramGraph B).Adj i j ↔ (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i := by
  by_cases hij : (i : ℕ) = j
  · obtain rfl : i = j := Fin.ext hij
    simp only [diagramGraph_adj, ne_eq, not_true_eq_false, false_and, false_iff]
    omega
  · have := hP.1.2.2 ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (Fin.mk.inj_iff.mp h))
    simpa using this

private theorem path_arrow (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1)))
    (x : ℕ) (hx : x + 1 < m) : 0 < ent B x (x + 1) := by
  have := hP.2 ⟨x, by omega⟩ ⟨x + 1, hx⟩ rfl
  rw [show ent B x (x + 1) = B ⟨x, by omega⟩ ⟨x + 1, by omega⟩ from
    ent_val B ⟨x, by omega⟩ ⟨x + 1, by omega⟩]
  simpa using this

/-- The adjacency of the normalized diagram in which the extra vertex `m` is adjacent to `a`
and `b`. -/
private def adjQ (m a b x y : ℕ) : Prop :=
  (x < m ∧ y < m ∧ (x + 1 = y ∨ y + 1 = x)) ∨ (x = m ∧ (y = a ∨ y = b)) ∨
    (y = m ∧ (x = a ∨ x = b))

private theorem adj_iff_adjQ (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1)))
    {a b : ℕ} (ha : a < m) (hb : b < m) {D : ℕ → Prop}
    (hU : ∀ j : Fin (m + 1), D j → (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = b))
    (i j : Fin (m + 1)) (hi : D i) (hj : D j) :
    (diagramGraph B).Adj i j ↔ adjQ m a b i j := by
  have hi' := i.2
  have hj' := j.2
  rcases (show (i : ℕ) < m ∨ (i : ℕ) = m by omega) with hi2 | hi2 <;>
    rcases (show (j : ℕ) < m ∨ (j : ℕ) = m by omega) with hj2 | hj2
  · rw [path_adj hP i j hi2 hj2]
    unfold adjQ
    omega
  · obtain rfl : j = Fin.last m := Fin.ext hj2
    rw [(diagramGraph B).adj_comm, hU i hi hi2]
    unfold adjQ
    simp only [Fin.val_last, true_and] at *
    omega
  · obtain rfl : i = Fin.last m := Fin.ext hi2
    rw [hU j hj hj2]
    unfold adjQ
    simp only [Fin.val_last, true_and] at *
    omega
  · obtain rfl : i = j := Fin.ext (by omega)
    simp only [diagramGraph_adj, ne_eq, not_true_eq_false, false_and, false_iff]
    unfold adjQ
    omega

/-- The vertices of the cycle `(a, a + 1, …, b, m)`. -/
private def cycPos (m a b k : ℕ) : ℕ := if k ≤ b - a then a + k else m

private theorem cycPos_lt {a b : ℕ} (hab : a < b) (hbm : b < m) :
    ∀ t < b - a + 2, cycPos m a b t < m + 1 :=
  fun t _ => by unfold cycPos; split_ifs <;> omega

/-- The weights of the cycle `(a, …, b, m)`, read through a reindexing. -/
private theorem cycleWeights_cycPos_cast {a b M : ℕ} (hab : a < b) (hbm : b < m)
    (h : b - a + 2 = M) (i : Fin M) :
    (cycleWeights B (arithMap (cycPos m a b) (cycPos_lt hab hbm)) ∘ Fin.cast h.symm) i =
      wt B (cycPos m a b i) (cycPos m a b (if (i : ℕ) + 1 = b - a + 2 then 0 else i + 1)) :=
  cycleWeights_arithMap B _ _ _

/-- If the extra vertex `m` is adjacent to `a < b` and to no index strictly between them, then
`(a, a + 1, …, b, m)` is a chordless cycle. -/
private theorem isChordlessCycle_cycPos
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a b : ℕ}
    (hab : a < b) (hbm : b < m)
    (hU : ∀ j : Fin (m + 1), a ≤ (j : ℕ) → (j : ℕ) ≤ b →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = b)) :
    IsChordlessCycle B (arithMap (cycPos m a b) (cycPos_lt hab hbm)) :=
  isChordlessCycle_arithMap (Q := adjQ m a b) (D := fun x => (a ≤ x ∧ x ≤ b) ∨ x = m)
    (adj_iff_adjQ hP (by omega) hbm (D := fun x => (a ≤ x ∧ x ≤ b) ∨ x = m)
      fun j hj hjm => hU j (by omega) (by omega)) (cycPos m a b)
    (cycPos_lt hab hbm) (fun t _ => by unfold cycPos; split_ifs <;> omega) (by omega)
    (fun s t hs ht h => by unfold cycPos at h; split_ifs at h <;> omega)
    (fun s t hs ht hst => by unfold adjQ cycPos; split_ifs <;> omega)

/-- The cycle `(a, …, b, m)` of a `2`-finite matrix is oriented with `b → m → a`. -/
private theorem cycPos_orientation (hS : SkewSymmetrizable B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a b : ℕ}
    (hab : a < b) (hbm : b < m)
    (hor : IsCyclicallyOriented B (arithMap (cycPos m a b) (cycPos_lt hab hbm))) :
    0 < ent B b m ∧ 0 < ent B m a := by
  have hpos : ∀ k, k ≤ b - a → cycPos m a b k = a + k := fun k hk => if_pos hk
  have hposU : cycPos m a b (b - a + 1) = m := if_neg (by omega)
  rcases hor with h | h
  · have h1 := h ⟨b - a, by omega⟩
    have h2 := h ⟨b - a + 1, by omega⟩
    have hent : ∀ (k : ℕ) (hk : k < b - a + 2),
        B (arithMap (cycPos m a b) (cycPos_lt hab hbm) ⟨k, hk⟩)
            (arithMap (cycPos m a b) (cycPos_lt hab hbm) (finRotate _ ⟨k, hk⟩)) =
          ent B (cycPos m a b k) (cycPos m a b (if k + 1 = b - a + 2 then 0 else k + 1)) :=
      fun k _ => (ent_val B _ _).symm.trans (by simp only [arithMap_val, val_finRotate_eq_ite])
    rw [hent] at h1 h2
    rw [if_neg (by omega), hpos _ le_rfl, hposU, show a + (b - a) = b by omega] at h1
    rw [if_pos rfl, hposU, hpos 0 (by omega), add_zero] at h2
    exact ⟨h1, h2⟩
  · have h1 := h ⟨0, by omega⟩
    have hent : ∀ (k : ℕ) (hk : k < b - a + 2),
        B (arithMap (cycPos m a b) (cycPos_lt hab hbm) (finRotate _ ⟨k, hk⟩))
            (arithMap (cycPos m a b) (cycPos_lt hab hbm) ⟨k, hk⟩) =
          ent B (cycPos m a b (if k + 1 = b - a + 2 then 0 else k + 1)) (cycPos m a b k) :=
      fun k _ => (ent_val B _ _).symm.trans (by simp only [arithMap_val, val_finRotate_eq_ite])
    rw [hent, if_neg (by omega), hpos 0 (by omega), hpos 1 (by omega), add_zero] at h1
    exact absurd h1 (ent_pos_asymm hS (path_arrow hP a (by omega)))

/-- The weights of a chordless cycle `(a, …, b, m)` of a `2`-finite matrix are in
`L_{b-a+2}`. -/
private theorem cycPos_weights {a b : ℕ} (hab : a < b) (hbm : b < m)
    (hadm : IsAdmissibleCycleWeights
      (cycleWeights B (arithMap (cycPos m a b) (cycPos_lt hab hbm)))) :
    ((∀ x, a ≤ x → x < b → wt B x (x + 1) = 1) ∧ wt B b m = 1 ∧ wt B m a = 1) ∨
      (b = a + 1 ∧ ((wt B a (a + 1) = 2 ∧ wt B (a + 1) m = 2 ∧ wt B m a = 1) ∨
        (wt B a (a + 1) = 2 ∧ wt B (a + 1) m = 1 ∧ wt B m a = 2) ∨
        (wt B a (a + 1) = 1 ∧ wt B (a + 1) m = 2 ∧ wt B m a = 2))) ∨
      (b = a + 2 ∧ ((wt B a (a + 1) = 2 ∧ wt B (a + 1) (a + 2) = 1 ∧ wt B (a + 2) m = 2 ∧
          wt B m a = 1) ∨
        (wt B a (a + 1) = 1 ∧ wt B (a + 1) (a + 2) = 2 ∧ wt B (a + 2) m = 1 ∧
          wt B m a = 2))) := by
  rcases hadm with h | ⟨h3, h⟩ | ⟨h4, h⟩
  · have hcw : ∀ (k : ℕ) (hk : k < b - a + 2),
        cycleWeights B (arithMap (cycPos m a b) (cycPos_lt hab hbm)) ⟨k, hk⟩ =
          wt B (cycPos m a b k) (cycPos m a b (if k + 1 = b - a + 2 then 0 else k + 1)) :=
      fun k _ => cycleWeights_arithMap B _ _ _
    have hpos : ∀ k, k ≤ b - a → cycPos m a b k = a + k := fun k hk => if_pos hk
    have hposU : cycPos m a b (b - a + 1) = m := if_neg (by omega)
    refine Or.inl ⟨fun x hx hxb => ?_, ?_, ?_⟩
    · have := h ⟨x - a, by omega⟩
      rwa [hcw, if_neg (by omega), hpos _ (by omega), hpos _ (by omega),
        show a + (x - a) = x by omega, show a + (x - a + 1) = x + 1 by omega] at this
    · have := h ⟨b - a, by omega⟩
      rwa [hcw, if_neg (by omega), hpos _ le_rfl, hposU, show a + (b - a) = b by omega] at this
    · have := h ⟨b - a + 1, by omega⟩
      rwa [hcw, if_pos rfl, hposU, hpos 0 (by omega), add_zero] at this
  · obtain rfl : b = a + 1 := by omega
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h <;>
    · have e₀ := (cycleWeights_cycPos_cast hab hbm h3 0).symm.trans (congrFun h 0)
      have e₁ := (cycleWeights_cycPos_cast hab hbm h3 1).symm.trans (congrFun h 1)
      have e₂ := (cycleWeights_cycPos_cast hab hbm h3 2).symm.trans (congrFun h 2)
      simp [cycPos] at e₀ e₁ e₂
      omega
  · obtain rfl : b = a + 2 := by omega
    refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;>
    · have e₀ := (cycleWeights_cycPos_cast hab hbm h4 0).symm.trans (congrFun h 0)
      have e₁ := (cycleWeights_cycPos_cast hab hbm h4 1).symm.trans (congrFun h 1)
      have e₂ := (cycleWeights_cycPos_cast hab hbm h4 2).symm.trans (congrFun h 2)
      have e₃ := (cycleWeights_cycPos_cast hab hbm h4 3).symm.trans (congrFun h 3)
      simp [cycPos] at e₀ e₁ e₂ e₃
      omega

/-- **The cycle through the extra vertex.** If the extra vertex `m` is adjacent to `a < b` and
to no index strictly between them, then `(a, a + 1, …, b, m)` is a chordless cycle; it is
cyclically oriented with `b → m → a`, and its weights are in `L_{b-a+2}`. -/
private theorem cycle_facts (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a b : ℕ}
    (hab : a < b) (hbm : b < m)
    (hU : ∀ j : Fin (m + 1), a ≤ (j : ℕ) → (j : ℕ) ≤ b →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = b)) :
    0 < ent B b m ∧ 0 < ent B m a ∧
      (((∀ x, a ≤ x → x < b → wt B x (x + 1) = 1) ∧ wt B b m = 1 ∧ wt B m a = 1) ∨
        (b = a + 1 ∧ ((wt B a (a + 1) = 2 ∧ wt B (a + 1) m = 2 ∧ wt B m a = 1) ∨
          (wt B a (a + 1) = 2 ∧ wt B (a + 1) m = 1 ∧ wt B m a = 2) ∨
          (wt B a (a + 1) = 1 ∧ wt B (a + 1) m = 2 ∧ wt B m a = 2))) ∨
        (b = a + 2 ∧ ((wt B a (a + 1) = 2 ∧ wt B (a + 1) (a + 2) = 1 ∧ wt B (a + 2) m = 2 ∧
            wt B m a = 1) ∨
          (wt B a (a + 1) = 1 ∧ wt B (a + 1) (a + 2) = 2 ∧ wt B (a + 2) m = 1 ∧
            wt B m a = 2)))) := by
  obtain ⟨hor, hadm⟩ :=
    hB.isCyclicallyOriented_of_isChordlessCycle (isChordlessCycle_cycPos hP hab hbm hU)
  exact ⟨(cycPos_orientation hB.1 hP hab hbm hor).1, (cycPos_orientation hB.1 hP hab hbm hor).2,
    cycPos_weights hab hbm hadm⟩

/-- **A path with a pendant vertex** is a tree diagram, hence of Dynkin class. -/
private theorem exists_of_adj_eq_single (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a : ℕ} (ha : a < m)
    (hU : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a)) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  have hA := adj_iff_adjQ hP ha ha (D := fun _ => True) (fun j _ hj => by rw [hU j hj, or_self])
  refine exists_isOfDynkinClass_of_isTreeDiagram hB ?_
  refine isTree_arith (Q := adjQ m a a) (fun i j => hA i j trivial trivial) id
    (fun x y _ _ h => h) 0 (by omega) (fun x hx h => ?_) (fun v => if v = m then a else v - 1)
    (fun v hv hv0 => ?_) (fun v w hv hw hv0 hlt h => ?_)
  · unfold adjQ at h
    simp only [id]
    omega
  · unfold adjQ
    simp only [id]
    split_ifs <;> omega
  · unfold adjQ at h
    simp only [id] at hlt ⊢
    split_ifs <;> omega

/-- In `μ_k(B)` the entry between `i` and `j` vanishes when `i → k → j → i` and
`w(j, i) = w(i, k) w(k, j)`. -/
private theorem diagramWeight_matrixMutation_eq_zero {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hS : SkewSymmetrizable B) {i k j : Fin n} (hik : 0 < B i k) (hkj : 0 < B k j)
    (hji : 0 < B j i) (hprod : diagramWeight B j i = diagramWeight B i k * diagramWeight B k j) :
    diagramWeight (matrixMutation le_rfl B k) i j = 0 := by
  obtain ⟨d, hd⟩ := id hS
  have hS' : SkewSymmetrizable (matrixMutation le_rfl B k) := ⟨d, hd.matrixMutation le_rfl k⟩
  have h1 := (hS.skewSymmetrization_matrixMutation_of_pos_pos hik hkj).1
  have hij : B i j < 0 := by rcases hS.entries_sign j i with h | h | h <;> omega
  have h2 := (hS.skewSymmetrization_apply i j).1
  rw [Real.sign_of_neg (by exact_mod_cast hij), diagramWeight_comm, hprod] at h2
  have h3 := (hS'.skewSymmetrization_apply i j).2.1
  rw [h1, h2] at h3
  push_cast at h3
  have : ((diagramWeight (matrixMutation le_rfl B k) i j : ℕ) : ℝ) = 0 := by
    rw [← h3]
    ring
  exact_mod_cast this

/-- Mutation at the extra vertex `m`, adjacent to `a` and `a + 1` only, keeps every weight but
that of the pair `{a, a + 1}`. -/
private theorem diagramWeight_matrixMutation_last (hS : SkewSymmetrizable B) {a : ℕ}
    (ham : a + 1 < m) (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 1) i j)
    (i j : Fin (m + 1)) (hp : ¬((i : ℕ) = a ∧ (j : ℕ) = a + 1))
    (hp' : ¬((i : ℕ) = a + 1 ∧ (j : ℕ) = a)) :
    diagramWeight (matrixMutation le_rfl B (Fin.last m)) i j = diagramWeight B i j := by
  obtain ⟨d, hd⟩ := id hS
  have hzero : ∀ i : Fin (m + 1), (i : ℕ) ≠ a → (i : ℕ) ≠ a + 1 →
      B i (Fin.last m) = 0 ∧ B (Fin.last m) i = 0 := by
    intro i hia hib
    have h0 := diagramWeight_eq_zero_of_not_adj hS (i := i) (j := Fin.last m) (by
      rw [hA]
      unfold adjQ
      simp only [Fin.val_last]
      omega)
    have h0' : B i (Fin.last m) = 0 := by
      by_contra h
      have := (hS.diagramWeight_pos_iff _ _).2 h
      omega
    exact ⟨h0', (hd.apply_eq_zero_comm _ _).1 h0'⟩
  by_cases hij : i = j
  · subst hij
    have hS' : SkewSymmetrizable (matrixMutation le_rfl B (Fin.last m)) :=
      ⟨d, hd.matrixMutation le_rfl _⟩
    simp [diagramWeight, hS.diag_eq_zero, hS'.diag_eq_zero]
  by_cases hi : i = Fin.last m
  · subst hi
    exact (hS.diagramWeight_matrixMutation_self _ j).2.1
  by_cases hj : j = Fin.last m
  · subst hj
    exact (hS.diagramWeight_matrixMutation_self _ i).1
  have hor : ((i : ℕ) ≠ a ∧ (i : ℕ) ≠ a + 1) ∨ ((j : ℕ) ≠ a ∧ (j : ℕ) ≠ a + 1) := by
    have := Fin.val_ne_of_ne hij
    omega
  have e : matrixMutation le_rfl B (Fin.last m) i j = B i j ∧
      matrixMutation le_rfl B (Fin.last m) j i = B j i := by
    rcases hor with h | h
    · exact ⟨matrixMutation_apply_of_eq_zero le_rfl B _ hi hj (Or.inl (hzero i h.1 h.2).1),
        matrixMutation_apply_of_eq_zero le_rfl B _ hj hi (Or.inr (hzero i h.1 h.2).2)⟩
    · exact ⟨matrixMutation_apply_of_eq_zero le_rfl B _ hi hj (Or.inr (hzero j h.1 h.2).2),
        matrixMutation_apply_of_eq_zero le_rfl B _ hj hi (Or.inl (hzero j h.1 h.2).1)⟩
  simp only [diagramWeight, e.1, e.2]

/-- The adjacency after the mutation at the extra vertex `m`, adjacent to `a` and `a + 1` only,
when it removes the pair `{a, a + 1}`. -/
private theorem adj_matrixMutation_last_iff (hS : SkewSymmetrizable B) {a : ℕ} (ham : a + 1 < m)
    (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 1) i j)
    (hyx : diagramWeight (matrixMutation le_rfl B (Fin.last m)) ⟨a + 1, by omega⟩ ⟨a, by omega⟩ =
      0) (i j : Fin (m + 1)) :
    (diagramGraph (matrixMutation le_rfl B (Fin.last m))).Adj i j ↔
      (adjQ m a (a + 1) i j ∧ ¬((i : ℕ) = a ∧ (j : ℕ) = a + 1) ∧
        ¬((i : ℕ) = a + 1 ∧ (j : ℕ) = a)) := by
  let x : Fin (m + 1) := ⟨a, by omega⟩
  let y : Fin (m + 1) := ⟨a + 1, by omega⟩
  by_cases hp : ((i : ℕ) = a ∧ (j : ℕ) = a + 1) ∨ ((i : ℕ) = a + 1 ∧ (j : ℕ) = a)
  · have h0 : diagramWeight (matrixMutation le_rfl B (Fin.last m)) i j = 0 := by
      rcases hp with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · obtain rfl : i = x := Fin.ext hi
        obtain rfl : j = y := Fin.ext hj
        rw [diagramWeight_comm]
        exact hyx
      · obtain rfl : i = y := Fin.ext hi
        obtain rfl : j = x := Fin.ext hj
        exact hyx
    rw [diagramGraph_adj, h0]
    simp only [lt_self_iff_false, and_false, false_iff]
    tauto
  · push Not at hp
    rw [diagramGraph_adj, diagramWeight_matrixMutation_last hS ham hA i j
      (fun h => by have := hp.1 h.1; omega) (fun h => by have := hp.2 h.1; omega),
      ← diagramGraph_adj, hA i j]
    exact ⟨fun h => ⟨h, fun h' => by have := hp.1 h'.1; omega,
      fun h' => by have := hp.2 h'.1; omega⟩, fun h => h.1⟩

/-- **A triangle whose mutation at the extra vertex is a path**, hence of Dynkin class. -/
private theorem exists_of_triangle (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a : ℕ}
    (ham : a + 1 < m)
    (hU : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = a + 1))
    (h1 : 0 < ent B (a + 1) m) (h2 : 0 < ent B m a)
    (hprod : wt B a (a + 1) = wt B (a + 1) m * wt B m a) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  have hS := hB.1
  have hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 1) i j := fun i j =>
    adj_iff_adjQ hP (by omega) ham (D := fun _ => True) (fun j _ hj => hU j hj) i j trivial trivial
  let x : Fin (m + 1) := ⟨a, by omega⟩
  let y : Fin (m + 1) := ⟨a + 1, by omega⟩
  have hyx : diagramWeight (matrixMutation le_rfl B (Fin.last m)) y x = 0 := by
    refine diagramWeight_matrixMutation_eq_zero hS (k := Fin.last m)
      (h1.trans_eq (ent_val B y (Fin.last m))) (h2.trans_eq (ent_val B (Fin.last m) x))
      ((path_arrow hP a ham).trans_eq (ent_val B x y)) ?_
    rwa [← wt_val, ← wt_val, ← wt_val]
  refine exists_isOfDynkinClass_of_matrixMutationList hB [Fin.last m] ?_
  refine exists_isOfDynkinClass_of_isTreeDiagram (hB.matrixMutationList [Fin.last m]) ?_
  rw [matrixMutationList_singleton]
  refine isTree_arith (Q := fun x y => adjQ m a (a + 1) x y ∧ ¬(x = a ∧ y = a + 1) ∧
    ¬(x = a + 1 ∧ y = a)) (adj_matrixMutation_last_iff hS ham hA hyx)
    (fun v => if v < m then 2 * v else 2 * a + 1) (fun v w hv hw h => ?_)
    0 (by omega) (fun v hv h => ?_) (fun v => if v = m then a else if v = a + 1 then m else v - 1)
    (fun v hv hv0 => ?_) (fun v w hv hw hv0 hlt h => ?_)
  · split_ifs at h <;> omega
  · unfold adjQ at h
    split_ifs <;> omega
  · unfold adjQ
    split_ifs <;> omega
  · unfold adjQ at h
    split_ifs at hlt ⊢ <;> omega

private theorem adjQ_comm {m a b x y : ℕ} : adjQ m a b x y ↔ adjQ m a b y x := by
  unfold adjQ
  omega

/-- The positions of the crown `S^{b-a-1}_{m-b,1,a+1}`: the cycle `b, m, a, a + 1, …, b - 1`,
the branch `b + 1, …, m - 1` at `b` and the branch `a - 1, …, 0` at `a`. -/
private def crownPos (m a b k : ℕ) : ℕ :=
  if k = 0 then b else if k = 1 then m else if k ≤ b - a + 1 then a + k - 2
  else if k ≤ m - a then b + (k - (b - a + 1)) else a - (k - (m - a))

open Classical in
/-- The crown model read through `crownPos`, for `b = a + s + 1` and `m = b + p + 1`. -/
private theorem crownModel_eq_adjQ (a s p i j : ℕ) (hij : i < j) (hj : j ≤ a + s + 2 + p) :
    crownModel s (p + 1) 1 (a + 1) i j =
      if adjQ (a + s + 2 + p) a (a + s + 1) (crownPos (a + s + 2 + p) a (a + s + 1) i)
        (crownPos (a + s + 2 + p) a (a + s + 1) j) then 1 else 0 := by
  have hcp : ∀ k, k ≤ a + s + 2 + p →
      (k = 0 ∧ crownPos (a + s + 2 + p) a (a + s + 1) k = a + s + 1) ∨
      (k = 1 ∧ crownPos (a + s + 2 + p) a (a + s + 1) k = a + s + 2 + p) ∨
      (2 ≤ k ∧ k ≤ s + 2 ∧ crownPos (a + s + 2 + p) a (a + s + 1) k + 2 = a + k) ∨
      (s + 2 < k ∧ k ≤ s + 2 + p ∧ crownPos (a + s + 2 + p) a (a + s + 1) k + 1 = a + k) ∨
      (s + 2 + p < k ∧ crownPos (a + s + 2 + p) a (a + s + 1) k + k = a + s + 2 + p) := by
    intro k hk
    unfold crownPos
    split_ifs <;> omega
  have h1 := hcp i (by omega)
  have h2 := hcp j hj
  generalize crownPos (a + s + 2 + p) a (a + s + 1) i = x at h1 ⊢
  generalize crownPos (a + s + 2 + p) a (a + s + 1) j = y at h2 ⊢
  simp only [crownModel, adjQ, Nat.add_sub_cancel]
  rcases h1 with h1 | h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 | h2 <;>
    split_ifs <;> omega

open Classical in
/-- When the path, the edge `{b, m}` and the edge `{m, a}` have weight `1`, the weights are those
of the adjacency `adjQ`. -/
private theorem diagramWeight_eq_ite_adjQ (hS : SkewSymmetrizable B) {a b : ℕ}
    (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a b i j)
    (hall : ∀ x, x + 1 < m → wt B x (x + 1) = 1) (hbw : wt B b m = 1) (haw : wt B m a = 1)
    (i j : Fin (m + 1)) : diagramWeight B i j = if adjQ m a b i j then 1 else 0 := by
  split_ifs with h
  · rw [← wt_val]
    unfold adjQ at h
    rcases h with ⟨hi, hj, h | h⟩ | ⟨hi, h | h⟩ | ⟨hj, h | h⟩
    · rw [← h]
      exact hall i (by omega)
    · rw [← h, wt_comm]
      exact hall j (by omega)
    · rw [hi, h]
      exact haw
    · rw [hi, h, wt_comm]
      exact hbw
    · rw [hj, h, wt_comm]
      exact haw
    · rw [hj, h]
      exact hbw
  · exact diagramWeight_eq_zero_of_not_adj hS (by rw [hA i j]; exact h)

/-- **The unit cycle with branches**: a crown, mutation equivalent to a tree. -/
private theorem exists_of_crown (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a b : ℕ}
    (hab : a + 2 ≤ b) (hbm : b < m)
    (hU : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = b))
    (hbU : 0 < ent B b m) (hUa : 0 < ent B m a)
    (hall : ∀ x, x + 1 < m → wt B x (x + 1) = 1) (hbw : wt B b m = 1) (haw : wt B m a = 1) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  classical
  have hWf := diagramWeight_eq_ite_adjQ hB.1 (fun i j => adj_iff_adjQ hP (by omega) hbm
    (D := fun _ => True) (fun j _ hj => hU j hj) i j trivial trivial) hall hbw haw
  obtain ⟨s, rfl⟩ : ∃ s, b = a + s + 1 := ⟨b - a - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, m = a + s + 2 + p := ⟨m - (a + s + 2), by omega⟩
  have hcard : p + 1 + 1 + (a + 1) + s = a + s + 2 + p + 1 := by omega
  have hg : ∀ t < p + 1 + 1 + (a + 1) + s,
      crownPos (a + s + 2 + p) a (a + s + 1) t < a + s + 2 + p + 1 := by
    intro t ht
    unfold crownPos
    split_ifs <;> omega
  have hinj : ∀ u v, u < p + 1 + 1 + (a + 1) + s → v < p + 1 + 1 + (a + 1) + s →
      crownPos (a + s + 2 + p) a (a + s + 1) u = crownPos (a + s + 2 + p) a (a + s + 1) v →
        u = v := by
    intro u v hu hv h
    unfold crownPos at h
    split_ifs at h <;> omega
  let e : Fin (p + 1 + 1 + (a + 1) + s) ≃ Fin (a + s + 2 + p + 1) :=
    Equiv.ofBijective (arithMap (crownPos (a + s + 2 + p) a (a + s + 1)) hg)
      ((Fintype.bijective_iff_injective_and_card _).2 ⟨arithMap_injective hinj, by simp [hcard]⟩)
  have hS : IsCrownShape B s (p + 1) 1 (a + 1) := by
    refine ⟨by omega, le_rfl, by omega, e, fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [hWf]
      change (if adjQ (a + s + 2 + p) a (a + s + 1) (crownPos (a + s + 2 + p) a (a + s + 1) i)
        (crownPos (a + s + 2 + p) a (a + s + 1) j) then 1 else 0) = _
      have := i.2
      have := j.2
      unfold orderedModel
      rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
      · rw [if_pos (show (i : ℕ) < j from h), crownModel_eq_adjQ a s p i j h (by omega)]
      · rw [if_neg (show ¬(i : ℕ) < j by omega), crownModel_eq_adjQ a s p j i h (by omega)]
        exact if_congr adjQ_comm rfl rfl
    · rw [show B (e i) (e j) = ent B (crownPos (a + s + 2 + p) a (a + s + 1) i)
          (crownPos (a + s + 2 + p) a (a + s + 1) j) from (ent_val B _ _).symm]
      have key : ∀ x y, (x = a + s + 1 ∧ y = a + s + 2 + p) ∨ (x = a + s + 2 + p ∧ y = a) ∨
          (x + 1 = y ∧ y < a + s + 2 + p) → 0 < ent B x y := by
        rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hy⟩)
        · exact hbU
        · exact hUa
        · exact path_arrow hP x hy
      apply key
      have := i.2
      have := j.2
      unfold crownPos
      split_ifs <;> omega
  obtain ⟨t, ht⟩ := exists_isTShape_matrixMutationList_of_isCrownShape hB.1 hS
  exact exists_isOfDynkinClass_of_matrixMutationList hB t
    (exists_isOfDynkinClass_of_isTreeDiagram (hB.matrixMutationList t)
      (IsTShape.isTreeDiagram ht))

/-- **(P1)** No two consecutive edges of the path carry a weight `3`: three consecutive vertices
of the path with a weight `3` form a subdiagram of shape `G₂^{(1)}(a)`. -/
private theorem path_weight_ne_three (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {x : ℕ}
    (hx : x + 2 < m) : wt B x (x + 1) ≠ 3 ∧ wt B (x + 1) (x + 2) ≠ 3 := by
  have hA : ∀ i j : Fin (m + 1), (i : ℕ) < m → (j : ℕ) < m →
      ((diagramGraph B).Adj i j ↔ (fun u v : ℕ => u + 1 = v ∨ v + 1 = u) i j) :=
    fun i j hi hj => path_adj hP i j hi hj
  constructor
  · intro h3
    have hq := isInducedPath_arithMap (Q := fun u v : ℕ => u + 1 = v ∨ v + 1 = u)
      (D := fun u => u < m) hA (L := 3) (fun t => x + t) (fun t ht => by omega)
      (fun t ht => by omega) (by omega) (fun s t _ _ h => by omega) (fun s t _ _ _ => by omega)
    refine hq.not_isTwoFinite_of_weight_three ?_ hB
    rw [← wt_val]
    convert h3 using 2 <;> simp
  · intro h3
    have hq := isInducedPath_arithMap (Q := fun u v : ℕ => u + 1 = v ∨ v + 1 = u)
      (D := fun u => u < m) hA (L := 3) (fun t => x + 2 - t) (fun t ht => by omega)
      (fun t ht => by omega) (by omega) (fun s t _ _ h => by omega) (fun s t _ _ _ => by omega)
    refine hq.not_isTwoFinite_of_weight_three ?_ hB
    rw [← wt_val, wt_comm]
    convert h3 using 2 <;> simp

/-- A weight `2` on the path below the unit cycle `(a, …, b, m)` gives a subdiagram of shape
`B^{(1)}`, on `(m; a + 1, a, a - 1, …, e)`. -/
private theorem false_of_bAffine_left (hB : IsTwoFinite B) {a b e : ℕ} (hab : a + 2 ≤ b)
    (hbm : b < m) (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a b i j)
    (hea : e < a) (he2 : wt B e (e + 1) = 2)
    (hw1 : ∀ x, e < x → x ≤ a → wt B x (x + 1) = 1) (haw : wt B m a = 1) : False := by
  have hg : ∀ t < a - e + 2, a + 1 - t < m + 1 := fun t ht => by omega
  have hq := isInducedPath_arithMap (Q := adjQ m a b) (D := fun _ => True)
    (fun i j _ _ => hA i j) (fun t => a + 1 - t) hg (fun _ _ => trivial) (by omega)
    (fun s t hs ht h => by omega) (fun s t hs ht hst => by simp only [adjQ]; omega)
  refine hq.not_isTwoFinite_of_bAffine (k := a - e + 2) (by omega) (y := Fin.last m) ?_ ?_ ?_ ?_
    hB
  · rintro ⟨t, ht⟩
    have := congrArg Fin.val ht
    simp only [arithMap_val, Fin.val_last] at this
    omega
  · intro i
    rw [hA]
    simp only [arithMap_val, Fin.val_last]
    unfold adjQ
    have := i.2
    omega
  · intro i hi
    rw [← wt_val]
    simp only [arithMap_val, Fin.val_last]
    rw [show a + 1 - (i : ℕ) = a by omega]
    exact haw
  · intro i j hij
    rw [← wt_val]
    simp only [arithMap_val]
    have := j.2
    rw [show a + 1 - (i : ℕ) = a - i + 1 by omega, show a + 1 - (j : ℕ) = a - i by omega,
      wt_comm]
    split_ifs with h
    · rw [show a - (i : ℕ) = e by omega]
      exact he2
    · exact hw1 _ (by omega) (by omega)

/-- A weight `2` on the path above the unit cycle `(a, …, b, m)` gives a subdiagram of shape
`B^{(1)}`, on `(m; b - 1, b, b + 1, …, e + 1)`. -/
private theorem false_of_bAffine_right (hB : IsTwoFinite B) {a b e : ℕ} (hab : a + 2 ≤ b)
    (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a b i j)
    (hbe : b ≤ e) (hem : e + 1 < m) (he2 : wt B e (e + 1) = 2)
    (hw1 : ∀ x, b - 1 ≤ x → x < e → wt B x (x + 1) = 1) (hbw : wt B b m = 1) : False := by
  have hg : ∀ t < e - b + 3, b - 1 + t < m + 1 := fun t ht => by omega
  have hq := isInducedPath_arithMap (Q := adjQ m a b) (D := fun _ => True)
    (fun i j _ _ => hA i j) (fun t => b - 1 + t) hg (fun _ _ => trivial) (by omega)
    (fun s t hs ht h => by omega) (fun s t hs ht hst => by simp only [adjQ]; omega)
  refine hq.not_isTwoFinite_of_bAffine (k := e - b + 3) (by omega) (y := Fin.last m) ?_ ?_ ?_ ?_
    hB
  · rintro ⟨t, ht⟩
    have := congrArg Fin.val ht
    simp only [arithMap_val, Fin.val_last] at this
    omega
  · intro i
    rw [hA]
    simp only [arithMap_val, Fin.val_last]
    unfold adjQ
    have := i.2
    omega
  · intro i hi
    rw [← wt_val]
    simp only [arithMap_val, Fin.val_last]
    rw [show b - 1 + (i : ℕ) = b by omega, wt_comm]
    exact hbw
  · intro i j hij
    rw [← wt_val]
    simp only [arithMap_val]
    have := j.2
    rw [show b - 1 + (j : ℕ) = b - 1 + i + 1 by omega]
    split_ifs with h
    · rw [show b - 1 + (i : ℕ) = e by omega]
      exact he2
    · exact hw1 _ (by omega) (by omega)

/-- A weight `2` on the path below the doubled triangle `(a, a + 1, m)` gives a subdiagram of
shape `C^{(1)}`, on `(m, a, a - 1, …, e)`. -/
private theorem false_of_cAffine_left (hB : IsTwoFinite B) {a e : ℕ} (ham : a + 1 < m)
    (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 1) i j)
    (hea : e < a) (he2 : wt B e (e + 1) = 2)
    (hw1 : ∀ x, e < x → x < a → wt B x (x + 1) = 1) (haw : wt B m a = 2) : False := by
  have hg : ∀ t < a - e + 1 + 1, (if t = 0 then m else a + 1 - t) < m + 1 := fun t ht => by
    split_ifs <;> omega
  have hq := isInducedPath_arithMap (Q := adjQ m a (a + 1)) (D := fun _ => True)
    (fun i j _ _ => hA i j) (fun t => if t = 0 then m else a + 1 - t) hg (fun _ _ => trivial)
    (by omega) (fun s t hs ht h => by split_ifs at h <;> omega)
    (fun s t hs ht hst => by simp only [adjQ]; split_ifs <;> omega)
  refine hq.not_isTwoFinite_of_cAffine (k := a - e + 1) (by omega) (fun i j hij => ?_) hB
  rw [← wt_val]
  simp only [arithMap_val]
  have := j.2
  by_cases hi0 : (i : ℕ) = 0
  · rw [if_pos hi0, if_neg (show ¬(j : ℕ) = 0 by omega), if_pos (Or.inl hi0),
      show a + 1 - (j : ℕ) = a by omega]
    exact haw
  · rw [if_neg hi0, if_neg (show ¬(j : ℕ) = 0 by omega), show a + 1 - (i : ℕ) = a - i + 1 by omega,
      show a + 1 - (j : ℕ) = a - i by omega, wt_comm]
    split_ifs with h
    · rw [show a - (i : ℕ) = e by omega]
      exact he2
    · exact hw1 _ (by omega) (by omega)

/-- A weight `2` on the path above the doubled triangle `(a, a + 1, m)` gives a subdiagram of
shape `C^{(1)}`, on `(m, a + 1, a + 2, …, e + 1)`. -/
private theorem false_of_cAffine_right (hB : IsTwoFinite B) {a e : ℕ}
    (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 1) i j)
    (hae : a + 1 ≤ e) (hem : e + 1 < m) (he2 : wt B e (e + 1) = 2)
    (hw1 : ∀ x, a < x → x < e → wt B x (x + 1) = 1) (hwa : wt B (a + 1) m = 2) : False := by
  have hg : ∀ t < e - a + 1 + 1, (if t = 0 then m else a + t) < m + 1 := fun t ht => by
    split_ifs <;> omega
  have hq := isInducedPath_arithMap (Q := adjQ m a (a + 1)) (D := fun _ => True)
    (fun i j _ _ => hA i j) (fun t => if t = 0 then m else a + t) hg (fun _ _ => trivial)
    (by omega) (fun s t hs ht h => by split_ifs at h <;> omega)
    (fun s t hs ht hst => by simp only [adjQ]; split_ifs <;> omega)
  refine hq.not_isTwoFinite_of_cAffine (k := e - a + 1) (by omega) (fun i j hij => ?_) hB
  rw [← wt_val]
  simp only [arithMap_val]
  have := j.2
  by_cases hi0 : (i : ℕ) = 0
  · rw [if_pos hi0, if_neg (show ¬(j : ℕ) = 0 by omega), if_pos (Or.inl hi0),
      show a + (j : ℕ) = a + 1 by omega, wt_comm]
    exact hwa
  · rw [if_neg hi0, if_neg (show ¬(j : ℕ) = 0 by omega), show a + (j : ℕ) = a + i + 1 by omega]
    split_ifs with h
    · rw [show a + (i : ℕ) = e by omega]
      exact he2
    · exact hw1 _ (by omega) (by omega)

/-- **A square of type `F₄` with a pendant vertex** (`m ≥ 4`): not `2`-finite. -/
private theorem false_of_square (hB : IsTwoFinite B) {a : ℕ} (ham : a + 2 < m) (hm : 4 ≤ m)
    (hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 2) i j)
    (hw : (wt B a (a + 1) = 2 ∧ wt B (a + 1) (a + 2) = 1 ∧ wt B (a + 2) m = 2 ∧
        wt B m a = 1) ∨
      (wt B a (a + 1) = 1 ∧ wt B (a + 1) (a + 2) = 2 ∧ wt B (a + 2) m = 1 ∧ wt B m a = 2)) :
    False := by
  have hg : ∀ t < 4, (if t ≤ 2 then a + t else m) < m + 1 := fun t ht => by
    split_ifs <;> omega
  have hx := isChordlessCycle_arithMap (Q := adjQ m a (a + 2)) (D := fun _ => True)
    (fun i j _ _ => hA i j) (fun t => if t ≤ 2 then a + t else m) hg (fun _ _ => trivial)
    (by norm_num) (fun s t hs ht h => by split_ifs at h <;> omega)
    (fun s t hs ht hst => by simp only [adjQ]; split_ifs <;> omega)
  have hw' : cycleWeights B (arithMap _ hg) = ![2, 1, 2, 1] ∨
      cycleWeights B (arithMap _ hg) = ![1, 2, 1, 2] := by
    rcases hw with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · exact Or.inl (funext fun k => by fin_cases k <;> simp [cycleWeights_arithMap, h0, h1, h2, h3])
    · exact Or.inr (funext fun k => by fin_cases k <;> simp [cycleWeights_arithMap, h0, h1, h2, h3])
  by_cases ha : 1 ≤ a
  · refine not_isTwoFinite_of_square_of_existsUnique_adj hx hw' (y := ⟨a - 1, by omega⟩)
      ⟨0, ?_, fun i hi => ?_⟩ hB
    · beta_reduce
      rw [hA]
      simp only [arithMap_val]
      unfold adjQ
      norm_num
      omega
    · beta_reduce at hi
      rw [hA] at hi
      simp only [arithMap_val] at hi
      unfold adjQ at hi
      have := i.2
      apply Fin.ext
      split_ifs at hi <;> simp <;> omega
  · refine not_isTwoFinite_of_square_of_existsUnique_adj hx hw' (y := ⟨a + 3, by omega⟩)
      ⟨2, ?_, fun i hi => ?_⟩ hB
    · beta_reduce
      rw [hA]
      simp only [arithMap_val]
      unfold adjQ
      norm_num
      omega
    · beta_reduce at hi
      rw [hA] at hi
      simp only [arithMap_val] at hi
      unfold adjQ at hi
      have := i.2
      apply Fin.ext
      split_ifs at hi <;> simp <;> omega

/-- **The doubled triangle on a unit path** slides to the end of the path: Dynkin class
`B_{m+1}`. -/
private theorem exists_of_doubledTriangle (hm : 2 ≤ m) (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a : ℕ}
    (ham : a + 1 < m)
    (hU : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = a + 1))
    (h1 : 0 < ent B (a + 1) m) (h2 : 0 < ent B m a)
    (hall : ∀ x, x + 1 < m → wt B x (x + 1) = 1) (hwa : wt B m a = 2)
    (hwa' : wt B (a + 1) m = 2) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  have h := isLinearlyOrientedPath_matrixMutationList_of_doubledTriangle hm hB.1
    (p := Fin.castSucc) (u := Fin.last m) (by rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi)
    hP (fun i j h => by
      rw [← wt_val, Fin.val_castSucc, Fin.val_castSucc, ← h]
      exact hall i (by omega))
    (a := ⟨a, by omega⟩) (a' := ⟨a + 1, ham⟩) rfl
    (fun i => by
      rw [hU _ (by simp)]
      simp [Fin.ext_iff])
    (h1.trans_eq (ent_val B (Fin.castSucc ⟨a + 1, ham⟩) (Fin.last m)))
    (h2.trans_eq (ent_val B (Fin.last m) (Fin.castSucc ⟨a, by omega⟩)))
    ((wt_val B _ _).symm.trans hwa) ((wt_val B _ _).symm.trans (by rw [wt_comm]; exact hwa'))
  exact ⟨_, rfl, h.2.2⟩

/-- **The square of type `F₄`** (`m = 3`): Dynkin class `F₄`. -/
private theorem exists_of_square_F₄ {B : Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℤ}
    (hB : IsTwoFinite B)
    (hA : ∀ i j : Fin (3 + 1), (diagramGraph B).Adj i j ↔ adjQ 3 0 2 i j)
    (h01 : 0 < ent B 0 1) (h12 : 0 < ent B 1 2) (h23 : 0 < ent B 2 3) (h30 : 0 < ent B 3 0)
    (hw : (wt B 0 1 = 2 ∧ wt B 1 2 = 1 ∧ wt B 2 3 = 2 ∧ wt B 3 0 = 1) ∨
      (wt B 0 1 = 1 ∧ wt B 1 2 = 2 ∧ wt B 2 3 = 1 ∧ wt B 3 0 = 2)) :
    ∃ X : DynkinSymbol, X.rank = 3 + 1 ∧ IsOfDynkinClass B [X] := by
  have hent : ∀ i j : Fin (3 + 1), B i j = ent B i j := fun i j => (ent_val B i j).symm
  have hwt : ∀ i j : Fin (3 + 1), diagramWeight B i j = wt B i j := fun i j => (wt_val B i j).symm
  rcases hw with ⟨w0, w1, w2, w3⟩ | ⟨w0, w1, w2, w3⟩
  · refine ⟨DynkinSymbol.F₄, rfl, isOfDynkinClass_F₄_of_cycleWeights_eq_two_one hB.1
      (v := Equiv.refl _) ⟨by norm_num, (Equiv.refl _).injective, fun p q hpq => ?_⟩
      (fun p => ?_) ?_⟩
    · rw [hA, Equiv.refl_apply, Equiv.refl_apply, Fin.ext_iff, Fin.ext_iff, val_finRotate_eq_ite,
        val_finRotate_eq_ite]
      have := p.2
      have := q.2
      have : (p : ℕ) ≠ q := fun h => hpq (Fin.ext h)
      unfold adjQ
      split_ifs <;> omega
    · rw [hent, Equiv.refl_apply, Equiv.refl_apply, val_finRotate_eq_ite]
      fin_cases p <;> simpa
    · funext p
      rw [cycleWeights, hwt, Equiv.refl_apply, Equiv.refl_apply, val_finRotate_eq_ite]
      fin_cases p <;> simpa
  · refine ⟨DynkinSymbol.F₄, rfl, isOfDynkinClass_F₄_of_cycleWeights_eq_two_one hB.1
      (v := finRotate _) ⟨by norm_num, (finRotate _).injective, fun p q hpq => ?_⟩
      (fun p => ?_) ?_⟩
    · rw [hA, Fin.ext_iff, Fin.ext_iff]
      simp only [val_finRotate_eq_ite]
      unfold adjQ
      fin_cases p <;> fin_cases q <;> simp at hpq ⊢
    · rw [hent]
      simp only [val_finRotate_eq_ite]
      fin_cases p <;> simpa
    · funext p
      rw [cycleWeights, hwt]
      simp only [val_finRotate_eq_ite]
      fin_cases p <;> simp [w0, w1, w2, w3]

/-- The edges of the path have positive weight. -/
private theorem one_le_wt_succ (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1)))
    {x : ℕ} (hx : x + 1 < m) : 1 ≤ wt B x (x + 1) := by
  have h := ((path_adj hP ⟨x, by omega⟩ ⟨x + 1, by omega⟩ (by simp; omega)
    (by simp; omega)).2 (Or.inl rfl)).2
  have := wt_val B ⟨x, by omega⟩ ⟨x + 1, by omega⟩
  simp only at this
  omega

private theorem wt_le_three (hB : IsTwoFinite B) (x y : ℕ) : wt B x y ≤ 3 := by
  unfold wt
  split_ifs
  · exact hB.diagramWeight_le_three _ _
  · omega

/-- **The extra vertex on a unit cycle `(a, …, b, m)`**: a triangle or a crown, of Dynkin class,
unless a weight `2` on the path gives a subdiagram of shape `B^{(1)}`. -/
private theorem exists_of_unit_cycle (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a b : ℕ}
    (hab : a < b) (hbm : b < m)
    (hU : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = b))
    (hbU : 0 < ent B b m) (hUa : 0 < ent B m a)
    (hcyc : ∀ x, a ≤ x → x < b → wt B x (x + 1) = 1) (hbw : wt B b m = 1) (haw : wt B m a = 1) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  classical
  have hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a b i j := fun i j =>
    adj_iff_adjQ hP (by omega) hbm (D := fun _ => True) (fun j _ hj => hU j hj) i j trivial
      trivial
  by_cases hb1 : b = a + 1
  · subst hb1
    exact exists_of_triangle hB hP hbm hU hbU hUa (by rw [hcyc a le_rfl (by omega), hbw, haw])
  by_cases hall : ∀ x, x + 1 < m → wt B x (x + 1) = 1
  · exact exists_of_crown hB hP (by omega) hbm hU hbU hUa hall hbw haw
  exfalso
  push Not at hall
  obtain ⟨x, hx, hx1⟩ := hall
  by_cases hl : ∃ e < a, wt B e (e + 1) ≠ 1
  · obtain ⟨e, hea, he1, hmax⟩ := exists_greatest_lt hl
    have := one_le_wt_succ hP (x := e) (by omega)
    have := wt_le_three hB e (e + 1)
    have := (path_weight_ne_three hB hP (x := e) (by omega)).1
    refine false_of_bAffine_left hB (by omega) hbm hA hea (by omega) (fun y hy hya => ?_) haw
    rcases (show y < a ∨ y = a by omega) with h | rfl
    · by_contra h'
      exact hmax y hy h h'
    · exact hcyc _ le_rfl (by omega)
  push Not at hl
  have hxb : b ≤ x := by
    by_contra h
    rcases (show x < a ∨ a ≤ x by omega) with h' | h'
    · exact hx1 (hl x h')
    · exact hx1 (hcyc x h' (by omega))
  have hex : ∃ e, b ≤ e ∧ e + 1 < m ∧ wt B e (e + 1) ≠ 1 := ⟨x, hxb, hx, hx1⟩
  obtain ⟨e, ⟨hbe, hem, he1⟩, hmin⟩ : ∃ e, (b ≤ e ∧ e + 1 < m ∧ wt B e (e + 1) ≠ 1) ∧
      ∀ y < e, ¬(b ≤ y ∧ y + 1 < m ∧ wt B y (y + 1) ≠ 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun y hy => Nat.find_min hex hy⟩
  have := one_le_wt_succ hP hem
  have := wt_le_three hB e (e + 1)
  have h3 := (path_weight_ne_three hB hP (x := e - 1) (by omega)).2
  rw [show e - 1 + 1 = e by omega, show e - 1 + 2 = e + 1 by omega] at h3
  refine false_of_bAffine_right hB (by omega) hA hbe hem (by omega) (fun y hy hye => ?_) hbw
  rcases (show y < b ∨ b ≤ y by omega) with h | h
  · exact hcyc y (by omega) h
  · by_contra h'
    exact hmin y hye ⟨h, by omega, h'⟩

/-- **The extra vertex on a triangle `(a, a + 1, m)` with a weight `2`**: a triangle or a doubled
triangle, of Dynkin class, unless a weight `2` on the path gives a subdiagram of shape
`C^{(1)}`. -/
private theorem exists_of_triangle_two (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a : ℕ}
    (ham : a + 1 < m)
    (hU : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = a + 1))
    (hbU : 0 < ent B (a + 1) m) (hUa : 0 < ent B m a)
    (hw : (wt B a (a + 1) = 2 ∧ wt B (a + 1) m = 2 ∧ wt B m a = 1) ∨
      (wt B a (a + 1) = 2 ∧ wt B (a + 1) m = 1 ∧ wt B m a = 2) ∨
      (wt B a (a + 1) = 1 ∧ wt B (a + 1) m = 2 ∧ wt B m a = 2)) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  classical
  have hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 1) i j := fun i j =>
    adj_iff_adjQ hP (by omega) ham (D := fun _ => True) (fun j _ hj => hU j hj) i j trivial
      trivial
  rcases hw with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact exists_of_triangle hB hP ham hU hbU hUa (by rw [h1, h2, h3])
  · exact exists_of_triangle hB hP ham hU hbU hUa (by rw [h1, h2, h3])
  by_cases hall : ∀ x, x + 1 < m → wt B x (x + 1) = 1
  · exact exists_of_doubledTriangle (by omega) hB hP ham hU hbU hUa hall h3 h2
  exfalso
  push Not at hall
  obtain ⟨x, hx, hx1⟩ := hall
  by_cases hl : ∃ e < a, wt B e (e + 1) ≠ 1
  · obtain ⟨e, hea, he1, hmax⟩ := exists_greatest_lt hl
    have := one_le_wt_succ hP (x := e) (by omega)
    have := wt_le_three hB e (e + 1)
    have := (path_weight_ne_three hB hP (x := e) (by omega)).1
    exact false_of_cAffine_left hB ham hA hea (by omega)
      (fun y hy hya => by_contra fun h' => hmax y hy hya h') h3
  push Not at hl
  have hxa : a + 1 ≤ x := by
    by_contra h
    rcases (show x < a ∨ x = a by omega) with h' | rfl
    · exact hx1 (hl x h')
    · exact hx1 h1
  have hex : ∃ e, a + 1 ≤ e ∧ e + 1 < m ∧ wt B e (e + 1) ≠ 1 := ⟨x, hxa, hx, hx1⟩
  obtain ⟨e, ⟨hae, hem, he1⟩, hmin⟩ : ∃ e, (a + 1 ≤ e ∧ e + 1 < m ∧ wt B e (e + 1) ≠ 1) ∧
      ∀ y < e, ¬(a + 1 ≤ y ∧ y + 1 < m ∧ wt B y (y + 1) ≠ 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun y hy => Nat.find_min hex hy⟩
  have := one_le_wt_succ hP hem
  have := wt_le_three hB e (e + 1)
  have h4 := (path_weight_ne_three hB hP (x := e - 1) (by omega)).2
  rw [show e - 1 + 1 = e by omega, show e - 1 + 2 = e + 1 by omega] at h4
  exact false_of_cAffine_right hB hA hae hem (by omega)
    (fun y hy hye => by_contra fun h' => hmin y hye ⟨by omega, by omega, h'⟩) h2

/-- **The extra vertex adjacent to two vertices of the path.** -/
private theorem exists_of_adj_eq_pair (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a b : ℕ}
    (hab : a < b) (hbm : b < m)
    (hU : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ (j : ℕ) = a ∨ (j : ℕ) = b)) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  obtain ⟨hbU, hUa, hw⟩ := cycle_facts hB hP hab hbm (fun j _ hj => hU j (by omega))
  rcases hw with ⟨hcyc, hbw, haw⟩ | ⟨rfl, hw⟩ | ⟨rfl, hw⟩
  · exact exists_of_unit_cycle hB hP hab hbm hU hbU hUa hcyc hbw haw
  · exact exists_of_triangle_two hB hP hbm hU hbU hUa hw
  have hA : ∀ i j : Fin (m + 1), (diagramGraph B).Adj i j ↔ adjQ m a (a + 2) i j := fun i j =>
    adj_iff_adjQ hP (by omega) hbm (D := fun _ => True) (fun j _ hj => hU j hj) i j trivial
      trivial
  rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | h4
  · obtain rfl : a = 0 := by omega
    exact exists_of_square_F₄ hB hA (path_arrow hP 0 (by omega)) (path_arrow hP 1 (by omega))
      hbU hUa hw
  · exact (false_of_square hB hbm h4 hA hw).elim

/-- The extra vertex has at most two neighbours on the path: neighbours `a < b < c` with none
in between give two cycles forcing opposite arrows between `b` and `m`. -/
private theorem false_of_adj_three (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1))) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) (hcm : c < m) (hwa : 0 < wt B m a) (hwb : 0 < wt B m b)
    (hwc : 0 < wt B m c) (hbmin : ∀ y < b, ¬(a < y ∧ y < m ∧ 0 < wt B m y))
    (hcmin : ∀ y < c, ¬(b < y ∧ y < m ∧ 0 < wt B m y))
    (hUw : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ 0 < wt B m j)) : False := by
  have f1 := (cycle_facts hB hP hab (by omega) (fun j hj1 hj2 => by
    rw [hUw j (by omega)]
    constructor
    · intro h
      by_contra h'
      exact hbmin j (by omega) ⟨by omega, by omega, h⟩
    · rintro (h | h) <;> rw [h] <;> assumption)).1
  have f2 := (cycle_facts hB hP hbc hcm (fun j hj1 hj2 => by
    rw [hUw j (by omega)]
    constructor
    · intro h
      by_contra h'
      exact hcmin j (by omega) ⟨by omega, by omega, h⟩
    · rintro (h | h) <;> rw [h] <;> assumption)).2.1
  exact ent_pos_asymm hB.1 f1 f2

/-- A `2`-finite diagram on `m + 1` vertices in which `0, 1, …, m - 1` is a linearly oriented
path and `m` is adjacent to some vertex of the path is of Dynkin class of rank `m + 1`. -/
private theorem exists_isOfDynkinClass_of_castSucc (hB : IsTwoFinite B)
    (hP : IsLinearlyOrientedPath B (Fin.castSucc : Fin m → Fin (m + 1)))
    (hK : ∃ x, x < m ∧ 0 < wt B m x) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  classical
  have hUw : ∀ j : Fin (m + 1), (j : ℕ) < m →
      ((diagramGraph B).Adj (Fin.last m) j ↔ 0 < wt B m j) := by
    intro j hj
    rw [diagramGraph_adj, ← wt_val, Fin.val_last]
    exact ⟨fun h => h.2, fun h => ⟨fun h' => by rw [← h'] at hj; simp at hj, h⟩⟩
  obtain ⟨a, ⟨ham, hwa⟩, hamin⟩ : ∃ a, (a < m ∧ 0 < wt B m a) ∧
      ∀ y < a, ¬(y < m ∧ 0 < wt B m y) :=
    ⟨Nat.find hK, Nat.find_spec hK, fun y hy => Nat.find_min hK hy⟩
  by_cases h2 : ∃ x, a < x ∧ x < m ∧ 0 < wt B m x
  · obtain ⟨b, ⟨hab, hbm, hwb⟩, hbmin⟩ : ∃ b, (a < b ∧ b < m ∧ 0 < wt B m b) ∧
        ∀ y < b, ¬(a < y ∧ y < m ∧ 0 < wt B m y) :=
      ⟨Nat.find h2, Nat.find_spec h2, fun y hy => Nat.find_min h2 hy⟩
    by_cases h3 : ∃ x, b < x ∧ x < m ∧ 0 < wt B m x
    · obtain ⟨c, ⟨hbc, hcm, hwc⟩, hcmin⟩ : ∃ c, (b < c ∧ c < m ∧ 0 < wt B m c) ∧
          ∀ y < c, ¬(b < y ∧ y < m ∧ 0 < wt B m y) :=
        ⟨Nat.find h3, Nat.find_spec h3, fun y hy => Nat.find_min h3 hy⟩
      exact (false_of_adj_three hB hP hab hbc hcm hwa hwb hwc hbmin hcmin hUw).elim
    · refine exists_of_adj_eq_pair hB hP hab hbm (fun j hj => ?_)
      rw [hUw j hj]
      constructor
      · intro h
        by_contra h'
        rcases (show (j : ℕ) < a ∨ (a < j ∧ (j : ℕ) < b) ∨ b < j by omega) with h'' | h'' | h''
        · exact hamin j h'' ⟨hj, h⟩
        · exact hbmin j h''.2 ⟨h''.1, hj, h⟩
        · exact h3 ⟨j, h'', hj, h⟩
      · rintro (h | h) <;> rw [h] <;> assumption
  · refine exists_of_adj_eq_single hB hP ham (fun j hj => ?_)
    rw [hUw j hj]
    constructor
    · intro h
      by_contra h'
      rcases (show (j : ℕ) < a ∨ a < j by omega) with h'' | h''
      · exact hamin j h'' ⟨hj, h⟩
      · exact h2 ⟨j, h'', hj, h⟩
    · intro h
      rwa [h]

end Normalized

/-! ### The main results -/

/-- **A linearly oriented path with one more vertex.** Let `m ≥ 1` and let `B` be a `2`-finite
connected `(m + 1) × (m + 1)` matrix with an enumeration `p₁, …, p_m, u` of its indices such
that `(p₁, …, p_m)` is a linearly oriented induced path. Then `B` is of Dynkin class `X` for a
Dynkin symbol `X` of rank `m + 1`. -/
@[cluster_algebras "lem_path_plus_vertex"]
theorem IsLinearlyOrientedPath.exists_isOfDynkinClass {m : ℕ} (hm : 1 ≤ m)
    {B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ} (hB : IsTwoFinite B) (hc : IsConnectedDiagram B)
    {p : Fin m → Fin (m + 1)} {u : Fin (m + 1)} (hu : u ∉ Set.range p)
    (hp : IsLinearlyOrientedPath B p) :
    ∃ X : DynkinSymbol, X.rank = m + 1 ∧ IsOfDynkinClass B [X] := by
  classical
  have hS := hB.1
  have hinj : Function.Injective (Fin.snoc (α := fun _ => Fin (m + 1)) p u) :=
    Fin.snoc_injective_of_injective hp.1.2.1 hu
  let σ : Equiv.Perm (Fin (m + 1)) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσc : ∀ i : Fin m, σ (Fin.castSucc i) = p i := fun i => by simp [σ]
  have hσl : σ (Fin.last m) = u := by simp [σ]
  have hB' : IsTwoFinite (B.submatrix σ σ) := hB.submatrix σ.toEmbedding
  have hadj' : ∀ i j, (diagramGraph (B.submatrix σ σ)).Adj i j ↔
      (diagramGraph B).Adj (σ i) (σ j) := fun i j => by
    rw [diagramGraph_adj, diagramGraph_adj]
    exact and_congr σ.injective.ne_iff.symm Iff.rfl
  have hP' : IsLinearlyOrientedPath (B.submatrix σ σ) (Fin.castSucc : Fin m → Fin (m + 1)) := by
    refine ⟨⟨hm, Fin.castSucc_injective m, fun i j hij => ?_⟩, fun i j hij => ?_⟩
    · rw [hadj', hσc, hσc]
      exact hp.1.2.2 i j hij
    · simp only [submatrix_apply, hσc]
      exact hp.2 i j hij
  have hK : ∃ x, x < m ∧ 0 < wt (B.submatrix σ σ) m x := by
    by_contra hno
    push Not at hno
    have hzero : ∀ j, j ∉ ({u} : Finset (Fin (m + 1))) → B u j = 0 := by
      intro j hj
      rw [Finset.mem_singleton] at hj
      obtain ⟨k, rfl⟩ := σ.surjective j
      have hk : (k : ℕ) < m := by
        have := k.2
        have : (k : ℕ) ≠ m := fun h => hj (by rw [show k = Fin.last m from Fin.ext h, hσl])
        omega
      have h0 := hno k hk
      have hw := wt_val (B.submatrix σ σ) (Fin.last m) k
      rw [Fin.val_last] at hw
      have h0' : diagramWeight B u (σ k) = 0 := by
        rw [← hσl]
        change diagramWeight (B.submatrix σ σ) (Fin.last m) k = 0
        omega
      by_contra hne
      have := (hS.diagramWeight_pos_iff u (σ k)).2 hne
      omega
    refine (hS.isConnectedDiagram_iff.1 hc) ⟨{u}, by simp, ⟨p ⟨0, hm⟩, ?_⟩,
      fun i hi j hj => ?_⟩
    · simp only [Finset.mem_compl, Finset.mem_singleton]
      exact fun h => hu ⟨_, h⟩
    · rw [Finset.mem_singleton] at hi
      subst hi
      exact hzero j hj
  obtain ⟨X, hX, hX'⟩ := exists_isOfDynkinClass_of_castSucc hB' hP' hK
  exact ⟨X, hX, hX'.of_diagramEquiv hS (skewSymmetrizable_submatrix hS σ)
    (mutationEquiv_submatrix B σ).diagramEquiv⟩

/-- An induced path through all indices is a tree diagram: each vertex of the path but the first
has exactly one earlier neighbour. -/
private theorem IsInducedPath.isTreeDiagram {M : ℕ} {C : Matrix (Fin M) (Fin M) ℤ}
    {v : Fin M ≃ Fin M} (hv : IsInducedPath C v) : IsTreeDiagram C := by
  have hM := hv.1
  refine isTree_of_existsUnique_lt_adj (fun i => (v.symm i : ℕ))
    (fun i j h => v.symm.injective (Fin.ext h)) (v ⟨0, by omega⟩) (fun w hw => ?_)
    (fun x hx => ?_)
  · simp only [Equiv.symm_apply_apply]
    have hne : v.symm w ≠ ⟨0, by omega⟩ := fun h' => hw.ne (by rw [← h']; simp)
    exact Nat.pos_of_ne_zero (fun h' => hne (Fin.ext h'))
  · obtain ⟨t, rfl⟩ := v.surjective x
    have ht : (t : ℕ) ≠ 0 := fun h' => hx (congrArg v (Fin.ext h'))
    refine ⟨v ⟨t - 1, by omega⟩, ⟨by simp; omega, ?_⟩, fun w hw => ?_⟩
    · refine (hv.2.2 _ _ (fun h' => ?_)).2 (Or.inl (by simp; omega))
      have := congrArg Fin.val h'
      simp at this
      omega
    · obtain ⟨s, rfl⟩ := v.surjective w
      simp only [Equiv.symm_apply_apply] at hw
      have hst : s ≠ t := fun h' => by subst h'; exact lt_irrefl _ hw.1
      have := (hv.2.2 s t hst).1 hw.2
      have hlt : (s : ℕ) < t := hw.1
      congr 1
      apply Fin.ext
      simp only
      omega

/-- A diagram with an induced path through all indices is mutation equivalent to a linearly
oriented path along the same enumeration. -/
private theorem exists_isLinearlyOrientedPath_matrixMutationList {M : ℕ}
    {C : Matrix (Fin M) (Fin M) ℤ} (hC : SkewSymmetrizable C) {v : Fin M ≃ Fin M}
    (hv : IsInducedPath C v) : ∃ t, IsLinearlyOrientedPath (matrixMutationList le_rfl C t) v := by
  classical
  have hadjQ : ∀ i j, (diagramGraph C).Adj i j →
      (if (v.symm i : ℕ) + 1 = v.symm j then 1 else 0) +
        (if (v.symm j : ℕ) + 1 = v.symm i then 1 else 0) = 1 := by
    intro i j hij
    obtain ⟨s, rfl⟩ := v.surjective i
    obtain ⟨t, rfl⟩ := v.surjective j
    have hst : s ≠ t := fun h' => hij.ne (by rw [h'])
    have := (hv.2.2 s t hst).1 hij
    simp only [Equiv.symm_apply_apply]
    split_ifs <;> omega
  have hneQ : ∀ i j, i ≠ j → ¬(diagramGraph C).Adj i j →
      (if (v.symm i : ℕ) + 1 = v.symm j then 1 else 0) = 0 := by
    intro i j hij hn
    obtain ⟨s, rfl⟩ := v.surjective i
    obtain ⟨t, rfl⟩ := v.surjective j
    have hst : s ≠ t := fun h' => hij (by rw [h'])
    simp only [Equiv.symm_apply_apply]
    rw [if_neg]
    exact fun h' => hn ((hv.2.2 s t hst).2 (Or.inl h'))
  obtain ⟨Q, hQa, -, hQ⟩ := orientation_of_arrow_counts (diagramGraph C)
    (fun i j => if (v.symm i : ℕ) + 1 = v.symm j then 1 else 0) (fun i => by simp) hadjQ hneQ
  obtain ⟨t, htw, hta⟩ := hv.isTreeDiagram.exists_matrixMutationList_arrows hC hQ
  refine ⟨t, ⟨hv.1, v.injective, fun s s' hss' => ?_⟩, fun s s' hss' => ?_⟩
  · rw [diagramGraph_adj, htw, ← diagramGraph_adj]
    exact hv.2.2 s s' hss'
  · rw [hta, hQa]
    simp [hss']

/-- **A diagram of path type with one more vertex.** Let `B` be a `2`-finite connected
`(M + 1) × (M + 1)` matrix, `M ≥ 1`, let `r` enumerate the indices other than `u`, and let `C`
be a path diagram with `B^r ∼ C`. Then `B` is of Dynkin class `X` for a Dynkin symbol `X` of
rank `M + 1`. -/
@[cluster_algebras "lem_path_type_plus_vertex"]
theorem exists_isOfDynkinClass_of_diagramEquiv_isPathDiagram {M : ℕ} (hM : 1 ≤ M)
    {B : Matrix (Fin (M + 1)) (Fin (M + 1)) ℤ} (hB : IsTwoFinite B) (hc : IsConnectedDiagram B)
    {u : Fin (M + 1)} {r : Fin M ↪ Fin (M + 1)} (hr : Set.range r = {u}ᶜ)
    {C : Matrix (Fin M) (Fin M) ℤ} (hC : SkewSymmetrizable C) (hCp : IsPathDiagram C)
    (h : DiagramEquiv (B.submatrix r r) C) :
    ∃ X : DynkinSymbol, X.rank = M + 1 ∧ IsOfDynkinClass B [X] := by
  classical
  have hS := hB.1
  obtain ⟨v, hv⟩ := hCp
  obtain ⟨t, hv'⟩ := exists_isLinearlyOrientedPath_matrixMutationList hC hv
  have hC' := skewSymmetrizable_matrixMutationList hC t
  have hBr := skewSymmetrizable_submatrix hS r
  have h' : DiagramEquiv (B.submatrix r r) (matrixMutationList le_rfl C t) :=
    h.trans hBr hC (mutationEquiv_matrixMutationList C t).diagramEquiv
  obtain ⟨s, π, -, hmut, hrange, hdiag⟩ := DiagramEquiv.exists_submatrix r h'
  have hB2 : IsTwoFinite (matrixMutationList le_rfl B s) := hB.matrixMutationList s
  obtain ⟨hw, harr⟩ := ((skewSymmetrizable_submatrix hB2.1 (r ∘ π)).diagram_eq_iff hC').1 hdiag
  have hinj : Function.Injective (r ∘ π ∘ v) :=
    (r.injective.comp π.injective).comp v.injective
  have hp : IsLinearlyOrientedPath (matrixMutationList le_rfl B s) (r ∘ π ∘ v) := by
    refine ⟨⟨hM, hinj, fun x y hxy => ?_⟩, fun x y hxy => ?_⟩
    · rw [← hv'.1.2.2 x y hxy, diagramGraph_adj, diagramGraph_adj, ← hw]
      exact and_congr ⟨fun _ => v.injective.ne hxy, fun _ => hinj.ne hxy⟩ Iff.rfl
    · exact (harr (v x) (v y)).2 (hv'.2 x y hxy)
  have hu : u ∉ Set.range (r ∘ π ∘ v) := by
    rintro ⟨x, hx⟩
    have : u ∈ Set.range r := ⟨π (v x), hx⟩
    rw [hr] at this
    exact this rfl
  obtain ⟨X, hX, hX'⟩ := hp.exists_isOfDynkinClass hM hB2
    (isConnectedDiagram_matrixMutationList hS hc s) hu
  exact ⟨X, hX, hX'.of_diagramEquiv hS hB2.1 hmut.diagramEquiv⟩

end ClusterAlgebras
