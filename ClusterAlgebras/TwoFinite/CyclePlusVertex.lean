/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.PathPlusVertex

/-!
# A cycle, or a diagram of type `D`, with one more vertex

We show that a `2`-finite connected matrix obtained by adding one vertex to an oriented unit
cycle of length at least `4`, or to a diagram mutation equivalent to one of Dynkin shape `D_M`,
is of Dynkin class `X` for a Dynkin symbol `X` of rank one more. The oriented unit `M`-cycle
represents the mutation class of `D_M`.

## Main results

* `ClusterAlgebras.IsOrientedUnitCycle.exists_isOfDynkinClass`: a `2`-finite connected matrix
  consisting of an oriented unit `L`-cycle, `L ≥ 4`, and one more vertex is of Dynkin class `X`
  for a Dynkin symbol `X` of rank `L + 1`.
* `ClusterAlgebras.exists_isOfDynkinClass_of_diagramEquiv_hasDynkinShape_D`: a `2`-finite
  connected matrix whose restriction away from one vertex is mutation equivalent to a matrix of
  Dynkin shape `D_M` is of Dynkin class `X` for a Dynkin symbol `X` of rank `M + 1`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n : ℕ}

/-- The weights of an oriented unit cycle, read on positions. -/
private theorem IsOrientedUnitCycle.diagramWeight_eq_cpv {B : Matrix (Fin n) (Fin n) ℤ}
    {L : ℕ} {c : Fin L → Fin n} (hv : IsOrientedUnitCycle B c) {p q : Fin L} (hpq : p ≠ q) :
    diagramWeight B (c p) (c q) = if (q : ℕ) = p + 1 ∨ (p : ℕ) = q + 1 ∨
      ((p : ℕ) = 0 ∧ (q : ℕ) + 1 = L) ∨ ((q : ℕ) = 0 ∧ (p : ℕ) + 1 = L) then 1 else 0 := by
  have hadj := hv.1.2.2 p q hpq
  rw [diagramGraph_adj] at hadj
  have hiff : (q = finRotate L p ∨ p = finRotate L q) ↔ ((q : ℕ) = p + 1 ∨ (p : ℕ) = q + 1 ∨
      ((p : ℕ) = 0 ∧ (q : ℕ) + 1 = L) ∨ ((q : ℕ) = 0 ∧ (p : ℕ) + 1 = L)) := by
    have := p.isLt
    have := q.isLt
    simp only [Fin.ext_iff, val_finRotate_eq_ite]
    split_ifs <;> omega
  rw [← if_congr hiff rfl rfl]
  split_ifs with h
  · rcases h with rfl | rfl
    · exact (hv.2 p).2
    · rw [diagramWeight_comm]
      exact (hv.2 q).2
  · by_contra h'
    exact h (hadj.1 ⟨hv.1.2.1.ne hpq, Nat.pos_of_ne_zero h'⟩)

/-- The arrows `c_p → c_{p+1}` of an oriented unit cycle, read on positions. -/
private theorem IsOrientedUnitCycle.pos_cpv {B : Matrix (Fin n) (Fin n) ℤ}
    {L : ℕ} {c : Fin L → Fin n} (hv : IsOrientedUnitCycle B c) {p q : Fin L}
    (hpq : (q : ℕ) = if (p : ℕ) + 1 = L then 0 else (p : ℕ) + 1) : 0 < B (c p) (c q) := by
  obtain rfl : q = finRotate L p := Fin.ext (by rw [val_finRotate_eq_ite, hpq])
  exact (hv.2 p).1

/-- A model weight is symmetric in its two positions. -/
private theorem orderedModel_comm_cpv (f : ℕ → ℕ → ℕ) {M : ℕ} {p q : Fin M} (h : p ≠ q) :
    orderedModel f p q = orderedModel f q p := by
  unfold orderedModel
  have := Fin.val_ne_of_ne h
  split_ifs <;> first | rfl | omega

/-- The weights of the crown `S^{L-3}_{1,2,1}` on two positions of its cycle. -/
private theorem orderedModel_crownModel_cpv {L : ℕ} (hL : 4 ≤ L) {x y : Fin (1 + 2 + 1 + (L - 3))}
    (hx : (x : ℕ) < L) (hy : (y : ℕ) < L) (hxy : (x : ℕ) ≠ y) :
    orderedModel (crownModel (L - 3) 1 2 1) x y = if (y : ℕ) = x + 1 ∨ (x : ℕ) = y + 1 ∨
      ((x : ℕ) = 0 ∧ (y : ℕ) + 1 = L) ∨ ((y : ℕ) = 0 ∧ (x : ℕ) + 1 = L) then 1 else 0 := by
  unfold orderedModel crownModel
  dsimp only
  split_ifs <;> omega

/-- The weights of the crown `S^{L-3}_{1,2,1}` between its branch vertex and its cycle. -/
private theorem orderedModel_crownModel_cpv' {L : ℕ} (hL : 4 ≤ L)
    {x y : Fin (1 + 2 + 1 + (L - 3))} (hx : (x : ℕ) < L) (hy : L ≤ (y : ℕ)) :
    orderedModel (crownModel (L - 3) 1 2 1) x y = if (x : ℕ) = 1 then 1 else 0 := by
  have := y.isLt
  unfold orderedModel crownModel
  dsimp only
  split_ifs <;> omega

/-- The rotation `x ↦ x + s` of `[0, L)`. -/
private theorem exists_rotation_cpv {L : ℕ} (s : Fin L) :
    ∃ ρ : Fin L → Fin L, ∀ (x : ℕ) (hx : x < L), (x + s < L ∧ (ρ ⟨x, hx⟩ : ℕ) = x + s) ∨
      (L ≤ x + s ∧ (ρ ⟨x, hx⟩ : ℕ) + L = x + s) :=
  ⟨fun x => ⟨if (x : ℕ) + s < L then (x : ℕ) + s else (x : ℕ) + s - L,
    by grind⟩, fun x hx => by grind⟩

/-- An oriented unit cycle `c₁, …, c_L` together with a vertex `u` joined by a single edge of
weight `1` to `c_j` is a crown `S^{L-3}_{1,2,1}`, with cycle `c_{j-1}, c_j, …, c_{j-2}`. -/
private theorem isCrownShape_cpv {L : ℕ} (hL : 4 ≤ L) {B : Matrix (Fin (L + 1)) (Fin (L + 1)) ℤ}
    {c : Fin L → Fin (L + 1)} {u : Fin (L + 1)} (hcyc : IsOrientedUnitCycle B c)
    (hcu : ∀ i, c i ≠ u) {j jm : Fin L}
    (hjm' : ((j : ℕ) = 0 ∧ (jm : ℕ) = L - 1) ∨ ((j : ℕ) ≠ 0 ∧ (jm : ℕ) + 1 = j))
    (hw : diagramWeight B u (c j) = 1) (hwu : ∀ i, i ≠ j → diagramWeight B u (c i) = 0) :
    IsCrownShape B (L - 3) 1 2 1 := by
  have hjmL := jm.isLt
  obtain ⟨ρ, hρ'⟩ := exists_rotation_cpv jm
  let f : Fin (1 + 2 + 1 + (L - 3)) → Fin (L + 1) := fun x =>
    if h : (x : ℕ) < L then c (ρ ⟨x, h⟩) else u
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hxL := x.isLt
    have hyL := y.isLt
    simp only [f] at hxy
    split_ifs at hxy with hx hy hy
    · have h1 := hρ' x hx
      have h2 := hρ' y hy
      have := congrArg Fin.val (hcyc.1.2.1 hxy)
      exact Fin.ext (by omega)
    · exact absurd hxy (hcu _)
    · exact absurd hxy.symm (hcu _)
    · exact Fin.ext (by omega)
  have hbr : ∀ (x : ℕ) (hx : x < L),
      diagramWeight B u (c (ρ ⟨x, hx⟩)) = if x = 1 then 1 else 0 := by
    intro x hx
    have h1 := hρ' x hx
    by_cases hρj : ρ ⟨x, hx⟩ = j
    · have := congrArg Fin.val hρj
      rw [hρj, hw, if_pos (by omega)]
    · have := Fin.val_ne_of_ne hρj
      rw [hwu _ hρj, if_neg (by omega)]
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, by simp only [Fintype.card_fin]; omega⟩
  refine ⟨le_rfl, by norm_num, le_rfl, Equiv.ofBijective f hfbij, fun x y hxy => ?_,
    fun x y h => ?_⟩
  · simp only [Equiv.ofBijective_apply, f]
    have hxL := x.isLt
    have hyL := y.isLt
    have hxy' : (x : ℕ) ≠ y := Fin.val_ne_of_ne hxy
    split_ifs with hx hy hy
    · have h1 := hρ' x hx
      have h2 := hρ' y hy
      rw [hcyc.diagramWeight_eq_cpv (fun h => hxy' (by have := congrArg Fin.val h; omega)),
        orderedModel_crownModel_cpv hL hx hy hxy']
      exact if_congr (by omega) rfl rfl
    · rw [diagramWeight_comm, orderedModel_crownModel_cpv' hL hx (by omega), hbr]
    · rw [orderedModel_comm_cpv _ hxy, orderedModel_crownModel_cpv' hL hy (by omega), hbr]
    · omega
  · simp only [Equiv.ofBijective_apply, f]
    obtain ⟨hx, hy⟩ : (x : ℕ) < L ∧ (y : ℕ) < L := by omega
    rw [dif_pos hx, dif_pos hy]
    apply hcyc.pos_cpv
    have h1 := hρ' x hx
    have h2 := hρ' y hy
    split_ifs <;> omega

/-- A matrix of Dynkin shape `D_M` is of shape `T_{1,1,M-3}`. -/
private theorem HasDynkinShape.isTShape_D_cpv {M : ℕ} {hM : 4 ≤ M}
    {C : Matrix (Fin M) (Fin M) ℤ} (hC : HasDynkinShape C [DynkinSymbol.D M hM]) :
    IsTShape (diagramWeight C) 1 1 (M - 3) := by
  obtain ⟨σ, -, hσ⟩ := hC
  obtain ⟨e, he⟩ := isTShape_dynkinWeightedGraph_D hM
  refine ⟨e.trans σ, fun p q hpq => ?_⟩
  rw [← he p q hpq, ← hσ]
  rfl

/-- Two matrices of Dynkin shape `D_M` have mutation equivalent diagrams. -/
private theorem diagramEquiv_of_hasDynkinShape_D_cpv {M : ℕ} {hM : 4 ≤ M}
    {C C' : Matrix (Fin M) (Fin M) ℤ} (hC : HasDynkinShape C [DynkinSymbol.D M hM])
    (hC' : HasDynkinShape C' [DynkinSymbol.D M hM]) : DiagramEquiv C C' := by
  have hT := IsTShape.isTreeDiagram hC.isTShape_D_cpv
  have hCs := hC.skewSymmetrizable
  have hC's := hC'.skewSymmetrizable
  obtain ⟨σ₁, -, h₁⟩ := hC
  obtain ⟨σ₂, -, h₂⟩ := hC'
  refine (hT.diagramEquiv_of_diagramWeight_eq hCs hC's (σ := σ₂.symm.trans σ₁)
    fun i j => ?_).1
  have e1 := h₁ (σ₂.symm i) (σ₂.symm j)
  have e2 := h₂ (σ₂.symm i) (σ₂.symm j)
  change diagramWeight C (σ₁ _) (σ₁ _) = _ at e1
  change diagramWeight C' (σ₂ _) (σ₂ _) = _ at e2
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at e2
  rw [Equiv.trans_apply, Equiv.trans_apply, e2, e1]

/-- The oriented unit `M`-cycle: the arrows `i → i + 1`, indices modulo `M`, of weight `1`. -/
private def unitCycleMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℤ :=
  of fun i j => if j = finRotate M i then 1 else if i = finRotate M j then -1 else 0

private theorem ne_finRotate_of_eq_finRotate {M : ℕ} (hM : 3 ≤ M) {i j : Fin M}
    (h : j = finRotate M i) : i ≠ finRotate M j :=
  fun h' => finRotate_finRotate_ne_self hM i (by rw [← h, ← h'])

/-- The oriented unit `M`-cycle is skew-symmetric, hence skew-symmetrizable. -/
private theorem skewSymmetrizable_unitCycleMatrix {M : ℕ} (hM : 3 ≤ M) :
    SkewSymmetrizable (unitCycleMatrix M) := by
  refine ⟨fun _ => 1, fun _ => one_pos, fun i j => ?_⟩
  simp only [unitCycleMatrix, of_apply, Int.cast_one, one_mul]
  by_cases h1 : j = finRotate M i
  · have h2 := ne_finRotate_of_eq_finRotate hM h1
    simp only [if_pos h1, if_neg h2, neg_neg]
  · by_cases h2 : i = finRotate M j
    · simp only [if_neg h1, if_pos h2]
    · simp only [if_neg h1, if_neg h2, neg_zero]

/-- The weights of the oriented unit `M`-cycle. -/
private theorem diagramWeight_unitCycleMatrix {M : ℕ} (hM : 3 ≤ M) {i j : Fin M} :
    diagramWeight (unitCycleMatrix M) i j = if j = finRotate M i ∨ i = finRotate M j then 1
      else 0 := by
  simp only [diagramWeight, unitCycleMatrix, of_apply]
  by_cases h1 : j = finRotate M i
  · have h2 := ne_finRotate_of_eq_finRotate hM h1
    simp only [if_pos h1, if_neg h2, if_pos (Or.inl h1 : j = finRotate M i ∨ i = finRotate M j)]
    rfl
  · by_cases h2 : i = finRotate M j
    · simp only [if_neg h1, if_pos h2,
        if_pos (Or.inr h2 : j = finRotate M i ∨ i = finRotate M j)]
      rfl
    · simp only [if_neg h1, if_neg h2, if_neg (not_or.2 ⟨h1, h2⟩), mul_zero]
      rfl

/-- `(1, …, M)` is an oriented unit cycle of the oriented unit `M`-cycle. -/
private theorem isOrientedUnitCycle_unitCycleMatrix {M : ℕ} (hM : 3 ≤ M) :
    IsOrientedUnitCycle (unitCycleMatrix M) (Equiv.refl (Fin M)) := by
  refine ⟨⟨hM, (Equiv.refl _).injective, fun p q hpq => ?_⟩, fun p => ⟨?_, ?_⟩⟩
  · simp only [Equiv.refl_apply]
    rw [diagramGraph_adj, diagramWeight_unitCycleMatrix hM]
    split_ifs with h
    · exact iff_of_true ⟨hpq, one_pos⟩ h
    · exact iff_of_false (fun h' => lt_irrefl 0 h'.2) h
  · simp [unitCycleMatrix]
  · simp only [cycleWeights, Equiv.refl_apply, diagramWeight_unitCycleMatrix hM, true_or,
      if_true]

/-- An oriented unit cycle is carried to an oriented unit cycle by an injective map preserving
weights and arrows. -/
private theorem IsOrientedUnitCycle.of_diagram_cpv {m : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    {Y : Matrix (Fin m) (Fin m) ℤ} {v : Fin m → Fin n} (hv : Function.Injective v)
    (hw : ∀ p q, diagramWeight B (v p) (v q) = diagramWeight Y p q)
    (hpos : ∀ p q, 0 < B (v p) (v q) ↔ 0 < Y p q) {w : Fin m → Fin m}
    (hY : IsOrientedUnitCycle Y w) : IsOrientedUnitCycle B (v ∘ w) := by
  refine ⟨⟨hY.1.1, hv.comp hY.1.2.1, fun p q hpq => ?_⟩, fun p =>
    ⟨(hpos _ _).2 (hY.2 p).1, (hw _ _).trans (hY.2 p).2⟩⟩
  rw [← hY.1.2.2 p q hpq, Function.comp_apply, Function.comp_apply, diagramGraph_adj,
    diagramGraph_adj, hw, hv.ne_iff]

/-- In a connected matrix with an enumeration `c₁, …, c_L, u` of its indices, `L ≥ 1`, the index
`u` is adjacent to some `c_j`. -/
private theorem IsConnectedDiagram.exists_adj_cpv {L : ℕ} (hL : 0 < L)
    {B : Matrix (Fin (L + 1)) (Fin (L + 1)) ℤ} (hBs : SkewSymmetrizable B)
    (hc : IsConnectedDiagram B) {c : Fin L → Fin (L + 1)} (hinj : Function.Injective c)
    {u : Fin (L + 1)} (hu : u ∉ Set.range c) : ∃ j, (diagramGraph B).Adj u (c j) := by
  have hcu : ∀ i, c i ≠ u := fun i h => hu ⟨i, h⟩
  have hcover : ∀ x, x = u ∨ ∃ i, c i = x := by
    intro x
    have h1 : insert u (Finset.univ.image c) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_insert_of_notMem (by simpa using hu),
        Finset.card_image_of_injective _ hinj]
      simp
    have : x ∈ insert u (Finset.univ.image c) := h1 ▸ Finset.mem_univ x
    simpa [eq_comm] using this
  by_contra hno
  push Not at hno
  apply hBs.isConnectedDiagram_iff.mp hc
  refine ⟨{u}, by simp, ⟨c ⟨0, hL⟩, by simp [hcu]⟩, fun i hi x hx => ?_⟩
  rw [Finset.mem_singleton] at hi hx
  subst hi
  obtain rfl | ⟨k, rfl⟩ := hcover x
  · exact absurd rfl hx
  by_contra hne
  exact hno k ⟨(hcu k).symm, (hBs.diagramWeight_pos_iff _ _).2 hne⟩

/-- An oriented unit cycle `c₁, …, c_L`, `L ≥ 4`, with an extra vertex `u` joined to `c_j` alone,
with weight `2`, contains the subdiagram `(c_{j-1}, c_{j+1}, c_j, u)` of shape `B₃^{(1)}`, so it
is not `2`-finite. -/
private theorem IsOrientedUnitCycle.not_isTwoFinite_of_diagramWeight_eq_two {L : ℕ} (hL : 4 ≤ L)
    {B : Matrix (Fin (L + 1)) (Fin (L + 1)) ℤ} {c : Fin L → Fin (L + 1)} {u : Fin (L + 1)}
    (hcyc : IsOrientedUnitCycle B c) (hcu : ∀ i, c i ≠ u) {j jm jp : Fin L}
    (hjm : ((j : ℕ) = 0 ∧ (jm : ℕ) = L - 1) ∨ ((j : ℕ) ≠ 0 ∧ (jm : ℕ) + 1 = j))
    (hjp : ((j : ℕ) + 1 = L ∧ (jp : ℕ) = 0) ∨ ((j : ℕ) + 1 ≠ L ∧ (jp : ℕ) = j + 1))
    (hwu : ∀ i, i ≠ j → diagramWeight B u (c i) = 0) (hw : diagramWeight B u (c j) = 2) :
    ¬IsTwoFinite B := by
  intro hB
  have hjL := j.isLt
  have hjpj : (jp : ℕ) ≠ j := by omega
  have hjmj : (jm : ℕ) ≠ j := by omega
  have hjmjp : (jm : ℕ) ≠ jp := by omega
  have hcne : ∀ p q : Fin L, (p : ℕ) ≠ q → c p ≠ c q :=
    fun p q h => hcyc.1.2.1.ne (Fin.ne_of_val_ne h)
  have hwc := fun (p q : Fin L) (h : (p : ℕ) ≠ q) =>
    hcyc.diagramWeight_eq_cpv (Fin.ne_of_val_ne h)
  have hjmjp0 : diagramWeight B (c jm) (c jp) = 0 := by rw [hwc _ _ hjmjp, if_neg (by omega)]
  have hjmj1 : diagramWeight B (c jm) (c j) = 1 := by rw [hwc _ _ hjmj, if_pos (by omega)]
  have hjjp : diagramWeight B (c j) (c jp) = 1 := by rw [hwc _ _ hjpj.symm, if_pos (by omega)]
  have hujp : diagramWeight B u (c jp) = 0 := hwu jp (Fin.ne_of_val_ne hjpj)
  have hujm : diagramWeight B u (c jm) = 0 := hwu jm (Fin.ne_of_val_ne hjmj)
  let v : Fin 4 → Fin (L + 1) := ![c jm, c jp, c j, u]
  have hv : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [v, hcu, (hcu _).symm, hcne _ _ hjmjp, hcne _ _ hjmjp.symm, hcne _ _ hjmj,
        hcne _ _ hjmj.symm, hcne _ _ hjpj, hcne _ _ hjpj.symm] at hab ⊢
  let r : Fin 4 ↪ Fin (L + 1) := ⟨v, hv⟩
  have hS : IsBAffineShape (diagramWeight (B.submatrix r r)) 3 := by
    refine ⟨le_rfl, Equiv.refl _, fun p q hpq => ?_⟩
    rw [Equiv.refl_apply, Equiv.refl_apply, (diagramWeight_submatrix B r p q).1]
    fin_cases p <;> fin_cases q <;>
      simp [r, v, orderedModel, bAffineModel, hjmjp0, hjmj1, hjjp, hujp, hujm, hw,
        diagramWeight_comm B (c jp) (c jm), diagramWeight_comm B (c j) (c jm),
        diagramWeight_comm B (c jp) (c j), diagramWeight_comm B (c jm) u,
        diagramWeight_comm B (c jp) u, diagramWeight_comm B (c j) u] at hpq ⊢
  exact not_isTwoFinite_of_isBAffineShape hS (hB.submatrix _)

/-- An oriented unit cycle `c₁, …, c_L`, `L ≥ 4`, with an extra vertex `u` joined to `c_j` alone,
with weight `3`, contains the subdiagram `(u, c_j, c_{j+1})` of shape `G₂^{(1)}(1)`, so it is not
`2`-finite. -/
private theorem IsOrientedUnitCycle.not_isTwoFinite_of_diagramWeight_eq_three {L : ℕ}
    (hL : 4 ≤ L) {B : Matrix (Fin (L + 1)) (Fin (L + 1)) ℤ} {c : Fin L → Fin (L + 1)}
    {u : Fin (L + 1)} (hcyc : IsOrientedUnitCycle B c) (hcu : ∀ i, c i ≠ u) {j jp : Fin L}
    (hjp : ((j : ℕ) + 1 = L ∧ (jp : ℕ) = 0) ∨ ((j : ℕ) + 1 ≠ L ∧ (jp : ℕ) = j + 1))
    (hwu : ∀ i, i ≠ j → diagramWeight B u (c i) = 0) (hw : diagramWeight B u (c j) = 3) :
    ¬IsTwoFinite B := by
  intro hB
  have hjpj : (jp : ℕ) ≠ j := by omega
  have hcne : ∀ p q : Fin L, (p : ℕ) ≠ q → c p ≠ c q :=
    fun p q h => hcyc.1.2.1.ne (Fin.ne_of_val_ne h)
  have hjjp : diagramWeight B (c j) (c jp) = 1 := by
    rw [hcyc.diagramWeight_eq_cpv (Fin.ne_of_val_ne hjpj.symm), if_pos (by omega)]
  have hujp : diagramWeight B u (c jp) = 0 := hwu jp (Fin.ne_of_val_ne hjpj)
  let v : Fin 3 → Fin (L + 1) := ![u, c j, c jp]
  have hv : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [v, hcu, (hcu _).symm, hcne _ _ hjpj, hcne _ _ hjpj.symm] at hab ⊢
  let r : Fin 3 ↪ Fin (L + 1) := ⟨v, hv⟩
  have hS : IsG2AffineShape (diagramWeight (B.submatrix r r)) 1 := by
    refine ⟨Or.inl rfl, Equiv.refl _, fun p q hpq => ?_⟩
    rw [Equiv.refl_apply, Equiv.refl_apply, (diagramWeight_submatrix B r p q).1]
    fin_cases p <;> fin_cases q <;>
      simp [r, v, orderedModel, g2AffineModel, hjjp, hujp, hw,
        diagramWeight_comm B (c jp) (c j), diagramWeight_comm B (c jp) u,
        diagramWeight_comm B (c j) u] at hpq ⊢
  exact not_isTwoFinite_of_isG2AffineShape hS (hB.submatrix _)

/-- **An oriented unit cycle with one more vertex.** Let `L ≥ 4` and let `B` be a `2`-finite
connected `(L + 1) × (L + 1)` matrix with an enumeration `c₁, …, c_L, u` of its indices such
that `(c₁, …, c_L)` is an oriented unit cycle. Then `B` is of Dynkin class `X` for a Dynkin
symbol `X` of rank `L + 1`. -/
@[cluster_algebras "lem_cycle_plus_vertex"]
theorem IsOrientedUnitCycle.exists_isOfDynkinClass {L : ℕ} (hL : 4 ≤ L)
    {B : Matrix (Fin (L + 1)) (Fin (L + 1)) ℤ} (hB : IsTwoFinite B) (hc : IsConnectedDiagram B)
    {c : Fin L → Fin (L + 1)} {u : Fin (L + 1)} (hu : u ∉ Set.range c)
    (hcyc : IsOrientedUnitCycle B c) :
    ∃ X : DynkinSymbol, X.rank = L + 1 ∧ IsOfDynkinClass B [X] := by
  have hBs := hB.1
  have hcu : ∀ i, c i ≠ u := fun i h => hu ⟨i, h⟩
  by_cases h2 : ∃ i i', i ≠ i' ∧ (diagramGraph B).Adj u (c i) ∧ (diagramGraph B).Adj u (c i')
  · obtain ⟨p, -, -, -, -, -, hcyc'⟩ := hcyc.exists_adj_eq_of_isTwoFinite hB hL hu h2
    have hBs' := skewSymmetrizable_matrixMutation hBs u
    exact ⟨_, rfl, IsOfDynkinClass.of_diagramEquiv hBs hBs'
      (mutationEquiv_matrixMutation B u).diagramEquiv
      (IsOrientedUnitCycle.isOfDynkinClass_D
        (v := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hcyc'.1.2.1)) hBs' hcyc'
        (by omega))⟩
  push Not at h2
  obtain ⟨j, hj⟩ := hc.exists_adj_cpv (by omega) hBs hcyc.1.2.1 hu
  have hwu : ∀ i, i ≠ j → diagramWeight B u (c i) = 0 := by
    intro i hij
    by_contra hne
    exact h2 j i (Ne.symm hij) hj ⟨(hcu i).symm, Nat.pos_of_ne_zero hne⟩
  have hjL := j.isLt
  obtain ⟨jm, hjm⟩ : ∃ x : Fin L,
      ((j : ℕ) = 0 ∧ (x : ℕ) = L - 1) ∨ ((j : ℕ) ≠ 0 ∧ (x : ℕ) + 1 = j) :=
    ⟨⟨if (j : ℕ) = 0 then L - 1 else (j : ℕ) - 1, by grind⟩, by grind⟩
  obtain ⟨jp, hjp⟩ : ∃ x : Fin L,
      ((j : ℕ) + 1 = L ∧ (x : ℕ) = 0) ∨ ((j : ℕ) + 1 ≠ L ∧ (x : ℕ) = j + 1) :=
    ⟨⟨if (j : ℕ) + 1 = L then 0 else (j : ℕ) + 1, by grind⟩, by grind⟩
  obtain hw | hw | hw : diagramWeight B u (c j) = 1 ∨ diagramWeight B u (c j) = 2 ∨
      diagramWeight B u (c j) = 3 := by
    have := hB.diagramWeight_le_three u (c j)
    have := hj.2
    omega
  · obtain ⟨t, ht⟩ := exists_isTShape_matrixMutationList_of_isCrownShape hBs
      (isCrownShape_cpv hL hcyc hcu hjm hw hwu)
    obtain ⟨X, ⟨σ, -⟩, hXc⟩ :=
      (hB.matrixMutationList t).hasDynkinShape_of_isTreeDiagram (IsTShape.isTreeDiagram ht)
    exact ⟨X, by simpa [DynkinSymbol.listRank] using Fintype.card_congr σ,
      IsOfDynkinClass.of_diagramEquiv hBs (hB.matrixMutationList t).1
        (mutationEquiv_matrixMutationList B t).diagramEquiv hXc⟩
  · exact (hcyc.not_isTwoFinite_of_diagramWeight_eq_two hL hcu hjm hjp hwu hw hB).elim
  · exact (hcyc.not_isTwoFinite_of_diagramWeight_eq_three hL hcu hjp hwu hw hB).elim

/-- **A diagram of type `D` with one more vertex.** Let `B` be a `2`-finite connected
`(M + 1) × (M + 1)` matrix, `M ≥ 4`, let `r` enumerate the indices other than `u`, and let `C`
have Dynkin shape `D_M` with `B^r ∼ C`. Then `B` is of Dynkin class `X` for a Dynkin symbol `X`
of rank `M + 1`. FWZ take `C` an orientation of `ω_{D_M}`; a matrix of Dynkin shape
`D_M` is a relabelling of one, which is more general. -/
@[cluster_algebras "lem_D_type_plus_vertex"]
theorem exists_isOfDynkinClass_of_diagramEquiv_hasDynkinShape_D {M : ℕ} (hM : 4 ≤ M)
    {B : Matrix (Fin (M + 1)) (Fin (M + 1)) ℤ} (hB : IsTwoFinite B) (hc : IsConnectedDiagram B)
    {u : Fin (M + 1)} {r : Fin M ↪ Fin (M + 1)} (hr : Set.range r = {u}ᶜ)
    {C : Matrix (Fin M) (Fin M) ℤ} (hC : HasDynkinShape C [DynkinSymbol.D M hM])
    (h : DiagramEquiv (B.submatrix r r) C) :
    ∃ X : DynkinSymbol, X.rank = M + 1 ∧ IsOfDynkinClass B [X] := by
  have hM3 : 3 ≤ M := by omega
  have hYs := skewSymmetrizable_unitCycleMatrix hM3
  have hYc := isOrientedUnitCycle_unitCycleMatrix hM3
  obtain ⟨C', hC', hYC'⟩ := hYc.isOfDynkinClass_D hYs hM
  have hCs := hC.skewSymmetrizable
  have hC's := hC'.skewSymmetrizable
  have hBY : DiagramEquiv (B.submatrix r r) (unitCycleMatrix M) :=
    h.trans (hB.submatrix r).1 hCs ((diagramEquiv_of_hasDynkinShape_D_cpv hC hC').trans hCs hC's
      (hYC'.symm hYs hC's))
  obtain ⟨s, π, -, hmut, -, hdiag⟩ := DiagramEquiv.exists_submatrix r hBY
  have hBs' := hB.matrixMutationList s
  obtain ⟨hw, hpos⟩ := ((skewSymmetrizable_submatrix hBs'.1 (r ∘ π)).diagram_eq_iff hYs).1 hdiag
  have hcyc := IsOrientedUnitCycle.of_diagram_cpv (r.injective.comp π.injective) hw hpos hYc
  have hu : u ∉ Set.range ((r ∘ π) ∘ Equiv.refl (Fin M)) := by
    rintro ⟨p, hp⟩
    exact (hr ▸ ⟨π p, hp⟩ : u ∈ ({u}ᶜ : Set _)) rfl
  obtain ⟨X, hXr, hXc⟩ := hcyc.exists_isOfDynkinClass hM hBs'
    (isConnectedDiagram_matrixMutationList hB.1 hc s) hu
  exact ⟨X, hXr, IsOfDynkinClass.of_diagramEquiv hB.1 hBs'.1 hmut.diagramEquiv hXc⟩

end ClusterAlgebras
