/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TwoFinite.External
public import ClusterAlgebras.TwoFinite.Shapes

/-!
# `2`-finite cycle diagrams and chordless cycles

An oriented unit cycle enumerating `[1, m]` is mutation equivalent to a tree of shape
`T_{1,1,m-3}`; consequently it is of Dynkin class `D_m` for `m ≥ 4` and of Dynkin class `A₃` for
`m = 3`. An oriented square with weights `(2, 1, 2, 1)` is of Dynkin class `F₄`. Every chordless
cycle of a `2`-finite matrix is cyclically oriented, with admissible weights.

## Main results

* `ClusterAlgebras.IsOrientedUnitCycle.exists_isTShape`: an oriented unit cycle is mutation
  equivalent to a tree of shape `T_{1,1,m-3}`.
* `ClusterAlgebras.IsOrientedUnitCycle.isOfDynkinClass_D`: an oriented unit cycle on `m ≥ 4`
  vertices is of Dynkin class `D_m`.
* `ClusterAlgebras.IsOrientedUnitCycle.isOfDynkinClass_A`: an oriented unit cycle on `3` vertices
  is of Dynkin class `A₃`.
* `ClusterAlgebras.isOfDynkinClass_F₄_of_cycleWeights_eq_two_one`: an oriented square with
  weights `(2, 1, 2, 1)` is of Dynkin class `F₄`.
* `ClusterAlgebras.IsTwoFinite.isCyclicallyOriented_of_isChordlessCycle`: every chordless cycle
  of a `2`-finite matrix is cyclically oriented, with weights in `L_m`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Section 5.10.
-/
@[expose] public section

namespace ClusterAlgebras

open Matrix

variable {n m : ℕ}

/-! ### Auxiliary facts -/

/-- A matrix having a mutation of Dynkin shape `X` is of Dynkin class `X`. -/
private theorem isOfDynkinClass_of_hasDynkinShape_matrixMutationList
    {B : Matrix (Fin n) (Fin n) ℤ} {t : List (Fin n)} {Xs : List DynkinSymbol}
    (h : HasDynkinShape (matrixMutationList le_rfl B t) Xs) : IsOfDynkinClass B Xs :=
  ⟨_, h, (mutationEquiv_matrixMutationList B t).diagramEquiv⟩

/-- The value of `finRotate (k + 3)`. -/
private theorem coe_finRotate_add_three {k : ℕ} (i : Fin (k + 3)) :
    (finRotate (k + 3) i : ℕ) = if (i : ℕ) = k + 2 then 0 else (i : ℕ) + 1 := by
  rw [coe_finRotate]
  simp [Fin.ext_iff]

/-- The weights of an oriented unit cycle: `1` on consecutive pairs, `0` on the others. -/
private theorem IsOrientedUnitCycle.diagramWeight_eq {B : Matrix (Fin n) (Fin n) ℤ}
    {v : Fin m → Fin n} (hv : IsOrientedUnitCycle B v) {p q : Fin m} (hpq : p ≠ q) :
    diagramWeight B (v p) (v q) = if q = finRotate m p ∨ p = finRotate m q then 1 else 0 := by
  have hadj := hv.1.2.2 p q hpq
  rw [diagramGraph_adj] at hadj
  split_ifs with h
  · rcases h with rfl | rfl
    · exact (hv.2 p).2
    · rw [diagramWeight_comm]
      exact (hv.2 q).2
  · by_contra h'
    exact h (hadj.1 ⟨hv.1.2.1.ne hpq, Nat.pos_of_ne_zero h'⟩)

/-- An oriented unit cycle enumerating `[1, m]` is of crown shape `S^{m-3}_{1,1,1}`. -/
private theorem IsOrientedUnitCycle.isCrownShape {B : Matrix (Fin m) (Fin m) ℤ}
    {v : Fin m ≃ Fin m} (hv : IsOrientedUnitCycle B v) : IsCrownShape B (m - 3) 1 1 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by have := hv.1.1; omega⟩
  have hN : 1 + 1 + 1 + (k + 3 - 3) = k + 3 := by omega
  refine ⟨le_rfl, le_rfl, le_rfl, (finCongr hN).trans v, ?_, ?_⟩
  · intro i j hij
    simp only [Equiv.trans_apply, finCongr_apply]
    rw [hv.diagramWeight_eq (fun h => hij (Fin.cast_injective hN h))]
    have hi := i.isLt
    have hj := j.isLt
    have hL : (Fin.cast hN j = finRotate (k + 3) (Fin.cast hN i) ∨
        Fin.cast hN i = finRotate (k + 3) (Fin.cast hN j)) ↔
        ((j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) = k + 2) ∨
          ((j : ℕ) = 0 ∧ (i : ℕ) = k + 2)) := by
      simp only [Fin.ext_iff, coe_finRotate_add_three, Fin.val_cast]
      split_ifs <;> omega
    have hR : orderedModel (crownModel (k + 3 - 3) 1 1 1) i j =
        if ((j : ℕ) = i + 1 ∨ (i : ℕ) = j + 1 ∨ ((i : ℕ) = 0 ∧ (j : ℕ) = k + 2) ∨
          ((j : ℕ) = 0 ∧ (i : ℕ) = k + 2)) then 1 else 0 := by
      unfold orderedModel crownModel
      simp only
      split_ifs <;> omega
    rw [hR]
    exact if_congr hL rfl rfl
  · rintro i j h
    simp only [Equiv.trans_apply, finCongr_apply]
    have hj : Fin.cast hN j = finRotate (k + 3) (Fin.cast hN i) := by
      have hi := i.isLt
      rw [Fin.ext_iff, coe_finRotate_add_three, Fin.val_cast, Fin.val_cast]
      split_ifs <;> omega
    rw [hj]
    exact (hv.2 _).1

/-- An oriented unit cycle enumerating `[1, m]` is mutation equivalent to a tree of shape
`T_{1,1,m-3}`. -/
@[cluster_algebras "lem_cycle_diagrams"]
theorem IsOrientedUnitCycle.exists_isTShape {B : Matrix (Fin m) (Fin m) ℤ}
    (hB : SkewSymmetrizable B) {v : Fin m ≃ Fin m} (hv : IsOrientedUnitCycle B v) :
    ∃ t : List (Fin m), IsTShape (diagramWeight (matrixMutationList le_rfl B t)) 1 1 (m - 3) :=
  exists_isTShape_matrixMutationList_of_isCrownShape hB hv.isCrownShape

/-- An oriented unit cycle enumerating `[1, m]`, `m ≥ 4`, is of Dynkin class `D_m`. -/
@[cluster_algebras "lem_cycle_diagrams"]
theorem IsOrientedUnitCycle.isOfDynkinClass_D {B : Matrix (Fin m) (Fin m) ℤ}
    (hB : SkewSymmetrizable B) {v : Fin m ≃ Fin m} (hv : IsOrientedUnitCycle B v) (hm : 4 ≤ m) :
    IsOfDynkinClass B [DynkinSymbol.D m hm] := by
  obtain ⟨t, ht⟩ := hv.exists_isTShape hB
  exact isOfDynkinClass_of_hasDynkinShape_matrixMutationList
    (hasDynkinShape_D_of_isTShape (skewSymmetrizable_matrixMutationList hB t) hm ht)

/-- An oriented unit cycle enumerating `[1, 3]` is of Dynkin class `A₃`. -/
@[cluster_algebras "lem_cycle_diagrams"]
theorem IsOrientedUnitCycle.isOfDynkinClass_A {B : Matrix (Fin 3) (Fin 3) ℤ}
    (hB : SkewSymmetrizable B) {v : Fin 3 ≃ Fin 3} (hv : IsOrientedUnitCycle B v) :
    IsOfDynkinClass B [DynkinSymbol.A 3 (by norm_num)] := by
  obtain ⟨t, e, he⟩ := hv.exists_isTShape hB
  refine isOfDynkinClass_of_hasDynkinShape_matrixMutationList (t := t) ?_
  have hB' := skewSymmetrizable_matrixMutationList hB t
  generalize matrixMutationList le_rfl B t = B' at he hB' ⊢
  let w : Fin 3 ≃ Fin 3 := (Equiv.swap 0 1).trans e
  have hw : ∀ p q : Fin 3, p ≠ q → diagramWeight B' (w p) (w q) =
      orderedModel (tShapeModel 1 1 0) (Equiv.swap 0 1 p) (Equiv.swap 0 1 q) := fun p q hpq =>
    he _ _ ((Equiv.swap 0 1).injective.ne hpq)
  have hpath : IsInducedPath B' w := by
    refine ⟨by norm_num, w.injective, fun p q hpq => ?_⟩
    rw [diagramGraph_adj, hw p q hpq]
    have hne : w p ≠ w q := w.injective.ne hpq
    fin_cases p <;> fin_cases q <;>
      simp [orderedModel, tShapeModel, Equiv.swap_apply_def] at hpq hne ⊢
  refine hasDynkinShape_A_of_isInducedPath hB' _ hpath fun p q hpq => ?_
  rw [hw p q (by rintro rfl; omega)]
  fin_cases p <;> fin_cases q <;>
    simp [orderedModel, tShapeModel, Equiv.swap_apply_def] at hpq ⊢

/-- An oriented square with weights `(2, 1, 2, 1)` enumerating `[1, 4]` is of Dynkin
class `F₄`. -/
@[cluster_algebras "lem_cycle_diagrams"]
theorem isOfDynkinClass_F₄_of_cycleWeights_eq_two_one {B : Matrix (Fin 4) (Fin 4) ℤ}
    (hB : SkewSymmetrizable B) {v : Fin 4 ≃ Fin 4} (hv : IsChordlessCycle B v)
    (hor : ∀ p, 0 < B (v p) (v (finRotate 4 p))) (hw : cycleWeights B v = ![2, 1, 2, 1]) :
    IsOfDynkinClass B [DynkinSymbol.F₄] := by
  obtain ⟨hpath, h₁, h₂, h₃⟩ :=
    isInducedPath_matrixMutationList_of_cycleWeights_eq_two_one hB hv hor hw
  refine isOfDynkinClass_of_hasDynkinShape_matrixMutationList (t := [v 0, v 1, v 0]) ?_
  have hB' := skewSymmetrizable_matrixMutationList hB [v 0, v 1, v 0]
  generalize matrixMutationList le_rfl B [v 0, v 1, v 0] = B' at hpath h₁ h₂ h₃ hB' ⊢
  let w : Fin 4 ≃ Fin 4 := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hpath.2.1)
  refine hasDynkinShape_F₄_of_isInducedPath (v := w) hB' hpath fun p q hpq => ?_
  fin_cases p <;> fin_cases q <;> simp_all [w]

/-- **Chordless cycles of a `2`-finite diagram**: every chordless cycle `(v₁, …, v_m)` of a
`2`-finite matrix is cyclically oriented, with weights in `L_m`. -/
@[cluster_algebras "lem_chordless_cycles"]
theorem IsTwoFinite.isCyclicallyOriented_of_isChordlessCycle {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : IsTwoFinite B) {v : Fin m → Fin n} (hv : IsChordlessCycle B v) :
    IsCyclicallyOriented B v ∧ IsAdmissibleCycleWeights (cycleWeights B v) := by
  let r : Fin m ↪ Fin n := ⟨v, hv.2.1⟩
  have hc : IsChordlessCycle (B.submatrix r r) (Equiv.refl (Fin m)) :=
    ⟨hv.1, (Equiv.refl _).injective, fun p q hpq => by
      rw [← hv.2.2 p q hpq]
      exact ⟨fun h => ⟨hv.2.1.ne h.1, h.2⟩, fun h => ⟨hpq, h.2⟩⟩⟩
  exact hc.isCyclicallyOriented_of_isTwoFinite (hB.submatrix r)

end ClusterAlgebras
