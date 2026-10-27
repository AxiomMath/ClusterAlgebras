/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.EntryIndependent

/-!
# Folding: the sign of an entry of the folded matrix

Let `B` be a `G`-admissible `m × n` integer matrix and `θ` an orbit labelling. The sign of an
entry `b^G_{pq} = ∑_{i ∈ θ(p)} b_{i j_q}` of the folded matrix can be read off the entries of
`B` over the orbits `θ(p)` and `θ(q)`: `b^G_{pq} > 0` if and only if `b_{ij} > 0` for some
`i ∈ θ(p)` and `j ∈ θ(q)`, if and only if every `i ∈ θ(p)` has some `j ∈ θ(q)` with
`b_{ij} > 0`; and likewise for `b^G_{pq} < 0`.

If some `b_{ij} > 0`, then every entry over `θ(p) × θ(q)` is nonnegative, because these entries
have one weak sign; computing `b^G_{pq}` with the column `j` then gives
`b^G_{pq} ≥ b_{ij} > 0`. If `b_{i₀ j₀} > 0` and `i = g(i₀)`, then condition (2) gives
`b_{i, g(j₀)} = b_{i₀ j₀} > 0`. The negative statements follow by applying the positive ones to
`-B`, which is again `G`-admissible, with `(-B)ᴳ = -Bᴳ`.

## Main results

* `ClusterAlgebras.foldedMatrix_pos_iff_exists`: `b^G_{pq} > 0` iff `b_{ij} > 0` for some
  `i ∈ θ(p)`, `j ∈ θ(q)`.
* `ClusterAlgebras.foldedMatrix_pos_iff_forall`: `b^G_{pq} > 0` iff every `i ∈ θ(p)` has some
  `j ∈ θ(q)` with `b_{ij} > 0`.
* `ClusterAlgebras.foldedMatrix_neg_iff_exists`, `ClusterAlgebras.foldedMatrix_neg_iff_forall`:
  the same for `b^G_{pq} < 0`.
* `ClusterAlgebras.IsGroupAdmissible.neg`, `ClusterAlgebras.foldedMatrix_neg`: `-B` is
  `G`-admissible, and `(-B)ᴳ = -Bᴳ`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4.
-/

@[expose] public section

namespace ClusterAlgebras

open MulAction

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}
  {B : Matrix (Fin m) (Fin n) ℤ}

/-- Conditions (2)–(4) are invariant under `B ↦ -B`: the negative of a `G`-admissible matrix
is `G`-admissible. -/
theorem IsGroupAdmissible.neg (hB : IsGroupAdmissible G hmn B) : IsGroupAdmissible G hmn (-B) where
  smul_eq g i j j' h := by simp [hB.smul_eq g i j j' h]
  eq_zero i i' h := by simp [hB.eq_zero i i' h]
  mul_nonneg i i' h j := by simpa using hB.mul_nonneg i i' h j

/-- A matrix is `G`-admissible if and only if its negative is. -/
@[simp]
theorem isGroupAdmissible_neg_iff : IsGroupAdmissible G hmn (-B) ↔ IsGroupAdmissible G hmn B :=
  ⟨fun h => neg_neg B ▸ h.neg, IsGroupAdmissible.neg⟩

/-- Folding commutes with negation: `(-B)ᴳ = -Bᴳ`. -/
@[simp]
theorem foldedMatrix_neg (θ : OrbitLabelling G m n mG nG) (B : Matrix (Fin m) (Fin n) ℤ) :
    foldedMatrix θ (-B) = -foldedMatrix θ B := by
  ext p q
  simp [foldedMatrix_apply]

/-- An entry of the folded matrix is positive, `b^G_{pq} > 0`, if and only if `b_{ij} > 0` for
some `i ∈ θ(p)` and `j ∈ θ(q)`. -/
@[cluster_algebras "lem_folded_pos_iff_exists"]
theorem foldedMatrix_pos_iff_exists (hB : IsGroupAdmissible G hmn B)
    (θ : OrbitLabelling G m n mG nG) (p : Fin mG) (q : Fin nG) :
    0 < foldedMatrix θ B p q ↔ ∃ i ∈ θ.orbit p, ∃ j ∈ θ.cols hmn q, 0 < B i j := by
  refine ⟨fun h => ?_, fun ⟨i, hi, j, hj, hpos⟩ => ?_⟩
  · rw [foldedMatrix_apply] at h
    by_contra! hneg
    exact h.not_ge <| Finset.sum_nonpos fun i hi => hneg i hi _ (θ.colRep_mem_cols hmn q)
  · rw [foldedMatrix_apply_eq_sum_of_mem_cols hB θ p q hj]
    refine hpos.trans_le (Finset.single_le_sum (f := fun i' => B i' j) (fun i' hi' => ?_) hi)
    exact (mul_nonneg_iff_of_pos_left hpos).1
      (hB.mul_nonneg_of_mem_orbit_of_mem_cols θ hi hi' hj hj)

/-- An entry of the folded matrix is positive, `b^G_{pq} > 0`, if and only if every
`i ∈ θ(p)` has some `j ∈ θ(q)` with `b_{ij} > 0`. -/
@[cluster_algebras "lem_folded_pos_iff_forall"]
theorem foldedMatrix_pos_iff_forall (hB : IsGroupAdmissible G hmn B)
    (θ : OrbitLabelling G m n mG nG) (p : Fin mG) (q : Fin nG) :
    0 < foldedMatrix θ B p q ↔ ∀ i ∈ θ.orbit p, ∃ j ∈ θ.cols hmn q, 0 < B i j := by
  rw [foldedMatrix_pos_iff_exists hB θ p q]
  refine ⟨?_, fun h => (θ.orbit_nonempty p).elim fun i hi => ⟨i, hi, h i hi⟩⟩
  rintro ⟨i₀, hi₀, j₀, hj₀, hpos⟩ i hi
  obtain ⟨g, rfl⟩ := mem_orbit_iff.1 (θ.mem_orbit_of_mem hi₀ hi)
  have hmem : g • Fin.castLE hmn j₀ ∈ θ.orbit (Fin.castLE θ.le q) :=
    θ.smul_mem_orbit (θ.mem_cols.1 hj₀) g
  let j : Fin n := ⟨(g • Fin.castLE hmn j₀ : Fin m), θ.val_lt_of_mem (θ.val_castLE_lt q) hmem⟩
  have hj : Fin.castLE hmn j = g • Fin.castLE hmn j₀ := Fin.ext rfl
  exact ⟨j, θ.mem_cols.2 (hj ▸ hmem), (hB.smul_eq g i₀ j₀ j hj).symm ▸ hpos⟩

/-- An entry of the folded matrix is negative, `b^G_{pq} < 0`, if and only if `b_{ij} < 0` for
some `i ∈ θ(p)` and `j ∈ θ(q)`. -/
@[cluster_algebras "lem_folded_neg_iff_exists"]
theorem foldedMatrix_neg_iff_exists (hB : IsGroupAdmissible G hmn B)
    (θ : OrbitLabelling G m n mG nG) (p : Fin mG) (q : Fin nG) :
    foldedMatrix θ B p q < 0 ↔ ∃ i ∈ θ.orbit p, ∃ j ∈ θ.cols hmn q, B i j < 0 := by
  simpa using foldedMatrix_pos_iff_exists hB.neg θ p q

/-- An entry of the folded matrix is negative, `b^G_{pq} < 0`, if and only if every
`i ∈ θ(p)` has some `j ∈ θ(q)` with `b_{ij} < 0`. -/
@[cluster_algebras "lem_folded_neg_iff_forall"]
theorem foldedMatrix_neg_iff_forall (hB : IsGroupAdmissible G hmn B)
    (θ : OrbitLabelling G m n mG nG) (p : Fin mG) (q : Fin nG) :
    foldedMatrix θ B p q < 0 ↔ ∀ i ∈ θ.orbit p, ∃ j ∈ θ.cols hmn q, B i j < 0 := by
  simpa using foldedMatrix_pos_iff_forall hB.neg θ p q

end ClusterAlgebras
