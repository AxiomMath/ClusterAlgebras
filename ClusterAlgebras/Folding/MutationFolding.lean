/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.EntryIndependent
public import ClusterAlgebras.Folding.SetMutation

/-!
# Mutation at an orbit commutes with folding

Let `B` be a `G`-admissible `m × n` integer matrix, `θ` an orbit labelling, `r` a mutable label
and `K = θ(r)`. Mutating `B` at every index of `K`, along the increasing sequence `s_K`, and then
folding gives the mutation of the folded matrix at `r`: `(μ_{s_K}(B))ᴳ = μ_r(Bᴳ)`.

By `IsGroupAdmissible.eq_zero` the entries `b_{kk'}`, `k, k' ∈ K`, vanish, so `D = μ_{s_K}(B)`
negates the rows and columns indexed by `K` and adds `∑_{k ∈ K} c(b_{ik}, b_{kj})` to every other
entry. On the row or the column of `r` both sides are then `-b^G_{pq}`. Elsewhere, with `I = θ(p)`
and `j = j_q`, one must show `∑_{i ∈ I} ∑_{k ∈ K} c(b_{ik}, b_{kj}) = c(b^G_{pr}, b^G_{rq})`. Write
`c(x, y) = [x]₊[y]₊ - [-x]₊[-y]₊`. By `IsGroupAdmissible.mul_nonneg` the entries `b_{ik}`, `i ∈ I`,
of a column `k` share a weak sign, and so do the entries `b_{kj}`, `k ∈ K`; on a family of one weak
sign the positive part of the sum is the sum of the positive parts. Since
`∑_{i ∈ I} b_{ik} = b^G_{pr}` for every `k ∈ K` and `∑_{k ∈ K} b_{kj} = b^G_{rq}`, the double sum
is `[b^G_{pr}]₊ [b^G_{rq}]₊ - [-b^G_{pr}]₊ [-b^G_{rq}]₊`.

## Main results

* `ClusterAlgebras.foldedMatrix_matrixMutationList_increasingSeq`: `(μ_{s_K}(B))ᴳ = μ_r(Bᴳ)`
  for `K = θ(r)`.
* `ClusterAlgebras.sum_sum_mutationCorrection_eq_of_mul_nonneg`: the corrections of the
  directions of `K`, summed over an orbit, are the correction of the folded entries.

## Implementation notes

* FWZ's Lemma 4.4.5 assumes in addition that `μ_K(B)` is `G`-admissible. That hypothesis only
  makes the folded matrix of `μ_K(B)` independent of the representatives `j_q` of the column
  orbits; here the folded matrix is defined with the least representative, so the hypothesis is
  not needed and is not assumed. Dropping it is a generalisation.

* The orbit `θ(r)` of a mutable label is a set of rows, `θ.orbit (Fin.castLE θ.le r)`, and also
  a set of columns, `θ.cols hmn r`; the first is the image of the second under
  `Fin.castLE hmn` (`ClusterAlgebras.OrbitLabelling.map_cols_eq_orbit`).

* The sign argument only uses `IsGroupAdmissible.mul_nonneg` along a single column and along a
  single row orbit, not the stronger `IsGroupAdmissible.mul_nonneg_of_mem_orbit` across pairs of
  columns.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Section 4.4, Lemma 4.4.5.
-/

@[expose] public section

namespace ClusterAlgebras

open MulAction

/-! ### Positive parts of a family of one weak sign -/

/-- On a family whose terms pairwise have nonnegative product, that is, which all share one
weak sign, the sum of the positive parts is the positive part of the sum. -/
theorem sum_max_zero_eq_max_zero_sum_of_mul_nonneg {R ι : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {s : Finset ι} {f : ι → R}
    (h : ∀ i ∈ s, ∀ i' ∈ s, 0 ≤ f i * f i') :
    ∑ i ∈ s, max 0 (f i) = max 0 (∑ i ∈ s, f i) := by
  by_cases hpos : ∃ i ∈ s, 0 < f i
  · obtain ⟨i₀, hi₀, hf⟩ := hpos
    have hnn : ∀ i ∈ s, 0 ≤ f i := fun i hi => nonneg_of_mul_nonneg_right (h i₀ hi₀ i hi) hf
    rw [Finset.sum_congr rfl fun i hi => max_eq_right (hnn i hi),
      max_eq_right (Finset.sum_nonneg hnn)]
  · push Not at hpos
    rw [Finset.sum_congr rfl fun i hi => max_eq_left (hpos i hi),
      max_eq_left (Finset.sum_nonpos hpos), Finset.sum_const_zero]

/-! ### Corrections summed over a pair of orbits -/

/-- Let `x_{ik}` (`i ∈ s`, `k ∈ t`) and `y_k` (`k ∈ t`) be integers such that each column
`(x_{ik})_{i ∈ s}` and the family `(y_k)_{k ∈ t}` share a weak sign. If every column sums to `X`
and the `y_k` sum to `Y`, then `∑_{i ∈ s} ∑_{k ∈ t} c(x_{ik}, y_k) = c(X, Y)`. -/
theorem sum_sum_mutationCorrection_eq_of_mul_nonneg {ι κ : Type*} {s : Finset ι}
    {t : Finset κ} {x : ι → κ → ℤ} {y : κ → ℤ} {X Y : ℤ}
    (hx : ∀ k ∈ t, ∀ i ∈ s, ∀ i' ∈ s, 0 ≤ x i k * x i' k)
    (hy : ∀ k ∈ t, ∀ k' ∈ t, 0 ≤ y k * y k') (hX : ∀ k ∈ t, ∑ i ∈ s, x i k = X)
    (hY : ∑ k ∈ t, y k = Y) :
    ∑ i ∈ s, ∑ k ∈ t, mutationCorrection (x i k) (y k) = mutationCorrection X Y := by
  have hpos : ∀ k ∈ t, ∑ i ∈ s, max 0 (x i k) = max 0 X := fun k hk => by
    rw [sum_max_zero_eq_max_zero_sum_of_mul_nonneg (hx k hk), hX k hk]
  have hneg : ∀ k ∈ t, ∑ i ∈ s, max 0 (-x i k) = max 0 (-X) := fun k hk => by
    rw [sum_max_zero_eq_max_zero_sum_of_mul_nonneg fun i hi i' hi' => by
      rw [neg_mul_neg]; exact hx k hk i hi i' hi', Finset.sum_neg_distrib, hX k hk]
  have hypos : ∑ k ∈ t, max 0 (y k) = max 0 Y := by
    rw [sum_max_zero_eq_max_zero_sum_of_mul_nonneg hy, hY]
  have hyneg : ∑ k ∈ t, max 0 (-y k) = max 0 (-Y) := by
    rw [sum_max_zero_eq_max_zero_sum_of_mul_nonneg fun k hk k' hk' => by
      rw [neg_mul_neg]; exact hy k hk k' hk', Finset.sum_neg_distrib, hY]
  simp_rw [mutationCorrection_eq_max, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := s)]
  simp_rw [← Finset.sum_mul]
  have e₁ : ∑ k ∈ t, (∑ i ∈ s, max 0 (x i k)) * max 0 (y k) = max 0 X * max 0 Y := by
    rw [← hypos, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by rw [hpos k hk]
  have e₂ : ∑ k ∈ t, (∑ i ∈ s, max 0 (-x i k)) * max 0 (-y k) = max 0 (-X) * max 0 (-Y) := by
    rw [← hyneg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by rw [hneg k hk]
  rw [e₁, e₂]

/-! ### Mutation at an orbit commutes with folding -/

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}
  {B : Matrix (Fin m) (Fin n) ℤ}

/-- **Mutation at an orbit commutes with folding** (FWZ, Lemma 4.4.5). For a `G`-admissible
matrix `B` and a mutable label `r` with orbit `K = θ(r)`, `(μ_{s_K}(B))ᴳ = μ_r(Bᴳ)`. -/
@[cluster_algebras "lem_mut_folding"]
theorem foldedMatrix_matrixMutationList_increasingSeq (hB : IsGroupAdmissible G hmn B)
    (θ : OrbitLabelling G m n mG nG) (r : Fin nG) :
    foldedMatrix θ (matrixMutationList hmn B (increasingSeq (θ.cols hmn r))) =
      matrixMutation θ.le (foldedMatrix θ B) r := by
  set K := θ.cols hmn r with hKdef
  have hK : ∀ k ∈ K, ∀ k' ∈ K, B (Fin.castLE hmn k) k' = 0 := fun k hk k' hk' =>
    hB.eq_zero k k' (θ.mem_orbit_of_mem (θ.mem_cols.1 hk) (θ.mem_cols.1 hk'))
  ext p q
  rw [foldedMatrix_apply]
  by_cases h : p = Fin.castLE θ.le r ∨ q = r
  · rw [matrixMutation_apply_of_eq θ.le _ r h, foldedMatrix_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases h with rfl | rfl
    · rw [matrixMutationList_increasingSeq_apply hK, if_pos (Or.inl
        ⟨⟨i, θ.val_lt_of_mem (θ.val_castLE_lt r) hi⟩, θ.mem_cols.2 hi, rfl⟩)]
    · exact matrixMutationList_increasingSeq_apply_of_mem_right hK i (θ.colRep_mem_cols hmn q)
  · obtain ⟨hp, hq⟩ := not_or.1 h
    have hqr : Fin.castLE θ.le q ≠ Fin.castLE θ.le r := fun h => hq (Fin.castLE_injective _ h)
    have hj : θ.colRep q ∉ K := fun hj =>
      Finset.disjoint_left.1 (θ.disjoint_orbit hqr) (θ.rep_mem _) (θ.mem_cols.1 hj)
    rw [matrixMutation_apply_of_ne_eq_mutationCorrection θ.le _ r hp hq, foldedMatrix_apply,
      Finset.sum_congr rfl fun i hi => matrixMutationList_increasingSeq_apply_of_notMem hK
        (fun k hk hik => Finset.disjoint_left.1 (θ.disjoint_orbit hp) hi
          (by rw [hik]; exact θ.mem_cols.1 hk)) hj,
      Finset.sum_add_distrib]
    congr 1
    refine sum_sum_mutationCorrection_eq_of_mul_nonneg
      (fun k _ i hi i' hi' => hB.mul_nonneg i i' (θ.mem_orbit_of_mem hi hi') k)
      (fun k hk k' hk' => hB.mul_nonneg _ _
        (θ.mem_orbit_of_mem (θ.mem_cols.1 hk) (θ.mem_cols.1 hk')) _)
      (fun k hk => (foldedMatrix_apply_eq_sum_of_mem_cols hB θ p r hk).symm) ?_
    rw [foldedMatrix_apply, θ.sum_orbit_eq_sum_cols hmn r]

end ClusterAlgebras
