/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Folding.EntryIndependent

/-!
# Folding a skew-symmetric matrix gives a skew-symmetrizable one

Let `B` be a `G`-admissible `m × n` integer matrix whose principal part is skew-symmetric,
and let `θ` be an orbit labelling. For mutable labels `p, q` write `I = θ(p)` and `J = θ(q)`.
Computing `b^G_{pq}` once with each column `j ∈ J` and summing,
`|J| b^G_{pq} = ∑_{j ∈ J} ∑_{i ∈ I} b_{ij} = -∑_{i ∈ I} ∑_{j ∈ J} b_{ji} = -|I| b^G_{qp}`.
With `d_p = ∏_{r ≠ p} |θ(r)|`, the product running over the mutable labels, this identity
becomes `d_p b^G_{pq} = -d_q b^G_{qp}`, so the folded matrix is extended skew-symmetrizable.

## Main results

* `ClusterAlgebras.card_cols_mul_foldedMatrix`: `|θ(q)| b^G_{pq} = -|θ(p)| b^G_{qp}`.
* `ClusterAlgebras.extSkewSymmetrizable_foldedMatrix`: FWZ's Lemma 4.4.3, `B̃ᴳ` is extended
  skew-symmetrizable.

## Implementation notes

* FWZ take `d_p = L / |θ(p)|` with `L = ∏_r |θ(r)|`; here `d_p` is the product of `|θ(r)|`
  over the mutable labels `r ≠ p`, the same integer written without a division. The proof
  uses only `d_p |θ(p)| = L` for every `p`, which also covers `p = q` without a case split.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapters 4–5*,
  Lemma 4.4.3.
-/

@[expose] public section

namespace ClusterAlgebras

open MulAction

variable {G : Type*} [Group G] {m n mG nG : ℕ} [MulAction G (Fin m)] {hmn : n ≤ m}
  {B : Matrix (Fin m) (Fin n) ℤ}

/-- If the principal part of a `G`-admissible matrix is skew-symmetric, then for mutable
labels `p, q`, `|θ(q)| b^G_{pq} = -|θ(p)| b^G_{qp}`. -/
theorem card_cols_mul_foldedMatrix (hB : IsGroupAdmissible G hmn B)
    (hskew : ∀ i j : Fin n, B (Fin.castLE hmn i) j = -B (Fin.castLE hmn j) i)
    (θ : OrbitLabelling G m n mG nG) (p q : Fin nG) :
    ((θ.cols hmn q).card : ℤ) * foldedMatrix θ B (Fin.castLE θ.le p) q =
      -(((θ.cols hmn p).card : ℤ) * foldedMatrix θ B (Fin.castLE θ.le q) p) := by
  have key : ∀ p q : Fin nG, ((θ.cols hmn q).card : ℤ) * foldedMatrix θ B (Fin.castLE θ.le p) q
      = ∑ j ∈ θ.cols hmn q, ∑ i ∈ θ.cols hmn p, B (Fin.castLE hmn i) j := by
    intro p q
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [foldedMatrix_apply_eq_sum_of_mem_cols hB θ _ q hj, θ.sum_orbit_eq_sum_cols hmn]
  rw [key, key, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hskew i j

/-- **FWZ's Lemma 4.4.3.** If `B` is `G`-admissible and its principal part is skew-symmetric,
then for any orbit labelling `θ` the folded matrix `B̃ᴳ` is extended skew-symmetrizable. -/
@[cluster_algebras "lem_folded_skew_symmetrizable"]
theorem extSkewSymmetrizable_foldedMatrix (hB : IsGroupAdmissible G hmn B)
    (hskew : ∀ i j : Fin n, B (Fin.castLE hmn i) j = -B (Fin.castLE hmn j) i)
    (θ : OrbitLabelling G m n mG nG) : ExtSkewSymmetrizable θ.le (foldedMatrix θ B) := by
  classical
  set c : Fin nG → ℤ := fun r => ((θ.cols hmn r).card : ℤ) with hc
  have hcpos : ∀ r, 0 < c r := fun r => by simpa [hc] using θ.card_cols_pos hmn r
  refine ⟨fun p => ∏ r ∈ Finset.univ.erase p, c r, fun p => Finset.prod_pos fun r _ => hcpos r,
    fun p q => ?_⟩
  have hd : ∀ p, (∏ r ∈ Finset.univ.erase p, c r) * c p = ∏ r, c r := fun p =>
    Finset.prod_erase_mul _ _ (Finset.mem_univ p)
  simp only [Int.cast_id, Matrix.submatrix_apply, id]
  refine mul_left_cancel₀ (mul_pos (hcpos p) (hcpos q)).ne' ?_
  calc c p * c q * ((∏ r ∈ Finset.univ.erase p, c r) * foldedMatrix θ B (Fin.castLE θ.le p) q)
      = (∏ r, c r) * (c q * foldedMatrix θ B (Fin.castLE θ.le p) q) := by
        rw [← hd p]
        ring
    _ = (∏ r, c r) * -(c p * foldedMatrix θ B (Fin.castLE θ.le q) p) := by
        rw [card_cols_mul_foldedMatrix hB hskew θ p q]
    _ = c p * c q * -((∏ r ∈ Finset.univ.erase q, c r) *
          foldedMatrix θ B (Fin.castLE θ.le q) p) := by
        rw [← hd q]
        ring

end ClusterAlgebras
