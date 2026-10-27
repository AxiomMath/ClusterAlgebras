/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Defs.SkewSymmetrizable

/-!
# The weights around a closed walk multiply to a perfect square

A remark of FWZ, drawn from skew-symmetrizability: the product of the weights of
`Γ(B)` around any cycle of its underlying graph is a perfect square. The weight of the edge
`(i, j)` is `|b i j * b j i|`, so that is the statement below.

## Design decisions

* The matrix has INTEGER entries, and that is the whole content. Over `ℝ` every nonnegative
  real is a square and each factor here is nonnegative, so the real statement is vacuous;
  what FWZ are saying is that an integer product of integer weights is a perfect
  square integer. `Diagram.weight` is real-valued because `Γ(B)` is built for real matrices,
  so the weight is written out here rather than taken from the diagram.

* Nothing is asked of the walk. The index type is `Fin (m + 1)` with `t + 1` wrapping, which
  makes it closed by construction; consecutive vertices need not be adjacent in `Γ(B)` and
  need not be distinct. A non-adjacent pair contributes `0 = 0 * 0` and does no harm. FWZ's
  cycle is the case where they are adjacent and distinct.

* The cyclic index also does the work in the proof. The `d`-ratios that would telescope along
  a path instead cancel because `t ↦ t + 1` is a bijection of `Fin (m + 1)`, which is
  `Fintype.prod_equiv` and needs no induction.

* No division anywhere: the per-edge identity is `d i * |b i j * b j i| = d j * b j i ^ 2`,
  an identity of integers, and the two products are compared by cancelling the positive
  integer `∏ d`. A proof through `d i / d j` would leave `ℤ`.
-/

@[expose] public section

namespace ClusterAlgebras

/-- **The weights of `Γ(B)` around a closed walk multiply to a perfect square.**

For a skew-symmetrizable integer matrix `B` and any closed walk `v : Fin (m + 1) → Fin n`
(indices taken cyclically), the product of `|B (v t) (v (t + 1)) * B (v (t + 1)) (v t)|` is a
perfect square in `ℤ`. -/
@[cluster_algebras "lem_cycle_weight_square"]
theorem SkewSymmetrizable.isSquare_prod_weight {n m : ℕ} {B : Matrix (Fin n) (Fin n) ℤ}
    (hB : SkewSymmetrizable B) (v : Fin (m + 1) → Fin n) :
    IsSquare (∏ t : Fin (m + 1), |B (v t) (v (t + 1)) * B (v (t + 1)) (v t)|) := by
  obtain ⟨d, hpos, hd⟩ := hB
  have key : ∀ i j : Fin n, d i * |B i j * B j i| = d j * B j i ^ 2 := by
    intro i j
    have h : d i * B i j = -(d j * B j i) := by simpa using hd i j
    have h2 : d i * (B i j * B j i) = -(d j * B j i ^ 2) := by linear_combination B j i * h
    have hle : B i j * B j i ≤ 0 := by
      by_contra hc
      linarith [mul_pos (hpos i) (not_le.mp hc), mul_nonneg (hpos j).le (sq_nonneg (B j i)), h2]
    rw [abs_of_nonpos hle, mul_neg, h2, neg_neg]
  have hDne : (∏ t : Fin (m + 1), d (v t)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun t _ => (hpos (v t)).ne'
  refine ⟨∏ t : Fin (m + 1), B (v (t + 1)) (v t), mul_left_cancel₀ hDne ?_⟩
  calc (∏ t : Fin (m + 1), d (v t)) * ∏ t : Fin (m + 1),
          |B (v t) (v (t + 1)) * B (v (t + 1)) (v t)|
      = ∏ t : Fin (m + 1), d (v t) * |B (v t) (v (t + 1)) * B (v (t + 1)) (v t)| :=
        Finset.prod_mul_distrib.symm
    _ = ∏ t : Fin (m + 1), d (v (t + 1)) * B (v (t + 1)) (v t) ^ 2 :=
        Finset.prod_congr rfl fun t _ => key (v t) (v (t + 1))
    _ = (∏ t : Fin (m + 1), d (v (t + 1))) * ∏ t : Fin (m + 1), B (v (t + 1)) (v t) ^ 2 :=
        Finset.prod_mul_distrib
    _ = (∏ t : Fin (m + 1), d (v t)) * ∏ t : Fin (m + 1), B (v (t + 1)) (v t) ^ 2 := by
        rw [Fintype.prod_equiv (Equiv.addRight (1 : Fin (m + 1)))
          (fun t => d (v (t + 1))) (fun t => d (v t)) fun t => by simp]
    _ = (∏ t : Fin (m + 1), d (v t)) *
          ((∏ t : Fin (m + 1), B (v (t + 1)) (v t)) * ∏ t : Fin (m + 1), B (v (t + 1)) (v t)) := by
        rw [← sq, Finset.prod_pow]

end ClusterAlgebras
