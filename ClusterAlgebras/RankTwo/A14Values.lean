/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.RankTwo.Sequence
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The values of `𝒜(1, 4)` at `z₁ = z₂ = 1`

Let `(z_k)_{k ∈ ℤ}` be the rank-two exchange sequence with `b = 1`, `c = 4` and
`z₁ = z₂ = 1`, in a linearly ordered field. Writing `a_j = z_{2j}` and `b_j = z_{2j+1}`, the
recursion reads `a_{j+1} = (b_j + 1) / a_j` and `b_{j+1} = (a_{j+1} ^ 4 + 1) / b_j`, with
`a_1 = 1` and `b_1 = 2`. An induction shows `a_j > 0` and `b_j ≥ a_j ^ 2`, whence
`a_{j+1} > a_j`: every term of positive index is positive, and the terms of even positive
index strictly increase.

## Main statements

* `ClusterAlgebras.rankTwoSeq_one_four_pos`: `z_k > 0` for every `k ≥ 1`.
* `ClusterAlgebras.rankTwoSeq_one_four_even_lt`: `z_{2j} < z_{2j+2}` for every `j ≥ 1`.

## Implementation notes

FWZ work over `ℚ`; the argument uses only the order and field structure, so the
statements are made for any linearly ordered field.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F]

/-- In `𝒜(1, 4)`, the exponent at an even index is `4`. -/
theorem rankTwoExp_one_four_two_mul_add_two (j : ℤ) : rankTwoExp 1 4 (2 * j + 2) = 4 := by
  simp [rankTwoExp]

/-- In `𝒜(1, 4)`, the exponent at an odd index is `1`. -/
theorem rankTwoExp_one_four_two_mul_add_one (j : ℤ) : rankTwoExp 1 4 (2 * j + 1) = 1 := by
  simp [rankTwoExp]

/-- In `𝒜(1, 4)` at `z₁ = z₂ = 1`: `z_{2j+4} = (z_{2j+3} + 1) / z_{2j+2}` for `j ≥ 0`. -/
theorem rankTwoSeq_one_four_even_succ {j : ℤ} (hj : 0 ≤ j) :
    rankTwoSeq 1 4 (1 : F) 1 (2 * j + 4) =
      (rankTwoSeq 1 4 (1 : F) 1 (2 * j + 3) + 1) / rankTwoSeq 1 4 (1 : F) 1 (2 * j + 2) := by
  have h := rankTwoSeq_succ (b := 1) (c := 4) (z₁ := (1 : F)) (z₂ := 1)
    (k := 2 * (j + 1) + 1) (by omega)
  rw [rankTwoExp_one_four_two_mul_add_one, pow_one] at h
  rw [show 2 * j + 4 = 2 * (j + 1) + 1 + 1 by ring, h, show 2 * (j + 1) + 1 - 1 = 2 * j + 2 by
    ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]

/-- In `𝒜(1, 4)` at `z₁ = z₂ = 1`: `z_{2j+3} = (z_{2j+2} ^ 4 + 1) / z_{2j+1}` for `j ≥ 0`. -/
theorem rankTwoSeq_one_four_odd_succ {j : ℤ} (hj : 0 ≤ j) :
    rankTwoSeq 1 4 (1 : F) 1 (2 * j + 3) =
      (rankTwoSeq 1 4 (1 : F) 1 (2 * j + 2) ^ 4 + 1) / rankTwoSeq 1 4 (1 : F) 1 (2 * j + 1) := by
  have h := rankTwoSeq_succ (b := 1) (c := 4) (z₁ := (1 : F)) (z₂ := 1)
    (k := 2 * j + 2) (by omega)
  rw [rankTwoExp_one_four_two_mul_add_two] at h
  rw [show 2 * j + 3 = 2 * j + 2 + 1 by ring, h, show 2 * j + 2 - 1 = 2 * j + 1 by ring]

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- The induction invariant for `𝒜(1, 4)` at `z₁ = z₂ = 1`: for `j ≥ 0`, `z_{2j+2} > 0` and
`z_{2j+3} ≥ z_{2j+2} ^ 2`. -/
theorem rankTwoSeq_one_four_invariant {j : ℤ} (hj : 0 ≤ j) :
    0 < rankTwoSeq 1 4 (1 : F) 1 (2 * j + 2) ∧
      rankTwoSeq 1 4 (1 : F) 1 (2 * j + 2) ^ 2 ≤ rankTwoSeq 1 4 (1 : F) 1 (2 * j + 3) := by
  induction j, hj using Int.leInduction with
  | base =>
    have h3 := rankTwoSeq_one_four_odd_succ (F := F) (j := 0) le_rfl
    norm_num at h3 ⊢
    rw [h3]
    norm_num
  | succ j hj ih =>
    obtain ⟨ha, hb⟩ := ih
    have ha' := rankTwoSeq_one_four_even_succ (F := F) hj
    have hb' := rankTwoSeq_one_four_odd_succ (F := F) (j := j + 1) (by omega)
    set a := rankTwoSeq 1 4 (1 : F) 1 (2 * j + 2)
    set b := rankTwoSeq 1 4 (1 : F) 1 (2 * j + 3)
    have hb0 : 0 < b := lt_of_lt_of_le (pow_pos ha 2) hb
    rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show 2 * (j + 1) + 3 = 2 * j + 5 by ring,
      show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at hb'
    rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring, show 2 * (j + 1) + 3 = 2 * j + 5 by ring]
    rw [hb']
    set a' := rankTwoSeq 1 4 (1 : F) 1 (2 * j + 4)
    have ha'pos : 0 < a' := by rw [ha']; positivity
    have hgt : a < a' := by
      rw [ha', lt_div_iff₀ ha]
      nlinarith
    refine ⟨ha'pos, ?_⟩
    rw [le_div_iff₀ hb0]
    have hb_eq : b = a * a' - 1 := by
      rw [ha']; field_simp; ring
    rw [hb_eq]
    have h1 : 0 ≤ a' ^ 3 * (a' - a) := by
      have := sub_pos.mpr hgt
      positivity
    nlinarith [sq_nonneg a']

/-- **The terms of `𝒜(1, 4)` at `z₁ = z₂ = 1` are positive.** In the rank-two exchange
sequence with `b = 1`, `c = 4` and `z₁ = z₂ = 1` over a linearly ordered field, `z_k > 0` for
every `k ≥ 1`. -/
@[cluster_algebras "lem_a14_values"]
theorem rankTwoSeq_one_four_pos {k : ℤ} (hk : 1 ≤ k) : 0 < rankTwoSeq 1 4 (1 : F) 1 k := by
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by ring⟩
    have := (rankTwoSeq_one_four_invariant (F := F) (j := i) (by omega)).1
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring]
  · rcases eq_or_lt_of_le hk with h | h
    · rw [← h]; simp
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by ring⟩
    obtain ⟨ha, hb⟩ := rankTwoSeq_one_four_invariant (F := F) (j := i) (by omega)
    rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
    exact lt_of_lt_of_le (pow_pos ha 2) hb

/-- **The even terms of `𝒜(1, 4)` at `z₁ = z₂ = 1` increase.** In the rank-two exchange
sequence with `b = 1`, `c = 4` and `z₁ = z₂ = 1` over a linearly ordered field,
`z_{2j} < z_{2j+2}` for every `j ≥ 1`. -/
@[cluster_algebras "lem_a14_values"]
theorem rankTwoSeq_one_four_even_lt {j : ℤ} (hj : 1 ≤ j) :
    rankTwoSeq 1 4 (1 : F) 1 (2 * j) < rankTwoSeq 1 4 (1 : F) 1 (2 * j + 2) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by ring⟩
  obtain ⟨ha, hb⟩ := rankTwoSeq_one_four_invariant (F := F) (j := i) (by omega)
  rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 + 2 = 2 * i + 4 by ring,
    rankTwoSeq_one_four_even_succ (by omega), lt_div_iff₀ ha]
  nlinarith

end ClusterAlgebras
