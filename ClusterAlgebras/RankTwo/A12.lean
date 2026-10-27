/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.RankTwo.Seeds
public import Mathlib.Tactic.FieldSimp

/-!
# `𝒜(1, 2)` is `6`-periodic

Let `(z_k)_{k ∈ ℤ}` be the rank-two exchange sequence with `b = 1` and `c = 2`, so that
`z_{k+1} = (z_k ^ 2 + 1) / z_{k-1}` for even `k` and `z_{k+1} = (z_k + 1) / z_{k-1}` for odd
`k`. Starting from `z₁, z₂` one computes
`z₃ = (z₂² + 1) / z₁`, `z₄ = (z₂² + z₁ + 1) / (z₁ z₂)`,
`z₅ = (z₁² + z₂² + 2 z₁ + 1) / (z₁ z₂²)`, `z₆ = (z₁ + 1) / z₂`, and then `z₇ = z₁`, `z₈ = z₂`.
When every term is nonzero, the sequence is determined by two consecutive terms and the
exponents `e_k` are unchanged by the even shift `6`, so `z_{k+6} = z_k` for every `k`.

## Main results

* `ClusterAlgebras.rankTwoSeq_one_two_add_six_of_isLabeledSeed`: if `((z₁, z₂), B)` is a labeled
  seed, with `B` the matrix with rows `(0, 1)` and `(-2, 0)`, then `z_{k+6} = z_k`.
* `ClusterAlgebras.rankTwoSeq_one_two_periodic`: in `ℚ(z₁, z₂)`, `z_{k+6} = z_k`.

## Implementation notes

The periodicity of `𝒜(1, 2)` is usually stated in `ℚ(z₁, z₂)`; the computation only uses that
the terms of the sequence are nonzero, which holds whenever `((z₁, z₂), B)` is a labeled seed
over a field of characteristic zero, so the result is first proved in that generality. The field
`ℚ(z₁, z₂)` is `FractionRing (MvPolynomial (Fin 2) ℚ)`, with `z₁, z₂` the images of the
indeterminates.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **The terms `z₇, z₈` of `𝒜(1, 2)`.** If every term of the rank-two exchange sequence with
`b = 1` and `c = 2` is nonzero, then `z₇ = z₁` and `z₈ = z₂`. -/
theorem rankTwoSeq_one_two_seven_eight {z₁ z₂ : F} (hne : ∀ k, rankTwoSeq 1 2 z₁ z₂ k ≠ 0) :
    rankTwoSeq 1 2 z₁ z₂ 7 = z₁ ∧ rankTwoSeq 1 2 z₁ z₂ 8 = z₂ := by
  have hs : ∀ k : ℤ, 2 ≤ k → rankTwoSeq 1 2 z₁ z₂ (k + 1) =
      (rankTwoSeq 1 2 z₁ z₂ k ^ rankTwoExp 1 2 k + 1) / rankTwoSeq 1 2 z₁ z₂ (k - 1) :=
    fun k hk => rankTwoSeq_succ hk
  have h1 := hne 1
  have h2 := hne 2
  simp only [rankTwoSeq_one, rankTwoSeq_two] at h1 h2
  have e3 : rankTwoSeq 1 2 z₁ z₂ 3 = (z₂ ^ 2 + 1) / z₁ := by
    simpa [rankTwoExp] using hs 2 le_rfl
  have n3 : z₂ ^ 2 + 1 ≠ 0 := (div_ne_zero_iff.1 (e3 ▸ hne 3)).1
  have e4 : rankTwoSeq 1 2 z₁ z₂ 4 = (z₂ ^ 2 + z₁ + 1) / (z₁ * z₂) := by
    have := hs 3 (by norm_num)
    norm_num [rankTwoExp, e3] at this
    rw [this]
    field_simp
    ring
  have n4 : z₂ ^ 2 + z₁ + 1 ≠ 0 := (div_ne_zero_iff.1 (e4 ▸ hne 4)).1
  have e5 : rankTwoSeq 1 2 z₁ z₂ 5 = (z₁ ^ 2 + z₂ ^ 2 + 2 * z₁ + 1) / (z₁ * z₂ ^ 2) := by
    have := hs 4 (by norm_num)
    norm_num [rankTwoExp, e3, e4] at this
    rw [this]
    field_simp
    ring
  have n5 : z₁ ^ 2 + z₂ ^ 2 + 2 * z₁ + 1 ≠ 0 := (div_ne_zero_iff.1 (e5 ▸ hne 5)).1
  have e6 : rankTwoSeq 1 2 z₁ z₂ 6 = (z₁ + 1) / z₂ := by
    have := hs 5 (by norm_num)
    norm_num [rankTwoExp, e4, e5] at this
    rw [this]
    field_simp
    ring
  have n6 : z₁ + 1 ≠ 0 := (div_ne_zero_iff.1 (e6 ▸ hne 6)).1
  have e7 : rankTwoSeq 1 2 z₁ z₂ 7 = z₁ := by
    have := hs 6 (by norm_num)
    norm_num [rankTwoExp, e5, e6] at this
    rw [this, div_eq_iff (div_ne_zero n5 (by simp [h1, h2]))]
    field_simp
    ring
  refine ⟨e7, ?_⟩
  have := hs 7 (by norm_num)
  norm_num [rankTwoExp, e6, e7] at this
  rw [this]
  field_simp

/-- **`6`-periodicity of `𝒜(1, 2)` for nonvanishing sequences.** If every term of the rank-two
exchange sequence with `b = 1` and `c = 2` is nonzero, then `z_{k+6} = z_k` for every `k`. -/
theorem rankTwoSeq_one_two_add_six_of_ne_zero {z₁ z₂ : F} (hne : ∀ k, rankTwoSeq 1 2 z₁ z₂ k ≠ 0)
    (k : ℤ) : rankTwoSeq 1 2 z₁ z₂ (k + 6) = rankTwoSeq 1 2 z₁ z₂ k :=
  rankTwoSeq_add_period (rankTwoExp_add_of_even (by decide)) hne
    (rankTwoSeq_one_two_seven_eight hne).1 (rankTwoSeq_one_two_seven_eight hne).2 k

/-- **`6`-periodicity of `𝒜(1, 2)` for a labeled seed.** If `((z₁, z₂), B)` is a labeled seed
in `F` over a field `K` of characteristic zero, with `B` the matrix with rows `(0, 1)` and
`(-2, 0)`, then the rank-two exchange sequence with `b = 1` and `c = 2` satisfies
`z_{k+6} = z_k` for every `k ∈ ℤ`. -/
theorem rankTwoSeq_one_two_add_six_of_isLabeledSeed [CharZero K] {z₁ z₂ : F}
    (hS : IsLabeledSeed K le_rfl
      (⟨![z₁, z₂], !![0, 1; -2, 0]⟩ : SeedData F 2 2)) (k : ℤ) :
    rankTwoSeq 1 2 z₁ z₂ (k + 6) = rankTwoSeq 1 2 z₁ z₂ k :=
  rankTwoSeq_one_two_add_six_of_ne_zero (rankTwoSeq_ne_zero_of_isLabeledSeed hS) k

/-- **`𝒜(1, 2)` is `6`-periodic.** In the field `ℚ(z₁, z₂)` of rational functions in two
indeterminates, the rank-two exchange sequence with `b = 1` and `c = 2` satisfies
`z_{k+6} = z_k` for every `k ∈ ℤ`. -/
@[cluster_algebras "lem_a12_periodic"]
theorem rankTwoSeq_one_two_periodic (k : ℤ) :
    rankTwoSeq 1 2
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 0))
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 1)) (k + 6) =
      rankTwoSeq 1 2
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 0))
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 1)) k := by
  have hB : ExtSkewSymmetrizable le_rfl (!![0, 1; -2, 0] : Matrix (Fin 2) (Fin 2) ℤ) :=
    ⟨![2, 1], by decide, by decide⟩
  have hS := isLabeledSeed_genericSeed le_rfl hB
  refine rankTwoSeq_one_two_add_six_of_isLabeledSeed (K := ℚ) ?_ k
  convert hS using 1
  exact SeedData.ext (funext fun i => by fin_cases i <;> rfl) rfl

end ClusterAlgebras
