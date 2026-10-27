/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.RankTwo.Seeds
public import ClusterAlgebras.Seed
public import Mathlib.Tactic.FieldSimp

/-!
# `𝒜(1, 1)` is `5`-periodic

Let `(z_k)_{k ∈ ℤ}` be the rank-two exchange sequence with `b = c = 1`, so that
`z_{k-1} z_{k+1} = z_k + 1` whenever its terms are nonzero. A direct computation gives
`z₃ = (z₂ + 1) / z₁`, `z₄ = (z₁ + z₂ + 1) / (z₁ z₂)`, `z₅ = (z₁ + 1) / z₂`, `z₆ = z₁` and
`z₇ = z₂`. Since all the exponents equal `1`, the shifted sequence `k ↦ z_{k+5}` satisfies the
same exchange relations and has the same terms of indices `1` and `2`, so it is `(z_k)` itself.
The terms are nonzero as soon as `((z₁, z₂), B)` is a labeled seed, where `B` has rows `(0, 1)`
and `(-1, 0)`; this holds in particular in `ℚ(z₁, z₂)`.

## Main results

* `ClusterAlgebras.rankTwoExp_one_one`: every exponent of `𝒜(1, 1)` is `1`.
* `ClusterAlgebras.rankTwoSeq_one_one_add_five_of_ne_zero`: the sequence is `5`-periodic when
  all its terms are nonzero.
* `ClusterAlgebras.rankTwoSeq_one_one_add_five_of_isLabeledSeed`: the sequence is
  `5`-periodic when `((z₁, z₂), B)` is a labeled seed.
* `ClusterAlgebras.rankTwoSeq_one_one_periodic`: the sequence in `ℚ(z₁, z₂)` is `5`-periodic.

## Implementation notes

The field `ℚ(z₁, z₂)` of rational functions is realized as the fraction field of
`MvPolynomial (Fin 2) ℚ`. The computation only uses that the terms of the sequence are nonzero,
so the statement is also given for any field and any `z₁, z₂` with that property, and in
particular for any labeled seed `((z₁, z₂), B)` over a field of characteristic zero.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {z₁ z₂ : F}

/-- In `𝒜(1, 1)` every exponent of the rank-two exchange sequence is `1`. -/
@[simp]
theorem rankTwoExp_one_one (k : ℤ) : rankTwoExp 1 1 k = 1 := by
  simp [rankTwoExp]

/-- **`𝒜(1, 1)` is `5`-periodic, for nonzero terms.** If every term of the rank-two exchange
sequence with `b = c = 1` is nonzero, then `z_{k+5} = z_k` for every `k ∈ ℤ`. -/
theorem rankTwoSeq_one_one_add_five_of_ne_zero (hne : ∀ k, rankTwoSeq 1 1 z₁ z₂ k ≠ 0)
    (k : ℤ) : rankTwoSeq 1 1 z₁ z₂ (k + 5) = rankTwoSeq 1 1 z₁ z₂ k := by
  set z := rankTwoSeq 1 1 z₁ z₂
  have hstep : ∀ k : ℤ, 2 ≤ k → z (k + 1) = (z k + 1) / z (k - 1) := fun k hk => by
    simpa using rankTwoSeq_succ (b := 1) (c := 1) (z₁ := z₁) (z₂ := z₂) hk
  have h₁ : z 1 = z₁ := rankTwoSeq_one
  have h₂ : z 2 = z₂ := rankTwoSeq_two
  have h₃ : z 3 = (z₂ + 1) / z₁ := by simpa [h₁, h₂] using hstep 2 le_rfl
  have h₄ : z 4 = (z 3 + 1) / z₂ := by simpa [h₂] using hstep 3 (by norm_num)
  have h₅ : z 5 = (z 4 + 1) / z 3 := by simpa using hstep 4 (by norm_num)
  have n₁ : z₁ ≠ 0 := h₁ ▸ hne 1
  have n₂ : z₂ ≠ 0 := h₂ ▸ hne 2
  have n₃ := hne 3
  have e₃ : z 3 * z₁ = z₂ + 1 := by rw [h₃, div_mul_cancel₀ _ n₁]
  have e₄ : z 4 * z₂ = z 3 + 1 := by rw [h₄, div_mul_cancel₀ _ n₂]
  have e₅ : z 5 * z 3 = z 4 + 1 := by rw [h₅, div_mul_cancel₀ _ n₃]
  have h₆ : z 6 = z₁ := by
    rw [show z 6 = (z 5 + 1) / z 4 by simpa using hstep 5 (by norm_num), div_eq_iff (hne 4)]
    apply mul_left_cancel₀ (mul_ne_zero n₂ n₃)
    linear_combination z₂ * e₅ - z₂ * z 4 * e₃ - z₂ * e₄
  have h₇ : z 7 = z₂ := by
    rw [show z 7 = (z 6 + 1) / z 5 by simpa using hstep 6 (by norm_num), h₆, div_eq_iff (hne 5)]
    apply mul_left_cancel₀ n₃
    linear_combination e₃ - z₂ * e₅ - e₄
  exact rankTwoSeq_add_period (fun _ => by simp) hne (by simpa using h₆) (by simpa using h₇) k

/-- **`𝒜(1, 1)` is `5`-periodic.** If `((z₁, z₂), B)` is a labeled seed in `F` over a field of
characteristic zero, where `B` has rows `(0, 1)` and `(-1, 0)`, then the rank-two exchange
sequence with `b = c = 1` satisfies `z_{k+5} = z_k` for every `k ∈ ℤ`. -/
theorem rankTwoSeq_one_one_add_five_of_isLabeledSeed [CharZero K]
    (hS : IsLabeledSeed K le_rfl (⟨![z₁, z₂], !![0, 1; -1, 0]⟩ : SeedData F 2 2)) (k : ℤ) :
    rankTwoSeq 1 1 z₁ z₂ (k + 5) = rankTwoSeq 1 1 z₁ z₂ k :=
  rankTwoSeq_one_one_add_five_of_ne_zero
    (rankTwoSeq_ne_zero_of_isLabeledSeed (b := 1) (c := 1) (by simpa using hS)) k

/-- **`𝒜(1, 1)` is `5`-periodic in `ℚ(z₁, z₂)`.** In the field of rational functions in two
indeterminates `z₁, z₂` over `ℚ`, the rank-two exchange sequence with `b = c = 1` satisfies
`z_{k+5} = z_k` for every `k ∈ ℤ`. -/
@[cluster_algebras "lem_a11_periodic"]
theorem rankTwoSeq_one_one_periodic (k : ℤ) :
    rankTwoSeq 1 1
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 0))
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 1)) (k + 5) =
      rankTwoSeq 1 1
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 0))
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
          (MvPolynomial.X 1)) k := by
  refine rankTwoSeq_one_one_add_five_of_isLabeledSeed (K := ℚ) ?_ k
  have hd : IsSkewSymmetrizingVector
      ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).submatrix (Fin.castLE le_rfl) id) ![1, 1] :=
    ⟨by decide, by decide⟩
  convert isLabeledSeed_genericSeed le_rfl ⟨_, hd⟩ using 1
  refine SeedData.ext ?_ rfl
  ext i
  fin_cases i <;> rfl

end ClusterAlgebras
