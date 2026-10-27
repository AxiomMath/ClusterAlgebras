/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.YPattern.Defs
public import ClusterAlgebras.RankTwo.Matrix
public import Mathlib.Tactic.FieldSimp

/-!
# The `Y`-pattern of type `A₂` is `10`-periodic

Start from a `Y`-seed `(Y(0), B₀)` of rank `2` with `B₀` the matrix with rows `(0, 1)` and
`(-1, 0)`, and mutate alternately in directions `1` and `2`. Mutating a `2 × 2`
skew-symmetrizable matrix negates it, so `B(t) = (-1)ᵗ B₀`, and at every step the entry of the
exchange matrix governing the mutation is `1`. The mutation rule then reads
`(Y₁, Y₂) ↦ (Y₁⁻¹, Y₁Y₂/(Y₁ + 1))` at even steps and `(Y₁, Y₂) ↦ (Y₁Y₂/(Y₂ + 1), Y₂⁻¹)` at odd
steps, and iterating it ten times returns to the starting `Y`-seed.

## Main results

* `ClusterAlgebras.YSeed.IsMutation.y_self`: the mutated entry is inverted.
* `ClusterAlgebras.YSeed.IsMutation.y_of_exchangeMatrix_eq_one`: when `bₖⱼ = 1`, the entry `j`
  becomes `YₖYⱼ/(Yₖ + 1)`.
* `ClusterAlgebras.YSeed.a2_isMutation_period_ten`: the `Y`-pattern of type `A₂` is
  `10`-periodic.

## Implementation notes

FWZ index the `Y`-seeds by `t ∈ [0, 10]`; here they form a family indexed by `ℕ`,
constrained only by the mutations from `t` to `t + 1` for `t < 10`, which is the same
statement. FWZ's direction `1` is the index `0 : Fin 2`, and direction `2` is `1`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] {n : ℕ}

/-- Under `Y`-seed mutation in direction `k`, the entry `k` is inverted. -/
theorem YSeed.IsMutation.y_self {k : Fin n} {s s' : YSeed F n} (h : YSeed.IsMutation k s s') :
    s'.y k = (s.y k)⁻¹ :=
  (h.2.2.2 k).1 rfl

/-- Under `Y`-seed mutation in direction `k`, if `bₖⱼ = 1` for some `j ≠ k`, then the entry
`j` becomes `YₖYⱼ/(Yₖ + 1)`. -/
theorem YSeed.IsMutation.y_of_exchangeMatrix_eq_one {k j : Fin n} {s s' : YSeed F n}
    (h : YSeed.IsMutation k s s') (hjk : j ≠ k) (hb : s.exchangeMatrix k j = 1) :
    s'.y j = s.y k * s.y j / (s.y k + 1) := by
  have h0 := h.1
  have h1 : s.y k + 1 ≠ 0 := fun h' => h.2.1 (eq_neg_of_add_eq_zero_left h')
  have h1' : 1 + s.y k ≠ 0 := by rwa [add_comm]
  rw [(h.2.2.2 j).2.2 hjk (by rw [hb]; exact zero_le_one), hb, zpow_neg_one]
  field_simp
  ring

/-- **The `Y`-pattern of type `A₂` is `10`-periodic.** Let `B₀` be the `2 × 2` matrix with rows
`(0, 1)` and `(-1, 0)`, and let `(Y(t), B(t))` be `Y`-seeds of rank `2` with `Y(0) = (y₁, y₂)`
and `B(0) = B₀`, such that `(Y(t), B(t))` and `(Y(t + 1), B(t + 1))` are related by `Y`-seed
mutation in direction `1` for even `t` and in direction `2` for odd `t`, for `t < 10`. Then
`Y(10) = Y(0)` and `B(10) = B(0)`. -/
@[cluster_algebras "lem_a2_y_periodic"]
theorem YSeed.a2_isMutation_period_ten {y₁ y₂ : F} (Y : ℕ → YSeed F 2)
    (h0 : (Y 0).y = ![y₁, y₂]) (hB0 : (Y 0).exchangeMatrix = !![0, 1; -1, 0])
    (hstep : ∀ t < 10, YSeed.IsMutation (if Even t then 0 else 1) (Y t) (Y (t + 1))) :
    (Y 10).y = (Y 0).y ∧ (Y 10).exchangeMatrix = (Y 0).exchangeMatrix := by
  have hneg : ∀ t < 10, (Y (t + 1)).exchangeMatrix = -(Y t).exchangeMatrix := fun t ht => by
    rw [(hstep t ht).2.2.1, (Y t).skewSymmetrizable.matrixMutation_eq_neg_of_fin_two]
  have hB : ∀ t < 10, (Y t).exchangeMatrix =
      if Even t then !![0, 1; -1, 0] else -!![0, 1; -1, 0] := by
    intro t ht
    induction t with
    | zero => simpa using hB0
    | succ t ih =>
      rw [hneg t (by omega), ih (by omega)]
      by_cases he : Even t
      · rw [if_pos he, if_neg (by simpa [Nat.even_add_one] using he)]
      · rw [if_neg he, if_pos (by simpa [Nat.even_add_one] using he), neg_neg]
  have ev : ∀ t < 10, Even t → YSeed.IsMutation 0 (Y t) (Y (t + 1)) ∧
      (Y t).exchangeMatrix 0 1 = 1 := fun t ht he => by
    refine ⟨by simpa [he] using hstep t ht, ?_⟩
    rw [hB t ht, if_pos he]; rfl
  have od : ∀ t < 10, ¬ Even t → YSeed.IsMutation 1 (Y t) (Y (t + 1)) ∧
      (Y t).exchangeMatrix 1 0 = 1 := fun t ht he => by
    refine ⟨by simpa [he] using hstep t ht, ?_⟩
    rw [hB t ht, if_neg he]; rfl
  obtain ⟨m0, e0⟩ := ev 0 (by norm_num) (by decide)
  obtain ⟨m1, e1⟩ := od 1 (by norm_num) (by decide)
  obtain ⟨m2, e2⟩ := ev 2 (by norm_num) (by decide)
  obtain ⟨m3, e3⟩ := od 3 (by norm_num) (by decide)
  obtain ⟨m4, e4⟩ := ev 4 (by norm_num) (by decide)
  obtain ⟨m5, e5⟩ := od 5 (by norm_num) (by decide)
  obtain ⟨m6, e6⟩ := ev 6 (by norm_num) (by decide)
  obtain ⟨m7, e7⟩ := od 7 (by norm_num) (by decide)
  obtain ⟨m8, e8⟩ := ev 8 (by norm_num) (by decide)
  obtain ⟨m9, e9⟩ := od 9 (by norm_num) (by decide)
  have a0 : (Y 0).y 0 = y₁ := by rw [h0]; rfl
  have b0 : (Y 0).y 1 = y₂ := by rw [h0]; rfl
  have hy₁ : y₁ ≠ 0 := a0 ▸ m0.1
  have hy₁' : y₁ + 1 ≠ 0 := fun h' => (a0 ▸ m0.2.1) (eq_neg_of_add_eq_zero_left h')
  have a1 : (Y 1).y 0 = y₁⁻¹ := by rw [m0.y_self, a0]
  have b1 : (Y 1).y 1 = y₁ * y₂ / (y₁ + 1) := by
    rw [m0.y_of_exchangeMatrix_eq_one (by decide) e0, a0, b0]
  have hy₂ : y₂ ≠ 0 := by
    have := b1 ▸ m1.1
    rintro rfl
    simp at this
  have hσ : y₁ * y₂ + y₁ + 1 ≠ 0 := by
    have := b1 ▸ m1.2.1
    intro h'
    apply this
    field_simp
    linear_combination h'
  obtain ⟨σ, hs⟩ : ∃ σ, σ = y₁ * y₂ + y₁ + 1 := ⟨_, rfl⟩
  rw [← hs] at hσ
  have c1 : (Y 1).y 1 + 1 = σ / (y₁ + 1) := by rw [b1]; field_simp; rw [hs]; ring
  have a2 : (Y 2).y 0 = y₂ / σ := by
    rw [m1.y_of_exchangeMatrix_eq_one (by decide) e1, c1, a1, b1]; field_simp
  have b2 : (Y 2).y 1 = (y₁ + 1) / (y₁ * y₂) := by
    rw [m1.y_self, b1]; field_simp
  have hy₂' : y₂ + 1 ≠ 0 := by
    have := a2 ▸ m2.2.1
    intro h'
    apply this
    rw [div_eq_iff hσ, hs]
    linear_combination (y₁ + 1) * h'
  have c2 : (Y 2).y 0 + 1 = (y₁ + 1) * (y₂ + 1) / σ := by rw [a2]; field_simp; rw [hs]; ring
  have a3 : (Y 3).y 0 = σ / y₂ := by
    rw [m2.y_self, a2]; field_simp
  have b3 : (Y 3).y 1 = 1 / (y₁ * (y₂ + 1)) := by
    rw [m2.y_of_exchangeMatrix_eq_one (by decide) e2, c2, a2, b2]; field_simp
  have c3 : (Y 3).y 1 + 1 = σ / (y₁ * (y₂ + 1)) := by rw [b3]; field_simp; rw [hs]; ring
  have a4 : (Y 4).y 0 = y₂⁻¹ := by
    rw [m3.y_of_exchangeMatrix_eq_one (by decide) e3, c3, a3, b3]; field_simp
  have b4 : (Y 4).y 1 = y₁ * (y₂ + 1) := by
    rw [m3.y_self, b3]; field_simp
  have c4 : (Y 4).y 0 + 1 = (y₂ + 1) / y₂ := by rw [a4]; field_simp; ring
  have a5 : (Y 5).y 0 = y₂ := by
    rw [m4.y_self, a4]; field_simp
  have b5 : (Y 5).y 1 = y₁ := by
    rw [m4.y_of_exchangeMatrix_eq_one (by decide) e4, c4, a4, b4]; field_simp
  have c5 : (Y 5).y 1 + 1 = y₁ + 1 := by rw [b5]
  have a6 : (Y 6).y 0 = y₁ * y₂ / (y₁ + 1) := by
    rw [m5.y_of_exchangeMatrix_eq_one (by decide) e5, c5, a5, b5]
  have b6 : (Y 6).y 1 = y₁⁻¹ := by
    rw [m5.y_self, b5]
  have c6 : (Y 6).y 0 + 1 = σ / (y₁ + 1) := by rw [a6]; field_simp; rw [hs]; ring
  have a7 : (Y 7).y 0 = (y₁ + 1) / (y₁ * y₂) := by
    rw [m6.y_self, a6]; field_simp
  have b7 : (Y 7).y 1 = y₂ / σ := by
    rw [m6.y_of_exchangeMatrix_eq_one (by decide) e6, c6, a6, b6]; field_simp
  have c7 : (Y 7).y 1 + 1 = (y₁ + 1) * (y₂ + 1) / σ := by rw [b7]; field_simp; rw [hs]; ring
  have a8 : (Y 8).y 0 = 1 / (y₁ * (y₂ + 1)) := by
    rw [m7.y_of_exchangeMatrix_eq_one (by decide) e7, c7, a7, b7]; field_simp
  have b8 : (Y 8).y 1 = σ / y₂ := by
    rw [m7.y_self, b7]; field_simp
  have c8 : (Y 8).y 0 + 1 = σ / (y₁ * (y₂ + 1)) := by rw [a8]; field_simp; rw [hs]; ring
  have a9 : (Y 9).y 0 = y₁ * (y₂ + 1) := by
    rw [m8.y_self, a8]; field_simp
  have b9 : (Y 9).y 1 = y₂⁻¹ := by
    rw [m8.y_of_exchangeMatrix_eq_one (by decide) e8, c8, a8, b8]; field_simp
  have c9 : (Y 9).y 1 + 1 = (y₂ + 1) / y₂ := by rw [b9]; field_simp; ring
  have a10 : (Y 10).y 0 = y₁ := by
    rw [m9.y_of_exchangeMatrix_eq_one (by decide) e9, c9, a9, b9]; field_simp
  have b10 : (Y 10).y 1 = y₂ := by
    rw [m9.y_self, b9]; field_simp
  refine ⟨?_, ?_⟩
  · ext j
    fin_cases j
    · exact a10.trans a0.symm
    · exact b10.trans b0.symm
  · rw [hneg 9 (by norm_num), hB 9 (by norm_num), if_neg (by decide), neg_neg, hB0]

end ClusterAlgebras
