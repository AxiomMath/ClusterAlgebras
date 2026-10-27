/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Laurent.Expansion
public import ClusterAlgebras.LaurentPhenomenon.Laurent
public import ClusterAlgebras.RankTwo.A14Values
public import ClusterAlgebras.RankTwo.Seeds

/-!
# The exchange sequence of `𝒜(1, 4)` is not periodic

Let `(z_k)_{k ∈ ℤ}` be the rank-two exchange sequence with `b = 1` and `c = 4` in the field
`ℚ(z₁, z₂)` of rational functions in two indeterminates. Then no shift `p ≥ 1` satisfies
`z_{k+p} = z_k` for all `k`.

Let `(w_k)` be the exchange sequence in `ℚ` with `w₁ = w₂ = 1`. The pair `(z₁, z₂)` with the
matrix `B` with rows `(0, 1)` and `(-4, 0)` is a labeled seed, and every `z_k` is an entry of a
seed obtained from it by mutations, hence lies in `ℤ[z₁^{±1}, z₂^{±1}]` by the Laurent
phenomenon. The ring homomorphism `φ : ℤ[z₁^{±1}, z₂^{±1}] → ℚ` with `φ(z₁) = φ(z₂) = 1`
respects the exchange relations, and since `w_k > 0` for `k ≥ 1`, induction gives
`φ(z_k) = w_k` for `k ≥ 1`. A period `p` would give `w_{2+2p} = w₂`, whereas the terms of even
positive index of `(w_k)` strictly increase.

## Main results

* `ClusterAlgebras.rankTwoSeq_one_four_not_periodic_of_isLabeledSeed`: the exchange sequence
  of `𝒜(1, 4)` is not periodic, for any labeled seed `((z₁, z₂), B)` over a field of
  characteristic zero.
* `ClusterAlgebras.rankTwoSeq_one_four_not_periodic`: the exchange sequence of `𝒜(1, 4)` in
  `ℚ(z₁, z₂)` is not periodic.

## Implementation notes

The argument uses only that `((z₁, z₂), B)` is a labeled seed over a field of characteristic
zero, so the result is first proved in that generality and then specialized to `ℚ(z₁, z₂)`.
The field `ℚ(z₁, z₂)` is `FractionRing (MvPolynomial (Fin 2) ℚ)`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- For a labeled seed `((z₁, z₂), B)` over a field of characteristic zero, the exchange
sequence of `𝒜(b, c)` specializes to the one at `z₁ = z₂ = 1` in `ℚ`: there is a ring
homomorphism from `ℤ[z₁^{±1}, z₂^{±1}]` to `ℚ` sending `z_k` to `w_k` for every `k ≥ 1`,
provided the `w_k` with `k ≥ 1` are nonzero. -/
private theorem exists_ringHom_laurentSubring_rankTwoSeq [CharZero K] {b c : ℕ} {z₁ z₂ : F}
    (hS : IsLabeledSeed K le_rfl
      (⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩ : SeedData F 2 2))
    (hw : ∀ k, 1 ≤ k → rankTwoSeq b c (1 : ℚ) 1 k ≠ 0) :
    ∃ (hmem : ∀ k, rankTwoSeq b c z₁ z₂ k ∈ laurentSubring ![z₁, z₂])
      (φ : laurentSubring ![z₁, z₂] →+* ℚ),
      ∀ k, 1 ≤ k → φ ⟨rankTwoSeq b c z₁ z₂ k, hmem k⟩ = rankTwoSeq b c (1 : ℚ) 1 k := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hmem : ∀ k, rankTwoSeq b c z₁ z₂ k ∈ laurentSubring ![z₁, z₂] := fun k => by
    obtain ⟨s, i, h⟩ := rankTwoSeq_eq_extCluster_seedMutationSeq hS k
    rw [h]
    exact hS.seedMutationSeq_extCluster_mem_laurentSubring le_rfl s i
  have hind : AlgebraicIndependent ℚ ![z₁, z₂] :=
    hS.1.1.restrictScalars (algebraMap ℚ K).injective
  obtain ⟨φ, hφ⟩ := exists_ringHom_laurentSubring hind (fun _ => (1 : ℚˣ))
  refine ⟨hmem, φ, ?_⟩
  set v : ℤ → ℚ := fun k => φ ⟨rankTwoSeq b c z₁ z₂ k, hmem k⟩ with hv
  have hne := rankTwoSeq_ne_zero_of_isLabeledSeed hS
  have hrel : ∀ k, v (k - 1) * v (k + 1) = v k ^ rankTwoExp b c k + 1 := fun k => by
    have h : (⟨rankTwoSeq b c z₁ z₂ (k - 1), hmem _⟩ : laurentSubring ![z₁, z₂]) *
        ⟨rankTwoSeq b c z₁ z₂ (k + 1), hmem _⟩ =
        ⟨rankTwoSeq b c z₁ z₂ k, hmem _⟩ ^ rankTwoExp b c k + 1 :=
      Subtype.ext (by push_cast; exact rankTwoSeq_mul_rankTwoSeq hne k)
    have := congrArg φ h
    rw [map_mul, map_add, map_pow, map_one] at this
    exact this
  have h1 : v 1 = 1 := by
    simpa [hv] using hφ 0
  have h2 : v 2 = 1 := by
    simpa [hv] using hφ 1
  have key : ∀ n : ℕ, v (n + 1) = rankTwoSeq b c (1 : ℚ) 1 (n + 1) ∧
      v (n + 2) = rankTwoSeq b c (1 : ℚ) 1 (n + 2) := by
    intro n
    induction n with
    | zero => simp [h1, h2]
    | succ n ih =>
      refine ⟨by push_cast; rw [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num]; exact ih.2, ?_⟩
      have hr := hrel (n + 2)
      have hz := rankTwoSeq_succ (b := b) (c := c) (z₁ := (1 : ℚ)) (z₂ := 1)
        (k := (n : ℤ) + 2) (by omega)
      rw [show (n : ℤ) + 2 - 1 = n + 1 by omega] at hr hz
      push_cast
      rw [show (n : ℤ) + 1 + 2 = n + 2 + 1 by omega, hz, ← ih.1, ← ih.2, ← hr,
        mul_div_cancel_left₀ _ (ih.1 ▸ hw _ (by omega))]
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨(k - 1).toNat, by omega⟩
  exact (key n).1

/-- In `𝒜(1, 4)` at `z₁ = z₂ = 1`, the terms of even index `≥ 2` strictly increase from `z₂`:
`z₂ < z_{2j}` for every `j ≥ 2`. -/
private theorem rankTwoSeq_one_four_two_lt_even {L : Type*} [Field L] [LinearOrder L]
    [IsStrictOrderedRing L] {j : ℤ} (hj : 2 ≤ j) :
    rankTwoSeq 1 4 (1 : L) 1 2 < rankTwoSeq 1 4 (1 : L) 1 (2 * j) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n + 2 := ⟨(j - 2).toNat, by omega⟩
  induction n with
  | zero =>
    simpa using rankTwoSeq_one_four_even_lt (F := L) (j := 1) le_rfl
  | succ n ih =>
    refine ih (by omega) |>.trans ?_
    have h := rankTwoSeq_one_four_even_lt (F := L) (j := (n : ℤ) + 2) (by omega)
    rwa [show 2 * ((n : ℤ) + 2) + 2 = 2 * (((n + 1 : ℕ) : ℤ) + 2) by push_cast; ring] at h

/-- **`𝒜(1, 4)` is not periodic**, for any labeled seed. If `((z₁, z₂), B)` with `B` the
matrix with rows `(0, 1)` and `(-4, 0)` is a labeled seed over a field of characteristic zero,
then no `p ≥ 1` satisfies `z_{k+p} = z_k` for every `k ∈ ℤ`. -/
theorem rankTwoSeq_one_four_not_periodic_of_isLabeledSeed [CharZero K] {z₁ z₂ : F}
    (hS : IsLabeledSeed K le_rfl
      (⟨![z₁, z₂], !![0, ((1 : ℕ) : ℤ); -((4 : ℕ) : ℤ), 0]⟩ : SeedData F 2 2)) :
    ¬ ∃ p : ℤ, 1 ≤ p ∧ ∀ k, rankTwoSeq 1 4 z₁ z₂ (k + p) = rankTwoSeq 1 4 z₁ z₂ k := by
  rintro ⟨p, hp, hper⟩
  obtain ⟨hmem, φ, hφ⟩ := exists_ringHom_laurentSubring_rankTwoSeq hS
    (fun k hk => (rankTwoSeq_one_four_pos hk).ne')
  have hz : rankTwoSeq 1 4 z₁ z₂ (2 * (p + 1)) = rankTwoSeq 1 4 z₁ z₂ 2 := by
    rw [show 2 * (p + 1) = 2 + p + p by ring, hper, hper]
  have h : rankTwoSeq 1 4 (1 : ℚ) 1 (2 * (p + 1)) = rankTwoSeq 1 4 (1 : ℚ) 1 2 := by
    rw [← hφ _ (by omega), ← hφ 2 (by norm_num)]
    exact congrArg φ (Subtype.ext hz)
  exact (rankTwoSeq_one_four_two_lt_even (L := ℚ) (j := p + 1) (by omega)).ne' h

/-- **`𝒜(1, 4)` is not periodic.** In the field `ℚ(z₁, z₂)` of rational functions in two
indeterminates, the rank-two exchange sequence with `b = 1` and `c = 4` admits no `p ≥ 1` with
`z_{k+p} = z_k` for every `k ∈ ℤ`. -/
@[cluster_algebras "lem_a14_not_periodic"]
theorem rankTwoSeq_one_four_not_periodic :
    ¬ ∃ p : ℤ, 1 ≤ p ∧ ∀ k,
      rankTwoSeq 1 4
          (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
            (MvPolynomial.X 0))
          (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
            (MvPolynomial.X 1)) (k + p) =
        rankTwoSeq 1 4
          (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
            (MvPolynomial.X 0))
          (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
            (MvPolynomial.X 1)) k := by
  set B : Matrix (Fin 2) (Fin 2) ℤ := !![0, ((1 : ℕ) : ℤ); -((4 : ℕ) : ℤ), 0]
  have hB : ExtSkewSymmetrizable le_rfl B :=
    ⟨![4, 1], fun i => by fin_cases i <;> simp, fun i j => by
      fin_cases i <;> fin_cases j <;> simp [B]⟩
  have hseed : (⟨![algebraMap (MvPolynomial (Fin 2) ℚ) _ (MvPolynomial.X 0),
      algebraMap (MvPolynomial (Fin 2) ℚ) _ (MvPolynomial.X 1)], B⟩ :
      SeedData (FractionRing (MvPolynomial (Fin 2) ℚ)) 2 2) = genericSeed B :=
    SeedData.ext (funext fun i => by fin_cases i <;> rfl) rfl
  exact rankTwoSeq_one_four_not_periodic_of_isLabeledSeed (K := ℚ)
    (hseed ▸ isLabeledSeed_genericSeed le_rfl hB)

end ClusterAlgebras
