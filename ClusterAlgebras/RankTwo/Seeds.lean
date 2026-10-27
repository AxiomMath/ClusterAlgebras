/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.RankTwo.Matrix
public import ClusterAlgebras.RankTwo.Sequence

/-!
# The seeds of a rank-two cluster algebra

Let `B` be the `2 × 2` matrix with rows `(0, b)` and `(-c, 0)`, and let `((z₁, z₂), B)` be a
labeled seed in `F` over a field `K` of characteristic zero. Mutating alternately in the
directions `1` and `2` produces a sequence of labeled seeds `(Σₖ)_{k ∈ ℤ}` with
`Σ₁ = ((z₁, z₂), B)` and `Σ_{k+1} = μ_{ℓ(k)}(Σₖ)`, where `ℓ(k) = 1` for odd `k` and `ℓ(k) = 2`
for even `k`. The matrix of `Σₖ` is `B` for odd `k` and `-B` for even `k`, and the cluster of
`Σₖ` is `(z_k, z_{k+1})` for odd `k` and `(z_{k+1}, z_k)` for even `k`, where `(z_k)` is the
rank-two exchange sequence of `b, c, z₁, z₂`. In particular every `z_k` is an entry of a
labeled seed obtained from `((z₁, z₂), B)` by a sequence of mutations, hence is nonzero.

## Main results

* `ClusterAlgebras.seedMutation_extCluster_zero_of_fin_two`,
  `ClusterAlgebras.seedMutation_extCluster_one_of_fin_two`: mutation of a seed with two entries.
* `ClusterAlgebras.exists_seedMutation_chain`: a two-sided chain of mutations of a labeled seed
  in prescribed directions.
* `ClusterAlgebras.extExchangeMatrix_rankTwoSeeds_eq`: the matrix of `Σₖ`.
* `ClusterAlgebras.cluster_rankTwoSeeds_eq`, `ClusterAlgebras.extCluster_rankTwoSeeds_eq`:
  the cluster of `Σₖ`.
* `ClusterAlgebras.exists_rankTwoSeeds`: the seeds `Σₖ` exist, and each is obtained from `Σ₁`
  by a sequence of mutations.
* `ClusterAlgebras.rankTwoSeq_eq_extCluster_seedMutationSeq`,
  `ClusterAlgebras.rankTwoSeq_ne_zero_of_isLabeledSeed`: every term of the rank-two exchange
  sequence is an entry of a seed mutation-equivalent to `((z₁, z₂), B)`, hence nonzero.

## Implementation notes

Directions are indexed by `Fin 2`, so the directions `1, 2` above are `0, 1` here, and `ℓ(k)`
is `0` for odd `k` and `1` for even `k`. Neither positivity of `b, c` nor the hypothesis that
`((z₁, z₂), B)` is a labeled seed is assumed: the hypothesis that every `Σₖ` is a labeled seed
makes each matrix skew-symmetrizable, which is all that the computation of the matrices needs,
and `Σ₁` is a labeled seed among them. The statements also cover `b = c = 0`, where every
exponent `rankTwoExp b c k` vanishes.
-/

@[expose] public section

namespace ClusterAlgebras

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Mutation

/-- The exchange binomial of a seed with two entries in direction `0`: if `b₀₀ = 0`, then
`M⁺₀ + M⁻₀ = x₁ ^ |b₁₀| + 1`. -/
theorem exchangeMonomialPos_add_exchangeMonomialNeg_zero_of_fin_two {x : Fin 2 → F}
    {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 0 0 = 0) :
    exchangeMonomialPos x M 0 + exchangeMonomialNeg x M 0 = x 1 ^ (M 1 0).natAbs + 1 := by
  rw [exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod, Fin.prod_univ_two,
    Fin.prod_univ_two, h]
  obtain ⟨e, he | he⟩ := Int.eq_nat_or_neg (M 1 0) <;> simp [he, add_comm]

/-- The exchange binomial of a seed with two entries in direction `1`: if `b₁₁ = 0`, then
`M⁺₁ + M⁻₁ = x₀ ^ |b₀₁| + 1`. -/
theorem exchangeMonomialPos_add_exchangeMonomialNeg_one_of_fin_two {x : Fin 2 → F}
    {M : Matrix (Fin 2) (Fin 2) ℤ} (h : M 1 1 = 0) :
    exchangeMonomialPos x M 1 + exchangeMonomialNeg x M 1 = x 0 ^ (M 0 1).natAbs + 1 := by
  rw [exchangeMonomialPos_eq_prod, exchangeMonomialNeg_eq_prod, Fin.prod_univ_two,
    Fin.prod_univ_two, h]
  obtain ⟨e, he | he⟩ := Int.eq_nat_or_neg (M 0 1) <;> simp [he, add_comm]

/-- **Mutation of a seed with two entries in direction `0`.** If `b₀₀ = 0`, the extended
cluster of `μ₀(S)` is `((x₁ ^ |b₁₀| + 1) / x₀, x₁)`. -/
theorem seedMutation_extCluster_zero_of_fin_two {S : SeedData F 2 2}
    (h : S.extExchangeMatrix 0 0 = 0) :
    (seedMutation le_rfl S 0).extCluster =
      ![(S.extCluster 1 ^ (S.extExchangeMatrix 1 0).natAbs + 1) / S.extCluster 0,
        S.extCluster 1] := by
  ext i
  fin_cases i <;>
    simp [seedMutation, exchangeMonomialPos_add_exchangeMonomialNeg_zero_of_fin_two h]

/-- **Mutation of a seed with two entries in direction `1`.** If `b₁₁ = 0`, the extended
cluster of `μ₁(S)` is `(x₀, (x₀ ^ |b₀₁| + 1) / x₁)`. -/
theorem seedMutation_extCluster_one_of_fin_two {S : SeedData F 2 2}
    (h : S.extExchangeMatrix 1 1 = 0) :
    (seedMutation le_rfl S 1).extCluster =
      ![S.extCluster 0,
        (S.extCluster 0 ^ (S.extExchangeMatrix 0 1).natAbs + 1) / S.extCluster 1] := by
  ext i
  fin_cases i <;>
    simp [seedMutation, exchangeMonomialPos_add_exchangeMonomialNeg_one_of_fin_two h]

end Mutation

section Chain

variable [CharZero K] {m n : ℕ}

/-- **A two-sided chain of mutations.** For a labeled seed `S₀` and directions
`ℓ : ℤ → Fin n` there are labeled seeds `(Sₖ)_{k ∈ ℤ}` with `S₁ = S₀` and
`S_{k+1} = μ_{ℓ(k)}(Sₖ)` for every `k`, each obtained from `S₀` by mutation along a
sequence. -/
theorem exists_seedMutation_chain (hmn : n ≤ m) {S₀ : SeedData F m n}
    (hS₀ : IsLabeledSeed K hmn S₀) (ℓ : ℤ → Fin n) :
    ∃ S : ℤ → SeedData F m n, (∀ k, IsLabeledSeed K hmn (S k)) ∧ S 1 = S₀ ∧
      (∀ k, S (k + 1) = seedMutation hmn (S k) (ℓ k)) ∧
      ∀ k, ∃ s : List (Fin n), S k = seedMutationSeq hmn S₀ s := by
  set up : ℕ → List (Fin n) := fun j => (List.range j).map fun i => ℓ (i + 1)
  set down : ℕ → List (Fin n) := fun j => (List.range j).map fun i => ℓ (-i)
  set S : ℤ → SeedData F m n := fun k => if 1 ≤ k then seedMutationSeq hmn S₀ (up (k - 1).toNat)
    else seedMutationSeq hmn S₀ (down (1 - k).toNat)
  have hseq : ∀ k, ∃ s : List (Fin n), S k = seedMutationSeq hmn S₀ s := fun k => by
    by_cases hk : 1 ≤ k
    · exact ⟨_, if_pos hk⟩
    · exact ⟨_, if_neg hk⟩
  have hlab : ∀ k, IsLabeledSeed K hmn (S k) := fun k => by
    obtain ⟨s, hs⟩ := hseq k
    rw [hs]
    exact hS₀.seedMutationSeq hmn s
  refine ⟨S, hlab, by simp [S, up], fun k => ?_, hseq⟩
  rcases le_or_gt 1 k with hk | hk
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨(k - 1).toNat, by omega⟩
    have h1 : S (j + 1) = seedMutationSeq hmn S₀ (up j) := by
      simp only [S, if_pos hk, add_sub_cancel_right, Int.toNat_natCast]
    have h2 : S (j + 1 + 1) = seedMutationSeq hmn S₀ (up (j + 1)) := by
      simp only [S, if_pos (by omega : (1 : ℤ) ≤ j + 1 + 1), add_sub_cancel_right]
      rfl
    rw [h1, h2]
    simp [up, List.range_succ]
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = -j := ⟨(-k).toNat, by omega⟩
    have h1 : S (-j + 1) = seedMutationSeq hmn S₀ (down j) := by
      by_cases hj : j = 0
      · subst hj
        simp [S, up, down]
      · simp only [S, if_neg (by omega : ¬(1 : ℤ) ≤ -j + 1)]
        congr 2
        omega
    have h2 : S (-j) = seedMutationSeq hmn S₀ (down (j + 1)) := by
      simp only [S, if_neg (by omega : ¬(1 : ℤ) ≤ -j)]
      congr 2
      omega
    have h3 : S (-j) = seedMutation hmn (S (-j + 1)) (ℓ (-j)) := by
      rw [h1, h2]
      simp [down, List.range_succ]
    rw [h3, seedMutation_seedMutation hmn (hlab _)]

end Chain

section Seeds

variable {b c : ℕ} {z₁ z₂ : F}

/-- **The matrices along a chain of mutations of a seed with two entries.** If
`(Sₖ)_{k ∈ ℤ}` are labeled seeds with two entries and `S_{k+1} = μ_{ℓ(k)}(Sₖ)` for all `k`,
for any directions `ℓ(k)`, then the matrix of `Sₖ` is that of `S₁` for odd `k` and its
negative for even `k`. -/
theorem extExchangeMatrix_rankTwoSeeds_eq (S : ℤ → SeedData F 2 2)
    (hS : ∀ k, IsLabeledSeed K le_rfl (S k)) (ℓ : ℤ → Fin 2)
    (hstep : ∀ k, S (k + 1) = seedMutation le_rfl (S k) (ℓ k)) (k : ℤ) :
    (S k).extExchangeMatrix =
      if Odd k then (S 1).extExchangeMatrix else -(S 1).extExchangeMatrix := by
  have hneg : ∀ k, (S (k + 1)).extExchangeMatrix = -(S k).extExchangeMatrix := fun k => by
    rw [hstep k]
    exact SkewSymmetrizable.matrixMutation_eq_neg_of_fin_two
      (by simpa [ExtSkewSymmetrizable] using (hS k).2) _
  rcases le_total 1 k with hk | hk
  · induction k, hk using Int.leInduction with
    | base => simp
    | succ n hn ih =>
      rw [hneg n, ih]
      by_cases h : Odd n
      · rw [if_pos h, if_neg (by simp only [Int.odd_iff] at h ⊢; omega)]
      · rw [if_neg h, if_pos (by simp only [Int.odd_iff] at h ⊢; omega), neg_neg]
  · induction k, hk using Int.leInductionDown with
    | base => simp
    | pred n hn ih =>
      rw [← neg_neg (S (n - 1)).extExchangeMatrix, ← hneg (n - 1), sub_add_cancel, ih]
      by_cases h : Odd n
      · rw [if_pos h, if_neg (by simp only [Int.odd_iff] at h ⊢; omega)]
      · rw [if_neg h, if_pos (by simp only [Int.odd_iff] at h ⊢; omega), neg_neg]

/-- The exponent `e_k` is `b` for odd `k`. -/
theorem rankTwoExp_of_odd {k : ℤ} (hk : Odd k) : rankTwoExp b c k = b := by
  simp [rankTwoExp, Int.not_even_iff_odd.2 hk]

/-- The exponent `e_k` is `c` for `k` not odd. -/
theorem rankTwoExp_of_not_odd {k : ℤ} (hk : ¬Odd k) : rankTwoExp b c k = c := by
  simp [rankTwoExp, Int.not_odd_iff_even.1 hk]

/-- **The extended clusters of the seeds of a rank-two cluster algebra.** With the hypotheses
of `cluster_rankTwoSeeds_eq`, the extended cluster of `Sₖ` is `(z_k, z_{k+1})` for odd `k`
and `(z_{k+1}, z_k)` for even `k`. -/
theorem extCluster_rankTwoSeeds_eq [CharZero K] (S : ℤ → SeedData F 2 2)
    (hS : ∀ k, IsLabeledSeed K le_rfl (S k))
    (h1 : S 1 = ⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩)
    (hstep : ∀ k, S (k + 1) = seedMutation le_rfl (S k) (if Odd k then 0 else 1)) (k : ℤ) :
    (S k).extCluster = if Odd k then ![rankTwoSeq b c z₁ z₂ k, rankTwoSeq b c z₁ z₂ (k + 1)]
      else ![rankTwoSeq b c z₁ z₂ (k + 1), rankTwoSeq b c z₁ z₂ k] := by
  set z := rankTwoSeq b c z₁ z₂
  have hM := extExchangeMatrix_rankTwoSeeds_eq S hS _ hstep
  have hent : ∀ k, (S k).extExchangeMatrix 0 0 = 0 ∧ (S k).extExchangeMatrix 1 1 = 0 ∧
      ((S k).extExchangeMatrix 1 0).natAbs = c ∧ ((S k).extExchangeMatrix 0 1).natAbs = b :=
    fun k => by rw [hM k, h1]; split_ifs <;> simp
  have hodd : ∀ n : ℤ, Odd (n + 1) ↔ ¬Odd n := fun n => by simp only [Int.odd_iff]; omega
  rcases le_total 1 k with hk | hk
  · induction k, hk using Int.leInduction with
    | base => simp [h1, z]
    | succ n hn ih =>
      rw [hstep n]
      by_cases h : Odd n
      · rw [if_pos h] at ih ⊢
        rw [seedMutation_extCluster_zero_of_fin_two (hent n).1, ih, (hent n).2.2.1,
          if_neg (by rw [hodd]; exact not_not.2 h)]
        have := rankTwoSeq_succ (b := b) (c := c) (z₁ := z₁) (z₂ := z₂) (k := n + 1) (by omega)
        rw [rankTwoExp_of_not_odd (by rw [hodd]; exact not_not.2 h), add_sub_cancel_right]
          at this
        ext i
        fin_cases i <;> simp [z, this]
      · rw [if_neg h] at ih
        rw [if_neg h] at ⊢
        rw [seedMutation_extCluster_one_of_fin_two (hent n).2.1, ih, (hent n).2.2.2,
          if_pos (by rw [hodd]; exact h)]
        have := rankTwoSeq_succ (b := b) (c := c) (z₁ := z₁) (z₂ := z₂) (k := n + 1) (by omega)
        rw [rankTwoExp_of_odd (by rw [hodd]; exact h), add_sub_cancel_right] at this
        ext i
        fin_cases i <;> simp [z, this]
  · induction k, hk using Int.leInductionDown with
    | base => simp [h1, z]
    | pred n hn ih =>
      have hinv : S (n - 1) = seedMutation le_rfl (S n) (if Odd (n - 1) then 0 else 1) := by
        have := hstep (n - 1)
        rw [sub_add_cancel] at this
        rw [this, seedMutation_seedMutation le_rfl (hS (n - 1))]
      have hodd' : Odd (n - 1) ↔ ¬Odd n := by simp only [Int.odd_iff]; omega
      have hpred := rankTwoSeq_pred (b := b) (c := c) (z₁ := z₁) (z₂ := z₂) hn
      rw [hinv]
      by_cases h : Odd n
      · rw [if_pos h] at ih
        simp only [show ¬Odd (n - 1) by rw [hodd']; exact not_not.2 h, if_false]
        rw [seedMutation_extCluster_one_of_fin_two (hent n).2.1, ih, (hent n).2.2.2]
        rw [rankTwoExp_of_odd h] at hpred
        ext i
        fin_cases i <;> simp [z, hpred]
      · rw [if_neg h] at ih
        simp only [show Odd (n - 1) by rw [hodd']; exact h, if_true]
        rw [seedMutation_extCluster_zero_of_fin_two (hent n).1, ih, (hent n).2.2.1]
        rw [rankTwoExp_of_not_odd h] at hpred
        ext i
        fin_cases i <;> simp [z, hpred]

/-- **The rank-two exchange sequence lists the cluster variables.** Let `B` be the matrix with
rows `(0, b)` and `(-c, 0)`, and let `(Sₖ)_{k ∈ ℤ}` be labeled seeds in `F` over a field `K`
of characteristic zero with `S₁ = ((z₁, z₂), B)` and `S_{k+1} = μ_{ℓ(k)}(Sₖ)`, where
`ℓ(k) = 0` for odd `k` and `ℓ(k) = 1` for even `k`. Then the cluster of `Sₖ` is
`(z_k, z_{k+1})` for odd `k` and `(z_{k+1}, z_k)` for even `k`, where `(z_k)` is the
rank-two exchange sequence of `b, c, z₁, z₂`. -/
@[cluster_algebras "lem_rank_two_seeds"]
theorem cluster_rankTwoSeeds_eq [CharZero K] (S : ℤ → SeedData F 2 2)
    (hS : ∀ k, IsLabeledSeed K le_rfl (S k))
    (h1 : S 1 = ⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩)
    (hstep : ∀ k, S (k + 1) = seedMutation le_rfl (S k) (if Odd k then 0 else 1)) (k : ℤ) :
    cluster le_rfl (S k) = if Odd k then ![rankTwoSeq b c z₁ z₂ k, rankTwoSeq b c z₁ z₂ (k + 1)]
      else ![rankTwoSeq b c z₁ z₂ (k + 1), rankTwoSeq b c z₁ z₂ k] :=
  extCluster_rankTwoSeeds_eq S hS h1 hstep k

/-- **The seeds of a rank-two cluster algebra exist.** For a labeled seed
`S₁ = ((z₁, z₂), B)`, with `B` the matrix with rows `(0, b)` and `(-c, 0)`, there are labeled
seeds `(Sₖ)_{k ∈ ℤ}` with `S_{k+1} = μ_{ℓ(k)}(Sₖ)`, where `ℓ(k) = 0` for odd `k` and
`ℓ(k) = 1` for even `k`, each obtained from `S₁` by mutation along a sequence. -/
theorem exists_rankTwoSeeds [CharZero K]
    (hS : IsLabeledSeed K le_rfl
      (⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩ : SeedData F 2 2)) :
    ∃ S : ℤ → SeedData F 2 2, (∀ k, IsLabeledSeed K le_rfl (S k)) ∧
      S 1 = ⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩ ∧
      (∀ k, S (k + 1) = seedMutation le_rfl (S k) (if Odd k then 0 else 1)) ∧
      ∀ k, ∃ s : List (Fin 2),
        S k = seedMutationSeq le_rfl ⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩ s :=
  exists_seedMutation_chain le_rfl hS _

/-- **Every term of the rank-two exchange sequence is a cluster variable.** If
`((z₁, z₂), B)` is a labeled seed, with `B` the matrix with rows `(0, b)` and `(-c, 0)`, then
every `z_k` is an entry of the extended cluster of a seed obtained from it by mutation along
a sequence. -/
theorem rankTwoSeq_eq_extCluster_seedMutationSeq [CharZero K]
    (hS : IsLabeledSeed K le_rfl
      (⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩ : SeedData F 2 2)) (k : ℤ) :
    ∃ (s : List (Fin 2)) (i : Fin 2), rankTwoSeq b c z₁ z₂ k =
      (seedMutationSeq le_rfl ⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩ s).extCluster i := by
  obtain ⟨S, hlab, h1, hstep, hseq⟩ := exists_rankTwoSeeds hS
  obtain ⟨s, hs⟩ := hseq k
  have h := extCluster_rankTwoSeeds_eq S hlab h1 hstep k
  refine ⟨s, if Odd k then 0 else 1, ?_⟩
  rw [← hs, h]
  split_ifs <;> simp

/-- **The rank-two exchange sequence does not vanish.** If `((z₁, z₂), B)` is a labeled seed,
with `B` the matrix with rows `(0, b)` and `(-c, 0)`, then `z_k ≠ 0` for every `k ∈ ℤ`. -/
theorem rankTwoSeq_ne_zero_of_isLabeledSeed [CharZero K]
    (hS : IsLabeledSeed K le_rfl
      (⟨![z₁, z₂], !![0, (b : ℤ); -(c : ℤ), 0]⟩ : SeedData F 2 2)) (k : ℤ) :
    rankTwoSeq b c z₁ z₂ k ≠ 0 := by
  obtain ⟨s, i, h⟩ := rankTwoSeq_eq_extCluster_seedMutationSeq hS k
  rw [h]
  exact hS.seedMutationSeq_extCluster_ne_zero le_rfl s i

end Seeds

end ClusterAlgebras
