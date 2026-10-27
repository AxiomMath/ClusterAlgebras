/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.MarkovQuiver
public import ClusterAlgebras.ExchangeMatrix
public import ClusterAlgebras.Seed

/-!
# The Markov seed pattern

The Markov matrix `B_M` is the exchange matrix of the Markov quiver under the identity
labelling: `b_{ij} = 2` if `j ≡ i + 1 (mod 3)`, `b_{ij} = -2` if `j ≡ i - 1 (mod 3)`, and
`b_{ii} = 0`. Mutation in any direction negates `±B_M`, so along any mutation sequence the
matrix stays `±B_M`, and every exchange relation reads `x_k x'_k = x_i² + x_j²`, where
`{i, j}` is the complement of `k`. From this the quantity
`(x₁² + x₂² + x₃²) / (x₁ x₂ x₃)` is a mutation invariant of the seed pattern: it is the
invariant behind the Markov equation `a₁² + a₂² + a₃² = 3 a₁ a₂ a₃`.

[FWZ] indexes by `[1, 3]`; here the indices are `Fin 3`, so index `i` of [FWZ] is Lean index
`i - 1`. The complement `{i, j}` of `k` is written `{k + 1, k + 2}`, computed in `Fin 3`.

## Main definitions

* `ClusterAlgebras.markovLabelling`: the identity labelling of the Markov quiver.
* `ClusterAlgebras.markovMatrix`: the Markov matrix `B_M`.

## Main results

* `ClusterAlgebras.markovMatrix_eq`: the entries of `B_M`.
* `ClusterAlgebras.matrixMutation_smul_markovMatrix`: `μ_k(ε B_M) = -ε B_M` for `ε = ±1`.
* `ClusterAlgebras.seedMutation_extCluster_self_of_markov`: the exchange relations.
* `ClusterAlgebras.IsLabeledSeed.markov_invariant`: the mutation invariant.

## Implementation notes

The exchange relation holds for any seed data whose matrix is `±B_M`, labeled seed or not,
because seed mutation is defined on all seed data; the hypothesis that the seed is labeled is
dropped there. The invariant needs it, to keep every entry of every extended cluster
nonzero.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras*,
  Chapter 3, §3.4.
-/

@[expose] public section

namespace ClusterAlgebras

/-- The **identity labelling** of the Markov quiver: vertex `i` gets index `i`. The quiver
has no frozen vertices, so all three indices are mutable. -/
@[cluster_algebras "def_markov_matrix"]
def markovLabelling : Labelling markovQuiver 3 3 where
  equiv := Equiv.refl _
  le := le_rfl
  mem_frozen_iff i := by
    simp only [markovQuiver, Finset.notMem_empty, false_iff, not_le]
    exact i.isLt

/-- The **Markov matrix** `B_M`: the extended exchange matrix of the Markov quiver under its
identity labelling. -/
@[cluster_algebras "def_markov_matrix"]
def markovMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  extExchangeMatrix markovQuiver markovLabelling

/-- The entries of the Markov matrix: `b_{ij} = 2` if `j = i + 1`, `-2` if `j = i - 1`, and
`0` on the diagonal, the indices taken in `Fin 3`. -/
theorem markovMatrix_eq : markovMatrix = !![0, 2, -2; -2, 0, 2; 2, -2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **Mutation negates the Markov matrix**: for `ε = ±1` and every direction `k`,
`μ_k(ε B_M) = -ε B_M`. -/
@[cluster_algebras "lem_markov_matrix_mutation"]
theorem matrixMutation_smul_markovMatrix {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (k : Fin 3) :
    matrixMutation le_rfl (ε • markovMatrix) k = -(ε • markovMatrix) := by
  rw [markovMatrix_eq]
  rcases hε with rfl | rfl <;> fin_cases k <;> decide

variable {F : Type*} [Field F]

/-- **The exchange relations of the Markov seed pattern.** If the matrix of `S` is `ε B_M`
with `ε = ±1`, the entry in position `k` of the extended cluster of `μ_k(S)` is
`(x_{k+1}² + x_{k+2}²) / x_k`, where `{k + 1, k + 2}` is the complement of `k` in `Fin 3`. -/
@[cluster_algebras "lem_markov_exchange_relation"]
theorem seedMutation_extCluster_self_of_markov {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {S : SeedData F 3 3} (hS : S.extExchangeMatrix = ε • markovMatrix) (k : Fin 3) :
    (seedMutation le_rfl S k).extCluster k =
      (S.extCluster (k + 1) ^ 2 + S.extCluster (k + 2) ^ 2) / S.extCluster k := by
  simp only [seedMutation, Fin.castLE_refl, Function.update_self, exchangeMonomialPos_eq_prod,
    exchangeMonomialNeg_eq_prod, Fin.prod_univ_three, hS, markovMatrix_eq]
  rcases hε with rfl | rfl <;> fin_cases k <;> simp <;> ring

/-- One mutation of a seed with matrix `ε B_M` gives a seed with matrix `-ε B_M`. -/
theorem seedMutation_extExchangeMatrix_of_markov {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {S : SeedData F 3 3} (hS : S.extExchangeMatrix = ε • markovMatrix) (k : Fin 3) :
    (seedMutation le_rfl S k).extExchangeMatrix = (-ε) • markovMatrix := by
  rw [seedMutation, hS, matrixMutation_smul_markovMatrix hε, neg_smul]

/-- Along any mutation sequence the matrix of a seed with matrix `ε B_M` is
`(-1)^d ε B_M`, where `d` is the length of the sequence; in particular it is `±B_M`. -/
theorem seedMutationSeq_extExchangeMatrix_of_markov {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {S : SeedData F 3 3} (hS : S.extExchangeMatrix = ε • markovMatrix) (s : List (Fin 3)) :
    (seedMutationSeq le_rfl S s).extExchangeMatrix = ((-1) ^ s.length * ε) • markovMatrix := by
  induction s generalizing S ε with
  | nil => simpa using hS
  | cons k s ih =>
    rw [seedMutationSeq_cons, ih (ε := -ε) (by omega)
      (seedMutation_extExchangeMatrix_of_markov hε hS k), List.length_cons, pow_succ]
    ring_nf

/-- Along any mutation sequence the matrix of a seed with matrix `±B_M` stays `±B_M`. -/
theorem seedMutationSeq_extExchangeMatrix_eq_markovMatrix_or_neg {S : SeedData F 3 3}
    (hS : S.extExchangeMatrix = markovMatrix ∨ S.extExchangeMatrix = -markovMatrix)
    (s : List (Fin 3)) :
    (seedMutationSeq le_rfl S s).extExchangeMatrix = markovMatrix ∨
      (seedMutationSeq le_rfl S s).extExchangeMatrix = -markovMatrix := by
  obtain ⟨ε, hε, hSε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ S.extExchangeMatrix = ε • markovMatrix := by
    rcases hS with h | h
    · exact ⟨1, .inl rfl, by simpa using h⟩
    · exact ⟨-1, .inr rfl, by simpa using h⟩
  rw [seedMutationSeq_extExchangeMatrix_of_markov hε hSε]
  rcases neg_one_pow_eq_or ℤ s.length with h | h <;> rcases hε with rfl | rfl <;> simp [h]

/-- The extended cluster after one mutation of a seed with matrix `ε B_M`: the entry in
position `k` becomes `(x_{k+1}² + x_{k+2}²) / x_k`, the others are kept. -/
theorem seedMutation_extCluster_of_markov {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {S : SeedData F 3 3} (hS : S.extExchangeMatrix = ε • markovMatrix) (k : Fin 3) :
    (seedMutation le_rfl S k).extCluster = Function.update S.extCluster k
      ((S.extCluster (k + 1) ^ 2 + S.extCluster (k + 2) ^ 2) / S.extCluster k) := by
  ext i
  rcases eq_or_ne i k with rfl | hi
  · rw [seedMutation_extCluster_self_of_markov hε hS, Function.update_self]
  · rw [Function.update_of_ne hi]
    exact Function.update_of_ne hi _ _

/-- One mutation of a seed with matrix `ε B_M` preserves `(x₀² + x₁² + x₂²) / (x₀ x₁ x₂)`,
provided every entry before and after is nonzero. -/
theorem seedMutation_markov_invariant {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {S : SeedData F 3 3}
    (hS : S.extExchangeMatrix = ε • markovMatrix) (k : Fin 3) (hx : ∀ i, S.extCluster i ≠ 0)
    (hyk : (seedMutation le_rfl S k).extCluster k ≠ 0) :
    ((seedMutation le_rfl S k).extCluster 0 ^ 2 + (seedMutation le_rfl S k).extCluster 1 ^ 2 +
        (seedMutation le_rfl S k).extCluster 2 ^ 2) /
      ((seedMutation le_rfl S k).extCluster 0 * (seedMutation le_rfl S k).extCluster 1 *
        (seedMutation le_rfl S k).extCluster 2) =
      (S.extCluster 0 ^ 2 + S.extCluster 1 ^ 2 + S.extCluster 2 ^ 2) /
        (S.extCluster 0 * S.extCluster 1 * S.extCluster 2) := by
  rw [seedMutation_extCluster_of_markov hε hS] at hyk ⊢
  rw [Function.update_self] at hyk
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have hsum := (div_ne_zero_iff.1 hyk).1
  fin_cases k <;> simp at hsum ⊢ <;> field_simp <;> ring

variable {K : Type*} [Field K] [CharZero K] [Algebra K F]

/-- **A mutation invariant of the Markov seed pattern**, for a labeled seed with
matrix `ε B_M`, where `ε = ±1`: along every mutation sequence,
`(y₀² + y₁² + y₂²) / (y₀ y₁ y₂)` is unchanged. -/
theorem IsLabeledSeed.markov_invariant_of_smul {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {S : SeedData F 3 3} (hS : IsLabeledSeed K le_rfl S)
    (hB : S.extExchangeMatrix = ε • markovMatrix) (s : List (Fin 3)) :
    ((ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 0 ^ 2 +
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 1 ^ 2 +
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 2 ^ 2) /
      ((ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 0 *
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 1 *
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 2) =
      (S.extCluster 0 ^ 2 + S.extCluster 1 ^ 2 + S.extCluster 2 ^ 2) /
        (S.extCluster 0 * S.extCluster 1 * S.extCluster 2) := by
  induction s generalizing S ε with
  | nil => rfl
  | cons k s ih =>
    refine (ih (by omega) (hS.seedMutation le_rfl k)
      (seedMutation_extExchangeMatrix_of_markov hε hB k)).trans ?_
    exact seedMutation_markov_invariant hε hB k
      (hS.seedMutationSeq_extCluster_ne_zero le_rfl [])
      (hS.seedMutationSeq_extCluster_ne_zero le_rfl [k] k)

/-- **A mutation invariant of the Markov seed pattern.** For a labeled seed `(x̃, B_M)` and
every mutation sequence `s`, the extended cluster `y` of `μ_s(x̃, B_M)` satisfies
`(y₀² + y₁² + y₂²) / (y₀ y₁ y₂) = (x₀² + x₁² + x₂²) / (x₀ x₁ x₂)`. -/
@[cluster_algebras "lem_markov_invariant"]
theorem IsLabeledSeed.markov_invariant {S : SeedData F 3 3} (hS : IsLabeledSeed K le_rfl S)
    (hB : S.extExchangeMatrix = markovMatrix) (s : List (Fin 3)) :
    ((ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 0 ^ 2 +
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 1 ^ 2 +
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 2 ^ 2) /
      ((ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 0 *
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 1 *
        (ClusterAlgebras.seedMutationSeq le_rfl S s).extCluster 2) =
      (S.extCluster 0 ^ 2 + S.extCluster 1 ^ 2 + S.extCluster 2 ^ 2) /
        (S.extCluster 0 * S.extCluster 1 * S.extCluster 2) :=
  hS.markov_invariant_of_smul (.inl rfl) (by rw [hB, one_smul]) s

end ClusterAlgebras
