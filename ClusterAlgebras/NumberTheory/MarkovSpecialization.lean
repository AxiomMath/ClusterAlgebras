/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.NumberTheory.MarkovSeed
public import ClusterAlgebras.NumberTheory.MarkovTriples
public import ClusterAlgebras.LaurentPhenomenon.Laurent

/-!
# Specializing the Markov cluster variables at one

Let `Σ = (X̃, B_M)` be the labeled seed of `ℚ(X₁, X₂, X₃)` formed by the indeterminates and the
Markov matrix. By the Laurent phenomenon, every entry of the extended cluster of every `μ_s(Σ)`
lies in `ℤ[X̃^{±1}]`. Let `φ : ℤ[X̃^{±1}] → ℚ` be a ring homomorphism with
`φ(X₁) = φ(X₂) = φ(X₃) = 1`. Along every mutation sequence the matrix stays `±B_M`, so each
exchange relation reads `y'_k y_k = y_i² + y_j²`, which `φ` turns into the rule defining the
Markov move `ν_k`. Hence `φ` sends the extended cluster of `μ_s(Σ)` to `ν_s(1, 1, 1)`.

FWZ index by `[1, 3]`; here the indices are `Fin 3`, so FWZ's index `i` is Lean
index `i - 1`, and the complement `{i, j}` of `k` is `{k + 1, k + 2}`, computed in `Fin 3`.

## Main results

* `ClusterAlgebras.isLabeledSeed_genericSeed_markovMatrix`: `Σ = (X̃, B_M)` is a labeled seed.
* `ClusterAlgebras.markov_map_seedMutationSeq_eq_markovMoveSeq`: `φ` sends the extended
  cluster of `μ_s(Σ)` to `ν_s(1, 1, 1)`.

## Implementation notes

The entries of `μ_s(Σ)` are elements of the field `ℚ(X₁, X₂, X₃)`, and `φ` is defined on the
subring `ℤ[X̃^{±1}]`; each entry is fed to `φ` together with the proof, given by the Laurent
phenomenon, that it lies there.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

/-- The Markov matrix is extended skew-symmetrizable: it is skew-symmetric, with
skew-symmetrizing vector `d = (1, 1, 1)`. -/
theorem extSkewSymmetrizable_markovMatrix : ExtSkewSymmetrizable le_rfl markovMatrix := by
  rw [markovMatrix_eq]
  exact ⟨![1, 1, 1], by decide, by decide⟩

/-- The **Markov seed** `Σ = (X̃, B_M)`, formed by the indeterminates of `ℚ(X₁, X₂, X₃)` and the
Markov matrix, is a labeled seed over `ℚ`. -/
theorem isLabeledSeed_genericSeed_markovMatrix :
    IsLabeledSeed ℚ le_rfl (genericSeed markovMatrix) :=
  isLabeledSeed_genericSeed _ extSkewSymmetrizable_markovMatrix

/-- **Specializing the Markov cluster variables at one.** Let `φ : ℤ[X̃^{±1}] → ℚ` be a ring
homomorphism with `φ(X₁) = φ(X₂) = φ(X₃) = 1`. For every sequence `s` of directions and every
position `i`, the entry in position `i` of the extended cluster of `μ_s(Σ)`, which lies in
`ℤ[X̃^{±1}]` by the Laurent phenomenon, is sent by `φ` to the `i`-th entry of
`ν_s(1, 1, 1)`. -/
@[cluster_algebras "lem_markov_specialization"]
theorem markov_map_seedMutationSeq_eq_markovMoveSeq
    (φ : laurentSubring (genericSeed markovMatrix).extCluster →+* ℚ)
    (hφ : ∀ i, φ ⟨_, mem_laurentSubring _ i⟩ = 1) (s : List (Fin 3)) (i : Fin 3) :
    φ ⟨_, isLabeledSeed_genericSeed_markovMatrix.seedMutationSeq_extCluster_mem_laurentSubring
      le_rfl s i⟩ = markovMoveSeq 1 s i := by
  have hS := isLabeledSeed_genericSeed_markovMatrix
  induction s using List.reverseRecOn generalizing i with
  | nil => exact hφ i
  | append_singleton s k ih =>
    rw [markovMoveSeq_concat]
    have hε : ((-1) ^ s.length * 1 : ℤ) = 1 ∨ ((-1) ^ s.length * 1 : ℤ) = -1 := by
      rcases neg_one_pow_eq_or ℤ s.length with h | h <;> simp [h]
    have hB := seedMutationSeq_extExchangeMatrix_of_markov (.inl rfl)
      (S := genericSeed markovMatrix) (one_smul ..).symm s
    rcases eq_or_ne i k with rfl | hik
    · obtain ⟨b, hb, hbs⟩ := isMarkovTriple_markovMoveSeq_one s
      have hne : markovMoveSeq 1 s i ≠ 0 := by
        rw [hbs]
        exact Nat.cast_ne_zero.2 (hb.pos i).ne'
      rw [markovMove_apply_self, eq_div_iff hne, ← ih, ← ih, ← ih, ← map_pow, ← map_pow,
        ← map_add, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subring.coe_mul, seedMutationSeq_append, seedMutationSeq_cons,
        seedMutationSeq_nil, seedMutation_extCluster_self_of_markov hε hB,
        div_mul_cancel₀ _ (hS.seedMutationSeq_extCluster_ne_zero le_rfl s i)]
      rfl
    · rw [markovMove_apply_of_ne _ hik, ← ih]
      congr 2
      simp only [seedMutationSeq_append, seedMutationSeq_cons, seedMutationSeq_nil,
        seedMutation, Fin.castLE_refl]
      exact Function.update_of_ne hik _ _

end ClusterAlgebras
