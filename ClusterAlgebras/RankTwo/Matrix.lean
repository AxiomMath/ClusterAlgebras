/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Seed

/-!
# Mutation of a `2 × 2` skew-symmetrizable matrix

Mutating a `2 × 2` skew-symmetrizable matrix in either direction negates it: every entry but
the diagonal one opposite the direction lies in the mutated row or column, and that diagonal
entry is zero.

## Main statements

* `ClusterAlgebras.SkewSymmetrizable.matrixMutation_eq_neg_of_fin_two`: `μₖ(B) = -B`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A skew-symmetrizable square matrix is sign-antisymmetric. -/
theorem SkewSymmetrizable.signAntisymmetric_self {n : ℕ} {B : Matrix (Fin n) (Fin n) R}
    (hB : SkewSymmetrizable B) : SignAntisymmetric le_rfl B :=
  ExtSkewSymmetrizable.signAntisymmetric le_rfl (by simpa [ExtSkewSymmetrizable] using hB)

/-- **Mutation of a `2 × 2` skew-symmetrizable matrix changes its sign.** For a
skew-symmetrizable `2 × 2` matrix `B` and either direction `k`, `μₖ(B) = -B`. -/
@[cluster_algebras "lem_rank_two_mutation"]
theorem SkewSymmetrizable.matrixMutation_eq_neg_of_fin_two {B : Matrix (Fin 2) (Fin 2) R}
    (hB : SkewSymmetrizable B) (k : Fin 2) : matrixMutation le_rfl B k = -B := by
  have hsign := hB.signAntisymmetric_self
  ext i j
  by_cases h : i = Fin.castLE le_rfl k ∨ j = k
  · rw [matrixMutation_apply_of_eq le_rfl B k h, Matrix.neg_apply]
  · push Not at h
    have hij : i = j := by
      have := h.1
      simp only [Fin.castLE_refl] at this
      omega
    subst hij
    have h0 := hsign.1 i
    have h1 := matrixMutation_diag_eq_zero le_rfl hsign k i
    simp only [Fin.castLE_refl] at h0 h1
    rw [Matrix.neg_apply, h0, neg_zero]
    exact h1

end ClusterAlgebras
