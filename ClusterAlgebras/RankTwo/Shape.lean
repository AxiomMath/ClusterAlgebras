/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.RankTwo.Matrix

/-!
# The shape of a `2 × 2` skew-symmetrizable matrix

A `2 × 2` skew-symmetrizable matrix `B` has zero diagonal, and its two off-diagonal entries
are either both zero or nonzero of opposite signs. Hence there are a sign `ε ∈ {1, -1}` and
`b, c` with either `b > 0` and `c > 0`, or `b = c = 0`, such that
`B = !![0, ε * b; -(ε * c), 0]`.

## Main results

* `ClusterAlgebras.SkewSymmetrizable.exists_rankTwo_shape`: the shape of a `2 × 2`
  skew-symmetrizable matrix.

## Implementation notes

The result is stated over any strictly ordered commutative ring `R`, not only over `ℤ`. Rows
and columns are indexed by `Fin 2`, so the indices are `0, 1` rather than `1, 2`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **The shape of a `2 × 2` skew-symmetrizable matrix.** For a skew-symmetrizable `2 × 2`
matrix `B` there are `ε ∈ {1, -1}` and `b, c`, with either `b > 0` and `c > 0` or
`b = c = 0`, such that `b₀₀ = b₁₁ = 0`, `b₀₁ = ε b` and `b₁₀ = -ε c`. -/
@[cluster_algebras "lem_rank_two_shape"]
theorem SkewSymmetrizable.exists_rankTwo_shape {B : Matrix (Fin 2) (Fin 2) R}
    (hB : SkewSymmetrizable B) :
    ∃ ε : R, (ε = 1 ∨ ε = -1) ∧ ∃ b c : R, ((0 < b ∧ 0 < c) ∨ (b = 0 ∧ c = 0)) ∧
      B 0 0 = 0 ∧ B 1 1 = 0 ∧ B 0 1 = ε * b ∧ B 1 0 = -(ε * c) := by
  have hsign := hB.signAntisymmetric_self
  have h00 : B 0 0 = 0 := by simpa using hsign.1 0
  have h11 : B 1 1 = 0 := by simpa using hsign.1 1
  rcases lt_trichotomy (B 0 1) 0 with h | h | h
  · exact ⟨-1, .inr rfl, -B 0 1, B 1 0, .inl ⟨neg_pos.2 h, by simpa using (hsign.2 1 0).2 h⟩,
      h00, h11, by ring, by ring⟩
  · have h' : B 1 0 = 0 := by
      simpa using hsign.eq_zero_of_eq_zero le_rfl (j := 0) (k := 1) (by simpa using h)
    exact ⟨1, .inl rfl, 0, 0, .inr ⟨rfl, rfl⟩, h00, h11, by simp [h], by simp [h']⟩
  · exact ⟨1, .inl rfl, B 0 1, -B 1 0, .inl ⟨h, neg_pos.2 (by simpa using (hsign.2 0 1).1 h)⟩,
      h00, h11, by ring, by ring⟩

end ClusterAlgebras
