/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.NumberTheory.RotationSequence
public import ClusterAlgebras.LaurentPhenomenon.Laurent

/-!
# The Somos-4 sequence

The Somos-4 sequence is the sequence of rational numbers `z₀ = z₁ = z₂ = z₃ = 1`,
`z_{t+4} = (z_{t+3} z_{t+1} + z_{t+2}²) / z_t`. Every term is an integer.

The proof realises the recurrence as a sequence of cluster mutations. The Somos-4 matrix `B_S`,
with rows `(0, -1, 2, -1)`, `(1, 0, -3, 2)`, `(-2, 3, 0, -1)` and `(1, -2, 1, 0)`, is
skew-symmetric and satisfies `μ₁(B_S) = ρ(B_S)`, so mutating the generic seed `(X̃, B_S)` of
`ℚ(X₁, …, X₄)` successively in the directions `1, 2, 3, 4, 1, 2, …` produces cluster variables
`w_t` with `w_{t+4} w_t = w_{t+1} w_{t+3} + w_{t+2}²`. By the Laurent phenomenon every `w_t` lies
in `ℤ[X̃^{±1}]`, and the ring homomorphism `ℤ[X̃^{±1}] → ℤ` sending every `Xᵢ` to `1` sends
`w_t` to `z_t`.

## Main definitions

* `ClusterAlgebras.somos4Matrix`: the Somos-4 matrix `B_S`.
* `ClusterAlgebras.somos4Seq`: the Somos-4 sequence.

## Main results

* `ClusterAlgebras.somos4Matrix_rotation`: `μ₁(B_S) = ρ(B_S)`.
* `ClusterAlgebras.somos4Seq_isInt`: every term of the Somos-4 sequence is an integer.

## Implementation notes

FWZ index by `[1, n]`, Lean by `Fin n`, so FWZ's index `i` is Lean index `i - 1`;
in particular FWZ's direction `1` is `0 : Fin 4`, and FWZ's entries
`(b₂₁, b₃₁, b₄₁) = (1, -2, 1)` are the Lean entries in rows `1, 2, 3` of column `0`.

The cluster variable `w_t` is the entry in position `p(t) = (t mod 4) + 1` of the seed
`Σ_{t-3}` obtained after `t - 3` steps (with `t - 3` truncated at `0`). For `t ≤ 3` this is the
indeterminate `X_{t+1}` of the initial seed, and for `t ≥ 4` it is the entry created by the
mutation at step `t - 4`, so FWZ's two-case definition is a single formula here.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras.
  Chapters 1–3*][FWZ16]
-/

@[expose] public section

namespace ClusterAlgebras

/-- The **Somos-4 matrix** `B_S`: the `4 × 4` integer matrix with rows `(0, -1, 2, -1)`,
`(1, 0, -3, 2)`, `(-2, 3, 0, -1)` and `(1, -2, 1, 0)`. -/
@[cluster_algebras "def_somos4_matrix"]
def somos4Matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, -1, 2, -1; 1, 0, -3, 2; -2, 3, 0, -1; 1, -2, 1, 0]

/-- **Mutating the Somos-4 matrix in direction `1` rotates it:** `μ₁(B_S) = ρ(B_S)`. -/
@[cluster_algebras "lem_somos4_rotation"]
theorem somos4Matrix_rotation :
    matrixMutation le_rfl somos4Matrix 0 = matrixCyclicShift somos4Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The Somos-4 matrix is skew-symmetric, so it is extended skew-symmetrizable with
skew-symmetrizing vector `d = (1, 1, 1, 1)`. -/
theorem extSkewSymmetrizable_somos4Matrix : ExtSkewSymmetrizable le_rfl somos4Matrix :=
  ⟨1, by decide, by decide⟩

/-- The **Somos-4 sequence** `z₀ = z₁ = z₂ = z₃ = 1`,
`z_{t+4} = (z_{t+3} z_{t+1} + z_{t+2}²) / z_t`, as rational numbers. -/
@[cluster_algebras "def_somos4_sequence"]
def somos4Seq : ℕ → ℚ
  | 0 | 1 | 2 | 3 => 1
  | t + 4 => (somos4Seq (t + 3) * somos4Seq (t + 1) + somos4Seq (t + 2) ^ 2) / somos4Seq t

/-- The defining recurrence of the Somos-4 sequence. -/
theorem somos4Seq_add_four (t : ℕ) :
    somos4Seq (t + 4) =
      (somos4Seq (t + 3) * somos4Seq (t + 1) + somos4Seq (t + 2) ^ 2) / somos4Seq t := by
  rw [somos4Seq]

/-- Every term of the Somos-4 sequence is positive. -/
theorem somos4Seq_pos : ∀ t, 0 < somos4Seq t
  | 0 | 1 | 2 | 3 => by simp [somos4Seq]
  | t + 4 => by
    have := somos4Seq_pos t
    have := somos4Seq_pos (t + 1)
    have := somos4Seq_pos (t + 2)
    have := somos4Seq_pos (t + 3)
    rw [somos4Seq_add_four]
    positivity

/-- Every term of the Somos-4 sequence is nonzero, so the divisions in its definition are
divisions by nonzero numbers. -/
theorem somos4Seq_ne_zero (t : ℕ) : somos4Seq t ≠ 0 :=
  (somos4Seq_pos t).ne'

/-- The seed `Σ_s` obtained from the generic seed `(X̃, B_S)` of `ℚ(X₁, …, X₄)` by mutating in
the directions `p(0), …, p(s - 1)`, where `p(r) = (r mod 4) + 1`. -/
noncomputable def somos4Seed (s : ℕ) : SeedData (FractionRing (MvPolynomial (Fin 4) ℚ)) 4 4 :=
  seedMutationSeq le_rfl (genericSeed somos4Matrix) ((List.range s).map (rotationDirection 4))

/-- Each `Σ_s` is a labeled seed over `ℚ`. -/
theorem isLabeledSeed_somos4Seed (s : ℕ) : IsLabeledSeed ℚ le_rfl (somos4Seed s) :=
  (isLabeledSeed_genericSeed le_rfl extSkewSymmetrizable_somos4Matrix).seedMutationSeq le_rfl _

/-- `Σ₀` is the generic seed `(X̃, B_S)`. -/
theorem somos4Seed_zero : somos4Seed 0 = genericSeed somos4Matrix :=
  rfl

/-- `Σ_{s+1} = μ_{p(s)}(Σ_s)`. -/
theorem somos4Seed_succ (s : ℕ) :
    somos4Seed (s + 1) = seedMutation le_rfl (somos4Seed s) (rotationDirection 4 s) := by
  rw [somos4Seed, List.range_succ, List.map_append, seedMutationSeq_append]
  rfl

/-- The **Somos-4 cluster variable** `w_t`: the entry in position `p(t)` of `Σ_{t-3}`. For
`t ≤ 3` it is the indeterminate `X_{t+1}`, and for `t ≥ 4` it is the entry created by the
mutation of `Σ_{t-4}` in direction `p(t - 4) = p(t)`. -/
noncomputable def somos4ClusterVariable (t : ℕ) : FractionRing (MvPolynomial (Fin 4) ℚ) :=
  (somos4Seed (t - 3)).extCluster (rotationDirection 4 t)

/-- The first four Somos-4 cluster variables are the indeterminates: `w_i = X_{i+1}` for
`i ∈ [0, 3]`. -/
theorem somos4ClusterVariable_val (i : Fin 4) :
    somos4ClusterVariable i = (genericSeed somos4Matrix).extCluster i := by
  rw [somos4ClusterVariable, show (i : ℕ) - 3 = 0 by omega, somos4Seed_zero]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- The Somos-4 cluster variables satisfy `w_{s+4} w_s = w_{s+1} w_{s+3} + w_{s+2}²`. -/
theorem somos4ClusterVariable_recurrence (s : ℕ) :
    somos4ClusterVariable (s + 4) * somos4ClusterVariable s =
      somos4ClusterVariable (s + 1) * somos4ClusterVariable (s + 3) +
        somos4ClusterVariable (s + 2) ^ 2 := by
  have h := rotationSequence_recurrence somos4Matrix_rotation (w := somos4ClusterVariable)
    (S := somos4Seed) isLabeledSeed_somos4Seed ?_ somos4Seed_succ ?_ s
  · rw [h, show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    simp [somos4Matrix, Finset.prod_insert]
  · simp only [somos4ClusterVariable_val, somos4Seed_zero]
    rfl
  · intro s
    simp [somos4ClusterVariable, show s + 4 - 3 = s + 1 by omega]

/-- Every Somos-4 cluster variable is an integer Laurent polynomial in `X̃`, by the Laurent
phenomenon. -/
theorem somos4ClusterVariable_mem_laurentSubring (t : ℕ) :
    somos4ClusterVariable t ∈ laurentSubring (genericSeed somos4Matrix).extCluster :=
  (isLabeledSeed_genericSeed le_rfl extSkewSymmetrizable_somos4Matrix
    ).seedMutationSeq_extCluster_mem_laurentSubring le_rfl _ _

/-- **The Somos-4 sequence consists of integers:** every term `z_t` is an integer. -/
@[cluster_algebras "thm_somos4_integers"]
theorem somos4Seq_isInt (t : ℕ) : ∃ m : ℤ, somos4Seq t = m := by
  have hlab := isLabeledSeed_genericSeed le_rfl extSkewSymmetrizable_somos4Matrix
  obtain ⟨φ, hφ⟩ := exists_ringHom_laurentSubring (A := ℤ) hlab.1.1 fun _ => 1
  let W (t : ℕ) : laurentSubring (genericSeed somos4Matrix).extCluster :=
    ⟨_, somos4ClusterVariable_mem_laurentSubring t⟩
  have hrec (s : ℕ) : W (s + 4) * W s = W (s + 1) * W (s + 3) + W (s + 2) ^ 2 :=
    Subtype.ext (somos4ClusterVariable_recurrence s)
  have hbase (i : Fin 4) : φ (W i) = 1 := by
    rw [show W i = ⟨_, mem_laurentSubring _ i⟩ from Subtype.ext (somos4ClusterVariable_val i),
      hφ]
    rfl
  have key (s : ℕ) : ∀ r < 4, (φ (W (s + r)) : ℚ) = somos4Seq (s + r) := by
    induction s with
    | zero =>
      intro r hr
      rw [zero_add, show r = ((⟨r, hr⟩ : Fin 4) : ℕ) from rfl, hbase]
      interval_cases r <;> rfl
    | succ s ih =>
      intro r hr
      by_cases hr' : r + 1 < 4
      · rw [show s + 1 + r = s + (r + 1) by omega]
        exact ih _ hr'
      · obtain rfl : r = 3 := by omega
        have h := congrArg (fun x => (φ x : ℚ)) (hrec s)
        simp only [map_mul, map_add, map_pow, Int.cast_mul, Int.cast_add, Int.cast_pow] at h
        have h0 : (φ (W s) : ℚ) = somos4Seq s := by simpa using ih 0 (by norm_num)
        rw [h0, ih 1 (by norm_num), ih 2 (by norm_num), ih 3 (by norm_num)] at h
        rw [show s + 1 + 3 = s + 4 by omega, somos4Seq_add_four, eq_div_iff (somos4Seq_ne_zero s),
          h]
        ring
  exact ⟨φ (W t), (key t 0 (by norm_num)).symm⟩

end ClusterAlgebras
