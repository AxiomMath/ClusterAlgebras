/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.NumberTheory.CyclicShift
public import ClusterAlgebras.Seed
public import ClusterAlgebras.Defs.MatrixMutationEquiv

/-!
# Rotation-periodic exchange matrices and their recurrences

Mutation commutes with a simultaneous relabelling of the rows and columns of a square
matrix: if `c_{σ(i)σ(j)} = b_{ij}` then `μ_{σ(k)}(C)_{σ(i)σ(j)} = μ_k(B)_{ij}`.

Let `B` be an `n × n` integer matrix whose mutation in the first direction is its cyclic shift,
`μ₁(B) = ρ(B)`. Mutating a labeled seed with matrix `B` successively in the directions
`1, 2, …, n, 1, 2, …` rotates the matrix at every step, `μ_{p(s)}(ρ^s(B)) = ρ^{s+1}(B)` with
`p(s) = (s mod n) + 1`, and each step replaces the oldest entry of the cluster. If the
successive new entries are `w_n, w_{n+1}, …` and the initial cluster is `(w_0, …, w_{n-1})`,
then every exchange relation is the same recurrence
`w_{s+n} w_s = ∏_{r=1}^{n-1} w_{s+r}^{[b_{r+1,1}]_+} + ∏_{r=1}^{n-1} w_{s+r}^{[-b_{r+1,1}]_+}`.

## Main definitions

* `rotationDirection n s`: the direction `p(s)` mutated at step `s`.

## Main results

* `matrixMutation_apply_relabel`: mutation commutes with relabelling the indices.
* `matrixCyclicShift_iterate`: `ρ^s(B)ᵢⱼ = b_{π^s(i) π^s(j)}`.
* `matrixMutation_rotationDirection_iterate`: `μ_{p(s)}(ρ^s(B)) = ρ^{s+1}(B)` when
  `μ₁(B) = ρ(B)`.
* `extExchangeMatrix_eq_iterate_matrixCyclicShift`: the matrix of the `s`-th seed is `ρ^s(B)`.
* `rotationSequence_recurrence`: the recurrence satisfied by the new cluster variables.

## Implementation notes

[fordy-marsh] index by `[1, n]`, Lean by `Fin n`, so index `i` of [fordy-marsh] is Lean index
`i - 1`. The direction `1` is `0 : Fin n`, the direction `p(s) = (s mod n) + 1` is
`rotationDirection n s`, whose value is `s % n`, and the row `r + 1` of the recurrence is the
Lean row `r`, for `r ∈ [1, n - 1]`. The permutation `π` is `(finRotate n).symm`, so `π^{-s}` is
`finRotate n ^ s`.

The hypotheses that `B` is skew-symmetrizable and that the ground field has characteristic zero
are not needed: the vanishing of `b₁₁` follows from the first seed being a labeled seed.

## References

* [fordy-marsh] A. P. Fordy, B. Marsh, *Cluster mutation-periodic quivers and associated
  Laurent sequences*, J. Algebraic Combin. 34 (2011), 19–66.
-/

@[expose] public section

namespace ClusterAlgebras

open Matrix

section Relabel

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ}

/-- **Mutation commutes with relabelling the indices.** If `σ` is a permutation of the indices
and `c_{σ(i)σ(j)} = b_{ij}` for all `i, j`, then `μ_{σ(k)}(C)_{σ(i)σ(j)} = μ_k(B)_{ij}`. -/
@[cluster_algebras "lem_matmut_relabel"]
theorem matrixMutation_apply_relabel {B C : Matrix (Fin n) (Fin n) R} (σ : Equiv.Perm (Fin n))
    (hC : ∀ i j, C (σ i) (σ j) = B i j) (k i j : Fin n) :
    matrixMutation le_rfl C (σ k) (σ i) (σ j) = matrixMutation le_rfl B k i j := by
  obtain rfl : B = C.submatrix σ σ := (Matrix.ext hC).symm
  rw [matrixMutation_submatrix, submatrix_apply]

end Relabel

section Rotation

variable {n : ℕ}

/-- The values of the powers of `finRotate n`: `(finRotate n)^s` adds `s` modulo `n`. -/
theorem val_finRotate_pow_apply (s : ℕ) (i : Fin n) :
    ((finRotate n ^ s) i : ℕ) = (i + s) % n := by
  induction s with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ s ih =>
    have := i.neZero
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      Nat.add_mod_mod, Nat.mod_add_mod, add_assoc]

variable (n) [NeZero n]

/-- The direction `p(s) = (s mod n) + 1` mutated at step `s`: the index of `Fin n` with value
`s % n`. -/
def rotationDirection (s : ℕ) : Fin n :=
  ⟨s % n, Nat.mod_lt _ (NeZero.pos n)⟩

variable {n}

/-- The value of the direction of step `s` is `s % n`. -/
@[simp]
theorem val_rotationDirection (s : ℕ) : (rotationDirection n s : ℕ) = s % n :=
  rfl

/-- Directions `n` steps apart coincide. -/
@[simp]
theorem rotationDirection_add_self (s : ℕ) :
    rotationDirection n (s + n) = rotationDirection n s :=
  Fin.ext (by simp)

/-- `(finRotate n)^s` sends `i` to the direction of step `s + i`. -/
theorem finRotate_pow_apply (s : ℕ) (i : Fin n) :
    (finRotate n ^ s) i = rotationDirection n (s + i) :=
  Fin.ext (by rw [val_finRotate_pow_apply, val_rotationDirection, add_comm])

/-- `(finRotate n)^s` sends `0` to the direction of step `s`. -/
theorem finRotate_pow_apply_zero (s : ℕ) : (finRotate n ^ s) 0 = rotationDirection n s := by
  simp [finRotate_pow_apply]

end Rotation

section Matrix

variable {α : Type*} {n : ℕ}

/-- The iterated cyclic shift: `ρ^s(B)ᵢⱼ = b_{π^s(i) π^s(j)}`, where `π^s` is the inverse of
`(finRotate n)^s`. -/
theorem matrixCyclicShift_iterate (B : Matrix (Fin n) (Fin n) α) (s : ℕ) :
    matrixCyclicShift^[s] B = B.submatrix (finRotate n ^ s).symm (finRotate n ^ s).symm := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih]
    ext i j
    simp [pow_succ', Equiv.Perm.mul_def]

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [NeZero n]

/-- **Mutation along the rotation rotates the matrix.** If `μ₁(B) = ρ(B)`, then mutating
`ρ^s(B)` in direction `p(s)` gives `ρ^{s+1}(B)`. -/
theorem matrixMutation_rotationDirection_iterate {B : Matrix (Fin n) (Fin n) R}
    (hrot : matrixMutation le_rfl B 0 = matrixCyclicShift B) (s : ℕ) :
    matrixMutation le_rfl (matrixCyclicShift^[s] B) (rotationDirection n s) =
      matrixCyclicShift^[s + 1] B := by
  rw [matrixCyclicShift_iterate, ← finRotate_pow_apply_zero s,
    ← Equiv.symm_symm (finRotate n ^ s), Equiv.symm_symm, Function.iterate_succ_apply,
    matrixCyclicShift_iterate, ← hrot]
  have h := matrixMutation_submatrix (le_refl n) B (finRotate n ^ s).symm ((finRotate n ^ s) 0)
  rwa [Equiv.symm_apply_apply] at h

end Matrix

section Seed

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n]

/-- **The matrices of the rotation sequence.** If `μ₁(B) = ρ(B)`, the first seed has matrix `B`
and each seed `Σ_{s+1}` is `μ_{p(s)}(Σ_s)`, then the matrix of `Σ_s` is `ρ^s(B)`. -/
theorem extExchangeMatrix_eq_iterate_matrixCyclicShift {B : Matrix (Fin n) (Fin n) ℤ}
    (hrot : matrixMutation le_rfl B 0 = matrixCyclicShift B) {S : ℕ → SeedData F n n}
    (hS0 : (S 0).extExchangeMatrix = B)
    (hS : ∀ s, S (s + 1) = seedMutation le_rfl (S s) (rotationDirection n s)) (s : ℕ) :
    (S s).extExchangeMatrix = matrixCyclicShift^[s] B := by
  induction s with
  | zero => exact hS0
  | succ s ih =>
    rw [hS, ← matrixMutation_rotationDirection_iterate hrot, ← ih]
    rfl

/-- **The clusters of the rotation sequence.** If the first seed has cluster
`(w_0, …, w_{n-1})`, each seed `Σ_{s+1}` is `μ_{p(s)}(Σ_s)` and the new entry of `Σ_{s+1}` is
`w_{s+n}`, then for `t ∈ [s, s + n - 1]` the entry of `Σ_s` in position `p(t)` is `w_t`. -/
theorem extCluster_rotationDirection_eq {w : ℕ → F} {S : ℕ → SeedData F n n}
    (hS0 : (S 0).extCluster = fun i : Fin n => w i)
    (hS : ∀ s, S (s + 1) = seedMutation le_rfl (S s) (rotationDirection n s))
    (hw : ∀ s, (S (s + 1)).extCluster (rotationDirection n s) = w (s + n))
    (s r : ℕ) (hr : r < n) :
    (S s).extCluster (rotationDirection n (s + r)) = w (s + r) := by
  induction s generalizing r with
  | zero =>
    rw [hS0, zero_add]
    simp [rotationDirection, Nat.mod_eq_of_lt hr]
  | succ s ih =>
    by_cases hrn : r + 1 = n
    · rw [show s + 1 + r = s + n by omega, rotationDirection_add_self]
      exact hw s
    · have hne : rotationDirection n (s + 1 + r) ≠ rotationDirection n s := by
        intro h
        have h' : s + (r + 1) ≡ s + 0 [MOD n] := by
          simpa [Nat.ModEq, Fin.ext_iff, show s + 1 + r = s + (r + 1) by omega] using h
        have := Nat.ModEq.add_left_cancel' s h'
        rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega : r + 1 < n), Nat.zero_mod] at this
        omega
      rw [hS, seedMutation]
      dsimp only
      rw [Fin.castLE_rfl, id, Function.update_of_ne hne,
        show s + 1 + r = s + (r + 1) by omega]
      exact ih (r + 1) (by omega)

/-- **A rotation-periodic exchange matrix produces a recurrence.** Let `B` be an `n × n`
integer matrix with `μ₁(B) = ρ(B)`, and let `Σ_s` be labeled seeds with
`Σ₀ = ((w_0, …, w_{n-1}), B)`, `Σ_{s+1} = μ_{p(s)}(Σ_s)`, and `w_{s+n}` the entry of
`Σ_{s+1}` in position `p(s)`. Then
`w_{s+n} w_s = ∏_{r=1}^{n-1} w_{s+r}^{[b_{r+1,1}]_+} + ∏_{r=1}^{n-1} w_{s+r}^{[-b_{r+1,1}]_+}`.
-/
@[cluster_algebras "lem_rotation_sequence"]
theorem rotationSequence_recurrence {B : Matrix (Fin n) (Fin n) ℤ}
    (hrot : matrixMutation le_rfl B 0 = matrixCyclicShift B) {w : ℕ → F}
    {S : ℕ → SeedData F n n} (hlab : ∀ s, IsLabeledSeed K le_rfl (S s))
    (hS0 : S 0 = ⟨fun i => w i, B⟩)
    (hS : ∀ s, S (s + 1) = seedMutation le_rfl (S s) (rotationDirection n s))
    (hw : ∀ s, (S (s + 1)).extCluster (rotationDirection n s) = w (s + n)) (s : ℕ) :
    w (s + n) * w s =
      ∏ r ∈ Finset.univ.erase (0 : Fin n), w (s + r) ^ (B r 0).toNat +
        ∏ r ∈ Finset.univ.erase (0 : Fin n), w (s + r) ^ (-B r 0).toNat := by
  have hcl := extCluster_rotationDirection_eq (by rw [hS0]) hS hw
  have hmat := extExchangeMatrix_eq_iterate_matrixCyclicShift hrot (by rw [hS0]) hS s
  have hx : (S s).extCluster (rotationDirection n s) = w s := by
    simpa using hcl s 0 (NeZero.pos n)
  have hx0 : w s ≠ 0 := hx ▸ (hlab s).1.1.ne_zero _
  have hB00 : B 0 0 = 0 := by
    simpa [hS0] using (hlab 0).extExchangeMatrix_castLE_self le_rfl 0
  have key : ∀ f : ℤ → ℕ, f 0 = 0 →
      ∏ i, (S s).extCluster i ^ f ((S s).extExchangeMatrix i (rotationDirection n s)) =
        ∏ r ∈ Finset.univ.erase (0 : Fin n), w (s + r) ^ f (B r 0) := by
    intro f hf
    rw [← Equiv.prod_comp (finRotate n ^ s), ← Finset.mul_prod_erase _ _ (Finset.mem_univ 0)]
    simp only [hmat, matrixCyclicShift_iterate, submatrix_apply, ← finRotate_pow_apply_zero,
      Equiv.symm_apply_apply, hB00, hf, pow_zero, one_mul]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [finRotate_pow_apply, hcl s r r.isLt]
  have h := hw s
  rw [hS, seedMutation] at h
  dsimp only at h
  rw [Fin.castLE_rfl, id, Function.update_self, hx, exchangeMonomialPos_eq_prod,
    exchangeMonomialNeg_eq_prod] at h
  rw [← h, div_mul_cancel₀ _ hx0, key _ rfl, key (fun b => (-b).toNat) rfl]

end Seed

end ClusterAlgebras
