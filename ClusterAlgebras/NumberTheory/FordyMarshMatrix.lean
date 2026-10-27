/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.External
public import ClusterAlgebras.NumberTheory.CyclicShift

/-!
# The Fordy–Marsh matrix

For an integer vector `a = (a₁, …, a_{n-1})` write
`γ(p, q) = [-a_p]₊ [a_q]₊ - [a_p]₊ [-a_q]₊`. The Fordy–Marsh matrix `B_a` is the skew-symmetric
`n × n` integer matrix whose entry in row `i` and column `j < i` is
`a_{i-j} + ∑_{k=1}^{j-1} γ(i-k, j-k)`. When `a` is palindromic, `aᵢ = a_{n-i}`, mutating `B_a`
in direction `1` is the same as cyclically shifting it, `μ₁(B_a) = ρ(B_a)`; and the first column
of `B_a` below the diagonal is `a` itself. This is what makes the Fordy–Marsh recurrence with
exponents `a` a sequence of cluster mutations.

## Main definitions

* `ClusterAlgebras.fordyMarshGamma`: the correction term `γ(p, q)`.
* `ClusterAlgebras.fordyMarshMatrix`: the Fordy–Marsh matrix `B_a`.

## Main results

* `ClusterAlgebras.fordyMarshMatrix_transpose`: `B_a` is skew-symmetric.
* `ClusterAlgebras.fordyMarshMatrix_apply_zero`: the first column of `B_a` is `a`.
* `ClusterAlgebras.fordyMarshMatrix_rotation`: for palindromic `a`, `μ₁(B_a) = ρ(B_a)`.

## Implementation notes

FWZ index rows and columns by `[1, n]`; here they are `Fin n`, so FWZ's index `i` is
Lean index `i - 1`, and FWZ's direction `1` is `0 : Fin n`. In Lean indices the entry
in row `i` and column `j < i` reads `a (i - j) + ∑_{k < j} γ(i - k, j - k)`, after the
substitution `k ↦ k + 1` in FWZ's sum.

The vector is a function `a : ℕ → ℤ`, of which only `a₁, …, a_{n-1}` are ever read: it is
FWZ's vector, extended arbitrarily, and nothing depends on the other values.

The positive part `[x]₊` is written `max 0 x`, the form in which matrix mutation is expanded
by `matrixMutation_apply_of_ne_eq_max`.

FWZ take `n ≥ 1`; the definition does not need it, and the results that name the
direction `0 : Fin n` assume `[NeZero n]`. That the first column is `a` holds for every `a`,
palindromic or not, so it is stated without that hypothesis.

The proof of `μ₁(B_a) = ρ(B_a)` compares the entries on and below the diagonal directly and
obtains those above it from skew-symmetry of both sides. For `μ₁(B_a)` this is the
preservation of a skew-symmetrizing vector under mutation,
`IsSkewSymmetrizingVector.matrixMutation`, applied with `d = (1, …, 1)`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*,
  Chapter 3, §3.4.
* [fordy-marsh] A. P. Fordy, B. Marsh, *Cluster mutation-periodic quivers and associated
  Laurent sequences*, J. Algebraic Combin. 34 (2011), 19–66.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

variable {n : ℕ} (a : ℕ → ℤ)

/-- The **Fordy–Marsh correction** `γ(p, q) = [-a_p]₊ [a_q]₊ - [a_p]₊ [-a_q]₊`. -/
@[cluster_algebras "def_fordy_marsh_matrix"]
def fordyMarshGamma (p q : ℕ) : ℤ :=
  max 0 (-a p) * max 0 (a q) - max 0 (a p) * max 0 (-a q)

/-- `γ` is antisymmetric. -/
theorem fordyMarshGamma_swap (p q : ℕ) : fordyMarshGamma a q p = -fordyMarshGamma a p q := by
  unfold fordyMarshGamma
  ring

/-- `γ` depends only on the two entries of `a` it reads. -/
theorem fordyMarshGamma_congr {p q p' q' : ℕ} (hp : a p = a p') (hq : a q = a q') :
    fordyMarshGamma a p q = fordyMarshGamma a p' q' := by
  simp only [fordyMarshGamma, hp, hq]

/-- The entry of the Fordy–Marsh matrix in (Lean) row `i` and column `j`, for `j < i`:
`a (i - j) + ∑_{k < j} γ(i - k, j - k)`. -/
def fordyMarshEntry (i j : ℕ) : ℤ :=
  a (i - j) + ∑ k ∈ range j, fordyMarshGamma a (i - k) (j - k)

/-- The **Fordy–Marsh matrix** `B_a` of `a`: zero on the diagonal, `fordyMarshEntry a i j`
below it, and the negated mirror entry above it. -/
@[cluster_algebras "def_fordy_marsh_matrix"]
def fordyMarshMatrix (n : ℕ) (a : ℕ → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if j < i then fordyMarshEntry a i j else if i < j then -fordyMarshEntry a j i else 0

/-- The entries below the diagonal. -/
theorem fordyMarshMatrix_apply_of_lt {i j : Fin n} (h : j < i) :
    fordyMarshMatrix n a i j = fordyMarshEntry a i j := by
  simp [fordyMarshMatrix, h]

/-- The entries above the diagonal. -/
theorem fordyMarshMatrix_apply_of_gt {i j : Fin n} (h : i < j) :
    fordyMarshMatrix n a i j = -fordyMarshEntry a j i := by
  simp [fordyMarshMatrix, h, h.not_gt]

/-- The diagonal vanishes. -/
@[simp]
theorem fordyMarshMatrix_apply_self (i : Fin n) : fordyMarshMatrix n a i i = 0 := by
  simp [fordyMarshMatrix]

/-- The Fordy–Marsh matrix is skew-symmetric, entrywise. -/
theorem fordyMarshMatrix_apply_swap (i j : Fin n) :
    fordyMarshMatrix n a j i = -fordyMarshMatrix n a i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [fordyMarshMatrix_apply_of_lt a h, fordyMarshMatrix_apply_of_gt a h, neg_neg]
  · simp
  · rw [fordyMarshMatrix_apply_of_lt a h, fordyMarshMatrix_apply_of_gt a h]

/-- The Fordy–Marsh matrix is skew-symmetric. -/
theorem fordyMarshMatrix_transpose : (fordyMarshMatrix n a).transpose = -fordyMarshMatrix n a := by
  ext i j
  exact fordyMarshMatrix_apply_swap a i j

/-- The constant vector `1` skew-symmetrizes the Fordy–Marsh matrix. -/
theorem isSkewSymmetrizingVector_fordyMarshMatrix :
    IsSkewSymmetrizingVector (fordyMarshMatrix n a) 1 :=
  ⟨fun _ => one_pos, fun i j => by simp [fordyMarshMatrix_apply_swap a i j]⟩

/-- The Fordy–Marsh matrix is skew-symmetrizable. -/
theorem skewSymmetrizable_fordyMarshMatrix : SkewSymmetrizable (fordyMarshMatrix n a) :=
  ⟨1, isSkewSymmetrizingVector_fordyMarshMatrix a⟩

/-- **The first column of the Fordy–Marsh matrix is `a`**: `B_a i 0 = a i` for every `i ≠ 0`,
for an arbitrary vector `a`. -/
@[cluster_algebras "lem_fordy_marsh_rotation"]
theorem fordyMarshMatrix_apply_zero [NeZero n] (i : Fin n) (hi : i ≠ 0) :
    fordyMarshMatrix n a i 0 = a i := by
  rw [fordyMarshMatrix_apply_of_lt a (Fin.pos_iff_ne_zero.mpr hi)]
  simp [fordyMarshEntry]

/-- The Somos-4 instance, `n = 4` and `a = (1, -2, 1)`. -/
example : fordyMarshMatrix 4 (fun i => if i = 2 then -2 else 1) =
    !![0, -1, 2, -1; 1, 0, -3, 2; -2, 3, 0, -1; 1, -2, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Moving one step down the diagonal adds one correction term. -/
theorem fordyMarshEntry_succ (i j : ℕ) :
    fordyMarshEntry a (i + 1) (j + 1) =
      fordyMarshEntry a i j + fordyMarshGamma a (i + 1) (j + 1) := by
  simp only [fordyMarshEntry, sum_range_succ', Nat.add_sub_add_right, Nat.sub_zero]
  ring

variable {a}

/-- **The vanishing sum.** For palindromic `a`, the last row of `B_a` below the diagonal is `a`
shifted by one: `(B_a)_{n, i-1} = a_{i-1}`, in Lean indices `B_a (n-1) m = a (m + 1)`. -/
theorem fordyMarshEntry_sub_one (ha : ∀ i, 1 ≤ i → i ≤ n - 1 → a i = a (n - i)) {m : ℕ}
    (hm : m + 1 < n) : fordyMarshEntry a (n - 1) m = a (m + 1) := by
  have h₁ : a (n - 1 - m) = a (m + 1) := by
    rw [ha _ (by omega) (by omega)]
    congr 1
    omega
  have h₂ : ∑ k ∈ range m, fordyMarshGamma a (n - 1 - k) (m - k) =
      ∑ k ∈ range m, fordyMarshGamma a (k + 1) (m - k) := by
    refine sum_congr rfl fun k hk => fordyMarshGamma_congr a ?_ rfl
    rw [mem_range] at hk
    rw [ha _ (by omega) (by omega)]
    congr 1
    omega
  have h₃ : ∑ k ∈ range m, fordyMarshGamma a (k + 1) (m - k) =
      -∑ k ∈ range m, fordyMarshGamma a (k + 1) (m - k) := by
    conv_lhs => rw [← sum_range_reflect]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [show m - 1 - k + 1 = m - k by omega, show m - (m - 1 - k) = k + 1 by omega,
      fordyMarshGamma_swap]
  rw [fordyMarshEntry, h₁, h₂]
  linarith

/-- **The Fordy–Marsh matrix of a palindromic vector is rotation-periodic**: if
`aᵢ = a_{n-i}` for all `i ∈ [1, n-1]`, then mutating `B_a` in the direction `0 : Fin n` is the
same as cyclically shifting it. -/
@[cluster_algebras "lem_fordy_marsh_rotation"]
theorem fordyMarshMatrix_rotation [NeZero n] (ha : ∀ i, 1 ≤ i → i ≤ n - 1 → a i = a (n - i)) :
    matrixMutation le_rfl (fordyMarshMatrix n a) 0 = matrixCyclicShift (fordyMarshMatrix n a) := by
  set B := fordyMarshMatrix n a with hB
  have hd := isSkewSymmetrizingVector_fordyMarshMatrix (n := n) a
  have hμswap (i j : Fin n) : matrixMutation le_rfl B 0 j i = -matrixMutation le_rfl B 0 i j := by
    simpa using (hd.matrixMutation le_rfl 0).2 j i
  have hμdiag (i : Fin n) : matrixMutation le_rfl B 0 i i = 0 :=
    matrixMutation_diag_eq_zero le_rfl (B := B) ⟨by simp [hB], fun i j => by
      simpa using hd.pos_iff_neg i j⟩ 0 i
  have hρswap (i j : Fin n) : matrixCyclicShift B j i = -matrixCyclicShift B i j := by
    simp only [matrixCyclicShift_apply, hB]
    exact fordyMarshMatrix_apply_swap a _ _
  have h0 : ((finRotate n).symm 0 : ℕ) = n - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
    rw [(Equiv.symm_apply_eq _).mpr (finRotate_last (n := m)).symm]
    simp
  have lower (i j : Fin n) (hij : j < i) :
      matrixMutation le_rfl B 0 i j = matrixCyclicShift B i j := by
    have hi : i ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le j) hij)
    have hi' := coe_finRotate_symm_of_ne_zero hi
    have hji : (j : ℕ) < i := hij
    have hi1 : 0 < (i : ℕ) := Nat.pos_of_ne_zero fun h => hi (Fin.ext (by simp [h]))
    have hin : (i : ℕ) < n := i.isLt
    rw [matrixCyclicShift_apply]
    by_cases hj : j = 0
    · subst hj
      have hlt : (finRotate n).symm i < (finRotate n).symm 0 := by
        rw [Fin.lt_def, hi', h0]
        omega
      rw [matrixMutation_apply_col, hB, fordyMarshMatrix_apply_zero a i hi,
        fordyMarshMatrix_apply_of_gt a hlt, h0, hi', fordyMarshEntry_sub_one ha (by omega)]
      congr 2
      omega
    · have hj' := coe_finRotate_symm_of_ne_zero hj
      have hj1 : 0 < (j : ℕ) := Nat.pos_of_ne_zero fun h => hj (Fin.ext (by simp [h]))
      have hlt : (finRotate n).symm j < (finRotate n).symm i := by
        rw [Fin.lt_def, hi', hj']
        omega
      have h0j : B 0 j = -a j := by
        rw [hB, fordyMarshMatrix_apply_swap a j 0, fordyMarshMatrix_apply_zero a j hj]
      rw [matrixMutation_apply_of_ne_eq_max le_rfl B 0 hi hj, castLE_self, h0j, hB,
        fordyMarshMatrix_apply_zero a i hi, fordyMarshMatrix_apply_of_lt a hij,
        fordyMarshMatrix_apply_of_lt a hlt, hi', hj']
      obtain ⟨i', hi''⟩ : ∃ i', (i : ℕ) = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j', hj''⟩ : ∃ j', (j : ℕ) = j' + 1 := ⟨j - 1, by omega⟩
      rw [hi'', hj'', fordyMarshEntry_succ, Nat.add_sub_cancel, Nat.add_sub_cancel,
        fordyMarshGamma, neg_neg]
      ring
  ext i j
  rcases lt_trichotomy j i with h | rfl | h
  · exact lower i j h
  · rw [hμdiag]
    simp [hB]
  · rw [hμswap j i, hρswap j i, lower j i h]

end ClusterAlgebras
