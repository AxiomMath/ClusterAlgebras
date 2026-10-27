/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Attr
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Ring

/-!
# The rank-two exchange sequence

For natural numbers `b, c` and elements `z₁, z₂` of a field `F`, the *rank-two exchange
sequence* `(z_k)_{k ∈ ℤ}` is determined by `z₁, z₂` and the relations
`z_{k+1} = (z_k ^ e_k + 1) / z_{k-1}` for `k ≥ 2` and `z_{k-1} = (z_k ^ e_k + 1) / z_{k+1}` for
`k ≤ 1`, where `e_k = c` for even `k` and `e_k = b` for odd `k`. Its terms are the cluster
variables of the rank-two cluster algebra `𝒜(b, c)`.

The sequence is built from two iterations on pairs, one running upwards from `(z₁, z₂)` and
one downwards from `(z₂, z₁)`. When all its terms are nonzero, it satisfies the exchange
relations `z_{k-1} z_{k+1} = z_k ^ e_k + 1` for every `k`, and any nowhere-vanishing sequence
satisfying them is determined by its terms of indices `1` and `2`.

## Main definitions

* `ClusterAlgebras.rankTwoExp`: the exponent `e_k`.
* `ClusterAlgebras.rankTwoSeq`: the rank-two exchange sequence.

## Main statements

* `ClusterAlgebras.rankTwoSeq_succ`, `ClusterAlgebras.rankTwoSeq_pred`: the defining
  recursions.
* `ClusterAlgebras.eq_rankTwoSeq_of_mul`: a nowhere-vanishing sequence satisfying the exchange
  relations is the rank-two exchange sequence of its terms of indices `1` and `2`.
* `ClusterAlgebras.rankTwoSeq_add_period`: periodicity follows from two consecutive equalities.

## Implementation notes

The integers `b, c` are usually taken positive; the definition does not need this, so it is not
assumed.
-/

@[expose] public section

namespace ClusterAlgebras

variable {F : Type*} [Field F] (b c : ℕ)

/-- The exponent `e_k` of the rank-two exchange sequence: `c` for even `k`, `b` for odd `k`. -/
@[cluster_algebras "def_rank_two_sequence"]
def rankTwoExp (k : ℤ) : ℕ :=
  if Even k then c else b

/-- The upward iteration: its `j`-th term is the pair `(z_{j+1}, z_{j+2})`. -/
def rankTwoUp (z₁ z₂ : F) : ℕ → F × F
  | 0 => (z₁, z₂)
  | j + 1 =>
    ((rankTwoUp z₁ z₂ j).2,
      ((rankTwoUp z₁ z₂ j).2 ^ rankTwoExp b c (j + 2) + 1) / (rankTwoUp z₁ z₂ j).1)

/-- The downward iteration: its `j`-th term is the pair `(z_{2-j}, z_{1-j})`. -/
def rankTwoDown (z₁ z₂ : F) : ℕ → F × F
  | 0 => (z₂, z₁)
  | j + 1 =>
    ((rankTwoDown z₁ z₂ j).2,
      ((rankTwoDown z₁ z₂ j).2 ^ rankTwoExp b c (1 - j) + 1) / (rankTwoDown z₁ z₂ j).1)

/-- The **rank-two exchange sequence** `(z_k)_{k ∈ ℤ}` of `b, c, z₁, z₂`: the sequence with the
given terms of indices `1` and `2` such that `z_{k+1} = (z_k ^ e_k + 1) / z_{k-1}` for `k ≥ 2`
and `z_{k-1} = (z_k ^ e_k + 1) / z_{k+1}` for `k ≤ 1` (`rankTwoSeq_one`, `rankTwoSeq_two`,
`rankTwoSeq_succ`, `rankTwoSeq_pred`). Division in `F` is total, so the sequence is defined for
all `b, c` and all `z₁, z₂`, including where a quotient has zero denominator. -/
@[cluster_algebras "def_rank_two_sequence"]
def rankTwoSeq (z₁ z₂ : F) (k : ℤ) : F :=
  if 1 ≤ k then (rankTwoUp b c z₁ z₂ (k - 1).toNat).1 else (rankTwoDown b c z₁ z₂ (2 - k).toNat).1

variable {b c} {z₁ z₂ : F}

/-- The `j`-th term of the upward iteration is the pair `(z_{j+1}, z_{j+2})` of terms of the
rank-two exchange sequence. -/
theorem rankTwoUp_eq (j : ℕ) :
    rankTwoUp b c z₁ z₂ j = (rankTwoSeq b c z₁ z₂ (j + 1), rankTwoSeq b c z₁ z₂ (j + 2)) := by
  have h1 : rankTwoSeq b c z₁ z₂ (j + 1) = (rankTwoUp b c z₁ z₂ j).1 := by
    rw [rankTwoSeq, if_pos (by omega)]
    congr 2
    omega
  have h2 : rankTwoSeq b c z₁ z₂ (j + 2) = (rankTwoUp b c z₁ z₂ j).2 := by
    rw [rankTwoSeq, if_pos (by omega), show ((j : ℤ) + 2 - 1).toNat = j + 1 by omega]
    rfl
  rw [h1, h2]

/-- The `j`-th term of the downward iteration is the pair `(z_{2-j}, z_{1-j})` of terms of the
rank-two exchange sequence. -/
theorem rankTwoDown_eq (j : ℕ) :
    rankTwoDown b c z₁ z₂ j = (rankTwoSeq b c z₁ z₂ (2 - j), rankTwoSeq b c z₁ z₂ (1 - j)) := by
  induction j with
  | zero =>
    have h2 : rankTwoSeq b c z₁ z₂ 2 = z₂ := by
      simp [rankTwoSeq, rankTwoUp]
    have h1 : rankTwoSeq b c z₁ z₂ 1 = z₁ := by simp [rankTwoSeq, rankTwoUp]
    simp [rankTwoDown, h1, h2]
  | succ j ih =>
    have hA : rankTwoSeq b c z₁ z₂ (2 - ((j + 1 : ℕ) : ℤ)) = (rankTwoDown b c z₁ z₂ j).2 := by
      rw [ih]
      congr 1
      push_cast
      omega
    have hB : rankTwoSeq b c z₁ z₂ (1 - ((j + 1 : ℕ) : ℤ)) = (rankTwoDown b c z₁ z₂ (j + 1)).2 := by
      rw [rankTwoSeq, if_neg (by omega), show (2 - (1 - ((j + 1 : ℕ) : ℤ))).toNat = j + 2 by omega]
      rfl
    rw [hA, hB]
    exact Prod.ext rfl rfl

/-- The term of index `1` of the rank-two exchange sequence is `z₁`. -/
@[simp]
theorem rankTwoSeq_one : rankTwoSeq b c z₁ z₂ 1 = z₁ := by
  simp [rankTwoSeq, rankTwoUp]

/-- The term of index `2` of the rank-two exchange sequence is `z₂`. -/
@[simp]
theorem rankTwoSeq_two : rankTwoSeq b c z₁ z₂ 2 = z₂ := by
  simp [rankTwoSeq, rankTwoUp]

/-- **The upward recursion**: `z_{k+1} = (z_k ^ e_k + 1) / z_{k-1}` for `k ≥ 2`. -/
@[cluster_algebras "def_rank_two_sequence"]
theorem rankTwoSeq_succ {k : ℤ} (hk : 2 ≤ k) :
    rankTwoSeq b c z₁ z₂ (k + 1) =
      (rankTwoSeq b c z₁ z₂ k ^ rankTwoExp b c k + 1) / rankTwoSeq b c z₁ z₂ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨(k - 2).toNat, by omega⟩
  have h := congrArg Prod.snd (rankTwoUp_eq (b := b) (c := c) (z₁ := z₁) (z₂ := z₂) (j + 1))
  simp only [rankTwoUp] at h
  rw [rankTwoUp_eq] at h
  push_cast at h
  rw [show (j : ℤ) + 2 + 1 = j + 1 + 2 by omega, ← h, show (j : ℤ) + 2 - 1 = j + 1 by omega]

/-- **The downward recursion**: `z_{k-1} = (z_k ^ e_k + 1) / z_{k+1}` for `k ≤ 1`. -/
@[cluster_algebras "def_rank_two_sequence"]
theorem rankTwoSeq_pred {k : ℤ} (hk : k ≤ 1) :
    rankTwoSeq b c z₁ z₂ (k - 1) =
      (rankTwoSeq b c z₁ z₂ k ^ rankTwoExp b c k + 1) / rankTwoSeq b c z₁ z₂ (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = 1 - j := ⟨(1 - k).toNat, by omega⟩
  have h := congrArg Prod.snd (rankTwoDown_eq (b := b) (c := c) (z₁ := z₁) (z₂ := z₂) (j + 1))
  simp only [rankTwoDown] at h
  rw [rankTwoDown_eq] at h
  push_cast at h
  rw [show (1 : ℤ) - j - 1 = 1 - (j + 1) by omega, ← h, show (1 : ℤ) - j + 1 = 2 - j by omega]

/-- **The exchange relations.** When every term of the rank-two exchange sequence is nonzero,
`z_{k-1} z_{k+1} = z_k ^ e_k + 1` for every `k ∈ ℤ`. -/
theorem rankTwoSeq_mul_rankTwoSeq (hne : ∀ k, rankTwoSeq b c z₁ z₂ k ≠ 0) (k : ℤ) :
    rankTwoSeq b c z₁ z₂ (k - 1) * rankTwoSeq b c z₁ z₂ (k + 1) =
      rankTwoSeq b c z₁ z₂ k ^ rankTwoExp b c k + 1 := by
  rcases le_or_gt 2 k with hk | hk
  · rw [rankTwoSeq_succ hk, mul_div_cancel₀ _ (hne _)]
  · rw [rankTwoSeq_pred (by omega), div_mul_cancel₀ _ (hne _)]

/-- **Uniqueness.** A sequence `w : ℤ → F` of nonzero elements satisfying the exchange
relations `w_{k-1} w_{k+1} = w_k ^ e_k + 1` for every `k` is the rank-two exchange sequence of
`b, c, w₁, w₂`. -/
theorem eq_rankTwoSeq_of_mul {w : ℤ → F} (hw : ∀ k, w k ≠ 0)
    (hrel : ∀ k, w (k - 1) * w (k + 1) = w k ^ rankTwoExp b c k + 1) :
    w = rankTwoSeq b c (w 1) (w 2) := by
  have up : ∀ j : ℕ, w (j + 1) = rankTwoSeq b c (w 1) (w 2) (j + 1) ∧
      w (j + 2) = rankTwoSeq b c (w 1) (w 2) (j + 2) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine ⟨by push_cast; rw [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num]; exact ih.2, ?_⟩
      have h := hrel (j + 2)
      have hz := rankTwoSeq_succ (b := b) (c := c) (z₁ := w 1) (z₂ := w 2)
        (k := (j : ℤ) + 2) (by omega)
      rw [show (j : ℤ) + 2 - 1 = j + 1 by omega] at h hz
      push_cast
      rw [show (j : ℤ) + 1 + 2 = j + 2 + 1 by omega, hz, ← ih.1, ← ih.2, ← h,
        mul_div_cancel_left₀ _ (hw _)]
  have down : ∀ j : ℕ, w (2 - j) = rankTwoSeq b c (w 1) (w 2) (2 - j) ∧
      w (1 - j) = rankTwoSeq b c (w 1) (w 2) (1 - j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine ⟨by push_cast; rw [show (2 : ℤ) - (j + 1) = 1 - j by omega]; exact ih.2, ?_⟩
      have h := hrel (1 - j)
      have hz := rankTwoSeq_pred (b := b) (c := c) (z₁ := w 1) (z₂ := w 2)
        (k := 1 - (j : ℤ)) (by omega)
      rw [show (1 : ℤ) - j + 1 = 2 - j by omega] at h hz
      push_cast
      rw [show (1 : ℤ) - (j + 1) = 1 - j - 1 by omega, hz, ← ih.1, ← ih.2, ← h,
        mul_div_cancel_right₀ _ (hw _)]
  funext k
  rcases le_or_gt 1 k with hk | hk
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨(k - 1).toNat, by omega⟩
    exact (up j).1
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = 1 - j := ⟨(1 - k).toNat, by omega⟩
    exact (down j).2

/-- **Periodicity from two consecutive equalities.** Let `p` be a shift preserving the
exponents (for instance `p` even, or `b = c`). If every term of the rank-two exchange sequence
is nonzero and `z_{1+p} = z₁`, `z_{2+p} = z₂`, then `z_{k+p} = z_k` for every `k ∈ ℤ`. -/
theorem rankTwoSeq_add_period {p : ℤ} (hp : ∀ k, rankTwoExp b c (k + p) = rankTwoExp b c k)
    (hne : ∀ k, rankTwoSeq b c z₁ z₂ k ≠ 0) (h₁ : rankTwoSeq b c z₁ z₂ (1 + p) = z₁)
    (h₂ : rankTwoSeq b c z₁ z₂ (2 + p) = z₂) (k : ℤ) :
    rankTwoSeq b c z₁ z₂ (k + p) = rankTwoSeq b c z₁ z₂ k := by
  have h := eq_rankTwoSeq_of_mul (b := b) (c := c) (w := fun k => rankTwoSeq b c z₁ z₂ (k + p))
    (fun k => hne _) (fun k => by
      have := rankTwoSeq_mul_rankTwoSeq hne (k + p)
      rw [hp] at this
      rw [show k - 1 + p = k + p - 1 by omega, show k + 1 + p = k + p + 1 by omega]
      exact this)
  have := congrFun h k
  rw [this, h₁, h₂]

/-- The exponents of the rank-two exchange sequence are unchanged by an even shift. -/
theorem rankTwoExp_add_of_even {p : ℤ} (hp : Even p) (k : ℤ) :
    rankTwoExp b c (k + p) = rankTwoExp b c k := by
  simp only [rankTwoExp, Int.even_add, hp, iff_true]

end ClusterAlgebras
