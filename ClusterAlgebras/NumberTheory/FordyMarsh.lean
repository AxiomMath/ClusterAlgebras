/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.NumberTheory.FordyMarshMatrix
public import ClusterAlgebras.NumberTheory.RotationSequence
public import ClusterAlgebras.LaurentPhenomenon.Laurent

/-!
# The Fordy–Marsh recurrences and their Laurent property

Let `n ≥ 1` and let `a = (a₁, …, a_{n-1})` be an integer vector. The Fordy–Marsh sequence of
`a` is the sequence `(z_t)_{t ≥ 1}` in the field `ℚ(Z₁, …, Zₙ)` of rational functions with
`z_t = Z_t` for `t ∈ [1, n]` and
`z_{t+n} = (∏_{i=1}^{n-1} z_{t+i}^{[a_i]₊} + ∏_{i=1}^{n-1} z_{t+i}^{[-a_i]₊}) / z_t`.

When `a` is palindromic, `aᵢ = a_{n-i}`, the Fordy–Marsh matrix `B_a` satisfies
`μ₁(B_a) = ρ(B_a)` and its first column is `a`, so mutating the generic seed `(Z, B_a)`
successively in the directions `1, 2, …, n, 1, 2, …` produces exactly the terms of the
sequence. By the Laurent phenomenon every term is then an integer Laurent polynomial in
`Z₁, …, Zₙ`.

## Main definitions

* `ClusterAlgebras.fordyMarshSeq`: the Fordy–Marsh sequence of `a`.

## Main results

* `ClusterAlgebras.fordyMarshSeq_add`: the Fordy–Marsh recurrence.
* `ClusterAlgebras.fordyMarshSeq_mem_laurentSubring`: for palindromic `a`, every term lies in
  `ℤ[Z₁^{±1}, …, Zₙ^{±1}]`.
* `ClusterAlgebras.fordyMarshSeq_ne_zero`: for palindromic `a`, no term vanishes.

## Implementation notes

FWZ index the sequence from `1` and the indeterminates by `[1, n]`; here both are
indexed from `0`, so FWZ's `z_t` is `fordyMarshSeq n a (t - 1)` and their `Z_i` is the
indeterminate `X (i - 1)` of `MvPolynomial (Fin n) ℚ`, viewed in its field of fractions. The
initial terms are then `fordyMarshSeq n a t = X t` for `t < n`, and the recurrence keeps its
form, `z (t + n) = (∏_{i=1}^{n-1} z (t + i) ^ [a_i]₊ + ∏_{i=1}^{n-1} z (t + i) ^ [-a_i]₊) / z t`
for every `t ≥ 0`, with the product running over the nonzero `i : Fin n`. The vector `a` is a
function `ℕ → ℤ` of which only `a₁, …, a_{n-1}` are read, and `[x]₊` is `Int.toNat x`.

FWZ assume `n ≥ 1`, which the recursion needs (it divides by the term `n` places
back); it is the instance argument `[NeZero n]`.

## References

* [fordy-marsh] A. P. Fordy, B. Marsh, *Cluster mutation-periodic quivers and associated
  Laurent sequences*, J. Algebraic Combin. 34 (2011), 19–66.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

variable (n : ℕ) [NeZero n] (a : ℕ → ℤ)

/-- The **Fordy–Marsh sequence** of `a`, in `ℚ(X₀, …, X_{n-1})`: its terms `t < n` are the
indeterminates `X t`, and the term `t + n` is
`(∏_{i=1}^{n-1} z (t + i) ^ [a_i]₊ + ∏_{i=1}^{n-1} z (t + i) ^ [-a_i]₊) / z t`.
FWZ index from `1`, so their `z_t` is the term `t - 1` here. -/
@[cluster_algebras "def_fordy_marsh_sequence"]
noncomputable def fordyMarshSeq : ℕ → FractionRing (MvPolynomial (Fin n) ℚ)
  | t =>
    if h : t < n then algebraMap (MvPolynomial (Fin n) ℚ) _ (MvPolynomial.X ⟨t, h⟩)
    else
      (∏ i ∈ univ.erase (0 : Fin n), fordyMarshSeq (t - n + i) ^ (a i).toNat +
          ∏ i ∈ univ.erase (0 : Fin n), fordyMarshSeq (t - n + i) ^ (-a i).toNat) /
        fordyMarshSeq (t - n)
decreasing_by
  all_goals have := NeZero.pos n
  all_goals omega

variable {n a}

/-- The initial terms of the Fordy–Marsh sequence are the indeterminates. -/
theorem fordyMarshSeq_of_lt {t : ℕ} (ht : t < n) :
    fordyMarshSeq n a t = algebraMap (MvPolynomial (Fin n) ℚ) _ (MvPolynomial.X ⟨t, ht⟩) := by
  rw [fordyMarshSeq, dif_pos ht]

/-- On `i : Fin n`, the term `i` of the Fordy–Marsh sequence is the indeterminate `X i`. -/
@[simp]
theorem fordyMarshSeq_val (i : Fin n) :
    fordyMarshSeq n a i = algebraMap (MvPolynomial (Fin n) ℚ) _ (MvPolynomial.X i) :=
  fordyMarshSeq_of_lt i.isLt

variable (n a) in
/-- **The Fordy–Marsh recurrence**:
`z (t + n) = (∏_{i=1}^{n-1} z (t + i) ^ [a_i]₊ + ∏_{i=1}^{n-1} z (t + i) ^ [-a_i]₊) / z t`. -/
theorem fordyMarshSeq_add (t : ℕ) :
    fordyMarshSeq n a (t + n) =
      (∏ i ∈ univ.erase (0 : Fin n), fordyMarshSeq n a (t + i) ^ (a i).toNat +
          ∏ i ∈ univ.erase (0 : Fin n), fordyMarshSeq n a (t + i) ^ (-a i).toNat) /
        fordyMarshSeq n a t := by
  rw [fordyMarshSeq, dif_neg (by omega), Nat.add_sub_cancel]

omit [NeZero n] in
/-- The Fordy–Marsh matrix is extended skew-symmetrizable, as a square matrix. -/
theorem extSkewSymmetrizable_fordyMarshMatrix :
    ExtSkewSymmetrizable le_rfl (fordyMarshMatrix n a) := by
  simpa [ExtSkewSymmetrizable, Fin.castLE_rfl] using skewSymmetrizable_fordyMarshMatrix a

/-- **The Fordy–Marsh sequence as a sequence of cluster mutations.** For palindromic `a`,
each term of the Fordy–Marsh sequence is an entry of the extended cluster of a seed obtained
from the generic seed `(X, B_a)` by a sequence of mutations. -/
theorem exists_fordyMarshSeq_eq_seedMutationSeq_extCluster
    (ha : ∀ i, 1 ≤ i → i ≤ n - 1 → a i = a (n - i)) (t : ℕ) :
    ∃ (s : List (Fin n)) (i : Fin n),
      fordyMarshSeq n a t =
        (seedMutationSeq le_rfl (genericSeed (fordyMarshMatrix n a)) s).extCluster i := by
  set B := fordyMarshMatrix n a
  set S₀ := genericSeed B
  have hlab₀ : IsLabeledSeed ℚ le_rfl S₀ :=
    isLabeledSeed_genericSeed le_rfl extSkewSymmetrizable_fordyMarshMatrix
  let S : ℕ → SeedData _ n n := fun s =>
    seedMutationSeq le_rfl S₀ ((List.range s).map (rotationDirection n))
  let w : ℕ → FractionRing (MvPolynomial (Fin n) ℚ) := fun t =>
    if h : t < n then S₀.extCluster ⟨t, h⟩
    else (S (t - n + 1)).extCluster (rotationDirection n (t - n))
  have hwS : ∀ t, ∃ s i, w t = (S s).extCluster i := by
    intro t
    by_cases h : t < n
    · exact ⟨0, ⟨t, h⟩, by simp [w, S, h]⟩
    · exact ⟨t - n + 1, rotationDirection n (t - n), by simp [w, h]⟩
  have hS : ∀ s, S (s + 1) = seedMutation le_rfl (S s) (rotationDirection n s) := by
    intro s
    simp [S, List.range_succ]
  have hlab : ∀ s, IsLabeledSeed ℚ le_rfl (S s) := fun s => hlab₀.seedMutationSeq le_rfl _
  have hS0 : S 0 = ⟨fun i => w i, B⟩ := by
    simp only [S, List.range_zero, List.map_nil, seedMutationSeq_nil]
    refine SeedData.ext ?_ rfl
    funext i
    simp [w]
  have hw : ∀ s, (S (s + 1)).extCluster (rotationDirection n s) = w (s + n) := by
    intro s
    simp [w]
  have hrec := rotationSequence_recurrence (fordyMarshMatrix_rotation ha) hlab hS0 hS hw
  have hne : ∀ t, w t ≠ 0 := by
    intro t
    obtain ⟨s, i, h⟩ := hwS t
    exact h ▸ hlab₀.seedMutationSeq_extCluster_ne_zero le_rfl _ i
  have heq : ∀ t, fordyMarshSeq n a t = w t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
    by_cases h : t < n
    · simp [fordyMarshSeq_of_lt h, w, h, S₀, genericSeed]
    obtain ⟨s, rfl⟩ : ∃ s, t = s + n := ⟨t - n, by omega⟩
    have hlt : ∀ i : Fin n, s + i < s + n := fun i => by omega
    have hs : fordyMarshSeq n a s = w s := ih s (by have := NeZero.pos n; omega)
    rw [fordyMarshSeq_add, div_eq_iff (hs ▸ hne s), hs, hrec]
    congr 1 <;> refine prod_congr rfl fun i hi => ?_ <;>
      rw [ih _ (hlt i), fordyMarshMatrix_apply_zero a i (ne_of_mem_erase hi)]
  obtain ⟨s, i, h⟩ := hwS t
  exact ⟨_, i, (heq t).trans h⟩

/-- **The Fordy–Marsh recurrences have the Laurent property.** For palindromic `a`,
`aᵢ = a_{n-i}` for `i ∈ [1, n - 1]`, every term of the Fordy–Marsh sequence of `a` lies in
`ℤ[X₀^{±1}, …, X_{n-1}^{±1}]`. -/
@[cluster_algebras "thm_fordy_marsh_laurent"]
theorem fordyMarshSeq_mem_laurentSubring (ha : ∀ i, 1 ≤ i → i ≤ n - 1 → a i = a (n - i)) (t : ℕ) :
    fordyMarshSeq n a t ∈ laurentSubring fun i : Fin n =>
      algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
        (MvPolynomial.X i) := by
  obtain ⟨s, i, h⟩ := exists_fordyMarshSeq_eq_seedMutationSeq_extCluster ha t
  rw [h]
  exact (isLabeledSeed_genericSeed le_rfl extSkewSymmetrizable_fordyMarshMatrix
    ).seedMutationSeq_extCluster_mem_laurentSubring le_rfl s i

/-- For palindromic `a`, no term of the Fordy–Marsh sequence vanishes. -/
theorem fordyMarshSeq_ne_zero (ha : ∀ i, 1 ≤ i → i ≤ n - 1 → a i = a (n - i)) (t : ℕ) :
    fordyMarshSeq n a t ≠ 0 := by
  obtain ⟨s, i, h⟩ := exists_fordyMarshSeq_eq_seedMutationSeq_extCluster ha t
  rw [h]
  exact (isLabeledSeed_genericSeed le_rfl extSkewSymmetrizable_fordyMarshMatrix
    ).seedMutationSeq_extCluster_ne_zero le_rfl s i

end ClusterAlgebras
