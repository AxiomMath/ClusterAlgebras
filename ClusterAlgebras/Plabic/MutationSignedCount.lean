/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Quiver

/-!
# Signed counts after a quiver mutation

Let `Q = (V, F, a)` be a quiver and `k` a mutable vertex. The signed count
`β(i, j) = a(i, j) - a(j, i)` of the mutation `μₖ(Q)` is read off from that of `Q`: it is negated
on pairs meeting `k`, unchanged on pairs of two frozen vertices, and otherwise shifted by
`a(i, k) a(k, j) - a(j, k) a(k, i)`.

## Main results

* `ClusterAlgebras.Quiver.signedCount_mutate`: the signed count of `μₖ(Q)`, together with the
  case lemmas `signedCount_mutate_of_left_eq`, `signedCount_mutate_of_right_eq`,
  `signedCount_mutate_of_frozen` and `signedCount_mutate_of_not_frozen`.

## Implementation notes

The mutation is the composite of the first step, the reversal at `k` and the cancellation;
cancellation leaves the signed count unchanged, so the computation happens on the reversal of the
first-step system.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

namespace Quiver

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The signed count of the mutated arrows is that of the reversal of the first-step system. -/
theorem signedCount_mutationArrows (Q : Quiver V) (k : V) :
    signedCount (Q.mutationArrows k) = signedCount (reversal (Q.stepOne k) k) :=
  signedCount_cancellation _

/-- On a pair whose first vertex is `k`, mutation negates the signed count. -/
theorem signedCount_mutate_of_left_eq (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) (j : V) :
    signedCount (Q.mutate hk).arrows k j = -signedCount Q.arrows k j := by
  rw [arrows_mutate, signedCount_mutationArrows]
  simp only [signedCount, reversal, true_or, or_true, if_true, stepOne_self_left,
    stepOne_self_right]
  ring

/-- On a pair whose second vertex is `k`, mutation negates the signed count. -/
theorem signedCount_mutate_of_right_eq (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) (i : V) :
    signedCount (Q.mutate hk).arrows i k = -signedCount Q.arrows i k := by
  rw [arrows_mutate, signedCount_mutationArrows]
  simp only [signedCount, reversal, true_or, or_true, if_true, stepOne_self_left,
    stepOne_self_right]
  ring

/-- On a pair of frozen vertices, mutation leaves the signed count unchanged. -/
theorem signedCount_mutate_of_frozen (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) {i j : V}
    (hi : i ∈ Q.frozen) (hj : j ∈ Q.frozen) :
    signedCount (Q.mutate hk).arrows i j = signedCount Q.arrows i j := by
  have hik : i ≠ k := fun h => hk (h ▸ hi)
  have hjk : j ≠ k := fun h => hk (h ▸ hj)
  rw [arrows_mutate, signedCount_mutationArrows]
  simp only [signedCount, reversal, hik, hjk, or_self, if_false, stepOne, hi, hj, and_self,
    if_true]

/-- On a pair avoiding `k` and not consisting of two frozen vertices, mutation adds
`a(i, k) a(k, j) - a(j, k) a(k, i)` to the signed count. -/
theorem signedCount_mutate_of_not_frozen (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) {i j : V}
    (hik : i ≠ k) (hjk : j ≠ k) (hij : ¬(i ∈ Q.frozen ∧ j ∈ Q.frozen)) :
    signedCount (Q.mutate hk).arrows i j =
      signedCount Q.arrows i j + (Q.arrows i k : ℤ) * Q.arrows k j -
        (Q.arrows j k : ℤ) * Q.arrows k i := by
  have hji : ¬(j ∈ Q.frozen ∧ i ∈ Q.frozen) := fun h => hij ⟨h.2, h.1⟩
  rw [arrows_mutate, signedCount_mutationArrows]
  simp only [signedCount, reversal, hik, hjk, or_self, if_false, stepOne, hij, hji]
  push_cast
  ring

/-- **Signed counts after a mutation** (FWZ). For a quiver `Q = (V, F, a)` and a mutable vertex
`k`, the signed count of `μₖ(Q)` at `(i, j)` is `-β_a(i, j)` if `k ∈ {i, j}`, is `β_a(i, j)` if
`k ∉ {i, j}` and `i, j ∈ F`, and is `β_a(i, j) + a(i, k) a(k, j) - a(j, k) a(k, i)` otherwise. -/
@[cluster_algebras "lem_mutation_signed_count"]
theorem signedCount_mutate (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) (i j : V) :
    signedCount (Q.mutate hk).arrows i j =
      if k = i ∨ k = j then -signedCount Q.arrows i j
      else if i ∈ Q.frozen ∧ j ∈ Q.frozen then signedCount Q.arrows i j
      else signedCount Q.arrows i j + (Q.arrows i k : ℤ) * Q.arrows k j -
        (Q.arrows j k : ℤ) * Q.arrows k i := by
  split_ifs with h1 h2
  · rcases h1 with rfl | rfl
    · exact Q.signedCount_mutate_of_left_eq hk j
    · exact Q.signedCount_mutate_of_right_eq hk i
  · exact Q.signedCount_mutate_of_frozen hk h2.1 h2.2
  · rw [not_or] at h1
    exact Q.signedCount_mutate_of_not_frozen hk (Ne.symm h1.1) (Ne.symm h1.2) h2

end Quiver

end ClusterAlgebras
