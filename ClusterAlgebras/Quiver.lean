/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.ArrowSystem
public import ClusterAlgebras.Definitions

/-!
# Quivers and quiver mutation

A quiver here is a finite vertex set with a distinguished subset of *frozen* vertices, carrying a
two-cycle-free arrow system with no arrow between two frozen vertices. This is not Mathlib's
`_root_.Quiver`, the category-theoretic typeclass `V → V → Sort`, which has no finiteness, no
arrow multiplicities, no two-cycle ban and no frozen vertices.

Mutation at a mutable vertex `k`, `Quiver.mutationArrows`, is the composite of three operations
on arrow systems:

* `Quiver.stepOne`, which adds `a i k * a k j` to each unfrozen pair;
* `reversal`, which reverses every arrow meeting `k`;
* `cancellation`, which deletes opposed pairs.

The result of mutation is again the arrow system of a quiver.

## Main results

* `Quiver.isArrowSystem_mutationArrows`: the mutated arrows form an arrow system.
* `Quiver.twoCycleFree_mutationArrows`: the mutated arrows are two-cycle-free.
* `Quiver.mutationArrows_eq_zero_of_frozen`: the mutated arrows join no two frozen vertices.

## Implementation notes

Mutation is defined by the three operations above rather than by the matrix mutation formula, so
that the agreement of the exchange matrix of the mutation with matrix mutation is a theorem
rather than a definitional equality. The system produced by `reversal` may contain two-cycles,
so the three operations act on arrow systems rather than on quivers.
-/

@[expose] public section

namespace ClusterAlgebras

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [cluster_algebras "def_quiver"] Quiver

namespace Quiver

omit [DecidableEq V] in
/-- A quiver is determined by its frozen set and its arrow counts: the other three fields
are proofs. -/
theorem ext' {Q Q' : Quiver V} (hf : Q.frozen = Q'.frozen) (ha : Q.arrows = Q'.arrows) :
    Q = Q' := by
  cases Q; cases Q'; subst hf; subst ha; rfl

attribute [cluster_algebras "def_mutation_step_one"] stepOne

/-- The first-step system is an arrow system. The vanishing of the correction
term on the diagonal is exactly two-cycle-freeness at `k`; that `k` is mutable is
not needed, so it is not assumed. -/
@[cluster_algebras "lem_step_one_arrow_system"]
theorem isArrowSystem_stepOne (Q : Quiver V) (k : V) : IsArrowSystem (Q.stepOne k) := by
  intro v
  simp only [stepOne]
  split
  · exact Q.isArrowSystem v
  · rcases Q.twoCycleFree v k with h | h <;> simp [Q.isArrowSystem v, h]

/-- The first step does not disturb the arrows out of `k`: the correction term
carries the factor `a k k`, which vanishes. -/
@[cluster_algebras "lem_step_one_fixes_k"]
theorem stepOne_self_left (Q : Quiver V) (k j : V) : Q.stepOne k k j = Q.arrows k j := by
  simp only [stepOne]
  split
  · rfl
  · simp [Q.isArrowSystem k]

/-- The first step does not disturb the arrows into `k`. -/
@[cluster_algebras "lem_step_one_fixes_k"]
theorem stepOne_self_right (Q : Quiver V) (k i : V) : Q.stepOne k i k = Q.arrows i k := by
  simp only [stepOne]
  split
  · rfl
  · simp [Q.isArrowSystem k]

end Quiver

attribute [cluster_algebras "def_mutation_step_two"] reversal

omit [Fintype V] in
/-- A reversal takes arrow systems to arrow systems: its values are values
of `c`, and both branches read the diagonal of `c` on the diagonal. -/
theorem isArrowSystem_reversal {c : V → V → ℕ} (h : IsArrowSystem c) (k : V) :
    IsArrowSystem (reversal c k) := by
  intro v
  simp only [reversal]
  split <;> exact h v

omit [Fintype V] in
/-- A reversal keeps a system two-cycle-free: on a pair meeting `k` it exchanges
the two directions, which preserves the property of one of them being empty. -/
theorem twoCycleFree_reversal {c : V → V → ℕ} (h : TwoCycleFree c) (k : V) :
    TwoCycleFree (reversal c k) := by
  intro i j
  simp only [reversal]
  by_cases hij : i = k ∨ j = k
  · rw [if_pos hij, if_pos hij.symm]
    exact h j i
  · rw [if_neg hij, if_neg (mt Or.symm hij)]
    exact h i j

namespace Quiver

/-- The mutated arrows form an arrow system. -/
@[cluster_algebras "lem_mutation_is_quiver"]
theorem isArrowSystem_mutationArrows (Q : Quiver V) (k : V) :
    IsArrowSystem (Q.mutationArrows k) :=
  (isArrowSystem_reversal (Q.isArrowSystem_stepOne k) k).cancellation

/-- The mutated arrows are two-cycle-free, being a cancellation. -/
@[cluster_algebras "lem_mutation_is_quiver"]
theorem twoCycleFree_mutationArrows (Q : Quiver V) (k : V) :
    TwoCycleFree (Q.mutationArrows k) :=
  cancellation_twoCycleFree _

/-- The mutated arrows still avoid joining two frozen vertices. Mutability of `k`
enters here and only here: it is what keeps a frozen pair clear of the reversal,
so the first-step system reads the pair off `Q` itself. -/
@[cluster_algebras "lem_mutation_is_quiver"]
theorem mutationArrows_eq_zero_of_frozen (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen)
    {u v : V} (hu : u ∈ Q.frozen) (hv : v ∈ Q.frozen) : Q.mutationArrows k u v = 0 := by
  have key : ∀ x y, x ∈ Q.frozen → y ∈ Q.frozen → reversal (Q.stepOne k) k x y = 0 := by
    intro x y hx hy
    have hne : ¬(x = k ∨ y = k) := by
      rintro (rfl | rfl)
      · exact hk hx
      · exact hk hy
    rw [reversal, if_neg hne, stepOne, if_pos ⟨hx, hy⟩]
    exact Q.frozen_eq_zero x hx y hy
  simp only [mutationArrows, cancellation_eq_sub, key u v hu hv, key v u hv hu]

attribute [cluster_algebras "def_quiver_mutation"] mutate

/-- Mutation does not move the frozen vertices. -/
@[simp]
theorem frozen_mutate (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) :
    (Q.mutate hk).frozen = Q.frozen := rfl

/-- The arrows of a mutation are the mutated arrows. -/
@[simp]
theorem arrows_mutate (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) :
    (Q.mutate hk).arrows = Q.mutationArrows k := rfl

end Quiver

end ClusterAlgebras
