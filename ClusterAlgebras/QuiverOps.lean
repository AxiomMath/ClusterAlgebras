/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Quiver

/-!
# Sources, sinks, opposites, isomorphisms, and the mutable part

A source or a sink `k` of a quiver is a vertex at which every correction term
`a i k * a k j` of mutation vanishes, so mutating at a mutable source or sink only reverses
the arrows at `k`.

The opposite quiver has the same vertices and frozen set, with every arrow reversed. The
mutable part is the quiver on the subtype of mutable vertices, with no frozen vertices.

## Main definitions

* `Quiver.op`: The opposite of a quiver.
* `Quiver.mutablePart`: The quiver carried by the mutable vertices.

## Main results

* `Quiver.mutate_arrows_of_isSource`: Mutation at a mutable source reverses the arrows at it.
* `Quiver.mutate_arrows_of_isSink`: Mutation at a mutable sink reverses the arrows at it.
-/

@[expose] public section

namespace ClusterAlgebras

variable {V : Type*} [Fintype V]

namespace Quiver

attribute [cluster_algebras "def_source"] IsSource

attribute [cluster_algebras "def_sink"] IsSink

/-- The arrow system of the opposite quiver, with every arrow reversed. -/
def opArrows (Q : Quiver V) : V → V → ℕ := fun i j => Q.arrows j i

/-- The arrows of `Q.opArrows` are those of `Q`, reversed. -/
@[simp]
theorem opArrows_apply (Q : Quiver V) (i j : V) : Q.opArrows i j = Q.arrows j i := rfl

/-- Reversing every arrow leaves an arrow system. -/
@[cluster_algebras "lem_opposite_is_quiver"]
theorem isArrowSystem_opArrows (Q : Quiver V) : IsArrowSystem Q.opArrows :=
  Q.isArrowSystem

/-- Reversing every arrow keeps the system two-cycle-free: the unordered pair of
opposed counts is unchanged. -/
@[cluster_algebras "lem_opposite_is_quiver"]
theorem twoCycleFree_opArrows (Q : Quiver V) : TwoCycleFree Q.opArrows :=
  fun i j => Q.twoCycleFree j i

/-- Reversing every arrow still joins no two frozen vertices. -/
@[cluster_algebras "lem_opposite_is_quiver"]
theorem opArrows_eq_zero_of_frozen (Q : Quiver V) {u v : V} (hu : u ∈ Q.frozen)
    (hv : v ∈ Q.frozen) : Q.opArrows u v = 0 :=
  Q.frozen_eq_zero v hv u hu

/-- The **opposite** of `Q`: the same vertices and frozen set, every arrow
reversed. -/
@[cluster_algebras "def_opposite_quiver"]
def op (Q : Quiver V) : Quiver V where
  frozen := Q.frozen
  arrows := Q.opArrows
  isArrowSystem := Q.isArrowSystem_opArrows
  twoCycleFree := Q.twoCycleFree_opArrows
  frozen_eq_zero _ hu _ hv := Q.opArrows_eq_zero_of_frozen hu hv

/-- Taking the opposite does not move the frozen vertices. -/
@[simp]
theorem frozen_op (Q : Quiver V) : Q.op.frozen = Q.frozen := rfl

/-- The arrows of the opposite run the other way. -/
@[simp]
theorem arrows_op (Q : Quiver V) (i j : V) : Q.op.arrows i j = Q.arrows j i := rfl

attribute [cluster_algebras "def_quiver_isomorphism"] Iso

variable [DecidableEq V]

/-- At a source the first step is inert: every correction has `a i k = 0` as a
factor. -/
theorem stepOne_of_isSource (Q : Quiver V) {k : V} (hs : Q.IsSource k) :
    Q.stepOne k = Q.arrows := by
  funext i j
  rw [stepOne]
  split
  · rfl
  · rw [hs i, zero_mul, add_zero]

/-- At a sink the first step is inert: every correction has `a k j = 0` as a
factor. -/
theorem stepOne_of_isSink (Q : Quiver V) {k : V} (hs : Q.IsSink k) :
    Q.stepOne k = Q.arrows := by
  funext i j
  rw [stepOne]
  split
  · rfl
  · rw [hs j, mul_zero, add_zero]

/-- **Mutating at a mutable source is just reversing the arrows at it.** -/
@[cluster_algebras "lem_mut_at_source"]
theorem mutate_arrows_of_isSource (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen)
    (hs : Q.IsSource k) : (Q.mutate hk).arrows = reversal Q.arrows k := by
  rw [arrows_mutate, mutationArrows, stepOne_of_isSource Q hs,
    cancellation_eq_self (twoCycleFree_reversal Q.twoCycleFree k)]

/-- **Mutating at a mutable sink is just reversing the arrows at it.** -/
@[cluster_algebras "lem_mut_at_sink"]
theorem mutate_arrows_of_isSink (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen)
    (hs : Q.IsSink k) : (Q.mutate hk).arrows = reversal Q.arrows k := by
  rw [arrows_mutate, mutationArrows, stepOne_of_isSink Q hs,
    cancellation_eq_self (twoCycleFree_reversal Q.twoCycleFree k)]

/-- The **mutable part** of `Q`: the quiver carried by the mutable vertices alone,
with no frozen vertices of its own. -/
@[cluster_algebras "def_mutable_part"]
def mutablePart (Q : Quiver V) : Quiver {v : V // v ∉ Q.frozen} where
  frozen := ∅
  arrows u v := Q.arrows u v
  isArrowSystem v := Q.isArrowSystem v
  twoCycleFree u v := Q.twoCycleFree u v
  frozen_eq_zero := by simp

/-- The mutable part has no frozen vertices. -/
@[simp]
theorem frozen_mutablePart (Q : Quiver V) : Q.mutablePart.frozen = ∅ := rfl

/-- The arrows of the mutable part are those of `Q` between mutable vertices. -/
@[simp]
theorem arrows_mutablePart (Q : Quiver V) (u v : {v : V // v ∉ Q.frozen}) :
    Q.mutablePart.arrows u v = Q.arrows u v := rfl

end Quiver

end ClusterAlgebras
