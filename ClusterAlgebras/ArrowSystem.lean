/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import Mathlib
public import ClusterAlgebras.Attr
public import ClusterAlgebras.Definitions

/-!
# Arrow systems and the cancellation of two-cycles

An *arrow system* records how many arrows run from each vertex to each other
vertex, with no arrow from a vertex to itself. Unlike a quiver it is allowed to
carry arrows in both directions between the same pair, and that latitude is what
makes it the right ambient notion for mutation: the first two steps of mutating a
quiver genuinely create opposed pairs, which the *cancellation* operator then
removes.

Arrow systems are therefore unbundled here — a plain function together with
separate predicates. Each construction below produces a bare function, and that
it is again an arrow system, or two-cycle-free, is a lemma about it. Bundling the
conditions into the data instead would make those lemmas hold by `rfl` and prove
nothing.

The *signed count* is the invariant that survives cancellation, and
`TwoCycleFree.eq_of_signedCount_eq` says it determines a two-cycle-free system
completely. That pair is what lets a mutation be identified by a count of arrows.

Finiteness of the vertex type plays no role in this file, so none is assumed; it
enters with the quiver, whose vertex set FWZ take to be finite.
-/

@[expose] public section

namespace ClusterAlgebras

variable {V : Type*} {a a' : V → V → ℕ}

attribute [cluster_algebras "def_arrow_system"] IsArrowSystem

attribute [cluster_algebras "def_signed_count"] signedCount

attribute [cluster_algebras "def_two_cycle_free"] TwoCycleFree

attribute [cluster_algebras "def_reduce"] cancellation

/-- Cancellation is truncated subtraction: subtracting the smaller of the two
counts and subtracting the opposite count agree, since both give `0` when the
opposite count is the larger. -/
theorem cancellation_eq_sub (a : V → V → ℕ) (i j : V) :
    cancellation a i j = a i j - a j i := by
  simp only [cancellation]
  omega

/-- The cancellation of an arrow system is an arrow system. -/
@[cluster_algebras "lem_reduce_arrow_system"]
theorem IsArrowSystem.cancellation (h : IsArrowSystem a) :
    IsArrowSystem (ClusterAlgebras.cancellation a) := fun v => by
  simp [cancellation_eq_sub, h v]

/-- The cancellation of any arrow system is two-cycle-free: between two vertices
it leaves arrows in at most one direction. No condition on the diagonal is
needed, so none is assumed. -/
@[cluster_algebras "lem_reduce_two_cycle_free"]
theorem cancellation_twoCycleFree (a : V → V → ℕ) :
    TwoCycleFree (cancellation a) := by
  intro i j
  simp only [cancellation_eq_sub]
  rcases le_total (a i j) (a j i) with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- Cancellation fixes a system that is already two-cycle-free: there is nothing
opposed left to cancel. -/
theorem cancellation_eq_self {a : V → V → ℕ} (h : TwoCycleFree a) : cancellation a = a := by
  funext i j
  rw [cancellation_eq_sub]
  rcases h i j with h0 | h0 <;> omega

/-- Cancellation leaves the signed count unchanged: it removes the same number
of arrows in each direction. -/
@[cluster_algebras "lem_reduce_signed_count"]
theorem signedCount_cancellation (a : V → V → ℕ) :
    signedCount (cancellation a) = signedCount a := by
  funext i j
  simp only [signedCount, cancellation_eq_sub]
  omega

/-- A two-cycle-free arrow system is determined by its signed count. This is the
extensionality principle that lets two mutations be compared by counting
arrows. -/
@[cluster_algebras "lem_two_cycle_free_ext"]
theorem TwoCycleFree.eq_of_signedCount_eq (h : TwoCycleFree a) (h' : TwoCycleFree a')
    (hβ : signedCount a = signedCount a') : a = a' := by
  funext i j
  have hij : signedCount a i j = signedCount a' i j := by rw [hβ]
  simp only [signedCount] at hij
  rcases h i j with hz | hz <;> rcases h' i j with hz' | hz' <;> omega

end ClusterAlgebras
