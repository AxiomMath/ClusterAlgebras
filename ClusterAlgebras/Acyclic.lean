/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.Graph

/-!
# Oriented cycles, and acyclic quivers

An oriented cycle in a quiver is a closed sequence of vertices, distinct apart from the
repetition that closes it, each carrying an arrow to the next; a quiver is acyclic when it
has none.

## Main results

* `IsOrientedCycle.two_le`: An oriented cycle has length at least two.
* `acyclic_of_arrows_eq_zero`: A quiver with no arrows is acyclic.

## Implementation notes

* An oriented cycle is a pair `(r, v)` with `r` its length and `v : ℕ → V` the sequence,
  rather than a `List V` or a `Fin r → V` with cyclic indices, so that `v t` and `v (t + 1)`
  are both available under the hypothesis `t < r` without a coercion. The conditions only
  constrain `v` on `[0, r]`.
* The distinctness condition is `Set.InjOn v (Set.Iio r)`: the vertices `v 0, …, v (r-1)`
  are pairwise distinct, and `v r` is excluded because it is `v 0`.
-/

@[expose] public section

namespace ClusterAlgebras

variable {V : Type*} [Fintype V]

attribute [cluster_algebras "def_oriented_cycle"] IsOrientedCycle

attribute [cluster_algebras "def_acyclic"] Acyclic

namespace IsOrientedCycle

variable {Q : Quiver V} {r : ℕ} {v : ℕ → V}

/-- The length of an oriented cycle is at least one. -/
theorem one_le (h : IsOrientedCycle Q r v) : 1 ≤ r := h.1

/-- An oriented cycle closes up. -/
theorem apply_length (h : IsOrientedCycle Q r v) : v r = v 0 := h.2.1

/-- The first `r` vertices of an oriented cycle are pairwise distinct. -/
theorem injOn (h : IsOrientedCycle Q r v) : Set.InjOn v (Set.Iio r) := h.2.2.1

/-- Each step of an oriented cycle carries an arrow. -/
theorem arrows_pos (h : IsOrientedCycle Q r v) {t : ℕ} (ht : t < r) :
    0 < Q.arrows (v t) (v (t + 1)) := h.2.2.2 t ht

/-- Consecutive vertices of an oriented cycle are distinct: an arrow joins no vertex to
itself. -/
theorem apply_ne_apply_succ (h : IsOrientedCycle Q r v) {t : ℕ} (ht : t < r) :
    v t ≠ v (t + 1) := by
  intro hv
  have := h.arrows_pos ht
  rw [hv] at this
  exact absurd (Q.isArrowSystem (v (t + 1))) this.ne'

/-- An oriented cycle has length at least two: at length one it would need an arrow from
a vertex to itself. -/
theorem two_le (h : IsOrientedCycle Q r v) : 2 ≤ r := by
  rcases Nat.lt_or_ge r 2 with hr | hr
  · interval_cases r
    · exact absurd h.one_le (by omega)
    · exact absurd (h.apply_length.symm.trans rfl) (h.apply_ne_apply_succ (by omega))
  · exact hr

end IsOrientedCycle

/-- A quiver with no arrows at all is acyclic. -/
theorem acyclic_of_arrows_eq_zero {Q : Quiver V} (h : ∀ u v, Q.arrows u v = 0) :
    Acyclic Q :=
  fun _ _ hc => absurd (h _ _) (hc.arrows_pos (t := 0) hc.one_le).ne'

end ClusterAlgebras
