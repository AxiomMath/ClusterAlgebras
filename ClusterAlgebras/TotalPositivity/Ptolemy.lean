/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.TotalPositivity.Segment
public import ClusterAlgebras.External

/-!
# The Ptolemy relation for Plücker coordinates of segments

Let `z` be a `2 × m` matrix over a commutative ring with `m ≥ 4`, and let `p ≠ q` be vertices of
the convex `m`-gon `ZMod m`. If `x` lies strictly between `p` and `q`, and `y` strictly between
`q` and `p`, in the cyclic order, then the segments `{p, q}` and `{x, y}` cross, and their
Plücker coordinates satisfy the **Ptolemy relation**
`P_{pq} P_{xy} = P_{px} P_{qy} + P_{py} P_{qx}`.

The representatives of `p, x, q, y` in `Fin m` are, in increasing order, `i < j < k < l`, and
`(p̄, x̄, q̄, ȳ)` is one of the four cyclic rotations of `(i, j, k, l)`. In each case the relation
is the three-term Grassmann–Plücker relation `P_{ik} P_{jl} = P_{ij} P_{kl} + P_{il} P_{jk}`,
up to the order of factors, of summands and of the elements of each pair.

## Main results

* `ClusterAlgebras.segmentPlucker_ptolemy`: the Ptolemy relation for crossing segments.

## Implementation notes

The three-term Grassmann–Plücker relation, a book exercise, enters as
`ClusterAlgebras.pluckerCoord_three_term`. The cyclic hypotheses are reduced to linear ones by
writing `m = n + 1`, so that `ZMod m` is `Fin m` and `sbtw` unfolds through `Fin.sbtw_iff`.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras. Chapter 1*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

variable {R : Type*} [CommRing R]

/-- The Ptolemy relation for `2 × n` Plücker coordinates, for columns `p, x, q, y` in cyclic
order on `Fin n`. -/
private theorem pluckerCoord_ptolemy_fin {n : ℕ} (hn : 4 ≤ n) (z : Matrix (Fin 2) (Fin n) R)
    {p q x y : Fin n} (hx : sbtw p x q) (hy : sbtw q y p) :
    pluckerCoord z {p, q} * pluckerCoord z {x, y} =
      pluckerCoord z {p, x} * pluckerCoord z {q, y} +
        pluckerCoord z {p, y} * pluckerCoord z {q, x} := by
  rw [Fin.sbtw_iff] at hx hy
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
  -- five of the nine order patterns are contradictory
  any_goals (exfalso; omega)
  · -- `y < p < x < q`
    have h := pluckerCoord_three_term hn z h3 h1 h2
    rw [Finset.pair_comm x y, Finset.pair_comm q y, Finset.pair_comm p y, Finset.pair_comm q x]
    linear_combination h
  · -- `p < x < q < y`
    have h := pluckerCoord_three_term hn z h1 h2 h4
    rw [Finset.pair_comm q x]
    linear_combination h
  · -- `x < q < y < p`
    have h := pluckerCoord_three_term hn z h1 h3 h4
    rw [Finset.pair_comm p q, Finset.pair_comm p x, Finset.pair_comm p y, Finset.pair_comm q x]
    linear_combination h
  · -- `q < y < p < x`
    have h := pluckerCoord_three_term hn z h3 h4 h2
    rw [Finset.pair_comm p q, Finset.pair_comm x y, Finset.pair_comm p y]
    linear_combination h

variable {m : ℕ} [NeZero m]

/-- **The Ptolemy relation.** For a `2 × m` matrix `z` with `m ≥ 4`, vertices `p ≠ q` of the
`m`-gon, `x` strictly between `p` and `q` and `y` strictly between `q` and `p`,
`P_{pq} P_{xy} = P_{px} P_{qy} + P_{py} P_{qx}`. -/
@[cluster_algebras "lem_ptolemy_cyclic"]
theorem segmentPlucker_ptolemy (hm : 4 ≤ m) (z : Matrix (Fin 2) (Fin m) R) {p q x y : ZMod m}
    (hpq : p ≠ q) (hx : sbtw p x q) (hy : sbtw q y p) :
    segmentPlucker z s(p, q) * segmentPlucker z s(x, y) =
      segmentPlucker z s(p, x) * segmentPlucker z s(q, y) +
        segmentPlucker z s(p, y) * segmentPlucker z s(q, x) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.ne m; omega⟩
  exact pluckerCoord_ptolemy_fin (p := p) (q := q) (x := x) (y := y) hm z hx hy

end ClusterAlgebras
