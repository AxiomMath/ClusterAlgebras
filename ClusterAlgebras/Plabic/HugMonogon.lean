/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.ParallelHugRail
public import ClusterAlgebras.Plabic.ThurstonMoves

/-!
# A hugging parallel returning path gives a hollow monogon

A parallel returning path `Q` hugging a simple strand path `P` can be turned, by swivel moves
changing the rotation only at the points of `P` it spans and at the interior points of `Q`, into a
hollow monogon [FWZ, Exercise 7.6.10].

The points of `P` from `z_{a+1}` to `z_{c+1}` and the interior points of `Q` form a staggered rail
of length `|Q| - 1` with the extra relation `η̄_{r,3} = ρ_{r,2}` (`Hugs.exists_staggeredRail`). Its
staggered combing, which is move-equivalent to the diagram
(`TripleDiagram.exists_moveEquivalent_staggeredComb`), has the tuple
`(η_{r,0}, η_{r,3}, ρ_{r,2}, …)`, so that `φ(ρ_{r,2}) = σ'(η_{r,3}) = ρ_{r,2}`: `{ρ_{r,2}}` is a
hollow monogon.

## Main results

* `ClusterAlgebras.TripleDiagram.exists_hollowMonogon_of_hugs`: a hugging parallel returning path
  gives a hollow monogon.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset RailLabel TripleData

namespace TripleDiagram

/-- Let `𝒳` be a triple diagram, `P` a simple strand path of `𝒳`, and `Q` a parallel returning path
of `P` from `z_a` to `z_c` that hugs `P`. Then there is a permutation `σ'` of the darts that
agrees with `σ` on every dart not lying at one of `z_a, …, z_c` or at an interior point of `Q`,
such that `(H, d ↦ d̄, σ', B, ε, o)` is a triple diagram move-equivalent to `𝒳` that has a hollow
monogon.

Indices are `0`-indexed as in `TripleData.IsReturningPath`: `Hugs P ζ Q a c` is a returning path
from the interior point `z_{a+1}` (entry `a` of `interiorPoints P`) to `z_{c+1}` (entry `c`), and
it is parallel when `a < c`; the points `z_{a+1}, …, z_{c+1}` are the entries of index
`a, …, c`. -/
@[cluster_algebras "lem_hug_parallel_monogon"]
theorem exists_hollowMonogon_of_hugs {b : ℕ} (X : TripleDiagram b)
    {P Q : List X.Dart} {ζ : StrandSide} {a c : ℕ} (hac : a < c)
    (hQ : X.data.Hugs P ζ Q a c) :
    ∃ σ' : Equiv.Perm X.Dart,
      (∀ d, (∀ l, a ≤ l → l ≤ c → (X.data.interiorPoints P)[l]? ≠ some (X.data.vertexOf d)) →
        X.data.vertexOf d ∉ X.data.interiorPoints Q → σ' d = X.data.rot d) ∧
      ∃ h : ({ X.data with rot := σ' } : TripleData X.Dart b).IsTripleDiagram,
        X.MoveEquivalent
          { Dart := X.Dart, data := { X.data with rot := σ' }, isTripleDiagram := h } ∧
        ∃ e, ({ X.data with rot := σ' } : TripleData X.Dart b).IsHollowMonogon {e} := by
  have hP := X.isTripleDiagram.toIsPreTripleDiagram
  obtain ⟨R, hclose, hpts⟩ := hQ.exists_staggeredRail hP hac
  obtain ⟨h, hmv⟩ := exists_moveEquivalent_staggeredComb X R
  have hr1 : 1 ≤ Q.length - 1 := R.one_le
  refine ⟨R.staggeredComb.rot, fun d hd hdQ => ?_, h, hmv, R.dart (rho (Q.length - 1) 2), ?_⟩
  · refine R.staggeredComb_rot_of_notMem fun hdR => ?_
    rcases hpts d hdR with ⟨l, hl1, hl2, hl⟩ | h'
    · exact hd l hl1 hl2 hl
    · exact hdQ h'
  · have hlast : [eta (Q.length - 1) 0, eta (Q.length - 1) 3, rho (Q.length - 1) 2,
        rho (Q.length - 1) 3, eta (Q.length - 1) 4, rho (Q.length - 1 - 1) 3] ∈
        staggeredCombLabels (Q.length - 1) :=
      (mem_staggeredCombLabels_iff hr1).2 (Or.inr (Or.inr (Or.inl rfl)))
    have hrot := (R.agreesOn_staggeredComb hP).1 _ hlast 1 (by simp)
    have hinv : X.data.inv (R.dart (rho (Q.length - 1) 2)) = R.dart (eta (Q.length - 1) 3) := by
      rw [← hclose, hP.inv_involutive]
    refine DiskMap.isHollowMonogon_singleton _ (R.toRailPoints.dart_notMem_bdry
      (rho_mem_labelSet le_rfl (by norm_num))) ?_
    change R.staggeredComb.rot (X.data.inv (R.dart (rho (Q.length - 1) 2))) =
      R.dart (rho (Q.length - 1) 2)
    rw [hinv]
    exact hrot

end TripleDiagram

end ClusterAlgebras
