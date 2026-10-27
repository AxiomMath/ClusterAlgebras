/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.TreesInequivalent

/-!
# Mutation equivalent acyclic quivers have the same underlying graph

All acyclic quivers without frozen vertices in one mutation equivalence class have the same
underlying undirected graph, as a consequence of the Caldero–Keller theorem
`ClusterAlgebras.caldero_keller`.

The underlying graph with its multiplicities is the function `(u, v) ↦ a u v + a v u`, so the
claim is that some bijection of the vertices carries one such function to the other.

## Main results

* `ClusterAlgebras.exists_equiv_arrows_add_arrows_of_mutationEquivalent`: mutation equivalent
  acyclic quivers without frozen vertices have the same underlying graph, up to a bijection of
  the vertices.

## Implementation notes

* The invariant used is `ClusterAlgebras.Quiver.MutationPath.arrows_add_arrows_of_atSourceOrSink`:
  a path through sources and sinks preserves the sum `a u v + a v u`.
* The conclusion is a bijection of the vertex sets, not an equality of graphs: mutation
  equivalence is insensitive to relabelling, so the labels are not determined.
-/

@[expose] public section

namespace ClusterAlgebras

universe u

/-- Mutation equivalent acyclic quivers without frozen vertices have the same underlying graph:
there is a bijection `f` of the vertices with
`Q'.arrows (f u) (f v) + Q'.arrows (f v) (f u) = Q.arrows u v + Q.arrows v u` for all `u`, `v`. -/
@[cluster_algebras "lem_acyclic_mut_equiv_same_graph"]
theorem exists_equiv_arrows_add_arrows_of_mutationEquivalent {V V' : Type u} [Fintype V]
    [Fintype V'] [DecidableEq V] {Q : Quiver V} {Q' : Quiver V'} (hQ : Acyclic Q)
    (hQ' : Acyclic Q') (hfQ : Q.frozen = ∅) (hfQ' : Q'.frozen = ∅)
    (h : Q.MutationEquivalent Q') :
    ∃ f : V ≃ V', ∀ u v,
      Q'.arrows (f u) (f v) + Q'.arrows (f v) (f u) = Q.arrows u v + Q.arrows v u := by
  obtain ⟨p, hsos, ⟨e⟩⟩ := caldero_keller hQ hQ' hfQ hfQ' h
  refine ⟨e.equiv, fun u v => ?_⟩
  rw [e.arrows_eq, e.arrows_eq]
  exact p.arrows_add_arrows_of_atSourceOrSink hsos u v

end ClusterAlgebras
