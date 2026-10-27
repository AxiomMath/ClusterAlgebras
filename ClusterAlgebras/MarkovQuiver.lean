/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.QuiverOps

/-!
# The Markov quiver is fixed by mutation

The Markov quiver `markovQuiver` is the quiver on `Fin 3` with a doubled arrow `0 → 1`, `1 → 2`
and `2 → 0`. Mutating it at any vertex yields a quiver isomorphic to it. It is not acyclic, yet
its mutation class is a single isomorphism class.

## Main results

* `markovQuiver_iso_mutate`: for every mutable vertex `k`, the mutation of `markovQuiver` at `k`
  is isomorphic to `markovQuiver`.

## Implementation notes

* The vertices are `Fin 3`, labelled `0, 1, 2` rather than `1, 2, 3`.

* Mutation at every vertex gives the same quiver, the cycle `0 → 2 → 1 → 0` with every arrow
  doubled, so the transposition of `1` and `2` is an isomorphism back to `markovQuiver` in all
  three cases, and no appeal to the cyclic symmetry of `markovQuiver` is needed.
-/

@[expose] public section

namespace ClusterAlgebras

attribute [cluster_algebras "def_markov_quiver"] markovQuiver

/-- Mutating `markovQuiver` at any mutable vertex `k` gives a quiver isomorphic to
`markovQuiver`. -/
@[cluster_algebras "lem_markov_self_similar"]
theorem markovQuiver_iso_mutate {k : Fin 3} (hk : k ∉ markovQuiver.frozen) :
    Nonempty ((markovQuiver.mutate hk).Iso markovQuiver) := by
  refine ⟨{ equiv := Equiv.swap 1 2, mem_frozen_iff := ?_, arrows_eq := ?_ }⟩
  · intro v
    rw [Quiver.frozen_mutate]
    simp [markovQuiver]
  · intro u v
    rw [Quiver.arrows_mutate]
    revert u v
    fin_cases k <;> decide

end ClusterAlgebras
