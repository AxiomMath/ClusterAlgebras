/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.MarkovQuiver
public import ClusterAlgebras.MutationTransport

/-!
# The mutation class of the Markov quiver is a single isomorphism class

The Markov quiver is self-similar: mutating it in any direction returns it up to isomorphism.
Hence its mutation equivalence class consists of a single element up to isomorphism, and in
particular it has finite mutation type.

## Main results

* `ClusterAlgebras.Quiver.nonempty_iso_markovQuiver_of_mutationEquivalent`: every quiver
  mutation equivalent to the Markov quiver is isomorphic to it.
* `ClusterAlgebras.Quiver.markovQuiver_hasFiniteMutationType`: the Markov quiver has finite
  mutation type.

## Implementation notes

The result along a mutation path, `nonempty_iso_markovQuiver_result`, is stated for any quiver
isomorphic to the Markov quiver `M` rather than for `M` itself: after one mutation the quiver
is `μ_k(M)`, which is isomorphic to `M` but not equal to it, so the statement must apply to
the tail of the path from `μ_k(M)`.
-/

@[expose] public section

namespace ClusterAlgebras

namespace Quiver

/-- **Every mutation path from a quiver isomorphic to the Markov quiver has result
isomorphic to it.** -/
theorem nonempty_iso_markovQuiver_result : ∀ {Q : Quiver (Fin 3)} (p : Q.MutationPath),
    Nonempty (Q.Iso markovQuiver) → Nonempty (p.result.Iso markovQuiver)
  | _, .nil _, h => h
  | _, .cons hk p, ⟨g⟩ =>
      nonempty_iso_markovQuiver_result p
        ⟨(g.mutate hk).trans (markovQuiver_iso_mutate (g.notMem_frozen hk)).some⟩

/-- **Everything mutation equivalent to the Markov quiver is isomorphic to it.** -/
@[cluster_algebras "lem_markov_mut_equiv_iso"]
theorem nonempty_iso_markovQuiver_of_mutationEquivalent {V : Type*} [Fintype V]
    {Q : Quiver V} (h : markovQuiver.MutationEquivalent Q) :
    Nonempty (Q.Iso markovQuiver) := by
  obtain ⟨p, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := nonempty_iso_markovQuiver_result p ⟨Iso.refl _⟩
  exact ⟨e.symm.trans f⟩

/-- **The Markov quiver has finite mutation type.** -/
@[cluster_algebras "lem_markov_finite_mutation_type"]
theorem markovQuiver_hasFiniteMutationType : markovQuiver.HasFiniteMutationType :=
  hasFiniteMutationType_of_forall_result {markovQuiver} (Set.finite_singleton _) fun p =>
    ⟨markovQuiver, rfl, nonempty_iso_markovQuiver_result p ⟨Iso.refl _⟩⟩

end Quiver

end ClusterAlgebras
