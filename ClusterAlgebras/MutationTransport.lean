/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.External

/-!
# Transporting a mutation along an isomorphism

An isomorphism of quivers carries a mutable vertex to a mutable vertex, and is again an
isomorphism between the two mutations. Iterating this along a mutation path, and running a path
backwards using the involutivity of mutation, gives the symmetry of mutation equivalence.

## Main definitions

* `ClusterAlgebras.Quiver.Iso.refl`: The identity isomorphism of a quiver.
* `ClusterAlgebras.Quiver.Iso.symm`: The inverse of an isomorphism of quivers.
* `ClusterAlgebras.Quiver.Iso.trans`: The composite of two isomorphisms of quivers.
* `ClusterAlgebras.Quiver.Iso.mutate`: An isomorphism `Q ≅ Q'` induces an isomorphism
  `μ_k(Q) ≅ μ_{φ(k)}(Q')`.

## Main results

* `ClusterAlgebras.Quiver.MutationPath.exists_iso_result`: A mutation path transports along an
  isomorphism.
* `ClusterAlgebras.Quiver.MutationPath.exists_result_eq`: From the result of a mutation path
  there is a mutation path back to its start.
* `ClusterAlgebras.Quiver.MutationEquivalent.symm`: Mutation equivalence is symmetric.

## Implementation notes

* The transport is proved one step of the mutation at a time — first step, reversal,
  cancellation. Each step depends only on the arrow counts, the frozen set, and equality with
  the mutating vertex, all of which an isomorphism respects. The reversal and cancellation
  lemmas are stated for an arbitrary arrow system, since the system they are applied to during
  a mutation is not the arrow system of a quiver.

* Symmetry depends on the involutivity of mutation, `ClusterAlgebras.Quiver.mutate_mutate`,
  which is assumed as an axiom.
-/

@[expose] public section

namespace ClusterAlgebras

universe u

variable {V : Type u} {V' : Type*} {V'' : Type*}
  [Fintype V] [Fintype V'] [Fintype V''] [DecidableEq V] [DecidableEq V'] [DecidableEq V'']

omit [Fintype V] [Fintype V'] in
/-- A reversal is computed from the arrow counts and equality with the mutating vertex, so a
bijection respecting the counts respects it. -/
theorem reversal_congr {c : V → V → ℕ} {c' : V' → V' → ℕ} (f : V ≃ V')
    (h : ∀ u v, c' (f u) (f v) = c u v) (k u v : V) :
    reversal c' (f k) (f u) (f v) = reversal c k u v := by
  have key : (f u = f k ∨ f v = f k) ↔ (u = k ∨ v = k) := by simp
  rw [reversal, reversal]
  by_cases hc : u = k ∨ v = k
  · rw [if_pos (key.2 hc), if_pos hc, h]
  · rw [if_neg fun hd => hc (key.1 hd), if_neg hc, h]

omit [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] in
/-- A cancellation is computed from the two arrow counts across a pair, so a bijection
respecting the counts respects it. -/
theorem cancellation_congr {c : V → V → ℕ} {c' : V' → V' → ℕ} (f : V ≃ V')
    (h : ∀ u v, c' (f u) (f v) = c u v) (u v : V) :
    cancellation c' (f u) (f v) = cancellation c u v := by
  simp only [cancellation, h]

namespace Quiver

/-- The identity isomorphism. -/
def Iso.refl (Q : Quiver V) : Q.Iso Q where
  equiv := Equiv.refl V
  mem_frozen_iff _ := Iff.rfl
  arrows_eq _ _ := rfl

/-- The inverse of an isomorphism. -/
def Iso.symm {Q : Quiver V} {Q' : Quiver V'} (e : Q.Iso Q') : Q'.Iso Q where
  equiv := e.equiv.symm
  mem_frozen_iff v := by simpa using (e.mem_frozen_iff (e.equiv.symm v)).symm
  arrows_eq u v := by simpa using (e.arrows_eq (e.equiv.symm u) (e.equiv.symm v)).symm

/-- The composite of two isomorphisms. -/
def Iso.trans {Q : Quiver V} {Q' : Quiver V'} {Q'' : Quiver V''} (e : Q.Iso Q')
    (f : Q'.Iso Q'') : Q.Iso Q'' where
  equiv := e.equiv.trans f.equiv
  mem_frozen_iff v := (f.mem_frozen_iff (e.equiv v)).trans (e.mem_frozen_iff v)
  arrows_eq u v := (f.arrows_eq (e.equiv u) (e.equiv v)).trans (e.arrows_eq u v)

omit [DecidableEq V] [DecidableEq V'] in
/-- **An isomorphism carries a mutable vertex to a mutable vertex**, the frozen sets
corresponding under it. -/
@[cluster_algebras "lem_mutation_transports_iso"]
theorem Iso.notMem_frozen {Q : Quiver V} {Q' : Quiver V'} (e : Q.Iso Q') {k : V}
    (hk : k ∉ Q.frozen) : e.equiv k ∉ Q'.frozen := fun h => hk ((e.mem_frozen_iff k).1 h)

/-- An isomorphism preserves the first step of a mutation. -/
theorem Iso.stepOne_eq {Q : Quiver V} {Q' : Quiver V'} (e : Q.Iso Q') (k u v : V) :
    Q'.stepOne (e.equiv k) (e.equiv u) (e.equiv v) = Q.stepOne k u v := by
  rw [stepOne, stepOne]
  by_cases h : u ∈ Q.frozen ∧ v ∈ Q.frozen
  · rw [if_pos ⟨(e.mem_frozen_iff u).2 h.1, (e.mem_frozen_iff v).2 h.2⟩, if_pos h, e.arrows_eq]
  · rw [if_neg fun hc => h ⟨(e.mem_frozen_iff u).1 hc.1, (e.mem_frozen_iff v).1 hc.2⟩,
      if_neg h, e.arrows_eq, e.arrows_eq, e.arrows_eq]

/-- **Mutation transports along an isomorphism**: the same bijection is an isomorphism from
`μ_k(Q)` to `μ_{φ(k)}(Q')`. -/
@[cluster_algebras "lem_mutation_transports_iso"]
def Iso.mutate {Q : Quiver V} {Q' : Quiver V'} (e : Q.Iso Q') {k : V} (hk : k ∉ Q.frozen) :
    (Q.mutate hk).Iso (Q'.mutate (e.notMem_frozen hk)) where
  equiv := e.equiv
  mem_frozen_iff v := by simpa using e.mem_frozen_iff v
  arrows_eq u v := by
    simp only [arrows_mutate, mutationArrows]
    exact cancellation_congr e.equiv (fun a b => reversal_congr e.equiv (e.stepOne_eq k) k a b) u v

namespace MutationPath

/-- **A mutation path transports along an isomorphism**: if `Q ≅ Q'`, then for every mutation
path from `Q` there is a mutation path from `Q'` whose result is isomorphic to its result. -/
theorem exists_iso_result : ∀ {Q : Quiver V} (p : Q.MutationPath) {Q' : Quiver V'}
    (_ : Q.Iso Q'), ∃ q : Q'.MutationPath, Nonempty (p.result.Iso q.result)
  | _, .nil _, _, e => ⟨.nil _, ⟨e⟩⟩
  | _, .cons hk p, _, e => by
      obtain ⟨q, ⟨f⟩⟩ := exists_iso_result p (e.mutate hk)
      exact ⟨.cons (e.notMem_frozen hk) q, ⟨f⟩⟩

/-- Equal quivers have equal mutations at a vertex, whatever the proofs of mutability. -/
theorem mutate_congr {Q R : Quiver V} (h : Q = R) {k : V} (hQ : k ∉ Q.frozen)
    (hR : k ∉ R.frozen) : Q.mutate hQ = R.mutate hR := by subst h; rfl

/-- **A mutation path can be run backwards**: from its result there is a path back to where
it started. -/
@[cluster_algebras "lem_mutation_path_reverse"]
theorem exists_result_eq : ∀ {Q : Quiver V} (p : Q.MutationPath),
    ∃ q : p.result.MutationPath, q.result = Q
  | _, .nil Q => ⟨.nil Q, rfl⟩
  | Q, .cons (k := k) hk p => by
      obtain ⟨q, hq⟩ := exists_result_eq p
      have hk' : k ∉ q.result.frozen := by rw [hq]; simpa using hk
      refine ⟨q.append (.cons hk' (.nil _)), ?_⟩
      simp only [result_append, result_cons, result_nil]
      rw [mutate_congr hq hk' hk]
      exact Quiver.mutate_mutate Q hk

end MutationPath

/-- **Mutation equivalence is symmetric.** -/
@[cluster_algebras "lem_mutation_equivalent_symm"]
theorem MutationEquivalent.symm {Q : Quiver V} {Q' : Quiver V'}
    (h : Q.MutationEquivalent Q') : Q'.MutationEquivalent Q := by
  obtain ⟨p, ⟨e⟩⟩ := h
  obtain ⟨q, hq⟩ := MutationPath.exists_result_eq p
  obtain ⟨r, ⟨f⟩⟩ := MutationPath.exists_iso_result q e
  refine ⟨r, ?_⟩
  rw [← hq]
  exact ⟨f.symm⟩

end Quiver

end ClusterAlgebras
