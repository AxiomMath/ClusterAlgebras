/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.QuiverOps

/-!
# Mutation paths, mutation equivalence, and mutation type

Mutation generates an equivalence: two quivers are *mutation equivalent* when a finite
sequence of mutations carries one to a quiver isomorphic to the other. This file
introduces the sequence (`ClusterAlgebras.Quiver.MutationPath`), the relation it generates
(`ClusterAlgebras.Quiver.MutationEquivalent`), the coarser relation obtained by first
discarding the frozen vertices (`ClusterAlgebras.Quiver.SameType`), and the finiteness
condition singling out the quivers with only finitely many mutation classes
(`ClusterAlgebras.Quiver.HasFiniteMutationType`).

FWZ describe a mutation path as a pair of finite sequences: quivers
`Q₀, …, Q_r` with `Q₀ = Q`, and vertices `k₁, …, k_r`, each `k_t` mutable in `Q_{t-1}`
and the arrow system of `Q_t` that of `μ_{k_t}(Q_{t-1})`. A quiver is its frozen set
together with its arrow system — its three conditions are propositions — and mutation
moves neither the vertex set nor the frozen set (`ClusterAlgebras.Quiver.frozen_mutate`),
so pinning the arrow system of `Q_t` pins `Q_t = μ_{k_t}(Q_{t-1})`. A path is therefore
recorded here as the chain of mutations itself: a list of vertices, each carrying the
proof that it is mutable in the quiver the chain has reached. Recording the intermediate
quivers as data would only repeat what the vertices already determine, while keeping the
chain — rather than a bare list of vertices — is what lets a condition on the *steps* of a
path, such as each being at a source or a sink of the quiver it is applied to, be stated
by recursion over the path.

`Quiver.MutationEquivalent` is heterogeneous in the vertex type, as `Quiver.Iso` is:
equivalence to a quiver on some other vertex set is exactly what the relation gets used
for. Reflexivity is immediate (`Quiver.MutationEquivalent.refl`); symmetry and
transitivity rest on mutation being an involution and on isomorphisms transporting
mutations, which are separate results and not assumed here.

For finite mutation type FWZ ask that the set of isomorphism classes of quivers
mutation equivalent to `Q` be finite. Rather than form that quotient, the condition is
recorded as the existence of a finite set of quivers meeting every one of those classes.
Representatives on `V` itself suffice, and none are lost: a quiver mutation equivalent to
`Q` is by definition isomorphic to the result of a path from `Q`, and every such result is
a quiver on `V`.
-/

@[expose] public section

namespace ClusterAlgebras

universe u

namespace Quiver

variable {V : Type u} [Fintype V] [DecidableEq V]

attribute [cluster_algebras "def_mutation_path"] MutationPath

namespace MutationPath

attribute [cluster_algebras "def_mutation_path"] result

/-- The empty path leaves the quiver alone. -/
@[simp]
theorem result_nil (Q : Quiver V) : (nil Q).result = Q := rfl

/-- A path beginning with a mutation at `k` ends where the rest of it ends, started from
`μ_k(Q)`. -/
@[simp]
theorem result_cons {Q : Quiver V} {k : V} (hk : k ∉ Q.frozen)
    (p : (Q.mutate hk).MutationPath) : (cons hk p).result = p.result := rfl

/-- The result of a mutation path has the same frozen vertices as the quiver it starts from. -/
@[simp]
theorem frozen_result {Q : Quiver V} (p : Q.MutationPath) : p.result.frozen = Q.frozen := by
  induction p with
  | nil Q => rfl
  | cons hk p ih => simpa using ih

/-- The **concatenation** of a mutation path from `Q` with one from its result. -/
def append : {Q : Quiver V} → (p : Q.MutationPath) → p.result.MutationPath → Q.MutationPath
  | _, .nil _, q => q
  | _, .cons hk p, q => .cons hk (p.append q)

/-- Concatenating two paths composes their effects. -/
@[simp]
theorem result_append : ∀ {Q : Quiver V} (p : Q.MutationPath) (q : p.result.MutationPath),
    (p.append q).result = q.result
  | _, .nil _, _ => rfl
  | _, .cons _ p, q => result_append p q

end MutationPath

variable {V' V'' : Type*} [Fintype V'] [Fintype V'']

attribute [cluster_algebras "def_mutation_equivalent"] MutationEquivalent

/-- A quiver is mutation equivalent to the result of any mutation path from it. -/
theorem mutationEquivalent_result {Q : Quiver V} (p : Q.MutationPath) :
    Q.MutationEquivalent p.result :=
  ⟨p, ⟨⟨Equiv.refl V, fun _ => Iff.rfl, fun _ _ => rfl⟩⟩⟩

/-- A quiver is mutation equivalent to its mutation at any mutable vertex. -/
theorem mutationEquivalent_mutate (Q : Quiver V) {k : V} (hk : k ∉ Q.frozen) :
    Q.MutationEquivalent (Q.mutate hk) :=
  mutationEquivalent_result (.cons hk (.nil _))

/-- Isomorphic quivers are mutation equivalent. -/
theorem MutationEquivalent.of_iso {Q : Quiver V} {Q' : Quiver V'} (e : Q.Iso Q') :
    Q.MutationEquivalent Q' :=
  ⟨.nil Q, ⟨e⟩⟩

/-- Mutation equivalence is reflexive. -/
@[refl]
theorem MutationEquivalent.refl (Q : Quiver V) : Q.MutationEquivalent Q :=
  mutationEquivalent_result (.nil Q)

/-- Mutation equivalence may be composed with an isomorphism on the right. -/
theorem MutationEquivalent.trans_iso {Q : Quiver V} {Q' : Quiver V'} {Q'' : Quiver V''}
    (h : Q.MutationEquivalent Q') (e : Q'.Iso Q'') : Q.MutationEquivalent Q'' := by
  obtain ⟨p, ⟨f⟩⟩ := h
  refine ⟨p, ⟨⟨f.equiv.trans e.equiv, fun v => ?_, fun u v => ?_⟩⟩⟩
  · exact (e.mem_frozen_iff (f.equiv v)).trans (f.mem_frozen_iff v)
  · exact (e.arrows_eq (f.equiv u) (f.equiv v)).trans (f.arrows_eq u v)

/-- A quiver has **finite mutation type** when the quivers mutation equivalent to it fall
into finitely many isomorphism classes: some finite set of quivers meets every one of
those classes. -/
@[cluster_algebras "def_finite_mutation_type"]
def HasFiniteMutationType (Q : Quiver V) : Prop :=
  ∃ S : Set (Quiver V), S.Finite ∧
    ∀ R : Quiver V, Q.MutationEquivalent R → ∃ R' ∈ S, Nonempty (R.Iso R')

/-- Finite mutation type may be checked on the results of mutation paths alone: every
quiver mutation equivalent to `Q` is isomorphic to one of them. -/
theorem hasFiniteMutationType_of_forall_result {Q : Quiver V} (S : Set (Quiver V))
    (hS : S.Finite) (h : ∀ p : Q.MutationPath, ∃ R ∈ S, Nonempty (p.result.Iso R)) :
    Q.HasFiniteMutationType := by
  refine ⟨S, hS, ?_⟩
  rintro R ⟨p, ⟨f⟩⟩
  obtain ⟨R', hR', ⟨g⟩⟩ := h p
  refine ⟨R', hR', ⟨⟨f.equiv.symm.trans g.equiv, fun v => ?_, fun u v => ?_⟩⟩⟩
  · have hf := f.mem_frozen_iff (f.equiv.symm v)
    simp only [Equiv.apply_symm_apply] at hf
    simpa [hf] using g.mem_frozen_iff (f.equiv.symm v)
  · have hf := f.arrows_eq (f.equiv.symm u) (f.equiv.symm v)
    simp only [Equiv.apply_symm_apply] at hf
    simpa [hf] using g.arrows_eq (f.equiv.symm u) (f.equiv.symm v)

section SameType

variable [DecidableEq V']

/-- Two quivers have the **same type** when their mutable parts are mutation equivalent. -/
@[cluster_algebras "def_same_type"]
def SameType (Q : Quiver V) (Q' : Quiver V') : Prop :=
  Q.mutablePart.MutationEquivalent Q'.mutablePart

/-- Every quiver has the same type as itself. -/
@[refl]
theorem SameType.refl (Q : Quiver V) : Q.SameType Q :=
  MutationEquivalent.refl _

end SameType

end Quiver

end ClusterAlgebras
