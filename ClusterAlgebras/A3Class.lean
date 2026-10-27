/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvin A. Swaminathan
-/
module

public import ClusterAlgebras.MutationTransport

/-!
# The mutation class of an orientation of the type `A₃` Dynkin diagram

A basic example of a mutation equivalence class: the class of an orientation of the type `A₃`
diagram consists of the quivers isomorphic to one of four, three of them orientations of the
path and the fourth an oriented `3`-cycle. In particular an oriented `3`-cycle counts as a
quiver of type `A₃`.

## Implementation notes

* The vertices are `Fin 3`, so `0, 1, 2` rather than `1, 2, 3`, following `markovQuiver`.

* Being of type `A₃` is recorded as a four-way disjunction of `Nonempty (_ ≃ _)`
  (`ClusterAlgebras.Quiver.IsA3`) rather than as membership in a finite set of quivers. The
  claim is about isomorphism classes, and a `Finset (Quiver (Fin 3))` would need
  `DecidableEq` on a structure carrying proof fields to be useful.

* Closure under mutation is proved once per representative — four lemmas of three cases
  each — and then transported: `Quiver.Iso.mutate` reduces an arbitrary quiver of type `A₃`
  to one of the four. Without that reduction there would be nothing to induct on, since the
  quivers along a path from `a3Path` are only isomorphic to the four, not equal to them.

* Of the twelve mutations, seven land on a representative on the nose and five need a
  relabelling: `Equiv.swap 0 2` twice, and the two three-cycles `finRotate 3` and its
  inverse once each. Every case is closed by `decide`, which computes the mutation.
-/

@[expose] public section

namespace ClusterAlgebras

/-- The path `0 → 1 → 2`, an orientation of the type `A₃` diagram. -/
@[cluster_algebras "def_a3_quivers"]
def a3Path : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 2 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide

/-- The orientation of the type `A₃` diagram with its middle vertex a source. -/
@[cluster_algebras "def_a3_quivers"]
def a3Source : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 1 ∧ v = 0 ∨ u = 1 ∧ v = 2 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide

/-- The orientation of the type `A₃` diagram with its middle vertex a sink. -/
@[cluster_algebras "def_a3_quivers"]
def a3Sink : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 1 ∨ u = 2 ∧ v = 1 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide

/-- The oriented `3`-cycle `1 → 0 → 2 → 1`, also counted as a quiver of type `A₃`. -/
@[cluster_algebras "def_a3_quivers"]
def a3Cycle : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 1 ∧ v = 0 ∨ u = 0 ∧ v = 2 ∨ u = 2 ∧ v = 1 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; fin_cases i <;> fin_cases j <;> decide
  frozen_eq_zero := by decide

namespace Quiver

variable {V : Type*} [Fintype V]

/-- A quiver is **of type `A₃`** when it is isomorphic to one of `a3Path`, `a3Source`, `a3Sink`,
or the oriented `3`-cycle `a3Cycle`. -/
def IsA3 (R : Quiver V) : Prop :=
  Nonempty (R.Iso a3Path) ∨ Nonempty (R.Iso a3Source) ∨ Nonempty (R.Iso a3Sink) ∨
    Nonempty (R.Iso a3Cycle)

/-- The path `a3Path` is of type `A₃`. -/
theorem isA3_a3Path : IsA3 a3Path := Or.inl ⟨Iso.refl _⟩

/-- The source orientation `a3Source` is of type `A₃`. -/
theorem isA3_a3Source : IsA3 a3Source := Or.inr (Or.inl ⟨Iso.refl _⟩)

/-- The sink orientation `a3Sink` is of type `A₃`. -/
theorem isA3_a3Sink : IsA3 a3Sink := Or.inr (Or.inr (Or.inl ⟨Iso.refl _⟩))

/-- The oriented `3`-cycle `a3Cycle` is of type `A₃`. -/
theorem isA3_a3Cycle : IsA3 a3Cycle := Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))

/-- Being of type `A₃` passes across an isomorphism. -/
theorem IsA3.of_iso {V' : Type*} [Fintype V'] {R : Quiver V} {R' : Quiver V'} (h : IsA3 R')
    (e : R.Iso R') : IsA3 R := by
  rcases h with h | h | h | h
  exacts [Or.inl ⟨e.trans h.some⟩, Or.inr (Or.inl ⟨e.trans h.some⟩),
    Or.inr (Or.inr (Or.inl ⟨e.trans h.some⟩)), Or.inr (Or.inr (Or.inr ⟨e.trans h.some⟩))]

/-- An isomorphism from a mutation of one of the four onto another of them, from the vertex map
and the twelve-case arrow computation.

The arrow hypothesis is phrased on `mutationArrows`, which mentions no mutability proof, so
each of the twelve instances below is a closed computation that `decide` can run. Phrased on
`(A.mutate hk).arrows` it would carry `hk` as a free variable and `decide` would refuse. -/
private def mutateIso {A T : Quiver (Fin 3)} {k : Fin 3} (hk : k ∉ A.frozen)
    (hA : A.frozen = ∅) (hT : T.frozen = ∅) (φ : Fin 3 ≃ Fin 3)
    (h : ∀ u v, T.arrows (φ u) (φ v) = A.mutationArrows k u v) : (A.mutate hk).Iso T where
  equiv := φ
  mem_frozen_iff v := by rw [Quiver.frozen_mutate, hA, hT]; simp
  arrows_eq := h

/-- Mutating the directed path gives the source orientation, the `3`-cycle, or the sink
orientation, according to the vertex. -/
theorem isA3_mutate_a3Path {k : Fin 3} (hk : k ∉ a3Path.frozen) : IsA3 (a3Path.mutate hk) := by
  fin_cases k
  · exact Or.inr (Or.inl ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩))

/-- Mutating the source orientation gives the path or the sink orientation. -/
theorem isA3_mutate_a3Source {k : Fin 3} (hk : k ∉ a3Source.frozen) :
    IsA3 (a3Source.mutate hk) := by
  fin_cases k
  · exact Or.inl ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩
  · exact Or.inr (Or.inr (Or.inl ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩))
  · exact Or.inl ⟨mutateIso hk rfl rfl (Equiv.swap 0 2) (by decide)⟩

/-- Mutating the sink orientation gives the path or the source orientation. -/
theorem isA3_mutate_a3Sink {k : Fin 3} (hk : k ∉ a3Sink.frozen) : IsA3 (a3Sink.mutate hk) := by
  fin_cases k
  · exact Or.inl ⟨mutateIso hk rfl rfl (Equiv.swap 0 2) (by decide)⟩
  · exact Or.inr (Or.inl ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩)
  · exact Or.inl ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩

/-- Mutating the oriented `3`-cycle gives the path in every direction, twice after a
relabelling by a three-cycle of the vertices. -/
theorem isA3_mutate_a3Cycle {k : Fin 3} (hk : k ∉ a3Cycle.frozen) :
    IsA3 (a3Cycle.mutate hk) := by
  fin_cases k
  · exact Or.inl ⟨mutateIso hk rfl rfl (finRotate 3) (by decide)⟩
  · exact Or.inl ⟨mutateIso hk rfl rfl (Equiv.refl _) (by decide)⟩
  · exact Or.inl ⟨mutateIso hk rfl rfl (finRotate 3).symm (by decide)⟩

variable [DecidableEq V]

/-- **Being of type `A₃` survives a mutation.** -/
theorem IsA3.mutate {R : Quiver V} (h : IsA3 R) {k : V} (hk : k ∉ R.frozen) :
    IsA3 (R.mutate hk) := by
  rcases h with h | h | h | h
  · exact (isA3_mutate_a3Path (h.some.notMem_frozen hk)).of_iso (h.some.mutate hk)
  · exact (isA3_mutate_a3Source (h.some.notMem_frozen hk)).of_iso (h.some.mutate hk)
  · exact (isA3_mutate_a3Sink (h.some.notMem_frozen hk)).of_iso (h.some.mutate hk)
  · exact (isA3_mutate_a3Cycle (h.some.notMem_frozen hk)).of_iso (h.some.mutate hk)

/-- Being of type `A₃` survives a whole mutation path. -/
theorem isA3_result : ∀ {Q : Quiver V} (p : Q.MutationPath), IsA3 Q → IsA3 p.result
  | _, .nil _, h => h
  | _, .cons hk p, h => isA3_result p (h.mutate hk)

end Quiver

/-- **The mutation class of an orientation of the type `A₃` diagram.** Every quiver mutation
equivalent to the directed path `0 → 1 → 2` is isomorphic to one of the four: the path, the
two orientations with the middle vertex a source or a sink, and the oriented `3`-cycle. -/
@[cluster_algebras "lem_a3_mutation_class"]
theorem isA3_of_mutationEquivalent {V : Type*} [Fintype V] {Q : Quiver V}
    (h : a3Path.MutationEquivalent Q) : Quiver.IsA3 Q := by
  obtain ⟨p, ⟨e⟩⟩ := h
  exact (Quiver.isA3_result p Quiver.isA3_a3Path).of_iso e.symm

end ClusterAlgebras
