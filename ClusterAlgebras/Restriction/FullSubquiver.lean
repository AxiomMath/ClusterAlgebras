/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Defs.MutationEquivalence

/-!
# Full subquivers

The *full subquiver* of a quiver `Q = (V, F, a)` on a set `U ⊆ V` keeps the vertices in
`U`, the frozen ones among them, and every arrow between two of them. Mutation at a mutable
vertex of `U` commutes with passing to the full subquiver, which is the quiver half of
[FWZ, Lemma 4.1.2]. A property of quivers is *hereditary* when it passes to every full
subquiver.

## Main definitions

* `ClusterAlgebras.Quiver.fullSubquiver`: The full subquiver of `Q` on `U`.
* `ClusterAlgebras.Quiver.IsHereditaryProperty`: A property of quivers that passes to every
  full subquiver.

## Main results

* `ClusterAlgebras.Quiver.mutate_fullSubquiver`: Mutation at a mutable vertex `k ∈ U`
  commutes with passing to the full subquiver on `U`.

## Implementation notes

* `U` is a `Finset V` and the full subquiver is a quiver on the subtype `↥U`, so its vertex
  set is literally `U`. Its frozen set is `Q.frozen.subtype (· ∈ U)`, which is `F ∩ U` read
  in `↥U`.

* The frozen set `Finset.subtype` needs membership in `U` decidable, so `V` is assumed to
  have decidable equality, which mutation needs as well.

* As with `ClusterAlgebras.Quiver.mutate`, the arrow system is a bare function
  (`ClusterAlgebras.Quiver.fullSubquiverArrows`) and the three quiver conditions on it are
  proved separately.

* A *property of quivers* is a predicate on quivers on every finite vertex type with
  decidable equality, in one universe. Decidable equality is part of it because mutation,
  and with it mutation equivalence and finite mutation type, needs it.

## References

* [S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*][FWZ]
-/

@[expose] public section

namespace ClusterAlgebras

namespace Quiver

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The arrow system of the full subquiver on `U`: the arrows of `Q` between vertices of
`U`. -/
def fullSubquiverArrows (Q : Quiver V) (U : Finset V) : U → U → ℕ :=
  fun u v => Q.arrows u v

omit [DecidableEq V] in
/-- The arrow counts of the full subquiver are those of `Q`. -/
@[simp]
theorem fullSubquiverArrows_apply (Q : Quiver V) (U : Finset V) (u v : U) :
    Q.fullSubquiverArrows U u v = Q.arrows u v :=
  rfl

omit [DecidableEq V] in
/-- The restricted arrows form an arrow system: no vertex of `U` carries a loop. -/
@[cluster_algebras "lem_full_subquiver_is_quiver"]
theorem isArrowSystem_fullSubquiverArrows (Q : Quiver V) (U : Finset V) :
    IsArrowSystem (Q.fullSubquiverArrows U) :=
  fun v => Q.isArrowSystem v

omit [DecidableEq V] in
/-- The restricted arrows are two-cycle-free, because those of `Q` are. -/
@[cluster_algebras "lem_full_subquiver_is_quiver"]
theorem twoCycleFree_fullSubquiverArrows (Q : Quiver V) (U : Finset V) :
    TwoCycleFree (Q.fullSubquiverArrows U) :=
  fun u v => Q.twoCycleFree u v

/-- The restricted arrows join no two frozen vertices of `U`, because those of `Q` join no
two frozen vertices. -/
@[cluster_algebras "lem_full_subquiver_is_quiver"]
theorem fullSubquiverArrows_eq_zero_of_frozen (Q : Quiver V) (U : Finset V) {u v : U}
    (hu : u ∈ Q.frozen.subtype (· ∈ U)) (hv : v ∈ Q.frozen.subtype (· ∈ U)) :
    Q.fullSubquiverArrows U u v = 0 :=
  Q.frozen_eq_zero _ (Finset.mem_subtype.mp hu) _ (Finset.mem_subtype.mp hv)

/-- The **full subquiver** `Q_U` of `Q` on `U ⊆ V`: the vertex set `U`, the frozen vertices
`F ∩ U`, and the arrows of `Q` between vertices of `U`. -/
@[cluster_algebras "def_full_subquiver"]
def fullSubquiver (Q : Quiver V) (U : Finset V) : Quiver U where
  frozen := Q.frozen.subtype (· ∈ U)
  arrows := Q.fullSubquiverArrows U
  isArrowSystem := Q.isArrowSystem_fullSubquiverArrows U
  twoCycleFree := Q.twoCycleFree_fullSubquiverArrows U
  frozen_eq_zero _ hu _ hv := Q.fullSubquiverArrows_eq_zero_of_frozen U hu hv

/-- The frozen set of a full subquiver is the trace of the frozen set. -/
theorem frozen_fullSubquiver (Q : Quiver V) (U : Finset V) :
    (Q.fullSubquiver U).frozen = Q.frozen.subtype (· ∈ U) :=
  rfl

/-- A vertex of `U` is frozen in `Q_U` exactly when it is frozen in `Q`. -/
@[simp]
theorem mem_frozen_fullSubquiver (Q : Quiver V) (U : Finset V) (u : U) :
    u ∈ (Q.fullSubquiver U).frozen ↔ (u : V) ∈ Q.frozen :=
  Finset.mem_subtype (p := (· ∈ U))

/-- The arrow counts of a full subquiver are those of `Q`. -/
@[simp]
theorem arrows_fullSubquiver (Q : Quiver V) (U : Finset V) (u v : U) :
    (Q.fullSubquiver U).arrows u v = Q.arrows u v :=
  rfl

/-- A vertex of `U` mutable in `Q` is mutable in `Q_U`. -/
theorem notMem_frozen_fullSubquiver (Q : Quiver V) {U : Finset V} {k : V} (hkU : k ∈ U)
    (hk : k ∉ Q.frozen) : (⟨k, hkU⟩ : U) ∉ (Q.fullSubquiver U).frozen := by
  simpa using hk

/-- **Mutation commutes with passing to a full subquiver**: for a mutable vertex `k ∈ U`,
`μ_k(Q_U) = (μ_k(Q))_U`. -/
@[cluster_algebras "lem_full_subquiver_mutation"]
theorem mutate_fullSubquiver (Q : Quiver V) (U : Finset V) {k : V}
    (hkU : k ∈ U) (hk : k ∉ Q.frozen) :
    (Q.fullSubquiver U).mutate (Q.notMem_frozen_fullSubquiver hkU hk) =
      (Q.mutate hk).fullSubquiver U := by
  refine Quiver.ext' rfl ?_
  funext i j
  have key : ∀ x y : U, reversal ((Q.fullSubquiver U).stepOne ⟨k, hkU⟩) ⟨k, hkU⟩ x y =
      reversal (Q.stepOne k) k x y := by
    intro x y
    simp only [reversal, stepOne, mem_frozen_fullSubquiver, arrows_fullSubquiver,
      ← Subtype.val_inj]
  simp only [arrows_mutate, mutationArrows, arrows_fullSubquiver, cancellation, key]

/-- A **hereditary property of quivers**: whenever a quiver `Q = (V, F, a)` has it, so does
every full subquiver `Q_U`, `U ⊆ V`. -/
@[cluster_algebras "def_hereditary_quiver"]
def IsHereditaryProperty
    (P : ∀ {W : Type u} [Fintype W] [DecidableEq W], Quiver W → Prop) : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (Q : Quiver W) (U : Finset W),
    P Q → P (Q.fullSubquiver U)

end Quiver

end ClusterAlgebras
