/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Restriction.FullSubquiver
public import ClusterAlgebras.MutationTransport

/-!
# Finite mutation type of quivers is hereditary

If a quiver `Q = (V, F, a)` has finite mutation type, then so does each of its full
subquivers `Q_U`, `U ⊆ V`
(`ClusterAlgebras.Quiver.isHereditaryProperty_hasFiniteMutationType`). This is the quiver
case of FWZ's Proposition 4.1.4.

The proof has two halves. First, a mutation path from `Q_U` lifts to a mutation path from
`Q` whose result restricts to the result of the given path
(`ClusterAlgebras.Quiver.MutationPath.exists_fullSubquiver_result`): every vertex mutated
along the path lies in `U \ F`, and mutation at such a vertex commutes with passing to the
full subquiver on `U`. Second, an isomorphism `φ : Q_d ≅ S` restricts to the full subquiver
on `U`, so if finitely many quivers `S_1, …, S_N` represent the mutation class of `Q`, then
the quivers obtained from them by restriction represent that of `Q_U`.

## Main definitions

* `ClusterAlgebras.Quiver.comap`: the pullback `S.comap f` of a quiver `S` on `V` along a
  map `f : W → V`, with arrows `S.arrows (f u) (f v)` and frozen vertices `f⁻¹(F)`.

## Main results

* `ClusterAlgebras.Quiver.MutationPath.exists_fullSubquiver_result`: mutation paths from a
  full subquiver lift.
* `ClusterAlgebras.Quiver.isHereditaryProperty_hasFiniteMutationType`: having finite
  mutation type is hereditary.

## Design decisions

The full subquiver `Q_U` is a quiver on the subtype `↥U`, so the representatives of its
mutation classes must be quivers on `↥U` as well, not quivers on the subsets `φ(U)` of the
vertex sets of the `S_j`. So instead of restricting `φ` to an isomorphism
`(Q_d)_U ≅ (S_j)_{φ(U)}`, the representative `S_j` is pulled back along `φ ∘ (↑) : ↥U → V`;
the identity of `↥U` is then an isomorphism `(Q_d)_U ≅ S_j.comap (φ ∘ (↑))`. As `φ` ranges
over the finitely many maps `↥U → V`, these pullbacks form a finite set.

The pullback `Quiver.comap` makes sense along any map, injective or not: a loop, a
two-cycle or an arrow between frozen vertices upstairs would be one downstairs.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras.
  Chapter 4*, Proposition 4.1.4.
-/

@[expose] public section

namespace ClusterAlgebras

namespace Quiver

universe u

section Comap

variable {V W W' : Type*} [Fintype V] [Fintype W] [Fintype W'] [DecidableEq V]

/-- The **pullback** of a quiver `S` on `V` along a map `f : W → V`: a vertex `w` is frozen
when `f w` is, and there are `S.arrows (f u) (f v)` arrows from `u` to `v`. No injectivity
of `f` is needed. -/
def comap (S : Quiver V) (f : W → V) : Quiver W where
  frozen := Finset.univ.filter fun w => f w ∈ S.frozen
  arrows u v := S.arrows (f u) (f v)
  isArrowSystem v := S.isArrowSystem (f v)
  twoCycleFree u v := S.twoCycleFree (f u) (f v)
  frozen_eq_zero _ hu _ hv :=
    S.frozen_eq_zero _ (Finset.mem_filter.mp hu).2 _ (Finset.mem_filter.mp hv).2

/-- A vertex is frozen in the pullback exactly when its image is frozen. -/
@[simp]
theorem mem_frozen_comap (S : Quiver V) (f : W → V) (w : W) :
    w ∈ (S.comap f).frozen ↔ f w ∈ S.frozen := by
  simp [comap]

/-- The arrow counts of the pullback are those between the images. -/
@[simp]
theorem arrows_comap (S : Quiver V) (f : W → V) (u v : W) :
    (S.comap f).arrows u v = S.arrows (f u) (f v) :=
  rfl

/-- The full subquiver on `U` is the pullback along the inclusion `↥U → V`. -/
theorem fullSubquiver_eq_comap (Q : Quiver V) (U : Finset V) :
    Q.fullSubquiver U = Q.comap ((↑) : U → V) :=
  Quiver.ext' (by ext u; simp) rfl

variable [DecidableEq W]

/-- An isomorphism `e : Q ≅ S` induces an isomorphism between the pullbacks of `Q` along `g`
and of `S` along `e ∘ g`, the identity on vertices. -/
def Iso.comap {Q : Quiver V} {S : Quiver W} (e : Q.Iso S) (g : W' → V) :
    (Q.comap g).Iso (S.comap (e.equiv ∘ g)) where
  equiv := Equiv.refl W'
  mem_frozen_iff w := by simpa using e.mem_frozen_iff (g w)
  arrows_eq u v := e.arrows_eq (g u) (g v)

end Comap

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Mutation paths from a full subquiver lift.** If `Q'` is a quiver whose full subquiver
on `U` is `P`, then every mutation path from `P` lifts to a mutation path from `Q'` whose
result has full subquiver on `U` equal to the result of the given path.

Each vertex mutated along the path is mutable in the full subquiver, so it lies in `U` and
is mutable in `Q'`; and mutation at it commutes with passing to the full subquiver on `U`
(`Quiver.mutate_fullSubquiver`). -/
theorem MutationPath.exists_fullSubquiver_result {U : Finset V} :
    ∀ {P : Quiver U} (p : P.MutationPath) (Q' : Quiver V), Q'.fullSubquiver U = P →
      ∃ q : Q'.MutationPath, q.result.fullSubquiver U = p.result
  | _, .nil _, Q', h => ⟨.nil Q', h⟩
  | _, .cons (k := k) hk p, Q', h => by
      have hk' : (k : V) ∉ Q'.frozen := by
        subst h
        simpa using hk
      have hmut : (Q'.mutate hk').fullSubquiver U = _ :=
        (Q'.mutate_fullSubquiver U k.2 hk').symm.trans
          (mutate_congr h (Q'.notMem_frozen_fullSubquiver k.2 hk') hk)
      obtain ⟨q, hq⟩ := exists_fullSubquiver_result p (Q'.mutate hk') hmut
      exact ⟨.cons hk' q, hq⟩

/-- **Finite mutation type of quivers is hereditary**: if `Q` has finite mutation type, so
does every full subquiver of `Q`.

If finitely many quivers `S` represent the mutation class of `Q`, then the pullbacks of the
members of `S` along the finitely many maps `↥U → V` represent that of `Q_U`: a mutation path
from `Q_U` lifts to one from `Q` (`Quiver.MutationPath.exists_fullSubquiver_result`), whose
result `Q_d` is isomorphic, by some `φ`, to a member `S_j` of `S`, and then
`(Q_d)_U ≅ S_j.comap (φ ∘ (↑))`. -/
@[cluster_algebras "prop_finite_mutation_type_hereditary_quiver"]
theorem isHereditaryProperty_hasFiniteMutationType :
    IsHereditaryProperty.{u} fun Q => Q.HasFiniteMutationType := by
  intro W _ _ Q U ⟨S, hS, hQ⟩
  refine hasFiniteMutationType_of_forall_result
    ((fun x : Quiver W × (U → W) => x.1.comap x.2) '' (S ×ˢ Set.univ))
    ((hS.prod Set.finite_univ).image _) fun p => ?_
  obtain ⟨q, hq⟩ := p.exists_fullSubquiver_result Q rfl
  obtain ⟨R, hR, ⟨e⟩⟩ := hQ q.result (mutationEquivalent_result q)
  refine ⟨R.comap (e.equiv ∘ (↑)), ⟨(R, e.equiv ∘ (↑)), ⟨hR, trivial⟩, rfl⟩, ?_⟩
  rw [← hq, fullSubquiver_eq_comap]
  exact ⟨e.comap _⟩

end Quiver

end ClusterAlgebras
