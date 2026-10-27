/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Restriction.ArborizableExample
public import ClusterAlgebras.Restriction.HereditaryQuiver

/-!
# Arborizability is not hereditary

A finite simple graph is a *forest* when any two of its vertices are joined by at most one
path, and a quiver is *arborizable* when it is mutation equivalent to an orientation of a
forest. The five-vertex quiver `Q^arb` is arborizable: three mutations turn it into the star
`Q^star`, an orientation of the star graph centred at FWZ's vertex `5`. Its full
subquiver on `{1, 2, 3}` is not: every quiver mutation equivalent to that triangle has three
vertices, any two joined by an arrow, so an orientation of a graph in its class orients the
triangle graph, which has two paths between any two of its vertices. Hence being arborizable
is not a hereditary property of quivers.

The same two quivers witness FWZ's remark that conditions (i)–(ii) of their Lemma 4.1.8
(`ClusterAlgebras.exists_obtainedByRestriction_iff_forall`) do not imply condition (iii),
that every member of the second class restricts to a member of the first. The class of the
triangle embeds into the class of `Q^star`, since `Q^star` is mutation equivalent to `Q^arb`,
of which the triangle is a full subquiver; yet no full subquiver of `Q^star` itself lies in the
class of the triangle, as two distinct vertices of `Q^star` are joined by an arrow only if one
of them is its centre.

## Main definitions

* `ClusterAlgebras.IsForest`: a forest, Mathlib's `SimpleGraph.IsAcyclic`.
* `ClusterAlgebras.Quiver.IsArborizable`: being mutation equivalent to an orientation of a
  forest.
* `ClusterAlgebras.Quiver.MutationClassEmbeddable`: the class of `Q` embeds into the class
  of `Q'`.

## Main results

* `ClusterAlgebras.isArborizable_arborizableExample`: `Q^arb` is arborizable.
* `ClusterAlgebras.not_isArborizable_arborizableTriangle`: `Q^arb_{1,2,3}` is not.
* `ClusterAlgebras.not_isHereditaryProperty_isArborizable`: arborizability is not
  hereditary, in every universe.
* `ClusterAlgebras.arborizableTriangle_mutationClassEmbeddable_starExample`: the class of
  `Q^arb_{1,2,3}` embeds into the class of `Q^star`.
* `ClusterAlgebras.not_mutationEquivalent_starExample_fullSubquiver`: no full subquiver of
  `Q^star` is mutation equivalent to `Q^arb_{1,2,3}`.
* `ClusterAlgebras.Quiver.Iso.isArborizable_iff`: arborizability is invariant under
  isomorphism.

## Design decisions

* FWZ's forest asks for at most one path of pairwise distinct vertices between any
  two vertices. That is Mathlib's `SimpleGraph.IsAcyclic`, by
  `SimpleGraph.isAcyclic_iff_path_unique`, so `IsForest` is an abbreviation for it, as
  `ClusterAlgebras.IsFiniteTree` is for `SimpleGraph.IsTree`.

* The forest of an arborizable quiver on `V : Type u` lives on a vertex type in the same
  universe `u`. Nothing is lost: a quiver mutation equivalent to one on `V` has its vertex
  set in bijection with `V`, and the forest and its orientation can be pulled back along that
  bijection; this is how `ClusterAlgebras.Quiver.Iso.isArborizable_iff` relates quivers in
  different universes.

* A hereditary property is quantified over quivers in a single universe. The examples live
  on `Fin 5`, so for a universe `u` they are pulled back along `ULift.{u} (Fin 5) ≃ Fin 5`,
  and isomorphism invariance carries arborizability across.

* FWZ obtain `Q^star ~ Q^arb` from `Q^arb ~ Q^star` by symmetry of mutation
  equivalence, which rests on mutation being an involution. Here the mutations at `4`, `2`
  and `3` (FWZ's `5`, `3`, `4`), which undo the three carrying `Q^arb` to `Q^star`,
  are computed directly instead
  (`ClusterAlgebras.starExample_mutationEquivalent_arborizableExample`).

* The star graph is Mathlib's `SimpleGraph.starGraph`, whose acyclicity is
  `SimpleGraph.isAcyclic_starGraph`. As in `ClusterAlgebras.arborizableExample`, vertex `i`
  of FWZ is `i - 1` here, so the centre `5` is `4`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras.
  Chapter 4*, Section 4.1, the remarks on arborizable quivers and following Lemma 4.1.8.
-/

@[expose] public section

namespace ClusterAlgebras

universe u u'

/-- A **forest**: a finite simple graph with no cycle, Mathlib's `SimpleGraph.IsAcyclic`.
FWZ ask that between any two vertices there be at most one path of pairwise distinct
vertices, which is `SimpleGraph.isAcyclic_iff_path_unique`. -/
@[cluster_algebras "def_forest", nolint unusedArguments]
abbrev IsForest {V : Type*} [Fintype V] (G : FiniteSimpleGraph V) : Prop := G.IsAcyclic

/-- **Three pairwise adjacent vertices rule out acyclicity**: the edge `u — w` and the walk
`u — v — w` are two distinct paths from `u` to `w`. -/
theorem not_isAcyclic_of_adj_of_adj_of_adj {V : Type*} {G : SimpleGraph V} {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwu : G.Adj w u) : ¬G.IsAcyclic := by
  intro hG
  have hp : (SimpleGraph.Walk.cons huv (.cons hvw .nil) : G.Walk u w).IsPath := by
    simp [SimpleGraph.Walk.cons_isPath_iff, huv.ne, hwu.ne.symm, hvw.ne]
  have h := congrArg (fun p : G.Path u w => p.1.length)
    (hG.path_unique ⟨_, hp⟩ (SimpleGraph.Path.singleton hwu.symm))
  simp at h

namespace Quiver

section Transport

variable {V : Type*} {W : Type*} [Fintype V] [Fintype W] [DecidableEq V]

/-- The pullback of a quiver along a bijection `e : W ≃ V` is isomorphic to it, by `e`. -/
def comapEquivIso (S : Quiver V) (e : W ≃ V) : (S.comap e).Iso S where
  equiv := e
  mem_frozen_iff _ := (S.mem_frozen_comap e _).symm
  arrows_eq _ _ := rfl

/-- **Orientations pull back along injections**: if `R` orients `G`, then the pullback of
`R` along an injective `f` orients the pullback of `G` along `f`. -/
theorem IsOrientation.comap {R : Quiver V} {G : FiniteSimpleGraph V} (h : R.IsOrientation G)
    {f : W → V} (hf : Function.Injective f) :
    (R.comap f).IsOrientation (G.comap f : FiniteSimpleGraph W) := by
  refine ⟨Finset.eq_empty_of_forall_notMem fun w hw => ?_, fun u v huv => ?_⟩
  · rw [mem_frozen_comap, h.1] at hw
    exact Finset.notMem_empty _ hw
  · exact h.2 (f u) (f v) (hf.ne huv)

end Transport

variable {V : Type*} {V' : Type*} {V'' : Type*} [Fintype V] [Fintype V'] [Fintype V'']
  [DecidableEq V] [DecidableEq V']

/-- Mutation equivalence may be composed with an isomorphism on the left: the mutation path
from the target of the isomorphism is carried back to its source. -/
theorem Iso.trans_mutationEquivalent {Q : Quiver V} {Q' : Quiver V'} {Q'' : Quiver V''}
    (e : Q.Iso Q') (h : Q'.MutationEquivalent Q'') : Q.MutationEquivalent Q'' := by
  obtain ⟨p, ⟨f⟩⟩ := h
  obtain ⟨q, ⟨g⟩⟩ := p.exists_iso_result e.symm
  exact ⟨q, ⟨g.symm.trans f⟩⟩

/-- A quiver `Q` is **arborizable** if it is mutation equivalent to an orientation `R` of a
forest `G`. The forest is on a finite type in the universe of the vertices of `Q`; as any
finite type is in bijection with some `Fin k`, nothing is lost by this. -/
@[cluster_algebras "def_arborizable"]
def IsArborizable {V : Type u} [Fintype V] [DecidableEq V] (Q : Quiver V) : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (G : FiniteSimpleGraph W) (R : Quiver W),
    IsForest G ∧ R.IsOrientation G ∧ Q.MutationEquivalent R

/-- **Arborizability passes along an isomorphism**, between vertex types in any two
universes. -/
theorem IsArborizable.of_iso {V : Type u} {V' : Type u'} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] {Q : Quiver V} {Q' : Quiver V'} (e : Q.Iso Q')
    (hQ : Q.IsArborizable) : Q'.IsArborizable := by
  obtain ⟨W, _, G, R, hG, hR, hQR⟩ := hQ
  have hQ'R := e.symm.trans_mutationEquivalent hQR
  obtain ⟨p, ⟨f⟩⟩ := hQR
  classical
  let g : V' ≃ W := e.equiv.symm.trans f.equiv
  exact ⟨V', inferInstance, G.comap g, R.comap g, hG.of_comap g.toEmbedding,
    hR.comap g.injective, hQ'R.trans_iso (R.comapEquivIso g).symm⟩

/-- **Arborizability is invariant under isomorphism**, between vertex types in any two
universes. -/
theorem Iso.isArborizable_iff {V : Type u} {V' : Type u'} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] {Q : Quiver V} {Q' : Quiver V'} (e : Q.Iso Q') :
    Q.IsArborizable ↔ Q'.IsArborizable :=
  ⟨IsArborizable.of_iso e, IsArborizable.of_iso e.symm⟩

/-- The class of `Q` is **embeddable** into the class of `Q'` if some `R` mutation
equivalent to `Q` is isomorphic to a full subquiver of some `R'` mutation equivalent to
`Q'`. The quivers `R` and `R'` are on finite types in the universes of the vertices of `Q`
and of `Q'`. This is the quiver counterpart of `ClusterAlgebras.MutationClassEmbeddable`. -/
@[cluster_algebras "def_embeddable_quiver"]
def MutationClassEmbeddable {V : Type u} {V' : Type u'} [Fintype V] [DecidableEq V]
    [Fintype V'] [DecidableEq V'] (Q : Quiver V) (Q' : Quiver V') : Prop :=
  ∃ (W : Type u) (_ : Fintype W) (W' : Type u') (_ : Fintype W') (_ : DecidableEq W')
    (R : Quiver W) (R' : Quiver W') (U : Finset W'),
    Q.MutationEquivalent R ∧ Q'.MutationEquivalent R' ∧ Nonempty (R.Iso (R'.fullSubquiver U))

end Quiver

/-- The star example orients the star graph centred at `4`. -/
theorem isOrientation_starExample_starGraph :
    starExample.IsOrientation (SimpleGraph.starGraph 4) := by
  refine ⟨rfl, ?_⟩
  simp only [SimpleGraph.starGraph_adj]
  decide

/-- The arborizable example is mutation equivalent to the star example, by the mutations at
`3`, `2` and `4`. -/
theorem arborizableExample_mutationEquivalent_starExample :
    arborizableExample.MutationEquivalent starExample := by
  have h₁ : (3 : Fin 5) ∉ arborizableExample.frozen := by simp
  have h₂ : (2 : Fin 5) ∉ (arborizableExample.mutate h₁).frozen := by simp
  have h₃ : (4 : Fin 5) ∉ ((arborizableExample.mutate h₁).mutate h₂).frozen := by simp
  refine ⟨.cons h₁ (.cons h₂ (.cons h₃ (.nil _))), ⟨?_⟩⟩
  simp only [Quiver.MutationPath.result_cons, Quiver.MutationPath.result_nil]
  rw [mutate_mutate_mutate_arborizableExample]
  exact Quiver.Iso.refl _

/-- The star example is mutation equivalent to the arborizable example, by the mutations at
`4`, `2` and `3`, which undo those carrying the arborizable example to the star. The three
mutations are computed directly, so no appeal to the involutivity of mutation is made. -/
theorem starExample_mutationEquivalent_arborizableExample :
    starExample.MutationEquivalent arborizableExample := by
  have h₁ : (4 : Fin 5) ∉ starExample.frozen := by simp
  have h₂ : (2 : Fin 5) ∉ (starExample.mutate h₁).frozen := by simp
  have h₃ : (3 : Fin 5) ∉ ((starExample.mutate h₁).mutate h₂).frozen := by simp
  refine ⟨.cons h₁ (.cons h₂ (.cons h₃ (.nil _))), ⟨?_⟩⟩
  simp only [Quiver.MutationPath.result_cons, Quiver.MutationPath.result_nil]
  have h : ((starExample.mutate h₁).mutate h₂).mutate h₃ = arborizableExample := by
    refine Quiver.ext' rfl (funext fun u => funext fun v => ?_)
    revert u v
    change ∀ u v, (((starExample.mutate (k := 4) (by decide)).mutate (k := 2)
      (by decide)).mutate (k := 3) (by decide)).arrows u v = arborizableExample.arrows u v
    decide
  rw [h]
  exact Quiver.Iso.refl _

/-- **The arborizable example is arborizable**: it is mutation equivalent to the star
example, which orients the star graph centred at `4`, a forest. -/
@[cluster_algebras "lem_arborizable_example_arborizable"]
theorem isArborizable_arborizableExample : arborizableExample.IsArborizable :=
  ⟨Fin 5, inferInstance, SimpleGraph.starGraph 4, starExample, SimpleGraph.isAcyclic_starGraph 4,
    isOrientation_starExample_starGraph, arborizableExample_mutationEquivalent_starExample⟩

/-- **No orientation of a forest is mutation equivalent to the triangle**: such an
orientation would have three vertices, any two joined by an arrow and hence adjacent in the
forest, which is impossible. -/
theorem not_mutationEquivalent_arborizableTriangle_of_isOrientation {W : Type*} [Fintype W]
    {G : FiniteSimpleGraph W} (hG : IsForest G) {R : Quiver W} (hR : R.IsOrientation G) :
    ¬arborizableTriangle.MutationEquivalent R := by
  classical
  intro h
  have hadj : ∀ u v : W, u ≠ v → G.Adj u v := by
    intro u v huv
    by_contra hna
    obtain ⟨h₁, h₂⟩ := (hR.2 u v huv).2 hna
    have := arrows_add_arrows_pos_of_mutationEquivalent_arborizableTriangle h huv
    omega
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ :=
    Finset.card_eq_three.mp (Finset.card_univ.trans
      (card_eq_three_of_mutationEquivalent_arborizableTriangle h))
  exact not_isAcyclic_of_adj_of_adj_of_adj (hadj x y hxy) (hadj y z hyz) (hadj z x hxz.symm) hG

/-- **The triangle `Q^arb_{1,2,3}` is not arborizable.** -/
@[cluster_algebras "lem_qi_not_arborizable"]
theorem not_isArborizable_arborizableTriangle : ¬arborizableTriangle.IsArborizable := by
  rintro ⟨W, _, G, R, hG, hR, h⟩
  exact not_mutationEquivalent_arborizableTriangle_of_isOrientation hG hR h

/-- The arborizable example, pulled back to `ULift (Fin 5)` in an arbitrary universe. -/
def arborizableExampleULift : Quiver (ULift.{u} (Fin 5)) :=
  arborizableExample.comap Equiv.ulift

/-- The vertices `{0, 1, 2}` of `ULift (Fin 5)`, those carried to `{0, 1, 2}` by
`Equiv.ulift`. -/
def triangleVerticesULift : Finset (ULift.{u} (Fin 5)) :=
  ({0, 1, 2} : Finset (Fin 5)).map Equiv.ulift.symm.toEmbedding

/-- The full subquiver of the pulled-back example on `{0, 1, 2}` is isomorphic to the
triangle. -/
def arborizableExampleULiftFullSubquiverIso :
    (arborizableExampleULift.{u}.fullSubquiver triangleVerticesULift).Iso arborizableTriangle where
  equiv := Equiv.ulift.subtypeEquiv fun a => by
    simp only [triangleVerticesULift, Finset.mem_map_equiv, Equiv.symm_symm]
  mem_frozen_iff _ := by simp [arborizableExampleULift]
  arrows_eq _ _ := rfl

/-- **Arborizability is not a hereditary property of quivers**, in any universe: the
arborizable example is arborizable, and its full subquiver on `{0, 1, 2}` is not. -/
@[cluster_algebras "lem_arborizable_not_hereditary"]
theorem not_isHereditaryProperty_isArborizable :
    ¬Quiver.IsHereditaryProperty.{u} fun Q => Q.IsArborizable := by
  intro h
  have hQ : arborizableExampleULift.{u}.IsArborizable :=
    ((arborizableExample.comapEquivIso Equiv.ulift).isArborizable_iff).mpr
      isArborizable_arborizableExample
  exact not_isArborizable_arborizableTriangle
    (arborizableExampleULiftFullSubquiverIso.isArborizable_iff.mp (h _ triangleVerticesULift hQ))

/-- **The class of the triangle embeds into the class of the star**: the star example is
mutation equivalent to the arborizable example, by the mutations at `4`, `2` and `3`, and
the triangle is the full subquiver of the arborizable example on `{0, 1, 2}`. -/
@[cluster_algebras "lem_qi_embeddable_star"]
theorem arborizableTriangle_mutationClassEmbeddable_starExample :
    arborizableTriangle.MutationClassEmbeddable starExample :=
  ⟨_, inferInstance, Fin 5, inferInstance, inferInstance, arborizableTriangle,
    arborizableExample, {0, 1, 2}, .refl _, starExample_mutationEquivalent_arborizableExample,
    ⟨Quiver.Iso.refl _⟩⟩

/-- In the star example no arrow joins two vertices that both differ from the centre `4`. -/
theorem arrows_add_arrows_starExample_eq_zero {u v : Fin 5} (hu : u ≠ 4) (hv : v ≠ 4) :
    starExample.arrows u v + starExample.arrows v u = 0 := by
  revert u v
  decide

/-- **No full subquiver of the star lies in the class of the triangle**: for every
`U ⊆ {0, …, 4}`, the triangle `Q^arb_{1,2,3}` is not mutation equivalent to `Q^star_U`. Such
a `U` would have three elements, any two joined by an arrow of `Q^star`, but two of them are
distinct from the centre `4`. -/
@[cluster_algebras "lem_star_no_subquiver_in_class"]
theorem not_mutationEquivalent_starExample_fullSubquiver (U : Finset (Fin 5)) :
    ¬arborizableTriangle.MutationEquivalent (starExample.fullSubquiver U) := by
  intro h
  have hcard : U.card = 3 := by
    simpa using card_eq_three_of_mutationEquivalent_arborizableTriangle h
  have hlt : 1 < (U.erase 4).card := by
    have := Finset.pred_card_le_card_erase (s := U) (a := 4)
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
  have hpos := arrows_add_arrows_pos_of_mutationEquivalent_arborizableTriangle h
    (u := ⟨a, Finset.mem_of_mem_erase ha⟩) (v := ⟨b, Finset.mem_of_mem_erase hb⟩)
    (by simpa using hab)
  simp only [Quiver.arrows_fullSubquiver] at hpos
  have := arrows_add_arrows_starExample_eq_zero (Finset.ne_of_mem_erase ha)
    (Finset.ne_of_mem_erase hb)
  omega

end ClusterAlgebras
