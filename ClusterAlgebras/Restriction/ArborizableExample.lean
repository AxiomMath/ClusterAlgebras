/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Restriction.FullSubquiver
public import ClusterAlgebras.MutationTransport

/-!
# The arborizable example and the mutation class of its triangle

FWZ's remark that arborizability is not hereditary rests on one five-vertex quiver
`Q^arb`, with no frozen vertices and the seven simple arrows `1 → 2`, `2 → 3`, `1 → 3`,
`3 → 5`, `5 → 1`, `3 → 4`, `4 → 1` (`ClusterAlgebras.arborizableExample`). Mutating it at
`4`, then `3`, then `5` gives the star `Q^star`, whose four arrows `1 → 5`, `3 → 5`,
`5 → 2`, `5 → 4` all meet `5` (`ClusterAlgebras.starExample`,
`ClusterAlgebras.mutate_mutate_mutate_arborizableExample`).

The full subquiver `A = Q^arb_{1,2,3}` is the acyclic triangle `1 → 2`, `2 → 3`, `1 → 3`
(`ClusterAlgebras.arborizableTriangle`), and its mutation `C = μ_2(A)` has the arrows
`2 → 1`, `3 → 2` and a double arrow `1 ⇒ 3` (`ClusterAlgebras.arborizableTriangleMut`).
Every quiver mutation equivalent to `A` is isomorphic to `A` or to `C`
(`ClusterAlgebras.nonempty_iso_of_mutationEquivalent_arborizableTriangle`). In both, any two
distinct vertices are joined by a positive number of arrows, and there are three vertices;
these two facts pass to every quiver of the class.

## Main definitions

* `ClusterAlgebras.arborizableExample`, `ClusterAlgebras.starExample`: the quivers `Q^arb`
  and `Q^star` on `Fin 5`.
* `ClusterAlgebras.arborizableTriangle`: the full subquiver `Q^arb_{1,2,3}`.
* `ClusterAlgebras.arborizableTriangleMut`: its mutation at the middle vertex.

## Main results

* `ClusterAlgebras.mutate_mutate_mutate_arborizableExample`: `μ_5 μ_3 μ_4 (Q^arb) = Q^star`.
* `ClusterAlgebras.nonempty_iso_of_mutationEquivalent_arborizableTriangle`: the mutation
  class of the triangle consists of two quivers up to isomorphism.
* `ClusterAlgebras.arrows_add_arrows_pos_of_mutationEquivalent_arborizableTriangle` and
  `ClusterAlgebras.card_eq_three_of_mutationEquivalent_arborizableTriangle`: in every quiver
  of that class there are three vertices, any two distinct ones joined by an arrow.

## Design decisions

* The vertices are `Fin 5`, so `0, 1, 2, 3, 4` where FWZ write `1, 2, 3, 4, 5`:
  vertex `i` of FWZ is `i - 1` here. Thus `μ_5 μ_3 μ_4` is mutation at `3`, then
  `2`, then `4`, the triangle is the full subquiver on `{0, 1, 2}`, and its middle vertex
  is `1`.

* The closure of the class of the triangle under mutation is computed on two models on
  `Fin 3` (`ClusterAlgebras.triangleA`, `ClusterAlgebras.triangleC`), following
  `ClusterAlgebras.a3Path`, and carried to the full subquiver, whose vertex type is the
  subtype of `{0, 1, 2}`, by an explicit isomorphism. The six mutations of the two models
  are closed computations: the arrow hypothesis of each relabelling is phrased on
  `mutationArrows`, which carries no mutability proof, so `decide` runs it.

* The three-fold mutation is stated for arbitrary mutability proofs, which are
  propositions; the computation is run on the decided ones.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to cluster algebras.
  Chapter 4*, Section 4.1, the remarks on arborizable quivers.
-/

@[expose] public section

namespace ClusterAlgebras

/-- The **arborizable example** `Q^arb` on `Fin 5`: no frozen vertices and the seven
simple arrows `0 → 1`, `1 → 2`, `0 → 2`, `2 → 4`, `4 → 0`, `2 → 3`, `3 → 0`. -/
@[cluster_algebras "def_arborizable_example"]
def arborizableExample : Quiver (Fin 5) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 2 ∨ u = 0 ∧ v = 2 ∨ u = 2 ∧ v = 4 ∨
    u = 4 ∧ v = 0 ∨ u = 2 ∧ v = 3 ∨ u = 3 ∧ v = 0 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; revert i j; decide
  frozen_eq_zero := by decide

/-- The **star example** `Q^star` on `Fin 5`: no frozen vertices and the four simple arrows
`0 → 4`, `2 → 4`, `4 → 1`, `4 → 3`. -/
@[cluster_algebras "def_star_example"]
def starExample : Quiver (Fin 5) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 4 ∨ u = 2 ∧ v = 4 ∨ u = 4 ∧ v = 1 ∨ u = 4 ∧ v = 3 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; revert i j; decide
  frozen_eq_zero := by decide

/-- No vertex of the arborizable example is frozen. -/
@[simp]
theorem frozen_arborizableExample : arborizableExample.frozen = ∅ := rfl

/-- No vertex of the star example is frozen. -/
@[simp]
theorem frozen_starExample : starExample.frozen = ∅ := rfl

/-- **Three mutations turn the arborizable example into the star**: mutating `Q^arb` at
`3`, then `2`, then `4` gives `Q^star`. -/
@[cluster_algebras "lem_arborizable_example_mutation"]
theorem mutate_mutate_mutate_arborizableExample (h₁ : (3 : Fin 5) ∉ arborizableExample.frozen)
    (h₂ : (2 : Fin 5) ∉ (arborizableExample.mutate h₁).frozen)
    (h₃ : (4 : Fin 5) ∉ ((arborizableExample.mutate h₁).mutate h₂).frozen) :
    ((arborizableExample.mutate h₁).mutate h₂).mutate h₃ = starExample := by
  refine Quiver.ext' rfl (funext fun u => funext fun v => ?_)
  revert u v
  change ∀ u v, (((arborizableExample.mutate (k := 3) (by decide)).mutate (k := 2)
    (by decide)).mutate (k := 4) (by decide)).arrows u v = starExample.arrows u v
  decide

/-- The **triangle** `Q^arb_{1,2,3}`: the full subquiver of the arborizable example on
`{0, 1, 2}`, with the arrows `0 → 1`, `1 → 2`, `0 → 2`. -/
def arborizableTriangle : Quiver ↥({0, 1, 2} : Finset (Fin 5)) :=
  arborizableExample.fullSubquiver {0, 1, 2}

/-- No vertex of the triangle is frozen. -/
@[simp]
theorem frozen_arborizableTriangle : arborizableTriangle.frozen = ∅ := rfl

/-- The middle vertex `1` of the triangle is mutable. -/
theorem one_notMem_frozen_arborizableTriangle :
    (⟨1, by decide⟩ : ↥({0, 1, 2} : Finset (Fin 5))) ∉ arborizableTriangle.frozen := by
  simp

/-- The mutation `μ_2(Q^arb_{1,2,3})` of the triangle at its middle vertex `1`, with the
arrows `1 → 0`, `2 → 1` and a double arrow `0 ⇒ 2`. -/
def arborizableTriangleMut : Quiver ↥({0, 1, 2} : Finset (Fin 5)) :=
  arborizableTriangle.mutate one_notMem_frozen_arborizableTriangle

/-- The acyclic triangle `0 → 1`, `1 → 2`, `0 → 2` on `Fin 3`, a model of
`ClusterAlgebras.arborizableTriangle`. -/
def triangleA : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 0 ∧ v = 1 ∨ u = 1 ∧ v = 2 ∨ u = 0 ∧ v = 2 then 1 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; revert i j; decide
  frozen_eq_zero := by decide

/-- The triangle `1 → 0`, `2 → 1` with a double arrow `0 ⇒ 2` on `Fin 3`, a model of
`ClusterAlgebras.arborizableTriangleMut`. -/
def triangleC : Quiver (Fin 3) where
  frozen := ∅
  arrows u v := if u = 1 ∧ v = 0 ∨ u = 2 ∧ v = 1 then 1 else if u = 0 ∧ v = 2 then 2 else 0
  isArrowSystem := by intro v; fin_cases v <;> decide
  twoCycleFree := by intro i j; revert i j; decide
  frozen_eq_zero := by decide

namespace Quiver

/-- An isomorphism from a mutation of a quiver without frozen vertices onto another quiver
without frozen vertices, from a vertex map matching the arrows of the second with the
mutated arrows of the first.

The arrow hypothesis is phrased on `mutationArrows`, which mentions no mutability proof, so
for concrete quivers it is a closed computation that `decide` can run. Phrased on
`(X.mutate hk).arrows` it would carry `hk` as a free variable and `decide` would refuse. -/
def Iso.ofMutationArrows {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    {X : Quiver V} {T : Quiver V'} {k : V} (hk : k ∉ X.frozen) (hX : X.frozen = ∅)
    (hT : T.frozen = ∅) (φ : V ≃ V') (h : ∀ u v, T.arrows (φ u) (φ v) = X.mutationArrows k u v) :
    (X.mutate hk).Iso T where
  equiv := φ
  mem_frozen_iff v := by rw [Quiver.frozen_mutate, hX, hT]; simp
  arrows_eq := h

/-- Every mutation of `triangleA` is isomorphic to `triangleA` or to `triangleC`. -/
private theorem triangleA_mutate {k : Fin 3} (hk : k ∉ triangleA.frozen) :
    Nonempty ((triangleA.mutate hk).Iso triangleA) ∨
      Nonempty ((triangleA.mutate hk).Iso triangleC) := by
  fin_cases k
  · exact Or.inl ⟨Iso.ofMutationArrows hk rfl rfl (finRotate 3).symm (by decide)⟩
  · exact Or.inr ⟨Iso.ofMutationArrows hk rfl rfl (Equiv.refl _) (by decide)⟩
  · exact Or.inl ⟨Iso.ofMutationArrows hk rfl rfl (finRotate 3) (by decide)⟩

/-- Every mutation of `triangleC` is isomorphic to `triangleA` or to `triangleC`. -/
private theorem triangleC_mutate {k : Fin 3} (hk : k ∉ triangleC.frozen) :
    Nonempty ((triangleC.mutate hk).Iso triangleA) ∨
      Nonempty ((triangleC.mutate hk).Iso triangleC) := by
  fin_cases k
  · exact Or.inr ⟨Iso.ofMutationArrows hk rfl rfl (Equiv.swap 0 2) (by decide)⟩
  · exact Or.inl ⟨Iso.ofMutationArrows hk rfl rfl (Equiv.refl _) (by decide)⟩
  · exact Or.inr ⟨Iso.ofMutationArrows hk rfl rfl (Equiv.swap 0 2) (by decide)⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Being isomorphic to `triangleA` or to `triangleC` survives a mutation. -/
private theorem triangle_mutate {R : Quiver V}
    (h : Nonempty (R.Iso triangleA) ∨ Nonempty (R.Iso triangleC)) {k : V}
    (hk : k ∉ R.frozen) :
    Nonempty ((R.mutate hk).Iso triangleA) ∨ Nonempty ((R.mutate hk).Iso triangleC) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rcases triangleA_mutate (e.notMem_frozen hk) with h | h
    exacts [Or.inl ⟨(e.mutate hk).trans h.some⟩, Or.inr ⟨(e.mutate hk).trans h.some⟩]
  · rcases triangleC_mutate (e.notMem_frozen hk) with h | h
    exacts [Or.inl ⟨(e.mutate hk).trans h.some⟩, Or.inr ⟨(e.mutate hk).trans h.some⟩]

/-- Being isomorphic to `triangleA` or to `triangleC` survives a whole mutation path. -/
private theorem triangle_result : ∀ {R : Quiver V} (p : R.MutationPath),
    (Nonempty (R.Iso triangleA) ∨ Nonempty (R.Iso triangleC)) →
      Nonempty (p.result.Iso triangleA) ∨ Nonempty (p.result.Iso triangleC)
  | _, .nil _, h => h
  | _, .cons hk p, h => triangle_result p (triangle_mutate h hk)

end Quiver

/-- The bijection from the vertex set `{0, 1, 2}` of the triangle to `Fin 3`, keeping
values. -/
def arborizableTriangleEquiv : ↥({0, 1, 2} : Finset (Fin 5)) ≃ Fin 3 where
  toFun x := ⟨x.1.val, (by decide : ∀ y ∈ ({0, 1, 2} : Finset (Fin 5)), y.val < 3) _ x.2⟩
  invFun i := ⟨Fin.castLE (by omega) i, by fin_cases i <;> decide⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The triangle is isomorphic to its model `triangleA`. -/
def arborizableTriangleIsoTriangleA : arborizableTriangle.Iso triangleA where
  equiv := arborizableTriangleEquiv
  mem_frozen_iff _ := by simp [triangleA]
  arrows_eq := by decide

/-- The mutation of the triangle at its middle vertex is isomorphic to its model
`triangleC`. -/
def arborizableTriangleMutIsoTriangleC : arborizableTriangleMut.Iso triangleC :=
  (arborizableTriangleIsoTriangleA.mutate one_notMem_frozen_arborizableTriangle).trans
    (Quiver.Iso.ofMutationArrows _ rfl rfl (Equiv.refl _) (by decide))

/-- **The mutation class of the triangle.** Every quiver mutation equivalent to the full
subquiver `Q^arb_{1,2,3}` of the arborizable example is isomorphic to it or to its mutation
at the middle vertex. -/
@[cluster_algebras "lem_qi_mutation_class"]
theorem nonempty_iso_of_mutationEquivalent_arborizableTriangle {W : Type*} [Fintype W]
    {R : Quiver W} (h : arborizableTriangle.MutationEquivalent R) :
    Nonempty (R.Iso arborizableTriangle) ∨ Nonempty (R.Iso arborizableTriangleMut) := by
  obtain ⟨p, ⟨e⟩⟩ := h
  rcases Quiver.triangle_result p (Or.inl ⟨arborizableTriangleIsoTriangleA⟩) with f | f
  · exact Or.inl ⟨e.symm.trans (f.some.trans arborizableTriangleIsoTriangleA.symm)⟩
  · exact Or.inr ⟨e.symm.trans (f.some.trans arborizableTriangleMutIsoTriangleC.symm)⟩

section ArrowsBetweenVertices

variable {W : Type*} [Fintype W] {R : Quiver W}

/-- A quiver isomorphic to the triangle or to its mutation at the middle vertex is isomorphic
to one of the two models on `Fin 3`. -/
private theorem nonempty_iso_triangleA_or_triangleC
    (h : Nonempty (R.Iso arborizableTriangle) ∨ Nonempty (R.Iso arborizableTriangleMut)) :
    Nonempty (R.Iso triangleA) ∨ Nonempty (R.Iso triangleC) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  exacts [Or.inl ⟨e.trans arborizableTriangleIsoTriangleA⟩,
    Or.inr ⟨e.trans arborizableTriangleMutIsoTriangleC⟩]

/-- In a quiver isomorphic to the triangle or to its mutation at the middle vertex, any two
distinct vertices are joined by a positive number of arrows. -/
theorem arrows_add_arrows_pos_of_iso_arborizableTriangle_or_mut
    (h : Nonempty (R.Iso arborizableTriangle) ∨ Nonempty (R.Iso arborizableTriangleMut))
    {u v : W} (huv : u ≠ v) : 0 < R.arrows u v + R.arrows v u := by
  have key : ∀ X : Quiver W, ∀ T : Quiver (Fin 3),
      (∀ a b : Fin 3, a ≠ b → 0 < T.arrows a b + T.arrows b a) → X.Iso T →
        0 < X.arrows u v + X.arrows v u := by
    intro X T hT e
    rw [← e.arrows_eq u v, ← e.arrows_eq v u]
    exact hT _ _ (e.equiv.injective.ne huv)
  rcases nonempty_iso_triangleA_or_triangleC h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  exacts [key R triangleA (by decide) e, key R triangleC (by decide) e]

/-- A quiver isomorphic to the triangle or to its mutation at the middle vertex has three
vertices. -/
theorem card_eq_three_of_iso_arborizableTriangle_or_mut
    (h : Nonempty (R.Iso arborizableTriangle) ∨ Nonempty (R.Iso arborizableTriangleMut)) :
    Fintype.card W = 3 := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · simpa using Fintype.card_congr (e.trans arborizableTriangleIsoTriangleA).equiv
  · simpa using Fintype.card_congr (e.trans arborizableTriangleMutIsoTriangleC).equiv

/-- In every quiver mutation equivalent to the triangle `Q^arb_{1,2,3}`, any two distinct
vertices are joined by a positive number of arrows. -/
theorem arrows_add_arrows_pos_of_mutationEquivalent_arborizableTriangle
    (h : arborizableTriangle.MutationEquivalent R) {u v : W} (huv : u ≠ v) :
    0 < R.arrows u v + R.arrows v u :=
  arrows_add_arrows_pos_of_iso_arborizableTriangle_or_mut
    (nonempty_iso_of_mutationEquivalent_arborizableTriangle h) huv

/-- Every quiver mutation equivalent to the triangle `Q^arb_{1,2,3}` has three vertices. -/
theorem card_eq_three_of_mutationEquivalent_arborizableTriangle
    (h : arborizableTriangle.MutationEquivalent R) : Fintype.card W = 3 :=
  card_eq_three_of_iso_arborizableTriangle_or_mut
    (nonempty_iso_of_mutationEquivalent_arborizableTriangle h)

end ArrowsBetweenVertices

end ClusterAlgebras
