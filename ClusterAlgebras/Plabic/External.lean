/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Affinization
public import ClusterAlgebras.Plabic.GrassmannNecklace
public import ClusterAlgebras.Plabic.LocalMoves
public import ClusterAlgebras.Plabic.MinimalTriple
public import ClusterAlgebras.Plabic.Rails
public import ClusterAlgebras.Plabic.StrongEquivalence
public import ClusterAlgebras.Plabic.Reduced
public import ClusterAlgebras.Plabic.Trips
public import ClusterAlgebras.Plabic.WeakSeparation

/-!
# Results on plabic graphs and weak separation assumed without proof

This file states, as axioms, four theorems on reduced plabic graphs and maximal weakly separated
collections due to Danilov–Karzanov–Koshevoy [DKK10] and Oh–Postnikov–Speyer [OPS15], together
with two invariance statements for trip permutations under moves and a characterization of the
decorated permutations whose affinization has length `0`. It also proves that the trip
permutation of a plabic graph is a bijection.

## Main results

* `IsMaximalWeaklySeparatedCollection.card_eq_mul_sub_add_one`: every maximal weakly separated
  collection of `a`-element subsets of `[1, b]` has `a (b - a) + 1` elements.
* `PlabicGraph.IsReduced.weaklySeparated_targetLabel`: the target face labels of a reduced plabic
  graph are pairwise weakly separated.
* `isMaximalWeaklySeparatedCollection_iff_exists_targetLabels`: the maximal weakly separated
  collections of `a`-element subsets of `[1, b]` are exactly the collections of target face labels
  of the reduced plabic graphs with decorated trip permutation `π̃_{a,b}`.
* `mapsTo_surjOn_targetLabels_positroid`: taking target face labels maps the reduced plabic graphs
  with decorated trip permutation `π̃` onto the maximal weakly separated collections inside the
  positroid of the Grassmann necklace of `π̃` containing that necklace.
* `PlabicData.IsPlabicGraph.tripPerm_bijective`: the trip permutation of a plabic graph is a
  bijection.
* `PlabicGraph.MoveEquivalent.tripPerm_eq`: move-equivalent plabic graphs have the same trip
  permutation.
* `PlabicGraph.IsReduced.decoratedTripPerm_eq`: a reduced plabic graph and any plabic graph
  move-equivalent to it have the same decorated trip permutation.
* `DecoratedPerm.eq_topCell_of_affineLength_eq_zero`: a decorated permutation whose affinization
  has length `0` is `π̃_{a,b}`.

## Implementation notes

* A label `i : Fin b` stands for the boundary vertex `i + 1` of `[1, b]`.

## References

* [V. I. Danilov, A. V. Karzanov, G. A. Koshevoy, *On maximal weakly separated set-systems*,
  J. Algebraic Combin. 32 (2010)][DKK10]
* [S. Oh, A. Postnikov, D. E. Speyer, *Weak separation and plabic graphs*, Proc. Lond. Math. Soc.
  (3) 110 (2015)][OPS15]
-/

@[expose] public section

namespace ClusterAlgebras

/-! ### Weak separation and target face labels -/

/-- **The size of a maximal weakly separated collection.** Let `b ≥ 1` and `0 ≤ a ≤ b`. Every
maximal weakly separated collection `𝒞 ⊆ ([b] choose a)` has exactly `a (b - a) + 1` elements
[DKK10], [OPS15]. -/
@[cluster_algebras "ext_max_weakly_separated_size"]
axiom IsMaximalWeaklySeparatedCollection.card_eq_mul_sub_add_one {b a : ℕ} (hb : 1 ≤ b)
    (hab : a ≤ b) {C : Finset (Finset (Fin b))} (hC : IsMaximalWeaklySeparatedCollection a C) :
    C.card = a * (b - a) + 1

/-- **Face labels are weakly separated.** Let `G` be a reduced plabic graph with `b` boundary
vertices and let `f, f'` be faces of `G`. Then the target labels `I_tgt(f)` and `I_tgt(f')` are
weakly separated [DKK10], [OPS15]. -/
@[cluster_algebras "ext_face_labels_weakly_separated"]
axiom PlabicGraph.IsReduced.weaklySeparated_targetLabel {b : ℕ} {G : PlabicGraph b}
    (hG : G.IsReduced) {f f' : Finset G.Dart} (hf : f ∈ G.data.faces)
    (hf' : f' ∈ G.data.faces) :
    WeaklySeparated (G.data.targetLabel f) (G.data.targetLabel f')

/-- **Maximal weakly separated collections are the label sets of the top cell.** Let `b ≥ 1`,
`0 ≤ a ≤ b` and `𝒞 ⊆ ([b] choose a)`. Then `𝒞` is a maximal weakly separated collection if and
only if `𝒞 = 𝓕_tgt(G)` for some reduced plabic graph `G` with `b` boundary vertices and
`π̃_G = π̃_{a,b}`.

The decorated trip permutation is formed from the bijectivity of the trip permutation, quantified
existentially (any proof gives the same `π̃_G`) [DKK10], [OPS15]. -/
@[cluster_algebras "ext_max_weakly_separated"]
axiom isMaximalWeaklySeparatedCollection_iff_exists_targetLabels {b a : ℕ} (hb : 1 ≤ b)
    (hab : a ≤ b) {C : Finset (Finset (Fin b))} (hC : C ⊆ Finset.powersetCard a Finset.univ) :
    IsMaximalWeaklySeparatedCollection a C ↔
      ∃ G : PlabicGraph b, G.IsReduced ∧
        (∃ hπ : Function.Bijective G.data.tripPerm,
          G.data.decoratedTripPerm hπ = DecoratedPerm.topCell a b) ∧
        C = G.data.targetLabels

/-- **Oh–Postnikov–Speyer.** Let `π̃` be a decorated permutation on `b` letters with `a`
anti-excedances, `𝓘 = 𝓘(π̃)` its Grassmann necklace and `𝓜_𝓘` its positroid. Then sending a
reduced plabic graph `G` to `𝓕_tgt(G)` induces a bijection from the set of strong equivalence
classes of reduced plabic graphs `G` with `b` boundary vertices and `π̃_G = π̃` onto the set of
collections `𝒞 ⊆ ([b] choose a)` that are weakly separated, satisfy `{I_1, …, I_b} ⊆ 𝒞 ⊆ 𝓜_𝓘`, and
are maximal under inclusion among such collections.

The induced map is well defined and injective on strong equivalence classes by the definition of
strong equivalence (`PlabicGraph.StronglyEquivalent`: equal `𝓕_tgt`); the content, stated here, is
that `𝓕_tgt(G)` is such a maximal collection for every such `G` (`MapsTo`), and that every such
collection arises (`SurjOn`). See [OPS15], Theorem 1.5. -/
@[cluster_algebras "ext_weakly_separated_positroid"]
axiom mapsTo_surjOn_targetLabels_positroid {b : ℕ} (π : DecoratedPerm b) :
    Set.MapsTo (fun G : PlabicGraph b => G.data.targetLabels)
        {G | G.IsReduced ∧ ∃ hπ, G.data.decoratedTripPerm hπ = π}
        {C | Maximal (DecoratedPerm.IsNecklaceWeaklySeparatedCollection π π.numAntiExcedances) C} ∧
      Set.SurjOn (fun G : PlabicGraph b => G.data.targetLabels)
        {G | G.IsReduced ∧ ∃ hπ, G.data.decoratedTripPerm hπ = π}
        {C | Maximal (DecoratedPerm.IsNecklaceWeaklySeparatedCollection π π.numAntiExcedances) C}

/-! ### Trip permutations -/

/-- **The trip permutation is a permutation.** Let `G` be a plabic graph with `b` boundary
vertices. Then its trip permutation `π_G` is a bijection of `[1, b]`: one-way trips starting at
different boundary vertices end at different boundary vertices. -/
@[cluster_algebras "lem_trip_permutation_bijective"]
theorem PlabicData.IsPlabicGraph.tripPerm_bijective {H : Type*} [Fintype H] [DecidableEq H]
    {b : ℕ} {G : PlabicData H b} (hG : G.IsPlabicGraph) : Function.Bijective G.tripPerm := by
  have key : ∀ {i j : Fin b}, G.tripLength i ≤ G.tripLength j →
      G.tripMap^[G.tripLength i] (G.leg i) = G.tripMap^[G.tripLength j] (G.leg j) → i = j := by
    intro i j hle h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, Function.iterate_add_apply] at h
    have h' := ((PlabicData.tripMap_bijective hG).injective.iterate _) h
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp only [Function.iterate_zero, id_eq] at h'
      exact hG.leg_injective h'
    · have hlt : k < G.tripLength j := by have := hG.tripLength_pos i; omega
      exact absurd ⟨i, h'⟩ (G.not_isLeg_of_lt_tripLength hkpos hlt)
  refine Finite.injective_iff_bijective.mp fun i j hij => ?_
  have hi := hG.leg_tripPerm i
  have hj := hG.leg_tripPerm j
  rw [hij] at hi
  rcases le_total (G.tripLength i) (G.tripLength j) with h | h
  · exact key h (hi.symm.trans hj)
  · exact (key h (hj.symm.trans hi)).symm

/-- **Move-equivalent graphs have the same trip permutation.** Let `G` and `G'` be plabic
graphs with `G ∼ G'`. Then `π_G = π_{G'}`. -/
@[cluster_algebras "lem_trip_permutation_move_invariant"]
axiom PlabicGraph.MoveEquivalent.tripPerm_eq {b : ℕ} {G G' : PlabicGraph b}
    (h : PlabicGraph.MoveEquivalent Set.univ G G') : G.data.tripPerm = G'.data.tripPerm

/-- **The decorated trip permutation of a reduced graph is invariant.** Let `G` be a reduced
plabic graph and `G'` a plabic graph with `G ∼ G'`. Then `(π_G, ε_G) = (π_{G'}, ε_{G'})`.

The decorated trip permutations are formed from the bijectivity of the trip permutations, passed
as `hπ` and `hπ'` (the statement does not depend on them). -/
@[cluster_algebras "lem_decorated_trip_permutation_move_invariant"]
axiom PlabicGraph.IsReduced.decoratedTripPerm_eq {b : ℕ} {G G' : PlabicGraph b}
    (hG : G.IsReduced) (h : PlabicGraph.MoveEquivalent Set.univ G G')
    (hπ : Function.Bijective G.data.tripPerm) (hπ' : Function.Bijective G'.data.tripPerm) :
    G.data.decoratedTripPerm hπ = G'.data.decoratedTripPerm hπ'

/-- **Length zero.** Let `π̃` be a decorated permutation on `b` letters with `a`
anti-excedances such that its affinization `f_{π̃}` has length `ℓ(f_{π̃}) = 0`. Then
`π̃ = π̃_{a,b}`. -/
@[cluster_algebras "lem_length_zero"]
axiom DecoratedPerm.eq_topCell_of_affineLength_eq_zero {b : ℕ} (π : DecoratedPerm b)
    (h : affineLength b π.affinization = 0) : π = DecoratedPerm.topCell π.numAntiExcedances b

end ClusterAlgebras
