/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.FundamentalTheorem
public import ClusterAlgebras.Plabic.BridgeDecompositionTheorem
public import ClusterAlgebras.Plabic.NonReduced

/-!
# The number of faces of a reduced plabic graph

Reduced plabic graphs with the same number `b` of boundary vertices and the same trip
permutation have equally many faces. The proof is by induction on `b`: without fixed points of
the trip permutation the decorated trip permutations agree and the fundamental theorem applies;
a fixed point is carried, after collapsing a tree, by a lollipop, which is extracted.

As a consequence, a nearly leafless plabic graph is reduced if and only if it has the fewest faces
among all plabic graphs with its trip permutation.

Comparing a reduced plabic graph `G` with a bridge decomposition of its decorated trip permutation
`π̃_G`, which has `r + 1` faces for a bridge sequence of length `r = a(b - a) - ℓ(f_{π̃_G})`, the
number of faces of `G` is `a(b - a) - ℓ(f_{π̃_G}) + 1`, where `a` is the number of anti-excedances
of `π̃_G` and `f_{π̃_G}` its affinization. So `G` has at most `a(b - a) + 1` faces, with equality
exactly when `π̃_G` is the top cell permutation `π̃_{a,b}`.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.card_faces_eq_of_tripPerm_eq`: reduced graphs with the
  same trip permutation have equally many faces.
* `ClusterAlgebras.PlabicGraph.isReduced_iff_forall_card_faces_le`: a nearly leafless graph is
  reduced if and only if it has the fewest faces among the graphs with its trip permutation.
* `ClusterAlgebras.PlabicGraph.IsReduced.card_faces_eq`: a reduced graph has
  `a(b - a) - ℓ(f_{π̃_G}) + 1` faces.
* `ClusterAlgebras.PlabicGraph.IsReduced.card_faces_le`: a reduced graph has at most
  `a(b - a) + 1` faces.
* `ClusterAlgebras.PlabicGraph.IsReduced.card_faces_eq_iff`: a reduced graph has exactly
  `a(b - a) + 1` faces if and only if `π̃_G = π̃_{a,b}`.

## Implementation notes

* Labels are `0`-indexed: `i : Fin b` is FWZ's label `i + 1`.
* The length `ℓ(f)` of an affine permutation takes values in `ℕ∞`, so the face count of
  `ClusterAlgebras.PlabicGraph.IsReduced.card_faces_eq` is stated in `ℕ∞`; the length is finite
  and at most `a(b - a)`, so the truncated subtraction there is the subtraction of integers.
* The decorated trip permutation is formed from a proof `hπ` that the trip permutation is a
  bijection; the statements do not depend on that proof.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-! ### Reduced graphs with the same trip permutation -/

/-- A reduced graph `G` with a fixed point `i` of `π_G` is move-equivalent to a graph with a
lollipop at `i`. -/
private theorem exists_moveEquivalent_isLollipopOfColour_of_tripPerm_eq_self
    {G : PlabicGraph b} (hG : G.IsReduced) {i : Fin b} (hi : G.data.tripPerm i = i) :
    ∃ G₁ : PlabicGraph b, MoveEquivalent Set.univ G G₁ ∧
      ∃ c u, G₁.data.IsLollipopOfColour i c u := by
  have key : ∃ G₁ : PlabicGraph b, MoveEquivalent Set.univ G G₁ ∧ ∃ u, G₁.data.IsLollipop i u := by
    rcases hG.exists_isLollipop_or_isCollapsible_of_tripPerm_eq_self hi with
      ⟨u, hu⟩ | ⟨T, hT, c, hc⟩
    · exact ⟨G, .refl _ _, u, hu⟩
    · obtain ⟨h1, hmove⟩ := hc.moveEquivalent_collapse G.isPlabicGraph
      obtain ⟨u, hu⟩ := T.exists_isLollipop_collapse G.isPlabicGraph c hT
      exact ⟨⟨_, _, h1⟩, hmove.mono (Set.subset_univ _), u, hu⟩
  obtain ⟨G₁, hGG₁, u, hu⟩ := key
  have hu' := hu.eq_singleton_inv_leg G₁.isPlabicGraph
  refine ⟨G₁, hGG₁, G₁.data.colour (G₁.data.inv (G₁.data.leg i)), u, hu, fun d hd => ?_⟩
  rw [hu', Finset.mem_singleton] at hd
  rw [hd]

/-- Reduced plabic graphs with the same number of boundary vertices and the same trip
permutation have the same number of faces. -/
private theorem card_faces_eq_of_tripPerm_eq_aux :
    ∀ (b : ℕ) (G G' : PlabicGraph b), G.IsReduced → G'.IsReduced →
      G.data.tripPerm = G'.data.tripPerm → G.data.faces.card = G'.data.faces.card := by
  intro b
  induction b with
  | zero =>
    intro G _ _ _ _
    exact absurd G.isPlabicGraph.one_le (by omega)
  | succ n ih =>
    intro G G' hG hG' hperm
    by_cases hfix : ∃ i, G.data.tripPerm i = i
    swap
    · push Not at hfix
      have hπ := G.isPlabicGraph.tripPerm_bijective
      have hπ' := G'.isPlabicGraph.tripPerm_bijective
      have hdec : G.data.decoratedTripPerm hπ = G'.data.decoratedTripPerm hπ' := by
        refine DecoratedPerm.ext ?_ fun x h1 _ => ?_
        · ext x
          rw [decoratedTripPerm_perm_apply, decoratedTripPerm_perm_apply, hperm]
        · exact absurd h1 (hfix x)
      exact (MoveEquivalent.card_eq
        ((hG.moveEquivalent_iff_decoratedTripPerm_eq hG' hπ hπ').2 hdec)).2.1
    obtain ⟨i, hi⟩ := hfix
    have hi' : G'.data.tripPerm i = i := by rwa [← hperm]
    obtain ⟨G₁, hGG₁, c, u, hu⟩ :=
      exists_moveEquivalent_isLollipopOfColour_of_tripPerm_eq_self hG hi
    obtain ⟨G₁', hGG₁', c', u', hu'⟩ :=
      exists_moveEquivalent_isLollipopOfColour_of_tripPerm_eq_self hG' hi'
    rw [(MoveEquivalent.card_eq hGG₁).2.1, (MoveEquivalent.card_eq hGG₁').2.1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rw [(G₁.isPlabicGraph.isomorphic_lollipopGraph hu).card_faces,
        (G₁'.isPlabicGraph.isomorphic_lollipopGraph hu').card_faces, card_faces_lollipopGraph,
        card_faces_lollipopGraph]
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨A, hA⟩ := G₁.isPlabicGraph.exists_isomorphic_lollipopInsertion hu
    obtain ⟨A', hA'⟩ := G₁'.isPlabicGraph.exists_isomorphic_lollipopInsertion hu'
    have hGI : MoveEquivalent Set.univ G (A.lollipopInsertion i c) :=
      hGG₁.trans (MoveEquivalent.of_isomorphic (S := Set.univ) (G := A.lollipopInsertion i c)
        (G' := G₁) hA).symm
    have hGI' : MoveEquivalent Set.univ G' (A'.lollipopInsertion i c') :=
      hGG₁'.trans (MoveEquivalent.of_isomorphic (S := Set.univ) (G := A'.lollipopInsertion i c')
        (G' := G₁') hA').symm
    have hAred : A.IsReduced := IsReduced.of_lollipopInsertion (hG.of_moveEquivalent hGI)
    have hAred' : A'.IsReduced := IsReduced.of_lollipopInsertion (hG'.of_moveEquivalent hGI')
    have hAA : A.data.tripPerm = A'.data.tripPerm := by
      funext j
      apply i.succAbove_right_injective
      rw [← tripPerm_lollipopInsertion_succAbove (c := c) A.isPlabicGraph,
        ← tripPerm_lollipopInsertion_succAbove (c := c') A'.isPlabicGraph]
      change (A.lollipopInsertion i c).data.tripPerm _ = (A'.lollipopInsertion i c').data.tripPerm _
      rw [← hGI.tripPerm_eq, ← hGI'.tripPerm_eq, hperm]
    rw [hA.card_faces, hA'.card_faces, card_faces_lollipopInsertion A.isPlabicGraph,
      card_faces_lollipopInsertion A'.isPlabicGraph]
    exact ih A A' hAred hAred' hAA

/-- Let `G` and `G'` be reduced plabic graphs with the same number `b` of boundary vertices and
with `π_G = π_{G'}`. Then `G` and `G'` have the same number of faces. -/
@[cluster_algebras "lem_reduced_same_faces"]
theorem IsReduced.card_faces_eq_of_tripPerm_eq {G G' : PlabicGraph b} (hG : G.IsReduced)
    (hG' : G'.IsReduced) (h : G.data.tripPerm = G'.data.tripPerm) :
    G.data.faces.card = G'.data.faces.card :=
  card_faces_eq_of_tripPerm_eq_aux b G G' hG hG' h

/-! ### Reduced graphs have the fewest faces -/

/-- A reduced plabic graph has at most as many faces as any plabic graph with the same trip
permutation. -/
theorem IsReduced.card_faces_le_of_tripPerm_eq {G : PlabicGraph b} (hred : G.IsReduced)
    (G' : PlabicGraph b) (hπ : G'.data.tripPerm = G.data.tripPerm) :
    G.data.faces.card ≤ G'.data.faces.card := by
  have key : ∀ n, ∀ G' : PlabicGraph b, G'.data.IsNearlyLeafless →
      G'.data.tripPerm = G.data.tripPerm → G'.data.faces.card = n →
      G.data.faces.card ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro G' hG' hπ hn
    by_cases hred' : G'.IsReduced
    · exact (hred.card_faces_eq_of_tripPerm_eq hred' hπ.symm).trans hn |>.le
    · obtain ⟨G'', hG'', hπ'', hlt⟩ :=
        exists_isNearlyLeafless_card_faces_lt_of_not_isReduced hG' hred'
      exact (ih _ (hn ▸ hlt) G'' hG'' (hπ''.trans hπ) rfl).trans (hn ▸ hlt).le
  obtain ⟨K, hK, hKπ, hKf⟩ := G'.isPlabicGraph.exists_isNearlyLeafless
  exact hKf ▸ key _ K hK (hKπ.trans hπ) rfl

/-- Let `G` be a nearly leafless plabic graph with `b` boundary vertices. Then `G` is reduced if
and only if every plabic graph `G'` with `b` boundary vertices and `π_{G'} = π_G` has at least as
many faces as `G`. -/
@[cluster_algebras "prop_reduced_min_faces"]
theorem isReduced_iff_forall_card_faces_le {G : PlabicGraph b} (hG : G.data.IsNearlyLeafless) :
    G.IsReduced ↔ ∀ G' : PlabicGraph b, G'.data.tripPerm = G.data.tripPerm →
      G.data.faces.card ≤ G'.data.faces.card := by
  refine ⟨fun hred => hred.card_faces_le_of_tripPerm_eq, fun h => ?_⟩
  by_contra hred
  obtain ⟨G'', -, hπ, hlt⟩ := exists_isNearlyLeafless_card_faces_lt_of_not_isReduced hG hred
  exact absurd (h G'' hπ) (not_le.2 hlt)

/-! ### The number of faces of a reduced graph -/

/-- A reduced plabic graph `G` has `r + 1` faces for some bridge sequence `s` of length `r` for
the affinization of its decorated trip permutation. -/
private theorem exists_isBridgeSequence_card_faces_eq {G : PlabicGraph b} (hG : G.IsReduced)
    (hπ : Function.Bijective G.data.tripPerm) :
    ∃ s, IsBridgeSequence b (G.data.decoratedTripPerm hπ).affinization s ∧
      G.data.faces.card = s.length + 1 := by
  have hb := G.isPlabicGraph.one_le
  set π := G.data.decoratedTripPerm hπ
  obtain ⟨s, hs⟩ := π.isBoundedAffinePerm_affinization.exists_isBridgeSequence
  let G' : PlabicGraph b :=
    ⟨BridgeDart b s, π.bridgeDecomposition s, π.isPlabicGraph_bridgeDecomposition hb hs⟩
  have hG' : G'.IsReduced := π.isReduced_bridgeDecomposition hb hs
  have hπ' := π.bijective_tripPerm_bridgeDecomposition hs
  have hdec : G'.data.decoratedTripPerm hπ' = π := π.decoratedTripPerm_bridgeDecomposition hs hπ'
  have hmove : MoveEquivalent Set.univ G G' :=
    (hG.moveEquivalent_iff_decoratedTripPerm_eq hG' hπ hπ').2 hdec.symm
  refine ⟨s, hs, (MoveEquivalent.card_eq hmove).2.1.trans ?_⟩
  exact card_faces_bridgeGraph hb hs.forall_mem_bounds hs.isNestedPairSequence _

/-- A reduced plabic graph `G` has `r + 1` faces where `ℓ(f_{π̃_G}) + r = a(b - a)`. -/
private theorem exists_card_faces_eq_add_one {G : PlabicGraph b} (hG : G.IsReduced)
    (hπ : Function.Bijective G.data.tripPerm) :
    ∃ r : ℕ, G.data.faces.card = r + 1 ∧
      affineLength b (G.data.decoratedTripPerm hπ).affinization + r =
        ((G.data.decoratedTripPerm hπ).numAntiExcedances *
          (b - (G.data.decoratedTripPerm hπ).numAntiExcedances) : ℕ) := by
  obtain ⟨s, hs, hcard⟩ := exists_isBridgeSequence_card_faces_eq hG hπ
  have hf := (G.data.decoratedTripPerm hπ).isBoundedAffinePerm_affinization
  refine ⟨s.length, hcard, ?_⟩
  rw [← hs.affineLength_swapProduct hf le_rfl,
    (hs.isBoundedAffinePerm_swapProduct hf _).affineLength_eq_of_forall_isFixedPointMod
      hs.isFixedPointMod]

/-- Let `G` be a reduced plabic graph with `b` boundary vertices whose decorated trip permutation
`π̃_G` has `a` anti-excedances. Then `G` has exactly `a(b - a) - ℓ(f_{π̃_G}) + 1` faces, where
`f_{π̃_G}` is the affinization of `π̃_G`. The decorated trip permutation is formed from any proof
`hπ` that `π_G` is a bijection. -/
@[cluster_algebras "prop_number_of_faces"]
theorem IsReduced.card_faces_eq {G : PlabicGraph b} (hG : G.IsReduced)
    (hπ : Function.Bijective G.data.tripPerm) {a : ℕ}
    (ha : (G.data.decoratedTripPerm hπ).numAntiExcedances = a) :
    (G.data.faces.card : ℕ∞) =
      (a * (b - a) : ℕ) - affineLength b (G.data.decoratedTripPerm hπ).affinization + 1 := by
  obtain ⟨r, hcard, hr⟩ := exists_card_faces_eq_add_one hG hπ
  rw [ha] at hr
  rw [hcard, ← hr]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (affineLength_ne_top (b := b)
    (G.data.decoratedTripPerm hπ).isBoundedAffinePerm_affinization.le_apply
    (G.data.decoratedTripPerm hπ).isBoundedAffinePerm_affinization.apply_le)
  rw [← hn]
  norm_cast
  omega

/-- Let `G` be a reduced plabic graph with `b` boundary vertices whose decorated trip permutation
`π̃_G` has `a` anti-excedances. Then `G` has at most `a(b - a) + 1` faces. -/
@[cluster_algebras "prop_max_number_of_faces"]
theorem IsReduced.card_faces_le {G : PlabicGraph b} (hG : G.IsReduced)
    (hπ : Function.Bijective G.data.tripPerm) {a : ℕ}
    (ha : (G.data.decoratedTripPerm hπ).numAntiExcedances = a) :
    G.data.faces.card ≤ a * (b - a) + 1 := by
  obtain ⟨r, hcard, hr⟩ := exists_card_faces_eq_add_one hG hπ
  rw [ha] at hr
  have : (r : ℕ∞) ≤ (a * (b - a) : ℕ) := hr ▸ le_add_self
  have : r ≤ a * (b - a) := by exact_mod_cast this
  omega

/-- The number of anti-excedances of a decorated permutation on `b` letters is at most `b`. -/
theorem _root_.ClusterAlgebras.DecoratedPerm.numAntiExcedances_le (π : DecoratedPerm b) :
    π.numAntiExcedances ≤ b :=
  (Finset.card_filter_le _ _).trans (Finset.card_fin b).le

/-- Let `G` be a reduced plabic graph with `b` boundary vertices whose decorated trip permutation
`π̃_G` has `a` anti-excedances. Then `G` has exactly `a(b - a) + 1` faces if and only if
`π̃_G = π̃_{a,b}`. -/
@[cluster_algebras "prop_max_faces_top_cell"]
theorem IsReduced.card_faces_eq_iff {G : PlabicGraph b} (hG : G.IsReduced)
    (hπ : Function.Bijective G.data.tripPerm) {a : ℕ}
    (ha : (G.data.decoratedTripPerm hπ).numAntiExcedances = a) :
    G.data.faces.card = a * (b - a) + 1 ↔
      G.data.decoratedTripPerm hπ = DecoratedPerm.topCell a b := by
  set π := G.data.decoratedTripPerm hπ with hπdef
  obtain ⟨r, hcard, hr⟩ := exists_card_faces_eq_add_one hG hπ
  rw [← hπdef, ha] at hr
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (affineLength_ne_top (b := b)
    π.isBoundedAffinePerm_affinization.le_apply π.isBoundedAffinePerm_affinization.apply_le)
  rw [← hn] at hr
  have hr' : n + r = a * (b - a) := by exact_mod_cast hr
  have key : G.data.faces.card = a * (b - a) + 1 ↔ affineLength b π.affinization = 0 := by
    rw [← hn, hcard]
    norm_cast
    omega
  rw [key]
  refine ⟨fun h0 => by rw [π.eq_topCell_of_affineLength_eq_zero h0, ha], fun htop => ?_⟩
  have hab : a ≤ b := ha ▸ π.numAntiExcedances_le
  rw [htop, DecoratedPerm.affinization_topCell hab, affineLength, Set.encard_eq_zero]
  ext ⟨p, q⟩
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, IsInversion]
  omega

end PlabicGraph

end ClusterAlgebras
