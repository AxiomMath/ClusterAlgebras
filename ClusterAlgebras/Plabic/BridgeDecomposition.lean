/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BridgePlabic
public import ClusterAlgebras.Plabic.BridgeWires
public import ClusterAlgebras.Plabic.Reduced

/-!
# The decorated trip permutation of a bridge decomposition

Let `π̃ = (π, ε)` be a decorated permutation on `b` letters and `s` a bridge sequence for its
affinization `f_π̃`. The bridge decomposition `G = G(π̃, s)` realizes `π̃`: its decorated trip
permutation is `(π_G, ε_G) = (π, ε)`.

The trip permutation of the bridge graph is the product `τ_r ∘ ⋯ ∘ τ₁` of the transpositions of
the pairs of `s`, and a bridge sequence factors `π` as this product; so `π_G = π`. A fixed point
`x` of `π` is a fixed point of `f_π̃` modulo `b`, hence lies in no pair of `s`, and `G` carries
there the lollipop `{λ_x}` of colour `ε(x)`. If `ε(x)` is white, this is a white lollipop at `x`.
If `ε(x)` is black, `{λ_x}` is the only lollipop at `x`, and a rooted tree of `G` with root `β(x)`
has the single non-root vertex `{λ_x}`, so it is not collapsible; hence `ε_G(x)` is black.

## Main results

* `ClusterAlgebras.DecoratedPerm.tripPerm_bridgeDecomposition`: `π_G = π`.
* `ClusterAlgebras.DecoratedPerm.heights_eq_empty_of_perm_apply_eq`: a fixed point of `π` is a
  lollipop position.
* `ClusterAlgebras.isWhiteDecorated_bridgeGraph_iff`: at a lollipop position `x` of a bridge
  graph `G(s, γ)`, the decoration is `γ(x)`.
* `ClusterAlgebras.DecoratedPerm.bijective_tripPerm_bridgeDecomposition`: `π_G` is a bijection,
  so `G` has a decorated trip permutation.
* `ClusterAlgebras.DecoratedPerm.decoratedTripPerm_bridgeDecomposition`: the decorated trip
  permutation of `G(π̃, s)` is `π̃`.

## Implementation notes

* Labels are `0`-indexed: `x : Fin b` is FWZ's label `x + 1`.
* The decorated trip permutation is defined given the bijectivity of the trip permutation; here
  that bijectivity follows from `π_G = π`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.10.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset BridgeGraph

/-- At a lollipop position `x` of a bridge graph, the vertex of the dart `λ_x` is `{λ_x}`. -/
theorem vertexOf_lam_bridgeGraph {b : ℕ} {s : List (ℤ × ℤ)} {γ : Fin b → Shade} {x : Fin b}
    (hx0 : heights s x = ∅) :
    (bridgeGraph b s γ).vertexOf ⟨.lam x, hx0⟩ = {⟨.lam x, hx0⟩} := by
  ext e
  rw [(bridgeGraph b s γ).mem_vertexOf, mem_singleton]
  refine ⟨fun h => ?_, fun h => h ▸ Equiv.Perm.SameCycle.refl _ _⟩
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self rfl n

/-- At a lollipop position `x` of a plabic bridge graph, no rooted tree with root `β(x)` is white
collapsible. -/
theorem not_isCollapsibleOfColour_white_bridgeGraph {b : ℕ} {s : List (ℤ × ℤ)}
    {γ : Fin b → Shade} (hG : (bridgeGraph b s γ).IsPlabicGraph) {x : Fin b}
    (hx0 : heights s x = ∅) (T : (bridgeGraph b s γ).RootedTree)
    (hTroot : T.root = (bridgeGraph b s γ).bvertex x) :
    ¬ T.IsCollapsibleOfColour .white := by
  intro hT
  let ℓ : BridgeDart b s := ⟨.lam x, hx0⟩
  have hinv : (bridgeGraph b s γ).inv ℓ = (bridgeGraph b s γ).leg x := rfl
  have hinv' : (bridgeGraph b s γ).inv ((bridgeGraph b s γ).leg x) = ℓ :=
    bridgeGraph.inv_involutive ℓ
  rcases hT.root_cases with ⟨hnb, -⟩ | ⟨-, h2⟩
  · exact hnb (hTroot ▸ ((bridgeGraph b s γ).mem_boundaryVertices.1 (hG.bvertex_mem x)).2)
  have key : ∀ u, Relation.ReflTransGen ((bridgeGraph b s γ).TreeAdj T.nonRoot) T.root u →
      u = T.root ∨ u = (bridgeGraph b s γ).vertexOf ℓ := by
    intro u hu
    induction hu with
    | refl => exact Or.inl rfl
    | tail _ hadj ih =>
      obtain ⟨d, hd, rfl, rfl⟩ := hadj
      have hdB := ((bridgeGraph b s γ).mem_treeDarts.1 hd).1
      rcases ih with h | h
      · right
        have hd' : d ∈ ((bridgeGraph b s γ).bvertex x).filter (· ∉ (bridgeGraph b s γ).bdry) :=
          mem_filter.2 ⟨by rw [← hTroot, ← h]; exact (bridgeGraph b s γ).self_mem_vertexOf d, hdB⟩
        rw [hG.filter_bvertex_notMem_bdry x, mem_singleton] at hd'
        rw [hd', hinv']
      · left
        have : d = ℓ := by
          have := (bridgeGraph b s γ).self_mem_vertexOf d
          rwa [h, vertexOf_lam_bridgeGraph hx0, mem_singleton] at this
        rw [this, hinv, hTroot]
        rfl
  have hsub : T.nonRoot ⊆ {(bridgeGraph b s γ).vertexOf ℓ} := fun w hw =>
    (key w (T.reflTransGen_treeAdj w (mem_insert_of_mem hw))).elim
      (fun h => absurd (h ▸ hw) T.root_notMem_nonRoot) mem_singleton.2
  have := (card_le_card hsub).trans_eq (card_singleton _)
  omega

/-- **The decoration of a bridge graph at a lollipop position.** Let `G = G(s, γ)` be a bridge
graph that is a plabic graph and `x` a lollipop position (it lies in no pair of `s`). Then `G` has
a white lollipop at `x` or a white collapsible tree rooted at `β(x)` iff `γ(x)` is white. -/
theorem isWhiteDecorated_bridgeGraph_iff {b : ℕ} {s : List (ℤ × ℤ)} {γ : Fin b → Shade}
    (hG : (bridgeGraph b s γ).IsPlabicGraph) {x : Fin b} (hx0 : heights s x = ∅) :
    (bridgeGraph b s γ).IsWhiteDecorated x ↔ γ x = .white := by
  let ℓ : BridgeDart b s := ⟨.lam x, hx0⟩
  have hinv : (bridgeGraph b s γ).inv ℓ = (bridgeGraph b s γ).leg x := rfl
  have hcol : (bridgeGraph b s γ).colour ℓ = γ x := rfl
  have hv : (bridgeGraph b s γ).vertexOf ℓ = {ℓ} := vertexOf_lam_bridgeGraph hx0
  have hint : (bridgeGraph b s γ).vertexOf ℓ ∈ (bridgeGraph b s γ).internalVertices := by
    refine (bridgeGraph b s γ).mem_internalVertices.2
      ⟨(bridgeGraph b s γ).mem_vertices.2 ⟨ℓ, rfl⟩, ?_⟩
    rintro ⟨d, hd, hdB⟩
    rw [hv, mem_singleton] at hd
    simp [hd, ℓ] at hdB
  have hlolli : (bridgeGraph b s γ).IsLollipop x ((bridgeGraph b s γ).vertexOf ℓ) :=
    ⟨⟨hint, by rw [hv, card_singleton]⟩, ℓ, (bridgeGraph b s γ).self_mem_vertexOf ℓ,
      hinv ▸ (bridgeGraph b s γ).leg_mem_bvertex x⟩
  constructor
  · rintro (⟨v, ⟨⟨hvI, -⟩, d, hdv, hdinv⟩, hvc⟩ | ⟨T, hTroot, hT⟩)
    · have hdB : d ∉ (bridgeGraph b s γ).bdry := fun h =>
        ((bridgeGraph b s γ).mem_internalVertices.1 hvI).2 ⟨d, hdv, h⟩
      have hd : (bridgeGraph b s γ).inv d ∈
          ((bridgeGraph b s γ).bvertex x).filter (· ∉ (bridgeGraph b s γ).bdry) :=
        mem_filter.2 ⟨hdinv, fun h => hdB (hG.inv_mem_bdry_iff.1 h)⟩
      rw [hG.filter_bvertex_notMem_bdry x, mem_singleton, ← hinv] at hd
      rw [← hcol, ← hG.inv_involutive.injective hd]
      exact hvc d hdv
    · exact absurd hT (not_isCollapsibleOfColour_white_bridgeGraph hG hx0 T hTroot)
  · intro hw
    refine Or.inl ⟨(bridgeGraph b s γ).vertexOf ℓ, hlolli, fun d hd => ?_⟩
    rw [hv, mem_singleton] at hd
    rw [hd, hcol, hw]

namespace DecoratedPerm

variable {b : ℕ} (π : DecoratedPerm b) {s : List (ℤ × ℤ)}

/-- The pairs of a bridge sequence satisfy `1 ≤ i_t < j_t ≤ b`. -/
private theorem bounds_of_isBridgeSequence (hs : IsBridgeSequence b π.affinization s) :
    ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b := fun p hp => by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
  have h := hs.isBridgePair t ht
  exact ⟨h.one_le, h.lt, h.le⟩

/-- **The trip permutation of a bridge decomposition** is the underlying permutation: if `s` is a
bridge sequence for the affinization of `π̃ = (π, ε)`, then `π_G = π` for `G = G(π̃, s)`. -/
theorem tripPerm_bridgeDecomposition (hs : IsBridgeSequence b π.affinization s) (x : Fin b) :
    (π.bridgeDecomposition s).tripPerm x = π.perm x := by
  have h1 := tripPerm_bridgeGraph (π.bounds_of_isBridgeSequence hs)
    (fun x => if h : π.perm x = x then π.colour ⟨x, h⟩ else .black) x
  have h2 := π.perm_eq_positionMap hs x
  rw [bridgeDecomposition_eq]
  ext
  omega

/-- The trip permutation of a bridge decomposition `G(π̃, s)` is a bijection, so `G(π̃, s)` has a
decorated trip permutation. -/
@[cluster_algebras "lem_bridge_decomposition_trip_permutation"]
theorem bijective_tripPerm_bridgeDecomposition (hs : IsBridgeSequence b π.affinization s) :
    Function.Bijective (π.bridgeDecomposition s).tripPerm := by
  rw [funext (π.tripPerm_bridgeDecomposition hs)]
  exact π.perm.bijective

/-- A fixed point of `π` lies in no pair of a bridge sequence for the affinization of `π̃`: it is
a lollipop position of the bridge graph. -/
theorem heights_eq_empty_of_perm_apply_eq (hs : IsBridgeSequence b π.affinization s) {x : Fin b}
    (hx : π.perm x = x) : heights s x = ∅ := by
  have hfix : IsFixedPointMod b (swapProduct b π.affinization s 0) (((x : ℕ) : ℤ) + 1) := by
    rw [swapProduct_zero, IsFixedPointMod, π.affinization_natCast_add_one, hx]
    split_ifs <;> simp [Int.ModEq]
  refine eq_empty_iff_forall_notMem.2 fun t ht => ?_
  obtain ⟨h1, h2, h3⟩ := mem_heights.1 ht
  have hne := hs.ne_of_isFixedPointMod (by omega) hfix (u := t - 1) (by omega) (Nat.zero_le _)
  rw [pair_eq_getElem h1 h2] at h3
  exact h3.elim hne.1 hne.2

/-- Let `π̃ = (π, ε)` be a decorated permutation on `b` letters, `s` a bridge sequence for its
affinization, and `G = G(π̃, s)`. Then the decorated trip permutation of `G` is `π̃`:
`(π_G, ε_G) = (π, ε)`. The trip permutation of `G` is a bijection by
`bijective_tripPerm_bridgeDecomposition`. -/
@[cluster_algebras "lem_bridge_decomposition_trip_permutation"]
theorem decoratedTripPerm_bridgeDecomposition (hs : IsBridgeSequence b π.affinization s)
    (h : Function.Bijective (π.bridgeDecomposition s).tripPerm) :
    (π.bridgeDecomposition s).decoratedTripPerm h = π := by
  refine DecoratedPerm.ext ?_ fun x h1 h2 => ?_
  · ext x
    rw [PlabicData.decoratedTripPerm_perm_apply, π.tripPerm_bridgeDecomposition hs]
  · rw [PlabicData.decoratedTripPerm_colour]
    have key := isWhiteDecorated_bridgeGraph_iff
      (π.isPlabicGraph_bridgeDecomposition (by have := x.pos; omega) hs)
      (π.heights_eq_empty_of_perm_apply_eq hs h2)
    simp only [dif_pos h2] at key
    cases hc : π.colour ⟨x, h2⟩
    · exact (PlabicData.tripDecoration_eq_white_iff _).2 (key.2 hc)
    · rw [hc] at key
      exact (PlabicData.tripDecoration_eq_black_iff _).2 fun hw => absurd (key.1 hw) (by decide)

end DecoratedPerm

end ClusterAlgebras
