/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Core
public import ClusterAlgebras.Plabic.Excision
public import ClusterAlgebras.Plabic.Trees
public import ClusterAlgebras.Plabic.TripRuns
public import ClusterAlgebras.Plabic.TripleDiagram

/-!
# Lollipops, stray leaves and hollow digons

This file proves the facts about small configurations used to compare the numbers of faces of
plabic graphs with the same trip permutation.

*The lollipop graph.* The lollipop graph `L_c` is a plabic graph with one boundary vertex and
exactly one face, whose internal vertex `{ḡ}` is a lollipop at `0` of colour `c`; conversely a
plabic graph with one boundary vertex and a lollipop `u` at `0` is isomorphic to `L_{κ(u)}`.

*Stray leaves.* Deleting an internal leaf that is not a lollipop keeps the boundary, the trip
permutation and the number of faces; repeating, every plabic graph has a nearly leafless relative
with the same trip permutation and as many faces.

*Hollow digons.* If `{d₁, d₂}` is a hollow digon of a plabic graph `K` whose two vertices have the
same colour, then the excision `K ⊖ {{d₂, d̄₂}}` of one side is a plabic graph with the trip
permutation of `K` and one face fewer. If the two vertices have different colours, the excision
`K ⊖ {{d₁, d̄₁}, {d₂, d̄₂}}` of both sides is a plabic graph with the trip permutation of `K` and
fewer faces.

## Main results

* `ClusterAlgebras.isPlabicGraph_lollipopGraph_and_isLollipopOfColour`: the lollipop graph is a
  plabic graph.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.isomorphic_lollipopGraph`: a plabic graph with one
  boundary vertex and a lollipop is a lollipop graph.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.exists_isNearlyLeafless`: stray leaves can be pruned.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.edgeExcision_of_isHollowDigon_of_colour_eq`: removing
  one side of a one-coloured hollow digon.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.edgeExcision_of_isHollowDigon_of_colour_ne`: removing
  both sides of a bicoloured hollow digon.

## Implementation notes

* **Comparing trips.** The trip permutations of a plabic graph `K` and of a graph `K'` whose darts
  are a subset of those of `K` are compared through `IsPlabicGraph.tripPerm_eq_of_firstReturn`:
  on a set `Y` of darts of both graphs containing the legs, the first-return maps of the two trip
  maps agree. In each application every dart of `Y` is followed, in `K` and in `K'`, by at most
  two darts outside `Y` before the trip returns to `Y`.
* **Labels.** The label `i : Fin b` is the label `i + 1` of [FWZ]; the unique label of a graph
  with one boundary vertex is `0 : Fin 1`, the label `1` of [FWZ].

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm

/-! ### The lollipop graph -/

/-- The internal vertex `{ḡ}` of `L_c` is a lollipop at the label `0` of colour `c`. -/
theorem isLollipopOfColour_lollipopGraph (c : Shade) :
    (lollipopGraph c).IsLollipopOfColour 0 c {.gBar} := by
  refine ⟨⟨⟨?_, ?_⟩, .gBar, ?_, ?_⟩, ?_⟩ <;> cases c <;> decide

/-- The lollipop graph `L_c` has exactly one face. -/
theorem card_faces_lollipopGraph (c : Shade) : (lollipopGraph c).faces.card = 1 := by
  rw [faces_lollipopGraph]
  rfl

/-- **The lollipop graph is a plabic graph**: `L_c` is a plabic graph with one boundary vertex
and exactly one face, and its internal vertex `{ḡ}` is a lollipop at the label `0` of colour `c`.
-/
@[cluster_algebras "lem_lollipop_graph_plabic"]
theorem isPlabicGraph_lollipopGraph_and_isLollipopOfColour (c : Shade) :
    (lollipopGraph c).IsPlabicGraph ∧ (lollipopGraph c).boundaryVertices.card = 1 ∧
      (lollipopGraph c).faces.card = 1 ∧ (lollipopGraph c).IsLollipopOfColour 0 c {.gBar} :=
  ⟨isPlabicGraph_lollipopGraph c, card_boundaryVertices_lollipopGraph c,
    card_faces_lollipopGraph c, isLollipopOfColour_lollipopGraph c⟩

/-! ### Counting orbits -/

section NumOrbits

variable {α β : Type*}

private theorem sameCycle_semiconj_iff [Finite α] [Finite β] {f : Perm α} {g : Perm β}
    (θ : α ≃ β) (h : ∀ x, θ (f x) = g (θ x)) {x y : α} :
    g.SameCycle (θ x) (θ y) ↔ f.SameCycle x y := by
  have hpow : ∀ (n : ℕ) (x : α), θ ((f ^ n) x) = (g ^ n) (θ x) := by
    intro n
    induction n with
    | zero => exact fun _ => rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Perm.mul_apply, h, ih, pow_succ', Perm.mul_apply]
  constructor
  · intro hg
    obtain ⟨n, hn⟩ := hg.exists_nat_pow_eq
    rw [← hpow] at hn
    exact ⟨n, by simpa using θ.injective hn⟩
  · intro hf
    obtain ⟨n, hn⟩ := hf.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← hpow, hn]⟩

private theorem numOrbits_of_semiconj [Finite α] [Finite β] {f : Perm α} {g : Perm β}
    (θ : α ≃ β) (h : ∀ x, θ (f x) = g (θ x)) : numOrbits f = numOrbits g :=
  Nat.card_congr (Quotient.congr θ fun _ _ => (sameCycle_semiconj_iff θ h).symm)

private theorem sumCongr_zpow' (a : Perm α) (b : Perm β) (n : ℤ) :
    Perm.sumCongr a b ^ n = Perm.sumCongr (a ^ n) (b ^ n) := by
  simpa using (map_zpow (Perm.sumCongrHom α β) (a, b) n).symm

private theorem numOrbits_sumCongr' [Finite α] [Finite β] (a : Perm α) (b : Perm β) :
    numOrbits (Perm.sumCongr a b) = numOrbits a + numOrbits b := by
  have hll : ∀ {x y : α}, (Perm.sumCongr a b).SameCycle (Sum.inl x) (Sum.inl y) ↔
      a.SameCycle x y := by
    simp [Perm.SameCycle, sumCongr_zpow']
  have hrr : ∀ {x y : β}, (Perm.sumCongr a b).SameCycle (Sum.inr x) (Sum.inr y) ↔
      b.SameCycle x y := by
    simp [Perm.SameCycle, sumCongr_zpow']
  have hlr : ∀ {x : α} {y : β}, ¬(Perm.sumCongr a b).SameCycle (Sum.inl x) (Sum.inr y) := by
    simp [Perm.SameCycle, sumCongr_zpow']
  have hrl : ∀ {x : β} {y : α}, ¬(Perm.sumCongr a b).SameCycle (Sum.inr x) (Sum.inl y) := by
    simp [Perm.SameCycle, sumCongr_zpow']
  unfold numOrbits
  rw [← Nat.card_sum]
  refine Nat.card_congr
    { toFun := Quotient.lift (Sum.elim (fun x => Sum.inl ⟦x⟧) (fun y => Sum.inr ⟦y⟧)) ?_
      invFun := Sum.elim
        (Quotient.map Sum.inl fun x y h => hll.2 h)
        (Quotient.map Sum.inr fun x y h => hrr.2 h)
      left_inv := ?_
      right_inv := ?_ }
  · rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (Quotient.sound (hll.1 h))
    · exact absurd h hlr
    · exact absurd h hrl
    · exact congrArg Sum.inr (Quotient.sound (hrr.1 h))
  · intro q
    induction q using Quotient.inductionOn with | h x => ?_
    rcases x with x | x <;> rfl
  · rintro (q | q)
    · induction q using Quotient.inductionOn with | h x => rfl
    · induction q using Quotient.inductionOn with | h x => rfl

/-- The orbits of a permutation preserving a set `C` are those inside `C` and those outside. -/
private theorem numOrbits_eq_add_subtypePerm [Finite α] (π : Perm α) (C : Set α)
    (h : ∀ x, π x ∈ C ↔ x ∈ C) :
    numOrbits π = numOrbits (π.subtypePerm h) +
      numOrbits (π.subtypePerm (p := fun x => x ∉ C) fun x => not_congr (h x)) := by
  classical
  rw [← numOrbits_sumCongr']
  symm
  exact numOrbits_of_semiconj (Equiv.sumCompl (· ∈ C)) fun x => by rcases x with x | x <;> rfl

private theorem numOrbits_of_isEmpty [IsEmpty α] (π : Perm α) : numOrbits π = 0 := by
  unfold numOrbits
  haveI : IsEmpty (Quotient (SameCycle.setoid π)) :=
    ⟨fun q => Quotient.inductionOn q isEmptyElim⟩
  exact Nat.card_of_isEmpty

private theorem two_mul_numOrbits_of_involutive [Fintype α] {ι : Perm α}
    (h : Function.Involutive ι) (hne : ∀ x, ι x ≠ x) : 2 * numOrbits ι = Fintype.card α := by
  classical
  have := (⟨ι, 1⟩ : RotationSystem α).card_eq_two_mul_card_edges h hne
  rw [← RotationSystem.numOrbits_inv ⟨ι, 1⟩ h] at this
  exact this.symm

private theorem sameCycle_of_iterate {f : Perm α} {x y : α} (n : ℕ) (h : (⇑f)^[n] x = y) :
    f.SameCycle x y :=
  ⟨n, by rwa [zpow_natCast, Equiv.Perm.coe_pow]⟩

/-- An orbit `{a, c}` of a permutation swapping `a` and `c`. -/
private theorem eq_or_eq_of_sameCycle [Finite α] {f : Perm α} {a c : α} (ha : f a = c)
    (hc : f c = a) {w : α} (h : f.SameCycle a w) : w = a ∨ w = c := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr ha
    · exact Or.inl hc

end NumOrbits

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-! ### A graph with one boundary vertex and a lollipop -/

section OneBoundary

variable {K : PlabicData H 1} (hK : K.IsPlabicGraph)

include hK

/-- The bijection `e ↦ p`, `ē ↦ p̄`, `g ↦ g`, `ḡ ↦ ḡ` from the darts of a lollipop graph. -/
private def lollipopDartMap (p g : H) (ι : H → H) : LollipopDart → H
  | .e => p
  | .eBar => ι p
  | .g => g
  | .gBar => ι g

/-- **A graph with one boundary vertex and a lollipop is a lollipop graph**: if the plabic graph
`K` with one boundary vertex has a lollipop at the label `0` of colour `c`, then `K` is isomorphic
to `L_c`. -/
@[cluster_algebras "lem_one_boundary_lollipop"]
theorem IsPlabicGraph.isomorphic_lollipopGraph {c : Shade} {u : Finset H}
    (hu : K.IsLollipopOfColour 0 c u) : K.Isomorphic (lollipopGraph c) := by
  have hinv := hK.inv_involutive
  have h0 : finRotate 1 0 = 0 := Subsingleton.elim _ _
  obtain ⟨p, hp, hp1, hp2⟩ := hK.exists_exterior 0
  rw [h0] at hp1
  obtain ⟨hv, hrq, hrp, hrg⟩ := DiskMap.rot_cycle_of_mem_boundaryVertices hinv hK.inv_mem_bdry
    hK.boundaryVertex_card hK.exists_orbit (hK.bvertex_mem 0) hp hp1 hp hp2
    (K.leg_mem_bvertex 0) (hK.leg_notMem_bdry 0)
  set g := K.leg 0 with hg_def
  have hpB : p ∈ K.bdry := K.exterior_subset_bdry hp
  have hipB : K.inv p ∈ K.bdry := hK.inv_mem_bdry p hpB
  have hgB : g ∉ K.bdry := hK.leg_notMem_bdry 0
  -- the lollipop is `{ḡ}`
  obtain ⟨⟨⟨huV, huc⟩, d, hdu, hdv⟩, hcol⟩ := hu
  obtain ⟨huV, huB⟩ := K.mem_internalVertices.1 huV
  have hdB : d ∉ K.bdry := fun h => huB ⟨d, hdu, h⟩
  have hidB : K.inv d ∉ K.bdry := fun h => hdB (hK.inv_mem_bdry_iff.1 h)
  have hdg : d = K.inv g := by
    rw [hv] at hdv
    simp only [mem_insert, mem_singleton] at hdv
    rcases hdv with h | h | h
    · exact absurd (h ▸ hipB) hidB
    · exact absurd (h ▸ hpB) hidB
    · rw [← h, hinv]
  have hu1 : u = {d} := by
    obtain ⟨a, rfl⟩ := card_eq_one.1 huc
    rw [mem_singleton.1 hdu]
  have hrd : K.rot d = d := by
    obtain ⟨x, rfl⟩ := K.mem_vertices.1 huV
    have : K.rot d ∈ K.vertexOf x := by
      rw [← K.vertexOf_eq_of_mem hdu]
      exact K.rot_mem_vertexOf d
    rw [hu1] at this
    exact mem_singleton.1 this
  have hcd : K.colour d = c := hcol d hdu
  subst hdg
  -- distinctness
  have hpip : p ≠ K.inv p := fun h => hK.inv_ne p h.symm
  have hgp : g ≠ p := fun h => hgB (h ▸ hpB)
  have hgip : g ≠ K.inv p := fun h => hgB (h ▸ hipB)
  have higp : K.inv g ≠ p := fun h => hdB (h ▸ hpB)
  have higip : K.inv g ≠ K.inv p := fun h => hdB (h ▸ hipB)
  have higg : K.inv g ≠ g := hK.inv_ne g
  -- every dart is one of the four
  have hall : ∀ x, x = p ∨ x = K.inv p ∨ x = g ∨ x = K.inv g := by
    intro x
    induction hK.reach p x with
    | refl => exact Or.inl rfl
    | rot _ ih =>
      rcases ih with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hrp))
      · exact Or.inl hrq
      · exact Or.inr (Or.inl hrg)
      · exact Or.inr (Or.inr (Or.inr hrd))
    | inv _ ih =>
      rcases ih with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (hinv _)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (hinv _)))
  set f := lollipopDartMap p g K.inv with hf
  have hinj : Function.Injective f := by
    intro x y hxy
    cases x <;> cases y <;> simp only [hf, lollipopDartMap] at hxy <;>
      first | rfl | exact absurd hxy (by assumption) | exact absurd hxy.symm (by assumption)
  have hsurj : Function.Surjective f := by
    intro x
    rcases hall x with rfl | rfl | rfl | rfl
    exacts [⟨.e, rfl⟩, ⟨.eBar, rfl⟩, ⟨.g, rfl⟩, ⟨.gBar, rfl⟩]
  refine ⟨Iso.symm
    { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
      map_inv := ?_
      map_rot := ?_
      mem_bdry_iff := ?_
      map_colour := ?_
      map_bvertex := ?_ }⟩
  · intro x
    cases x
    · rfl
    · exact (hinv p).symm
    · rfl
    · exact (hinv g).symm
  · intro x
    have e1 : (lollipopGraph c).rot .e = .g := by cases c <;> decide
    have e2 : (lollipopGraph c).rot .eBar = .e := by cases c <;> decide
    have e3 : (lollipopGraph c).rot .g = .eBar := by cases c <;> decide
    have e4 : (lollipopGraph c).rot .gBar = .gBar := by cases c <;> decide
    cases x
    exacts [e1 ▸ hrp.symm, e2 ▸ hrq.symm, e3 ▸ hrg.symm, e4 ▸ hrd.symm]
  · intro x
    cases x
    · exact iff_of_true hpB (by cases c <;> decide)
    · exact iff_of_true hipB (by cases c <;> decide)
    · exact iff_of_false hgB (by cases c <;> decide)
    · exact iff_of_false hdB (by cases c <;> decide)
  · intro x hx
    cases x <;> first | exact hcd | exact absurd hx (by cases c <;> decide)
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [hK.filter_bvertex_notMem_bdry 0]
    have : ((lollipopGraph c).bvertex 0).filter (· ∉ (lollipopGraph c).bdry) = {.g} := by
      cases c <;> decide
    rw [this, map_singleton]
    rfl

end OneBoundary

/-! ### Comparing trip permutations through a subset of darts -/

section Compare

variable {p : H → Prop} [Fintype (Subtype p)] [DecidableEq (Subtype p)]

/-- Let `K'` be a plabic graph whose darts are some of the darts of the plabic graph `K`, with the
same legs, and `Y` a set of darts of `K'` containing the legs. If each `y ∈ Y` returns to `Y`, in
`K` and in `K'`, at the same dart, then `π_{K'} = π_K`. -/
theorem IsPlabicGraph.tripPerm_eq_of_subtype {G : PlabicData H b} {G' : PlabicData (Subtype p) b}
    (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph) (hleg : ∀ i, (G'.leg i : H) = G.leg i)
    (Y : Set H) (hYp : ∀ y ∈ Y, p y) (hY : ∀ i, G.leg i ∈ Y)
    (hT : ∀ y (hy : y ∈ Y), ∃ m n, 0 < m ∧ 0 < n ∧ G.tripMap^[m] y ∈ Y ∧
      (∀ j, 0 < j → j < m → G.tripMap^[j] y ∉ Y) ∧
      ((G'.tripMap^[n] ⟨y, hYp y hy⟩ : Subtype p) : H) = G.tripMap^[m] y ∧
      ∀ j, 0 < j → j < n → ((G'.tripMap^[j] ⟨y, hYp y hy⟩ : Subtype p) : H) ∉ Y) :
    G'.tripPerm = G.tripPerm := by
  set Y' : Set (Subtype p) := {y | (y : H) ∈ Y}
  let e : Y' ≃ Y :=
    { toFun := fun y => ⟨(y : Subtype p), y.2⟩
      invFun := fun y => ⟨⟨y, hYp y y.2⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine hG'.tripPerm_eq_of_firstReturn hG e (fun i => ⟨by
    change ((G'.leg i : Subtype p) : H) ∈ Y
    rw [hleg]; exact hY i, hleg i⟩) fun y => ?_
  obtain ⟨⟨y, hpy⟩, hy'⟩ := y
  have hy : y ∈ Y := hy'
  obtain ⟨m, n, hm, hn, hmY, hmmin, hnm, hnmin⟩ := hT y hy
  have h1 : ((firstReturn hG'.tripEquiv Y' ⟨⟨y, hpy⟩, hy'⟩ : Subtype p) : H) =
      G.tripMap^[m] y := by
    have hmem : (hG'.tripEquiv ^ n) ⟨y, hpy⟩ ∈ Y' := by
      change (((hG'.tripEquiv ^ n) ⟨y, hpy⟩ : Subtype p) : H) ∈ Y
      rw [hG'.tripEquiv_pow_apply, hnm]
      exact hmY
    have hmin : ∀ j, 0 < j → j < n → (hG'.tripEquiv ^ j) ⟨y, hpy⟩ ∉ Y' := by
      intro j hj hjn
      change (((hG'.tripEquiv ^ j) ⟨y, hpy⟩ : Subtype p) : H) ∉ Y
      rw [hG'.tripEquiv_pow_apply]
      exact hnmin j hj hjn
    rw [coe_firstReturn_of_pow hn hmem hmin, hG'.tripEquiv_pow_apply]
    exact hnm
  have h2 : (firstReturn hG.tripEquiv Y ⟨y, hy⟩ : H) = G.tripMap^[m] y := by
    have hmem : (hG.tripEquiv ^ m) y ∈ Y := by
      rwa [hG.tripEquiv_pow_apply]
    have hmin : ∀ j, 0 < j → j < m → (hG.tripEquiv ^ j) y ∉ Y := by
      intro j hj hjm
      rw [hG.tripEquiv_pow_apply]
      exact hmmin j hj hjm
    rw [coe_firstReturn_of_pow (y := ⟨y, hy⟩) hm hmem hmin, hG.tripEquiv_pow_apply]
  exact Subtype.ext (h1.trans h2.symm)

end Compare

/-! ### Pruning stray leaves -/

section PruneLeaves

variable {G : PlabicData H b} {ℓ : H} (hG : G.IsPlabicGraph)
  (hu : G.IsInternalLeaf (G.vertexOf ℓ)) (hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices)

include hG hu hv

omit [Fintype H] [DecidableEq H] hG hu hv in
private theorem mem_compl_pair_iff' {x : H} :
    x ∈ (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) ↔ x ≠ ℓ ∧ x ≠ G.inv ℓ := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

private theorem leafDeletion_colour_eq (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    (G.leafDeletion hG hu hv).colour x = G.colour x := by
  rw [leafDeletion_colour]
  split_ifs with h
  · exact (hG.colour_eq_of_mem_vertexOf (G.vertexOf_mem_internalVertices.1 hv) h).symm
  · rfl

/-- The inverse rotation of the deletion agrees with `σ⁻¹`, except that it sends `σ(ℓ̄)` to
`σ⁻¹(ℓ̄)`. -/
private theorem coe_leafDeletion_rot_symm (x : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ((G.leafDeletion hG hu hv).rot.symm x : H) =
      if G.rot.symm x = G.inv ℓ then G.rot.symm (G.inv ℓ) else G.rot.symm x := by
  set w := (G.leafDeletion hG hu hv).rot.symm x with hw_def
  have hx : ((G.leafDeletion hG hu hv).rot w : H) = x := by simp [w]
  rw [coe_leafDeletion_rot] at hx
  have hw := (mem_compl_pair_iff' (G := G)).1 w.2
  split_ifs at hx with h
  · rw [if_pos (by rw [← hx, Equiv.symm_apply_apply])]
    exact ((Equiv.symm_apply_eq _).2 h.symm).symm
  · rw [if_neg (by rw [← hx, Equiv.symm_apply_apply]; exact hw.2), ← hx,
      Equiv.symm_apply_apply]

/-- The turn of the deletion agrees with the turn of `G`, except that a turn onto `ℓ̄` is
continued by the turn at `ℓ̄`. -/
private theorem coe_turn_leafDeletion (z : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ((G.leafDeletion hG hu hv).turn z : H) =
      if G.turn z = G.inv ℓ then G.turn (G.inv ℓ) else G.turn z := by
  have hz := (mem_compl_pair_iff' (G := G)).1 z.2
  have hvℓ : ¬G.IsBoundaryVertex (G.vertexOf (G.inv ℓ)) := G.vertexOf_mem_internalVertices.1 hv
  by_cases hb : G.IsBoundaryVertex (G.vertexOf z)
  · rw [turn_of_isBoundaryVertex ((isBoundaryVertex_vertexOf_leafDeletion_iff hG hu hv z).2 hb),
      turn_of_isBoundaryVertex hb, if_neg hz.2]
  · have hb' := mt (isBoundaryVertex_vertexOf_leafDeletion_iff hG hu hv z).1 hb
    cases hc : G.colour z
    · rw [turn_of_white hb' (by rw [leafDeletion_colour_eq, hc]), turn_of_white hb hc,
        coe_leafDeletion_rot_symm]
      split_ifs with h
      · have hc' : G.colour (G.inv ℓ) = .white := by
          rw [← h, hG.colour_eq_of_mem_vertexOf hb (G.rot_symm_mem_vertexOf _), hc]
        rw [turn_of_white hvℓ hc']
      · rfl
    · rw [turn_of_black hb' (by rw [leafDeletion_colour_eq, hc]), turn_of_black hb hc,
        coe_leafDeletion_rot]
      split_ifs with h
      · have hc' : G.colour (G.inv ℓ) = .black := by
          rw [← h, hG.colour_eq_of_mem_vertexOf hb (G.rot_mem_vertexOf _), hc]
        rw [turn_of_black hvℓ hc']
      · rfl

/-- The trip map of the deletion agrees with that of `G`, except that a trip running into `ℓ̄`
continues with `T(ℓ)`. -/
private theorem coe_tripMap_leafDeletion (y : (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H)) :
    ((G.leafDeletion hG hu hv).tripMap y : H) =
      if G.tripMap y = G.inv ℓ then G.tripMap ℓ else G.tripMap y :=
  coe_turn_leafDeletion hG hu hv _

/-- Deleting an internal leaf keeps the trip permutation. -/
theorem tripPerm_leafDeletion : (G.leafDeletion hG hu hv).tripPerm = G.tripPerm := by
  have hinv := hG.inv_involutive
  have hvℓ : ¬G.IsBoundaryVertex (G.vertexOf (G.inv ℓ)) := G.vertexOf_mem_internalVertices.1 hv
  have hℓ : ∀ x, x ∈ G.vertexOf ℓ ↔ x = ℓ := fun x => mem_vertexOf_iff_of_isInternalLeaf hu
  -- `T(ℓ̄) = ℓ`
  have hTℓ' : G.tripMap (G.inv ℓ) = ℓ := by
    rw [tripMap_apply, hinv]
    exact (hℓ _).1 (turn_mem_vertexOf ℓ)
  set Y : Set H := {x | x ≠ ℓ ∧ x ≠ G.inv ℓ ∧ x ∉ G.bdry} with hY_def
  -- `T(ℓ) = turn(ℓ̄)` lies in `Y`
  have hTℓ : G.tripMap ℓ ∈ Y := by
    have hmem : G.tripMap ℓ ∈ G.vertexOf (G.inv ℓ) := turn_mem_vertexOf _
    refine ⟨fun h => ?_, fun h => ?_, notMem_bdry_of_mem_vertexOf hvℓ hmem⟩
    · rw [h] at hmem
      have := G.vertexOf_eq_of_mem hmem
      exact hG.inv_ne ℓ ((hℓ _).1 (this ▸ G.self_mem_vertexOf _))
    · have hne := rot_inv_ne_of_isInternalLeaf hG hu hv
      rw [tripMap_apply] at h
      cases hc : G.colour (G.inv ℓ)
      · rw [turn_of_white hvℓ hc, Equiv.symm_apply_eq] at h
        exact hne h.symm
      · rw [turn_of_black hvℓ hc] at h
        exact hne h
  refine hG.tripPerm_eq_of_subtype (isPlabicGraph_leafDeletion hG hu hv) (fun i => rfl) Y
    (fun y hy => (mem_compl_pair_iff' (G := G)).2 ⟨hy.1, hy.2.1⟩)
    (fun i => ⟨((mem_compl_pair_iff' (G := G)).1 (leg_mem_compl_pair hG hu hv i)).1,
      ((mem_compl_pair_iff' (G := G)).1 (leg_mem_compl_pair hG hu hv i)).2,
      hG.leg_notMem_bdry i⟩) fun y hy => ?_
  by_cases h : G.tripMap y = G.inv ℓ
  · refine ⟨3, 1, by norm_num, one_pos, ?_, fun j hj hj3 => ?_, ?_, fun j hj hj1 => by omega⟩
    · change G.tripMap (G.tripMap (G.tripMap y)) ∈ Y
      rw [h, hTℓ']
      exact hTℓ
    · interval_cases j
      · change G.tripMap y ∉ Y
        rw [h]
        exact fun hh => hh.2.1 rfl
      · change G.tripMap (G.tripMap y) ∉ Y
        rw [h, hTℓ']
        exact fun hh => hh.1 rfl
    · change ((G.leafDeletion hG hu hv).tripMap _ : H) = G.tripMap (G.tripMap (G.tripMap y))
      rw [coe_tripMap_leafDeletion, if_pos h, h, hTℓ']
  · refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_, fun j hj hj1 => by omega⟩
    · refine ⟨fun h' => ?_, h, (not_congr (tripMap_mem_bdry_iff hG y)).2 hy.2.2⟩
      have hmem : ℓ ∈ G.vertexOf (G.inv y) := h' ▸ turn_mem_vertexOf (G.inv y)
      have h1 : G.inv y = ℓ := (hℓ _).1 (G.vertexOf_eq_of_mem hmem ▸ G.self_mem_vertexOf _)
      exact hy.2.1 (by rw [← h1, hinv])
    · change ((G.leafDeletion hG hu hv).tripMap _ : H) = G.tripMap y
      rw [coe_tripMap_leafDeletion, if_neg h]

/-- Deleting an internal leaf keeps the number of faces. -/
theorem card_faces_leafDeletion : (G.leafDeletion hG hu hv).faces.card = G.faces.card := by
  have hK := isPlabicGraph_leafDeletion hG hu hv
  rw [DiskMap.faces, DiskMap.faces, card_erase_of_mem hK.exterior_mem_faceOrbits,
    card_erase_of_mem hG.exterior_mem_faceOrbits, card_faceOrbits_leafDeletion]

end PruneLeaves

/-- **Stray leaves can be pruned**: for every plabic graph `K` with `b` boundary vertices there
is a nearly leafless plabic graph `K'` with `b` boundary vertices, `π_{K'} = π_K`, and as many
faces as `K`. -/
@[cluster_algebras "lem_prune_leaves"]
theorem IsPlabicGraph.exists_isNearlyLeafless {H : Type} [Fintype H] [DecidableEq H]
    {K : PlabicData H b} (hK : K.IsPlabicGraph) :
    ∃ K' : PlabicGraph b, K'.data.IsNearlyLeafless ∧ K'.data.tripPerm = K.tripPerm ∧
      K'.data.faces.card = K.faces.card := by
  suffices key : ∀ n, ∀ (H : Type) [Fintype H] [DecidableEq H] (K : PlabicData H b),
      K.IsPlabicGraph → Fintype.card H = n → ∃ K' : PlabicGraph b, K'.data.IsNearlyLeafless ∧
        K'.data.tripPerm = K.tripPerm ∧ K'.data.faces.card = K.faces.card from
    key _ H K hK rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ G hG hn
  by_cases hN : G.IsNearlyLeafless
  · exact ⟨⟨H, G, hG⟩, hN, rfl, rfl⟩
  obtain ⟨v, hvl, hvn⟩ : ∃ v, G.IsInternalLeaf v ∧ ¬∃ i, G.IsLollipop i v := by
    by_contra hcon
    exact hN fun v hv => by_contra fun h => hcon ⟨v, hv, h⟩
  obtain ⟨ℓ, rfl⟩ := G.mem_vertices.1 (G.mem_internalVertices.1 hvl.1).1
  have hv : G.vertexOf (G.inv ℓ) ∈ G.internalVertices := by
    by_contra hb
    rw [G.vertexOf_mem_internalVertices, not_not] at hb
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hb)
    exact hvn ⟨i, hvl, ℓ, G.self_mem_vertexOf ℓ, by rw [hi]; exact G.self_mem_vertexOf _⟩
  have hcard : Fintype.card (({ℓ, G.inv ℓ} : Set H)ᶜ : Set H) < n :=
    hn ▸ Fintype.card_subtype_lt (x := ℓ) (by simp)
  obtain ⟨K', h1, h2, h3⟩ := ih _ hcard _ _ (isPlabicGraph_leafDeletion hG hvl hv) rfl
  exact ⟨K', h1, h2.trans (tripPerm_leafDeletion hG hvl hv),
    h3.trans (card_faces_leafDeletion hG hvl hv)⟩

/-! ### Excision of edges at internal vertices

Throughout, `X = 𝓔.biUnion id` is the set of excised darts and `σ_X = G.excisionRot 𝓔`. -/

section Excision

variable {G : PlabicData H b} {𝓔 : Finset (Finset H)}

/-- Every power of `σ_X` maps a dart into `X` iff the dart lies in `X`. -/
theorem excisionRot_pow_mem_iff {z : H} (n : ℕ) :
    ((G.excisionRot 𝓔) ^ n) z ∈ 𝓔.biUnion id ↔ z ∈ 𝓔.biUnion id := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, excisionRot_mem_iff, ih]

/-- On a dart outside `X`, the powers of `σ_X` are the powers of the first-return map of the
rotation to the complement of `X`. -/
theorem excisionRot_pow_apply_of_notMem {z : H} (hz : z ∉ 𝓔.biUnion id) (n : ℕ) :
    ((G.excisionRot 𝓔) ^ n) z =
      (((firstReturnPerm G.rot ((↑(𝓔.biUnion id) : Set H)ᶜ)) ^ n) ⟨z, by simpa using hz⟩ : H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply, excisionRot_apply_of_notMem]
    · rfl
    · simpa using ((firstReturnPerm G.rot ((↑(𝓔.biUnion id) : Set H)ᶜ) ^ n)
        ⟨z, by simpa using hz⟩).2

/-- Two darts outside `X` lie in one orbit of `σ_X` iff they lie at one vertex. -/
theorem sameCycle_excisionRot_iff {z w : H} (hz : z ∉ 𝓔.biUnion id) (hw : w ∉ 𝓔.biUnion id) :
    (G.excisionRot 𝓔).SameCycle z w ↔ G.rot.SameCycle z w := by
  have hzS : z ∈ ((↑(𝓔.biUnion id) : Set H)ᶜ) := by simpa using hz
  have hwS : w ∈ ((↑(𝓔.biUnion id) : Set H)ᶜ) := by simpa using hw
  rw [← sameCycle_firstReturnPerm_iff G.rot _ (y := ⟨z, hzS⟩) (y' := ⟨w, hwS⟩)]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rw [excisionRot_pow_apply_of_notMem hz] at hn
    exact ⟨n, by simpa using Subtype.ext hn⟩
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, excisionRot_pow_apply_of_notMem hz, hn]⟩

/-- The excision step relation is symmetric when `G.inv` is involutive. -/
theorem ExcisionStep.symm (hinv : Function.Involutive G.inv) {z z' : H}
    (h : G.ExcisionStep 𝓔 z z') : G.ExcisionStep 𝓔 z' z := by
  obtain ⟨hz, hz', h | h | h⟩ := h
  · exact ⟨hz', hz, Or.inr (Or.inl h)⟩
  · exact ⟨hz', hz, Or.inl h⟩
  · exact ⟨hz', hz, Or.inr (Or.inr (by rw [h, hinv]))⟩

/-- The reflexive-transitive closure of the excision step relation is symmetric. -/
theorem reflTransGen_excisionStep_symm (hinv : Function.Involutive G.inv) {z z' : H}
    (h : Relation.ReflTransGen (G.ExcisionStep 𝓔) z z') :
    Relation.ReflTransGen (G.ExcisionStep 𝓔) z' z := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact (Relation.ReflTransGen.single (hst.symm hinv)).trans ih

/-- Darts outside `X` at one vertex are joined by steps of the excision. -/
theorem reflTransGen_excisionStep_of_sameCycle {z w : H} (hz : z ∉ 𝓔.biUnion id)
    (hw : w ∉ 𝓔.biUnion id) (h : G.rot.SameCycle z w) :
    Relation.ReflTransGen (G.ExcisionStep 𝓔) z w := by
  obtain ⟨n, rfl⟩ := ((sameCycle_excisionRot_iff hz hw).2 h).exists_nat_pow_eq
  clear hw h
  induction n with
  | zero => exact .refl
  | succ n ih =>
    refine ih.tail ⟨(excisionRot_pow_mem_iff n).not.2 hz, (excisionRot_pow_mem_iff _).not.2 hz,
      Or.inl ?_⟩
    rw [pow_succ', Perm.mul_apply]

private theorem faceOf_eq_exterior (hG : G.IsPlabicGraph) {e : H} (he : e ∈ G.exterior) :
    G.faceOf e = G.exterior := by
  obtain ⟨a, ha⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
  rw [← ha] at he ⊢
  exact G.faceOf_eq_of_mem he

private theorem facePerm_mem_exterior (hG : G.IsPlabicGraph) {e : H} (he : e ∈ G.exterior) :
    G.facePerm e ∈ G.exterior := by
  rw [← faceOf_eq_exterior hG he]
  exact G.facePerm_mem_faceOf e

/-- A dart joined by excision steps to a surviving dart survives the excision. -/
theorem mem_excisionDarts_of_reflTransGen {z w : H} (hz : z ∈ G.excisionDarts 𝓔)
    (h : Relation.ReflTransGen (G.ExcisionStep 𝓔) z w) : w ∈ G.excisionDarts 𝓔 := by
  induction h with
  | refl => exact hz
  | tail _ hst ih => exact mem_excisionDarts_of_step ih hst

variable {hG : G.IsPlabicGraph} {h𝓔 : 𝓔 ⊆ G.edges} {h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry}

/-- The inverse rotation of the excision is `σ_X⁻¹`. -/
theorem coe_edgeExcision_rot_symm (z : G.excisionDarts 𝓔) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).rot.symm z : H) = (G.excisionRot 𝓔).symm z := by
  refine (Equiv.eq_symm_apply _).2 ?_
  rw [← coe_edgeExcision_rot (hG := hG) (h𝓔 := h𝓔) (h𝓔B := h𝓔B), Equiv.apply_symm_apply]

/-- A dart of the excision lies at the vertex of another iff it does in `G`. -/
theorem mem_vertexOf_edgeExcision_iff {z w : G.excisionDarts 𝓔} :
    w ∈ (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertexOf z ↔ (w : H) ∈ G.vertexOf z := by
  rw [RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf]
  change ((G.excisionRot 𝓔).subtypePerm fun _ => excisionRot_mem_excisionDarts_iff).SameCycle z w
    ↔ _
  rw [sameCycle_subtypePerm]
  exact sameCycle_excisionRot_iff (notMem_of_mem_excisionDarts z.2)
    (notMem_of_mem_excisionDarts w.2)

/-- A vertex of the excision is a boundary vertex iff the corresponding vertex of `G` is. -/
theorem isBoundaryVertex_vertexOf_edgeExcision_iff (z : G.excisionDarts 𝓔) :
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).IsBoundaryVertex
        ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertexOf z) ↔
      G.IsBoundaryVertex (G.vertexOf z) := by
  constructor
  · rintro ⟨w, hw, hwB⟩
    exact ⟨w, mem_vertexOf_edgeExcision_iff.1 hw, mem_edgeExcision_bdry.1 hwB⟩
  · rintro ⟨w, hw, hwB⟩
    exact ⟨⟨w, bdry_subset_excisionDarts h𝓔B hwB⟩, mem_vertexOf_edgeExcision_iff.2 hw,
      mem_edgeExcision_bdry.2 hwB⟩

/-- The turn of the excision at a boundary vertex. -/
theorem coe_edgeExcision_turn_of_isBoundaryVertex {z : G.excisionDarts 𝓔}
    (hb : G.IsBoundaryVertex (G.vertexOf z)) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).turn z : H) = z := by
  rw [turn_of_isBoundaryVertex ((isBoundaryVertex_vertexOf_edgeExcision_iff z).2 hb)]

/-- The turn of the excision at an internal black vertex is `σ_X`. -/
theorem coe_edgeExcision_turn_of_black {z : G.excisionDarts 𝓔}
    (hb : ¬G.IsBoundaryVertex (G.vertexOf z)) (hc : G.colour z = .black) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).turn z : H) = G.excisionRot 𝓔 z := by
  rw [turn_of_black (mt (isBoundaryVertex_vertexOf_edgeExcision_iff z).1 hb)
    (by rw [edgeExcision_colour, hc]), coe_edgeExcision_rot]

/-- The turn of the excision at an internal white vertex is `σ_X⁻¹`. -/
theorem coe_edgeExcision_turn_of_white {z : G.excisionDarts 𝓔}
    (hb : ¬G.IsBoundaryVertex (G.vertexOf z)) (hc : G.colour z = .white) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).turn z : H) = (G.excisionRot 𝓔).symm z := by
  rw [turn_of_white (mt (isBoundaryVertex_vertexOf_edgeExcision_iff z).1 hb)
    (by rw [edgeExcision_colour, hc]), coe_edgeExcision_rot_symm]

/-- The trip map of the excision when `v(w̄)` is a boundary vertex. -/
theorem coe_edgeExcision_tripMap_of_isBoundaryVertex {w : G.excisionDarts 𝓔}
    (hb : G.IsBoundaryVertex (G.vertexOf (G.inv w))) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap w : H) = G.inv w :=
  coe_edgeExcision_turn_of_isBoundaryVertex (z := (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).inv w) hb

/-- The trip map of the excision when `v(w̄)` is internal and black. -/
theorem coe_edgeExcision_tripMap_of_black {w : G.excisionDarts 𝓔}
    (hb : ¬G.IsBoundaryVertex (G.vertexOf (G.inv w))) (hc : G.colour (G.inv w) = .black) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap w : H) = G.excisionRot 𝓔 (G.inv w) :=
  coe_edgeExcision_turn_of_black (z := (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).inv w) hb hc

/-- The trip map of the excision when `v(w̄)` is internal and white. -/
theorem coe_edgeExcision_tripMap_of_white {w : G.excisionDarts 𝓔}
    (hb : ¬G.IsBoundaryVertex (G.vertexOf (G.inv w))) (hc : G.colour (G.inv w) = .white) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap w : H) = (G.excisionRot 𝓔).symm (G.inv w) :=
  coe_edgeExcision_turn_of_white (z := (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).inv w) hb hc

section Internal

/-! In the rest of this section every dart of `X` lies at an internal vertex. -/

variable (hX : ∀ x ∈ 𝓔.biUnion id, ¬G.IsBoundaryVertex (G.vertexOf x))

include hX

/-- A dart at a boundary vertex does not lie in `X`. -/
theorem notMem_biUnion_of_isBoundaryVertex {z : H} (hz : G.IsBoundaryVertex (G.vertexOf z)) :
    z ∉ 𝓔.biUnion id := fun h => hX z h hz

/-- At a boundary vertex, `σ_X` agrees with the rotation of `G`. -/
theorem excisionRot_apply_of_isBoundaryVertex {z : H} (hz : G.IsBoundaryVertex (G.vertexOf z)) :
    G.excisionRot 𝓔 z = G.rot z :=
  excisionRot_apply_of_rot_notMem (notMem_biUnion_of_isBoundaryVertex hX hz)
    (notMem_biUnion_of_isBoundaryVertex hX (by rwa [G.vertexOf_rot]))

/-- Every dart at a boundary vertex survives the excision. -/
theorem mem_excisionDarts_of_isBoundaryVertex {z : H} (hz : G.IsBoundaryVertex (G.vertexOf z)) :
    z ∈ G.excisionDarts 𝓔 := by
  have hzX := notMem_biUnion_of_isBoundaryVertex hX hz
  obtain ⟨w, hw, hwB⟩ := hz
  have hwX := notMem_biUnion_of_isBoundaryVertex hX (G.isBoundaryVertex_vertexOf_of_mem hwB)
  exact mem_excisionDarts.2 ⟨hzX, w, hwB, hwX,
    reflTransGen_excisionStep_of_sameCycle hwX hzX (G.mem_vertexOf.1 hw).symm⟩

/-- At a boundary vertex the excision does not change the vertex. -/
theorem map_vertexOf_edgeExcision_of_isBoundaryVertex (z : G.excisionDarts 𝓔)
    (hz : G.IsBoundaryVertex (G.vertexOf z)) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertexOf z).map (Function.Embedding.subtype _) =
      G.vertexOf z := by
  ext w
  simp only [mem_map, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact mem_vertexOf_edgeExcision_iff.1 ha
  · intro hw
    have hw' : G.IsBoundaryVertex (G.vertexOf w) := by rwa [G.vertexOf_eq_of_mem hw]
    exact ⟨⟨w, mem_excisionDarts_of_isBoundaryVertex hX hw'⟩,
      mem_vertexOf_edgeExcision_iff.2 hw, rfl⟩

/-- The legs of the excision are the legs of `G`. -/
theorem coe_edgeExcision_leg (i : Fin b) :
    ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).leg i : H) = G.leg i :=
  coe_edgeExcision_leg_of_mem (mem_excisionDarts_of_isBoundaryVertex hX
    (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)))

/-- Along the exterior, the powers of the face permutation of the excision agree with those of
`G`, and stay in the exterior. -/
theorem coe_edgeExcision_facePerm_pow_of_mem_exterior {w : G.excisionDarts 𝓔}
    (hw : (w : H) ∈ G.exterior) (n : ℕ) :
    (((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).facePerm ^ n) w : H) = (G.facePerm ^ n) w ∧
      (G.facePerm ^ n) (w : H) ∈ G.exterior := by
  induction n with
  | zero => exact ⟨rfl, hw⟩
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply]
    obtain ⟨h1, h2⟩ := ih
    have hiB : G.inv ((G.facePerm ^ n) w) ∈ G.bdry :=
      hG.inv_mem_bdry _ (G.exterior_subset_bdry h2)
    refine ⟨?_, facePerm_mem_exterior hG h2⟩
    rw [RotationSystem.facePerm_apply, coe_edgeExcision_rot, coe_edgeExcision_inv, h1,
      excisionRot_apply_of_isBoundaryVertex hX (G.isBoundaryVertex_vertexOf_of_mem hiB),
      RotationSystem.facePerm_apply]

/-- The face orbit of the excision through a dart of the exterior is the exterior. -/
theorem mem_edgeExcision_faceOf_iff_of_mem_exterior {w : G.excisionDarts 𝓔}
    (hw : (w : H) ∈ G.exterior) (y : G.excisionDarts 𝓔) :
    y ∈ (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOf w ↔ (y : H) ∈ G.exterior := by
  have key := fun n => coe_edgeExcision_facePerm_pow_of_mem_exterior hX (hG := hG) (h𝓔 := h𝓔)
    (h𝓔B := h𝓔B) hw n
  rw [RotationSystem.mem_faceOf]
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [(key n).1]
    exact (key n).2
  · intro h
    rw [← faceOf_eq_exterior hG hw, RotationSystem.mem_faceOf] at h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Subtype.ext ((key n).1.trans hn)

/-- If every dart of `X` lies at an internal vertex, the excision is a connected rotation
system. -/
theorem isConnected_edgeExcision : (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).IsConnected := by
  set K := G.edgeExcision hG 𝓔 h𝓔 h𝓔B with hK
  have hinv := hG.inv_involutive
  have hstep : ∀ z z' : G.excisionDarts 𝓔, G.ExcisionStep 𝓔 z z' → K.Reach z z' := by
    rintro z z' ⟨-, -, h | h | h⟩
    · obtain rfl : z' = K.rot z := Subtype.ext h
      exact (RotationSystem.Reach.refl z).rot
    · obtain rfl : z = K.rot z' := Subtype.ext h
      exact (RotationSystem.Reach.refl z').rot.symm
    · obtain rfl : z' = K.inv z := Subtype.ext h
      exact (RotationSystem.Reach.refl z).inv
  have hrtg : ∀ (z : H) (hz : z ∈ G.excisionDarts 𝓔) (w : H),
      Relation.ReflTransGen (G.ExcisionStep 𝓔) z w →
        ∀ hw : w ∈ G.excisionDarts 𝓔, K.Reach ⟨z, hz⟩ ⟨w, hw⟩ := by
    intro z hz w h
    induction h with
    | refl => exact fun _ => .refl _
    | @tail c d _ hst ih =>
      intro hd
      have hc : c ∈ G.excisionDarts 𝓔 := mem_excisionDarts_of_step hd (hst.symm hinv)
      exact (ih hc).trans (hstep ⟨c, hc⟩ ⟨d, hd⟩ hst)
  obtain ⟨a, ha⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
  have haE : a ∈ G.exterior := ha ▸ G.self_mem_faceOf a
  have haH : a ∈ G.excisionDarts 𝓔 :=
    bdry_subset_excisionDarts h𝓔B (G.exterior_subset_bdry haE)
  have hext : ∀ e (he : e ∈ G.exterior), K.Reach ⟨a, haH⟩
      ⟨e, bdry_subset_excisionDarts h𝓔B (G.exterior_subset_bdry he)⟩ := by
    intro e he
    have hface := (mem_edgeExcision_faceOf_iff_of_mem_exterior hX (hG := hG) (h𝓔 := h𝓔)
      (h𝓔B := h𝓔B) (w := ⟨a, haH⟩) haE
      ⟨e, bdry_subset_excisionDarts h𝓔B (G.exterior_subset_bdry he)⟩).2 he
    rw [RotationSystem.mem_faceOf] at hface
    obtain ⟨n, hn⟩ := hface.exists_nat_pow_eq
    rw [← hn]
    exact K.reach_pow_apply (fun x => (RotationSystem.Reach.refl x).inv.rot) n _
  have hB : ∀ x (hx : x ∈ G.bdry), K.Reach ⟨a, haH⟩ ⟨x, bdry_subset_excisionDarts h𝓔B hx⟩ := by
    intro x hx
    rw [← hG.exterior_union_map_inv, mem_union] at hx
    rcases hx with hx | hx
    · exact hext x hx
    · obtain ⟨e, he, rfl⟩ := mem_map.1 hx
      exact (hext e he).inv
  have hall : ∀ z : G.excisionDarts 𝓔, K.Reach ⟨a, haH⟩ z := by
    rintro ⟨z, hz⟩
    obtain ⟨-, x, hxB, -, hxz⟩ := mem_excisionDarts.1 hz
    exact (hB x hxB).trans (hrtg x _ z hxz hz)
  refine RotationSystem.IsConnected.of_reach ⟨⟨a, haH⟩⟩ (fun z => Subtype.ext (hinv z))
    (fun z h => hG.inv_ne z (congrArg Subtype.val h)) fun z w => (hall z).symm.trans (hall w)

/-- Every boundary vertex of the excision has three darts, two of them on the boundary. -/
theorem boundaryVertex_card_edgeExcision :
    ∀ v ∈ (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).boundaryVertices,
      v.card = 3 ∧ (v.filter (· ∈ (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).bdry)).card = 2 := by
  set K := G.edgeExcision hG 𝓔 h𝓔 h𝓔B
  intro v hv'
  obtain ⟨hvV, hvB⟩ := K.mem_boundaryVertices.1 hv'
  obtain ⟨x, rfl⟩ := K.mem_vertices.1 hvV
  have hb := (isBoundaryVertex_vertexOf_edgeExcision_iff x).1 hvB
  have hm := map_vertexOf_edgeExcision_of_isBoundaryVertex hX (hG := hG) (h𝓔 := h𝓔)
    (h𝓔B := h𝓔B) x hb
  obtain ⟨h3, h2⟩ := hG.boundaryVertex_card _ (G.vertexOf_mem_boundaryVertices.2 hb)
  constructor
  · rw [← card_map (Function.Embedding.subtype _), hm]
    exact h3
  · rw [← card_map (Function.Embedding.subtype _), ← h2, ← hm, filter_map]
    congr 2
    exact filter_congr fun y _ => mem_edgeExcision_bdry

/-- The exterior of the excision is a face orbit forming half of its boundary. -/
theorem exists_orbit_edgeExcision :
    ∃ f ∈ (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOrbits, f ⊆ (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).bdry ∧
      f ∪ f.map (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).inv.toEmbedding =
        (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).bdry ∧
      Disjoint f (f.map (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).inv.toEmbedding) := by
  set K := G.edgeExcision hG 𝓔 h𝓔 h𝓔B
  have hBH : ∀ x ∈ G.bdry, x ∈ G.excisionDarts 𝓔 := fun x hx => bdry_subset_excisionDarts h𝓔B hx
  obtain ⟨w, hw⟩ := G.mem_faceOrbits.1 hG.exterior_mem_faceOrbits
  have hwE : w ∈ G.exterior := hw ▸ G.self_mem_faceOf w
  have hwH : w ∈ G.excisionDarts 𝓔 := hBH w (G.exterior_subset_bdry hwE)
  have hext := mem_edgeExcision_faceOf_iff_of_mem_exterior hX (hG := hG) (h𝓔 := h𝓔)
    (h𝓔B := h𝓔B) (w := ⟨w, hwH⟩) hwE
  refine ⟨K.faceOf ⟨w, hwH⟩, RotationSystem.faceOf_mem_faceOrbits _ _, fun y hy => ?_, ?_, ?_⟩
  · exact mem_edgeExcision_bdry.2 (G.exterior_subset_bdry ((hext y).1 hy))
  · ext y
    rw [mem_union, hext, mem_edgeExcision_bdry, ← hG.exterior_union_map_inv, mem_union]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · simp only [mem_map, Equiv.coe_toEmbedding]
      rintro ⟨c, hc, rfl⟩
      exact ⟨c, (hext c).1 hc, rfl⟩
    · simp only [mem_map, Equiv.coe_toEmbedding]
      rintro ⟨c, hc, hcy⟩
      exact ⟨⟨c, hBH c (G.exterior_subset_bdry hc)⟩, (hext _).2 hc, Subtype.ext hcy⟩
  · rw [disjoint_left]
    intro y hy hy'
    refine disjoint_left.1 hG.disjoint_exterior_map_inv ((hext y).1 hy) ?_
    obtain ⟨c, hc, rfl⟩ := mem_map.1 hy'
    exact mem_map.2 ⟨c, (hext c).1 hc, rfl⟩

/-- If every dart of `X` lies at an internal vertex and the excision satisfies Euler's relation,
then the excision is a plabic graph. -/
theorem isPlabicGraph_edgeExcision
    (heuler : ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertices.card : ℤ) -
      (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).edges.card +
        (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOrbits.card = 2) :
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).IsPlabicGraph := by
  set K := G.edgeExcision hG 𝓔 h𝓔 h𝓔B with hK
  have hleg : ∀ i, K.leg i = ⟨G.leg i, mem_excisionDarts_of_isBoundaryVertex hX
      (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))⟩ :=
    fun i => Subtype.ext (coe_edgeExcision_leg hX i)
  have hbv : ∀ i, (K.bvertex i).map (Function.Embedding.subtype _) = G.bvertex i := by
    intro i
    rw [PlabicData.bvertex, hleg i]
    exact map_vertexOf_edgeExcision_of_isBoundaryVertex hX _
      (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))
  have hBH : ∀ x ∈ G.bdry, x ∈ G.excisionDarts 𝓔 := fun x hx => bdry_subset_excisionDarts h𝓔B hx
  exact
  { toIsConnected := isConnected_edgeExcision hX
    inv_mem_bdry := fun x hx => by
      rw [mem_edgeExcision_bdry] at hx ⊢
      exact hG.inv_mem_bdry _ hx
    euler := heuler
    boundaryVertex_card := boundaryVertex_card_edgeExcision hX
    exists_orbit := exists_orbit_edgeExcision hX
    one_le := hG.one_le
    colour_rot := fun x hx => by
      rw [isBoundaryVertex_vertexOf_edgeExcision_iff] at hx
      rw [edgeExcision_colour, edgeExcision_colour]
      have hrx : ((K.rot x : G.excisionDarts 𝓔) : H) ∈ G.vertexOf x :=
        mem_vertexOf_edgeExcision_iff.1 (RotationSystem.rot_mem_vertexOf _ x)
      exact hG.colour_eq_of_mem_vertexOf hx hrx
    leg_notMem_bdry := fun i => by
      rw [mem_edgeExcision_bdry, coe_edgeExcision_leg hX]
      exact hG.leg_notMem_bdry i
    bvertex_mem := fun i => K.vertexOf_mem_boundaryVertices.2
      ((isBoundaryVertex_vertexOf_edgeExcision_iff _).2
        (by rw [coe_edgeExcision_leg hX]
            exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)))
    bvertex_injective := fun i j h => hG.bvertex_injective (by rw [← hbv i, h, hbv])
    exists_bvertex_eq := fun v hv' => by
      obtain ⟨hvV, hvB⟩ := K.mem_boundaryVertices.1 hv'
      obtain ⟨x, rfl⟩ := K.mem_vertices.1 hvV
      have hb := (isBoundaryVertex_vertexOf_edgeExcision_iff x).1 hvB
      obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hb)
      exact ⟨i, map_injective (Function.Embedding.subtype _) (by
        rw [hbv, map_vertexOf_edgeExcision_of_isBoundaryVertex hX _ hb, hi])⟩
    exists_exterior := fun i => by
      obtain ⟨d, hd, h1, h2⟩ := hG.exists_exterior i
      have hdB := G.exterior_subset_bdry hd
      refine ⟨⟨d, hBH d hdB⟩, ?_, ?_, ?_⟩
      · rw [DiskMap.mem_exterior, mem_edgeExcision_bdry, mem_edgeExcision_bdry,
          coe_edgeExcision_rot,
          excisionRot_apply_of_isBoundaryVertex hX (G.isBoundaryVertex_vertexOf_of_mem hdB)]
        exact G.mem_exterior.1 hd
      · rw [← mem_map' (Function.Embedding.subtype _), hbv]
        exact h1
      · rw [← mem_map' (Function.Embedding.subtype _), hbv]
        exact h2 }

end Internal

end Excision

/-! ### Counting the vertices, edges and faces of an excision -/

section Counting

variable {G : PlabicData H b} {𝓔 : Finset (Finset H)}

/-- The darts `H \ X` outside the excised edges. -/
private abbrev exS (𝓔 : Finset (Finset H)) : Set H := ((↑(𝓔.biUnion id) : Set H)ᶜ)

private theorem inv_mem_exS_iff (hG : G.IsPlabicGraph) (h𝓔 : 𝓔 ⊆ G.edges) (x : H) :
    G.inv x ∈ exS 𝓔 ↔ x ∈ exS 𝓔 := by
  simp only [exS, Set.mem_compl_iff, Finset.mem_coe]
  exact ⟨fun h hx => h (inv_mem_biUnion_of_subset_edges hG h𝓔 hx),
    fun h hx => h (hG.inv_involutive x ▸ inv_mem_biUnion_of_subset_edges hG h𝓔 hx)⟩

private theorem inv_notMem_biUnion (hG : G.IsPlabicGraph) (h𝓔 : 𝓔 ⊆ G.edges) {y : H}
    (hy : y ∉ 𝓔.biUnion id) : G.inv y ∉ 𝓔.biUnion id := fun h =>
  hy (hG.inv_involutive y ▸ inv_mem_biUnion_of_subset_edges hG h𝓔 h)

/-- The involution of `H \ X`. -/
private noncomputable abbrev exInv (hG : G.IsPlabicGraph) (h𝓔 : 𝓔 ⊆ G.edges) :
    Perm (exS 𝓔) :=
  G.inv.subtypePerm (inv_mem_exS_iff hG h𝓔)

/-- The darts of `H \ X` which are darts of the excision. -/
private abbrev exC (G : PlabicData H b) (𝓔 : Finset (Finset H)) : Set (exS 𝓔) :=
  {s | (s : H) ∈ G.excisionDarts 𝓔}

omit [Fintype H] in
private theorem notMem_of_mem_exS {z : H} (h : z ∈ exS 𝓔) : z ∉ 𝓔.biUnion id :=
  fun hz => h (Finset.mem_coe.2 hz)

omit [Fintype H] in
private theorem mem_exS_of_notMem {z : H} (h : z ∉ 𝓔.biUnion id) : z ∈ exS 𝓔 :=
  fun hz => h (Finset.mem_coe.1 hz)

omit [Fintype H] in
private theorem notMem_exS_of_mem {z : H} (h : z ∈ 𝓔.biUnion id) : z ∉ exS 𝓔 :=
  fun hz => hz (Finset.mem_coe.2 h)

private theorem coe_firstReturnPerm_exS (s : exS 𝓔) :
    (firstReturnPerm G.rot (exS 𝓔) s : H) = G.excisionRot 𝓔 s := by
  rw [excisionRot_apply_of_notMem (notMem_of_mem_exS s.2)]
  rfl

private theorem firstReturnPerm_mem_exC_iff (s : exS 𝓔) :
    firstReturnPerm G.rot (exS 𝓔) s ∈ exC G 𝓔 ↔ s ∈ exC G 𝓔 := by
  change (firstReturnPerm G.rot (exS 𝓔) s : H) ∈ G.excisionDarts 𝓔 ↔ (s : H) ∈ G.excisionDarts 𝓔
  rw [coe_firstReturnPerm_exS]
  exact excisionRot_mem_excisionDarts_iff

private theorem exInv_mem_exC_iff (hG : G.IsPlabicGraph) (h𝓔 : 𝓔 ⊆ G.edges) (s : exS 𝓔) :
    exInv hG h𝓔 s ∈ exC G 𝓔 ↔ s ∈ exC G 𝓔 :=
  inv_mem_excisionDarts_iff hG.inv_involutive fun _ hx => inv_mem_biUnion_of_subset_edges hG h𝓔 hx

variable {hG : G.IsPlabicGraph} {h𝓔 : 𝓔 ⊆ G.edges} {h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry}

/-- The darts of `H` split into those of the excision, the rest of `H \ X`, and `X`. -/
private theorem card_exC_add_card_add_card (G : PlabicData H b) (𝓔 : Finset (Finset H))
    [Fintype {s // s ∈ exC G 𝓔}] [Fintype {s // s ∉ exC G 𝓔}] :
    Fintype.card {s // s ∈ exC G 𝓔} + Fintype.card {s // s ∉ exC G 𝓔} +
      (𝓔.biUnion id).card = Fintype.card H := by
  have h1 := Fintype.card_subtype_compl (fun s => s ∈ exC G 𝓔)
  have h2 := Fintype.card_subtype_le (fun s => s ∈ exC G 𝓔)
  have h3 := Fintype.card_compl_set ((↑(𝓔.biUnion id) : Set H))
  have h4 : Fintype.card ((↑(𝓔.biUnion id) : Set H)) = (𝓔.biUnion id).card := by
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
  have h5 : Fintype.card ((↑(𝓔.biUnion id) : Set H)) ≤ Fintype.card H :=
    Fintype.card_subtype_le _
  have h6 : Fintype.card (exS 𝓔) = Fintype.card ((↑(𝓔.biUnion id) : Set H)ᶜ : Set H) := rfl
  omega

/-- **Counting an excision.** With `M` the rotation system on `H \ X` given by `σ_X` and the
involution, the vertices, edges and face orbits of the excision are those of `M` except for those
of the rest `R` of `H \ X`; the rest has no face orbit only if it is empty, and if it is
connected it satisfies the Euler inequality. -/
private theorem edgeExcision_counts : ∃ VR FR nR : ℕ,
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertices.card + VR =
      numOrbits (firstReturnPerm G.rot (exS 𝓔)) ∧
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOrbits.card + FR =
      numOrbits (firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔) ∧
    2 * (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).edges.card + nR + (𝓔.biUnion id).card =
      Fintype.card H ∧
    ((∀ z, z ∉ 𝓔.biUnion id → z ∈ G.excisionDarts 𝓔) → VR = 0 ∧ FR = 0 ∧ nR = 0) ∧
    ((∃ z, z ∉ 𝓔.biUnion id ∧ z ∉ G.excisionDarts 𝓔) → 0 < FR) ∧
    ((∀ z w, z ∉ 𝓔.biUnion id → w ∉ 𝓔.biUnion id → z ∉ G.excisionDarts 𝓔 →
        w ∉ G.excisionDarts 𝓔 → Relation.ReflTransGen (G.ExcisionStep 𝓔) z w) →
      2 * (FR + VR) ≤ nR + 4) := by
  classical
  set K := G.edgeExcision hG 𝓔 h𝓔 h𝓔B with hK
  have hinv := hG.inv_involutive
  set σS := firstReturnPerm G.rot (exS 𝓔) with hσS
  set ιS := exInv hG h𝓔 with hιS
  have hCσ : ∀ s, σS s ∈ exC G 𝓔 ↔ s ∈ exC G 𝓔 := firstReturnPerm_mem_exC_iff
  have hCι : ∀ s, ιS s ∈ exC G 𝓔 ↔ s ∈ exC G 𝓔 := exInv_mem_exC_iff hG h𝓔
  have hCφ : ∀ s, (σS * ιS) s ∈ exC G 𝓔 ↔ s ∈ exC G 𝓔 := fun s => by
    rw [Perm.mul_apply, hCσ, hCι]
  -- the excision is the restriction of `M` to `C`
  have hnotX : ∀ z : G.excisionDarts 𝓔, (z : H) ∈ exS 𝓔 := fun z =>
    mem_exS_of_notMem (notMem_of_mem_excisionDarts z.2)
  let eC : G.excisionDarts 𝓔 ≃ {s // s ∈ exC G 𝓔} :=
    { toFun := fun z => ⟨⟨z, hnotX z⟩, z.2⟩
      invFun := fun s => ⟨s.1.1, s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hV : K.vertices.card = numOrbits (σS.subtypePerm hCσ) := by
    rw [← RotationSystem.numOrbits_rot]
    refine numOrbits_of_semiconj eC fun z => Subtype.ext (Subtype.ext ?_)
    change ((K.rot z : G.excisionDarts 𝓔) : H) = (σS ⟨z, hnotX z⟩ : H)
    rw [coe_edgeExcision_rot, hσS, coe_firstReturnPerm_exS]
  have hF : K.faceOrbits.card = numOrbits ((σS * ιS).subtypePerm hCφ) := by
    rw [← RotationSystem.numOrbits_facePerm]
    refine numOrbits_of_semiconj eC fun z => Subtype.ext (Subtype.ext ?_)
    change ((K.rot (K.inv z) : G.excisionDarts 𝓔) : H) = (σS (ιS ⟨z, hnotX z⟩) : H)
    rw [coe_edgeExcision_rot, hσS, coe_firstReturnPerm_exS]
    rfl
  have hE : 2 * K.edges.card = Fintype.card {s // s ∈ exC G 𝓔} := by
    rw [← RotationSystem.card_eq_two_mul_card_edges _ (fun z => Subtype.ext (hinv z))
      (fun z h => hG.inv_ne z (congrArg Subtype.val h))]
    exact Fintype.card_congr eC
  have hS := card_exC_add_card_add_card G 𝓔
  refine ⟨numOrbits (σS.subtypePerm (p := fun s => s ∉ exC G 𝓔) fun s => not_congr (hCσ s)),
    numOrbits ((σS * ιS).subtypePerm (p := fun s => s ∉ exC G 𝓔) fun s => not_congr (hCφ s)),
    Fintype.card {s // s ∉ exC G 𝓔}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV, numOrbits_eq_add_subtypePerm σS (exC G 𝓔) hCσ]
  · rw [hF, numOrbits_eq_add_subtypePerm (σS * ιS) (exC G 𝓔) hCφ]
  · omega
  · intro hall
    haveI : IsEmpty {s // s ∉ exC G 𝓔} :=
      ⟨fun s => s.2 (hall s.1.1 (notMem_of_mem_exS s.1.2))⟩
    exact ⟨numOrbits_of_isEmpty _, numOrbits_of_isEmpty _, Fintype.card_eq_zero⟩
  · rintro ⟨z, hzX, hzC⟩
    haveI : Nonempty {s // s ∉ exC G 𝓔} := ⟨⟨⟨z, mem_exS_of_notMem hzX⟩, hzC⟩⟩
    exact numOrbits_pos _
  · intro hconn
    by_cases hR : Fintype.card {s // s ∉ exC G 𝓔} = 0
    · haveI : IsEmpty {s // s ∉ exC G 𝓔} := Fintype.card_eq_zero_iff.1 hR
      rw [numOrbits_of_isEmpty, numOrbits_of_isEmpty]
      omega
    haveI : Nonempty {s // s ∉ exC G 𝓔} := Fintype.card_pos_iff.1 (Nat.pos_of_ne_zero hR)
    set σR := σS.subtypePerm (p := fun s => s ∉ exC G 𝓔) fun s => not_congr (hCσ s)
    set ιR := ιS.subtypePerm (p := fun s => s ∉ exC G 𝓔) fun s => not_congr (hCι s)
    have hιR : Function.Involutive ιR := fun s => Subtype.ext (Subtype.ext (hinv _))
    have hιRne : ∀ s, ιR s ≠ s := fun s h => hG.inv_ne s.1.1 (congrArg (fun t => t.1.1) h)
    have hφR : σR * ιR = (σS * ιS).subtypePerm (p := fun s => s ∉ exC G 𝓔)
        fun s => not_congr (hCφ s) := by
      ext s
      rfl
    -- steps inside the rest are steps of the rotation system on the rest
    let R : RotationSystem {s // s ∉ exC G 𝓔} := ⟨ιR, σR⟩
    have hstep : ∀ c d : {s // s ∉ exC G 𝓔}, G.ExcisionStep 𝓔 c.1 d.1 → R.Reach c d := by
      rintro c d ⟨-, -, h | h | h⟩
      · obtain rfl : d = σR c := by
          refine Subtype.ext (Subtype.ext ?_)
          change (d : H) = (σS c.1 : H)
          rw [hσS, coe_firstReturnPerm_exS, h]
        exact (RotationSystem.Reach.refl c).rot
      · obtain rfl : c = σR d := by
          refine Subtype.ext (Subtype.ext ?_)
          change (c : H) = (σS d.1 : H)
          rw [hσS, coe_firstReturnPerm_exS, h]
        exact (RotationSystem.Reach.refl d).rot.symm
      · obtain rfl : d = ιR c := Subtype.ext (Subtype.ext h)
        exact (RotationSystem.Reach.refl c).inv
    have hreach : ∀ c d : {s // s ∉ exC G 𝓔}, R.Reach c d := by
      intro c d
      have h := hconn c.1.1 d.1.1 (notMem_of_mem_exS c.1.2) (notMem_of_mem_exS d.1.2) c.2 d.2
      obtain ⟨⟨c, hcS⟩, hcC⟩ := c
      obtain ⟨⟨d, hdS⟩, hdC⟩ := d
      change Relation.ReflTransGen (G.ExcisionStep 𝓔) c d at h
      induction h with
      | refl => exact .refl _
      | @tail u v _ hst ih =>
        have hu : u ∉ 𝓔.biUnion id := hst.1
        have huC : u ∉ G.excisionDarts 𝓔 := fun hu' =>
          hdC (mem_excisionDarts_of_step hu' hst)
        exact (ih (mem_exS_of_notMem hu) huC).trans
          (hstep ⟨⟨u, mem_exS_of_notMem hu⟩, huC⟩ ⟨⟨v, hdS⟩, hdC⟩ hst)
    have h := numOrbits_mul_add_numOrbits_add_numOrbits_le σR ιR hιR hreach
    have h2 := two_mul_numOrbits_of_involutive hιR hιRne
    rw [hφR] at h
    omega

/-- Darts in one orbit of the face permutation of `H \ X` are joined by steps of the excision. -/
private theorem reflTransGen_of_sameCycle_exS (hG : G.IsPlabicGraph) (h𝓔 : 𝓔 ⊆ G.edges)
    {a c : exS 𝓔} (h : (firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔).SameCycle a c) :
    Relation.ReflTransGen (G.ExcisionStep 𝓔) a c := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    set u := ((firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔) ^ n) a
    have hu := notMem_of_mem_exS u.2
    have hiu : G.inv u ∉ 𝓔.biUnion id := notMem_of_mem_exS (exInv hG h𝓔 u).2
    have e : (((firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔) u : exS 𝓔) : H) =
        G.excisionRot 𝓔 (G.inv u) := by
      rw [Perm.mul_apply, coe_firstReturnPerm_exS]
      rfl
    rw [e]
    exact (ih.tail ⟨hu, hiu, Or.inr (Or.inr rfl)⟩).tail
      ⟨hiu, excisionRot_mem_iff.not.2 hiu, Or.inl rfl⟩

end Counting

/-! ### First returns in few steps -/

private theorem coe_firstReturn_eq_iterate {X : Type*} [Finite X] {π : Perm X} {Y : Set X}
    {y : Y} {m : ℕ} (hm : 0 < m) (hmY : (⇑π)^[m] y ∈ Y)
    (hmin : ∀ j, 0 < j → j < m → (⇑π)^[j] y ∉ Y) : (firstReturn π Y y : X) = (⇑π)^[m] y := by
  simp only [← Equiv.Perm.coe_pow] at hmY hmin ⊢
  exact coe_firstReturn_of_pow hm hmY hmin

private theorem coe_firstReturn_eq_of_iterate {X : Type*} [Finite X] {π : Perm X} {Y : Set X}
    {y : Y} {m : ℕ} {v : X} (hm : 0 < m) (hv : (⇑π)^[m] y = v) (hvY : v ∈ Y)
    (hmin : ∀ j, 0 < j → j < m → (⇑π)^[j] y ∉ Y) : (firstReturn π Y y : X) = v := by
  rw [coe_firstReturn_eq_iterate hm (hv ▸ hvY) hmin, hv]

section TwoSteps

variable {G : PlabicData H b} {𝓔 : Finset (Finset H)}

/-- `σ_X(z) = σ²(z)` when `σ(z) ∈ X` and `σ²(z) ∉ X`. -/
theorem excisionRot_apply_eq_rot_rot {z : H} (hz : z ∉ 𝓔.biUnion id)
    (h1 : G.rot z ∈ 𝓔.biUnion id) (h2 : G.rot (G.rot z) ∉ 𝓔.biUnion id) :
    G.excisionRot 𝓔 z = G.rot (G.rot z) := by
  rw [excisionRot_apply_of_notMem hz]
  refine coe_firstReturn_eq_iterate (m := 2) (by norm_num) (mem_exS_of_notMem h2) ?_
  intro j hj hj2
  interval_cases j
  exact fun h => h (Finset.mem_coe.2 h1)

/-- `σ_X(z) = σ³(z)` when `σ(z), σ²(z) ∈ X` and `σ³(z) ∉ X`. -/
theorem excisionRot_apply_eq_rot_rot_rot {z : H} (hz : z ∉ 𝓔.biUnion id)
    (h1 : G.rot z ∈ 𝓔.biUnion id) (h2 : G.rot (G.rot z) ∈ 𝓔.biUnion id)
    (h3 : G.rot (G.rot (G.rot z)) ∉ 𝓔.biUnion id) :
    G.excisionRot 𝓔 z = G.rot (G.rot (G.rot z)) := by
  rw [excisionRot_apply_of_notMem hz]
  refine coe_firstReturn_eq_iterate (m := 3) (by norm_num) (mem_exS_of_notMem h3) ?_
  intro j hj hj3
  interval_cases j
  · exact fun h => h (Finset.mem_coe.2 h1)
  · exact fun h => h (Finset.mem_coe.2 h2)

/-- `σ_X⁻¹(z) = σ⁻¹(z)` when `z, σ⁻¹(z) ∉ X`. -/
theorem excisionRot_symm_apply_of_notMem {z : H} (hz : z ∉ 𝓔.biUnion id)
    (h : G.rot.symm z ∉ 𝓔.biUnion id) : (G.excisionRot 𝓔).symm z = G.rot.symm z := by
  rw [Equiv.symm_apply_eq, excisionRot_apply_of_rot_notMem h (by rwa [Equiv.apply_symm_apply]),
    Equiv.apply_symm_apply]

/-- **Joining a dart to a union of vertices.** If `A` is a union of vertices containing `X` and
some dart, every dart outside `X` is joined by steps of the excision to a dart of `A \ X`. -/
theorem exists_reflTransGen_excisionStep_mem (hG : G.IsPlabicGraph) (h𝓔 : 𝓔 ⊆ G.edges)
    {A : Finset H} (hA : ∀ w, G.rot w ∈ A ↔ w ∈ A) (hXA : ∀ x ∈ 𝓔.biUnion id, x ∈ A) {a : H}
    (ha : a ∈ A) {z : H} (hz : z ∉ 𝓔.biUnion id) :
    ∃ q ∈ A, q ∉ 𝓔.biUnion id ∧ Relation.ReflTransGen (G.ExcisionStep 𝓔) z q := by
  have key : ∀ w, G.Reach z w → (∃ q ∈ A, q ∉ 𝓔.biUnion id ∧
      Relation.ReflTransGen (G.ExcisionStep 𝓔) z q) ∨
      (w ∉ A ∧ Relation.ReflTransGen (G.ExcisionStep 𝓔) z w) := by
    intro w hw
    induction hw with
    | refl =>
      by_cases hzA : z ∈ A
      · exact Or.inl ⟨z, hzA, hz, .refl⟩
      · exact Or.inr ⟨hzA, .refl⟩
    | @rot w _ ih =>
      rcases ih with h | ⟨hwA, hzw⟩
      · exact Or.inl h
      · have hwX : w ∉ 𝓔.biUnion id := fun h => hwA (hXA w h)
        have hσA : G.rot w ∉ A := fun h => hwA ((hA w).1 h)
        have hσX : G.rot w ∉ 𝓔.biUnion id := fun h => hσA (hXA _ h)
        exact Or.inr ⟨hσA, hzw.tail
          ⟨hwX, hσX, Or.inl (excisionRot_apply_of_rot_notMem hwX hσX).symm⟩⟩
    | @inv w _ ih =>
      rcases ih with h | ⟨hwA, hzw⟩
      · exact Or.inl h
      · have hwX : w ∉ 𝓔.biUnion id := fun h => hwA (hXA w h)
        have hιX : G.inv w ∉ 𝓔.biUnion id := fun h => hwX (by
          have := inv_mem_biUnion_of_subset_edges hG h𝓔 h
          rwa [hG.inv_involutive] at this)
        have hstep := hzw.tail ⟨hwX, hιX, Or.inr (Or.inr rfl)⟩
        by_cases hιA : G.inv w ∈ A
        · exact Or.inl ⟨_, hιA, hιX, hstep⟩
        · exact Or.inr ⟨hιA, hstep⟩
  rcases key a (hG.reach z a) with h | ⟨haA, -⟩
  · exact h
  · exact absurd ha haA

end TwoSteps

/-- A disk map has one face fewer than orbits of its face permutation. -/
theorem _root_.ClusterAlgebras.DiskMap.IsDiskMap.card_faces_add_one {M : DiskMap H}
    (hM : M.IsDiskMap) : M.faces.card + 1 = M.faceOrbits.card :=
  card_erase_add_one hM.exterior_mem_faceOrbits

/-- In a hollow digon `{d₁, d₂}`, the vertices `v(d₁)` and `v(d₂)` are distinct. -/
theorem vertexOf_ne_of_isHollowDigon {G : PlabicData H b} {d₁ d₂ : H}
    (hd : G.IsHollowDigon {d₁, d₂}) : G.vertexOf d₁ ≠ G.vertexOf d₂ := by
  obtain ⟨-, e₁, e₂, he, hne⟩ := hd
  intro h
  have h1 : e₁ ∈ ({d₁, d₂} : Finset H) := by rw [he]; simp
  have h2 : e₂ ∈ ({d₁, d₂} : Finset H) := by rw [he]; simp
  simp only [mem_insert, mem_singleton] at h1 h2
  apply hne
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  exacts [rfl, h, h.symm, rfl]

/-- The pair `{d, d̄}` is an edge of the graph. -/
theorem pair_inv_mem_edges (G : PlabicData H b) (d : H) : ({d, G.inv d} : Finset H) ∈ G.edges :=
  G.mem_edges.2 ⟨d, rfl⟩

/-! ### Removing one side of a one-coloured hollow digon -/

section SameColour

variable {G : PlabicData H b} (hG : G.IsPlabicGraph) {d₁ d₂ : H} (hd : G.IsHollowDigon {d₁, d₂})
  (h𝓔 : {{d₂, G.inv d₂}} ⊆ G.edges)
  (h𝓔B : ∀ e ∈ ({{d₂, G.inv d₂}} : Finset (Finset H)), Disjoint e G.bdry)

include hG hd

/-- **Removing one side of a one-coloured hollow digon**: if `{d₁, d₂}` is a hollow digon of the
plabic graph `G` whose two vertices have the same colour, then the excision `G ⊖ {{d₂, d̄₂}}` is a
plabic graph with the trip permutation of `G` and one face fewer than `G`. -/
@[cluster_algebras "lem_excision_same_colour_digon"]
theorem IsPlabicGraph.edgeExcision_of_isHollowDigon_of_colour_eq
    (hc : G.colour d₁ = G.colour d₂) :
    (G.edgeExcision hG {{d₂, G.inv d₂}} h𝓔 h𝓔B).IsPlabicGraph ∧
      (G.edgeExcision hG {{d₂, G.inv d₂}} h𝓔 h𝓔B).tripPerm = G.tripPerm ∧
      (G.edgeExcision hG {{d₂, G.inv d₂}} h𝓔 h𝓔B).faces.card + 1 = G.faces.card := by
  set 𝓔 : Finset (Finset H) := {{d₂, G.inv d₂}} with h𝓔_def
  have hinv := hG.inv_involutive
  obtain ⟨hxI, hyI, ⟨-, hd2x, hd1d2', hs1⟩, ⟨-, hd1y, hd2d1', hs2⟩⟩ :=
    hG.toIsDiskMap.hollowDigon_shape hd
  have hxy := vertexOf_ne_of_isHollowDigon hd
  have hσ1 : G.rot (G.inv d₂) = d₁ := by rw [← hs1, Equiv.apply_symm_apply]
  have hσ2 : G.rot (G.inv d₁) = d₂ := by rw [← hs2, Equiv.apply_symm_apply]
  have hvx : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := G.vertexOf_eq_of_mem hd2x
  have hvy : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := G.vertexOf_eq_of_mem hd1y
  have hmemX : ∀ z, z ∈ 𝓔.biUnion id ↔ z = d₂ ∨ z = G.inv d₂ := by
    intro z
    simp [𝓔]
  set s := G.rot.symm (G.inv d₂) with hs_def
  set r := G.rot d₂ with hr_def
  have hσs : G.rot s = G.inv d₂ := Equiv.apply_symm_apply _ _
  have hvs : G.vertexOf s = G.vertexOf d₁ := by
    rw [← hvx]
    exact G.vertexOf_eq_of_mem (G.rot_symm_mem_vertexOf _)
  have hvr : G.vertexOf r = G.vertexOf d₂ := G.vertexOf_rot d₂
  have hd12 : d₁ ≠ d₂ := fun h => hxy (by rw [h])
  have hd1X : d₁ ∉ 𝓔.biUnion id := by
    rw [hmemX]
    exact not_or.2 ⟨hd12, hd1d2'⟩
  have hid1X : G.inv d₁ ∉ 𝓔.biUnion id := by
    rw [hmemX]
    exact not_or.2 ⟨hd2d1'.symm, fun h => hd12 (G.inv.injective h)⟩
  have hrX : r ∉ 𝓔.biUnion id := by
    rw [hmemX]
    refine not_or.2 ⟨fun h => hd2d1' ?_, fun h => hxy ?_⟩
    · have hsc : G.rot.SameCycle d₂ (G.inv d₁) := G.mem_vertexOf.1 hd1y
      exact hsc.eq_of_left h
    · rw [← hvx, ← h, hvr]
  have hsX : s ∉ 𝓔.biUnion id := by
    rw [hmemX]
    refine not_or.2 ⟨fun h => hxy (by rw [← hvs, h]), fun h => hd1d2' ?_⟩
    rw [← hσ1, ← h, hσs, h]
  have hX : ∀ x ∈ 𝓔.biUnion id, ¬G.IsBoundaryVertex (G.vertexOf x) := by
    intro x hx
    rcases (hmemX x).1 hx with rfl | rfl
    · exact hyI
    · rwa [hvx]
  -- every dart outside `X` survives the excision
  have hA : ∀ w, G.rot w ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ ↔ w ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ := by
    intro w
    simp only [mem_union, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hXA : ∀ x ∈ 𝓔.biUnion id, x ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ := by
    intro x hx
    rcases (hmemX x).1 hx with rfl | rfl
    · exact mem_union_right _ (G.self_mem_vertexOf _)
    · exact mem_union_left _ hd2x
  have hjoin : ∀ q ∈ G.vertexOf d₁ ∪ G.vertexOf d₂, q ∉ 𝓔.biUnion id →
      Relation.ReflTransGen (G.ExcisionStep 𝓔) q d₁ := by
    intro q hq hqX
    rcases mem_union.1 hq with hq | hq
    · exact reflTransGen_excisionStep_of_sameCycle hqX hd1X (G.mem_vertexOf.1 hq).symm
    · refine (reflTransGen_excisionStep_of_sameCycle hqX hid1X
        ((G.mem_vertexOf.1 hq).symm.trans (G.mem_vertexOf.1 hd1y))).tail
        ⟨hid1X, hd1X, Or.inr (Or.inr (hinv d₁).symm)⟩
  have hall : ∀ z, z ∉ 𝓔.biUnion id → z ∈ G.excisionDarts 𝓔 := by
    obtain ⟨b0, hb0⟩ := hG.toIsDiskMap.bdry_nonempty
    have hb0X : b0 ∉ 𝓔.biUnion id := notMem_biUnion_of_isBoundaryVertex hX
      (G.isBoundaryVertex_vertexOf_of_mem hb0)
    obtain ⟨qb, hqbA, hqbX, hbq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA hXA
      (mem_union_left _ (G.self_mem_vertexOf d₁)) hb0X
    intro z hz
    obtain ⟨qz, hqzA, hqzX, hzq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA hXA
      (mem_union_left _ (G.self_mem_vertexOf d₁)) hz
    exact mem_excisionDarts.2 ⟨hz, b0, hb0, hb0X, (hbq.trans (hjoin qb hqbA hqbX)).trans
      (reflTransGen_excisionStep_symm hinv (hzq.trans (hjoin qz hqzA hqzX)))⟩
  -- counting
  obtain ⟨VR, FR, nR, hVc, hFc, hEc, hempty, -, -⟩ :=
    edgeExcision_counts (G := G) (𝓔 := 𝓔) (hG := hG) (h𝓔 := h𝓔) (h𝓔B := h𝓔B)
  obtain ⟨hVR, hFR, hnR⟩ := hempty hall
  have hVS : numOrbits (firstReturnPerm G.rot (exS 𝓔)) = G.vertices.card := by
    rw [numOrbits_firstReturnPerm _ _ fun w => ?_, RotationSystem.numOrbits_rot]
    by_cases hw : w ∈ 𝓔.biUnion id
    · rcases (hmemX w).1 hw with rfl | rfl
      · exact ⟨_, mem_exS_of_notMem hid1X, G.mem_vertexOf.1 hd1y⟩
      · exact ⟨_, mem_exS_of_notMem hd1X, (G.mem_vertexOf.1 (hvx ▸ G.self_mem_vertexOf d₁))⟩
    · exact ⟨w, mem_exS_of_notMem hw, .refl _ _⟩
  -- the face permutation of the excision is a first return of `φ ∘ (d̄₂ d₁)`
  set ψ := G.facePerm * swap (G.inv d₂) d₁ with hψ_def
  have hφ1 : G.facePerm d₁ = d₂ := by rw [RotationSystem.facePerm_apply, hσ2]
  have hφ2 : G.facePerm d₂ = d₁ := by rw [RotationSystem.facePerm_apply, hσ1]
  have hψ1 : ψ d₁ = r := by
    rw [hψ_def, Perm.mul_apply, swap_apply_right, RotationSystem.facePerm_apply, hinv]
  have hψ2 : ψ d₂ = d₁ := by
    rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne (fun h => hG.inv_ne d₂ h.symm)
      hd12.symm, hφ2]
  have hψ3 : ψ (G.inv d₂) = d₂ := by
    rw [hψ_def, Perm.mul_apply, swap_apply_left, hφ1]
  have hψS : firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔 = firstReturnPerm ψ (exS 𝓔) := by
    ext ⟨z, hz⟩
    have hzX := notMem_of_mem_exS hz
    rw [Perm.mul_apply, coe_firstReturnPerm_exS, coe_firstReturnPerm]
    change G.excisionRot 𝓔 (G.inv z) = _
    by_cases h1 : z = d₁
    · subst h1
      rw [excisionRot_apply_eq_rot_rot hid1X (by rw [hσ2, hmemX]; exact Or.inl rfl)
        (by rwa [hσ2]), hσ2, coe_firstReturn_of_apply_mem
        (by rw [hψ1]; exact mem_exS_of_notMem hrX), hψ1]
    by_cases h2 : z = G.inv s
    · subst h2
      have hne1 : G.inv s ≠ G.inv d₂ := fun h => hsX ((hmemX _).2 (Or.inl (G.inv.injective h)))
      have hne2 : G.inv s ≠ d₁ := h1
      have hψs : ψ (G.inv s) = G.inv d₂ := by
        rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne hne1 hne2,
          RotationSystem.facePerm_apply, hinv, hσs]
      rw [hinv, excisionRot_apply_eq_rot_rot hsX (by rw [hσs, hmemX]; exact Or.inr rfl)
        (by rwa [hσs, hσ1]), hσs, hσ1]
      symm
      refine coe_firstReturn_eq_of_iterate (m := 3) (by norm_num) ?_ (mem_exS_of_notMem hd1X) ?_
      · change ψ (ψ (ψ (G.inv s))) = d₁
        rw [hψs, hψ3, hψ2]
      · intro j hj hj3
        interval_cases j
        · change ψ (G.inv s) ∉ exS 𝓔
          rw [hψs]
          exact fun h => h ((hmemX _).2 (Or.inr rfl))
        · change ψ (ψ (G.inv s)) ∉ exS 𝓔
          rw [hψs, hψ3]
          exact fun h => h ((hmemX _).2 (Or.inl rfl))
    · have hzd2 : z ≠ G.inv d₂ := fun h => hzX ((hmemX _).2 (Or.inr h))
      have hψz : ψ z = G.rot (G.inv z) := by
        rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne hzd2 h1, RotationSystem.facePerm_apply]
      have hσzX : G.rot (G.inv z) ∉ 𝓔.biUnion id := by
        rw [hmemX]
        refine not_or.2 ⟨fun h => h1 ?_, fun h => h2 ?_⟩
        · rw [← hσ2] at h
          rw [← hinv z, G.rot.injective h, hinv]
        · rw [← hσs] at h
          rw [← hinv z, G.rot.injective h]
      have hizX : G.inv z ∉ 𝓔.biUnion id := inv_notMem_biUnion hG h𝓔 hzX
      rw [excisionRot_apply_of_rot_notMem hizX hσzX, coe_firstReturn_of_apply_mem
        (by rw [hψz]; exact mem_exS_of_notMem hσzX), hψz]
  have hnsc : ¬G.facePerm.SameCycle (G.inv d₂) d₁ := fun h =>
    (eq_or_eq_of_sameCycle hφ1 hφ2 h.symm).elim (fun h' => hd1d2' h'.symm) (hG.inv_ne d₂)
  have hFS : numOrbits (firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔) + 1 =
      G.faceOrbits.card := by
    rw [hψS, numOrbits_firstReturnPerm _ _ fun w => ?_, hψ_def,
      numOrbits_mul_swap_of_not_sameCycle _ hnsc, RotationSystem.numOrbits_facePerm]
    · have := G.faceOrbits.card_pos.2 ⟨_, G.faceOf_mem_faceOrbits d₁⟩
      omega
    by_cases hw : w ∈ 𝓔.biUnion id
    · rcases (hmemX w).1 hw with rfl | rfl
      · refine ⟨d₁, mem_exS_of_notMem hd1X, ?_⟩
        exact ⟨(1 : ℕ), by rw [zpow_natCast, pow_one, hψ2]⟩
      · refine ⟨d₁, mem_exS_of_notMem hd1X, ?_⟩
        exact ⟨(2 : ℕ), by rw [zpow_natCast, pow_two, Perm.mul_apply, hψ3, hψ2]⟩
    · exact ⟨w, mem_exS_of_notMem hw, .refl _ _⟩
  have hXcard : (𝓔.biUnion id).card = 2 := by
    have : 𝓔.biUnion id = {d₂, G.inv d₂} := by simp [𝓔]
    rw [this, card_pair (fun h => hG.inv_ne d₂ h.symm)]
  have hEG := G.card_eq_two_mul_card_edges hinv hG.inv_ne
  have heulerG := hG.euler
  rw [hVR] at hVc
  rw [hFR] at hFc
  rw [hnR] at hEc
  have heuler : ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertices.card : ℤ) -
      (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).edges.card +
        (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOrbits.card = 2 := by
    omega
  have hKp := isPlabicGraph_edgeExcision hX heuler
  have hfaces : (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faces.card + 1 = G.faces.card := by
    have h1 := hKp.toIsDiskMap.card_faces_add_one
    have h2 := hG.toIsDiskMap.card_faces_add_one
    omega
  refine ⟨hKp, ?_, hfaces⟩
  -- trips
  have hcolx : ∀ w ∈ G.vertexOf d₁, G.colour w = G.colour d₁ := fun w hw =>
    hG.colour_eq_of_mem_vertexOf hxI hw
  have hcoly : ∀ w ∈ G.vertexOf d₂, G.colour w = G.colour d₁ := fun w hw =>
    (hG.colour_eq_of_mem_vertexOf hyI hw).trans hc.symm
  have hcolX : ∀ w ∈ 𝓔.biUnion id, G.colour w = G.colour d₁ := by
    intro w hw
    rcases (hmemX w).1 hw with rfl | rfl
    · exact hcoly _ (G.self_mem_vertexOf _)
    · exact hcolx _ hd2x
  have hρs : G.excisionRot 𝓔 s = d₁ := by
    rw [excisionRot_apply_eq_rot_rot hsX (by rw [hσs, hmemX]; exact Or.inr rfl)
      (by rwa [hσs, hσ1]), hσs, hσ1]
  have hρd : G.excisionRot 𝓔 (G.inv d₁) = r := by
    rw [excisionRot_apply_eq_rot_rot hid1X (by rw [hσ2, hmemX]; exact Or.inl rfl)
      (by rwa [hσ2]), hσ2]
  have hlegX : ∀ i, G.leg i ∉ 𝓔.biUnion id := fun i => notMem_biUnion_of_isBoundaryVertex hX
    (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))
  have hlegb : ∀ i, G.IsBoundaryVertex (G.vertexOf (G.leg i)) := fun i =>
    G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)
  have hinvX : ∀ y, y ∉ 𝓔.biUnion id → G.inv y ∉ 𝓔.biUnion id := fun _ =>
    inv_notMem_biUnion hG h𝓔
  have hrd1 : r ≠ d₁ := fun h => hxy (by rw [← hvr, h])
  have hsid1 : s ≠ G.inv d₁ := fun h => hxy (by rw [← hvs, h, hvy])
  cases hcd : G.colour d₁
  · -- white vertices
    refine hG.tripPerm_eq_of_subtype hKp (coe_edgeExcision_leg hX)
      {z | z ∉ 𝓔.biUnion id ∧ z ∉ G.bdry ∧ z ≠ G.inv d₁} (fun y hy => hall y hy.1)
      (fun i => ⟨hlegX i, hG.leg_notMem_bdry i,
        fun h => hyI (by rw [← hvy, ← h]; exact hlegb i)⟩) ?_
    rintro y ⟨hyX, hyB, hyd⟩
    have hzX := hinvX y hyX
    have hzB : G.inv y ∉ G.bdry := fun h => hyB (hG.inv_mem_bdry_iff.1 h)
    by_cases hb : G.IsBoundaryVertex (G.vertexOf (G.inv y))
    · have hT : G.tripMap y = G.inv y := by rw [tripMap_apply, turn_of_isBoundaryVertex hb]
      refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
        fun j hj hj1 => by omega⟩
      · change G.tripMap y ∈ _
        rw [hT]
        exact ⟨hzX, hzB, fun h => hyI (by rwa [← hvy, ← h])⟩
      · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
        rw [coe_edgeExcision_tripMap_of_isBoundaryVertex (w := ⟨y, hall y hyX⟩) hb, hT]
    cases hcz : G.colour (G.inv y)
    · -- `v(ȳ)` white
      have hT : G.tripMap y = G.rot.symm (G.inv y) := by rw [tripMap_apply, turn_of_white hb hcz]
      by_cases hσX : G.rot.symm (G.inv y) ∈ 𝓔.biUnion id
      · rcases (hmemX _).1 hσX with h | h
        · -- `ȳ = r`
          have hyr : G.inv y = r := by rw [hr_def, ← h, Equiv.apply_symm_apply]
          have hTd2 : G.tripMap d₂ = s := by
            rw [tripMap_apply, turn_of_white (by rwa [hvx]) (by rw [hcolx _ hd2x, hcd])]
          refine ⟨2, 2, two_pos, two_pos, ?_, ?_, ?_, ?_⟩
          · change G.tripMap (G.tripMap y) ∈ _
            rw [hT, h, hTd2]
            exact ⟨hsX, notMem_bdry_of_mem_vertexOf hxI
              (by rw [← hvs]; exact G.self_mem_vertexOf _),
              hsid1⟩
          · intro j hj hj2
            interval_cases j
            change G.tripMap y ∉ _
            rw [hT, h]
            exact fun hh => hh.1 ((hmemX _).2 (Or.inl rfl))
          · have h1 : ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, hall y hyX⟩ : H) = G.inv d₁ := by
              rw [coe_edgeExcision_tripMap_of_white (w := ⟨y, hall y hyX⟩) hb hcz]
              change (G.excisionRot 𝓔).symm (G.inv y) = _
              rw [hyr, Equiv.symm_apply_eq, hρd]
            change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap
              ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩) : H) = G.tripMap (G.tripMap y)
            rw [coe_edgeExcision_tripMap_of_white (by rwa [h1, hinv])
              (by rw [h1, hinv, hcd]), h1, hinv, hT, h, hTd2, Equiv.symm_apply_eq, hρs]
          · intro j hj hj2
            interval_cases j
            change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) ∉ _
            rw [coe_edgeExcision_tripMap_of_white (w := ⟨y, hall y hyX⟩) hb hcz]
            change (G.excisionRot 𝓔).symm (G.inv y) ∉ _
            rw [hyr, (Equiv.symm_apply_eq _).2 hρd.symm]
            exact fun hh => hh.2.2 rfl
        · -- `ȳ = d₁`, so `y = d̄₁`
          exfalso
          apply hyd
          have : G.inv y = d₁ := by rw [← hσ1, ← h, Equiv.apply_symm_apply]
          rw [← this, hinv]
      · have hσY : G.rot.symm (G.inv y) ≠ G.inv d₁ := by
          intro h
          apply hyX
          rw [hmemX]
          right
          have : G.inv y = d₂ := by rw [← hσ2, ← h, Equiv.apply_symm_apply]
          rw [← this, hinv]
        refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
          fun j hj hj1 => by omega⟩
        · change G.tripMap y ∈ _
          rw [hT]
          exact ⟨hσX, notMem_bdry_of_mem_vertexOf hb (G.rot_symm_mem_vertexOf _), hσY⟩
        · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
          rw [coe_edgeExcision_tripMap_of_white (w := ⟨y, hall y hyX⟩) hb hcz, hT]
          exact excisionRot_symm_apply_of_notMem hzX hσX
    · -- `v(ȳ)` black, away from the digon
      have hT : G.tripMap y = G.rot (G.inv y) := by rw [tripMap_apply, turn_of_black hb hcz]
      have hcσ : G.colour (G.rot (G.inv y)) = .black := by rw [hG.colour_rot _ hb, hcz]
      have hσX : G.rot (G.inv y) ∉ 𝓔.biUnion id := fun h => by
        have := hcolX _ h
        rw [hcσ, hcd] at this
        exact Shade.noConfusion this
      refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
        fun j hj hj1 => by omega⟩
      · change G.tripMap y ∈ _
        rw [hT]
        refine ⟨hσX, notMem_bdry_of_mem_vertexOf hb (G.rot_mem_vertexOf _), fun h => ?_⟩
        have := hcoly _ hd1y
        rw [← h, hcσ, hcd] at this
        exact Shade.noConfusion this
      · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
        rw [coe_edgeExcision_tripMap_of_black (w := ⟨y, hall y hyX⟩) hb hcz, hT]
        exact excisionRot_apply_of_rot_notMem hzX hσX
  · -- black vertices
    refine hG.tripPerm_eq_of_subtype hKp (coe_edgeExcision_leg hX)
      {z | z ∉ 𝓔.biUnion id ∧ z ∉ G.bdry ∧ z ≠ d₁} (fun y hy => hall y hy.1)
      (fun i => ⟨hlegX i, hG.leg_notMem_bdry i,
        fun h => hxI (by rw [← h]; exact hlegb i)⟩) ?_
    rintro y ⟨hyX, hyB, hyd⟩
    have hzX := hinvX y hyX
    have hzB : G.inv y ∉ G.bdry := fun h => hyB (hG.inv_mem_bdry_iff.1 h)
    by_cases hb : G.IsBoundaryVertex (G.vertexOf (G.inv y))
    · have hT : G.tripMap y = G.inv y := by rw [tripMap_apply, turn_of_isBoundaryVertex hb]
      refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
        fun j hj hj1 => by omega⟩
      · change G.tripMap y ∈ _
        rw [hT]
        exact ⟨hzX, hzB, fun h => hxI (by rwa [← h])⟩
      · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
        rw [coe_edgeExcision_tripMap_of_isBoundaryVertex (w := ⟨y, hall y hyX⟩) hb, hT]
    cases hcz : G.colour (G.inv y)
    · -- `v(ȳ)` white, away from the digon
      have hT : G.tripMap y = G.rot.symm (G.inv y) := by rw [tripMap_apply, turn_of_white hb hcz]
      have hcσ : G.colour (G.rot.symm (G.inv y)) = .white := by
        rw [hG.colour_eq_of_mem_vertexOf hb (G.rot_symm_mem_vertexOf _), hcz]
      have hσX : G.rot.symm (G.inv y) ∉ 𝓔.biUnion id := fun h => by
        have := hcolX _ h
        rw [hcσ, hcd] at this
        exact Shade.noConfusion this
      refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
        fun j hj hj1 => by omega⟩
      · change G.tripMap y ∈ _
        rw [hT]
        refine ⟨hσX, notMem_bdry_of_mem_vertexOf hb (G.rot_symm_mem_vertexOf _), fun h => ?_⟩
        have := hcσ
        rw [h, hcd] at this
        exact Shade.noConfusion this
      · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
        rw [coe_edgeExcision_tripMap_of_white (w := ⟨y, hall y hyX⟩) hb hcz, hT]
        exact excisionRot_symm_apply_of_notMem hzX hσX
    · -- `v(ȳ)` black
      have hT : G.tripMap y = G.rot (G.inv y) := by rw [tripMap_apply, turn_of_black hb hcz]
      by_cases hσX : G.rot (G.inv y) ∈ 𝓔.biUnion id
      · rcases (hmemX _).1 hσX with h | h
        · -- `ȳ = d̄₁`, so `y = d₁`
          exfalso
          apply hyd
          rw [← hσ2] at h
          rw [← hinv y, G.rot.injective h, hinv]
        · -- `ȳ = s`
          have hys : G.inv y = s := G.rot.injective (h.trans hσs.symm)
          have hTd2 : G.tripMap (G.inv d₂) = r := by
            rw [tripMap_apply, hinv, turn_of_black hyI (by rw [← hc, hcd])]
          refine ⟨2, 2, two_pos, two_pos, ?_, ?_, ?_, ?_⟩
          · change G.tripMap (G.tripMap y) ∈ _
            rw [hT, h, hTd2]
            exact ⟨hrX, notMem_bdry_of_mem_vertexOf hyI (G.rot_mem_vertexOf _), hrd1⟩
          · intro j hj hj2
            interval_cases j
            change G.tripMap y ∉ _
            rw [hT, h]
            exact fun hh => hh.1 ((hmemX _).2 (Or.inr rfl))
          · have h1 : ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, hall y hyX⟩ : H) = d₁ := by
              rw [coe_edgeExcision_tripMap_of_black (w := ⟨y, hall y hyX⟩) hb hcz]
              change G.excisionRot 𝓔 (G.inv y) = _
              rw [hys, hρs]
            change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap
              ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩) : H) = G.tripMap (G.tripMap y)
            rw [coe_edgeExcision_tripMap_of_black (by rwa [h1, hvy])
              (by rw [h1, hcoly _ hd1y, hcd]), h1, hρd, hT, h, hTd2]
          · intro j hj hj2
            interval_cases j
            change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) ∉ _
            rw [coe_edgeExcision_tripMap_of_black (w := ⟨y, hall y hyX⟩) hb hcz]
            change G.excisionRot 𝓔 (G.inv y) ∉ _
            rw [hys, hρs]
            exact fun hh => hh.2.2 rfl
      · have hσY : G.rot (G.inv y) ≠ d₁ := by
          intro h
          apply hyX
          rw [hmemX]
          left
          rw [← hσ1] at h
          rw [← hinv y, G.rot.injective h, hinv]
        refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
          fun j hj hj1 => by omega⟩
        · change G.tripMap y ∈ _
          rw [hT]
          exact ⟨hσX, notMem_bdry_of_mem_vertexOf hb (G.rot_mem_vertexOf _), hσY⟩
        · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
          rw [coe_edgeExcision_tripMap_of_black (w := ⟨y, hall y hyX⟩) hb hcz, hT]
          exact excisionRot_apply_of_rot_notMem hzX hσX

end SameColour

/-! ### Removing both sides of a bicoloured hollow digon -/

section Bicoloured

variable {G : PlabicData H b} (hG : G.IsPlabicGraph)

include hG

omit [Fintype H] hG in
/-- Membership in the darts of the two edges `{d₁, d̄₁}` and `{d₂, d̄₂}`. -/
theorem mem_biUnion_pair_inv_iff {d₁ d₂ z : H} :
    z ∈ ({{d₁, G.inv d₁}, {d₂, G.inv d₂}} : Finset (Finset H)).biUnion id ↔
      z = d₁ ∨ z = G.inv d₁ ∨ z = d₂ ∨ z = G.inv d₂ := by
  simp only [biUnion_insert, singleton_biUnion, id, mem_union, mem_insert, mem_singleton,
    or_assoc]

/-- The darts of both sides of a hollow digon lie at internal vertices. -/
theorem IsPlabicGraph.not_isBoundaryVertex_of_mem_biUnion_pair_inv {d₁ d₂ : H}
    (hd : G.IsHollowDigon {d₁, d₂}) :
    ∀ x ∈ ({{d₁, G.inv d₁}, {d₂, G.inv d₂}} : Finset (Finset H)).biUnion id,
      ¬G.IsBoundaryVertex (G.vertexOf x) := by
  obtain ⟨hxI, hyI, ⟨-, hd2x, -, -⟩, ⟨-, hd1y, -, -⟩⟩ := hG.toIsDiskMap.hollowDigon_shape hd
  intro x hx
  rcases mem_biUnion_pair_inv_iff.1 hx with rfl | rfl | rfl | rfl
  · exact hxI
  · rwa [G.vertexOf_eq_of_mem hd1y]
  · exact hyI
  · rwa [G.vertexOf_eq_of_mem hd2x]

/-- Both sides of a hollow digon consist of four distinct darts. -/
theorem IsPlabicGraph.card_biUnion_pair_inv {d₁ d₂ : H} (hd : G.IsHollowDigon {d₁, d₂}) :
    (({{d₁, G.inv d₁}, {d₂, G.inv d₂}} : Finset (Finset H)).biUnion id).card = 4 := by
  obtain ⟨-, -, ⟨-, -, hd1d2', -⟩, ⟨-, -, hd2d1', -⟩⟩ := hG.toIsDiskMap.hollowDigon_shape hd
  have hxy := vertexOf_ne_of_isHollowDigon hd
  have hd12 : d₁ ≠ d₂ := fun h => hxy (by rw [h])
  have hid12 : G.inv d₁ ≠ G.inv d₂ := fun h => hd12 (G.inv.injective h)
  have : ({{d₁, G.inv d₁}, {d₂, G.inv d₂}} : Finset (Finset H)).biUnion id =
      {d₁, G.inv d₁, d₂, G.inv d₂} := by
    ext z
    rw [mem_biUnion_pair_inv_iff]
    simp
  have hd1i : d₁ ≠ G.inv d₁ := fun h => hG.inv_ne d₁ h.symm
  rw [this, card_insert_of_notMem (by simp [hd1i, hd12, hd1d2']),
    card_insert_of_notMem (by simp [hd2d1'.symm, hid12]), card_pair fun h => hG.inv_ne d₂ h.symm]

/-- Excising both sides of a hollow digon `{d₁, d₂}` when `v(d₁) = {d₁, d̄₂}`: the result is a
plabic graph with fewer faces. -/
private theorem edgeExcision_pair_of_rot_eq {d₁ d₂ : H} (hd : G.IsHollowDigon {d₁, d₂})
    (hA : G.rot d₁ = G.inv d₂) {𝓔 : Finset (Finset H)}
    (h𝓔eq : 𝓔 = {{d₁, G.inv d₁}, {d₂, G.inv d₂}}) (h𝓔 : 𝓔 ⊆ G.edges)
    (h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry) :
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).IsPlabicGraph ∧
      (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faces.card < G.faces.card := by
  have hinv := hG.inv_involutive
  obtain ⟨hxI, hyI, ⟨-, hd2x, hd1d2', hs1⟩, ⟨-, hd1y, hd2d1', hs2⟩⟩ :=
    hG.toIsDiskMap.hollowDigon_shape hd
  have hxy := vertexOf_ne_of_isHollowDigon hd
  have hσ1 : G.rot (G.inv d₂) = d₁ := by rw [← hs1, Equiv.apply_symm_apply]
  have hσ2 : G.rot (G.inv d₁) = d₂ := by rw [← hs2, Equiv.apply_symm_apply]
  have hvx : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := G.vertexOf_eq_of_mem hd2x
  have hvy : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := G.vertexOf_eq_of_mem hd1y
  have hd12 : d₁ ≠ d₂ := fun h => hxy (by rw [h])
  have hid12 : G.inv d₁ ≠ G.inv d₂ := fun h => hd12 (G.inv.injective h)
  have hd1i : d₁ ≠ G.inv d₁ := fun h => hG.inv_ne d₁ h.symm
  have hd2i : d₂ ≠ G.inv d₂ := fun h => hG.inv_ne d₂ h.symm
  have hmemX : ∀ z, z ∈ 𝓔.biUnion id ↔ z = d₁ ∨ z = G.inv d₁ ∨ z = d₂ ∨ z = G.inv d₂ :=
    fun _ => h𝓔eq ▸ mem_biUnion_pair_inv_iff
  have hX : ∀ x ∈ 𝓔.biUnion id, ¬G.IsBoundaryVertex (G.vertexOf x) :=
    h𝓔eq ▸ hG.not_isBoundaryVertex_of_mem_biUnion_pair_inv hd
  have hXcard : (𝓔.biUnion id).card = 4 := h𝓔eq ▸ hG.card_biUnion_pair_inv hd
  have hxX : ∀ w ∈ G.vertexOf d₁, w = d₁ ∨ w = G.inv d₂ := fun w hw =>
    eq_or_eq_of_sameCycle hA hσ1 (G.mem_vertexOf.1 hw)
  -- `v(d₂) ⊄ X`, by transitivity
  have hp : G.rot d₂ ≠ G.inv d₁ := by
    intro hp
    obtain ⟨b0, hb0⟩ := hG.toIsDiskMap.bdry_nonempty
    have key : ∀ w, G.Reach d₁ w → w ∈ 𝓔.biUnion id := by
      intro w hw
      induction hw with
      | refl => exact (hmemX _).2 (Or.inl rfl)
      | rot _ ih =>
        rw [hmemX]
        rcases (hmemX _).1 ih with h | h | h | h <;> rw [h]
        · exact Or.inr (Or.inr (Or.inr hA))
        · exact Or.inr (Or.inr (Or.inl hσ2))
        · exact Or.inr (Or.inl hp)
        · exact Or.inl hσ1
      | inv _ ih => exact inv_mem_biUnion_of_subset_edges hG h𝓔 ih
    exact hX b0 (key b0 (hG.reach d₁ b0)) (G.isBoundaryVertex_vertexOf_of_mem hb0)
  obtain ⟨r, hr⟩ : ∃ r, G.rot d₂ = r := ⟨_, rfl⟩
  obtain ⟨p, hσp⟩ : ∃ p, G.rot p = G.inv d₁ := ⟨_, Equiv.apply_symm_apply _ _⟩
  rw [hr] at hp
  have hvr : G.vertexOf r = G.vertexOf d₂ := by rw [← hr, G.vertexOf_rot]
  have hvp : G.vertexOf p = G.vertexOf d₂ := by rw [← G.vertexOf_rot p, hσp, hvy]
  have hrX : r ∉ 𝓔.biUnion id := by
    rw [hmemX]
    rintro (h | h | h | h)
    · exact hxy (by rw [← h, hvr])
    · exact hp h
    · exact hd2d1' ((G.mem_vertexOf.1 hd1y).eq_of_left (by rw [Function.IsFixedPt, hr, h]))
    · exact hxy (by rw [← hvx, ← h, hvr])
  have hpX : p ∉ 𝓔.biUnion id := by
    rw [hmemX]
    rintro (h | h | h | h)
    · exact hxy (by rw [← h, hvp])
    · exact hd2d1' (by rw [← hσ2, ← h, hσp, h])
    · exact hp (by rw [← hr, ← h, hσp])
    · exact hxy (by rw [← hvx, ← h, hvp])
  -- every dart outside `X` survives the excision
  have hA' : ∀ w, G.rot w ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ ↔
      w ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ := by
    intro w
    simp only [mem_union, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hXA : ∀ x ∈ 𝓔.biUnion id, x ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ := by
    intro x hx
    rcases (hmemX x).1 hx with rfl | rfl | rfl | rfl
    · exact mem_union_left _ (G.self_mem_vertexOf _)
    · exact mem_union_right _ hd1y
    · exact mem_union_right _ (G.self_mem_vertexOf _)
    · exact mem_union_left _ hd2x
  have hjoin : ∀ q ∈ G.vertexOf d₁ ∪ G.vertexOf d₂, q ∉ 𝓔.biUnion id →
      Relation.ReflTransGen (G.ExcisionStep 𝓔) q r := by
    intro q hq hqX
    rcases mem_union.1 hq with hq | hq
    · exfalso
      rcases hxX q hq with h | h
      · exact hqX ((hmemX _).2 (Or.inl h))
      · exact hqX ((hmemX _).2 (Or.inr (Or.inr (Or.inr h))))
    · refine reflTransGen_excisionStep_of_sameCycle hqX hrX ?_
      exact (G.mem_vertexOf.1 hq).symm.trans
        (G.mem_vertexOf.1 (by rw [← hr]; exact G.rot_mem_vertexOf d₂))
  have hall : ∀ z, z ∉ 𝓔.biUnion id → z ∈ G.excisionDarts 𝓔 := by
    obtain ⟨b0, hb0⟩ := hG.toIsDiskMap.bdry_nonempty
    have hb0X : b0 ∉ 𝓔.biUnion id := notMem_biUnion_of_isBoundaryVertex hX
      (G.isBoundaryVertex_vertexOf_of_mem hb0)
    obtain ⟨qb, hqbA, hqbX, hbq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA' hXA
      (mem_union_left _ (G.self_mem_vertexOf d₁)) hb0X
    intro z hz
    obtain ⟨qz, hqzA, hqzX, hzq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA' hXA
      (mem_union_left _ (G.self_mem_vertexOf d₁)) hz
    exact mem_excisionDarts.2 ⟨hz, b0, hb0, hb0X, (hbq.trans (hjoin qb hqbA hqbX)).trans
      (reflTransGen_excisionStep_symm hinv (hzq.trans (hjoin qz hqzA hqzX)))⟩
  -- counting
  obtain ⟨VR, FR, nR, hVc, hFc, hEc, hempty, -, -⟩ :=
    edgeExcision_counts (G := G) (𝓔 := 𝓔) (hG := hG) (h𝓔 := h𝓔) (h𝓔B := h𝓔B)
  obtain ⟨hVR, hFR, hnR⟩ := hempty hall
  have hρp : G.excisionRot 𝓔 p = r := by
    rw [excisionRot_apply_eq_rot_rot_rot hpX (by rw [hσp, hmemX]; exact Or.inr (Or.inl rfl))
      (by rw [hσp, hσ2, hmemX]; exact Or.inr (Or.inr (Or.inl rfl)))
      (by rwa [hσp, hσ2, hr]), hσp, hσ2, hr]
  have hσX : ∀ z, z ∉ 𝓔.biUnion id → z ≠ p → G.rot z ∉ 𝓔.biUnion id := by
    intro z hz hzp h
    rcases (hmemX _).1 h with h | h | h | h
    · exact hz ((hmemX _).2 (Or.inr (Or.inr (Or.inr (G.rot.injective (h.trans hσ1.symm))))))
    · exact hzp (G.rot.injective (h.trans hσp.symm))
    · exact hz ((hmemX _).2 (Or.inr (Or.inl (G.rot.injective (h.trans hσ2.symm)))))
    · exact hz ((hmemX _).2 (Or.inl (G.rot.injective (h.trans hA.symm))))
  -- the vertices: `v(d₁)` disappears
  set σ' := G.rot * swap d₁ d₂ with hσ'_def
  have hσ'1 : σ' d₁ = r := by rw [hσ'_def, Perm.mul_apply, swap_apply_left, hr]
  have hσ'2 : σ' d₂ = G.inv d₂ := by rw [hσ'_def, Perm.mul_apply, swap_apply_right, hA]
  have hσ'3 : σ' (G.inv d₂) = d₁ := by
    rw [hσ'_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd1d2'.symm hd2i.symm, hσ1]
  have hσ'4 : σ' (G.inv d₁) = d₂ := by
    rw [hσ'_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd1i.symm hd2d1'.symm, hσ2]
  have hσ'z : ∀ z, z ∉ 𝓔.biUnion id → σ' z = G.rot z := fun z hz => by
    rw [hσ'_def, Perm.mul_apply, swap_apply_of_ne_of_ne (fun h => hz ((hmemX _).2 (Or.inl h)))
      (fun h => hz ((hmemX _).2 (Or.inr (Or.inr (Or.inl h)))))]
  have hVS : numOrbits (firstReturnPerm G.rot (exS 𝓔)) + 1 = G.vertices.card := by
    have heq : firstReturnPerm G.rot (exS 𝓔) = firstReturnPerm σ' (exS 𝓔) := by
      ext ⟨z, hz⟩
      have hzX := notMem_of_mem_exS hz
      rw [coe_firstReturnPerm_exS, coe_firstReturnPerm]
      change G.excisionRot 𝓔 z = _
      by_cases hzp : z = p
      · rw [show G.excisionRot 𝓔 z = r by rw [hzp, hρp]]
        have hp' : p ∈ exS 𝓔 := mem_exS_of_notMem hpX
        have e1 : σ' p = G.inv d₁ := by rw [hσ'z _ hpX, hσp]
        have key : (⟨z, hz⟩ : exS 𝓔) = ⟨p, hp'⟩ := Subtype.ext hzp
        rw [key]
        symm
        refine coe_firstReturn_eq_of_iterate (m := 5) (by norm_num) ?_ (mem_exS_of_notMem hrX) ?_
        · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [e1, hσ'4, hσ'2, hσ'3, hσ'1]
        · intro j hj hj5
          interval_cases j <;>
            simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          · rw [e1]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inl rfl)))
          · rw [e1, hσ'4]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inr (Or.inl rfl))))
          · rw [e1, hσ'4, hσ'2]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inr (Or.inr rfl))))
          · rw [e1, hσ'4, hσ'2, hσ'3]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inl rfl))
      · have h1 := hσX z hzX hzp
        rw [excisionRot_apply_of_rot_notMem hzX h1]
        symm
        rw [coe_firstReturn_of_apply_mem (by rw [hσ'z z hzX]; exact mem_exS_of_notMem h1),
          hσ'z z hzX]
    have hsc : ¬G.rot.SameCycle d₁ d₂ := fun h => hxy ((G.vertexOf_eq_vertexOf_iff).2 h)
    rw [heq, numOrbits_firstReturnPerm _ _ fun w => ?_, hσ'_def,
      numOrbits_mul_swap_of_not_sameCycle _ hsc, RotationSystem.numOrbits_rot]
    · have := G.vertices.card_pos.2 ⟨_, G.vertexOf_mem_vertices d₁⟩
      omega
    by_cases hw : w ∈ 𝓔.biUnion id
    · refine ⟨r, mem_exS_of_notMem hrX, ?_⟩
      rcases (hmemX w).1 hw with rfl | rfl | rfl | rfl
      · exact sameCycle_of_iterate 1 hσ'1
      · exact sameCycle_of_iterate 4 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hσ'4, hσ'2, hσ'3, hσ'1])
      · exact sameCycle_of_iterate 3 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hσ'2, hσ'3, hσ'1])
      · exact sameCycle_of_iterate 2 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hσ'3, hσ'1])
    · exact ⟨w, mem_exS_of_notMem hw, .refl _ _⟩
  -- the faces: the digon disappears
  set ψ := G.facePerm * swap d₁ (G.inv d₁) with hψ_def
  have hψ1 : ψ d₁ = G.inv d₂ := by
    rw [hψ_def, Perm.mul_apply, swap_apply_left, RotationSystem.facePerm_apply, hinv, hA]
  have hψ2 : ψ (G.inv d₁) = d₂ := by
    rw [hψ_def, Perm.mul_apply, swap_apply_right, RotationSystem.facePerm_apply, hσ2]
  have hψ3 : ψ d₂ = d₁ := by
    rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd12.symm hd2d1',
      RotationSystem.facePerm_apply, hσ1]
  have hψ4 : ψ (G.inv d₂) = r := by
    rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd1d2'.symm hid12.symm,
      RotationSystem.facePerm_apply, hinv, hr]
  have hψz : ∀ z, z ∉ 𝓔.biUnion id → ψ z = G.rot (G.inv z) := fun z hz => by
    rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne (fun h => hz ((hmemX _).2 (Or.inl h)))
      (fun h => hz ((hmemX _).2 (Or.inr (Or.inl h)))), RotationSystem.facePerm_apply]
  have hinvX : ∀ y, y ∉ 𝓔.biUnion id → G.inv y ∉ 𝓔.biUnion id := fun _ =>
    inv_notMem_biUnion hG h𝓔
  have hFS : numOrbits (firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔) + 1 =
      G.faceOrbits.card := by
    have heq : firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔 = firstReturnPerm ψ (exS 𝓔) := by
      ext ⟨z, hz⟩
      have hzX := notMem_of_mem_exS hz
      rw [Perm.mul_apply, coe_firstReturnPerm_exS, coe_firstReturnPerm]
      change G.excisionRot 𝓔 (G.inv z) = _
      by_cases hzp : G.inv z = p
      · rw [hzp, hρp]
        have hip : G.inv p ∉ 𝓔.biUnion id := hinvX p hpX
        have e1 : ψ (G.inv p) = G.inv d₁ := by rw [hψz _ hip, hinv, hσp]
        have hz' : z = G.inv p := by rw [← hzp, hinv]
        have key : (⟨z, hz⟩ : exS 𝓔) = ⟨G.inv p, mem_exS_of_notMem hip⟩ := Subtype.ext hz'
        rw [key]
        symm
        refine coe_firstReturn_eq_of_iterate (m := 5) (by norm_num) ?_ (mem_exS_of_notMem hrX) ?_
        · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [e1, hψ2, hψ3, hψ1, hψ4]
        · intro j hj hj5
          interval_cases j <;>
            simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          · rw [e1]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inl rfl)))
          · rw [e1, hψ2]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inr (Or.inl rfl))))
          · rw [e1, hψ2, hψ3]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inl rfl))
          · rw [e1, hψ2, hψ3, hψ1]
            exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inr (Or.inr rfl))))
      · have h1 := hσX _ (hinvX z hzX) hzp
        rw [excisionRot_apply_of_rot_notMem (hinvX z hzX) h1]
        symm
        rw [coe_firstReturn_of_apply_mem (by rw [hψz z hzX]; exact mem_exS_of_notMem h1),
          hψz z hzX]
    have hφ1 : G.facePerm d₁ = d₂ := by rw [RotationSystem.facePerm_apply, hσ2]
    have hφ2 : G.facePerm d₂ = d₁ := by rw [RotationSystem.facePerm_apply, hσ1]
    have hnsc : ¬G.facePerm.SameCycle d₁ (G.inv d₁) := fun h => by
      rcases eq_or_eq_of_sameCycle hφ1 hφ2 h with h' | h'
      · exact hd1i h'.symm
      · exact hd2d1' h'.symm
    rw [heq, numOrbits_firstReturnPerm _ _ fun w => ?_, hψ_def,
      numOrbits_mul_swap_of_not_sameCycle _ hnsc, RotationSystem.numOrbits_facePerm]
    · have := G.faceOrbits.card_pos.2 ⟨_, G.faceOf_mem_faceOrbits d₁⟩
      omega
    by_cases hw : w ∈ 𝓔.biUnion id
    · refine ⟨r, mem_exS_of_notMem hrX, ?_⟩
      rcases (hmemX w).1 hw with rfl | rfl | rfl | rfl
      · exact sameCycle_of_iterate 2 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hψ1, hψ4])
      · exact sameCycle_of_iterate 4 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hψ2, hψ3, hψ1, hψ4])
      · exact sameCycle_of_iterate 3 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hψ3, hψ1, hψ4])
      · exact sameCycle_of_iterate 1 hψ4
    · exact ⟨w, mem_exS_of_notMem hw, .refl _ _⟩
  have hEG := G.card_eq_two_mul_card_edges hinv hG.inv_ne
  have heulerG := hG.euler
  rw [hVR] at hVc
  rw [hFR] at hFc
  rw [hnR] at hEc
  have heuler : ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertices.card : ℤ) -
      (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).edges.card +
        (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOrbits.card = 2 := by
    omega
  have hKp := isPlabicGraph_edgeExcision hX heuler
  refine ⟨hKp, ?_⟩
  have h1 := hKp.toIsDiskMap.card_faces_add_one
  have h2 := hG.toIsDiskMap.card_faces_add_one
  omega

/-- Excising both sides of a hollow digon `{d₁, d₂}` when neither vertex consists of darts of the
digon alone: the result is a plabic graph with fewer faces. -/
private theorem edgeExcision_pair_of_rot_ne {d₁ d₂ : H} (hd : G.IsHollowDigon {d₁, d₂})
    (hs : G.rot d₁ ≠ G.inv d₂) (hp : G.rot d₂ ≠ G.inv d₁) {𝓔 : Finset (Finset H)}
    (h𝓔eq : 𝓔 = {{d₁, G.inv d₁}, {d₂, G.inv d₂}}) (h𝓔 : 𝓔 ⊆ G.edges)
    (h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry) :
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).IsPlabicGraph ∧
      (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faces.card < G.faces.card := by
  have hinv := hG.inv_involutive
  obtain ⟨hxI, hyI, ⟨-, hd2x, hd1d2', hs1⟩, ⟨-, hd1y, hd2d1', hs2⟩⟩ :=
    hG.toIsDiskMap.hollowDigon_shape hd
  have hxy := vertexOf_ne_of_isHollowDigon hd
  have hσ1 : G.rot (G.inv d₂) = d₁ := by rw [← hs1, Equiv.apply_symm_apply]
  have hσ2 : G.rot (G.inv d₁) = d₂ := by rw [← hs2, Equiv.apply_symm_apply]
  have hvx : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := G.vertexOf_eq_of_mem hd2x
  have hvy : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := G.vertexOf_eq_of_mem hd1y
  have hd12 : d₁ ≠ d₂ := fun h => hxy (by rw [h])
  have hid12 : G.inv d₁ ≠ G.inv d₂ := fun h => hd12 (G.inv.injective h)
  have hd1i : d₁ ≠ G.inv d₁ := fun h => hG.inv_ne d₁ h.symm
  have hd2i : d₂ ≠ G.inv d₂ := fun h => hG.inv_ne d₂ h.symm
  have hmemX : ∀ z, z ∈ 𝓔.biUnion id ↔ z = d₁ ∨ z = G.inv d₁ ∨ z = d₂ ∨ z = G.inv d₂ :=
    fun _ => h𝓔eq ▸ mem_biUnion_pair_inv_iff
  have hX : ∀ x ∈ 𝓔.biUnion id, ¬G.IsBoundaryVertex (G.vertexOf x) :=
    h𝓔eq ▸ hG.not_isBoundaryVertex_of_mem_biUnion_pair_inv hd
  have hXcard : (𝓔.biUnion id).card = 4 := h𝓔eq ▸ hG.card_biUnion_pair_inv hd
  have hinvX : ∀ y, y ∉ 𝓔.biUnion id → G.inv y ∉ 𝓔.biUnion id := fun _ =>
    inv_notMem_biUnion hG h𝓔
  obtain ⟨q, hq⟩ : ∃ q, G.rot d₁ = q := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, G.rot d₂ = r := ⟨_, rfl⟩
  obtain ⟨s, hσs⟩ : ∃ s, G.rot s = G.inv d₂ := ⟨_, Equiv.apply_symm_apply _ _⟩
  obtain ⟨p, hσp⟩ : ∃ p, G.rot p = G.inv d₁ := ⟨_, Equiv.apply_symm_apply _ _⟩
  rw [hq] at hs
  rw [hr] at hp
  have hvq : G.vertexOf q = G.vertexOf d₁ := by rw [← hq, G.vertexOf_rot]
  have hvr : G.vertexOf r = G.vertexOf d₂ := by rw [← hr, G.vertexOf_rot]
  have hvs : G.vertexOf s = G.vertexOf d₁ := by rw [← G.vertexOf_rot s, hσs, hvx]
  have hvp : G.vertexOf p = G.vertexOf d₂ := by rw [← G.vertexOf_rot p, hσp, hvy]
  have hqX : q ∉ 𝓔.biUnion id := by
    rw [hmemX]
    rintro (h | h | h | h)
    · exact hd1d2' ((G.mem_vertexOf.1 hd2x).eq_of_left (by rw [Function.IsFixedPt, hq, h]))
    · exact hxy (by rw [← hvq, h, hvy])
    · exact hxy (by rw [← hvq, h])
    · exact hs h
  have hrX : r ∉ 𝓔.biUnion id := by
    rw [hmemX]
    rintro (h | h | h | h)
    · exact hxy (by rw [← h, hvr])
    · exact hp h
    · exact hd2d1' ((G.mem_vertexOf.1 hd1y).eq_of_left (by rw [Function.IsFixedPt, hr, h]))
    · exact hxy (by rw [← hvx, ← h, hvr])
  have hsX : s ∉ 𝓔.biUnion id := by
    rw [hmemX]
    rintro (h | h | h | h)
    · exact hs (by rw [← hq, ← h, hσs])
    · exact hxy (by rw [← hvs, h, hvy])
    · exact hxy (by rw [← hvs, h])
    · exact hd1d2' (by rw [← hσ1, ← h, hσs, h])
  have hpX : p ∉ 𝓔.biUnion id := by
    rw [hmemX]
    rintro (h | h | h | h)
    · exact hxy (by rw [← h, hvp])
    · exact hd2d1' (by rw [← hσ2, ← h, hσp, h])
    · exact hp (by rw [← hr, ← h, hσp])
    · exact hxy (by rw [← hvx, ← h, hvp])
  have hσX : ∀ z, z ∉ 𝓔.biUnion id → z ≠ p → z ≠ s → G.rot z ∉ 𝓔.biUnion id := by
    intro z hz hzp hzs h
    rcases (hmemX _).1 h with h | h | h | h
    · exact hz ((hmemX _).2 (Or.inr (Or.inr (Or.inr (G.rot.injective (h.trans hσ1.symm))))))
    · exact hzp (G.rot.injective (h.trans hσp.symm))
    · exact hz ((hmemX _).2 (Or.inr (Or.inl (G.rot.injective (h.trans hσ2.symm)))))
    · exact hzs (G.rot.injective (h.trans hσs.symm))
  have hρp : G.excisionRot 𝓔 p = r := by
    rw [excisionRot_apply_eq_rot_rot_rot hpX (by rw [hσp, hmemX]; exact Or.inr (Or.inl rfl))
      (by rw [hσp, hσ2, hmemX]; exact Or.inr (Or.inr (Or.inl rfl)))
      (by rwa [hσp, hσ2, hr]), hσp, hσ2, hr]
  have hρs : G.excisionRot 𝓔 s = q := by
    rw [excisionRot_apply_eq_rot_rot_rot hsX
      (by rw [hσs, hmemX]; exact Or.inr (Or.inr (Or.inr rfl)))
      (by rw [hσs, hσ1, hmemX]; exact Or.inl rfl)
      (by rwa [hσs, hσ1, hq]), hσs, hσ1, hq]
  have hps : p ≠ s := fun h => hxy (by rw [← hvs, ← h, hvp])
  -- the two classes `v(d₁) \ X` and `v(d₂) \ X`
  have hA' : ∀ w, G.rot w ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ ↔
      w ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ := by
    intro w
    simp only [mem_union, RotationSystem.mem_vertexOf, sameCycle_apply_right]
  have hXA : ∀ x ∈ 𝓔.biUnion id, x ∈ G.vertexOf d₁ ∪ G.vertexOf d₂ := by
    intro x hx
    rcases (hmemX x).1 hx with rfl | rfl | rfl | rfl
    · exact mem_union_left _ (G.self_mem_vertexOf _)
    · exact mem_union_right _ hd1y
    · exact mem_union_right _ (G.self_mem_vertexOf _)
    · exact mem_union_left _ hd2x
  have hside : ∀ u ∈ G.vertexOf d₁ ∪ G.vertexOf d₂, u ∉ 𝓔.biUnion id →
      Relation.ReflTransGen (G.ExcisionStep 𝓔) u q ∨
        Relation.ReflTransGen (G.ExcisionStep 𝓔) u r := by
    intro u hu huX
    rcases mem_union.1 hu with hu | hu
    · exact Or.inl (reflTransGen_excisionStep_of_sameCycle huX hqX ((G.mem_vertexOf.1 hu).symm.trans
        (G.mem_vertexOf.1 (by rw [← hq]; exact G.rot_mem_vertexOf d₁))))
    · exact Or.inr (reflTransGen_excisionStep_of_sameCycle huX hrX ((G.mem_vertexOf.1 hu).symm.trans
        (G.mem_vertexOf.1 (by rw [← hr]; exact G.rot_mem_vertexOf d₂))))
  obtain ⟨b0, hb0⟩ := hG.toIsDiskMap.bdry_nonempty
  have hb0X : b0 ∉ 𝓔.biUnion id := notMem_biUnion_of_isBoundaryVertex hX
    (G.isBoundaryVertex_vertexOf_of_mem hb0)
  have hb0H : b0 ∈ G.excisionDarts 𝓔 := bdry_subset_excisionDarts h𝓔B hb0
  obtain ⟨qb, hqbA, hqbX, hbq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA' hXA
    (mem_union_left _ (G.self_mem_vertexOf d₁)) hb0X
  have hqbH : qb ∈ G.excisionDarts 𝓔 := mem_excisionDarts_of_reflTransGen hb0H hbq
  -- counting
  obtain ⟨VR, FR, nR, hVc, hFc, hEc, hempty, hpos, hconn⟩ :=
    edgeExcision_counts (G := G) (𝓔 := 𝓔) (hG := hG) (h𝓔 := h𝓔) (h𝓔B := h𝓔B)
  have hVS : numOrbits (firstReturnPerm G.rot (exS 𝓔)) = G.vertices.card := by
    rw [numOrbits_firstReturnPerm _ _ fun w => ?_, RotationSystem.numOrbits_rot]
    by_cases hw : w ∈ 𝓔.biUnion id
    · rcases (hmemX w).1 hw with rfl | rfl | rfl | rfl
      · exact ⟨q, mem_exS_of_notMem hqX, sameCycle_of_iterate 1 hq⟩
      · exact ⟨r, mem_exS_of_notMem hrX, sameCycle_of_iterate 2 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hσ2, hr])⟩
      · exact ⟨r, mem_exS_of_notMem hrX, sameCycle_of_iterate 1 hr⟩
      · exact ⟨q, mem_exS_of_notMem hqX, sameCycle_of_iterate 2 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hσ1, hq])⟩
    · exact ⟨w, mem_exS_of_notMem hw, .refl _ _⟩
  -- the faces
  set ψ₁ := G.facePerm * swap (G.inv d₁) (G.inv d₂) with hψ₁_def
  set ψ := ψ₁ * swap d₁ (G.inv d₁) with hψ_def
  have hψ1 : ψ d₁ = r := by
    rw [hψ_def, Perm.mul_apply, swap_apply_left, hψ₁_def, Perm.mul_apply, swap_apply_left,
      RotationSystem.facePerm_apply, hinv, hr]
  have hψ2 : ψ (G.inv d₁) = d₂ := by
    rw [hψ_def, Perm.mul_apply, swap_apply_right, hψ₁_def, Perm.mul_apply,
      swap_apply_of_ne_of_ne hd1i hd1d2', RotationSystem.facePerm_apply, hσ2]
  have hψ3 : ψ d₂ = d₁ := by
    rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd12.symm hd2d1', hψ₁_def,
      Perm.mul_apply, swap_apply_of_ne_of_ne hd2d1' hd2i, RotationSystem.facePerm_apply, hσ1]
  have hψ4 : ψ (G.inv d₂) = q := by
    rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd1d2'.symm hid12.symm, hψ₁_def,
      Perm.mul_apply, swap_apply_right, RotationSystem.facePerm_apply, hinv, hq]
  have hψz : ∀ z, z ∉ 𝓔.biUnion id → ψ z = G.rot (G.inv z) := fun z hz => by
    rw [hψ_def, Perm.mul_apply, swap_apply_of_ne_of_ne (fun h => hz ((hmemX _).2 (Or.inl h)))
      (fun h => hz ((hmemX _).2 (Or.inr (Or.inl h)))), hψ₁_def, Perm.mul_apply,
      swap_apply_of_ne_of_ne (fun h => hz ((hmemX _).2 (Or.inr (Or.inl h))))
      (fun h => hz ((hmemX _).2 (Or.inr (Or.inr (Or.inr h))))), RotationSystem.facePerm_apply]
  have heq : firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔 = firstReturnPerm ψ (exS 𝓔) := by
    ext ⟨z, hz⟩
    have hzX := notMem_of_mem_exS hz
    rw [Perm.mul_apply, coe_firstReturnPerm_exS, coe_firstReturnPerm]
    change G.excisionRot 𝓔 (G.inv z) = _
    by_cases hzp : G.inv z = p
    · rw [hzp, hρp]
      have hip : G.inv p ∉ 𝓔.biUnion id := hinvX p hpX
      have e1 : ψ (G.inv p) = G.inv d₁ := by rw [hψz _ hip, hinv, hσp]
      have hz' : z = G.inv p := by rw [← hzp, hinv]
      have key : (⟨z, hz⟩ : exS 𝓔) = ⟨G.inv p, mem_exS_of_notMem hip⟩ := Subtype.ext hz'
      rw [key]
      symm
      refine coe_firstReturn_eq_of_iterate (m := 4) (by norm_num) ?_ (mem_exS_of_notMem hrX) ?_
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        rw [e1, hψ2, hψ3, hψ1]
      · intro j hj hj4
        interval_cases j <;>
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        · rw [e1]
          exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inl rfl)))
        · rw [e1, hψ2]
          exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inr (Or.inl rfl))))
        · rw [e1, hψ2, hψ3]
          exact notMem_exS_of_mem ((hmemX _).2 (Or.inl rfl))
    by_cases hzs : G.inv z = s
    · rw [hzs, hρs]
      have his : G.inv s ∉ 𝓔.biUnion id := hinvX s hsX
      have e1 : ψ (G.inv s) = G.inv d₂ := by rw [hψz _ his, hinv, hσs]
      have hz' : z = G.inv s := by rw [← hzs, hinv]
      have key : (⟨z, hz⟩ : exS 𝓔) = ⟨G.inv s, mem_exS_of_notMem his⟩ := Subtype.ext hz'
      rw [key]
      symm
      refine coe_firstReturn_eq_of_iterate (m := 2) (by norm_num) ?_ (mem_exS_of_notMem hqX) ?_
      · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        rw [e1, hψ4]
      · intro j hj hj2
        interval_cases j
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
        rw [e1]
        exact notMem_exS_of_mem ((hmemX _).2 (Or.inr (Or.inr (Or.inr rfl))))
    · have h1 := hσX _ (hinvX z hzX) hzp hzs
      rw [excisionRot_apply_of_rot_notMem (hinvX z hzX) h1]
      symm
      rw [coe_firstReturn_of_apply_mem (by rw [hψz z hzX]; exact mem_exS_of_notMem h1),
        hψz z hzX]
  have hmeet : ∀ w, ∃ y ∈ exS 𝓔, ψ.SameCycle w y := by
    intro w
    by_cases hw : w ∈ 𝓔.biUnion id
    · rcases (hmemX w).1 hw with rfl | rfl | rfl | rfl
      · exact ⟨r, mem_exS_of_notMem hrX, sameCycle_of_iterate 1 hψ1⟩
      · exact ⟨r, mem_exS_of_notMem hrX, sameCycle_of_iterate 3 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hψ2, hψ3, hψ1])⟩
      · exact ⟨r, mem_exS_of_notMem hrX, sameCycle_of_iterate 2 (by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
          rw [hψ3, hψ1])⟩
      · exact ⟨q, mem_exS_of_notMem hqX, sameCycle_of_iterate 1 hψ4⟩
    · exact ⟨w, mem_exS_of_notMem hw, .refl _ _⟩
  have hψ₁1 : ψ₁ d₁ = d₂ := by
    rw [hψ₁_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd1i hd1d2',
      RotationSystem.facePerm_apply, hσ2]
  have hψ₁2 : ψ₁ d₂ = d₁ := by
    rw [hψ₁_def, Perm.mul_apply, swap_apply_of_ne_of_ne hd2d1' hd2i,
      RotationSystem.facePerm_apply, hσ1]
  have hns : ¬ψ₁.SameCycle d₁ (G.inv d₁) := fun h => by
    rcases eq_or_eq_of_sameCycle hψ₁1 hψ₁2 h with h' | h'
    · exact hd1i h'.symm
    · exact hd2d1' h'.symm
  haveI : Nonempty H := hG.nonempty
  have hψnum : numOrbits ψ + 1 = numOrbits ψ₁ := by
    rw [hψ_def, numOrbits_mul_swap_of_not_sameCycle _ hns]
    have := numOrbits_pos ψ₁
    omega
  have hFS : numOrbits (firstReturnPerm G.rot (exS 𝓔) * exInv hG h𝓔) = numOrbits ψ := by
    rw [heq, numOrbits_firstReturnPerm _ _ hmeet]
  have hEG := G.card_eq_two_mul_card_edges hinv hG.inv_ne
  have heulerG := hG.euler
  have hFG : numOrbits G.facePerm = G.faceOrbits.card := RotationSystem.numOrbits_facePerm _
  by_cases hF : G.facePerm.SameCycle (G.inv d₁) (G.inv d₂)
  · -- the two faces beside the digon coincide: the rest may be cut off
    have hψ₁num : numOrbits ψ₁ = numOrbits G.facePerm + 1 :=
      numOrbits_mul_swap_of_sameCycle _ hid12 hF
    have hKc := isConnected_edgeExcision hX (hG := hG) (h𝓔 := h𝓔) (h𝓔B := h𝓔B)
    have hle := hKc.card_faceOrbits_add_card_vertices_le
    have hconn' : ∀ z w, z ∉ 𝓔.biUnion id → w ∉ 𝓔.biUnion id → z ∉ G.excisionDarts 𝓔 →
        w ∉ G.excisionDarts 𝓔 → Relation.ReflTransGen (G.ExcisionStep 𝓔) z w := by
      intro z w hzX hwX hzH hwH
      obtain ⟨qz, hqzA, hqzX, hzq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA' hXA
        (mem_union_left _ (G.self_mem_vertexOf d₁)) hzX
      obtain ⟨qw, hqwA, hqwX, hwq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA' hXA
        (mem_union_left _ (G.self_mem_vertexOf d₁)) hwX
      have hnH : ∀ u v, u ∉ G.excisionDarts 𝓔 → Relation.ReflTransGen (G.ExcisionStep 𝓔) u v →
          v ∉ G.excisionDarts 𝓔 := fun u v hu huv hv =>
        hu (mem_excisionDarts_of_reflTransGen hv (reflTransGen_excisionStep_symm hinv huv))
      have hqzH := hnH z qz hzH hzq
      have hqwH := hnH w qw hwH hwq
      rcases hside qz hqzA hqzX with h1 | h1 <;> rcases hside qw hqwA hqwX with h2 | h2
      · exact (hzq.trans h1).trans (reflTransGen_excisionStep_symm hinv (hwq.trans h2))
      · exfalso
        rcases hside qb hqbA hqbX with h3 | h3
        · exact hnH qz q hqzH h1 (mem_excisionDarts_of_reflTransGen hqbH h3)
        · exact hnH qw r hqwH h2 (mem_excisionDarts_of_reflTransGen hqbH h3)
      · exfalso
        rcases hside qb hqbA hqbX with h3 | h3
        · exact hnH qw q hqwH h2 (mem_excisionDarts_of_reflTransGen hqbH h3)
        · exact hnH qz r hqzH h1 (mem_excisionDarts_of_reflTransGen hqbH h3)
      · exact (hzq.trans h1).trans (reflTransGen_excisionStep_symm hinv (hwq.trans h2))
    have hR : ∃ z, z ∉ 𝓔.biUnion id ∧ z ∉ G.excisionDarts 𝓔 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hVR, hFR, hnR⟩ := hempty hcon
      rw [hVR] at hVc
      rw [hFR] at hFc
      rw [hnR] at hEc
      omega
    have hFRpos := hpos hR
    have hbound := hconn hconn'
    have heuler : ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertices.card : ℤ) -
        (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).edges.card +
          (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOrbits.card = 2 := by
      omega
    have hKp := isPlabicGraph_edgeExcision hX heuler
    refine ⟨hKp, ?_⟩
    have h1 := hKp.toIsDiskMap.card_faces_add_one
    have h2 := hG.toIsDiskMap.card_faces_add_one
    omega
  · -- the two faces beside the digon are distinct: they merge
    have hψ₁num : numOrbits ψ₁ = numOrbits G.facePerm - 1 :=
      numOrbits_mul_swap_of_not_sameCycle _ hF
    have hψ₁pos := numOrbits_pos ψ₁
    -- `q` and `r` are joined
    have hqr : Relation.ReflTransGen (G.ExcisionStep 𝓔) q r := by
      have h1 : ψ₁.SameCycle q r := by
        refine (sameCycle_mul_swap_iff _ hF).2 (Or.inr (Or.inl ⟨?_, ?_⟩))
        · refine (sameCycle_of_iterate 1 ?_).symm
          change G.rot (G.inv (G.inv d₁)) = q
          rw [hinv, hq]
        · refine (sameCycle_of_iterate 1 ?_).symm
          change G.rot (G.inv (G.inv d₂)) = r
          rw [hinv, hr]
      have h2 : ψ.SameCycle q r := (sameCycle_mul_swap_iff _ hns).2 (Or.inl h1)
      have h3 := (sameCycle_firstReturnPerm_iff ψ (exS 𝓔) (y := ⟨q, mem_exS_of_notMem hqX⟩)
        (y' := ⟨r, mem_exS_of_notMem hrX⟩)).2 h2
      rw [← heq] at h3
      exact reflTransGen_of_sameCycle_exS hG h𝓔 h3
    have hjoin : ∀ u ∈ G.vertexOf d₁ ∪ G.vertexOf d₂, u ∉ 𝓔.biUnion id →
        Relation.ReflTransGen (G.ExcisionStep 𝓔) u r := by
      intro u hu huX
      rcases hside u hu huX with h | h
      · exact h.trans hqr
      · exact h
    have hall : ∀ z, z ∉ 𝓔.biUnion id → z ∈ G.excisionDarts 𝓔 := by
      intro z hz
      obtain ⟨qz, hqzA, hqzX, hzq⟩ := exists_reflTransGen_excisionStep_mem hG h𝓔 hA' hXA
        (mem_union_left _ (G.self_mem_vertexOf d₁)) hz
      exact mem_excisionDarts.2 ⟨hz, b0, hb0, hb0X, (hbq.trans (hjoin qb hqbA hqbX)).trans
        (reflTransGen_excisionStep_symm hinv (hzq.trans (hjoin qz hqzA hqzX)))⟩
    obtain ⟨hVR, hFR, hnR⟩ := hempty hall
    rw [hVR] at hVc
    rw [hFR] at hFc
    rw [hnR] at hEc
    have heuler : ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).vertices.card : ℤ) -
        (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).edges.card +
          (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faceOrbits.card = 2 := by
      omega
    have hKp := isPlabicGraph_edgeExcision hX heuler
    refine ⟨hKp, ?_⟩
    have h1 := hKp.toIsDiskMap.card_faces_add_one
    have h2 := hG.toIsDiskMap.card_faces_add_one
    omega

/-- Excising both sides of a hollow digon gives a plabic graph with fewer faces. -/
private theorem edgeExcision_pair {d₁ d₂ : H} (hd : G.IsHollowDigon {d₁, d₂})
    {𝓔 : Finset (Finset H)} (h𝓔eq : 𝓔 = {{d₁, G.inv d₁}, {d₂, G.inv d₂}})
    (h𝓔 : 𝓔 ⊆ G.edges) (h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry) :
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).IsPlabicGraph ∧
      (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).faces.card < G.faces.card := by
  by_cases hA : G.rot d₁ = G.inv d₂
  · exact edgeExcision_pair_of_rot_eq hG hd hA h𝓔eq h𝓔 h𝓔B
  by_cases hB : G.rot d₂ = G.inv d₁
  · exact edgeExcision_pair_of_rot_eq hG (d₁ := d₂) (d₂ := d₁) (by rwa [pair_comm]) hB
      (by rw [h𝓔eq, pair_comm]) h𝓔 h𝓔B
  · exact edgeExcision_pair_of_rot_ne hG hd hA hB h𝓔eq h𝓔 h𝓔B

/-- Excising both sides of a hollow digon `{d₁, d₂}` with `v(d₁)` black and `v(d₂)` white keeps
the trip permutation. -/
private theorem tripPerm_edgeExcision_pair {d₁ d₂ : H} (hd : G.IsHollowDigon {d₁, d₂})
    (hc₁ : G.colour d₁ = .black) (hc₂ : G.colour d₂ = .white) {𝓔 : Finset (Finset H)}
    (h𝓔eq : 𝓔 = {{d₁, G.inv d₁}, {d₂, G.inv d₂}}) (h𝓔 : 𝓔 ⊆ G.edges)
    (h𝓔B : ∀ e ∈ 𝓔, Disjoint e G.bdry) (hK : (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).IsPlabicGraph) :
    (G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripPerm = G.tripPerm := by
  have hinv := hG.inv_involutive
  obtain ⟨hxI, hyI, ⟨-, hd2x, hd1d2', hs1⟩, ⟨-, hd1y, hd2d1', hs2⟩⟩ :=
    hG.toIsDiskMap.hollowDigon_shape hd
  have hxy := vertexOf_ne_of_isHollowDigon hd
  have hσ1 : G.rot (G.inv d₂) = d₁ := by rw [← hs1, Equiv.apply_symm_apply]
  have hσ2 : G.rot (G.inv d₁) = d₂ := by rw [← hs2, Equiv.apply_symm_apply]
  have hvx : G.vertexOf (G.inv d₂) = G.vertexOf d₁ := G.vertexOf_eq_of_mem hd2x
  have hvy : G.vertexOf (G.inv d₁) = G.vertexOf d₂ := G.vertexOf_eq_of_mem hd1y
  have hmemX : ∀ z, z ∈ 𝓔.biUnion id ↔ z = d₁ ∨ z = G.inv d₁ ∨ z = d₂ ∨ z = G.inv d₂ :=
    fun _ => h𝓔eq ▸ mem_biUnion_pair_inv_iff
  have hX : ∀ x ∈ 𝓔.biUnion id, ¬G.IsBoundaryVertex (G.vertexOf x) :=
    h𝓔eq ▸ hG.not_isBoundaryVertex_of_mem_biUnion_pair_inv hd
  have hcolx : ∀ w ∈ G.vertexOf d₁, G.colour w = .black := fun w hw =>
    (hG.colour_eq_of_mem_vertexOf hxI hw).trans hc₁
  have hcoly : ∀ w ∈ G.vertexOf d₂, G.colour w = .white := fun w hw =>
    (hG.colour_eq_of_mem_vertexOf hyI hw).trans hc₂
  have hXH : ∀ x ∈ 𝓔.biUnion id, x ∉ G.excisionDarts 𝓔 := fun x hx h =>
    notMem_of_mem_excisionDarts h hx
  refine hG.tripPerm_eq_of_subtype hK (coe_edgeExcision_leg hX)
    {z | z ∈ G.excisionDarts 𝓔 ∧ z ∉ G.bdry} (fun y hy => hy.1)
    (fun i => ⟨mem_excisionDarts_of_isBoundaryVertex hX
      (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)), hG.leg_notMem_bdry i⟩) ?_
  rintro y ⟨hyH, hyB⟩
  have hzH : G.inv y ∈ G.excisionDarts 𝓔 := (inv_mem_excisionDarts_iff hinv
    fun _ hx => inv_mem_biUnion_of_subset_edges hG h𝓔 hx).2 hyH
  have hzX : G.inv y ∉ 𝓔.biUnion id := notMem_of_mem_excisionDarts hzH
  have hzB : G.inv y ∉ G.bdry := fun h => hyB (hG.inv_mem_bdry_iff.1 h)
  by_cases hb : G.IsBoundaryVertex (G.vertexOf (G.inv y))
  · have hT : G.tripMap y = G.inv y := by rw [tripMap_apply, turn_of_isBoundaryVertex hb]
    refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_, fun j hj hj1 => by omega⟩
    · change G.tripMap y ∈ _
      rw [hT]
      exact ⟨hzH, hzB⟩
    · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
      rw [coe_edgeExcision_tripMap_of_isBoundaryVertex (w := ⟨y, hyH⟩) hb, hT]
  cases hcz : G.colour (G.inv y)
  · -- `v(ȳ)` white
    have hT : G.tripMap y = G.rot.symm (G.inv y) := by rw [tripMap_apply, turn_of_white hb hcz]
    by_cases hσX : G.rot.symm (G.inv y) ∈ 𝓔.biUnion id
    · rcases (hmemX _).1 hσX with h | h | h | h
      · -- `ȳ = σ(d₁)` is black
        exfalso
        have : G.inv y ∈ G.vertexOf d₁ := by
          rw [← Equiv.apply_symm_apply G.rot (G.inv y), h]
          exact G.rot_mem_vertexOf d₁
        rw [hcolx _ this] at hcz
        exact Shade.noConfusion hcz
      · exact absurd ((hmemX _).2 (Or.inr (Or.inr (Or.inl
          (by rw [← hσ2, ← h, Equiv.apply_symm_apply]))))) hzX
      · -- `ȳ = r = σ(d₂)`
        obtain ⟨p, hσp⟩ : ∃ p, G.rot p = G.inv d₁ := ⟨_, Equiv.apply_symm_apply _ _⟩
        have hyr : G.rot d₂ = G.inv y := by rw [← h, Equiv.apply_symm_apply]
        have hvp : G.vertexOf p = G.vertexOf d₂ := by rw [← G.vertexOf_rot p, hσp, hvy]
        have hpX : p ∉ 𝓔.biUnion id := by
          rw [hmemX]
          rintro (h' | h' | h' | h')
          · exact hxy (by rw [← h', hvp])
          · exact hd2d1' (by rw [← hσ2, ← h', hσp, h'])
          · exact hzX (by rw [← hyr, ← h', hσp, hmemX]; exact Or.inr (Or.inl rfl))
          · exact hxy (by rw [← hvx, ← h', hvp])
        have hρp : G.excisionRot 𝓔 p = G.inv y := by
          rw [excisionRot_apply_eq_rot_rot_rot hpX
            (by rw [hσp, hmemX]; exact Or.inr (Or.inl rfl))
            (by rw [hσp, hσ2, hmemX]; exact Or.inr (Or.inr (Or.inl rfl)))
            (by rwa [hσp, hσ2, hyr]), hσp, hσ2, hyr]
        have hTd2 : G.tripMap d₂ = d₁ := by
          rw [tripMap_apply, turn_of_black (by rwa [hvx]) (hcolx _ hd2x), hσ1]
        have hTd1 : G.tripMap d₁ = p := by
          rw [tripMap_apply, turn_of_white (by rwa [hvy]) (hcoly _ hd1y), ← hσp,
            Equiv.symm_apply_apply]
        have hpH : p ∈ G.excisionDarts 𝓔 := by
          rw [← excisionRot_mem_excisionDarts_iff, hρp]
          exact hzH
        refine ⟨3, 1, by norm_num, one_pos, ?_, ?_, ?_, fun j hj hj1 => by omega⟩
        · change G.tripMap (G.tripMap (G.tripMap y)) ∈ _
          rw [hT, h, hTd2, hTd1]
          exact ⟨hpH, notMem_bdry_of_mem_vertexOf hyI (by rw [← hvp]; exact G.self_mem_vertexOf _)⟩
        · intro j hj hj3
          interval_cases j
          · change G.tripMap y ∉ _
            rw [hT, h]
            exact fun hh => hXH _ ((hmemX _).2 (Or.inr (Or.inr (Or.inl rfl)))) hh.1
          · change G.tripMap (G.tripMap y) ∉ _
            rw [hT, h, hTd2]
            exact fun hh => hXH _ ((hmemX _).2 (Or.inl rfl)) hh.1
        · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) =
            G.tripMap (G.tripMap (G.tripMap y))
          rw [coe_edgeExcision_tripMap_of_white (w := ⟨y, hyH⟩) hb hcz, hT, h, hTd2, hTd1]
          change (G.excisionRot 𝓔).symm (G.inv y) = p
          rw [Equiv.symm_apply_eq, hρp]
      · exact absurd ((hmemX _).2 (Or.inl (by rw [← hσ1, ← h, Equiv.apply_symm_apply]))) hzX
    · refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
        fun j hj hj1 => by omega⟩
      · change G.tripMap y ∈ _
        rw [hT]
        refine ⟨?_, notMem_bdry_of_mem_vertexOf hb (G.rot_symm_mem_vertexOf _)⟩
        rw [← excisionRot_mem_excisionDarts_iff, ← excisionRot_symm_apply_of_notMem hzX hσX,
          Equiv.apply_symm_apply]
        exact hzH
      · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
        rw [coe_edgeExcision_tripMap_of_white (w := ⟨y, hyH⟩) hb hcz, hT]
        exact excisionRot_symm_apply_of_notMem hzX hσX
  · -- `v(ȳ)` black
    have hT : G.tripMap y = G.rot (G.inv y) := by rw [tripMap_apply, turn_of_black hb hcz]
    by_cases hσX : G.rot (G.inv y) ∈ 𝓔.biUnion id
    · rcases (hmemX _).1 hσX with h | h | h | h
      · exact absurd ((hmemX _).2 (Or.inr (Or.inr (Or.inr
          (G.rot.injective (h.trans hσ1.symm)))))) hzX
      · -- `ȳ = p` is white
        exfalso
        have hv : G.vertexOf (G.inv y) = G.vertexOf d₂ := by
          rw [← G.vertexOf_rot (G.inv y), h, hvy]
        have : G.inv y ∈ G.vertexOf d₂ := hv ▸ G.self_mem_vertexOf _
        rw [hcoly _ this] at hcz
        exact Shade.noConfusion hcz
      · exact absurd ((hmemX _).2 (Or.inr (Or.inl (G.rot.injective (h.trans hσ2.symm))))) hzX
      · -- `ȳ = s`, with `σ(s) = d̄₂`
        obtain ⟨q, hq⟩ : ∃ q, G.rot d₁ = q := ⟨_, rfl⟩
        have hvq : G.vertexOf q = G.vertexOf d₁ := by rw [← hq, G.vertexOf_rot]
        have hqX : q ∉ 𝓔.biUnion id := by
          rw [hmemX]
          rintro (h' | h' | h' | h')
          · exact hd1d2' ((G.mem_vertexOf.1 hd2x).eq_of_left (by rw [Function.IsFixedPt, hq, h']))
          · exact hxy (by rw [← hvq, h', hvy])
          · exact hxy (by rw [← hvq, h'])
          · exact hzX (by
              rw [hmemX]
              exact Or.inl (G.rot.injective (h.trans (hq.trans h').symm)))
        have hρs : G.excisionRot 𝓔 (G.inv y) = q := by
          rw [excisionRot_apply_eq_rot_rot_rot hzX
            (by rw [h, hmemX]; exact Or.inr (Or.inr (Or.inr rfl)))
            (by rw [h, hσ1, hmemX]; exact Or.inl rfl)
            (by rwa [h, hσ1, hq]), h, hσ1, hq]
        have hTd2 : G.tripMap (G.inv d₂) = G.inv d₁ := by
          rw [tripMap_apply, hinv, turn_of_white hyI hc₂, ← hσ2, Equiv.symm_apply_apply]
        have hTd1 : G.tripMap (G.inv d₁) = q := by
          rw [tripMap_apply, hinv, turn_of_black hxI hc₁, hq]
        have hqH : q ∈ G.excisionDarts 𝓔 := by
          rw [← hρs]
          exact excisionRot_mem_excisionDarts_iff.2 hzH
        refine ⟨3, 1, by norm_num, one_pos, ?_, ?_, ?_, fun j hj hj1 => by omega⟩
        · change G.tripMap (G.tripMap (G.tripMap y)) ∈ _
          rw [hT, h, hTd2, hTd1]
          exact ⟨hqH, notMem_bdry_of_mem_vertexOf hxI (by rw [← hvq]; exact G.self_mem_vertexOf _)⟩
        · intro j hj hj3
          interval_cases j
          · change G.tripMap y ∉ _
            rw [hT, h]
            exact fun hh => hXH _ ((hmemX _).2 (Or.inr (Or.inr (Or.inr rfl)))) hh.1
          · change G.tripMap (G.tripMap y) ∉ _
            rw [hT, h, hTd2]
            exact fun hh => hXH _ ((hmemX _).2 (Or.inr (Or.inl rfl))) hh.1
        · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) =
            G.tripMap (G.tripMap (G.tripMap y))
          rw [coe_edgeExcision_tripMap_of_black (w := ⟨y, hyH⟩) hb hcz, hT, h, hTd2, hTd1]
          exact hρs
    · refine ⟨1, 1, one_pos, one_pos, ?_, fun j hj hj1 => by omega, ?_,
        fun j hj hj1 => by omega⟩
      · change G.tripMap y ∈ _
        rw [hT]
        refine ⟨?_, notMem_bdry_of_mem_vertexOf hb (G.rot_mem_vertexOf _)⟩
        rw [← excisionRot_apply_of_rot_notMem hzX hσX]
        exact excisionRot_mem_excisionDarts_iff.2 hzH
      · change ((G.edgeExcision hG 𝓔 h𝓔 h𝓔B).tripMap ⟨y, _⟩ : H) = G.tripMap y
        rw [coe_edgeExcision_tripMap_of_black (w := ⟨y, hyH⟩) hb hcz, hT]
        exact excisionRot_apply_of_rot_notMem hzX hσX

/-- **Removing both sides of a bicoloured hollow digon**: if `{d₁, d₂}` is a hollow digon of the
plabic graph `G` whose two vertices have different colours, then the excision
`G ⊖ {{d₁, d̄₁}, {d₂, d̄₂}}` is a plabic graph with the trip
permutation of `G` and fewer faces than `G`. -/
@[cluster_algebras "lem_excision_bicoloured_digon"]
theorem IsPlabicGraph.edgeExcision_of_isHollowDigon_of_colour_ne {d₁ d₂ : H}
    (hd : G.IsHollowDigon {d₁, d₂}) (h𝓔 : {{d₁, G.inv d₁}, {d₂, G.inv d₂}} ⊆ G.edges)
    (h𝓔B : ∀ e ∈ ({{d₁, G.inv d₁}, {d₂, G.inv d₂}} : Finset (Finset H)), Disjoint e G.bdry)
    (hc : G.colour d₁ ≠ G.colour d₂) :
    (G.edgeExcision hG {{d₁, G.inv d₁}, {d₂, G.inv d₂}} h𝓔 h𝓔B).IsPlabicGraph ∧
      (G.edgeExcision hG {{d₁, G.inv d₁}, {d₂, G.inv d₂}} h𝓔 h𝓔B).tripPerm = G.tripPerm ∧
      (G.edgeExcision hG {{d₁, G.inv d₁}, {d₂, G.inv d₂}} h𝓔 h𝓔B).faces.card <
        G.faces.card := by
  obtain ⟨hKp, hfaces⟩ := edgeExcision_pair hG hd rfl h𝓔 h𝓔B
  refine ⟨hKp, ?_, hfaces⟩
  cases h₁ : G.colour d₁ <;> cases h₂ : G.colour d₂
  · exact absurd (h₁.trans h₂.symm) hc
  · exact tripPerm_edgeExcision_pair hG (d₁ := d₂) (d₂ := d₁) (by rwa [pair_comm]) h₂ h₁
      (pair_comm _ _) h𝓔 h𝓔B hKp
  · exact tripPerm_edgeExcision_pair hG hd h₁ h₂ rfl h𝓔 h𝓔B hKp
  · exact absurd (h₁.trans h₂.symm) hc

end Bicoloured

end PlabicData

end ClusterAlgebras
