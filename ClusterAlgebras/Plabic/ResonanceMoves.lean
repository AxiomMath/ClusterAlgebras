/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ClusterAlgebras.Plabic.Resonance
public import ClusterAlgebras.Plabic.BivalentMoves
public import ClusterAlgebras.Plabic.EdgeContractionMoves
public import ClusterAlgebras.Plabic.Reduced
public import ClusterAlgebras.Plabic.BridgeTrips
public import ClusterAlgebras.Plabic.BridgeWires

/-!
# Resonance under local moves and for bridge decompositions

Let `G` be a plabic graph. The resonance property of `G` is preserved by the local moves
between nearly leafless plabic graphs.

*Removing a bivalent vertex* `v = {d₁, d₂}` of a nearly leafless graph keeps the trip sets of the
remaining darts, since the trip map of `G_v` is the first return of that of `G`; the two darts of
`v` carry the same label, and the resonance property of `G_v` forces that label to have two
elements.

*Contracting an edge* `{d, d̄}` whose endpoints `x = (d a₁ … a_p)` and `y = (d̄ b₁ … b_q)` have at
least two darts each keeps the trip sets, labels and corner trip sets of the remaining darts. The
corner sequences read clockwise are `(α, A, β)` at `x`, `(β, C, α)` at `y` and `(α, A, β, C)` at
the merged vertex, so the resonance condition holds at both `x` and `y` if and only if it holds at
the merged vertex, by merging and splitting cyclically increasing sequences.

Together with isomorphisms and square moves, this shows that any two nearly leafless equivalent
plabic graphs have the resonance property simultaneously.

*Bridge decompositions.* In the bridge graph of a bridge sequence `s` for an `(a, b)`-bounded
affine permutation `f`, the internal vertices other than lollipops are the two ends of the
bridges. At the `t`-th bridge `(i, j)` the labels are read off the one-way trips running down the
lines: with `ω_τ = ρ_τ⁻¹` the inverses of the position maps, `a = ω_{t-1}(i)`, `c = ω_{t-1}(j)`,
`p = ω_r(i)` and `q = ω_r(j)`, the white end carries the labels `{a, p}, {a, c}, {c, p}` and the
black end `{c, q}, {a, q}, {a, c}`. Since wires keep their order while they are not at fixed
points, `a < c`, and `p` and `q` lie outside `[a, c]` unless the end is the lowest vertex of its
line, in which case the vertex has two darts with the label `{a, c}`.

## Main results

* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasResonanceProperty_iff_bivalentRemoval`: removing a
  bivalent vertex preserves resonance.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.hasResonanceProperty_iff_contractEdge`: contracting an
  edge between non-leaves preserves resonance.
* `ClusterAlgebras.PlabicGraph.IsLocalMove.hasResonanceProperty_iff`: local moves between nearly
  leafless graphs preserve resonance.
* `ClusterAlgebras.PlabicGraph.NearlyLeaflessEquivalent.hasResonanceProperty_iff`: nearly leafless
  equivalent graphs have the resonance property simultaneously.
* `ClusterAlgebras.IsBridgeSequence.hasResonanceProperty_bridgeGraph`: the bridge graph of a
  bridge sequence for a bounded affine permutation has the resonance property.
* `ClusterAlgebras.DecoratedPerm.hasResonanceProperty_bridgeDecomposition`: bridge decompositions
  have the resonance property.

## Implementation notes

* The darts of `G_v` and `G_e` form subtypes of the darts of `G`; trip sets, labels and corner
  trip sets of the two graphs are compared on these subtypes.
* At the merged vertex the corner sequences are maps `Fin m → Fin b`, read as lists by
  `List.ofFn`.
* Labels are `0`-indexed: `x : Fin b` stands for the label `x + 1` of [FWZ], and the integers
  `a, c, p, q` above are the labels `x` with `x + 1` equal to them. Pairs of a bridge sequence are
  indexed from `0`: the `t`-th pair of [FWZ] is `s[t - 1]`.
* The resonance of bridge decompositions holds for the bridge graph of any bridge sequence of a
  bounded affine permutation and any colouring of the lollipops; the bridge decomposition is the
  case of the affinization of a decorated permutation. No hypothesis `b ≥ 1` is needed: without
  bridges every internal vertex is a lollipop.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160, Section 7.11.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset Equiv Equiv.Perm Function

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-! ### Generalities -/

/-- If the trip map of `G'`, a plabic graph on a set `Y` of darts of `G` with the legs of `G`, is
the first return of the trip map of `G` to `Y`, then the trip sets agree on `Y`. -/
private theorem tripSet_eq_of_coe_tripMap (hG : G.IsPlabicGraph) {Y : Set H} [Fintype Y]
    {G' : PlabicData Y b} (hG' : G'.IsPlabicGraph) (hleg : ∀ i, (G'.leg i : H) = G.leg i)
    (hT : ∀ y, (G'.tripMap y : H) = firstReturn hG.tripEquiv Y y) (y : Y) :
    G'.tripSet y = G.tripSet y := by
  have := hG.tripSet_eq_of_firstReturn hG' (Y := Y) (Y' := (Set.univ : Set Y))
    (Equiv.Set.univ Y).symm
    (fun i => ⟨by rw [← hleg i]; exact (G'.leg i).2, Subtype.ext (hleg i).symm⟩)
    (fun z => Subtype.ext (Subtype.ext ?_)) y
  · simpa using this.symm
  · change (firstReturn hG.tripEquiv Y z : H) =
      ((firstReturn hG'.tripEquiv Set.univ ⟨z, trivial⟩ : Y) : H)
    rw [coe_firstReturn_of_apply_mem (π := hG'.tripEquiv) (Set.mem_univ _),
      IsPlabicGraph.tripEquiv_apply, hT]

private theorem rot_symm_pow_mem_vertexOf (G : PlabicData H b) (d : H) (n : ℕ) :
    (G.rot.symm ^ n) d ∈ G.vertexOf d := by
  rw [RotationSystem.mem_vertexOf]
  have : G.rot⁻¹.SameCycle d ((G.rot⁻¹ ^ n) d) := Perm.sameCycle_pow_right.2 (.refl _ _)
  exact Perm.sameCycle_inv.1 this

/-- A dart at a boundary vertex which is not in `B` is a leg. -/
private theorem IsPlabicGraph.exists_leg_eq (hG : G.IsPlabicGraph) {x : H}
    (hx : G.IsBoundaryVertex (G.vertexOf x)) (hxB : x ∉ G.bdry) : ∃ i, G.leg i = x := by
  obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hx)
  refine ⟨i, ?_⟩
  have : x ∈ (G.bvertex i).filter (· ∉ G.bdry) :=
    mem_filter.2 ⟨by rw [hi]; exact G.self_mem_vertexOf x, hxB⟩
  rw [hG.filter_bvertex_notMem_bdry, mem_singleton] at this
  exact this.symm

private theorem val_finRotate_two {m : ℕ} (hm : m = 2) (k : Fin m) :
    ((finRotate m k : Fin m) : ℕ) = ((k : ℕ) + 1) % 2 := by
  subst hm
  fin_cases k <;> rfl

/-- The resonance condition at a vertex with two darts carrying the same label of size two. -/
private theorem resonanceCondition_of_card_eq_two {a : H} (h2 : (G.vertexOf a).card = 2)
    {L : Finset (Fin b)} (hL : L.card = 2)
    (hlab : ∀ e ∈ G.vertexOf a, G.edgeLabel (G.edgeOf e) = L) :
    G.ResonanceCondition (G.vertexOf a) := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.1 hL
  wlog hlt : x < y generalizing x y
  · exact this y x hxy.symm (by rw [pair_comm]; exact card_pair hxy)
      (fun e he => by rw [hlab e he, pair_comm]) (lt_of_le_of_ne (not_lt.1 hlt) hxy.symm)
  refine ⟨h2.ge, a, G.self_mem_vertexOf a, fun k => if (k : ℕ) = 0 then x else y,
    fun k k' hkk' => ?_, fun k => ?_⟩
  · have hk : (k : ℕ) < (k' : ℕ) := hkk'
    have hk' : (k' : ℕ) < 2 := h2 ▸ k'.2
    simpa only [show (k : ℕ) = 0 by omega, show (k' : ℕ) ≠ 0 by omega, ite_true, ite_false]
      using hlt
  · rw [hlab _ (rot_symm_pow_mem_vertexOf G a k)]
    have hk : (k : ℕ) < 2 := h2 ▸ k.2
    have hrot := val_finRotate_two h2 k
    change _ = {if (k : ℕ) = 0 then x else y, if ((finRotate _ k : Fin _) : ℕ) = 0 then x else y}
    rcases (by omega : (k : ℕ) = 0 ∨ (k : ℕ) = 1) with h0 | h1
    · rw [hrot, h0]
      simp
    · rw [hrot, h1]
      simp [pair_comm]

/-- The dart of a lollipop runs to a boundary vertex. -/
private theorem IsLollipop.isBoundaryVertex_inv (hG : G.IsPlabicGraph) {i : Fin b} {a : H}
    (h : G.IsLollipop i (G.vertexOf a)) : G.IsBoundaryVertex (G.vertexOf (G.inv a)) := by
  obtain ⟨⟨-, hcard⟩, e, he, hei⟩ := h
  obtain ⟨c, hc⟩ := card_eq_one.1 hcard
  obtain rfl : e = a := by
    have ha := G.self_mem_vertexOf a
    rw [hc, mem_singleton] at he ha
    rw [he, ha]
  rw [G.vertexOf_eq_of_mem hei]
  exact G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i)

/-- In a nearly leafless graph, an internal vertex which is not a lollipop has at least two
darts. -/
private theorem two_le_card_of_isNearlyLeafless (hnl : G.IsNearlyLeafless) {a : H}
    (ha : ¬G.IsBoundaryVertex (G.vertexOf a)) (hlol : ∀ i, ¬G.IsLollipop i (G.vertexOf a)) :
    2 ≤ (G.vertexOf a).card := by
  by_contra hlt
  have h1 : (G.vertexOf a).card = 1 :=
    le_antisymm (by omega) (card_pos.2 ⟨a, G.self_mem_vertexOf a⟩)
  obtain ⟨i, hi⟩ := hnl _ ⟨G.vertexOf_mem_internalVertices.2 ha, h1⟩
  exact hlol i hi

/-! ### Removing a bivalent vertex -/

section Bivalent

variable {d : H} (hG : G.IsPlabicGraph) (hd : G.IsBivalentRemovable d)

private theorem tripSet_bivalentRemoval (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).tripSet y = G.tripSet y :=
  tripSet_eq_of_coe_tripMap hG (isPlabicGraph_bivalentRemoval hG hd)
    (coe_bivalentRemoval_leg hG hd) (coe_bivalentRemoval_tripMap hG hd) y

/-- The removal of a bivalent vertex keeps the labels of the remaining darts. -/
private theorem edgeLabel_bivalentRemoval (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).edgeLabel ((G.bivalentRemoval hG hd).edgeOf y) =
      G.edgeLabel (G.edgeOf y) := by
  have hT1 : G.tripMap (G.inv d) = G.rot d := by
    rw [tripMap_apply, hG.inv_involutive, hd.turn_eq_rot]
  have hT2 : G.tripMap (G.inv (G.rot d)) = d := by
    rw [tripMap_apply, hG.inv_involutive, hd.turn_rot]
  have hnl : ∀ e ∈ G.vertexOf d, ¬G.IsLeg e := fun e he =>
    hG.not_isLeg_of_not_isBoundaryVertex
      (by rw [G.vertexOf_eq_of_mem he]; exact hd.not_isBoundaryVertex)
  have e1 : G.tripSet d = G.tripSet (G.inv (G.rot d)) := by
    have := hG.tripSet_tripMap (d := G.inv (G.rot d))
      (by rw [hT2]; exact hnl _ (G.self_mem_vertexOf d))
    rwa [hT2] at this
  have e2 : G.tripSet (G.rot d) = G.tripSet (G.inv d) := by
    have := hG.tripSet_tripMap (d := G.inv d) (by rw [hT1]; exact hnl _ (G.rot_mem_vertexOf d))
    rwa [hT1] at this
  rw [edgeLabel_edgeOf, edgeLabel_edgeOf, tripSet_bivalentRemoval, tripSet_bivalentRemoval]
  by_cases h₁ : (y : H) = G.inv d
  · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁, h₁, hG.inv_involutive, e1]
  by_cases h₂ : (y : H) = G.inv (G.rot d)
  · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂, h₂, hG.inv_involutive, e2]
  rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]

private theorem coe_bivalentRemoval_rot_symm_pow (y : ({d, G.rot d}ᶜ : Set H)) (n : ℕ) :
    (((G.bivalentRemoval hG hd).rot.symm ^ n) y : H) = (G.rot.symm ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply, ← ih]
    apply G.rot.injective
    rw [Equiv.apply_symm_apply, ← coe_bivalentRemoval_rot hG hd, Equiv.apply_symm_apply]

private theorem edgeLabel_bivalentRemoval_rot_symm_pow (y : ({d, G.rot d}ᶜ : Set H)) (n : ℕ) :
    (G.bivalentRemoval hG hd).edgeLabel
        ((G.bivalentRemoval hG hd).edgeOf (((G.bivalentRemoval hG hd).rot.symm ^ n) y)) =
      G.edgeLabel (G.edgeOf ((G.rot.symm ^ n) y)) := by
  rw [edgeLabel_bivalentRemoval, coe_bivalentRemoval_rot_symm_pow]

private theorem card_bivalentRemoval_vertexOf (y : ({d, G.rot d}ᶜ : Set H)) :
    ((G.bivalentRemoval hG hd).vertexOf y).card = (G.vertexOf y).card := by
  rw [← map_bivalentRemoval_vertexOf hG hd y, card_map]

private theorem vertexOf_mem_internalVertices_bivalentRemoval_iff
    (y : ({d, G.rot d}ᶜ : Set H)) :
    (G.bivalentRemoval hG hd).vertexOf y ∈ (G.bivalentRemoval hG hd).internalVertices ↔
      G.vertexOf y ∈ G.internalVertices := by
  rw [DiskMap.vertexOf_mem_internalVertices, DiskMap.vertexOf_mem_internalVertices,
    isBoundaryVertex_bivalentRemoval_vertexOf_iff hG hd]

/-- A lollipop of `G` other than `v` is a lollipop of `G_v`. -/
private theorem isLollipop_bivalentRemoval {y : ({d, G.rot d}ᶜ : Set H)} {i : Fin b}
    (h : G.IsLollipop i (G.vertexOf y)) :
    (G.bivalentRemoval hG hd).IsLollipop i ((G.bivalentRemoval hG hd).vertexOf y) := by
  have hb := h.isBoundaryVertex_inv hG
  obtain ⟨⟨hv, hcard⟩, e, he, hei⟩ := h
  obtain ⟨c, hc⟩ := card_eq_one.1 hcard
  obtain rfl : e = y := by
    have hy := G.self_mem_vertexOf (y : H)
    rw [hc, mem_singleton] at he hy
    rw [he, hy]
  have h₁ : (y : H) ≠ G.inv d := fun h' => by
    rw [h', hG.inv_involutive] at hb
    exact hd.not_isBoundaryVertex hb
  have h₂ : (y : H) ≠ G.inv (G.rot d) := fun h' => by
    rw [h', hG.inv_involutive, G.vertexOf_rot] at hb
    exact hd.not_isBoundaryVertex hb
  refine ⟨⟨(vertexOf_mem_internalVertices_bivalentRemoval_iff hG hd y).2 hv, ?_⟩, y,
    (G.bivalentRemoval hG hd).self_mem_vertexOf y, ?_⟩
  · rwa [card_bivalentRemoval_vertexOf]
  · rwa [← mem_map' (Embedding.subtype _), map_bivalentRemoval_bvertex hG hd,
      Embedding.coe_subtype, coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]

/-- If `G_v` has the resonance property, it holds at the vertex of every dart of `G_v` whose
vertex in `G` is internal with at least two darts. -/
private theorem resonanceCondition_bivalentRemoval_of_two_le
    (h : (G.bivalentRemoval hG hd).HasResonanceProperty) (x : ({d, G.rot d}ᶜ : Set H))
    (hx : G.vertexOf x ∈ G.internalVertices) (h2 : 2 ≤ (G.vertexOf x).card) :
    (G.bivalentRemoval hG hd).ResonanceCondition ((G.bivalentRemoval hG hd).vertexOf x) :=
  h _ ((vertexOf_mem_internalVertices_bivalentRemoval_iff hG hd x).2 hx) fun i hl => by
    have := hl.1.2
    rw [card_bivalentRemoval_vertexOf] at this
    omega

/-- If `G_v` has the resonance property, the resonance condition holds at the removed vertex
`v` of `G`. -/
private theorem resonanceCondition_vertexOf_of_bivalentRemoval (hnl : G.IsNearlyLeafless)
    (h : (G.bivalentRemoval hG hd).HasResonanceProperty) : G.ResonanceCondition (G.vertexOf d) := by
  have hG' : (G.bivalentRemoval hG hd).IsPlabicGraph := isPlabicGraph_bivalentRemoval hG hd
  have hRC := resonanceCondition_bivalentRemoval_of_two_le hG hd h
  let x₁ : ({d, G.rot d}ᶜ : Set H) := ⟨G.inv d, hd.inv_mem hG⟩
  let x₂ : ({d, G.rot d}ᶜ : Set H) := ⟨G.inv (G.rot d), hd.inv_rot_mem hG⟩
  have hx12 : (G.bivalentRemoval hG hd).inv x₁ = x₂ :=
    Subtype.ext (coe_bivalentRemoval_inv_of_eq_inv hG hd rfl)
  have hlab₁ : G.edgeLabel (G.edgeOf d) =
      (G.bivalentRemoval hG hd).edgeLabel ((G.bivalentRemoval hG hd).edgeOf x₁) := by
    rw [edgeLabel_bivalentRemoval]
    exact (hG.edgeLabel_edgeOf_inv d).symm
  have hlab₂ : G.edgeLabel (G.edgeOf (G.rot d)) =
      (G.bivalentRemoval hG hd).edgeLabel ((G.bivalentRemoval hG hd).edgeOf x₁) := by
    rw [← hG'.edgeLabel_edgeOf_inv x₁, hx12, edgeLabel_bivalentRemoval]
    exact (hG.edgeLabel_edgeOf_inv _).symm
  have hcardx : ∀ x : ({d, G.rot d}ᶜ : Set H), G.vertexOf (G.inv x) = G.vertexOf d →
      ¬G.IsBoundaryVertex (G.vertexOf x) →
      ((G.bivalentRemoval hG hd).edgeLabel ((G.bivalentRemoval hG hd).edgeOf x)).card = 2 := by
    intro x hvx hb
    have h2 := two_le_card_of_isNearlyLeafless hnl hb fun i hl =>
      hd.not_isBoundaryVertex (by rw [← hvx]; exact hl.isBoundaryVertex_inv hG)
    exact (hRC x (G.vertexOf_mem_internalVertices.2 hb) h2).card_edgeLabel
      ((G.bivalentRemoval hG hd).self_mem_vertexOf x)
  have hcard : ((G.bivalentRemoval hG hd).edgeLabel
      ((G.bivalentRemoval hG hd).edgeOf x₁)).card = 2 := by
    by_cases hb₁ : G.IsBoundaryVertex (G.vertexOf (G.inv d))
    · by_cases hb₂ : G.IsBoundaryVertex (G.vertexOf (G.inv (G.rot d)))
      · obtain ⟨i, hi⟩ := hG.exists_leg_eq hb₁ (hd.inv_notMem_bdry hG)
        obtain ⟨j, hj⟩ := hG.exists_leg_eq hb₂ (hd.inv_rot_notMem_bdry hG)
        rw [edgeLabel_edgeOf, hx12, tripSet_bivalentRemoval, tripSet_bivalentRemoval]
        change (G.tripSet (G.inv d) ∪ G.tripSet (G.inv (G.rot d))).card = 2
        rw [← hi, ← hj, hG.tripSet_leg, hG.tripSet_leg, ← insert_eq]
        exact card_pair fun hij => hd.inv_ne_inv_rot (by rw [← hi, ← hj, hij])
      · rw [← hG'.edgeLabel_edgeOf_inv, hx12]
        exact hcardx x₂ (by
          change G.vertexOf (G.inv (G.inv (G.rot d))) = _
          rw [hG.inv_involutive, G.vertexOf_rot]) hb₂
    · refine hcardx x₁ ?_ hb₁
      change G.vertexOf (G.inv (G.inv d)) = _
      rw [hG.inv_involutive]
  refine resonanceCondition_of_card_eq_two hd.card_vertexOf hcard fun e he => ?_
  rcases hd.mem_vertexOf_iff.1 he with rfl | rfl
  exacts [hlab₁, hlab₂]

end Bivalent

/-- If `G` is a nearly leafless plabic graph and `v = {d₁, d₂}` an internal vertex of `G` with
`d₂ = σ d₁` and `d̄₁ ≠ d₂`, then `G` has the resonance property if and only if the removal `G_v`
of `v` has. The vertex is given by its dart `d = d₁`. -/
@[cluster_algebras "lem_resonance_bivalent_removal"]
theorem IsPlabicGraph.hasResonanceProperty_iff_bivalentRemoval (hG : G.IsPlabicGraph)
    (hnl : G.IsNearlyLeafless) {d : H} (hd : G.IsBivalentRemovable d) :
    G.HasResonanceProperty ↔ (G.bivalentRemoval hG hd).HasResonanceProperty := by
  constructor
  · intro h w hw hlol
    obtain ⟨hwV, -⟩ := (G.bivalentRemoval hG hd).mem_internalVertices.1 hw
    obtain ⟨a, rfl⟩ := (G.bivalentRemoval hG hd).mem_vertices.1 hwV
    have hres := h _ ((vertexOf_mem_internalVertices_bivalentRemoval_iff hG hd a).1 hw)
      fun i hl => hlol i (isLollipop_bivalentRemoval hG hd hl)
    exact hres.of_edgeLabel_eq (card_bivalentRemoval_vertexOf hG hd a)
      (edgeLabel_bivalentRemoval_rot_symm_pow hG hd a)
  · intro h w hw hlol
    obtain ⟨hwV, hwB⟩ := G.mem_internalVertices.1 hw
    obtain ⟨a, rfl⟩ := G.mem_vertices.1 hwV
    by_cases ha : a ∈ ({d, G.rot d}ᶜ : Set H)
    · exact (resonanceCondition_bivalentRemoval_of_two_le hG hd h ⟨a, ha⟩ hw
        (two_le_card_of_isNearlyLeafless hnl hwB hlol)).of_edgeLabel_eq
          (card_bivalentRemoval_vertexOf hG hd ⟨a, ha⟩).symm
          fun n => (edgeLabel_bivalentRemoval_rot_symm_pow hG hd ⟨a, ha⟩ n).symm
    · have hva : G.vertexOf a = G.vertexOf d := by
        rcases notMem_compl_pair_iff.1 ha with rfl | rfl
        exacts [rfl, G.vertexOf_rot d]
      rw [hva]
      exact resonanceCondition_vertexOf_of_bivalentRemoval hG hd hnl h

/-! ### Darts around a vertex -/

section Orbit

variable {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α) (x : α)

omit [Fintype α] [DecidableEq α] in
/-- If `g^n` fixes `x`, then `g^m x` only depends on `m` modulo `n`. -/
private theorem pow_mod_apply_of_pow_apply_eq {g : Perm α} {x : α} {n : ℕ} (h : (g ^ n) x = x)
    (m : ℕ) : (g ^ (m % n)) x = (g ^ m) x := by
  have hpp : Function.IsPeriodicPt g n x := by
    change (⇑g)^[n] x = x
    rwa [Perm.iterate_eq_pow]
  simpa only [Perm.iterate_eq_pow] using hpp.iterate_mod_apply m

private theorem pow_apply_injective_of_lt_card {i j : ℕ}
    (hi : i < (univ.filter (g.SameCycle x)).card) (hj : j < (univ.filter (g.SameCycle x)).card)
    (h : (g ^ i) x = (g ^ j) x) : i = j := by
  wlog hij : i < j generalizing i j
  · rcases Nat.lt_or_ge j i with h' | h'
    · exact (this hj hi h.symm h').symm
    · omega
  have hper : (g ^ (j - i)) ((g ^ i) x) = (g ^ i) x := by
    rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij.le]
    exact h.symm
  have hsub : univ.filter (g.SameCycle x) ⊆
      (range (j - i)).image fun k => (g ^ k) ((g ^ i) x) := by
    intro y hy
    have hy' : g.SameCycle ((g ^ i) x) y := Perm.sameCycle_pow_left.2 (mem_filter.1 hy).2
    obtain ⟨N, hN⟩ := hy'.exists_nat_pow_eq
    exact mem_image.2 ⟨N % (j - i), mem_range.2 (Nat.mod_lt _ (by omega)),
      (pow_mod_apply_of_pow_apply_eq hper N).trans hN⟩
  have := (card_le_card hsub).trans card_image_le
  rw [card_range] at this
  omega

private theorem exists_pow_apply_eq_of_lt_card {y : α} (hy : g.SameCycle x y) :
    ∃ k < (univ.filter (g.SameCycle x)).card, (g ^ k) x = y := by
  have hsub : (range (univ.filter (g.SameCycle x)).card).image (fun k => (g ^ k) x) ⊆
      univ.filter (g.SameCycle x) := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := mem_image.1 hz
    exact mem_filter.2 ⟨mem_univ _, Perm.sameCycle_pow_right.2 (.refl _ _)⟩
  have hcard : ((range (univ.filter (g.SameCycle x)).card).image (fun k => (g ^ k) x)).card =
      (univ.filter (g.SameCycle x)).card := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact pow_apply_injective_of_lt_card g x (mem_range.1 hi) (mem_range.1 hj) h
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard])
  have hmem : y ∈ univ.filter (g.SameCycle x) := mem_filter.2 ⟨mem_univ _, hy⟩
  rw [← heq] at hmem
  obtain ⟨k, hk, rfl⟩ := mem_image.1 hmem
  exact ⟨k, mem_range.1 hk, rfl⟩

private theorem pow_card_filter_sameCycle_apply :
    (g ^ (univ.filter (g.SameCycle x)).card) x = x := by
  have hpos : 0 < (univ.filter (g.SameCycle x)).card :=
    card_pos.2 ⟨x, mem_filter.2 ⟨mem_univ _, .refl _ _⟩⟩
  obtain ⟨k, hk, hkx⟩ := exists_pow_apply_eq_of_lt_card g x
    (Perm.sameCycle_pow_right.2 (.refl g x) :
      g.SameCycle x ((g ^ (univ.filter (g.SameCycle x)).card) x))
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [← hkx, pow_zero, Perm.one_apply]
  · exfalso
    have h1 : (g ^ ((univ.filter (g.SameCycle x)).card - k)) x = (g ^ 0) x := by
      apply (g ^ k).injective
      rw [show (g ^ k) ((g ^ ((univ.filter (g.SameCycle x)).card - k)) x) =
          (g ^ (univ.filter (g.SameCycle x)).card) x by
        rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hk.le], pow_zero,
        Perm.one_apply, hkx]
    have := pow_apply_injective_of_lt_card g x (by omega) hpos h1
    omega

end Orbit

private theorem vertexOf_eq_filter_rot_symm (G : PlabicData H b) (a : H) :
    G.vertexOf a = univ.filter (Perm.SameCycle G.rot.symm a) := by
  ext y
  rw [RotationSystem.mem_vertexOf, mem_filter, ← Perm.inv_def, Perm.sameCycle_inv]
  simp

/-- Turning `|v(a)|` times clockwise around `v(a)` comes back to `a`. -/
private theorem rot_symm_pow_card_vertexOf (G : PlabicData H b) (a : H) :
    (G.rot.symm ^ (G.vertexOf a).card) a = a := by
  rw [vertexOf_eq_filter_rot_symm]
  exact pow_card_filter_sameCycle_apply _ _

/-- `σ^{-k}(a) ≠ a` for `0 < k < |v(a)|`. -/
private theorem rot_symm_pow_ne_self (G : PlabicData H b) {a : H} {k : ℕ} (hk0 : 0 < k)
    (hk : k < (G.vertexOf a).card) : (G.rot.symm ^ k) a ≠ a := fun h => by
  rw [vertexOf_eq_filter_rot_symm] at hk
  have := pow_apply_injective_of_lt_card _ _ hk (j := 0) (by omega) (by rwa [pow_zero])
  omega

/-- `σ(a) = σ^{-(|v(a)| - 1)}(a)`. -/
private theorem rot_eq_rot_symm_pow (G : PlabicData H b) (a : H) :
    G.rot a = (G.rot.symm ^ ((G.vertexOf a).card - 1)) a := by
  have hpos : 0 < (G.vertexOf a).card := card_pos.2 ⟨a, G.self_mem_vertexOf a⟩
  have h := rot_symm_pow_card_vertexOf G a
  rw [show (G.vertexOf a).card = ((G.vertexOf a).card - 1) + 1 by omega, pow_succ',
    Perm.mul_apply] at h
  exact ((Equiv.symm_apply_eq _).1 h).symm

omit [Fintype H] [DecidableEq H] in
private theorem rot_rot_symm_pow_succ (G : PlabicData H b) (a : H) (k : ℕ) :
    G.rot ((G.rot.symm ^ (k + 1)) a) = (G.rot.symm ^ k) a := by
  rw [pow_succ', Perm.mul_apply, Equiv.apply_symm_apply]

/-! ### Contracting an edge -/

/-- Gluing the corner sequences of the two endpoints of a contracted edge: if
`(c₀, …, c_{m-1}) = (α, A, β)` and `(c'₀, …, c'_{n-1}) = (β, C, α)`, and `c''` lists
`α, A, β, C`, then `c''` is cyclically increasing if and only if both `c` and `c'` are. -/
private theorem cyclicallyIncreasing_ofFn_glue {α : Type*} [LinearOrder α] {m n k : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hk : k = m + n - 2)
    (cx : Fin m → α) (cy : Fin n → α) (cz : Fin k → α)
    (hz : ∀ i : Fin k, cz i =
      if h : (i : ℕ) < m then cx ⟨i, h⟩ else cy ⟨i + 1 - m, by have := i.2; omega⟩)
    (h₁ : cx ⟨m - 1, by omega⟩ = cy ⟨0, by omega⟩)
    (h₂ : cy ⟨n - 1, by omega⟩ = cx ⟨0, by omega⟩) :
    CyclicallyIncreasing (List.ofFn cz) ↔
      CyclicallyIncreasing (List.ofFn cx) ∧ CyclicallyIncreasing (List.ofFn cy) := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 2 := ⟨n - 2, by omega⟩
  subst hk
  set A := List.ofFn fun j : Fin p => cx j.castSucc.succ
  set C := List.ofFn fun j : Fin q => cy j.castSucc.succ
  have ex : List.ofFn cx = cx 0 :: (A ++ [cx (Fin.last (p + 1))]) := by
    rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append]
    rfl
  have ey : List.ofFn cy = cx (Fin.last (p + 1)) :: (C ++ [cx 0]) := by
    rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append]
    have e1 : cy 0 = cx (Fin.last (p + 1)) := h₁.symm
    have e2 : cy (Fin.last q).succ = cx 0 := h₂
    rw [e1, e2]
  have ez : List.ofFn cz = List.ofFn cx ++ C := by
    rw [List.ofFn_congr (show p + 2 + (q + 2) - 2 = p + 2 + q by omega), List.ofFn_add]
    congr 1
    · congr 1
      funext i
      rw [hz, dite_eq_left (by simp)]
      rfl
    · congr 1
      funext j
      rw [hz, dite_eq_right (by simp)]
      congr 1
      ext
      simp
      omega
  rw [ez, ex, ey]
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  constructor
  · intro h
    refine ⟨h.of_sublist ?_ (by simp), ?_⟩
    · exact List.Sublist.cons_cons _ (List.Sublist.append_left (by simp) _)
    · refine h.of_sublist_rotate (A.length + 1) ?_ (by simp)
      have : (cx 0 :: (A ++ cx (Fin.last (p + 1)) :: C)).rotate (A.length + 1) =
          cx (Fin.last (p + 1)) :: C ++ cx 0 :: A := by
        simp
      rw [this]
      simp
  · rintro ⟨hA, hB⟩
    simpa using CyclicallyIncreasing.merge (a := cx 0) (b := cx (Fin.last (p + 1))) (A := A)
      (B := C) (by simpa using hA) (by simpa using hB)

/-- `σ^{-n}(a) = σ^{-(n mod m)}(a)` for the number `m` of darts at `v(a)`. -/
private theorem rot_symm_pow_mod_card (G : PlabicData H b) (a : H) (n : ℕ) :
    (G.rot.symm ^ (n % (G.vertexOf a).card)) a = (G.rot.symm ^ n) a :=
  pow_mod_apply_of_pow_apply_eq (rot_symm_pow_card_vertexOf G a) n

/-- Every dart of `v(a)` is `σ^{-k}(a)` for some `k` less than the number of darts. -/
private theorem exists_lt_rot_symm_pow_eq (G : PlabicData H b) {a e : H}
    (he : e ∈ G.vertexOf a) : ∃ k < (G.vertexOf a).card, (G.rot.symm ^ k) a = e := by
  rw [RotationSystem.mem_vertexOf] at he
  obtain ⟨n, hn⟩ := (Perm.sameCycle_inv.2 he).exists_nat_pow_eq
  exact ⟨n % (G.vertexOf a).card, Nat.mod_lt _ (card_pos.2 ⟨a, G.self_mem_vertexOf a⟩),
    (rot_symm_pow_mod_card G a n).trans hn⟩

/-- The resonance condition through the corners read clockwise from one given dart. -/
private theorem IsPlabicGraph.resonanceCondition_iff_exists (hG : G.IsPlabicGraph) {a : H}
    (ha : ¬G.IsBoundaryVertex (G.vertexOf a)) :
    G.ResonanceCondition (G.vertexOf a) ↔ 2 ≤ (G.vertexOf a).card ∧
      ∃ c : Fin (G.vertexOf a).card → Fin b,
        (∀ k : Fin (G.vertexOf a).card, G.cornerTripSet ((G.rot.symm ^ (k : ℕ)) a) = {c k}) ∧
          CyclicallyIncreasing (List.ofFn c) := by
  rw [hG.resonanceCondition_iff_cornerTripSet ((DiskMap.vertexOf_mem_internalVertices _).2 ha)]
  constructor
  · rintro ⟨h2, -, h⟩
    exact ⟨h2, h a (G.self_mem_vertexOf a)⟩
  · rintro ⟨h2, c, hc, hci⟩
    have hpos : 0 < (G.vertexOf a).card := by omega
    refine ⟨h2, fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := exists_lt_rot_symm_pow_eq G he
      rw [hc ⟨k, hk⟩, card_singleton]
    · obtain ⟨t, -, rfl⟩ := exists_lt_rot_symm_pow_eq G he
      refine ⟨fun k => c ⟨((k : ℕ) + t) % (G.vertexOf a).card, Nat.mod_lt _ hpos⟩,
        fun k => ?_, ?_⟩
      · rw [← Perm.mul_apply, ← pow_add, ← rot_symm_pow_mod_card G a]
        exact hc ⟨_, Nat.mod_lt _ hpos⟩
      · have : List.ofFn (fun k : Fin (G.vertexOf a).card =>
            c ⟨((k : ℕ) + t) % (G.vertexOf a).card, Nat.mod_lt _ hpos⟩) =
            (List.ofFn c).rotate t := by
          refine List.ext_getElem (by simp) fun n h1 h2 => ?_
          simp [List.getElem_rotate]
        rw [this]
        exact hci.rotate t

section Contraction

variable {d : H} (hG : G.IsPlabicGraph) (he : G.IsContractibleEdge d)
  {hleg : ∀ i, G.leg i ∈ ({d, G.inv d} : Set H)ᶜ}

include hG he

private theorem tripSet_contractEdge (y : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).tripSet y = G.tripSet y :=
  tripSet_eq_of_coe_tripMap hG (hG.contractEdge he) coe_contractEdge_leg
    (coe_contractEdge_tripMap hG he) y

/-- The contraction keeps the labels of the remaining darts. -/
private theorem edgeLabel_contractEdge (y : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).edgeLabel ((G.contractEdge d hleg).edgeOf y) =
      G.edgeLabel (G.edgeOf y) := by
  rw [edgeLabel_edgeOf, edgeLabel_edgeOf, tripSet_contractEdge hG he, tripSet_contractEdge hG he,
    coe_contractEdge_inv hG.inv_involutive]

/-- The contraction keeps the corner trip sets of the remaining darts. -/
private theorem cornerTripSet_contractEdge (y : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).cornerTripSet y = G.cornerTripSet y := by
  cases hc : G.colour y
  · rw [cornerTripSet_of_white (by rw [contractEdge_colour, hc]), cornerTripSet_of_white hc,
      tripSet_contractEdge hG he, coe_contractEdge_inv hG.inv_involutive]
  · rw [cornerTripSet_of_black (by rw [contractEdge_colour, hc]), cornerTripSet_of_black hc,
      tripSet_contractEdge hG he]

omit hG he in
/-- Away from the endpoints of the edge, the rotation of the contraction is that of `G`. -/
private theorem coe_contractEdge_rot_symm_pow_of_notMem
    {a : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (ha : (a : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) (n : ℕ) :
    (((G.contractEdge d hleg).rot.symm ^ n) a : H) = (G.rot.symm ^ n) a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hw : ∀ k, (G.rot.symm ^ k) (a : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) := fun k => by
      rwa [mem_union_vertexOf_iff_of_vertexOf_eq
        (G.vertexOf_eq_of_mem (rot_symm_pow_mem_vertexOf G _ _))]
    have hr : (G.contractEdge d hleg).rot ⟨(G.rot.symm ^ (n + 1)) a,
        mem_compl_pair_of_notMem (hw (n + 1))⟩ = ((G.contractEdge d hleg).rot.symm ^ n) a := by
      apply Subtype.ext
      rw [coe_contractEdge_rot_of_mem, rot_rot_symm_pow_succ G, ih]
      rw [rot_rot_symm_pow_succ G]
      exact mem_compl_pair_of_notMem (hw n)
    rw [pow_succ', Perm.mul_apply, ← hr, Equiv.symm_apply_apply]

omit hG in
private theorem map_vertexOf_contractEdge_of_notMem' {a : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (ha : (a : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).vertexOf a).map (Embedding.subtype _) = G.vertexOf a :=
  map_vertexOf_contractEdge_of_notMem he.not_sameCycle ha

omit hG in
private theorem card_vertexOf_contractEdge_of_notMem {a : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (ha : (a : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).vertexOf a).card = (G.vertexOf a).card := by
  rw [← map_vertexOf_contractEdge_of_notMem' he ha, card_map]

omit hG in
private theorem vertexOf_mem_internalVertices_contractEdge_iff
    (a : (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).vertexOf a ∈ (G.contractEdge d hleg).internalVertices ↔
      G.vertexOf a ∈ G.internalVertices := by
  rw [DiskMap.vertexOf_mem_internalVertices, DiskMap.vertexOf_mem_internalVertices,
    isBoundaryVertex_vertexOf_contractEdge_iff he]

/-- Away from the endpoints of the edge, the lollipops of the contraction are those of `G`. -/
private theorem isLollipop_contractEdge_iff {a : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (ha : (a : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d)) (i : Fin b) :
    (G.contractEdge d hleg).IsLollipop i ((G.contractEdge d hleg).vertexOf a) ↔
      G.IsLollipop i (G.vertexOf a) := by
  have hmap := map_vertexOf_contractEdge_of_notMem' (hleg := hleg) he ha
  have hbv := map_bvertex_contractEdge (hleg := hleg) hG he i
  constructor
  · rintro ⟨⟨hv, hcard⟩, e, he', hei⟩
    refine ⟨⟨(vertexOf_mem_internalVertices_contractEdge_iff he a).1 hv,
      by rwa [← card_vertexOf_contractEdge_of_notMem he ha]⟩, e, ?_, ?_⟩
    · rw [← hmap]
      exact mem_map_of_mem _ he'
    · rw [← hbv, ← coe_contractEdge_inv hG.inv_involutive (hleg := hleg)]
      exact mem_map_of_mem (Embedding.subtype _) hei
  · rintro ⟨⟨hv, hcard⟩, e, he', hei⟩
    have heY : e ∈ ({d, G.inv d} : Set H)ᶜ := mem_compl_pair_of_notMem (by
      rwa [mem_union_vertexOf_iff_of_vertexOf_eq (G.vertexOf_eq_of_mem he')])
    refine ⟨⟨(vertexOf_mem_internalVertices_contractEdge_iff he a).2 hv,
      by rwa [card_vertexOf_contractEdge_of_notMem he ha]⟩, ⟨e, heY⟩, ?_, ?_⟩
    · rw [← mem_map' (Embedding.subtype _), hmap]
      exact he'
    · rw [← mem_map' (Embedding.subtype _), hbv, Embedding.coe_subtype,
        coe_contractEdge_inv hG.inv_involutive]
      exact hei

/-- The two corner identities at the contracted edge: `cr(σ d̄) = cr(d)` and `cr(σ d) = cr(d̄)`. -/
private theorem cornerTripSet_rot_inv_eq :
    G.cornerTripSet (G.rot (G.inv d)) = G.cornerTripSet d ∧
      G.cornerTripSet (G.rot d) = G.cornerTripSet (G.inv d) := by
  have hinv := hG.inv_involutive
  have hU : ∀ z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d), ¬G.IsBoundaryVertex (G.vertexOf z) :=
    fun z hz hb => he.notMem_of_isBoundaryVertex hb hz
  have hκ : ∀ z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d), G.colour z = G.colour d :=
    fun z hz => colour_eq_of_mem_union hG he hz
  have hd : d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) := mem_union_left _ (G.self_mem_vertexOf _)
  have hd' : G.inv d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    mem_union_right _ (G.self_mem_vertexOf _)
  have hb1 : G.rot (G.inv d) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    mem_union_right _ (G.rot_mem_vertexOf _)
  have ha1 : G.rot d ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    mem_union_left _ (G.rot_mem_vertexOf _)
  have hleg' : ∀ z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d), ¬G.IsLeg z :=
    fun z hz => hG.not_isLeg_of_not_isBoundaryVertex (hU z hz)
  cases hc : G.colour d
  · have hw : ∀ z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d), G.colour z = .white :=
      fun z hz => (hκ z hz).trans hc
    rw [cornerTripSet_of_white (hw _ hb1), cornerTripSet_of_white (hw _ hd),
      cornerTripSet_of_white (hw _ ha1), cornerTripSet_of_white (hw _ hd'), hinv]
    have t1 : G.tripMap (G.inv (G.rot (G.inv d))) = G.inv d := by
      rw [tripMap_apply, hinv, turn_of_white (hU _ hb1) (hw _ hb1), Equiv.symm_apply_apply]
    have t2 : G.tripMap (G.inv (G.rot d)) = d := by
      rw [tripMap_apply, hinv, turn_of_white (hU _ ha1) (hw _ ha1), Equiv.symm_apply_apply]
    have e1 := hG.tripSet_tripMap (d := G.inv (G.rot (G.inv d))) (by rw [t1]; exact hleg' _ hd')
    have e2 := hG.tripSet_tripMap (d := G.inv (G.rot d)) (by rw [t2]; exact hleg' _ hd)
    rw [t1] at e1
    rw [t2] at e2
    exact ⟨e1.symm, e2.symm⟩
  · have hk : ∀ z ∈ G.vertexOf d ∪ G.vertexOf (G.inv d), G.colour z = .black :=
      fun z hz => (hκ z hz).trans hc
    rw [cornerTripSet_of_black (hk _ hb1), cornerTripSet_of_black (hk _ hd),
      cornerTripSet_of_black (hk _ ha1), cornerTripSet_of_black (hk _ hd')]
    have t1 : G.tripMap d = G.rot (G.inv d) := by
      rw [tripMap_apply, turn_of_black (hU _ hd') (hk _ hd')]
    have t2 : G.tripMap (G.inv d) = G.rot d := by
      rw [tripMap_apply, hinv, turn_of_black (hU _ hd) (hk _ hd)]
    have e1 := hG.tripSet_tripMap (d := d) (by rw [t1]; exact hleg' _ hb1)
    have e2 := hG.tripSet_tripMap (d := G.inv d) (by rw [t2]; exact hleg' _ ha1)
    rw [t1] at e1
    rw [t2] at e2
    exact ⟨e1, e2⟩

omit hG in
private theorem rot_symm_pow_mem_compl {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < (G.vertexOf d).card) :
    (G.rot.symm ^ k) d ∈ ({d, G.inv d} : Set H)ᶜ := by
  refine mem_compl_pair_iff.2 ⟨rot_symm_pow_ne_self G (by omega) hk2, fun h => ?_⟩
  have := G.vertexOf_eq_of_mem (rot_symm_pow_mem_vertexOf G d k)
  rw [h] at this
  exact he.vertexOf_ne this.symm

omit hG in
private theorem rot_symm_pow_inv_mem_compl {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k < (G.vertexOf (G.inv d)).card) :
    (G.rot.symm ^ k) (G.inv d) ∈ ({d, G.inv d} : Set H)ᶜ := by
  refine mem_compl_pair_iff.2 ⟨fun h => ?_, rot_symm_pow_ne_self G (by omega) hk2⟩
  have := G.vertexOf_eq_of_mem (rot_symm_pow_mem_vertexOf G (G.inv d) k)
  rw [h] at this
  exact he.vertexOf_ne this

omit hG in
/-- The merged vertex has `|v(d)| + |v(d̄)| - 2` darts. -/
private theorem card_vertexOf_contractEdge_of_mem {a : (({d, G.inv d} : Set H)ᶜ : Set H)}
    (ha : (a : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)) :
    ((G.contractEdge d hleg).vertexOf a).card =
      (G.vertexOf d).card + (G.vertexOf (G.inv d)).card - 2 := by
  have hne := he.vertexOf_ne
  rw [← card_map (Embedding.subtype _), map_vertexOf_contractEdge_of_mem he.not_sameCycle ha,
    mergedVertex, card_sdiff_of_subset, card_union_of_disjoint, card_pair]
  · exact fun h => hne (congrArg G.vertexOf h)
  · exact disjoint_left.2 fun x h1 h2 =>
      hne ((G.vertexOf_eq_of_mem h1).symm.trans (G.vertexOf_eq_of_mem h2))
  · exact insert_subset_iff.2 ⟨mem_union_left _ (G.self_mem_vertexOf _),
      singleton_subset_iff.2 (mem_union_right _ (G.self_mem_vertexOf _))⟩

omit hG in
private theorem coe_contractEdge_rot_symm_pow_of_lt
    (hb1 : G.rot (G.inv d) ∈ ({d, G.inv d} : Set H)ᶜ) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k < (G.vertexOf d).card) :
    ((((G.contractEdge d hleg).rot.symm ^ k) ⟨_, hb1⟩ : (({d, G.inv d} : Set H)ᶜ : Set H)) : H) =
      (G.rot.symm ^ k) d := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    have hr : (G.contractEdge d hleg).rot ⟨(G.rot.symm ^ 1) d,
        rot_symm_pow_mem_compl he le_rfl hk2⟩ = ⟨_, hb1⟩ :=
      Subtype.ext (coe_contractEdge_rot_of_eq (by simp) hb1)
    rw [← hr, pow_one, Equiv.symm_apply_apply]
  | succ k hk ih =>
    have hr : (G.contractEdge d hleg).rot ⟨(G.rot.symm ^ (k + 1)) d,
        rot_symm_pow_mem_compl he (by omega) hk2⟩ =
        ((G.contractEdge d hleg).rot.symm ^ k) ⟨_, hb1⟩ := by
      apply Subtype.ext
      rw [coe_contractEdge_rot_of_mem, rot_rot_symm_pow_succ G, ih (by omega)]
      rw [rot_rot_symm_pow_succ G]
      exact rot_symm_pow_mem_compl he hk (by omega)
    rw [pow_succ', Perm.mul_apply, ← hr, Equiv.symm_apply_apply]

omit hG in
private theorem coe_contractEdge_rot_symm_pow_add_of_lt
    (hb1 : G.rot (G.inv d) ∈ ({d, G.inv d} : Set H)ᶜ) (h₁ : 2 ≤ (G.vertexOf d).card) {j : ℕ}
    (hj1 : 1 ≤ j) (hj2 : j < (G.vertexOf (G.inv d)).card) :
    ((((G.contractEdge d hleg).rot.symm ^ ((G.vertexOf d).card - 1 + j)) ⟨_, hb1⟩ :
      (({d, G.inv d} : Set H)ᶜ : Set H)) : H) = (G.rot.symm ^ j) (G.inv d) := by
  induction j, hj1 using Nat.le_induction with
  | base =>
    have ha1 : G.rot d ∈ ({d, G.inv d} : Set H)ᶜ := by
      rw [rot_eq_rot_symm_pow G]
      exact rot_symm_pow_mem_compl he (by omega) (by omega)
    have hr : (G.contractEdge d hleg).rot ⟨(G.rot.symm ^ 1) (G.inv d),
        rot_symm_pow_inv_mem_compl he le_rfl hj2⟩ =
        ((G.contractEdge d hleg).rot.symm ^ ((G.vertexOf d).card - 1)) ⟨_, hb1⟩ := by
      apply Subtype.ext
      rw [coe_contractEdge_rot_of_eq_inv (by simp) ha1,
        coe_contractEdge_rot_symm_pow_of_lt he hb1 (by omega) (by omega)]
      exact rot_eq_rot_symm_pow G d
    rw [pow_succ', Perm.mul_apply, ← hr, Equiv.symm_apply_apply]
  | succ j hj ih =>
    have hr : (G.contractEdge d hleg).rot ⟨(G.rot.symm ^ (j + 1)) (G.inv d),
        rot_symm_pow_inv_mem_compl he (by omega) hj2⟩ =
        ((G.contractEdge d hleg).rot.symm ^ ((G.vertexOf d).card - 1 + j)) ⟨_, hb1⟩ := by
      apply Subtype.ext
      rw [coe_contractEdge_rot_of_mem, rot_rot_symm_pow_succ G, ih (by omega)]
      rw [rot_rot_symm_pow_succ G]
      exact rot_symm_pow_inv_mem_compl he hj (by omega)
    rw [show (G.vertexOf d).card - 1 + (j + 1) = (G.vertexOf d).card - 1 + j + 1 by omega,
      pow_succ', Perm.mul_apply, ← hr, Equiv.symm_apply_apply]

omit hG he in
/-- Two cyclically increasing sequences of singletons `X`, `Y` of lengths `mx`, `my`, glued along
`X (mx - 1) = Y 0` and `Y (my - 1) = X 0`, give a cyclically increasing sequence `Z` of length
`mx + my - 2`. -/
private theorem exists_cyclicallyIncreasing_glue {mx my mz : ℕ} (hmz : mz = mx + my - 2)
    (X Y Z : ℕ → Finset (Fin b)) (hZX : ∀ k < mx, Z k = X k)
    (hZY : ∀ j, 1 ≤ j → j < my → Z (mx - 1 + j) = Y j) (hXY : X (mx - 1) = Y 0)
    (hYX : Y (my - 1) = X 0)
    (hx2 : 2 ≤ mx) (cx : Fin mx → Fin b) (hcx : ∀ k : Fin mx, X k = {cx k})
    (hcix : CyclicallyIncreasing (List.ofFn cx))
    (hy2 : 2 ≤ my) (cy : Fin my → Fin b) (hcy : ∀ k : Fin my, Y k = {cy k})
    (hciy : CyclicallyIncreasing (List.ofFn cy)) :
    2 ≤ mz ∧ ∃ cz : Fin mz → Fin b, (∀ k : Fin mz, Z k = {cz k}) ∧
      CyclicallyIncreasing (List.ofFn cz) := by
  have e₁ : cx ⟨mx - 1, by omega⟩ = cy ⟨0, by omega⟩ :=
    singleton_injective ((hcx ⟨mx - 1, by omega⟩).symm.trans (hXY.trans (hcy ⟨0, by omega⟩)))
  have e₂ : cy ⟨my - 1, by omega⟩ = cx ⟨0, by omega⟩ :=
    singleton_injective ((hcy ⟨my - 1, by omega⟩).symm.trans (hYX.trans (hcx ⟨0, by omega⟩)))
  obtain ⟨cz, hcz⟩ : ∃ cz : Fin mz → Fin b, ∀ i : Fin mz, cz i =
      if h : (i : ℕ) < mx then cx ⟨i, h⟩ else cy ⟨i + 1 - mx, by have := i.2; omega⟩ :=
    ⟨_, fun i => rfl⟩
  refine ⟨by omega, cz, ?_,
    (cyclicallyIncreasing_ofFn_glue hx2 hy2 hmz cx cy cz hcz e₁ e₂).2 ⟨hcix, hciy⟩⟩
  rintro ⟨k, hk⟩
  change Z k = _
  rw [hcz]
  split_ifs with hkx
  · change k < mx at hkx
    rw [hZX k hkx]
    exact hcx ⟨k, hkx⟩
  · change ¬k < mx at hkx
    have := hZY (k + 1 - mx) (by omega) (by omega)
    rw [show mx - 1 + (k + 1 - mx) = k by omega] at this
    rw [this]
    exact hcy ⟨k + 1 - mx, by omega⟩

omit hG he in
/-- A cyclically increasing sequence of singletons `Z` of length `mx + my - 2`, glued from `X` and
`Y` along `X (mx - 1) = Y 0`, splits into cyclically increasing sequences `X` and `Y`. -/
private theorem exists_cyclicallyIncreasing_of_glue {mx my mz : ℕ} (h₁ : 2 ≤ mx) (h₂ : 2 ≤ my)
    (hmz : mz = mx + my - 2) (X Y Z : ℕ → Finset (Fin b)) (hZX : ∀ k < mx, Z k = X k)
    (hZY : ∀ j, 1 ≤ j → j < my → Z (mx - 1 + j) = Y j) (hXY : X (mx - 1) = Y 0)
    (hZ : ∀ k, Z (k % mz) = Z k) (hz2 : 2 ≤ mz) (cz : Fin mz → Fin b)
    (hcz : ∀ k : Fin mz, Z k = {cz k}) (hciz : CyclicallyIncreasing (List.ofFn cz)) :
    (2 ≤ mx ∧ ∃ cx : Fin mx → Fin b, (∀ k : Fin mx, X k = {cx k}) ∧
        CyclicallyIncreasing (List.ofFn cx)) ∧
      (2 ≤ my ∧ ∃ cy : Fin my → Fin b, (∀ k : Fin my, Y k = {cy k}) ∧
        CyclicallyIncreasing (List.ofFn cy)) := by
  have hcz' : ∀ k (hk : k < mz), Z k = {cz ⟨k, hk⟩} := fun k hk => hcz ⟨k, hk⟩
  obtain ⟨cx, hcx⟩ : ∃ cx : Fin mx → Fin b, ∀ i : Fin mx,
      cx i = cz ⟨i, by have := i.2; omega⟩ := ⟨_, fun i => rfl⟩
  obtain ⟨cy, hcy⟩ : ∃ cy : Fin my → Fin b, ∀ j : Fin my,
      cy j = cz ⟨((j : ℕ) + mx - 1) % mz, Nat.mod_lt _ (by omega)⟩ := ⟨_, fun j => rfl⟩
  have hglue : ∀ i : Fin mz, cz i =
      if h : (i : ℕ) < mx then cx ⟨i, h⟩ else cy ⟨i + 1 - mx, by have := i.2; omega⟩ := by
    intro i
    split_ifs with h
    · rw [hcx]
    · rw [hcy]
      congr 1
      apply Fin.ext
      change (i : ℕ) = ((i : ℕ) + 1 - mx + mx - 1) % mz
      rw [show (i : ℕ) + 1 - mx + mx - 1 = i by omega, Nat.mod_eq_of_lt i.2]
  have e₁ : cx ⟨mx - 1, by omega⟩ = cy ⟨0, by omega⟩ := by
    rw [hcx, hcy]
    congr 1
    apply Fin.ext
    change mx - 1 = (0 + mx - 1) % mz
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  have e₂ : cy ⟨my - 1, by omega⟩ = cx ⟨0, by omega⟩ := by
    rw [hcx, hcy]
    congr 1
    apply Fin.ext
    change (my - 1 + mx - 1) % mz = 0
    rw [show my - 1 + mx - 1 = mz by omega, Nat.mod_self]
  have hglue' := cyclicallyIncreasing_ofFn_glue h₁ h₂ hmz cx cy cz hglue e₁ e₂
  refine ⟨⟨h₁, cx, fun k => ?_, (hglue'.1 hciz).1⟩, ⟨h₂, cy, fun j => ?_, (hglue'.1 hciz).2⟩⟩
  · rw [hcx, ← hZX k k.2]
    exact hcz' k _
  · rw [hcy]
    obtain ⟨j, hj⟩ := j
    change Y j = _
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [← hXY, ← hZX (mx - 1) (by omega), hcz' (mx - 1) (by omega)]
      congr 2
      apply Fin.ext
      change mx - 1 = (0 + mx - 1) % mz
      rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · rw [← hZY j hj1 hj, ← hZ, hcz' _ (Nat.mod_lt _ (by omega))]
      congr 2
      apply Fin.ext
      change (mx - 1 + j) % mz = (j + mx - 1) % mz
      congr 1
      omega

omit hG he in
/-- Two sequences of singletons `X`, `Y` of lengths `mx`, `my` glued into a periodic sequence `Z`
of length `mx + my - 2` along `X (mx - 1) = Y 0` and `Y (my - 1) = X 0`: the elements of `X` and
`Y` are cyclically increasing if and only if those of `Z` are. -/
private theorem exists_cyclicallyIncreasing_glue_iff {mx my mz : ℕ} (h₁ : 2 ≤ mx) (h₂ : 2 ≤ my)
    (hmz : mz = mx + my - 2) (X Y Z : ℕ → Finset (Fin b)) (hZX : ∀ k < mx, Z k = X k)
    (hZY : ∀ j, 1 ≤ j → j < my → Z (mx - 1 + j) = Y j) (hXY : X (mx - 1) = Y 0)
    (hYX : Y (my - 1) = X 0) (hZ : ∀ k, Z (k % mz) = Z k) :
    (2 ≤ mx ∧ ∃ cx : Fin mx → Fin b, (∀ k : Fin mx, X k = {cx k}) ∧
        CyclicallyIncreasing (List.ofFn cx)) ∧
      (2 ≤ my ∧ ∃ cy : Fin my → Fin b, (∀ k : Fin my, Y k = {cy k}) ∧
        CyclicallyIncreasing (List.ofFn cy)) ↔
      2 ≤ mz ∧ ∃ cz : Fin mz → Fin b, (∀ k : Fin mz, Z k = {cz k}) ∧
        CyclicallyIncreasing (List.ofFn cz) :=
  ⟨fun ⟨⟨hx2, cx, hcx, hcix⟩, ⟨hy2, cy, hcy, hciy⟩⟩ =>
    exists_cyclicallyIncreasing_glue hmz X Y Z hZX hZY hXY hYX hx2 cx hcx hcix hy2 cy hcy hciy,
    fun ⟨hz2, cz, hcz, hciz⟩ =>
      exists_cyclicallyIncreasing_of_glue h₁ h₂ hmz X Y Z hZX hZY hXY hZ hz2 cz hcz hciz⟩

/-- The resonance condition holds at the merged vertex of the contraction if and only if it holds
at both endpoints of the contracted edge. -/
private theorem resonanceCondition_merged_iff (h₁ : 2 ≤ (G.vertexOf d).card)
    (h₂ : 2 ≤ (G.vertexOf (G.inv d)).card)
    (hb1 : G.rot (G.inv d) ∈ ({d, G.inv d} : Set H)ᶜ) :
    G.ResonanceCondition (G.vertexOf d) ∧ G.ResonanceCondition (G.vertexOf (G.inv d)) ↔
      (G.contractEdge d hleg).ResonanceCondition
        ((G.contractEdge d hleg).vertexOf ⟨_, hb1⟩) := by
  have hzb : ¬(G.contractEdge d hleg).IsBoundaryVertex
      ((G.contractEdge d hleg).vertexOf ⟨_, hb1⟩) := fun h =>
    he.not_isBoundaryVertex_inv (by
      rw [← G.vertexOf_rot]
      exact (isBoundaryVertex_vertexOf_contractEdge_iff he).1 h)
  rw [hG.resonanceCondition_iff_exists he.not_isBoundaryVertex,
    hG.resonanceCondition_iff_exists he.not_isBoundaryVertex_inv,
    (hG.contractEdge he).resonanceCondition_iff_exists hzb]
  obtain ⟨E1, E2⟩ := cornerTripSet_rot_inv_eq hG he
  have hZX : ∀ k < (G.vertexOf d).card, (G.contractEdge d hleg).cornerTripSet
      (((G.contractEdge d hleg).rot.symm ^ k) ⟨_, hb1⟩) =
        G.cornerTripSet ((G.rot.symm ^ k) d) := by
    rintro (_ | k) hk
    · simp only [pow_zero, Perm.one_apply]
      rw [cornerTripSet_contractEdge hG he, ← E1]
    · rw [cornerTripSet_contractEdge hG he,
        coe_contractEdge_rot_symm_pow_of_lt he hb1 (by omega) hk]
  have hZY : ∀ j, 1 ≤ j → j < (G.vertexOf (G.inv d)).card →
      (G.contractEdge d hleg).cornerTripSet
          (((G.contractEdge d hleg).rot.symm ^ ((G.vertexOf d).card - 1 + j)) ⟨_, hb1⟩) =
        G.cornerTripSet ((G.rot.symm ^ j) (G.inv d)) := fun j hj1 hj2 => by
    rw [cornerTripSet_contractEdge hG he,
      coe_contractEdge_rot_symm_pow_add_of_lt he hb1 h₁ hj1 hj2]
  have hXY : G.cornerTripSet ((G.rot.symm ^ ((G.vertexOf d).card - 1)) d) =
      G.cornerTripSet ((G.rot.symm ^ 0) (G.inv d)) := by
    rw [← rot_eq_rot_symm_pow G, E2, pow_zero, Perm.one_apply]
  have hYX : G.cornerTripSet ((G.rot.symm ^ ((G.vertexOf (G.inv d)).card - 1)) (G.inv d)) =
      G.cornerTripSet ((G.rot.symm ^ 0) d) := by
    rw [← rot_eq_rot_symm_pow G, E1, pow_zero, Perm.one_apply]
  exact exists_cyclicallyIncreasing_glue_iff h₁ h₂
    (card_vertexOf_contractEdge_of_mem he (hleg := hleg) (a := ⟨_, hb1⟩)
      (mem_union_right _ (G.rot_mem_vertexOf _)))
    (fun k => G.cornerTripSet ((G.rot.symm ^ k) d))
    (fun k => G.cornerTripSet ((G.rot.symm ^ k) (G.inv d)))
    (fun k => (G.contractEdge d hleg).cornerTripSet
      (((G.contractEdge d hleg).rot.symm ^ k) ⟨_, hb1⟩))
    hZX hZY hXY hYX (fun k => by rw [rot_symm_pow_mod_card])

end Contraction

/-- If `{d, d̄}` is a contractible edge of the plabic graph `G` (its endpoints are distinct
internal vertices of the same colour) and `v(d)`, `v(d̄)` each consist of at least two darts, then
`G` has the resonance property if and only if its contraction `G_e` along `{d, d̄}` has. -/
@[cluster_algebras "lem_resonance_contraction"]
theorem IsPlabicGraph.hasResonanceProperty_iff_contractEdge (hG : G.IsPlabicGraph) {d : H}
    (he : G.IsContractibleEdge d) (h₁ : 2 ≤ (G.vertexOf d).card)
    (h₂ : 2 ≤ (G.vertexOf (G.inv d)).card)
    {hleg : ∀ i, G.leg i ∈ ({d, G.inv d} : Set H)ᶜ} :
    G.HasResonanceProperty ↔ (G.contractEdge d hleg).HasResonanceProperty := by
  have hb1 : G.rot (G.inv d) ∈ ({d, G.inv d} : Set H)ᶜ := by
    rw [rot_eq_rot_symm_pow G]
    exact rot_symm_pow_inv_mem_compl he (by omega) (by omega)
  have hb1U : G.rot (G.inv d) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d) :=
    mem_union_right _ (G.rot_mem_vertexOf _)
  have core := resonanceCondition_merged_iff hG he (hleg := hleg) h₁ h₂ hb1
  have hz2 : 2 ≤ ((G.contractEdge d hleg).vertexOf ⟨_, hb1⟩).card := by
    rw [card_vertexOf_contractEdge_of_mem he (a := ⟨_, hb1⟩) hb1U]
    omega
  have hzint : (G.contractEdge d hleg).vertexOf ⟨_, hb1⟩ ∈
      (G.contractEdge d hleg).internalVertices :=
    (vertexOf_mem_internalVertices_contractEdge_iff he _).2
      (by rw [G.vertexOf_rot]; exact he.inv_mem_internalVertices)
  have hlab : ∀ {a : (({d, G.inv d} : Set H)ᶜ : Set H)},
      (a : H) ∉ G.vertexOf d ∪ G.vertexOf (G.inv d) → ∀ n : ℕ,
      (G.contractEdge d hleg).edgeLabel ((G.contractEdge d hleg).edgeOf
        (((G.contractEdge d hleg).rot.symm ^ n) a)) =
        G.edgeLabel (G.edgeOf ((G.rot.symm ^ n) a)) := fun ha n => by
    rw [edgeLabel_contractEdge hG he, coe_contractEdge_rot_symm_pow_of_notMem ha]
  constructor
  · intro h w hw hlol
    obtain ⟨hwV, -⟩ := (G.contractEdge d hleg).mem_internalVertices.1 hw
    obtain ⟨a, rfl⟩ := (G.contractEdge d hleg).mem_vertices.1 hwV
    by_cases ha : (a : H) ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · have : (G.contractEdge d hleg).vertexOf a = (G.contractEdge d hleg).vertexOf ⟨_, hb1⟩ :=
        map_injective (Embedding.subtype _) (by
          rw [map_vertexOf_contractEdge_of_mem he.not_sameCycle ha,
            map_vertexOf_contractEdge_of_mem he.not_sameCycle hb1U])
      rw [this]
      exact core.1 ⟨h _ he.mem_internalVertices fun i hl => by have := hl.1.2; omega,
        h _ he.inv_mem_internalVertices fun i hl => by have := hl.1.2; omega⟩
    · exact (h _ ((vertexOf_mem_internalVertices_contractEdge_iff he a).1 hw)
        fun i hl => hlol i ((isLollipop_contractEdge_iff hG he ha i).2 hl)).of_edgeLabel_eq
          (card_vertexOf_contractEdge_of_notMem he ha) (hlab ha)
  · intro h w hw hlol
    obtain ⟨hwV, -⟩ := G.mem_internalVertices.1 hw
    obtain ⟨a, rfl⟩ := G.mem_vertices.1 hwV
    by_cases ha : a ∈ G.vertexOf d ∪ G.vertexOf (G.inv d)
    · obtain ⟨hx, hy⟩ := core.2 (h _ hzint fun i hl => by have := hl.1.2; omega)
      rcases mem_union.1 ha with ha | ha <;> rw [G.vertexOf_eq_of_mem ha]
      exacts [hx, hy]
    · have haY := mem_compl_pair_of_notMem ha
      exact (h _ ((vertexOf_mem_internalVertices_contractEdge_iff he ⟨a, haY⟩).2 hw)
        fun i hl => hlol i ((isLollipop_contractEdge_iff hG he (a := ⟨a, haY⟩) ha i).1 hl)
          ).of_edgeLabel_eq (card_vertexOf_contractEdge_of_notMem he (a := ⟨a, haY⟩) ha).symm
          fun n => (hlab (a := ⟨a, haY⟩) ha n).symm

/-- In a nearly leafless plabic graph, the endpoints of a contractible edge are not leaves. -/
private theorem IsContractibleEdge.two_le_card (hG : G.IsPlabicGraph) (hnl : G.IsNearlyLeafless)
    {d : H} (he : G.IsContractibleEdge d) :
    2 ≤ (G.vertexOf d).card ∧ 2 ≤ (G.vertexOf (G.inv d)).card :=
  ⟨two_le_card_of_isNearlyLeafless hnl he.not_isBoundaryVertex fun _ hl =>
      he.not_isBoundaryVertex_inv (hl.isBoundaryVertex_inv hG),
    two_le_card_of_isNearlyLeafless hnl he.not_isBoundaryVertex_inv fun _ hl =>
      he.not_isBoundaryVertex (by
        have := hl.isBoundaryVertex_inv hG
        rwa [hG.inv_involutive] at this)⟩

end PlabicData

namespace PlabicGraph

variable {b : ℕ} {G G' : PlabicGraph b}

/-- If `G` and `G'` are nearly leafless plabic graphs and `G'` is obtained from `G` by a local
move, then `G` has the resonance property if and only if `G'` has. -/
@[cluster_algebras "lem_resonance_moves"]
theorem IsLocalMove.hasResonanceProperty_iff {t : LocalMoveType}
    (hG : G.data.IsNearlyLeafless) (hG' : G'.data.IsNearlyLeafless) (h : IsLocalMove t G G') :
    G.data.HasResonanceProperty ↔ G'.data.HasResonanceProperty := by
  cases t with
  | m1 =>
    obtain ⟨c, hq, hiso⟩ := h
    rw [G.isPlabicGraph.hasResonanceProperty_iff_squareMove hq]
    exact (G'.isPlabicGraph.hasResonanceProperty_iff_of_isomorphic
      (G.isPlabicGraph.squareMove c) hiso).symm
  | m2 =>
    rcases h with ⟨d, hd, hiso⟩ | ⟨d, hd, hiso⟩
    · rw [G.isPlabicGraph.hasResonanceProperty_iff_bivalentRemoval hG hd]
      exact (G'.isPlabicGraph.hasResonanceProperty_iff_of_isomorphic
        (PlabicData.isPlabicGraph_bivalentRemoval G.isPlabicGraph hd) hiso).symm
    · rw [G'.isPlabicGraph.hasResonanceProperty_iff_bivalentRemoval hG' hd]
      exact G.isPlabicGraph.hasResonanceProperty_iff_of_isomorphic
        (PlabicData.isPlabicGraph_bivalentRemoval G'.isPlabicGraph hd) hiso
  | m3 =>
    rcases h with ⟨d, he, hiso⟩ | ⟨d, he, hiso⟩
    · obtain ⟨h₁, h₂⟩ := he.two_le_card G.isPlabicGraph hG
      rw [G.isPlabicGraph.hasResonanceProperty_iff_contractEdge he h₁ h₂
        (hleg := he.leg_mem G.isPlabicGraph)]
      exact (G'.isPlabicGraph.hasResonanceProperty_iff_of_isomorphic
        (G.isPlabicGraph.contractEdge he) hiso).symm
    · obtain ⟨h₁, h₂⟩ := he.two_le_card G'.isPlabicGraph hG'
      rw [G'.isPlabicGraph.hasResonanceProperty_iff_contractEdge he h₁ h₂
        (hleg := he.leg_mem G'.isPlabicGraph)]
      exact G.isPlabicGraph.hasResonanceProperty_iff_of_isomorphic
        (G'.isPlabicGraph.contractEdge he) hiso

/-- If the plabic graphs `G` and `G'` are nearly leafless equivalent, then `G` has the resonance
property if and only if `G'` has. -/
@[cluster_algebras "lem_resonance_nearly_leafless_equivalent"]
theorem NearlyLeaflessEquivalent.hasResonanceProperty_iff (h : NearlyLeaflessEquivalent G G') :
    G.data.HasResonanceProperty ↔ G'.data.HasResonanceProperty := by
  obtain ⟨h0, h⟩ := h
  induction h with
  | refl => rfl
  | @tail G₁ G₂ hab hstep ih =>
    obtain ⟨hnl, hstep⟩ := hstep
    have hnl₁ : G₁.data.IsNearlyLeafless :=
      NearlyLeaflessEquivalent.isNearlyLeafless_right ⟨h0, hab⟩
    refine ih.trans ?_
    rcases hstep with hiso | ⟨t, -, hmove⟩
    · exact (G₂.isPlabicGraph.hasResonanceProperty_iff_of_isomorphic G₁.isPlabicGraph hiso).symm
    · exact hmove.hasResonanceProperty_iff hnl₁ hnl

end PlabicGraph

/-! ### Vertices with two or three darts -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- A dart of the one-way trip from `x` has the trip set `{x}`. -/
private theorem tripSet_eq_singleton (hG : G.IsPlabicGraph) {d : H} {x : Fin b}
    (h : d ∈ G.oneWayTrip x) : G.tripSet d = {x} :=
  eq_singleton_iff_unique_mem.2
    ⟨mem_tripSet.2 h, fun _ hy => hG.eq_of_mem_oneWayTrip (mem_tripSet.1 hy) h⟩

/-- The edge of a dart in the trip of `x` whose reverse is in the trip of `y` is labelled `{x, y}`.
-/
private theorem edgeLabel_edgeOf_eq_pair {d : H} {x y : Fin b} (h₁ : G.tripSet d = {x})
    (h₂ : G.tripSet (G.inv d) = {y}) : G.edgeLabel (G.edgeOf d) = {x, y} := by
  rw [edgeLabel_edgeOf, h₁, h₂, ← insert_eq]

/-- If `σ^{-n}(a) = a` with `n > 0`, the vertex of `a` consists of the darts `σ^{-k}(a)`,
`k < n`. -/
private theorem vertexOf_eq_image_range {a : H} {n : ℕ} (hn : 0 < n)
    (h : (G.rot.symm ^ n) a = a) :
    G.vertexOf a = (range n).image fun k => (G.rot.symm ^ k) a := by
  ext e
  rw [mem_image]
  constructor
  · intro he
    rw [RotationSystem.mem_vertexOf] at he
    obtain ⟨m, hm⟩ := (Perm.sameCycle_inv.2 he).exists_nat_pow_eq
    exact ⟨m % n, mem_range.2 (Nat.mod_lt _ hn), (pow_mod_apply_of_pow_apply_eq h m).trans hm⟩
  · rintro ⟨k, -, rfl⟩
    exact rot_symm_pow_mem_vertexOf G a k

private theorem val_finRotate_three {m : ℕ} (hm : m = 3) (k : Fin m) :
    ((finRotate m k : Fin m) : ℕ) = ((k : ℕ) + 1) % 3 := by
  subst hm
  fin_cases k <;> rfl

/-- **The resonance condition at a vertex with three darts.** If `a, a₁ = σ⁻¹(a), a₂ = σ⁻¹(a₁)`
are distinct with `σ⁻¹(a₂) = a`, and their labels are `{x, y}, {y, z}, {x, z}` for labels
`x < y < z`, then the resonance condition holds at the vertex of `a`. -/
private theorem resonanceCondition_of_three {a a₁ a₂ : H} (h₁ : G.rot.symm a = a₁)
    (h₂ : G.rot.symm a₁ = a₂) (h₃ : G.rot.symm a₂ = a) (hne₁ : a₁ ≠ a) (hne₂ : a₂ ≠ a)
    (hne₁₂ : a₂ ≠ a₁) {x y z : Fin b} (hxy : x < y) (hyz : y < z)
    (l₀ : G.edgeLabel (G.edgeOf a) = {x, y}) (l₁ : G.edgeLabel (G.edgeOf a₁) = {y, z})
    (l₂ : G.edgeLabel (G.edgeOf a₂) = {x, z}) : G.ResonanceCondition (G.vertexOf a) := by
  have p1 : (G.rot.symm ^ 1) a = a₁ := by rw [pow_one, h₁]
  have p2 : (G.rot.symm ^ 2) a = a₂ := by rw [pow_succ', Perm.mul_apply, p1, h₂]
  have p3 : (G.rot.symm ^ 3) a = a := by rw [pow_succ', Perm.mul_apply, p2, h₃]
  have hcard : (G.vertexOf a).card = 3 := by
    rw [vertexOf_eq_image_range (by norm_num) p3, card_image_of_injOn, card_range]
    intro k hk k' hk' hkk'
    simp only [coe_range, Set.mem_Iio] at hk hk'
    simp only at hkk'
    interval_cases k <;> interval_cases k' <;> first
      | rfl
      | (exfalso
         simp only [pow_zero, Perm.one_apply, p1, p2] at hkk'
         first
         | exact hne₁ hkk'.symm | exact hne₁ hkk' | exact hne₂ hkk'.symm | exact hne₂ hkk'
         | exact hne₁₂ hkk'.symm | exact hne₁₂ hkk')
  refine ⟨by omega, a, G.self_mem_vertexOf a,
    fun k => if (k : ℕ) = 0 then x else if (k : ℕ) = 1 then y else z, fun k k' hkk' => ?_,
    fun k => ?_⟩
  · have hk : (k : ℕ) < (k' : ℕ) := hkk'
    have hk' : (k' : ℕ) < 3 := hcard ▸ k'.2
    beta_reduce
    rcases (by omega : (k : ℕ) = 0 ∧ (k' : ℕ) = 1 ∨ (k : ℕ) = 0 ∧ (k' : ℕ) = 2 ∨
      (k : ℕ) = 1 ∧ (k' : ℕ) = 2) with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      simp only [h, h'] <;> norm_num
    · exact hxy
    · exact hxy.trans hyz
    · exact hyz
  · have hk : (k : ℕ) < 3 := hcard ▸ k.2
    have hrot := val_finRotate_three hcard k
    beta_reduce
    rw [hrot]
    rcases (by omega : (k : ℕ) = 0 ∨ (k : ℕ) = 1 ∨ (k : ℕ) = 2) with h | h | h <;> rw [h]
    · rw [pow_zero, Perm.one_apply, l₀]
      norm_num
    · rw [p1, l₁]
      norm_num
    · rw [p2, l₂, pair_comm]
      norm_num

/-- **The resonance condition at a vertex with two darts.** If `a₁ = σ⁻¹(a) ≠ a` and
`σ⁻¹(a₁) = a`, and both darts carry the same label of two elements, then the resonance condition
holds at the vertex of `a`. -/
private theorem resonanceCondition_of_two {a a₁ : H} (h₁ : G.rot.symm a = a₁)
    (h₂ : G.rot.symm a₁ = a) (hne : a₁ ≠ a) {L : Finset (Fin b)} (hL : L.card = 2)
    (l₀ : G.edgeLabel (G.edgeOf a) = L) (l₁ : G.edgeLabel (G.edgeOf a₁) = L) :
    G.ResonanceCondition (G.vertexOf a) := by
  have p1 : (G.rot.symm ^ 1) a = a₁ := by rw [pow_one, h₁]
  have p2 : (G.rot.symm ^ 2) a = a := by rw [pow_succ', Perm.mul_apply, p1, h₂]
  have hv := vertexOf_eq_image_range (G := G) (by norm_num) p2
  have hcard : (G.vertexOf a).card = 2 := by
    rw [hv, card_image_of_injOn, card_range]
    intro k hk k' hk' hkk'
    simp only [coe_range, Set.mem_Iio] at hk hk'
    simp only at hkk'
    interval_cases k <;> interval_cases k' <;> first
      | rfl
      | (exfalso
         simp only [pow_zero, Perm.one_apply, p1] at hkk'
         first | exact hne hkk'.symm | exact hne hkk')
  refine resonanceCondition_of_card_eq_two hcard hL fun e he => ?_
  rw [hv, mem_image] at he
  obtain ⟨k, hk, rfl⟩ := he
  rw [mem_range] at hk
  interval_cases k
  · rw [pow_zero, Perm.one_apply]
    exact l₀
  · rw [p1]
    exact l₁

end PlabicData

/-! ### Bridge decompositions -/

section BridgeInequalities

variable {a b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- Two integers of an open interval of length `b` congruent modulo `b` are equal. -/
private theorem eq_of_modEq_of_lt_of_lt {x y l : ℤ} (hx : l < x ∧ x < l + b)
    (hy : l < y ∧ y < l + b) (h : x ≡ y [ZMOD b]) : x = y := by
  have := Int.eq_zero_of_abs_lt_dvd (m := b) (x := y - x) (Int.modEq_iff_dvd.mp h)
    (by rw [abs_lt]; omega)
  omega

/-- `ρ_{t+1}⁻¹ = ρ_t⁻¹ ∘ τ_{t+1}`. -/
private theorem positionMap_succ_symm_apply' {t : ℕ} (ht : t < s.length) (v : ℤ) :
    (positionMap s (t + 1)).symm v = (positionMap s t).symm (Equiv.swap s[t].1 s[t].2 v) := by
  rw [Equiv.symm_apply_eq, positionMap_succ ht, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
    Equiv.swap_apply_self]

/-- A letter in no pair after the `t`-th keeps its position: `ρ_u⁻¹(h) = ρ_t⁻¹(h)` for `u ≥ t`. -/
private theorem positionMap_symm_eq_of_forall_ne {t : ℕ} {h : ℤ}
    (hne : ∀ u (hu : u < s.length), t ≤ u → h ≠ s[u].1 ∧ h ≠ s[u].2) {u : ℕ} (htu : t ≤ u) :
    (positionMap s u).symm h = (positionMap s t).symm h := by
  induction u, htu using Nat.le_induction with
  | base => rfl
  | succ u htu ih =>
    rcases lt_or_ge u s.length with hul | hul
    · rw [positionMap_succ_symm_apply' hul,
        Equiv.swap_apply_of_ne_of_ne (hne u hul htu).1 (hne u hul htu).2, ih]
    · rw [positionMap_of_length_le (by omega), ← positionMap_of_length_le hul, ih]

/-- If `y < y'` in `[1, b]` are not fixed points of `f_t` modulo `b` and `f_t(y) < f_t(y')`,
then `ρ_t⁻¹(y) < ρ_t⁻¹(y')`. -/
private theorem IsBridgeSequence.positionMap_symm_lt (hs : IsBridgeSequence b f s) {t : ℕ}
    {y y' : ℤ} (hy : 1 ≤ y ∧ y ≤ b) (hy' : 1 ≤ y' ∧ y' ≤ b) (hlt : y < y')
    (hny : ¬IsFixedPointMod b (swapProduct b f s t) y)
    (hny' : ¬IsFixedPointMod b (swapProduct b f s t) y')
    (hf : swapProduct b f s t y < swapProduct b f s t y') :
    (positionMap s t).symm y < (positionMap s t).symm y' := by
  have hx := positionMap_symm_mem_Icc (b := (b : ℤ)) hs.mem_Icc t hy'
  have hx' := positionMap_symm_mem_Icc (b := (b : ℤ)) hs.mem_Icc t hy
  rcases lt_trichotomy ((positionMap s t).symm y) ((positionMap s t).symm y') with h | h | h
  · exact h
  · exact absurd ((positionMap s t).symm.injective h) hlt.ne
  · exfalso
    have e := swapProduct_positionMap f hs.mem_Icc t hx
    have e' := swapProduct_positionMap f hs.mem_Icc t hx'
    rw [Equiv.apply_symm_apply] at e e'
    have := hs.positionMap_lt_positionMap hx hx' (t₀ := 0) (t₁ := t) (Nat.zero_le _)
      (by simpa using h) (by rwa [← e, ← e'])
      (by rwa [Equiv.apply_symm_apply]) (by rwa [Equiv.apply_symm_apply])
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    omega

/-- `f_{t+1} = f_t ∘ (i j)` on `[1, b]`, where `(i, j) = s[t]`. -/
private theorem IsBridgeSequence.swapProduct_succ_apply (hs : IsBridgeSequence b f s) {t : ℕ}
    (ht : t < s.length) {n : ℤ} (hn : 1 ≤ n ∧ n ≤ (b : ℤ)) :
    swapProduct b f s (t + 1) n = swapProduct b f s t (Equiv.swap s[t].1 s[t].2 n) := by
  have hp := hs.isBridgePair t ht
  have := hp.lt
  have := hp.one_le
  have := hp.le
  rw [swapProduct_succ ht, Function.comp_apply,
    affineTransposition_eq_swap ⟨hp.one_le, by omega⟩ ⟨by omega, hp.le⟩ hn]

/-- A letter of `[1, b]` lying in a pair after the `t`-th is not a fixed point of `f_{t+1}`. -/
private theorem IsBridgeSequence.not_isFixedPointMod_of_later (hs : IsBridgeSequence b f s)
    {t : ℕ} {h : ℤ} (hh : 1 ≤ h ∧ h ≤ (b : ℤ))
    (hL : ∃ u, ∃ hu : u < s.length, t < u ∧ (h = s[u].1 ∨ h = s[u].2)) :
    ¬IsFixedPointMod b (swapProduct b f s (t + 1)) h := by
  obtain ⟨u, hu, htu, he⟩ := hL
  intro hfix
  have := hs.ne_of_isFixedPointMod hh hfix hu htu
  exact he.elim this.1 this.2

/-- For `k ∈ [1, b]`, `ℓ = ρ_t(ρ_r⁻¹(k))` lies in `[1, b]`, `f_t(ℓ) ≡ k`, and
`ρ_t⁻¹(ℓ) = ρ_r⁻¹(k)`. -/
private theorem IsBridgeSequence.positionMap_positionMap_symm_length
    (hs : IsBridgeSequence b f s) (t : ℕ) {k : ℤ} (hk : 1 ≤ k ∧ k ≤ (b : ℤ)) :
    (1 ≤ positionMap s t ((positionMap s s.length).symm k) ∧
        positionMap s t ((positionMap s s.length).symm k) ≤ (b : ℤ)) ∧
      swapProduct b f s t (positionMap s t ((positionMap s s.length).symm k)) ≡ k [ZMOD b] ∧
      (positionMap s t).symm (positionMap s t ((positionMap s s.length).symm k)) =
        (positionMap s s.length).symm k := by
  have hpk := positionMap_symm_mem_Icc (b := (b : ℤ)) hs.mem_Icc s.length hk
  refine ⟨positionMap_mem_Icc (b := (b : ℤ)) hs.mem_Icc t hpk, ?_, by simp⟩
  rw [swapProduct_positionMap f hs.mem_Icc t hpk]
  simpa only [Equiv.apply_symm_apply] using (hs.positionMap_modEq hpk).symm

/-- A point that is not a fixed point modulo `b` of a bounded affine permutation `g` satisfies
`ℓ < g ℓ < ℓ + b`. -/
private theorem IsBoundedAffinePerm.lt_apply_of_not_isFixedPointMod {g : ℤ → ℤ}
    (hg : IsBoundedAffinePerm a b g) {ℓ : ℤ} (hℓ : ¬IsFixedPointMod b g ℓ) :
    ℓ < g ℓ ∧ g ℓ < ℓ + b :=
  ⟨lt_of_le_of_ne (hg.le_apply ℓ) fun e => hℓ (isFixedPointMod_of_eq e.symm),
    lt_of_le_of_ne (hg.apply_le ℓ) fun e => hℓ (isFixedPointMod_of_eq_add e)⟩

/-- With `(i, j) = s[t]`: if `i` lies in a later pair, then `ρ_r⁻¹(i) < ρ_t⁻¹(i)` or
`ρ_t⁻¹(j) < ρ_r⁻¹(i)`. -/
private theorem IsBridgeSequence.positionMap_symm_fst_lt_or_lt (hf : IsBoundedAffinePerm a b f)
    (hs : IsBridgeSequence b f s) {t : ℕ} (ht : t < s.length)
    (hL : ∃ u, ∃ hu : u < s.length, t < u ∧ (s[t].1 = s[u].1 ∨ s[t].1 = s[u].2)) :
    (positionMap s s.length).symm s[t].1 < (positionMap s t).symm s[t].1 ∨
      (positionMap s t).symm s[t].2 < (positionMap s s.length).symm s[t].1 := by
  have hp := hs.isBridgePair t ht
  have hgb := hs.isBoundedAffinePerm_swapProduct hf t
  have hij := hp.lt
  have hi1 := hp.one_le
  have hjb := hp.le
  have hiI : 1 ≤ s[t].1 ∧ s[t].1 ≤ (b : ℤ) := ⟨hi1, by omega⟩
  have hjI : 1 ≤ s[t].2 ∧ s[t].2 ≤ (b : ℤ) := ⟨by omega, hjb⟩
  have hfix := hs.not_isFixedPointMod_of_later hiI hL
  rw [IsFixedPointMod, hs.swapProduct_succ_apply ht hiI, Equiv.swap_apply_left] at hfix
  obtain ⟨⟨hℓ1, hℓ2⟩, hgℓ, hωℓ⟩ := hs.positionMap_positionMap_symm_length t hiI
  set i := s[t].1
  set j := s[t].2
  set g := swapProduct b f s t with hg
  obtain ⟨hval1, hval2, hval3⟩ := hgb.isBridgePair_values hp
  set ℓ := positionMap s t ((positionMap s s.length).symm i)
  rw [← hωℓ]
  have hℓi : ℓ ≠ i := fun e => hp.not_isFixedPointMod_left (by rwa [e] at hgℓ)
  have hℓj : ℓ ≠ j := fun e => hfix (by rwa [← e])
  have hnf : ¬IsFixedPointMod b g ℓ := fun hfix =>
    hℓi (eq_of_modEq_of_mem_Icc ⟨hℓ1, hℓ2⟩ hiI (hfix.symm.trans hgℓ))
  have hout : ¬(i < ℓ ∧ ℓ < j) := fun h => hnf (hp.isFixedPointMod_of_lt_of_lt ℓ h.1 h.2)
  obtain ⟨hb1, hb2⟩ := hgb.lt_apply_of_not_isFixedPointMod hnf
  rcases lt_or_gt_of_ne hℓi with hlt | hgt
  · have e : g ℓ = i := eq_of_modEq_of_lt_of_lt (l := ℓ) ⟨hb1, hb2⟩ ⟨hlt, by omega⟩ hgℓ
    left
    exact hs.positionMap_symm_lt ⟨hℓ1, hℓ2⟩ hiI hlt hnf hp.not_isFixedPointMod_left
      (by rw [← hg, e]; omega)
  · have hgt' : j < ℓ := lt_of_le_of_ne (not_lt.1 fun h => hout ⟨hgt, h⟩) (Ne.symm hℓj)
    have e : g ℓ = i + b := eq_of_modEq_of_lt_of_lt (l := ℓ) ⟨hb1, hb2⟩ ⟨by omega, by omega⟩
      (hgℓ.trans (show i + b ≡ i [ZMOD b] by simp [Int.ModEq]).symm)
    right
    exact hs.positionMap_symm_lt hjI ⟨hℓ1, hℓ2⟩ hgt' hp.not_isFixedPointMod_right hnf
      (lt_of_le_of_ne (by rwa [← hg, e]) fun e' => hℓj (hgb.bijective.1 e').symm)

/-- With `(i, j) = s[t]`: if `j` lies in a later pair, then `ρ_r⁻¹(j) < ρ_t⁻¹(i)` or
`ρ_t⁻¹(j) < ρ_r⁻¹(j)`. -/
private theorem IsBridgeSequence.positionMap_symm_snd_lt_or_lt (hf : IsBoundedAffinePerm a b f)
    (hs : IsBridgeSequence b f s) {t : ℕ} (ht : t < s.length)
    (hL : ∃ u, ∃ hu : u < s.length, t < u ∧ (s[t].2 = s[u].1 ∨ s[t].2 = s[u].2)) :
    (positionMap s s.length).symm s[t].2 < (positionMap s t).symm s[t].1 ∨
      (positionMap s t).symm s[t].2 < (positionMap s s.length).symm s[t].2 := by
  have hp := hs.isBridgePair t ht
  have hgb := hs.isBoundedAffinePerm_swapProduct hf t
  have hij := hp.lt
  have hi1 := hp.one_le
  have hjb := hp.le
  have hiI : 1 ≤ s[t].1 ∧ s[t].1 ≤ (b : ℤ) := ⟨hi1, by omega⟩
  have hjI : 1 ≤ s[t].2 ∧ s[t].2 ≤ (b : ℤ) := ⟨by omega, hjb⟩
  have hfix := hs.not_isFixedPointMod_of_later hjI hL
  rw [IsFixedPointMod, hs.swapProduct_succ_apply ht hjI, Equiv.swap_apply_right] at hfix
  obtain ⟨⟨hℓ1, hℓ2⟩, hgℓ, hωℓ⟩ := hs.positionMap_positionMap_symm_length t hjI
  set i := s[t].1
  set j := s[t].2
  set g := swapProduct b f s t with hg
  obtain ⟨hval1, hval2, hval3⟩ := hgb.isBridgePair_values hp
  set ℓ := positionMap s t ((positionMap s s.length).symm j)
  rw [← hωℓ]
  have hℓj : ℓ ≠ j := fun e => hp.not_isFixedPointMod_right (by rwa [e] at hgℓ)
  have hℓi : ℓ ≠ i := fun e => hfix (by rwa [← e])
  have hnf : ¬IsFixedPointMod b g ℓ := fun hfix =>
    hℓj (eq_of_modEq_of_mem_Icc ⟨hℓ1, hℓ2⟩ hjI (hfix.symm.trans hgℓ))
  have hout : ¬(i < ℓ ∧ ℓ < j) := fun h => hnf (hp.isFixedPointMod_of_lt_of_lt ℓ h.1 h.2)
  obtain ⟨hb1, hb2⟩ := hgb.lt_apply_of_not_isFixedPointMod hnf
  rcases lt_or_gt_of_ne hℓi with hlt | hgt
  · have e : g ℓ = j := eq_of_modEq_of_lt_of_lt (l := ℓ) ⟨hb1, hb2⟩ ⟨by omega, by omega⟩ hgℓ
    left
    exact hs.positionMap_symm_lt ⟨hℓ1, hℓ2⟩ hiI hlt hnf hp.not_isFixedPointMod_left
      (lt_of_le_of_ne (by rwa [← hg, e]) fun e' => hℓi (hgb.bijective.1 e'))
  · have hgt' : j < ℓ := lt_of_le_of_ne (not_lt.1 fun h => hout ⟨hgt, h⟩) (Ne.symm hℓj)
    have e : g ℓ = j + b := eq_of_modEq_of_lt_of_lt (l := ℓ) ⟨hb1, hb2⟩ ⟨by omega, by omega⟩
      (hgℓ.trans (show j + b ≡ j [ZMOD b] by simp [Int.ModEq]).symm)
    right
    exact hs.positionMap_symm_lt hjI ⟨hℓ1, hℓ2⟩ hgt' hp.not_isFixedPointMod_right hnf
      (by rw [← hg, e]; omega)

/-- A letter in no pair after the `t`-th has `ρ_r⁻¹(h) = ρ_{t+1}⁻¹(h)`. -/
private theorem positionMap_symm_length_eq_of_not_later {t : ℕ} {h : ℤ}
    (hL : ¬∃ u, ∃ hu : u < s.length, t < u ∧ (h = s[u].1 ∨ h = s[u].2)) (ht : t < s.length) :
    (positionMap s s.length).symm h = (positionMap s (t + 1)).symm h :=
  positionMap_symm_eq_of_forall_ne (fun u hu htu =>
    ⟨fun e => hL ⟨u, hu, by omega, Or.inl e⟩, fun e => hL ⟨u, hu, by omega, Or.inr e⟩⟩)
    (by omega)

/-- The inequalities at the `t`-th bridge (indexed from `0`). With `(i, j) = s[t]`,
`a = ρ_t⁻¹(i)`, `c = ρ_t⁻¹(j)`, `p = ρ_r⁻¹(i)` and `q = ρ_r⁻¹(j)`: `a < c`; if `i` lies in a later
pair then `p < a` or `c < p`, and otherwise `p = c`; if `j` lies in a later pair then `q < a` or
`c < q`, and otherwise `q = a`. -/
private theorem IsBridgeSequence.bridge_inequalities (hf : IsBoundedAffinePerm a b f)
    (hs : IsBridgeSequence b f s) {t : ℕ} (ht : t < s.length) :
    (positionMap s t).symm s[t].1 < (positionMap s t).symm s[t].2 ∧
    ((∃ u, ∃ hu : u < s.length, t < u ∧ (s[t].1 = s[u].1 ∨ s[t].1 = s[u].2)) →
      (positionMap s s.length).symm s[t].1 < (positionMap s t).symm s[t].1 ∨
        (positionMap s t).symm s[t].2 < (positionMap s s.length).symm s[t].1) ∧
    ((¬∃ u, ∃ hu : u < s.length, t < u ∧ (s[t].1 = s[u].1 ∨ s[t].1 = s[u].2)) →
      (positionMap s s.length).symm s[t].1 = (positionMap s t).symm s[t].2) ∧
    ((∃ u, ∃ hu : u < s.length, t < u ∧ (s[t].2 = s[u].1 ∨ s[t].2 = s[u].2)) →
      (positionMap s s.length).symm s[t].2 < (positionMap s t).symm s[t].1 ∨
        (positionMap s t).symm s[t].2 < (positionMap s s.length).symm s[t].2) ∧
    ((¬∃ u, ∃ hu : u < s.length, t < u ∧ (s[t].2 = s[u].1 ∨ s[t].2 = s[u].2)) →
      (positionMap s s.length).symm s[t].2 = (positionMap s t).symm s[t].1) := by
  have hp := hs.isBridgePair t ht
  have hij := hp.lt
  have hi1 := hp.one_le
  have hjb := hp.le
  refine ⟨hs.positionMap_symm_lt ⟨hi1, by omega⟩ ⟨by omega, hjb⟩ hij hp.not_isFixedPointMod_left
      hp.not_isFixedPointMod_right hp.apply_lt_apply, hs.positionMap_symm_fst_lt_or_lt hf ht,
    fun hL => ?_, hs.positionMap_symm_snd_lt_or_lt hf ht, fun hL => ?_⟩
  · rw [positionMap_symm_length_eq_of_not_later hL ht, positionMap_succ_symm_apply' ht,
      Equiv.swap_apply_left]
  · rw [positionMap_symm_length_eq_of_not_later hL ht, positionMap_succ_symm_apply' ht,
      Equiv.swap_apply_right]

end BridgeInequalities

section BridgeEnds

open BridgeGraph BridgeSymbol PlabicData

variable {a b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- The `t`-th bridge on strand `z` is not the lowest one exactly when a later pair of `s` contains
the letter `z + 1`. -/
theorem lt_top_iff_exists_later_pair {z : Fin b} {t : ℕ} (hz : t + 1 ∈ heights s z) :
    t + 1 < top s z ↔
      ∃ u, ∃ hu : u < s.length, t < u ∧ ((z : ℤ) + 1 = s[u].1 ∨ (z : ℤ) + 1 = s[u].2) := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := mem_heights.1 (top_mem ⟨_, hz⟩)
    refine ⟨top s z - 1, by omega, by omega, ?_⟩
    rwa [← pair_eq_getElem h1 h2]
  · rintro ⟨u, hu, htu, he⟩
    have := le_top (mem_heights.2 ⟨by omega, by omega, by rwa [pair_succ hu]⟩ :
      u + 1 ∈ heights s z)
    omega

/-- No height of strand `z` lies strictly between the previous height `prev s z (t + 1)` and
`t + 1`. -/
theorem notMem_Icc_prev_of_mem_heights (z : Fin b) {t : ℕ} :
    ∀ v ∈ heights s z, v ∉ Icc (prev s z (t + 1) + 1) t := by
  intro v hv hvI
  rw [Finset.mem_Icc] at hvI
  have := le_prev hv (show v < t + 1 by omega)
  omega

/-- The ends of the `t`-th bridge (indexed from `0`) of the bridge graph of a bridge sequence
satisfy the resonance condition. -/
private theorem IsBridgeSequence.resonanceCondition_bridgeEnds (hb : 1 ≤ b)
    (hf : IsBoundedAffinePerm a b f) (hs : IsBridgeSequence b f s) (γ : Fin b → Shade) {t : ℕ}
    (ht : t < s.length) (hdT : IsDart (b := b) s (.bridge (t + 1))) :
    (bridgeGraph b s γ).ResonanceCondition ((bridgeGraph b s γ).vertexOf ⟨.bridge (t + 1), hdT⟩) ∧
      (bridgeGraph b s γ).ResonanceCondition
        ((bridgeGraph b s γ).vertexOf ⟨.bridgeRev (t + 1), hdT⟩) := by
  have hs' : ∀ p ∈ s, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b := fun p hp => by
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hp
    have h := hs.isBridgePair u hu
    exact ⟨h.one_le, h.lt, h.le⟩
  have hn := hs.isNestedPairSequence
  have hG := isPlabicGraph_bridgeGraph hb hs' hn γ
  have hpT : pair s (t + 1) = s[t] := pair_succ ht
  obtain ⟨x, y, hx, hy, hxy, hTx, hTy⟩ := exists_ends hs' (t := t + 1) (by omega) (by omega)
  rw [hpT] at hx hy
  have hxP : (x : ℤ) + 1 = (pair s (t + 1)).1 := by rwa [hpT]
  have hyP : (y : ℤ) + 1 = (pair s (t + 1)).2 := by rwa [hpT]
  have hxy' : (x : ℤ) + 1 < (y : ℤ) + 1 := by
    rw [hx, hy]
    exact (hs' _ (List.getElem_mem ht)).2.1
  have hyx : (y : ℤ) + 1 ≠ (pair s (t + 1)).1 := by rw [← hxP]; omega
  obtain ⟨hA, hB, hC, hB', hC'⟩ := hs.bridge_inequalities hf ht
  rw [← hx, ← hy] at hA hB hC hB' hC'
  have hIcc : ∀ (τ : ℕ) (z : Fin b), 1 ≤ (positionMap s τ).symm ((z : ℤ) + 1) ∧
      (positionMap s τ).symm ((z : ℤ) + 1) ≤ b := fun τ z =>
    positionMap_symm_mem_Icc (b := (b : ℤ)) hs.mem_Icc τ ⟨by omega, by have := z.isLt; omega⟩
  obtain ⟨la, hla⟩ := exists_label_eq (b := b) (hIcc t x)
  obtain ⟨lc, hlc⟩ := exists_label_eq (b := b) (hIcc t y)
  obtain ⟨lp, hlp⟩ := exists_label_eq (b := b) (hIcc s.length x)
  obtain ⟨lq, hlq⟩ := exists_label_eq (b := b) (hIcc s.length y)
  have hac : la < lc := Fin.lt_def.2 (by rw [← hla, ← hlc] at hA; omega)
  have hπp : (bridgeGraph b s γ).tripPerm lp = x := by
    have := tripPerm_bridgeGraph hs' γ lp
    rw [hlp, Equiv.apply_symm_apply] at this
    exact Fin.ext (by omega)
  have hπq : (bridgeGraph b s γ).tripPerm lq = y := by
    have := tripPerm_bridgeGraph hs' γ lq
    rw [hlq, Equiv.apply_symm_apply] at this
    exact Fin.ext (by omega)
  obtain ⟨hdx0, hmx0⟩ := dn_mem_oneWayTrip_bridgeGraph hb hs' hn γ (y := x) (τ := t)
    (u := prev s x (t + 1)) (by have := le_top hTx; omega) (prev_eq_zero_or_mem x (t + 1))
    (by have := prev_lt (s := s) (x := x) (u := t + 1) (by omega); omega)
    (notMem_Icc_prev_of_mem_heights x) hla
  obtain ⟨hdy0, hmy0⟩ := dn_mem_oneWayTrip_bridgeGraph hb hs' hn γ (y := y) (τ := t)
    (u := prev s y (t + 1)) (by have := le_top hTy; omega) (prev_eq_zero_or_mem y (t + 1))
    (by have := prev_lt (s := s) (x := y) (u := t + 1) (by omega); omega)
    (notMem_Icc_prev_of_mem_heights y) hlc
  have hmupx := up_mem_oneWayTrip_bridgeGraph hb hs' hn γ hTx hπp
  have hmupy := up_mem_oneWayTrip_bridgeGraph hb hs' hn γ hTy hπq
  have hmc' := bridgeRev_mem_oneWayTrip_bridgeGraph hb hs' hn γ hdT hyP hlc
  have trc : (bridgeGraph b s γ).tripSet ⟨.bridge (t + 1), hdT⟩ = {la} := by
    have e : (bridgeGraph b s γ).tripMap ⟨.dn x (prev s x (t + 1)), hdx0⟩ =
        ⟨.bridge (t + 1), hdT⟩ :=
      Subtype.ext ((tripMap_bridgeGraph_dn hs' γ (prev_lt_top hTx) (next_prev hTx) hdx0).1 hxP)
    have := hG.tripSet_tripMap (d := ⟨.dn x (prev s x (t + 1)), hdx0⟩) (by
      rw [e]
      exact hG.not_isLeg_of_not_isBoundaryVertex (bridgeGraph.not_isBoundaryVertex_bridge γ hdT))
    rwa [e, tripSet_eq_singleton hG hmx0] at this
  have lcT : (bridgeGraph b s γ).edgeLabel ((bridgeGraph b s γ).edgeOf ⟨.bridge (t + 1), hdT⟩) =
      {la, lc} := edgeLabel_edgeOf_eq_pair trc (tripSet_eq_singleton hG hmc')
  have lcT' : (bridgeGraph b s γ).edgeLabel
      ((bridgeGraph b s γ).edgeOf ⟨.bridgeRev (t + 1), hdT⟩) = {lc, la} :=
    edgeLabel_edgeOf_eq_pair (tripSet_eq_singleton hG hmc') trc
  have lux : (bridgeGraph b s γ).edgeLabel ((bridgeGraph b s γ).edgeOf ⟨.up x (t + 1), hTx⟩) =
      {lp, la} := edgeLabel_edgeOf_eq_pair (tripSet_eq_singleton hG hmupx)
    (tripSet_eq_singleton hG hmx0)
  have luy : (bridgeGraph b s γ).edgeLabel ((bridgeGraph b s γ).edgeOf ⟨.up y (t + 1), hTy⟩) =
      {lq, lc} := edgeLabel_edgeOf_eq_pair (tripSet_eq_singleton hG hmupy)
    (tripSet_eq_singleton hG hmy0)
  have rc : ∀ h : t + 1 < top s x, (bridgeGraph b s γ).rot.symm ⟨.bridge (t + 1), hdT⟩ =
      ⟨.dn x (t + 1), Or.inr ⟨hTx, h⟩⟩ := fun h => Subtype.ext (by
    rw [bridgeGraph.rot_symm_val, rotateInv_bridge_of_eq hxP, ite_eq_left h])
  have rc₀ : ¬t + 1 < top s x → (bridgeGraph b s γ).rot.symm ⟨.bridge (t + 1), hdT⟩ =
      ⟨.up x (t + 1), hTx⟩ := fun h => Subtype.ext (by
    rw [bridgeGraph.rot_symm_val, rotateInv_bridge_of_eq hxP, ite_eq_right h])
  have rux : (bridgeGraph b s γ).rot.symm ⟨.up x (t + 1), hTx⟩ = ⟨.bridge (t + 1), hdT⟩ :=
    Subtype.ext (by rw [bridgeGraph.rot_symm_val, rotateInv_up, ite_eq_left hxP])
  have rdx : ∀ h : t + 1 < top s x, (bridgeGraph b s γ).rot.symm ⟨.dn x (t + 1), Or.inr ⟨hTx, h⟩⟩ =
      ⟨.up x (t + 1), hTx⟩ := fun h => Subtype.ext (by
    rw [bridgeGraph.rot_symm_val, rotateInv_dn_of_ne_zero (by omega), ite_eq_left hxP])
  have rc' : (bridgeGraph b s γ).rot.symm ⟨.bridgeRev (t + 1), hdT⟩ = ⟨.up y (t + 1), hTy⟩ :=
    Subtype.ext (by
      rw [bridgeGraph.rot_symm_val, rotateInv_bridgeRev_of_eq hyP (by rw [← hxP, ← hyP]; omega)])
  have ruy : ∀ h : t + 1 < top s y, (bridgeGraph b s γ).rot.symm ⟨.up y (t + 1), hTy⟩ =
      ⟨.dn y (t + 1), Or.inr ⟨hTy, h⟩⟩ := fun h => Subtype.ext (by
    rw [bridgeGraph.rot_symm_val, rotateInv_up, ite_eq_right hyx, ite_eq_left h])
  have ruy₀ : ¬t + 1 < top s y → (bridgeGraph b s γ).rot.symm ⟨.up y (t + 1), hTy⟩ =
      ⟨.bridgeRev (t + 1), hdT⟩ := fun h => Subtype.ext (by
    rw [bridgeGraph.rot_symm_val, rotateInv_up, ite_eq_right hyx, ite_eq_right h])
  have rdy : ∀ h : t + 1 < top s y, (bridgeGraph b s γ).rot.symm ⟨.dn y (t + 1), Or.inr ⟨hTy, h⟩⟩ =
      ⟨.bridgeRev (t + 1), hdT⟩ := fun h => Subtype.ext (by
    rw [bridgeGraph.rot_symm_val, rotateInv_dn_of_ne_zero (by omega), ite_eq_right hyx])
  have hne : ∀ {d e : BridgeSymbol b} {hd : IsDart s d} {he : IsDart s e}, d ≠ e →
      (⟨d, hd⟩ : BridgeDart b s) ≠ ⟨e, he⟩ := fun h h' => h (congrArg Subtype.val h')
  constructor
  · by_cases h : t + 1 < top s x
    · have hc'' : (lc : ℤ) + 1 = (positionMap s (t + 1)).symm ((x : ℤ) + 1) := by
        rwa [positionMap_succ_symm_apply' ht, hx, Equiv.swap_apply_left, ← hy]
      obtain ⟨hdx, hmdx⟩ := dn_mem_oneWayTrip_bridgeGraph hb hs' hn γ (y := x) (τ := t + 1)
        (u := t + 1) h (Or.inr hTx) le_rfl (fun v _ hv => by rw [Finset.mem_Icc] at hv; omega) hc''
      have hmup := up_mem_oneWayTrip_bridgeGraph hb hs' hn γ (next_mem h) hπp
      have ldx : (bridgeGraph b s γ).edgeLabel
          ((bridgeGraph b s γ).edgeOf ⟨.dn x (t + 1), Or.inr ⟨hTx, h⟩⟩) = {lc, lp} := by
        rw [edgeLabel_edgeOf, show (bridgeGraph b s γ).inv ⟨.dn x (t + 1), Or.inr ⟨hTx, h⟩⟩ =
          ⟨.up x (next s x (t + 1)), next_mem h⟩ from Subtype.ext (reverse_dn_of_lt_top h),
          tripSet_eq_singleton hG hmdx, tripSet_eq_singleton hG hmup, ← insert_eq]
      rcases hB ((lt_top_iff_exists_later_pair hTx).1 h) with hp | hp
      · rw [← hla, ← hlp] at hp
        have hpa : lp < la := Fin.lt_def.2 (by omega)
        have := resonanceCondition_of_three rux (rc h) (rdx h) (hne (by simp)) (hne (by simp))
          (hne (by simp)) hpa hac lux lcT (by rw [ldx, pair_comm])
        rwa [← (bridgeGraph b s γ).vertexOf_eq_of_mem
          ((bridgeGraph b s γ).rot_symm_mem_vertexOf ⟨.up x (t + 1), hTx⟩), rux] at this
      · rw [← hlc, ← hlp] at hp
        have hcp : lc < lp := Fin.lt_def.2 (by omega)
        exact resonanceCondition_of_three (rc h) (rdx h) rux (hne (by simp)) (hne (by simp))
          (hne (by simp)) hac hcp lcT ldx (by rw [lux, pair_comm])
    · have hpc : lp = lc := Fin.ext (by
        have := hC fun hL => h ((lt_top_iff_exists_later_pair hTx).2 hL)
        rw [← hlp, ← hlc] at this
        omega)
      refine resonanceCondition_of_two (rc₀ h) rux (hne (by simp)) (card_pair hac.ne) lcT ?_
      rw [lux, hpc, pair_comm]
  · by_cases h : t + 1 < top s y
    · have ha'' : (la : ℤ) + 1 = (positionMap s (t + 1)).symm ((y : ℤ) + 1) := by
        rwa [positionMap_succ_symm_apply' ht, hy, Equiv.swap_apply_right, ← hx]
      obtain ⟨hdy, hmdy⟩ := dn_mem_oneWayTrip_bridgeGraph hb hs' hn γ (y := y) (τ := t + 1)
        (u := t + 1) h (Or.inr hTy) le_rfl (fun v _ hv => by rw [Finset.mem_Icc] at hv; omega) ha''
      have hmup := up_mem_oneWayTrip_bridgeGraph hb hs' hn γ (next_mem h) hπq
      have ldy : (bridgeGraph b s γ).edgeLabel
          ((bridgeGraph b s γ).edgeOf ⟨.dn y (t + 1), Or.inr ⟨hTy, h⟩⟩) = {la, lq} := by
        rw [edgeLabel_edgeOf, show (bridgeGraph b s γ).inv ⟨.dn y (t + 1), Or.inr ⟨hTy, h⟩⟩ =
          ⟨.up y (next s y (t + 1)), next_mem h⟩ from Subtype.ext (reverse_dn_of_lt_top h),
          tripSet_eq_singleton hG hmdy, tripSet_eq_singleton hG hmup, ← insert_eq]
      rcases hB' ((lt_top_iff_exists_later_pair hTy).1 h) with hq | hq
      · rw [← hla, ← hlq] at hq
        have hqa : lq < la := Fin.lt_def.2 (by omega)
        have := resonanceCondition_of_three (rdy h) rc' (ruy h) (hne (by simp)) (hne (by simp))
          (hne (by simp)) hqa hac (by rw [ldy, pair_comm]) (by rw [lcT', pair_comm]) luy
        rwa [← (bridgeGraph b s γ).vertexOf_eq_of_mem
          ((bridgeGraph b s γ).rot_symm_mem_vertexOf ⟨.dn y (t + 1), Or.inr ⟨hTy, h⟩⟩),
          rdy h] at this
      · rw [← hlc, ← hlq] at hq
        have hcq : lc < lq := Fin.lt_def.2 (by omega)
        exact resonanceCondition_of_three rc' (ruy h) (rdy h) (hne (by simp)) (hne (by simp))
          (hne (by simp)) hac hcq (by rw [lcT', pair_comm]) (by rw [luy, pair_comm]) ldy
    · have hqa : lq = la := Fin.ext (by
        have := hC' fun hL => h ((lt_top_iff_exists_later_pair hTy).2 hL)
        rw [← hlq, ← hla] at this
        omega)
      refine resonanceCondition_of_two rc' (ruy₀ h) (hne (by simp)) (card_pair hac.ne') lcT' ?_
      rw [luy, hqa, pair_comm]

end BridgeEnds

section BridgeResonance

open BridgeGraph BridgeSymbol PlabicData

variable {a b : ℕ} {f : ℤ → ℤ} {s : List (ℤ × ℤ)}

/-- The ends of every bridge of the bridge graph of a bridge sequence satisfy the resonance
condition. -/
private theorem IsBridgeSequence.resonanceCondition_bridge_bridgeRev
    (hf : IsBoundedAffinePerm a b f) (hs : IsBridgeSequence b f s) (γ : Fin b → Shade) {T : ℕ}
    (hT : IsDart (b := b) s (.bridge T)) :
    (bridgeGraph b s γ).ResonanceCondition ((bridgeGraph b s γ).vertexOf ⟨.bridge T, hT⟩) ∧
      (bridgeGraph b s γ).ResonanceCondition
        ((bridgeGraph b s γ).vertexOf ⟨.bridgeRev T, hT⟩) := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by have := hT.1; omega⟩
  have hp := hs.isBridgePair t (by have := hT.2; omega)
  have hb : 1 ≤ b := by
    have := hp.one_le
    have := hp.lt
    have := hp.le
    omega
  exact hs.resonanceCondition_bridgeEnds hb hf γ (by have := hT.2; omega) hT

/-- A vertex of the bridge graph containing a dart `c_T` satisfies the resonance condition. -/
private theorem IsBridgeSequence.resonanceCondition_of_bridge_mem (hf : IsBoundedAffinePerm a b f)
    (hs : IsBridgeSequence b f s) (γ : Fin b → Shade) {T : ℕ} (hT : IsDart (b := b) s (.bridge T))
    {e : BridgeDart b s}
    (he : (⟨.bridge T, hT⟩ : BridgeDart b s) ∈ (bridgeGraph b s γ).vertexOf e) :
    (bridgeGraph b s γ).ResonanceCondition ((bridgeGraph b s γ).vertexOf e) := by
  rw [← (bridgeGraph b s γ).vertexOf_eq_of_mem he]
  exact (hs.resonanceCondition_bridge_bridgeRev hf γ hT).1

/-- A vertex of the bridge graph containing a dart `c̄_T` satisfies the resonance condition. -/
private theorem IsBridgeSequence.resonanceCondition_of_bridgeRev_mem
    (hf : IsBoundedAffinePerm a b f) (hs : IsBridgeSequence b f s) (γ : Fin b → Shade) {T : ℕ}
    (hT : IsDart (b := b) s (.bridgeRev T)) {e : BridgeDart b s}
    (he : (⟨.bridgeRev T, hT⟩ : BridgeDart b s) ∈ (bridgeGraph b s γ).vertexOf e) :
    (bridgeGraph b s γ).ResonanceCondition ((bridgeGraph b s γ).vertexOf e) := by
  rw [← (bridgeGraph b s γ).vertexOf_eq_of_mem he]
  exact (hs.resonanceCondition_bridge_bridgeRev hf γ hT).2

/-- **Bridge graphs of bridge sequences have the resonance property.** If `f` is an
`(a, b)`-bounded affine permutation and `s` a bridge sequence for `f`, then the bridge graph
`G(s, γ)` has the resonance property for every colouring `γ` of its lollipops. -/
theorem IsBridgeSequence.hasResonanceProperty_bridgeGraph (hf : IsBoundedAffinePerm a b f)
    (hs : IsBridgeSequence b f s) (γ : Fin b → Shade) :
    (bridgeGraph b s γ).HasResonanceProperty := by
  have hbridge : ∀ {u : ℕ} {x : Fin b}, u ∈ heights s x → IsDart (b := b) s (.bridge u) :=
    fun hu => ⟨pos_of_mem_heights hu, le_length_of_mem_heights hu⟩
  intro v hv hlol
  obtain ⟨hvV, hvB⟩ := (bridgeGraph b s γ).mem_internalVertices.1 hv
  obtain ⟨⟨d, hd⟩, rfl⟩ := (bridgeGraph b s γ).mem_vertices.1 hvV
  cases d with
  | bdry x =>
    exact absurd ((bridgeGraph b s γ).isBoundaryVertex_vertexOf_of_mem (d := ⟨.bdry x, hd⟩)
      (bridgeGraph.mem_bdry.2 trivial)) hvB
  | bdryRev x =>
    exact absurd ((bridgeGraph b s γ).isBoundaryVertex_vertexOf_of_mem (d := ⟨.bdryRev x, hd⟩)
      (bridgeGraph.mem_bdry.2 trivial)) hvB
  | lam x =>
    exfalso
    have h1 : ((bridgeGraph b s γ).rot.symm ^ 1) ⟨.lam x, hd⟩ = ⟨.lam x, hd⟩ := by
      rw [pow_one]
      rfl
    refine hlol x ⟨⟨hv, ?_⟩, ⟨.lam x, hd⟩, (bridgeGraph b s γ).self_mem_vertexOf _,
      (bridgeGraph b s γ).self_mem_vertexOf _⟩
    rw [vertexOf_eq_image_range one_pos h1]
    simp
  | dn x u =>
    rcases Nat.eq_zero_or_pos u with rfl | hu
    · exact absurd (bridgeGraph.isBoundaryVertex_leg x) hvB
    · obtain ⟨hux, -⟩ := hd.resolve_left (by omega)
      by_cases hl : (x : ℤ) + 1 = (pair s u).1
      · refine hs.resonanceCondition_of_bridge_mem hf γ (hbridge hux) ?_
        have e : (bridgeGraph b s γ).rot ⟨.dn x u, hd⟩ = ⟨.bridge u, hbridge hux⟩ :=
          Subtype.ext (by rw [bridgeGraph.rot_val, rotate_dn_of_ne_zero (by omega), ite_eq_left hl])
        rw [← e]
        exact (bridgeGraph b s γ).rot_mem_vertexOf _
      · refine hs.resonanceCondition_of_bridgeRev_mem hf γ (hbridge hux) ?_
        have e : (bridgeGraph b s γ).rot.symm ⟨.dn x u, hd⟩ = ⟨.bridgeRev u, hbridge hux⟩ :=
          Subtype.ext (by
            rw [bridgeGraph.rot_symm_val, rotateInv_dn_of_ne_zero (by omega), ite_eq_right hl])
        rw [← e]
        exact (bridgeGraph b s γ).rot_symm_mem_vertexOf _
  | up x u =>
    have hux : u ∈ heights s x := hd
    by_cases hl : (x : ℤ) + 1 = (pair s u).1
    · refine hs.resonanceCondition_of_bridge_mem hf γ (hbridge hux) ?_
      have e : (bridgeGraph b s γ).rot.symm ⟨.up x u, hd⟩ = ⟨.bridge u, hbridge hux⟩ :=
        Subtype.ext (by rw [bridgeGraph.rot_symm_val, rotateInv_up, ite_eq_left hl])
      rw [← e]
      exact (bridgeGraph b s γ).rot_symm_mem_vertexOf _
    · refine hs.resonanceCondition_of_bridgeRev_mem hf γ (hbridge hux) ?_
      have e : (bridgeGraph b s γ).rot ⟨.up x u, hd⟩ = ⟨.bridgeRev u, hbridge hux⟩ :=
        Subtype.ext (by rw [bridgeGraph.rot_val, rotate_up, ite_eq_right hl])
      rw [← e]
      exact (bridgeGraph b s γ).rot_mem_vertexOf _
  | bridge t =>
    exact hs.resonanceCondition_of_bridge_mem hf γ hd ((bridgeGraph b s γ).self_mem_vertexOf _)
  | bridgeRev t =>
    exact hs.resonanceCondition_of_bridgeRev_mem hf γ hd ((bridgeGraph b s γ).self_mem_vertexOf _)

/-- If `π̃` is a decorated permutation on `b` letters and `s` a bridge sequence for its
affinization, then the bridge decomposition `G(π̃, s)` has the resonance property. -/
@[cluster_algebras "lem_bridge_resonance"]
theorem DecoratedPerm.hasResonanceProperty_bridgeDecomposition (π : DecoratedPerm b)
    (hs : IsBridgeSequence b π.affinization s) :
    (π.bridgeDecomposition s).HasResonanceProperty :=
  hs.hasResonanceProperty_bridgeGraph π.isBoundedAffinePerm_affinization _

end BridgeResonance

end ClusterAlgebras
