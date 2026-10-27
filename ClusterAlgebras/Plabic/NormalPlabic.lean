/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.Trips

/-!
# Normal plabic graphs, recolouring lollipops, bad features, sides of loops

A plabic graph is *normal* if every edge joining two internal vertices joins a white vertex to a
black one, every white vertex has exactly three darts, and every leg runs to a black vertex. In a
normal plabic graph the far end of every dart at a white vertex is a black internal vertex.

The *recolouring* `R_i(G)` of a plabic graph at a label `i` exchanges the colour of the lollipop
at `i`, if there is one, and does nothing otherwise. It is again a plabic graph, with the same
trip map: the only dart whose turn could change is the single dart `ḡ_i` of the lollipop, and
there `σ(ḡ_i) = σ⁻¹(ḡ_i) = ḡ_i`.

A *trip* is a one-way trip or a roundtrip. A plabic graph *has a bad feature* if it has a
roundtrip, an *essential self-intersection* (a dart `d ∉ B` whose ends are internal vertices,
with `d` and `d̄` on one trip) or a *bad double crossing* (two distinct trips traversing two
distinct edges in the same order).

Finally, for an internal vertex `u` whose rotation is the cycle
`(d, a₁, …, a_k, d̄, b₁, …, b_l)`, the *side* of `(u, d)` is the set of darts reached from `a₁`
by steps avoiding `d` and `d̄`: across an edge, along the rotation at a vertex other than `u`, or
within one of the two arcs `{a₁, …, a_k}`, `{b₁, …, b_l}` of `u`.

## Main definitions

* `ClusterAlgebras.PlabicData.IsNormal`, `ClusterAlgebras.PlabicData.IsNormalPlabicGraph`:
  the conditions of normality, and normal plabic graphs.
* `ClusterAlgebras.PlabicData.recolourLollipop`: the recolouring `R_i(G)` of a lollipop.
* `ClusterAlgebras.PlabicData.Trip`, `ClusterAlgebras.PlabicData.IsEssentialSelfIntersection`,
  `ClusterAlgebras.PlabicData.IsBadDoubleCrossing`, `ClusterAlgebras.PlabicData.HasBadFeature`:
  trips, essential self-intersections, bad double crossings and bad features.
* `ClusterAlgebras.RotationSystem.loopSide`: the side of a loop.

## Main results

* `ClusterAlgebras.PlabicData.IsNormalPlabicGraph.inv_internal_black_of_white`: in a normal
  plabic graph the far end of a dart at a white vertex is a black internal vertex.
* `ClusterAlgebras.PlabicData.IsPlabicGraph.recolourLollipop`,
  `ClusterAlgebras.PlabicData.tripMap_recolourLollipop`: recolouring a lollipop gives a plabic
  graph with the same trip map.

## Implementation notes

* **Colours.** As throughout the chapter, colours are recorded on darts (`PlabicData.colour`), and
  a white (black) vertex is an internal vertex whose darts are white (black). "The leg `g_i` runs
  to a black vertex" means that `v(ḡ_i)` is internal and black. An edge `{d, d̄}` joins a white
  vertex to a black one exactly when the colours of `d` and `d̄` differ, there being two colours.
* **Normality.** `IsNormal` collects the three conditions of normality on the data of a plabic
  graph, so that tuples satisfying only some of the conditions of a plabic graph can be required
  to satisfy them; `IsNormalPlabicGraph` is `IsPlabicGraph` together with `IsNormal`.
* **Recolouring.** `R_i(G)` is defined for all data: the colour of the darts of the vertex
  `v(ḡ_i)`, with `g_i = leg i`, is exchanged when that vertex is internal with one dart. The disk
  map and the labelling are those of `G`, definitionally.
* **Trips.** A trip is an element of the type `PlabicData.Trip`, a one-way trip `oneWay i` from a
  label `i` or a roundtrip `round O` given by its orbit `O`; its darts are `Trip.darts`. Two trips
  are distinct when they are distinct elements of this type; for a plabic graph this is
  distinctness of their sets of darts (`IsPlabicGraph.darts_injective`). A trip traverses the edge
  `e` when one of its darts lies in `e`. "Later" refers to the positions `k` of the darts
  `Tᵏ(g_i)`, `0 ≤ k < m_i`, of the one-way trip from `i` (`Trip.TraversesThen`); a roundtrip
  traverses `e₂` later than `e₁` whenever it traverses both. The edges of the graph are the edges
  `{d, d̄}` of the rotation system disjoint from `B`.
* **Sides of loops.** For a dart `d` the rotation at `u = v(d)` is read from `d`: the arc
  `{a₁, …, a_k}` is `rotArc d d̄`, the darts `σᵐ(d)` with `0 < m` before the first return of the
  rotation to `d̄`, and `{b₁, …, b_l}` is `rotArc d̄ d`; then `a₁ = σ(d)`. The sequences
  `z₀ = a₁, …, z_n = z` of [FWZ] are the `Relation.ReflTransGen` of the step relation
  `RotationSystem.LoopStep`. The definition makes sense for every dart; it is the side of [FWZ]
  when `d̄ ∈ v(d)` and `σ(d) ≠ d̄`.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} (G : PlabicData H b)

/-! ### Normal plabic graphs -/

/-- The conditions of **normality** on the data of a plabic graph: every edge joining two
internal vertices joins a white vertex to a black one, every white vertex consists of exactly
three darts, and every leg `g_i` runs to a black (internal) vertex. -/
@[cluster_algebras "def_normal_plabic_graph"]
structure IsNormal : Prop where
  /-- An edge `{d, d̄}` joining two internal vertices joins vertices of distinct colours. -/
  colour_inv_ne : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) →
    ¬G.IsBoundaryVertex (G.vertexOf (G.inv d)) → G.colour (G.inv d) ≠ G.colour d
  /-- Every white vertex consists of exactly three darts. -/
  card_vertexOf_of_white : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G.colour d = .white →
    (G.vertexOf d).card = 3
  /-- Every leg `g_i` runs to an internal vertex. -/
  not_isBoundaryVertex_inv_leg : ∀ i, ¬G.IsBoundaryVertex (G.vertexOf (G.inv (G.leg i)))
  /-- Every leg `g_i` runs to a black vertex. -/
  colour_inv_leg : ∀ i, G.colour (G.inv (G.leg i)) = .black

/-- A **normal plabic graph**: a plabic graph in which every edge joining two internal vertices
joins a white vertex to a black one, every white vertex consists of exactly three darts, and for
every `i` the leg `g_i` runs to a black vertex. -/
@[cluster_algebras "def_normal_plabic_graph"]
structure IsNormalPlabicGraph : Prop extends G.IsPlabicGraph, G.IsNormal

variable {G}

/-- In a normal plabic graph, if `a` is a dart at a white vertex `w`, then `v(ā)` is a black
internal vertex. -/
@[cluster_algebras "lem_normal_white_partner"]
theorem IsNormalPlabicGraph.inv_internal_black_of_white (hG : G.IsNormalPlabicGraph) {a : H}
    (ha : ¬G.IsBoundaryVertex (G.vertexOf a)) (hc : G.colour a = .white) :
    ¬G.IsBoundaryVertex (G.vertexOf (G.inv a)) ∧ G.colour (G.inv a) = .black := by
  have hb : ¬G.IsBoundaryVertex (G.vertexOf (G.inv a)) := by
    intro hb
    have haB : a ∉ G.bdry := notMem_bdry_of_mem_vertexOf ha (G.self_mem_vertexOf a)
    have hiB : G.inv a ∉ G.bdry := fun h => haB ((hG.inv_mem_bdry_iff).1 h)
    obtain ⟨i, hi⟩ := hG.exists_bvertex_eq _ (G.vertexOf_mem_boundaryVertices.2 hb)
    have hmem : G.inv a ∈ (G.bvertex i).filter (· ∉ G.bdry) :=
      mem_filter.2 ⟨hi ▸ G.self_mem_vertexOf _, hiB⟩
    rw [hG.filter_bvertex_notMem_bdry, mem_singleton] at hmem
    have := hG.colour_inv_leg i
    rw [← hmem, hG.inv_involutive a, hc] at this
    exact Shade.noConfusion this
  refine ⟨hb, ?_⟩
  have := hG.colour_inv_ne a ha hb
  rw [hc] at this
  cases h : G.colour (G.inv a)
  · exact absurd h this
  · rfl

/-! ### Recolouring a lollipop -/

variable (G)

/-- The **recolouring of `G` at `i`**, written `R_i(G)`: if the vertex `v(ḡ_i)` (with
`g_i = leg i`) is an internal vertex consisting of exactly one dart, the colour of that vertex is
exchanged for the other colour; otherwise `R_i(G) = G`. The disk map and the labelling are
unchanged. -/
@[cluster_algebras "def_lollipop_recolouring"]
def recolourLollipop (i : Fin b) : PlabicData H b :=
  letI : Decidable (G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i)))) :=
    inferInstanceAs (Decidable (_ ∧ _))
  { G with
    colour := fun d =>
      if G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧ d ∈ G.vertexOf (G.inv (G.leg i)) then
        (G.colour d).swap
      else G.colour d }

variable {G}

/-- Recolouring a lollipop does not change the disk map. -/
@[simp]
theorem toDiskMap_recolourLollipop (i : Fin b) : (G.recolourLollipop i).toDiskMap = G.toDiskMap :=
  rfl

/-- Recolouring a lollipop does not change the labelling. -/
@[simp]
theorem leg_recolourLollipop (i : Fin b) : (G.recolourLollipop i).leg = G.leg := rfl

/-- If `v(ḡ_i)` is an internal leaf, `R_i(G)` swaps the colour of each dart of `v(ḡ_i)`. -/
theorem colour_recolourLollipop_of_mem {i : Fin b}
    (hi : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i)))) {d : H}
    (hd : d ∈ G.vertexOf (G.inv (G.leg i))) :
    (G.recolourLollipop i).colour d = (G.colour d).swap := by
  simp only [recolourLollipop]
  rw [if_pos ⟨hi, hd⟩]

/-- Unless `v(ḡ_i)` is an internal leaf containing `d`, `R_i(G)` keeps the colour of `d`. -/
theorem colour_recolourLollipop_of_notMem {i : Fin b} {d : H}
    (hd : ¬(G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
      d ∈ G.vertexOf (G.inv (G.leg i)))) :
    (G.recolourLollipop i).colour d = G.colour d := by
  simp only [recolourLollipop]
  rw [if_neg hd]

omit [Fintype H] [DecidableEq H] in
/-- Data of plabic graphs with the same disk map, colours and labelling are equal. -/
private theorem ext_of_colour {G G' : PlabicData H b} (h₁ : G.toDiskMap = G'.toDiskMap)
    (h₂ : G.colour = G'.colour) (h₃ : G.leg = G'.leg) : G = G' := by
  cases G
  cases G'
  simp_all

/-- If `v(ḡ_i)` is not an internal vertex with one dart, `R_i(G) = G`. -/
theorem recolourLollipop_eq_self {i : Fin b}
    (hi : ¬G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i)))) : G.recolourLollipop i = G := by
  have hc : (G.recolourLollipop i).colour = G.colour :=
    funext fun d => colour_recolourLollipop_of_notMem fun h => hi h.1
  exact ext_of_colour rfl hc rfl

/-- Recolouring twice at the same label gives back the graph: `R_i(R_i(G)) = G`. -/
@[simp]
theorem recolourLollipop_recolourLollipop (i : Fin b) :
    (G.recolourLollipop i).recolourLollipop i = G := by
  by_cases hi : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i)))
  · have hc : ((G.recolourLollipop i).recolourLollipop i).colour = G.colour := by
      funext d
      by_cases hd : d ∈ G.vertexOf (G.inv (G.leg i))
      · rw [colour_recolourLollipop_of_mem (G := G.recolourLollipop i) hi hd,
          colour_recolourLollipop_of_mem hi hd]
        cases G.colour d <;> rfl
      · rw [colour_recolourLollipop_of_notMem (G := G.recolourLollipop i) fun h => hd h.2,
          colour_recolourLollipop_of_notMem fun h => hd h.2]
    exact ext_of_colour rfl hc rfl
  · rw [recolourLollipop_eq_self hi, recolourLollipop_eq_self hi]

/-- Recolouring a lollipop does not change the turns. -/
@[simp]
theorem turn_recolourLollipop (i : Fin b) (z : H) : (G.recolourLollipop i).turn z = G.turn z := by
  by_cases hz : G.IsBoundaryVertex (G.vertexOf z)
  · rw [turn_of_isBoundaryVertex hz, turn_of_isBoundaryVertex (G := G.recolourLollipop i) hz]
  have hz' : ¬(G.recolourLollipop i).IsBoundaryVertex ((G.recolourLollipop i).vertexOf z) := hz
  by_cases h : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
      z ∈ G.vertexOf (G.inv (G.leg i))
  · have hcard : (G.vertexOf z).card = 1 := by
      rw [G.vertexOf_eq_of_mem h.2]
      exact h.1.2
    have h1 : G.rot z = z :=
      card_le_one.1 hcard.le _ (G.rot_mem_vertexOf z) _ (G.self_mem_vertexOf z)
    have h2 : G.rot.symm z = z :=
      card_le_one.1 hcard.le _ (G.rot_symm_mem_vertexOf z) _ (G.self_mem_vertexOf z)
    unfold turn
    rw [if_neg hz, if_neg hz']
    cases (G.recolourLollipop i).colour z <;> cases G.colour z <;>
      simp only [toDiskMap_recolourLollipop, h1, h2]
  · have hc := colour_recolourLollipop_of_notMem h
    unfold turn
    rw [if_neg hz, if_neg hz', hc]
    rfl

/-- **Recolouring a lollipop keeps the trip map**: the trip map of `R_i(G)` is the trip map of
`G`. This holds for all data, on all darts. -/
@[simp, cluster_algebras "lem_recolouring_plabic"]
theorem tripMap_recolourLollipop (i : Fin b) : (G.recolourLollipop i).tripMap = G.tripMap :=
  funext fun d => turn_recolourLollipop i (G.inv d)

/-- If `G` is a plabic graph with `b` boundary vertices, so is its recolouring `R_i(G)`. -/
@[cluster_algebras "lem_recolouring_plabic"]
theorem IsPlabicGraph.recolourLollipop (hG : G.IsPlabicGraph) (i : Fin b) :
    (G.recolourLollipop i).IsPlabicGraph where
  toIsDiskMap := hG.toIsDiskMap
  one_le := hG.one_le
  colour_rot d hd := by
    have hd' : ¬G.IsBoundaryVertex (G.vertexOf d) := hd
    change (G.recolourLollipop i).colour (G.rot d) = (G.recolourLollipop i).colour d
    have hmem : G.rot d ∈ G.vertexOf (G.inv (G.leg i)) ↔ d ∈ G.vertexOf (G.inv (G.leg i)) := by
      simp only [RotationSystem.mem_vertexOf, Equiv.Perm.sameCycle_apply_right]
    by_cases h : G.IsInternalLeaf (G.vertexOf (G.inv (G.leg i))) ∧
        d ∈ G.vertexOf (G.inv (G.leg i))
    · rw [colour_recolourLollipop_of_mem h.1 h.2, colour_recolourLollipop_of_mem h.1
        (hmem.2 h.2), hG.colour_rot d hd']
    · rw [colour_recolourLollipop_of_notMem h, colour_recolourLollipop_of_notMem
        (by rwa [hmem]), hG.colour_rot d hd']
  leg_notMem_bdry := hG.leg_notMem_bdry
  bvertex_mem := hG.bvertex_mem
  bvertex_injective := hG.bvertex_injective
  exists_bvertex_eq := hG.exists_bvertex_eq
  exists_exterior := hG.exists_exterior

/-! ### Bad features -/

variable (G)

/-- A **trip**: a one-way trip, given by its starting label `i`, or a roundtrip, given by its
orbit `O`. -/
@[cluster_algebras "def_bad_feature"]
inductive Trip : Type _
  /-- The one-way trip from the label `i`. -/
  | oneWay (i : Fin b) : Trip
  /-- The roundtrip whose darts are the orbit `O`. -/
  | round (O : Set H) (hO : G.IsRoundtrip O) : Trip

variable {G}

namespace Trip

/-- The set of darts of a trip: the darts `Tᵏ(g_i)`, `0 ≤ k < m_i`, of the one-way trip from `i`,
or the orbit of a roundtrip. -/
def darts : G.Trip → Set H
  | oneWay i => {d | d ∈ G.oneWayTrip i}
  | round O _ => O

/-- The trip `τ` **traverses `e₁` and later traverses `e₂`**: for the one-way trip from `i`, some
dart `Tᵖ¹(g_i) ∈ e₁` comes before some dart `Tᵖ²(g_i) ∈ e₂`, `p₁ < p₂ < m_i`; for a roundtrip,
some dart lies in `e₁` and some dart lies in `e₂`. -/
def TraversesThen : G.Trip → Finset H → Finset H → Prop
  | oneWay i, e₁, e₂ => ∃ p₁ p₂, p₁ < p₂ ∧ p₂ < G.tripLength i ∧
      G.tripMap^[p₁] (G.leg i) ∈ e₁ ∧ G.tripMap^[p₂] (G.leg i) ∈ e₂
  | round O _, e₁, e₂ => (∃ d ∈ O, d ∈ e₁) ∧ ∃ d ∈ O, d ∈ e₂

/-- The darts of the one-way trip from `i` are the darts `Tᵏ(g_i)` with `k < m_i`. -/
@[simp]
theorem mem_darts_oneWay {i : Fin b} {d : H} :
    d ∈ (oneWay i : G.Trip).darts ↔ ∃ k < G.tripLength i, G.tripMap^[k] (G.leg i) = d :=
  mem_oneWayTrip

/-- The darts of a roundtrip are its orbit. -/
@[simp]
theorem darts_round {O : Set H} (hO : G.IsRoundtrip O) : (round O hO : G.Trip).darts = O := rfl

end Trip

variable (G)

/-- An **essential self-intersection**: a dart `d ∉ B` such that `v(d)` and `v(d̄)` are internal
vertices and `d` and `d̄` belong to the same trip. -/
@[cluster_algebras "def_bad_feature"]
def IsEssentialSelfIntersection (d : H) : Prop :=
  d ∉ G.bdry ∧ ¬G.IsBoundaryVertex (G.vertexOf d) ∧ ¬G.IsBoundaryVertex (G.vertexOf (G.inv d)) ∧
    ∃ τ : G.Trip, d ∈ τ.darts ∧ G.inv d ∈ τ.darts

/-- A **bad double crossing**: two distinct trips `τ ≠ τ'` and two distinct edges `e₁ ≠ e₂` of
the graph (edges of the rotation system disjoint from `B`) such that each of `τ`, `τ'` traverses
`e₁` and later traverses `e₂`. -/
@[cluster_algebras "def_bad_feature"]
def IsBadDoubleCrossing (τ τ' : G.Trip) (e₁ e₂ : Finset H) : Prop :=
  τ ≠ τ' ∧ e₁ ∈ G.edges ∧ Disjoint e₁ G.bdry ∧ e₂ ∈ G.edges ∧ Disjoint e₂ G.bdry ∧ e₁ ≠ e₂ ∧
    τ.TraversesThen e₁ e₂ ∧ τ'.TraversesThen e₁ e₂

/-- A plabic graph **has a bad feature** if it has a roundtrip, an essential self-intersection or
a bad double crossing. -/
@[cluster_algebras "def_bad_feature"]
def HasBadFeature : Prop :=
  G.HasRoundtrip ∨ (∃ d, G.IsEssentialSelfIntersection d) ∨
    ∃ τ τ' e₁ e₂, G.IsBadDoubleCrossing τ τ' e₁ e₂

variable {G}

/-- In a plabic graph, distinct trips have distinct sets of darts. -/
theorem IsPlabicGraph.darts_injective (hG : G.IsPlabicGraph) :
    Function.Injective (Trip.darts (G := G)) := by
  have hleg : ∀ i, G.leg i ∈ (Trip.oneWay i : G.Trip).darts := fun i =>
    Trip.mem_darts_oneWay.2 ⟨0, hG.tripLength_pos i, rfl⟩
  have hone : ∀ i j, G.leg i ∈ (Trip.oneWay j : G.Trip).darts → i = j := by
    intro i j h
    obtain ⟨k, hk, hkd⟩ := Trip.mem_darts_oneWay.1 h
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact hG.leg_injective hkd.symm
    · exact absurd ⟨i, hkd.symm⟩ (not_isLeg_of_lt_tripLength hk0 hk)
  rintro (i | ⟨O, hO⟩) (j | ⟨O', hO'⟩) h
  · rw [hone i j (h ▸ hleg i)]
  · obtain ⟨d, hd, hdO, hl⟩ := hO'
    have hi := hleg i
    rw [h, Trip.darts_round] at hi
    exact (hl i hi).elim
  · obtain ⟨d, hd, hdO, hl⟩ := hO
    have hj := hleg j
    rw [← h, Trip.darts_round] at hj
    exact (hl j hj).elim
  · simp only [Trip.darts_round] at h
    subst h
    rfl

end PlabicData

/-! ### The side of a loop -/

namespace RotationSystem

variable {H : Type*} [Fintype H] [DecidableEq H] (R : RotationSystem H)

/-- The first positive `m` with `σᵐ(x) = y`, and `0` if there is none. -/
noncomputable def rotDist (x y : H) : ℕ := sInf {m | 0 < m ∧ (R.rot ^ m) x = y}

/-- The **open arc** of the rotation from `x` to `y`: the darts `σᵐ(x)` with `0 < m` met before
the rotation first reaches `y`. If the rotation at `v(x)` is the cycle
`(x, a₁, …, a_k, y, …)`, this is `{a₁, …, a_k}`; if `y ∉ v(x)`, it is empty. -/
def rotArc (x y : H) : Set H := {a | ∃ m, 0 < m ∧ m < R.rotDist x y ∧ (R.rot ^ m) x = a}

/-- A **step** `z → z'` of `loopSide` for the dart `d` at `u = v(d)`, whose rotation is the
cycle `(d, a₁, …, a_k, d̄, b₁, …, b_l)`: both darts lie outside `{d, d̄}`, and `z' = z̄`, or
`z' = σ^{±1}(z)` with `z ∉ u`, or both darts lie in `{a₁, …, a_k}`, or both lie in
`{b₁, …, b_l}`. -/
def LoopStep (d z z' : H) : Prop :=
  z ≠ d ∧ z ≠ R.inv d ∧ z' ≠ d ∧ z' ≠ R.inv d ∧
    (z' = R.inv z ∨ (z ∉ R.vertexOf d ∧ (z' = R.rot z ∨ z' = R.rot.symm z)) ∨
      (z ∈ R.rotArc d (R.inv d) ∧ z' ∈ R.rotArc d (R.inv d)) ∨
      (z ∈ R.rotArc (R.inv d) d ∧ z' ∈ R.rotArc (R.inv d) d))

/-- The **side** of `(u, d)`, for a dart `d` at a vertex `u = v(d)` whose rotation is the cycle
`(d, a₁, …, a_k, d̄, b₁, …, b_l)` with `k ≥ 1`: the set of darts `z ∉ {d, d̄}` reached from
`a₁ = σ(d)` by a sequence `z₀ = a₁, z₁, …, z_n = z` of darts outside `{d, d̄}` in which each
`z_{j+1}` is `z̄_j`, or `σ^{±1}(z_j)` with `z_j ∉ u`, or `z_j` and `z_{j+1}` both lie in
`{a₁, …, a_k}` or both lie in `{b₁, …, b_l}`. -/
@[cluster_algebras "def_loop_side"]
def loopSide (d : H) : Set H :=
  {z | z ≠ d ∧ z ≠ R.inv d ∧ Relation.ReflTransGen (R.LoopStep d) (R.rot d) z}

variable {R}

omit [Fintype H] [DecidableEq H] in
/-- `a` lies in `rotArc x y` iff `a = σᵐ(x)` for some `0 < m < rotDist x y`. -/
theorem mem_rotArc {x y a : H} :
    a ∈ R.rotArc x y ↔ ∃ m, 0 < m ∧ m < R.rotDist x y ∧ (R.rot ^ m) x = a :=
  Iff.rfl

/-- `z` lies in the side of `(u, d)` iff `z ∉ {d, d̄}` and `z` is reached from `σ(d)` by steps. -/
theorem mem_loopSide {d z : H} :
    z ∈ R.loopSide d ↔ z ≠ d ∧ z ≠ R.inv d ∧ Relation.ReflTransGen (R.LoopStep d) (R.rot d) z :=
  Iff.rfl

/-- If `y ∈ v(x)`, the rotation reaches `y` from `x` after `rotDist x y ≥ 1` steps. -/
theorem rotDist_spec {x y : H} (h : y ∈ R.vertexOf x) :
    0 < R.rotDist x y ∧ (R.rot ^ R.rotDist x y) x = y := by
  obtain ⟨n, hn⟩ := (R.mem_vertexOf.1 h).exists_nat_pow_eq
  have hpos := (isOfFinOrder_of_finite R.rot).orderOf_pos
  refine Nat.sInf_mem (s := {m | 0 < m ∧ (R.rot ^ m) x = y}) ⟨n + orderOf R.rot, by omega, ?_⟩
  rw [pow_add, pow_orderOf_eq_one, mul_one, hn]

/-- If `y ∈ v(x)` and `σ(x) ≠ y`, then `σ(x)` lies in the arc `rotArc x y`; in particular the
arc `{a₁, …, a_k}` from `d` to `d̄` starts at `a₁ = σ(d)`. -/
theorem rot_mem_rotArc {x y : H} (h : y ∈ R.vertexOf x) (hne : R.rot x ≠ y) :
    R.rot x ∈ R.rotArc x y := by
  obtain ⟨hpos, hy⟩ := rotDist_spec h
  refine ⟨1, one_pos, ?_, by rw [pow_one]⟩
  rcases Nat.lt_or_ge 1 (R.rotDist x y) with h1 | h1
  · exact h1
  · have : R.rotDist x y = 1 := by omega
    rw [this, pow_one] at hy
    exact absurd hy hne

/-- The steps `LoopStep` are reversible. -/
theorem LoopStep.symm (hinv : Function.Involutive R.inv) {d z z' : H}
    (h : R.LoopStep d z z') : R.LoopStep d z' z := by
  obtain ⟨h1, h2, h3, h4, h⟩ := h
  refine ⟨h3, h4, h1, h2, ?_⟩
  rcases h with h | ⟨hu, h | h⟩ | ⟨ha, ha'⟩ | ⟨hb, hb'⟩
  · exact Or.inl (by rw [h, hinv z])
  · refine Or.inr (Or.inl ⟨?_, Or.inr (by rw [h, Equiv.symm_apply_apply])⟩)
    rwa [h, RotationSystem.mem_vertexOf, Equiv.Perm.sameCycle_apply_right,
      ← RotationSystem.mem_vertexOf]
  · refine Or.inr (Or.inl ⟨?_, Or.inl (by rw [h, Equiv.apply_symm_apply])⟩)
    rwa [h, RotationSystem.mem_vertexOf, Equiv.Perm.sameCycle_symm_apply_right,
      ← RotationSystem.mem_vertexOf]
  · exact Or.inr (Or.inr (Or.inl ⟨ha', ha⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb', hb⟩))

/-- The side of `(u, d)` is closed under the steps `LoopStep`. -/
theorem LoopStep.mem_loopSide {d z z' : H} (hz : z ∈ R.loopSide d) (h : R.LoopStep d z z') :
    z' ∈ R.loopSide d :=
  ⟨h.2.2.1, h.2.2.2.1, hz.2.2.tail h⟩

/-- `a₁ = σ(d)` lies in the side of `(u, d)` when it is neither `d` nor `d̄`. -/
theorem rot_mem_loopSide {d : H} (h₁ : R.rot d ≠ d) (h₂ : R.rot d ≠ R.inv d) :
    R.rot d ∈ R.loopSide d :=
  ⟨h₁, h₂, Relation.ReflTransGen.refl⟩

/-- The steps being reversible, a dart `z ∉ {d, d̄}` lies in the side of `(u, d)` exactly when
`a₁ = σ(d)` is reached from `z` by steps. -/
theorem mem_loopSide_iff (hinv : Function.Involutive R.inv) {d z : H} :
    z ∈ R.loopSide d ↔
      z ≠ d ∧ z ≠ R.inv d ∧ Relation.ReflTransGen (R.LoopStep d) z (R.rot d) := by
  have : Std.Symm (R.LoopStep d) := ⟨fun _ _ h => h.symm hinv⟩
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨Relation.ReflTransGen.stdSymm.symm _ _, Relation.ReflTransGen.stdSymm.symm _ _⟩

end RotationSystem

end ClusterAlgebras
