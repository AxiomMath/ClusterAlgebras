/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.DecoratedPermutation
public import ClusterAlgebras.Plabic.EdgeContractionMoves
public import ClusterAlgebras.Plabic.LocalMoves
public import ClusterAlgebras.Plabic.Trees
public import ClusterAlgebras.Plabic.Trips

/-!
# Reduced plabic graphs

A rooted tree `T = (v, W)` of a plabic graph `G` is *collapsible of colour `c`* if the plabic
graph `P_T` formed by `T` alone is `{M2, M3}`-equivalent to the lollipop graph `L_c`, and either
the root `v` is internal of colour `c`, or `v` is a boundary vertex and `|W| ≥ 2`. A plabic graph
`G` is *reduced* if no plabic graph `G' ∼ G` contains a hollow digon, or an internal leaf that is
neither a lollipop nor a non-root vertex of a collapsible tree of `G'`; by construction this is
invariant under move equivalence.

The *decorated trip permutation* of `G` colours each fixed point `i` of the trip permutation `π_G`
white if `G` has a white lollipop at `i` or a white collapsible tree rooted at `β(i)`, and black
otherwise. Two plabic graphs are *nearly leafless equivalent* if they are joined by a sequence of
isomorphisms and local moves all of whose terms are nearly leafless.

The plabic graphs with one boundary vertex and exactly one face, the *plabic trees*, carry a
confluence theory for the moves (M2) and (M3) applied in the reducing direction: a *reduction step*
removes a bivalent vertex or contracts an edge joining two internal vertices of the same colour.

## Main definitions

* `ClusterAlgebras.PlabicData.RootedTree.IsCollapsibleOfColour`,
  `ClusterAlgebras.PlabicData.RootedTree.IsCollapsible`: collapsible trees.
* `ClusterAlgebras.PlabicGraph.IsReduced`: reduced plabic graphs.
* `ClusterAlgebras.PlabicData.tripDecoration`, `ClusterAlgebras.PlabicData.decoratedTripPerm`: the
  decorated trip permutation.
* `ClusterAlgebras.PlabicGraph.NearlyLeaflessEquivalent`: nearly leafless equivalence.
* `ClusterAlgebras.PlabicGraph.IsReductionStep`, `ClusterAlgebras.PlabicGraph.IsIrreducible`:
  reduction steps of plabic graphs.

## Main results

* `ClusterAlgebras.PlabicGraph.IsReduced.of_moveEquivalent`: reducedness is invariant under move
  equivalence.
* `ClusterAlgebras.PlabicGraph.IsReductionStep.diamond`: reduction steps of plabic trees commute
  up to isomorphism.
* `ClusterAlgebras.PlabicGraph.isomorphic_of_moveEquivalent_of_isIrreducible`: `0`-irreducible
  plabic trees that are `{M2, M3}`-equivalent are isomorphic.
* `ClusterAlgebras.PlabicData.RootedTree.moveEquivalent_lollipopPlabicGraph_iff`: for an internal
  root, `P_T` is `{M2, M3}`-equivalent to `L_{κ(v)}` iff a `1`-irreducible reduction of `P_T` has
  `ḡ` as a vertex by itself.

## Implementation notes

* Move equivalence is a relation on the type `PlabicGraph b` of plabic graphs bundled with their
  darts. The graph `P_T` of a rooted tree and the lollipop graph `L_c` are bundled as elements of
  `PlabicGraph 1`; this asks the darts of `G` to form a `Type`.
* The colour `κ(v)` of an internal root is the colour of each of its darts.
* The decoration `ε_G` is a function on the fixed points of the trip permutation `π_G`. The pair
  `(π_G, ε_G)` is a decorated permutation once `π_G` is a bijection, and
  `PlabicData.decoratedTripPerm` takes that bijectivity as an argument.
* "`Q'` is the removal (contraction) of `Q`" is read up to isomorphism, as in the local moves. The
  side condition `ḡ₁ ∉ x` of a `1`-reduction step is imposed on every leg; for the plabic graphs
  with one boundary vertex, on which `ḡ₁` is defined, this is the condition on `ḡ₁`.
* Removals and contractions are compared through a single construction: the restriction of a
  graph to a set `S` of darts whose involution and rotation are the first returns to `S` of
  `ι ∘ (p q)` and `σ ∘ (p q)`, where `{p, q}` is the deleted vertex or edge. Two steps deleting
  disjoint pairs then give the same restriction in either order, since the first return to a
  subset of `S` of a first return to `S` is the first return to the subset.
* The Church–Rosser argument of `PlabicGraph.isomorphic_of_moveEquivalent_of_isIrreducible` runs
  on the quotient of `PlabicGraph b` by isomorphism, with `Relation.church_rosser` and
  `Relation.equivalence_join_reflTransGen`.
* In `PlabicData.RootedTree.moveEquivalent_lollipopPlabicGraph_iff`, `R` is known only up to
  isomorphism, so the dart `ḡ` of `R` is named as the dart across the leg of `R`; reduction steps
  never change it nor its colour.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-- The lollipop graph `L_c` bundled as an element of `PlabicGraph 1`. -/
def lollipopPlabicGraph (c : Shade) : PlabicGraph 1 :=
  ⟨LollipopDart, lollipopGraph c, isPlabicGraph_lollipopGraph c⟩

namespace PlabicData

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

namespace RootedTree

/-- A rooted tree `T = (v, W)` of `G` is a **collapsible tree of colour `c`** if `P_T` is a plabic
graph, `P_T` is `{M2, M3}`-equivalent to the lollipop graph `L_c`, and either `v` is an internal
vertex of colour `c` (`T` collapses onto `v`), or `v` is a boundary vertex and `|W| ≥ 2` (`T`
collapses to a lollipop of colour `c` at `v`). -/
@[cluster_algebras "def_collapsible_tree"]
structure IsCollapsibleOfColour (T : G.RootedTree) (c : Shade) : Prop where
  /-- `P_T` is a plabic graph. -/
  isPlabicGraph : T.plabicData.IsPlabicGraph
  /-- `P_T` is `{M2, M3}`-equivalent to `L_c`. -/
  moveEquivalent : PlabicGraph.MoveEquivalent {.m2, .m3}
    ⟨T.Dart, T.plabicData, isPlabicGraph⟩ (lollipopPlabicGraph c)
  /-- The root is internal of colour `c`, or a boundary vertex with `|W| ≥ 2`. -/
  root_cases : (¬G.IsBoundaryVertex T.root ∧ ∀ d ∈ T.root, G.colour d = c) ∨
    (G.IsBoundaryVertex T.root ∧ 2 ≤ T.nonRoot.card)

/-- A rooted tree is a **collapsible tree** if it is a collapsible tree of some colour. -/
@[cluster_algebras "def_collapsible_tree"]
def IsCollapsible (T : G.RootedTree) : Prop :=
  ∃ c, T.IsCollapsibleOfColour c

/-- A collapsible tree of colour `c` is a collapsible tree. -/
theorem IsCollapsibleOfColour.isCollapsible {T : G.RootedTree} {c : Shade}
    (h : T.IsCollapsibleOfColour c) : T.IsCollapsible :=
  ⟨c, h⟩

end RootedTree

/-! ### The decorated trip permutation -/

variable (G) in
/-- The fixed point `i` of `π_G` is **white for the decoration** of `G`: `G` has a white lollipop
at `i` or a collapsible tree of colour white with root `β(i)`. -/
def IsWhiteDecorated (i : Fin b) : Prop :=
  (∃ v, G.IsLollipopOfColour i .white v) ∨
    ∃ T : G.RootedTree, T.root = G.bvertex i ∧ T.IsCollapsibleOfColour .white

open scoped Classical in
variable (G) in
/-- The **decoration** `ε_G` of the fixed points of the trip permutation: `ε_G(i)` is white if `G`
has a white lollipop at `i` or a collapsible tree of colour white with root `β(i)`, and black
otherwise. Labels are `0`-indexed: `i : Fin b` is the boundary vertex numbered `i + 1`. -/
@[cluster_algebras "def_decorated_trip_permutation"]
noncomputable def tripDecoration (i : {i : Fin b // G.tripPerm i = i}) : Shade :=
  if G.IsWhiteDecorated i then .white else .black

/-- `ε_G(i)` is white if and only if `i` is white for the decoration of `G`. -/
theorem tripDecoration_eq_white_iff (i : {i : Fin b // G.tripPerm i = i}) :
    G.tripDecoration i = .white ↔ G.IsWhiteDecorated i := by
  classical
  unfold tripDecoration
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- `ε_G(i)` is black if and only if `i` is not white for the decoration of `G`. -/
theorem tripDecoration_eq_black_iff (i : {i : Fin b // G.tripPerm i = i}) :
    G.tripDecoration i = .black ↔ ¬G.IsWhiteDecorated i := by
  classical
  unfold tripDecoration
  split_ifs with h
  · exact iff_of_false (by decide) (not_not.2 h)
  · exact iff_of_true rfl h

variable (G) in
/-- The **decorated trip permutation** `π̃_G = (π_G, ε_G)`, given that the trip permutation `π_G`
is a bijection. -/
@[cluster_algebras "def_decorated_trip_permutation"]
noncomputable def decoratedTripPerm (h : Function.Bijective G.tripPerm) : DecoratedPerm b where
  perm := Equiv.ofBijective _ h
  colour := G.tripDecoration

/-- The permutation of `π̃_G` is the trip permutation `π_G`. -/
@[simp]
theorem decoratedTripPerm_perm_apply (h : Function.Bijective G.tripPerm) (i : Fin b) :
    (G.decoratedTripPerm h).perm i = G.tripPerm i := rfl

/-- The colouring of the fixed points of `π̃_G` is the decoration `ε_G`. -/
@[simp]
theorem decoratedTripPerm_colour (h : Function.Bijective G.tripPerm)
    (i : {i : Fin b // (G.decoratedTripPerm h).perm i = i}) :
    (G.decoratedTripPerm h).colour i = G.tripDecoration ⟨i, i.2⟩ := rfl

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-! ### Reduced plabic graphs -/

/-- A plabic graph `G` is **reduced** if no plabic graph `G' ∼ G` contains a hollow digon or an
internal leaf that is not a lollipop and is not a vertex, other than the root, of a collapsible
tree of `G'`. -/
@[cluster_algebras "def_reduced_plabic_graph"]
def IsReduced (G : PlabicGraph b) : Prop :=
  ∀ G' : PlabicGraph b, MoveEquivalent Set.univ G' G →
    (∀ f, ¬G'.data.IsHollowDigon f) ∧
      ∀ v, G'.data.IsInternalLeaf v →
        (∃ i, G'.data.IsLollipop i v) ∨ ∃ T : G'.data.RootedTree, T.IsCollapsible ∧ v ∈ T.nonRoot

/-- **Reducedness is invariant under move equivalence**: if `G` is reduced and `G ∼ G'`, then `G'`
is reduced. -/
@[cluster_algebras "lem_reduced_move_invariant"]
theorem IsReduced.of_moveEquivalent {G G' : PlabicGraph b} (hG : G.IsReduced)
    (h : MoveEquivalent Set.univ G G') : G'.IsReduced :=
  fun G'' h'' => hG G'' (h''.trans h.symm)

/-! ### Nearly leafless equivalence -/

/-- A **step of a nearly leafless equivalence**: `G'` is nearly leafless, and is isomorphic to `G`
or obtained from `G` by a local move. -/
def NearlyLeaflessStep (G G' : PlabicGraph b) : Prop :=
  G'.data.IsNearlyLeafless ∧ MoveStep Set.univ G G'

/-- Two plabic graphs `G` and `G'` are **nearly leafless equivalent** if there is a finite sequence
`G = G₀, G₁, …, G_r = G'` of nearly leafless plabic graphs such that each `G_t` is isomorphic to
`G_{t-1}` or obtained from `G_{t-1}` by a local move. -/
@[cluster_algebras "def_nearly_leafless_equivalent"]
def NearlyLeaflessEquivalent (G G' : PlabicGraph b) : Prop :=
  G.data.IsNearlyLeafless ∧ Relation.ReflTransGen NearlyLeaflessStep G G'

namespace NearlyLeaflessEquivalent

variable {G G' G'' : PlabicGraph b}

/-- A nearly leafless plabic graph is nearly leafless equivalent to itself. -/
theorem refl (hG : G.data.IsNearlyLeafless) : NearlyLeaflessEquivalent G G :=
  ⟨hG, .refl⟩

/-- Nearly leafless equivalence is transitive. -/
theorem trans (h : NearlyLeaflessEquivalent G G') (h' : NearlyLeaflessEquivalent G' G'') :
    NearlyLeaflessEquivalent G G'' :=
  ⟨h.1, h.2.trans h'.2⟩

/-- The right end of a nearly leafless equivalence is nearly leafless. -/
theorem isNearlyLeafless_right (h : NearlyLeaflessEquivalent G G') : G'.data.IsNearlyLeafless := by
  obtain ⟨h0, h⟩ := h
  induction h with
  | refl => exact h0
  | tail _ hst _ => exact hst.1

/-- Nearly leafless equivalence is symmetric. -/
theorem symm (h : NearlyLeaflessEquivalent G G') : NearlyLeaflessEquivalent G' G := by
  refine ⟨h.isNearlyLeafless_right, ?_⟩
  obtain ⟨h0, h⟩ := h
  induction h with
  | refl => exact .refl
  | @tail B C hBC hst ih =>
    have hB : B.data.IsNearlyLeafless := isNearlyLeafless_right ⟨h0, hBC⟩
    exact Relation.ReflTransGen.head ⟨hB, hst.2.symm⟩ ih

/-- A nearly leafless equivalence is a move equivalence. -/
theorem moveEquivalent (h : NearlyLeaflessEquivalent G G') : MoveEquivalent Set.univ G G' :=
  Relation.ReflTransGen.mono (fun _ _ hs => hs.2) h.2

end NearlyLeaflessEquivalent

/-! ### Reduction steps of plabic trees -/

/-- `Q'` is obtained from `Q` by an **`ε`-reduction step**, for `ε ∈ {0, 1}`: either `Q'` is
(isomorphic to) the removal of an internal vertex `x` of `Q` consisting of exactly two darts
`d₁, d₂ = σ d₁` with `d̄₁ ≠ d₂`, where for `ε = 1` moreover `ḡ ∉ x` for the legs `g`; or `Q'` is
(isomorphic to) the contraction of `Q` along an edge whose endpoints are distinct internal vertices
of the same colour. -/
@[cluster_algebras "def_tree_reduction_step"]
def IsReductionStep (ε : Fin 2) (Q Q' : PlabicGraph b) : Prop :=
  (∃ (d : Q.Dart) (hd : Q.data.IsBivalentRemovable d),
      (ε = 1 → ∀ i, Q.data.inv (Q.data.leg i) ∉ Q.data.vertexOf d) ∧
        Q'.data.Isomorphic (Q.data.bivalentRemoval Q.isPlabicGraph hd)) ∨
    ∃ d, Q.IsEdgeContraction Q' d

/-- `Q` is **`ε`-irreducible** if no plabic graph is obtained from `Q` by an `ε`-reduction step. -/
@[cluster_algebras "def_tree_reduction_step"]
def IsIrreducible (ε : Fin 2) (Q : PlabicGraph b) : Prop :=
  ∀ Q', ¬IsReductionStep ε Q Q'

/-- A reduction step is a local move of type (M2) or (M3). -/
theorem IsReductionStep.moveStep {ε : Fin 2} {Q Q' : PlabicGraph b}
    (h : IsReductionStep ε Q Q') : MoveStep {.m2, .m3} Q Q' := by
  rcases h with ⟨d, hd, -, hiso⟩ | ⟨d, h⟩
  · exact Or.inr ⟨.m2, by simp, Or.inl ⟨d, hd, hiso⟩⟩
  · exact Or.inr ⟨.m3, by simp, Or.inl ⟨d, h⟩⟩

end PlabicGraph

/-! ### Restrictions by first returns -/

section FirstReturn

open Equiv Equiv.Perm

variable {X Y : Type*}

private theorem pow_apply_of_semiconj {π : Perm X} {π' : Perm Y} (θ : X ≃ Y)
    (h : ∀ x, θ (π x) = π' (θ x)) (n : ℕ) (x : X) : θ ((π ^ n) x) = (π' ^ n) (θ x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, h, ih]

private theorem sameCycle_apply_iff_of_semiconj [Finite X] {π : Perm X} {π' : Perm Y} (θ : X ≃ Y)
    (h : ∀ x, θ (π x) = π' (θ x)) {x y : X} : π'.SameCycle (θ x) (θ y) ↔ π.SameCycle x y := by
  have h' : ∀ y, θ.symm (π' y) = π (θ.symm y) := fun y => by
    apply θ.injective
    rw [h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · have : Finite Y := Finite.of_equiv X θ
    obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    exact ⟨n, by simpa [hn] using (pow_apply_of_semiconj θ.symm h' n (θ x)).symm⟩
  · obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
    exact ⟨n, by rw [zpow_natCast, ← pow_apply_of_semiconj θ h, hn]⟩

/-- A bijection intertwining two permutations carries first returns to first returns. -/
private theorem coe_firstReturn_of_semiconj [Finite X] [Finite Y] {π : Perm X} {π' : Perm Y}
    (θ : X ≃ Y)
    (h : ∀ x, θ (π x) = π' (θ x)) {S : Set X} {S' : Set Y} (hS : ∀ x, θ x ∈ S' ↔ x ∈ S)
    (y : S) :
    θ (firstReturn π S y) = firstReturn π' S' ⟨θ y, (hS y).2 y.2⟩ := by
  rw [coe_firstReturn π S y, pow_apply_of_semiconj θ h]
  symm
  refine coe_firstReturn_of_pow (y := ⟨θ y, (hS y).2 y.2⟩) (firstReturnTime_pos y) ?_ ?_
  · change (π' ^ _) (θ y) ∈ S'
    rw [← pow_apply_of_semiconj θ h, hS]
    exact pow_firstReturnTime_apply_mem y
  · intro j hj hjm
    change (π' ^ j) (θ y) ∉ S'
    rw [← pow_apply_of_semiconj θ h, hS]
    exact pow_apply_notMem_of_lt_firstReturnTime hj hjm

/-- Composing with a transposition of two points of `S` commutes with the first return to `S`. -/
private theorem firstReturnPerm_mul_swap [Finite X] [DecidableEq X] (π : Perm X) {S : Set X}
    (p q : S) :
    firstReturnPerm (π * swap (p : X) q) S = firstReturnPerm π S * swap p q := by
  ext y
  simp only [Perm.mul_apply, coe_firstReturnPerm]
  refine coe_firstReturn_eq_of_eqOn_compl ?_ fun z hz => ?_
  · rw [Perm.mul_apply, Subtype.coe_injective.map_swap]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne (by rintro rfl; exact hz p.2)
      (by rintro rfl; exact hz q.2)]

/-- The first return to `S' ⊆ S` of the first return to `S` is the first return to `S'`. -/
private theorem coe_coe_firstReturn_firstReturnPerm [Finite X] (π : Perm X) {S : Set X} {S' : Set S}
    {T : Set X} (hT : ∀ x, x ∈ T ↔ ∃ h : x ∈ S, (⟨x, h⟩ : S) ∈ S') (y : S') :
    ((firstReturn (firstReturnPerm π S) S' y : S) : X) =
      firstReturn π T ⟨((y : S) : X), (hT _).2 ⟨(y : S).2, y.2⟩⟩ := by
  set F := firstReturnPerm π S with hFdef
  have hTS : ∀ x : S, (x : X) ∈ T ↔ x ∈ S' := fun x => by
    rw [hT]
    exact ⟨fun ⟨_, h'⟩ => h', fun h => ⟨x.2, h⟩⟩
  have hF : ∀ z : S, ((F z : S) : X) = (π ^ firstReturnTime π S z) z := fun z => by
    rw [hFdef, coe_firstReturnPerm, coe_firstReturn]
  have claim : ∀ k : ℕ, ∀ z : S, 0 < k → (F ^ k) z ∈ S' →
      (∀ j, 0 < j → j < k → (F ^ j) z ∉ S') →
      ∃ n, 0 < n ∧ (π ^ n) (z : X) = (((F ^ k) z : S) : X) ∧
        ∀ j, 0 < j → j < n → (π ^ j) (z : X) ∉ T := by
    intro k
    induction k with
    | zero => intro z h; omega
    | succ k ih =>
      intro z _ hk hmin
      have hm : 0 < firstReturnTime π S z := firstReturnTime_pos z
      have hmS : ∀ j, 0 < j → j < firstReturnTime π S z → (π ^ j) (z : X) ∉ T :=
        fun j hj hjm hT' => pow_apply_notMem_of_lt_firstReturnTime hj hjm ((hT _).1 hT').1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨_, hm, by rw [zero_add, pow_one, hF], hmS⟩
      · have hk' : (F ^ k) (F z) ∈ S' := by rwa [← Perm.mul_apply, ← pow_succ]
        obtain ⟨n', hn', heq, hmin'⟩ := ih (F z) hk0 hk' fun j hj hjk => by
          rw [← Perm.mul_apply, ← pow_succ]
          exact hmin (j + 1) (by omega) (by omega)
        refine ⟨firstReturnTime π S z + n', by omega, ?_, ?_⟩
        · rw [pow_succ, Perm.mul_apply, ← heq, hF, add_comm, pow_add, Perm.mul_apply]
        · intro j hj hjn
          rcases lt_trichotomy j (firstReturnTime π S z) with hjm | rfl | hjm
          · exact hmS j hj hjm
          · rw [← hF, hTS]
            have := hmin 1 one_pos (by omega)
            rwa [pow_one] at this
          · have : (π ^ j) (z : X) = (π ^ (j - firstReturnTime π S z)) (F z : X) := by
              rw [hF, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hjm.le]
            rw [this]
            exact hmin' _ (by omega) (by omega)
  obtain ⟨n, hn, heq, hmin⟩ := claim (firstReturnTime F S' y) y (firstReturnTime_pos y)
    (pow_firstReturnTime_apply_mem y) fun j hj hjk => pow_apply_notMem_of_lt_firstReturnTime hj hjk
  rw [coe_firstReturn, ← heq]
  refine (coe_firstReturn_of_pow (π := π) (Y := T) (y := ⟨((y : S) : X), (hT _).2 ⟨(y : S).2, y.2⟩⟩)
    hn ?_ hmin).symm
  change (π ^ n) ((y : S) : X) ∈ T
  rw [heq, hTS]
  exact pow_firstReturnTime_apply_mem y

end FirstReturn

namespace PlabicData

open Equiv Equiv.Perm

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b : ℕ}

/-- A bijection of darts intertwining the rotations maps each vertex onto a vertex. -/
private theorem map_vertexOf_of_semiconj {G : PlabicData H b} {G' : PlabicData H' b} (e : H ≃ H')
    (map_rot : ∀ d, e (G.rot d) = G'.rot (e d)) (d : H) :
    (G.vertexOf d).map e.toEmbedding = G'.vertexOf (e d) := by
  ext y
  rw [mem_map_equiv, RotationSystem.mem_vertexOf, RotationSystem.mem_vertexOf,
    ← sameCycle_apply_iff_of_semiconj e map_rot, Equiv.apply_symm_apply]

/-- An isomorphism of tuples, built from a bijection of darts commuting with the involutions and
the rotations, preserving `B`, the colours of internal vertices and the legs. -/
private def Iso.ofMapLeg {G : PlabicData H b} {G' : PlabicData H' b} (e : H ≃ H')
    (map_inv : ∀ d, e (G.inv d) = G'.inv (e d)) (map_rot : ∀ d, e (G.rot d) = G'.rot (e d))
    (mem_bdry_iff : ∀ d, e d ∈ G'.bdry ↔ d ∈ G.bdry)
    (map_colour : ∀ d, ¬G.IsBoundaryVertex (G.vertexOf d) → G'.colour (e d) = G.colour d)
    (map_leg : ∀ i, e (G.leg i) = G'.leg i) : G.Iso G' where
  toEquiv := e
  map_inv := map_inv
  map_rot := map_rot
  mem_bdry_iff := mem_bdry_iff
  map_colour := map_colour
  map_bvertex i := by
    simp only [bvertex]
    rw [← map_leg, ← map_vertexOf_of_semiconj e map_rot, filter_map]
    congr 1
    refine filter_congr fun x _ => ?_
    simp [mem_bdry_iff]

/-- The tuple on a set `S` of darts of `G` with involution and rotation the first returns of `α`
and `β` to `S`, and the boundary, colours and legs of `G`. Removals of bivalent vertices and
contractions of edges are of this form. -/
private noncomputable def firstReturnRestrict (G : PlabicData H b) (S : Set H)
    [DecidablePred (· ∈ S)]
    (α β : Perm H) (hleg : ∀ i, G.leg i ∈ S) : PlabicData S b where
  inv := firstReturnPerm α S
  rot := firstReturnPerm β S
  bdry := G.bdry.subtype (· ∈ S)
  colour x := G.colour x
  leg i := ⟨G.leg i, hleg i⟩

section FirstReturnRestrict

variable {G : PlabicData H b}

omit [DecidableEq H] in
@[simp]
private theorem mem_firstReturnRestrict_bdry {S : Set H} [DecidablePred (· ∈ S)] {α β : Perm H}
    {hleg : ∀ i, G.leg i ∈ S} {x : S} :
    x ∈ (G.firstReturnRestrict S α β hleg).bdry ↔ (x : H) ∈ G.bdry :=
  mem_subtype

/-- Restrictions to equal sets by equal permutations are isomorphic. -/
private noncomputable def firstReturnRestrictCongr {S S' : Set H} [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ S')] {α β α' β' : Perm H} (hS : S = S') (hα : α = α') (hβ : β = β')
    (hleg : ∀ i, G.leg i ∈ S) (hleg' : ∀ i, G.leg i ∈ S') :
    (G.firstReturnRestrict S α β hleg).Iso (G.firstReturnRestrict S' α' β' hleg') := by
  refine Iso.ofMapLeg (Equiv.subtypeEquivRight fun x => by rw [hS]) (fun x => ?_) (fun x => ?_)
    (fun x => ?_) (fun _ _ => rfl) fun _ => rfl
  · apply Subtype.ext
    change (firstReturn α S x : H) = (firstReturn α' S' _ : H)
    subst hS hα
    rfl
  · apply Subtype.ext
    change (firstReturn β S x : H) = (firstReturn β' S' _ : H)
    subst hS hβ
    rfl
  · simp

/-- A restriction of a restriction of `G`, by first returns of the composites with a
transposition, is a restriction of `G`. -/
private noncomputable def firstReturnRestrictNestedIso {S : Set H} [DecidablePred (· ∈ S)]
    {α β : Perm H}
    {hleg : ∀ i, G.leg i ∈ S} {R : PlabicData S b} (hR : R = G.firstReturnRestrict S α β hleg)
    {S' : Set S} [DecidablePred (· ∈ S')] (p q : S) (hleg' : ∀ i, R.leg i ∈ S') {T : Set H}
    [DecidablePred (· ∈ T)] (hT : ∀ x, x ∈ T ↔ ∃ h : x ∈ S, (⟨x, h⟩ : S) ∈ S')
    (hlegT : ∀ i, G.leg i ∈ T) :
    (R.firstReturnRestrict S' (R.inv * swap p q) (R.rot * swap p q) hleg').Iso
      (G.firstReturnRestrict T (α * swap (p : H) q) (β * swap (p : H) q) hlegT) := by
  subst hR
  refine Iso.ofMapLeg ((Equiv.subtypeSubtypeEquivSubtypeExists (· ∈ S) (· ∈ S')).trans
    (Equiv.subtypeEquivRight fun x => (hT x).symm)) (fun x => ?_) (fun x => ?_) (fun x => ?_)
    (fun _ _ => rfl) fun _ => rfl
  · apply Subtype.ext
    change (((firstReturnPerm (firstReturnPerm α S * swap p q) S' x : S)) : H) =
      firstReturn (α * swap (p : H) q) T _
    rw [← firstReturnPerm_mul_swap, coe_firstReturnPerm, coe_coe_firstReturn_firstReturnPerm _ hT]
    rfl
  · apply Subtype.ext
    change (((firstReturnPerm (firstReturnPerm β S * swap p q) S' x : S)) : H) =
      firstReturn (β * swap (p : H) q) T _
    rw [← firstReturnPerm_mul_swap, coe_firstReturnPerm, coe_coe_firstReturn_firstReturnPerm _ hT]
    rfl
  · simp

/-- An isomorphism `θ : G → G'` carries a restriction of `G` to the corresponding restriction of
`G'`. -/
private noncomputable def firstReturnRestrictMapIso {G' : PlabicData H' b} (θ : G.Iso G')
    {S : Set H}
    {S' : Set H'} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ S')]
    (hS : ∀ x, θ.toEquiv x ∈ S' ↔ x ∈ S) {α β : Perm H} {α' β' : Perm H'}
    (hα : ∀ x, θ.toEquiv (α x) = α' (θ.toEquiv x)) (hβ : ∀ x, θ.toEquiv (β x) = β' (θ.toEquiv x))
    (hleg : ∀ i, G.leg i ∈ S) (hleg' : ∀ i, G'.leg i ∈ S')
    (hlegθ : ∀ i, θ.toEquiv (G.leg i) = G'.leg i)
    (hcol : ∀ x : S, ¬(G.firstReturnRestrict S α β hleg).IsBoundaryVertex
      ((G.firstReturnRestrict S α β hleg).vertexOf x) → G'.colour (θ.toEquiv x) = G.colour x) :
    (G.firstReturnRestrict S α β hleg).Iso (G'.firstReturnRestrict S' α' β' hleg') :=
  Iso.ofMapLeg (θ.toEquiv.subtypeEquiv fun x => (hS x).symm)
    (fun x => Subtype.ext (coe_firstReturn_of_semiconj θ.toEquiv hα hS x))
    (fun x => Subtype.ext (coe_firstReturn_of_semiconj θ.toEquiv hβ hS x))
    (fun x => by simp [θ.mem_bdry_iff]) hcol fun i => Subtype.ext (hlegθ i)

end FirstReturnRestrict

/-! ### Removals and contractions as restrictions -/

section Moves

variable {G : PlabicData H b}

omit [Fintype H] [DecidableEq H] in
private theorem eq_of_inv_of_rot {G G' : PlabicData H b} (h₁ : G.inv = G'.inv) (h₂ : G.rot = G'.rot)
    (h₃ : G.bdry = G'.bdry) (h₄ : G.colour = G'.colour) (h₅ : G.leg = G'.leg) : G = G' := by
  rcases G with ⟨⟨⟨i, r⟩, B⟩, c, l⟩
  rcases G' with ⟨⟨⟨i', r'⟩, B'⟩, c', l'⟩
  simp only at h₁ h₂ h₃ h₄ h₅
  subst h₁ h₂ h₃ h₄ h₅
  rfl

/-- The removal of a bivalent vertex `{d, σ d}` is the restriction to `H \ {d, σ d}` by the first
returns of `ι ∘ (d σd)` and `σ ∘ (d σd)`. -/
private theorem bivalentRemoval_eq_firstReturnRestrict (hG : G.IsPlabicGraph) {d : H}
    (hd : G.IsBivalentRemovable d) :
    G.bivalentRemoval hG hd = G.firstReturnRestrict ({d, G.rot d}ᶜ : Set H)
      (G.inv * swap d (G.rot d)) (G.rot * swap d (G.rot d)) (hd.leg_mem hG) := by
  have hinv := hG.inv_involutive
  refine eq_of_inv_of_rot ?_ ?_ rfl rfl rfl
  · ext y
    have hy := y.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
    change _ = (firstReturn (G.inv * swap d (G.rot d)) _ y : H)
    by_cases h₁ : (y : H) = G.inv d
    · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁]
      have e₁ : ((G.inv * swap d (G.rot d)) ^ 1) (y : H) = d := by
        rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2, h₁, hinv]
      have e₂ : ((G.inv * swap d (G.rot d)) ^ 2) (y : H) = G.inv (G.rot d) := by
        rw [pow_succ', Perm.mul_apply, e₁, Perm.mul_apply, swap_apply_left]
      rw [coe_firstReturn_of_pow (m := 2) (by norm_num) (e₂ ▸ hd.inv_rot_mem hG), e₂]
      intro j hj hj2
      obtain rfl : j = 1 := by omega
      rw [e₁]
      simp
    · by_cases h₂ : (y : H) = G.inv (G.rot d)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂]
        have e₁ : ((G.inv * swap d (G.rot d)) ^ 1) (y : H) = G.rot d := by
          rw [pow_one, Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2, h₂, hinv]
        have e₂ : ((G.inv * swap d (G.rot d)) ^ 2) (y : H) = G.inv d := by
          rw [pow_succ', Perm.mul_apply, e₁, Perm.mul_apply, swap_apply_right]
        rw [coe_firstReturn_of_pow (m := 2) (by norm_num) (e₂ ▸ hd.inv_mem hG), e₂]
        intro j hj hj2
        obtain rfl : j = 1 := by omega
        rw [e₁]
        simp
      · rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂]
        have e : (G.inv * swap d (G.rot d)) y = G.inv y := by
          rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2]
        have hmem : G.inv y ∈ ({d, G.rot d}ᶜ : Set H) := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun h => h₁ ((hinv _).symm.trans (congrArg G.inv h)),
            fun h => h₂ ((hinv _).symm.trans (congrArg G.inv h))⟩
        rw [coe_firstReturn_of_apply_mem (e ▸ hmem), e]
  · ext y
    have hy := y.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
    change (G.rot y : H) = (firstReturn (G.rot * swap d (G.rot d)) _ y : H)
    have e : (G.rot * swap d (G.rot d)) y = G.rot y := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2]
    rw [coe_firstReturn_of_apply_mem (e ▸ (hd.rot_mem_iff y).2 y.2), e]

/-- The contraction along `{d, d̄}` is the restriction to `H \ {d, d̄}` by the first returns of
`ι ∘ (d d̄)` and `σ ∘ (d d̄)`. -/
private theorem contractEdge_eq_firstReturnRestrict (hinv : Function.Involutive G.inv) {d : H}
    (hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    G.contractEdge d hleg = G.firstReturnRestrict (({d, G.inv d} : Set H)ᶜ : Set H)
      (G.inv * swap d (G.inv d)) (G.rot * swap d (G.inv d)) hleg := by
  refine eq_of_inv_of_rot ?_ rfl rfl rfl rfl
  ext y
  change _ = (firstReturn (G.inv * swap d (G.inv d)) _ y : H)
  have hy := mem_compl_pair_iff.1 y.2
  have e : (G.inv * swap d (G.inv d)) y = G.inv y := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hy.1 hy.2]
  rw [coe_contractEdge_inv hinv,
    coe_firstReturn_of_apply_mem (e ▸ (apply_mem_compl_pair_iff hinv d y).2 y.2), e]

variable {G' : PlabicData H' b}

/-- An isomorphism carries a removable bivalent vertex to a removable bivalent vertex. -/
private theorem IsBivalentRemovable.of_iso (θ : G.Iso G') {d : H} (hd : G.IsBivalentRemovable d) :
    G'.IsBivalentRemovable (θ.toEquiv d) where
  not_isBoundaryVertex := by
    rw [θ.isBoundaryVertex_vertexOf_iff]
    exact hd.not_isBoundaryVertex
  card_vertexOf := by
    rw [θ.card_vertexOf]
    exact hd.card_vertexOf
  inv_ne_rot := by
    rw [← θ.map_inv, ← θ.map_rot]
    exact θ.toEquiv.injective.ne hd.inv_ne_rot

/-- An isomorphism carries a contractible edge to a contractible edge. -/
private theorem IsContractibleEdge.of_iso (θ : G.Iso G') {d : H} (he : G.IsContractibleEdge d) :
    G'.IsContractibleEdge (θ.toEquiv d) where
  vertexOf_ne := by
    rw [← θ.map_inv, Ne, θ.vertexOf_eq_vertexOf_iff]
    exact he.vertexOf_ne
  mem_internalVertices := (θ.vertexOf_mem_internalVertices_iff d).2 he.mem_internalVertices
  inv_mem_internalVertices := by
    rw [← θ.map_inv, θ.vertexOf_mem_internalVertices_iff]
    exact he.inv_mem_internalVertices
  colour_inv := by
    rw [← θ.map_inv, θ.map_colour _ he.not_isBoundaryVertex_inv,
      θ.map_colour _ he.not_isBoundaryVertex]
    exact he.colour_inv

/-- An isomorphism `θ : G → G'` of plabic graphs carries the removal of a bivalent vertex of `G`
to the removal of its image. -/
private theorem Iso.bivalentRemoval_isomorphic (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (θ : G.Iso G') {d : H} (hd : G.IsBivalentRemovable d) :
    (G.bivalentRemoval hG hd).Isomorphic (G'.bivalentRemoval hG' (hd.of_iso θ)) := by
  rw [bivalentRemoval_eq_firstReturnRestrict, bivalentRemoval_eq_firstReturnRestrict]
  refine ⟨firstReturnRestrictMapIso θ (fun x => ?_) (fun x => ?_) (fun x => ?_) _ _
    (fun i => Iso.map_leg hG hG' θ i) fun x hx => ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, ← θ.map_rot,
      θ.toEquiv.injective.eq_iff]
  · rw [Perm.mul_apply, Perm.mul_apply, θ.map_inv, θ.toEquiv.injective.map_swap, θ.map_rot]
  · rw [Perm.mul_apply, Perm.mul_apply, θ.map_rot, θ.toEquiv.injective.map_swap, θ.map_rot]
  · rw [← bivalentRemoval_eq_firstReturnRestrict hG hd,
      isBoundaryVertex_bivalentRemoval_vertexOf_iff] at hx
    exact θ.map_colour _ hx

/-- An isomorphism `θ : G → G'` of plabic graphs carries the contraction of `G` along an edge to
the contraction of `G'` along its image. -/
private theorem Iso.contractEdge_isomorphic (hG : G.IsPlabicGraph) (hG' : G'.IsPlabicGraph)
    (θ : G.Iso G') {d : H} (he : G.IsContractibleEdge d) :
    (G.contractEdge d (he.leg_mem hG)).Isomorphic
      (G'.contractEdge (θ.toEquiv d) ((he.of_iso θ).leg_mem hG')) := by
  rw [contractEdge_eq_firstReturnRestrict hG.inv_involutive,
    contractEdge_eq_firstReturnRestrict hG'.inv_involutive]
  refine ⟨firstReturnRestrictMapIso θ (fun x => ?_) (fun x => ?_) (fun x => ?_) _ _
    (fun i => Iso.map_leg hG hG' θ i) fun x hx => ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, ← θ.map_inv,
      θ.toEquiv.injective.eq_iff]
  · rw [Perm.mul_apply, Perm.mul_apply, θ.map_inv, θ.toEquiv.injective.map_swap, θ.map_inv]
  · rw [Perm.mul_apply, Perm.mul_apply, θ.map_rot, θ.toEquiv.injective.map_swap, θ.map_inv]
  · rw [← contractEdge_eq_firstReturnRestrict hG.inv_involutive,
      isBoundaryVertex_vertexOf_contractEdge_iff he] at hx
    exact θ.map_colour _ hx

end Moves

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- The removal of a bivalent vertex, as a bundled plabic graph. -/
private noncomputable def removal (Q : PlabicGraph b) {d : Q.Dart}
    (hd : Q.data.IsBivalentRemovable d) :
    PlabicGraph b :=
  ⟨_, Q.data.bivalentRemoval Q.isPlabicGraph hd, isPlabicGraph_bivalentRemoval _ _⟩

/-- The contraction along an edge, as a bundled plabic graph. -/
private noncomputable def contraction (Q : PlabicGraph b) {d : Q.Dart}
    (he : Q.data.IsContractibleEdge d) : PlabicGraph b :=
  ⟨_, Q.data.contractEdge d (he.leg_mem Q.isPlabicGraph), Q.isPlabicGraph.contractEdge he⟩

private theorem isReductionStep_removal {ε : Fin 2} (Q : PlabicGraph b) {d : Q.Dart}
    (hd : Q.data.IsBivalentRemovable d)
    (hside : ε = 1 → ∀ i, Q.data.inv (Q.data.leg i) ∉ Q.data.vertexOf d) :
    IsReductionStep ε Q (Q.removal hd) :=
  Or.inl ⟨d, hd, hside, PlabicData.Isomorphic.refl _⟩

private theorem isReductionStep_contraction {ε : Fin 2} (Q : PlabicGraph b) {d : Q.Dart}
    (he : Q.data.IsContractibleEdge d) : IsReductionStep ε Q (Q.contraction he) :=
  Or.inr ⟨d, he, PlabicData.Isomorphic.refl _⟩

/-- A reduction step from `B` gives a reduction step to the same graph from any `A` isomorphic to
`B`. -/
theorem IsReductionStep.of_isomorphic {ε : Fin 2} {A B C : PlabicGraph b} (hAB : A.Isomorphic B)
    (h : IsReductionStep ε B C) : IsReductionStep ε A C := by
  obtain ⟨θ'⟩ := hAB
  set θ := θ'.symm
  rcases h with ⟨d, hd, hside, hC⟩ | ⟨d, he, hC⟩
  · refine Or.inl ⟨θ.toEquiv d, hd.of_iso θ, fun hε i hi => hside hε i ?_,
      PlabicData.Isomorphic.trans _ hC
        (θ.bivalentRemoval_isomorphic B.isPlabicGraph A.isPlabicGraph hd)⟩
    rw [← θ.map_vertexOf, ← Iso.map_leg B.isPlabicGraph A.isPlabicGraph θ, ← θ.map_inv,
      mem_map_equiv, Equiv.symm_apply_apply] at hi
    exact hi
  · exact Or.inr ⟨θ.toEquiv d, he.of_iso θ,
      PlabicData.Isomorphic.trans _ hC
        (θ.contractEdge_isomorphic B.isPlabicGraph A.isPlabicGraph he)⟩

/-- A reduction step to `B` is a reduction step to any `C` isomorphic to `B`. -/
theorem IsReductionStep.of_isomorphic_right {ε : Fin 2} {A B C : PlabicGraph b}
    (h : IsReductionStep ε A B) (hBC : B.Isomorphic C) : IsReductionStep ε A C := by
  rcases h with ⟨d, hd, hside, hB⟩ | ⟨d, he, hB⟩
  · exact Or.inl ⟨d, hd, hside,
      PlabicData.Isomorphic.trans _ (PlabicData.Isomorphic.symm _ hBC) hB⟩
  · exact Or.inr ⟨d, he,
      PlabicData.Isomorphic.trans _ (PlabicData.Isomorphic.symm _ hBC) hB⟩

end PlabicGraph

/-! ### Reduction steps of plabic trees: the concrete cases -/

namespace PlabicData

open Equiv Equiv.Perm

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

section Diamond

variable {G : PlabicData H b}

private theorem nested_isomorphic {S : Set H} [DecidablePred (· ∈ S)] {α β : Perm H}
    {hleg : ∀ i, G.leg i ∈ S} {R : PlabicData S b} (hR : R = G.firstReturnRestrict S α β hleg)
    {S' : Set S} [DecidablePred (· ∈ S')] (p q : S) (hleg' : ∀ i, R.leg i ∈ S') {T : Set H}
    [DecidablePred (· ∈ T)] (hT : ∀ x, x ∈ T ↔ ∃ h : x ∈ S, (⟨x, h⟩ : S) ∈ S')
    (hlegT : ∀ i, G.leg i ∈ T) {p' q' : H} (hp : (p : H) = p') (hq : (q : H) = q') :
    (R.firstReturnRestrict S' (R.inv * swap p q) (R.rot * swap p q) hleg').Isomorphic
      (G.firstReturnRestrict T (α * swap p' q') (β * swap p' q') hlegT) := by
  subst hp hq
  exact ⟨firstReturnRestrictNestedIso hR p q hleg' hT hlegT⟩

omit [Fintype H] [DecidableEq H] in
private theorem nodup_four {a c e f : H} (h₁ : a ≠ c) (h₂ : a ≠ e) (h₃ : a ≠ f) (h₄ : c ≠ e)
    (h₅ : c ≠ f) (h₆ : e ≠ f) : [a, c, e, f].Nodup := by
  simp [h₁, h₂, h₃, h₄, h₅, h₆]

/-- Deleting two disjoint pairs of darts in either order gives isomorphic restrictions. -/
private theorem firstReturnRestrict_swap_isomorphic {a₁ c₁ a₂ c₂ : H}
    (hnd : [a₁, c₁, a₂, c₂].Nodup) (hleg : ∀ i, G.leg i ∈ ({a₁, c₁, a₂, c₂} : Set H)ᶜ)
    (hleg' : ∀ i, G.leg i ∈ ({a₂, c₂, a₁, c₁} : Set H)ᶜ) :
    (G.firstReturnRestrict ({a₁, c₁, a₂, c₂} : Set H)ᶜ (G.inv * swap a₁ c₁ * swap a₂ c₂)
      (G.rot * swap a₁ c₁ * swap a₂ c₂) hleg).Isomorphic
    (G.firstReturnRestrict ({a₂, c₂, a₁, c₁} : Set H)ᶜ (G.inv * swap a₂ c₂ * swap a₁ c₁)
      (G.rot * swap a₂ c₂ * swap a₁ c₁) hleg') := by
  have hc := (disjoint_swap_swap hnd).commute.eq
  refine ⟨firstReturnRestrictCongr ?_ ?_ ?_ _ _⟩
  · ext x
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · rw [mul_assoc, hc, ← mul_assoc]
  · rw [mul_assoc, hc, ← mul_assoc]

variable (hG : G.IsPlabicGraph)

include hG

private theorem leg_ne_of_not_isBoundaryVertex {x : H} (hx : ¬G.IsBoundaryVertex (G.vertexOf x))
    (i : Fin b) : G.leg i ≠ x := by
  rintro rfl
  exact hx (G.vertexOf_mem_boundaryVertices.1 (hG.bvertex_mem i))

private theorem IsBivalentRemovable.rot' {d : H} (hd : G.IsBivalentRemovable d) :
    G.IsBivalentRemovable (G.rot d) where
  not_isBoundaryVertex := by
    rw [G.vertexOf_rot]
    exact hd.not_isBoundaryVertex
  card_vertexOf := by
    rw [G.vertexOf_rot]
    exact hd.card_vertexOf
  inv_ne_rot := by
    rw [hd.rot_rot]
    exact hd.inv_rot_ne hG

private theorem IsContractibleEdge.inv' {d : H} (he : G.IsContractibleEdge d) :
    G.IsContractibleEdge (G.inv d) where
  vertexOf_ne := by
    rw [hG.inv_involutive d]
    exact he.vertexOf_ne.symm
  mem_internalVertices := he.inv_mem_internalVertices
  inv_mem_internalVertices := by
    rw [hG.inv_involutive d]
    exact he.mem_internalVertices
  colour_inv := by
    rw [hG.inv_involutive d]
    exact he.colour_inv.symm

private theorem bivalentRemoval_isomorphic_rot {d : H} (hd : G.IsBivalentRemovable d) :
    (G.bivalentRemoval hG hd).Isomorphic (G.bivalentRemoval hG (hd.rot' hG)) := by
  rw [bivalentRemoval_eq_firstReturnRestrict, bivalentRemoval_eq_firstReturnRestrict]
  refine ⟨firstReturnRestrictCongr ?_ ?_ ?_ _ _⟩
  · rw [hd.rot_rot, Set.pair_comm]
  · rw [hd.rot_rot, swap_comm]
  · rw [hd.rot_rot, swap_comm]

omit hG in
private theorem contractEdge_isomorphic_of_eq {d d' : H} (h : d = d')
    (hleg : ∀ i, G.leg i ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
    (hleg' : ∀ i, G.leg i ∈ (({d', G.inv d'} : Set H)ᶜ : Set H)) :
    (G.contractEdge d hleg).Isomorphic (G.contractEdge d' hleg') := by
  subst h
  exact Isomorphic.refl _

private theorem contractEdge_isomorphic_inv {d : H} (he : G.IsContractibleEdge d) :
    (G.contractEdge d (he.leg_mem hG)).Isomorphic
      (G.contractEdge (G.inv d) ((he.inv' hG).leg_mem hG)) := by
  rw [contractEdge_eq_firstReturnRestrict hG.inv_involutive,
    contractEdge_eq_firstReturnRestrict hG.inv_involutive]
  refine ⟨firstReturnRestrictCongr ?_ ?_ ?_ _ _⟩
  · rw [hG.inv_involutive d, Set.pair_comm]
  · rw [hG.inv_involutive d, swap_comm]
  · rw [hG.inv_involutive d, swap_comm]

/-- Removing a bivalent vertex `{d, σ d}` and contracting the edge `{d, d̄}` give isomorphic
graphs. -/
private theorem bivalentRemoval_isomorphic_contractEdge {d : H} (hd : G.IsBivalentRemovable d)
    (he : G.IsContractibleEdge d) :
    (G.bivalentRemoval hG hd).Isomorphic (G.contractEdge d (he.leg_mem hG)) := by
  have hinv := hG.inv_involutive
  have n₁ : G.rot d ≠ d := hd.rot_ne
  have n₂ : G.inv d ≠ G.rot d := hd.inv_ne_rot
  have n₃ : G.inv d ≠ d := hG.inv_ne d
  have n₄ : G.inv (G.rot d) ≠ G.rot d := hG.inv_ne _
  have n₅ : G.inv (G.rot d) ≠ G.inv d := fun h => n₁ (G.inv.injective h)
  set τ := swap (G.rot d) (G.inv d) with hτ
  have τd : τ d = d := swap_apply_of_ne_of_ne n₁.symm n₃.symm
  have hS : ∀ x, x ∈ ({d, G.rot d}ᶜ : Set H) ↔ τ x ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
    intro x
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hτ, swap_apply_eq_iff, swap_apply_eq_iff, swap_apply_of_ne_of_ne n₁.symm n₃.symm,
      swap_apply_right]
  have hfix : ∀ x : H, x ≠ G.rot d → x ≠ G.inv d → τ x = x := fun x h₁ h₂ =>
    swap_apply_of_ne_of_ne h₁ h₂
  refine ⟨Iso.ofMapLeg (τ.subtypeEquiv hS) (fun x => Subtype.ext ?_) (fun x => Subtype.ext ?_)
    (fun x => ?_) (fun x _ => ?_) (fun i => Subtype.ext ?_)⟩
  · have hx := x.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    simp only [Equiv.subtypeEquiv_apply]
    rw [coe_contractEdge_inv hinv]
    change τ _ = G.inv (τ x)
    by_cases h₁ : (x : H) = G.inv d
    · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁, h₁, hτ, swap_apply_right,
        swap_apply_of_ne_of_ne n₄ n₅]
    · by_cases h₂ : (x : H) = G.inv (G.rot d)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂, h₂, hτ, swap_apply_right,
          swap_apply_of_ne_of_ne n₄ n₅, hinv]
      · rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂, hfix _ hx.2 h₁]
        exact hfix _ (fun h => h₂ ((hinv _).symm.trans (congrArg G.inv h)))
          fun h => hx.1 (G.inv.injective h)
  · have hx := x.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    simp only [Equiv.subtypeEquiv_apply, coe_bivalentRemoval_rot]
    have hσ : ∀ y : H, G.rot y = d → y = G.rot d := fun y h => by
      apply G.rot.injective
      rw [h, hd.rot_rot]
    by_cases h₁ : (x : H) = G.inv d
    · have hy : τ (x : H) = G.rot d := by rw [h₁, hτ, swap_apply_right]
      have hxd : G.rot (τ x) = d := by rw [hy, hd.rot_rot]
      by_cases ha : G.rot (G.inv d) = G.inv d
      · rw [coe_contractEdge_rot_of_eq_of_eq (x := ⟨τ x, (hS x).1 x.2⟩) hxd ha, h₁, ha, hτ,
          swap_apply_right]
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨n₁, n₂.symm⟩
      · have hm : G.rot (G.inv d) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun h => n₂ (hσ _ h), ha⟩
        rw [coe_contractEdge_rot_of_eq (x := ⟨τ x, (hS x).1 x.2⟩) hxd hm, h₁]
        exact hfix _ (fun h => n₃ (G.rot.injective h)) ha
    · have hτx : τ (x : H) = x := hfix _ hx.2 h₁
      by_cases h₂ : G.rot (x : H) = G.inv d
      · have hm : G.rot d ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨n₁, n₂.symm⟩
        rw [coe_contractEdge_rot_of_eq_inv (x := ⟨τ x, (hS x).1 x.2⟩)
          (show G.rot (τ x) = G.inv d by rw [hτx, h₂]) hm, h₂,
          hτ, swap_apply_right]
      · have hm : G.rot (τ x) ∈ (({d, G.inv d} : Set H)ᶜ : Set H) := by
          rw [hτx]
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨fun h => hx.2 (hσ _ h), h₂⟩
        rw [coe_contractEdge_rot_of_mem (x := ⟨τ x, (hS x).1 x.2⟩) hm]
        change τ (G.rot x) = G.rot (τ x)
        rw [hτx]
        exact hfix _ (fun h => hx.1 (G.rot.injective h)) h₂
  · have hx := x.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    simp only [Equiv.subtypeEquiv_apply, mem_contractEdge_bdry, mem_bivalentRemoval_bdry]
    by_cases h₁ : (x : H) = G.inv d
    · rw [h₁, hτ, swap_apply_right]
      exact iff_of_false hd.rot_notMem_bdry (hd.inv_notMem_bdry hG)
    · rw [hfix _ hx.2 h₁]
  · simp only [Equiv.subtypeEquiv_apply, contractEdge_colour, bivalentRemoval_colour]
    have hx := x.2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    by_cases h₁ : (x : H) = G.inv d
    · rw [h₁, hτ, swap_apply_right, hG.colour_rot _ hd.not_isBoundaryVertex, he.colour_inv]
    · rw [hfix _ hx.2 h₁]
  · simp only [Equiv.subtypeEquiv_apply, coe_contractEdge_leg, coe_bivalentRemoval_leg]
    refine hfix _ (leg_ne_of_not_isBoundaryVertex hG ?_ i)
      (leg_ne_of_not_isBoundaryVertex hG he.not_isBoundaryVertex_inv i)
    rw [G.vertexOf_rot]
    exact hd.not_isBoundaryVertex

private theorem parallel (hbv : G.boundaryVertices.card = 1) (hf : G.faces.card = 1) {d d' : H}
    (hd : d ∉ G.bdry) (hd' : d' ∉ G.bdry) (h₁ : G.vertexOf d = G.vertexOf d')
    (h₂ : G.vertexOf (G.inv d) = G.vertexOf (G.inv d')) : d' = d ∨ d' = G.inv d := by
  by_contra h
  refine hG.endpoints_ne_of_card_faces_eq_one hbv hf hd hd' (fun h' => h ?_) (by rw [h₁, h₂])
  exact (G.edgeOf_eq_edgeOf_iff hG.inv_involutive).1 h'.symm

omit hG in
private theorem mem_compl_rot_of_vertexOf_ne {d e : H} (h : G.vertexOf d ≠ G.vertexOf e) :
    e ∈ ({d, G.rot d}ᶜ : Set H) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨by rintro rfl; exact h rfl, by rintro rfl; exact h (G.vertexOf_rot d).symm⟩

/-- The side condition of a `1`-reduction step survives the removal of another vertex. -/
private theorem side_bivalentRemoval {d : H} (hd : G.IsBivalentRemovable d) {e : H}
    (he : e ∈ ({d, G.rot d}ᶜ : Set H)) (hsd : ∀ i, G.inv (G.leg i) ∉ G.vertexOf d)
    (hse : ∀ i, G.inv (G.leg i) ∉ G.vertexOf e) (i : Fin b) :
    (G.bivalentRemoval hG hd).inv ((G.bivalentRemoval hG hd).leg i) ∉
      (G.bivalentRemoval hG hd).vertexOf ⟨e, he⟩ := by
  have hinv := hG.inv_involutive
  have h₁ : G.leg i ≠ G.inv d := fun h => hsd i (by rw [h, hinv]; exact G.self_mem_vertexOf d)
  have h₂ : G.leg i ≠ G.inv (G.rot d) := fun h =>
    hsd i (by rw [h, hinv]; exact G.rot_mem_vertexOf d)
  rw [mem_bivalentRemoval_vertexOf,
    coe_bivalentRemoval_inv_of_ne (y := (G.bivalentRemoval hG hd).leg i) hG hd h₁ h₂]
  exact hse i

variable (hbv : G.boundaryVertices.card = 1) (hf : G.faces.card = 1)

include hbv hf

private theorem isBivalentRemovable_bivalentRemoval {d e : H} (hd : G.IsBivalentRemovable d)
    (he : G.IsBivalentRemovable e) (hde : G.vertexOf d ≠ G.vertexOf e) :
    (G.bivalentRemoval hG hd).IsBivalentRemovable ⟨e, mem_compl_rot_of_vertexOf_ne hde⟩ where
  not_isBoundaryVertex := by
    rw [isBoundaryVertex_bivalentRemoval_vertexOf_iff]
    exact he.not_isBoundaryVertex
  card_vertexOf := by
    rw [← card_map, map_bivalentRemoval_vertexOf]
    exact he.card_vertexOf
  inv_ne_rot := by
    intro h
    have h' := congrArg Subtype.val h
    rw [coe_bivalentRemoval_rot] at h'
    change _ = G.rot e at h'
    by_cases h₁ : e = G.inv d
    · rw [coe_bivalentRemoval_inv_of_eq_inv hG hd h₁] at h'
      rcases parallel hG hbv hf hd.notMem_bdry hd.rot_notMem_bdry (G.vertexOf_rot d).symm
        (by rw [h', G.vertexOf_rot, h₁]) with h'' | h''
      · exact hd.rot_ne h''
      · exact hd.inv_ne_rot h''.symm
    · by_cases h₂ : e = G.inv (G.rot d)
      · rw [coe_bivalentRemoval_inv_of_eq_inv_rot hG hd h₂] at h'
        rcases parallel hG hbv hf hd.notMem_bdry hd.rot_notMem_bdry (G.vertexOf_rot d).symm
          (by rw [h', G.vertexOf_rot, h₂]) with h'' | h''
        · exact hd.rot_ne h''
        · exact hd.inv_ne_rot h''.symm
      · rw [coe_bivalentRemoval_inv_of_ne hG hd h₁ h₂] at h'
        exact he.inv_ne_rot h'

private theorem isContractibleEdge_contractEdge {d e : H} (hd : G.IsContractibleEdge d)
    (he : G.IsContractibleEdge e) (hde : e ∈ (({d, G.inv d} : Set H)ᶜ : Set H)) :
    (G.contractEdge d (hd.leg_mem hG)).IsContractibleEdge ⟨e, hde⟩ := by
  have hinv := hG.inv_involutive
  have hde' := mem_compl_pair_iff.1 hde
  have heB : e ∉ G.bdry := fun h => he.not_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem h)
  have hdB : d ∉ G.bdry := fun h => hd.not_isBoundaryVertex (G.isBoundaryVertex_vertexOf_of_mem h)
  have hinvB : G.inv d ∉ G.bdry := fun h => hdB (hG.inv_mem_bdry_iff.1 h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have hs := (RotationSystem.vertexOf_eq_vertexOf_iff _).1 h
    rw [sameCycle_contractEdge_rot_iff hd.not_sameCycle, coe_contractEdge_inv hinv] at hs
    simp only at hs
    rcases hs with hs | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hG.vertexOf_ne_vertexOf_inv_of_card_faces_eq_one hbv hf heB
        ((G.vertexOf_eq_vertexOf_iff).2 hs)
    · rcases parallel hG hbv hf hdB heB ((G.vertexOf_eq_vertexOf_iff).2 h₁).symm
        ((G.vertexOf_eq_vertexOf_iff).2 h₂).symm with h | h
      · exact hde'.1 h
      · exact hde'.2 h
    · rcases parallel hG hbv hf hdB (fun h => heB (hG.inv_mem_bdry_iff.1 h))
        ((G.vertexOf_eq_vertexOf_iff).2 h₂).symm
        (by rw [hinv]; exact ((G.vertexOf_eq_vertexOf_iff).2 h₁).symm) with h | h
      · exact hde'.2 (by rw [← h, hinv])
      · exact hde'.1 (G.inv.injective h)
  · rw [DiskMap.vertexOf_mem_internalVertices, isBoundaryVertex_vertexOf_contractEdge_iff hd]
    exact he.not_isBoundaryVertex
  · rw [DiskMap.vertexOf_mem_internalVertices, isBoundaryVertex_vertexOf_contractEdge_iff hd,
      coe_contractEdge_inv hinv]
    exact he.not_isBoundaryVertex_inv
  · rw [contractEdge_colour, contractEdge_colour, coe_contractEdge_inv hinv]
    exact he.colour_inv

end Diamond

end PlabicData

namespace PlabicData

open Equiv Equiv.Perm

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

section Diamond

variable {G : PlabicData H b} (hG : G.IsPlabicGraph)

include hG

/-- Two removals of distinct bivalent vertices, in this order, give a restriction of `G`. -/
private theorem bivalentRemoval_bivalentRemoval_isomorphic {d e : H}
    (hd : G.IsBivalentRemovable d) (hde : e ∈ ({d, G.rot d}ᶜ : Set H))
    (he' : (G.bivalentRemoval hG hd).IsBivalentRemovable ⟨e, hde⟩)
    (hlegT : ∀ i, G.leg i ∈ ({d, G.rot d, e, G.rot e} : Set H)ᶜ) :
    ((G.bivalentRemoval hG hd).bivalentRemoval (isPlabicGraph_bivalentRemoval hG hd) he').Isomorphic
      (G.firstReturnRestrict ({d, G.rot d, e, G.rot e} : Set H)ᶜ
        (G.inv * swap d (G.rot d) * swap e (G.rot e))
        (G.rot * swap d (G.rot d) * swap e (G.rot e)) hlegT) := by
  rw [bivalentRemoval_eq_firstReturnRestrict (isPlabicGraph_bivalentRemoval hG hd) he']
  refine nested_isomorphic (bivalentRemoval_eq_firstReturnRestrict hG hd) _ _ _ (fun x => ?_)
    hlegT rfl rfl
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    Subtype.ext_iff, coe_bivalentRemoval_rot]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

/-- Two contractions along distinct edges, in this order, give a restriction of `G`. -/
private theorem contractEdge_contractEdge_isomorphic {d e : H} (hd : G.IsContractibleEdge d)
    (hde : e ∈ (({d, G.inv d} : Set H)ᶜ : Set H))
    (he' : (G.contractEdge d (hd.leg_mem hG)).IsContractibleEdge ⟨e, hde⟩)
    (hlegT : ∀ i, G.leg i ∈ ({d, G.inv d, e, G.inv e} : Set H)ᶜ) :
    ((G.contractEdge d (hd.leg_mem hG)).contractEdge ⟨e, hde⟩
      (he'.leg_mem (hG.contractEdge hd))).Isomorphic
      (G.firstReturnRestrict ({d, G.inv d, e, G.inv e} : Set H)ᶜ
        (G.inv * swap d (G.inv d) * swap e (G.inv e))
        (G.rot * swap d (G.inv d) * swap e (G.inv e)) hlegT) := by
  have hinv := hG.inv_involutive
  rw [contractEdge_eq_firstReturnRestrict (hG.contractEdge hd).inv_involutive]
  refine nested_isomorphic (contractEdge_eq_firstReturnRestrict hinv _) _ _ _ (fun x => ?_)
    hlegT rfl (coe_contractEdge_inv hinv _)
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    Subtype.ext_iff, coe_contractEdge_inv hinv]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

/-- A removal followed by a contraction along an edge not at the removed vertex gives a
restriction of `G`. -/
private theorem contractEdge_bivalentRemoval_isomorphic {d e : H}
    (hd : G.IsBivalentRemovable d) (hde : e ∈ ({d, G.rot d}ᶜ : Set H))
    (he₁ : e ≠ G.inv d) (he₂ : e ≠ G.inv (G.rot d))
    (he' : (G.bivalentRemoval hG hd).IsContractibleEdge ⟨e, hde⟩)
    (hlegT : ∀ i, G.leg i ∈ ({d, G.rot d, e, G.inv e} : Set H)ᶜ) :
    ((G.bivalentRemoval hG hd).contractEdge ⟨e, hde⟩
      (he'.leg_mem (isPlabicGraph_bivalentRemoval hG hd))).Isomorphic
      (G.firstReturnRestrict ({d, G.rot d, e, G.inv e} : Set H)ᶜ
        (G.inv * swap d (G.rot d) * swap e (G.inv e))
        (G.rot * swap d (G.rot d) * swap e (G.inv e)) hlegT) := by
  have hc : ((G.bivalentRemoval hG hd).inv ⟨e, hde⟩ : H) = G.inv e :=
    coe_bivalentRemoval_inv_of_ne hG hd he₁ he₂
  rw [contractEdge_eq_firstReturnRestrict (isPlabicGraph_bivalentRemoval hG hd).inv_involutive]
  refine nested_isomorphic (bivalentRemoval_eq_firstReturnRestrict hG hd) _ _ _ (fun x => ?_)
    hlegT rfl hc
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    Subtype.ext_iff, hc]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

/-- A contraction followed by the removal of a vertex not at the contracted edge gives a
restriction of `G`. -/
private theorem bivalentRemoval_contractEdge_isomorphic {d e : H}
    (he : G.IsContractibleEdge e) (hde : d ∈ (({e, G.inv e} : Set H)ᶜ : Set H))
    (hrd : G.rot d ∈ (({e, G.inv e} : Set H)ᶜ : Set H))
    (hd' : (G.contractEdge e (he.leg_mem hG)).IsBivalentRemovable ⟨d, hde⟩)
    (hlegT : ∀ i, G.leg i ∈ ({e, G.inv e, d, G.rot d} : Set H)ᶜ) :
    ((G.contractEdge e (he.leg_mem hG)).bivalentRemoval (hG.contractEdge he) hd').Isomorphic
      (G.firstReturnRestrict ({e, G.inv e, d, G.rot d} : Set H)ᶜ
        (G.inv * swap e (G.inv e) * swap d (G.rot d))
        (G.rot * swap e (G.inv e) * swap d (G.rot d)) hlegT) := by
  have hc : ((G.contractEdge e (he.leg_mem hG)).rot ⟨d, hde⟩ : H) = G.rot d :=
    coe_contractEdge_rot_of_mem hrd
  rw [bivalentRemoval_eq_firstReturnRestrict (hG.contractEdge he) hd']
  refine nested_isomorphic (contractEdge_eq_firstReturnRestrict hG.inv_involutive _) _ _ _
    (fun x => ?_) hlegT rfl hc
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
    Subtype.ext_iff, hc]
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

variable (hbv : G.boundaryVertices.card = 1) (hf : G.faces.card = 1)

include hbv hf

omit hbv hf in
/-- An edge not at a removed bivalent vertex stays contractible. -/
private theorem isContractibleEdge_bivalentRemoval {d e : H} (hd : G.IsBivalentRemovable d)
    (he : G.IsContractibleEdge e) (hde : e ∈ ({d, G.rot d}ᶜ : Set H))
    (he₁ : e ≠ G.inv d) (he₂ : e ≠ G.inv (G.rot d)) :
    (G.bivalentRemoval hG hd).IsContractibleEdge ⟨e, hde⟩ := by
  have hc : ((G.bivalentRemoval hG hd).inv ⟨e, hde⟩ : H) = G.inv e :=
    coe_bivalentRemoval_inv_of_ne hG hd he₁ he₂
  refine ⟨fun h => he.vertexOf_ne ?_, ?_, ?_, ?_⟩
  · have := congrArg (Finset.map (Function.Embedding.subtype _)) h
    rwa [map_bivalentRemoval_vertexOf, map_bivalentRemoval_vertexOf, hc] at this
  · rw [DiskMap.vertexOf_mem_internalVertices, isBoundaryVertex_bivalentRemoval_vertexOf_iff]
    exact he.not_isBoundaryVertex
  · rw [DiskMap.vertexOf_mem_internalVertices, isBoundaryVertex_bivalentRemoval_vertexOf_iff, hc]
    exact he.not_isBoundaryVertex_inv
  · rw [bivalentRemoval_colour, bivalentRemoval_colour, hc]
    exact he.colour_inv

omit hbv hf in
/-- A bivalent vertex away from a contracted edge stays removable. -/
private theorem isBivalentRemovable_contractEdge {d e : H} (hd : G.IsBivalentRemovable d)
    (he : G.IsContractibleEdge e) (hde : d ∈ (({e, G.inv e} : Set H)ᶜ : Set H))
    (hnot : d ∉ G.vertexOf e ∪ G.vertexOf (G.inv e))
    (hrd : G.rot d ∈ (({e, G.inv e} : Set H)ᶜ : Set H)) :
    (G.contractEdge e (he.leg_mem hG)).IsBivalentRemovable ⟨d, hde⟩ where
  not_isBoundaryVertex := by
    rw [isBoundaryVertex_vertexOf_contractEdge_iff he]
    exact hd.not_isBoundaryVertex
  card_vertexOf := by
    rw [← card_map, map_vertexOf_contractEdge_of_notMem he.not_sameCycle hnot]
    exact hd.card_vertexOf
  inv_ne_rot := by
    intro h
    have h' := congrArg Subtype.val h
    rw [coe_contractEdge_inv hG.inv_involutive, coe_contractEdge_rot_of_mem hrd] at h'
    exact hd.inv_ne_rot h'

omit hbv hf in
/-- The side condition of a `1`-reduction step survives a contraction away from the vertex. -/
private theorem side_contractEdge {d e : H} (he : G.IsContractibleEdge e)
    (hde : d ∈ (({e, G.inv e} : Set H)ᶜ : Set H))
    (hnot : d ∉ G.vertexOf e ∪ G.vertexOf (G.inv e))
    (hsd : ∀ i, G.inv (G.leg i) ∉ G.vertexOf d) (i : Fin b) :
    (G.contractEdge e (he.leg_mem hG)).inv ((G.contractEdge e (he.leg_mem hG)).leg i) ∉
      (G.contractEdge e (he.leg_mem hG)).vertexOf ⟨d, hde⟩ := by
  intro hi
  have := (mem_map' (Function.Embedding.subtype _)).2 hi
  rw [map_vertexOf_contractEdge_of_notMem he.not_sameCycle hnot] at this
  simp only [Function.Embedding.coe_subtype, coe_contractEdge_inv hG.inv_involutive,
    coe_contractEdge_leg] at this
  exact hsd i this

end Diamond

end PlabicData

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

private theorem iso_trans {H₁ H₂ H₃ : Type*} [Fintype H₁] [DecidableEq H₁] [Fintype H₂]
    [DecidableEq H₂] [Fintype H₃] [DecidableEq H₃] {A : PlabicData H₁ b} {B : PlabicData H₂ b}
    {C : PlabicData H₃ b} (h : A.Isomorphic B) (h' : B.Isomorphic C) : A.Isomorphic C :=
  Isomorphic.trans _ h h'

private theorem iso_symm {H₁ H₂ : Type*} [Fintype H₁] [DecidableEq H₁] [Fintype H₂]
    [DecidableEq H₂] {A : PlabicData H₁ b} {B : PlabicData H₂ b} (h : A.Isomorphic B) :
    B.Isomorphic A :=
  Isomorphic.symm _ h

private theorem leg_mem_compl_four {G : PlabicData H b} (hG : G.IsPlabicGraph) {p q r s : H}
    (hp : ¬G.IsBoundaryVertex (G.vertexOf p)) (hq : ¬G.IsBoundaryVertex (G.vertexOf q))
    (hr : ¬G.IsBoundaryVertex (G.vertexOf r)) (hs : ¬G.IsBoundaryVertex (G.vertexOf s))
    (i : Fin b) : G.leg i ∈ ({p, q, r, s} : Set H)ᶜ := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨leg_ne_of_not_isBoundaryVertex hG hp i, leg_ne_of_not_isBoundaryVertex hG hq i,
    leg_ne_of_not_isBoundaryVertex hG hr i, leg_ne_of_not_isBoundaryVertex hG hs i⟩

private theorem not_isBoundaryVertex_vertexOf_rot {G : PlabicData H b} {d : H}
    (hd : ¬G.IsBoundaryVertex (G.vertexOf d)) : ¬G.IsBoundaryVertex (G.vertexOf (G.rot d)) := by
  rwa [G.vertexOf_rot]

end PlabicData

namespace PlabicGraph

variable {b : ℕ}

open PlabicData

/-- `Q₃` is isomorphic to `R` or to a graph obtained from `R` by an `ε`-reduction step. -/
private def Joins (ε : Fin 2) (R Q₃ : PlabicGraph b) : Prop :=
  Q₃.Isomorphic R ∨ ∃ Q', IsReductionStep ε R Q' ∧ Q₃.Isomorphic Q'

private theorem Joins.of_isomorphic {ε : Fin 2} {R R' Q₃ : PlabicGraph b} (h : Joins ε R Q₃)
    (hR : R'.Isomorphic R) : Joins ε R' Q₃ := by
  rcases h with h | ⟨Q', hs, hi⟩
  · exact Or.inl (iso_trans h (iso_symm hR))
  · exact Or.inr ⟨Q', hs.of_isomorphic hR, hi⟩

private theorem joins_refl (ε : Fin 2) (R : PlabicGraph b) : Joins ε R R :=
  Or.inl (PlabicData.Isomorphic.refl _)

private theorem joins_of_step {ε : Fin 2} {R Q₃ : PlabicGraph b} (h : IsReductionStep ε R Q₃) :
    Joins ε R Q₃ :=
  Or.inr ⟨Q₃, h, PlabicData.Isomorphic.refl _⟩

private theorem diamond_removal_removal {ε : Fin 2} {Q : PlabicGraph b}
    (hbv : Q.data.boundaryVertices.card = 1) (hf : Q.data.faces.card = 1) {d e : Q.Dart}
    (hd : Q.data.IsBivalentRemovable d) (he : Q.data.IsBivalentRemovable e)
    (hsd : ε = 1 → ∀ i, Q.data.inv (Q.data.leg i) ∉ Q.data.vertexOf d)
    (hse : ε = 1 → ∀ i, Q.data.inv (Q.data.leg i) ∉ Q.data.vertexOf e) :
    ∃ Q₃, Joins ε (Q.removal hd) Q₃ ∧ Joins ε (Q.removal he) Q₃ := by
  have hG := Q.isPlabicGraph
  by_cases hde : Q.data.vertexOf d = Q.data.vertexOf e
  · refine ⟨Q.removal hd, joins_refl _ _, Or.inl ?_⟩
    have hmem : e ∈ Q.data.vertexOf d := hde ▸ Q.data.self_mem_vertexOf e
    rcases hd.mem_vertexOf_iff.1 hmem with rfl | rfl
    · exact PlabicData.Isomorphic.refl _
    · exact bivalentRemoval_isomorphic_rot hG hd
  · have hed : Q.data.vertexOf e ≠ Q.data.vertexOf d := Ne.symm hde
    have hd' := isBivalentRemovable_bivalentRemoval hG hbv hf hd he hde
    have he' := isBivalentRemovable_bivalentRemoval hG hbv hf he hd hed
    have m₁ := mem_compl_rot_of_vertexOf_ne hde
    have m₂ := mem_compl_rot_of_vertexOf_ne (G := Q.data) (d := d) (e := Q.data.rot e)
      (by rwa [Q.data.vertexOf_rot])
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at m₁ m₂
    have hnd : [d, Q.data.rot d, e, Q.data.rot e].Nodup :=
      nodup_four hd.rot_ne.symm (Ne.symm m₁.1) (Ne.symm m₂.1) (Ne.symm m₁.2) (Ne.symm m₂.2)
        he.rot_ne.symm
    have hl₁ := leg_mem_compl_four hG hd.not_isBoundaryVertex
      (not_isBoundaryVertex_vertexOf_rot hd.not_isBoundaryVertex) he.not_isBoundaryVertex
      (not_isBoundaryVertex_vertexOf_rot he.not_isBoundaryVertex)
    have hl₂ := leg_mem_compl_four hG he.not_isBoundaryVertex
      (not_isBoundaryVertex_vertexOf_rot he.not_isBoundaryVertex) hd.not_isBoundaryVertex
      (not_isBoundaryVertex_vertexOf_rot hd.not_isBoundaryVertex)
    refine ⟨(Q.removal hd).removal hd', joins_of_step (isReductionStep_removal _ hd'
        fun h₁ => side_bivalentRemoval hG hd _ (hsd h₁) (hse h₁)),
      Or.inr ⟨(Q.removal he).removal he', isReductionStep_removal _ he'
        fun h₁ => side_bivalentRemoval hG he _ (hse h₁) (hsd h₁), ?_⟩⟩
    exact iso_trans (bivalentRemoval_bivalentRemoval_isomorphic hG hd _ hd' hl₁)
      (iso_trans (firstReturnRestrict_swap_isomorphic hnd hl₁ hl₂)
        (iso_symm (bivalentRemoval_bivalentRemoval_isomorphic hG he _ he' hl₂)))

private theorem diamond_contraction_contraction {ε : Fin 2} {Q : PlabicGraph b}
    (hbv : Q.data.boundaryVertices.card = 1) (hf : Q.data.faces.card = 1) {d e : Q.Dart}
    (hd : Q.data.IsContractibleEdge d) (he : Q.data.IsContractibleEdge e) :
    ∃ Q₃, Joins ε (Q.contraction hd) Q₃ ∧ Joins ε (Q.contraction he) Q₃ := by
  have hG := Q.isPlabicGraph
  have hinv := hG.inv_involutive
  by_cases hde : e = d ∨ e = Q.data.inv d
  · refine ⟨Q.contraction hd, joins_refl _ _, Or.inl ?_⟩
    rcases hde with rfl | rfl
    · exact PlabicData.Isomorphic.refl _
    · exact contractEdge_isomorphic_inv hG hd
  · rw [not_or] at hde
    have m₁ : e ∈ (({d, Q.data.inv d} : Set Q.Dart)ᶜ : Set Q.Dart) := mem_compl_pair_iff.2 hde
    have hed : d ≠ e ∧ d ≠ Q.data.inv e :=
      ⟨Ne.symm hde.1, fun h => hde.2 (by rw [h, hinv])⟩
    have m₂ : d ∈ (({e, Q.data.inv e} : Set Q.Dart)ᶜ : Set Q.Dart) := mem_compl_pair_iff.2 hed
    have hd' := isContractibleEdge_contractEdge hG hbv hf hd he m₁
    have he' := isContractibleEdge_contractEdge hG hbv hf he hd m₂
    have hnd : [d, Q.data.inv d, e, Q.data.inv e].Nodup :=
      nodup_four (hG.inv_ne d).symm hed.1 hed.2 (Ne.symm hde.2)
        (fun h => hed.1 (Q.data.inv.injective h)) (hG.inv_ne e).symm
    have hl₁ := leg_mem_compl_four hG hd.not_isBoundaryVertex hd.not_isBoundaryVertex_inv
      he.not_isBoundaryVertex he.not_isBoundaryVertex_inv
    have hl₂ := leg_mem_compl_four hG he.not_isBoundaryVertex he.not_isBoundaryVertex_inv
      hd.not_isBoundaryVertex hd.not_isBoundaryVertex_inv
    refine ⟨(Q.contraction hd).contraction hd', joins_of_step (isReductionStep_contraction _ hd'),
      Or.inr ⟨(Q.contraction he).contraction he', isReductionStep_contraction _ he', ?_⟩⟩
    exact iso_trans (contractEdge_contractEdge_isomorphic hG hd m₁ hd' hl₁)
      (iso_trans (firstReturnRestrict_swap_isomorphic hnd hl₁ hl₂)
        (iso_symm (contractEdge_contractEdge_isomorphic hG he m₂ he' hl₂)))

private theorem diamond_removal_contraction {ε : Fin 2} {Q : PlabicGraph b} {d e : Q.Dart}
    (hd : Q.data.IsBivalentRemovable d)
    (hsd : ε = 1 → ∀ i, Q.data.inv (Q.data.leg i) ∉ Q.data.vertexOf d)
    (he : Q.data.IsContractibleEdge e) :
    ∃ Q₃, Joins ε (Q.removal hd) Q₃ ∧ Joins ε (Q.contraction he) Q₃ := by
  have hG := Q.isPlabicGraph
  have hinv := hG.inv_involutive
  by_cases hinc : e = d ∨ e = Q.data.rot d ∨ Q.data.inv e = d ∨ Q.data.inv e = Q.data.rot d
  · refine ⟨Q.removal hd, joins_refl _ _, Or.inl ?_⟩
    have hr := bivalentRemoval_isomorphic_rot hG hd
    have hinvi := contractEdge_isomorphic_inv hG he
    rcases hinc with h | h | h | h
    · exact iso_trans (bivalentRemoval_isomorphic_contractEdge hG hd (h ▸ he))
        (contractEdge_isomorphic_of_eq h.symm _ _)
    · exact iso_trans hr (iso_trans
        (bivalentRemoval_isomorphic_contractEdge hG (hd.rot' hG) (h ▸ he))
        (contractEdge_isomorphic_of_eq h.symm _ _))
    · exact iso_trans (bivalentRemoval_isomorphic_contractEdge hG hd (h ▸ he.inv' hG))
        (iso_trans (contractEdge_isomorphic_of_eq h.symm _ _) (iso_symm hinvi))
    · exact iso_trans hr (iso_trans
        (bivalentRemoval_isomorphic_contractEdge hG (hd.rot' hG) (h ▸ he.inv' hG))
        (iso_trans (contractEdge_isomorphic_of_eq h.symm _ _) (iso_symm hinvi)))
  · simp only [not_or] at hinc
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hinc
    have m₁ : e ∈ ({d, Q.data.rot d}ᶜ : Set Q.Dart) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h₁, h₂⟩
    have he₁ : e ≠ Q.data.inv d := fun h => h₃ (by rw [h, hinv])
    have he₂ : e ≠ Q.data.inv (Q.data.rot d) := fun h => h₄ (by rw [h, hinv])
    have m₂ : d ∈ (({e, Q.data.inv e} : Set Q.Dart)ᶜ : Set Q.Dart) :=
      mem_compl_pair_iff.2 ⟨Ne.symm h₁, Ne.symm h₃⟩
    have hrd : Q.data.rot d ∈ (({e, Q.data.inv e} : Set Q.Dart)ᶜ : Set Q.Dart) :=
      mem_compl_pair_iff.2 ⟨Ne.symm h₂, Ne.symm h₄⟩
    have hnot : d ∉ Q.data.vertexOf e ∪ Q.data.vertexOf (Q.data.inv e) := by
      rw [Finset.mem_union, not_or]
      refine ⟨fun hm => ?_, fun hm => ?_⟩
      · have h' : e ∈ Q.data.vertexOf d := by
          rw [Q.data.vertexOf_eq_of_mem hm]
          exact Q.data.self_mem_vertexOf e
        exact (hd.mem_vertexOf_iff.1 h').elim h₁ h₂
      · have h' : Q.data.inv e ∈ Q.data.vertexOf d := by
          rw [Q.data.vertexOf_eq_of_mem hm]
          exact Q.data.self_mem_vertexOf _
        exact (hd.mem_vertexOf_iff.1 h').elim h₃ h₄
    have he' := isContractibleEdge_bivalentRemoval hG hd he m₁ he₁ he₂
    have hd' := isBivalentRemovable_contractEdge hG hd he m₂ hnot hrd
    have hnd : [d, Q.data.rot d, e, Q.data.inv e].Nodup :=
      nodup_four hd.rot_ne.symm (Ne.symm h₁) (Ne.symm h₃) (Ne.symm h₂) (Ne.symm h₄)
        (hG.inv_ne e).symm
    have hl₁ := leg_mem_compl_four hG hd.not_isBoundaryVertex
      (not_isBoundaryVertex_vertexOf_rot hd.not_isBoundaryVertex) he.not_isBoundaryVertex
      he.not_isBoundaryVertex_inv
    have hl₂ := leg_mem_compl_four hG he.not_isBoundaryVertex he.not_isBoundaryVertex_inv
      hd.not_isBoundaryVertex (not_isBoundaryVertex_vertexOf_rot hd.not_isBoundaryVertex)
    refine ⟨(Q.removal hd).contraction he', joins_of_step (isReductionStep_contraction _ he'),
      Or.inr ⟨(Q.contraction he).removal hd', isReductionStep_removal _ hd'
        fun hε => side_contractEdge hG he m₂ hnot (hsd hε), ?_⟩⟩
    exact iso_trans (contractEdge_bivalentRemoval_isomorphic hG hd m₁ he₁ he₂ he' hl₁)
      (iso_trans (firstReturnRestrict_swap_isomorphic hnd hl₁ hl₂)
        (iso_symm (bivalentRemoval_contractEdge_isomorphic hG he m₂ hrd hd' hl₂)))

/-- **Reduction steps of plabic trees commute**. Let `ε ∈ {0, 1}`, let `Q` be a plabic graph with
one boundary vertex and exactly one face, and let `Q₁` and `Q₂` be obtained from `Q` by
`ε`-reduction steps. Then there is a plabic graph `Q₃` such that, for each `i ∈ {1, 2}`, `Q₃` is
isomorphic to `Qᵢ` or to a graph obtained from `Qᵢ` by an `ε`-reduction step. -/
@[cluster_algebras "lem_tree_reduction_diamond"]
theorem IsReductionStep.diamond {ε : Fin 2} {Q Q₁ Q₂ : PlabicGraph b}
    (hbv : Q.data.boundaryVertices.card = 1) (hf : Q.data.faces.card = 1)
    (h₁ : IsReductionStep ε Q Q₁) (h₂ : IsReductionStep ε Q Q₂) :
    ∃ Q₃ : PlabicGraph b,
      (Q₃.Isomorphic Q₁ ∨ ∃ Q', IsReductionStep ε Q₁ Q' ∧ Q₃.Isomorphic Q') ∧
        (Q₃.Isomorphic Q₂ ∨ ∃ Q', IsReductionStep ε Q₂ Q' ∧ Q₃.Isomorphic Q') := by
  rcases h₁ with ⟨d, hd, hsd, hQ₁⟩ | ⟨d, hd, hQ₁⟩ <;>
    rcases h₂ with ⟨e, he, hse, hQ₂⟩ | ⟨e, he, hQ₂⟩
  · obtain ⟨Q₃, j₁, j₂⟩ := diamond_removal_removal hbv hf hd he hsd hse
    exact ⟨Q₃, j₁.of_isomorphic hQ₁, j₂.of_isomorphic hQ₂⟩
  · obtain ⟨Q₃, j₁, j₂⟩ := diamond_removal_contraction hd hsd he
    exact ⟨Q₃, j₁.of_isomorphic hQ₁, j₂.of_isomorphic hQ₂⟩
  · obtain ⟨Q₃, j₂, j₁⟩ := diamond_removal_contraction he hse hd
    exact ⟨Q₃, j₁.of_isomorphic hQ₁, j₂.of_isomorphic hQ₂⟩
  · obtain ⟨Q₃, j₁, j₂⟩ := diamond_contraction_contraction hbv hf hd he
    exact ⟨Q₃, j₁.of_isomorphic hQ₁, j₂.of_isomorphic hQ₂⟩

/-! ### Irreducible plabic trees -/

/-- Isomorphism of bundled plabic graphs, as a setoid. -/
private def isoSetoid (b : ℕ) : Setoid (PlabicGraph b) where
  r := PlabicGraph.Isomorphic
  iseqv := ⟨fun _ => PlabicData.Isomorphic.refl _, iso_symm, iso_trans⟩

/-- A `0`-reduction step from a plabic graph with exactly one face. -/
private def TreeStep (A C : PlabicGraph b) : Prop :=
  A.data.faces.card = 1 ∧ IsReductionStep 0 A C

/-- `TreeStep` on isomorphism classes. -/
private def QStep : Quotient (isoSetoid b) → Quotient (isoSetoid b) → Prop :=
  Quotient.lift₂ TreeStep fun A C A' C' (hA : A.Isomorphic A') (hC : C.Isomorphic C') =>
    propext ⟨fun ⟨hf, hs⟩ => ⟨(PlabicData.Isomorphic.card_faces hA).symm.trans hf,
        (hs.of_isomorphic (iso_symm hA)).of_isomorphic_right hC⟩,
      fun ⟨hf, hs⟩ => ⟨(PlabicData.Isomorphic.card_faces hA).trans hf,
        (hs.of_isomorphic hA).of_isomorphic_right (iso_symm hC)⟩⟩

private theorem qStep_mk {A C : PlabicGraph b} :
    QStep (Quotient.mk (isoSetoid b) A) (Quotient.mk (isoSetoid b) C) ↔ TreeStep A C :=
  Iff.rfl

private theorem qStep_diamond (hb : b = 1) (a c₁ c₂ : Quotient (isoSetoid b)) (h₁ : QStep a c₁)
    (h₂ : QStep a c₂) :
    ∃ d, Relation.ReflGen QStep c₁ d ∧ Relation.ReflTransGen QStep c₂ d := by
  obtain ⟨A, rfl⟩ := Quotient.exists_rep a
  obtain ⟨C₁, rfl⟩ := Quotient.exists_rep c₁
  obtain ⟨C₂, rfl⟩ := Quotient.exists_rep c₂
  obtain ⟨hf, s₁⟩ := qStep_mk.1 h₁
  obtain ⟨-, s₂⟩ := qStep_mk.1 h₂
  have hbv : A.data.boundaryVertices.card = 1 := by
    rw [A.isPlabicGraph.card_boundaryVertices, hb]
  obtain ⟨Q₃, j₁, j₂⟩ := IsReductionStep.diamond hbv hf s₁ s₂
  have hf₁ : C₁.data.faces.card = 1 := (s₁.moveStep.card_eq.1).symm.trans hf
  have hf₂ : C₂.data.faces.card = 1 := (s₂.moveStep.card_eq.1).symm.trans hf
  refine ⟨Quotient.mk (isoSetoid b) Q₃, ?_, ?_⟩
  · rcases j₁ with h | ⟨Q', hs, hi⟩
    · rw [Quotient.sound (show (isoSetoid b) C₁ Q₃ from iso_symm h)]
    · exact Relation.ReflGen.single (qStep_mk.2 ⟨hf₁, hs.of_isomorphic_right (iso_symm hi)⟩)
  · rcases j₂ with h | ⟨Q', hs, hi⟩
    · rw [Quotient.sound (show (isoSetoid b) C₂ Q₃ from iso_symm h)]
    · exact Relation.ReflTransGen.single
        (qStep_mk.2 ⟨hf₂, hs.of_isomorphic_right (iso_symm hi)⟩)

private theorem eq_of_reflTransGen_qStep {Q : PlabicGraph b} (hQ : IsIrreducible 0 Q)
    {D : Quotient (isoSetoid b)} (h : Relation.ReflTransGen QStep (Quotient.mk _ Q) D) :
    D = Quotient.mk _ Q := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · exact h.symm
  · obtain ⟨C, rfl⟩ := Quotient.exists_rep c
    exact (hQ C (qStep_mk.1 hc).2).elim

/-- **Irreducible plabic trees in one class are isomorphic**. Let `Q` and `Q'` be plabic graphs
with one boundary vertex and exactly one face that are `{M2, M3}`-equivalent and `0`-irreducible.
Then `Q` and `Q'` are isomorphic. -/
@[cluster_algebras "lem_tree_reduction_normal_form"]
theorem isomorphic_of_moveEquivalent_of_isIrreducible {Q Q' : PlabicGraph b}
    (hbv : Q.data.boundaryVertices.card = 1) (hf : Q.data.faces.card = 1)
    (_hbv' : Q'.data.boundaryVertices.card = 1) (_hf' : Q'.data.faces.card = 1)
    (h : MoveEquivalent {.m2, .m3} Q Q') (hQ : IsIrreducible 0 Q) (hQ' : IsIrreducible 0 Q') :
    Q.Isomorphic Q' := by
  have hb : b = 1 := by rw [← Q.isPlabicGraph.card_boundaryVertices, hbv]
  have heq := Relation.equivalence_join_reflTransGen (qStep_diamond hb)
  have key : ∀ A, MoveEquivalent {.m2, .m3} Q A →
      Relation.Join (Relation.ReflTransGen QStep) (Quotient.mk (isoSetoid b) Q)
        (Quotient.mk (isoSetoid b) A) := by
    intro A hA
    induction hA with
    | refl => exact heq.refl _
    | @tail B C hQB hBC ih =>
      refine heq.trans ih ?_
      have hfB : B.data.faces.card = 1 := (MoveEquivalent.card_eq hQB).2.1.symm.trans hf
      have hfC : C.data.faces.card = 1 := (MoveStep.card_eq hBC).1.symm.trans hfB
      have h0 : ¬((0 : Fin 2) = 1) := by decide
      rcases hBC with hiso | ⟨t, ht, hloc⟩
      · rw [Quotient.sound (show (isoSetoid b) B C from iso_symm hiso)]
        exact heq.refl _
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with rfl | rfl
        · rcases hloc with ⟨d, hd, hiso⟩ | ⟨d, hd, hiso⟩
          · exact ⟨_, Relation.ReflTransGen.single
              (qStep_mk.2 ⟨hfB, Or.inl ⟨d, hd, fun h => (h0 h).elim, hiso⟩⟩),
              Relation.ReflTransGen.refl⟩
          · exact ⟨_, Relation.ReflTransGen.refl, Relation.ReflTransGen.single
              (qStep_mk.2 ⟨hfC, Or.inl ⟨d, hd, fun h => (h0 h).elim, hiso⟩⟩)⟩
        · rcases hloc with ⟨d, hd⟩ | ⟨d, hd⟩
          · exact ⟨_, Relation.ReflTransGen.single (qStep_mk.2 ⟨hfB, Or.inr ⟨d, hd⟩⟩),
              Relation.ReflTransGen.refl⟩
          · exact ⟨_, Relation.ReflTransGen.refl,
              Relation.ReflTransGen.single (qStep_mk.2 ⟨hfC, Or.inr ⟨d, hd⟩⟩)⟩
  obtain ⟨D, h₁, h₂⟩ := key Q' h
  have e₁ := eq_of_reflTransGen_qStep hQ h₁
  have e₂ := eq_of_reflTransGen_qStep hQ' h₂
  exact Quotient.exact (e₁.symm.trans e₂)

end PlabicGraph

/-! ### Frozen reduction of the plabic graph of a tree -/

namespace PlabicData

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- In a plabic graph with one boundary vertex, the dart across the leg lies at an internal
vertex. -/
private theorem not_isBoundaryVertex_inv_leg {X : PlabicData H 1} (hX : X.IsPlabicGraph) :
    ¬X.IsBoundaryVertex (X.vertexOf (X.inv (X.leg 0))) := by
  intro hB
  obtain ⟨i, hi⟩ := hX.exists_bvertex_eq _ (X.vertexOf_mem_boundaryVertices.2 hB)
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hmem : X.inv (X.leg 0) ∈ (X.bvertex 0).filter (· ∉ X.bdry) := by
    rw [mem_filter, hi]
    exact ⟨X.self_mem_vertexOf _, fun h => hX.leg_notMem_bdry 0 (hX.inv_mem_bdry_iff.1 h)⟩
  rw [hX.filter_bvertex_notMem_bdry, mem_singleton] at hmem
  exact hX.inv_ne _ hmem

private theorem rot_eq_of_card_vertexOf_inv_leg_eq_one {X : PlabicData H 1}
    (hX : X.IsPlabicGraph) (h₁ : (X.vertexOf (X.inv (X.leg 0))).card = 1) :
    ∃ ex ∈ X.bdry, X.rot ex = X.leg 0 ∧ X.rot (X.leg 0) = X.inv ex ∧ X.rot (X.inv ex) = ex ∧
      X.rot (X.inv (X.leg 0)) = X.inv (X.leg 0) := by
  have hdeg := hX.boundaryVertex_card
  have hv₀ : X.IsBoundaryVertex (X.vertexOf (X.leg 0)) :=
    X.vertexOf_mem_boundaryVertices.1 (hX.bvertex_mem 0)
  obtain ⟨ex, hex, hex₀, hiex₀⟩ := hX.exists_exterior 0
  rw [show finRotate 1 0 = 0 from Subsingleton.elim _ _] at hex₀
  have hexB := X.exterior_subset_bdry hex
  have hbarB : X.inv ex ∈ X.bdry := hX.inv_mem_bdry _ hexB
  have notB_eq : ∀ y ∈ X.bvertex 0, y ∉ X.bdry → y = X.leg 0 := fun y hy hyB => by
    have : y ∈ (X.bvertex 0).filter (· ∉ X.bdry) := mem_filter.2 ⟨hy, hyB⟩
    rwa [hX.filter_bvertex_notMem_bdry 0, mem_singleton] at this
  have hrot_mem : ∀ y ∈ X.bvertex 0, X.rot y ∈ X.bvertex 0 := fun y hy => by
    unfold bvertex at hy ⊢
    rw [← X.vertexOf_eq_of_mem hy]
    exact X.rot_mem_vertexOf y
  have hne₁ : X.inv ex ≠ ex := hX.inv_ne ex
  have tri : ∀ y ∈ X.bvertex 0, y = ex ∨ y = X.inv ex ∨ y = X.leg 0 := by
    intro y hy
    by_cases hyB : y ∈ X.bdry
    · by_contra hcon
      simp only [not_or] at hcon
      exact DiskMap.not_three_mem_bdry hdeg hv₀ hex₀ hiex₀ hy hexB hbarB hyB hne₁.symm
        (Ne.symm hcon.1) (Ne.symm hcon.2.1)
    · exact Or.inr (Or.inr (notB_eq y hy hyB))
  have hvex : X.IsBoundaryVertex (X.vertexOf ex) := X.isBoundaryVertex_vertexOf_of_mem hexB
  have e₁ : X.rot ex = X.leg 0 := notB_eq _ (hrot_mem _ hex₀) (X.mem_exterior.1 hex).2
  have e₂ : X.rot (X.leg 0) = X.inv ex := by
    rcases tri _ (hrot_mem _ (X.leg_mem_bvertex 0)) with h | h | h
    · exact absurd (by rw [e₁, h]) (DiskMap.rot_rot_ne_of_isBoundaryVertex hdeg hvex)
    · exact h
    · exact absurd h (DiskMap.rot_ne_of_isBoundaryVertex hdeg hv₀)
  have e₃ : X.rot (X.inv ex) = ex := by
    rcases tri _ (hrot_mem _ hiex₀) with h | h | h
    · exact h
    · exact absurd h (DiskMap.rot_ne_of_isBoundaryVertex hdeg
        (X.isBoundaryVertex_vertexOf_of_mem hbarB))
    · exact absurd (X.rot.injective (h.trans e₁.symm)) hne₁
  have e₄ : X.rot (X.inv (X.leg 0)) = X.inv (X.leg 0) := by
    obtain ⟨a, ha⟩ := card_eq_one.1 h₁
    have m₁ := X.self_mem_vertexOf (X.inv (X.leg 0))
    have m₂ := X.rot_mem_vertexOf (X.inv (X.leg 0))
    rw [ha, mem_singleton] at m₁ m₂
    exact m₂.trans m₁.symm
  exact ⟨ex, hexB, e₁, e₂, e₃, e₄⟩

/-- A plabic graph with one boundary vertex in which the dart across the leg forms a vertex by
itself, of colour `c`, is isomorphic to the lollipop graph `L_c`. -/
private theorem lollipopGraph_isomorphic {X : PlabicData H 1} (hX : X.IsPlabicGraph) {c : Shade}
    (h₁ : (X.vertexOf (X.inv (X.leg 0))).card = 1) (hc : X.colour (X.inv (X.leg 0)) = c) :
    (lollipopGraph c).Isomorphic X := by
  obtain ⟨ex, hexB, e₁, e₂, e₃, e₄⟩ := rot_eq_of_card_vertexOf_inv_leg_eq_one hX h₁
  have hinv := hX.inv_involutive
  have hx₀B := hX.leg_notMem_bdry 0
  have hbarB : X.inv ex ∈ X.bdry := hX.inv_mem_bdry _ hexB
  have n₁ : ex ≠ X.inv ex := (hX.inv_ne ex).symm
  have n₂ : ex ≠ X.leg 0 := fun h => hx₀B (h ▸ hexB)
  have n₃ : ex ≠ X.inv (X.leg 0) := fun h => n₂ (by rw [← e₁, h, e₄])
  have n₄ : X.inv ex ≠ X.leg 0 := fun h => hx₀B (h ▸ hbarB)
  have n₅ : X.inv ex ≠ X.inv (X.leg 0) := fun h => n₂ (X.inv.injective h)
  have n₆ : X.leg 0 ≠ X.inv (X.leg 0) := (hX.inv_ne _).symm
  let f : LollipopDart → H
    | .e => ex
    | .eBar => X.inv ex
    | .g => X.leg 0
    | .gBar => X.inv (X.leg 0)
  have hf : Function.Injective f := by
    intro a a' h
    cases a <;> cases a' <;> first
      | rfl
      | exact absurd h ‹_›
      | exact absurd h.symm ‹_›
  have hsurj : ∀ y, X.Reach ex y → y ∈ Set.range f := by
    intro y hy
    induction hy with
    | refl => exact ⟨.e, rfl⟩
    | rot _ ih =>
      obtain ⟨a, rfl⟩ := ih
      cases a
      exacts [⟨.g, e₁.symm⟩, ⟨.e, e₃.symm⟩, ⟨.eBar, e₂.symm⟩, ⟨.gBar, e₄.symm⟩]
    | inv _ ih =>
      obtain ⟨a, rfl⟩ := ih
      cases a
      exacts [⟨.eBar, rfl⟩, ⟨.e, (hinv ex).symm⟩, ⟨.gBar, rfl⟩, ⟨.g, (hinv _).symm⟩]
  have hL : ∀ d : LollipopDart, (lollipopGraph c).IsBoundaryVertex ((lollipopGraph c).vertexOf d) ∨
      d = .gBar := by
    cases c <;> decide
  have r₁ : (lollipopGraph c).rot .e = .g := by cases c <;> decide
  have r₂ : (lollipopGraph c).rot .eBar = .e := by cases c <;> decide
  have r₃ : (lollipopGraph c).rot .g = .eBar := by cases c <;> decide
  have r₄ : (lollipopGraph c).rot .gBar = .gBar := by cases c <;> decide
  refine ⟨Iso.ofMapLeg (Equiv.ofBijective f ⟨hf, fun y => hsurj y (hX.reach ex y)⟩)
    (fun d => ?_) (fun d => ?_) (fun d => ?_) (fun d hd => ?_) fun i => ?_⟩
  · cases d
    exacts [rfl, (hinv ex).symm, rfl, (hinv _).symm]
  · cases d
    exacts [(congrArg f r₁).trans e₁.symm, (congrArg f r₂).trans e₃.symm,
      (congrArg f r₃).trans e₂.symm, (congrArg f r₄).trans e₄.symm]
  · cases d
    · exact iff_of_true hexB (by cases c <;> decide)
    · exact iff_of_true hbarB (by cases c <;> decide)
    · exact iff_of_false hx₀B (by cases c <;> decide)
    · exact iff_of_false (fun h => hx₀B (hX.inv_mem_bdry_iff.1 h)) (by cases c <;> decide)
  · rcases hL d with h | rfl
    · exact absurd h hd
    · exact hc
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl

end PlabicData

namespace PlabicGraph

open PlabicData

/-- The lollipop graph is `ε`-irreducible. -/
private theorem isIrreducible_lollipopPlabicGraph (c : Shade) (ε : Fin 2) :
    IsIrreducible ε (lollipopPlabicGraph c) := by
  intro Q' hs
  have k₁ : ∀ x : LollipopDart, ((lollipopGraph c).vertexOf x).card ≠ 2 := by
    cases c <;> decide
  have k₂ : ∀ x : LollipopDart, (lollipopGraph c).vertexOf x ∈ (lollipopGraph c).internalVertices →
      (lollipopGraph c).vertexOf ((lollipopGraph c).inv x) ∈ (lollipopGraph c).internalVertices →
      False := by
    cases c <;> decide
  rcases hs with ⟨x, hx, -, -⟩ | ⟨x, hx, -⟩
  · exact k₁ x hx.card_vertexOf
  · exact k₂ x hx.mem_internalVertices hx.inv_mem_internalVertices

/-- A `1`-reduction step keeps the colour of the dart across the leg. -/
private theorem colour_inv_leg_eq_of_isReductionStep {A C : PlabicGraph 1}
    (h : IsReductionStep 1 A C) :
    C.data.colour (C.data.inv (C.data.leg 0)) = A.data.colour (A.data.inv (A.data.leg 0)) := by
  have hx := not_isBoundaryVertex_inv_leg C.isPlabicGraph
  have hA := A.isPlabicGraph
  have hinv := hA.inv_involutive
  rcases h with ⟨d, hd, hside, ⟨θ⟩⟩ | ⟨d, he, ⟨θ⟩⟩
  · have hs := hside rfl 0
    have h₁ : A.data.leg 0 ≠ A.data.inv d := fun h =>
      hs (by rw [h, hinv]; exact A.data.self_mem_vertexOf d)
    have h₂ : A.data.leg 0 ≠ A.data.inv (A.data.rot d) := fun h =>
      hs (by rw [h, hinv]; exact A.data.rot_mem_vertexOf d)
    rw [← θ.map_colour _ hx, θ.map_inv,
      Iso.map_leg C.isPlabicGraph (isPlabicGraph_bivalentRemoval hA hd) θ, bivalentRemoval_colour,
      coe_bivalentRemoval_inv_of_ne (y := (A.data.bivalentRemoval hA hd).leg 0) hA hd h₁ h₂]
    rfl
  · rw [← θ.map_colour _ hx, θ.map_inv, Iso.map_leg C.isPlabicGraph (hA.contractEdge he) θ,
      contractEdge_colour, coe_contractEdge_inv hinv]
    rfl

private theorem invariants_of_reflTransGen_isReductionStep {P R : PlabicGraph 1} {c : Shade}
    (hPf : P.data.faces.card = 1) (hPc : P.data.colour (P.data.inv (P.data.leg 0)) = c)
    (hR : Relation.ReflTransGen (IsReductionStep 1) P R) :
    R.data.faces.card = 1 ∧ R.data.colour (R.data.inv (R.data.leg 0)) = c ∧
      MoveEquivalent {.m2, .m3} P R := by
  induction hR with
  | refl => exact ⟨hPf, hPc, MoveEquivalent.refl _ _⟩
  | tail _ hs ih =>
    exact ⟨(hs.moveStep.card_eq.1).symm.trans ih.1,
      (colour_inv_leg_eq_of_isReductionStep hs).trans ih.2.1,
      ih.2.2.trans (MoveEquivalent.of_moveStep hs.moveStep)⟩

private theorem not_isBivalentRemovable_bivalentRemoval {R : PlabicGraph 1}
    (hRf : R.data.faces.card = 1) {g : R.Dart} (hg : R.data.IsBivalentRemovable g)
    (hrem : ∀ x, R.data.IsBivalentRemovable x → g ∈ R.data.vertexOf x)
    (y : ({g, R.data.rot g}ᶜ : Set R.Dart)) :
    ¬(R.data.bivalentRemoval R.isPlabicGraph hg).IsBivalentRemovable y := by
  intro hy
  have hyb := (isBoundaryVertex_bivalentRemoval_vertexOf_iff R.isPlabicGraph hg y).not.1
    hy.not_isBoundaryVertex
  have hyX : R.data.IsBivalentRemovable y := by
    refine ⟨hyb, ?_, fun h => ?_⟩
    · rw [← map_bivalentRemoval_vertexOf R.isPlabicGraph hg y, card_map]
      exact hy.card_vertexOf
    · refine R.isPlabicGraph.vertexOf_ne_vertexOf_inv_of_card_faces_eq_one
        R.isPlabicGraph.card_boundaryVertices hRf
        (fun hB => hyb (R.data.isBoundaryVertex_vertexOf_of_mem hB)) ?_
      rw [h, R.data.vertexOf_rot]
  have h₂ : (y : R.Dart) ∈ R.data.vertexOf g := by
    rw [R.data.vertexOf_eq_of_mem (hrem _ hyX)]
    exact R.data.self_mem_vertexOf _
  have hy2 := y.2
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy2
  exact (hg.mem_vertexOf_iff.1 h₂).elim hy2.1 hy2.2

private theorem not_isContractibleEdge_bivalentRemoval {R : PlabicGraph 1} {g : R.Dart}
    (hg : R.data.IsBivalentRemovable g) (hlg : R.data.inv g = R.data.leg 0)
    (hcon : ∀ x, ¬R.data.IsContractibleEdge x) (y : ({g, R.data.rot g}ᶜ : Set R.Dart)) :
    ¬(R.data.bivalentRemoval R.isPlabicGraph hg).IsContractibleEdge y := by
  have hv₀ := R.data.vertexOf_mem_boundaryVertices.1 (R.isPlabicGraph.bvertex_mem 0)
  intro hy
  have hyint := hy.mem_internalVertices
  rw [DiskMap.vertexOf_mem_internalVertices,
    isBoundaryVertex_bivalentRemoval_vertexOf_iff] at hyint
  by_cases h₁ : (y : R.Dart) = R.data.inv g
  · rw [h₁, hlg] at hyint
    exact hyint hv₀
  by_cases h₂ : (y : R.Dart) = R.data.inv (R.data.rot g)
  · have hyint' := hy.inv_mem_internalVertices
    rw [DiskMap.vertexOf_mem_internalVertices, isBoundaryVertex_bivalentRemoval_vertexOf_iff,
      coe_bivalentRemoval_inv_of_eq_inv_rot R.isPlabicGraph hg h₂, hlg] at hyint'
    exact hyint' hv₀
  have hc' := coe_bivalentRemoval_inv_of_ne R.isPlabicGraph hg h₁ h₂
  refine hcon y ⟨fun h => hy.vertexOf_ne ?_, ?_, ?_, ?_⟩
  · apply Finset.map_injective (Function.Embedding.subtype _)
    rwa [map_bivalentRemoval_vertexOf, map_bivalentRemoval_vertexOf, hc']
  · rwa [DiskMap.vertexOf_mem_internalVertices]
  · have := hy.inv_mem_internalVertices
    rw [DiskMap.vertexOf_mem_internalVertices,
      isBoundaryVertex_bivalentRemoval_vertexOf_iff, hc'] at this
    rwa [DiskMap.vertexOf_mem_internalVertices]
  · have := hy.colour_inv
    rwa [bivalentRemoval_colour, bivalentRemoval_colour, hc'] at this

private theorem false_of_card_vertexOf_inv_leg_eq_two {R : PlabicGraph 1} {c : Shade}
    (hRf : R.data.faces.card = 1) (hRc : R.data.colour (R.data.inv (R.data.leg 0)) = c)
    (hML : MoveEquivalent {.m2, .m3} R (lollipopPlabicGraph c))
    (hrem : ∀ x, R.data.IsBivalentRemovable x → R.data.inv (R.data.leg 0) ∈ R.data.vertexOf x)
    (hcon : ∀ x, ¬R.data.IsContractibleEdge x)
    (hm : (R.data.vertexOf (R.data.inv (R.data.leg 0))).card = 2) : False := by
  have hX := R.isPlabicGraph
  have hinv := hX.inv_involutive
  have hgint := not_isBoundaryVertex_inv_leg hX
  set g' := R.data.inv (R.data.leg 0) with hg'
  have hlg : R.data.inv g' = R.data.leg 0 := hinv _
  have hleg_ne : R.data.leg 0 ≠ R.data.rot g' := fun h => hgint (by
    rw [← R.data.vertexOf_rot g', ← h]
    exact R.data.vertexOf_mem_boundaryVertices.1 (hX.bvertex_mem 0))
  have hgr : R.data.IsBivalentRemovable g' := ⟨hgint, hm, by rwa [hlg]⟩
  have hstep : IsReductionStep 0 R (R.removal hgr) :=
    isReductionStep_removal R hgr fun h => absurd h (by decide)
  have hR'0 : IsIrreducible 0 (R.removal hgr) := by
    rintro Q' (⟨y, hy, -, -⟩ | ⟨y, hy, -⟩)
    · exact not_isBivalentRemovable_bivalentRemoval hRf hgr hrem y hy
    · exact not_isContractibleEdge_bivalentRemoval hgr hlg hcon y hy
  obtain ⟨θ⟩ := isomorphic_of_moveEquivalent_of_isIrreducible
    (R.removal hgr).isPlabicGraph.card_boundaryVertices
    ((hstep.moveStep.card_eq.1).symm.trans hRf)
    (lollipopPlabicGraph c).isPlabicGraph.card_boundaryVertices
    (by change (lollipopGraph c).faces.card = 1; rw [faces_lollipopGraph]; rfl)
    ((MoveEquivalent.of_moveStep hstep.moveStep).symm.trans hML) hR'0
    (isIrreducible_lollipopPlabicGraph c 0)
  set a := R.data.rot g'
  have haB : a ∉ R.data.bdry := fun hB => by
    have := R.data.isBoundaryVertex_vertexOf_of_mem hB
    rw [R.data.vertexOf_rot] at this
    exact hgint this
  have hia : R.data.inv a ∈ ({g', R.data.rot g'}ᶜ : Set R.Dart) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h => hleg_ne ?_, hX.inv_ne a⟩
    calc R.data.leg 0 = R.data.inv g' := hlg.symm
      _ = R.data.inv (R.data.inv a) := by rw [h]
      _ = a := hinv a
  have hint : ¬R.data.IsBoundaryVertex (R.data.vertexOf (R.data.inv a)) := by
    intro hB
    obtain ⟨i, hi⟩ := hX.exists_bvertex_eq _ (R.data.vertexOf_mem_boundaryVertices.2 hB)
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have hmem : R.data.inv a ∈ (R.data.bvertex 0).filter (· ∉ R.data.bdry) := by
      rw [mem_filter, hi]
      exact ⟨R.data.self_mem_vertexOf _, fun h => haB (hX.inv_mem_bdry_iff.1 h)⟩
    rw [hX.filter_bvertex_notMem_bdry, mem_singleton] at hmem
    exact hgr.rot_ne ((hinv a).symm.trans (congrArg R.data.inv hmem))
  have hcol := θ.map_colour ⟨R.data.inv a, hia⟩
    ((isBoundaryVertex_bivalentRemoval_vertexOf_iff hX hgr _).not.2 hint)
  change _ = R.data.colour (R.data.inv a) at hcol
  refine hcon a ⟨hX.vertexOf_ne_vertexOf_inv_of_card_faces_eq_one hX.card_boundaryVertices hRf haB,
    ?_, ?_, ?_⟩
  · rwa [DiskMap.vertexOf_mem_internalVertices, R.data.vertexOf_rot]
  · rwa [DiskMap.vertexOf_mem_internalVertices]
  · rw [← hcol, hX.colour_rot _ hgint, hRc]
    rfl

private theorem moveEquivalent_lollipopPlabicGraph_iff_of_card_faces_eq_one {P R : PlabicGraph 1}
    {c : Shade} (hPf : P.data.faces.card = 1) (hPc : P.data.colour (P.data.inv (P.data.leg 0)) = c)
    (hR : Relation.ReflTransGen (IsReductionStep 1) P R) (hirr : IsIrreducible 1 R) :
    MoveEquivalent {.m2, .m3} P (lollipopPlabicGraph c) ↔
      (R.data.vertexOf (R.data.inv (R.data.leg 0))).card = 1 := by
  obtain ⟨hRf, hRc, hPR⟩ := invariants_of_reflTransGen_isReductionStep hPf hPc hR
  have hX := R.isPlabicGraph
  have hrem : ∀ x (hx : R.data.IsBivalentRemovable x),
      R.data.inv (R.data.leg 0) ∈ R.data.vertexOf x := by
    intro x hx
    by_contra hn
    refine hirr _ (isReductionStep_removal R hx fun _ i => ?_)
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hn
  have hcon : ∀ x, ¬R.data.IsContractibleEdge x := fun x hx =>
    hirr _ (isReductionStep_contraction R hx)
  refine ⟨fun hML => ?_, fun h₁ =>
    hPR.trans (MoveEquivalent.of_isomorphic (lollipopGraph_isomorphic hX h₁ hRc))⟩
  replace hML : MoveEquivalent {.m2, .m3} R (lollipopPlabicGraph c) := hPR.symm.trans hML
  by_contra hcard
  by_cases hm : (R.data.vertexOf (R.data.inv (R.data.leg 0))).card = 2
  · exact false_of_card_vertexOf_inv_leg_eq_two hRf hRc hML hrem hcon hm
  have hR0 : IsIrreducible 0 R := by
    rintro Q' (⟨x, hx, -, -⟩ | ⟨x, hx, -⟩)
    · exact hm (by rw [R.data.vertexOf_eq_of_mem (hrem x hx)]; exact hx.card_vertexOf)
    · exact hcon x hx
  obtain ⟨θ⟩ := isomorphic_of_moveEquivalent_of_isIrreducible hX.card_boundaryVertices hRf
    (lollipopPlabicGraph c).isPlabicGraph.card_boundaryVertices
    (by change (lollipopGraph c).faces.card = 1; rw [faces_lollipopGraph]; rfl) hML hR0
    (isIrreducible_lollipopPlabicGraph c 0)
  have h₁ := θ.card_vertexOf (R.data.inv (R.data.leg 0))
  rw [θ.map_inv, Iso.map_leg hX (lollipopPlabicGraph c).isPlabicGraph θ] at h₁
  have hL₁ : ((lollipopGraph c).vertexOf ((lollipopGraph c).inv
      ((lollipopGraph c).leg 0))).card = 1 := by
    cases c <;> decide
  exact hcard (h₁.symm.trans hL₁)

end PlabicGraph

namespace PlabicData

namespace RootedTree

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {G : PlabicData H b}

/-- **Frozen reduction of the plabic graph of a tree**. Let `T = (v, W)` be a rooted tree of a
plabic graph `G` with `v` internal, let `c = κ(v)`, and let `R` be a `1`-irreducible plabic graph
obtained from `P_T` by a finite sequence of `1`-reduction steps. Then `P_T` is
`{M2, M3}`-equivalent to `L_c` if and only if the vertex of `R` containing `ḡ` consists of the dart
`ḡ` alone. Here `ḡ` is the dart of `R` across its leg `g`. -/
@[cluster_algebras "lem_frozen_reduction"]
theorem moveEquivalent_lollipopPlabicGraph_iff (hG : G.IsPlabicGraph) (T : G.RootedTree)
    (hv : ¬G.IsBoundaryVertex T.root) {c : Shade} (hc : ∀ d ∈ T.root, G.colour d = c)
    {R : PlabicGraph 1}
    (hR : Relation.ReflTransGen (PlabicGraph.IsReductionStep 1)
      ⟨T.Dart, T.plabicData, T.isPlabicGraph_plabicData hG⟩ R)
    (hirr : PlabicGraph.IsIrreducible 1 R) :
    PlabicGraph.MoveEquivalent {.m2, .m3} ⟨T.Dart, T.plabicData, T.isPlabicGraph_plabicData hG⟩
        (lollipopPlabicGraph c) ↔
      (R.data.vertexOf (R.data.inv (R.data.leg 0))).card = 1 := by
  refine PlabicGraph.moveEquivalent_lollipopPlabicGraph_iff_of_card_faces_eq_one
    (T.card_faces_plabicData hG) ?_ hR hirr
  have hl : ((T.plabicData.leg 0 : T.Dart) : H ⊕ LollipopDart) = .inr .g := by
    change (T.legDart : H ⊕ LollipopDart) = _
    unfold legDart
    rw [dif_neg hv]
  change T.colourAux (T.plabicData.inv (T.plabicData.leg 0)).1 = c
  rw [T.coe_inv_plabicData hG, hl]
  exact hc _ T.intervalStart_mem_root

end RootedTree

end PlabicData

end ClusterAlgebras
