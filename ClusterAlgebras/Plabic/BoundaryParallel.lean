/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.ArcCut
public import ClusterAlgebras.Plabic.BadFeatures

/-!
# Boundary-parallel arcs, standard triple diagrams and the straightening property

For a triple diagram `X` and its arc `S` from `s_i`, this file studies the cut `X|_{S,ζ}` of `X`
along `S` on a side `ζ`: moves of the cut lift to moves of `X`, returning paths of `S` are the
returning arcs of the cut, and when `S` is boundary-parallel along a minimal interval `I` the
darts on the side of `I` and the arcs of the cut are described explicitly. It defines the
straightening property and standard triple diagrams, by recursion on the number of arcs.

## Main definitions

* `StrandSide.opposite`: The side opposite to a given side.
* `intervalSide`: The side of an arc on which an interval of its source lies.
* `TripleData.HIsomorphic`: Isomorphism of triple data whose numbers of arcs are equal.
* `TripleDiagram.HasStraighteningProperty`: The straightening property of a triple diagram.
* `TripleData.IsStandard`, `TripleDiagram.IsStandard`: Standard triple diagrams.

## Main results

* `TripleData.IsSimpleArc.exists_moveEquivalent_hIsomorphic_arcCut`: Moves of the cut along a
  simple arc lift to moves of the diagram.
* `TripleData.IsSimpleArc.isMonogonStable_arcCut`: Cuts of a monogon-stable diagram along a simple
  arc are monogon-stable.
* `TripleData.IsSimpleArc.exists_isReturningPath_iff`: Returning paths of a simple arc are the
  returning arcs of the cut.
* `TripleData.IsBoundaryParallel.arcSideDarts_intervalSide`: The darts on the side of `I` of a
  boundary-parallel arc are the legs at the interior positions of `I` and their reverses.
* `TripleData.IsSimpleArc.exists_arc_arcCut_of_isMinimalInterval`: Every arc of the cut along a
  minimal interval joins a leg at an interior position of `I` to a dart of the side list.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

namespace StrandSide

/-- The side **opposite** to `ζ`. -/
def opposite : StrandSide → StrandSide
  | right => left
  | left => right

/-- The side opposite to `right` is `left`. -/
@[simp]
theorem opposite_right : right.opposite = left := rfl

/-- The side opposite to `left` is `right`. -/
@[simp]
theorem opposite_left : left.opposite = right := rfl

/-- Taking the opposite side is an involution. -/
@[simp]
theorem opposite_opposite (ζ : StrandSide) : ζ.opposite.opposite = ζ := by
  cases ζ <;> rfl

end StrandSide

/-- The **side of an interval** `I` of `i` for `π`: the arc from `s_i = ε(p)` to `ε(q)` has the
interior positions of `I` on its left if `I` runs clockwise from `p` to `q`, and on its right
otherwise. -/
def intervalSide {b : ℕ} (π : Fin b → Fin b) (i : Fin b) (I : Finset (Fin (2 * b))) :
    StrandSide :=
  if I = cyclicIcc (sourceIndex i) (targetIndex (π i)) then .left else .right

namespace TripleData

variable {H H' : Type*} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] {b b' : ℕ}

/-- Triple data `X` with `b` arcs and `X'` with `b'` arcs are **isomorphic** when `b = b'` and `X`,
read with `b'` arcs, is isomorphic to `X'`. This is isomorphism for triple data whose numbers of
arcs are equal but not syntactically so, such as two cuts. -/
def HIsomorphic (X : TripleData H b) (X' : TripleData H' b') : Prop :=
  ∃ h : b = b', (h ▸ X : TripleData H b').Isomorphic X'

/-- Isomorphic triple data with the same number of arcs are isomorphic in the sense of
`HIsomorphic`. -/
theorem Isomorphic.hIsomorphic {X : TripleData H b} {X' : TripleData H' b}
    (h : X.Isomorphic X') : X.HIsomorphic X' :=
  ⟨rfl, h⟩

/-- For the same number of arcs, `HIsomorphic` is `Isomorphic`. -/
theorem hIsomorphic_iff_isomorphic {X : TripleData H b} {X' : TripleData H' b} :
    X.HIsomorphic X' ↔ X.Isomorphic X' :=
  ⟨fun ⟨_, h⟩ => h, Isomorphic.hIsomorphic⟩

/-- `HIsomorphic` is symmetric. -/
theorem HIsomorphic.symm {X : TripleData H b} {X' : TripleData H' b'} (h : X.HIsomorphic X') :
    X'.HIsomorphic X := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, Isomorphic.symm _ h⟩

/-- `HIsomorphic` is transitive. -/
theorem HIsomorphic.trans {H'' : Type*} [Fintype H''] [DecidableEq H''] {b'' : ℕ}
    {X : TripleData H b} {X' : TripleData H' b'} {X'' : TripleData H'' b''}
    (h : X.HIsomorphic X') (h' : X'.HIsomorphic X'') : X.HIsomorphic X'' := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  exact ⟨rfl, Isomorphic.trans _ h h'⟩

/-- An isomorphism maps a monogon onto a monogon. -/
theorem Iso.hasMonogon {X : TripleData H b} {X' : TripleData H' b} (θ : X.Iso X')
    (h : X.HasMonogon) : X'.HasMonogon := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P.map θ.toEquiv, θ.isStrandPath_map hP.isStrandPath, ?_, ?_, ?_⟩
  · rw [θ.pathStart_map]
    exact θ.map_mem_internalVertices hP.pathStart_mem
  · rw [θ.pathStart_map, θ.pathEnd_map, hP.pathEnd_eq]
  · intro e₁ he₁ eₘ heₘ
    rw [List.head?_map, Option.mem_map] at he₁
    rw [List.getLast?_map, Option.mem_map] at heₘ
    obtain ⟨a, ha, rfl⟩ := he₁
    obtain ⟨c, hc, rfl⟩ := heₘ
    rw [← θ.map_inv, ← θ.map_rot_pow_three]
    exact θ.toEquiv.injective.ne (hP.inv_ne a ha c hc)

/-- Isomorphic triple data both have a monogon or both have none. -/
theorem HIsomorphic.hasMonogon_iff {X : TripleData H b} {X' : TripleData H' b'}
    (h : X.HIsomorphic X') : X.HasMonogon ↔ X'.HasMonogon := by
  obtain ⟨rfl, ⟨θ⟩⟩ := h
  exact ⟨θ.hasMonogon, θ.symm.hasMonogon⟩

end TripleData

namespace TripleDiagram

variable {b : ℕ}

/-- A triple diagram `X` has the **straightening property** if no triple diagram move-equivalent
to `X` has a parallel digon, and for every minimal interval `I` of `X`, of `i` say, some triple
diagram move-equivalent to `X` has its arc from `s_i` boundary-parallel along `I`. -/
@[cluster_algebras "def_straightening_property"]
def HasStraighteningProperty (X : TripleDiagram b) : Prop :=
  (∀ X' : TripleDiagram b, X.MoveEquivalent X' → ¬X'.data.HasParallelDigon) ∧
    ∀ i I, X.IsMinimalInterval i I →
      ∃ X' : TripleDiagram b, X.MoveEquivalent X' ∧ X'.data.IsBoundaryParallel i I

end TripleDiagram

namespace TripleData

/-- **Standard triple diagrams**, by recursion on the number `b` of arcs. A triple diagram with
one arc is standard if it has no triple point. A triple diagram `X` with `b ≥ 2` arcs is standard
if there are a minimal interval `I` of `X`, of `i` say, such that the arc `S` from `s_i` is
boundary-parallel along `I`, and, with `η` the side opposite to that of `I`, the cut `X|_{S,η}`
(which has `b - 1` arcs) is standard. -/
@[cluster_algebras "def_standard_triple_diagram"]
inductive IsStandard : {H : Type} → [Fintype H] → [DecidableEq H] → {b : ℕ} → TripleData H b →
    Prop
  /-- A triple diagram with one arc and no triple point is standard. -/
  | one {H : Type} [Fintype H] [DecidableEq H] (X : TripleData H 1) (hX : X.IsTripleDiagram)
      (h : X.internalVertices = ∅) : IsStandard X
  /-- A triple diagram with `b ≥ 2` arcs whose arc from `s_i` is boundary-parallel along a minimal
  interval `I` of `i`, and whose cut along it on the side opposite to `I` is standard, is
  standard. -/
  | cut {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} (X : TripleData H b)
      (hX : X.IsTripleDiagram) (hb : 2 ≤ b) (i : Fin b) (I : Finset (Fin (2 * b)))
      (hI : IsMinimalInterval X.strandPerm i I) (hS : X.IsBoundaryParallel i I)
      (h : IsStandard (X.arcCut i (intervalSide X.strandPerm i I).opposite)) : IsStandard X

end TripleData

namespace TripleDiagram

/-- A **standard triple diagram**: see `TripleData.IsStandard`. -/
@[cluster_algebras "def_standard_triple_diagram"]
def IsStandard {b : ℕ} (X : TripleDiagram b) : Prop := X.data.IsStandard

end TripleDiagram

/-! ### Arcs and side lists -/

namespace TripleData

section ArcFacts

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {i : Fin b}

/-- A strand path starting at the dart `a_j` of the source `s_j` whose last dart runs to an
endpoint is the arc from `s_j`. -/
theorem eq_arc_of_isStrandPath {P : List H} {j : Fin b} (hP : X.IsStrandPath P)
    (hhead : P.head? = some (X.endDart (sourceIndex j)))
    (hlast : ∀ e ∈ P.getLast?, X.RunsToEndpoint e) : P = X.arc j := by
  obtain ⟨n, hn⟩ : ∃ n, P.length = n + 1 :=
    ⟨P.length - 1, by have := List.length_pos_of_ne_nil hP.ne_nil; omega⟩
  have hstep := (X.isStrandPath_iff_getElem.1 hP).2.2
  have hdart : ∀ t (ht : t < P.length), P[t] = X.arcDart j t := by
    intro t ht
    induction t with
    | zero =>
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem ht] at hhead
      rw [arcDart_zero]
      exact Option.some_injective _ hhead
    | succ t ih =>
      rw [arcDart_succ, ← ih (by omega), (hstep t ht).strandMap_eq]
  have hlen : X.arcLength j = n + 1 := by
    rw [arcLength_eq_succ_iff]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [← hdart n (by omega)]
      apply hlast
      have h1 : P.length - 1 = n := by omega
      rw [List.getLast?_eq_getElem?, h1, List.getElem?_eq_getElem (by omega)]
      rfl
    · rw [← hdart k (by omega)]
      exact (hstep k (by omega)).1
  apply List.ext_getElem
  · rw [length_arc, hlen, hn]
  · intro t h₁ h₂
    rw [hdart t h₁, getElem_arc]

private theorem arcLength_pos' (hX : X.IsTripleDiagram) : 0 < X.arcLength i :=
  Nat.pos_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)

private theorem not_runsToEndpoint_arcDart' (hX : X.IsTripleDiagram) {k : ℕ}
    (hk : k + 1 < X.arcLength i) : ¬X.RunsToEndpoint (X.arcDart i k) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  exact (X.arcLength_eq_succ_iff.1 hm).2 k (by omega)

private theorem runsToEndpoint_arcDart_last' (hX : X.IsTripleDiagram) :
    X.RunsToEndpoint (X.arcDart i (X.arcLength i - 1)) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  rw [hm, Nat.succ_sub_one]
  exact (X.arcLength_eq_succ_iff.1 hm).1

/-- The vertex of a dart of the arc from `s_i` is an endpoint or a triple point the arc passes
through. -/
private theorem isBoundaryVertex_or_passesThrough_of_mem_arc {e : H} (he : e ∈ X.arc i) :
    X.IsBoundaryVertex (X.vertexOf e) ∨ X.PassesThrough (X.arc i).toFinset (X.vertexOf e) := by
  by_cases h : X.IsBoundaryVertex (X.vertexOf e)
  · exact Or.inl h
  · exact Or.inr ⟨X.vertexOf_mem_internalVertices.2 h, e, List.mem_toFinset.2 he, rfl⟩

/-- The vertex of the reverse of a dart of the arc from `s_i` is an endpoint or a triple point
the arc passes through. -/
private theorem isBoundaryVertex_or_passesThrough_of_inv_mem_arc (hX : X.IsTripleDiagram)
    {e : H} (he : e ∈ X.arc i) :
    X.IsBoundaryVertex (X.vertexOf (X.inv e)) ∨
      X.PassesThrough (X.arc i).toFinset (X.vertexOf (X.inv e)) := by
  obtain ⟨t, ht, rfl⟩ := mem_arc_toFinset.1 (List.mem_toFinset.2 he)
  by_cases ht' : t + 1 < X.arcLength i
  · have hmem : X.arcDart i (t + 1) ∈ X.arc i :=
      List.mem_toFinset.1 (mem_arc_toFinset.2 ⟨t + 1, ht', rfl⟩)
    have hv : X.vertexOf (X.arcDart i (t + 1)) = X.vertexOf (X.inv (X.arcDart i t)) := by
      rw [arcDart_succ_eq hX ht', X.vertexOf_rot_pow_apply]
    rw [← hv]
    exact isBoundaryVertex_or_passesThrough_of_mem_arc hmem
  · left
    have := runsToEndpoint_arcDart_last' (i := i) hX
    rwa [show X.arcLength i - 1 = t by omega] at this

/-- The darts of the arc from `s_i` other than the last. -/
private theorem mem_dropLast_arc {e : H} :
    e ∈ (X.arc i).dropLast ↔ ∃ k, k + 1 < X.arcLength i ∧ e = X.arcDart i k := by
  rw [List.mem_iff_getElem]
  simp only [List.length_dropLast, length_arc, List.getElem_dropLast, getElem_arc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by omega, rfl⟩

/-- The `ζ` list of the arc from `s_i` consists of the `ζ` darts at its triple points. -/
theorem mem_sideList_arc {ζ : StrandSide} {d : H} :
    d ∈ X.sideList ζ (X.arc i) ↔
      ∃ k, k + 1 < X.arcLength i ∧ d ∈ X.sideDarts ζ (X.arcDart i k) := by
  cases ζ <;>
  · simp only [sideList, List.mem_flatMap, List.mem_reverse, mem_dropLast_arc]
    constructor
    · rintro ⟨e, ⟨k, hk, rfl⟩, h⟩
      exact ⟨k, hk, h⟩
    · rintro ⟨k, hk, h⟩
      exact ⟨_, ⟨k, hk, rfl⟩, h⟩

/-- The `ζ` list of the arc from `s_i` is part of its `ζ` cut list. -/
theorem mem_arcCutList_of_mem_sideList {ζ : StrandSide} {d : H}
    (hd : d ∈ X.sideList ζ (X.arc i)) : d ∈ X.arcCutList i ζ := by
  obtain ⟨k, hk, h⟩ := mem_sideList_arc.1 hd
  cases ζ
  · refine mem_rightCutList.2 (Or.inr ⟨k, hk, ?_⟩)
    simpa [sideDarts] using h
  · refine mem_leftCutList.2 (Or.inr ⟨k, hk, ?_⟩)
    simpa [sideDarts] using h

/-- A dart of the `ζ` cut list is a leg or a dart of the `ζ` list. -/
theorem exists_endDart_or_mem_sideList_of_mem_arcCutList {ζ : StrandSide} {d : H}
    (hd : d ∈ X.arcCutList i ζ) : (∃ r, d = X.endDart r) ∨ d ∈ X.sideList ζ (X.arc i) := by
  cases ζ
  · rcases mem_rightCutList.1 hd with ⟨r, -, rfl⟩ | ⟨k, hk, h⟩
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr (mem_sideList_arc.2 ⟨k, hk, by simpa [sideDarts] using h⟩)
  · rcases mem_leftCutList.1 hd with ⟨r, -, rfl⟩ | ⟨k, hk, h⟩
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr (mem_sideList_arc.2 ⟨k, hk, by simpa [sideDarts] using h⟩)

/-- A dart of a cut list lies at an endpoint or at a triple point of the arc. -/
private theorem isBoundaryVertex_or_passesThrough_of_mem_arcCutList (hX : X.IsTripleDiagram)
    {ζ : StrandSide} {d : H} (hd : d ∈ X.arcCutList i ζ) :
    X.IsBoundaryVertex (X.vertexOf d) ∨ X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
  rcases exists_endDart_or_mem_sideList_of_mem_arcCutList hd with ⟨r, rfl⟩ | h
  · exact Or.inl (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
  · obtain ⟨k, hk, h⟩ := mem_sideList_arc.1 h
    right
    have hmem : X.arcDart i (k + 1) ∈ X.arc i :=
      List.mem_toFinset.1 (mem_arc_toFinset.2 ⟨k + 1, hk, rfl⟩)
    have hv : X.vertexOf d = X.vertexOf (X.arcDart i (k + 1)) := by
      rw [arcDart_succ_eq hX hk, X.vertexOf_rot_pow_apply]
      cases ζ <;> simp only [sideDarts, List.mem_cons, List.not_mem_nil, or_false] at h <;>
        rcases h with rfl | rfl <;> simp [X.vertexOf_rot_pow_apply, X.vertexOf_rot]
    rw [hv]
    exact ⟨X.vertexOf_mem_internalVertices.2 (by
      rw [arcDart_succ_eq hX hk, X.vertexOf_rot_pow_apply]
      exact not_runsToEndpoint_arcDart' hX hk), _, List.mem_toFinset.2 hmem, rfl⟩

/-- A dart of `H_ζ(S)` outside the `ζ` cut list lies at a triple point avoided by `S`. -/
theorem IsSimpleArc.avoided_of_mem_arcSideDarts (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} {d : H} (hd : d ∈ X.arcSideDarts i ζ) (hL : d ∉ X.arcCutList i ζ) :
    X.vertexOf d ∈ X.internalVertices ∧ ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) := by
  cases ζ
  · rcases hS.mem_rightCutList_or_of_mem_rightSide hX hd with h | h
    · exact absurd h hL
    · exact h
  · rcases hS.mem_leftCutList_or_of_mem_leftSide hX hd with h | h
    · exact absurd h hL
    · exact h

/-- A dart at a triple point avoided by `S` is not in a cut list. -/
theorem notMem_arcCutList_of_avoided (hX : X.IsTripleDiagram) {ζ : StrandSide} {d : H}
    (hint : X.vertexOf d ∈ X.internalVertices)
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) : d ∉ X.arcCutList i ζ := by
  intro hL
  rcases isBoundaryVertex_or_passesThrough_of_mem_arcCutList hX hL with hb | hp
  · exact (X.mem_internalVertices.1 hint).2 hb
  · exact hpass hp

/-- At a triple point avoided by `S`, a side containing one dart contains all of them. -/
theorem IsSimpleArc.mem_arcSideDarts_of_mem_vertexOf (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {ζ : StrandSide} {x e : H} (hx : X.vertexOf x ∈ X.internalVertices)
    (hpass : ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf x))
    (hxK : x ∈ X.arcSideDarts i ζ) (he : e ∈ X.vertexOf x) : e ∈ X.arcSideDarts i ζ := by
  have hxx := X.self_mem_vertexOf x
  have hdisj := disjoint_left.1 (disjoint_rightSide_leftSide (X := X) (i := i))
  rcases hS.forall_mem_rightSide_or_forall_mem_leftSide hX hx hpass with h | h <;> cases ζ
  · exact h e he
  · exact absurd (h x hxx) (fun h' => hdisj h' hxK)
  · exact absurd hxK (fun h' => hdisj h' (h x hxx))
  · exact h e he

end ArcFacts

end TripleData

/-! ### Moves of a cut lift to moves of the diagram -/

namespace TripleData

section Lift

variable {H : Type} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {i : Fin b}

omit [Fintype H] in
/-- A digon of a cut along `(K, L)` is a digon of the cut along `(K', L')` for `K' = K`,
`L' = L`. -/
private theorem isDigon_cut_congr {Y : TripleData H b} {K K' : Finset H} {L L' : List H} {s : ℕ}
    (hK : K' = K) (hL : L' = L) {d : H} (hd : d ∈ K) (hd' : d ∈ K')
    (h : (Y.cut K L s).IsDigon ((Y.cut K L s).faceOf (.inl ⟨d, hd⟩))) :
    (Y.cut K' L' s).IsDigon ((Y.cut K' L' s).faceOf (.inl ⟨d, hd'⟩)) := by
  subst hK hL
  exact h

omit [Fintype H] in
/-- The cut along `(K', L')`, for `K' = K` and `L' = L`, is isomorphic to whatever the cut along
`(K, L)` is isomorphic to. -/
private theorem hIsomorphic_cut_congr {Y : TripleData H b} {K K' : Finset H} {L L' : List H}
    {s : ℕ} (hK : K' = K) (hL : L' = L) {H'' : Type} [Fintype H''] [DecidableEq H'']
    {Z : TripleData H'' (L.length / 2)} (h : (Y.cut K L s).Isomorphic Z) :
    (Y.cut K' L' s).HIsomorphic Z := by
  subst hK hL
  exact h.hIsomorphic

/-- The invariant of the induction in `IsSimpleArc.exists_moveEquivalent_hIsomorphic_arcCut`:
`X'` is reached from `X` by swivel moves, has the data of `X` except for the rotation, which
agrees with `σ` off `H_ζ(S)` minus the cut list, has the simple arc `S` with the same side and cut
list, and its cut along `S` is `W`. -/
private def LiftInvariant (X : TripleData H b) (i : Fin b) (ζ : StrandSide)
    (W : TripleData (CutDart (X.arcSideDarts i ζ) (X.arcCutList i ζ).length)
      ((X.arcCutList i ζ).length / 2)) (X' : TripleData H b) : Prop :=
  Relation.ReflTransGen SwivelStep X X' ∧ X'.inv = X.inv ∧ X'.bdry = X.bdry ∧
    X'.endDart = X.endDart ∧ X'.isOut = X.isOut ∧
    (∀ d, (d ∉ X.arcSideDarts i ζ ∨ d ∈ X.arcCutList i ζ) → X'.rot d = X.rot d) ∧
    X'.IsSimpleArc i ∧ X'.arc i = X.arc i ∧ X'.arcSideDarts i ζ = X.arcSideDarts i ζ ∧
    X'.arcCutList i ζ = X.arcCutList i ζ ∧
    W = X'.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift

/-- One swivel move of the cut lifts. -/
private theorem LiftInvariant.step (hX : X.IsTripleDiagram) {ζ : StrandSide}
    {W W' : TripleData (CutDart (X.arcSideDarts i ζ) (X.arcCutList i ζ).length)
      ((X.arcCutList i ζ).length / 2)} {X₁ : TripleData H b} (h : X.LiftInvariant i ζ W X₁)
    (hst : W.SwivelStep W') : ∃ X₂, X.LiftInvariant i ζ W' X₂ := by
  obtain ⟨hch, hinv, hbdry, hend, hout, hrot, hS₁, harc, hK, hL, rfl⟩ := h
  set K := X.arcSideDarts i ζ with hKdef
  set L := X.arcCutList i ζ with hLdef
  have hX₁ : X₁.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hch hX
  have hc : X₁.IsCutData K L := by
    have := hS₁.isCutData_arcCutList hX₁ ζ
    rwa [hK, hL] at this
  obtain ⟨e, hD, rfl⟩ := hst
  rcases e with e | p
  swap
  · exfalso
    have hdisj := ((X₁.cut K L ζ.cutShift).mem_internalFaces.1 hD.1).2
    exact disjoint_left.1 hdisj ((X₁.cut K L ζ.cutShift).self_mem_faceOf _)
      (IsCutData.mem_cut_bdry.2 rfl)
  obtain ⟨h₂, -, he1, he2, -, hDX⟩ := hc.isDigon_of_isDigon_cut hX₁.toIsPreTripleDiagram hD
  have hcut := hc.swivelMove_cut hX₁.toIsPreTripleDiagram hD
  have hd₁ : e.1 ∈ X₁.arcSideDarts i ζ := hK ▸ e.2
  have hD' := isDigon_cut_congr (Y := X₁) (s := ζ.cutShift) hK hL e.2 hd₁ hD
  obtain ⟨-, -, hS₂, harc₂, hK₂, hL₂, -⟩ := hS₁.arcCut_swivelMove hX₁ ζ hd₁ hD'
  have hUK : ∀ z ∈ X₁.vertexOf e.1 ∪ X₁.vertexOf (X₁.facePerm e.1), z ∈ K ∧ z ∉ L := by
    intro z hz
    rcases mem_union.1 hz with hz | hz
    · exact hc.mem_of_mem_vertexOf _ e.2 he1 z hz
    · exact hc.mem_of_mem_vertexOf _ h₂ he2 z hz
  refine ⟨X₁.swivelMove e.1, hch.tail ⟨e.1, hDX, rfl⟩, hinv, hbdry, hend, hout,
    fun d hd => ?_, hS₂, harc₂.trans harc, hK₂.trans hK, hL₂.trans hL, hcut.symm⟩
  have hdU : d ∉ X₁.vertexOf e.1 ∪ X₁.vertexOf (X₁.facePerm e.1) := by
    intro hdU
    obtain ⟨h1, h2⟩ := hUK d hdU
    rcases hd with hd | hd
    · exact hd h1
    · exact h2 hd
  rw [swivelMove_rot, swivelRot_apply_of_notMem hdU]
  exact hrot d hd

/-- **Moves of the cut lift**. Let `S` be the simple arc from `s_i` of a triple diagram
`X = (H, d ↦ d̄, σ, B, ε, o)`, `ζ` a side with `N_ζ ≥ 2`, and `Y ∼ X|_{S,ζ}`. Then there is a
triple diagram `X' = (H, d ↦ d̄, σ', B, ε, o) ∼ X` such that `σ'(d) = σ(d)` for every dart `d`
that does not lie at a triple point of `X` avoided by `S`, the arc from `s_i` in `X'` is the
simple arc `S` (the same darts), the set `H_ζ(S)` and the `ζ` cut list of `X'` are those of `X`,
and `X'|_{S,ζ}` is isomorphic to `Y`. -/
@[cluster_algebras "lem_arc_cut_lift"]
theorem IsSimpleArc.exists_moveEquivalent_hIsomorphic_arcCut (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) (ζ : StrandSide) (hN : 2 ≤ (X.arcCutList i ζ).length)
    {Y : TripleDiagram ((X.arcCutList i ζ).length / 2)}
    (hY : TripleDiagram.MoveEquivalent ⟨_, X.arcCut i ζ, hS.isTripleDiagram_arcCut hX ζ hN⟩ Y) :
    ∃ (X' : TripleData H b) (hX' : X'.IsTripleDiagram),
      TripleDiagram.MoveEquivalent ⟨H, X, hX⟩ ⟨H, X', hX'⟩ ∧
      X'.inv = X.inv ∧ X'.bdry = X.bdry ∧ X'.endDart = X.endDart ∧ X'.isOut = X.isOut ∧
      (∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
          ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d) ∧
      X'.IsSimpleArc i ∧ X'.arc i = X.arc i ∧ X'.arcSideDarts i ζ = X.arcSideDarts i ζ ∧
      X'.arcCutList i ζ = X.arcCutList i ζ ∧ (X'.arcCut i ζ).HIsomorphic Y.data := by
  obtain ⟨W, hW, hWY⟩ := hY.exists_swivelSteps
  have key : ∀ W', Relation.ReflTransGen SwivelStep (X.arcCut i ζ) W' →
      ∃ X₁, X.LiftInvariant i ζ W' X₁ := by
    intro W' h
    induction h with
    | refl =>
      exact ⟨X, Relation.ReflTransGen.refl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hS, rfl, rfl,
        rfl, rfl⟩
    | tail _ hst ih =>
      obtain ⟨X₁, h₁⟩ := ih
      exact h₁.step hX hst
  obtain ⟨X', hch, hinv, hbdry, hend, hout, hrot, hS', harc, hK, hL, rfl⟩ := key W hW
  have hX' : X'.IsTripleDiagram := isTripleDiagram_of_reflTransGen_swivelStep hch hX
  refine ⟨X', hX', TripleDiagram.MoveEquivalent.of_reflTransGen_swivelStep (X := ⟨H, X, hX⟩)
    (X' := ⟨H, X', hX'⟩) hch (Isomorphic.refl _), hinv, hbdry, hend, hout, fun d hd => ?_, hS',
    harc, hK, hL, hIsomorphic_cut_congr hK hL hWY⟩
  apply hrot
  by_contra h
  rw [not_or, not_not] at h
  exact hd (hS.avoided_of_mem_arcSideDarts hX h.1 h.2)

/-- **Cuts of a monogon-stable diagram are monogon-stable**: if `X` is monogon-stable, `S` the
simple arc from `s_i` and `ζ` a side with `N_ζ ≥ 2`, then `X|_{S,ζ}` is monogon-stable. -/
@[cluster_algebras "lem_cut_monogon_stable"]
theorem IsSimpleArc.isMonogonStable_arcCut (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (hXs : TripleDiagram.IsMonogonStable ⟨H, X, hX⟩) (ζ : StrandSide)
    (hN : 2 ≤ (X.arcCutList i ζ).length) :
    TripleDiagram.IsMonogonStable ⟨_, X.arcCut i ζ, hS.isTripleDiagram_arcCut hX ζ hN⟩ := by
  intro Y hY hmono
  obtain ⟨X', hX', hXX', -, -, -, -, -, hS', -, -, -, hiso⟩ :=
    hS.exists_moveEquivalent_hIsomorphic_arcCut hX ζ hN hY
  obtain ⟨P, hP⟩ := hiso.hasMonogon_iff.2 hmono
  obtain ⟨Q, rfl, -⟩ := hS'.exists_isStrandPath_of_isStrandPath_arcCut hX' ζ hP.isStrandPath
  exact hXs _ hXX' ⟨_, hS'.isMonogon_of_isMonogon_arcCut hX' ζ hP⟩

end Lift

end TripleData

/-! ### Returning paths are the returning arcs of the cut -/

namespace TripleData

section Returning

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {i : Fin b}

omit [Fintype H] [DecidableEq H] in
/-- A list all of whose entries satisfy `p` is a list of elements of the subtype. -/
private theorem exists_eq_map_subtypeVal {p : H → Prop} :
    ∀ l : List H, (∀ x ∈ l, p x) → ∃ l' : List {x // p x}, l = l'.map Subtype.val
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨l', hl'⟩ := exists_eq_map_subtypeVal l fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact ⟨⟨x, h x List.mem_cons_self⟩ :: l', by rw [List.map_cons, ← hl']⟩

omit [Fintype H] [DecidableEq H] in
private theorem exists_getElem_of_mem_dropLast {l : List H} {x : H} (hx : x ∈ l.dropLast) :
    ∃ t, ∃ ht : t + 1 < l.length, x = l[t] := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx
  simp only [List.length_dropLast] at ht
  exact ⟨t, by omega, List.getElem_dropLast _⟩

omit [Fintype H] [DecidableEq H] in
private theorem getElem_mem_dropLast {l : List H} {t : ℕ} (ht : t + 1 < l.length) :
    l[t] ∈ l.dropLast :=
  List.mem_iff_getElem.2 ⟨t, by simp only [List.length_dropLast]; omega,
    List.getElem_dropLast _⟩

/-- The interior points of the arc from `s_i` are its triple points `v(ē_l)`. -/
private theorem mem_interiorPoints_arc {z : Finset H} :
    z ∈ X.interiorPoints (X.arc i) ↔
      ∃ k, k + 1 < X.arcLength i ∧ z = X.vertexOf (X.inv (X.arcDart i k)) := by
  simp only [interiorPoints, List.mem_map, mem_dropLast_arc]
  constructor
  · rintro ⟨e, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩

/-- A simple arc is a simple strand path. -/
theorem IsSimpleArc.isSimpleStrandPath (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) :
    X.IsSimpleStrandPath (X.arc i) where
  isStrandPath := X.isStrandPath_arc hX.toIsPreTripleDiagram
    (hX.toIsPreTripleDiagram.arcLength_ne_zero i)
  nodup := by
    rw [List.nodup_iff_injective_get]
    rintro ⟨a, ha⟩ ⟨c, hc⟩ h
    simp only [interiorPoints, List.length_map, List.length_dropLast, length_arc] at ha hc
    simp only [interiorPoints, List.get_eq_getElem, List.getElem_map, List.getElem_dropLast,
      getElem_arc] at h
    exact Fin.ext (hS a c (by omega) (by omega) h)
  pathStart_notMem := by
    rw [mem_interiorPoints_arc]
    rintro ⟨k, hk, h⟩
    have hm := arcLength_pos' (i := i) hX
    have h0 : X.pathStart (X.arc i) = X.vertexOf (X.arcDart i 0) := by
      apply pathStart_of_head?
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [length_arc]; omega),
        getElem_arc]
    rw [h0, arcDart_zero] at h
    apply not_runsToEndpoint_arcDart' hX hk
    change X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i k)))
    rw [← h]
    exact (X.mem_boundaryVertices.1 (hX.endpoint_mem _)).2
  pathEnd_notMem := by
    rw [mem_interiorPoints_arc]
    rintro ⟨k, hk, h⟩
    have hm := arcLength_pos' (i := i) hX
    have h0 : X.pathEnd (X.arc i) = X.vertexOf (X.inv (X.arcDart i (X.arcLength i - 1))) := by
      apply pathEnd_of_getLast?
      rw [List.getLast?_eq_getElem?, length_arc,
        List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc]
    rw [h0] at h
    apply not_runsToEndpoint_arcDart' hX hk
    change X.IsBoundaryVertex (X.vertexOf (X.inv (X.arcDart i k)))
    rw [← h]
    exact runsToEndpoint_arcDart_last' hX

/-- The first dart of a returning path of the arc from `s_i` on side `ζ` is a dart of the `ζ` list
of the arc. -/
theorem IsReturningPath.head?_mem_sideList_arc {ζ : StrandSide} {Q : List H} {a c : ℕ}
    (hR : X.IsReturningPath (X.arc i) ζ Q a c) : ∀ f ∈ Q.head?, f ∈ X.sideList ζ (X.arc i) := by
  intro f hf
  obtain ⟨e, he, f', hf', h⟩ := hR.head?_mem
  rw [Option.mem_def.1 hf, Option.mem_def, Option.some.injEq] at hf'
  subst hf'
  have ha := hR.lt_left
  rw [length_arc] at ha
  rw [List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc,
    Option.mem_def, Option.some.injEq] at he
  subst he
  exact mem_sideList_arc.2 ⟨a, ha, h⟩

/-- The reverse of the last dart of a returning path of the arc from `s_i` on side `ζ` is a dart of
the `ζ` list of the arc. -/
theorem IsReturningPath.inv_getLast?_mem_sideList_arc {ζ : StrandSide} {Q : List H} {a c : ℕ}
    (hR : X.IsReturningPath (X.arc i) ζ Q a c) :
    ∀ f ∈ Q.getLast?, X.inv f ∈ X.sideList ζ (X.arc i) := by
  intro f hf
  obtain ⟨e, he, f', hf', h⟩ := hR.getLast?_mem
  rw [Option.mem_def.1 hf, Option.mem_def, Option.some.injEq] at hf'
  subst hf'
  have hc := hR.lt_right
  rw [length_arc] at hc
  rw [List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc,
    Option.mem_def, Option.some.injEq] at he
  subst he
  exact mem_sideList_arc.2 ⟨c, hc, h⟩

/-- The interior points of a returning path of the arc from `s_i` are internal vertices through
which the arc does not pass. -/
theorem IsReturningPath.avoids_arc {ζ : StrandSide} {Q : List H} {a c : ℕ}
    (hR : X.IsReturningPath (X.arc i) ζ Q a c) (t : ℕ) (ht : t + 1 < Q.length) :
    X.vertexOf (X.inv Q[t]) ∈ X.internalVertices ∧
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf (X.inv Q[t])) := by
  have hz : X.vertexOf (X.inv Q[t]) ∈ X.interiorPoints Q :=
    List.mem_map.2 ⟨_, getElem_mem_dropLast ht, rfl⟩
  refine ⟨X.vertexOf_mem_internalVertices.2
    ((X.isStrandPath_iff_getElem.1 hR.isStrandPath).2.2 t ht).1, ?_⟩
  rintro ⟨-, e, he, hv⟩
  exact (hR.interiorPoints_ne _ hz e (List.mem_toFinset.1 he)).1 hv.symm

/-- Every dart of a returning path of a simple arc on side `ζ` lies in `H_ζ(S)`. -/
theorem IsSimpleArc.mem_arcSideDarts_of_isReturningPath (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {ζ : StrandSide} {Q : List H} {a c : ℕ}
    (hR : X.IsReturningPath (X.arc i) ζ Q a c) : ∀ f ∈ Q, f ∈ X.arcSideDarts i ζ := by
  have hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := hS.isCutData_arcCutList hX ζ
  have hstep := (X.isStrandPath_iff_getElem.1 hR.isStrandPath).2.2
  suffices h : ∀ t (ht : t < Q.length), Q[t] ∈ X.arcSideDarts i ζ by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hf
    exact h t ht
  intro t ht
  induction t with
  | zero =>
    refine hc.mem_of_mem_list _ (mem_arcCutList_of_mem_sideList (hR.head?_mem_sideList_arc _ ?_))
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem ht]
    rfl
  | succ t ih =>
    have hK := hc.inv_mem _ (ih (by omega))
    obtain ⟨hint, hpass⟩ := hR.avoids_arc t ht
    rw [(hstep t ht).2]
    exact hS.mem_arcSideDarts_of_mem_vertexOf hX hint hpass hK
      (RotationSystem.rot_pow_apply_mem_vertexOf _ 3 _)

/-- A list of darts of `H_ζ(S)` which is a strand path of `X` and whose interior reverses avoid the
cut list is a strand path of the cut `X|_{S,ζ}`. -/
theorem IsSimpleArc.isStrandPath_arcCut_map_inl (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} {Q' : List {d // d ∈ X.arcSideDarts i ζ}}
    (hP : X.IsStrandPath (Q'.map Subtype.val))
    (hnotL : ∀ t (ht : t + 1 < Q'.length), X.inv Q'[t].1 ∉ X.arcCutList i ζ) :
    (X.arcCut i ζ).IsStrandPath (Q'.map Sum.inl) := by
  have hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := hS.isCutData_arcCutList hX ζ
  have hYc : X.arcCut i ζ = X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift := rfl
  have hstep := (X.isStrandPath_iff_getElem.1 hP).2.2
  rw [isStrandPath_iff_getElem]
  refine ⟨fun h => hP.ne_nil (List.map_eq_nil_iff.2 (List.map_eq_nil_iff.1 h)), fun t ht => ?_,
    fun t ht => ?_⟩
  · simp only [List.getElem_map]
    refine ⟨fun h => ?_, ?_⟩
    · rw [hYc, IsCutData.mem_cut_bdry] at h
      exact Bool.false_ne_true h
    · exact hP.isOut_eq_true (Q'[t]'(by simpa using ht)).1
        (List.mem_map.2 ⟨_, List.getElem_mem _, rfl⟩)
  · simp only [List.length_map] at ht
    simp only [List.getElem_map]
    have hL := hnotL t ht
    have hs := hstep t (by simpa using ht)
    simp only [List.getElem_map] at hs
    obtain ⟨hm, -, he⟩ := hc.cut_rot_pow_inl_of_notMem (s := ζ.cutShift)
      ⟨X.inv Q'[t].1, hc.inv_mem _ Q'[t].2⟩ hL 3
    refine ⟨?_, ?_⟩
    · change ¬(X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf
        ((X.arcCut i ζ).inv (.inl Q'[t])))
      rw [hYc, hc.cut_inv_inl hX.inv_involutive]
      exact hc.cut_not_isBoundaryVertex_vertexOf_inl hL
    · rw [hYc, hc.cut_inv_inl hX.inv_involutive, he]
      congr 1
      exact Subtype.ext hs.2

/-- A dart `q` of `H_ζ(S)` whose reverse is a dart of the `ζ` list of `S` ends at a boundary vertex
of the cut `X|_{S,ζ}`. -/
theorem IsSimpleArc.isBoundaryVertex_arcCut_of_inv_mem_sideList (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {ζ : StrandSide} {q : {d // d ∈ X.arcSideDarts i ζ}}
    (hq : X.inv q.1 ∈ X.sideList ζ (X.arc i)) :
    (X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf ((X.arcCut i ζ).inv (.inl q))) := by
  have hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := hS.isCutData_arcCutList hX ζ
  have hYc : X.arcCut i ζ = X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift := rfl
  obtain ⟨k', hk', hkq'⟩ := List.mem_iff_getElem.1 (mem_arcCutList_of_mem_sideList hq)
  rw [hYc, hc.cut_inv_inl hX.inv_involutive]
  apply hc.cut_isBoundaryVertex_vertexOf_of_mem_cutTriple (k := ⟨k', hk'⟩)
  rw [cutTriple, hc.cutListDart_eq]
  exact mem_insert.2 (Or.inl (congrArg Sum.inl (Subtype.ext hkq'.symm)))

/-- A returning path of a simple arc `S` on side `ζ` is an arc of the cut `X|_{S,ζ}`. -/
theorem IsSimpleArc.exists_arc_arcCut_of_isReturningPath (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {ζ : StrandSide} (hN : 2 ≤ (X.arcCutList i ζ).length) {Q : List H}
    {a c : ℕ} (hR : X.IsReturningPath (X.arc i) ζ Q a c) :
    ∃ (Q' : List {d // d ∈ X.arcSideDarts i ζ}) (j : Fin ((X.arcCutList i ζ).length / 2)),
      Q = Q'.map Subtype.val ∧ Q'.map Sum.inl = (X.arcCut i ζ).arc j := by
  have hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := hS.isCutData_arcCutList hX ζ
  have hYp := (hS.isTripleDiagram_arcCut hX ζ hN).toIsPreTripleDiagram
  have hYc : X.arcCut i ζ = X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift := rfl
  have hP := hR.isStrandPath
  obtain ⟨Q', rfl⟩ := exists_eq_map_subtypeVal (p := (· ∈ X.arcSideDarts i ζ)) Q
    (hS.mem_arcSideDarts_of_isReturningPath hX hR)
  have hYP := hS.isStrandPath_arcCut_map_inl hX hP fun t ht => by
    have := hR.avoids_arc t (by simpa using ht)
    simp only [List.getElem_map] at this
    exact notMem_arcCutList_of_avoided hX this.1 this.2
  obtain ⟨q₁, hq₁⟩ : ∃ q₁, Q'.head? = some q₁ := by
    cases Q' with
    | nil => exact absurd rfl hP.ne_nil
    | cons q Q' => exact ⟨q, rfl⟩
  have hq₁L : q₁.1 ∈ X.arcCutList i ζ := mem_arcCutList_of_mem_sideList
    (hR.head?_mem_sideList_arc q₁.1 (by rw [List.head?_map, hq₁]; rfl))
  obtain ⟨k, hk, hkq⟩ := List.mem_iff_getElem.1 hq₁L
  obtain ⟨r, hr⟩ := cutEndIndex_surjective (H := H) (s := ζ.cutShift)
    (even_length_arcCutList (X := X) (i := i) ζ) ⟨k, hk⟩
  have hend : (X.arcCut i ζ).endDart r = .inl q₁ := by
    rw [hYc, cut_endDart, hr, hc.cutListDart_eq]
    exact congrArg Sum.inl (Subtype.ext hkq)
  obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := exists_sourceIndex_or_targetIndex r
  swap
  · exfalso
    have h1 := hYp.isOut_target j
    rw [hend] at h1
    have h2 := hP.isOut_eq_true q₁.1 (List.mem_map.2 ⟨q₁, List.mem_of_head? hq₁, rfl⟩)
    change X.isOut q₁.1 = false at h1
    rw [h1] at h2
    exact Bool.false_ne_true h2
  refine ⟨Q', j, rfl, eq_arc_of_isStrandPath hYP (by rw [List.head?_map, hq₁, hend]; rfl) ?_⟩
  intro e he
  rw [List.getLast?_map, Option.mem_map] at he
  obtain ⟨q, hq, rfl⟩ := he
  exact hS.isBoundaryVertex_arcCut_of_inv_mem_sideList hX
    (hR.inv_getLast?_mem_sideList_arc q.1 (by rw [List.getLast?_map, hq]; rfl))

/-- A vertex of `X` which is internal and through which the arc from `s_i` does not pass is
neither the vertex of a dart of the arc nor of its reverse. -/
private theorem ne_vertexOf_of_not_passesThrough_arc (hX : X.IsTripleDiagram) {z : Finset H}
    (hz : z ∈ X.internalVertices) (hpass : ¬X.PassesThrough (X.arc i).toFinset z) {e : H}
    (he : e ∈ X.arc i) : z ≠ X.vertexOf e ∧ z ≠ X.vertexOf (X.inv e) := by
  have hb : ¬X.IsBoundaryVertex z := (X.mem_internalVertices.1 hz).2
  constructor
  · rintro rfl
    exact (isBoundaryVertex_or_passesThrough_of_mem_arc he).elim hb hpass
  · rintro rfl
    exact (isBoundaryVertex_or_passesThrough_of_inv_mem_arc hX he).elim hb hpass

private theorem exists_getElem?_arc_of_mem_sideList {ζ : StrandSide} {f : H}
    (hf : f ∈ X.sideList ζ (X.arc i)) :
    ∃ a, a + 1 < (X.arc i).length ∧ ∃ e ∈ (X.arc i)[a]?, f ∈ X.sideDarts ζ e := by
  obtain ⟨k, hk, h⟩ := mem_sideList_arc.1 hf
  refine ⟨k, by rw [length_arc]; exact hk, X.arcDart i k, ?_, h⟩
  rw [List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc]
  rfl

/-- An arc of the cut `X|_{S,ζ}` whose first dart and the reverse of whose last dart are darts of
the `ζ` list of `S` is a returning path of `S` on side `ζ`. -/
theorem IsSimpleArc.exists_isReturningPath_of_arc_arcCut (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {ζ : StrandSide} (hN : 2 ≤ (X.arcCutList i ζ).length)
    {Q' : List {d // d ∈ X.arcSideDarts i ζ}} {j : Fin ((X.arcCutList i ζ).length / 2)}
    (hQ' : Q'.map Sum.inl = (X.arcCut i ζ).arc j)
    (hf₁ : ∀ f ∈ (Q'.map Subtype.val).head?, f ∈ X.sideList ζ (X.arc i))
    (hfₙ : ∀ f ∈ (Q'.map Subtype.val).getLast?, X.inv f ∈ X.sideList ζ (X.arc i)) :
    ∃ a c, X.IsReturningPath (X.arc i) ζ (Q'.map Subtype.val) a c := by
  have hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := hS.isCutData_arcCutList hX ζ
  have hYp := (hS.isTripleDiagram_arcCut hX ζ hN).toIsPreTripleDiagram
  have hYc : X.arcCut i ζ = X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift := rfl
  have hYP : (X.arcCut i ζ).IsStrandPath (Q'.map Sum.inl) := by
    rw [hQ']
    exact (X.arcCut i ζ).isStrandPath_arc hYp (hYp.arcLength_ne_zero j)
  obtain ⟨Q'', hQ'', hP⟩ := hS.exists_isStrandPath_of_isStrandPath_arcCut hX ζ hYP
  rw [(List.map_injective_iff.2 Sum.inl_injective) hQ''.symm] at hP
  have hne : Q'.map Subtype.val ≠ [] := hP.ne_nil
  obtain ⟨f₁, hhead⟩ : ∃ f, (Q'.map Subtype.val).head? = some f :=
    Option.isSome_iff_exists.1 (List.isSome_head?.2 hne)
  obtain ⟨fₙ, hlast⟩ : ∃ f, (Q'.map Subtype.val).getLast? = some f :=
    Option.isSome_iff_exists.1 (List.getLast?_isSome.2 hne)
  obtain ⟨a, ha, e, he, hfe⟩ := exists_getElem?_arc_of_mem_sideList (hf₁ f₁ hhead)
  obtain ⟨c, hc', e', he', hfe'⟩ := exists_getElem?_arc_of_mem_sideList (hfₙ fₙ hlast)
  refine ⟨a, c, hS.isSimpleStrandPath hX, hP, ha, hc', ⟨e, he, f₁, hhead, hfe⟩,
    ⟨e', he', fₙ, hlast, hfe'⟩, ?_⟩
  intro z hz
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hz
  obtain ⟨t, ht, rfl⟩ := exists_getElem_of_mem_dropLast hf
  simp only [List.length_map] at ht
  have hs := ((X.arcCut i ζ).isStrandPath_iff_getElem.1 hYP).2.2 t (by simpa using ht)
  simp only [List.getElem_map] at hs ⊢
  have hb := hs.1
  change ¬(X.arcCut i ζ).IsBoundaryVertex ((X.arcCut i ζ).vertexOf
    ((X.arcCut i ζ).inv (.inl Q'[t]))) at hb
  rw [hYc, hc.cut_inv_inl hX.inv_involutive, hc.cut_not_isBoundaryVertex_iff] at hb
  obtain ⟨d, hdL, hd⟩ := hb
  have hdL' : X.inv Q'[t].1 ∉ X.arcCutList i ζ := by
    rwa [show X.inv Q'[t].1 = d.1 from congrArg Subtype.val (Sum.inl_injective hd)]
  obtain ⟨hint, hpass⟩ := hS.avoided_of_mem_arcSideDarts hX (hc.inv_mem _ Q'[t].2) hdL'
  exact fun e he => ne_vertexOf_of_not_passesThrough_arc hX hint hpass he

/-- **Returning paths are the returning arcs of the cut**. Let `S` be the simple arc from `s_i` of
a triple diagram `X`, `ζ` a side with `N_ζ ≥ 2`, and `Q = (f₁, …, f_n)` a sequence of darts. Then
`Q` is a returning path of `S` on side `ζ` if and only if `Q` is an arc of `X|_{S,ζ}` (whose darts
are darts `Sum.inl d`, `d ∈ H_ζ(S)`) whose first dart and the reverse of whose last dart are darts
of the `ζ` list of `S`. -/
@[cluster_algebras "lem_returning_cut_arc"]
theorem IsSimpleArc.exists_isReturningPath_iff (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) (hN : 2 ≤ (X.arcCutList i ζ).length) (Q : List H) :
    (∃ a c, X.IsReturningPath (X.arc i) ζ Q a c) ↔
      (∃ (Q' : List {d // d ∈ X.arcSideDarts i ζ}) (j : Fin ((X.arcCutList i ζ).length / 2)),
        Q = Q'.map Subtype.val ∧ Q'.map Sum.inl = (X.arcCut i ζ).arc j) ∧
      (∀ f ∈ Q.head?, f ∈ X.sideList ζ (X.arc i)) ∧
      ∀ f ∈ Q.getLast?, X.inv f ∈ X.sideList ζ (X.arc i) := by
  constructor
  · rintro ⟨a, c, hR⟩
    exact ⟨hS.exists_arc_arcCut_of_isReturningPath hX hN hR, hR.head?_mem_sideList_arc,
      hR.inv_getLast?_mem_sideList_arc⟩
  · rintro ⟨⟨Q', j, rfl, hQ'⟩, hf₁, hfₙ⟩
    exact hS.exists_isReturningPath_of_arc_arcCut hX hN hQ' hf₁ hfₙ

end Returning

end TripleData

/-! ### Clockwise distances and interiors of cyclic intervals -/

section CyclicDistance

variable {n : ℕ}

private theorem fin_val_sub (a c : Fin n) :
    ((a - c : Fin n) : ℕ) = if (c : ℕ) ≤ a then (a : ℕ) - c else n + (a : ℕ) - c := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.2 h
  · exact Fin.coe_sub_iff_lt.2 (not_le.1 h)

private theorem val_finRotate_eq (j : Fin n) : (finRotate n j : ℕ) = ((j : ℕ) + 1) % n := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · subst h
      simp
    · have : (j : ℕ) < n := Fin.val_lt_last h
      rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

private theorem val_finRotate_pow (q : Fin n) (s : ℕ) :
    ((finRotate n ^ s) q : ℕ) = ((q : ℕ) + s) % n := by
  induction s with
  | zero => simp [Nat.mod_eq_of_lt q.isLt]
  | succ s ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, val_finRotate_eq, ih, Nat.mod_add_mod, add_assoc]

private theorem val_finRotate_pow_sub (q : Fin n) {s : ℕ} (hs : s < n) :
    (((finRotate n ^ s) q - q : Fin n) : ℕ) = s := by
  rw [fin_val_sub, val_finRotate_pow]
  have := q.isLt
  by_cases h : (q : ℕ) + s < n
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

private theorem finRotate_pow_val_sub (r q : Fin n) :
    (finRotate n ^ ((r - q : Fin n) : ℕ)) q = r := by
  apply Fin.ext
  rw [val_finRotate_pow, fin_val_sub]
  have := q.isLt
  have := r.isLt
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem val_sub_eq_zero_iff {r q : Fin n} : ((r - q : Fin n) : ℕ) = 0 ↔ r = q := by
  constructor
  · intro h
    rw [← finRotate_pow_val_sub r q, h, pow_zero, Equiv.Perm.one_apply]
  · rintro rfl
    rw [fin_val_sub]
    simp

private theorem finRotate_pow_injective (q : Fin n) {s t : ℕ} (hs : s < n) (ht : t < n)
    (h : (finRotate n ^ s) q = (finRotate n ^ t) q) : s = t := by
  simpa only [val_finRotate_pow_sub q hs, val_finRotate_pow_sub q ht] using
    congrArg (fun r : Fin n => ((r - q : Fin n) : ℕ)) h

/-- The positions of a cyclic interval other than its ends are the `t + 1`-st clockwise successors
of its first end, `t + 1 < c - a`. -/
theorem mem_cyclicIcc_sdiff_iff {a c r : Fin n} :
    r ∈ cyclicIcc a c \ {a, c} ↔
      ∃ t, t + 1 < ((c - a : Fin n) : ℕ) ∧ r = (finRotate n ^ (t + 1)) a := by
  rw [mem_sdiff, mem_cyclicIcc, mem_insert, mem_singleton, Fin.le_def]
  constructor
  · rintro ⟨hle, hne⟩
    have h0 : ((r - a : Fin n) : ℕ) ≠ 0 := fun h => hne (Or.inl (val_sub_eq_zero_iff.1 h))
    have hc : ((r - a : Fin n) : ℕ) ≠ ((c - a : Fin n) : ℕ) := fun h => hne (Or.inr (by
      rw [← finRotate_pow_val_sub r a, h, finRotate_pow_val_sub]))
    refine ⟨((r - a : Fin n) : ℕ) - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0), finRotate_pow_val_sub]
  · rintro ⟨t, ht, rfl⟩
    have hlt : t + 1 < n := ht.trans (c - a).isLt
    rw [val_finRotate_pow_sub a hlt]
    refine ⟨ht.le, ?_⟩
    have := val_finRotate_pow_sub a hlt
    rintro (h | h)
    · rw [h, val_sub_eq_zero_iff.2 rfl] at this
      omega
    · rw [h] at this
      omega

end CyclicDistance

/-! ### The cut list of a simple arc, entry by entry -/

/-- Entries of a list built from pairs. -/
private theorem getElem?_flatMap_pair {α : Type*} (f g : ℕ → α) (n : ℕ) :
    ((List.range n).flatMap fun k => [f k, g k]).length = 2 * n ∧
    ∀ j < 2 * n, ((List.range n).flatMap fun k => [f k, g k])[j]? =
      some (if j % 2 = 0 then f (j / 2) else g (j / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hl, hg⟩ := ih
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    refine ⟨by simp only [List.length_append, hl, List.length_cons, List.length_nil]; ring,
      fun j hj => ?_⟩
    by_cases hj' : j < 2 * n
    · rw [List.getElem?_append_left (by rw [hl]; exact hj'), hg j hj']
    · rw [List.getElem?_append_right (by rw [hl]; omega), hl]
      obtain h | h : j = 2 * n ∨ j = 2 * n + 1 := by omega
      · subst h
        have h1 : 2 * n % 2 = 0 := by omega
        have h2 : 2 * n / 2 = n := by omega
        simp [h1, h2]
      · subst h
        have h1 : (2 * n + 1) % 2 = 1 := by omega
        have h2 : (2 * n + 1) / 2 = n := by omega
        simp [h1, h2]

/-- Entries of a list built from pairs, in reverse order. -/
private theorem getElem?_flatMap_pair_reverse {α : Type*} (f g : ℕ → α) (n : ℕ) :
    ((List.range n).reverse.flatMap fun k => [f k, g k]).length = 2 * n ∧
    ∀ j < 2 * n, ((List.range n).reverse.flatMap fun k => [f k, g k])[j]? =
      some (if j % 2 = 0 then f (n - 1 - j / 2) else g (n - 1 - j / 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hl, hg⟩ := ih
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_cons, List.cons_append]
    refine ⟨by simp only [List.length_cons, hl]; ring, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j <;> simp
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      simp only [List.getElem?_cons_succ]
      rw [hg j' (by omega)]
      have e1 : (j' + 2) % 2 = j' % 2 := by omega
      have e2 : n + 1 - 1 - (j' + 2) / 2 = n - 1 - j' / 2 := by omega
      rw [e1, e2]

private theorem dropLast_map_range {α : Type*} (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).dropLast = (List.range (n - 1)).map f := by
  cases n with
  | zero => rfl
  | succ n => rw [List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat,
      Nat.add_sub_cancel]

namespace TripleData

section CutListEntries

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {i : Fin b}

variable (X) in
/-- The first end of the run of positions on the side `ζ` of the arc from `s_i = ε(p)` to `ε(q)`:
`q` on the right and `p` on the left. The positions on side `ζ` are those strictly between
`arcSideStart i ζ` and `arcSideEnd i ζ` clockwise. -/
def arcSideStart (i : Fin b) : StrandSide → Fin (2 * b)
  | .right => X.arcEndIndex i
  | .left => sourceIndex i

variable (X) in
/-- The second end of the run of positions on the side `ζ` of the arc from `s_i = ε(p)` to
`ε(q)`: `p` on the right and `q` on the left. -/
def arcSideEnd (i : Fin b) : StrandSide → Fin (2 * b)
  | .right => sourceIndex i
  | .left => X.arcEndIndex i

private theorem sideList_arc_right :
    X.sideList .right (X.arc i) = (List.range (X.arcLength i - 1)).flatMap fun k =>
      [X.rot (X.inv (X.arcDart i k)), (X.rot ^ 2) (X.inv (X.arcDart i k))] := by
  change (X.arc i).dropLast.flatMap (X.sideDarts .right) = _
  rw [arc, dropLast_map_range, List.flatMap_map]
  rfl

private theorem sideList_arc_left :
    X.sideList .left (X.arc i) = (List.range (X.arcLength i - 1)).reverse.flatMap fun k =>
      [(X.rot ^ 4) (X.inv (X.arcDart i k)), (X.rot ^ 5) (X.inv (X.arcDart i k))] := by
  change (X.arc i).dropLast.reverse.flatMap (X.sideDarts .left) = _
  rw [arc, dropLast_map_range, ← List.map_reverse, List.flatMap_map]
  rfl

/-- The `ζ` list of the arc `S = (e₁, …, e_m)` from `s_i` has `2(m - 1)` entries. -/
theorem length_sideList_arc (ζ : StrandSide) :
    (X.sideList ζ (X.arc i)).length = 2 * (X.arcLength i - 1) := by
  cases ζ
  · rw [sideList_arc_right]
    exact (getElem?_flatMap_pair _ _ _).1
  · rw [sideList_arc_left]
    exact (getElem?_flatMap_pair_reverse _ _ _).1

/-- The entries of the right list of the arc `S` from `s_i`: entry `j` (`0`-indexed) is
`σ^{j mod 2 + 1}(ē_{⌊j/2⌋ + 1})`. -/
theorem getElem_sideList_arc_right {j : ℕ} (hj : j < (X.sideList .right (X.arc i)).length) :
    (X.sideList .right (X.arc i))[j] =
      (X.rot ^ (j % 2 + 1)) (X.inv (X.arcDart i (j / 2))) := by
  have hl := length_sideList_arc (X := X) (i := i) .right
  have h := (getElem?_flatMap_pair (fun k => X.rot (X.inv (X.arcDart i k)))
    (fun k => (X.rot ^ 2) (X.inv (X.arcDart i k))) (X.arcLength i - 1)).2 j (by omega)
  rw [← sideList_arc_right, List.getElem?_eq_getElem hj] at h
  rw [Option.some_injective _ h]
  split_ifs with h2
  · rw [h2, zero_add, pow_one]
  · rw [show j % 2 = 1 by omega]

/-- The entries of the left list of the arc `S = (e₁, …, e_m)` from `s_i`: entry `j`
(`0`-indexed) is `σ^{j mod 2 + 4}(ē_{m - 1 - ⌊j/2⌋})`. -/
theorem getElem_sideList_arc_left {j : ℕ} (hj : j < (X.sideList .left (X.arc i)).length) :
    (X.sideList .left (X.arc i))[j] =
      (X.rot ^ (j % 2 + 4)) (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - j / 2))) := by
  have hl := length_sideList_arc (X := X) (i := i) .left
  have h := (getElem?_flatMap_pair_reverse (fun k => (X.rot ^ 4) (X.inv (X.arcDart i k)))
    (fun k => (X.rot ^ 5) (X.inv (X.arcDart i k))) (X.arcLength i - 1)).2 j (by omega)
  rw [← sideList_arc_left, List.getElem?_eq_getElem hj] at h
  rw [Option.some_injective _ h]
  split_ifs with h2
  · rw [h2]
  · rw [show j % 2 = 1 by omega]

/-- The `ζ` cut list of the arc from `s_i` consists of the legs at the positions strictly between
`arcSideStart i ζ` and `arcSideEnd i ζ`, in clockwise order, followed by the `ζ` list of the
arc. -/
theorem arcCutList_eq_append (ζ : StrandSide) :
    X.arcCutList i ζ =
      (List.range (((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1)).map
        (fun t => X.endDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ))) ++
      X.sideList ζ (X.arc i) := by
  cases ζ
  · change X.rightCutList i = _
    rw [rightCutList, sideList_arc_right]
    rfl
  · change X.leftCutList i = _
    rw [leftCutList, sideList_arc_left]
    rfl

/-- An interval of `i` runs clockwise from `arcSideStart` to `arcSideEnd` on its side. -/
theorem _root_.ClusterAlgebras.IsIntervalOf.eq_cyclicIcc_arcSide {I : Finset (Fin (2 * b))}
    (hI : IsIntervalOf X.strandPerm i I) :
    I = cyclicIcc (X.arcSideStart i (intervalSide X.strandPerm i I))
      (X.arcSideEnd i (intervalSide X.strandPerm i I)) := by
  unfold intervalSide
  split_ifs with h
  · exact h
  · rcases hI with h' | h'
    · exact absurd h' h
    · exact h'

/-- The interior positions of an interval of `i` are the positions strictly between
`arcSideStart` and `arcSideEnd` on its side. -/
theorem _root_.ClusterAlgebras.IsIntervalOf.mem_intervalInterior_iff {I : Finset (Fin (2 * b))}
    (hI : IsIntervalOf X.strandPerm i I) {r : Fin (2 * b)} :
    r ∈ intervalInterior X.strandPerm i I ↔
      ∃ t, t + 1 < ((X.arcSideEnd i (intervalSide X.strandPerm i I) -
          X.arcSideStart i (intervalSide X.strandPerm i I) : Fin (2 * b)) : ℕ) ∧
        r = (finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i (intervalSide X.strandPerm i I)) := by
  rw [← mem_cyclicIcc_sdiff_iff, ← hI.eq_cyclicIcc_arcSide, intervalInterior]
  have : ({sourceIndex i, targetIndex (X.strandPerm i)} : Finset (Fin (2 * b))) =
      {X.arcSideStart i (intervalSide X.strandPerm i I),
        X.arcSideEnd i (intervalSide X.strandPerm i I)} := by
    cases intervalSide X.strandPerm i I
    · exact pair_comm _ _
    · rfl
  rw [this]

/-- The number of interior positions of an interval of `i`. -/
theorem _root_.ClusterAlgebras.IsIntervalOf.card_intervalInterior_eq {I : Finset (Fin (2 * b))}
    (hI : IsIntervalOf X.strandPerm i I) :
    (intervalInterior X.strandPerm i I).card =
      ((X.arcSideEnd i (intervalSide X.strandPerm i I) -
          X.arcSideStart i (intervalSide X.strandPerm i I) : Fin (2 * b)) : ℕ) - 1 := by
  have hb : NeZero (2 * b) := ⟨by have := i.isLt; omega⟩
  have h := hI.card_intervalInterior
  have hc := card_cyclicIcc (X.arcSideStart i (intervalSide X.strandPerm i I))
    (X.arcSideEnd i (intervalSide X.strandPerm i I))
  rw [← hI.eq_cyclicIcc_arcSide] at hc
  omega

end CutListEntries

end TripleData

/-! ### Chords of a cut without triple points -/

namespace TripleData

namespace IsCutData

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {K : Finset H}
  {L : List H}

omit [Fintype H] [DecidableEq H] in
/-- The endpoint label `r` of the cut with shift `s ≤ 1` at which the cut list entry `x` sits:
`r + s ≡ x` modulo `N`. -/
private theorem exists_cutEndIndex_eq (hev : Even L.length) {s : ℕ} (hs : s ≤ 1) {x : ℕ}
    (hx : x < L.length) :
    ∃ r : Fin (2 * (L.length / 2)), cutEndIndex L s r = ⟨x, hx⟩ ∧
      (r : ℕ) = if s ≤ x then x - s else x + L.length - s := by
  have h2 := Nat.two_mul_div_two_of_even hev
  have hval : (if s ≤ x then x - s else x + L.length - s) < 2 * (L.length / 2) := by
    rw [h2]; split_ifs <;> omega
  refine ⟨⟨_, hval⟩, Fin.ext ?_, rfl⟩
  simp only [cutEndIndex]
  split_ifs with h
  · rw [Nat.sub_add_cancel h, Nat.mod_eq_of_lt hx]
  · rw [show x + L.length - s + s = x + L.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hx]

/-- **Chords of a cut without crossing**: in a cut along `(K, L)` with shift `s ≤ 1` that is a
triple diagram, if `t < v < u < w` are indices of `L` with `ḡ_t = g_u`, then `ḡ_v ≠ g_w`. -/
theorem inv_getElem_ne_of_lt (hc : X.IsCutData K L) (hinv : Function.Involutive X.inv)
    {s : ℕ} (hs : s ≤ 1) (hY : (X.cut K L s).IsTripleDiagram) (hev : Even L.length)
    {t v u w : ℕ} (htv : t < v) (hvu : v < u) (huw : u < w) (hw : w < L.length)
    (h : X.inv L[t] = L[u]) : X.inv L[v] ≠ L[w] := by
  intro h'
  obtain ⟨a, ha, hav⟩ := exists_cutEndIndex_eq (s := s) hev hs (x := t) (by omega)
  obtain ⟨b', hb, hbv⟩ := exists_cutEndIndex_eq (s := s) hev hs (x := v) (by omega)
  obtain ⟨c, hcc, hcv⟩ := exists_cutEndIndex_eq (s := s) hev hs (x := u) (by omega)
  obtain ⟨d, hd, hdv⟩ := exists_cutEndIndex_eq (s := s) hev hs (x := w) hw
  have h2 := Nat.two_mul_div_two_of_even hev
  have hend : ∀ (r : Fin (2 * (L.length / 2))) (x : ℕ) (hx : x < L.length),
      cutEndIndex L s r = ⟨x, hx⟩ →
        (X.cut K L s).endDart r = .inl ⟨L[x], hc.mem_of_mem_list _ (List.getElem_mem _)⟩ := by
    intro r x hx hr
    rw [cut_endDart, hr, hc.cutListDart_eq]
  have key := TripleData.inv_endDart_ne_endDart_of_cyclic hY (a := a) (b := b') (c := c) (d := d)
  have hval : ∀ (p q : Fin (2 * (L.length / 2))),
      ((p - q : Fin (2 * (L.length / 2))) : ℕ) =
        if (q : ℕ) ≤ p then (p : ℕ) - q else L.length + (p : ℕ) - q := by
    intro p q
    rw [fin_val_sub]
    split_ifs
    · rfl
    · omega
  simp only [hval] at key
  rw [hav, hbv, hcv, hdv] at key
  apply key (by split_ifs <;> omega) (by split_ifs <;> omega) (by split_ifs <;> omega)
  · rw [hend a t _ ha, hend c u _ hcc, hc.cut_inv_inl hinv]
    exact congrArg Sum.inl (Subtype.ext h)
  · rw [hend b' v _ hb, hend d w _ hd, hc.cut_inv_inl hinv]
    exact congrArg Sum.inl (Subtype.ext h')

end IsCutData

end TripleData

/-! ### The shape of a boundary-parallel arc -/

/-- If `g₀, …, g_{4k-1}` are distinct, `ι` is injective, `ι` maps the first `2k` entries into the
last `2k` entries and onto them, and the chords `t ↦ u` with `ι g_t = g_u` do not cross,
then `ι g_t = g_{4k-1-t}` for `t < 2k`. -/
private theorem eq_sub_of_noncrossing {α : Type*} {ι : α → α} (hι : Function.Injective ι)
    {g : ℕ → α} {k : ℕ} (hinj : ∀ x y, x < 4 * k → y < 4 * k → g x = g y → x = y)
    (h₁ : ∀ t < 2 * k, ∃ u, 2 * k ≤ u ∧ u < 4 * k ∧ ι (g t) = g u)
    (h₂ : ∀ w, 2 * k ≤ w → w < 4 * k → ∃ v < 2 * k, ι (g v) = g w)
    (hnc : ∀ t v u w, t < v → v < u → u < w → w < 4 * k → ι (g t) = g u → ι (g v) ≠ g w) :
    ∀ t < 2 * k, ι (g t) = g (4 * k - 1 - t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    obtain ⟨u, hu1, hu2, hut⟩ := h₁ t ht
    rcases lt_trichotomy u (4 * k - 1 - t) with hlt | heq | hgt
    · exfalso
      obtain ⟨v, hv, hvw⟩ := h₂ (4 * k - 1 - t) (by omega) (by omega)
      rcases lt_trichotomy v t with hvt | rfl | hvt
      · have := ih v hvt hv
        rw [this] at hvw
        have := hinj _ _ (by omega) (by omega) hvw
        omega
      · rw [hut] at hvw
        have := hinj _ _ hu2 (by omega) hvw
        omega
      · exact hnc t v u (4 * k - 1 - t) hvt (by omega) hlt (by omega) hut hvw
    · rw [hut, heq]
    · exfalso
      have h' := ih (4 * k - 1 - u) (by omega) (by omega)
      rw [show 4 * k - 1 - (4 * k - 1 - u) = u by omega, ← hut] at h'
      have := hinj _ _ (by omega) (by omega) (hι h')
      omega

namespace TripleData

section Shape

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {i : Fin b}

omit [Fintype H] [DecidableEq H] in
private theorem getD_eq_getElem' {L : List H} {x : ℕ} (d : H) (hx : x < L.length) :
    L.getD x d = L[x] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]
  rfl

/-- A dart of `H_ζ(S)` lies in the `ζ` cut list or at a triple point avoided by `S`. -/
theorem IsSimpleArc.mem_arcCutList_or_avoided (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} {d : H} (hd : d ∈ X.arcSideDarts i ζ) :
    d ∈ X.arcCutList i ζ ∨
      (X.vertexOf d ∈ X.internalVertices ∧ ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) := by
  cases ζ
  · exact hS.mem_rightCutList_or_of_mem_rightSide hX hd
  · exact hS.mem_leftCutList_or_of_mem_leftSide hX hd

/-- **Sides by reachability**: for a simple arc `S`, the set `H_ζ(S)` is the least set of darts
that contains the `ζ` cut list of `S`, is closed under `d ↦ d̄`, and is closed under `σ` and `σ⁻¹`
at the triple points avoided by `S`. -/
theorem IsSimpleArc.isLeast_arcSideDarts (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    (ζ : StrandSide) :
    IsLeast {K : Set H | (∀ d ∈ X.arcCutList i ζ, d ∈ K) ∧ (∀ d ∈ K, X.inv d ∈ K) ∧
      ∀ d ∈ K, X.vertexOf d ∈ X.internalVertices →
        ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) → X.rot d ∈ K ∧ X.rot.symm d ∈ K}
      (X.arcSideDarts i ζ : Set H) := by
  cases ζ
  · exact hS.isLeast_rightSide hX
  · exact hS.isLeast_leftSide hX

/-- The cut list of a boundary-parallel arc starts with the legs at the interior positions and
ends with the side list of the arc. -/
private theorem IsBoundaryParallel.shape_legs (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ) :
    (X.arcCutList i ζ).length = 4 * (X.arcLength i - 1) ∧
    (∀ t < 2 * (X.arcLength i - 1), (X.arcCutList i ζ)[t]? =
      some (X.endDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ)))) ∧
    ∀ j < 2 * (X.arcLength i - 1),
      (X.arcCutList i ζ)[2 * (X.arcLength i - 1) + j]? = (X.sideList ζ (X.arc i))[j]? := by
  subst hζ
  set ζ := intervalSide X.strandPerm i I with hζdef
  set k := X.arcLength i - 1 with hkdef
  have hk := hB.two_mul_arcLength_sub_one hX
  obtain ⟨hI, -, -, -⟩ := hB
  have hcard := hI.card_intervalInterior_eq (X := X)
  rw [← hζdef] at hcard
  set legs := (List.range (((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1)).map
    (fun t => X.endDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ))) with hlegs
  have hL : X.arcCutList i ζ = legs ++ X.sideList ζ (X.arc i) :=
    arcCutList_eq_append (X := X) (i := i) ζ
  have hSL := length_sideList_arc (X := X) (i := i) ζ
  have hlegl : legs.length = 2 * k := by
    rw [hlegs, List.length_map, List.length_range]
    omega
  refine ⟨by rw [hL, List.length_append, hlegl, hSL]; omega, fun t ht => ?_, fun j hj => ?_⟩
  · rw [hL, List.getElem?_append_left (by omega), hlegs, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  · rw [hL, List.getElem?_append_right (by omega), hlegl, Nat.add_sub_cancel_left]

/-- On a boundary-parallel arc, the reverse of each leg at an interior position lies on the side
list of the arc. -/
private theorem IsBoundaryParallel.inv_mem_sideList_of_getElem?_arcCutList
    (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I)
    {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ) :
    ∀ t < 2 * (X.arcLength i - 1), ∀ d, (X.arcCutList i ζ)[t]? = some d →
      X.inv d ∈ X.sideList ζ (X.arc i) := by
  have hleg := (hB.shape_legs hX hζ).2.1
  subst hζ
  set ζ := intervalSide X.strandPerm i I with hζdef
  set k := X.arcLength i - 1 with hkdef
  have hk := hB.two_mul_arcLength_sub_one hX
  obtain ⟨hI, hS, -, hpass⟩ := hB
  have hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := hS.isCutData_arcCutList hX ζ
  have hcard := hI.card_intervalInterior_eq (X := X)
  rw [← hζdef] at hcard
  intro t ht d hd
  have hiK := hc.inv_mem _ (hc.mem_of_mem_list _ (List.mem_of_getElem? hd))
  have hp := hpass _ ((hI.mem_intervalInterior_iff (X := X)).2 ⟨t, by rw [← hζdef]; omega, rfl⟩)
  rw [hleg t ht, Option.some.injEq] at hd
  rw [hd] at hp
  rcases hS.mem_arcCutList_or_avoided hX hiK with hmem | ⟨-, hav⟩
  · rw [arcCutList_eq_append (X := X) (i := i) ζ, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exfalso
      obtain ⟨t', -, ht'⟩ := List.mem_map.1 hmem
      have hb := (X.mem_boundaryVertices.1 (hX.endpoint_mem
        ((finRotate (2 * b) ^ (t' + 1)) (X.arcSideStart i ζ)))).2
      change X.IsBoundaryVertex (X.vertexOf (X.endDart _)) at hb
      rw [ht'] at hb
      exact (X.mem_internalVertices.1 hp.1).2 hb
    · exact hmem
  · exact absurd hp hav

/-- On a boundary-parallel arc, every entry of the second half of the cut list is the reverse of
an entry of the first half. -/
private theorem IsBoundaryParallel.exists_map_inv_getElem?_arcCutList
    (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I)
    {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ) :
    ∀ w < 4 * (X.arcLength i - 1), 2 * (X.arcLength i - 1) ≤ w →
      ∃ v < 2 * (X.arcLength i - 1), (X.arcCutList i ζ)[v]?.map X.inv = (X.arcCutList i ζ)[w]? := by
  obtain ⟨hlen, -, hside⟩ := hB.shape_legs hX hζ
  have h₁ := hB.inv_mem_sideList_of_getElem?_arcCutList hX hζ
  obtain ⟨-, hS, -, -⟩ := hB
  have hL := arcCutList_eq_append (X := X) (i := i) ζ
  set L := X.arcCutList i ζ with hLdef
  set k := X.arcLength i - 1 with hkdef
  have hc : X.IsCutData (X.arcSideDarts i ζ) L := hS.isCutData_arcCutList hX ζ
  have hSL := length_sideList_arc (X := X) (i := i) ζ
  have hSLnd : (X.sideList ζ (X.arc i)).Nodup := by
    have := hc.nodup
    rw [hL] at this
    exact (List.nodup_append.1 this).2.1
  have hgetD : ∀ x < L.length, L[x]? = some (L.getD x (X.arcDart i 0)) := fun x hx => by
    rw [getD_eq_getElem' _ hx, List.getElem?_eq_getElem hx]
  intro w hw hw'
  set F : Finset H := (range (2 * k)).image fun v => X.inv (L.getD v (X.arcDart i 0))
  have hF : F ⊆ (X.sideList ζ (X.arc i)).toFinset := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hd
    rw [mem_range] at hv
    exact List.mem_toFinset.2 (h₁ v hv _ (hgetD v (by omega)))
  have hFc : F.card = 2 * k := by
    rw [card_image_of_injOn, card_range]
    intro v hv v' hv' h
    simp only [coe_range, Set.mem_Iio] at hv hv'
    have h' := hX.inv_involutive.injective h
    rw [getD_eq_getElem' _ (by omega), getD_eq_getElem' _ (by omega)] at h'
    exact hc.nodup.getElem_inj_iff.1 h'
  have hFe : F = (X.sideList ζ (X.arc i)).toFinset := eq_of_subset_of_card_le hF (by
    rw [List.toFinset_card_of_nodup hSLnd, hSL, hFc])
  have hmem : L.getD w (X.arcDart i 0) ∈ F := by
    rw [hFe, List.mem_toFinset]
    have := hside (w - 2 * k) (by omega)
    rw [show 2 * k + (w - 2 * k) = w by omega, hgetD w (by omega)] at this
    exact List.mem_of_getElem? this.symm
  obtain ⟨v, hv, hvw⟩ := mem_image.1 hmem
  rw [mem_range] at hv
  refine ⟨v, hv, ?_⟩
  rw [hgetD v (by omega), hgetD w (by omega), Option.map_some, hvw]

/-- For a boundary-parallel arc, with `ζ` the side of `I`, `2k` the number of interior positions
and `L = (g₀, …, g_{4k-1})` the `ζ` cut list, the first `2k` entries are the legs at the interior
positions in clockwise order, the last `2k` are the `ζ` list of the arc, every one of those is the
reverse of one of the first `2k`, and `ḡ_t = g_{4k-1-t}` for `t < 2k`. -/
private theorem IsBoundaryParallel.shape (hX : X.IsTripleDiagram) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ) :
    (X.arcCutList i ζ).length = 4 * (X.arcLength i - 1) ∧
    (∀ t < 2 * (X.arcLength i - 1), (X.arcCutList i ζ)[t]? =
      some (X.endDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ)))) ∧
    (∀ j < 2 * (X.arcLength i - 1),
      (X.arcCutList i ζ)[2 * (X.arcLength i - 1) + j]? = (X.sideList ζ (X.arc i))[j]?) ∧
    (∀ w < 4 * (X.arcLength i - 1), 2 * (X.arcLength i - 1) ≤ w →
      ∃ v < 2 * (X.arcLength i - 1), (X.arcCutList i ζ)[v]?.map X.inv = (X.arcCutList i ζ)[w]?) ∧
    ∀ t < 2 * (X.arcLength i - 1),
      (X.arcCutList i ζ)[t]?.map X.inv = (X.arcCutList i ζ)[4 * (X.arcLength i - 1) - 1 - t]? := by
  obtain ⟨hlen, hleg, hside⟩ := hB.shape_legs hX hζ
  have h₁ := hB.inv_mem_sideList_of_getElem?_arcCutList hX hζ
  have h₂ := hB.exists_map_inv_getElem?_arcCutList hX hζ
  refine ⟨hlen, hleg, hside, h₂, ?_⟩
  obtain ⟨-, hS, -, -⟩ := hB
  set L := X.arcCutList i ζ with hLdef
  set k := X.arcLength i - 1 with hkdef
  have hc : X.IsCutData (X.arcSideDarts i ζ) L := hS.isCutData_arcCutList hX ζ
  have hSL := length_sideList_arc (X := X) (i := i) ζ
  have hgetD : ∀ x < L.length, L[x]? = some (L.getD x (X.arcDart i 0)) := fun x hx => by
    rw [getD_eq_getElem' _ hx, List.getElem?_eq_getElem hx]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · intro t ht
    omega
  have hY : (X.arcCut i ζ).IsTripleDiagram :=
    hS.isTripleDiagram_arcCut hX ζ (by rw [← hLdef]; omega)
  have hs : ζ.cutShift ≤ 1 := by cases ζ <;> simp [StrandSide.cutShift]
  set d₀ := X.arcDart i 0
  have key := eq_sub_of_noncrossing (ι := X.inv) hX.inv_involutive.injective
    (g := fun x => L.getD x d₀) (k := k)
    (fun x y hx hy h => by
      rw [getD_eq_getElem' _ (by omega), getD_eq_getElem' _ (by omega)] at h
      exact hc.nodup.getElem_inj_iff.1 h)
    (fun t ht => by
      obtain ⟨j, hj, hjt⟩ := List.mem_iff_getElem.1 (h₁ t ht _ (hgetD t (by omega)))
      rw [hSL] at hj
      refine ⟨2 * k + j, by omega, by omega, ?_⟩
      have := hside j (by omega)
      rw [hgetD _ (by omega), List.getElem?_eq_getElem (by rw [hSL]; omega), hjt,
        Option.some.injEq] at this
      exact this.symm)
    (fun w hw' hw => by
      obtain ⟨v, hv, hvw⟩ := h₂ w hw hw'
      refine ⟨v, hv, ?_⟩
      rw [hgetD v (by omega), hgetD w (by omega), Option.map_some, Option.some.injEq] at hvw
      exact hvw)
    (fun t v u w htv hvu huw hw h h' => by
      rw [getD_eq_getElem' _ (by omega), getD_eq_getElem' _ (by omega)] at h h'
      exact hc.inv_getElem_ne_of_lt hX.inv_involutive hs hY (even_length_arcCutList ζ) htv hvu
        huw (by omega) h h')
  intro t ht
  have := key t ht
  rw [hgetD t (by omega), hgetD _ (by omega), Option.map_some, this]

/-- An interval of `i` that runs both ways has no interior position. -/
private theorem intervalInterior_eq_empty_of_eq {I : Finset (Fin (2 * b))}
    (h₁ : I = cyclicIcc (sourceIndex i) (targetIndex (X.strandPerm i)))
    (h₂ : I = cyclicIcc (targetIndex (X.strandPerm i)) (sourceIndex i)) :
    intervalInterior X.strandPerm i I = ∅ := by
  have h := cyclicIcc_inter_cyclicIcc (sourceIndex i) (targetIndex (X.strandPerm i))
  rw [← h₁, ← h₂, inter_self] at h
  rw [intervalInterior, h, sdiff_self]
  rfl

/-- **The shape of a boundary-parallel arc**, when `I` runs clockwise from `p` to `q`: for the arc
`S = (e₁, …, e_m)` from `s_i = ε(p)` to `ε(q)`, boundary-parallel along `I`, `n̄_{p+2l-1} = σ⁵ ē_l`
and `n̄_{p+2l} = σ⁴ ē_l` for `l ∈ [1, m - 1]`. Here `l` is `0`-indexed: `e_{l+1}` is
`X.arcDart i l`, and `p + t` is the `t`-th clockwise successor of `p`. -/
@[cluster_algebras "lem_boundary_parallel_structure"]
theorem IsBoundaryParallel.inv_endDart_of_eq_cyclicIcc (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I)
    (hI : I = cyclicIcc (sourceIndex i) (targetIndex (X.strandPerm i))) {l : ℕ}
    (hl : l + 1 < X.arcLength i) :
    X.inv (X.endDart ((finRotate (2 * b) ^ (2 * l + 1)) (sourceIndex i))) =
        (X.rot ^ 5) (X.inv (X.arcDart i l)) ∧
      X.inv (X.endDart ((finRotate (2 * b) ^ (2 * l + 2)) (sourceIndex i))) =
        (X.rot ^ 4) (X.inv (X.arcDart i l)) := by
  have hζ : intervalSide X.strandPerm i I = .left := if_pos hI
  obtain ⟨hlen, hleg, hside, -, hrev⟩ := hB.shape hX hζ
  set k := X.arcLength i - 1 with hk
  have hSL := length_sideList_arc (X := X) (i := i) .left
  have key : ∀ t < 2 * k, ∀ j, j < 2 * k → 4 * k - 1 - t = 2 * k + j →
      X.inv (X.endDart ((finRotate (2 * b) ^ (t + 1)) (sourceIndex i))) =
        (X.rot ^ (j % 2 + 4)) (X.inv (X.arcDart i (X.arcLength i - 1 - 1 - j / 2))) := by
    intro t ht j hj htj
    have h := hrev t ht
    rwa [hleg t ht, htj, hside j hj, List.getElem?_eq_getElem (by rw [hSL]; omega),
      getElem_sideList_arc_left, Option.map_some, Option.some.injEq] at h
  constructor
  · have := key (2 * l) (by omega) (2 * k - 1 - 2 * l) (by omega) (by omega)
    rwa [show (2 * k - 1 - 2 * l) % 2 + 4 = 5 by omega,
      show X.arcLength i - 1 - 1 - (2 * k - 1 - 2 * l) / 2 = l by omega] at this
  · have := key (2 * l + 1) (by omega) (2 * k - 2 - 2 * l) (by omega) (by omega)
    rwa [show (2 * k - 2 - 2 * l) % 2 + 4 = 4 by omega,
      show X.arcLength i - 1 - 1 - (2 * k - 2 - 2 * l) / 2 = l by omega] at this

/-- **The shape of a boundary-parallel arc**, when `I` runs clockwise from `q` to `p`: for the arc
`S = (e₁, …, e_m)` from `s_i = ε(p)` to `ε(q)`, boundary-parallel along `I`,
`n̄_{q+2l-1} = σ² ē_{m-l}` and `n̄_{q+2l} = σ ē_{m-l}` for `l ∈ [1, m - 1]`. Here `l` is
`0`-indexed: `ē_{m-l-1}` is `X.inv (X.arcDart i (m - 2 - l))`, and `q + t` is the `t`-th
clockwise successor of `q`. -/
@[cluster_algebras "lem_boundary_parallel_structure"]
theorem IsBoundaryParallel.inv_endDart_of_eq_cyclicIcc' (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I)
    (hI : I = cyclicIcc (targetIndex (X.strandPerm i)) (sourceIndex i)) {l : ℕ}
    (hl : l + 1 < X.arcLength i) :
    X.inv (X.endDart ((finRotate (2 * b) ^ (2 * l + 1)) (targetIndex (X.strandPerm i)))) =
        (X.rot ^ 2) (X.inv (X.arcDart i (X.arcLength i - 2 - l))) ∧
      X.inv (X.endDart ((finRotate (2 * b) ^ (2 * l + 2)) (targetIndex (X.strandPerm i)))) =
        X.rot (X.inv (X.arcDart i (X.arcLength i - 2 - l))) := by
  have hk2 := hB.two_mul_arcLength_sub_one hX
  have hζ : intervalSide X.strandPerm i I = .right := by
    unfold intervalSide
    split_ifs with h
    · rw [intervalInterior_eq_empty_of_eq h hI, card_empty] at hk2
      omega
    · rfl
  obtain ⟨hlen, hleg, hside, -, hrev⟩ := hB.shape hX hζ
  set k := X.arcLength i - 1 with hk
  have hSL := length_sideList_arc (X := X) (i := i) .right
  have key : ∀ t < 2 * k, ∀ j, j < 2 * k → 4 * k - 1 - t = 2 * k + j →
      X.inv (X.endDart ((finRotate (2 * b) ^ (t + 1)) (targetIndex (X.strandPerm i)))) =
        (X.rot ^ (j % 2 + 1)) (X.inv (X.arcDart i (j / 2))) := by
    intro t ht j hj htj
    have h := hrev t ht
    rwa [hleg t ht, htj, hside j hj, List.getElem?_eq_getElem (by rw [hSL]; omega),
      getElem_sideList_arc_right, Option.map_some, Option.some.injEq] at h
  constructor
  · have := key (2 * l) (by omega) (2 * k - 1 - 2 * l) (by omega) (by omega)
    rwa [show (2 * k - 1 - 2 * l) % 2 + 1 = 2 by omega,
      show (2 * k - 1 - 2 * l) / 2 = X.arcLength i - 2 - l by omega] at this
  · have := key (2 * l + 1) (by omega) (2 * k - 2 - 2 * l) (by omega) (by omega)
    rwa [show (2 * k - 2 - 2 * l) % 2 + 1 = 1 by omega, pow_one,
      show (2 * k - 2 - 2 * l) / 2 = X.arcLength i - 2 - l by omega] at this

/-- **The shape of a boundary-parallel arc**: the side `ζ` of `I` satisfies
`H_ζ(S) = {n_r, n̄_r : r interior to I}`. -/
@[cluster_algebras "lem_boundary_parallel_structure"]
theorem IsBoundaryParallel.arcSideDarts_intervalSide (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I) :
    X.arcSideDarts i (intervalSide X.strandPerm i I) =
      (intervalInterior X.strandPerm i I).biUnion fun r => {X.endDart r, X.inv (X.endDart r)} := by
  set ζ := intervalSide X.strandPerm i I with hζdef
  obtain ⟨hlen, hleg, -, h₂, -⟩ := hB.shape hX hζdef.symm
  have hk2 := hB.two_mul_arcLength_sub_one hX
  obtain ⟨hI, hS, -, hpass⟩ := hB
  have hc : X.IsCutData (X.arcSideDarts i ζ) (X.arcCutList i ζ) := hS.isCutData_arcCutList hX ζ
  have hcard := hI.card_intervalInterior_eq (X := X)
  rw [← hζdef] at hcard
  have hint : ∀ r ∈ intervalInterior X.strandPerm i I, ∃ t < 2 * (X.arcLength i - 1),
      (X.arcCutList i ζ)[t]? = some (X.endDart r) := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := (hI.mem_intervalInterior_iff (X := X)).1 hr
    rw [← hζdef] at ht ⊢
    exact ⟨t, by omega, hleg t (by omega)⟩
  apply Subset.antisymm
  · have hmem : ((intervalInterior X.strandPerm i I).biUnion
        fun r => ({X.endDart r, X.inv (X.endDart r)} : Finset H) : Set H) ∈
        {K : Set H | (∀ d ∈ X.arcCutList i ζ, d ∈ K) ∧ (∀ d ∈ K, X.inv d ∈ K) ∧
          ∀ d ∈ K, X.vertexOf d ∈ X.internalVertices →
            ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d) →
              X.rot d ∈ K ∧ X.rot.symm d ∈ K} := by
      refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd hdint hdpass => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_iff_getElem.1 hd
        rw [mem_coe, mem_biUnion]
        rcases lt_or_ge x (2 * (X.arcLength i - 1)) with hx' | hx'
        · have := hleg x hx'
          rw [List.getElem?_eq_getElem hx, Option.some.injEq] at this
          refine ⟨_, (hI.mem_intervalInterior_iff (X := X)).2 ⟨x, by rw [← hζdef]; omega, rfl⟩,
            ?_⟩
          rw [this, ← hζdef]
          exact mem_insert_self _ _
        · obtain ⟨v, hv, hvx⟩ := h₂ x (by omega) hx'
          have hl := hleg v hv
          rw [hl, Option.map_some, List.getElem?_eq_getElem hx, Option.some.injEq] at hvx
          refine ⟨_, (hI.mem_intervalInterior_iff (X := X)).2 ⟨v, by rw [← hζdef]; omega, rfl⟩,
            ?_⟩
          rw [← hvx, ← hζdef]
          exact mem_insert_of_mem (mem_singleton_self _)
      · rw [mem_coe, mem_biUnion] at hd ⊢
        obtain ⟨r, hr, hd⟩ := hd
        refine ⟨r, hr, ?_⟩
        rcases mem_insert.1 hd with rfl | hd
        · exact mem_insert_of_mem (mem_singleton_self _)
        · rw [mem_singleton.1 hd, hX.inv_involutive]
          exact mem_insert_self _ _
      · exfalso
        rw [mem_coe, mem_biUnion] at hd
        obtain ⟨r, hr, hd⟩ := hd
        rcases mem_insert.1 hd with rfl | hd
        · exact (X.mem_internalVertices.1 hdint).2
            (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2
        · rw [mem_singleton.1 hd] at hdpass
          exact hdpass (hpass r hr)
    exact coe_subset.1 ((hS.isLeast_arcSideDarts hX ζ).2 hmem)
  · intro d hd
    rw [mem_biUnion] at hd
    obtain ⟨r, hr, hd⟩ := hd
    obtain ⟨t, ht, htr⟩ := hint r hr
    have hrL : X.endDart r ∈ X.arcCutList i ζ := List.mem_of_getElem? htr
    have hrK := hc.mem_of_mem_list _ hrL
    rcases mem_insert.1 hd with rfl | hd
    · exact hrK
    · rw [mem_singleton.1 hd]
      exact hc.inv_mem _ hrK

end Shape

end TripleData

/-! ### Arcs of the cut along a minimal interval -/

/-- A finset exchanged with its complement by an involution has as many elements as its
complement. -/
theorem card_eq_card_compl_of_involutive {α : Type*} [Fintype α] [DecidableEq α] {ω : α → α}
    (hω : Function.Involutive ω) {P : Finset α} (hωP : ∀ r, ω r ∈ P ↔ r ∉ P) :
    P.card = Pᶜ.card :=
  le_antisymm
    (card_le_card_of_injOn ω (fun r hr => by
      rw [coe_compl, Set.mem_compl_iff, mem_coe, hωP, not_not]
      exact hr) hω.injective.injOn)
    (card_le_card_of_injOn ω (fun r hr => by
      rw [mem_coe, hωP]
      simpa using hr) hω.injective.injOn)

namespace TripleData

section ArcsOfCut

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {i : Fin b}

/-- The strand map of a pre-triple diagram is injective. -/
private theorem strandMap_injective : Function.Injective X.strandMap := by
  have hv : ∀ d d', X.RunsToEndpoint d → ¬X.RunsToEndpoint d' →
      X.inv d ≠ X.rot (X.rot (X.rot (X.inv d'))) := by
    intro d d' hd hd' h
    apply hd'
    change X.IsBoundaryVertex (X.vertexOf (X.inv d'))
    have := congrArg X.vertexOf h
    rw [X.vertexOf_rot, X.vertexOf_rot, X.vertexOf_rot] at this
    rw [← this]
    exact hd
  intro d d' h
  by_cases hd : X.RunsToEndpoint d <;> by_cases hd' : X.RunsToEndpoint d'
  · rw [X.strandMap_of_runsToEndpoint hd, X.strandMap_of_runsToEndpoint hd'] at h
    exact X.inv.injective h
  · rw [X.strandMap_of_runsToEndpoint hd, X.strandMap_of_not_runsToEndpoint hd'] at h
    exact absurd h (hv d d' hd hd')
  · rw [X.strandMap_of_not_runsToEndpoint hd, X.strandMap_of_runsToEndpoint hd'] at h
    exact absurd h.symm (hv d' d hd' hd)
  · rw [X.strandMap_of_not_runsToEndpoint hd, X.strandMap_of_not_runsToEndpoint hd'] at h
    exact X.inv.injective (X.rot.injective (X.rot.injective (X.rot.injective h)))

/-- Two arcs, the second at least as long as the first, with the same last dart are equal. -/
private theorem eq_of_arcDart_last_eq_aux (hX : X.IsPreTripleDiagram) {j j' : Fin b}
    (hle : X.arcLength j ≤ X.arcLength j')
    (h : X.arcDart j (X.arcLength j - 1) = X.arcDart j' (X.arcLength j' - 1)) : j = j' := by
  have hm := hX.arcLength_ne_zero j
  have hm' := hX.arcLength_ne_zero j'
  have h' : X.strandMap^[X.arcLength j - 1] (X.endDart (sourceIndex j)) =
      X.strandMap^[X.arcLength j - 1]
        (X.arcDart j' (X.arcLength j' - X.arcLength j)) := by
    change X.arcDart j _ = _
    rw [h, arcDart, arcDart, ← Function.iterate_add_apply]
    congr 1
    omega
  have h0 := strandMap_injective.iterate _ h'
  rcases Nat.eq_zero_or_pos (X.arcLength j' - X.arcLength j) with h1 | h1
  · rw [h1, arcDart_zero] at h0
    exact sourceIndex_injective (hX.endpoint_injective (by
      rw [endpoint, endpoint, h0]))
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, X.arcLength j' - X.arcLength j = t + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
      h1).symm⟩
    rw [ht] at h0
    obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hm'
    have hs := X.strandStep_arcDart hM (k := t) (by omega)
    have hb := (X.mem_boundaryVertices.1 (hX.endpoint_mem (sourceIndex j))).2
    change X.IsBoundaryVertex (X.vertexOf (X.endDart (sourceIndex j))) at hb
    rw [h0, hs.vertexOf_eq] at hb
    exact hs.1 hb

/-- Distinct arcs of a pre-triple diagram have distinct last darts. -/
private theorem eq_of_arcDart_last_eq (hX : X.IsPreTripleDiagram) {j j' : Fin b}
    (h : X.arcDart j (X.arcLength j - 1) = X.arcDart j' (X.arcLength j' - 1)) : j = j' := by
  rcases le_total (X.arcLength j) (X.arcLength j') with hle | hle
  · exact eq_of_arcDart_last_eq_aux hX hle h
  · exact (eq_of_arcDart_last_eq_aux hX hle h.symm).symm

/-- The strand permutation of a triple diagram is injective. -/
private theorem strandPerm_injective' (hX : X.IsTripleDiagram) :
    Function.Injective X.strandPerm := by
  intro j j' h
  have h1 := endDart_arcEndIndex hX j
  rw [show X.arcEndIndex j = X.arcEndIndex j' by simp only [arcEndIndex, h],
    endDart_arcEndIndex hX j'] at h1
  exact eq_of_arcDart_last_eq hX.toIsPreTripleDiagram (X.inv.injective h1).symm

/-- The two ends of the arc from `s_j` of a cut, as entries of the cut list. -/
private theorem arc_arcCut_ends (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i)
    {ζ : StrandSide} (hN : 2 ≤ (X.arcCutList i ζ).length)
    (j : Fin ((X.arcCutList i ζ).length / 2)) :
    ∃ Q : List {d // d ∈ X.arcSideDarts i ζ}, Q.map Sum.inl = (X.arcCut i ζ).arc j ∧
      X.IsStrandPath (Q.map Subtype.val) ∧
      (Q.map Subtype.val).head? =
        some (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ)] ∧
      (Q.map Subtype.val).getLast?.map X.inv =
        some (X.arcCutList i ζ)[(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
          (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ)] := by
  have hc := hS.isCutData_arcCutList hX ζ
  have hY : (X.arcCut i ζ).IsTripleDiagram := hS.isTripleDiagram_arcCut hX ζ hN
  have hYp := hY.toIsPreTripleDiagram
  have hYc : X.arcCut i ζ = X.cut (X.arcSideDarts i ζ) (X.arcCutList i ζ) ζ.cutShift := rfl
  have hm := hYp.arcLength_ne_zero j
  have hYP : (X.arcCut i ζ).IsStrandPath ((X.arcCut i ζ).arc j) :=
    (X.arcCut i ζ).isStrandPath_arc hYp hm
  obtain ⟨Q, hQ, hP⟩ := hS.exists_isStrandPath_of_isStrandPath_arcCut hX ζ hYP
  refine ⟨Q, hQ.symm, hP, ?_, ?_⟩
  · have h0 : ((X.arcCut i ζ).arc j).head? = some ((X.arcCut i ζ).endDart (sourceIndex j)) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [length_arc]; omega),
        getElem_arc, arcDart_zero]
    rw [hQ, List.head?_map, hYc, cut_endDart, hc.cutListDart_eq] at h0
    rw [List.head?_map]
    obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.1 h0
    rw [hq, Option.map_some, congrArg Subtype.val (Sum.inl_injective hq')]
  · have h0 : ((X.arcCut i ζ).arc j).getLast? =
        some ((X.arcCut i ζ).arcDart j ((X.arcCut i ζ).arcLength j - 1)) := by
      rw [List.getLast?_eq_getElem?, length_arc,
        List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc]
    have h1 := endDart_arcEndIndex hY j
    rw [hQ, List.getLast?_map] at h0
    obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.1 h0
    rw [← hq', hYc, hc.cut_inv_inl hX.inv_involutive] at h1
    rw [List.getLast?_map, hq, Option.map_some, Option.map_some]
    change (X.arcCut i ζ).endDart (targetIndex ((X.arcCut i ζ).strandPerm j)) = _ at h1
    rw [hYc, cut_endDart, hc.cutListDart_eq] at h1
    exact congrArg some (congrArg Subtype.val (Sum.inl_injective h1)).symm

/-- The length of the cut list of a minimal interval `I` on side `ζ`: the `c` interior positions
of `I` and the `2(m - 1)` darts of the `ζ` list of `S`. -/
private theorem length_arcCutList_of_isMinimalInterval {I : Finset (Fin (2 * b))}
    (hI : IsMinimalInterval X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) :
    (X.arcCutList i ζ).length =
      (intervalInterior X.strandPerm i I).card + 2 * (X.arcLength i - 1) := by
  have hcard := hI.1.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  rw [arcCutList_eq_append (X := X) (i := i) ζ, List.length_append, List.length_map,
    List.length_range, length_sideList_arc (X := X) (i := i) ζ, hcard]

/-- The entries of the cut list of a minimal interval `I` before position `c` are the legs at the
interior positions of `I`. -/
private theorem exists_getElem_arcCutList_eq_endDart {I : Finset (Fin (2 * b))}
    (hI : IsMinimalInterval X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {x : ℕ}
    (hx : x < (intervalInterior X.strandPerm i I).card) :
    ∃ r ∈ intervalInterior X.strandPerm i I,
      ∃ hx : x < (X.arcCutList i ζ).length, (X.arcCutList i ζ)[x] = X.endDart r := by
  have hcard := hI.1.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  have hlen := length_arcCutList_of_isMinimalInterval hI hζ
  have hL := arcCutList_eq_append (X := X) (i := i) ζ
  refine ⟨(finRotate (2 * b) ^ (x + 1)) (X.arcSideStart i ζ),
    (hI.1.mem_intervalInterior_iff (X := X)).2 ⟨x, by rw [hζ]; omega, by rw [hζ]⟩,
    by omega, ?_⟩
  have : (X.arcCutList i ζ)[x]? =
      some (X.endDart ((finRotate (2 * b) ^ (x + 1)) (X.arcSideStart i ζ))) := by
    rw [hL, List.getElem?_append_left (by simp; omega), List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  rwa [List.getElem?_eq_getElem (by omega), Option.some.injEq] at this

/-- The entries of the cut list of a minimal interval `I` from position `c` on are the darts of the
`ζ` list of `S`. -/
private theorem getElem_arcCutList_mem_sideList {I : Finset (Fin (2 * b))}
    (hI : IsMinimalInterval X.strandPerm i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {x : ℕ} (hx : x < (X.arcCutList i ζ).length)
    (hcx : (intervalInterior X.strandPerm i I).card ≤ x) :
    (X.arcCutList i ζ)[x] ∈ X.sideList ζ (X.arc i) := by
  have hcard := hI.1.card_intervalInterior_eq (X := X)
  rw [hζ] at hcard
  have : (X.arcCutList i ζ)[x]? =
      (X.sideList ζ (X.arc i))[x - (intervalInterior X.strandPerm i I).card]? := by
    rw [arcCutList_eq_append (X := X) (i := i) ζ, List.getElem?_append_right (by simp; omega),
      List.length_map, List.length_range, hcard]
  rw [List.getElem?_eq_getElem hx] at this
  exact List.mem_of_getElem? this.symm

/-- Without returning path on side `ζ`, exactly one end of each arc of the cut along a minimal
interval `I` is a leg at an interior position of `I`. -/
private theorem cutEndIndex_sourceIndex_lt_card_iff (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {I : Finset (Fin (2 * b))} (hI : IsMinimalInterval X.strandPerm i I)
    {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ)
    (hN : 2 ≤ (X.arcCutList i ζ).length) (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c)
    (j : Fin ((X.arcCutList i ζ).length / 2)) :
    (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) <
        (intervalInterior X.strandPerm i I).card ↔
      ¬(cutEndIndex (X.arcCutList i ζ) ζ.cutShift
        (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ) <
          (intervalInterior X.strandPerm i I).card := by
  obtain ⟨Q, hQ, hP, hhead, hlast⟩ := arc_arcCut_ends hX hS hN j
  constructor
  · intro hs ht
    obtain ⟨r, hr, hx, hfr⟩ := exists_getElem_arcCutList_eq_endDart hI hζ hs
    obtain ⟨r', hr', hx', hfr'⟩ := exists_getElem_arcCutList_eq_endDart hI hζ ht
    rw [hfr] at hhead
    rw [hfr'] at hlast
    obtain ⟨q, hq, hqr⟩ := Option.map_eq_some_iff.1 hlast
    have hout := hP.isOut_eq_true _ (List.mem_of_head? hhead)
    obtain ⟨j', rfl⟩ | ⟨j', rfl⟩ := exists_sourceIndex_or_targetIndex r
    swap
    · rw [hX.isOut_target] at hout
      exact Bool.false_ne_true hout
    have harc := eq_arc_of_isStrandPath hP hhead (fun e he => by
      rw [hq, Option.mem_def, Option.some.injEq] at he
      subst he
      change X.IsBoundaryVertex (X.vertexOf (X.inv q))
      rw [hqr]
      exact (X.mem_boundaryVertices.1 (hX.endpoint_mem r')).2)
    have hm := hX.toIsPreTripleDiagram.arcLength_ne_zero j'
    have hlast' : (X.arc j').getLast? = some (X.arcDart j' (X.arcLength j' - 1)) := by
      rw [List.getLast?_eq_getElem?, length_arc,
        List.getElem?_eq_getElem (by rw [length_arc]; omega), getElem_arc]
    rw [← harc, hq, Option.some.injEq] at hlast'
    have hend := endDart_arcEndIndex hX j'
    rw [← hlast', hqr] at hend
    have hq' : X.arcEndIndex j' = r' := hX.endpoint_injective (by
      rw [endpoint, endpoint, hend])
    have hne : j' ≠ i := by
      rintro rfl
      simp [intervalInterior] at hr
    apply hI.2 j' hne
    refine ⟨(mem_sdiff.1 hr).1, ?_⟩
    change X.arcEndIndex j' ∈ I
    rw [hq']
    exact (mem_sdiff.1 hr').1
  · intro ht
    by_contra hs
    obtain ⟨f', hf', hlast⟩ := Option.map_eq_some_iff.1 hlast
    obtain ⟨a', c', hR⟩ := (hS.exists_isReturningPath_iff hX ζ hN (Q.map Subtype.val)).2
      ⟨⟨Q, j, rfl, hQ⟩, fun f hf => by
        rw [hhead, Option.mem_def, Option.some.injEq] at hf
        rw [← hf]
        exact getElem_arcCutList_mem_sideList hI hζ _ (by omega),
      fun f hf => by
        rw [hf', Option.mem_def, Option.some.injEq] at hf
        rw [← hf, hlast]
        exact getElem_arcCutList_mem_sideList hI hζ _ (by omega)⟩
    exact hret _ a' c' hR

/-- The map exchanging the two ends of each arc of a triple diagram is an involution of its
endpoint indices. -/
private theorem exists_involutive_swap_arcEnds {H' : Type*} [Fintype H'] [DecidableEq H']
    {n : ℕ} {Y : TripleData H' n} (hY : Y.IsTripleDiagram) :
    ∃ ω : Fin (2 * n) → Fin (2 * n), Function.Involutive ω ∧
      (∀ j, ω (sourceIndex j) = targetIndex (Y.strandPerm j)) ∧
      ∀ j, ω (targetIndex (Y.strandPerm j)) = sourceIndex j := by
  have hπ : Function.Bijective Y.strandPerm :=
    Finite.injective_iff_bijective.1 (strandPerm_injective' hY)
  set e := Equiv.ofBijective _ hπ
  let ω : Fin (2 * n) → Fin (2 * n) := fun r =>
    if (r : ℕ) % 2 = 0 then targetIndex (Y.strandPerm ⟨r / 2, by omega⟩)
    else sourceIndex (e.symm ⟨r / 2, by omega⟩)
  have hωs : ∀ j, ω (sourceIndex j) = targetIndex (Y.strandPerm j) := by
    intro j
    dsimp only [ω]
    rw [if_pos (by rw [sourceIndex_val]; omega)]
    congr 2
    exact Fin.ext (by simp)
  have hωt : ∀ j, ω (targetIndex (Y.strandPerm j)) = sourceIndex j := by
    intro j
    dsimp only [ω]
    rw [if_neg (by rw [targetIndex_val]; omega)]
    congr 1
    rw [Equiv.symm_apply_eq]
    change _ = Y.strandPerm j
    apply Fin.ext
    change ((targetIndex (Y.strandPerm j) : Fin _) : ℕ) / 2 = _
    rw [targetIndex_val]
    omega
  refine ⟨ω, fun r => ?_, hωs, hωt⟩
  obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := exists_sourceIndex_or_targetIndex r
  · rw [hωs, hωt]
  · obtain ⟨j', rfl⟩ := hπ.2 j
    rw [hωt, hωs]

omit [Fintype H] [DecidableEq H] in
/-- The endpoint indices of a cut whose entry in the cut list `L` lies before position `c ≤ |L|`
number `c`. -/
private theorem card_filter_cutEndIndex_lt {L : List H} {s c : ℕ} (hev : Even L.length)
    (hc : c ≤ L.length) :
    ((univ : Finset (Fin (2 * (L.length / 2)))).filter
      fun r => (cutEndIndex L s r : ℕ) < c).card = c := by
  have hbij : Function.Bijective (cutEndIndex (H := H) L s) :=
    ⟨cutEndIndex_injective, cutEndIndex_surjective hev⟩
  have : ((univ : Finset (Fin (2 * (L.length / 2)))).filter
      fun r => (cutEndIndex L s r : ℕ) < c).map ⟨_, hbij.1⟩ =
      univ.filter fun x : Fin L.length => (x : ℕ) < c := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hx
      obtain ⟨r, rfl⟩ := hbij.2 x
      exact ⟨r, hx, rfl⟩
  rw [← card_map ⟨_, hbij.1⟩, this, Fin.card_filter_val_lt]
  omega

/-- **Arcs of the cut along `I`**. Let `I` be a minimal interval of `i` with side `ζ`, and let the
arc `S` from `s_i` be simple with `N_ζ ≥ 2` and without returning path on side `ζ`. Then every arc
of `X|_{S,ζ}` (a list `Q` of darts of `H_ζ(S)`) joins a leg `n_r` at an interior position `r` of
`I` to a dart of the `ζ` list of `S`: its first dart `f` and the reverse of its last dart `f'` are
such a leg and such a dart, in either order. -/
@[cluster_algebras "lem_cut_along_interval_arcs"]
theorem IsSimpleArc.exists_arc_arcCut_of_isMinimalInterval (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {I : Finset (Fin (2 * b))} (hI : IsMinimalInterval X.strandPerm i I)
    {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ)
    (hN : 2 ≤ (X.arcCutList i ζ).length) (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c)
    (j : Fin ((X.arcCutList i ζ).length / 2)) :
    ∃ Q : List {d // d ∈ X.arcSideDarts i ζ}, Q.map Sum.inl = (X.arcCut i ζ).arc j ∧
      ∃ f f', (Q.map Subtype.val).head? = some f ∧ (Q.map Subtype.val).getLast? = some f' ∧
        ((∃ r ∈ intervalInterior X.strandPerm i I, f = X.endDart r) ∧
            X.inv f' ∈ X.sideList ζ (X.arc i) ∨
          f ∈ X.sideList ζ (X.arc i) ∧
            ∃ r ∈ intervalInterior X.strandPerm i I, X.inv f' = X.endDart r) := by
  obtain ⟨Q, hQ, -, hhead, hlast⟩ := arc_arcCut_ends hX hS hN j
  obtain ⟨f', hf', hlast⟩ := Option.map_eq_some_iff.1 hlast
  refine ⟨Q, hQ, _, f', hhead, hf', ?_⟩
  have hcase := cutEndIndex_sourceIndex_lt_card_iff hX hS hI hζ hN hret j
  by_cases hs : (cutEndIndex (X.arcCutList i ζ) ζ.cutShift (sourceIndex j) : ℕ) <
      (intervalInterior X.strandPerm i I).card
  · have ht := hcase.1 hs
    obtain ⟨r, hr, hx, hfr⟩ := exists_getElem_arcCutList_eq_endDart hI hζ hs
    exact Or.inl ⟨⟨r, hr, hfr⟩, by
      rw [hlast]
      exact getElem_arcCutList_mem_sideList hI hζ _ (by omega)⟩
  · have ht : (cutEndIndex (X.arcCutList i ζ) ζ.cutShift
        (targetIndex ((X.arcCut i ζ).strandPerm j)) : ℕ) <
          (intervalInterior X.strandPerm i I).card :=
      not_not.1 (mt hcase.2 hs)
    obtain ⟨r, hr, hx, hfr⟩ := exists_getElem_arcCutList_eq_endDart hI hζ ht
    exact Or.inr ⟨getElem_arcCutList_mem_sideList hI hζ _ (by omega), r, hr, by rw [hlast, hfr]⟩

/-- **Arcs of the cut along `I`**: under the hypotheses of
`IsSimpleArc.exists_arc_arcCut_of_isMinimalInterval`, `S` passes through exactly `k` triple points,
where `2k` is the number of interior positions of `I`. -/
@[cluster_algebras "lem_cut_along_interval_arcs"]
theorem IsSimpleArc.two_mul_ncard_passesThrough_of_isMinimalInterval (hX : X.IsTripleDiagram)
    (hS : X.IsSimpleArc i) {I : Finset (Fin (2 * b))} (hI : IsMinimalInterval X.strandPerm i I)
    {ζ : StrandSide} (hζ : intervalSide X.strandPerm i I = ζ)
    (hN : 2 ≤ (X.arcCutList i ζ).length) (hret : ∀ Q a c, ¬X.IsReturningPath (X.arc i) ζ Q a c) :
    2 * {v | X.PassesThrough (X.arc i).toFinset v}.ncard =
      (intervalInterior X.strandPerm i I).card := by
  rw [hS.ncard_passesThrough hX]
  have hY := hS.isTripleDiagram_arcCut hX ζ hN
  have hcase := cutEndIndex_sourceIndex_lt_card_iff hX hS hI hζ hN hret
  have hlen := length_arcCutList_of_isMinimalInterval hI hζ
  have hev : Even (X.arcCutList i ζ).length := even_length_arcCutList ζ
  have h2 := Nat.two_mul_div_two_of_even hev
  obtain ⟨ω, hωω, hωs, hωt⟩ := exists_involutive_swap_arcEnds hY
  have hπ : Function.Surjective (X.arcCut i ζ).strandPerm :=
    (Finite.injective_iff_bijective.1 (strandPerm_injective' hY)).2
  set P := (univ : Finset (Fin (2 * ((X.arcCutList i ζ).length / 2)))).filter
    fun r => (cutEndIndex (X.arcCutList i ζ) ζ.cutShift r : ℕ) <
      (intervalInterior X.strandPerm i I).card with hPdef
  have hωP : ∀ r, ω r ∈ P ↔ r ∉ P := by
    intro r
    simp only [hPdef, mem_filter, mem_univ, true_and]
    obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := exists_sourceIndex_or_targetIndex r
    · rw [hωs]
      exact iff_not_comm.1 (hcase j)
    · obtain ⟨j', rfl⟩ := hπ j
      rw [hωt]
      exact hcase j'
  have hPc : P.card + Pᶜ.card = (X.arcCutList i ζ).length := by
    rw [card_add_card_compl, Fintype.card_fin, h2]
  have hPP := card_eq_card_compl_of_involutive hωω hωP
  have hPcard : P.card = (intervalInterior X.strandPerm i I).card := by
    rw [hPdef]
    exact card_filter_cutEndIndex_lt hev (by omega)
  omega

end ArcsOfCut

end TripleData

/-! ### The cut on the side opposite to a boundary-parallel arc -/

namespace TripleData

section OppositeCut

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ} {X : TripleData H b} {i : Fin b}

/-- The first end of the run on the opposite side of an arc is the second end of the run on the
side `ζ`. -/
@[simp]
theorem arcSideStart_opposite (ζ : StrandSide) :
    X.arcSideStart i ζ.opposite = X.arcSideEnd i ζ := by
  cases ζ <;> rfl

/-- The second end of the run on the opposite side of an arc is the first end of the run on the
side `ζ`. -/
@[simp]
theorem arcSideEnd_opposite (ζ : StrandSide) :
    X.arcSideEnd i ζ.opposite = X.arcSideStart i ζ := by
  cases ζ <;> rfl

/-- The two ends of the run of positions on either side of an arc are distinct. -/
theorem arcSideStart_ne_arcSideEnd (ζ : StrandSide) : X.arcSideStart i ζ ≠ X.arcSideEnd i ζ := by
  cases ζ
  · exact sourceIndex_ne_targetIndex _ _ |>.symm
  · exact sourceIndex_ne_targetIndex _ _

private theorem val_sub_add_val_sub {n : ℕ} {a c : Fin n} (h : a ≠ c) :
    ((a - c : Fin n) : ℕ) + ((c - a : Fin n) : ℕ) = n := by
  have h' : (a : ℕ) ≠ c := fun e => h (Fin.ext e)
  rw [fin_val_sub, fin_val_sub]
  have := a.isLt
  have := c.isLt
  split_ifs <;> omega

private theorem pos_val_sub {n : ℕ} {a c : Fin n} (h : a ≠ c) : 0 < ((a - c : Fin n) : ℕ) :=
  Nat.pos_of_ne_zero fun h' => h (val_sub_eq_zero_iff.1 h')

/-- The numbers of positions on the two sides of the arc from `s_i` add up to `2b - 2`. -/
theorem val_sub_arcSide_add (ζ : StrandSide) :
    ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1 +
      (((X.arcSideEnd i ζ.opposite - X.arcSideStart i ζ.opposite : Fin (2 * b)) : ℕ) - 1) =
        2 * b - 2 := by
  rw [arcSideStart_opposite, arcSideEnd_opposite]
  have h := val_sub_add_val_sub (arcSideStart_ne_arcSideEnd (X := X) (i := i) ζ).symm
  have h1 := pos_val_sub (arcSideStart_ne_arcSideEnd (X := X) (i := i) ζ).symm
  have h2 := pos_val_sub (arcSideStart_ne_arcSideEnd (X := X) (i := i) ζ)
  omega

/-- Every position other than `p` and `q` lies strictly between the ends of the run of one of the
two sides. -/
theorem exists_eq_finRotate_pow_arcSideStart {r : Fin (2 * b)} (hp : r ≠ sourceIndex i)
    (hq : r ≠ X.arcEndIndex i) (ζ : StrandSide) :
    (∃ u, u + 1 < ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) ∧
        r = (finRotate (2 * b) ^ (u + 1)) (X.arcSideStart i ζ)) ∨
      ∃ t, t + 1 < ((X.arcSideEnd i ζ.opposite - X.arcSideStart i ζ.opposite : Fin (2 * b)) : ℕ) ∧
        r = (finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ.opposite) := by
  rw [← mem_cyclicIcc_sdiff_iff, ← mem_cyclicIcc_sdiff_iff, arcSideStart_opposite,
    arcSideEnd_opposite]
  have hne := arcSideStart_ne_arcSideEnd (X := X) (i := i) ζ
  have hpq : r ∉ ({X.arcSideStart i ζ, X.arcSideEnd i ζ} : Finset (Fin (2 * b))) := by
    rw [mem_insert, mem_singleton]
    rintro (h | h) <;> cases ζ <;> simp_all [arcSideStart, arcSideEnd]
  have hpq' : r ∉ ({X.arcSideEnd i ζ, X.arcSideStart i ζ} : Finset (Fin (2 * b))) := by
    rwa [pair_comm]
  have hu := cyclicIcc_union_cyclicIcc hne
  have hr : r ∈ cyclicIcc (X.arcSideStart i ζ) (X.arcSideEnd i ζ) ∪
      cyclicIcc (X.arcSideEnd i ζ) (X.arcSideStart i ζ) := by
    rw [hu]
    exact mem_univ _
  rcases mem_union.1 hr with h | h
  · exact Or.inl (mem_sdiff.2 ⟨h, hpq⟩)
  · exact Or.inr (mem_sdiff.2 ⟨h, hpq'⟩)

/-- The legs of the cut list: entry `t` of the `ζ` cut list is the leg at the position `t + 1`
steps clockwise from `arcSideStart i ζ`. -/
theorem getElem?_arcCutList_of_lt (ζ : StrandSide) {t : ℕ}
    (ht : t + 1 < ((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ)) :
    (X.arcCutList i ζ)[t]? =
      some (X.endDart ((finRotate (2 * b) ^ (t + 1)) (X.arcSideStart i ζ))) := by
  rw [arcCutList_eq_append, List.getElem?_append_left (by simp; omega), List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

/-- The `ζ` list sits at the end of the `ζ` cut list. -/
theorem getElem?_arcCutList_add (ζ : StrandSide) (j : ℕ) :
    (X.arcCutList i ζ)[((X.arcSideEnd i ζ - X.arcSideStart i ζ : Fin (2 * b)) : ℕ) - 1 + j]? =
      (X.sideList ζ (X.arc i))[j]? := by
  rw [arcCutList_eq_append, List.getElem?_append_right (by simp), List.length_map,
    List.length_range, Nat.add_sub_cancel_left]

/-- For an arc boundary-parallel along `I` with side `ζ` and `u < 2k`, the dart `σ³ n̄_r` opposite
to `n̄_r` at the point of the arc of the interior position `r = A + u + 1` (`A` the start of the
run of `I`) is the entry of the opposite cut list of index `c + u ⊕ 1`, `c` the number of positions
on the opposite side. -/
theorem IsBoundaryParallel.getElem?_arcCutList_opposite (hX : X.IsTripleDiagram)
    {I : Finset (Fin (2 * b))} (hB : X.IsBoundaryParallel i I) {ζ : StrandSide}
    (hζ : intervalSide X.strandPerm i I = ζ) {u : ℕ} (hu : u < 2 * (X.arcLength i - 1)) :
    (X.arcCutList i ζ.opposite)[((X.arcSideEnd i ζ.opposite - X.arcSideStart i ζ.opposite :
        Fin (2 * b)) : ℕ) - 1 + (if u % 2 = 0 then u + 1 else u - 1)]? =
      some ((X.rot ^ 3) (X.inv (X.endDart ((finRotate (2 * b) ^ (u + 1))
        (X.arcSideStart i ζ))))) := by
  rw [getElem?_arcCutList_add]
  have hSL := length_sideList_arc (X := X) (i := i) ζ.opposite
  have hσ : ∀ l, l + 1 < X.arcLength i → ∀ m n : ℕ,
      (X.rot ^ m) ((X.rot ^ n) (X.inv (X.arcDart i l))) =
        (X.rot ^ ((m + n) % 6)) (X.inv (X.arcDart i l)) := by
    intro l hl m n
    rw [← Equiv.Perm.mul_apply, ← pow_add,
      hX.toIsPreTripleDiagram.rot_pow_mod_six (not_runsToEndpoint_arcDart' hX hl)]
  have hI := hB.1.eq_cyclicIcc_arcSide (X := X)
  rw [hζ] at hI
  obtain ⟨l, hl, rfl | rfl⟩ : ∃ l, l + 1 < X.arcLength i ∧ (u = 2 * l ∨ u = 2 * l + 1) :=
    ⟨u / 2, by omega, by omega⟩
  · rw [if_pos (by omega), List.getElem?_eq_getElem (by rw [hSL]; omega)]
    cases ζ
    · have hf := (hB.inv_endDart_of_eq_cyclicIcc' hX hI hl).1
      simp only [StrandSide.opposite_right]
      rw [getElem_sideList_arc_left, show X.arcSideStart i .right =
        targetIndex (X.strandPerm i) from rfl, hf, hσ _ (by omega),
        show (2 * l + 1) % 2 + 4 = (3 + 2) % 6 by omega,
        show X.arcLength i - 1 - 1 - (2 * l + 1) / 2 = X.arcLength i - 2 - l by omega]
    · have hf := (hB.inv_endDart_of_eq_cyclicIcc hX hI hl).1
      simp only [StrandSide.opposite_left]
      rw [getElem_sideList_arc_right, show X.arcSideStart i .left = sourceIndex i from rfl, hf,
        hσ _ hl, show (2 * l + 1) % 2 + 1 = (3 + 5) % 6 by omega,
        show (2 * l + 1) / 2 = l by omega]
  · rw [if_neg (by omega), List.getElem?_eq_getElem (by rw [hSL]; omega)]
    cases ζ
    · have hf := (hB.inv_endDart_of_eq_cyclicIcc' hX hI hl).2
      simp only [StrandSide.opposite_right]
      have hf' : X.inv (X.endDart ((finRotate (2 * b) ^ (2 * l + 2))
          (targetIndex (X.strandPerm i)))) =
          (X.rot ^ 1) (X.inv (X.arcDart i (X.arcLength i - 2 - l))) := by
        rwa [pow_one]
      rw [getElem_sideList_arc_left, show X.arcSideStart i .right =
        targetIndex (X.strandPerm i) from rfl, show 2 * l + 1 + 1 = 2 * l + 2 by ring, hf',
        hσ _ (by omega), show (2 * l + 1 - 1) % 2 + 4 = (3 + 1) % 6 by omega,
        show X.arcLength i - 1 - 1 - (2 * l + 1 - 1) / 2 = X.arcLength i - 2 - l by omega]
    · have hf := (hB.inv_endDart_of_eq_cyclicIcc hX hI hl).2
      simp only [StrandSide.opposite_left]
      rw [getElem_sideList_arc_right, show X.arcSideStart i .left = sourceIndex i from rfl,
        show 2 * l + 1 + 1 = 2 * l + 2 by ring, hf, hσ _ hl,
        show (2 * l + 1 - 1) % 2 + 1 = (3 + 4) % 6 by omega,
        show (2 * l + 1 - 1) / 2 = l by omega]

end OppositeCut

end TripleData

end ClusterAlgebras
