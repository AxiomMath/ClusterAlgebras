/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BoundaryParallelCuts
public import ClusterAlgebras.Plabic.Straighten

/-!
# Monogon-stable triple diagrams with the same strand permutation are move-equivalent

Two monogon-stable triple diagrams `X, X'` with `b` arcs and the same strand permutation `π` are
move-equivalent. This is one implication of the straightening theorem of FWZ, proved without
reference to standard diagrams, by induction on `b`.

Choose an interval `I` of `π`, of `i` say, with as few positions as possible; it is a minimal
interval, since an interval containing both ends of another pair contains one of the two
intervals of that pair, which is then strictly smaller. By straightening, `X ∼ X₁` and
`X' ∼ X'₁` where the arcs `S, S'` from `s_i` are boundary-parallel along `I`. Let `η` be the side
opposite to `I`. The cuts `X₁|_{S,η}` and `X'₁|_{S',η}` have `b - 1` arcs and the same strand
permutation. If `b = 1` they have no darts at all, and gluing gives `X₁ ≅ X'₁`. If `b ≥ 2` they
are monogon-stable triple diagrams, hence move-equivalent by induction; lifting the moves gives
`X₂ ∼ X₁` whose arc from `s_i` is still `S`, still boundary-parallel along `I`, with
`X₂|_{S,η} ≅ X'₁|_{S',η}`, and gluing gives `X₂ ≅ X'₁`.

## Main results

* `ClusterAlgebras.TripleDiagram.IsMonogonStable.moveEquivalent_of_strandPerm_eq`: monogon-stable
  triple diagrams with the same number of arcs and the same strand permutation are
  move-equivalent.

## Implementation notes

* The case `b = 1` is not treated through the explicit description of a triple diagram with one
  arc and no triple point: the cut on the side `η` of an arc boundary-parallel along an interval
  with no interior position has an empty cut list, hence no darts, and the gluing lemma applies
  to two such empty cuts.
* The number of arcs of a cut is `N_η / 2`, which equals `b - 1` only propositionally; the
  induction is a strong induction on `b`, and the second cut is transported to the number of arcs
  of the first.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Minimal intervals exist -/

section MinimalInterval

private theorem val_sub_eq_ite' {n : ℕ} (p a : Fin n) :
    ((p - a : Fin n) : ℕ) = if (a : ℕ) ≤ p then (p : ℕ) - a else n - a + p := by
  rw [Fin.val_sub]
  have := a.isLt
  have := p.isLt
  split_ifs with h
  · rw [show n - (a : ℕ) + p = (p - a) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- If `x` comes no later than `y` in the cyclic interval from `a` to `c`, the cyclic interval
from `x` to `y` is strictly smaller, unless `x = a` and `y = c`. -/
private theorem card_cyclicIcc_lt {n : ℕ} [NeZero n] {a c x y : Fin n}
    (hy : y ∈ cyclicIcc a c) (hxy : ((x - a : Fin n) : ℕ) ≤ (y - a : Fin n))
    (hne : ¬(x = a ∧ y = c)) : (cyclicIcc x y).card < (cyclicIcc a c).card := by
  rw [card_cyclicIcc, card_cyclicIcc]
  rw [mem_cyclicIcc, Fin.le_def] at hy
  simp only [Fin.ext_iff] at hne
  simp only [val_sub_eq_ite'] at hy hxy ⊢
  have := a.isLt
  have := c.isLt
  have := x.isLt
  have := y.isLt
  split_ifs at hy hxy ⊢ <;> omega

/-- Every map `π : Fin b → Fin b` with `b ≠ 0` has a minimal interval. -/
private theorem exists_isMinimalInterval {b : ℕ} [NeZero b] (π : Fin b → Fin b) :
    ∃ i I, IsMinimalInterval π i I := by
  haveI : NeZero (2 * b) := ⟨by have := NeZero.ne b; omega⟩
  let f : Fin b × Bool → Finset (Fin (2 * b)) := fun p =>
    cond p.2 (cyclicIcc (sourceIndex p.1) (targetIndex (π p.1)))
      (cyclicIcc (targetIndex (π p.1)) (sourceIndex p.1))
  have hf : ∀ p, IsIntervalOf π p.1 (f p) := by
    rintro ⟨i, _ | _⟩
    exacts [Or.inr rfl, Or.inl rfl]
  obtain ⟨p, -, hp⟩ := exists_min_image univ (fun p => (f p).card) univ_nonempty
  refine ⟨p.1, f p, hf p, fun j hj ⟨hsj, htj⟩ => ?_⟩
  have main : ∀ a c, f p = cyclicIcc a c →
      (a = sourceIndex p.1 ∧ c = targetIndex (π p.1)) ∨
        (a = targetIndex (π p.1) ∧ c = sourceIndex p.1) → False := by
    intro a c hac hends
    rw [hac] at hsj htj
    by_cases hle : ((sourceIndex j - a : Fin (2 * b)) : ℕ) ≤ (targetIndex (π j) - a : Fin (2 * b))
    · have hlt := card_cyclicIcc_lt (x := sourceIndex j) htj hle (by
        rintro ⟨h1, h2⟩
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hj (sourceIndex_injective h1)
        · exact sourceIndex_ne_targetIndex _ _ h1)
      have h : (f p).card ≤ (cyclicIcc (sourceIndex j) (targetIndex (π j))).card :=
        hp (j, true) (mem_univ _)
      rw [← hac] at hlt
      omega
    · have hlt := card_cyclicIcc_lt (x := targetIndex (π j)) hsj (by omega) (by
        rintro ⟨h1, h2⟩
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact sourceIndex_ne_targetIndex _ _ h1.symm
        · exact hj (sourceIndex_injective h2))
      have h : (f p).card ≤ (cyclicIcc (targetIndex (π j)) (sourceIndex j)).card :=
        hp (j, false) (mem_univ _)
      rw [← hac] at hlt
      omega
  rcases hf p with h | h
  · exact main _ _ h (Or.inl ⟨rfl, rfl⟩)
  · exact main _ _ h (Or.inr ⟨rfl, rfl⟩)

end MinimalInterval

/-! ### Empty cuts and transport along the number of arcs -/

namespace TripleData

section Helpers

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

/-- A side of a simple arc whose cut list is empty has no darts. -/
private theorem arcSideDarts_eq_empty_of_arcCutList_eq_nil {X : TripleData H b} {i : Fin b}
    (hX : X.IsTripleDiagram) (hS : X.IsSimpleArc i) {ζ : StrandSide}
    (h : X.arcCutList i ζ = []) : X.arcSideDarts i ζ = ∅ := by
  have hc := hS.isCutData_arcCutList hX ζ
  by_contra hne
  obtain ⟨d, hd⟩ := nonempty_iff_ne_empty.2 hne
  have hall : ∀ e, X.toRotationSystem.Reach d e → e ∈ X.arcSideDarts i ζ := by
    intro e he
    induction he with
    | refl => exact hd
    | rot _ ih => exact (hc.mem_of_mem_vertexOf _ ih (by simp [h]) _ (X.rot_mem_vertexOf _)).1
    | inv _ ih => exact hc.inv_mem _ ih
  let r : Fin (2 * b) := ⟨0, by have := hX.one_le; omega⟩
  exact hc.not_isBoundaryVertex _ (hall (X.endDart r) (hX.toIsDiskMap.toIsConnected.reach d _))
    (by simp [h]) (X.mem_boundaryVertices.1 (hX.endpoint_mem r)).2

omit [Fintype H] [DecidableEq H] in
/-- The darts of a cut with no darts on the side and an empty cut list form an empty type. -/
private theorem isEmpty_cutDart {K : Finset H} {N : ℕ} (hK : K = ∅) (hN : N = 0) :
    IsEmpty (CutDart K N) := by
  subst hK hN
  constructor
  rintro (⟨d, hd⟩ | ⟨k, _⟩)
  · simp at hd
  · exact k.elim0

/-- Triple data with no arcs on empty sets of darts are isomorphic. -/
private theorem hIsomorphic_of_isEmpty {H₁ H₂ : Type*} [Fintype H₁] [DecidableEq H₁]
    [Fintype H₂] [DecidableEq H₂] [IsEmpty H₁] [IsEmpty H₂] {m m' : ℕ} (Y : TripleData H₁ m)
    (Y' : TripleData H₂ m') (hm : m = 0) (hm' : m' = 0) : Y.HIsomorphic Y' := by
  subst hm hm'
  exact Isomorphic.hIsomorphic
    ⟨{ toEquiv := Equiv.equivOfIsEmpty H₁ H₂
       map_inv := isEmptyElim
       map_rot := isEmptyElim
       mem_bdry_iff := isEmptyElim
       map_isOut := isEmptyElim
       map_endpoint := fun r => absurd r.isLt (by simp) }⟩

/-- Two rotation systems whose rotations agree on the vertex of `e` have the same vertex at `e`. -/
private theorem vertexOf_eq_of_rot_eq {R R' : RotationSystem H} {e : H}
    (h : ∀ d ∈ R.vertexOf e, R'.rot d = R.rot d) : R'.vertexOf e = R.vertexOf e := by
  have key : ∀ n : ℕ, (R'.rot ^ n) e = (R.rot ^ n) e ∧ (R.rot ^ n) e ∈ R.vertexOf e := by
    intro n
    induction n with
    | zero => exact ⟨rfl, R.self_mem_vertexOf e⟩
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, h _ h2]
      refine ⟨rfl, ?_⟩
      rw [← R.vertexOf_eq_of_mem h2]
      exact R.rot_mem_vertexOf _
  ext x
  rw [R'.mem_vertexOf, R.mem_vertexOf]
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := hx.exists_nat_pow_eq
    rw [(key n).1]
    exact ⟨n, by simp⟩
  · intro hx
    obtain ⟨n, rfl⟩ := hx.exists_nat_pow_eq
    rw [← (key n).1]
    exact ⟨n, by simp⟩

/-- **Boundary-parallel arcs survive a lift.** If `X'` has the involution, `B` and legs of `X`, a
rotation agreeing with that of `X` at every dart not lying at a triple point avoided by the arc
`S` from `s_i`, the same arc `S` (simple) and the same strand permutation, and `S` is
boundary-parallel along `I` in `X`, then it is boundary-parallel along `I` in `X'`. -/
private theorem isBoundaryParallel_of_lift {X X' : TripleData H b} {i : Fin b}
    (hX : X.IsTripleDiagram) (hX' : X'.IsTripleDiagram) (hπ : X'.strandPerm = X.strandPerm)
    (hinv : X'.inv = X.inv) (hbdry : X'.bdry = X.bdry) (hend : X'.endDart = X.endDart)
    (hrot : ∀ d, ¬(X.vertexOf d ∈ X.internalVertices ∧
      ¬X.PassesThrough (X.arc i).toFinset (X.vertexOf d)) → X'.rot d = X.rot d)
    (hS' : X'.IsSimpleArc i) (harc : X'.arc i = X.arc i) {I : Finset (Fin (2 * b))}
    (hB : X.IsBoundaryParallel i I) : X'.IsBoundaryParallel i I := by
  have hvert : ∀ v, X.PassesThrough (X.arc i).toFinset v → ∀ e ∈ v, X'.vertexOf e = v := by
    rintro v ⟨hv, d, hdS, rfl⟩ e he
    rw [← X.vertexOf_eq_of_mem he]
    refine vertexOf_eq_of_rot_eq (R := X.toRotationSystem) (R' := X'.toRotationSystem)
      fun x hx => hrot x ?_
    rintro ⟨-, hnot⟩
    rw [X.vertexOf_eq_of_mem hx, X.vertexOf_eq_of_mem he] at hnot
    exact hnot ⟨hv, d, hdS, rfl⟩
  have hpass : ∀ v, X.PassesThrough (X.arc i).toFinset v →
      X'.PassesThrough (X'.arc i).toFinset v := by
    rintro v ⟨hv, d, hd, rfl⟩
    have hd' := hvert _ ⟨hv, d, hd, rfl⟩ d (X.self_mem_vertexOf d)
    refine ⟨X'.mem_internalVertices.2 ⟨X'.mem_vertices.2 ⟨d, hd'⟩, ?_⟩, d, harc ▸ hd, hd'⟩
    have := (X.mem_internalVertices.1 hv).2
    unfold DiskMap.IsBoundaryVertex at this ⊢
    rwa [hbdry]
  refine ⟨hπ ▸ hB.1, hS', ?_, fun r hr => ?_⟩
  · rw [hS'.ncard_passesThrough hX', ← length_arc, harc, length_arc,
      ← hB.2.1.ncard_passesThrough hX, hπ]
    exact hB.2.2.1
  · rw [hπ] at hr
    have h := hB.2.2.2 r hr
    rw [hinv, hend, hvert _ h _ (X.self_mem_vertexOf _)]
    exact hpass _ h

end Helpers

end TripleData

namespace TripleDiagram

/-- A triple diagram transported along an equality of numbers of arcs is monogon-stable if the
original one is. -/
private theorem isMonogonStable_cast {m m' : ℕ} (h : m = m') {Z : TripleDiagram m}
    (hZ : Z.IsMonogonStable) : (h ▸ Z).IsMonogonStable := by
  subst h
  exact hZ

/-- A triple diagram transported along an equality of numbers of arcs is isomorphic to the
original one. -/
private theorem hIsomorphic_cast {m m' : ℕ} (h : m = m') (Z : TripleDiagram m) :
    (h ▸ Z).data.HIsomorphic Z.data := by
  subst h
  exact TripleData.Isomorphic.hIsomorphic (TripleData.Isomorphic.refl _)

/-- Transporting a triple diagram along an equality of numbers of arcs does not change its strand
permutation, read at corresponding indices. -/
private theorem strandPerm_cast {m m' : ℕ} (h : m = m') (Z : TripleDiagram m) (u : Fin m')
    (u' : Fin m) (hu : (u : ℕ) = u') : ((h ▸ Z).data.strandPerm u : ℕ) = Z.data.strandPerm u' := by
  subst h
  rw [Fin.ext hu]

/-- With fewer than two arcs, two triple diagrams with the same strand permutation and arcs from
`s_i` boundary-parallel along `I` have empty cuts on the opposite side, hence are isomorphic. -/
private theorem moveEquivalent_of_lt_two {b : ℕ} {X₁ X₁' : TripleDiagram b} {i : Fin b}
    {I : Finset (Fin (2 * b))} {η : StrandSide} (hb2 : b < 2)
    (hπ₁ : X₁.data.strandPerm = X₁'.data.strandPerm) (hB₁ : X₁.data.IsBoundaryParallel i I)
    (hB₁' : X₁'.data.IsBoundaryParallel i I)
    (hη : η = (intervalSide X₁.data.strandPerm i I).opposite) : X₁.MoveEquivalent X₁' := by
  obtain ⟨hlen, hlen', -⟩ :=
    hB₁.arcCut_strandPerm_eq X₁.isTripleDiagram X₁'.isTripleDiagram hπ₁ hB₁' hη
  have hnil : X₁.data.arcCutList i η = [] := List.eq_nil_of_length_eq_zero (by
    obtain ⟨k, hk⟩ := TripleData.even_length_arcCutList (X := X₁.data) (i := i) η
    omega)
  have hnil' : X₁'.data.arcCutList i η = [] := List.eq_nil_of_length_eq_zero (by
    obtain ⟨k, hk⟩ := TripleData.even_length_arcCutList (X := X₁'.data) (i := i) η
    omega)
  haveI := TripleData.isEmpty_cutDart (N := (X₁.data.arcCutList i η).length)
    (TripleData.arcSideDarts_eq_empty_of_arcCutList_eq_nil X₁.isTripleDiagram hB₁.2.1 hnil)
    (by simp [hnil])
  haveI := TripleData.isEmpty_cutDart (N := (X₁'.data.arcCutList i η).length)
    (TripleData.arcSideDarts_eq_empty_of_arcCutList_eq_nil X₁'.isTripleDiagram hB₁'.2.1 hnil')
    (by simp [hnil'])
  exact MoveEquivalent.of_isomorphic
    (hB₁.isomorphic_of_hIsomorphic_arcCut X₁.isTripleDiagram X₁'.isTripleDiagram
      (congrFun hπ₁ i) hB₁' hη (TripleData.hIsomorphic_of_isEmpty _ _ (by omega) (by omega)))

/-- With at least two arcs, two triple diagrams with the same strand permutation and arcs from
`s_i` boundary-parallel along `I` are move-equivalent, provided monogon-stable diagrams with fewer
arcs and equal strand permutations are. -/
private theorem moveEquivalent_of_two_le {b : ℕ} {X X' X₁ X₁' : TripleDiagram b} {i : Fin b}
    {I : Finset (Fin (2 * b))} {η : StrandSide} (hb2 : 2 ≤ b)
    (ih : ∀ m < b, ∀ {Y Y' : TripleDiagram m}, Y.IsMonogonStable → Y'.IsMonogonStable →
      Y.data.strandPerm = Y'.data.strandPerm → Y.MoveEquivalent Y')
    (hX : X.IsMonogonStable) (hX' : X'.IsMonogonStable) (hXX₁ : X.MoveEquivalent X₁)
    (hXX₁' : X'.MoveEquivalent X₁') (hπ₁ : X₁.data.strandPerm = X₁'.data.strandPerm)
    (hB₁ : X₁.data.IsBoundaryParallel i I) (hB₁' : X₁'.data.IsBoundaryParallel i I)
    (hη : η = (intervalSide X₁.data.strandPerm i I).opposite) : X₁.MoveEquivalent X₁' := by
  obtain ⟨hlen, hlen', hperm⟩ :=
    hB₁.arcCut_strandPerm_eq X₁.isTripleDiagram X₁'.isTripleDiagram hπ₁ hB₁' hη
  have hS := hB₁.2.1
  have hS' := hB₁'.2.1
  have hN : 2 ≤ (X₁.data.arcCutList i η).length := by omega
  have hN' : 2 ≤ (X₁'.data.arcCutList i η).length := by omega
  let Y : TripleDiagram ((X₁.data.arcCutList i η).length / 2) :=
    ⟨_, X₁.data.arcCut i η, hS.isTripleDiagram_arcCut X₁.isTripleDiagram η hN⟩
  let Y' : TripleDiagram ((X₁'.data.arcCutList i η).length / 2) :=
    ⟨_, X₁'.data.arcCut i η, hS'.isTripleDiagram_arcCut X₁'.isTripleDiagram η hN'⟩
  have hm : (X₁'.data.arcCutList i η).length / 2 = (X₁.data.arcCutList i η).length / 2 := by
    omega
  have hYs : Y.IsMonogonStable := hS.isMonogonStable_arcCut X₁.isTripleDiagram
    (fun W hW => hX W (hXX₁.trans hW)) η hN
  have hYs' : Y'.IsMonogonStable := hS'.isMonogonStable_arcCut X₁'.isTripleDiagram
    (fun W hW => hX' W (hXX₁'.trans hW)) η hN'
  have hYY : Y.MoveEquivalent (hm ▸ Y') := by
    refine ih _ (by omega) hYs (isMonogonStable_cast hm hYs') ?_
    funext u
    apply Fin.ext
    rw [strandPerm_cast hm Y' u ⟨u, by omega⟩ rfl]
    exact hperm u ⟨u, by omega⟩ rfl
  obtain ⟨X₂, hX₂, hX₁X₂, hinv, hbdry, hend, -, hrot, hS₂, harc, -, -, hiso⟩ :=
    hS.exists_moveEquivalent_hIsomorphic_arcCut X₁.isTripleDiagram η hN hYY
  have hπ₂ : X₂.strandPerm = X₁.data.strandPerm := hX₁X₂.strandPerm_eq
  have hB₂ : X₂.IsBoundaryParallel i I :=
    TripleData.isBoundaryParallel_of_lift X₁.isTripleDiagram hX₂ hπ₂ hinv hbdry hend hrot hS₂
      harc hB₁
  have hglue := hB₂.isomorphic_of_hIsomorphic_arcCut hX₂ X₁'.isTripleDiagram
    (by rw [hπ₂, hπ₁]) hB₁' (by rwa [hπ₂]) (hiso.trans (hIsomorphic_cast hm Y'))
  exact hX₁X₂.trans (MoveEquivalent.of_isomorphic (X := ⟨_, X₂, hX₂⟩) (X' := X₁') hglue)

/-! ### The theorem -/

/-- Let `X, X'` be monogon-stable triple diagrams with the same number `b` of arcs and
`π_X = π_{X'}`. Then `X ∼ X'`. -/
@[cluster_algebras "lem_monogon_stable_equivalent"]
theorem IsMonogonStable.moveEquivalent_of_strandPerm_eq {b : ℕ} {X X' : TripleDiagram b}
    (hX : X.IsMonogonStable) (hX' : X'.IsMonogonStable)
    (hπ : X.data.strandPerm = X'.data.strandPerm) : X.MoveEquivalent X' := by
  revert X X'
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro X X' hX hX' hπ
  have hb : 1 ≤ b := X.isTripleDiagram.one_le
  haveI : NeZero b := ⟨by omega⟩
  obtain ⟨i, I, hI⟩ := exists_isMinimalInterval X.data.strandPerm
  have hI' : X'.IsMinimalInterval i I := by
    change ClusterAlgebras.IsMinimalInterval X'.data.strandPerm i I
    rw [← hπ]
    exact hI
  obtain ⟨X₁, hXX₁, hB₁⟩ := hX.hasStraighteningProperty.2 i I hI
  obtain ⟨X₁', hXX₁', hB₁'⟩ := hX'.hasStraighteningProperty.2 i I hI'
  have hπ₁ : X₁.data.strandPerm = X₁'.data.strandPerm := by
    rw [hXX₁.strandPerm_eq, hXX₁'.strandPerm_eq, hπ]
  obtain ⟨η, hη⟩ : ∃ η, η = (intervalSide X₁.data.strandPerm i I).opposite := ⟨_, rfl⟩
  suffices h : X₁.MoveEquivalent X₁' from hXX₁.trans (h.trans hXX₁'.symm)
  rcases Nat.lt_or_ge b 2 with hb2 | hb2
  · exact moveEquivalent_of_lt_two hb2 hπ₁ hB₁ hB₁' hη
  · exact moveEquivalent_of_two_le hb2 ih hX hX' hXX₁ hXX₁' hπ₁ hB₁ hB₁' hη

end TripleDiagram

end ClusterAlgebras
