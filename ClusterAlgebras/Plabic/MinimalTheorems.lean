/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Defant
-/
module

public import ClusterAlgebras.Plabic.BadFeatures
public import ClusterAlgebras.Plabic.MinimalMonogon
public import ClusterAlgebras.Plabic.MonogonStableEquivalent
public import ClusterAlgebras.Plabic.ReturningPaths

/-!
# Minimal triple diagrams: the main theorems

This file collects the main results of Thurston's theory of minimal triple diagrams.

* Minimal triple diagrams are monogon-stable, and monogon-stable diagrams with the same strand
  permutation are move-equivalent; so any two minimal triple diagrams with the same number of
  arcs and the same strand permutation are move-equivalent.
* Conversely a monogon-stable diagram is move-equivalent to a diagram with the least number of
  triple points among those with its strand permutation, hence is minimal itself. Consequently a
  non-minimal triple diagram is move-equivalent to one with a hollow monogon.
* Standard triple diagrams, obtained by running a boundary-parallel strand along a minimal
  interval and continuing in the remaining disk, are minimal.
* A triple diagram is minimal if and only if it has no badgon: badgons propagate backwards along
  swivel moves, so a diagram with no badgon is monogon-stable.

## Main results

* `ClusterAlgebras.TripleDiagram.IsMinimal.moveEquivalent_of_strandPerm_eq`: minimal triple
  diagrams with the same strand permutation are move-equivalent.
* `ClusterAlgebras.TripleDiagram.IsMonogonStable.isMinimal`: monogon-stable diagrams are minimal.
* `ClusterAlgebras.TripleDiagram.exists_moveEquivalent_isHollowMonogon_of_not_isMinimal`: a
  non-minimal diagram is move-equivalent to one with a hollow monogon.
* `ClusterAlgebras.TripleDiagram.IsStandard.isMinimal`: standard triple diagrams are minimal.
* `ClusterAlgebras.TripleDiagram.isMinimal_iff_not_hasBadgon`: a triple diagram is minimal if and
  only if it has no badgon.

## Implementation notes

* The number of arcs of a cut is `N_η / 2`, which equals `b - 1` only propositionally; in the
  proof that standard diagrams are minimal, the cut of the standard diagram is transported to the
  number of arcs of the cut of the straightened minimal diagram.

## References

* [FWZ] S. Fomin, L. Williams, A. Zelevinsky, *Introduction to Cluster Algebras*, Chapter 7,
  arXiv:2106.02160.
-/

@[expose] public section

namespace ClusterAlgebras

open Finset

/-! ### Transport along lifts and along numbers of arcs -/

namespace TripleData

section Helpers

variable {H : Type*} [Fintype H] [DecidableEq H] {b : ℕ}

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
    simpa [DiskMap.IsBoundaryVertex, hbdry] using (X.mem_internalVertices.1 hv).2
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

variable {b : ℕ}

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

/-- The strand permutation of a triple diagram transported along an equality of numbers of
arcs. -/
private theorem strandPerm_cast {m m' : ℕ} (h : m = m') (Z : TripleDiagram m) (u : Fin m')
    (u' : Fin m) (hu : (u : ℕ) = u') : ((h ▸ Z).data.strandPerm u : ℕ) = Z.data.strandPerm u' := by
  subst h
  rw [Fin.ext hu]

/-! ### Existence of minimal diagrams -/

/-- Among the triple diagrams with `b` arcs and the strand permutation of `X`, some diagram is
minimal: one with the least number of triple points. -/
theorem exists_isMinimal_strandPerm_eq (X : TripleDiagram b) :
    ∃ Y : TripleDiagram b, Y.data.strandPerm = X.data.strandPerm ∧ Y.IsMinimal := by
  classical
  have hex : ∃ n, ∃ Y : TripleDiagram b, Y.data.strandPerm = X.data.strandPerm ∧
      Y.data.internalVertices.card = n := ⟨_, X, rfl, rfl⟩
  obtain ⟨Y, hY, hYn⟩ := Nat.find_spec hex
  refine ⟨Y, hY, fun Z hZ => ?_⟩
  rw [hYn]
  exact Nat.find_min' hex ⟨Z, hZ.trans hY, rfl⟩

/-! ### Minimal diagrams are move-equivalent -/

/-- **Minimal triple diagrams are move-equivalent**: any two minimal triple diagrams with the same
number of arcs and the same strand permutation are move-equivalent. -/
@[cluster_algebras "thm_minimal_move_equivalent"]
theorem IsMinimal.moveEquivalent_of_strandPerm_eq {X X' : TripleDiagram b} (hX : X.IsMinimal)
    (hX' : X'.IsMinimal) (hπ : X.data.strandPerm = X'.data.strandPerm) : X.MoveEquivalent X' :=
  hX.isMonogonStable.moveEquivalent_of_strandPerm_eq hX'.isMonogonStable hπ

/-- **Monogon-stable diagrams are minimal**: a monogon-stable triple diagram is minimal. -/
@[cluster_algebras "lem_monogon_stable_minimal"]
theorem IsMonogonStable.isMinimal {X : TripleDiagram b} (hX : X.IsMonogonStable) :
    X.IsMinimal := by
  obtain ⟨Y, hYX, hY⟩ := X.exists_isMinimal_strandPerm_eq
  exact hY.of_moveEquivalent (hY.isMonogonStable.moveEquivalent_of_strandPerm_eq hX hYX)

/-- **Non-minimal diagrams can be given a hollow monogon**: if `X` is not minimal, some triple
diagram move-equivalent to `X` has a hollow monogon. -/
@[cluster_algebras "lem_hollow_monogon"]
theorem exists_moveEquivalent_isHollowMonogon_of_not_isMinimal {X : TripleDiagram b}
    (hX : ¬X.IsMinimal) :
    ∃ X' : TripleDiagram b, X.MoveEquivalent X' ∧ ∃ c, X'.data.IsHollowMonogon {c} := by
  have hs : ¬X.IsMonogonStable := fun h => hX h.isMinimal
  simp only [IsMonogonStable, not_forall, not_not] at hs
  obtain ⟨X', hXX', hmono⟩ := hs
  obtain ⟨X'', hX'X'', hc⟩ := X'.exists_moveEquivalent_isHollowMonogon hmono
  exact ⟨X'', hXX'.trans hX'X'', hc⟩

/-! ### Standard diagrams are minimal -/

/-- Standard triple data satisfying the conditions of a triple diagram form a minimal triple
diagram. -/
private theorem isMinimal_of_isStandard {H : Type} [Fintype H] [DecidableEq H] {b : ℕ}
    {X : TripleData H b} (h : X.IsStandard) (hX : X.IsTripleDiagram) :
    IsMinimal ⟨H, X, hX⟩ := by
  induction h with
  | one X hX₀ h₀ =>
    intro Z _
    simp [h₀]
  | @cut H _ _ b X hX₀ hb i I hI hB _ ih =>
    obtain ⟨Y, hYX, hY⟩ := exists_isMinimal_strandPerm_eq ⟨H, X, hX⟩
    have hI' : Y.IsMinimalInterval i I := by
      change ClusterAlgebras.IsMinimalInterval Y.data.strandPerm i I
      rw [hYX]
      exact hI
    obtain ⟨Y₁, hYY₁, hB₁⟩ := hY.isMonogonStable.hasStraighteningProperty.2 i I hI'
    have hπ₁ : X.strandPerm = Y₁.data.strandPerm := by
      rw [hYY₁.strandPerm_eq, hYX]
    obtain ⟨hlen, hlen', hperm⟩ :=
      hB.arcCut_strandPerm_eq hX Y₁.isTripleDiagram hπ₁ hB₁ rfl
    have hS := hB.2.1
    have hS₁ := hB₁.2.1
    have hN : 2 ≤ (X.arcCutList i (intervalSide X.strandPerm i I).opposite).length := by omega
    have hN₁ : 2 ≤ (Y₁.data.arcCutList i (intervalSide X.strandPerm i I).opposite).length := by
      omega
    let C : TripleDiagram ((X.arcCutList i (intervalSide X.strandPerm i I).opposite).length / 2) :=
      ⟨_, X.arcCut i _, hS.isTripleDiagram_arcCut hX _ hN⟩
    let C₁ : TripleDiagram
        ((Y₁.data.arcCutList i (intervalSide X.strandPerm i I).opposite).length / 2) :=
      ⟨_, Y₁.data.arcCut i _, hS₁.isTripleDiagram_arcCut Y₁.isTripleDiagram _ hN₁⟩
    have hm : (X.arcCutList i (intervalSide X.strandPerm i I).opposite).length / 2 =
        (Y₁.data.arcCutList i (intervalSide X.strandPerm i I).opposite).length / 2 := by
      omega
    have hC₁s : C₁.IsMonogonStable :=
      hS₁.isMonogonStable_arcCut Y₁.isTripleDiagram
        (hY.of_moveEquivalent hYY₁).isMonogonStable _ hN₁
    have hCC : C₁.MoveEquivalent (hm ▸ C) := by
      refine hC₁s.moveEquivalent_of_strandPerm_eq (isMonogonStable_cast hm
        (ih (hS.isTripleDiagram_arcCut hX _ hN)).isMonogonStable) ?_
      funext u
      apply Fin.ext
      rw [strandPerm_cast hm C u ⟨u, by omega⟩ rfl]
      exact (hperm ⟨u, by omega⟩ u rfl).symm
    obtain ⟨Y₂, hY₂, hY₁Y₂, hinv, hbdry, hend, -, hrot, hS₂, harc, -, -, hiso⟩ :=
      hS₁.exists_moveEquivalent_hIsomorphic_arcCut Y₁.isTripleDiagram _ hN₁ hCC
    have hπ₂ : Y₂.strandPerm = Y₁.data.strandPerm := hY₁Y₂.strandPerm_eq
    have hB₂ : Y₂.IsBoundaryParallel i I :=
      TripleData.isBoundaryParallel_of_lift Y₁.isTripleDiagram hY₂ hπ₂ hinv hbdry hend hrot hS₂
        harc hB₁
    exact hY.of_moveEquivalent (hYY₁.trans (hY₁Y₂.trans
      (MoveEquivalent.of_isomorphic (X := ⟨_, Y₂, hY₂⟩) (X' := ⟨H, X, hX⟩)
        (hB₂.isomorphic_of_hIsomorphic_arcCut hY₂ hX (by rw [hπ₂, hπ₁]) hB
          (by rw [hπ₂, ← hπ₁]) (hiso.trans (hIsomorphic_cast hm C))))))

/-- **Standard triple diagrams are minimal**: every standard triple diagram is minimal. -/
@[cluster_algebras "lem_standard_minimal"]
theorem IsStandard.isMinimal {X : TripleDiagram b} (hX : X.IsStandard) : X.IsMinimal :=
  isMinimal_of_isStandard hX X.isTripleDiagram

/-! ### Minimality and badgons -/

/-- If a diagram reached from `X` by swivel moves at digons has a badgon, so does `X`. -/
private theorem hasBadgon_of_reflTransGen_swivelStep {H : Type} [Fintype H] [DecidableEq H]
    {X Z : TripleData H b} (hX : X.IsTripleDiagram)
    (hXZ : Relation.ReflTransGen TripleData.SwivelStep X Z) (hZ : Z.HasBadgon) : X.HasBadgon := by
  induction hXZ with
  | refl => exact hZ
  | tail hXW hst ih =>
    obtain ⟨d₁, hd, rfl⟩ := hst
    apply ih
    have hW := TripleData.isTripleDiagram_of_reflTransGen_swivelStep hXW hX
    obtain ⟨hd', -, ⟨θ⟩⟩ := hd.swivelMove_swivelMove hW.toIsPreTripleDiagram
    exact θ.hasBadgon (TripleData.hasBadgon_swivelMove (hd.isTripleDiagram_swivelMove hW) hd' hZ)

/-- **Minimality and badgons**: a triple diagram is minimal if and only if it has no badgon. -/
@[cluster_algebras "thm_minimal_iff_no_badgon"]
theorem isMinimal_iff_not_hasBadgon {X : TripleDiagram b} :
    X.IsMinimal ↔ ¬X.data.HasBadgon := by
  refine ⟨IsMinimal.not_hasBadgon, fun h => IsMonogonStable.isMinimal fun X' hXX' hmono => ?_⟩
  obtain ⟨Y, hY, ⟨θ⟩⟩ := hXX'.exists_swivelSteps
  exact h (hasBadgon_of_reflTransGen_swivelStep X.isTripleDiagram hY
    (θ.symm.hasBadgon (Or.inl hmono)))

end TripleDiagram

end ClusterAlgebras
